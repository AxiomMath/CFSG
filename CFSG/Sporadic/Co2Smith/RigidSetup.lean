module

public import CFSG.Sporadic.Co2Smith.FrameRel
public import CFSG.Sporadic.Co2Smith.RigidCount
public import CFSG.Sporadic.Co2Smith.PinCheck
public import CFSG.Sporadic.Co2Smith.SmithCo2

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open CFSG.Assembly.LowTwoRank

universe u

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def resS0 :
    S0 →* Sp62 := resSp.comp (Subgroup.inclusion S0_le_Cz)

theorem resS0_injective :
    Function.Injective resS0 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : Subgroup.inclusion S0_le_Cz g ∈ resSp.ker := hg
  rw [ker_resSp, Subgroup.mem_subgroupOf] at h1
  have h2 : (g : K) ∈ S0 ⊓ Qsub := ⟨g.2, h1⟩
  rw [S0_inf_Q, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

theorem resS0_bijective :
    Function.Bijective resS0 :=
  resS0_injective.bijective_of_nat_card_le (by rw [natCard_sp62, card_S0])

instance isSimpleGroup_S0 :
    IsSimpleGroup S0 :=
  have := isSimpleGroup_sp62
  (MulEquiv.ofBijective resS0 resS0_bijective).isSimpleGroup

theorem frS_zero_ne_one :
    frS 0 ≠ 1 := by
  intro h
  have h1 : (frE 0).val.val = rowsMatrix 22 (idRows 22) := by
    rw [← frS_val (by norm_num), h, Subgroup.coe_one, val_val_one, rowsMatrix_idRows]
  have h2 := eq_of_rowsMatrix_eq (validM_fRows (by norm_num)) validM_idRows
    ((frE_val (by norm_num)).symm.trans h1)
  have h3 := frameNe_check
  rw [Native.frameNeOK, h2] at h3
  simp at h3

theorem frS_eight_ne_one :
    frS 8 ≠ 1 := by
  intro h
  apply xE_ne_one
  rw [xE, ← frS_val (by norm_num), h, Subgroup.coe_one]

structure LocalConfig :
    Type (u + 1) where
  H : Type u
  [grp : Group H]
  [fin : Finite H]
  loc : SmithLocal H
  ψ : S0 →* H ⧸ CFSG.pCore 2 H
  ψ_inj : Function.Injective ψ
  ℓ : S0 → H
  ℓ_mk : ∀ g, (QuotientGroup.mk (ℓ g) : H ⧸ CFSG.pCore 2 H) = ψ g
  xh : H
  xh_pow : xh ^ 5 = 1
  xh_mk : (QuotientGroup.mk xh : H ⧸ CFSG.pCore 2 H) = ψ (frS 8)

attribute [instance] LocalConfig.grp LocalConfig.fin

namespace LocalConfig

variable (c : LocalConfig.{u})

abbrev E : Subgroup c.H := CFSG.pCore 2 c.H

theorem card_E : Nat.card c.E = 2 ^ 9 := c.loc.card_pCore

theorem card_H : Nat.card c.H = 743178240 := by
  obtain ⟨φ⟩ := c.loc.quotient_equiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup c.E, Nat.card_congr φ.toEquiv,
    natCard_sp62, c.card_E]
  norm_num

theorem card_quot : Nat.card (c.H ⧸ c.E) = 1451520 := by
  obtain ⟨φ⟩ := c.loc.quotient_equiv
  rw [Nat.card_congr φ.toEquiv, natCard_sp62]

theorem ψ_bijective :
    Function.Bijective c.ψ :=
  c.ψ_inj.bijective_of_nat_card_le (by rw [c.card_quot, card_S0])

@[expose] noncomputable def fr (i : ℕ) : c.H := c.ℓ (frS i)

theorem orderOf_xh :
    orderOf c.xh = 5 :=
  orderOf_eq_prime c.xh_pow fun h => frS_eight_ne_one (c.ψ_inj (by
    rw [map_one, ← c.xh_mk, h, QuotientGroup.mk_one]))

theorem mem_center_of_comm_xh
    (e : c.E) (he : c.xh * e = e * c.xh) :
    e ∈ Subgroup.center c.E := by
  have hp : IsPGroup 5 (Subgroup.zpowers c.xh) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.orderOf_xh, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hPcard : Nat.card P = 5 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp P.isPGroup'
    have hdvd : 5 ^ k ∣ 743178240 := hk ▸ c.card_H ▸ Subgroup.card_subgroup_dvd_card _
    have hz5 : Nat.card (Subgroup.zpowers c.xh) = 5 := by
      rw [Nat.card_zpowers, c.orderOf_xh]
    have hge : 5 ≤ 5 ^ k :=
      calc 5 = Nat.card (Subgroup.zpowers c.xh) := hz5.symm
        _ ≤ Nat.card P := Subgroup.card_le_of_le hP
        _ = 5 ^ k := hk
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k <;> simp_all
      · exfalso
        have : 25 ∣ 743178240 := (pow_dvd_pow 5 h).trans hdvd
        norm_num at this
    rw [hk, hk1, pow_one]
  have hPeq : (P : Subgroup c.H) = Subgroup.zpowers c.xh :=
    (Subgroup.eq_of_le_of_card_ge hP
      (by rw [hPcard, Nat.card_zpowers, c.orderOf_xh])).symm
  have hcomm : ∀ p ∈ P, p * (e : c.H) = e * p := by
    intro p hp
    have hp' : p ∈ Subgroup.zpowers c.xh := hPeq ▸ hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp'
    exact (Commute.zpow_left he k).eq
  rw [Subgroup.mem_center_iff]
  intro e'
  apply Subtype.ext
  exact (c.loc.sylow_five P e e.2 hcomm e' e'.2).symm

@[expose] noncomputable def cE (h : c.H) : c.E ≃* c.E := MulAut.conjNormal h

theorem cE_val
    (h : c.H) (e : c.E) : (c.cE h e : c.H) = h * e * h⁻¹ :=
  MulAut.conjNormal_apply h e

theorem cE_mul
    (h₁ h₂ : c.H) (e : c.E) : c.cE (h₁ * h₂) e = c.cE h₁ (c.cE h₂ e) := by
  apply Subtype.ext
  rw [cE_val, cE_val, cE_val]
  group

theorem cE_one
    (e : c.E) : c.cE 1 e = e := by
  apply Subtype.ext
  rw [cE_val]
  group

theorem cE_pow
    (h : c.H) (n : ℕ) (e : c.E) : (c.cE h)^[n] e = c.cE (h ^ n) e := by
  induction n generalizing e with
  | zero => rw [Function.iterate_zero, id, pow_zero, cE_one]
  | succ n ih => rw [Function.iterate_succ_apply, ih, ← cE_mul, ← pow_succ]

theorem cE_xh_iff
    (e : c.E) : c.cE c.xh e = e ↔ c.xh * e = e * c.xh := by
  rw [← Subtype.coe_inj, cE_val, mul_inv_eq_iff_eq_mul]

theorem card_modEq_CEx
    (T : Subgroup c.E) (hT : ∀ t ∈ T, c.cE c.xh t ∈ T)
    (hC : ∀ e : c.E, c.xh * e = e * c.xh → e ∈ T) :
    Nat.card T ≡ Nat.card {e : c.E // c.xh * e = e * c.xh} [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let f : T → T := fun t => ⟨c.cE c.xh t, hT t t.2⟩
  have hf : ∀ t, f^[5 ^ 1] t = t := by
    intro t
    have key : ∀ n (t : T), ((f^[n] t : T) : c.E) = (c.cE c.xh)^[n] t := by
      intro n
      induction n with
      | zero => intro t; rfl
      | succ n ih =>
        intro t
        rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    apply Subtype.ext
    rw [key, cE_pow, pow_one, c.xh_pow, cE_one]
  have h := card_modEq_fixed f hf
  have e : Nat.card {t : T // f t = t} = Nat.card {e : c.E // c.xh * e = e * c.xh} :=
    Nat.card_congr
      { toFun := fun t => ⟨t.1.1, (c.cE_xh_iff _).mp (congrArg Subtype.val t.2)⟩
        invFun := fun e => ⟨⟨e.1, hC e.1 e.2⟩, Subtype.ext ((c.cE_xh_iff _).mpr e.2)⟩
        left_inv := fun t => rfl
        right_inv := fun e => rfl }
  rw [← e]
  exact h

theorem char_mem {G : Type*} [Group G] (N : Subgroup G) [N.Characteristic] (ϕ : G ≃* G) {n : G}
    (hn : n ∈ N) : ϕ n ∈ N := by
  have h := (inferInstance : N.Characteristic).fixed ϕ
  rw [← h] at hn
  exact hn

@[expose] noncomputable def secAct (N : Subgroup c.E) [N.Characteristic] (h : c.H) :
    c.E ⧸ N →* c.E ⧸ N :=
  QuotientGroup.map N N (c.cE h).toMonoidHom fun _ hn => char_mem N (c.cE h) hn

theorem secAct_mk
    (N : Subgroup c.E) [N.Characteristic] (h : c.H) (e : c.E) :
    c.secAct N h (QuotientGroup.mk e) = QuotientGroup.mk (c.cE h e) := rfl

theorem secAct_mul (N : Subgroup c.E) [N.Characteristic] (h₁ h₂ : c.H) (q : c.E ⧸ N) :
    c.secAct N (h₁ * h₂) q = c.secAct N h₁ (c.secAct N h₂ q) := by
  induction q using QuotientGroup.induction_on with
  | H e => rw [secAct_mk, secAct_mk, secAct_mk, cE_mul]

theorem secAct_one (N : Subgroup c.E) [N.Characteristic] (q : c.E ⧸ N) :
    c.secAct N 1 q = q := by
  induction q using QuotientGroup.induction_on with
  | H e => rw [secAct_mk, cE_one]

theorem secAct_of_mem (N : Subgroup c.E) [N.Characteristic]
    (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N) {e : c.H} (he : e ∈ c.E) (q : c.E ⧸ N) :
    c.secAct N e q = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [secAct_mk, QuotientGroup.eq]
    have h := hab ⟨e, he⟩ x⁻¹
    have e1 : (c.cE e x)⁻¹ * x = ⟨e, he⟩ * x⁻¹ * (⟨e, he⟩ : c.E)⁻¹ * x⁻¹⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, cE_val, inv_inv]
      group
    rw [e1]
    exact h

@[expose] noncomputable def qAct (N : Subgroup c.E) [N.Characteristic]
    (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N) (q : c.H ⧸ c.E) : c.E ⧸ N →* c.E ⧸ N :=
  Quotient.liftOn' q (fun h => c.secAct N h) fun h h' hh => by
    ext x
    have hm : h⁻¹ * h' ∈ c.E := QuotientGroup.leftRel_apply.mp hh
    have e1 : h' = h * (h⁻¹ * h') := by group
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [e1, secAct_mul, c.secAct_of_mem N hab hm]

theorem qAct_mk
    (N : Subgroup c.E) [N.Characteristic] (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N)
    (h : c.H) : c.qAct N hab (QuotientGroup.mk h) = c.secAct N h := rfl

theorem qAct_mul (N : Subgroup c.E) [N.Characteristic]
    (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N) (p q : c.H ⧸ c.E) (x : c.E ⧸ N) :
    c.qAct N hab (p * q) x = c.qAct N hab p (c.qAct N hab q x) := by
  induction p using QuotientGroup.induction_on with
  | H h =>
    induction q using QuotientGroup.induction_on with
    | H h' => rw [← QuotientGroup.mk_mul, qAct_mk, qAct_mk, qAct_mk, secAct_mul]

@[expose] noncomputable def sA (N : Subgroup c.E) [N.Characteristic]
    (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N) (g : S0) : c.E ⧸ N →* c.E ⧸ N :=
  c.qAct N hab (c.ψ g)

theorem sA_mul (N : Subgroup c.E) [N.Characteristic] (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N)
    (g h : S0) (q : c.E ⧸ N) : c.sA N hab (g * h) q = c.sA N hab g (c.sA N hab h q) := by
  rw [sA, map_mul, qAct_mul]
  rfl

theorem sA_one (N : Subgroup c.E) [N.Characteristic] (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N)
    (q : c.E ⧸ N) : c.sA N hab 1 q = q := by
  rw [sA, map_one, ← QuotientGroup.mk_one, qAct_mk, secAct_one]

theorem sA_eq_secAct (N : Subgroup c.E) [N.Characteristic]
    (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N) {g : S0} {h : c.H}
    (hgh : (QuotientGroup.mk h : c.H ⧸ c.E) = c.ψ g) : c.sA N hab g = c.secAct N h := by
  rw [sA, ← hgh, qAct_mk]

theorem sA_xh (N : Subgroup c.E) [N.Characteristic]
    (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N) : c.sA N hab (frS 8) = c.secAct N c.xh :=
  c.sA_eq_secAct N hab c.xh_mk

theorem sec_card_mod5
    (N : Subgroup c.E) [N.Characteristic]
    (hN : ∀ e : c.E, c.xh * e = e * c.xh → e ∈ N) (U : Subgroup (c.E ⧸ N))
    (hU : ∀ u ∈ U, c.secAct N c.xh u ∈ U) : Nat.card U % 5 = 1 := by
  set T := U.comap (QuotientGroup.mk' N) with hT
  have hTinv : ∀ t ∈ T, c.cE c.xh t ∈ T := by
    intro t ht
    exact hU _ ht
  have hNT : N ≤ T := by
    intro n hn
    show (n : c.E ⧸ N) ∈ U
    rw [(QuotientGroup.eq_one_iff n).mpr hn]
    exact U.one_mem
  have hNinv : ∀ n ∈ N, c.cE c.xh n ∈ N := fun n hn => char_mem N (c.cE c.xh) hn
  have h1 := c.card_modEq_CEx T hTinv fun e he => hNT (hN e he)
  have h2 := c.card_modEq_CEx N hNinv hN
  have hcardT : Nat.card T = Nat.card U * Nat.card N := by
    have hi : T.index = U.index :=
      Subgroup.index_comap_of_surjective U (QuotientGroup.mk'_surjective N)
    have e1 := Subgroup.card_mul_index T
    have e2 := Subgroup.card_mul_index U
    have e3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hne : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hi] at e1
    rw [← e2] at e3
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (by rw [e1, e3]; ring)
  have h3 : Nat.card U * Nat.card N ≡ 1 * Nat.card N [MOD 5] := by
    rw [← hcardT, one_mul]
    exact h1.trans h2.symm
  have hcop : Nat.Coprime (Nat.card N) 5 := by
    have hdvd : Nat.card N ∣ 2 ^ 9 := c.card_E ▸ Subgroup.card_subgroup_dvd_card N
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj]
    exact Nat.Coprime.pow_left _ (by norm_num)
  exact Nat.ModEq.cancel_right_of_coprime hcop.symm h3

theorem sec_card_mod5' (N : Subgroup c.E) [N.Characteristic]
    (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N) (hN : ∀ e : c.E, c.xh * e = e * c.xh → e ∈ N)
    (U : Subgroup (c.E ⧸ N)) (hU : ∀ u ∈ U, c.sA N hab (frS 8) u ∈ U) : Nat.card U % 5 = 1 :=
  c.sec_card_mod5 N hN U (by rw [← c.sA_xh N hab]; exact hU)

theorem sec_trivial_of_y1
    (N : Subgroup c.E) [N.Characteristic]
    (hab : ∀ a b : c.E, a * b * a⁻¹ * b⁻¹ ∈ N) (Ω : Subgroup (c.E ⧸ N))
    (hΩ : ∀ g : S0, ∀ a ∈ Ω, c.sA N hab g a ∈ Ω)
    (hy : ∀ a ∈ Ω, c.sA N hab (frS 0) a = a) :
    ∀ g : S0, ∀ a ∈ Ω, c.sA N hab g a = a := by
  let K0 : Subgroup S0 :=
    { carrier := {g | ∀ a ∈ Ω, c.sA N hab g a = a}
      mul_mem' := fun {g h} hg hh a ha => by
        rw [Set.mem_ofPred_eq] at hg hh
        rw [sA_mul, hh a ha, hg a ha]
      one_mem' := fun a _ => c.sA_one N hab a
      inv_mem' := fun {g} hg a ha => by
        rw [Set.mem_ofPred_eq] at hg
        have hb := hΩ g⁻¹ a ha
        have e1 := hg _ hb
        rw [← sA_mul, mul_inv_cancel, sA_one] at e1
        exact e1.symm }
  have hK0 : K0.Normal := ⟨fun g hg h a ha => by
    show c.sA N hab (h * g * h⁻¹) a = a
    have hb := hΩ h⁻¹ a ha
    rw [sA_mul, sA_mul, hg _ hb, ← sA_mul, mul_inv_cancel, sA_one]⟩
  have hy0 : frS 0 ∈ K0 := hy
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K0 with h | h
  · exact absurd (h ▸ hy0 : frS 0 ∈ (⊥ : Subgroup S0)) (by
      rw [Subgroup.mem_bot]; exact frS_zero_ne_one)
  · intro g a ha
    have hg : g ∈ K0 := h ▸ Subgroup.mem_top g
    exact hg a ha

end LocalConfig

section OfLocal

variable {H : Type u} [Group H] (hH : SmithLocal H)
include hH

@[expose] noncomputable def psiOf :
    S0 →* H ⧸ CFSG.pCore 2 H :=
  (Classical.choice hH.quotient_equiv).symm.toMonoidHom.comp resS0

theorem psiOf_injective :
    Function.Injective (psiOf hH) :=
  (Classical.choice hH.quotient_equiv).symm.injective.comp resS0_injective

theorem pow_512_of_mem {e : H} (he : e ∈ CFSG.pCore 2 H) : e ^ 512 = 1 := by
  have h := pow_card_eq_one' (G := CFSG.pCore 2 H) (x := ⟨e, he⟩)
  rw [hH.card_pCore] at h
  have h2 := congrArg (fun x : CFSG.pCore 2 H => (x : H)) h
  simpa using h2

@[expose] noncomputable def xhOf :
    H := (Quotient.out (psiOf hH (frS 8))) ^ 1536

theorem xhOf_mk :

    (QuotientGroup.mk (xhOf hH) : H ⧸ CFSG.pCore 2 H) = psiOf hH (frS 8) := by
  rw [xhOf, QuotientGroup.mk_pow, QuotientGroup.out_eq', ← map_pow]
  congr 1
  calc frS 8 ^ 1536 = (frS 8 ^ 5) ^ 307 * frS 8 := by rw [← pow_mul, ← pow_succ]
    _ = frS 8 := by rw [frS_x_pow, one_pow, one_mul]

theorem xhOf_pow :
    xhOf hH ^ 5 = 1 := by
  set h₀ := Quotient.out (psiOf hH (frS 8))
  have hE : h₀ ^ 5 ∈ CFSG.pCore 2 H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.out_eq', ← map_pow,
      frS_x_pow, map_one]
  calc xhOf hH ^ 5 = ((h₀ ^ 5) ^ 512) ^ 3 := by
        rw [xhOf, ← pow_mul, ← pow_mul, ← pow_mul]
    _ = 1 := by rw [pow_512_of_mem hH hE, one_pow]

@[expose] noncomputable def LocalConfig.ofLocal
    [Finite H] : LocalConfig.{u} where
  H := H
  loc := hH
  ψ := psiOf hH
  ψ_inj := psiOf_injective hH
  ℓ g := Quotient.out (psiOf hH g)
  ℓ_mk _ := QuotientGroup.out_eq' _
  xh := xhOf hH
  xh_pow := xhOf_pow hH
  xh_mk := xhOf_mk hH

end OfLocal

structure SmithConfig :
    Type (u + 1) extends LocalConfig.{u} where
  ℓ_mul : ∀ g h : S0, ℓ (g * h) = ℓ g * ℓ h

namespace SmithConfig

variable (c : SmithConfig.{u})

@[expose] noncomputable def ι : S0 →* c.H := MonoidHom.mk' c.ℓ c.ℓ_mul

theorem mk_ι
    (g : S0) : (QuotientGroup.mk (c.ι g) : c.H ⧸ c.E) = c.ψ g := c.ℓ_mk g

theorem inj : Function.Injective c.ι := fun g h hgh =>
  c.ψ_inj (by rw [← c.mk_ι, ← c.mk_ι, hgh])

theorem inf_eq : c.ι.range ⊓ c.E = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨g, rfl⟩, hx⟩
  have h1 : c.ψ g = c.ψ 1 := by
    rw [← c.mk_ι, map_one, (QuotientGroup.eq_one_iff _).mpr hx]
  rw [c.ψ_inj h1, map_one]
  exact Subgroup.one_mem _

noncomputable abbrev ofComplement
    (H : Type u) [Group H] [Finite H] (loc : SmithLocal H)
    (ι : S0 →* H) (inj : Function.Injective ι) (inf_eq : ι.range ⊓ CFSG.pCore 2 H = ⊥) :
    SmithConfig.{u} where
  H := H
  loc := loc
  ψ := (QuotientGroup.mk' (CFSG.pCore 2 H)).comp ι
  ψ_inj := by
    intro g h hgh
    have h1 : (ι g)⁻¹ * ι h ∈ CFSG.pCore 2 H := QuotientGroup.eq.mp hgh
    have h2 : (ι g)⁻¹ * ι h ∈ ι.range ⊓ CFSG.pCore 2 H :=
      ⟨⟨g⁻¹ * h, by rw [map_mul, map_inv]⟩, h1⟩
    rw [inf_eq, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact inj h2
  ℓ := ι
  ℓ_mk _ := rfl
  xh := ι (frS 8)
  xh_pow := by rw [← map_pow, frS_x_pow, map_one]
  xh_mk := rfl
  ℓ_mul := map_mul ι

end SmithConfig

end CFSG.Sporadic.Co2Smith
