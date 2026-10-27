module

public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126a
public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126c
public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126d
public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126e
public import CFSG.Quasithin.Vol2.Ch12Sec6T2Basic

public section

namespace CFSG.Quasithin.H13.F126

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.LieType.BorelTits S126 S126P Equiv

variable {G : Type} [Group G]

section Star

variable {H : Subgroup G}

theorem mkH_eq_one_iff {x : ↥H} :
    (QuotientGroup.mk x : S126.HStar H) = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    exact ⟨x, by assumption, rfl⟩
  · rintro ⟨q, hq, hqx⟩
    rw [← Subtype.ext hqx]
    exact hq

theorem mem_pCoreOf_of_mk_eq {x y : ↥H}
    (hxy : (QuotientGroup.mk x : S126.HStar H) = QuotientGroup.mk y) :
    (x : G)⁻¹ * y ∈ pCoreOf 2 H := by
  rw [QuotientGroup.eq] at hxy
  exact ⟨x⁻¹ * y, by assumption, rfl⟩

theorem card_star [Finite G] {X : Subgroup G} (hXH : X ≤ H) :
    Nat.card (S126.star H X) * Nat.card ↥(X ⊓ pCoreOf 2 H) = Nat.card X := by
  let f : ↥(X.subgroupOf H) →* S126.HStar H :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (X.subgroupOf H).subtype
  have hr : f.range = S126.star H X := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hk : Nat.card f.ker = Nat.card ↥(X ⊓ pCoreOf 2 H) := by
    refine Nat.card_congr ⟨fun x => ⟨(((x : ↥(X.subgroupOf H)) : ↥H) : G), ?_, ?_⟩,
      fun y => ⟨⟨⟨y, hXH y.2.1⟩, y.2.1⟩, ?_⟩, fun x => ?_, fun y => ?_⟩
    · exact (x : ↥(X.subgroupOf H)).2
    · exact mkH_eq_one_iff.1 x.2
    · exact mkH_eq_one_iff.2 y.2.2
    · rfl
    · rfl
  have hX : Nat.card ↥(X.subgroupOf H) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  rw [← hX, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hr, hk]

end Star

section Core

variable {T V L V₁ Vp H : Subgroup G}

theorem conj_inv_mul_conj_mem [Finite G] (h : HypF91 T V L V₁ Vp H) {z₁ z₂ : G} (hz₂ : z₂ ∈ H)
    (hq : z₂⁻¹ * z₁ ∈ pCoreOf 2 H) {v : G} (hv : v ∈ conjClosure Vp H) :
    (z₁ * v * z₁⁻¹)⁻¹ * (z₂ * v * z₂⁻¹) ∈ V₁ := by
  have hc : (z₂⁻¹ * z₁) * v⁻¹ * (z₂⁻¹ * z₁)⁻¹ * v⁻¹⁻¹ ∈ V₁ := by
    rw [h.pCoreOf_eq_centralizerMod] at hq
    exact hq.2.2 v⁻¹ ((conjClosure Vp H).inv_mem hv)
  have hcomm := Subgroup.mem_centralizer_iff.1 (h.H_le_centralizer hz₂) _ hc
  have e : (z₁ * v * z₁⁻¹)⁻¹ * (z₂ * v * z₂⁻¹) =
      z₂ * ((z₂⁻¹ * z₁) * v⁻¹ * (z₂⁻¹ * z₁)⁻¹ * v⁻¹⁻¹) * z₂⁻¹ := by group
  rw [e, ← hcomm, mul_inv_cancel_right]
  exact hc

theorem psiH_conj [Finite G] (h : HypF91 T V L V₁ Vp H) (e : S126.HStar H ≃* S53)
    (q : S126.HStar H) :
    psiH h q * psiH h (xQ e) * (psiH h q)⁻¹ = psiH h (xQ e) ∨
      psiH h q * psiH h (xQ e) * (psiH h q)⁻¹ = psiH h (xQ e) ^ 2 := by
  rcases conj_xQ e q with hq | hq
  · left
    rw [← map_inv, ← map_mul, ← map_mul, hq]
  · right
    rw [← map_inv, ← map_mul, ← map_mul, hq, map_pow]

end Core

section Aut

variable {W : Type*} [CommGroup W]

theorem cm_sq_le (x : MulAut W) : cm (x ^ 2) ≤ cm x := by
  rintro _ ⟨w, -, rfl⟩
  have e : cmHom (x ^ 2) w = cmHom x (x w) * cmHom x w := by
    simp only [cmHom_apply, pow_two, MulAut.mul_apply]
    group
  rw [e]
  exact (cm x).mul_mem (mem_cm x _) (mem_cm x w)

theorem cm_invariant_of_conj {x g : MulAut W} (hg : g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x ^ 2) :
    ∀ s ∈ cm x, g s ∈ cm x := by
  intro s hs
  have h1 : g s ∈ cm (g * x * g⁻¹) := by
    have := cmOn_conj x g ⊤
    rw [map_top_mulAut] at this
    show g s ∈ cmOn (g * x * g⁻¹) ⊤
    rw [this]
    exact ⟨s, hs, rfl⟩
  rcases hg with hg | hg
  · rwa [hg] at h1
  · rw [hg] at h1
    exact cm_sq_le x h1

theorem fx_invariant_of_conj {x g : MulAut W}
    (hg : g⁻¹ * x * g = x ∨ g⁻¹ * x * g = x ^ 2) : ∀ s ∈ fx x, g s ∈ fx x := by
  intro s hs
  rw [mem_fx] at hs ⊢
  have h2 : (x ^ 2) s = s := by rw [pow_two, MulAut.mul_apply, hs, hs]
  have key : (g⁻¹ * x * g) s = s := by
    rcases hg with hg | hg
    · rw [hg]; exact hs
    · rw [hg]; exact h2
  calc x (g s) = g ((g⁻¹ * x * g) s) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    _ = g s := by rw [key]

end Aut

section Coord

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem mem_V1_iff_beta (F : Frame126 T L V) (v : ↥V) : (v : G) ∈ F.V1 ↔ F.β v ∈ W1 := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hwv' : w = v := Subtype.ext hwv
    subst hwv'
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem mem_V5_iff_beta (F : Frame126 T L V) (v : ↥V) : (v : G) ∈ F.V5 ↔ F.β v ∈ W5 := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hwv' : w = v := Subtype.ext hwv
    subst hwv'
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem actEq_of_conj (F : Frame126 T L V) {z₁ z₂ : G}
    (hz₁ : z₁ ∈ Subgroup.normalizer (V : Set G)) (hz₂ : z₂ ∈ Subgroup.normalizer (V : Set G))
    {σ₁ σ₂ : Perm (Fin 8)} (h₁ : ActsAs F z₁ σ₁) (h₂ : ActsAs F z₂ σ₂)
    (h : ∀ v ∈ F.V5, (z₁ * v * z₁⁻¹)⁻¹ * (z₂ * v * z₂⁻¹) ∈ F.V1) : ActEq σ₁ σ₂ := by
  intro y hy
  obtain ⟨v, rfl⟩ := F.β_surj y
  have hv5 : (v : G) ∈ F.V5 := (mem_V5_iff_beta F v).2 hy
  set w₁ : ↥V := ⟨z₁ * v * z₁⁻¹, conj_mem hz₁ v⟩
  set w₂ : ↥V := ⟨z₂ * v * z₂⁻¹, conj_mem hz₂ v⟩
  have h1 : F.β (w₁⁻¹ * w₂) ∈ W1 := (mem_V1_iff_beta F (w₁⁻¹ * w₂)).1 (h v hv5)
  rw [map_mul, map_inv, h₁ v w₁ rfl, h₂ v w₂ rfl] at h1
  have h2 := W1.inv_mem h1
  rwa [mul_inv_rev, inv_inv, S126L20a.D8_comm] at h2

theorem conj_of_actEq (F : Frame126 T L V) {z₁ z₂ : G}
    (hz₁ : z₁ ∈ Subgroup.normalizer (V : Set G)) (hz₂ : z₂ ∈ Subgroup.normalizer (V : Set G))
    {σ₁ σ₂ : Perm (Fin 8)} (h₁ : ActsAs F z₁ σ₁) (h₂ : ActsAs F z₂ σ₂) (h : ActEq σ₁ σ₂) :
    ∀ v ∈ F.V5, (z₁ * v * z₁⁻¹)⁻¹ * (z₂ * v * z₂⁻¹) ∈ F.V1 := by
  rintro _ ⟨u, hu, rfl⟩
  have h1 := W1.inv_mem (h _ hu)
  rw [mul_inv_rev, inv_inv, S126L20a.D8_comm] at h1
  set w₁ : ↥V := ⟨z₁ * u * z₁⁻¹, conj_mem hz₁ u⟩
  set w₂ : ↥V := ⟨z₂ * u * z₂⁻¹, conj_mem hz₂ u⟩
  rw [← h₁ u w₁ rfl, ← h₂ u w₂ rfl, ← map_inv, ← map_mul] at h1
  exact (mem_V1_iff_beta F (w₁⁻¹ * w₂)).2 h1

theorem mem_V1_of_actFpf (F : Frame126 T L V) {z : G} (hz : z ∈ Subgroup.normalizer (V : Set G))
    {σ : Perm (Fin 8)} (hσ : ActsAs F z σ) (hf : ActFpf σ) {v : G} (hv : v ∈ F.V5)
    (h : (z * v * z⁻¹)⁻¹ * v ∈ F.V1) : v ∈ F.V1 := by
  obtain ⟨u, hu, rfl⟩ := hv
  set w : ↥V := ⟨z * u * z⁻¹, conj_mem hz u⟩
  have h1 : F.β (w⁻¹ * u) ∈ W1 := (mem_V1_iff_beta F (w⁻¹ * u)).1 h
  rw [map_mul, map_inv, hσ u w rfl] at h1
  have h2 := W1.inv_mem h1
  rw [mul_inv_rev, inv_inv, S126L20a.D8_comm] at h2
  exact (mem_V1_iff_beta F u).2 (hf _ hu h2)

end Coord

theorem e9_mul : ∀ i j k l : Fin 3, aP ^ i.val * bP ^ j.val * (aP ^ k.val * bP ^ l.val) =
    aP ^ (i + k).val * bP ^ (j + l).val := by
  decide +kernel

theorem e9_inv : ∀ i j : Fin 3, (aP ^ i.val * bP ^ j.val)⁻¹ = aP ^ (-i).val * bP ^ (-j).val := by
  decide +kernel

theorem e9_inj : ∀ i j k l : Fin 3, aP ^ i.val * bP ^ j.val = aP ^ k.val * bP ^ l.val →
    i = k ∧ j = l := by
  decide +kernel

@[expose] def E9 : Subgroup (Perm (Fin 8)) where
  carrier := {σ | ∃ i j : Fin 3, σ = aP ^ i.val * bP ^ j.val}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact ⟨i + k, j + l, e9_mul i j k l⟩
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    exact ⟨-i, -j, e9_inv i j⟩

theorem card_E9 : Nat.card E9 = 9 := by
  have hbij : Function.Bijective
      (fun p : Fin 3 × Fin 3 => (⟨aP ^ p.1.val * bP ^ p.2.val, p.1, p.2, rfl⟩ : E9)) := by
    constructor
    · rintro ⟨i, j⟩ ⟨k, l⟩ hij
      have := e9_inj i j k l (congrArg Subtype.val hij)
      exact Prod.ext this.1 this.2
    · rintro ⟨σ, i, j, rfl⟩
      exact ⟨(i, j), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_fin]

theorem sq_of_mem_E16 {τ : Perm (Fin 8)} (hτ : τ ∈ S126E.E16) : τ ^ 2 = 1 := by
  obtain ⟨u, v, rfl⟩ := hτ
  calc S126E.tau u v ^ 2 = (S126E.tau u v)⁻¹ * S126E.tau u v := by rw [pow_two, S126E.tau_inv]
    _ = 1 := inv_mul_cancel _

theorem L1_le_L {L W : Subgroup G} : Li L W ≤ L := (oTwoRes_le _).trans inf_le_left

theorem L1_le_normalizer {L W : Subgroup G} : Li L W ≤ Subgroup.normalizer (W : Set G) :=
  (oTwoRes_le _).trans inf_le_right

section Lift

variable [Finite G] {T L V H : Subgroup G} [IsMulCommutative ↥V]

theorem nine_dvd_card_star_L1 (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (h : HypF91 T V L F.V1 F.V5 H) : 9 ∣ Nat.card (S126.star H (Li L F.V1)) := by
  have hL1H : Li L F.V1 ≤ H := le_sup_left.trans h.L₁T_le_H
  set f : ↥L →* Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp (S126L19a.psi F hH)
  set I := ((Li L F.V1).subgroupOf L).map f
  have hmem : ∀ c : Perm (Fin 8), c ∈ alternatingGroup (Fin 8) → c ^ 3 = 1 →
      (∀ i : Fin 8, (i.val < 4 ↔ (c i).val < 4)) → c ∈ I := by
    intro c hc hc3 hcb
    obtain ⟨l, hl1, hlV, hl⟩ := S126L1b.exists_mem_L1 F hc hc3 hcb
    exact ⟨⟨l, L1_le_L hl1⟩, hl1, (S126L19a.actsAs_psi F hH ⟨l, L1_le_L hl1⟩).unique hl hlV⟩
  have hE9 : E9 ≤ I := by
    rintro _ ⟨i, j, rfl⟩
    exact I.mul_mem (I.pow_mem (hmem aP aP_mem aP_pow_three aP_block) _)
      (I.pow_mem (hmem bP bP_mem bP_pow_three bP_block) _)
  have h9I : 9 ∣ Nat.card I := by
    rw [← card_E9]
    exact Subgroup.card_dvd_of_le hE9
  have hIL : Nat.card I ∣ Nat.card (Li L F.V1) :=
    (Subgroup.card_map_dvd _ f).trans
      (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe L1_le_L).toEquiv))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.to_le (pCoreOf_isPGroup 2 H)
    (inf_le_right : Li L F.V1 ⊓ pCoreOf 2 H ≤ _)).exists_card_eq
  have h9 : 9 ∣ Nat.card (S126.star H (Li L F.V1)) * 2 ^ k := by
    rw [← hk, card_star hL1H]
    exact h9I.trans hIL
  exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_right h9

theorem exists_lift (F : Frame126 T L V) (hH : Hyp126 G T L V) (h : HypF91 T V L F.V1 F.V5 H)
    (e : S126.HStar H ≃* S53) :
    ∃ y : ↥H, (y : G) ∈ Li L F.V1 ∧ (QuotientGroup.mk y : S126.HStar H) = xQ e ∧
      ∃ σ : Perm (Fin 8), ActsAs F (y : G) σ ∧ σ ^ 3 = 1 ∧
        ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  obtain ⟨z₀, hz₀L1, hz₀⟩ :=
    zpowers_le_of_dvd e (nine_dvd_card_star_L1 F hH h) (Subgroup.mem_zpowers _)
  have hz₀L1' : (z₀ : G) ∈ Li L F.V1 := hz₀L1
  have hz₀' : (QuotientGroup.mk z₀ : S126.HStar H) = xQ e := hz₀
  have hz₀V : (z₀ : G) ∈ Subgroup.normalizer (V : Set G) := hLV (L1_le_L hz₀L1')
  set σ₀ : Perm (Fin 8) :=
    ((S126L19a.psi F hH ⟨z₀, L1_le_L hz₀L1'⟩ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8))
  have hσ₀ : ActsAs F (z₀ : G) σ₀ := S126L19a.actsAs_psi F hH ⟨z₀, L1_le_L hz₀L1'⟩
  have hz₀3 : ((z₀ ^ 3 : ↥H) : G) ∈ pCoreOf 2 H := by
    rw [← mkH_eq_one_iff, QuotientGroup.mk_pow, hz₀', xQ_pow_three]
  have hA : ActEq (σ₀ ^ 3) 1 := by
    refine actEq_of_conj F (Subgroup.pow_mem _ hz₀V 3) (Subgroup.one_mem _) (hσ₀.pow hz₀V 3)
      (ActsAs.one F) fun v hv => ?_
    refine conj_inv_mul_conj_mem h (Subgroup.one_mem H) ?_ (le_conjClosure F.V5 H hv)
    rw [inv_one, one_mul, ← Subgroup.coe_pow]
    exact hz₀3
  have hσ₀3 : σ₀ ^ 3 ∈ S126E.E16 := S126L24.mem_E16_of_cent fun y hy => by
    have := hA y hy
    rwa [dAct_one] at this
  have hσ3 : (σ₀ ^ 16) ^ 3 = 1 := by
    rw [← pow_mul, show 16 * 3 = 3 * 2 * 8 from rfl, pow_mul, pow_mul, sq_of_mem_E16 hσ₀3,
      one_pow]
  have hyσ : ActsAs F ((z₀ ^ 16 : ↥H) : G) (σ₀ ^ 16) := by
    rw [Subgroup.coe_pow]
    exact hσ₀.pow hz₀V 16
  have hyL1 : ((z₀ ^ 16 : ↥H) : G) ∈ Li L F.V1 := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hz₀L1' 16
  refine ⟨z₀ ^ 16, hyL1, ?_, σ₀ ^ 16, hyσ, hσ3, ?_⟩
  · rw [QuotientGroup.mk_pow, hz₀', show 16 = 3 * 5 + 1 from rfl, pow_add, pow_mul,
      xQ_pow_three, one_pow, one_mul, pow_one]
  · rcases S126L19a.blocks_of_mem_V1 F (L1_le_normalizer hyL1) hyσ with hb | hb
    · exact hb
    · exfalso
      set σ := σ₀ ^ 16
      have e3 : (σ ^ 3) 0 = σ (σ (σ 0)) := by rw [pow_three, Perm.mul_apply, Perm.mul_apply]
      rw [hσ3, Perm.one_apply] at e3
      have h0 := (hb 0).1 (by decide)
      have h1 : (σ (σ 0)).val < 4 := by
        by_contra hc
        exact absurd ((hb (σ 0)).2 (by omega)) (by omega)
      have h3 := (hb (σ (σ 0))).1 h1
      rw [← e3] at h3
      exact absurd h3 (by decide)

theorem actEq_conj_bsw (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (h : HypF91 T V L F.V1 F.V5 H) (e : S126.HStar H ≃* S53) {y : ↥H}
    (hyL1 : (y : G) ∈ Li L F.V1) (hy : (QuotientGroup.mk y : S126.HStar H) = xQ e)
    {σ : Perm (Fin 8)} (hσ : ActsAs F (y : G) σ) :
    ActEq (S126L1c.bsw * σ * S126L1c.bsw⁻¹) σ ∨
      ActEq (S126L1c.bsw * σ * S126L1c.bsw⁻¹) (σ ^ 2) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hyV : (y : G) ∈ Subgroup.normalizer (V : Set G) := hLV (L1_le_L hyL1)
  obtain ⟨t, ⟨htT, htL⟩, ht⟩ :=
    S126T2.exists_TL_of_Q8 F hH S126L1c.bsw ⟨S126L1c.bsw_mem, S126L1c.bsw_mem_A8⟩
  have htH : t ∈ H := le_sup_right.trans h.L₁T_le_H htT
  have htV : t ∈ Subgroup.normalizer (V : Set G) := hLV htL
  set tH : ↥H := ⟨t, htH⟩
  have hz₁V : t * (y : G) * t⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htV hyV) (Subgroup.inv_mem _ htV)
  have hz₁ : ActsAs F (t * (y : G) * t⁻¹) (S126L1c.bsw * σ * S126L1c.bsw⁻¹) :=
    (ht.mul hσ hyV).mul ht.inv (Subgroup.inv_mem _ htV)
  have hmk : (QuotientGroup.mk (tH * y * tH⁻¹) : S126.HStar H) =
      QuotientGroup.mk tH * xQ e * (QuotientGroup.mk tH)⁻¹ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy]
  rcases conj_xQ e (QuotientGroup.mk tH) with hc | hc
  · left
    rw [hc, ← hy] at hmk
    refine actEq_of_conj F hz₁V hyV hz₁ hσ fun v hv => ?_
    exact conj_inv_mul_conj_mem h y.2 (mem_pCoreOf_of_mk_eq hmk.symm)
      (le_conjClosure F.V5 H hv)
  · right
    rw [hc, ← hy, ← QuotientGroup.mk_pow] at hmk
    refine actEq_of_conj F hz₁V (Subgroup.pow_mem _ hyV 2) hz₁ (hσ.pow hyV 2) fun v hv => ?_
    have hq := mem_pCoreOf_of_mk_eq hmk.symm
    rw [Subgroup.coe_pow] at hq
    exact conj_inv_mul_conj_mem h (Subgroup.pow_mem _ y.2 2) hq (le_conjClosure F.V5 H hv)

theorem not_actEq_one (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (h : HypF91 T V L F.V1 F.V5 H) (e : S126.HStar H ≃* S53) {y : ↥H}
    (hyL1 : (y : G) ∈ Li L F.V1) (hy : (QuotientGroup.mk y : S126.HStar H) = xQ e)
    {σ : Perm (Fin 8)} (hσ : ActsAs F (y : G) σ) : ¬ ActEq σ 1 := by
  intro hA
  let _ : CommGroup ↥(UT F.V1 F.V5 H) := commGroupOfElemAbelian h.isElemAbelian_tilde
  have hyV : (y : G) ∈ Subgroup.normalizer (V : Set G) :=
    hH.hyp.irrPlus.2.2.1 (L1_le_L hyL1)
  have hfix := conj_of_actEq F hyV (Subgroup.one_mem _) hσ (ActsAs.one F) hA
  set x := psiH h (xQ e) with hx
  have hxS : ∀ w : ↥(UT F.V1 F.V5 H), (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5 →
      w ∈ fx x := by
    intro w hw
    rw [mem_fx]
    obtain ⟨⟨v, hvN⟩, hv5, hvw⟩ := mem_secImg.1 hw
    apply Subtype.ext
    rw [hx, ← hy, psiH_mk, thetaH_apply, ← hvw, thetaH_apply_secMk, secMk_eq_secMk_iff]
    have h2 := hfix v hv5
    rwa [one_mul, inv_one, mul_one] at h2
  have hinv : ∀ z : ↥H, ∀ s ∈ fx x, thetaH h z s ∈ fx x := by
    intro z
    refine fx_invariant_of_conj ?_
    have := psiH_conj h e (QuotientGroup.mk z)⁻¹
    rwa [map_inv, inv_inv, psiH_mk] at this
  have htop := eq_top_of_le h (fx x) hxS hinv
  have hx1 : x = 1 := MulEquiv.ext fun w => by
    rw [MulAut.one_apply]
    exact mem_fx.1 (by rw [htop]; exact Subgroup.mem_top w)
  exact xQ_ne_one e (psiH_injective h (by rw [← hx, hx1, map_one]))

theorem fpf_xQ (F : Frame126 T L V) (hH : Hyp126 G T L V) (h : HypF91 T V L F.V1 F.V5 H)
    (e : S126.HStar H ≃* S53) (w : ↥(UT F.V1 F.V5 H)) (hw : psiH h (xQ e) w = w) : w = 1 := by
  let _ : CommGroup ↥(UT F.V1 F.V5 H) := commGroupOfElemAbelian h.isElemAbelian_tilde
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  obtain ⟨y, hyL1, hy, σ, hσ, hσ3, hblock⟩ := exists_lift F hH h e
  have hyV : (y : G) ∈ Subgroup.normalizer (V : Set G) := hLV (L1_le_L hyL1)
  have hfpf : ActFpf σ := actFpf_of_conj hblock hσ3 (actEq_conj_bsw F hH h e hyL1 hy hσ)
    (not_actEq_one F hH h e hyL1 hy hσ)
  have hL15 : (y : G) ∈ Subgroup.normalizer (F.V5 : Set G) :=
    (le_sup_left.trans h.L₁T_normalizes_Vp) hyL1
  set x := psiH h (xQ e) with hx
  have hxv : ∀ (s : ↥(UT F.V1 F.V5 H)) (v : G) (hvN : v ∈ N1 F.V1),
      (s : SecQuot (N1 F.V1) F.V1) = secMk (N1 F.V1) F.V1 ⟨v, hvN⟩ →
      ((x s : ↥(UT F.V1 F.V5 H)) : SecQuot (N1 F.V1) F.V1) =
        secMk (N1 F.V1) F.V1 ⟨(y : G) * v * (y : G)⁻¹, (N1 F.V1).mul_mem ((N1 F.V1).mul_mem
          (le_N1 h y.2) hvN) ((N1 F.V1).inv_mem (le_N1 h y.2))⟩ := by
    intro s v hvN hs
    rw [hx, ← hy, psiH_mk, thetaH_apply, hs]
    exact thetaH_apply_secMk h y hvN
  obtain ⟨S5, hS5def⟩ : ∃ S : Subgroup ↥(UT F.V1 F.V5 H),
      S = (tildeOf F.V1 F.V5).subgroupOf (UT F.V1 F.V5 H) := ⟨_, rfl⟩
  have hmemS5 : ∀ s, s ∈ S5 ↔ (s : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5 := fun s => by
    rw [hS5def, Subgroup.mem_subgroupOf]
  have hxS5 : ∀ s ∈ S5, x s ∈ S5 := by
    intro s hs
    obtain ⟨⟨v, hvN⟩, hv5, hvs⟩ := mem_secImg.1 ((hmemS5 s).1 hs)
    rw [hmemS5, hxv s v hvN hvs.symm]
    exact secMk_mem_secImg ((Subgroup.mem_normalizer_iff.1 hL15 v).1 hv5)
  have hyfix : ∀ s ∈ S5, x s = s → s = 1 := by
    intro s hs hxs
    obtain ⟨⟨v, hvN⟩, hv5, hvs⟩ := mem_secImg.1 ((hmemS5 s).1 hs)
    have h1 := congrArg Subtype.val hxs
    rw [hxv s v hvN hvs.symm, ← hvs, secMk_eq_secMk_iff] at h1
    apply Subtype.ext
    rw [← hvs]
    exact secMk_eq_one_iff.2 (mem_V1_of_actFpf F hyV hσ hfpf hv5 h1)
  have hS5 : ∀ u : ↥(UT F.V1 F.V5 H), (u : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5 →
      u ∈ cm x := by
    let f : ↥S5 →* ↥S5 := ((cmHom x).comp S5.subtype).codRestrict S5 fun s =>
      S5.mul_mem (hxS5 s s.2) (S5.inv_mem s.2)
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro s hs
      rw [MonoidHom.mem_ker] at hs
      have h1 : x (s : ↥(UT F.V1 F.V5 H)) * (s : ↥(UT F.V1 F.V5 H))⁻¹ = 1 :=
        congrArg Subtype.val hs
      rw [mul_inv_eq_one] at h1
      exact Subgroup.mem_bot.2 (Subtype.ext (hyfix s s.2 h1))
    intro u hu
    obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.1 hf) ⟨u, (hmemS5 u).2 hu⟩
    exact ⟨s, Subgroup.mem_top _, congrArg Subtype.val hs⟩
  have hcm : cm x = ⊤ := by
    refine eq_top_of_le h (cm x) hS5 fun z => cm_invariant_of_conj ?_
    have := psiH_conj h e (QuotientGroup.mk z)
    rwa [psiH_mk] at this
  have hcard := card_cm_mul_card_fx x
  rw [hcm, Subgroup.card_top] at hcard
  have h1 : Nat.card (fx x) = 1 :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard.trans (mul_one _).symm)
  have : w ∈ fx x := mem_fx.2 hw
  rw [Subgroup.card_eq_one.1 h1] at this
  exact Subgroup.mem_bot.1 this

end Lift

end CFSG.Quasithin.H13.F126
