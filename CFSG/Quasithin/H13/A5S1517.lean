module

public import CFSG.Quasithin.H13.A5Inputs
public import CFSG.Quasithin.EmptyFaithful.S1422Quot
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.Quasithin.H13.A5F91

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Blueprint
open scoped MatrixGroups

structure Data13515 {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
    (H I : Subgroup G) : Prop where
  H_eq : H = S.G1
  M_eq : Subgroup.normalizer (L : Set G) = L ⊔ T
  V_eq : pCoreOf 2 (L ⊔ T) = V
  center_QH : centerOf (pCoreOf 2 H) = S.V1
  I_le : I ≤ H
  I_normal : H ≤ Subgroup.normalizer (I : Set G)
  I_S3 : Nonempty (oTwoQuot ↥I ≃* Equiv.Perm (Fin 3))
  card_O2_I : Nat.card (pCoreOf 2 I) = 32
  H_eq_gen : H = S.L1 ⊔ I ⊔ T


theorem InK4_of_InD : ∀ σ : Equiv.Perm (Fin 5), InD σ → σ.sign = 1 → InK4 σ := by
  decide +kernel

theorem InK4_conj : ∀ σ τ : Equiv.Perm (Fin 5), σ 4 = 4 → σ.sign = 1 → InK4 τ →
    InK4 (σ * τ * σ⁻¹) := by
  decide +kernel

theorem fix4_of_normalizes_K4 : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 →
    (∀ τ, InK4 τ → InK4 (σ * τ * σ⁻¹)) → σ 4 = 4 := by
  decide +kernel


theorem eq_two_of_isL2Quot_card_sixty {f : ℕ} (hf : 1 ≤ f) {X : Type*} [Group X]
    (h : IsL2Quot f X) (hX : Nat.card X = 60) : f = 2 := by
  have hc := h.card hf
  rw [hX] at hc
  rcases Nat.lt_or_ge f 3 with h3 | h3
  · interval_cases f <;> simp_all
  · exfalso
    have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ 4 ^ f := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have : 8 * 63 ≤ 2 ^ f * (4 ^ f - 1) := Nat.mul_le_mul h8 (by omega)
    omega

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem card_oTwoQuot_L : Nat.card (oTwoQuot ↥L) = 60 := by
  obtain ⟨φ, hφ, hker⟩ := S.a5
  have e : oTwoQuot ↥L ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  rw [Nat.card_congr e.toEquiv]
  exact card_A5

theorem isL2Quot_two_L : IsL2Quot 2 (oTwoQuot ↥L) := by
  obtain ⟨φ, hφ, hker⟩ := S.a5
  have e : oTwoQuot ↥L ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have hSL : Nat.card SL(2, GaloisField 2 2) = 60 := by
    rw [card_sl_two_gf2 2 (by norm_num)]; norm_num
  obtain ⟨f⟩ := sl2_four_equiv_alt5 (GaloisField 2 2) hK hSL
  exact ⟨e.trans (f.symm.trans (pslTwoGf2EquivSl 2).symm)⟩

theorem rho_eq_one_iff (g : ↥(Subgroup.normalizer (V : Set G))) :
    S.frame.ρ g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := (S.conj_eq_iff g ⟨v, hv⟩).2 (by rw [h, map_one, MulAut.one_apply])
    calc v * g = g * v * (g : G)⁻¹ * g := by rw [this]
      _ = g * v := by group
  · intro h
    apply pact_injective
    refine MulEquiv.ext fun x => ?_
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
    have := (S.conj_eq_iff g v).1 (by
      have := Subgroup.mem_centralizer_iff.mp h v v.2
      calc (g : G) * v * (g : G)⁻¹ = v * g * (g : G)⁻¹ := by rw [this]
        _ = v := by group)
    rw [map_one, MulAut.one_apply]
    exact this


theorem sylow_of_le {X : Subgroup G} (hTX : T ≤ X) : IsSylowTwoOf T X :=
  isSylowTwoOf_of_le S.h13.sylow hTX

theorem sylow_inf_L : IsSylowTwoOf (T ⊓ L) L :=
  A4.isSylowTwoOf_inf_normal S.sylow_LT le_sup_left
    (sup_le Subgroup.le_normalizer S.T_le_NL)

theorem K4_TL (σ : Equiv.Perm (Fin 5)) (hσ : InK4 σ) :
    ∃ t : ↥(Subgroup.normalizer (V : Set G)), (t : G) ∈ T ⊓ L ∧ S.frame.ρ t = σ := by
  obtain ⟨t, htT, hρt⟩ := S.frame.K4_T σ hσ
  have hsign : σ.sign = 1 := by
    rcases hσ with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨l, hlL, hρl⟩ := (S.frame.image_L σ).2 hsign
  have hker : S.frame.ρ (l * t⁻¹) = 1 := by rw [map_mul, map_inv, hρl, hρt, mul_inv_cancel]
  have hc := (S.rho_eq_one_iff _).1 hker
  have hlt : (l : G) * (t : G)⁻¹ ∈ pCoreOf 2 (L ⊔ T) := by
    rw [← S.cLT]
    exact ⟨Subgroup.mul_mem _ (le_sup_left (a := L) hlL)
      (Subgroup.inv_mem _ (le_sup_right (a := L) htT)), hc⟩
  have hlT : (l : G) ∈ T := by
    have : (l : G) = ((l : G) * (t : G)⁻¹) * t := by group
    rw [this]
    exact T.mul_mem (S.pCoreOf_LT_le_T hlt) htT
  exact ⟨l, ⟨hlT, hlL⟩, hρl⟩

theorem InK4_of_mem_TL (t : ↥(Subgroup.normalizer (V : Set G))) (ht : (t : G) ∈ T ⊓ L) :
    InK4 (S.frame.ρ t) :=
  InK4_of_InD _ (S.frame.T_D t ht.1) ((S.frame.image_L _).1 ⟨t, ht.2, rfl⟩)

theorem mem_T_of_InK4 (x : ↥(Subgroup.normalizer (V : Set G))) (hxL : (x : G) ∈ L ⊔ T)
    (hx : InK4 (S.frame.ρ x)) : (x : G) ∈ T := by
  obtain ⟨t, htT, hρt⟩ := S.frame.K4_T _ hx
  have hker : S.frame.ρ (t⁻¹ * x) = 1 := by rw [map_mul, map_inv, hρt, inv_mul_cancel]
  have hc := (S.rho_eq_one_iff _).1 hker
  have hmem : (t : G)⁻¹ * x ∈ pCoreOf 2 (L ⊔ T) := by
    rw [← S.cLT]
    exact ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (le_sup_right (a := L) htT)) hxL, hc⟩
  have : (x : G) = t * ((t : G)⁻¹ * x) := by group
  rw [this]
  exact T.mul_mem htT (S.pCoreOf_LT_le_T hmem)

theorem L1_le_borel_L : S.L1 ≤ borelOf L T := by
  have key : ∀ x y : G, x ∈ S.L1 → y ∈ T ⊓ L → x * y * x⁻¹ ∈ T ⊓ L := by
    intro x y hxL1 hy
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L hxL1)
    have hρx4 : S.frame.ρ ⟨x, hxN⟩ 4 = 4 :=
      S.rho_four_of_conj_z _ (S.conj_z_of_normalizes (S.L1_le_NV1 hxL1))
    have hρxs : (S.frame.ρ ⟨x, hxN⟩).sign = 1 :=
      (S.frame.image_L _).1 ⟨_, S.L1_le_L hxL1, rfl⟩
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le hy.1
    have hxyL : x * y * x⁻¹ ∈ L := L.mul_mem (L.mul_mem (S.L1_le_L hxL1) hy.2)
      (L.inv_mem (S.L1_le_L hxL1))
    have hxyN : x * y * x⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hyN) (Subgroup.inv_mem _ hxN)
    refine ⟨S.mem_T_of_InK4 ⟨_, hxyN⟩ (le_sup_left (a := L) hxyL) ?_, hxyL⟩
    have : (⟨x * y * x⁻¹, hxyN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨x, hxN⟩ * ⟨y, hyN⟩ * (⟨x, hxN⟩)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    exact InK4_conj _ _ hρx4 hρxs (S.InK4_of_mem_TL ⟨y, hyN⟩ hy)
  intro x hx
  refine ⟨S.L1_le_L hx, ?_⟩
  show x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x y hx
  · intro hy
    have := key _ _ (S.L1.inv_mem hx) hy
    simpa [mul_assoc] using this

theorem borel_L_le : borelOf L T ≤ S.L1 ⊔ T := by
  have h1 : borelOf L T ≤ L ⊓ Subgroup.normalizer (S.V1 : Set G) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hx.1
    have hsign : (S.frame.ρ ⟨x, hxN⟩).sign = 1 := (S.frame.image_L _).1 ⟨_, hx.1, rfl⟩
    have h4 : S.frame.ρ ⟨x, hxN⟩ 4 = 4 := by
      refine fix4_of_normalizes_K4 _ hsign fun τ hτ => ?_
      obtain ⟨t, htTL, rfl⟩ := S.K4_TL τ hτ
      have hxt : x * t * x⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp hx.2 t).mp htTL
      have hxtN : x * t * x⁻¹ ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le hxt.1
      have := S.InK4_of_mem_TL ⟨_, hxtN⟩ hxt
      have e : (⟨x * t * x⁻¹, hxtN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨x, hxN⟩ * t * (⟨x, hxN⟩)⁻¹ := rfl
      rwa [e, map_mul, map_mul, map_inv] at this
    have hxz : x * S.z * x⁻¹ = S.z := by
      rw [S.conj_eq_iff ⟨x, hxN⟩ ⟨S.z, S.z_mem_V⟩, S.psi_z]
      exact pact_W4 h4
    show x ∈ Subgroup.normalizer (S.V1 : Set G)
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc x * S.z = x * S.z * x⁻¹ * x := by group
      _ = S.z * x := by rw [hxz]
  have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ Subgroup.normalizer (S.V1 : Set G)) := by
    refine F7.isSylowTwoOf_mono_right S.sylow_inf_L ?_ inf_le_left
    exact le_inf inf_le_right (inf_le_left.trans S.T_le_NV1)
  have h2 := le_oTwoRes_sup_of_isSylowTwoOf hsyl
  exact h1.trans (h2.trans (sup_le_sup le_rfl inf_le_left))


section Data

variable {H I : Subgroup G} (hH : H ∈ S.Hz) (D : Data13515 S H I)
include hH D

omit hH in
theorem card_oTwoQuot_I : Nat.card (oTwoQuot ↥I) = 6 := by
  obtain ⟨e⟩ := D.I_S3
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

omit hH in
theorem card_I : Nat.card I = 192 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥I)
  have h2 : Nat.card (CFSG.Open.pCore 2 ↥I) = 32 := by
    rw [← D.card_O2_I]
    exact (Subgroup.card_map_of_injective I.subtype_injective).symm
  have h3 : Nat.card (↥I ⧸ CFSG.Open.pCore 2 ↥I) = 6 := S.card_oTwoQuot_I D
  rw [h1, h2, h3]

omit D in
theorem T_le_H : T ≤ H := le_sup_right.trans hH.1.1

theorem sylow_inf_I : IsSylowTwoOf (T ⊓ I) I :=
  A4.isSylowTwoOf_inf_normal (S.sylow_of_le (S.T_le_H hH)) D.I_le D.I_normal

theorem card_inf_I : Nat.card ↥(T ⊓ I) = 64 := by
  obtain ⟨-, hP, hodd⟩ := S.sylow_inf_I hH D
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  have hmul := Subgroup.card_mul_index ((T ⊓ I).subgroupOf I)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, S.card_I D, hk]
    at hmul
  rw [hk]
  have hk7 : k ≤ 7 := by
    by_contra hk7
    have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases Nat.eq_zero_or_pos ((T ⊓ I).subgroupOf I).index with h0 | hpos
    · rw [h0] at hmul; omega
    · nlinarith
  interval_cases k <;> omega

theorem borel_I_le_T : borelOf I T ≤ T := by
  set P := T ⊓ I with hP
  have hPB : P ≤ borelOf I T := le_inf inf_le_right (Subgroup.le_normalizer)
  have hBI : borelOf I T ≤ I := inf_le_left
  have hidx : P.relIndex I = 3 := by
    have h := Subgroup.relIndex_mul_index (H := P) (K := I) inf_le_right
    have hc := Subgroup.card_mul_index (P.subgroupOf I)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
      S.card_inf_I hH D, S.card_I D] at hc
    rw [Subgroup.relIndex]
    omega
  have hmul := Subgroup.relIndex_mul_relIndex P (borelOf I T) I hPB hBI
  rw [hidx] at hmul
  have hcases : (borelOf I T).relIndex I = 1 ∨ (borelOf I T).relIndex I = 3 := by
    have hd : (borelOf I T).relIndex I ∣ 3 := Dvd.intro_left _ hmul
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hd with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hcases with h | h
  ·
    exfalso
    have hIB : I ≤ borelOf I T := Subgroup.relIndex_eq_one.1 h
    have hPO : P ≤ pCoreOf 2 I :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (hIB.trans inf_le_right) (S.sylow_inf_I hH D).2.1
    have := Subgroup.card_le_of_le hPO
    rw [S.card_inf_I hH D, D.card_O2_I] at this
    omega
  · have h1 : P.relIndex (borelOf I T) = 1 := by
      rw [h] at hmul
      omega
    exact (Subgroup.relIndex_eq_one.1 h1).trans inf_le_left

omit D in
theorem borel_L_le_H : borelOf L T ≤ H := S.borel_L_le.trans hH.1.1

theorem center_T_le_V1 : centerOf T ≤ S.V1 := by
  intro x hx
  have hQT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le (S.sylow_of_le (S.T_le_H hH))
  have hchar : CharTwo H := S.charTwo_of_inH ⟨S.T_le_H hH, hH.1.2⟩
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.centralizer_le (s := (pCoreOf 2 H : Set G)) (t := (T : Set G)) hQT hx.2
  have hxQ : x ∈ pCoreOf 2 H := hchar ⟨S.T_le_H hH hx.1, hxC⟩
  rw [← D.center_QH]
  exact ⟨hxQ, hxC⟩

end Data


theorem pRank_le_two_of_isTwoLocal {X : Subgroup G} (hX : IsTwoLocal X) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p X ≤ 2 := by
  have hbdd : BddAbove {k | ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsTwoLocal H ∧
      CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨q, K, hq, -, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq.one_lt K
    have h1 : CFSG.Open.pRank q K < q ^ CFSG.Open.pRank q K := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    omega
  have h := S.h13.qtke.2.2
  exact (le_csSup hbdd ⟨p, X, hp, hp2, hX, rfl⟩).trans h

theorem isQuasithinSub (X : Subgroup G) : IsQuasithinSub X := by
  intro p hp hp2 R _ hRne hR2
  have hloc : IsTwoLocal (Subgroup.normalizer (R : Set G)) := ⟨R, hRne, hR2, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
    (S.pRank_le_two_of_isTwoLocal hloc hp hp2)

section Data

variable {H I : Subgroup G} (hH : H ∈ S.Hz) (D : Data13515 S H I)
include hH D

omit hH in
theorem charTwo_of_le_H {X : Subgroup G} (hTX : T ≤ X) (hXH : X ≤ H) : CharTwo X := by
  refine S.charTwo_of_inH ⟨hTX, fun h => ?_⟩
  have hV1 : S.V1 ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((S.V1_le_V.trans S.V_le_T).trans hTX)
      (hXH.trans (D.H_eq ▸ S.G1_eq_normalizer ▸ le_rfl)) ((S.isPGroup_V).to_le S.V1_le_V)
  rw [h, le_bot_iff] at hV1
  have := S.card_V1
  rw [hV1] at this
  simp at this

theorem hyp111 : Hyp111 I L T where
  h1 :=
    { finite := inferInstance
      pgroup := S.isPGroup_T
      normalizes := (S.T_le_H hH).trans D.I_normal
      sylow := S.sylow_inf_I hH D
      listed := Or.inl ⟨1, le_rfl, ⟨D.I_S3.some.trans permThreeEquivPSL⟩⟩
      borel_le := (S.borel_L_le_H hH).trans D.I_normal
      charTwo := S.charTwo_of_le_H D (le_sup_right.trans le_sup_left)
        (sup_le (sup_le D.I_le (S.T_le_H hH)) (S.borel_L_le_H hH)) }
  h2 :=
    { finite := inferInstance
      pgroup := S.isPGroup_T
      normalizes := S.T_le_NL
      sylow := S.sylow_inf_L
      listed := Or.inl ⟨2, by norm_num, S.isL2Quot_two_L⟩
      borel_le := (S.borel_I_le_T hH D).trans S.T_le_NL
      charTwo := by
        have e : L ⊔ T ⊔ borelOf I T = L ⊔ T := sup_eq_left.2 ((S.borel_I_le_T hH D).trans
          le_sup_right)
        rw [e]
        exact S.charTwo_of_inH ⟨le_sup_right, fun h => by
          have := S.V_le_pCoreOf_LT
          rw [h, le_bot_iff] at this
          have hc := S.card_V
          rw [this] at hc
          simp at hc⟩ }
  o2 := by
    refine S.o2_eq_bot_of_not_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right) ?_
    intro hle
    apply hH.2.2
    rw [D.H_eq_gen]
    exact sup_le (sup_le (S.L1_le_L.trans (le_sup_right.trans (le_sup_left.trans hle)))
      (le_sup_left.trans (le_sup_left.trans hle))) (le_sup_right.trans hle)

theorem sup_bigB : I ⊔ bigB I L T = H ∧ L ⊔ bigB I L T = L ⊔ T := by
  have hBI := S.borel_I_le_T hH D
  have hBL := S.borel_L_le_H hH
  constructor
  · apply le_antisymm
    · exact sup_le D.I_le (sup_le (sup_le (hBI.trans (S.T_le_H hH)) hBL) (S.T_le_H hH))
    · rw [D.H_eq_gen]
      refine sup_le (sup_le ?_ le_sup_left) (le_sup_right.trans le_sup_right)
      exact S.L1_le_borel_L.trans ((le_sup_right.trans le_sup_left).trans le_sup_right)
  · apply le_antisymm
    · exact sup_le le_sup_left (sup_le (sup_le (hBI.trans le_sup_right) (inf_le_left.trans
        le_sup_left)) le_sup_right)
    · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)

omit hH D in
theorem not_center_T_le_centralizer_L :
    ¬ centerOf T ≤ Subgroup.centralizer (L : Set G) := by
  intro h
  have hz : S.z ∈ centerOf T := ⟨S.V_le_T S.z_mem_V, Subgroup.mem_centralizer_iff.2 fun t ht =>
    by
      have := S.conj_z_of_mem_T ht
      calc t * S.z = t * S.z * t⁻¹ * t := by group
        _ = S.z * t := by rw [this]⟩
  obtain ⟨σ, hσs, hσ4⟩ : ∃ σ : Equiv.Perm (Fin 5), σ.sign = 1 ∧ σ 4 ≠ 4 :=
    ⟨Equiv.swap 0 4 * Equiv.swap 1 2, by decide, by decide⟩
  obtain ⟨l, hlL, hlσ⟩ := (S.frame.image_L σ).2 hσs
  apply hσ4
  have hlz : (l : G) * S.z * (l : G)⁻¹ = S.z := by
    have := Subgroup.mem_centralizer_iff.mp (h hz) l hlL
    calc (l : G) * S.z * (l : G)⁻¹ = S.z * l * (l : G)⁻¹ := by rw [this]
      _ = S.z := by group
  rw [← hlσ]
  exact S.rho_four_of_conj_z _ hlz

end Data


section Ident

variable {H I : Subgroup G} (hH : H ∈ S.Hz) (D : Data13515 S H I)
include hH D

theorem amalgam_U42 (hF112 : F112LegacyPrintedError) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H (L ⊔ T)) (IsLieOverTwo .PSU 4 1) ∨
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups H (L ⊔ T)) := by
  have hnorm : (T.subgroupOf (T ⊔ borelOf I T)).Normal := by
    rw [sup_eq_left.2 (S.borel_I_le_T hH D), Subgroup.subgroupOf_self]
    infer_instance
  obtain ⟨L1', L2', hswap, hZ, hlist, -⟩ :=
    hF112 G I L T (S.hyp111 hH D) (S.isQuasithinSub _) (Or.inl hnorm)
  have hZI : centerOf T ≤ Subgroup.centralizer (I : Set G) := by
    intro x hx
    have hxV1 := S.center_T_le_V1 hH D hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyG1 : y ∈ S.G1 := D.H_eq ▸ D.I_le hy
    rw [← S.centralizer_V1] at hyG1
    exact (Subgroup.mem_centralizer_iff.mp hyG1 x hxV1).symm
  obtain ⟨h1', h2'⟩ : L1' = I ∧ L2' = L := by
    rcases hswap with h | ⟨h1, -⟩
    · exact h
    · exfalso
      rw [h1] at hZ
      exact S.not_center_T_le_centralizer_L (hZ (Or.inl hZI))
  rw [h1', h2'] at hlist
  have hcI := S.card_oTwoQuot_I D
  have hcL := S.card_oTwoQuot_L
  have hcI' : Nat.card (OTwoQuot I) = 6 := hcI
  have hamal : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (I ⊔ bigB I L T)
      (L ⊔ bigB I L T)) (IsLieOverTwo .PSU 4 1) ∨
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups (I ⊔ bigB I L T) (L ⊔ bigB I L T)) := by
    unfold F112ListBare at hlist
    rcases hlist with ⟨f, hf, -, h⟩ | ⟨f, hf, -, h⟩ | ⟨f, hf, -, hI, hL, -⟩ |
        ⟨f, hf, -, hI, -⟩ | ⟨a, -, -, -, hL, -⟩ | ⟨f, hf, ham, hI, -⟩ | ⟨-, -, -, hL, -⟩ |
        ⟨-, -, hL, -⟩ | ⟨-, -, -, hL, -⟩ | ⟨-, hI, -⟩ | ⟨-, -, -, ⟨eL⟩, -⟩ | ⟨-, -, -, hL, -⟩ |
        ⟨-, -, -, hL, -⟩
    · exfalso
      rcases h with ⟨hf2, -, hlin, -⟩ | ⟨-, ⟨e⟩, -⟩
      · have := isLin2Type_eq_one_of_card_six hf hlin hcI'
        omega
      · have h1 := Nat.card_congr e.toEquiv
        rw [S.card_I D, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
        exact absurd h1 (by decide)
    · exfalso
      rcases h with ⟨hf2, -, hlin, -⟩ | ⟨-, ⟨e⟩, -⟩
      · have := isLin2Type_eq_one_of_card_six hf hlin hcI'
        omega
      · have h1 := Nat.card_congr e.toEquiv
        rw [Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
          Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h1
        have h2 : Nat.card I ≤ Nat.card ↥(I ⊔ T) :=
          Subgroup.card_le_of_le le_sup_left
        rw [S.card_I D, h1] at h2
        exact absurd h2 (by decide)
    · exfalso
      have h1 := hI.eq_one_of_card_eq_six hf hcI
      subst h1
      have := hL.card le_rfl
      omega
    · exfalso
      have h1 := hI.eq_one_of_card_eq_six (by omega) hcI
      omega
    · exfalso
      have h1 := eq_two_of_isL2Quot_card_sixty (by omega) hL hcL
      omega
    · have h1 := hI.eq_one_of_card_eq_six hf hcI
      subst h1
      exact ham
    · exfalso
      have h1 := eq_two_of_isL2Quot_card_sixty (by norm_num) hL hcL
      omega
    · exfalso
      have := hL.card le_rfl
      omega
    · exfalso
      have := hL.card le_rfl
      omega
    · exfalso
      have h1 := hI.eq_one_of_card_eq_six (by norm_num) hcI
      omega
    · exfalso
      have h1 := Nat.card_congr eL.toEquiv
      rw [hcL, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
      exact absurd h1 (by decide)
    · exfalso
      have := hL.card le_rfl
      omega
    · exfalso
      have := hL.card le_rfl
      omega
  obtain ⟨h1, h2⟩ := S.sup_bigB hH D
  rwa [h1, h2] at hamal

theorem prop_13_5_17 (hF112 : F112LegacyPrintedError) (hF431 : StmtF431U42) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 := by
  have hamal := S.amalgam_U42 hH D hF112
  have hHM : ¬ H ⊔ (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) := fun h =>
    hH.2.2 (le_sup_left.trans h)
  have ho2 : pCoreOf 2 (H ⊔ (L ⊔ T)) = ⊥ := S.o2_eq_bot_of_not_le le_sup_right hHM
  have hzH : S.z ∈ H := by
    rw [D.H_eq]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzc : S.z ∈ centerOf (H ⊓ (L ⊔ T)) := by
    refine ⟨⟨hzH, le_sup_right (a := L) (S.V_le_T S.z_mem_V)⟩, ?_⟩
    show S.z ∈ Subgroup.centralizer ((H ⊓ (L ⊔ T) : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxG1 : x ∈ S.G1 := D.H_eq ▸ hx.1
    exact Subgroup.mem_centralizer_singleton_iff.mp hxG1
  have hCz : Subgroup.centralizer ({S.z} : Set G) ≤ H := by rw [D.H_eq]; rfl
  have hN1 : Subgroup.normalizer (centerOf (pCoreOf 2 H) : Set G) = H := by
    rw [D.center_QH, ← S.G1_eq_normalizer, D.H_eq]
  have hN2 : Subgroup.normalizer (centerOf (pCoreOf 2 (L ⊔ T)) : Set G) = L ⊔ T := by
    rw [D.V_eq]
    have hcV : centerOf V = V := le_antisymm inf_le_left (le_inf le_rfl
      (fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw =>
        congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)))
    rw [hcV]
    exact le_antisymm (S.NV_le_M.trans D.M_eq.le) S.reduced.2.1
  exact hF431 G S.h13.simple S.h13.nonabelian H (L ⊔ T) S.z hamal ho2 S.z_sq S.z_ne_one hzc hCz
    hN1 hN2

theorem amalgam_U42_corrected (hF112 : F112Statement) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H (L ⊔ T)) (IsLieOverTwo .PSU 4 1) ∨
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups H (L ⊔ T)) := by
  have hnorm : (T.subgroupOf (T ⊔ borelOf I T)).Normal := by
    rw [sup_eq_left.2 (S.borel_I_le_T hH D), Subgroup.subgroupOf_self]
    infer_instance
  obtain ⟨L1', L2', hswap, hZ, hlist, -⟩ :=
    hF112 G I L T ⟨S.hyp111 hH D, S.isQuasithinSub _, Or.inl hnorm⟩
  have hZI : centerOf T ≤ Subgroup.centralizer (I : Set G) := by
    intro x hx
    have hxV1 := S.center_T_le_V1 hH D hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyG1 : y ∈ S.G1 := D.H_eq ▸ D.I_le hy
    rw [← S.centralizer_V1] at hyG1
    exact (Subgroup.mem_centralizer_iff.mp hyG1 x hxV1).symm
  obtain ⟨h1', h2'⟩ : L1' = I ∧ L2' = L := by
    rcases hswap with h | ⟨h1, -⟩
    · exact h
    · exfalso
      rw [h1] at hZ
      exact S.not_center_T_le_centralizer_L (hZ (Or.inl hZI))
  rw [h1', h2'] at hlist
  have hcI := S.card_oTwoQuot_I D
  have hcL := S.card_oTwoQuot_L
  have hcI' : Nat.card (OTwoQuot I) = 6 := hcI
  have hamal : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (I ⊔ bigB I L T)
      (L ⊔ bigB I L T)) (IsLieOverTwo .PSU 4 1) ∨
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups (I ⊔ bigB I L T) (L ⊔ bigB I L T)) := by
    unfold F112List at hlist
    rcases hlist with ⟨f, hf, -, h⟩ | ⟨f, hf, -, h⟩ | ⟨f, hf, -, hI, hL, -⟩ |
        ⟨f, hf, -, hI, -⟩ | ⟨a, -, -, -, hL, -⟩ | ⟨f, hf, ham, hI, -⟩ | ⟨-, -, -, hL, -⟩ |
        ⟨-, -, hL, -⟩ | ⟨-, -, -, hL, -⟩ | ⟨-, hI, -⟩ | ⟨-, -, -, ⟨eL⟩, -⟩ | ⟨-, -, -, hL, -⟩ |
        ⟨-, -, -, hL, -⟩
    · exfalso
      rcases h with ⟨hf2, -, hlin, -⟩ | ⟨-, ⟨e⟩, -⟩
      · have := isLin2Type_eq_one_of_card_six hf hlin hcI'
        omega
      · have h1 := Nat.card_congr e.toEquiv
        rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h1
        have h2 : Nat.card I ≤ Nat.card ↥(I ⊔ T) :=
          Subgroup.card_le_of_le le_sup_left
        rw [S.card_I D, h1] at h2
        exact absurd h2 (by decide)
    · exfalso
      rcases h with ⟨hf2, -, hlin, -⟩ | ⟨-, ⟨e⟩, -⟩
      · have := isLin2Type_eq_one_of_card_six hf hlin hcI'
        omega
      · have h1 := Nat.card_congr e.toEquiv
        rw [Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
          Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h1
        have h2 : Nat.card I ≤ Nat.card ↥(I ⊔ T) :=
          Subgroup.card_le_of_le le_sup_left
        rw [S.card_I D, h1] at h2
        exact absurd h2 (by decide)
    · exfalso
      have h1 := hI.eq_one_of_card_eq_six hf hcI
      subst h1
      have := hL.card le_rfl
      omega
    · exfalso
      have h1 := hI.eq_one_of_card_eq_six (by omega) hcI
      omega
    · exfalso
      have h1 := eq_two_of_isL2Quot_card_sixty (by omega) hL hcL
      omega
    · have h1 := hI.eq_one_of_card_eq_six hf hcI
      subst h1
      exact ham
    · exfalso
      have h1 := eq_two_of_isL2Quot_card_sixty (by norm_num) hL hcL
      omega
    · exfalso
      have := hL.card le_rfl
      omega
    · exfalso
      have := hL.card le_rfl
      omega
    · exfalso
      have h1 := hI.eq_one_of_card_eq_six (by norm_num) hcI
      omega
    · exfalso
      have h1 := Nat.card_congr eL.toEquiv
      rw [hcL, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
      exact absurd h1 (by decide)
    · exfalso
      have := hL.card le_rfl
      omega
    · exfalso
      have := hL.card le_rfl
      omega
  obtain ⟨h1, h2⟩ := S.sup_bigB hH D
  rwa [h1, h2] at hamal

theorem prop_13_5_17_corrected (hF112 : F112Statement) (hF431 : StmtF431U42) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 := by
  have hamal := S.amalgam_U42_corrected hH D hF112
  have hHM : ¬ H ⊔ (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) := fun h =>
    hH.2.2 (le_sup_left.trans h)
  have ho2 : pCoreOf 2 (H ⊔ (L ⊔ T)) = ⊥ := S.o2_eq_bot_of_not_le le_sup_right hHM
  have hzH : S.z ∈ H := by
    rw [D.H_eq]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzc : S.z ∈ centerOf (H ⊓ (L ⊔ T)) := by
    refine ⟨⟨hzH, le_sup_right (a := L) (S.V_le_T S.z_mem_V)⟩, ?_⟩
    show S.z ∈ Subgroup.centralizer ((H ⊓ (L ⊔ T) : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxG1 : x ∈ S.G1 := D.H_eq ▸ hx.1
    exact Subgroup.mem_centralizer_singleton_iff.mp hxG1
  have hCz : Subgroup.centralizer ({S.z} : Set G) ≤ H := by rw [D.H_eq]; rfl
  have hN1 : Subgroup.normalizer (centerOf (pCoreOf 2 H) : Set G) = H := by
    rw [D.center_QH, ← S.G1_eq_normalizer, D.H_eq]
  have hN2 : Subgroup.normalizer (centerOf (pCoreOf 2 (L ⊔ T)) : Set G) = L ⊔ T := by
    rw [D.V_eq]
    have hcV : centerOf V = V := le_antisymm inf_le_left (le_inf le_rfl
      (fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw =>
        congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)))
    rw [hcV]
    exact le_antisymm (S.NV_le_M.trans D.M_eq.le) S.reduced.2.1
  exact hF431 G S.h13.simple S.h13.nonabelian H (L ⊔ T) S.z hamal ho2 S.z_sq S.z_ne_one hzc hCz
    hN1 hN2

end Ident

end Setting

end CFSG.Quasithin.H13.A5
