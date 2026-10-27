module

public import CFSG.Quasithin.EmptyFaithful.S152Y14
public import CFSG.Quasithin.EmptyFaithful.S152UGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizes_of_commutator_le_inf152 {A B : Subgroup G} (h : ⁅A, B⁆ ≤ A ⊓ B) :
    A ≤ Subgroup.normalizer (B : Set G) ∧ B ≤ Subgroup.normalizer (A : Set G) := by
  have key : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ B := (h (Subgroup.commutator_mem_commutator ha hb)).2
    have : a * b * a⁻¹ = ⁅a, b⁆ * b := by rw [commutatorElement_def]; group
    rw [this]
    exact B.mul_mem h1 hb
  have key' : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := by
    intro b hb a ha
    have h1 : ⁅a, b⁆ ∈ A := (h (Subgroup.commutator_mem_commutator ha hb)).1
    have : b * a * b⁻¹ = ⁅a, b⁆⁻¹ * a := by rw [commutatorElement_def]; group
    rw [this]
    exact A.mul_mem (A.inv_mem h1) ha
  constructor
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨key a ha b, fun hb => ?_⟩
    have h1 := key a⁻¹ (A.inv_mem ha) _ hb
    have e : a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b := by group
    rwa [e] at h1
  · intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨key' b hb a, fun ha => ?_⟩
    have h1 := key' b⁻¹ (B.inv_mem hb) _ ha
    have e : b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ = a := by group
    rwa [e] at h1

omit [Finite G] in
theorem oTwoUpper_eq_bot_of_isPGroup152 {P : Subgroup G} (hP : IsPGroup 2 P) : oTwoUpper P = ⊥ := by
  rw [eq_bot_iff]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨hxP, hxo⟩ := hx
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · rw [pow_zero] at hj
    simpa using orderOf_eq_one_iff.mp hj
  · exfalso
    rw [hj, pow_succ] at hxo
    exact (Nat.not_even_iff_odd.mpr hxo) (by simp)

omit [Finite G] in
theorem sup_zpowers_eq_of_relIndex_two152 {S T : Subgroup G} (hST : S ≤ T) (h2 : S.relIndex T = 2)
    {t : G} (htT : t ∈ T) (htS : t ∉ S) : S ⊔ Subgroup.zpowers t = T := by
  have hle : S ⊔ Subgroup.zpowers t ≤ T := sup_le hST ((Subgroup.zpowers_le).mpr htT)
  rcases eq_or_eq_of_relIndex_two le_sup_left hle h2 with h | h
  · exact absurd (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) htS
  · exact h

omit [Finite G] in
theorem mul_inv_mem_of_relIndex_two152 {H₀ H : Subgroup G} (h : H₀.relIndex H = 2) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) (hx0 : x ∉ H₀) (hy0 : y ∉ H₀) : x * y⁻¹ ∈ H₀ := by
  have h2 : (H₀.subgroupOf H).index = 2 := h
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp h2
  have key : ∀ z : H, (z : G) ∉ H₀ → z * c ∈ H₀.subgroupOf H := by
    intro z hz
    rcases hc z with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd (Subgroup.mem_subgroupOf.mp h1) hz
  have h1 := key ⟨x, hx⟩ hx0
  have h2 := key ⟨y, hy⟩ hy0
  have h3 := (H₀.subgroupOf H).mul_mem h1 ((H₀.subgroupOf H).inv_mem h2)
  have e : (⟨x, hx⟩ * c) * (⟨y, hy⟩ * c)⁻¹ = (⟨x, hx⟩ * ⟨y, hy⟩⁻¹ : H) := by group
  rw [e] at h3
  exact Subgroup.mem_subgroupOf.mp h3

omit [Finite G] in
theorem sq_mem_of_relIndex_two152 {S T : Subgroup G} (h2 : S.relIndex T = 2) {t : G} (htT : t ∈ T)
    (htS : t ∉ S) : t ^ 2 ∈ S := by
  have := mul_inv_mem_of_relIndex_two152 h2 htT (T.inv_mem htT) htS
    (fun h => htS (by simpa using S.inv_mem h))
  simpa [sq] using this

omit [Finite G] in
theorem conj_mem_of_relIndex_two152 {S T : Subgroup G} (hST : S ≤ T) (h2 : S.relIndex T = 2) {τ s : G}
    (hτ : τ ∈ T) (hs : s ∈ S) : τ * s * τ⁻¹ ∈ S := by
  have hn : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h2
  have := hn.conj_mem ⟨s, hST hs⟩ (by simpa [Subgroup.mem_subgroupOf] using hs) ⟨τ, hτ⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem oTwoUpper_ne_bot_of_iso152 {H V H₁ H₂ : Subgroup G} (hP : IsHPair H V H₁ H₂) :
    oTwoUpper H₁ ≠ ⊥ := by
  obtain ⟨e⟩ := hP.iso₁
  have h3 : 3 ∣ Nat.card (imageOTwoQuot H H₁) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := imageOTwoQuot H H₁) 3 h3
  obtain ⟨y, hyH, hyH₁, hy⟩ := mem_imageOTwoQuot_iff.mp u.2
  have hu3 : orderOf (u : OTwoQuot H) = 3 := by rw [Subgroup.orderOf_coe]; exact hu
  have hdvd : 3 ∣ orderOf y := by
    rw [← hu3, ← hy]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← QuotientGroup.mk_pow]
    have : (⟨y, hyH⟩ : ↥H) ^ orderOf y = 1 := Subtype.ext (pow_orderOf_eq_one y)
    rw [this]
    rfl
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hm3 : 3 ∣ m := by
    rw [hkm] at hdvd
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right k (by decide)) hdvd)
  have hord : orderOf (y ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hkm]; exact dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hzH₁ : y ^ 2 ^ k ∈ H₁ := H₁.pow_mem hyH₁ _
  have hzO : y ^ 2 ^ k ∈ oTwoUpper H₁ := mem_oTwoUpper_of_odd hzH₁ (by rw [hord]; exact hm)
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hzO
  rw [hzO, orderOf_one] at hord
  have : 3 ≤ m := Nat.le_of_dvd (by rw [← hord]; norm_num) hm3
  omega

omit [Finite G] in
theorem le_normalizer_sup152 {A B C : Subgroup G} (hB : A ≤ Subgroup.normalizer (B : Set G))
    (hC : A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := fun _ ha =>
  Subgroup.inf_normalizer_le_normalizer_sup B C ⟨hB ha, hC ha⟩

theorem unique_of_autOn_eq152 {T Mc M : Subgroup G} (hs : Setting152 T Mc M)
    (h : S152Y.Data T Mc M) (h2 : StageLemma15202) {X : Subgroup G} (hXM : X ≤ M)
    (hX : autOn X (V154 T Mc M) = oTwoUpper (mBar0 T Mc M)) : IsUniqueM (X ⊔ T) M := by
  have hTM : T ≤ M := h.T_le
  have hsyl0 := A4.isSylowTwoOf_inf_normal (S152Y.isSylowTwoOf_Tb h) (S152Y.mBar0_le T Mc M)
    (S152Y.mBar0_normalizer T Mc M)
  set Eb : Subgroup (MulAut (V154 T Mc M)) := oTwoUpper (mBar0 T Mc M) with hEb
  set S0 : Subgroup (MulAut (V154 T Mc M)) := autOn T (V154 T Mc M) ⊓ mBar0 T Mc M with hS0
  have hM0 : mBar0 T Mc M = Eb ⊔ S0 := eq_oTwoUpper_sup_of_isSylowTwoOf hsyl0
  refine h2 G T Mc M hs (X ⊔ T) le_sup_right (sup_le hXM hTM) (Or.inl ?_)
  intro m hm
  have hmM : m ∈ M := preOn_le _ _ _ hm
  obtain ⟨-, hmN, hmb⟩ := mem_preOn.mp hm
  have hSN : S0 ≤ Subgroup.normalizer (Eb : Set (MulAut (V154 T Mc M))) :=
    inf_le_right.trans (le_normalizer_oTwoUpper _)
  have hmul : ((Eb ⊔ S0 : Subgroup (MulAut (V154 T Mc M))) : Set (MulAut (V154 T Mc M))) =
      (Eb : Set (MulAut (V154 T Mc M))) * (S0 : Set (MulAut (V154 T Mc M))) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSN
  have hmb' : conjAct (V154 T Mc M) ⟨m, hmN⟩ ∈
      (Eb : Set (MulAut (V154 T Mc M))) * (S0 : Set (MulAut (V154 T Mc M))) := by
    rw [← hmul, ← hM0]
    exact hmb
  obtain ⟨eb, heb, sb, hsb, hes⟩ := hmb'
  rw [← hX] at heb
  obtain ⟨y, hyN, hyY, hye⟩ := mem_autOn_iff_exists.mp heb
  obtain ⟨t, htN, htT, hts⟩ := mem_autOn_iff_exists.mp hsb.1
  have hytN : y * t ∈ Subgroup.normalizer (V154 T Mc M : Set G) := Subgroup.mul_mem _ hyN htN
  have hconj : conjAct (V154 T Mc M) ⟨y * t, hytN⟩ = conjAct (V154 T Mc M) ⟨m, hmN⟩ := by
    have : (⟨y * t, hytN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) = ⟨y, hyN⟩ * ⟨t, htN⟩ := rfl
    rw [this, map_mul, hye, hts]
    exact hes
  have hc : (y * t)⁻¹ * m ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
    (conjAct_eq_iff hytN hmN).mp hconj
  have hyM : y ∈ M := hXM hyY
  have hcM : (y * t)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem (M.mul_mem hyM (h.T_le htT))) hmM
  exact ⟨y * t, Subgroup.mul_mem_sup hyY htT, (y * t)⁻¹ * m, ⟨hcM, hc⟩, mul_inv_cancel_left _ _⟩

end CFSG.Quasithin
