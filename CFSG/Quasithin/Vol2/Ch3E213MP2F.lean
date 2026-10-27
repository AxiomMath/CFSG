module

public import CFSG.Quasithin.Vol2.Ch3E213MP2E
public import CFSG.Quasithin.H13.QRCPairedHigh
public import CFSG.Quasithin.Vol2.Ch3E213MP2C
public import CFSG.Quasithin.Vol2.Ch3E213MP2D

public section

namespace CFSG.Quasithin.Ch3E213M.P2

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.Blueprint

variable {A : Type*} [Group A] [Finite A] {K₁ K₂ : Subgroup A}

theorem paired_suzuki_quotient
    {a : ℕ} {k : Type} [Field k] (ha : 1 ≤ a) (hk : Nat.card k = 2 ^ (2 * a + 1))
    (θ₁ : K₁ ≃* suzukiGroup a k) (θ₂ : K₂ ≃* suzukiGroup a k)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥) (hKn : (K₁ ⊔ K₂).Normal)
    (hCK : ∀ x : A, (∀ y ∈ K₁ ⊔ K₂, x * y = y * x) → x = 1) {S : Subgroup A}
    (hSsyl : IsSylowOf 2 S ⊤) (hKS : K₁ ⊔ K₂ ⊔ S = ⊤) {s : A} (hs : s ∈ S)
    (hsK : K₁.map (MulAut.conj s).toMonoidHom = K₂) {B E : Subgroup A} (hSB : S ≤ B)
    (hBtop : B < ⊤) (hBmax : ∀ Y : Subgroup A, S ≤ Y → Y < ⊤ → Y ≤ B) [IsElementaryAbelian 2 E]
    (hEO : E ≤ inSubgroup (CFSG.pCore 2) B) (hES : E ≤ S) (hSE : S ≤ normalizer (E : Set A))
    (hE4 : 4 ≤ Nat.card E) :
    ∃ (x₁ : A) (L₁ : Subgroup A), x₁ ∈ L₁ ∧ L₁ ≤ K₁ ∧
      E ⊔ conjugate E x₁ = L₁ ⊔ (E ⊔ K₁) ⊓ K₂ ∧ IsElementaryAbelian 2 ((E ⊔ K₁) ⊓ K₂ : Subgroup A) ∧
      (E ⊔ K₁) ⊓ K₂ ≤ S ∧ IsSylowOf 2 (S ⊓ L₁) L₁ ∧ kerIn (B ⊓ L₁) L₁ = ⊥ ∧
      inSubgroup (CFSG.pCore 2) L₁ = ⊥ ∧ inSubgroup (CFSG.pCore 2) (B ⊓ L₁) = S ⊓ L₁ ∧
      ((∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ Nonempty (L₁ ≃* DihedralGroup ℓ) ∧
          Nat.card ↥((E ⊔ (E ⊔ K₁) ⊓ K₂) ⊓ L₁) = 2 ∧ Nat.card L₁ = 2 * ℓ) ∨
        ∃ b : ℕ, 1 ≤ b ∧ Nonempty (L₁ ≃* suzukiGroup b (GaloisField 2 (2 * b + 1)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite (suzukiGroup a k) := (CFSG.LieType.Ree.suzuki_simple ha hk).1
  have : IsSimpleGroup (suzukiGroup a k) := (CFSG.LieType.Ree.suzuki_simple ha hk).2.2
  have : IsSimpleGroup K₂ := θ₂.isSimpleGroup
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hd' : K₂ ⊓ K₁ = ⊥ := by rw [inf_comm, hd]
  have hKn' : (K₂ ⊔ K₁).Normal := by rwa [sup_comm]
  have hS2 : IsPGroup 2 S := hSsyl.isPGroup
  set E₁ := (E ⊔ K₂) ⊓ K₁ with hE₁
  set E₂ := (E ⊔ K₁) ⊓ K₂ with hE₂
  have h₁ : IsSylowOf 2 (S ⊓ K₁) K₁ := isSylowOf_inf_left hc hSsyl hKn
  have h₂ : IsSylowOf 2 (S ⊓ K₂) K₂ := isSylowOf_inf_left hc' hSsyl hKn'
  obtain ⟨U₁, hU₁⟩ := h₁.exists_sylow_eq_subgroupOf
  have hdSz := H13.QRC.benderData_suzuki ha hk
  obtain ⟨θ, hθU, -⟩ := H13.QRC.exists_mulEquiv_map_sylow θ₁ U₁.isPGroup' U₁.not_dvd_index
    hdSz.isPGroup hdSz.not_dvd_index
  have hD : H13.QRC.BenderData K₁ (U₁ : Subgroup K₁) (2 * a + 1) := by
    have h := hdSz.map θ.symm
    rwa [H13.QRC.map_symm_eq_of_map_eq θ hθU] at h
  have hBK₁ := borel_inf_left hc hd hKn hS2 hU₁ hD h₁ h₂ hKS hs hsK hSB hBtop hBmax
  obtain ⟨h', hh', p, hp, hp2, hh'p⟩ := exists_prime_orderOf_mem_normalizer hD (by omega)
  have hhB : (h' : A) ∈ B ⊓ K₁ := hBK₁ ▸ ⟨h', hh', rfl⟩
  have hEK : E ≤ K₁ ⊔ K₂ := hEO.trans (pCore_le_sup ha hk θ₁ θ₂ hc hd hKn hCK hhB.1 hhB.2 hp
    hp2 (by rw [Subgroup.orderOf_coe, hh'p]))
  have hEU : E ≤ S ⊓ K₁ ⊔ S ⊓ K₂ :=
    (le_inf hES hEK).trans (inf_sup_eq_of_isSylowOf hc hd hS2 h₁ h₂).le
  have hE₁U : E₁ ≤ S ⊓ K₁ := H13.QRC.proj_le hc hd hEU inf_le_right inf_le_right
  have hE₂U : E₂ ≤ S ⊓ K₂ :=
    H13.QRC.proj_le hc' hd' (sup_comm (S ⊓ K₁) _ ▸ hEU) inf_le_right inf_le_right
  have hEE : E ≤ E₁ ⊔ E₂ := H13.QRC.le_sup_projections hc hEK
  have : IsElementaryAbelian 2 E₁ := isElementaryAbelian_proj hc hd hEK
  have hel₂ : IsElementaryAbelian 2 E₂ := isElementaryAbelian_proj hc' hd' (sup_comm K₁ K₂ ▸ hEK)
  have hE₂comm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥E₂)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZ₂ : ∀ z ∈ K₂, (∀ y ∈ K₂, z * y = y * z) → z = 1 := fun z hz hzc =>
    eq_one_of_commute_sup hc hCK hz hzc
  have hcard : Nat.card K₂ = Nat.card K₁ :=
    (Nat.card_congr θ₂.toEquiv).trans (Nat.card_congr θ₁.toEquiv).symm
  have hK₂ : K₂ ≠ ⊥ := fun h0 => by
    have h1 : Nat.card K₂ = 1 := by rw [h0, card_bot]
    rw [Nat.card_congr θ₂.toEquiv] at h1
    exact (Finite.one_lt_card_iff_nontrivial.2
      (CFSG.LieType.Ree.suzuki_simple ha hk).2.1).ne' h1
  have hs₂ := map_conj_eq_left_of_swap hc hd hKn hZ₂ hcard hK₂ hsK
  have hE₁₂ : E₁.map (MulAut.conj s).toMonoidHom = E₂ :=
    H13.QRC.map_proj_of_swap hsK hs₂ (hSE hs)
  have hcardE : Nat.card E₁ = Nat.card E₂ := by
    rw [← hE₁₂, card_map_of_injective (f := (MulAut.conj s).toMonoidHom) (MulAut.conj s).injective]
  obtain ⟨r, hr⟩ := (IsElementaryAbelian.isPGroup 2 E₁).exists_card_eq
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      rw [h, pow_zero] at hr
      have h1 : E₁ = ⊥ := card_eq_one.1 hr
      have h2 : E₂ = ⊥ := card_eq_one.1 (hcardE ▸ hr)
      rw [h1, h2, sup_bot_eq] at hEE
      have h3 := card_le_of_le hEE
      rw [card_bot] at h3
      omega
    · exact h
  have hE₁K : E₁ ≤ K₁ := inf_le_right
  have hE₂K : E₂ ≤ K₂ := inf_le_right
  have hE₂S : E₂ ≤ S := hE₂U.trans inf_le_left
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  ·
    have hE₁c : Nat.card E₁ = 2 := by rw [hr, show r = 1 by omega, pow_one]
    have : Nontrivial E₁ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE₁c]; norm_num)
    obtain ⟨⟨e, heE⟩, he1⟩ := exists_ne (1 : E₁)
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    have hoe : orderOf e = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian e heE) he1'
    have hE₁z : E₁ = zpowers e := by
      symm
      refine eq_of_le_of_card_ge (zpowers_le.2 heE) ?_
      rw [hE₁c, Nat.card_zpowers, hoe]
    have heU : e ∈ S ⊓ K₁ := hE₁U heE
    have he'U : (⟨e, heU.2⟩ : K₁) ∈ (U₁ : Subgroup K₁) := by
      rw [hU₁]
      exact heU
    have he'o : orderOf (⟨e, heU.2⟩ : K₁) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hoe
    obtain ⟨x', hx'N, ℓ, hℓ, hℓ2, hx'o, hx'e⟩ := exists_inverted_of_bender hD he'U he'o
    have hx₁K : (x' : A) ∈ K₁ := x'.2
    have hox : orderOf (x' : A) = ℓ := by rw [Subgroup.orderOf_coe, hx'o]
    have hex : e * (x' : A) * e⁻¹ = (x' : A)⁻¹ := by
      have := congrArg Subtype.val hx'e
      simpa using this
    have hx₁B : (x' : A) ∉ B := by
      intro hB
      apply hx'N
      have h1 : (x' : A) ∈ B ⊓ K₁ := ⟨hB, hx₁K⟩
      rw [hBK₁] at h1
      obtain ⟨z, hz, hzx⟩ := h1
      rwa [← K₁.subtype_injective hzx]
    obtain ⟨hx₁L, hDih, hcardL, -, -, hsyl, hcore, hO2, hO2P⟩ :=
      dihedral_pair hℓ hℓ2 hE₁z hoe hox hex hx₁B (hE₁U.trans inf_le_left) hSB
    have hL₁K : E₁ ⊔ conjugate E₁ (x' : A) ≤ K₁ := by
      refine sup_le hE₁K fun y hy => ?_
      rw [mem_conjugate_iff] at hy
      have h1 : y = (x' : A)⁻¹ * ((x' : A) * y * (x' : A)⁻¹) * (x' : A) := by group
      rw [h1]
      exact K₁.mul_mem (K₁.mul_mem (K₁.inv_mem hx₁K) (hE₁K hy)) hx₁K
    have hcard12 : Nat.card ↥(E₁ ⊔ E₂) = 4 := by
      rw [H13.QRC.card_sup_of_commute (fun a ha b hb => hc a (hE₁K ha) b (hE₂K hb))
        (eq_bot_iff.2 ((inf_le_inf hE₁K hE₂K).trans hd.le)), hE₁c, ← hcardE, hE₁c]
    have hE12 : E = E₁ ⊔ E₂ := eq_of_le_of_card_ge hEE (by rw [hcard12]; exact hE4)
    have hE₁E : E₁ ≤ E := hE12 ▸ le_sup_left
    have hLeq : E ⊔ conjugate E (x' : A) = E₁ ⊔ conjugate E₁ (x' : A) ⊔ E₂ := by
      refine le_antisymm (H13.QRC.sup_conjugate_le hc hEK hx₁K) (sup_le ?_ ?_)
      · exact sup_le (hE₁E.trans le_sup_left) ((map_mono hE₁E).trans le_sup_right)
      · exact (hE12 ▸ le_sup_right : E₂ ≤ E).trans le_sup_left
    have hEL : (E ⊔ E₂) ⊓ (E₁ ⊔ conjugate E₁ (x' : A)) = E₁ :=
      le_antisymm (inf_le_inf (sup_le_sup_left hE₂K _) hL₁K)
        (le_inf (hE₁E.trans le_sup_left) le_sup_left)
    refine ⟨x', _, hx₁L, hL₁K, hLeq, hel₂, hE₂S, hsyl, hcore, hO2, hO2P,
      Or.inl ⟨ℓ, hℓ, hℓ2, hDih, ?_, hcardL⟩⟩
    rw [hEL, hE₁c]
  ·
    have hE₁4 : 4 ≤ Nat.card E₁ := by
      rw [hr]
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ r := Nat.pow_le_pow_right two_pos hr2
    obtain ⟨x, hxN, -, hxL, hLeq', hLK, hsyl, hcore, hO2, hO2P, -, -⟩ :=
      H13.QRC.bender_pair_in_quotient hU₁ hD hBK₁ hE₁U hE₁4
    have h3 : ¬ 3 ∣ Nat.card K₁ := by
      rw [Nat.card_congr θ₁.toEquiv]
      exact H13.QRC.not_three_dvd_card_suzukiGroup hk
    have : IsElementaryAbelian 2 (E₁.subgroupOf K₁) := IsElementaryAbelian.subgroupOf hE₁K
    have hE'U : E₁.subgroupOf K₁ ≤ (U₁ : Subgroup K₁) := by
      rw [hU₁]
      exact fun y hy => hE₁U hy
    have hE'4 : 4 ≤ Nat.card (E₁.subgroupOf K₁) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hE₁K).toEquiv]
    obtain ⟨b, hb, -, -, e, -, -⟩ := H13.QRC.bender_pair_suzuki hD h3 hE'U hE'4 hxN
    set L' := E₁.subgroupOf K₁ ⊔ conjugate (E₁.subgroupOf K₁) x with hL'
    have eL : ↥(L'.map K₁.subtype) ≃* suzukiGroup b (GaloisField 2 (2 * b + 1)) :=
      (L'.equivMapOfInjective K₁.subtype K₁.subtype_injective).symm.trans e
    have hcardF : Nat.card (GaloisField 2 (2 * b + 1)) = 2 ^ (2 * b + 1) :=
      GaloisField.card 2 (2 * b + 1) (by omega)
    have : Group.IsPerfect (suzukiGroup b (GaloisField 2 (2 * b + 1))) :=
      (CFSG.LieType.Ree.suzuki_perfect hb hcardF).2
    have : Group.IsPerfect ↥(L'.map K₁.subtype) :=
      Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
    have hLeq : E ⊔ conjugate E (x : A) = L'.map K₁.subtype ⊔ E₂ :=
      H13.QRC.sup_conjugate_eq_of_perfect hc hEK x.2 hLeq' hE₂comm
    exact ⟨x, _, hxL, hLK, hLeq, hel₂, hE₂S, hsyl, hcore, hO2, hO2P, Or.inr ⟨b, hb, ⟨eL⟩⟩⟩


end CFSG.Quasithin.Ch3E213M.P2
