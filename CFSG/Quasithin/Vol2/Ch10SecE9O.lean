module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122APerfect
public import CFSG.Quasithin.Vol2.Ch10SecQ34LA
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_sup_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm

omit [Finite G] in
theorem exists_pow_of_mem_zpowers {y g : G} (hy : IsOfFinOrder y)
    (hg : g ∈ Subgroup.zpowers y) : ∃ n : ℕ, g = y ^ n := by
  obtain ⟨n, hn⟩ := (hy.mem_powers_iff_mem_zpowers).mpr hg
  exact ⟨n, hn.symm⟩

theorem exists_elemAbelian_of_centralizes {X R : Subgroup G} {y : G} (hR2 : IsPGroup 2 R)
    (hRX : R ≤ X) (hXR : X ≤ Subgroup.normalizer (R : Set G)) (hidx : R.relIndex X = 9)
    (h3 : ∀ x ∈ X, x ^ 3 ∈ R) (hcomm : ∀ x ∈ X, ∀ x' ∈ X, x * x' * x⁻¹ * x'⁻¹ ∈ R)
    (hyX : y ∈ Subgroup.normalizer (X : Set G)) (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hy3 : orderOf y = 3) (hyn : y ∉ X) (hcent : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ R) :
    ∃ E : Subgroup G, E ≤ X ⊔ Subgroup.zpowers y ∧ IsElementaryAbelian 3 ↥E ∧
      ∃ k : ℕ, 3 ≤ k ∧ Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := X ⊔ Subgroup.zpowers y with hH
  have hzX : Subgroup.zpowers y ≤ Subgroup.normalizer (X : Set G) := Subgroup.zpowers_le.mpr hyX
  have hXz : X ⊓ Subgroup.zpowers y = ⊥ := by
    have hcard : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hy3]
    have hdvd : Nat.card ↥(X ⊓ Subgroup.zpowers y) ∣ 3 :=
      hcard ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have : X ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hcard])
      exact hyn ((this ▸ inf_le_left : Subgroup.zpowers y ≤ X) (Subgroup.mem_zpowers y))
  have hHX : X.relIndex H = 3 := by
    rw [hH, sup_comm, relIndex_sup_of_le_normalizer hzX]
    have h1 := Subgroup.relIndex_mul_card X (Subgroup.zpowers y)
    rw [hXz, Subgroup.card_bot, mul_one, Nat.card_zpowers, hy3] at h1
    exact h1
  have hcardH : Nat.card H = 3 * Nat.card X := by
    have h1 := Subgroup.relIndex_mul_card X H
    rw [inf_eq_left.mpr le_sup_left, hHX] at h1
    exact h1.symm
  have hcardX : Nat.card X = 9 * Nat.card R := by
    have h1 := Subgroup.relIndex_mul_card R X
    rw [inf_eq_left.mpr hRX, hidx] at h1
    exact h1.symm
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥H) := inferInstance
  have h27 : 3 ^ 3 ∣ Nat.card ↥H := ⟨Nat.card R, by rw [hcardH, hcardX]; ring⟩
  have hS27 := S.pow_dvd_card_of_pow_dvd_card h27
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  set Em := (S : Subgroup ↥H).map H.subtype with hEm
  have hcardE : Nat.card Em = 3 ^ k := by
    rw [hEm, Subgroup.card_map_of_injective H.subtype_injective, hk]
  have hk3 : 3 ≤ k := by
    rw [hk] at hS27
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hS27
  have hEH : Em ≤ H := Subgroup.map_subtype_le _
  set M := Subgroup.normalizer (R : Set G) with hM
  have hHM : H ≤ M := sup_le hXR (Subgroup.zpowers_le.mpr hyR)
  have : (R.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hπ1 : ∀ (g : G) (hg : g ∈ M),
      QuotientGroup.mk' (R.subgroupOf M) ⟨g, hg⟩ = 1 ↔ g ∈ R := fun g hg => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcommπ : ∀ (a b : G) (ha : a ∈ M) (hb : b ∈ M), a * b * a⁻¹ * b⁻¹ ∈ R →
      Commute (QuotientGroup.mk' (R.subgroupOf M) ⟨a, ha⟩)
        (QuotientGroup.mk' (R.subgroupOf M) ⟨b, hb⟩) := by
    intro a b ha hb hab
    have h1 := (hπ1 _ (M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb))).mpr
      hab
    have e : (⟨a * b * a⁻¹ * b⁻¹, M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha))
        (M.inv_mem hb)⟩ : ↥M) = ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hπ : ∀ (g : G) (hg : g ∈ M), ∀ n : ℕ,
      QuotientGroup.mk' (R.subgroupOf M) ⟨g ^ n, M.pow_mem hg n⟩ =
        QuotientGroup.mk' (R.subgroupOf M) ⟨g, hg⟩ ^ n := fun g hg n => by
    rw [← map_pow]; rfl
  have hyM : y ∈ M := hHM (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hdec : ∀ g ∈ H, ∃ x ∈ X, ∃ n : ℕ, g = x * y ^ n := by
    intro g hg
    have hg' : g ∈ ((X ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X (Subgroup.zpowers y) hzX] at hg'
    obtain ⟨x, hx, z, hz, rfl⟩ := Set.mem_mul.mp hg'
    obtain ⟨n, rfl⟩ := exists_pow_of_mem_zpowers (isOfFinOrder_of_finite y) hz
    exact ⟨x, hx, n, rfl⟩
  have hπmul : ∀ (x : G) (hx : x ∈ M) (n : ℕ), QuotientGroup.mk' (R.subgroupOf M)
      ⟨x * y ^ n, M.mul_mem hx (M.pow_mem hyM n)⟩ =
      QuotientGroup.mk' (R.subgroupOf M) ⟨x, hx⟩ *
        QuotientGroup.mk' (R.subgroupOf M) ⟨y, hyM⟩ ^ n := fun x hx n => by
    rw [← hπ y hyM n, ← map_mul]; rfl
  have hcX : ∀ (x : G) (hx : x ∈ X) (x' : G) (hx' : x' ∈ X),
      Commute (QuotientGroup.mk' (R.subgroupOf M) ⟨x, hXR hx⟩)
        (QuotientGroup.mk' (R.subgroupOf M) ⟨x', hXR hx'⟩) := fun x hx x' hx' =>
    hcommπ x x' (hXR hx) (hXR hx') (hcomm x hx x' hx')
  have hcy : ∀ (x : G) (hx : x ∈ X), Commute (QuotientGroup.mk' (R.subgroupOf M) ⟨y, hyM⟩)
      (QuotientGroup.mk' (R.subgroupOf M) ⟨x, hXR hx⟩) := fun x hx =>
    hcommπ y x hyM (hXR hx) (hcent x hx)
  have hpy : QuotientGroup.mk' (R.subgroupOf M) ⟨y, hyM⟩ ^ 3 = 1 := by
    rw [← hπ y hyM 3]
    exact (hπ1 _ _).mpr (by rw [← hy3, pow_orderOf_eq_one]; exact R.one_mem)
  have hpx : ∀ (x : G) (hx : x ∈ X), QuotientGroup.mk' (R.subgroupOf M) ⟨x, hXR hx⟩ ^ 3 = 1 :=
      fun x hx => by
    rw [← hπ x (hXR hx) 3]
    exact (hπ1 _ _).mpr (h3 x hx)
  have hHcomm : ∀ g ∈ H, ∀ g' ∈ H, g * g' * g⁻¹ * g'⁻¹ ∈ R := by
    intro g hg g' hg'
    obtain ⟨x, hx, a, rfl⟩ := hdec g hg
    obtain ⟨x', hx', b, rfl⟩ := hdec g' hg'
    refine (hπ1 _ (M.mul_mem (M.mul_mem (M.mul_mem (hHM hg) (hHM hg')) (M.inv_mem (hHM hg)))
      (M.inv_mem (hHM hg')))).mp ?_
    have hC : Commute (QuotientGroup.mk' (R.subgroupOf M) ⟨x * y ^ a, hHM hg⟩)
        (QuotientGroup.mk' (R.subgroupOf M) ⟨x' * y ^ b, hHM hg'⟩) := by
      rw [hπmul x (hXR hx) a, hπmul x' (hXR hx') b]
      exact Commute.mul_left (Commute.mul_right (hcX x hx x' hx') ((hcy x hx).symm.pow_right b))
        (Commute.mul_right ((hcy x' hx').pow_left a) (Commute.pow_pow_self _ a b))
    have e : (⟨x * y ^ a * (x' * y ^ b) * (x * y ^ a)⁻¹ * (x' * y ^ b)⁻¹, _⟩ : ↥M) =
        ⟨x * y ^ a, hHM hg⟩ * ⟨x' * y ^ b, hHM hg'⟩ * ⟨x * y ^ a, hHM hg⟩⁻¹ *
          ⟨x' * y ^ b, hHM hg'⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hC.eq, mul_inv_cancel_right,
      mul_inv_cancel]
  have hHcube : ∀ g ∈ H, g ^ 3 ∈ R := by
    intro g hg
    obtain ⟨x, hx, a, rfl⟩ := hdec g hg
    refine (hπ1 _ (M.pow_mem (hHM hg) 3)).mp ?_
    rw [hπ _ (hHM hg) 3, hπmul x (hXR hx) a, ((hcy x hx).symm.pow_right a).mul_pow, hpx x hx,
      one_mul, ← pow_mul, mul_comm, pow_mul, hpy, one_pow]
  obtain ⟨r, hr⟩ := hR2.exists_card_eq
  have hdisj : Em ⊓ R = ⊥ := (Subgroup.disjoint_of_coprime_natCard (by
    rw [hcardE, hr]; exact Nat.Coprime.pow k r (by norm_num))).eq_bot
  have hmemR : ∀ g ∈ Em, g ∈ R → g = 1 := fun g hg hgR => by
    have : g ∈ Em ⊓ R := ⟨hg, hgR⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  refine ⟨Em, hEH.trans le_rfl, ?_, k, hk3, hcardE⟩
  refine { toIsMulCommutative := isMulCommutative_iff.mpr fun a b => Subtype.ext ?_,
           exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext ?_ }
  · have h1 := hmemR _ (Em.mul_mem (Em.mul_mem (Em.mul_mem a.2 b.2) (Em.inv_mem a.2))
      (Em.inv_mem b.2)) (hHcomm _ (hEH a.2) _ (hEH b.2))
    simp only [Subgroup.coe_mul]
    calc (a : G) * b = (a * b * (a : G)⁻¹ * (b : G)⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hmemR _ (Em.pow_mem a.2 3) (hHcube _ (hEH a.2))

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
