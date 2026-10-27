module

public import CFSG.Assembly.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin

namespace F918V5G

variable {G : Type*} [Group G]

theorem le_pRank_of_card [Finite G] {p : ℕ} (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : CFSG.Assembly.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Assembly.pRank p H := CFSG.SectionRank.le_pRank hp hEH hE hk

theorem two_le_pRank_of_not_cyclic [Finite G] {H Q : Subgroup G} (hQH : Q ≤ H)
    (hQ : IsPGroup 3 Q) (hnc : ¬ IsCyclic ↥Q) : 2 ≤ CFSG.Assembly.pRank 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 ↥Q) := ⟨hQ⟩
  obtain ⟨S, -, hS9, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have := hSel
  have hEel : CFSG.IsElementaryAbelian 3 ↥(S.map Q.subtype) := CFSG.IsElementaryAbelian.map_subtype
  refine le_pRank_of_card (by norm_num) (E := S.map Q.subtype)
    ((Subgroup.map_subtype_le S).trans hQH) ⟨hEel.toIsMulCommutative, fun x hx => ?_⟩ ?_
  · exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hS9]

@[expose] def HasNoncentral3 (K : Subgroup G) : Prop :=
  ∃ P : Subgroup G, P ≤ K ∧ IsPGroup 3 P ∧ ¬ P ≤ Subgroup.centralizer (K : Set G)

theorem hasNoncentral3_of_three_dvd [Finite G] {K : Subgroup G}
    (h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) : HasNoncentral3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  refine ⟨(P : Subgroup ↥K).map K.subtype, Subgroup.map_subtype_le _,
    P.isPGroup'.map K.subtype, fun hle => ?_⟩
  have hP : (P : Subgroup ↥K) ≤ Subgroup.center ↥K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_centralizer_iff.mp (hle ⟨x, hx, rfl⟩) (y : G) y.2
    exact Subtype.ext this
  have hdvd : (Subgroup.center ↥K).index ∣ (P : Subgroup ↥K).index :=
    Subgroup.index_dvd_of_le hP
  exact P.not_dvd_index (h3.trans hdvd)

theorem HasNoncentral3.map_conj {K : Subgroup G} (h : HasNoncentral3 K) (m : G) :
    HasNoncentral3 (K.map (MulAut.conj m).toMonoidHom) := by
  obtain ⟨P, hPK, hP3, hPc⟩ := h
  refine ⟨P.map (MulAut.conj m).toMonoidHom, Subgroup.map_mono hPK, hP3.map _, fun hle => hPc ?_⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : m * k * m⁻¹ * (m * x * m⁻¹) = m * x * m⁻¹ * (m * k * m⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (hle ⟨x, hx, rfl⟩) (m * k * m⁻¹) ⟨k, hk, rfl⟩
  have h2 : m * (k * x) * m⁻¹ = m * (x * k) * m⁻¹ := by
    have e1 : m * (k * x) * m⁻¹ = m * k * m⁻¹ * (m * x * m⁻¹) := by group
    have e2 : m * (x * k) * m⁻¹ = m * x * m⁻¹ * (m * k * m⁻¹) := by group
    rw [e1, e2]
    exact h1
  exact mul_left_cancel (mul_right_cancel h2)

theorem two_le_pRank_of_commuting [Finite G] {Y K₁ K₂ : Subgroup G} (h1 : K₁ ≤ Y)
    (h2 : K₂ ≤ Y) (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hn1 : HasNoncentral3 K₁)
    (hn2 : HasNoncentral3 K₂) : 2 ≤ CFSG.Assembly.pRank 3 Y := by
  obtain ⟨P₁, hP₁K, hP₁, hP₁c⟩ := hn1
  obtain ⟨P₂, hP₂K, hP₂, hP₂c⟩ := hn2
  have hP₁K₂ : ¬ P₁ ≤ K₂ := fun h => hP₁c fun x hx => Subgroup.mem_centralizer_iff.mpr
    fun k hk => hcomm k hk x (h hx)
  have hP₂K₁ : ¬ P₂ ≤ K₁ := fun h => hP₂c fun x hx => Subgroup.mem_centralizer_iff.mpr
    fun k hk => (hcomm x (h hx) k hk).symm
  have hfix : ∀ g ∈ P₁, ∀ z ∈ P₂, g * z * g⁻¹ = z := fun g hg z hz =>
    mul_inv_eq_iff_eq_mul.mpr (hcomm g (hP₁K hg) z (hP₂K hz))
  have hnorm : P₁ ≤ Subgroup.normalizer (P₂ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rwa [hfix x hx y hy]
    · intro hy
      have h3 := hfix x⁻¹ (P₁.inv_mem hx) _ hy
      have h4 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rw [h4] at h3
      rw [h3]
      exact hy
  have hQ : IsPGroup 3 (P₁ ⊔ P₂ : Subgroup G) := hP₁.to_sup_of_normal_right' hP₂ hnorm
  have hQY : P₁ ⊔ P₂ ≤ Y := sup_le (hP₁K.trans h1) (hP₂K.trans h2)
  refine two_le_pRank_of_not_cyclic hQY hQ fun hcyc => ?_
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hcyc
  have hP₁Q : P₁ ≤ P₁ ⊔ P₂ := le_sup_left
  have hP₂Q : P₂ ≤ P₁ ⊔ P₂ := le_sup_right
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 3)).mp hP₁
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 3)).mp hP₂
  have hAcard : Nat.card ↥(P₁.subgroupOf (P₁ ⊔ P₂)) = 3 ^ a := by
    rw [← ha]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁Q).toEquiv
  have hBcard : Nat.card ↥(P₂.subgroupOf (P₁ ⊔ P₂)) = 3 ^ b := by
    rw [← hb]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₂Q).toEquiv
  rcases le_total a b with hab | hab
  · have hle : P₁.subgroupOf (P₁ ⊔ P₂) ≤ P₂.subgroupOf (P₁ ⊔ P₂) := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, hAcard, hBcard]
      exact pow_dvd_pow 3 hab
    exact hP₁K₂ fun x hx => hP₂K (hle (show (⟨x, hP₁Q hx⟩ : ↥(P₁ ⊔ P₂)) ∈
      P₁.subgroupOf (P₁ ⊔ P₂) from hx))
  · have hle : P₂.subgroupOf (P₁ ⊔ P₂) ≤ P₁.subgroupOf (P₁ ⊔ P₂) := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, hAcard, hBcard]
      exact pow_dvd_pow 3 hab
    exact hP₂K₁ fun x hx => hP₁K (hle (show (⟨x, hP₂Q hx⟩ : ↥(P₁ ⊔ P₂)) ∈
      P₂.subgroupOf (P₁ ⊔ P₂) from hx))

end F918V5G

end CFSG.Quasithin
