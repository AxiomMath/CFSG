module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

theorem card_le_four_of_sq {S : Subgroup (DihedralGroup 4)} (h : ∀ x ∈ S, x * x = 1) :
    Nat.card S ≤ 4 := by
  classical
  have hle : Nat.card S ≤ 6 := by
    have h1 : Nat.card S ≤ Nat.card {x : DihedralGroup 4 // x * x = 1} :=
      Nat.card_le_card_of_injective (fun s => ⟨(s : DihedralGroup 4), h s s.2⟩)
        fun a b hab => Subtype.ext
          (congrArg (fun x : {x : DihedralGroup 4 // x * x = 1} => x.1) hab)
    have h6 : Nat.card {x : DihedralGroup 4 // x * x = 1} = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega
  have hdvd : Nat.card S ∣ 8 := by
    have := Subgroup.card_subgroup_dvd_card S
    rwa [DihedralGroup.nat_card] at this
  have hpos : 0 < Nat.card S := Nat.card_pos
  interval_cases hn : Nat.card S <;> omega

theorem normal_of_elem16 {E : Subgroup (DihedralGroup 4 × DihedralGroup 4)}
    (hcard : Nat.card E = 16) (hsq : ∀ x ∈ E, x * x = 1) : E.Normal := by
  classical
  set P₁ : Subgroup (DihedralGroup 4) := E.map (MonoidHom.fst _ _) with hP₁
  set P₂ : Subgroup (DihedralGroup 4) := E.map (MonoidHom.snd _ _) with hP₂
  have h1 : ∀ x ∈ P₁, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have := congrArg Prod.fst (hsq y hy)
    simpa using this
  have h2 : ∀ x ∈ P₂, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have := congrArg Prod.snd (hsq y hy)
    simpa using this
  have c1 := card_le_four_of_sq h1
  have c2 := card_le_four_of_sq h2
  have hle : E ≤ P₁.prod P₂ := fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hcp : Nat.card (P₁.prod P₂) = Nat.card P₁ * Nat.card P₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv P₁ P₂).toEquiv, Nat.card_prod]
  have heq : E = P₁.prod P₂ :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcard, hcp]
      exact (Nat.mul_le_mul c1 c2).trans (by norm_num))
  have hp : Nat.card P₁ * Nat.card P₂ = 16 := by
    rw [← hcp, ← heq, hcard]
  have hP1 : Nat.card P₁ = 4 := by
    by_contra h
    have h3 : Nat.card P₁ ≤ 3 := by omega
    have := Nat.mul_le_mul h3 c2
    omega
  have hP2 : Nat.card P₂ = 4 := by
    by_contra h
    have h3 : Nat.card P₂ ≤ 3 := by omega
    have := Nat.mul_le_mul c1 h3
    omega
  have hD : Nat.card (DihedralGroup 4) = 8 := by rw [DihedralGroup.nat_card]
  have i1 : P₁.index = 2 := by
    have := Subgroup.card_mul_index P₁
    rw [hP1, hD] at this
    omega
  have i2 : P₂.index = 2 := by
    have := Subgroup.card_mul_index P₂
    rw [hP2, hD] at this
    omega
  have : P₁.Normal := Subgroup.normal_of_index_eq_two i1
  have : P₂.Normal := Subgroup.normal_of_index_eq_two i2
  rw [heq]
  infer_instance

variable {G : Type} [Group G]

theorem le_normalizer_of_dihedral {R A : Subgroup G}
    (e : Nonempty (↥R ≃* DihedralGroup 4 × DihedralGroup 4)) (hAR : A ≤ R)
    (hA : Nat.card A = 16) (hsq : ∀ a ∈ A, a * a = 1) :
    R ≤ Subgroup.normalizer (A : Set G) := by
  obtain ⟨e⟩ := e
  set S : Subgroup ↥R := A.subgroupOf R with hS
  set E : Subgroup (DihedralGroup 4 × DihedralGroup 4) := S.map e.toMonoidHom with hE
  have hcardS : Nat.card S = 16 := by
    rw [hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAR).toEquiv, hA]
  have hcardE : Nat.card E = 16 := by
    rw [hE, Subgroup.card_map_of_injective e.injective, hcardS]
  have hsqE : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (s : G) * s = 1 := hsq _ hs
    have : s * s = 1 := Subtype.ext hs'
    simp [← map_mul, this]
  have hnE := normal_of_elem16 hcardE hsqE
  have hSE : S = E.comap e.toMonoidHom := by
    rw [hE]
    exact (Subgroup.comap_map_eq_self_of_injective e.injective S).symm
  have : S.Normal := by
    rw [hSE]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAR).1 this

end CFSG.Quasithin.H13.F431.U42Aut
