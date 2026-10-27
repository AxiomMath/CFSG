module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqAbs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace S153M

section Diag

theorem normalizer_sup_central_le {X : Type} [Group X] [Finite X] {S₁ : Subgroup X}
    (hS₁ : IsSylowTwoOf S₁ ⊤) {C : Subgroup X} (hC : C ≤ Subgroup.center X) :
    Subgroup.normalizer ((S₁ ⊔ C : Subgroup X) : Set X) ≤ Subgroup.normalizer (S₁ : Set X) := by
  intro x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup X := S₁ ⊔ C with hR
  have hSR : S₁ ≤ R := le_sup_left
  have hRN : R ≤ Subgroup.normalizer (S₁ : Set X) :=
    sup_le Subgroup.le_normalizer (hC.trans (Subgroup.center_le_normalizer _))
  have hnorm : (S₁.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSR).2 hRN
  have hP2 : IsPGroup 2 (S₁.subgroupOf R) := hS₁.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSR).symm
  have hodd : ¬ 2 ∣ (S₁.subgroupOf R).index := by
    intro hd
    have h1 : (S₁.subgroupOf R).index = S₁.relIndex R := rfl
    have h2 : S₁.relIndex R ∣ S₁.index := Subgroup.relIndex_dvd_index_of_le hSR
    have h3 : (S₁.subgroupOf ⊤).index = S₁.index := Subgroup.relIndex_top_right S₁
    exact hS₁.2.2 (by rw [h3]; exact (h1 ▸ hd).trans h2)
  let P : Sylow 2 ↥R := hP2.toSylow hodd
  have hPn : P.Normal := by
    exact hnorm
  have hchar := Sylow.characteristic_of_normal P hPn
  let e : ↥R ≃* ↥R := R.normalizerMonoidHom ⟨x, hx⟩
  have hfix := hchar.fixed e
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxR : ∀ z : X, x * z * x⁻¹ ∈ R ↔ z ∈ R := fun z => by
    simpa using (Subgroup.mem_normalizer_iff.mp hx z).symm
  constructor
  · intro hy
    have hyR : y ∈ R := hSR hy
    have h1 : (⟨y, hyR⟩ : ↥R) ∈ (P : Subgroup ↥R) := hy
    have h2 : (⟨y, hyR⟩ : ↥R) ∈ (P : Subgroup ↥R).comap e.toMonoidHom := by
      rw [hfix]
      exact h1
    exact h2
  · intro hy
    have hyR : y ∈ R := (hxR y).1 (hSR hy)
    have h2 : (⟨y, hyR⟩ : ↥R) ∈ (P : Subgroup ↥R).comap e.toMonoidHom := hy
    rw [hfix] at h2
    exact h2

theorem coatom_image {X Z : Type} [Group X] [Group Z] [Finite X] (σ : X →* Z)
    (hσ : Function.Surjective σ) (hz : σ.ker ≤ Subgroup.center X) {S₁ : Subgroup X}
    (hS₁ : IsSylowTwoOf S₁ ⊤) {Q : Subgroup X} (hQ : Q ⋖ ⊤)
    (hQS : ∀ x ∈ Subgroup.normalizer (S₁ : Set X), x ∈ Q) :
    Q.map σ ≠ ⊤ ∧ (∀ Q' : Subgroup Z, Q.map σ ≤ Q' → Q' = Q.map σ ∨ Q' = ⊤) ∧
      ∀ z ∈ Subgroup.normalizer ((S₁.map σ : Subgroup Z) : Set Z), z ∈ Q.map σ := by
  have hkerQ : σ.ker ≤ Q := fun x hx =>
    hQS x (Subgroup.center_le_normalizer _ (hz hx))
  have hpre : (Q.map σ).comap σ = Q := by
    rw [Subgroup.comap_map_eq]
    exact sup_eq_left.mpr hkerQ
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : (⊤ : Subgroup X) = Q := by
      rw [← hpre, h]
      rfl
    exact hQ.ne this.symm
  · intro Q' hQ'
    have h1 : Q ≤ Q'.comap σ := by
      rw [← hpre]
      exact Subgroup.comap_mono hQ'
    rcases hQ.wcovBy.eq_or_eq h1 le_top with h | h
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective hσ Q', h]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective hσ Q', h, Subgroup.map_top_of_surjective σ hσ]
  · intro z hz'
    obtain ⟨x, rfl⟩ := hσ z
    have hxR : x ∈ Subgroup.normalizer ((S₁ ⊔ σ.ker : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.mp hz' (σ y)
      have e1 : (S₁ ⊔ σ.ker : Subgroup X) = (S₁.map σ).comap σ := by
        rw [Subgroup.comap_map_eq]
      rw [e1]
      simpa [Subgroup.mem_comap, map_mul, map_inv] using h1
    exact ⟨x, hQS x (normalizer_sup_central_le hS₁ hz hxR), rfl⟩

theorem isSylowTwoOf_subgroupOf_top' {Γ : Type} [Group Γ] {X S : Subgroup Γ} (hS : IsSylowTwoOf S X) :
    IsSylowTwoOf (S.subgroupOf X) ⊤ := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  have h3 : ((S.subgroupOf X).subgroupOf ⊤).index = (S.subgroupOf X).index :=
    Subgroup.relIndex_top_right _
  rw [h3]
  exact hS.2.2

theorem isSylowTwoOf_of_subgroupOf_top {Γ : Type} [Group Γ] {X S : Subgroup Γ} (hSX : S ≤ X)
    (hS : IsSylowTwoOf (S.subgroupOf X) ⊤) : IsSylowTwoOf S X := by
  refine ⟨hSX, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSX), ?_⟩
  have h := hS.2.2
  have h3 : ((S.subgroupOf X).subgroupOf ⊤).index = (S.subgroupOf X).index :=
    Subgroup.relIndex_top_right _
  rwa [h3] at h

theorem isSylowTwoOf_map_top_surj {A B : Type} [Group A] [Finite A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) {P : Subgroup A} (hP : IsSylowTwoOf P ⊤) :
    IsSylowTwoOf (P.map f) ⊤ := by
  refine ⟨le_top, hP.2.1.map f, fun hd => hP.2.2 ?_⟩
  have h1 : (P.map f).relIndex ⊤ = (P.map f).index := Subgroup.relIndex_top_right _
  have h2 : 2 ∣ (P.map f).index := by
    rw [← h1]
    exact hd
  have h3 : (P.subgroupOf ⊤).index = P.index := Subgroup.relIndex_top_right P
  rw [h3]
  exact h2.trans (Subgroup.index_map_dvd P hf)

theorem not_isDiagramNontrivial_of_coatom {Γ : Type} [Group Γ] {Ks S Ts : Subgroup Γ}
    (hS : IsSylowTwoOf S Ks) {X : Type} [Group X] [Finite X] (σ : X →* ↥Ks)
    (hσ : Function.Surjective σ) (hz : σ.ker ≤ Subgroup.center X) {S₁ : Subgroup X}
    (hS₁ : IsSylowTwoOf S₁ ⊤) (hSσ : S₁.map σ = S.subgroupOf Ks) {Q : Subgroup X} (hQ : Q ⋖ ⊤)
    (hQS : ∀ x ∈ Subgroup.normalizer (S₁ : Set X), x ∈ Q)
    (hα : ∀ t ∈ Ts, ∃ α : X ≃* X, (∀ x : X, ((σ (α x) : ↥Ks) : Γ) = t * (σ x : Γ) * t⁻¹) ∧
      ∀ x ∈ Q, α x ∈ Q) :
    ¬ E2.IsDiagramNontrivial Ts Ks S := by
  obtain ⟨hne, hmax, hN⟩ := coatom_image σ hσ hz hS₁ hQ hQS
  set P : Subgroup Γ := (Q.map σ).map Ks.subtype with hP
  have hPK : P ≤ Ks := Subgroup.map_subtype_le _
  have hmemP : ∀ g : Γ, g ∈ P ↔ ∃ y : ↥Ks, y ∈ Q.map σ ∧ (y : Γ) = g := fun g => by
    rw [hP, Subgroup.mem_map]
    rfl
  have hPne : P ≠ Ks := by
    intro h
    apply hne
    refine (Subgroup.eq_top_iff' _).2 fun y => ?_
    have : (y : Γ) ∈ P := by rw [h]; exact y.2
    obtain ⟨y', hy', hyy'⟩ := (hmemP _).1 this
    have : y' = y := Subtype.ext hyy'
    rwa [← this]
  have hPmax : ∀ Q'' : Subgroup Γ, Q'' ≤ Ks → P ≤ Q'' → Q'' = P ∨ Q'' = Ks := by
    intro Q'' hQK hPQ
    have h1 : Q.map σ ≤ Q''.subgroupOf Ks := by
      intro z hz'
      exact hPQ ((hmemP _).2 ⟨z, hz', rfl⟩)
    rcases hmax _ h1 with h | h
    · left
      have : Q'' = (Q''.subgroupOf Ks).map Ks.subtype := (Subgroup.map_subgroupOf_eq_of_le hQK).symm
      rw [this, h]
    · right
      exact le_antisymm hQK (Subgroup.subgroupOf_eq_top.mp h)
  have hB : Ks ⊓ Subgroup.normalizer (S : Set Γ) ≤ P := by
    rintro x ⟨hxK, hxN⟩
    have hy : (⟨x, hxK⟩ : ↥Ks) ∈ Subgroup.normalizer ((S₁.map σ : Subgroup ↥Ks) : Set ↥Ks) := by
      rw [Subgroup.mem_normalizer_iff, hSσ]
      intro h
      have := Subgroup.mem_normalizer_iff.mp hxN (h : Γ)
      exact this
    exact (hmemP _).2 ⟨⟨x, hxK⟩, hN _ hy, rfl⟩
  have hfwd : ∀ t ∈ Ts, ∀ g ∈ P, t * g * t⁻¹ ∈ P := by
    intro t ht g hg
    obtain ⟨y, ⟨x, hxQ, rfl⟩, rfl⟩ := (hmemP _).1 hg
    obtain ⟨α, hα1, hα2⟩ := hα t ht
    refine (hmemP _).2 ⟨σ (α x), ⟨α x, hα2 x hxQ, rfl⟩, ?_⟩
    exact hα1 x
  have hT : Ts ≤ Subgroup.normalizer (P : Set Γ) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hfwd t ht g
    · intro hg
      have := hfwd t⁻¹ (Ts.inv_mem ht) _ hg
      simpa [mul_assoc] using this
  exact H13.Lem1227Eq.not_isDiagramNontrivial_of_stable hS hPK hPne hPmax hB hT

end Diag

end S153M

end CFSG.Quasithin
