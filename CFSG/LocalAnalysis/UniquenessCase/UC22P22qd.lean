module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.ABGLocalTools

private theorem uc22p22qd_isSylowOf_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsSylowOf p P ⊤) (g : G) :
    IsSylowOf p (P.comap (MulAut.conj g).toMonoidHom) ⊤ := by
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨-, hpg, hdvd⟩ := hP
  refine ⟨le_top, hpg.comap_of_injective _ (MulAut.conj g).injective, ?_⟩
  rw [Subgroup.relIndex_top_right, Subgroup.index_comap_of_surjective (H := P)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective]
  rwa [Subgroup.relIndex_top_right] at hdvd

private theorem uc22p22qd_mem_normalizer {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {n : G}
    (h : ∀ x ∈ Q, n * x * n⁻¹ ∈ Q) : n ∈ normalizer (Q : Set G) := by
  have hle : Q.map (MulAut.conj n).toMonoidHom ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : Q.map (MulAut.conj n).toMonoidHom = Q :=
    Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (MulAut.conj n).injective).ge
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have hxy' : (MulAut.conj n) x = (MulAut.conj n) y := hxy
  exact (MulAut.conj n).injective hxy' ▸ hx

private theorem uc22p22qd_comm_conj {G : Type*} [Group G] {y a g : G}
    (h : (g * y * g⁻¹) * a = a * (g * y * g⁻¹)) : g⁻¹ * a * g * y = y * (g⁻¹ * a * g) := by
  calc g⁻¹ * a * g * y = g⁻¹ * (a * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * y * g⁻¹) * a) * g := by rw [h]
    _ = y * (g⁻¹ * a * g) := by group

private theorem uc22p22qd_conj_eq {G : Type*} [Group G] {x g k : G}
    (h : g⁻¹ * x * g * k = k * (g⁻¹ * x * g)) : (g * k)⁻¹ * x * (g * k) = g⁻¹ * x * g := by
  calc (g * k)⁻¹ * x * (g * k) = k⁻¹ * (g⁻¹ * x * g * k) := by group
    _ = k⁻¹ * (k * (g⁻¹ * x * g)) := by rw [h]
    _ = g⁻¹ * x * g := by group

theorem uc22p22q_central_of_weaklyClosed {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P P₀ : Subgroup G} (hP : IsPGroup p P) (hP₀ : P₀ ≤ P) (hcard : Nat.card P₀ = p)
    (hwc : ∀ g : G, (∀ x ∈ P₀, g⁻¹ * x * g ∈ P) → ∀ x ∈ P₀, g⁻¹ * x * g ∈ P₀) :
    ∀ y ∈ P, ∀ z ∈ P₀, y * z = z * y := by
  have hn : ∀ y ∈ P, ∀ x ∈ P₀, y * x * y⁻¹ ∈ P₀ := by
    intro y hy x hx
    have h := hwc y⁻¹ (fun x' hx' => by
      rw [inv_inv]
      exact P.mul_mem (P.mul_mem hy (hP₀ hx')) (P.inv_mem hy)) x hx
    rwa [inv_inv] at h
  let act : P → P₀ → P₀ := fun y x => ⟨y * x * y⁻¹, hn y y.2 x x.2⟩
  have hact₁ : ∀ x, act 1 x = x := fun x => Subtype.ext (by simp [act])
  have hact₂ : ∀ y y' x, act (y * y') x = act y (act y' x) := fun y y' x =>
    Subtype.ext (by simp [act, mul_assoc])
  letI : MulAction P P₀ := { smul := act, one_smul := hact₁, mul_smul := hact₂ }
  haveI : Fact p.Prime := ⟨hp⟩
  have hsmul : ∀ (y : P) (x : P₀), ((y • x : P₀) : G) = y * x * y⁻¹ := fun _ _ => rfl
  have hone : (1 : P₀) ∈ MulAction.fixedPoints P P₀ :=
    MulAction.mem_fixedPoints.2 fun y => Subtype.ext (by simp [hsmul y 1])
  have hmod := hP.card_modEq_card_fixedPoints P₀
  rw [hcard] at hmod
  have hdvd : p ∣ (MulAction.fixedPoints P P₀).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
  have hge : p ≤ (MulAction.fixedPoints P P₀).ncard :=
    Nat.le_of_dvd ((Set.ncard_pos (Set.toFinite _)).2 ⟨1, hone⟩) hdvd
  have hle : (MulAction.fixedPoints P P₀).ncard ≤ p := hcard ▸ Set.ncard_le_card _
  have huniv : MulAction.fixedPoints P P₀ = Set.univ :=
    (Set.eq_univ_iff_ncard _).2 ((le_antisymm hle hge).trans hcard.symm)
  intro y hy z hz
  have hfix : (⟨z, hz⟩ : P₀) ∈ MulAction.fixedPoints P P₀ := huniv ▸ Set.mem_univ _
  have h := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hfix ⟨y, hy⟩)
  rw [hsmul] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem uc22p22q_fusion_of_central {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsSylowOf p P ⊤) {A X : Subgroup G} (hXA : X ≤ A)
    (hAcen : ∀ y ∈ P, ∀ a ∈ A, y * a = a * y) {g : G} (hg : ∀ x ∈ X, g⁻¹ * x * g ∈ A) :
    ∃ n ∈ normalizer (P : Set G), ∀ x ∈ X, g⁻¹ * x * g = n⁻¹ * x * n := by
  let H : Subgroup G := Subgroup.centralizer ((fun x => g⁻¹ * x * g) '' (X : Set G))
  have hPH : P ≤ H := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (hAcen y hy _ (hg x hx)).symm
  have hP'H : P.comap (MulAut.conj g).toMonoidHom ≤ H := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact uc22p22qd_comm_conj (hAcen _ hy x (hXA hx))
  obtain ⟨k, hkH, hk⟩ := (hP.of_le hPH le_top).exists_mem_conj
    ((uc22p22qd_isSylowOf_conj hP g).of_le hP'H le_top)
  refine ⟨g * k, ?_, fun x hx => ?_⟩
  · rw [mem_normalizer_iff]
    intro h
    have h1 := hk (k * h * k⁻¹)
    have e1 : k⁻¹ * (k * h * k⁻¹) * k = h := by group
    have e2 : g * k * h * (g * k)⁻¹ = g * (k * h * k⁻¹) * g⁻¹ := by group
    rw [e1] at h1
    rw [e2]
    exact h1.symm
  · exact (uc22p22qd_conj_eq (Subgroup.mem_centralizer_iff.1 hkH _ ⟨x, hx, rfl⟩)).symm

theorem uc22p22q_stronglyClosed_lift {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P P₀ P₁ : Subgroup G} (hP : IsSylowOf p P ⊤) (hP₀P : P₀ ≤ P)
    (hcen₀ : ∀ y ∈ P, ∀ z ∈ P₀, y * z = z * y)
    (hwc : ∀ g : G, (∀ x ∈ P₀, g⁻¹ * x * g ∈ P) → ∀ x ∈ P₀, g⁻¹ * x * g ∈ P₀)
    (hcen₁ : ∀ y ∈ P, ∀ a ∈ P₁, y * a = a * y)
    (hN : ∀ a ∈ P₁, ∀ n ∈ normalizer (P₀ : Set G), n⁻¹ * a * n ∈ P → n⁻¹ * a * n ∈ P₁) :
    ∀ a ∈ P₁, ∀ g : G, g⁻¹ * a * g ∈ P → g⁻¹ * a * g ∈ P₁ := by
  intro a ha g hb
  let C : Subgroup G := Subgroup.centralizer {g⁻¹ * a * g}
  have hSC : P.comap (MulAut.conj g).toMonoidHom ≤ C := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact uc22p22qd_comm_conj (hcen₁ _ hy a ha)
  have hP₀C : P₀ ≤ C := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hcen₀ _ hb z hz
  obtain ⟨k, hkC, hk⟩ := UC6.exists_conj_le_of_isSylowOf
    ((uc22p22qd_isSylowOf_conj hP g).of_le hSC le_top) hP₀C (hP.isPGroup.to_le hP₀P)
  have h1 : ∀ x ∈ P₀, (k * g⁻¹)⁻¹ * x * (k * g⁻¹) ∈ P := by
    intro x hx
    have e : (k * g⁻¹)⁻¹ * x * (k * g⁻¹) = g * (k⁻¹ * x * k) * g⁻¹ := by group
    rw [e]
    exact hk x hx
  have h2 := hwc (k * g⁻¹) h1
  have hn : g * k⁻¹ ∈ normalizer (P₀ : Set G) := by
    refine uc22p22qd_mem_normalizer fun x hx => ?_
    have e : g * k⁻¹ * x * (g * k⁻¹)⁻¹ = (k * g⁻¹)⁻¹ * x * (k * g⁻¹) := by group
    rw [e]
    exact h2 x hx
  have hnab : (g * k⁻¹)⁻¹ * a * (g * k⁻¹) = g⁻¹ * a * g :=
    uc22p22qd_conj_eq (Subgroup.mem_centralizer_iff.1 (C.inv_mem hkC) _ (Set.mem_singleton _))
  have h3 := hN a ha (g * k⁻¹) hn (by rw [hnab]; exact hb)
  rwa [hnab] at h3

end CFSG.LocalAnalysis.UniquenessCase.UC22
