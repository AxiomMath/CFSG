module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcPacket

open CFSG.StandardType CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable
  {X : Type} [Group X] {τ : CFSG.Blueprint.Chevalley.Tag} {f p : ℕ}
  {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X}
  (P : ExcPacket τ f p G₀ B₁ D J x R Rm)

include P in
theorem x_mem : x ∈ D := by
  rw [← P.closure_eq]
  exact Subgroup.subset_closure (by simp)

theorem coord_mul (hDB : D ≤ B₁) {a b : X} (ha : a ∈ D) (hb : b ∈ D) :
    P.coord (a * b) = P.coord a * P.coord b := by
  apply rootDiagUnit_injective (τ := τ) (K := ExcOmega f)
  have h1 : P.Θ (⟨a * b, hDB (mul_mem ha hb)⟩ : ↥B₁) =
      rootDiagUnit τ (P.coord (a * b)) := P.Θ_eq_coord _ (mul_mem ha hb)
  have h2 : P.Θ (⟨a, hDB ha⟩ : ↥B₁) = rootDiagUnit τ (P.coord a) := P.Θ_eq_coord _ ha
  have h3 : P.Θ (⟨b, hDB hb⟩ : ↥B₁) = rootDiagUnit τ (P.coord b) := P.Θ_eq_coord _ hb
  have hmul : P.Θ (⟨a * b, hDB (mul_mem ha hb)⟩ : ↥B₁) =
      P.Θ (⟨a, hDB ha⟩ : ↥B₁) * P.Θ (⟨b, hDB hb⟩ : ↥B₁) :=
    map_mul P.Θ ⟨a, hDB ha⟩ ⟨b, hDB hb⟩
  rw [h1, h2, h3] at hmul
  rw [hmul, rootDiagUnit_mul]

private theorem excPB_coord_one : P.coord (1 : X) = 1 := by
  apply rootDiagUnit_injective (τ := τ) (K := ExcOmega f)
  have h := P.Θ_eq_coord (1 : ↥B₁) (one_mem D)
  rw [map_one] at h
  simpa [Subgroup.coe_one, rootDiagUnit_one] using h.symm

private theorem excPB_coord_inv (hDB : D ≤ B₁) {a : X} (ha : a ∈ D) :
    P.coord a⁻¹ = (P.coord a)⁻¹ := by
  apply rootDiagUnit_injective (τ := τ) (K := ExcOmega f)
  have h1 : P.Θ (⟨a⁻¹, hDB (inv_mem ha)⟩ : ↥B₁) = rootDiagUnit τ (P.coord a⁻¹) :=
    P.Θ_eq_coord _ (inv_mem ha)
  have h2 : P.Θ (⟨a, hDB ha⟩ : ↥B₁) = rootDiagUnit τ (P.coord a) := P.Θ_eq_coord _ ha
  have hinv : P.Θ (⟨a⁻¹, hDB (inv_mem ha)⟩ : ↥B₁) =
      (P.Θ (⟨a, hDB ha⟩ : ↥B₁))⁻¹ := by
    rw [show (⟨a⁻¹, hDB (inv_mem ha)⟩ : ↥B₁) = (⟨a, hDB ha⟩ : ↥B₁)⁻¹ from rfl, map_inv]
  rw [h1, h2, rootDiagUnit_inv] at hinv
  exact hinv

private theorem excPB_rootChar_coord_eq_one (hDB : D ≤ B₁) {γ : Fin τ.rank → ℤ}
    (hx : rootChar (P.coord x) γ = 1) (hd : rootChar (P.coord P.d) γ = 1)
    {e : X} (he : e ∈ D) : rootChar (P.coord e) γ = 1 := by
  have hmul : ∀ {a b : X}, a ∈ D → b ∈ D →
      rootChar (P.coord (a * b)) γ = rootChar (P.coord a) γ * rootChar (P.coord b) γ := by
    intro a b ha hb
    rw [P.coord_mul hDB ha hb]
    simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  have hinv : ∀ {a : X}, a ∈ D →
      rootChar (P.coord a⁻¹) γ = (rootChar (P.coord a) γ)⁻¹ := by
    intro a ha
    rw [excPB_coord_inv P hDB ha]
    simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]
  rw [← P.closure_eq] at he
  induction he using Subgroup.closure_induction with
  | mem y hy =>
      rcases (by simpa using hy) with rfl | rfl
      · exact hx
      · exact hd
  | one => rw [excPB_coord_one P]; simp [rootChar]
  | mul a b ha hb iha ihb =>
      have haD : a ∈ D := by rw [← P.closure_eq]; exact ha
      have hbD : b ∈ D := by rw [← P.closure_eq]; exact hb
      rw [hmul haD hbD, iha, ihb, mul_one]
  | inv a ha iha =>
      have haD : a ∈ D := by rw [← P.closure_eq]; exact ha
      rw [hinv haD, iha, inv_one]

private theorem excPB_jointChar_ofAdd_eq_one_iff {a₁ a₂ : Fin τ.rank → (ExcOmega f)ˣ}
    {γ : Fin τ.rank → ℤ} :
    LieCore.jointChar a₁ a₂ (Multiplicative.ofAdd γ) = 1 ↔
      rootChar a₁ γ = 1 ∧ rootChar a₂ γ = 1 := by
  simp [LieCore.jointChar, CFSG.LieType.AlgebraicGroups.rootCharHom]

theorem kernelRoots_chiD_subset (hDB : D ≤ B₁) {e : X} (he : e ∈ D) :
    kernelRoots P.chiD ⊆ kernelRoots (P.chiAt e) := by
  intro γ hγ
  obtain ⟨hroot, hchar⟩ := hγ
  have hpair : rootChar (P.coord x) γ = 1 ∧ rootChar (P.coord P.d) γ = 1 := by
    simpa [ExcPacket.chiD, excPB_jointChar_ofAdd_eq_one_iff] using hchar
  have hcoord : rootChar (P.coord e) γ = 1 :=
    excPB_rootChar_coord_eq_one P hDB hpair.1 hpair.2 he
  exact ⟨hroot, by simpa [ExcPacket.chiAt,
    CFSG.LieType.AlgebraicGroups.rootCharHom] using hcoord⟩

theorem mapsTo_rho_chiAt {e : X} (he : e ∈ D) :
    Set.MapsTo P.ρ (kernelRoots (P.chiAt e)) (kernelRoots (P.chiAt e)) := by
  intro γ hγ
  obtain ⟨hroot, hchar⟩ := hγ
  have hchar' : rootChar (P.coord e) γ = 1 := by
    simpa [ExcPacket.chiAt, CFSG.LieType.AlgebraicGroups.rootCharHom] using hchar
  refine ⟨(P.frob.isRoot_iff γ).2 hroot, ?_⟩
  have hq : rootChar (P.coord e) (P.ρ γ) = 1 := by
    rw [P.frob.rootChar_eq (P.coord e) (P.coord_torus e he) γ hroot, hchar', one_pow]
  simpa [ExcPacket.chiAt, CFSG.LieType.AlgebraicGroups.rootCharHom] using hq

theorem mapsTo_rho_chiD : Set.MapsTo P.ρ (kernelRoots P.chiD) (kernelRoots P.chiD) := by
  intro γ hγ
  obtain ⟨hroot, hchar⟩ := hγ
  have hpair : rootChar (P.coord x) γ = 1 ∧ rootChar (P.coord P.d) γ = 1 := by
    simpa [ExcPacket.chiD, excPB_jointChar_ofAdd_eq_one_iff] using hchar
  refine ⟨(P.frob.isRoot_iff γ).2 hroot, ?_⟩
  have hx : rootChar (P.coord x) (P.ρ γ) = 1 := by
    rw [P.frob.rootChar_eq (P.coord x) (P.coord_torus x (x_mem P)) γ hroot, hpair.1, one_pow]
  have hd : rootChar (P.coord P.d) (P.ρ γ) = 1 := by
    rw [P.frob.rootChar_eq (P.coord P.d) (P.coord_torus P.d P.d_mem) γ hroot, hpair.2,
      one_pow]
  have hpair' : rootChar (P.coord x) (P.ρ γ) = 1 ∧
      rootChar (P.coord P.d) (P.ρ γ) = 1 := ⟨hx, hd⟩
  simpa [ExcPacket.chiD, excPB_jointChar_ofAdd_eq_one_iff] using hpair'

theorem b_eq_one_or_two : P.b = 1 ∨ P.b = 2 := by
  rcases P.orbit with h | ⟨h, _⟩
  · exact Or.inl (by simpa [ExcPacket.b, ExcPacket.rootsJ, ExcPacket.chiD] using h)
  · exact Or.inr (by simpa [ExcPacket.b, ExcPacket.rootsJ, ExcPacket.chiD] using h)

theorem image_rootsJ_ne_of_b_eq_two (h : P.b = 2) :
    (P.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' P.rootsJ ≠ P.rootsJ := by
  intro himg
  have hmem : 1 ∈ {s : ℕ | 0 < s ∧
      (P.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' P.rootsJ = P.rootsJ} := by
    refine ⟨Nat.one_pos, ?_⟩
    rwa [Function.iterate_one]
  have hle : P.b ≤ 1 := by
    simpa [ExcPacket.b, componentOrbitLength] using Nat.sInf_le hmem
  omega

end CFSG.StandardType.LieKnownR2.ExcPos.ExcPacket

end
