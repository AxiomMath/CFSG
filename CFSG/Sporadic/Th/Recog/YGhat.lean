module

public import CFSG.Sporadic.Th.Recog.YG2
public import CFSG.Quasithin.Recognition.G23Ctx.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Max3

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_ghat_quot (C : ThCore G)
    (hψa : (C.ψ ⟨Max3.z, Max3.z_mem_M⟩ : G) = C.z)
    {tM : ↥Max3.M} (htM : orderOf tM = 3)
    {E₀ : Subgroup ↥Max3.M} {e₀ : ↥Max3.M} (he₀ : e₀ ∈ E₀) (he₀1 : e₀ ≠ 1)
    (he₀z : (e₀ : J) ≠ Max3.z)
    (hE₀c : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hE₀2 : ∀ x ∈ E₀, x * x = 1)
    (hE₀8 : Nat.card E₀ = 8) (hzE₀ : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ E₀)
    (hE₀t : ∀ x ∈ E₀, x * tM = tM * x)
    (hCE : ∀ m : ↥Max3.M, m * tM = tM * m → (∀ x ∈ E₀, m * x = x * m) →
      ∃ x ∈ E₀, ∃ k : ℕ, m = x * tM ^ k)
    (htrans : ∀ w ∈ E₀, w ≠ 1 → (w : J) ≠ Max3.z → ∃ n : ↥Max3.M, n * tM = tM * n ∧
      (∀ x ∈ E₀, n * x * n⁻¹ ∈ E₀) ∧ n * e₀ * n⁻¹ = w)
    (hZt : ∀ w : ↥Max3.M, (w : J) ∈ Max3.Q → w * tM = tM * w → w ≠ 1 → (w : J) ≠ Max3.z →
      ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ q * tM = tM * q ∧ q * w ≠ w * q)
    (hC13 : ∃ g : G, g * C.z * g⁻¹ = (C.ψ e₀ : G) ∧
      ∀ x ∈ E₀, ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ (C.ψ q : G) = g⁻¹ * (C.ψ x : G) * g)
    (hy : ∃ y ∈ Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
      y * (C.ψ e₀ : G) * y⁻¹ = C.z)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    (hG1 : ∃ H H₁ H₂ : Subgroup Y, CFSG.Quasithin.G23Type.G23One H H₁ H₂) :
    Nonempty (Y ≃* CFSG.GH74.QTGen4.Recog.G23.Ghat) := by
  have : Finite Y := Finite.of_surjective π hπ
  exact CFSG.HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_adjointGroup_G2_of_lieModel
    (CFSG.Quasithin.G23Type.Ctx.statementI45_holds Y (isG23Type_quot C hψa htM he₀ he₀1 he₀z
      hE₀c hE₀2 hE₀8 hzE₀ hE₀t hCE htrans hZt hC13 hy π hπ hker hG1))

theorem exists_surjective_ghat (C : ThCore G)
    (hψa : (C.ψ ⟨Max3.z, Max3.z_mem_M⟩ : G) = C.z)
    {tM : ↥Max3.M} (htM : orderOf tM = 3)
    {E₀ : Subgroup ↥Max3.M} {e₀ : ↥Max3.M} (he₀ : e₀ ∈ E₀) (he₀1 : e₀ ≠ 1)
    (he₀z : (e₀ : J) ≠ Max3.z)
    (hE₀c : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hE₀2 : ∀ x ∈ E₀, x * x = 1)
    (hE₀8 : Nat.card E₀ = 8) (hzE₀ : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ E₀)
    (hE₀t : ∀ x ∈ E₀, x * tM = tM * x)
    (hCE : ∀ m : ↥Max3.M, m * tM = tM * m → (∀ x ∈ E₀, m * x = x * m) →
      ∃ x ∈ E₀, ∃ k : ℕ, m = x * tM ^ k)
    (htrans : ∀ w ∈ E₀, w ≠ 1 → (w : J) ≠ Max3.z → ∃ n : ↥Max3.M, n * tM = tM * n ∧
      (∀ x ∈ E₀, n * x * n⁻¹ ∈ E₀) ∧ n * e₀ * n⁻¹ = w)
    (hZt : ∀ w : ↥Max3.M, (w : J) ∈ Max3.Q → w * tM = tM * w → w ≠ 1 → (w : J) ≠ Max3.z →
      ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ q * tM = tM * q ∧ q * w ≠ w * q)
    (hC13 : ∃ g : G, g * C.z * g⁻¹ = (C.ψ e₀ : G) ∧
      ∀ x ∈ E₀, ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ (C.ψ q : G) = g⁻¹ * (C.ψ x : G) * g)
    (hy : ∃ y ∈ Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
      y * (C.ψ e₀ : G) * y⁻¹ = C.z)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    (hG1 : ∃ H H₁ H₂ : Subgroup Y, CFSG.Quasithin.G23Type.G23One H H₁ H₂) :
    ∃ π' : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →*
        CFSG.GH74.QTGen4.Recog.G23.Ghat,
      Function.Surjective π' ∧ π'.ker = Subgroup.zpowers
        ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_ghat_quot C hψa htM he₀ he₀1 he₀z hE₀c hE₀2 hE₀8 hzE₀ hE₀t hCE
    htrans hZt hC13 hy π hπ hker hG1
  exact ⟨e.toMonoidHom.comp π, e.surjective.comp hπ,
    (MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective).trans hker⟩

end CFSG.Sporadic.Th.Recog
