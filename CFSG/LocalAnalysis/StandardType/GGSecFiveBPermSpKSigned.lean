module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer

public section

namespace CFSG.StandardType

open CFSG.Open

private theorem conj_eq_of_kappa {G S : Type*} [Group G] [Group S] {p n : ℕ}
    {κ : S →* G} (hκ : Function.Injective κ)
    {D : (Fin n → Multiplicative (ZMod p)) →* S}
    {u : S} {b φb : G} {f f' : Fin n → Multiplicative (ZMod p)}
    (hb : ∀ s : S, b * κ s * b⁻¹ = κ (D f * s * (D f)⁻¹))
    (hφ : φb = κ u * b * (κ u)⁻¹)
    (hφ' : ∀ s : S, φb * κ s * φb⁻¹ = κ (D f' * s * (D f')⁻¹))
    (hZ : Subgroup.center S = ⊥) :
    u * D f * u⁻¹ = D f' := by
  have hconj : ∀ s : S,
      (u * D f * u⁻¹) * s * (u * D f * u⁻¹)⁻¹ = D f' * s * (D f')⁻¹ := by
    intro s
    apply hκ
    have hu : (u * D f * u⁻¹) * s * (u * D f * u⁻¹)⁻¹ =
        u * (D f * (u⁻¹ * s * u) * (D f)⁻¹) * u⁻¹ := by group
    rw [hu]
    conv_lhs => rw [map_mul, map_mul, map_inv]
    rw [← hb (u⁻¹ * s * u)]
    calc κ u * (b * κ (u⁻¹ * s * u) * b⁻¹) * (κ u)⁻¹
        = φb * κ s * φb⁻¹ := by
          rw [map_mul, map_mul, map_inv, hφ]
          group
      _ = κ (D f' * s * (D f')⁻¹) := hφ' s
  have hc : (D f')⁻¹ * (u * D f * u⁻¹) ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h2 : ((D f')⁻¹ * (u * D f * u⁻¹)) * s *
        ((D f')⁻¹ * (u * D f * u⁻¹))⁻¹ = s := by
      calc ((D f')⁻¹ * (u * D f * u⁻¹)) * s * ((D f')⁻¹ * (u * D f * u⁻¹))⁻¹
          = (D f')⁻¹ * ((u * D f * u⁻¹) * s * (u * D f * u⁻¹)⁻¹) * D f' := by group
        _ = (D f')⁻¹ * (D f' * s * (D f')⁻¹) * D f' := by rw [hconj s]
        _ = s := by group
    have hcomm : ((D f')⁻¹ * (u * D f * u⁻¹)) * s =
        s * ((D f')⁻¹ * (u * D f * u⁻¹)) := by
      calc ((D f')⁻¹ * (u * D f * u⁻¹)) * s
          = (((D f')⁻¹ * (u * D f * u⁻¹)) * s *
              ((D f')⁻¹ * (u * D f * u⁻¹))⁻¹) *
              ((D f')⁻¹ * (u * D f * u⁻¹)) := by group
        _ = s * ((D f')⁻¹ * (u * D f * u⁻¹)) := by rw [h2]
    exact hcomm.symm
  have hc1 : (D f')⁻¹ * (u * D f * u⁻¹) = 1 := by
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  exact (inv_mul_eq_one.mp hc1).symm

theorem ggSecFiveBPermSpK_signedPerm_of_mem_automizer_of_normalizes {G S : Type} [Group G]
    [Group S] {p r : ℕ} {Bs K : Subgroup G} {κ : S →* G} (hκ : Function.Injective κ)
    (hκK : κ.range = K) (hZ : Subgroup.center S = ⊥)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    (hN : ∀ u : S, (∀ f, ∃ f', u * D f * u⁻¹ = D f') →
      ∃ (π : Equiv.Perm (Fin (r + 1))) (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', u * D f * u⁻¹ = D f' →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i))
    (T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))) (hTs : Function.Surjective T)
    (hT : ∀ (b : ↥Bs) (s : S), (b : G) * κ s * (b : G)⁻¹ = κ (D (T b) * s * (D (T b))⁻¹))
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer K Bs) :
    ∃ (π : Equiv.Perm (Fin (r + 1))) (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ (b : ↥Bs) (i : Fin (r + 1)),
        Multiplicative.toAdd (T (φ b) (π i)) = ε i * Multiplicative.toAdd (T b i) := by
  classical
  obtain ⟨g, hgK, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
  rw [← hκK] at hgK
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hgK
  have hkey : ∀ b : ↥Bs, u * D (T b) * u⁻¹ = D (T (φ b)) := fun b =>
    conj_eq_of_kappa hκ (D := D) (u := u) (b := (b : G)) (φb := (φ b : G))
      (f := T b) (f' := T (φ b)) (fun s => hT b s) (hg b) (fun s => hT (φ b) s) hZ
  obtain ⟨π, ε, hε, hπ⟩ := hN u fun f => by
    obtain ⟨b, rfl⟩ := hTs f
    exact ⟨T (φ b), hkey b⟩
  exact ⟨π, ε, hε, fun b i => hπ (T b) (T (φ b)) (hkey b) i⟩

end CFSG.StandardType

end
