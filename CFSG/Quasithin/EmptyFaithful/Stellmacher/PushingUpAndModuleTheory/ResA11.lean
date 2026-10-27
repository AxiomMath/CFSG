module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA10

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X K V₀ : Subgroup G} {c : G}
  (hX : X ≤ Subgroup.normalizer (K : Set G)) (hKd : KData K V₀ c)
  (ψ : ↥X →* Perm (Fin 5)) (hψs : Function.Surjective ψ)
  (hker : ∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ K)

include hX hKd hψs hker in
theorem lemmaX_core (hK2 : IsPGroup 2 K) (hcX : c ∈ X) {l o : G} (hl : l ∈ conjClosure X c)
    (ho : o ∈ normClosure X V₀) {A : Subgroup G} (hAK : A ≤ K)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ a ∈ A, ∀ b ∈ A, a * ((l * o) * b * (l * o)⁻¹) = ((l * o) * b * (l * o)⁻¹) * a := by
  intro a ha b hb
  have haK : a ∈ K := hAK ha
  have hbK : b ∈ K := hAK hb
  obtain ⟨yb, hyb, ob, hob, hbe⟩ := exists_decomp hX hKd ψ hψs hker hK2 hcX hbK
  have hybK : yb ∈ K := hyb.1
  have hlyb : l * yb = yb * l := (Subgroup.mem_centralizer_iff.mp hyb.2 l hl)
  have hlX : l ∈ X := (comm_conjClosure_mem hX hKd hcX hl).1
  have hobK : ob ∈ K := normClosure_le_K hX hKd hob
  have hoK : o ∈ K := normClosure_le_K hX hKd ho
  have hobN : l * ob * l⁻¹ ∈ normClosure X V₀ := conj_mem_normClosure hob hlX
  have hconj : (l * o) * b * (l * o)⁻¹ = yb * (l * ob * l⁻¹) := by
    have h1 : o * b * o⁻¹ = b := by
      rw [(normClosure_central hX hKd ho hbK)]; group
    calc (l * o) * b * (l * o)⁻¹ = l * (o * b * o⁻¹) * l⁻¹ := by group
      _ = l * b * l⁻¹ := by rw [h1]
      _ = l * (yb * ob) * l⁻¹ := by rw [← hbe]
      _ = (l * yb) * ob * l⁻¹ := by group
      _ = (yb * l) * ob * l⁻¹ := by rw [hlyb]
      _ = yb * (l * ob * l⁻¹) := by group
  rw [hconj]
  set z := l * ob * l⁻¹ with hz
  have hzK : z ∈ K := normClosure_le_K hX hKd hobN
  have hza : z * a = a * z := normClosure_central hX hKd hobN haK
  have hoba : ob * a = a * ob := normClosure_central hX hKd hob haK
  have hay : a * yb = yb * a := by
    have h1 := hAc a ha b hb
    rw [hbe] at h1
    have h2 : a * yb * ob = yb * a * ob := by
      calc a * yb * ob = a * (yb * ob) := by group
        _ = (yb * ob) * a := h1
        _ = yb * (ob * a) := by group
        _ = yb * (a * ob) := by rw [hoba]
        _ = yb * a * ob := by group
    exact mul_right_cancel h2
  calc a * (yb * z) = (a * yb) * z := by group
    _ = (yb * a) * z := by rw [hay]
    _ = yb * (a * z) := by group
    _ = yb * (z * a) := by rw [hza]
    _ = yb * z * a := by group

end CFSG.Quasithin.F53
