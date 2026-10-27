module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem tail1812Two_exists_section {K H L : Subgroup G} (hL : IsComponentModN K H L) {Y : Type}
    [Group Y] {π : ↥H →* Y} (hπs : Function.Surjective π)
    (hπk : ∀ h : ↥H, π h = 1 → (h : G) ∈ K) {Kk : Subgroup Y}
    (hmem : ∀ h : ↥H, π h ∈ Kk ↔ (h : G) ∈ K) {X : Type} [Group X] (φ : ↥L →* X)
    (hφs : Function.Surjective φ) (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ K) :
    ∃ φ' : ↥((L.subgroupOf H).map π) →* X, Function.Surjective φ' ∧
      (∀ k : ↥((L.subgroupOf H).map π), φ' k = 1 ↔ (k : Y) ∈ Kk) ∧
        ((L.subgroupOf H).map π).IsSubnormal := by
  obtain ⟨-, -, hLH, hsub, -⟩ := hL
  have hsub' : (L.subgroupOf H).IsSubnormal := CFSG.Open.IsSubnormal.subgroupOf hsub
  have hsubc : ((L.subgroupOf H).map π).IsSubnormal := hsub'.map hπs
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  let ψ : ↥(L.subgroupOf H) →* X := φ.comp (e : ↥(L.subgroupOf H) →* ↥L)
  let ρ : ↥(L.subgroupOf H) →* ↥((L.subgroupOf H).map π) :=
    (π.comp (L.subgroupOf H).subtype).codRestrict ((L.subgroupOf H).map π)
      (fun x => Subgroup.mem_map_of_mem π x.2)
  have hρs : Function.Surjective ρ := by
    intro k
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.1 k.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxk⟩
  have hρval : ∀ x : ↥(L.subgroupOf H), (ρ x : Y) = π (x : ↥H) := fun _ => rfl
  have heval : ∀ x : ↥(L.subgroupOf H), ((e x : ↥L) : G) = ((x : ↥H) : G) := fun _ => rfl
  have hker : ρ.ker ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxY : (ρ x : Y) = 1 :=
      congrArg (fun z : ↥((L.subgroupOf H).map π) => (z : Y)) hx
    have hxπ : π (x : ↥H) = 1 := by rw [← hρval x]; exact hxY
    have hxK : ((x : ↥H) : G) ∈ K := hπk (x : ↥H) hxπ
    show φ (e x) = 1
    exact (hφk (e x)).2 (by rw [heval x]; exact hxK)
  let φ' : ↥((L.subgroupOf H).map π) →* X :=
    MonoidHom.liftOfSurjective ρ hρs ⟨ψ, hker⟩
  have hφ'ρ : ∀ x, φ' (ρ x) = ψ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ρ (Function.surjInv hρs)
      (Function.rightInverse_surjInv hρs) ⟨ψ, hker⟩ x
  refine ⟨φ', ?_, ?_, hsubc⟩
  · intro x
    obtain ⟨l, rfl⟩ := hφs x
    refine ⟨ρ (e.symm l), ?_⟩
    rw [hφ'ρ]
    show φ (e (e.symm l)) = φ l
    rw [MulEquiv.apply_symm_apply]
  · intro k
    obtain ⟨x, rfl⟩ := hρs k
    rw [hφ'ρ]
    show φ (e x) = 1 ↔ ((ρ x : ↥((L.subgroupOf H).map π)) : Y) ∈ Kk
    rw [hφk]
    exact (hmem (x : ↥H)).symm

end CFSG.LocalAnalysis.WeakClosure81

end
