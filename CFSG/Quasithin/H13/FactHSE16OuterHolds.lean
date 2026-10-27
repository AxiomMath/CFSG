module

public import CFSG.Quasithin.H13.HSLocE16
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.RankThree.Native CFSG.Open

theorem factHSE16Outer_holds :
    CFSG.Quasithin.H13.FactHSE16Outer := by
  intro X _ _ hXe B P E hA A hA7 hAprops
  obtain ⟨φ⟩ := hXe
  let ψ : X ≃* PG := φ.trans hs100Equiv
  let E' : Subgroup PG := E.map ψ.toMonoidHom
  let B' : Subgroup PG := B.map ψ.toMonoidHom
  let P' : Subgroup PG := P.map ψ.toMonoidHom
  have hperf : ⁅B', B'⁆ = B' := by
    rw [← Subgroup.map_commutator, hA.perfect]
  have hcardB : Nat.card B' = 360 * Nat.card P' := by
    rw [Subgroup.card_map_of_injective ψ.injective, Subgroup.card_map_of_injective ψ.injective]
    exact hA.card
  have hEP : E' ≤ P' := Subgroup.map_mono hA.le_P
  have hEab : IsElemAbelian 2 E' := CFSG.Open.IsElemAbelian.map hA.elemAbelian _
  have hEcard : Nat.card E' = 16 := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hA.card_E
  have hBnorm : B' ≤ Subgroup.normalizer (E' : Set PG) := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    have hbn := Subgroup.mem_normalizer_iff.mp (hA.normalizes_E hb₀)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e1 : h ∈ E' ↔ ψ.symm h ∈ E := Subgroup.mem_map_equiv
    have e2 : ψ.toMonoidHom b₀ * h * (ψ.toMonoidHom b₀)⁻¹ ∈ E' ↔ b₀ * ψ.symm h * b₀⁻¹ ∈ E := by
      rw [show E' = E.map ψ.toMonoidHom from rfl, Subgroup.mem_map_equiv]
      simp
    rw [e1, e2]
    exact hbn (ψ.symm h)
  let c : MulAut X → MulAut PG := fun α => ψ.symm.trans (α.trans ψ)
  have hcapply : ∀ (α : MulAut X) (x : X), c α (ψ x) = ψ (α x) := by
    intro α x
    show ψ (α (ψ.symm (ψ x))) = ψ (α x)
    rw [MulEquiv.symm_apply_apply]
  have hcinj : Function.Injective c := by
    intro α β hαβ
    apply MulEquiv.ext
    intro x
    have := hcapply α x
    rw [hαβ, hcapply β x] at this
    exact ψ.injective this.symm
  classical
  let A' : Finset (MulAut PG) := A.image c
  have hA'card : 7 ≤ A'.card := by
    rw [Finset.card_image_of_injective _ hcinj]
    exact hA7
  have hA'prop : ∀ β ∈ A', (∀ z ∈ E', β z = z) ∧ ∀ z ∈ E', β ≠ MulAut.conj z := by
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hβ
    obtain ⟨hαE, hαconj⟩ := hAprops α hα
    refine ⟨fun z hz => ?_, fun z hz hcz => ?_⟩
    · obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
      show c α (ψ z₀) = ψ z₀
      rw [hcapply, hαE z₀ hz₀]
    · obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
      refine hαconj z₀ hz₀ (MulEquiv.ext fun x => ψ.injective ?_)
      have h1 := hcapply α x
      rw [hcz] at h1
      rw [← h1]
      simp [MulAut.conj_apply]
  obtain ⟨β, hβA', hsimple, hcard⟩ :=
    e16Outer_PG hperf hcardB hEP hEab hEcard hBnorm A' hA'card hA'prop
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hβA'
  refine ⟨α, hα, ?_⟩
  have hAC : autCentralizer (c α) = (autCentralizer α).map ψ.toMonoidHom := by
    ext p
    rw [show p ∈ (autCentralizer α).map ψ.toMonoidHom ↔ ψ.symm p ∈ autCentralizer α from
      Subgroup.mem_map_equiv]
    show c α p = p ↔ α (ψ.symm p) = ψ.symm p
    have h1 := hcapply α (ψ.symm p)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    constructor
    · intro h; exact ψ.injective (by rw [MulEquiv.apply_symm_apply]; exact h)
    · intro h; rw [h, MulEquiv.apply_symm_apply]
  have hpc : perfectCore (autCentralizer (c α)) =
      (perfectCore (autCentralizer α)).map ψ.toMonoidHom := by
    rw [hAC, map_perfectCore]
  rw [hpc] at hsimple hcard
  refine ⟨?_, ?_⟩
  · haveI := hsimple
    exact ((perfectCore (autCentralizer α)).equivMapOfInjective ψ.toMonoidHom ψ.injective).isSimpleGroup
  · rw [Subgroup.card_map_of_injective ψ.injective] at hcard
    exact hcard

end CFSG.Quasithin.H13.LocDbl.HSLoc
