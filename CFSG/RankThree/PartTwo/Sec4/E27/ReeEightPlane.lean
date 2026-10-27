module

public import CFSG.RankThree.PartTwo.Sec4.E27.ReeEightCover
public import CFSG.RankThree.PartTwo.Sec4.E27.ReeEightGen
public import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits HuppertReeEight CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27.ReeEight

@[expose] def ReeEightChecks : Prop :=
  sylowCheck () = true ∧ coverCheck () = true ∧ genCheck () = true

section Plane


theorem conj_comm {g k u : ↥titsA} (h : k * u = u * k) :
    (g⁻¹ * k * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * k * g) := by
  calc (g⁻¹ * k * g) * (g⁻¹ * u * g) = g⁻¹ * (k * u) * g := by group
    _ = g⁻¹ * (u * k) * g := by rw [h]
    _ = (g⁻¹ * u * g) * (g⁻¹ * k * g) := by group

theorem conj_ne_one {g u : ↥titsA} (h : u ≠ 1) : g⁻¹ * u * g ≠ 1 := by
  intro h1
  apply h
  have := congrArg (fun z => g * z * g⁻¹) h1
  simpa [mul_assoc] using this

theorem titsA_plane_closure (hc : ReeEightChecks) {E : Subgroup ↥titsA} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 9) :
    Subgroup.closure {k : ↥titsA | ∃ b ∈ E, b ≠ 1 ∧ k * b = b * k} = ⊤ := by
  obtain ⟨hs, hcv, hg⟩ := hc
  have hE' : CFSG.IsElementaryAbelian 3 E := isElemAbelian_iff_isElementaryAbelian.mp hE
  obtain ⟨g, d, hd, hu, hv⟩ := planeCover_of_checks hs hcv hE' (by rw [hcard]; norm_num)
  obtain ⟨hpl, -⟩ := coverCheck_spec hcv
  obtain ⟨hlu, hlv, hpair⟩ := hpl d hd
  obtain ⟨hu1, -, -, -, hvn⟩ := (isPairE_iff (rep_valA hlu) (rep_valA hlv)).1 hpair
  have hv1 : valA d.v ≠ 1 := fun h1 => hvn (Or.inl h1)
  set F : Subgroup ↥titsA := Subgroup.closure {k : ↥titsA | ∃ b ∈ E, b ≠ 1 ∧ k * b = b * k} with hF
  let F' : Subgroup ↥titsA := F.comap (MulAut.conj g⁻¹).toMonoidHom
  have hmemF' : ∀ t : ↥titsA, t ∈ F' ↔ g⁻¹ * t * g ∈ F := fun t => by
    simp [F', Subgroup.mem_comap, MulAut.conj_apply]
  have hF1 : ∀ k : ↥titsA, k * valA d.u = valA d.u * k → k ∈ F' := fun k hk =>
    (hmemF' k).2 (Subgroup.subset_closure ⟨g⁻¹ * valA d.u * g, hu, conj_ne_one hu1, conj_comm hk⟩)
  have hF2 : ∀ k : ↥titsA, k * valA d.v = valA d.v * k → k ∈ F' := fun k hk =>
    (hmemF' k).2 (Subgroup.subset_closure ⟨g⁻¹ * valA d.v * g, hv, conj_ne_one hv1, conj_comm hk⟩)
  have htop : F' = ⊤ := eq_top_of_genCheck hg hd hlu hlv hF1 hF2
  rw [eq_top_iff]
  intro s _
  have hs' : g * s * g⁻¹ ∈ F' := by
    rw [htop]
    trivial
  have := (hmemF' _).1 hs'
  simpa [mul_assoc] using this

end Plane

end CFSG.RankThree.PartTwo.Sec4.E27.ReeEight
