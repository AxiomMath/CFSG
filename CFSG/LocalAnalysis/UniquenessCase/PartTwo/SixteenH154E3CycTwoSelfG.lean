module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoCoreAG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {X : Type} [CommGroup X] {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}
  {q m : ℕ}

theorem s16h_e3_CycTwoSelfG_centralizer_le [Finite X] [Finite (MulAut X)] (hq : q.Prime)
    (F : s16h_CycFrameG q m Mb ψ z U) {D : Subgroup (MulAut ↥U)}
    (hDA : D ≤ autSub (s16h_CycN Mb z) U) (hDe : IsElemAbelian q D)
    (hzD : F.rho ⟨z, F.z_mem_N⟩ ∈ D)
    (hSyl : ∀ a ∈ autSub (s16h_CycN Mb z) U, (∃ k : ℕ, orderOf a = q ^ k) → a ∈ D)
    (hcent : ∀ c ∈ autSub (s16h_CycN Mb z) U,
      c ∈ Subgroup.centralizer (D : Set (MulAut ↥U)) → c ∈ D) :
    Subgroup.centralizer (F.core D : Set (MulAut X)) ⊓ Mb ≤ F.core D := by
  intro g hg
  obtain ⟨hgCent, hgMb⟩ := Subgroup.mem_inf.mp hg
  have hzP : z ∈ F.core D := F.z_mem_core D hzD
  have hzg : z * g = g * z := (Subgroup.mem_centralizer_iff.mp hgCent) z hzP
  have hgz : g * z * g⁻¹ = z := by
    rw [hzg.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : ∀ h ∈ Subgroup.zpowers z, g * h * g⁻¹ = h := by
    rw [Subgroup.forall_mem_zpowers]
    intro k
    rw [← conj_zpow (i := k) (a := g) (b := z), hgz]
  have hfix_inv : ∀ h ∈ Subgroup.zpowers z, g⁻¹ * h * g = h := by
    intro h hh
    have h1 : g⁻¹ * (g * h * g⁻¹) * g = g⁻¹ * h * g :=
      congrArg (fun t => g⁻¹ * t * g) (hfix h hh)
    have h2 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rw [h2] at h1
    exact h1.symm
  have hmemN : g ∈ s16h_CycN Mb z := by
    refine ⟨hgMb, ?_⟩
    refine Subgroup.mem_set_normalizer_iff.mpr fun h => ?_
    constructor
    · intro hh
      rw [hfix h hh]
      exact hh
    · intro hh
      have h1 : g⁻¹ * (g * h * g⁻¹) * g ∈ Subgroup.zpowers z := by
        rw [hfix_inv (g * h * g⁻¹) hh]
        exact hh
      have h2 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      rwa [h2] at h1
  refine ⟨hmemN, ?_⟩
  intro m hmMb hconj
  have hDAP : D ≤ autSub (F.core D) U :=
    s16h_e3_CycTwoCoreAG_le_autSub hq F hDA hDe hSyl
  have hmemAut : F.rho ⟨m⁻¹ * g * m, hconj⟩ ∈ autSub (s16h_CycN Mb z) U := by
    rw [← F.rho_range]
    exact ⟨⟨m⁻¹ * g * m, hconj⟩, rfl⟩
  have hmemCent : F.rho ⟨m⁻¹ * g * m, hconj⟩ ∈
      Subgroup.centralizer (D : Set (MulAut ↥U)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨g', hg'P, hg'eq⟩ := mem_autSub.mp (hDAP hd)
    have hyN : (g' : MulAut X) ∈ s16h_CycN Mb z := F.core_le_N D hg'P
    have hxy : (m⁻¹ * g * m) * (g' : MulAut X) = (g' : MulAut X) * (m⁻¹ * g * m) := by
      have hy' : m * (g' : MulAut X) * m⁻¹ ∈ F.core D := F.conj_mem_core D hmMb hg'P
      have hcomm : (m * (g' : MulAut X) * m⁻¹) * g =
          g * (m * (g' : MulAut X) * m⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hgCent) _ hy'
      calc (m⁻¹ * g * m) * (g' : MulAut X)
          = m⁻¹ * (g * (m * (g' : MulAut X) * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * (g' : MulAut X) * m⁻¹) * g) * m := by rw [← hcomm]
        _ = (g' : MulAut X) * (m⁻¹ * g * m) := by group
    have hd_eq : F.rho ⟨(g' : MulAut X), hyN⟩ = d := by
      rw [← hg'eq]
      refine MulEquiv.ext fun u => Subtype.ext ?_
      rw [F.rho_apply, resHom_apply]
    have hcommN : (⟨m⁻¹ * g * m, hconj⟩ : ↥(s16h_CycN Mb z)) *
        ⟨(g' : MulAut X), hyN⟩ =
        ⟨(g' : MulAut X), hyN⟩ * ⟨m⁻¹ * g * m, hconj⟩ := Subtype.ext hxy
    rw [← hd_eq, ← map_mul, ← map_mul, hcommN]
  exact hcent _ hmemAut hmemCent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
