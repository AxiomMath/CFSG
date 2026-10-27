module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16c11_v1_realizes_comp {W W' : Type} [CommGroup W] [CommGroup W']
    {A : Subgroup (MulAut W)} {B : Subgroup (MulAut W')} (e : ↥B →* ↥A)
    (he : Function.Surjective e) {U : Subgroup W} (hU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U)
    {I : Subgroup W'} (s : ↥U →* ↥I) (hs : Function.Surjective s)
    (hequiv : ∀ (b : ↥B) (u : ↥U),
      ((s ⟨((e b : ↥A) : MulAut W) (u : W), hU _ (e b).2 (u : W) u.2⟩ : ↥I) : W') =
        (b : MulAut W') ((s u : ↥I) : W'))
    {D : FFModel} (hR : D.Realizes B I ⊥) :
    D.Realizes A U ((s.ker).map U.subtype) := by
  obtain ⟨π, hπs, -, hkerle, hBI, hBZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hR
  refine ⟨e.comp π, he.comp hπs, Subgroup.map_subtype_le _, hkerle, ?_, ?_, hsec, hkerinv,
    β.comp s, hβs.comp hs, ?_, ?_⟩
  · intro a u hu
    exact hU a a.2 u hu
  · intro a z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨b, hb⟩ := he a
    rw [← hb]
    have hmem : ((e b : ↥A) : MulAut W) (u : W) ∈ U := hU (e b) (e b).2 (u : W) u.2
    refine Subgroup.mem_map.2 ⟨⟨_, hmem⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    refine Subtype.ext ?_
    rw [hequiv b u, MonoidHom.mem_ker.mp hu]
    simp
  · intro u
    rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot]
    constructor
    · intro h1
      refine Subgroup.mem_map.2 ⟨u, MonoidHom.mem_ker.mpr ?_, rfl⟩
      exact Subtype.ext (by simpa using h1)
    · intro hu
      obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hu
      rw [show v = u from Subtype.ext hvu] at hv
      simpa using MonoidHom.mem_ker.mp hv
  · intro γ u m hu hm hbu
    have hu' : ((π γ : ↥B) : MulAut W') ((s u : ↥I) : W') ∈ I := hBI (π γ) (s u) (s u).2
    have hqeq : s ⟨((e.comp π γ : ↥A) : MulAut W) (u : W), hu⟩ =
        ⟨((π γ : ↥B) : MulAut W') ((s u : ↥I) : W'), hu'⟩ :=
      Subtype.ext (by simpa [MonoidHom.comp_apply] using hequiv (π γ) u)
    rw [MonoidHom.comp_apply, hqeq]
    exact hβe γ (s u) m hu' hm (by simpa [MonoidHom.comp_apply] using hbu)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
