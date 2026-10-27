module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F08

private theorem k891hnorm_opp_le {G : Type} [Group G] (p : ℕ) (Y : Subgroup G) :
    Opp p Y ≤ Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact (Subgroup.closure_le Y).mpr fun x hx => hx.1

private theorem k891hnorm_derInf8_le {G : Type} [Group G] (Y : Subgroup G) : DerInf8 Y ≤ Y := by
  unfold DerInf8
  exact Subgroup.map_subtype_le _

private theorem k891hnorm_opp_map_conj {G : Type} [Group G] (p : ℕ) (C : Subgroup G) (k : G)
    (hC : C.map (MulAut.conj k).toMonoidHom = C) :
    (Opp p C).map (MulAut.conj k).toMonoidHom = Opp p C := by
  have h := CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy p k C
  simp only [CFSG.RankThree.PartOne.conjBy] at h
  rw [hC] at h
  exact h.symm

private theorem k891hnorm_derInf8_map_conj {G : Type} [Group G] (C : Subgroup G) (k : G)
    (hC : C.map (MulAut.conj k).toMonoidHom = C) :
    (DerInf8 C).map (MulAut.conj k).toMonoidHom = DerInf8 C := by
  have hk : k ∈ Subgroup.normalizer (C : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hC
  have hk' : k ∈ Subgroup.normalizer ((DerInf8 C : Subgroup G) : Set G) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map C hk
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hk'

private theorem k891hnorm_C_map_conj {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (hbasic : R891Basic D L S) (k : G) (hk : k ∈ R891H L S ⊓ D.M) :
    (L ⊓ Subgroup.centralizer (R891Z L S : Set G)).map (MulAut.conj k).toMonoidHom =
      L ⊓ Subgroup.centralizer (R891Z L S : Set G) := by
  have hkH : k ∈ R891H L S := hk.1
  have hkM : k ∈ D.M := hk.2
  have hLmap : L.map (MulAut.conj k).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hbasic.normal hkM)
  have hZmap : (R891Z L S).map (MulAut.conj k).toMonoidHom = R891Z L S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer (R891Z L S : Set G) hkH)
  have hCentMap : (Subgroup.centralizer (R891Z L S : Set G)).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer (R891Z L S : Set G) := by
    have h := CFSG.RankThree.PartOne.Equivariance.centralizer_conjBy k (R891Z L S)
    simp only [CFSG.RankThree.PartOne.conjBy] at h
    rw [hZmap] at h
    exact h.symm
  rw [Subgroup.map_inf L (Subgroup.centralizer (R891Z L S : Set G))
    (MulAut.conj k).toMonoidHom (MulAut.conj k).injective, hLmap, hCentMap]

private theorem k891hnorm_X_map_conj {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (n : ℕ) (hbasic : R891Basic D L S)
    (k : G) (hk : k ∈ R891H L S ⊓ D.M) :
    (R891X L (R891Z L S) n).map (MulAut.conj k).toMonoidHom = R891X L (R891Z L S) n := by
  have hCmap := k891hnorm_C_map_conj D L S hbasic k hk
  unfold R891X
  split_ifs with hn
  · exact k891hnorm_opp_map_conj 2 _ k hCmap
  · exact k891hnorm_derInf8_map_conj _ k hCmap

private theorem k891hnorm_X_conj_mem {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (n : ℕ) (hbasic : R891Basic D L S)
    (k : G) (hk : k ∈ R891H L S ⊓ D.M) {x : G} (hx : x ∈ R891X L (R891Z L S) n) :
    k * x * k⁻¹ ∈ R891X L (R891Z L S) n := by
  have hmap := k891hnorm_X_map_conj D L S n hbasic k hk
  have hmem : (MulAut.conj k).toMonoidHom x ∈
      (R891X L (R891Z L S) n).map (MulAut.conj k).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [hmap] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem s891_h_norm {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) (n : ℕ)
    (hset : R891Set D L S n) (hbasic : R891Basic D L S) :
    R891Norm895 D L S n := by
  classical
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hset.mem.1
  have hXleC : R891X L (R891Z L S) n ≤ L ⊓ Subgroup.centralizer (R891Z L S : Set G) := by
    unfold R891X
    split_ifs with hn
    · exact k891hnorm_opp_le 2 _
    · exact k891hnorm_derInf8_le _
  have hXleM : R891X L (R891Z L S) n ≤ D.M := (hXleC.trans inf_le_left).trans hLM
  have hImgLe : R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤
      R891Img (R891H L S) (R891Z L S) D.M := by
    rw [R891Img, R891Img]
    apply Subgroup.map_mono
    intro x hx
    exact hXleM hx
  unfold R891Norm895
  constructor
  · exact hImgLe
  · rw [Subgroup.normal_subgroupOf_iff hImgLe]
    intro a b ha hb
    rw [R891Img, Subgroup.mem_map] at ha
    rw [R891Img, Subgroup.mem_map] at hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨m, hm, rfl⟩ := hb
    rw [R891Img]
    refine Subgroup.mem_map.mpr ⟨m * x * m⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hmH : (m : G) ∈ R891H L S := m.2
      have hmM : (m : G) ∈ D.M := hm
      have hxX : (x : G) ∈ R891X L (R891Z L S) n := hx
      have hconj := k891hnorm_X_conj_mem D L S n hbasic (m : G) ⟨hmH, hmM⟩ hxX
      simpa using hconj
    · simp

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
