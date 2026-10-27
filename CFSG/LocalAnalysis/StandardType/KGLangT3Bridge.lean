module

public import CFSG.LocalAnalysis.StandardType.KGLangT3Defs
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineComponent
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)


private theorem l02qjbr_isComponentOf_map_of_injective {G G' : Type} [Group G] [Group G']
    (f : G →* G') (hf : Function.Injective f) {L K : Subgroup G}
    (h : IsComponentOf L K) : IsComponentOf (L.map f) (K.map f) := by
  obtain ⟨hLK, hsub, hq⟩ := h
  exact ⟨Subgroup.map_mono hLK, IsSubnormal.map f hsub,
    Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective L f hf).symm hq⟩

private lemma l02qjbr_map_symm_eq_comap {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (N : Subgroup H) :
    N.map e.symm.toMonoidHom = N.comap e.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [Subgroup.mem_comap]
    simpa using hn
  · intro hx
    rw [Subgroup.mem_comap] at hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩

private lemma l02qjbr_subgroupOf_map_eq {n : ℕ} (K : Type) [Field K] (k : Type) [Field k]
    [Algebra k K] (D : TriD4LineKGXData n K k) (J₀ : Subgroup (GGTriD4R n K))
    (hJ : IsComponentOf J₀ (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))) :
    (J₀.subgroupOf (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))).map
        D.Θ.toMonoidHom = triD4LineN0 k K := by
  have hcomp : IsComponentOf
      (J₀.subgroupOf (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact IsSubnormal.of_mathlib (IsSubnormal.subgroupOf hJ.2.1)
    · exact Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ.1) hJ.2.2
  have hcompmap : IsComponentOf
      ((J₀.subgroupOf (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))).map
        D.Θ.toMonoidHom) ⊤ := by
    have h := l02qjbr_isComponentOf_map_of_injective D.Θ.toMonoidHom D.Θ.injective hcomp
    simpa [Subgroup.map_top, MulEquiv.range_eq_top] using h
  exact (triD4LineN0_unique_component k K _).mp hcompmap

private lemma l02qjbr_alpha_mem_centralizer {n : ℕ} {K : Type} [Field K] {k : Type} [Field k]
    [Algebra k K] (D : TriD4LineKGXData n K k) (y : GGTriD4R n K)
    (hy : y ∈ Subgroup.centralizer {D.z₀}) :
    D.α y ∈ Subgroup.centralizer {D.z₀} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  calc D.α y * D.z₀ = D.α (y * D.z₀) := by rw [map_mul, D.α_z₀]
    _ = D.α (D.z₀ * y) := by rw [hy]
    _ = D.z₀ * D.α y := by rw [map_mul, D.α_z₀]

private theorem l02qjbr_slKerEquiv_conjNormal {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (h : LargeEvenSLGroup (Fin d) K) :
    TypeA.slKerEquiv d K (MulAut.conjNormal A h) =
      slConjugation d K A (TypeA.slKerEquiv d K h) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hc : ∀ h : LargeEvenSLGroup (Fin d) K,
      Matrix.SpecialLinearGroup.toGL (TypeA.slKerEquiv d K h) = (h : GL (Fin d) K) :=
    fun h => Units.ext (TypeA.coe_slKerEquiv h)
  rw [toGL_slConjugation, hc, hc, MulAut.conjNormal_apply]

private theorem l02qjbr_recipeEquiv_linConjAut {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (x : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    TypeA.recipeEquiv d K (TableB.linConjAut (Fin d) K A x) =
      LinearFlag.conjAut d K A (TypeA.recipeEquiv d K x) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  rw [TableB.linConjAut_mk]
  rw [show (TypeA.recipeEquiv d K) (↑(MulAut.conjNormal A h)) =
      LinearFlag.proj d K (TypeA.slKerEquiv d K (MulAut.conjNormal A h))
    from TypeA.recipeEquiv_mk (MulAut.conjNormal A h)]
  rw [show (TypeA.recipeEquiv d K) (↑h) = LinearFlag.proj d K (TypeA.slKerEquiv d K h)
    from TypeA.recipeEquiv_mk h]
  rw [LinearFlag.conjAut_proj, l02qjbr_slKerEquiv_conjNormal]

theorem kgLangT3_component_eq {n : ℕ} (K : Type) [Field K] (k : Type) [Field k] [Algebra k K]
    (D : TriD4LineKGXData n K k) (J₀ : Subgroup (GGTriD4R n K))
    (hJ : IsComponentOf J₀ (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))) :
    ∀ (y : GGTriD4R n K) (hy : y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))),
      y ∈ J₀ ↔ (D.Θ ⟨y, hy⟩ : TriD4LineX k K) ∈ triD4LineN0 k K := by
  intro y hy
  have hN0 := l02qjbr_subgroupOf_map_eq K k D J₀ hJ
  rw [← hN0]
  constructor
  · intro hyJ
    rw [Subgroup.mem_map]
    exact ⟨⟨y, hy⟩, by rwa [Subgroup.mem_subgroupOf], rfl⟩
  · intro hΘ
    rw [Subgroup.mem_map] at hΘ
    obtain ⟨a, ha, haeq⟩ := hΘ
    have hay : a = ⟨y, hy⟩ := D.Θ.injective haeq
    rw [hay] at ha
    rwa [Subgroup.mem_subgroupOf] at ha

theorem kgLangT3_exists_component {n : ℕ} (K : Type) [Field K] (k : Type) [Field k] [Algebra k K]
    (D : TriD4LineKGXData n K k) :
    ∃ J₀ : Subgroup (GGTriD4R n K),
      IsComponentOf J₀ (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))) := by
  let C : Subgroup (GGTriD4R n K) := Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))
  let N : Subgroup (TriD4LineX k K) := triD4LineN0 k K
  have hN0comp : IsComponentOf N ⊤ := (triD4LineN0_unique_component k K N).mpr rfl
  have hcompL : IsComponentOf (N.comap D.Θ.toMonoidHom) ⊤ := by
    have h := l02qjbr_isComponentOf_map_of_injective D.Θ.symm.toMonoidHom D.Θ.symm.injective
      hN0comp
    rw [l02qjbr_map_symm_eq_comap D.Θ N] at h
    simpa [Subgroup.map_top, MulEquiv.range_eq_top] using h
  refine ⟨(N.comap D.Θ.toMonoidHom).map C.subtype, ?_⟩
  have h := l02qjbr_isComponentOf_map_of_injective C.subtype C.subtype_injective hcompL
  simpa [C, Subgroup.map_top, Subgroup.range_subtype] using h

theorem kgLangT3_alpha_fix_component {n : ℕ} (K : Type) [Field K] (k : Type) [Field k]
    [Algebra k K] (D : TriD4LineKGXData n K k) (J₀ : Subgroup (GGTriD4R n K))
    (hJ : IsComponentOf J₀ (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))) :
    ∀ j ∈ J₀, D.α j = j := by
  intro j hj
  have hJle : j ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := hJ.1 hj
  have hα : D.α j ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) :=
    l02qjbr_alpha_mem_centralizer D j hJle
  have hΘj : (D.Θ ⟨j, hJle⟩ : TriD4LineX k K) ∈ triD4LineN0 k K :=
    (kgLangT3_component_eq K k D J₀ hJ j hJle).mp hj
  have hfix : D.Θ ⟨D.α j, hα⟩ = D.Θ ⟨j, hJle⟩ := by
    rw [D.Θ_α ⟨j, hJle⟩ hα, triD4LineSigma_eq_self_of_mem_N0 k K D.σ hΘj]
  exact congrArg Subtype.val (D.Θ.injective hfix)

theorem kgLangT3_N0_equiv_psl3 (k K : Type) [Field k] [Field K] [Algebra k K] :
    ∃ ι : ↥(triD4LineN0 k K) ⧸ Subgroup.center ↥(triD4LineN0 k K) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin 3) k),
      ∀ (g : GL (Fin 3) k) (c : Kˣ)
        (hdet : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
        (m m' : ↥(triD4LineN0 k K)),
        (m' : TriD4LineX k K) =
            triD4LineMk k K g c hdet * m * (triD4LineMk k K g c hdet)⁻¹ →
          ι (QuotientGroup.mk m') = TableB.linConjAut (Fin 3) k g (ι (QuotientGroup.mk m)) := by
  classical
  let SL := Matrix.SpecialLinearGroup (Fin 3) k
  let N : Type := ↥(triD4LineN0 k K)
  let eSL3 : SL ≃* N :=
    (MonoidHom.ofInjective (triD4LineSL3_injective k K)).trans
      (MulEquiv.subgroupCongr (triD4LineSL3_range k K))
  have hcoeSL3 : ∀ s : SL, ((eSL3 s : N) : TriD4LineX k K) = triD4LineSL3 k K s :=
    fun s => rfl
  have hmapCenterSymm := Subgroup.map_center_eq eSL3.symm
  have hmapCenterRefl := Subgroup.map_center_eq (MulEquiv.refl SL)
  let q : N ⧸ Subgroup.center N ≃* SL ⧸ Subgroup.center SL :=
    QuotientGroup.congr (Subgroup.center N) (Subgroup.center SL) eSL3.symm hmapCenterSymm
  let eProj : SL ⧸ Subgroup.center SL ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) k) :=
    (QuotientGroup.congr (Subgroup.center SL) (LinearFlag.scalars 3 k) (MulEquiv.refl SL)
      (by
        rw [hmapCenterRefl]
        exact (LinearFlag.scalars_eq_center 3 k).symm)).trans (TypeA.recipeEquiv 3 k).symm
  let ι : N ⧸ Subgroup.center N ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) k) :=
    q.trans eProj
  refine ⟨ι, ?_⟩
  intro g c hdet m m' hm'
  have hq : ∀ m : N, q (QuotientGroup.mk' (Subgroup.center N) m) =
      QuotientGroup.mk' (Subgroup.center SL) (eSL3.symm m) := by
    intro m
    exact QuotientGroup.congr_mk' (Subgroup.center N) (Subgroup.center SL) eSL3.symm
      hmapCenterSymm m
  have heProj : ∀ s : SL, eProj (QuotientGroup.mk' (Subgroup.center SL) s) =
      (TypeA.recipeEquiv 3 k).symm (LinearFlag.proj 3 k s) := by
    intro s
    dsimp only [eProj, MulEquiv.trans_apply]
    rw [QuotientGroup.congr_mk']
    rfl
  let s : SL := eSL3.symm m
  let s' : SL := eSL3.symm m'
  have hs : eSL3 s = m := eSL3.apply_symm_apply m
  have hs' : eSL3 s' = m' := eSL3.apply_symm_apply m'
  let s'' : SL := slConjugation 3 k g s
  have hs''val : Matrix.SpecialLinearGroup.toGL s'' =
      g * Matrix.SpecialLinearGroup.toGL s * g⁻¹ := toGL_slConjugation 3 k g s
  have hs'' : s' = s'' := by
    apply triD4LineSL3_injective k K
    have h1 : (triD4LineSL3 k K s' : TriD4LineX k K) =
        triD4LineMk k K g c hdet * triD4LineSL3 k K s *
          (triD4LineMk k K g c hdet)⁻¹ := by
      have h := hm'
      rw [← hs', ← hs] at h
      simpa only [hcoeSL3] using h
    have h2 : triD4LineMk k K g c hdet * triD4LineSL3 k K s *
        (triD4LineMk k K g c hdet)⁻¹ = triD4LineSL3 k K s'' :=
      triD4LineMk_mul_SL3_mul_inv k K g c hdet s s'' hs''val
    exact h1.trans h2
  have hproj : LinearFlag.proj 3 k s' = LinearFlag.conjAut 3 k g (LinearFlag.proj 3 k s) := by
    rw [hs'']
    exact (LinearFlag.conjAut_proj g s).symm
  have hιm : ι (QuotientGroup.mk m) =
      (TypeA.recipeEquiv 3 k).symm (LinearFlag.proj 3 k s) := by
    rw [← QuotientGroup.mk'_apply]
    dsimp only [ι, MulEquiv.trans_apply]
    rw [hq m]
    exact heProj s
  have hιm' : ι (QuotientGroup.mk m') =
      (TypeA.recipeEquiv 3 k).symm (LinearFlag.proj 3 k s') := by
    rw [← QuotientGroup.mk'_apply]
    dsimp only [ι, MulEquiv.trans_apply]
    rw [hq m']
    exact heProj s'
  rw [hιm', hιm]
  have hbridge : TableB.linConjAut (Fin 3) k g
        ((TypeA.recipeEquiv 3 k).symm (LinearFlag.proj 3 k s)) =
      (TypeA.recipeEquiv 3 k).symm
        (LinearFlag.conjAut 3 k g (LinearFlag.proj 3 k s)) := by
    apply (TypeA.recipeEquiv 3 k).injective
    rw [l02qjbr_recipeEquiv_linConjAut, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rw [hbridge, ← hproj]

theorem kgLangT3_component_equiv {n : ℕ} (K : Type) [Field K] (k : Type) [Field k] [Algebra k K]
    (D : TriD4LineKGXData n K k) (J₀ : Subgroup (GGTriD4R n K))
    (hJ : IsComponentOf J₀ (Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))) :
    ∃ ι : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) k),
      ∀ (y : GGTriD4R n K) (hy : y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))
        (g : GL (Fin 3) k) (c : Kˣ)
        (hdet : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c),
        (D.Θ ⟨y, hy⟩ : TriD4LineX k K) = triD4LineMk k K g c hdet →
        ∀ j j' : ↥J₀, (j' : GGTriD4R n K) = y * j * y⁻¹ →
          ι (QuotientGroup.mk j') = TableB.linConjAut (Fin 3) k g (ι (QuotientGroup.mk j)) := by
  let C : Subgroup (GGTriD4R n K) := Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))
  let N : Subgroup (TriD4LineX k K) := triD4LineN0 k K
  have hN0 : (J₀.subgroupOf C).map D.Θ.toMonoidHom = N :=
    l02qjbr_subgroupOf_map_eq K k D J₀ hJ
  let eJ : ↥J₀ ≃* ↥N :=
    (Subgroup.subgroupOfEquivOfLe hJ.1).symm.trans
      ((Subgroup.equivMapOfInjective (J₀.subgroupOf C) D.Θ.toMonoidHom D.Θ.injective).trans
        (MulEquiv.subgroupCongr hN0))
  have hcoeeJ : ∀ j : ↥J₀, ((eJ j : ↥N) : TriD4LineX k K) =
      D.Θ ⟨(j : GGTriD4R n K), hJ.1 j.2⟩ := fun j => rfl
  obtain ⟨ιN, hιN⟩ := kgLangT3_N0_equiv_psl3 k K
  let eQ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* ↥N ⧸ Subgroup.center ↥N :=
    QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥N) eJ
      (Subgroup.map_center_eq eJ)
  let ι : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) k) :=
    eQ.trans ιN
  refine ⟨ι, ?_⟩
  intro y hy g c hdet hΘy j j' hjj'
  have hιe : ∀ j : ↥J₀, ι (QuotientGroup.mk j) = ιN (QuotientGroup.mk (eJ j)) := by
    intro j
    rw [← QuotientGroup.mk'_apply]
    dsimp only [ι, eQ, MulEquiv.trans_apply]
    rw [QuotientGroup.congr_mk']
    rw [QuotientGroup.mk'_apply]
  have hΘj' := hcoeeJ j'
  have hΘj := hcoeeJ j
  have hCeq : (⟨(j' : GGTriD4R n K), hJ.1 j'.2⟩ : C) =
      ⟨y, hy⟩ * ⟨(j : GGTriD4R n K), hJ.1 j.2⟩ * ⟨y, hy⟩⁻¹ := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hjj'
  have hΘeq : D.Θ ⟨(j' : GGTriD4R n K), hJ.1 j'.2⟩ =
      D.Θ ⟨y, hy⟩ * D.Θ ⟨(j : GGTriD4R n K), hJ.1 j.2⟩ * (D.Θ ⟨y, hy⟩)⁻¹ := by
    rw [hCeq, map_mul, map_mul, map_inv]
  have hhyp : ((eJ j' : ↥N) : TriD4LineX k K) =
      triD4LineMk k K g c hdet * (eJ j) * (triD4LineMk k K g c hdet)⁻¹ := by
    rw [hΘj', hΘj, hΘeq, hΘy]
  have hthis := hιN g c hdet (eJ j) (eJ j') hhyp
  calc ι (QuotientGroup.mk j') = ιN (QuotientGroup.mk (eJ j')) := hιe j'
    _ = TableB.linConjAut (Fin 3) k g (ιN (QuotientGroup.mk (eJ j))) := hthis
    _ = TableB.linConjAut (Fin 3) k g (ι (QuotientGroup.mk j)) := by rw [hιe j]

end CFSG.StandardType
