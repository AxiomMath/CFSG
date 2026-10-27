module

public import CFSG.LocalAnalysis.StandardType.GGTBJSuBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdAct
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
import CFSG.GroupTheory.ConjKerCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)
open CFSG.RankThree.Classical (permGL)

private lemma ggTBJsudB_actsDiagU_exists_units {K : Type} [Field K] {n d : ℕ}
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} {a : MulAut L'} {t : Fin d → K}
    (ha : LineU.ActsDiagU φ a t) :
    ∃ (σ : Fin d → Kˣ) (hD : diagHom d σ ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
      (∀ k, ((σ k : Kˣ) : K) = t k) ∧
        ∀ s : ↥(unitarySU 2 n K d), a (φ s) = φ (LineU.conjN (diagHom d σ) hD s) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  have h0 : ∀ k, t k ≠ 0 := fun k => LineU.diag_ne_zero_of_eq hDt k
  set σ : Fin d → Kˣ := fun k => Units.mk0 (t k) (h0 k) with hσ
  have hDσ : D = diagHom d σ := by
    apply Units.ext
    rw [hDt, coe_diagHom]
    rfl
  subst hDσ
  exact ⟨σ, hD, fun k => rfl, hact⟩

private lemma ggTBJsudB_conj_mul_conj {L' : Type} [Group L'] (y : MulAut L') (l : L') :
    y * MulAut.conj l * y⁻¹ = MulAut.conj (y l) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private lemma ggTBJsudB_suPairs_conj {K : Type} [Field K] {n d : ℕ} {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} {y : MulAut L'} {σ : Fin d → Kˣ}
    (hD : diagHom d σ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hact : ∀ s : ↥(unitarySU 2 n K d), y (φ s) = φ (LineU.conjN (diagHom d σ) hD s)) :
    (y, diagHom d σ) ∈ SUTorus.suPairs (MulAut.conj.comp φ) := by
  refine ⟨hD, fun u v huv => ?_⟩
  have hvu : v = LineU.conjN (diagHom d σ) hD u :=
    Subtype.ext (by rw [LineU.coe_conjN]; exact huv)
  rw [hvu]
  simp only [MonoidHom.comp_apply]
  rw [← hact u]
  exact ggTBJsudB_conj_mul_conj y (φ u)

private lemma ggTBJsudB_ggFix_conj_centralizer {L' : Type} [Group L'] (y : MulAut L') :
    ggFix (MulAut.conj y) = Subgroup.centralizer ({y} : Set (MulAut L')) := by
  ext f
  rw [mem_ggFix, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

private lemma ggTBJsudB_scalar_mem_center {K : Type} [Field K] {n d : ℕ}
    {g : ↥(unitarySU 2 n K d)} {c : K}
    (hc : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) :
    g ∈ Subgroup.center ↥(unitarySU 2 n K d) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  apply Units.ext
  ext i j
  simp only [Units.val_mul, hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact mul_comm _ c

private lemma ggTBJsudB_le_of_le_sup_center {G : Type*} [Group G] {H K : Subgroup G}
    (hH : ⁅H, H⁆ = H) (h : H ≤ K ⊔ Subgroup.center G) : H ≤ K := by
  rw [← hH]
  calc ⁅H, H⁆ ≤ ⁅K ⊔ Subgroup.center G, K ⊔ Subgroup.center G⁆ := Subgroup.commutator_mono h h
    _ = ⁅K, K⁆ :=
      CFSG.ComponentClassification.CentralExtensions.commutator_sup_central K (Subgroup.center G)
        le_rfl
    _ ≤ K := Subgroup.commutator_le_self K

theorem ggTBJ_sud_blockData {K : Type} [Field K] [Finite K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    (hperf : commutator ↥(unitarySU 2 n K d) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {y : MulAut L'} {t : Fin d → K} (hy : LineU.ActsDiagU φ y t) {J : Subgroup L'}
    (hJ : CFSG.Assembly.IsComponentOf J (ggFix y)) :
    ∃ I : Finset (Fin d), (∀ i ∈ I, ∀ j ∈ I, t i = t j) ∧
      (∀ i ∈ I, ∀ j ∈ I, φ (LineU.permSU hK (Equiv.swap i j)) ∈ J) ∧
      ∀ (a : MulAut L') (s : Fin d → K), LineU.ActsDiagU φ a s →
        (∀ i ∈ I, ∀ j ∈ I, s i = s j) → ∀ l ∈ J, a l = l := by
  classical
  cases d with
  | zero =>
    have hsub : Subsingleton ↥(unitarySU 2 n K 0) := by
      constructor
      intro x y
      refine Subtype.ext (Units.ext ?_)
      funext i j
      exact i.elim0
    have hsubL : Subsingleton L' :=
      @Function.Surjective.subsingleton ↥(unitarySU 2 n K 0) L' φ hsub hφs
    refine ⟨∅, ?_, ?_, ?_⟩
    · intro i hi
      simp at hi
    · intro i hi
      simp at hi
    · intro a s ha hs l hl
      exact @Subsingleton.elim L' hsubL (a l) l
  | succ m =>
    obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (n := 2 ^ n + 1) (by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega)
    have hker_conj : (MulAut.conj : L' →* MulAut L').ker = Subgroup.center L' :=
      CFSG.GroupTheory.ker_conj_eq_center
    have hkerψ : (MulAut.conj.comp φ : ↥(unitarySU 2 n K (m + 1)) →* MulAut L').ker ≤
        Subgroup.center ↥(unitarySU 2 n K (m + 1)) := by
      intro g hg
      have hφg : φ g ∈ Subgroup.center L' := by
        rw [← hker_conj, MonoidHom.mem_ker]
        exact hg
      have hscalar : ∀ s : ↥(unitarySU 2 n K (m + 1)),
          MulAut.conj g s * s⁻¹ ∈ Subgroup.center ↥(unitarySU 2 n K (m + 1)) := by
        intro s
        have hcomm : φ (g * s * g⁻¹ * s⁻¹) = 1 := by
          have h1 : φ s * φ g = φ g * φ s := Subgroup.mem_center_iff.mp hφg (φ s)
          calc φ (g * s * g⁻¹ * s⁻¹) = φ g * φ s * (φ g)⁻¹ * (φ s)⁻¹ := by
                rw [map_mul, map_mul, map_mul, map_inv, map_inv]
            _ = φ s * φ g * (φ g)⁻¹ * (φ s)⁻¹ := by rw [← h1]
            _ = 1 := by group
        obtain ⟨c, hc⟩ := hφker (g * s * g⁻¹ * s⁻¹) hcomm
        refine ggTBJsudB_scalar_mem_center (c := c) ?_
        have he : MulAut.conj g s * s⁻¹ = g * s * g⁻¹ * s⁻¹ := by rw [MulAut.conj_apply]
        rw [he]
        exact hc
      have hfix : (⊤ : Subgroup ↥(unitarySU 2 n K (m + 1))) ≤ ggFix (MulAut.conj g) := by
        have h := TableBUD.commutator_le_ggFix (a := MulAut.conj g) (Y := ⊤)
          (fun y _ => hscalar y)
        rwa [show ⁅(⊤ : Subgroup ↥(unitarySU 2 n K (m + 1))), ⊤⁆ = ⊤ from hperf] at h
      rw [Subgroup.mem_center_iff]
      intro s
      have hs : g * s * g⁻¹ = s := by
        have h := mem_ggFix.mp (hfix (Subgroup.mem_top s))
        rwa [MulAut.conj_apply] at h
      calc s * g = (g * s * g⁻¹) * g := by rw [hs]
        _ = g * s := by group
    obtain ⟨σ, hDσ, hσt, hσact⟩ := ggTBJsudB_actsDiagU_exists_units hy
    have hySuPairs : (y, diagHom (m + 1) σ) ∈
        SUTorus.suPairs (MulAut.conj.comp φ) :=
      ggTBJsudB_suPairs_conj hDσ hσact
    have hJ' : CFSG.Assembly.IsComponentOf (J.map (MulAut.conj : L' →* MulAut L'))
        ((MulAut.conj.comp φ).range ⊓
          Subgroup.centralizer ({y} : Set (MulAut L'))) := by
      have hkerπ : (MulAut.conj : L' →* MulAut L').ker ≤ Subgroup.center L' := hker_conj.le
      have hc : ∀ l : L', MulAut.conj y (MulAut.conj l) = MulAut.conj (y l) :=
        fun l => ggTBJsudB_conj_mul_conj y l
      have hnorm := USixTwo.fix_normal_comap (π := (MulAut.conj : L' →* MulAut L'))
        (a := y) (ab := MulAut.conj y) hkerπ hc
      have hle : ggFix y ≤
          (ggFix (MulAut.conj y)).comap (MulAut.conj : L' →* MulAut L') :=
        USixTwo.fix_le_comap hc
      have hP : IsSubnormal J
          ((ggFix (MulAut.conj y)).comap (MulAut.conj : L' →* MulAut L')) :=
        hJ.2.1.trans (IsSubnormal.step hle hnorm (IsSubnormal.refl _))
      have hcomp : IsComponentOf J
          ((ggFix (MulAut.conj y)).comap (MulAut.conj : L' →* MulAut L')) :=
        ⟨hJ.1.trans hle, hP, hJ.2.2⟩
      have hnot : ¬ J ≤ (MulAut.conj : L' →* MulAut L').ker := fun h =>
        Line63.H5.not_le_center_of_isQuasisimple hJ.2.2 (h.trans hker_conj.le)
      have hmap := Line63.H5.isComponentOf_map_of_not_le_ker
        (MulAut.conj : L' →* MulAut L') hcomp hnot
      have hψrange : (MulAut.conj.comp φ).range = (MulAut.conj : L' →* MulAut L').range := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφs, ← MonoidHom.range_eq_map]
      have hPmap : ((ggFix (MulAut.conj y)).comap (MulAut.conj : L' →* MulAut L')).map
          (MulAut.conj : L' →* MulAut L') = (MulAut.conj.comp φ).range ⊓
            Subgroup.centralizer ({y} : Set (MulAut L')) := by
        rw [Subgroup.map_comap_eq, ggTBJsudB_ggFix_conj_centralizer, ← hψrange]
      rwa [hPmap] at hmap
    have hδ : ∀ e ∈ ({y} : Set (MulAut L')),
        (e, diagHom (m + 1) σ) ∈ SUTorus.suPairs (MulAut.conj.comp φ) := by
      intro e he
      rw [Set.mem_singleton_iff] at he
      subst he
      exact hySuPairs
    obtain ⟨i, hJi⟩ := SUTorus.exists_le_map_blockSU hK hp hpq hkerψ hδ (J := J.map
      (MulAut.conj : L' →* MulAut L')) hJ'
    set I : Finset (Fin (m + 1)) :=
      LinTorus.diagClass ({y} : Set (MulAut L')) (fun _ => σ) i with hIdef
    have hI2 : 2 ≤ I.card := by
      by_contra hlt
      have hI1 : I = {i} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨LinTorus.self_mem_diagClass ({y} : Set (MulAut L')) (fun _ => σ) i,
          fun j hj => Finset.card_le_one.mp (by omega) j hj i
            (LinTorus.self_mem_diagClass ({y} : Set (MulAut L')) (fun _ => σ) i)⟩
      rw [hI1, SUTorus.blockSU_singleton hK, Subgroup.map_bot] at hJi
      exact commutator_ne_bot_of_isQuasisimple hJ'.2.2
        (by rw [le_bot_iff.mp hJi, Subgroup.commutator_bot_left])
    have hblock : IsSubnormal
        ((TableBUE.blockSU (K := K) (n := n) I).map (MulAut.conj.comp φ))
        ((MulAut.conj.comp φ).range ⊓ Subgroup.centralizer ({y} : Set (MulAut L'))) :=
      SUTorus.isSubnormal_map_blockSU hkerψ hδ i
    have hKI : IsComponentOf
        ((TableBUE.blockSU (K := K) (n := n) I).map (MulAut.conj.comp φ))
        ((MulAut.conj.comp φ).range ⊓ Subgroup.centralizer ({y} : Set (MulAut L'))) :=
      ⟨isSubnormal_le_of_assembly hblock, hblock,
        SURepair.isQuasisimple_map_blockSU_of_two_le hK hn hkerψ hI2⟩
    have hJeq' : J.map (MulAut.conj : L' →* MulAut L') =
        (TableBUE.blockSU (K := K) (n := n) I).map (MulAut.conj.comp φ) := by
      refine le_antisymm hJi ?_
      rcases isComponentOf_le_or_commutator_eq_bot hKI hJ'.2.1 with h1 | h1
      · exact h1
      · exfalso
        have h2 : ⁅J.map (MulAut.conj : L' →* MulAut L'),
            J.map (MulAut.conj : L' →* MulAut L')⁆ ≤
            ⁅(TableBUE.blockSU (K := K) (n := n) I).map (MulAut.conj.comp φ),
              J.map (MulAut.conj : L' →* MulAut L')⁆ :=
          Subgroup.commutator_mono hJi le_rfl
        rw [h1, le_bot_iff] at h2
        exact commutator_ne_bot_of_isQuasisimple hJ'.2.2 h2
    have hkerφ : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K (m + 1)) := fun g hg => by
      obtain ⟨c, hc⟩ := hφker g (MonoidHom.mem_ker.mp hg)
      exact ggTBJsudB_scalar_mem_center (c := c) hc
    have hJeq : J = (TableBUE.blockSU (K := K) (n := n) I).map φ := by
      have hmap : J.map (MulAut.conj : L' →* MulAut L') =
          ((TableBUE.blockSU (K := K) (n := n) I).map φ).map
            (MulAut.conj : L' →* MulAut L') := by
        rw [hJeq', Subgroup.map_map]
      have hJperf : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJ.2.2
      have hKperf : ⁅(TableBUE.blockSU (K := K) (n := n) I).map φ,
          (TableBUE.blockSU (K := K) (n := n) I).map φ⁆ =
          (TableBUE.blockSU (K := K) (n := n) I).map φ :=
        commutator_self_eq_of_isQuasisimple
          (SURepair.isQuasisimple_map_blockSU_of_two_le hK hn hkerφ hI2)
      refine le_antisymm ?_ ?_
      · refine ggTBJsudB_le_of_le_sup_center hJperf ?_
        have h := Subgroup.map_le_map_iff.mp hmap.le
        rwa [hker_conj] at h
      · refine ggTBJsudB_le_of_le_sup_center hKperf ?_
        have h := Subgroup.map_le_map_iff.mp hmap.ge
        rwa [hker_conj] at h
    refine ⟨I, ?_, ?_, ?_⟩
    · intro a ha b hb
      have hmem : y ∈ ({y} : Set (MulAut L')) := Set.mem_singleton y
      have h1 : σ a = σ b :=
        (LinTorus.mem_diagClass.mp ha y hmem).trans
          (LinTorus.mem_diagClass.mp hb y hmem).symm
      calc t a = ((σ a : Kˣ) : K) := (hσt a).symm
        _ = ((σ b : Kˣ) : K) := by rw [h1]
        _ = t b := hσt b
    · intro a ha b hb
      rw [hJeq]
      refine Subgroup.mem_map_of_mem φ ?_
      rw [TableBUE.mem_blockSU, LineU.coe_permSU]
      exact TableBUE.isBlockOn_permGL_swap ha hb
    · intro a s ha hs l hl
      obtain ⟨σ', hD', hσ't, hσ'act⟩ := ggTBJsudB_actsDiagU_exists_units ha
      rw [hJeq] at hl
      obtain ⟨u, hu, rfl⟩ := hl
      have hσ'const : ∀ i ∈ I, ∀ j ∈ I, σ' i = σ' j := by
        intro a' ha' b' hb'
        exact Units.ext (by rw [hσ't a', hσ't b', hs a' ha' b' hb'])
      have hcomm := TableBUE.diagHom_mul_comm_of_isBlockOn (S := I) (σ := σ') hσ'const
        (TableBUE.mem_blockSU.mp hu)
      have hconj : LineU.conjN (diagHom (m + 1) σ') hD' u = u := by
        apply Subtype.ext
        rw [LineU.coe_conjN, hcomm]
        group
      rw [hσ'act u, hconj]

end CFSG.StandardType

end
