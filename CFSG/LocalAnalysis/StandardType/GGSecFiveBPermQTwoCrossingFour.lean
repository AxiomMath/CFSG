module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpEquiv
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLGenerate
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLFrameSwap
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCentralizer
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrame
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCrossing
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

namespace CFSG.StandardType

open Polynomial Matrix CFSG.RankThree.CALinearPlane
open scoped MatrixGroups

namespace QTwoBlocks

theorem coordBlockSL_map_le_centralizer {G : Type} [Group G] {F : Type} [Field F] {m : ℕ}
    (κ : SL(m, F) →* G) {I J : Finset (Fin m)} (hIJ : Disjoint I J) :
    (coordBlockSL F I).map κ ≤ Subgroup.centralizer ((coordBlockSL F J).map κ : Set G) := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hz
  have hu' : u ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear I := by
    rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    simpa only [Matrix.one_apply] using mem_coordBlockSL_iff.mp hu
  have hv' : v ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear J := by
    rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    simpa only [Matrix.one_apply] using mem_coordBlockSL_iff.mp hv
  have huv := CFSG.SeitzReduction.LinearPilot.commute_blockSpecialLinear_of_disjoint hIJ hu' hv'
  simpa only [map_mul] using congrArg κ huv.eq.symm

theorem disjoint_frameBlockCoords {m e s d : ℕ} (ε : Fin m ≃ (Fin e × Fin s) ⊕ Fin d)
    {A B : Finset (Fin s)} (hAB : Disjoint A B) :
    Disjoint (CoordSL.frameBlockCoords ε A) (CoordSL.frameBlockCoords ε B) := by
  refine Finset.disjoint_left.mpr fun x hxA hxB => ?_
  rcases hε : ε x with ⟨a, i⟩ | z
  · rw [CoordSL.mem_frameBlockCoords_inl hε] at hxA hxB
    exact Finset.disjoint_left.mp hAB hxA hxB
  · exact CoordSL.not_mem_frameBlockCoords_inr hε hxA

theorem disjoint_frameBlockCoords_fixS_compl {m e s d : ℕ}
    (ε : Fin m ≃ (Fin e × Fin s) ⊕ Fin d) {A B : Finset (Fin s)} (hAB : Disjoint A B) :
    Disjoint (CoordSL.frameBlockCoords ε A) (SLNS.fixS ε Bᶜ) := by
  refine Finset.disjoint_left.mpr fun x hxA hxB => ?_
  rcases hε : ε x with ⟨a, i⟩ | z
  · rw [CoordSL.mem_frameBlockCoords_inl hε] at hxA
    have hiB : i ∈ B := by simpa [SLNS.mem_fixS, SLNS.inT, hε] using hxB
    exact Finset.disjoint_left.mp hAB hxA hiB
  · exact CoordSL.not_mem_frameBlockCoords_inr hε hxA

theorem fixS_compl_eq_frameBlockCoords {m e s d : ℕ} (ε : Fin m ≃ (Fin e × Fin s) ⊕ Fin d)
    (hd : d = 0) (A : Finset (Fin s)) : SLNS.fixS ε Aᶜ = CoordSL.frameBlockCoords ε A := by
  ext x
  rcases hε : ε x with ⟨a, i⟩ | z
  · rw [CoordSL.mem_frameBlockCoords_inl hε]
    simp [SLNS.mem_fixS, SLNS.inT, hε]
  · have hz := z.isLt
    omega

theorem fixS_compl_sdiff_eq_frameBlockCoords {m e s d : ℕ}
    (ε : Fin m ≃ (Fin e × Fin s) ⊕ Fin d) {A B : Finset (Fin s)} (hAB : Disjoint A B) :
    SLNS.fixS ε Aᶜ \ SLNS.fixS ε Bᶜ = CoordSL.frameBlockCoords ε A := by
  ext x
  rw [Finset.mem_sdiff]
  rcases hε : ε x with ⟨a, i⟩ | z
  · rw [CoordSL.mem_frameBlockCoords_inl hε]
    simp only [SLNS.mem_fixS, SLNS.inT, hε, Sum.elim_inl, Finset.mem_compl, not_not]
    exact ⟨fun h => h.1, fun h => ⟨h, Finset.disjoint_left.mp hAB h⟩⟩
  · simp [SLNS.mem_fixS, SLNS.inT, hε, CoordSL.not_mem_frameBlockCoords_inr hε]

end QTwoBlocks

theorem ggReflComm_map_conj_of_permAut {G : Type} [Group G] {Bs : Subgroup G} {p n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {w : G}
    (hw : w ∈ Subgroup.normalizer (Bs : Set G)) {τ : Equiv.Perm (Fin n)}
    (hτ : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut τ) (i j : Fin n) :
    (⁅Subgroup.centralizer (ggBsCoordEq Bs eta i j : Set G), Bs⁆).map
        (MulAut.conj w).toMonoidHom =
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (τ i) (τ j) : Set G), Bs⁆ :=
  ggReflComm_map_conj (φ := ggConjAut Bs hw) (fun _ => rfl)
    (eta_ggConjAut_apply_of_permAut hw hτ) i j

namespace GGSecFiveBPermQTwoKFrame

variable {G : Type} [Group G] {Bs K : Subgroup G} {n m d : ℕ}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {π : Fin 4 ≃ Fin n}
  {g : (ZMod 2)[X]} [Fact (Irreducible g)]
  {ε : Fin m ≃ (Fin (CoordSL.rootPB g).dim × Fin 3) ⊕ Fin d}
  {hC : (CoordSL.rootMat g).det = 1} {hCp : CoordSL.rootMat g ^ 3 = 1} {κ : SL(m, ZMod 2) →* G}

private theorem le_centralizer_of_map_conj {H N : Subgroup G} (w : G)
    (h : H.map (MulAut.conj w).toMonoidHom ≤
      Subgroup.centralizer (N.map (MulAut.conj w).toMonoidHom : Set G)) :
    H ≤ Subgroup.centralizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hxz := Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_map_of_mem _ hx)) _
    (Subgroup.mem_map_of_mem _ hz)
  apply (MulAut.conj w).injective
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hxz

private theorem swap_apply_ne {i j k : Fin 4} (hki : k ≠ i) (hkj : k ≠ j) :
    Equiv.swap (π i) (π j) (π k) = π k :=
  Equiv.swap_apply_of_ne_of_ne (π.injective.ne hki) (π.injective.ne hkj)

private theorem pair_blockComm [Finite G] (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2) {a b : Fin 3} (hab : a ≠ b) :
    ggBlockComm Bs eta {π a.succ, π b.succ} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({a, b} : Finset (Fin 3))ᶜ)).map κ := by
  classical
  have hS : ({a, b} : Finset (Fin 3)) ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    rw [Finset.card_pair hab, Finset.card_univ, Fintype.card_fin] at hc
    omega
  simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton] using hF.blockComm hBs hyB hK (S := {a, b})
      (Finset.insert_nonempty _ _) hS (by
        rw [QTwoBlocks.card_fixS_compl, hdim, Finset.card_pair hab]
        omega)

private theorem single_blockComm [Finite G]
    (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2) (hd : d = 1) (a : Fin 3) :
    ggBlockComm Bs eta {π a.succ} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({a} : Finset (Fin 3))ᶜ)).map κ := by
  classical
  have hS : ({a} : Finset (Fin 3)) ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    rw [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hc
    omega
  simpa only [Finset.coe_singleton, Set.image_singleton] using hF.blockComm hBs hyB hK
    (S := {a}) (Finset.singleton_nonempty _) hS
    (by rw [QTwoBlocks.card_fixS_compl, hdim, hd]; simp)

private theorem frameBlock_pair_eq_sup (hdim : (CoordSL.rootPB g).dim = 2)
    {S : Fin n → Subgroup G}
    (hSK : ∀ a : Fin 3, S (π a.succ) =
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a})).map κ)
    (hRK : ∀ a b : Fin 3, a ≠ b →
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
        ((coordBlockSL (AdjoinRoot g) {a, b}).map (CoordSL.theta g ε)).map κ)
    {a b : Fin 3} (hab : a ≠ b) :
    (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a, b})).map κ =
      S (π a.succ) ⊔ S (π b.succ) ⊔
        ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ := by
  rw [CoordSL.coordBlockSL_frameBlockCoords_pair_eq_sup ε hab (by rw [hdim]), Subgroup.map_sup,
    Subgroup.map_sup, ← hSK a, ← hSK b, ← hRK a b hab]

private theorem reflComm_le (hdim : (CoordSL.rootPB g).dim = 2)
    (hRK : ∀ a b : Fin 3, a ≠ b →
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
        ((coordBlockSL (AdjoinRoot g) {a, b}).map (CoordSL.theta g ε)).map κ)
    {a b : Fin 3} (hab : a ≠ b) :
    ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ ≤
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a, b})).map κ := by
  rw [hRK a b hab]
  refine Subgroup.map_mono ?_
  rw [CoordSL.coordBlockSL_frameBlockCoords_pair_eq_sup ε hab (by rw [hdim])]
  exact le_sup_right

theorem crossing_even_four [Finite G]
    (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2)
    (hlift : ∀ a b : Fin n, a ≠ b → ∃ w, ∃ hw : w ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap a b))
    (hd : d = 0) (S : Fin n → Subgroup G)
    (hSK : ∀ a : Fin 3, S (π a.succ) =
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a})).map κ)
    (hSeq : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)) (τ : Equiv.Perm (Fin n)),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut τ →
        ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (τ i))
    (hRK : ∀ a b : Fin 3, a ≠ b →
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
        ((coordBlockSL (AdjoinRoot g) {a, b}).map (CoordSL.theta g ε)).map κ)
    (σ : SL(4, GaloisField 2 2) →* G)
    (hRL₁ : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 1) (π 2) : Set G), Bs⁆ =
      (coordBlockSL (GaloisField 2 2) {1, 2}).map σ)
    (hRL₂ : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 3) (π 0) : Set G), Bs⁆ =
      (coordBlockSL (GaloisField 2 2) {3, 0}).map σ) :
    ∀ x ∈ ggBlockComm Bs eta {π 1, π 2},
      ∀ z ∈ ggBlockComm Bs eta {π 3, π 0}, x * z = z * x := by
  classical
  obtain ⟨w₁, hw₁, hτ₁⟩ := hlift (π 0) (π 1) (π.injective.ne (by decide))
  obtain ⟨w₂, hw₂, hτ₂⟩ := hlift (π 0) (π 2) (π.injective.ne (by decide))
  obtain ⟨w₃, hw₃, hτ₃⟩ := hlift (π 0) (π 3) (π.injective.ne (by decide))
  have hS1 : S (π 1) = (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {0})).map κ := hSK 0
  have hS2 : S (π 2) = (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {1})).map κ := hSK 1
  have hS3 : S (π 3) = (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {2})).map κ := hSK 2
  have hM12 : ggBlockComm Bs eta {π 1, π 2} =
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {0, 1})).map κ := by
    rw [← QTwoBlocks.fixS_compl_eq_frameBlockCoords ε hd]
    exact pair_blockComm hF hBs hyB hK hdim (a := 0) (b := 1) (by decide)
  have hM31 : ggBlockComm Bs eta {π 3, π 1} =
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {2, 0})).map κ := by
    rw [← QTwoBlocks.fixS_compl_eq_frameBlockCoords ε hd]
    exact pair_blockComm hF hBs hyB hK hdim (a := 2) (b := 0) (by decide)
  have hgen12 : (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {0, 1})).map κ =
      S (π 1) ⊔ S (π 2) ⊔
        ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 1) (π 2) : Set G), Bs⁆ :=
    frameBlock_pair_eq_sup hdim hSK hRK (a := 0) (b := 1) (by decide)
  have hgen31 : (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {2, 0})).map κ =
      S (π 3) ⊔ S (π 1) ⊔
        ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 3) (π 1) : Set G), Bs⁆ :=
    frameBlock_pair_eq_sup hdim hSK hRK (a := 2) (b := 0) (by decide)
  have hR32 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 3) (π 2) : Set G), Bs⁆ ≤
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {2, 1})).map κ :=
    reflComm_le hdim hRK (a := 2) (b := 1) (by decide)
  have hR31 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 3) (π 1) : Set G), Bs⁆ ≤
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {2, 0})).map κ :=
    reflComm_le hdim hRK (a := 2) (b := 0) (by decide)
  have hM30 : ggBlockComm Bs eta {π 3, π 0} = S (π 3) ⊔ S (π 0) ⊔
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 3) (π 0) : Set G), Bs⁆ := by
    apply Subgroup.map_injective (f := (MulAut.conj w₁).toMonoidHom) (MulAut.conj w₁).injective
    rw [ggBlockComm_map_conj hw₁ hτ₁, Subgroup.map_sup, Subgroup.map_sup, hSeq w₁ hw₁ _ hτ₁,
      hSeq w₁ hw₁ _ hτ₁, ggReflComm_map_conj_of_permAut hw₁ hτ₁]
    simp only [Set.image_insert_eq, Set.image_singleton, Equiv.swap_apply_left,
      swap_apply_ne (π := π) (i := 0) (j := 1) (k := 3) (by decide) (by decide)]
    rw [hM31, hgen31]
  have hD3 : S (π 3) ≤ Subgroup.centralizer (ggBlockComm Bs eta {π 1, π 2} : Set G) := by
    rw [hM12, hS3]
    exact QTwoBlocks.coordBlockSL_map_le_centralizer κ
      (QTwoBlocks.disjoint_frameBlockCoords ε (by decide))
  have hD0 : S (π 0) ≤ Subgroup.centralizer (ggBlockComm Bs eta {π 1, π 2} : Set G) := by
    apply le_centralizer_of_map_conj w₃
    rw [hSeq w₃ hw₃ _ hτ₃, ggBlockComm_map_conj hw₃ hτ₃]
    simp only [Set.image_insert_eq, Set.image_singleton, Equiv.swap_apply_left,
      swap_apply_ne (π := π) (i := 0) (j := 3) (k := 1) (by decide) (by decide),
      swap_apply_ne (π := π) (i := 0) (j := 3) (k := 2) (by decide) (by decide)]
    exact hD3
  have hDR : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 3) (π 0) : Set G), Bs⁆ ≤
      Subgroup.centralizer (ggBlockComm Bs eta {π 1, π 2} : Set G) := by
    rw [Subgroup.le_centralizer_iff, hM12, hgen12]
    refine sup_le (sup_le ?_ ?_) ?_
    ·
      apply le_centralizer_of_map_conj w₂
      rw [hSeq w₂ hw₂ _ hτ₂, ggReflComm_map_conj_of_permAut hw₂ hτ₂]
      simp only [Equiv.swap_apply_left,
        swap_apply_ne (π := π) (i := 0) (j := 2) (k := 1) (by decide) (by decide),
        swap_apply_ne (π := π) (i := 0) (j := 2) (k := 3) (by decide) (by decide)]
      rw [hS1]
      exact (QTwoBlocks.coordBlockSL_map_le_centralizer κ
        (QTwoBlocks.disjoint_frameBlockCoords ε (by decide))).trans
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR32))
    ·
      apply le_centralizer_of_map_conj w₁
      rw [hSeq w₁ hw₁ _ hτ₁, ggReflComm_map_conj_of_permAut hw₁ hτ₁]
      simp only [Equiv.swap_apply_left,
        swap_apply_ne (π := π) (i := 0) (j := 1) (k := 2) (by decide) (by decide),
        swap_apply_ne (π := π) (i := 0) (j := 1) (k := 3) (by decide) (by decide)]
      rw [hS2]
      exact (QTwoBlocks.coordBlockSL_map_le_centralizer κ
        (QTwoBlocks.disjoint_frameBlockCoords ε (by decide))).trans
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR31))
    ·
      rw [hRL₁, hRL₂]
      exact QTwoBlocks.coordBlockSL_map_le_centralizer σ (by decide)
  have hle : ggBlockComm Bs eta {π 3, π 0} ≤
      Subgroup.centralizer (ggBlockComm Bs eta {π 1, π 2} : Set G) := by
    rw [hM30]
    exact sup_le (sup_le hD3 hD0) hDR
  intro x hx z hz
  exact Subgroup.mem_centralizer_iff.mp (hle hz) x hx

theorem crossing_odd_four [Finite G]
    (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2)
    (hlift : ∀ a b : Fin n, a ≠ b → ∃ w, ∃ hw : w ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap a b))
    (hd : d = 1) (S : Fin n → Subgroup G)
    (hSK : ∀ a : Fin 3, S (π a.succ) =
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a})).map κ)
    (hSeq : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)) (τ : Equiv.Perm (Fin n)),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut τ →
        ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (τ i))
    (hRK : ∀ a b : Fin 3, a ≠ b →
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
        ((coordBlockSL (AdjoinRoot g) {a, b}).map (CoordSL.theta g ε)).map κ) :
    ∀ x ∈ ggBlockComm Bs eta {π 1, π 2} ⊓
        Subgroup.centralizer (ggBlockComm Bs eta {π 3} : Set G),
      ∀ z ∈ ggBlockComm Bs eta {π 0}, x * z = z * x := by
  classical
  obtain ⟨w₃, hw₃, hτ₃⟩ := hlift (π 0) (π 3) (π.injective.ne (by decide))
  have hM12 : ggBlockComm Bs eta {π 1, π 2} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({0, 1} : Finset (Fin 3))ᶜ)).map κ :=
    pair_blockComm hF hBs hyB hK hdim (a := 0) (b := 1) (by decide)
  have hM3 : ggBlockComm Bs eta {π 3} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({2} : Finset (Fin 3))ᶜ)).map κ :=
    single_blockComm hF hBs hyB hK hdim hd 2
  have hJI : ∃ x ∈ SLNS.fixS ε ({2} : Finset (Fin 3))ᶜ,
      x ∉ SLNS.fixS ε ({0, 1} : Finset (Fin 3))ᶜ := by
    let a : Fin (CoordSL.rootPB g).dim := ⟨0, by omega⟩
    refine ⟨ε.symm (Sum.inl (a, 2)), ?_, ?_⟩
    · simp [SLNS.mem_fixS, SLNS.inT]
    · simp [SLNS.mem_fixS, SLNS.inT]
  have hZ : ggBlockComm Bs eta {π 1, π 2} ⊓
      Subgroup.centralizer (ggBlockComm Bs eta {π 3} : Set G) =
        (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {0, 1})).map κ := by
    rw [hM12, hM3, coordBlockSL_map_inf_centralizer_eq_sdiff κ hF.1 _ _
      (by rw [QTwoBlocks.card_fixS_compl, hdim, hd]; simp) hJI,
      QTwoBlocks.fixS_compl_sdiff_eq_frameBlockCoords ε (A := {0, 1}) (B := {2}) (by decide)]
  have hgen : (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {0, 1})).map κ =
      S (π 1) ⊔ S (π 2) ⊔
        ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 1) (π 2) : Set G), Bs⁆ :=
    frameBlock_pair_eq_sup hdim hSK hRK (a := 0) (b := 1) (by decide)
  have hZw : (ggBlockComm Bs eta {π 1, π 2} ⊓
      Subgroup.centralizer (ggBlockComm Bs eta {π 3} : Set G)).map (MulAut.conj w₃).toMonoidHom =
        (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {0, 1})).map κ := by
    rw [hZ, hgen, Subgroup.map_sup, Subgroup.map_sup, hSeq w₃ hw₃ _ hτ₃, hSeq w₃ hw₃ _ hτ₃,
      ggReflComm_map_conj_of_permAut hw₃ hτ₃,
      swap_apply_ne (π := π) (i := 0) (j := 3) (k := 1) (by decide) (by decide),
      swap_apply_ne (π := π) (i := 0) (j := 3) (k := 2) (by decide) (by decide)]
  have hM0w : (ggBlockComm Bs eta {π 0}).map (MulAut.conj w₃).toMonoidHom =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({2} : Finset (Fin 3))ᶜ)).map κ := by
    rw [ggBlockComm_map_conj hw₃ hτ₃, Set.image_singleton, Equiv.swap_apply_left, hM3]
  have hle : ggBlockComm Bs eta {π 0} ≤ Subgroup.centralizer
      ((ggBlockComm Bs eta {π 1, π 2} ⊓
        Subgroup.centralizer (ggBlockComm Bs eta {π 3} : Set G) : Subgroup G) : Set G) := by
    apply le_centralizer_of_map_conj w₃
    rw [hM0w, hZw]
    exact QTwoBlocks.coordBlockSL_map_le_centralizer κ
      (QTwoBlocks.disjoint_frameBlockCoords_fixS_compl ε (A := {0, 1}) (B := {2})
        (by decide)).symm
  intro x hx z hz
  exact Subgroup.mem_centralizer_iff.mp (hle hz) x hx

private theorem lift_of_LFrame {L : Subgroup G} {σ : SL(4, GaloisField 2 2) →* G}
    {χ : Multiplicative (ZMod 3) →* (GaloisField 2 2)ˣ}
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3) :
    ∀ a b : Fin n, a ≠ b → ∃ w, ∃ hw : w ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap a b) := by
  intro a b hab
  obtain ⟨hw, hτ⟩ := hLF.permSL_swap_normalizer hBs hA (by norm_num)
    (i := π.symm a) (j := π.symm b) (π.symm.injective.ne hab)
  refine ⟨_, hw, ?_⟩
  simpa only [Equiv.apply_symm_apply] using hτ

theorem crossing_even_four_of_LFrame [Finite G]
    (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2)
    (hd : d = 0) (S : Fin n → Subgroup G)
    (hSK : ∀ a : Fin 3, S (π a.succ) =
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a})).map κ)
    (hSeq : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)) (τ : Equiv.Perm (Fin n)),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut τ →
        ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (τ i))
    (hRK : ∀ a b : Fin 3, a ≠ b →
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
        ((coordBlockSL (AdjoinRoot g) {a, b}).map (CoordSL.theta g ε)).map κ)
    {L : Subgroup G} {xL : G} {σ : SL(4, GaloisField 2 2) →* G}
    {χ : Multiplicative (ZMod 3) →* (GaloisField 2 2)ˣ}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a) (hxB : xL ∈ Bs)
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({xL} : Set G)))
    (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3) :
    ∀ x ∈ ggBlockComm Bs eta {π 1, π 2},
      ∀ z ∈ ggBlockComm Bs eta {π 3, π 0}, x * z = z * x := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  have hcb : ∀ I : Finset (Fin 4), coordBlockSL (GaloisField 2 2) I =
      CFSG.SeitzReduction.LinearPilot.blockSpecialLinear I := fun I => by
    ext A
    simp only [mem_coordBlockSL_iff, CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear,
      Matrix.one_apply]
  have hrefl : ∀ a : Fin 3,
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G), Bs⁆ =
        (coordBlockSL (GaloisField 2 2) {a.castSucc, a.succ}).map σ := fun a => by
    rw [ggSecFiveBPermSp_reflComm_L hp2 le_rfl hBc hBs hxB hL hLF a, MonoidHom.range_comp,
      CFSG.SeitzReduction.LinearPilot.range_blockSL2_eq, hcb]
  have hR12 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 1) (π 2) : Set G), Bs⁆ =
      (coordBlockSL (GaloisField 2 2) {1, 2}).map σ := hrefl 1
  have hR01 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 0) (π 1) : Set G), Bs⁆ =
      (coordBlockSL (GaloisField 2 2) {0, 1}).map σ := hrefl 0
  obtain ⟨hw, hτ⟩ := hLF.permSL_swap_normalizer hBs hA (by norm_num) (i := 1) (j := 3)
    (by decide)
  set P : SL(4, GaloisField 2 2) := TypeA.permSL (Equiv.swap (1 : Fin 4) 3) with hPdef
  have hP : (coordBlockSL (GaloisField 2 2) ({0, 1} : Finset (Fin 4))).map
      (MulAut.conj P).toMonoidHom = coordBlockSL (GaloisField 2 2) {3, 0} := by
    have hset : ({0, 1} : Finset (Fin 4)).map (Equiv.swap (1 : Fin 4) 3).symm.toEmbedding =
        {3, 0} := by decide
    rw [hcb, hcb, ← hset]
    refine CFSG.SeitzReduction.LinearPilot.map_conj_blockSpecialLinear_of_mul_eq P ?_
    rw [hPdef, TypeA.coe_permSL]
    exact CFSG.SeitzReduction.LinearPilot.blockComplProj_mul_permMatrix _ _
  have hσP : (MulAut.conj (σ P)).toMonoidHom.comp σ = σ.comp (MulAut.conj P).toMonoidHom := by
    refine MonoidHom.ext fun u => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  have hR30 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 3) (π 0) : Set G), Bs⁆ =
      (coordBlockSL (GaloisField 2 2) {3, 0}).map σ := by
    have h := ggReflComm_map_conj_of_permAut hw hτ (π 0) (π 1)
    rw [swap_apply_ne (π := π) (i := 1) (j := 3) (k := 0) (by decide) (by decide),
      Equiv.swap_apply_left] at h
    rw [ggBsCoordEq_comm (π 3) (π 0), ← h, hR01, Subgroup.map_map, hσP, ← Subgroup.map_map, hP]
  exact crossing_even_four hF hBs hyB hK hdim (lift_of_LFrame hBs hLF hA) hd S hSK hSeq hRK σ
    hR12 hR30

theorem crossing_odd_four_of_LFrame [Finite G]
    (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2)
    (hd : d = 1) (S : Fin n → Subgroup G)
    (hSK : ∀ a : Fin 3, S (π a.succ) =
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a})).map κ)
    (hSeq : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)) (τ : Equiv.Perm (Fin n)),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut τ →
        ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (τ i))
    (hRK : ∀ a b : Fin 3, a ≠ b →
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
        ((coordBlockSL (AdjoinRoot g) {a, b}).map (CoordSL.theta g ε)).map κ)
    {L : Subgroup G} {σ : SL(4, GaloisField 2 2) →* G}
    {χ : Multiplicative (ZMod 3) →* (GaloisField 2 2)ˣ}
    (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3) :
    ∀ x ∈ ggBlockComm Bs eta {π 1, π 2} ⊓
        Subgroup.centralizer (ggBlockComm Bs eta {π 3} : Set G),
      ∀ z ∈ ggBlockComm Bs eta {π 0}, x * z = z * x :=
  crossing_odd_four hF hBs hyB hK hdim (lift_of_LFrame hBs hLF hA) hd S hSK hSeq hRK

end GGSecFiveBPermQTwoKFrame

end CFSG.StandardType

end
