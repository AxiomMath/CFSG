module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCtx
public import CFSG.LocalAnalysis.WeakClosure81.W19Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem kpack_mem_normalizer_iff_cj_eq {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] {g : LGL 2 W} {A : Subgroup (LGL 2 W)} :
    g ∈ Subgroup.normalizer (A : Set (LGL 2 W)) ↔ cj g A = A :=
  Subgroup.mem_normalizer_iff_map_conj_eq

private theorem kpack_normalizer_le_normalizer_centralizer (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
  Subgroup.le_normalizer_of_normal_subgroupOf (H := Subgroup.centralizer (X : Set G))
    (K := Subgroup.normalizer (X : Set G))
    (Subgroup.centralizer_le_normalizer (X : Set G))

private theorem kpack_relIndex_inf_le_relIndex_sup (A B : Subgroup G) :
    (A ⊓ B).relIndex A ≤ B.relIndex (A ⊔ B) := by
  have hcard : (A ⊓ B).relIndex A = (B.subgroupOf A).index := by
    show ((A ⊓ B).subgroupOf A).index = (B.subgroupOf A).index
    rw [Subgroup.inf_subgroupOf_left]
  rw [hcard]
  exact Finite.card_le_of_embedding
    (Subgroup.quotientSubgroupOfEmbeddingOfLE (α := G) B (le_sup_left : A ≤ A ⊔ B))

private theorem kpack_padicValNat_two_lt_of_lt_pow {n j : ℕ} (hn0 : n ≠ 0)
    (hn : n < 2 ^ j) : padicValNat 2 n < j :=
  (padicValNat_le_nat_log n).trans_lt (Nat.log_lt_of_lt_pow hn0 hn)

private theorem kpack_mem_sup_of_le_normalizer {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) {x : G} :
    x ∈ A ⊔ C ↔ ∃ a ∈ A, ∃ c ∈ C, a * c = x := by
  constructor
  · intro hx
    have hx' : x ∈ (A : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A C hAC]
      exact hx
    exact Set.mem_mul.mp hx'
  · rintro ⟨a, ha, c, hc, rfl⟩
    show a * c ∈ (↑(A ⊔ C) : Set G)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A C hAC]
    exact Set.mem_mul.mpr ⟨a, ha, c, hc, rfl⟩

private theorem kpack_conj_mem {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) {a : G} (ha : a ∈ A) {c : G} (hc : c ∈ C) :
    a * c * a⁻¹ ∈ C :=
  (Subgroup.mem_normalizer_iff.mp (hAC ha) c).mp hc

private theorem kpack_sq_mem_of_mem_sup {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) (hA2 : ∀ a ∈ A, a * a = 1) {x : G}
    (hx : x ∈ A ⊔ C) : x * x ∈ C := by
  obtain ⟨a, ha, c, hc, rfl⟩ := (kpack_mem_sup_of_le_normalizer hAC).mp hx
  have h1 : (a * c) * (a * c) = (a * c * a⁻¹) * (a * a) * c := by group
  rw [h1, hA2 a ha, mul_one]
  exact C.mul_mem (kpack_conj_mem hAC ha hc) hc

private theorem kpack_commutator_mem_of_mem_sup {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G))
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) {x y : G} (hx : x ∈ A ⊔ C)
    (hy : y ∈ A ⊔ C) : x * y * x⁻¹ * y⁻¹ ∈ C := by
  obtain ⟨a, ha, c, hc, rfl⟩ := (kpack_mem_sup_of_le_normalizer hAC).mp hx
  obtain ⟨a', ha', c', hc', rfl⟩ := (kpack_mem_sup_of_le_normalizer hAC).mp hy
  have hkey : (a * c) * (a' * c') * (a * c)⁻¹ * (a' * c')⁻¹ =
      (a * c * a⁻¹) * ((a * a') * c' * (a * a')⁻¹) *
        ((a * a') * c⁻¹ * (a * a')⁻¹) *
        ((a * a' * a⁻¹) * c'⁻¹ * (a * a' * a⁻¹)⁻¹) * (a * a' * a⁻¹ * a'⁻¹) := by
    group
  rw [hkey]
  have h1 : a * c * a⁻¹ ∈ C := kpack_conj_mem hAC ha hc
  have h2 : (a * a') * c' * (a * a')⁻¹ ∈ C :=
    kpack_conj_mem hAC (A.mul_mem ha ha') hc'
  have h3 : (a * a') * c⁻¹ * (a * a')⁻¹ ∈ C :=
    kpack_conj_mem hAC (A.mul_mem ha ha') (C.inv_mem hc)
  have h4 : (a * a' * a⁻¹) * c'⁻¹ * (a * a' * a⁻¹)⁻¹ ∈ C :=
    kpack_conj_mem hAC (A.mul_mem (A.mul_mem ha ha') (A.inv_mem ha)) (C.inv_mem hc')
  have h5 : a * a' * a⁻¹ * a'⁻¹ = 1 := by rw [hAcomm a ha a' ha']; group
  rw [h5, mul_one]
  exact C.mul_mem (C.mul_mem (C.mul_mem h1 h2) h3) h4

namespace Gam183

variable {V H E : Subgroup G} {i : ℕ}

theorem conj (hE : H ≤ normalizer (E : Set G)) {g y : G} (hy : y ∈ H) (hg : Gam183 V H E i g) :
    Gam183 V H E i (g * y) :=
  (Gam188.conj hE hy (k := E3.mQuot (vInH V H g) (vInH V H g ⊓ Subgroup.centralizer (E : Set G)))
    ⟨hg, le_rfl⟩).1

end Gam183

namespace Hyp183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem quadratic_of_ne_bot (h : Hyp183 D V₀ V H i) {g : G}
    (hE : eOmegaZ H D.T ⊓ conjSubgroup V₀ g ≠ ⊥) :
    ⁅⁅eOmegaZ H D.T, vInH V H g⁆, vInH V H g⁆ = ⊥ := by
  set E : Subgroup G := eOmegaZ H D.T with hEeq
  set A : Subgroup G := vInH V H g with hAeq
  have hAE : A ≤ conjSubgroup V g := inf_le_left
  have hlt : (⊥ : Subgroup G) < E ⊓ conjSubgroup V₀ g := bot_lt_iff_ne_bot.mpr hE
  obtain ⟨w, hw, hwbot⟩ := SetLike.exists_of_lt hlt
  have hw1 : w ≠ 1 := fun h1 => hwbot (Subgroup.mem_bot.mpr h1)
  have hwCent : E ≤ Subgroup.centralizer ({w} : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr h.isElemAbelian_eOmegaZ.1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw.1))
  have hwM : E ≤ conjSubgroup D.M g :=
    hwCent.trans (centralizer_le_conj_M h.setting h.ne_bot g hw.2 hw1)
  have hMnormg : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, h.setting.normalizer_eq]
  have hEnorm : E ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    rw [hMnormg]
    exact hwM
  have hcomm1 : ⁅E, A⁆ ≤ conjSubgroup V g := by
    refine Subgroup.commutator_le.mpr fun e he a ha => ?_
    have haV : a ∈ conjSubgroup V g := hAE ha
    have h1 : e * a * e⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.mp (hEnorm he) a).mp haV
    rw [commutatorElement_def]
    exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem haV)
  have hcomm2 : ⁅⁅E, A⁆, A⁆ ≤ ⁅conjSubgroup V g, conjSubgroup V g⁆ :=
    Subgroup.commutator_mono hcomm1 hAE
  have hVg_bot : ⁅conjSubgroup V g, conjSubgroup V g⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (E3.isElemAbelian_conjSubgroup h.setting.isElemAbelian g).1)
  exact le_bot_iff.mp (hcomm2.trans_eq hVg_bot)

end Hyp183

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem inCalA_pre (x : Ctx188 D V₀ V H i j) {g : G} (hg : Gam183 V H (eOmegaZ H D.T) i g)
    {A : Subgroup G}
    (hA : A = vInH V H g ⊔ (H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G))) :
    H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ A ∧ A ≤ H ∧
      ¬ A ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) ∧
      (∀ x ∈ A, ∀ y ∈ A,
        x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (eOmegaZ H D.T : Set G)) ∧
      (∀ x ∈ A, x * x ∈ Subgroup.centralizer (eOmegaZ H D.T : Set G)) := by
  subst hA
  set E : Subgroup G := eOmegaZ H D.T with hEeq
  set Dg : Subgroup G := vInH V H g with hDgeq
  set C : Subgroup G := H ⊓ Subgroup.centralizer (E : Set G) with hCeq
  have hAH : Dg ≤ H := inf_le_right
  have hAab : IsElemAbelian 2 Dg :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  have hCnormH : H ≤ Subgroup.normalizer (C : Set G) := by
    rw [hCeq]
    exact (le_inf H.le_normalizer
      ((Hyp183.normalizer_eOmegaZ H D.T).trans
        (kpack_normalizer_le_normalizer_centralizer E))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAC : Dg ≤ Subgroup.normalizer (C : Set G) := hAH.trans hCnormH
  have hAcomm : ∀ a ∈ Dg, ∀ a' ∈ Dg, a * a' = a' * a := fun a ha a' ha' => hAab.comm ha ha'
  have hA2 : ∀ a ∈ Dg, a * a = 1 := fun a ha => by simpa [pow_two] using hAab.2 a ha
  have hCle : C ≤ Subgroup.centralizer (E : Set G) := by rw [hCeq]; exact inf_le_right
  refine ⟨le_sup_right, sup_le hAH ?_, ?_, ?_, ?_⟩
  · rw [hCeq]; exact inf_le_left
  · intro hle
    exact hg.2 (le_sup_left.trans hle)
  · intro a ha b hb
    exact hCle (kpack_commutator_mem_of_mem_sup hAC hAcomm ha hb)
  · intro a ha
    exact hCle (kpack_sq_mem_of_mem_sup hAC hA2 ha)

theorem exists_index_witness_of_sixth (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {B : Subgroup G}
    (hCB : H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ B)
    (hBA : B ≤ vInH V H g ⊔ (H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)))
    (hidx : B.relIndex
      (vInH V H g ⊔ (H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G))) < 2 ^ j)
    (hne : eOmegaZ H D.T ⊓ Subgroup.centralizer
        ((vInH V H g ⊔ (H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) : Subgroup G) :
          Set G) ≠
      eOmegaZ H D.T ⊓ Subgroup.centralizer (B : Set G)) :
    ∃ B₀ : Subgroup G, B₀ ≤ vInH V H g ∧
      vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ B₀ ∧
      E3.mQuot (vInH V H g) B₀ + 1 ≤ j ∧
      eOmegaZ H D.T ⊓ Subgroup.centralizer (vInH V H g : Set G) ≠
        eOmegaZ H D.T ⊓ Subgroup.centralizer (B₀ : Set G) := by
  classical
  set E : Subgroup G := eOmegaZ H D.T with hEeq
  set Dg : Subgroup G := vInH V H g with hDgeq
  set C : Subgroup G := H ⊓ Subgroup.centralizer (E : Set G) with hCeq
  have hAH : Dg ≤ H := inf_le_right
  have hsup : Dg ⊔ B = Dg ⊔ C :=
    le_antisymm (sup_le le_sup_left hBA) (sup_le le_sup_left (hCB.trans le_sup_right))
  have hrel : (B ⊓ Dg).relIndex Dg ≤ B.relIndex (Dg ⊔ C) := by
    have h1 := kpack_relIndex_inf_le_relIndex_sup Dg B
    rw [inf_comm, hsup] at h1
    exact h1
  have hrel_lt : (B ⊓ Dg).relIndex Dg < 2 ^ j := hrel.trans_lt hidx
  have hmq : E3.mQuot Dg (B ⊓ Dg) + 1 ≤ j := by
    have hn0 : (B ⊓ Dg).relIndex Dg ≠ 0 := E3.relIndex_ne_zero' Dg (B ⊓ Dg)
    have hlt : padicValNat 2 ((B ⊓ Dg).relIndex Dg) < j :=
      kpack_padicValNat_two_lt_of_lt_pow hn0 hrel_lt
    unfold E3.mQuot
    omega
  refine ⟨B ⊓ Dg, inf_le_right, ?_, hmq, ?_⟩
  · rintro e ⟨heDg, heC⟩
    exact ⟨hCB ⟨hAH heDg, heC⟩, heDg⟩
  · intro heq
    apply hne
    apply le_antisymm
    · exact inf_le_inf_left E (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBA))
    · rintro e ⟨heE, heB⟩
      have heB₀ : e ∈ Subgroup.centralizer ((B ⊓ Dg : Subgroup G) : Set G) :=
        Subgroup.centralizer_le
          (SetLike.coe_subset_coe.mpr (inf_le_left : B ⊓ Dg ≤ B)) heB
      have heDg : e ∈ Subgroup.centralizer (Dg : Set G) := by
        have hmem : e ∈ E ⊓ Subgroup.centralizer ((B ⊓ Dg : Subgroup G) : Set G) :=
          ⟨heE, heB₀⟩
        rw [← heq] at hmem
        exact hmem.2
      have heC : e ∈ Subgroup.centralizer (C : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact (Subgroup.mem_centralizer_iff.mp hc.2 e heE).symm
      have hle : Dg ⊔ C ≤ Subgroup.centralizer ({e} : Set G) := by
        refine sup_le ?_ ?_
        · rw [Subgroup.mem_centralizer_iff] at heDg
          intro d hd
          exact Subgroup.mem_centralizer_singleton_iff.mpr (heDg d hd)
        · rw [Subgroup.mem_centralizer_iff] at heC
          intro c hc
          exact Subgroup.mem_centralizer_singleton_iff.mpr (heC c hc)
      exact ⟨heE, fun a ha =>
        (Subgroup.mem_centralizer_iff.mp (hle ha) e (Set.mem_singleton e)).symm⟩

theorem exists_index_witness (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) :
    ∃ B : Subgroup G, B ≤ vInH V H g ∧
      vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ B ∧
      E3.mQuot (vInH V H g) B + 1 ≤ j ∧
      eOmegaZ H D.T ⊓ Subgroup.centralizer (vInH V H g : Set G) ≠
        eOmegaZ H D.T ⊓ Subgroup.centralizer (B : Set G) := by
  classical
  have hab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  obtain ⟨c1, c2, c3, c4, c5⟩ := x.inCalA_pre hg rfl
  have hnot := x.not_inCalA (vInH V H g) inf_le_right hab
  by_contra hcon
  refine hnot ?_
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InCalA
  refine ⟨c1, c2, c3, c4, c5, fun B hCB hBA hidx => ?_⟩
  by_contra hne
  exact hcon (x.exists_index_witness_of_sixth hg hCB hBA hidx hne)

theorem exists_comm_witness (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) :
    ∃ B : Subgroup G, B ≤ vInH V H g ∧
      vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ B ∧
      E3.mQuot (vInH V H g) B + 1 ≤ j ∧
      ∃ e ∈ eOmegaZ H D.T ⊓ Subgroup.centralizer (B : Set G), ∃ d ∈ vInH V H g,
        ⁅e, d⁆ ≠ 1 ∧ ⁅e, d⁆ ∈ eOmegaZ H D.T ⊓ conjSubgroup V₀ g := by
  classical
  set E : Subgroup G := eOmegaZ H D.T with hEeq
  set Dg : Subgroup G := vInH V H g with hDgeq
  obtain ⟨B, hBD, hBC, hB1, hne⟩ := x.exists_index_witness hg
  have hCentLe : E ⊓ Subgroup.centralizer (Dg : Set G) ≤
      E ⊓ Subgroup.centralizer (B : Set G) :=
    inf_le_inf_left E (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBD))
  obtain ⟨e, heB, heNotDg⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hCentLe hne)
  have heE : e ∈ E := heB.1
  have heNotCent : e ∉ Subgroup.centralizer (Dg : Set G) := fun h => heNotDg ⟨heE, h⟩
  have hx : ∃ d ∈ Dg, d * e ≠ e * d := by
    by_contra h
    apply heNotCent
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    by_contra hde
    exact h ⟨d, hd, hde⟩
  obtain ⟨d, hd, hde⟩ := hx
  have hcomm_ne : ⁅e, d⁆ ≠ 1 := fun h1 =>
    hde ((commutatorElement_eq_one_iff_mul_comm.1 h1).symm)
  have hk : (j - 1) + i < mBar D.M V₀ V x.hyp.setting.isElemAbelian := by
    have h1 := x.bound
    have h2 := x.two_le
    omega
  have hBk : E3.mQuot Dg B ≤ j - 1 := by
    change E3.mQuot (vInH V H g) B ≤ j - 1
    omega
  have hmem : ⁅e, d⁆ ∈ E ⊓ conjSubgroup V₀ g :=
    (x.comm_le (k := j - 1) hk hg hBD hBk)
      (Subgroup.commutator_mem_commutator ⟨heE, heB.2⟩ hd)
  exact ⟨B, hBD, hBC, hB1, e, ⟨heE, heB.2⟩, d, hd, hcomm_ne, hmem⟩

theorem inf_ne_bot_of_gam183 (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) : eOmegaZ H D.T ⊓ conjSubgroup V₀ g ≠ ⊥ := by
  obtain ⟨-, -, -, -, e, -, d, -, hne, hmem⟩ := x.exists_comm_witness hg
  intro hbot
  rw [hbot] at hmem
  exact hne (Subgroup.mem_bot.1 hmem)

@[expose] def packFamilyU (D : Data G) (V H : Subgroup G) (i : ℕ)
    (M : ModDataE H (eOmegaZ H D.T)) : Set (Subgroup (LGL 2 M.W)) :=
  {A | ∃ g : G, Gam183 V H (eOmegaZ H D.T) i g ∧ A = M.img (vInH V H g)}

@[expose] noncomputable def packSpaceU (D : Data G) (V₀ V H : Subgroup G) (i : ℕ)
    (M : ModDataE H (eOmegaZ H D.T)) (A : Subgroup (LGL 2 M.W)) : Submodule (ZMod 2) M.W :=
  ⨆ g : {g : G // Gam183 V H (eOmegaZ H D.T) i g ∧ M.img (vInH V H g) = A},
    M.sp (conjSubgroup V₀ g.1)

theorem comm_mem_conj_of_img_eq (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {g g' : G} (hg' : Gam183 V H (eOmegaZ H D.T) i g')
    (himg : M.img (vInH V H g) = M.img (vInH V H g')) {B : Subgroup G}
    (hBD : B ≤ vInH V H g)
    (hBC : vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ B)
    (hB : E3.mQuot (vInH V H g) B + 1 ≤ j) {e d : G}
    (he : e ∈ eOmegaZ H D.T ⊓ Subgroup.centralizer (B : Set G)) (hd : d ∈ vInH V H g) :
    ⁅e, d⁆ ∈ conjSubgroup V₀ g' := by
  classical
  have hdH : d ∈ H := hd.2
  have heE : e ∈ eOmegaZ H D.T := he.1
  have hcommE : ∀ {a : G}, a ∈ H → ∀ {e : G}, e ∈ eOmegaZ H D.T →
      ⁅a, e⁆ ∈ eOmegaZ H D.T := by
    intro a ha e he
    have h1 : a * e * a⁻¹ ∈ eOmegaZ H D.T :=
      (Subgroup.mem_normalizer_iff.1 (Hyp183.normalizer_eOmegaZ H D.T ha) e).1 he
    rw [commutatorElement_def]
    exact (eOmegaZ H D.T).mul_mem h1 ((eOmegaZ H D.T).inv_mem he)
  have hρ : M.ρ ⟨d, hdH⟩ ∈ M.img (vInH V H g) := M.mem_img.2 ⟨⟨d, hdH⟩, hd, rfl⟩
  have hρ' : M.ρ ⟨d, hdH⟩ ∈ M.img (vInH V H g') := by
    rw [← himg]
    exact hρ
  obtain ⟨j', hj'D', hj'ρ⟩ := M.mem_img.1 hρ'
  have hcomm_eq : ⁅d, e⁆ = ⁅(j' : G), e⁆ := by
    apply M.ι_injOn (hcommE hdH heE) (hcommE j'.2 heE)
    rw [M.ι_commutator hdH heE, M.ι_commutator (j := (j' : G)) j'.2 heE]
    exact (congrArg (fun r => r (M.ι e) - M.ι e) hj'ρ).symm
  have hde_eq : ⁅e, d⁆ = ⁅e, (j' : G)⁆ := by
    apply inv_injective
    rw [commutatorElement_inv, commutatorElement_inv, hcomm_eq]
  have hB_le_img : M.img B ≤ M.img (vInH V H g') := (M.img_mono hBD).trans_eq himg
  obtain ⟨B₀, hB₀D', hB₀C', hB₀img⟩ :=
    M.exists_preimage (A := vInH V H g') inf_le_right hB_le_img
  have hB₀H : B₀ ≤ H := hB₀D'.trans inf_le_right
  have hDgab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  have hDg'ab : IsElemAbelian 2 (vInH V H g') :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g').mono inf_le_left
  have hmOf_g := M.mOf_img (A := vInH V H g) inf_le_right hDgab hBD hBC
  have hmOf_g' := M.mOf_img (A := vInH V H g') inf_le_right hDg'ab hB₀D' hB₀C'
  have hmQ : E3.mQuot (vInH V H g') B₀ = E3.mQuot (vInH V H g) B := by
    calc E3.mQuot (vInH V H g') B₀ = mOf (M.img (vInH V H g')) (M.img B₀) := hmOf_g'.symm
      _ = mOf (M.img (vInH V H g)) (M.img B) := by rw [← himg, hB₀img]
      _ = E3.mQuot (vInH V H g) B := hmOf_g
  have hsp_eq : M.sp (Subgroup.centralizer (B : Set G)) =
      M.sp (Subgroup.centralizer (B₀ : Set G)) := by
    rw [← M.fixSub_img (hBD.trans inf_le_right), ← M.fixSub_img hB₀H, hB₀img]
  have heCentB₀ : e ∈ Subgroup.centralizer (B₀ : Set G) := by
    have hmem : M.ι e ∈ M.sp (Subgroup.centralizer (B₀ : Set G)) := by
      rw [← hsp_eq]
      exact ⟨e, ⟨he.2, heE⟩, rfl⟩
    obtain ⟨e'', he''B₀E, he''ι⟩ := M.mem_sp.1 hmem
    have heq : e'' = e := M.ι_injOn he''B₀E.2 heE he''ι
    rw [← heq]
    exact he''B₀E.1
  have hk : (j - 1) + i < mBar D.M V₀ V x.hyp.setting.isElemAbelian := by
    have h1 := x.bound
    have h2 := x.two_le
    omega
  have hBk : E3.mQuot (vInH V H g') B₀ ≤ j - 1 := by rw [hmQ]; omega
  have hmem : ⁅e, (j' : G)⁆ ∈
      ⁅eOmegaZ H D.T ⊓ Subgroup.centralizer (B₀ : Set G), vInH V H g'⁆ :=
    Subgroup.commutator_mem_commutator ⟨heE, heCentB₀⟩ hj'D'
  have hmem' : ⁅e, (j' : G)⁆ ∈ eOmegaZ H D.T ⊓ conjSubgroup V₀ g' :=
    (x.comm_le (k := j - 1) hk hg' hB₀D' hBk) hmem
  rw [← hde_eq] at hmem'
  exact hmem'.2

theorem packSpaceU_eq (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) {g g' : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) (hg' : Gam183 V H (eOmegaZ H D.T) i g')
    (himg : M.img (vInH V H g) = M.img (vInH V H g')) :
    M.sp (conjSubgroup V₀ g) = M.sp (conjSubgroup V₀ g') := by
  obtain ⟨B, hBD, hBC, hB, e, he, d, hd, hne, hmem⟩ := x.exists_comm_witness hg
  have hmem' : ⁅e, d⁆ ∈ conjSubgroup V₀ g' :=
    x.comm_mem_conj_of_img_eq M hg' himg hBD hBC hB he hd
  have hbot : conjSubgroup V₀ g ⊓ conjSubgroup V₀ g' ≠ ⊥ := fun h =>
    hne (Subgroup.mem_bot.1 (h ▸ (⟨hmem.2, hmem'⟩ :
      ⁅e, d⁆ ∈ conjSubgroup V₀ g ⊓ conjSubgroup V₀ g')))
  exact congrArg M.sp (Hyp183.conj_eq_of_inf_ne_bot x.hyp hbot).1

theorem packSpaceU_eq_apply (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) :
    packSpaceU D V₀ V H i M (M.img (vInH V H g)) = M.sp (conjSubgroup V₀ g) := by
  apply le_antisymm
  · exact iSup_le fun g' => le_of_eq (x.packSpaceU_eq M g'.2.1 hg g'.2.2)
  · exact le_iSup (fun g' : {g₁ : G // Gam183 V H (eOmegaZ H D.T) i g₁ ∧
      M.img (vInH V H g₁) = M.img (vInH V H g)} => M.sp (conjSubgroup V₀ g'.1)) ⟨g, hg, rfl⟩

theorem packU_ne_bot (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, A ≠ ⊥ := by
  rintro A ⟨h, hg, rfl⟩ hbot
  have hle : vInH V H h ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
    intro d hd
    have hdH : d ∈ H := hd.2
    have h1 : M.ρ ⟨d, hdH⟩ = 1 := by
      have hmem : M.ρ ⟨d, hdH⟩ ∈ M.img (vInH V H h) :=
        M.mem_img.2 ⟨⟨d, hdH⟩, hd, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    exact (M.ρ_eq_one_iff ⟨d, hdH⟩).1 h1
  exact hg.2 hle

theorem packU_inf_pCore (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, A ⊓ pCoreOf 2 (M.img H) = ⊥ := fun A _ => by
  rw [x.pCoreOf_img_eq_bot M, inf_bot_eq]

theorem packU_normalizer_eq (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, M.img H ⊓ Subgroup.normalizer (A : Set (LGL 2 M.W)) =
      stabilizerOf (M.img H) (packSpaceU D V₀ V H i M A) := by
  rintro A ⟨g, hg, rfl⟩
  rw [x.packSpaceU_eq_apply M hg]
  ext r
  constructor
  · rintro ⟨hrG, hrN⟩
    obtain ⟨y, hyH, rfl⟩ := M.mem_img.1 hrG
    refine ⟨M.mem_img.2 ⟨y, y.2, rfl⟩, ?_⟩
    have hNA : cj (M.ρ y) (M.img (vInH V H g)) = M.img (vInH V H g) :=
      cj_eq_of_mem_normalizer hrN
    rw [M.img_conj (A := vInH V H g) inf_le_right y, ← vInH_mul g (H.inv_mem y.2)] at hNA
    have hgy : Gam183 V H (eOmegaZ H D.T) i (g * (y : G)⁻¹) :=
      Gam183.conj (Hyp183.normalizer_eOmegaZ H D.T) (H.inv_mem y.2) hg
    rw [M.conjSub_sp (conjSubgroup V₀ g) y, conjSubgroup_conjSubgroup]
    exact x.packSpaceU_eq M hgy hg hNA
  · rintro ⟨hrG, hrS⟩
    obtain ⟨y, hyH, rfl⟩ := M.mem_img.1 hrG
    refine ⟨M.mem_img.2 ⟨y, y.2, rfl⟩, ?_⟩
    apply kpack_mem_normalizer_iff_cj_eq.mpr
    rw [M.img_conj (A := vInH V H g) inf_le_right y, ← vInH_mul g (H.inv_mem y.2)]
    rw [M.conjSub_sp (conjSubgroup V₀ g) y, conjSubgroup_conjSubgroup] at hrS
    have hspg_ne : M.sp (conjSubgroup V₀ g) ≠ ⊥ := by
      intro hbot
      have hbot' : conjSubgroup V₀ g ⊓ eOmegaZ H D.T = ⊥ := (M.sp_eq_bot_iff).1 hbot
      rw [inf_comm] at hbot'
      exact x.inf_ne_bot_of_gam183 hg hbot'
    have hsp_inf : M.sp (conjSubgroup V₀ g ⊓ conjSubgroup V₀ (g * (y : G)⁻¹)) ≠ ⊥ := by
      rw [M.sp_inf, hrS, inf_idem]
      exact hspg_ne
    have hne : conjSubgroup V₀ g ⊓ conjSubgroup V₀ (g * (y : G)⁻¹) ≠ ⊥ := by
      intro hbot
      exact hsp_inf ((M.sp_eq_bot_iff).2 (by rw [hbot, bot_inf_eq]))
    have hce := Hyp183.conj_eq_of_inf_ne_bot x.hyp hne
    have hD : vInH V H (g * (y : G)⁻¹) = vInH V H g := by
      unfold vInH
      rw [hce.2.symm]
    rw [hD]

theorem packU_disjoint (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, ∀ B ∈ packFamilyU D V H i M, A ≠ B →
      packSpaceU D V₀ V H i M A ⊓ packSpaceU D V₀ V H i M B = ⊥ := by
  rintro A ⟨g, hg, rfl⟩ B ⟨g', hg', rfl⟩ hAB
  rw [x.packSpaceU_eq_apply M hg, x.packSpaceU_eq_apply M hg']
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  by_contra hv0
  have hsp_ne : M.sp (conjSubgroup V₀ g ⊓ conjSubgroup V₀ g') ≠ ⊥ := by
    intro hbot
    have hmem : v ∈ (⊥ : Submodule (ZMod 2) M.W) := by
      rw [← hbot, M.sp_inf]
      exact hv
    rw [Submodule.mem_bot] at hmem
    exact hv0 hmem
  have hne : conjSubgroup V₀ g ⊓ conjSubgroup V₀ g' ≠ ⊥ := fun hbot =>
    hsp_ne ((M.sp_eq_bot_iff).2 (by rw [hbot, bot_inf_eq]))
  have hD : vInH V H g = vInH V H g' := by
    unfold vInH
    rw [(Hyp183.conj_eq_of_inf_ne_bot x.hyp hne).2]
  exact hAB (by rw [hD])

theorem packU_cond2 (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, ∀ B : Subgroup (LGL 2 M.W), B ≤ A → mOf A B ≤ x.iStar →
      CFSG.Quasithin.G11.commSpace A (fixSub B) ≤ packSpaceU D V₀ V H i M A := by
  rintro A ⟨g, hg, rfl⟩ B hBA hBk
  obtain ⟨B₀, hB₀D, hB₀C, hB₀img⟩ := M.exists_preimage (A := vInH V H g) inf_le_right hBA
  have hB₀H : B₀ ≤ H := hB₀D.trans inf_le_right
  have hDab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  have hmOf : E3.mQuot (vInH V H g) B₀ ≤ x.iStar := by
    rw [← M.mOf_img (A := vInH V H g) inf_le_right hDab hB₀D hB₀C, hB₀img]
    exact hBk
  have hfix : fixSub B = M.sp (Subgroup.centralizer (B₀ : Set G)) := by
    rw [← hB₀img]
    exact M.fixSub_img hB₀H
  have hle : ⁅Subgroup.centralizer (B₀ : Set G) ⊓ eOmegaZ H D.T, vInH V H g⁆ ≤
      conjSubgroup V₀ g := by
    rw [inf_comm]
    exact (x.comm_le x.iStar_add_lt hg hB₀D hmOf).trans inf_le_right
  calc CFSG.Quasithin.G11.commSpace (M.img (vInH V H g)) (fixSub B)
      = CFSG.Quasithin.G11.commSpace (M.img (vInH V H g))
          (M.sp (Subgroup.centralizer (B₀ : Set G))) := by
        rw [hfix]
    _ ≤ M.sp (conjSubgroup V₀ g) := M.commSpace_img_sp_le (A := vInH V H g) inf_le_right hle
    _ = packSpaceU D V₀ V H i M (M.img (vInH V H g)) :=
        (x.packSpaceU_eq_apply M hg).symm

theorem packU_equivariant (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M, ∀ g ∈ M.img H,
      packSpaceU D V₀ V H i M (cj g A) = conjSub g (packSpaceU D V₀ V H i M A) := by
  rintro A ⟨h, hg, rfl⟩ g hgmem
  obtain ⟨y, hyH, rfl⟩ := M.mem_img.1 hgmem
  have hgy : Gam183 V H (eOmegaZ H D.T) i (h * (y : G)⁻¹) :=
    Gam183.conj (Hyp183.normalizer_eOmegaZ H D.T) (H.inv_mem y.2) hg
  have hcj : cj (M.ρ y) (M.img (vInH V H h)) = M.img (vInH V H (h * (y : G)⁻¹)) := by
    rw [M.img_conj (A := vInH V H h) inf_le_right y, vInH_mul h (H.inv_mem y.2)]
  rw [hcj, x.packSpaceU_eq_apply M hgy, x.packSpaceU_eq_apply M hg,
    M.conjSub_sp (conjSubgroup V₀ h) y, conjSubgroup_conjSubgroup]

theorem assumption131U (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    Assumption131 (M.img H) (packFamilyU D V H i M) (packSpaceU D V₀ V H i M) x.iStar := by
  refine
    { pos_i := x.iStar_pos
      le_G := ?_
      isElemAb := ?_
      invariant := ?_
      ne_bot := packU_ne_bot M
      inf_pCore := x.packU_inf_pCore M
      normalizer_eq := x.packU_normalizer_eq M
      disjoint := x.packU_disjoint M
      cond2 := x.packU_cond2 M
      quadratic := ?_
      equivariant := x.packU_equivariant M }
  · rintro A ⟨g, hg, rfl⟩
    exact M.img_mono inf_le_right
  · rintro A ⟨g, hg, rfl⟩
    exact M.isElemAbelian_img
      ((E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left)
  · rintro A ⟨h, hg, rfl⟩ g hgmem
    obtain ⟨y, hyH, rfl⟩ := M.mem_img.1 hgmem
    refine ⟨h * (y : G)⁻¹,
      Gam183.conj (Hyp183.normalizer_eOmegaZ H D.T) (H.inv_mem y.2) hg, ?_⟩
    rw [M.img_conj (A := vInH V H h) inf_le_right y, vInH_mul h (H.inv_mem y.2)]
  · rintro A ⟨g, hg, rfl⟩
    exact M.commSpace_commSub_img_eq_bot (A := vInH V H g) inf_le_right
      (x.hyp.quadratic_of_ne_bot (x.inf_ne_bot_of_gam183 hg))

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
