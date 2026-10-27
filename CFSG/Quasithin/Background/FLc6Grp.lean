module

public import CFSG.Quasithin.Background.FLcR2C
public import CFSG.Quasithin.Background.FLc2Simple
public import CFSG.Quasithin.Background.FLcP0Ker
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.FLcR2A

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G]

theorem le_normalizer_sup {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hA' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hx)
  have hB' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hx)
  rw [Subgroup.map_sup, hA', hB']

theorem oTwoUpper_le_of_le_sup {L S P : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hn : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L) (hP : P ≤ L ⊔ S) : oTwoUpper P ≤ L := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  obtain ⟨l, hl, s, hs, rfl⟩ := mem_sup_prod_of_conj hn x (hP hx)
  obtain ⟨a, ha⟩ := hS ⟨s, hs⟩
  have hsa : s ^ (2 ^ a) = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  obtain ⟨l', hl', hm⟩ := exists_pow_mem_of_normalizes hn hl hs (2 ^ a)
  rw [hsa, mul_one] at hm
  exact ⟨a, by rw [hm]; exact hl'⟩

@[expose] def yNode (L S : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) (i : ℕ) : Subgroup G :=
  oTwoUpper (parab (L ⊔ S) n W i)

@[expose] def kNode (L S : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) : Subgroup G :=
  yNode L S n W 1 ⊔ yNode L S n W 2

@[expose] def qNode (L S : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) : Subgroup G :=
  pCoreOf 2 (parab (L ⊔ S) n W 2)

@[expose] def gNode (L S : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) : Subgroup G :=
  kNode L S n W ⊔ qNode L S n W

theorem yNode_le_parab (L S : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G) (i : ℕ) :
    yNode L S n W i ≤ parab (L ⊔ S) n W i :=
  CFSG.Quasithin.oTwoUpper_le _

theorem mem_stated_of_gl_two {n : ℕ} (g : GL (Fin n) (ZMod 2)) :
    g ∈ CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

theorem yNode_le_L (i : ℕ) : yNode L S n W i ≤ L :=
  oTwoUpper_le_of_le_sup D.S2 D.S_norm (parab_le _ _ _ _)

theorem kNode_le_L : kNode L S n W ≤ L := sup_le (D.yNode_le_L 1) (D.yNode_le_L 2)

theorem S_le_normalizer_yNode (i : ℕ) : S ≤ Subgroup.normalizer (yNode L S n W i : Set G) :=
  (D.S_le_parab i).trans (le_normalizer_oTwoUpper _)

theorem S_le_normalizer_kNode : S ≤ Subgroup.normalizer (kNode L S n W : Set G) :=
  le_normalizer_sup (D.S_le_normalizer_yNode 1) (D.S_le_normalizer_yNode 2)

theorem qNode_le_S [Finite G] : qNode L S n W ≤ S := D.pCoreOf_le_S_node 2

theorem qNode_le_normalizer_kNode [Finite G] :
    qNode L S n W ≤ Subgroup.normalizer (kNode L S n W : Set G) :=
  D.qNode_le_S.trans D.S_le_normalizer_kNode

omit D in
theorem qNode_isPGroup [Finite G] : IsPGroup 2 ↥(qNode L S n W) := pCoreOf_isPGroup 2 _

omit D in
theorem yNode_le_normalizer_W (i k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) (hki : k ≠ i) :
    yNode L S n W i ≤ Subgroup.normalizer (W k : Set G) := fun _ hx =>
  (mem_parab.1 (yNode_le_parab L S n W i hx)).2 k hk1 hkn hki

omit D in
theorem kNode_le_normalizer_W (k : ℕ) (hk3 : 3 ≤ k) (hkn : k < n) :
    kNode L S n W ≤ Subgroup.normalizer (W k : Set G) :=
  sup_le (yNode_le_normalizer_W 1 k (by omega) hkn (by omega))
    (yNode_le_normalizer_W 2 k (by omega) hkn (by omega))

theorem qNode_le_normalizer_W [Finite G] (k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    qNode L S n W ≤ Subgroup.normalizer (W k : Set G) := D.qNode_le_S.trans (D.W_norm k hk1 hkn)

theorem gNode_le_sup [Finite G] : gNode L S n W ≤ L ⊔ S :=
  sup_le (D.kNode_le_L.trans le_sup_left) (D.qNode_le_S.trans le_sup_right)

omit D in
theorem kNode_le_gNode : kNode L S n W ≤ gNode L S n W := le_sup_left

omit D in
theorem qNode_le_gNode : qNode L S n W ≤ gNode L S n W := le_sup_right

theorem gNode_le_normalizer_W [Finite G] (k : ℕ) (hk3 : 3 ≤ k) (hkn : k < n) :
    gNode L S n W ≤ Subgroup.normalizer (W k : Set G) :=
  sup_le (kNode_le_normalizer_W k hk3 hkn) (D.qNode_le_normalizer_W k (by omega) hkn)

theorem S_le_normalizer_qNode : S ≤ Subgroup.normalizer (qNode L S n W : Set G) :=
  (D.S_le_parab 2).trans (le_normalizer_pCoreOf 2 _)

theorem S_le_normalizer_gNode : S ≤ Subgroup.normalizer (gNode L S n W : Set G) :=
  le_normalizer_sup D.S_le_normalizer_kNode D.S_le_normalizer_qNode

end P0Setup

@[expose] def blk3 {n : ℕ} (hn : 3 ≤ n) (g : SLt n) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => mat g (Fin.castLE hn i) (Fin.castLE hn j)

theorem sum_eq_sum_castLE {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 3 ≤ n) (f : Fin n → M)
    (hf : ∀ k : Fin n, 3 ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k : Fin 3, f (Fin.castLE hn k) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hn) (f := f)
    (fun x _ y _ hxy => Fin.castLE_injective hn hxy)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro k _ hk
  apply hf
  by_contra hlt
  push Not at hlt
  exact hk (Finset.mem_image.2 ⟨⟨k.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem blk3_mul {n : ℕ} (hn : 3 ≤ n) (g h : SLt n)
    (hh : h ∈ stabilizer (flagSpace n (ZMod 2) 3)) :
    blk3 hn (g * h) = blk3 hn g * blk3 hn h := by
  ext i j
  simp only [blk3, mat_mul, Matrix.mul_apply]
  rw [sum_eq_sum_castLE hn (fun k => mat g (Fin.castLE hn i) k * mat h k (Fin.castLE hn j))
    (fun k hk => by rw [stab_entry_zero hh (by simp) hk, mul_zero])]

theorem blk3_one {n : ℕ} (hn : 3 ≤ n) : blk3 hn (1 : SLt n) = 1 := by
  ext i j
  simp [blk3, Matrix.one_apply, Fin.castLE_inj]

theorem det_blk3 {n : ℕ} (hn : 3 ≤ n) {g : SLt n}
    (hg : g ∈ stabilizer (flagSpace n (ZMod 2) 3)) : (blk3 hn g).det = 1 := by
  have h1 : blk3 hn g * blk3 hn g⁻¹ = 1 := by
    rw [← blk3_mul hn g g⁻¹ ((stabilizer _).inv_mem hg), mul_inv_cancel, blk3_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one] at h2
  generalize (blk3 hn g).det = a at h2 ⊢
  generalize (blk3 hn g⁻¹).det = b at h2
  revert a b
  decide

@[expose] def blk3Hom {n : ℕ} (hn : 3 ≤ n) : ↥(stabilizer (flagSpace n (ZMod 2) 3)) →* SLt 3 :=
  MonoidHom.mk' (fun g => ⟨blk3 hn g.1, det_blk3 hn g.2⟩)
    (fun g h => Subtype.ext (blk3_mul hn g.1 h.1 h.2))

@[expose] def a3T1 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def b3T2 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 1, 0]

theorem blk3_T1 {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) : blk3 h3 (T1 n h3) = a3T1 := by
  rcases hn with rfl | rfl <;> decide +revert

theorem blk3_T2 {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) : blk3 h3 (T2 n h3) = b3T2 := by
  rcases hn with rfl | rfl <;> decide +revert

@[expose] def gen3A : SLt 3 := ⟨a3T1, by decide⟩

@[expose] def gen3B : SLt 3 := ⟨b3T2, by decide⟩

@[expose] def wordEval3 : List Bool → SLt 3
  | [] => 1
  | b :: w => (if b then gen3B else gen3A) * wordEval3 w

theorem wordEval3_mem (H : Subgroup (SLt 3)) (hA : gen3A ∈ H) (hB : gen3B ∈ H) :
    ∀ w : List Bool, wordEval3 w ∈ H
  | [] => H.one_mem
  | b :: w => by
    cases b
    · exact H.mul_mem hA (wordEval3_mem H hA hB w)
    · exact H.mul_mem hB (wordEval3_mem H hA hB w)

theorem transvection_words :
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) = wordEval3 [false, true, false, false, true, true, false, false, true] ∧
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 2) = wordEval3 [false, true, false, true, true, false, false, true, true] ∧
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2) = wordEval3 [true, false, false, true, true, false, false, true, false] ∧
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 2) = wordEval3 [false, true, true, false, false, true, true, false, true, true] ∧
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : ZMod 2) = wordEval3 [false, false, true, true, false, false, true, false, true] ∧
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) = wordEval3 [false, true, true, false, false, true, true, false, true] := by
  decide

theorem closure_gen3A_gen3B : Subgroup.closure ({gen3A, gen3B} : Set (SLt 3)) = ⊤ := by
  set H := Subgroup.closure ({gen3A, gen3B} : Set (SLt 3)) with hH
  have hA : gen3A ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : gen3B ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨w01, w02, w10, w12, w20, w21⟩ := transvection_words
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 3) (K := ZMod 2), Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp only [Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
    exact H.one_mem
  · simp only [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [w01]; exact wordEval3_mem H hA hB _
    · rw [w02]; exact wordEval3_mem H hA hB _
    · rw [w10]; exact wordEval3_mem H hA hB _
    · exact absurd rfl hij
    · rw [w12]; exact wordEval3_mem H hA hB _
    · rw [w20]; exact wordEval3_mem H hA hB _
    · rw [w21]; exact wordEval3_mem H hA hB _
    · exact absurd rfl hij

theorem T1_mem_Qn {n : ℕ} (h3 : 3 ≤ n) : T1 n h3 ∈ Qn n 1 :=
  (Qn n 1).mul_mem (Ut_le_Qn n 1 (tv_mem_Ut _)) (reflection_mem_Qn (by norm_num) (by omega))

theorem T2_mem_Qn {n : ℕ} (h3 : 3 ≤ n) : T2 n h3 ∈ Qn n 2 :=
  (Qn n 2).mul_mem (Ut_le_Qn n 2 (tv_mem_Ut _)) (reflection_mem_Qn (by norm_num) (by omega))

theorem T1_mem_stab3 {n : ℕ} (h3 : 3 ≤ n) (h4 : 3 < n) :
    T1 n h3 ∈ stabilizer (flagSpace n (ZMod 2) 3) :=
  mem_Qn.1 (T1_mem_Qn h3) 3 (by norm_num) h4 (by norm_num)

theorem T2_mem_stab3 {n : ℕ} (h3 : 3 ≤ n) (h4 : 3 < n) :
    T2 n h3 ∈ stabilizer (flagSpace n (ZMod 2) 3) :=
  mem_Qn.1 (T2_mem_Qn h3) 3 (by norm_num) h4 (by norm_num)

theorem fixes_of_blk3_eq_one {n : ℕ} (hn : 3 ≤ n) {g : SLt n}
    (hg : g ∈ stabilizer (flagSpace n (ZMod 2) 3)) (hb : blk3 hn g = 1) {v : Vt n}
    (hv : v ∈ flagSpace n (ZMod 2) 3) : mat g *ᵥ v = v := by
  rw [mem_flagSpace] at hv
  ext r
  show ∑ c, mat g r c * v c = v r
  by_cases hr : r.val < 3
  · rw [sum_eq_sum_castLE hn (fun c => mat g r c * v c)
      (fun c hc => by rw [hv c hc, mul_zero])]
    have hr' : r = Fin.castLE hn ⟨r.val, hr⟩ := Fin.ext rfl
    have h1 : ∀ c : Fin 3, mat g r (Fin.castLE hn c) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) ⟨r.val, hr⟩ c := by
      intro c
      rw [← hb]
      simp only [blk3]
      rw [← hr']
    simp only [h1, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [← hr']
  · have hr3 : 3 ≤ r.val := by omega
    rw [hv r hr3]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c.val < 3
    · rw [stab_entry_zero hg hc hr3, zero_mul]
    · rw [hv c (by omega), mul_zero]

theorem mem_Ut_of_blk3_eq_one {n : ℕ} (hn : 3 ≤ n) (h3n : 3 < n) {g : SLt n}
    (hst : ∀ j, 3 ≤ j → j < n → g ∈ stabilizer (flagSpace n (ZMod 2) j))
    (hb : blk3 hn g = 1) : g ∈ Ut n := by
  have hg3 := hst 3 le_rfl h3n
  have hfix : ∀ v ∈ flagSpace n (ZMod 2) 3, mat g *ᵥ v = v := fun v hv =>
    fixes_of_blk3_eq_one hn hg3 hb hv
  refine mem_Ut_of_stab_all fun j hj1 hjn => ?_
  by_cases hj : 3 ≤ j
  · exact hst j hj hjn
  · apply mem_stabilizer_of_forall
    intro v hv
    have := hfix v (flagSpace_mono (by omega) hv)
    rw [this]
    exact hv

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

theorem alphaOn_mem_stab {K : Subgroup G} (hK : K ≤ L)
    (hKW : K ≤ Subgroup.normalizer (W 3 : Set G)) (h3n : 3 < n) (x : ↥K) :
    D.α ⟨(x : G), hK x.2⟩ ∈ stabilizer (flagSpace n (ZMod 2) 3) :=
  (D.mem_normalizer_W (by norm_num) h3n ⟨(x : G), hK x.2⟩).1 (hKW x.2)

@[expose] noncomputable def phiOn {K : Subgroup G} (hK : K ≤ L)
    (hKW : K ≤ Subgroup.normalizer (W 3 : Set G)) (h3n : 3 < n) : ↥K →* SLt 3 :=
  (blk3Hom h3n.le).comp ((D.α.comp (Subgroup.inclusion hK)).codRestrict _
    (D.alphaOn_mem_stab hK hKW h3n))

@[expose] noncomputable def phiK (hn : n = 4 ∨ n = 5) : ↥(kNode L S n W) →* SLt 3 :=
  D.phiOn D.kNode_le_L (kNode_le_normalizer_W 3 le_rfl (by omega)) (by omega)

theorem phiK_val (hn : n = 4 ∨ n = 5) (x : ↥(kNode L S n W)) :
    ((D.phiK hn x : SLt 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      blk3 (by omega : 3 ≤ n) (D.α ⟨(x : G), D.kNode_le_L x.2⟩) := rfl

theorem phiK_ker_two [Finite G] (hn : n = 4 ∨ n = 5) (x : ↥(kNode L S n W))
    (hx : D.phiK hn x = 1) : ∃ k : ℕ, (x : G) ^ 2 ^ k = 1 := by
  have h3n : 3 < n := by omega
  have hb : blk3 (by omega : 3 ≤ n) (D.α ⟨(x : G), D.kNode_le_L x.2⟩) = 1 := by
    have := congrArg (fun y : SLt 3 => (y : Matrix (Fin 3) (Fin 3) (ZMod 2))) hx
    simpa [phiK_val] using this
  have hU : D.α ⟨(x : G), D.kNode_le_L x.2⟩ ∈ Ut n := by
    refine mem_Ut_of_blk3_eq_one (by omega) h3n (fun j hj3 hjn => ?_) hb
    exact (D.mem_normalizer_W (by omega) hjn ⟨(x : G), D.kNode_le_L x.2⟩).1
      (kNode_le_normalizer_W j hj3 hjn x.2)
  exact D.two_elt_of_Ut (dec_self (L := L) (S := S) (UL := UL) ⟨(x : G), D.kNode_le_L x.2⟩) hU

omit D in
theorem mem_of_sq_mem_A {H : Subgroup (SLt 3)} (h : gen3A * gen3A ∈ H) : gen3A ∈ H := by
  have e : gen3A = (gen3A * gen3A) * (gen3A * gen3A) := by decide
  rw [e]
  exact H.mul_mem h h

omit D in
theorem mem_of_sq_mem_B {H : Subgroup (SLt 3)} (h : gen3B * gen3B ∈ H) : gen3B ∈ H := by
  have e : gen3B = (gen3B * gen3B) * (gen3B * gen3B) := by decide
  rw [e]
  exact H.mul_mem h h

theorem phiK_surjective [Finite G] (hn : n = 4 ∨ n = 5) : Function.Surjective (D.phiK hn) := by
  have h3 : 3 ≤ n := by omega
  have h3n : 3 < n := by omega
  obtain ⟨hT1, hT2, -⟩ := node_compute hn h3
  have hA : gen3A ∈ (D.phiK hn).range := by
    obtain ⟨l, hodd, hl⟩ := D.exists_odd_lift hT1
    have hαl : D.α l ∈ Qn n 1 := by
      rcases hl with h | h
      · rw [h]; exact T1_mem_Qn h3
      · rw [h]; exact (Qn n 1).mul_mem (T1_mem_Qn h3) (T1_mem_Qn h3)
    have hlP : (l : G) ∈ parab (L ⊔ S) n W 1 := D.mem_parab_of_alpha l hαl
    have hlK : (l : G) ∈ kNode L S n W :=
      Subgroup.mem_sup_left (show (l : G) ∈ yNode L S n W 1 from mem_oTwoUpper_of_odd hlP hodd)
    have hφ : ((D.phiK hn ⟨(l : G), hlK⟩ : SLt 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        blk3 h3 (D.α l) := rfl
    rcases hl with h | h
    · refine ⟨⟨(l : G), hlK⟩, Subtype.ext ?_⟩
      rw [hφ, h, blk3_T1 hn h3]
      rfl
    · refine mem_of_sq_mem_A (H := (D.phiK hn).range) ⟨⟨(l : G), hlK⟩, Subtype.ext ?_⟩
      rw [hφ, h, blk3_mul h3 _ _ (T1_mem_stab3 h3 h3n), blk3_T1 hn h3]
      rfl
  have hB : gen3B ∈ (D.phiK hn).range := by
    obtain ⟨l, hodd, hl⟩ := D.exists_odd_lift hT2
    have hαl : D.α l ∈ Qn n 2 := by
      rcases hl with h | h
      · rw [h]; exact T2_mem_Qn h3
      · rw [h]; exact (Qn n 2).mul_mem (T2_mem_Qn h3) (T2_mem_Qn h3)
    have hlP : (l : G) ∈ parab (L ⊔ S) n W 2 := D.mem_parab_of_alpha l hαl
    have hlK : (l : G) ∈ kNode L S n W :=
      Subgroup.mem_sup_right (show (l : G) ∈ yNode L S n W 2 from mem_oTwoUpper_of_odd hlP hodd)
    have hφ : ((D.phiK hn ⟨(l : G), hlK⟩ : SLt 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        blk3 h3 (D.α l) := rfl
    rcases hl with h | h
    · refine ⟨⟨(l : G), hlK⟩, Subtype.ext ?_⟩
      rw [hφ, h, blk3_T2 hn h3]
      rfl
    · refine mem_of_sq_mem_B (H := (D.phiK hn).range) ⟨⟨(l : G), hlK⟩, Subtype.ext ?_⟩
      rw [hφ, h, blk3_mul h3 _ _ (T2_mem_stab3 h3 h3n), blk3_T2 hn h3]
      rfl
  have htop : (D.phiK hn).range = ⊤ := by
    rw [eq_top_iff, ← closure_gen3A_gen3B, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hA
    · simpa using hB
  intro y
  have : y ∈ (D.phiK hn).range := by rw [htop]; trivial
  exact this

theorem phiK_ker [Finite G] (hn : n = 4 ∨ n = 5) :
    (D.phiK hn).ker = CFSG.pCore 2 ↥(kNode L S n W) := by
  apply le_antisymm
  · refine le_sSup ⟨(D.phiK hn).normal_ker, ?_⟩
    refine isPGroup_two_of_forall (G := ↥(kNode L S n W)) fun x hx => ?_
    obtain ⟨k, hk⟩ := D.phiK_ker_two hn x hx
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hnorm : (CFSG.pCore 2 ↥(kNode L S n W)).Normal := CFSG.pCore_normal (p := 2) (G := ↥(kNode L S n W))
    have hpg : IsPGroup 2 ↥(CFSG.pCore 2 ↥(kNode L S n W)) := CFSG.pCore_isPGroup (p := 2) (G := ↥(kNode L S n W))
    have hmapnorm : ((CFSG.pCore 2 ↥(kNode L S n W)).map (D.phiK hn)).Normal :=
      Subgroup.Normal.map hnorm _ (D.phiK_surjective hn)
    have := hmapnorm
    rcases (isSimpleGroup_SLt (le_refl 3)).eq_bot_or_eq_top_of_normal
      ((CFSG.pCore 2 ↥(kNode L S n W)).map (D.phiK hn)) with h | h
    · have hmem : D.phiK hn x ∈ (CFSG.pCore 2 ↥(kNode L S n W)).map (D.phiK hn) := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      apply not_isPGroup_SLt (by norm_num : 2 ≤ 3)
      intro g
      have hg : g ∈ (CFSG.pCore 2 ↥(kNode L S n W)).map (D.phiK hn) := by rw [h]; trivial
      obtain ⟨c, hc, rfl⟩ := hg
      obtain ⟨k, hk⟩ := hpg ⟨c, hc⟩
      refine ⟨k, ?_⟩
      have h1 : c ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [← map_pow, h1, map_one]

omit D in
theorem isSolvable_of_two_elts {X : Subgroup G} [Finite G]
    (h : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k = 1) : Group.IsSolvable ↥X := by
  have hp : IsPGroup 2 ↥X := isPGroup_two_of_forall h
  have : Group.IsNilpotent ↥X := hp.isNilpotent
  infer_instance

omit D in
theorem kNode_ne_bot_aux [Finite G] {K : Subgroup G} (φ : ↥K →* SLt 3)
    (hφ : Function.Surjective φ) : K ≠ ⊥ := by
  intro hK
  obtain ⟨x, hx⟩ := hφ gen3A
  have hx1 : x = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall K).1 hK (x : G) x.2)
  have : gen3A = 1 := by rw [← hx, hx1, map_one]
  revert this
  decide

theorem kNode_mem_cComp_self [Finite G] (hn : n = 4 ∨ n = 5) :
    kNode L S n W ∈ cComp (kNode L S n W) := by
  have hperf : ⁅kNode L S n W, kNode L S n W⁆ = kNode L S n W := D.rank2_c hn
  have hsurj := D.phiK_surjective hn
  refine ⟨kNode_ne_bot_aux (D.phiK hn) hsurj, hperf, IsSubnormal.refl _, fun K' hlt hne' hperf' hsub => ?_⟩
  obtain ⟨P, hPK, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt hsub hlt
  have hPle : P ≤ kNode L S n W := hPK.le
  have hmapn : ((P.subgroupOf (kNode L S n W)).map (D.phiK hn)).Normal :=
    Subgroup.Normal.map hPn _ hsurj
  have := hmapn
  rcases (isSimpleGroup_SLt (le_refl 3)).eq_bot_or_eq_top_of_normal
    ((P.subgroupOf (kNode L S n W)).map (D.phiK hn)) with h | h
  ·
    have hP2 : ∀ x ∈ P, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
      intro x hx
      have hmem : (⟨x, hPle hx⟩ : ↥(kNode L S n W)) ∈ P.subgroupOf (kNode L S n W) := hx
      have h1 : D.phiK hn ⟨x, hPle hx⟩ ∈ (P.subgroupOf (kNode L S n W)).map (D.phiK hn) := ⟨_, hmem, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact D.phiK_ker_two hn ⟨x, hPle hx⟩ h1
    have hsol : Group.IsSolvable ↥K' := isSolvable_of_two_elts fun x hx => hP2 x (hK'P hx)
    have h1 := (isSolvable_iff_perfectCore_eq_bot K').mp hsol
    rw [perfectCore_eq_self_of_perfect hperf'] at h1
    exact hne' h1
  ·
    set N : Subgroup G := (D.phiK hn).ker.map (kNode L S n W).subtype with hN
    have hNK : N ≤ kNode L S n W := Subgroup.map_subtype_le _
    have hN2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := D.phiK_ker_two hn y hy
      exact ⟨k, hk⟩
    have hKPN : kNode L S n W = P ⊔ N := by
      refine le_antisymm (fun x hx => ?_) (sup_le hPle hNK)
      have h1 : D.phiK hn ⟨x, hx⟩ ∈ (P.subgroupOf (kNode L S n W)).map (D.phiK hn) := by
        rw [h]; trivial
      obtain ⟨p, hp, hpx⟩ := h1
      have hker : (p⁻¹ * ⟨x, hx⟩ : ↥(kNode L S n W)) ∈ (D.phiK hn).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
      have hxN : (((p⁻¹ * ⟨x, hx⟩ : ↥(kNode L S n W)) : ↥(kNode L S n W)) : G) ∈ N := ⟨_, hker, rfl⟩
      have hpP : (p : G) ∈ P := hp
      have : x = (p : G) * (((p⁻¹ * ⟨x, hx⟩ : ↥(kNode L S n W)) : ↥(kNode L S n W)) : G) := by
        simp
      rw [this]
      exact (P ⊔ N).mul_mem (Subgroup.mem_sup_left hpP) (Subgroup.mem_sup_right hxN)
    have hle := perfectCore_le_of_sup_solvable hPle hPn hKPN (isSolvable_of_two_elts hN2)
    rw [perfectCore_eq_self_of_perfect hperf] at hle
    exact hPK.ne (le_antisymm hPle hle)

theorem kNode_mem_cComp_gNode [Finite G] (hn : n = 4 ∨ n = 5) :
    kNode L S n W ∈ cComp (gNode L S n W) := by
  have hK := D.kNode_mem_cComp_self hn
  have hnorm : gNode L S n W ≤ Subgroup.normalizer (kNode L S n W : Set G) :=
    sup_le Subgroup.le_normalizer D.qNode_le_normalizer_kNode
  exact cComp_mem_of_subnormal (A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hnorm)) hK

theorem fixes_of_centralizes {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) {l : ↥L}
    (hl : (l : G) ∈ Subgroup.centralizer (W k : Set G)) {v : Vt n}
    (hv : v ∈ flagSpace n (ZMod 2) k) : mat (D.α l) *ᵥ v = v := by
  set u : ↥UL := D.β.symm (Multiplicative.ofAdd v) with hu
  have hβu : Multiplicative.toAdd (D.β u) = v := by
    rw [hu, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have huk : (u : G) ∈ W k := by
    refine (D.W_mem hk1 hkn u).2 ⟨u.2, ?_⟩
    show Multiplicative.toAdd (D.β u) ∈ _
    rw [hβu]
    exact hv
  have h1 : (u : G) * (l : G) = (l : G) * (u : G) := Subgroup.mem_centralizer_iff.1 hl _ huk
  have h4 : (u : G) = (l : G) * (u : G) * (l : G)⁻¹ := by
    calc (u : G) = (u : G) * (l : G) * (l : G)⁻¹ := by group
      _ = (l : G) * (u : G) * (l : G)⁻¹ := by rw [h1]
  have h5 := D.rel l u u h4
  rw [hβu] at h5
  exact h5.symm

theorem blk3_eq_one_of_centralizes (h3n : 3 < n) {l : ↥L}
    (hl : (l : G) ∈ Subgroup.centralizer (W 3 : Set G)) :
    blk3 h3n.le (D.α l) = 1 := by
  ext i j
  have hv : (Pi.single (Fin.castLE h3n.le j) (1 : ZMod 2) : Vt n) ∈ flagSpace n (ZMod 2) 3 := by
    rw [mem_flagSpace]
    intro r hr
    have : r ≠ Fin.castLE h3n.le j := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    simp [this]
  have h1 := congrFun (D.fixes_of_centralizes (by norm_num) h3n hl hv) (Fin.castLE h3n.le i)
  simp only [Matrix.mulVec_single_one] at h1
  simp only [blk3, Matrix.one_apply]
  rw [show (mat (D.α l)) (Fin.castLE h3n.le i) (Fin.castLE h3n.le j) =
    (Pi.single (Fin.castLE h3n.le j) (1 : ZMod 2) : Vt n) (Fin.castLE h3n.le i) from h1]
  simp [Pi.single_apply, Fin.castLE_inj]

theorem inf_centralizer_isPGroup [Finite G] (hn : n = 4 ∨ n = 5) :
    IsPGroup 2 ↥(kNode L S n W ⊓ Subgroup.centralizer (W 3 : Set G)) := by
  refine isPGroup_two_of_forall fun x hx => ?_
  have h3n : 3 < n := by omega
  have hb := D.blk3_eq_one_of_centralizes h3n (l := ⟨x, D.kNode_le_L hx.1⟩) hx.2
  have h1 : D.phiK hn ⟨x, hx.1⟩ = 1 := Subtype.ext (by
    rw [phiK_val]
    exact hb)
  exact D.phiK_ker_two hn ⟨x, hx.1⟩ h1

omit D in
theorem inf_centralizer_le_pCoreOf_of_kernel [Finite G] {L' Q U : Subgroup G}
    (hQL : Q ≤ Subgroup.normalizer (L' : Set G)) (hLQU : L' ⊔ Q ≤ Subgroup.normalizer (U : Set G))
    (hker : IsPGroup 2 ↥(L' ⊓ Subgroup.centralizer (U : Set G))) (hQ : IsPGroup 2 ↥Q) :
    (L' ⊔ Q) ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 (L' ⊔ Q) := by
  have hXN : L' ⊔ Q ≤ Subgroup.normalizer
      (((L' ⊔ Q) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      le_normalizer_of_conj_mem (X := Subgroup.normalizer (U : Set G))
        (fun p hp y hy => conj_mem_centralizer hp hy) (hLQU hx)⟩
  have hX2 : IsPGroup 2 ↥((L' ⊔ Q) ⊓ Subgroup.centralizer (U : Set G)) := by
    rintro ⟨x, hxLQ, hxC⟩
    have hxLQ' : x ∈ ((L' ⊔ Q : Subgroup G) : Set G) := hxLQ
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L' Q hQL] at hxLQ'
    obtain ⟨l, hl, q, hq, hlq⟩ := hxLQ'
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hQ
    obtain ⟨l', hl', hpow⟩ := A4.exists_pow_mul_eq hl (hQL hq) (Nat.card ↥Q)
    have hq1 : q ^ Nat.card ↥Q = 1 := by
      have : (⟨q, hq⟩ : ↥Q) ^ Nat.card ↥Q = 1 := pow_card_eq_one'
      exact congrArg Subtype.val this
    have hlq' : l * q = x := hlq
    rw [hq1, mul_one, hlq'] at hpow
    have hmem : x ^ Nat.card ↥Q ∈ L' ⊓ Subgroup.centralizer (U : Set G) :=
      ⟨by rw [hpow]; exact hl', Subgroup.pow_mem _ hxC _⟩
    obtain ⟨k, hk⟩ := hker ⟨_, hmem⟩
    have h1 : (x ^ Nat.card ↥Q) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨a + k, Subtype.ext ?_⟩
    have h2 : x ^ 2 ^ (a + k) = 1 := by
      rw [← h1, ← pow_mul, ha, pow_add]
    simpa using h2
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hXN hX2

theorem UL_sq {u : G} (hu : u ∈ UL) : u * u = 1 := by
  have h1 : D.β (⟨u, hu⟩ * ⟨u, hu⟩) = 1 := by
    rw [map_mul]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_one]
    generalize Multiplicative.toAdd (D.β ⟨u, hu⟩) = v
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize v i = a
    revert a
    decide
  have h2 : (⟨u, hu⟩ * ⟨u, hu⟩ : ↥UL) = 1 := D.β.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem UL_comm {u v : G} (hu : u ∈ UL) (hv : v ∈ UL) : u * v = v * u := by
  have h1 : D.β (⟨u, hu⟩ * ⟨v, hv⟩) = D.β (⟨v, hv⟩ * ⟨u, hu⟩) := by
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val (D.β.injective h1)

theorem UL_isPGroup : IsPGroup 2 ↥UL := by
  refine isPGroup_two_of_forall fun x hx => ⟨1, ?_⟩
  simpa [pow_two] using D.UL_sq hx

theorem UL_le_qNode [Finite G] (hUL : UL ≤ L ⊔ S) : UL ≤ qNode L S n W := by
  have hP : UL ≤ parab (L ⊔ S) n W 2 := fun u hu => mem_parab.2 ⟨hUL hu, fun j hj1 hjn _ =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun w hw =>
      D.UL_comm (D.W_le j hj1 hjn hw) hu)⟩
  exact le_pCoreOf_of_le_normalizer 2 hP
    ((parab_le _ _ _ _).trans (sup_le D.L_le D.S_le)) D.UL_isPGroup

theorem charTwo_gNode [Finite G] (hn : n = 4 ∨ n = 5) (hUL : UL ≤ L ⊔ S) :
    CharTwo (gNode L S n W) := by
  intro x hx
  have hULq := D.UL_le_qNode hUL
  have hULG : UL ≤ gNode L S n W := hULq.trans le_sup_right
  have hGUL : gNode L S n W ≤ Subgroup.normalizer (UL : Set G) :=
    sup_le (D.kNode_le_L.trans D.L_le) (D.qNode_le_S.trans D.S_le)
  have hULO : UL ≤ pCoreOf 2 (gNode L S n W) := le_pCoreOf_of_le_normalizer 2 hULG hGUL D.UL_isPGroup
  have hxW : x ∈ Subgroup.centralizer (W 3 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.1 hx.2 w (hULO (D.W_le 3 (by norm_num) (by omega) hw))
  exact inf_centralizer_le_pCoreOf_of_kernel D.qNode_le_normalizer_kNode
    (D.gNode_le_normalizer_W 3 le_rfl (by omega)) (D.inf_centralizer_isPGroup hn) qNode_isPGroup
    ⟨hx.1, hxW⟩

end P0Setup

theorem isPSL_of_equiv_SLt {X : Type} [Group X] {n : ℕ} (hn : 3 ≤ n) (e : X ≃* SLt n) :
    IsPSL n 2 1 X := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, ZMod 2, inferInstance, inferInstance,
    by simp, ?_⟩
  · intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  · exact ⟨e.trans ((slEquivGLt n).trans
      (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hK n).symm)⟩

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

theorem isRankTwoLie2Derived_kNode [Finite G] (hn : n = 4 ∨ n = 5) :
    IsRankTwoLie2Derived ((↥(kNode L S n W) ⧸ CFSG.pCore 2 ↥(kNode L S n W)) ⧸
      Subgroup.center (↥(kNode L S n W) ⧸ CFSG.pCore 2 ↥(kNode L S n W))) := by
  have hnorm : (CFSG.pCore 2 ↥(kNode L S n W)).Normal := CFSG.pCore_normal (p := 2) (G := ↥(kNode L S n W))
  let e1 : (↥(kNode L S n W) ⧸ CFSG.pCore 2 ↥(kNode L S n W)) ≃* SLt 3 :=
    (QuotientGroup.quotientMulEquivOfEq (D.phiK_ker hn).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (D.phiK hn) (D.phiK_surjective hn))
  have hcenter : Subgroup.center (↥(kNode L S n W) ⧸ CFSG.pCore 2 ↥(kNode L S n W)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact center_trivial_of_equiv e1 (fun h => Subgroup.mem_center_iff.1 hz h)
  let e2 : ((↥(kNode L S n W) ⧸ CFSG.pCore 2 ↥(kNode L S n W)) ⧸
      Subgroup.center (↥(kNode L S n W) ⧸ CFSG.pCore 2 ↥(kNode L S n W))) ≃*
      (↥(kNode L S n W) ⧸ CFSG.pCore 2 ↥(kNode L S n W)) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact Or.inl ⟨1, isPSL_of_equiv_SLt le_rfl (e2.trans e1)⟩

omit D in
theorem blk2_sq_of_two_pow {m m' : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hm : m * m' = 1) {k : ℕ}
    (hk : m ^ 2 ^ k = 1) : m * m = 1 := by
  have h6 : m ^ 6 = 1 := gl2_pow_six m m' hm
  cases k with
  | zero =>
    have : m = 1 := by simpa using hk
    rw [this]
    simp
  | succ k =>
    have hn : (m ^ 2) ^ 2 ^ k = 1 := by rw [← pow_mul, ← pow_succ']; exact hk
    have h3 : (m ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact h6
    have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have : (m ^ 2) ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.2 ⟨hn, h3⟩
    rw [hg, pow_one] at this
    rw [← pow_two]
    exact this

@[expose] def blk2T2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 1, 0]

omit D in
theorem blk2_key : ∀ (t₁ t' m : Matrix (Fin 2) (Fin 2) (ZMod 2)),
    (t₁ = blk2T2 ∨ t₁ = blk2T2 * blk2T2) → t' * t₁ = 1 → m * m = 1 →
    (m * (t₁ * m * t')) * (m * (t₁ * m * t')) = 1 → m = 1 := by
  decide

omit D in
theorem blk_T2 {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) :
    blk (ix 1 (by omega)) (ix 2 (by omega)) (T2 n h3) = blk2T2 := by
  rcases hn with rfl | rfl <;> decide +revert

omit D in
theorem T1_entry {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) :
    mat (T1 n h3) (ix 1 (by omega)) (ix 0 (by omega)) = 1 ∧
      mat (T1 n h3 * T1 n h3) (ix 1 (by omega)) (ix 0 (by omega)) = 1 := by
  rcases hn with rfl | rfl <;> decide +revert

theorem blk_sq_of_two_elt [Finite G] (hn2 : 2 + 1 < n) {P Q : Fin n} (hP : P.val + 1 = 2)
    (hQ : Q.val = 2) {x : G} (hx : x ∈ parab (L ⊔ S) n W 2) {lx : ↥L} (hd : Dec L S UL x lx)
    (h2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : blk P Q (D.α lx) * blk P Q (D.α lx) = 1 := by
  obtain ⟨k, hk⟩ := h2
  have hα : D.α lx ∈ Qn n 2 := D.alpha_mem_Qn hx hd
  have hne : P ≠ Q := fun h => by rw [h] at hP; omega
  have hdk := D.dec_pow hd (2 ^ k)
  rw [hk] at hdk
  obtain ⟨c, hc, hxc⟩ := hdk
  have h1 : D.α (lx ^ 2 ^ k) = 1 := by
    apply D.alpha_eq_one_of_mem_centralizer
    have : ((lx ^ 2 ^ k : ↥L) : G) = c⁻¹ := eq_inv_of_mul_eq_one_left hxc.symm
    rw [this]
    exact (Subgroup.centralizer _).inv_mem hc.1
  have h2 : (blk P Q (D.α lx)) ^ 2 ^ k = 1 := by
    rw [← blk_pow_Qn (by norm_num) hn2 hP hQ hα, ← map_pow, h1]
    exact blk_one hne
  have hinv : blk P Q (D.α lx) * blk P Q (D.α lx)⁻¹ = 1 := by
    rw [← blk_mul_Qn (by norm_num) hn2 hP hQ hα ((Qn n 2).inv_mem hα), mul_inv_cancel]
    exact blk_one hne
  exact blk2_sq_of_two_pow hinv h2

theorem inf_le_parab [Finite G] :
    gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G) ≤ parab (L ⊔ S) n W 2 := by
  intro x hx
  refine mem_parab.2 ⟨D.gNode_le_sup hx.1, fun j hj1 hjn hj2 => ?_⟩
  by_cases hj : j = 1
  · subst hj
    exact hx.2
  · exact D.gNode_le_normalizer_W j (by omega) hjn hx.1

theorem pCoreOf_H_le_qNode [Finite G] (hn : n = 4 ∨ n = 5) :
    pCoreOf 2 (gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G)) ≤ qNode L S n W := by
  have h3 : 3 ≤ n := by omega
  have h2n : 2 + 1 < n := by omega
  obtain ⟨-, hT2, -⟩ := node_compute hn h3
  obtain ⟨l₂, hodd₂, hl₂⟩ := D.exists_odd_lift hT2
  have hαl₂ : D.α l₂ ∈ Qn n 2 := by
    rcases hl₂ with h | h
    · rw [h]; exact T2_mem_Qn h3
    · rw [h]; exact (Qn n 2).mul_mem (T2_mem_Qn h3) (T2_mem_Qn h3)
  have hl₂P : (l₂ : G) ∈ parab (L ⊔ S) n W 2 := D.mem_parab_of_alpha l₂ hαl₂
  have hl₂K : (l₂ : G) ∈ kNode L S n W :=
    Subgroup.mem_sup_right (show (l₂ : G) ∈ yNode L S n W 2 from mem_oTwoUpper_of_odd hl₂P hodd₂)
  have hl₂H : (l₂ : G) ∈ gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G) :=
    ⟨Subgroup.mem_sup_left hl₂K, (mem_parab.1 hl₂P).2 1 le_rfl (by omega) (by norm_num)⟩
  have hP : (ix 1 (by omega) : Fin n).val + 1 = 2 := rfl
  have hQ : (ix 2 (by omega) : Fin n).val = 2 := rfl
  set P : Fin n := ix 1 (by omega) with hPdef
  set Q : Fin n := ix 2 (by omega) with hQdef
  have hne : P ≠ Q := fun h => by rw [h] at hP; omega
  have hT2blk : blk P Q (T2 n h3) = blk2T2 := blk_T2 hn h3
  have ht : blk P Q (D.α l₂) = blk2T2 ∨ blk P Q (D.α l₂) = blk2T2 * blk2T2 := by
    rcases hl₂ with h | h
    · left
      rw [h]
      exact hT2blk
    · right
      rw [h, blk_mul_Qn (by norm_num) h2n hP hQ (T2_mem_Qn h3) (T2_mem_Qn h3), hT2blk]
  intro b hb
  have hbH := pCoreOf_le 2 _ hb
  have hbP : b ∈ parab (L ⊔ S) n W 2 := D.inf_le_parab hbH
  obtain ⟨lb, cb, hcb, hbl⟩ := D.decomp (mem_parab.1 hbP).1
  have hdb : Dec L S UL b lb := ⟨cb, hcb, hbl⟩
  have hdl₂ : Dec L S UL (l₂ : G) l₂ := dec_self l₂
  have hb' : (l₂ : G) * b * (l₂ : G)⁻¹ ∈
      pCoreOf 2 (gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G)) :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hl₂H) b).1 hb
  have hx : b * ((l₂ : G) * b * (l₂ : G)⁻¹) ∈
      pCoreOf 2 (gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G)) := Subgroup.mul_mem _ hb hb'
  have hg2 := pCoreOf_isPGroup 2 (gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G))
  have hbP2 : ∃ k : ℕ, b ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hg2 ⟨b, hb⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxP2 : ∃ k : ℕ, (b * ((l₂ : G) * b * (l₂ : G)⁻¹)) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hg2 ⟨_, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxP : b * ((l₂ : G) * b * (l₂ : G)⁻¹) ∈ parab (L ⊔ S) n W 2 :=
    D.inf_le_parab (pCoreOf_le 2 _ hx)
  have hdconj : Dec L S UL ((l₂ : G) * b * (l₂ : G)⁻¹) (l₂ * lb * l₂⁻¹) :=
    D.dec_mul (D.dec_mul hdl₂ hdb) (D.dec_inv hdl₂)
  have hdx : Dec L S UL (b * ((l₂ : G) * b * (l₂ : G)⁻¹)) (lb * (l₂ * lb * l₂⁻¹)) :=
    D.dec_mul hdb hdconj
  have hm : blk P Q (D.α lb) * blk P Q (D.α lb) = 1 :=
    D.blk_sq_of_two_elt h2n hP hQ hbP hdb hbP2
  have hM := D.blk_sq_of_two_elt h2n hP hQ hxP hdx hxP2
  have hαb : D.α lb ∈ Qn n 2 := D.alpha_mem_Qn hbP hdb
  have hαi : (D.α l₂)⁻¹ ∈ Qn n 2 := (Qn n 2).inv_mem hαl₂
  have hblkM : blk P Q (D.α (lb * (l₂ * lb * l₂⁻¹))) =
      blk P Q (D.α lb) * (blk P Q (D.α l₂) * blk P Q (D.α lb) * blk P Q (D.α l₂)⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv,
      blk_mul_Qn (by norm_num) h2n hP hQ hαb ((Qn n 2).mul_mem ((Qn n 2).mul_mem hαl₂ hαb) hαi),
      blk_mul_Qn (by norm_num) h2n hP hQ ((Qn n 2).mul_mem hαl₂ hαb) hαi,
      blk_mul_Qn (by norm_num) h2n hP hQ hαl₂ hαb]
  have htt : blk P Q (D.α l₂)⁻¹ * blk P Q (D.α l₂) = 1 := by
    rw [← blk_mul_Qn (by norm_num) h2n hP hQ hαi hαl₂, inv_mul_cancel]
    exact blk_one hne
  rw [hblkM] at hM
  have hm1 : blk P Q (D.α lb) = 1 :=
    blk2_key (blk P Q (D.α l₂)) (blk P Q (D.α l₂)⁻¹) (blk P Q (D.α lb)) ht htt hm hM
  have hbE : b ∈ D.Ebk (i := 2) (by norm_num) h2n (P := P) (Q := Q) hP hQ :=
    (D.mem_Ebk (i := 2) (by norm_num) h2n hP hQ).2 ⟨hbP, lb, hdb, hm1⟩
  exact D.Ebk_le_pCoreOf (i := 2) (by norm_num) h2n hP hQ hbE

theorem coe_gNode [Finite G] :
    ((gNode L S n W : Subgroup G) : Set G) = (kNode L S n W : Set G) * (qNode L S n W : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ D.qNode_le_normalizer_kNode

theorem ms2 [Finite G] (hn : n = 4 ∨ n = 5) :
    ∃ H' : Subgroup G, H' < gNode L S n W ∧ ¬ 2 ∣ H'.relIndex (gNode L S n W) ∧
      qNode L S n W = pCoreOf 2 H' := by
  have h3 : 3 ≤ n := by omega
  have h1n : 1 < n := by omega
  refine ⟨gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G), ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun h => ?_
    have hle : gNode L S n W ≤ Subgroup.normalizer (W 1 : Set G) := inf_eq_left.1 h
    obtain ⟨hT1, -, -⟩ := node_compute hn h3
    obtain ⟨l₁, hodd, hl⟩ := D.exists_odd_lift hT1
    have hαl : D.α l₁ ∈ Qn n 1 := by
      rcases hl with h | h
      · rw [h]; exact T1_mem_Qn h3
      · rw [h]; exact (Qn n 1).mul_mem (T1_mem_Qn h3) (T1_mem_Qn h3)
    have hlP : (l₁ : G) ∈ parab (L ⊔ S) n W 1 := D.mem_parab_of_alpha l₁ hαl
    have hlK : (l₁ : G) ∈ kNode L S n W :=
      Subgroup.mem_sup_left (show (l₁ : G) ∈ yNode L S n W 1 from mem_oTwoUpper_of_odd hlP hodd)
    have hst : D.α l₁ ∈ stabilizer (flagSpace n (ZMod 2) 1) :=
      (D.mem_normalizer_W le_rfl h1n l₁).1 (hle (kNode_le_gNode hlK))
    have h0 := stab_entry_zero hst (c := ix 0 (by omega)) (r := ix 1 (by omega))
      (by simp [ix]) (by simp [ix])
    obtain ⟨e1, e2⟩ := T1_entry hn h3
    rcases hl with h | h
    · rw [h, e1] at h0
      exact one_ne_zero h0
    · rw [h, e2] at h0
      exact one_ne_zero h0
  · have hSyl : IsSylowTwoOf S (gNode L S n W ⊔ S) :=
      A4.isSylowTwoOf_mono D.syl le_sup_right (sup_le D.gNode_le_sup le_sup_right)
    have hS0 : IsSylowTwoOf (S ⊓ gNode L S n W) (gNode L S n W) :=
      A4.isSylowTwoOf_inf_normal hSyl le_sup_left
        (sup_le Subgroup.le_normalizer D.S_le_normalizer_gNode)
    have hS0H : S ⊓ gNode L S n W ≤ gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G) :=
      fun x hx => ⟨hx.2, D.W_norm 1 le_rfl h1n hx.1⟩
    have h1 := Subgroup.relIndex_mul_relIndex (S ⊓ gNode L S n W)
      (gNode L S n W ⊓ Subgroup.normalizer (W 1 : Set G)) (gNode L S n W) hS0H inf_le_left
    intro hd
    exact hS0.2.2 (dvd_trans hd (Dvd.intro_left _ h1))
  · refine le_antisymm ?_ (D.pCoreOf_H_le_qNode hn)
    refine le_pCoreOf_of_le_normalizer 2 (fun x hx => ⟨qNode_le_gNode hx,
      D.qNode_le_normalizer_W 1 le_rfl h1n hx⟩) ?_ qNode_isPGroup
    exact D.inf_le_parab.trans (le_normalizer_pCoreOf 2 _)

theorem isMSPair_gNode [Finite G] (hn : n = 4 ∨ n = 5) (hUL : UL ≤ L ⊔ S)
    (hsqtk : IsSQTKIn (L ⊔ S))
    (hMS3 : ∀ C : Subgroup G, C ≤ qNode L S n W → C ≠ ⊥ → (C.subgroupOf (qNode L S n W)).Characteristic →
      ¬ gNode L S n W ≤ Subgroup.normalizer (C : Set G)) :
    IsMSPair (gNode L S n W) (qNode L S n W) :=
  ⟨⟨IsSQTKIn.mono hsqtk D.gNode_le_sup, D.charTwo_gNode hn hUL, kNode L S n W, D.kNode_mem_cComp_gNode hn,
    D.coe_gNode, D.isRankTwoLie2Derived_kNode hn⟩, Or.inl (D.ms2 hn), hMS3⟩

theorem exists_isModO2Surj [Finite G] (hn : n = 4 ∨ n = 5) :
    ∃ α : ↥(kNode L S n W) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)),
      IsModO2Surj (kNode L S n W) α := by
  refine ⟨((slEquivGLt 3).toMonoidHom.comp (D.phiK hn)).codRestrict _
    (fun x => mem_stated_of_gl_two _), ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := D.phiK_surjective hn ((slEquivGLt 3).symm y.1)
    refine ⟨x, Subtype.ext ?_⟩
    show (slEquivGLt 3) (D.phiK hn x) = y.1
    rw [hx]
    simp
  · rw [← D.phiK_ker hn]
    ext x
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (slEquivGLt 3) (D.phiK hn x) = 1 := congrArg Subtype.val h
      exact (slEquivGLt 3).injective (by rw [h1, map_one])
    · intro h
      apply Subtype.ext
      show (slEquivGLt 3) (D.phiK hn x) = 1
      rw [h, map_one]

end P0Setup

end CFSG.Quasithin.FLc
