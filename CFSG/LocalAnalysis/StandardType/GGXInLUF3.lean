module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
import CFSG.LocalAnalysis.StandardType.GGSixTCPSLMatrix
import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
import CFSG.LocalAnalysis.StandardType.GGL45TGSU
import CFSG.LocalAnalysis.StandardType.GGPGLToralityMatrix
import CFSG.GroupTheory.TwoWeightData

public section

open scoped Pointwise
attribute [local instance] commutatorElement
namespace CFSG.StandardType.GGXInL
open CFSG.Assembly
variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

section Frame3Aux

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel
open Matrix

private noncomputable def frame3Aux_conjL {H : Type} [Group H] {L' E' : Subgroup H}
    (h : E' ≤ Subgroup.normalizer (L' : Set H)) (b : ↥E') (l : ↥L') : ↥L' :=
  ⟨(b : H) * (l : H) * (b : H)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (h b.2) (l : H)).mp l.2⟩

private lemma frame3Aux_eps_conjLQ_pow {H : Type} [Group H] {N : Subgroup H} [N.Normal]
    {L' E' : Subgroup H} {n : ℕ} {K : Type} [Field K] [Finite K]
    (F : lup8f_UFrame2 H N L' E' n K) (b : ↥E') (l : ↥L') (k : ℕ) :
    (F.eps (lup8f_conjLQ N L' E' F.E'_le_norm (b ^ k) l) : GL (Fin n) K) =
      MulAut.conj ((F.mat b) ^ k)
        (F.eps ⟨QuotientGroup.mk' N (l : H),
          Subgroup.mem_map_of_mem _ l.2⟩ : GL (Fin n) K) := by
  induction k with
  | zero => simp [lup8f_conjLQ]
  | succ k ih =>
      rw [pow_succ']
      have h1 : lup8f_conjLQ N L' E' F.E'_le_norm (b * b ^ k) l =
          lup8f_conjLQ N L' E' F.E'_le_norm b (frame3Aux_conjL F.E'_le_norm (b ^ k) l) := by
        apply Subtype.ext
        simp [lup8f_conjLQ, frame3Aux_conjL, mul_assoc]
      rw [h1, F.mat_ind b (frame3Aux_conjL F.E'_le_norm (b ^ k) l)]
      have h2 : (⟨QuotientGroup.mk' N (frame3Aux_conjL F.E'_le_norm (b ^ k) l : H),
          Subgroup.mem_map_of_mem _ (frame3Aux_conjL F.E'_le_norm (b ^ k) l).2⟩ :
            ↥(L'.map (QuotientGroup.mk' N))) =
          lup8f_conjLQ N L' E' F.E'_le_norm (b ^ k) l := by
        apply Subtype.ext
        rfl
      rw [h2, ih, pow_succ']
      simp [map_mul]

private lemma frame3Aux_mat_cube_mem_scalars
    (hS : GGQTwoSetting p B Bs x L D J)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hp : p = 3) (hn : 6 ≤ n) (b : ↥(lup8f_E' L Bs)) :
    (F.mat b) ^ 3 ∈ LargeEvenScalars (Fin n) K := by
  classical
  let H := lup8f_HT L Bs
  let L' : Subgroup H := lup8f_L' L Bs
  let E' : Subgroup H := lup8f_E' L Bs
  let N : Subgroup H := C.N
  have hpowBs : ∀ y ∈ Bs, y ^ p = 1 := hS.1.1.2.1.2.1.2
  have hb3 : (b : H) ^ 3 = 1 := by
    apply Subtype.ext
    have hbG : ((b : H) : G) ∈ Bs := Subgroup.mem_subgroupOf.mp b.2
    have hb := hpowBs ((b : H) : G) hbG
    rwa [hp] at hb
  have hb3' : b ^ 3 = 1 := Subtype.ext hb3
  have hcomm : ∀ g : ↥(LargeEvenSUGroup (Fin n) K 2),
      Commute ((F.mat b) ^ 3) (g : GL (Fin n) K) := by
    intro g
    obtain ⟨u, hu_eps⟩ := F.eps.surjective g
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp u.2
    let l : ↥L' := ⟨y, hy⟩
    have hu : u = ⟨QuotientGroup.mk' N (l : H), Subgroup.mem_map_of_mem _ l.2⟩ :=
      Subtype.ext (by simpa [l] using hyu.symm)
    have h1 : lup8f_conjLQ N L' E' C.E'_le_norm (b ^ 3) l =
        ⟨QuotientGroup.mk' N (l : H), Subgroup.mem_map_of_mem _ l.2⟩ := by
      rw [hb3']
      apply Subtype.ext
      simp [lup8f_conjLQ]
    have hiter := frame3Aux_eps_conjLQ_pow F b l 3
    rw [h1] at hiter
    rw [← hu] at hiter
    have hconj : (F.eps u : GL (Fin n) K) =
        ((F.mat b) ^ 3) * (F.eps u : GL (Fin n) K) * ((F.mat b) ^ 3)⁻¹ := by
      simpa [MulAut.conj_apply, ← map_pow] using hiter
    rw [hu_eps] at hconj
    exact (by
      calc ((F.mat b) ^ 3) * (g : GL (Fin n) K)
          = (((F.mat b) ^ 3) * (g : GL (Fin n) K) * ((F.mat b) ^ 3)⁻¹) *
              ((F.mat b) ^ 3) := by group
        _ = (g : GL (Fin n) K) * ((F.mat b) ^ 3) := by rw [← hconj])
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by rw [M.card_K]; norm_num⟩
  have hd : 3 ≤ n := by omega
  exact GGL45TG.SU.mem_scalars_of_commute_su (n := 1) (d := n) h hd ((F.mat b) ^ 3)
    (fun g hg => hcomm ⟨g, hg⟩)

private def frame3Aux_fieldData (M : lup8f_UnitaryMarking Bs L n K) :
    UnitaryFieldData 2 1 K :=
  ⟨Nat.prime_two, le_rfl, by rw [M.card_K]; norm_num⟩

private lemma frame3Aux_mat_mem_unitary (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (b : ↥(lup8f_E' L Bs)) :
    F.mat b ∈ primeFormUnitary (frame3Aux_fieldData M) (idGram K n) := by
  obtain ⟨μ, hμ0, hμq, hμ⟩ := F.mat_mem b
  have hμ1 : μ = 1 := by
    have h : μ * (μ - 1) = 0 := by
      calc μ * (μ - 1) = μ ^ 2 - μ := by ring
        _ = 0 := by rw [hμq, sub_self]
    rcases mul_eq_zero.mp h with h0 | h1
    · exact absurd h0 hμ0
    · exact sub_eq_zero.mp h1
  have hbar : (frame3Aux_fieldData M).bar = fun x : K => x ^ 2 := by
    funext x
    rw [UnitaryFieldData.bar_apply]
    norm_num
  rw [mem_primeFormUnitary, hbar]
  simpa [idGram, hμ1] using hμ

private lemma frame3Aux_mem_GUSet_of_mem_unitary (M : lup8f_UnitaryMarking Bs L n K)
    {P : GL (Fin n) K} (hP : P ∈ primeFormUnitary (frame3Aux_fieldData M) (idGram K n)) :
    P ∈ LargeEvenGUSet (Fin n) K 2 := by
  have hbar : (frame3Aux_fieldData M).bar = fun x : K => x ^ 2 := by
    funext x
    rw [UnitaryFieldData.bar_apply]
    norm_num
  rw [mem_primeFormUnitary, hbar] at hP
  refine ⟨1, one_ne_zero, by norm_num, ?_⟩
  simpa [LargeEvenGUSet, idGram, one_smul] using hP

private lemma frame3Aux_diag_of_isDiag (g : GL (Fin n) K)
    (hM : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag) :
    ∃ σ : Fin n → Kˣ,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal (fun i => (σ i : K)) := by
  have hd : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun i => (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i) :=
    hM.diagonal_diag.symm
  have hne : ∀ i, (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i ≠ 0 := by
    intro i
    exact CFSG.StandardType.TypeA.PGLTor.diag_ne_zero_of_eq_diagonal (D := g) hd i
  exact ⟨fun i => Units.mk0 _ (hne i), hd⟩

private lemma frame3Aux_caseB (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hB : ∀ b : ↥(lup8f_E' L Bs), (F.mat b) ^ 3 = 1) :
    ∃ (P : GL (Fin n) K), P ∈ LargeEvenGUSet (Fin n) K 2 ∧
      ∀ b : ↥(lup8f_E' L Bs), ∃ σ : Fin n → Kˣ,
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (F.mat b : Matrix (Fin n) (Fin n) K) *
          (P : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun i => (σ i : K)) := by
  classical
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  obtain ⟨P, hP, hPd⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_unitary_isDiag_conj
      (frame3Aux_fieldData M) h3 (Set.range F.mat)
      (fun x hx => by obtain ⟨b, rfl⟩ := hx; exact frame3Aux_mat_mem_unitary M C F b)
      (fun x hx y hy => by
        obtain ⟨b, rfl⟩ := hx
        obtain ⟨b', rfl⟩ := hy
        exact F.commute b b')
      (fun x hx => by obtain ⟨b, rfl⟩ := hx; exact hB b)
  refine ⟨P, frame3Aux_mem_GUSet_of_mem_unitary M hP, ?_⟩
  intro b
  obtain ⟨σ, hσ⟩ := frame3Aux_diag_of_isDiag (P⁻¹ * F.mat b * P) (hPd (F.mat b) ⟨b, rfl⟩)
  exact ⟨σ, by simpa only [Units.val_mul] using hσ⟩

private lemma frame3Aux_card_units (M : lup8f_UnitaryMarking Bs L n K) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, M.card_K]

private lemma frame3Aux_no_cube_root (M : lup8f_UnitaryMarking Bs L n K) {u : Kˣ} (hu1 : u ≠ 1) :
    ∀ μ : K, μ ^ 3 ≠ (u : K) := by
  intro μ hμ
  have hcard : Nat.card Kˣ = 3 := frame3Aux_card_units M
  by_cases hμ0 : μ = 0
  · rw [hμ0] at hμ
    simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hμ
    exact (Units.ne_zero u) hμ.symm
  · let μu : Kˣ := Units.mk0 μ hμ0
    have h3 : μ ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Kˣ) (x := μu)
      rw [hcard] at h
      simpa [μu] using congrArg Units.val h
    apply hu1
    apply Units.ext
    rw [Units.val_one, ← hμ]
    exact h3

private abbrev frame3Aux_Gp : Subgroup (GL (Fin n) K) :=
  Subgroup.closure (LargeEvenGUSet (Fin n) K 2)

private def frame3Aux_gen
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K) :
    ↥(lup8f_E' L Bs) → ↥(frame3Aux_Gp (n := n) (K := K)) :=
  fun b => ⟨F.mat b, by
    simp only [frame3Aux_Gp]
    exact Subgroup.subset_closure (F.mat_mem b)⟩

private def frame3Aux_Hp
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K) :
    Subgroup ↥(frame3Aux_Gp (n := n) (K := K)) :=
  Subgroup.closure (Set.range (frame3Aux_gen C F))

private lemma frame3Aux_Hp_comm
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K) :
    ∀ x ∈ frame3Aux_Hp C F, ∀ y ∈ frame3Aux_Hp C F, x * y = y * x := by
  simp only [frame3Aux_Hp]
  apply CFSG.GroupTheory.TwoWeights.closure_comm
  intro x hx y hy
  obtain ⟨b, rfl⟩ := hx
  obtain ⟨b', rfl⟩ := hy
  apply Subtype.ext
  exact F.commute b b'

private lemma frame3Aux_Hp_cube
    (hS : GGQTwoSetting p B Bs x L D J)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hp : p = 3) (hn : 6 ≤ n) :
    ∀ x ∈ frame3Aux_Hp C F, ∃ w : Kˣ,
      (((x : ↥(frame3Aux_Gp (n := n) (K := K))) : GL (Fin n) K)) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin n) w := by
  classical
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have h := frame3Aux_mat_cube_mem_scalars hS M C F hp hn b
      rw [CFSG.Assembly.largeEvenScalars_def, MonoidHom.mem_range] at h
      obtain ⟨w, hw⟩ := h
      exact ⟨w, by simpa [frame3Aux_gen] using hw.symm⟩
  | one => exact ⟨1, by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨wx, hwx⟩ := ihx
      obtain ⟨wy, hwy⟩ := ihy
      have hcomm : Commute ((x : ↥(frame3Aux_Gp (n := n) (K := K))) : GL (Fin n) K)
          ((y : ↥(frame3Aux_Gp (n := n) (K := K))) : GL (Fin n) K) :=
        congrArg (fun z : ↥(frame3Aux_Gp (n := n) (K := K)) => (z : GL (Fin n) K))
          (frame3Aux_Hp_comm C F x hx y hy)
      refine ⟨wx * wy, ?_⟩
      change (((x : ↥(frame3Aux_Gp (n := n) (K := K))) : GL (Fin n) K) *
          ((y : ↥(frame3Aux_Gp (n := n) (K := K))) : GL (Fin n) K)) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin n) (wx * wy)
      rw [Commute.mul_pow hcomm 3, hwx, hwy, ← map_mul]
  | inv x hx ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨w⁻¹, ?_⟩
      change ((((x : ↥(frame3Aux_Gp (n := n) (K := K))) : GL (Fin n) K))⁻¹) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin n) w⁻¹
      rw [inv_pow, hw, ← map_inv]

private lemma frame3Aux_caseC_lift
    (hS : GGQTwoSetting p B Bs x L D J)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hp : p = 3) (hn : 6 ≤ n) (b0 : ↥(lup8f_E' L Bs)) :
    ∃ gl : ↥F.A → GL (Fin n) K,
      (∀ a b, gl a * gl b = gl b * gl a) ∧
      (∀ a, gl a * F.mat b0 = F.mat b0 * gl a) ∧
      (∀ a, gl a ∈ frame3Aux_Gp) ∧
      (∀ a, ∃ w : Kˣ, (gl a) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) w) ∧
      (∀ a (h : gl a ∈ frame3Aux_Gp),
        LargeEvenProjMk (frame3Aux_Gp) ⟨gl a, h⟩ = (a : LargeEvenProj (frame3Aux_Gp))) := by
  classical
  have hA : F.A = (frame3Aux_Hp C F).map (LargeEvenProjMk (frame3Aux_Gp)) := by
    rw [F.A_def]; simp only [frame3Aux_Hp]
    rw [MonoidHom.map_closure]; congr 1
    ext z
    constructor
    · intro h
      obtain ⟨b, hz⟩ := h
      exact ⟨frame3Aux_gen C F b, ⟨b, rfl⟩, hz⟩
    · intro h
      obtain ⟨y, hy, hz⟩ := h
      obtain ⟨b, rfl⟩ := hy
      exact ⟨b, hz⟩
  have hsurj : ∀ a : ↥F.A, ∃ x : ↥(frame3Aux_Gp), x ∈ frame3Aux_Hp C F ∧
      LargeEvenProjMk (frame3Aux_Gp) x = (a : LargeEvenProj (frame3Aux_Gp)) := by
    intro a
    have ha : (a : LargeEvenProj (frame3Aux_Gp)) ∈
        (frame3Aux_Hp C F).map (LargeEvenProjMk (frame3Aux_Gp)) := by
      rw [← hA]
      exact a.2
    rw [Subgroup.mem_map] at ha
    obtain ⟨x, hx, hxa⟩ := ha
    exact ⟨x, hx, hxa⟩
  let g : ↥F.A → ↥(frame3Aux_Gp) := fun a => Classical.choose (hsurj a)
  have hg : ∀ a, LargeEvenProjMk (frame3Aux_Gp) (g a) =
      (a : LargeEvenProj (frame3Aux_Gp)) :=
    fun a => (Classical.choose_spec (hsurj a)).2
  have hgHp : ∀ a, g a ∈ frame3Aux_Hp C F := fun a => (Classical.choose_spec (hsurj a)).1
  have hcommHp := frame3Aux_Hp_comm C F
  let gl : ↥F.A → GL (Fin n) K := fun a => (g a : GL (Fin n) K)
  refine ⟨gl, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact congrArg (fun z : ↥(frame3Aux_Gp) => (z : GL (Fin n) K))
      (hcommHp (g a) (hgHp a) (g b) (hgHp b))
  · intro a
    have hgenb0 : frame3Aux_gen C F b0 ∈ frame3Aux_Hp C F :=
      Subgroup.subset_closure ⟨b0, rfl⟩
    exact congrArg (fun z : ↥(frame3Aux_Gp) => (z : GL (Fin n) K))
      (hcommHp (g a) (hgHp a) (frame3Aux_gen C F b0) hgenb0)
  · intro a
    exact (g a).2
  · intro a
    exact frame3Aux_Hp_cube hS M C F hp hn (g a) (hgHp a)
  · intro a h
    simpa [gl] using hg a

private lemma frame3Aux_caseC_count
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    [CharP K 2]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (b0 : ↥(lup8f_E' L Bs)) (u : Kˣ)
    (hu_eq : (F.mat b0) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) u)
    (hu : ∀ μ : K, μ ^ 3 ≠ (u : K)) (gl : ↥F.A → GL (Fin n) K)
    (hcomm : ∀ a b, gl a * gl b = gl b * gl a)
    (hga : ∀ a, gl a * F.mat b0 = F.mat b0 * gl a)
    (hmem : ∀ a, gl a ∈ frame3Aux_Gp)
    (hpow : ∀ a, ∃ w : Kˣ, (gl a) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) w)
    (hquot : ∀ a (h : gl a ∈ frame3Aux_Gp),
      LargeEvenProjMk (frame3Aux_Gp) ⟨gl a, h⟩ = (a : LargeEvenProj (frame3Aux_Gp))) :
    ∃ m, n = 3 * m ∧ Nat.card F.A ≤ 3 ^ m := by
  classical
  have hginj : ∀ a b (w : Kˣ),
      gl a = gl b * Matrix.GeneralLinearGroup.scalar (Fin n) w → a = b := by
    intro a b w h
    have hsG : Matrix.GeneralLinearGroup.scalar (Fin n) w ∈ frame3Aux_Gp := by
      have h1 : (gl b)⁻¹ * gl a = Matrix.GeneralLinearGroup.scalar (Fin n) w := by
        rw [h]
        group
      rw [← h1]
      exact (frame3Aux_Gp).mul_mem ((frame3Aux_Gp).inv_mem (hmem b)) (hmem a)
    have h1 : LargeEvenProjMk (frame3Aux_Gp) ⟨gl a, hmem a⟩ =
        LargeEvenProjMk (frame3Aux_Gp) ⟨gl b, hmem b⟩ := by
      have heq : (⟨gl a, hmem a⟩ : ↥(frame3Aux_Gp)) =
          ⟨gl b, hmem b⟩ * ⟨Matrix.GeneralLinearGroup.scalar (Fin n) w, hsG⟩ := by
        apply Subtype.ext
        exact h
      rw [heq, map_mul]
      have hsw : LargeEvenProjMk (frame3Aux_Gp)
          ⟨Matrix.GeneralLinearGroup.scalar (Fin n) w, hsG⟩ = 1 := by
        apply (QuotientGroup.eq_one_iff _).mpr
        exact Subgroup.mem_subgroupOf.mpr ⟨w, rfl⟩
      rw [hsw, mul_one]
    apply Subtype.ext
    rw [← hquot a (hmem a), ← hquot b (hmem b), h1]
  exact CFSG.StandardType.TableCRes.card_le_of_nonpow_matrix
    (F := K) (N := n) (p := 3) Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2)
    (F.mat b0) u hu_eq hu gl hcomm hga hpow hginj

private lemma frame3Aux_caseC_contra
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hn : 6 ≤ n) {m : ℕ} (hn3 : n = 3 * m)
    (hcardA : Nat.card F.A ≤ 3 ^ m) : False := by
  have hmax : max (n - 3) 3 = n - 3 := by omega
  have hrank := F.rank_ge
  rw [hmax] at hrank
  have hm_lt : m < n - 3 := by omega
  have hpowlt : 3 ^ m < 3 ^ (n - 3) :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mpr hm_lt
  exact (not_le.mpr hpowlt) (hrank.trans hcardA)

private lemma frame3Aux_caseC
    (hS : GGQTwoSetting p B Bs x L D J)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hp : p = 3) (hn : 6 ≤ n)
    (b0 : ↥(lup8f_E' L Bs)) (hb0 : (F.mat b0) ^ 3 ≠ 1) : False := by
  classical
  haveI : CharP K 2 := (frame3Aux_fieldData M).charP
  have hmem := frame3Aux_mat_cube_mem_scalars hS M C F hp hn b0
  rw [CFSG.Assembly.largeEvenScalars_def, MonoidHom.mem_range] at hmem
  obtain ⟨u, hu_eq⟩ := hmem
  have hu_eq' : (F.mat b0) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) u := hu_eq.symm
  have hu1 : u ≠ 1 := by
    intro hu1
    apply hb0
    rw [hu_eq', hu1, map_one]
  have hu : ∀ μ : K, μ ^ 3 ≠ (u : K) := frame3Aux_no_cube_root M hu1
  obtain ⟨gl, hcomm, hga, hmemGp, hpow, hquot⟩ :=
    frame3Aux_caseC_lift hS M C F hp hn b0
  obtain ⟨m, hn3, hcardA⟩ :=
    frame3Aux_caseC_count C F b0 u hu_eq' hu gl hcomm hga hmemGp hpow hquot
  exact frame3Aux_caseC_contra C F hn hn3 hcardA

end Frame3Aux

noncomputable def lup8f_frame3 (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame2 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hp : p = 3) (hdvd : 3 ∣ n) (hn : 6 ≤ n) :
    lup8f_UFrame3 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K := by
  classical
  by_cases hB : ∀ b : ↥(lup8f_E' L Bs), (F.mat b) ^ 3 = 1
  · let P : GL (Fin n) K := Classical.choose (frame3Aux_caseB M C F hB)
    have hP := Classical.choose_spec (frame3Aux_caseB M C F hB)
    exact { F with P := P, P_mem := hP.1, diag := hP.2 }
  · rw [not_forall] at hB
    let b0 : ↥(lup8f_E' L Bs) := Classical.choose hB
    have hb0 : (F.mat b0) ^ 3 ≠ 1 := Classical.choose_spec hB
    exact (frame3Aux_caseC hS M C F hp hn b0 hb0).elim

end CFSG.StandardType.GGXInL

end
