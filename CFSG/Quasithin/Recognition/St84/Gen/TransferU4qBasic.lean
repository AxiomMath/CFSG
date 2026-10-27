module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalDefs
public import CFSG.Quasithin.Recognition.St84.TransferInner

import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointTorusAct
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalTorus
import CFSG.Quasithin.Recognition.St84.Gen.TransferEdgeHyp
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

abbrev U4qEdgeData (L1 L2 S : Subgroup H) (f : ℕ) : Prop :=
  U4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
    (S ⊓ f112saK L1 L2 S) f

variable {L1 L2 S : Subgroup H} {m n f : ℕ}

theorem f112ll_u4q_eq_of_localData (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    f = m ∧ n = 2 * f := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hcardα : Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ (5 * f + m) := by
    rw [(f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR).card_eq,
      twoPart_of_isL2Quot (a := 5 * f) (by omega)
        (f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2) hd.card_left]
  have hcardβ : Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ (4 * f + n) := by
    rw [(f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF hR).card_eq,
      twoPart_of_isL2Quot (a := 4 * f) (by omega)
        (f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2) hd.card_right]
  have hcardS : Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ (6 * f) := by
    rw [(f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR).card_eq, hd.twoPart_left]
  have hfm : f = m := by
    have h : 6 * f = 5 * f + m :=
      Nat.pow_right_injective (a := 2) (by norm_num) (hcardS.symm.trans hcardα)
    omega
  have hnf : n = 2 * f := by
    have h : 6 * f = 4 * f + n :=
      Nat.pow_right_injective (a := 2) (by norm_num) (hcardS.symm.trans hcardβ)
    omega
  exact ⟨hfm, hnf⟩

theorem f112ll_u4q_card_T (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ (6 * f) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  rw [(f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR).card_eq, hd.twoPart_left]

theorem f112ll_u4q_commutator_le_center_left (hd : U4qEdgeData L1 L2 S f) :
    ⁅pCoreOf 2 (f112saP1' L1 L2 S), pCoreOf 2 (f112saP1' L1 L2 S)⁆ ≤
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  have hspec : IsSpecialPGroup 2 ↥(pCoreOf 2 (f112saP1' L1 L2 S)) := by
    have h := hd.special_left.1
    rwa [pCoreOf_oTwoPrime] at h
  rcases hspec.2 with ⟨hab, -⟩ | ⟨hcomm, -, -⟩
  · rw [Subgroup.commutator_self_eq_bot_iff.mpr hab]
    exact bot_le
  · rw [← Subgroup.map_subtype_commutator (pCoreOf 2 (f112saP1' L1 L2 S)), hcomm]
    rintro x ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz (⟨y, hy⟩ : ↥(pCoreOf 2 (f112saP1' L1 L2 S))))

theorem f112ll_u4q_center_le_centralizer_left (hd : U4qEdgeData L1 L2 S f) :
    centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) ≤
      Subgroup.centralizer (oTwoPrime (f112saP1' L1 L2 S) : Set H) := by
  have h := Subgroup.le_centralizer_iff.mp hd.center_left
  rwa [pCoreOf_oTwoPrime] at h

theorem f112ll_u4q_exists_torus_left (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    ∃ J : Subgroup H, J ≤ bigB (oTwoPrime (f112saP1' L1 L2 S))
        (oTwoPrime (f112saP2' L1 L2 S)) (S ⊓ f112saK L1 L2 S) ∧ Odd (Nat.card J) ∧
      (∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
        ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) ∧
      pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer (J : Set H) = ⊥ := by
  have hH : Hyp111 (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) := f112ll_hyp111_edge hF hm hn h1 h2
  have hcardT := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hf : 2 ≤ f := by
    have := (f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd).1
    omega
  obtain ⟨J, hJB, hJcomm, hJcard, hJconj, -, -⟩ :=
    U4qLocalData.exists_torus (f := f) hf hH hd hcardT
  have hodd : Odd (Nat.card J) := by
    rw [hJcard, show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact odd_two_pow_sub_one (by omega)
  refine ⟨J, hJB, hodd, ?_, ?_⟩
  · intro j hj l hl
    have h := hJconj j hj l hl
    rw [pCoreOf_oTwoPrime] at h
    exact h
  · have h := U4qLocalData.pCoreOf_inf_centralizer_torus (L1 := oTwoPrime (f112saP1' L1 L2 S))
      (L2 := oTwoPrime (f112saP2' L1 L2 S)) (S := S ⊓ f112saK L1 L2 S) (H₀ := J)
      hH hd hcardT ⟨hJB, hJcomm, hJcard, hJconj⟩ hf
    rwa [pCoreOf_oTwoPrime] at h

private theorem u4q_conj_mem_centerOf {Q : Subgroup H} {g z : H}
    (hg : g ∈ Subgroup.normalizer (Q : Set H)) (hz : z ∈ centerOf Q) :
    g * z * g⁻¹ ∈ centerOf Q := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1, ?_⟩
  change g * z * g⁻¹ ∈ Subgroup.centralizer (Q : Set H)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : g⁻¹ * y * g ∈ Q := by
    have h : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by rw [h]; exact hy)
  have h1 : (g⁻¹ * y * g) * z = z * (g⁻¹ * y * g) :=
    Subgroup.mem_centralizer_iff.mp hz.2 _ hy'
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = (g * z * g⁻¹) * y := by group

private theorem u4q_torus_le_normalizer {L1 L2 S D : Subgroup H} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hDsub : D ≤ f112saX2 L1 L2 S ⊓ borelOf L2 S) :
    D ≤ f112saK L1 L2 S ∧ D ≤ oTwoPrime (f112saP2' L1 L2 S) ∧
      D ≤ Subgroup.normalizer (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) : Set H) ∧
      D ≤ Subgroup.normalizer (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) : Set H) := by
  have hDX2 : D ≤ f112saX2 L1 L2 S := hDsub.trans inf_le_left
  have hDB : D ≤ bigB L1 L2 S := hDX2.trans (f112sa_X2_le_bigB L1 L2 S)
  have hDLβ : D ≤ oTwoPrime (f112saP2' L1 L2 S) :=
    (hDX2.trans (f112sa_X2_le_oTwoRes L1 L2 S)).trans
      (f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot hn h2)
  have hDNP1' : D ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    hDB.trans ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S).trans
      (f112sa_P1_le_normalizer_P1' hF))
  have hDNLα : D ≤ Subgroup.normalizer (oTwoPrime (f112saP1' L1 L2 S) : Set H) :=
    fun d hdD => mem_normalizer_oTwoPrime (hDNP1' hdD)
  refine ⟨hDX2.trans le_sup_right, hDLβ, ?_, ?_⟩
  · intro d hdD
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hDNLα hdD)
  · intro d hdD
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hDLβ hdD)

private theorem u4q_exists_center_element {L1 L2 S : Subgroup H} {f : ℕ} {K : Type} [Field K]
    (c₂ : U4qCoordRight (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f K) :
    ∃ z0 : ↥(pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))),
      (z0 : H) ∈ centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) ∧
        (z0 : H) ≠ 1 ∧ Multiplicative.toAdd (c₂.β z0) = !![1, 0; 0, 0] := by
  have hE00 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f) =
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K).transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zero_pow (pow_ne_zero _ two_ne_zero)]
  obtain ⟨z0, hz0⟩ := (c₂.range_iff (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K)).mpr hE00
  have hz0Z : (z0 : H) ∈ centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) :=
    (c₂.mem_center_iff z0).mpr ⟨by rw [hz0]; rfl, by rw [hz0]; rfl⟩
  have hz0ne : (z0 : H) ≠ 1 := by
    intro hone
    have h1 : Multiplicative.toAdd (c₂.β z0) = 0 := by
      rw [show z0 = 1 from Subtype.ext hone, map_one, toAdd_one]
    rw [hz0] at h1
    have h10 : (1 : K) = 0 := by simpa using congrFun (congrFun h1 0) 0
    exact one_ne_zero h10
  exact ⟨z0, hz0Z, hz0ne, hz0⟩

private theorem u4q_upper_triangular {L1 L2 S D : Subgroup H} {f : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData 2 f K)
    {c₂ : U4qCoordRight (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f K}
    (hDLβ : D ≤ oTwoPrime (f112saP2' L1 L2 S))
    (hDNQα : D ≤ Subgroup.normalizer
      (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) : Set H))
    (hDNQβ : D ≤ Subgroup.normalizer
      (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) : Set H))
    {z0 : ↥(pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)))}
    (hz0Z : (z0 : H) ∈ centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))))
    (hz0 : Multiplicative.toAdd (c₂.β z0) = !![1, 0; 0, 0]) :
    ∀ d : ↥D,
      (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  intro d
  let u' : ↥(pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))) :=
    ⟨(d : H) * (z0 : H) * (d : H)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hDNQβ d.2) (z0 : H)).mp z0.2⟩
  have hu'Z : (u' : H) ∈ centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) :=
    u4q_conj_mem_centerOf (hDNQα d.2) hz0Z
  have h11 := ((c₂.mem_center_iff u').mp hu'Z).2
  have heq := c₂.equivariant ⟨(d : H), hDLβ d.2⟩ z0 u' rfl
  rw [heq, hz0] at h11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at h11
  ring_nf at h11
  rcases mul_eq_zero.mp h11 with h | h
  · exact h
  · exact (map_eq_zero hU.bar).mp h

private theorem u4q_exists_unitsHom {L1 L2 S D : Subgroup H} {f : ℕ} {K : Type} [Field K]
    {c₂ : U4qCoordRight (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f K}
    (hDLβ : D ≤ oTwoPrime (f112saP2' L1 L2 S))
    (hAf10 : ∀ d : ↥D,
      (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ∃ Φ : ↥D →* Kˣ, ∀ d : ↥D,
      (Φ d : K) = (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  let Af : ↥D → Matrix.SpecialLinearGroup (Fin 2) K :=
    fun d => c₂.α ⟨(d : H), hDLβ d.2⟩
  have hAf00ne : ∀ d : ↥D, (Af d : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro d
    have hdet : (Af d : Matrix (Fin 2) (Fin 2) K).det = 1 := (Af d).2
    rw [Matrix.det_fin_two, show (Af d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 from hAf10 d,
      mul_zero, sub_zero] at hdet
    have h : (Af d : Matrix (Fin 2) (Fin 2) K) 0 0 *
        (Af d : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
      rw [hdet]
      exact one_ne_zero
    exact left_ne_zero_of_mul h
  have hAfmul : ∀ a b : ↥D, Af (a * b) = Af a * Af b := by
    intro a b
    change c₂.α ⟨((a : H) * (b : H)), hDLβ (a * b).2⟩ =
      c₂.α ⟨(a : H), hDLβ a.2⟩ * c₂.α ⟨(b : H), hDLβ b.2⟩
    rw [← map_mul]
    rfl
  have hAfone : Af 1 = 1 := by
    change c₂.α ⟨(1 : H), hDLβ (1 : ↥D).2⟩ = 1
    rw [show (⟨(1 : H), hDLβ (1 : ↥D).2⟩ : ↥(oTwoPrime (f112saP2' L1 L2 S))) = 1
      from Subtype.ext rfl, map_one]
  let Φ : ↥D →* Kˣ :=
    { toFun := fun d => Units.mk0 ((Af d : Matrix (Fin 2) (Fin 2) K) 0 0) (hAf00ne d)
      map_one' := by
        apply Units.ext
        rw [Units.val_mk0, hAfone]
        simp
      map_mul' := by
        intro a b
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul]
        rw [hAfmul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          show (Af b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 from hAf10 b, mul_zero, add_zero] }
  exact ⟨Φ, fun d => by simp [Φ, Af]⟩

private theorem u4q_unitsHom_eq_one_mem_pCoreOf {L1 L2 S D : Subgroup H} {f : ℕ}
    {K : Type} [Field K] [CharP K 2]
    {c₂ : U4qCoordRight (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f K}
    (hDLβ : D ≤ oTwoPrime (f112saP2' L1 L2 S))
    (hAf10 : ∀ d : ↥D,
      (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (hDcard : Nat.card ↥D = 2 ^ (2 * f) - 1) (hf : 1 ≤ f)
    {Φ : ↥D →* Kˣ}
    (hΦval : ∀ d : ↥D, (Φ d : K) =
      (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0)
    {d : ↥D} (hd1 : Φ d = 1) :
    (d : H) ∈ pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) := by
  have hA00 : (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h := congrArg Units.val hd1
    rw [hΦval d] at h
    simpa using h
  have hA11 : (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have hdet : (c₂.α ⟨(d : H), hDLβ d.2⟩ :
        Matrix (Fin 2) (Fin 2) K).det = 1 := (c₂.α ⟨(d : H), hDLβ d.2⟩).2
    rw [Matrix.det_fin_two, hAf10 d, mul_zero, sub_zero, hA00, one_mul] at hdet
    exact hdet
  have hsq : c₂.α ⟨(d : H), hDLβ d.2⟩ * c₂.α ⟨(d : H), hDLβ d.2⟩ = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hA00, hA11, hAf10 d,
        CharTwo.add_self_eq_zero]
  have hsq' : c₂.α ⟨((d ^ 2 : ↥D) : H), hDLβ (d ^ 2).2⟩ = 1 := by
    have e : (⟨((d ^ 2 : ↥D) : H), hDLβ (d ^ 2).2⟩ :
          ↥(oTwoPrime (f112saP2' L1 L2 S))) =
        ⟨(d : H), hDLβ d.2⟩ * ⟨(d : H), hDLβ d.2⟩ :=
      Subtype.ext (by simp [pow_two])
    calc c₂.α ⟨((d ^ 2 : ↥D) : H), hDLβ (d ^ 2).2⟩
        = c₂.α (⟨(d : H), hDLβ d.2⟩ * ⟨(d : H), hDLβ d.2⟩) := congrArg c₂.α e
      _ = 1 := by rw [map_mul, hsq]
  have hd2Qβ : (d : H) ^ 2 ∈ pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) := by
    have hmem : ((d ^ 2 : ↥D) : H) ∈ pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) :=
      (c₂.eq_one_iff ⟨((d ^ 2 : ↥D) : H), hDLβ (d ^ 2).2⟩).mp hsq'
    have hv : (d : H) ^ 2 = ((d ^ 2 : ↥D) : H) := by
      rw [pow_two, pow_two, Subgroup.coe_mul]
    exact hv ▸ hmem
  have hoddD : Odd (2 ^ (2 * f) - 1) := odd_two_pow_sub_one (by omega)
  have hoddDcard : Odd (Nat.card ↥D) := by rwa [hDcard]
  have hodd : Odd (orderOf d) := Odd.of_dvd_nat hoddDcard (orderOf_dvd_natCard d)
  obtain ⟨k, hk⟩ := hodd
  have hpow : (d : H) = ((d : H) ^ 2) ^ (k + 1) := by
    have e : (d : H) ^ orderOf (d : ↥D) = 1 := by
      rw [← Subgroup.orderOf_coe]
      exact pow_orderOf_eq_one _
    rw [hk] at e
    calc (d : H) = (d : H) ^ (2 * k + 1) * (d : H) := by rw [e, one_mul]
      _ = ((d : H) ^ 2) ^ (k + 1) := by
        rw [← pow_mul, ← pow_succ, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
  rw [hpow]
  exact Subgroup.pow_mem _ hd2Qβ (k + 1)

private theorem u4q_unitsHom_injective {L1 L2 S D : Subgroup H} {f : ℕ} {K : Type} [Field K]
    [CharP K 2]
    {c₂ : U4qCoordRight (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f K}
    (hDLβ : D ≤ oTwoPrime (f112saP2' L1 L2 S))
    (hAf10 : ∀ d : ↥D,
      (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (hDcard : Nat.card ↥D = 2 ^ (2 * f) - 1) (hf : 1 ≤ f)
    {Φ : ↥D →* Kˣ}
    (hΦval : ∀ d : ↥D, (Φ d : K) =
      (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0) :
    Function.Injective Φ := by
  rw [injective_iff_map_eq_one]
  intro d hd1
  have hdQβ := u4q_unitsHom_eq_one_mem_pCoreOf hDLβ hAf10 hDcard hf hΦval hd1
  have hoddD : Odd (2 ^ (2 * f) - 1) := odd_two_pow_sub_one (by omega)
  have hDQβ : D ⊓ pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (oTwoPrime (f112saP2' L1 L2 S))).exists_card_eq
    rw [hDcard, hj]
    exact Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hoddD)
  have hmem : (d : H) ∈ D ⊓ pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) :=
    Subgroup.mem_inf.mpr ⟨d.2, hdQβ⟩
  rw [hDQβ] at hmem
  simpa using hmem

private theorem u4q_exists_norm_ne_one {f : ℕ} {K : Type} [Field K] [Fintype K]
    (hU : UnitaryFieldData 2 f K) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ (2 * f)) :
    ∃ y : Kˣ, (y : K) * hU.bar (y : K) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hpow : ∀ y : Kˣ, y ^ (2 ^ f + 1) = 1 := by
    intro y
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h := hcon y
    rw [hU.bar_apply] at h
    rw [pow_add, pow_one, mul_comm]
    exact h
  have hdvd : Fintype.card K - 1 ∣ 2 ^ f + 1 :=
    (FiniteField.forall_pow_eq_one_iff K (2 ^ f + 1)).mp hpow
  rw [show Fintype.card K = 2 ^ (2 * f) by
    rw [← Nat.card_eq_fintype_card]; exact hcard] at hdvd
  have hle : 2 ^ (2 * f) - 1 ≤ 2 ^ f + 1 := Nat.le_of_dvd (by positivity) hdvd
  have hlt : 2 ^ f + 1 < 2 ^ (2 * f) - 1 := by
    have hq4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have h2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by
      rw [← pow_mul]
      congr 1
      ring
    rw [Nat.lt_sub_iff_add_lt, h2]
    nlinarith
  omega

private theorem u4q_center_element_norm {L1 L2 S D : Subgroup H} {f : ℕ} {K : Type}
    [Field K]
    {c₂ : U4qCoordRight (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f K}
    (hU : UnitaryFieldData 2 f K)
    (hDLβ : D ≤ oTwoPrime (f112saP2' L1 L2 S)) {d : ↥D} {z : H}
    (hzZ : z ∈ centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))))
    (hzQβ : z ∈ pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))) (hz1 : z ≠ 1)
    (hdz : d * z * d⁻¹ = z) :
    (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 *
      hU.bar ((c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0) = 1 := by
  have hX01 : Multiplicative.toAdd (c₂.β ⟨z, hzQβ⟩) 0 1 = 0 :=
    ((c₂.mem_center_iff ⟨z, hzQβ⟩).mp hzZ).1
  have hX11 : Multiplicative.toAdd (c₂.β ⟨z, hzQβ⟩) 1 1 = 0 :=
    ((c₂.mem_center_iff ⟨z, hzQβ⟩).mp hzZ).2
  have hX10 : Multiplicative.toAdd (c₂.β ⟨z, hzQβ⟩) 1 0 = 0 := by
    have h := congrFun (congrFun ((c₂.range_iff _).mp ⟨⟨z, hzQβ⟩, rfl⟩) 0) 1
    simp only [Matrix.map_apply, Matrix.transpose_apply, hX01] at h
    rw [← h]
    exact zero_pow (pow_ne_zero _ two_ne_zero)
  set a : K := Multiplicative.toAdd (c₂.β ⟨z, hzQβ⟩) 0 0 with ha
  have hX : Multiplicative.toAdd (c₂.β ⟨z, hzQβ⟩) = !![a, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hX01, hX10, hX11, ha]
  have ha0 : a ≠ 0 := by
    intro ha0
    have hβ : c₂.β ⟨z, hzQβ⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_one, hX, ha0]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hβ' : c₂.β ⟨z, hzQβ⟩ =
        c₂.β (1 : ↥(pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)))) := by rw [hβ, map_one]
    have hz_eq : z = 1 := by simpa using congrArg Subtype.val (c₂.injective_β hβ')
    exact hz1 hz_eq
  have heq := c₂.equivariant ⟨(d : H), hDLβ d.2⟩ ⟨z, hzQβ⟩ ⟨z, hzQβ⟩ hdz.symm
  rw [hX] at heq
  have h00 := congrFun (congrFun heq 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at h00
  have h00' : a = a * ((c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 *
      hU.bar ((c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0)) := by
    rw [hU.bar_apply]
    linear_combination h00
  have h' : a * 1 = a * ((c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 *
      hU.bar ((c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0)) := by
    rw [mul_one]
    exact h00'
  exact (mul_left_cancel₀ ha0 h').symm

private theorem u4q_centerOf_inf_centralizer_eq_bot {L1 L2 S D : Subgroup H} {f : ℕ}
    {K : Type} [Field K]
    {c₂ : U4qCoordRight (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f K}
    (hU : UnitaryFieldData 2 f K)
    (hH : Hyp111 (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (hd : U4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f)
    (hcardT : Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ (6 * f))
    (hDLβ : D ≤ oTwoPrime (f112saP2' L1 L2 S)) {d : ↥D}
    (hAfnorm : (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 *
      hU.bar ((c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0) ≠ 1) :
    centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) ⊓
      Subgroup.centralizer ({(d : H)} : Set H) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzZ, hzC⟩
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hzQβ : z ∈ pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) :=
    hd.center_le_right hH hcardT hzZ
  have hdz : d * z * d⁻¹ = z := by
    have hc := Subgroup.mem_centralizer_iff.mp hzC (d : H) (Set.mem_singleton (d : H))
    rw [hc, Subgroup.coe_inv, mul_assoc, mul_inv_cancel, mul_one]
  exact hAfnorm (u4q_center_element_norm hU hDLβ hzZ hzQβ hz1 hdz)

private theorem u4q_centerOf_T_inf_centralizer_eq_bot {L1 L2 S D : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) {d : ↥D}
    (hZbot : centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) ⊓
      Subgroup.centralizer ({(d : H)} : Set H) = ⊥) :
    centerOf (S ⊓ f112saK L1 L2 S) ⊓
      Subgroup.centralizer ({(d : H)} : Set H) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzT, hzC⟩
  have hzZ : z ∈ centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) := by
    rw [pCoreOf_oTwoPrime]
    exact f112sa_centerOf_T_le_P1'_of_hyp111R hF hR hzT
  have hmem : z ∈ centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) ⊓
      Subgroup.centralizer ({(d : H)} : Set H) := ⟨hzZ, hzC⟩
  rw [hZbot] at hmem
  exact hmem

theorem f112ll_u4q_W_eq_bot (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    f112saW L1 L2 S = ⊥ := by
  classical
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨hf_eq, hn_eq⟩ := f112ll_u4q_eq_of_localData hF hm hn h1 h2 hd
  have hf : 2 ≤ f := by omega
  let P1 := f112saP1' L1 L2 S
  let Lα := oTwoPrime P1
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  have hcardT : Nat.card ↥T = 2 ^ (6 * f) := f112ll_u4q_card_T hF hm hn h1 h2 hd
  have hH : Hyp111 Lα Lβ T := f112ll_hyp111_edge hF hm hn h1 h2
  obtain ⟨D, hDsub, hDcard⟩ := f112_exists_torus_X2 hF (by omega) h2
  have hDcard' : Nat.card ↥D = 2 ^ (2 * f) - 1 := by rw [hDcard, hn_eq]
  obtain ⟨K, hKfield, hKfin, ⟨c₂⟩⟩ := U4qLocalData.exists_coordRight hH hd hcardT
  letI := hKfield
  letI := hKfin
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, c₂.card⟩
  haveI : CharP K 2 := hU.charP
  obtain ⟨hDK, hDLβ, hDNQα, hDNQβ⟩ := u4q_torus_le_normalizer hF hn h2 hDsub
  obtain ⟨z0, hz0Z, -, hz0⟩ := u4q_exists_center_element c₂
  have hAf10 : ∀ d : ↥D,
      (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    u4q_upper_triangular hU hDLβ hDNQα hDNQβ hz0Z hz0
  obtain ⟨Φ, hΦval⟩ := u4q_exists_unitsHom hDLβ hAf10
  have hΦinj : Function.Injective Φ :=
    u4q_unitsHom_injective hDLβ hAf10 hDcard' (by omega) hΦval
  have hcardΦ : Nat.card Kˣ ≤ Nat.card ↥D := by
    rw [Nat.card_units, c₂.card, hDcard']
  have hΦsurj : Function.Surjective Φ := (hΦinj.bijective_of_nat_card_le hcardΦ).2
  obtain ⟨y, hy1⟩ := u4q_exists_norm_ne_one hU hf c₂.card
  obtain ⟨d, hdΦ⟩ := hΦsurj y
  have hAfnorm : (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 *
      hU.bar ((c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0) ≠ 1 := by
    have hval : (c₂.α ⟨(d : H), hDLβ d.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 = (y : K) := by
      have h := congrArg Units.val hdΦ
      rw [hΦval d] at h
      simpa using h
    rw [hval]
    exact hy1
  have hZbot := u4q_centerOf_inf_centralizer_eq_bot hU hH hd hcardT hDLβ hAfnorm
  have hZT := u4q_centerOf_T_inf_centralizer_eq_bot hF hR hZbot
  exact f112saW_eq_bot_of_centerOf_inf_centralizer_le_of_hyp111R hF hR
    (k1 := (d : H)) (k2 := (d : H)) (hDK d.2) (hDK d.2)
    (by rw [hZT]; exact bot_le) (by rw [hZT]; exact bot_le)
end CFSG.Quasithin.F112R.St84

end
