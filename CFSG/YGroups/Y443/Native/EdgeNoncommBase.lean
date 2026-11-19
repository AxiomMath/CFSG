
module

public import CFSG.YGroups.Y443.Native.HomBase
public import CFSG.YGroups.Y443.CentralProjection
public import CFSG.YGroups.Y443.Native.EdgeNoncommInputs
public import CFSG.Monster.AxisCount.DenseNative
public import CFSG.YGroups.Defs
public import CFSG.YGroups.Exact.Y322Inputs
public import CFSG.YGroups.Y322CentralInputs
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.YGroups.Y443.Native.OrderRelInputs
public import CFSG.YGroups.Y443.Native.PairRelAInputs
public import CFSG.YGroups.Y443.Native.PairRelBInputs
public import CFSG.YGroups.Y443.Native.PairRelCInputs
public import CFSG.YGroups.Y443.Native.PairRelDInputs
public import CFSG.YGroups.Y443.Native.Words
public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.Griess.ThreeVectorSeparation
public import CFSG.Monster.Griess.Invariance.Diagonal
public import CFSG.Monster.Griess.Invariance.Octad.Basic
public import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public meta import CFSG.YGroups.Y443.Native.Words
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import CFSG.YGroups.Y443.Native.CandidateData
public import CFSG.YGroups.Y443.Native.OrderRelBase
public import CFSG.YGroups.Y443.Native.PairRelABase
public import CFSG.YGroups.Y443.Native.PairRelBBase
public import CFSG.YGroups.Y443.Native.PairRelCBase
public import CFSG.YGroups.Y443.Native.PairRelDBase
public import CFSG.YGroups.Y443.Native.SpiderRelBase
public import CFSG.YGroups.Y443.Perfect

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native CFSG.Open

namespace EdgeNoncomm

theorem pairsWord_cons (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    pairsWord (p :: ps) = pairsWord ps ++ pw p := by
  rw [pairsWord, pairsWord, List.map_cons, List.reverse_cons, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

noncomputable def axS : MonsterY443Gen → MonsterY443Derived
  | none => 1
  | some g => axElt g

noncomputable def agS : MonsterY443Gen → Gmat
  | none => 1
  | some g => gGen g

theorem coe_axS (s : MonsterY443Gen) :
    ((axS s : MonsterY443Derived) : MonsterY443) =
      PresentedGroup.of none * PresentedGroup.of s := by
  cases s with
  | none => exact (gen_mul_self none).symm
  | some g => rfl

theorem y443T_mul_eq
    (s r : MonsterY443Gen) : y443T s * y443T r = (axS s)⁻¹ * axS r := by
  apply Subtype.ext
  rw [y443T_mul_coe, Subgroup.coe_mul, Subgroup.coe_inv, coe_axS, coe_axS, e443_phi_pair]

theorem wIdx_add_one : ∀ g : E443Gen, wIdx g + 1 = y443LetterOfGen (some g) := by decide

theorem coe_agS_L (s : MonsterY443Gen) :
    ((agS s : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin (gL (y443LetterOfGen s)) := by
  cases s with
  | none => rfl
  | some g =>
    rw [← wIdx_add_one g]
    exact coe_gGen g

noncomputable def agC (c : ℕ) : Gmat := agS (y443GenOfLetter c)

theorem coe_agC_L {c : ℕ} (hc : c < 12) :
    ((agC c : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin (gL c) := by
  rw [agC, coe_agS_L, y443LetterOfGen_genOfLetter c hc]

noncomputable def pairsProd (ps : List (ℕ × ℕ)) : Gmat :=
  (ps.map fun p => (agC p.1)⁻¹ * agC p.2).prod

theorem nP_lt : ∀ p ∈ nP, p.1 < 12 ∧ p.2 < 12 := by decide

theorem y443C_eq :
    y443C = (y443Tl 0 * y443Tl 1 * y443Tl 2 * y443Tl 3 * y443Tl 5 * y443Tl 6 *
    y443Tl 9) ^ 9 := by
  rw [← y443Pi_F0, y443F0]
  simp only [map_pow, map_mul, y443Pi_gen]

theorem y443X_eq : y443X = y443Tl 4 := by
  have h := y443GenOfLetter_letterOfGen y443E1
  rw [y443LetterOfGen_E1] at h
  rw [y443X, y443Tl, h]

theorem y443C_mul_X :
    y443C * y443X = (nP.map fun p => y443Tl p.1 * y443Tl p.2).prod := by
  have hQ : y443Tl 0 * y443Tl 1 * y443Tl 2 * y443Tl 3 * y443Tl 5 * y443Tl 6 * y443Tl 9 *
      (y443Tl 0 * y443Tl 1 * y443Tl 2 * y443Tl 3 * y443Tl 5 * y443Tl 6 * y443Tl 9) =
      (qP.map fun p => y443Tl p.1 * y443Tl p.2).prod := by
    simp only [qP, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hR : y443Tl 0 * y443Tl 1 * y443Tl 2 * y443Tl 3 * y443Tl 5 * y443Tl 6 * y443Tl 9 *
      y443Tl 4 = (rP.map fun p => y443Tl p.1 * y443Tl p.2).prod := by
    simp only [rP, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [y443C_eq, y443X_eq]
  set x₀ := y443Tl 0 * y443Tl 1 * y443Tl 2 * y443Tl 3 * y443Tl 5 * y443Tl 6 * y443Tl 9
  calc x₀ ^ 9 * y443Tl 4 = (x₀ * x₀) * (x₀ * x₀) * (x₀ * x₀) * (x₀ * x₀) * (x₀ * y443Tl 4) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = _ := by
        rw [hQ, hR, nP]
        simp only [List.map_append, List.prod_append]

theorem cf_eq_of_interp_eq
    {u v : Native.DVec} (h : interp u = interp v) {k : ℕ}
    (hk : k < 196884) : cf u k = cf v k := by
  by_cases h1 : k < 300
  · obtain ⟨hlt1, hlt2⟩ := aPos_lt k h1
    have h2 := congrArg (fun x : SpaceB => (x.1 : Matrix (Fin 24) (Fin 24) ℚ)
      (finOf (Native.aPos k).1) (finOf (Native.aPos k).2)) h
    have h3 : (u.D.getD (Native.aIdx (finOf (Native.aPos k).1 : ℕ)
        (finOf (Native.aPos k).2 : ℕ)) 0 : ℚ) / 2 ^ u.e =
        (v.D.getD (Native.aIdx (finOf (Native.aPos k).1 : ℕ)
          (finOf (Native.aPos k).2 : ℕ)) 0 : ℚ) / 2 ^ v.e := h2
    rw [finOf_val _ hlt1, finOf_val _ hlt2, aIdx_aPos k h1] at h3
    exact h3
  · by_cases h2 : k < 98580
    · have hp : k - 300 < 98280 := by omega
      have h3 := congrArg (fun x : SpaceB => x.2.1 (shortOf ⟨k - 300, hp⟩)) h
      have h4 : (u.D.getD (300 + posOf (shortOf ⟨k - 300, hp⟩)) 0 : ℚ) / 2 ^ u.e =
          (v.D.getD (300 + posOf (shortOf ⟨k - 300, hp⟩)) 0 : ℚ) / 2 ^ v.e := h3
      rw [posOf_shortOf] at h4
      have e : 300 + ((⟨k - 300, hp⟩ : Fin 98280) : ℕ) = k := by
        show 300 + (k - 300) = k
        omega
      rw [e] at h4
      exact h4
    · have hr : (k - 98580) / 24 < 4096 := by omega
      have hj : (k - 98580) % 24 < 24 := by omega
      have h3 := congrArg (fun x : SpaceB =>
        x.2.2 (spinOfRow ((k - 98580) / 24)) (finOf ((k - 98580) % 24))) h
      have h4 : (u.D.getD (98580 + 24 * rowOf (spinOfRow ((k - 98580) / 24)) +
          (finOf ((k - 98580) % 24) : ℕ)) 0 : ℚ) / 2 ^ u.e =
          (v.D.getD (98580 + 24 * rowOf (spinOfRow ((k - 98580) / 24)) +
            (finOf ((k - 98580) % 24) : ℕ)) 0 : ℚ) / 2 ^ v.e := h3
      rw [rowOf_spinOfRow hr, finOf_val _ hj] at h4
      have e : 98580 + 24 * ((k - 98580) / 24) + (k - 98580) % 24 = k := by omega
      rw [e] at h4
      exact h4

theorem moveCheckAux_spec {u v : Native.DVec} (h : moveCheckAux u v = true) :
    ∃ k < 196884, u.D.getD k 0 * 2 ^ v.e ≠ v.D.getD k 0 * 2 ^ u.e := by
  unfold moveCheckAux at h
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne] at h
  exact h

theorem moveCheck_sound
    {w : List Native.Gen} {v : Native.DVec} (h : moveCheck w v = true) :
    wordLin w (interp v) ≠ interp v := by
  unfold moveCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hv, hm⟩ := h
  have hw : ∀ g ∈ w, g.validB = true := fun g hg => List.all_eq_true.1 hv g hg
  obtain ⟨k, hk, hne⟩ := moveCheckAux_spec hm
  intro heq
  rw [← evalWord_sound w hw v] at heq
  have hcf := cf_eq_of_interp_eq heq hk
  apply hne
  unfold cf at hcf
  have h2 : (2 : ℚ) ^ (Native.evalWord w v).e ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (2 : ℚ) ^ v.e ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_eq_div_iff h2 h3] at hcf
  exact_mod_cast hcf

theorem pow_four_eq_one_of_comm {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : a * (b * a * b) = (b * a * b) * a) : (a * b) ^ 4 = 1 := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hn : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, hai, hbi]
  have h2 : (a * b) ^ 2 = ((a * b) ^ 2)⁻¹ := by
    rw [← inv_pow, hn, pow_two, pow_two]
    simpa only [mul_assoc] using h
  calc (a * b) ^ 4 = (a * b) ^ 2 * (a * b) ^ 2 := by rw [← pow_add]
    _ = 1 := mul_eq_one_iff_eq_inv.2 h2

end EdgeNoncomm

end CFSG.YGroups.Y443
