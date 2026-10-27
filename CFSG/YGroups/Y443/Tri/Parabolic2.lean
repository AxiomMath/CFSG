module

public import CFSG.YGroups.Y443.CentralProjection
public import CFSG.YGroups.Y433.TwoCentral
public import Certificates.Certificate10093
public import Certificates.Certificate10098
public import Certificates.Certificate10103

public section

namespace CFSG.YGroups

open CFSG.Open (MonsterY443 MonsterY443Gen MonsterY443Adj MonsterY443Derived)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

namespace Y443

theorem mul_mul_cancel_of_mul_self {G : Type*} [Group G] {x : G} (h : x * x = 1) (z : G) :
    x * (x * z) = z := by
  rw [← mul_assoc, h, one_mul]

@[expose] def ρL (c : ℕ) : ℕ :=
  if 1 ≤ c ∧ c ≤ 4 then c + 4 else if 5 ≤ c ∧ c ≤ 8 then c - 4 else c

theorem ρL_ρL (c : ℕ) : ρL (ρL c) = c := by
  unfold ρL
  split_ifs <;> omega

theorem ρL_lt {c : ℕ} (hc : c < 12) : ρL c < 12 := by
  unfold ρL
  split_ifs <;> omega

theorem ρL_zero : ρL 0 = 0 := rfl

theorem ρL_of_ge {c : ℕ} (hc : 9 ≤ c) : ρL c = c := by
  unfold ρL
  split_ifs <;> omega

theorem pairsPreserved_ρL : Relabel.PairsPreserved 4 4 3 4 4 3 ρL := by decide

section SpiderSwap

local notation "yg" => yGen 4 4 3

private def Comm4 (s t : ℕ) : Prop :=
  s < 12 ∧ t < 12 ∧ s ≠ t ∧ (s, t) ∉ yEdges 4 4 3 ∧ (t, s) ∉ yEdges 4 4 3

private instance (s t : ℕ) : Decidable (Comm4 s t) := by
  unfold Comm4
  infer_instance

private theorem yg_comm {s t : ℕ} (h : Comm4 s t) : yg s * yg t = yg t * yg s :=
  (Relabel.commute_yGen_of_not_edge h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).eq

private theorem yg_lcomm {s t : ℕ} (h : Comm4 s t) (z : YGroup 4 4 3) :
    yg s * (yg t * z) = yg t * (yg s * z) := by
  rw [← mul_assoc, yg_comm h, mul_assoc]

private theorem yg_commute_word {s : ℕ} {w : List ℕ} (hs : s < 12)
    (h : ∀ c ∈ w, c < 12 ∧ c ≠ s ∧ (s, c) ∉ yEdges 4 4 3 ∧ (c, s) ∉ yEdges 4 4 3) :
    yg s * evalWord yg w = evalWord yg w * yg s :=
  (Relabel.commute_yGen_evalWord (p := 4) (q := 4) (r := 3) hs h).eq

private theorem yg_cube : (yg 9 * yg 10) ^ 3 = 1 := by
  have h := Y443.yGen_pair_pow (p := 4) (q := 4) (r := 3) (s := 9) (t := 10) (by norm_num)
    (by decide)
  have e : pairExp 4 4 3 9 10 = 3 := by decide
  rwa [e] at h

private theorem braid_five : yg 9 * (yg 10 * (yg 9 * (yg 10 * yg 9))) = yg 10 := by
  have h := yg_cube
  have h10 := yGen_mul_self 4 4 3 10
  rw [pow_three] at h
  have e : yg 9 * (yg 10 * (yg 9 * (yg 10 * yg 9))) =
      (yg 9 * yg 10 * (yg 9 * yg 10 * (yg 9 * yg 10))) * yg 10 := by
    simp only [mul_assoc, h10, mul_one]
  rw [e, h, one_mul]

private theorem braid_four : yg 9 * (yg 10 * (yg 9 * yg 10)) = yg 10 * yg 9 := by
  have h9 := yGen_mul_self 4 4 3 9
  have e : yg 9 * (yg 10 * (yg 9 * yg 10)) =
      (yg 9 * (yg 10 * (yg 9 * (yg 10 * yg 9)))) * yg 9 := by
    simp only [mul_assoc, h9, mul_one]
  rw [e, braid_five]

private theorem braid_four' (z : YGroup 4 4 3) :
    yg 9 * (yg 10 * (yg 9 * (yg 10 * z))) = yg 10 * (yg 9 * z) := by
  calc yg 9 * (yg 10 * (yg 9 * (yg 10 * z))) = (yg 9 * (yg 10 * (yg 9 * yg 10))) * z := by
        simp only [mul_assoc]
    _ = yg 10 * (yg 9 * z) := by rw [braid_four, mul_assoc]

private theorem spider_flat :
    (yg 0 * yg 1 * yg 2) * (yg 0 * yg 5 * yg 6) * (yg 0 * yg 9 * yg 10) =
      yg 0 * yg 1 * yg 0 * yg 5 * yg 0 * yg 9 * yg 10 * yg 6 * yg 2 := by
  have h1 : yg 2 * ((yg 0 * yg 5 * yg 6) * (yg 0 * yg 9 * yg 10)) =
      ((yg 0 * yg 5 * yg 6) * (yg 0 * yg 9 * yg 10)) * yg 2 := by
    simpa only [evalWord_cons, evalWord_nil, mul_one, mul_assoc] using
      yg_commute_word (s := 2) (w := [0, 5, 6, 0, 9, 10]) (by norm_num) (by decide)
  have h2 : yg 6 * (yg 0 * yg 9 * yg 10) = (yg 0 * yg 9 * yg 10) * yg 6 := by
    simpa only [evalWord_cons, evalWord_nil, mul_one, mul_assoc] using
      yg_commute_word (s := 6) (w := [0, 9, 10]) (by norm_num) (by decide)
  calc (yg 0 * yg 1 * yg 2) * (yg 0 * yg 5 * yg 6) * (yg 0 * yg 9 * yg 10)
      = yg 0 * yg 1 * (yg 2 * ((yg 0 * yg 5 * yg 6) * (yg 0 * yg 9 * yg 10))) := by
        simp only [mul_assoc]
    _ = yg 0 * yg 1 * (((yg 0 * yg 5 * yg 6) * (yg 0 * yg 9 * yg 10)) * yg 2) := by rw [h1]
    _ = yg 0 * yg 1 * (yg 0 * yg 5 * (yg 6 * (yg 0 * yg 9 * yg 10))) * yg 2 := by
        simp only [mul_assoc]
    _ = yg 0 * yg 1 * (yg 0 * yg 5 * ((yg 0 * yg 9 * yg 10) * yg 6)) * yg 2 := by rw [h2]
    _ = yg 0 * yg 1 * yg 0 * yg 5 * yg 0 * yg 9 * yg 10 * yg 6 * yg 2 := by
        simp only [mul_assoc]

@[expose] noncomputable def spiderConj : YGroup 4 4 3 := yg 2 * yg 6 * (yg 9 * yg 10 * yg 9)

theorem spiderConj_mul_self : spiderConj * spiderConj = 1 := by
  have h2 := yGen_mul_self 4 4 3 2
  have h6 := yGen_mul_self 4 4 3 6
  have h9 := yGen_mul_self 4 4 3 9
  have h10 := yGen_mul_self 4 4 3 10
  have hV : (yg 9 * yg 10 * yg 9) * (yg 9 * yg 10 * yg 9) = 1 := by
    simp only [mul_assoc]
    rw [mul_mul_cancel_of_mul_self h9, mul_mul_cancel_of_mul_self h10, h9]
  have c2V : yg 2 * (yg 9 * yg 10 * yg 9) = (yg 9 * yg 10 * yg 9) * yg 2 := by
    simpa only [evalWord_cons, evalWord_nil, mul_one, mul_assoc] using
      yg_commute_word (s := 2) (w := [9, 10, 9]) (by norm_num) (by decide)
  have c6V : yg 6 * (yg 9 * yg 10 * yg 9) = (yg 9 * yg 10 * yg 9) * yg 6 := by
    simpa only [evalWord_cons, evalWord_nil, mul_one, mul_assoc] using
      yg_commute_word (s := 6) (w := [9, 10, 9]) (by norm_num) (by decide)
  have c26 : yg 2 * yg 6 = yg 6 * yg 2 := yg_comm (by decide)
  have hU : (yg 2 * yg 6) * (yg 2 * yg 6) = 1 := by
    have := (show Commute (yg 6) (yg 2) from c26.symm).mul_mul_mul_comm (yg 2) (yg 6)
    rw [this, h2, h6, mul_one]
  have hUV : Commute (yg 2 * yg 6) (yg 9 * yg 10 * yg 9) :=
    Commute.mul_left (show Commute (yg 2) _ from c2V) (show Commute (yg 6) _ from c6V)
  have := hUV.symm.mul_mul_mul_comm (yg 2 * yg 6) (yg 9 * yg 10 * yg 9)
  unfold spiderConj
  rw [this, hU, hV, mul_one]

theorem spider_swap_conj :
    spiderConj * (blk1 * blk2 * blk3) * spiderConj = (blk2 * blk1 * blk3)⁻¹ := by
  have h2 := yGen_mul_self 4 4 3 2
  have h6 := yGen_mul_self 4 4 3 6
  have hL : spiderConj * ((yg 0 * yg 1 * yg 2) * (yg 0 * yg 5 * yg 6) * (yg 0 * yg 9 * yg 10)) *
      spiderConj = yg 2 * (yg 6 * (yg 10 * (yg 9 * (yg 0 * (yg 1 * (yg 0 * (yg 5 * yg 0))))))) := by
    rw [spider_flat]
    unfold spiderConj
    simp only [mul_assoc]
    rw [mul_mul_cancel_of_mul_self h2, mul_mul_cancel_of_mul_self h6, braid_five]
    rw [yg_comm (s := 0) (t := 10) (by decide), yg_lcomm (s := 5) (t := 10) (by decide),
      yg_lcomm (s := 0) (t := 10) (by decide), yg_lcomm (s := 1) (t := 10) (by decide),
      yg_lcomm (s := 0) (t := 10) (by decide), braid_four']
  have hR : ((yg 0 * yg 5 * yg 6) * (yg 0 * yg 1 * yg 2) * (yg 0 * yg 9 * yg 10))⁻¹ =
      yg 2 * (yg 6 * (yg 10 * (yg 9 * (yg 0 * (yg 1 * (yg 0 * (yg 5 * yg 0))))))) := by
    simp only [mul_inv_rev, yGen_inv, mul_assoc]
    rw [yg_lcomm (s := 0) (t := 2) (by decide), yg_lcomm (s := 9) (t := 2) (by decide),
      yg_lcomm (s := 10) (t := 2) (by decide)]
    rw [yg_lcomm (s := 0) (t := 6) (by decide), yg_lcomm (s := 1) (t := 6) (by decide),
      yg_lcomm (s := 0) (t := 6) (by decide), yg_lcomm (s := 9) (t := 6) (by decide),
      yg_lcomm (s := 10) (t := 6) (by decide)]
  show spiderConj * ((yg 0 * yg 1 * yg 2) * (yg 0 * yg 5 * yg 6) * (yg 0 * yg 9 * yg 10)) *
      spiderConj = ((yg 0 * yg 5 * yg 6) * (yg 0 * yg 1 * yg 2) * (yg 0 * yg 9 * yg 10))⁻¹
  rw [hL, hR]

theorem spider_swap : (blk2 * blk1 * blk3) ^ 10 = 1 := by
  have hg := spiderConj_mul_self
  have hginv : spiderConj⁻¹ = spiderConj := inv_eq_of_mul_eq_one_right hg
  have h1 : blk2 * blk1 * blk3 = (spiderConj * (blk1 * blk2 * blk3) * spiderConj)⁻¹ := by
    rw [spider_swap_conj, inv_inv]
  have h2 : (spiderConj * (blk1 * blk2 * blk3) * spiderConj) ^ 10 =
      spiderConj * (blk1 * blk2 * blk3) ^ 10 * spiderConj := by
    have := conj_pow (a := spiderConj) (b := blk1 * blk2 * blk3) (i := 10)
    rwa [hginv] at this
  rw [h1, inv_pow, h2, spider443, mul_one, hg, inv_one]

theorem spider_ρL :
    evalWord (fun c => yGen 4 4 3 (ρL c)) (spiderWord 4 4) ^ 10 = 1 := by
  have e : evalWord (fun c => yGen 4 4 3 (ρL c)) (spiderWord 4 4) = blk2 * blk1 * blk3 := by
    rw [Relabel.evalWord_spiderWord]
    rfl
  rw [e]
  exact spider_swap

end SpiderSwap

@[expose] noncomputable def ρY : YGroup 4 4 3 →* YGroup 4 4 3 :=
  Relabel.hom ρL pairsPreserved_ρL (fun _ _ _ => spider_ρL)

theorem ρY_yGen {c : ℕ} (hc : c < 12) : ρY (yGen 4 4 3 c) = yGen 4 4 3 (ρL c) :=
  Relabel.hom_yGen (show c < ngen 4 4 3 from hc)

theorem ρY_ρY (x : YGroup 4 4 3) : ρY (ρY x) = x := by
  have h : ρY.comp ρY = MonoidHom.id (YGroup 4 4 3) := by
    refine PresentedGroup.ext fun c => ?_
    have hc : (c : ℕ) < 12 := c.2
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, ← yGen_of_lt c.2, ρY_yGen hc,
      ρY_yGen (ρL_lt hc), ρL_ρL]
  exact DFunLike.congr_fun h x

@[expose] noncomputable def ρYEquiv : YGroup 4 4 3 ≃* YGroup 4 4 3 :=
  MulEquiv.mk' ⟨ρY, ρY, ρY_ρY, ρY_ρY⟩ ρY.map_mul

end Y443

section ArmSwap

open Y443

@[expose] noncomputable def y443Rho : MonsterY443 ≃* MonsterY443 :=
  y443EquivOpen.symm.trans (ρYEquiv.trans y443EquivOpen)

@[expose] def y443E2 : MonsterY443Gen := some ⟨1, ⟨3, by decide⟩⟩

@[expose] def y443D2 : MonsterY443Gen := some ⟨1, ⟨2, by decide⟩⟩

theorem y443LetterOfGen_E2 : y443LetterOfGen y443E2 = 8 := rfl

theorem y443LetterOfGen_D2 : y443LetterOfGen y443D2 = 7 := rfl

theorem y443E2_ne_E1 : y443E2 ≠ y443E1 := by decide

theorem y443E2_ne_D1 : y443E2 ≠ y443D1 := by decide

theorem y443D1_ne_E2 : y443D1 ≠ y443E2 := by decide

theorem y443E1_ne_D2 : y443E1 ≠ y443D2 := by decide

theorem y443D2_ne_E1 : y443D2 ≠ y443E1 := by decide

theorem y443D1_ne_E1 : y443D1 ≠ y443E1 := by decide

theorem y443D2_ne_E2 : y443D2 ≠ y443E2 := by decide

@[expose] def y443RhoSym (s : MonsterY443Gen) : MonsterY443Gen :=
  y443GenOfLetter (ρL (y443LetterOfGen s))

theorem y443LetterOfGen_rhoSym (s : MonsterY443Gen) :
    y443LetterOfGen (y443RhoSym s) = ρL (y443LetterOfGen s) :=
  y443LetterOfGen_genOfLetter _ (ρL_lt (y443LetterOfGen_lt s))

theorem y443RhoSym_rhoSym (s : MonsterY443Gen) : y443RhoSym (y443RhoSym s) = s := by
  calc y443RhoSym (y443RhoSym s) = y443GenOfLetter (ρL (y443LetterOfGen (y443RhoSym s))) := rfl
    _ = s := by rw [y443LetterOfGen_rhoSym, ρL_ρL, y443GenOfLetter_letterOfGen]

theorem y443RhoSym_E1 : y443RhoSym y443E1 = y443E2 := by decide

theorem y443RhoSym_E2 : y443RhoSym y443E2 = y443E1 := by decide

theorem y443RhoSym_D1 : y443RhoSym y443D1 = y443D2 := by decide

theorem y443RhoSym_D2 : y443RhoSym y443D2 = y443D1 := by decide

theorem y443RhoSym_eq_E1_iff {s : MonsterY443Gen} : y443RhoSym s = y443E1 ↔ s = y443E2 := by
  constructor
  · intro h
    rw [← y443RhoSym_rhoSym s, h, y443RhoSym_E1]
  · rintro rfl
    exact y443RhoSym_E2

theorem y443RhoSym_eq_E2_iff {s : MonsterY443Gen} : y443RhoSym s = y443E2 ↔ s = y443E1 := by
  constructor
  · intro h
    rw [← y443RhoSym_rhoSym s, h, y443RhoSym_E2]
  · rintro rfl
    exact y443RhoSym_E1

theorem y443RhoSym_eq_D1_iff {s : MonsterY443Gen} : y443RhoSym s = y443D1 ↔ s = y443D2 := by
  constructor
  · intro h
    rw [← y443RhoSym_rhoSym s, h, y443RhoSym_D1]
  · rintro rfl
    exact y443RhoSym_D2

theorem y443RhoSym_eq_D2_iff {s : MonsterY443Gen} : y443RhoSym s = y443D2 ↔ s = y443D1 := by
  constructor
  · intro h
    rw [← y443RhoSym_rhoSym s, h, y443RhoSym_D2]
  · rintro rfl
    exact y443RhoSym_D1

theorem y443Rho_gen {c : ℕ} (hc : c < 12) : y443Rho (y443Gen c) = y443Gen (ρL c) := by
  have h1 : y443EquivOpen.symm (y443Gen c) = yGen 4 4 3 c :=
    y443EquivOpen.symm_apply_eq.2 (y443EquivOpen_yGen_eq hc).symm
  show y443EquivOpen (ρYEquiv (y443EquivOpen.symm (y443Gen c))) = y443Gen (ρL c)
  rw [h1]
  show y443EquivOpen (ρY (yGen 4 4 3 c)) = _
  rw [ρY_yGen hc, y443EquivOpen_yGen_eq (ρL_lt hc)]

theorem y443Rho_rho (x : MonsterY443) : y443Rho (y443Rho x) = x := by
  show y443EquivOpen (ρYEquiv (y443EquivOpen.symm (y443EquivOpen (ρYEquiv
    (y443EquivOpen.symm x))))) = x
  rw [MulEquiv.symm_apply_apply]
  show y443EquivOpen (ρY (ρY (y443EquivOpen.symm x))) = x
  rw [ρY_ρY, MulEquiv.apply_symm_apply]

theorem y443Rho_of (s : MonsterY443Gen) :
    y443Rho (PresentedGroup.of s) = PresentedGroup.of (y443RhoSym s) := by
  rw [← y443Gen_letterOfGen s, y443Rho_gen (y443LetterOfGen_lt s), y443Gen]
  rfl

theorem y443Parity_rho (x : MonsterY443) : y443Parity (y443Rho x) = y443Parity x := by
  have h : y443Parity.comp y443Rho.toMonoidHom = y443Parity := by
    refine PresentedGroup.ext fun s => ?_
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, y443Rho_of, y443Parity_of,
      y443Parity_of]
  exact DFunLike.congr_fun h x

theorem y443Rho_mem_derived {x : MonsterY443} (hx : x ∈ MonsterY443Derived) :
    y443Rho x ∈ MonsterY443Derived := by
  rw [y443_mem_derived_iff] at hx ⊢
  rw [y443Parity_rho, hx]

theorem y443Rho_symm : y443Rho.symm = y443Rho :=
  MulEquiv.ext fun x => y443Rho.symm_apply_eq.2 (y443Rho_rho x).symm

theorem y443Rho_map_derived :
    MonsterY443Derived.map y443Rho.toMonoidHom = MonsterY443Derived := by
  ext x
  rw [Subgroup.mem_map_equiv, y443Rho_symm, y443_mem_derived_iff, y443_mem_derived_iff,
    y443Parity_rho]

theorem y443EquivOpen_zY' : y443EquivOpen Y443.zY' =
    (y443Gen 0 * y443Gen 9 * y443Gen 10 * y443Gen 11 * y443Gen 5 * y443Gen 6 * y443Gen 1) ^ 9 := by
  simp only [Y443.zY', map_pow, map_mul, Nat.ofNat_pos, y443EquivOpen_yGen, Nat.reduceLT,
    Nat.lt_add_one, Nat.one_lt_ofNat, y443Gen]

theorem y443Rho_Z :
    y443Rho y443Z = y443Z := by
  have h : y443Rho y443Z =
      (y443Gen 0 * y443Gen 9 * y443Gen 10 * y443Gen 11 * y443Gen 5 * y443Gen 6 *
        y443Gen 1) ^ 9 := by
    simp only [y443Z, map_pow, map_mul, y443Rho_gen (show 0 < 12 by norm_num),
      y443Rho_gen (show 9 < 12 by norm_num), y443Rho_gen (show 10 < 12 by norm_num),
      y443Rho_gen (show 11 < 12 by norm_num), y443Rho_gen (show 1 < 12 by norm_num),
      y443Rho_gen (show 2 < 12 by norm_num), y443Rho_gen (show 5 < 12 by norm_num)]
    rfl
  rw [h, ← y443EquivOpen_zY', ← y443EquivOpen_zY, Y443.y322_transfer_Z.1]

@[expose] noncomputable def y443RhoM : MonsterY443Derived ≃* MonsterY443Derived where
  toFun m := ⟨y443Rho (m : MonsterY443), y443Rho_mem_derived m.2⟩
  invFun m := ⟨y443Rho (m : MonsterY443), y443Rho_mem_derived m.2⟩
  left_inv m := Subtype.ext (y443Rho_rho (m : MonsterY443))
  right_inv m := Subtype.ext (y443Rho_rho (m : MonsterY443))
  map_mul' m n := Subtype.ext (map_mul y443Rho (m : MonsterY443) (n : MonsterY443))

theorem y443RhoM_coe (m : MonsterY443Derived) :
    ((y443RhoM m : MonsterY443Derived) : MonsterY443) = y443Rho (m : MonsterY443) := rfl

theorem y443RhoM_rhoM (m : MonsterY443Derived) : y443RhoM (y443RhoM m) = m :=
  Subtype.ext (y443Rho_rho (m : MonsterY443))

theorem y443RhoM_symm : y443RhoM.symm = y443RhoM :=
  MulEquiv.ext fun m => y443RhoM.symm_apply_eq.2 (y443RhoM_rhoM m).symm

theorem y443RhoM_T
    (s : MonsterY443Gen) : y443RhoM (y443T s) = y443T (y443RhoSym s) := by
  refine Subtype.ext ?_
  rw [y443RhoM_coe, y443T_coe, y443T_coe, map_mul, y443Rho_of, y443Rho_Z]

theorem y443RhoM_Tl
    {c : ℕ} (hc : c < 12) : y443RhoM (y443Tl c) = y443Tl (ρL c) := by
  unfold y443Tl
  rw [y443RhoM_T]
  unfold y443RhoSym
  rw [y443LetterOfGen_genOfLetter c hc]

@[expose] noncomputable def y443H' : Subgroup MonsterY443Derived :=
  Subgroup.closure (y443T '' {s | s ≠ y443E2})

@[expose] noncomputable def y443K' : Subgroup MonsterY443Derived :=
  Subgroup.closure (y443T '' {s | s ≠ y443E2 ∧ s ≠ y443D2})

@[expose] noncomputable def y443R : Subgroup MonsterY443Derived :=
  Subgroup.closure (y443T '' {s | s ≠ y443E1 ∧ s ≠ y443E2})

@[expose] noncomputable def y443X' : MonsterY443Derived := y443T y443E2

@[expose] noncomputable def y443Y' : MonsterY443Derived := y443T y443D2

@[expose] noncomputable def y443C' : MonsterY443Derived := y443RhoM y443C

@[expose] noncomputable def y443S : MonsterY443Derived := y443X * y443C * y443Y * y443X

theorem y443T_mem_H' {s : MonsterY443Gen} (hs : s ≠ y443E2) : y443T s ∈ y443H' :=
  Subgroup.subset_closure ⟨s, hs, rfl⟩

theorem y443T_mem_K' {s : MonsterY443Gen} (hs : s ≠ y443E2) (hs' : s ≠ y443D2) :
    y443T s ∈ y443K' :=
  Subgroup.subset_closure ⟨s, ⟨hs, hs'⟩, rfl⟩

theorem y443T_mem_R {s : MonsterY443Gen} (hs : s ≠ y443E1) (hs' : s ≠ y443E2) :
    y443T s ∈ y443R :=
  Subgroup.subset_closure ⟨s, ⟨hs, hs'⟩, rfl⟩

theorem y443Tl_mem_H' {k : ℕ} (hk : k < 12) (hk8 : k ≠ 8) : y443Tl k ∈ y443H' := by
  refine y443T_mem_H' fun h => hk8 ?_
  have := congrArg y443LetterOfGen h
  rw [y443LetterOfGen_genOfLetter k hk, y443LetterOfGen_E2] at this
  exact this

theorem y443Tl_mem_R {k : ℕ} (hk : k < 12) (hk4 : k ≠ 4) (hk8 : k ≠ 8) : y443Tl k ∈ y443R := by
  refine y443T_mem_R (fun h => hk4 ?_) fun h => hk8 ?_
  · have := congrArg y443LetterOfGen h
    rw [y443LetterOfGen_genOfLetter k hk, y443LetterOfGen_E1] at this
    exact this
  · have := congrArg y443LetterOfGen h
    rw [y443LetterOfGen_genOfLetter k hk, y443LetterOfGen_E2] at this
    exact this

theorem y443RhoSym_image (p : MonsterY443Gen → Prop) :
    y443RhoSym '' {s | p s} = {s | p (y443RhoSym s)} := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    show p (y443RhoSym (y443RhoSym t))
    rw [y443RhoSym_rhoSym]
    exact ht
  · intro hs
    exact ⟨y443RhoSym s, hs, y443RhoSym_rhoSym s⟩

theorem y443RhoM_map_closure_T
    (P : Set MonsterY443Gen) :
    (Subgroup.closure (y443T '' P)).map y443RhoM.toMonoidHom =
      Subgroup.closure (y443T '' (y443RhoSym '' P)) := by
  have e : y443RhoM.toMonoidHom '' (y443T '' P) = y443T '' (y443RhoSym '' P) := by
    rw [← Set.image_comp, ← Set.image_comp]
    congr 1
    funext s
    exact y443RhoM_T s
  rw [MonoidHom.map_closure, e]

theorem y443RhoM_map_H :
    y443H.map y443RhoM.toMonoidHom = y443H' := by
  have e : {s | y443RhoSym s ≠ y443E1} = {s | s ≠ y443E2} :=
    Set.ext fun s => not_congr y443RhoSym_eq_E1_iff
  rw [y443H, y443H', y443RhoM_map_closure_T, y443RhoSym_image, e]

theorem y443RhoM_map_K :
    y443K.map y443RhoM.toMonoidHom = y443K' := by
  have e : {s | y443RhoSym s ≠ y443E1 ∧ y443RhoSym s ≠ y443D1} =
      {s | s ≠ y443E2 ∧ s ≠ y443D2} :=
    Set.ext fun s => and_congr (not_congr y443RhoSym_eq_E1_iff) (not_congr y443RhoSym_eq_D1_iff)
  rw [y443K, y443K', y443RhoM_map_closure_T, y443RhoSym_image, e]

theorem y443RhoM_map_R :
    y443R.map y443RhoM.toMonoidHom = y443R := by
  have e : {s | y443RhoSym s ≠ y443E1 ∧ y443RhoSym s ≠ y443E2} =
      {s | s ≠ y443E1 ∧ s ≠ y443E2} :=
    Set.ext fun s => (and_congr (not_congr y443RhoSym_eq_E1_iff)
      (not_congr y443RhoSym_eq_E2_iff)).trans and_comm
  rw [y443R, y443RhoM_map_closure_T, y443RhoSym_image, e]

theorem y443RhoM_map_H' :
    y443H'.map y443RhoM.toMonoidHom = y443H := by
  rw [← y443RhoM_map_H, Subgroup.map_map]
  have : y443RhoM.toMonoidHom.comp y443RhoM.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext y443RhoM_rhoM
  rw [this, Subgroup.map_id]

theorem y443RhoM_X :
    y443RhoM y443X = y443X' := by
  show y443RhoM (y443T y443E1) = y443T y443E2
  rw [y443RhoM_T, y443RhoSym_E1]

theorem y443RhoM_Y :
    y443RhoM y443Y = y443Y' := by
  show y443RhoM (y443T y443D1) = y443T y443D2
  rw [y443RhoM_T, y443RhoSym_D1]

theorem y443RhoM_C : y443RhoM y443C = y443C' := rfl

theorem y443RhoM_mem_H_iff
    {m : MonsterY443Derived} : y443RhoM m ∈ y443H ↔ m ∈ y443H' := by
  rw [← y443RhoM_map_H, Subgroup.mem_map_equiv, y443RhoM_symm]

theorem y443RhoM_mem_H'_iff
    {m : MonsterY443Derived} : y443RhoM m ∈ y443H' ↔ m ∈ y443H := by
  rw [← y443RhoM_map_H', Subgroup.mem_map_equiv, y443RhoM_symm]

@[expose] noncomputable def y443HEquivH' :
    y443H ≃* y443H' :=
  (y443RhoM.subgroupMap y443H).trans (MulEquiv.subgroupCongr y443RhoM_map_H)

theorem y443HEquivH'_coe
    (h : y443H) :
    ((y443HEquivH' h : y443H') : MonsterY443Derived) = y443RhoM (h : MonsterY443Derived) := rfl

theorem y443_arm_swap_images :
    y443RhoM y443C = y443C' ∧ y443RhoM y443X = y443X' ∧ y443RhoM y443Y = y443Y' ∧
      y443H.map y443RhoM.toMonoidHom = y443H' ∧ y443K.map y443RhoM.toMonoidHom = y443K' ∧
      y443R.map y443RhoM.toMonoidHom = y443R :=
  ⟨y443RhoM_C, y443RhoM_X, y443RhoM_Y, y443RhoM_map_H, y443RhoM_map_K, y443RhoM_map_R⟩

theorem y443RhoM_C' : y443RhoM y443C' = y443C := y443RhoM_rhoM y443C

@[expose] noncomputable def y443F0Sw : MonsterY443 :=
  (y443Gen 0 * y443Gen 5 * y443Gen 6 * y443Gen 7 * y443Gen 1 * y443Gen 2 * y443Gen 9) ^ 9

theorem y443Rho_F0 : y443Rho y443F0 = y443F0Sw := by
  simp only [y443F0, y443F0Sw, map_pow, map_mul, y443Rho_gen (show 0 < 12 by norm_num),
    y443Rho_gen (show 1 < 12 by norm_num), y443Rho_gen (show 2 < 12 by norm_num),
    y443Rho_gen (show 3 < 12 by norm_num), y443Rho_gen (show 5 < 12 by norm_num),
    y443Rho_gen (show 6 < 12 by norm_num), y443Rho_gen (show 9 < 12 by norm_num)]
  rfl

theorem y443C'_coe :
    (y443C' : MonsterY443) = y443F0Sw * y443Z := by
  show ((y443RhoM y443C : MonsterY443Derived) : MonsterY443) = _
  rw [y443RhoM_coe, y443C_coe, map_mul, y443Rho_F0, y443Rho_Z]

section Transfer

variable {G : Type*} [Group G] (f : MonsterY443Derived →* G)

theorem y443H_map_comp_rho :
    y443H.map (f.comp y443RhoM.toMonoidHom) = y443H'.map f := by
  rw [← y443RhoM_map_H, Subgroup.map_map]

theorem y443K_map_comp_rho :
    y443K.map (f.comp y443RhoM.toMonoidHom) = y443K'.map f := by
  rw [← y443RhoM_map_K, Subgroup.map_map]

theorem comp_rho_C : f.comp y443RhoM.toMonoidHom y443C = f y443C' := rfl

theorem comp_rho_X :
    f.comp y443RhoM.toMonoidHom y443X = f y443X' :=
  congrArg f y443RhoM_X

theorem comp_rho_Y :
    f.comp y443RhoM.toMonoidHom y443Y = f y443Y' :=
  congrArg f y443RhoM_Y

theorem injOn_comp_rho_iff :
    Set.InjOn (f.comp y443RhoM.toMonoidHom) y443H ↔ Set.InjOn f y443H' := by
  constructor
  · intro h a ha b hb hab
    have ha' : y443RhoM a ∈ y443H := y443RhoM_mem_H_iff.2 ha
    have hb' : y443RhoM b ∈ y443H := y443RhoM_mem_H_iff.2 hb
    have := h ha' hb' (by
      show f (y443RhoM (y443RhoM a)) = f (y443RhoM (y443RhoM b))
      rw [y443RhoM_rhoM, y443RhoM_rhoM]
      exact hab)
    exact y443RhoM.injective this
  · intro h a ha b hb hab
    exact y443RhoM.injective (h (y443RhoM_mem_H'_iff.2 ha) (y443RhoM_mem_H'_iff.2 hb) hab)

theorem natCard_H_map_comp_rho :
    Nat.card (y443H.map (f.comp y443RhoM.toMonoidHom)) = Nat.card (y443H'.map f) := by
  rw [y443H_map_comp_rho]

theorem comp_rho_X_not_mem_iff :
    f.comp y443RhoM.toMonoidHom y443X ∉ y443H.map (f.comp y443RhoM.toMonoidHom) ↔
      f y443X' ∉ y443H'.map f := by
  rw [y443H_map_comp_rho, comp_rho_X]

end Transfer

section ConjTransfer

variable {G : Type*} [Group G] (f : MonsterY443Derived →* G) (u : G)

theorem comp_rho_eq_conj_of
    (h : ∀ s : MonsterY443Gen, f (y443RhoM (y443T s)) = u * f (y443T s) * u⁻¹) :
    f.comp y443RhoM.toMonoidHom = (MulAut.conj u).toMonoidHom.comp f := by
  have hle : (⊤ : Subgroup MonsterY443Derived) ≤
      MonoidHom.eqLocus (f.comp y443RhoM.toMonoidHom) ((MulAut.conj u).toMonoidHom.comp f) := by
    rw [← y443_closure_range_T, Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    exact h s
  ext m
  exact hle (Subgroup.mem_top m)

theorem H'_map_eq_conj_of
    (h : ∀ s : MonsterY443Gen, f (y443RhoM (y443T s)) = u * f (y443T s) * u⁻¹) :
    y443H'.map f = (y443H.map f).map (MulAut.conj u).toMonoidHom := by
  rw [← y443H_map_comp_rho, comp_rho_eq_conj_of f u h, ← Subgroup.map_map]

theorem f_C'_eq_conj_of
    (h : ∀ s : MonsterY443Gen, f (y443RhoM (y443T s)) = u * f (y443T s) * u⁻¹) :
    f y443C' = u * f y443C * u⁻¹ := by
  have := DFunLike.congr_fun (comp_rho_eq_conj_of f u h) y443C
  exact this

theorem injOn_H'_of_conj_of
    (h : ∀ s : MonsterY443Gen, f (y443RhoM (y443T s)) = u * f (y443T s) * u⁻¹)
    (hinj : Set.InjOn f y443H) : Set.InjOn f y443H' := by
  rw [← injOn_comp_rho_iff, comp_rho_eq_conj_of f u h]
  intro a ha b hb hab
  exact hinj ha hb ((MulAut.conj u).injective hab)

end ConjTransfer

theorem y443C_eq_pow :

    y443C = (y443Tl 0 * y443Tl 1 * y443Tl 2 * y443Tl 3 * y443Tl 5 *
    y443Tl 6 * y443Tl 9) ^ 9 := by
  rw [← y443Pi_F0, y443F0]
  simp only [map_pow, map_mul, y443Pi_gen]

theorem y443C'_eq_pow :

    y443C' = (y443Tl 0 * y443Tl 5 * y443Tl 6 * y443Tl 7 * y443Tl 1 *
    y443Tl 2 * y443Tl 9) ^ 9 := by
  show y443RhoM y443C = _
  rw [y443C_eq_pow]
  simp only [map_pow, map_mul, y443RhoM_Tl (show 0 < 12 by norm_num),
    y443RhoM_Tl (show 1 < 12 by norm_num), y443RhoM_Tl (show 2 < 12 by norm_num),
    y443RhoM_Tl (show 3 < 12 by norm_num), y443RhoM_Tl (show 5 < 12 by norm_num),
    y443RhoM_Tl (show 6 < 12 by norm_num), y443RhoM_Tl (show 9 < 12 by norm_num)]
  rfl

theorem y443C_mem_R :
    y443C ∈ y443R := by
  rw [y443C_eq_pow]
  refine Subgroup.pow_mem _ ?_ 9
  refine y443R.mul_mem (y443R.mul_mem (y443R.mul_mem (y443R.mul_mem (y443R.mul_mem
    (y443R.mul_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_ <;>
    exact y443Tl_mem_R (by norm_num) (by norm_num) (by norm_num)

theorem y443R_le_H : y443R ≤ y443H := by
  rw [y443R, Subgroup.closure_le]
  rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
  exact y443T_mem_H hs

theorem y443R_le_H' : y443R ≤ y443H' := by
  rw [y443R, Subgroup.closure_le]
  rintro _ ⟨s, ⟨-, hs⟩, rfl⟩
  exact y443T_mem_H' hs

theorem y443R_le_inf : y443R ≤ y443H ⊓ y443H' := le_inf y443R_le_H y443R_le_H'

theorem y443K_le_H :
    y443K ≤ y443H := fun _ hk => (y443K_le_H_and_conj hk).1

theorem y443K'_le_H' :
    y443K' ≤ y443H' := by
  rw [← y443RhoM_map_K, ← y443RhoM_map_H]
  exact Subgroup.map_mono y443K_le_H

theorem y443C_mem_H' :
    y443C ∈ y443H' := y443R_le_H' y443C_mem_R

theorem y443X_mem_H' : y443X ∈ y443H' := y443T_mem_H' y443E2_ne_E1.symm

theorem y443Y_mem_H' : y443Y ∈ y443H' := y443T_mem_H' y443D1_ne_E2

theorem y443Y_mem_R : y443Y ∈ y443R := y443T_mem_R y443D1_ne_E1 y443D1_ne_E2

theorem y443C'_mem_H' :
    y443C' ∈ y443H' := by
  rw [← y443RhoM_map_H]
  exact Subgroup.mem_map_of_mem _ y443C_mem_H

theorem y443C'_mem_R :
    y443C' ∈ y443R := by
  rw [← y443RhoM_map_R]
  exact Subgroup.mem_map_of_mem _ y443C_mem_R

theorem y443C'_mem_H :
    y443C' ∈ y443H := y443R_le_H y443C'_mem_R

theorem y443C'_comm_H'
    {h : MonsterY443Derived} (hh : h ∈ y443H') : h * y443C' = y443C' * h := by
  have h1 := y443C_comm_H (y443RhoM_mem_H_iff.2 hh)
  have h2 := congrArg y443RhoM h1
  rw [map_mul, map_mul, y443RhoM_rhoM] at h2
  exact h2

theorem y443C_mem_center_R :
    ∃ hc : y443C ∈ y443R, (⟨y443C, hc⟩ : y443R) ∈ Subgroup.center y443R := by
  refine ⟨y443C_mem_R, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (y443C_comm_H (y443R_le_H g.2))

theorem y443C'_mem_center_R :
    ∃ hc : y443C' ∈ y443R, (⟨y443C', hc⟩ : y443R) ∈ Subgroup.center y443R := by
  refine ⟨y443C'_mem_R, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (y443C'_comm_H' (y443R_le_H' g.2))

theorem y443C'_mem_center_H' :
    ∃ hc : y443C' ∈ y443H', (⟨y443C', hc⟩ : y443H') ∈ Subgroup.center y443H' := by
  refine ⟨y443C'_mem_H', ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (y443C'_comm_H' g.2)

theorem y443X'_mem_H : y443X' ∈ y443H := y443T_mem_H y443E2_ne_E1

theorem y443Y'_mem_H : y443Y' ∈ y443H := y443T_mem_H y443D2_ne_E1

theorem y443Y'_mem_R : y443Y' ∈ y443R := y443T_mem_R y443D2_ne_E1 y443D2_ne_E2

theorem y443C_comm_X' :
    y443X' * y443C = y443C * y443X' := y443C_comm_H y443X'_mem_H

theorem y443C'_comm_X :
    y443X * y443C' = y443C' * y443X := y443C'_comm_H' y443X_mem_H'

theorem y443T_comm_X'
    {s : MonsterY443Gen} (hs : s ≠ y443E2) (hs' : s ≠ y443D2) :
    y443T s * y443X' = y443X' * y443T s := by
  have h := y443T_comm_X (s := y443RhoSym s) (fun h => hs (y443RhoSym_eq_E1_iff.1 h))
    (fun h => hs' (y443RhoSym_eq_D1_iff.1 h))
  have := congrArg y443RhoM h
  rw [map_mul, map_mul, y443RhoM_T, y443RhoSym_rhoSym, y443RhoM_X] at this
  exact this

theorem y443X'_mul_self :
    y443X' * y443X' = 1 := y443T_mul_self _

theorem y443Y'_mul_self :
    y443Y' * y443Y' = 1 := y443T_mul_self _

theorem y443C'_mul_self :
    y443C' * y443C' = 1 := by
  rw [← y443RhoM_C, ← map_mul, y443C_mul_self, map_one]

theorem y443_x'y'_cube :
    (y443X' * y443Y') ^ 3 = 1 := by
  rw [← y443RhoM_X, ← y443RhoM_Y, ← map_mul, ← map_pow, y443_xy_cube, map_one]

theorem y443Y'_mem_H' : y443Y' ∈ y443H' := y443T_mem_H' y443D2_ne_E2

theorem y443K'_le :

    y443K' ≤ y443H' ⊓ y443H'.map (MulAut.conj y443X').toMonoidHom := by
  intro k hk
  rw [← y443RhoM_map_K] at hk
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.1 hk
  obtain ⟨h1, h2⟩ := y443K_le hk₀
  refine ⟨?_, ?_⟩
  · rw [← y443RhoM_map_H]
    exact Subgroup.mem_map_of_mem _ h1
  · obtain ⟨h, hh, hk'⟩ := Subgroup.mem_map.1 h2
    refine Subgroup.mem_map.2 ⟨y443RhoM h, ?_, ?_⟩
    · rw [← y443RhoM_map_H]
      exact Subgroup.mem_map_of_mem _ hh
    · have := congrArg y443RhoM hk'
      rw [← y443RhoM_X]
      simpa [MulAut.conj_apply] using this

theorem y443S_mem_H' :
    y443S ∈ y443H' :=
  y443H'.mul_mem (y443H'.mul_mem (y443H'.mul_mem y443X_mem_H' y443C_mem_H') y443Y_mem_H')
    y443X_mem_H'

theorem y443S_mul_self :
    y443S * y443S = 1 := by
  have hx := y443X_mul_self
  have hc := y443C_mul_self
  have hy := y443Y_mul_self
  have hyc : y443Y * y443C = y443C * y443Y := y443C_comm_H y443Y_mem_H
  unfold y443S
  simp only [mul_assoc]
  rw [mul_mul_cancel_of_mul_self hx, (show Commute y443Y y443C from hyc).left_comm,
    mul_mul_cancel_of_mul_self hc, mul_mul_cancel_of_mul_self hy, hx]

theorem y443S_conj_mem_H'
    {r : MonsterY443Derived} (hr : r ∈ y443R) :
    y443S * r * y443S ∈ y443H' :=
  y443H'.mul_mem (y443H'.mul_mem y443S_mem_H' (y443R_le_H' hr)) y443S_mem_H'

theorem y443_closure_R_K :
    Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ (y443K : Set MonsterY443Derived)) =
      y443H := by
  refine le_antisymm ((Subgroup.closure_le _).2 (Set.union_subset y443R_le_H y443K_le_H)) ?_
  rw [y443H, Subgroup.closure_le]
  rintro _ ⟨s, hs, rfl⟩
  by_cases hs2 : s = y443E2
  · subst hs2
    refine Subgroup.subset_closure (Or.inr ?_)
    exact y443T_mem_K hs y443E2_ne_D1
  · exact Subgroup.subset_closure (Or.inl (y443T_mem_R hs hs2))

theorem y443_closure_R_K' :
    Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ (y443K' : Set MonsterY443Derived)) =
      y443H' := by
  have h := congrArg (Subgroup.map y443RhoM.toMonoidHom) y443_closure_R_K
  rw [MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map,
    y443RhoM_map_R, y443RhoM_map_K, y443RhoM_map_H] at h
  exact h

theorem y443_closure_R_X :
    Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ {y443X}) = y443H' := by
  refine le_antisymm ((Subgroup.closure_le _).2
    (Set.union_subset y443R_le_H' (Set.singleton_subset_iff.2 y443X_mem_H'))) ?_
  rw [y443H', Subgroup.closure_le]
  rintro _ ⟨s, hs, rfl⟩
  by_cases hs1 : s = y443E1
  · subst hs1
    exact Subgroup.subset_closure (Or.inr rfl)
  · exact Subgroup.subset_closure (Or.inl (y443T_mem_R hs1 hs))

theorem y443_closure_R_X' :
    Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ {y443X'}) = y443H := by
  have h := congrArg (Subgroup.map y443RhoM.toMonoidHom) y443_closure_R_X
  rw [MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, y443RhoM_map_R,
    Set.image_singleton, y443RhoM_map_H'] at h
  have e : y443RhoM.toMonoidHom y443X = y443X' := y443RhoM_X
  rwa [e] at h

theorem y443_closure_H_H' :
    Subgroup.closure ((y443H : Set MonsterY443Derived) ∪ (y443H' : Set MonsterY443Derived)) =
      ⊤ := by
  rw [eq_top_iff, ← y443_closure_range_T, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  by_cases hs : s = y443E1
  · subst hs
    exact Subgroup.subset_closure (Or.inr (y443T_mem_H' y443E2_ne_E1.symm))
  · exact Subgroup.subset_closure (Or.inl (y443T_mem_H hs))

theorem y443_sup_H_H' :
    y443H ⊔ y443H' = ⊤ := by
  rw [Subgroup.sup_eq_closure]
  exact y443_closure_H_H'

theorem y443_closure_H'_X' :
    Subgroup.closure ((y443H' : Set MonsterY443Derived) ∪ {y443X'}) = ⊤ := by
  rw [eq_top_iff, ← y443_closure_range_T, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  by_cases hs : s = y443E2
  · subst hs
    exact Subgroup.subset_closure (Or.inr rfl)
  · exact Subgroup.subset_closure (Or.inl (y443T_mem_H' hs))

theorem y443_closure_R_X_X' :
    Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ {y443X, y443X'}) = ⊤ := by
  rw [eq_top_iff, ← y443_closure_range_T, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  by_cases hs1 : s = y443E1
  · subst hs1
    exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · by_cases hs2 : s = y443E2
    · subst hs2
      exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
    · exact Subgroup.subset_closure (Or.inl (y443T_mem_R hs1 hs2))

theorem y443C_mem_center_of_C'_eq
    (h : y443C' = y443C) :
    y443C ∈ Subgroup.center MonsterY443Derived := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hle : (⊤ : Subgroup MonsterY443Derived) ≤ Subgroup.centralizer {y443C} := by
    rw [← y443_closure_H_H', Subgroup.closure_le]
    rintro m (hm | hm)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (y443C_comm_H hm)
    · have := y443C'_comm_H' hm
      rw [h] at this
      exact Subgroup.mem_centralizer_singleton_iff.2 this
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))

theorem y443C'_ne_C_of
    {G : Type*} [Group G] (f : MonsterY443Derived →* G) {g : G}
    (hg : g ∈ f.range) (hne : f y443C * g ≠ g * f y443C) : y443C' ≠ y443C := by
  intro h
  obtain ⟨m, rfl⟩ := hg
  have := Subgroup.mem_center_iff.1 (y443C_mem_center_of_C'_eq h) m
  exact hne (by rw [← map_mul, ← map_mul, this])

theorem y443_inf_eq_R_of_injOn {G : Type*} [Group G] (f : MonsterY443Derived →* G)
    (hinj : Set.InjOn f y443H) (hRH : y443H.map f ⊓ y443H'.map f = y443R.map f) :
    y443H ⊓ y443H' = y443R := by
  refine le_antisymm (fun m hm => ?_) y443R_le_inf
  have hfm : f m ∈ y443R.map f := hRH ▸ ⟨Subgroup.mem_map_of_mem f hm.1,
    Subgroup.mem_map_of_mem f hm.2⟩
  obtain ⟨r, hr, hrm⟩ := Subgroup.mem_map.1 hfm
  have : r = m := hinj (y443R_le_H hr) hm.1 hrm
  rw [← this]
  exact hr

theorem y443_closure_R_S_of_injOn
    {G : Type*} [Group G] (f : MonsterY443Derived →* G)
    (hinj : Set.InjOn f y443H')
    (hgen : Subgroup.closure ((f '' (y443R : Set MonsterY443Derived)) ∪ {f y443S}) =
      y443H'.map f) :
    Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ {y443S}) = y443H' := by
  have hle : Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ {y443S}) ≤ y443H' :=
    (Subgroup.closure_le _).2 (Set.union_subset y443R_le_H'
      (Set.singleton_subset_iff.2 y443S_mem_H'))
  refine le_antisymm hle fun h hh => ?_
  have hfh : f h ∈ (Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ {y443S})).map f := by
    rw [MonoidHom.map_closure, Set.image_union, Set.image_singleton, hgen]
    exact Subgroup.mem_map_of_mem f hh
  obtain ⟨n, hn, hnh⟩ := Subgroup.mem_map.1 hfh
  have : n = h := hinj (hle hn) hh hnh
  rw [← this]
  exact hn

theorem y443_closure_H_S_eq_top
    (h : Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ {y443S}) = y443H') :
    Subgroup.closure ((y443H : Set MonsterY443Derived) ∪ {y443S}) = ⊤ := by
  have hS : y443S ∈ Subgroup.closure ((y443H : Set MonsterY443Derived) ∪ {y443S}) :=
    Subgroup.subset_closure (Or.inr rfl)
  have hH' : y443H' ≤ Subgroup.closure ((y443H : Set MonsterY443Derived) ∪ {y443S}) := by
    rw [← h, Subgroup.closure_le]
    rintro m (hm | rfl)
    · exact Subgroup.subset_closure (Or.inl (y443R_le_H hm))
    · exact hS
  rw [eq_top_iff, ← y443_closure_H_H', Subgroup.closure_le]
  rintro m (hm | hm)
  · exact Subgroup.subset_closure (Or.inl hm)
  · exact hH' hm

theorem y443_second_parabolic_source :
    (y443X ∈ y443H' ∧ y443C ∈ y443H' ∧ y443Y ∈ y443H') ∧
    (y443C ∈ y443R ∧ y443C' ∈ y443R ∧ y443R ≤ y443H ⊓ y443H') ∧
    (y443S ∈ y443H' ∧ y443S * y443S = 1) ∧
    ((∃ hc : y443C ∈ y443R, (⟨y443C, hc⟩ : y443R) ∈ Subgroup.center y443R) ∧
      (∃ hc : y443C' ∈ y443R, (⟨y443C', hc⟩ : y443R) ∈ Subgroup.center y443R) ∧
      (∃ hc : y443C' ∈ y443H', (⟨y443C', hc⟩ : y443H') ∈ Subgroup.center y443H')) ∧
    (Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ (y443K : Set MonsterY443Derived)) =
        y443H ∧
      Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ (y443K' : Set MonsterY443Derived)) =
        y443H' ∧
      Subgroup.closure ((y443R : Set MonsterY443Derived) ∪ {y443X}) = y443H' ∧
      Subgroup.closure ((y443H : Set MonsterY443Derived) ∪ (y443H' : Set MonsterY443Derived)) =
        ⊤ ∧
      Subgroup.closure ((y443H' : Set MonsterY443Derived) ∪ {y443X'}) = ⊤) :=
  ⟨⟨y443X_mem_H', y443C_mem_H', y443Y_mem_H'⟩, ⟨y443C_mem_R, y443C'_mem_R, y443R_le_inf⟩,
    ⟨y443S_mem_H', y443S_mul_self⟩,
    ⟨y443C_mem_center_R, y443C'_mem_center_R, y443C'_mem_center_H'⟩,
    ⟨y443_closure_R_K, y443_closure_R_K', y443_closure_R_X, y443_closure_H_H',
      y443_closure_H'_X'⟩⟩

theorem y443H_finite_card_le_of
    (hQ : Finite Q343 ∧ Nat.card Q343 ≤ Q343N) :
    Finite y443H ∧ Nat.card y443H ≤ Q343N := by
  obtain ⟨hfin, hcard⟩ := hQ
  obtain ⟨φ, hφ, -⟩ := y443_Q343_epimorphism
  have := hfin
  exact ⟨Finite.of_surjective φ hφ, (Nat.card_le_card_of_surjective φ hφ).trans hcard⟩

theorem natCard_H'_eq_natCard_H :
    Nat.card y443H' = Nat.card y443H :=
  Nat.card_congr y443HEquivH'.symm.toEquiv

theorem y443H'_finite_card_le_of
    (hQ : Finite Q343 ∧ Nat.card Q343 ≤ Q343N) :
    Finite y443H' ∧ Nat.card y443H' ≤ Q343N := by
  obtain ⟨hfin, hcard⟩ := y443H_finite_card_le_of hQ
  have := hfin
  exact ⟨Finite.of_equiv _ y443HEquivH'.toEquiv, by rw [natCard_H'_eq_natCard_H]; exact hcard⟩

theorem y443_Q343_epimorphism' :
    ∃ φ : Q343 →* y443H', Function.Surjective φ ∧
      ∀ c : ℕ, c < 11 →
        ((φ (Q343.π (yGen 3 4 3 c)) : y443H') : MonsterY443Derived) =
          y443T (y443GenOfLetter (ρL (shiftAt 3 c))) := by
  obtain ⟨φ, hφ, hgen⟩ := y443_Q343_epimorphism
  refine ⟨y443HEquivH'.toMonoidHom.comp φ, y443HEquivH'.surjective.comp hφ, fun c hc => ?_⟩
  show ((y443HEquivH' (φ (Q343.π (yGen 3 4 3 c))) : y443H') : MonsterY443Derived) = _
  rw [y443HEquivH'_coe, hgen c hc, y443RhoM_T]
  unfold y443RhoSym
  rw [y443LetterOfGen_genOfLetter _ (by unfold shiftAt; split_ifs <;> omega)]

theorem y443R_card_le_of
    (hQ : Finite Q343 ∧ Nat.card Q343 ≤ Q343N) :
    Nat.card y443R ≤ Nat.card y443H := by
  have := (y443H_finite_card_le_of hQ).1
  exact Subgroup.card_le_of_le y443R_le_H

theorem y443_inf_card_le_of
    (hQ : Finite Q343 ∧ Nat.card Q343 ≤ Q343N) :
    Nat.card (y443H ⊓ y443H' : Subgroup MonsterY443Derived) ≤ Q343N := by
  have := (y443H_finite_card_le_of hQ).1
  exact (Subgroup.card_le_of_le inf_le_left).trans (y443H_finite_card_le_of hQ).2

end ArmSwap

end CFSG.YGroups
