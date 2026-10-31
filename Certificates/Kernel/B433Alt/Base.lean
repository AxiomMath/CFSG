module

public import CFSG.Certificates.Kernel.B433Alt.Sound
public import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Kernel.B433Alt.Md.L
public import Certificates.Kernel.B433Alt.Md.P0
public import Certificates.Kernel.B433Alt.Md.P1
public import Certificates.Kernel.B433Alt.Ch.E0
public import Certificates.Kernel.B433Alt.Ch.E1
public import Certificates.Kernel.B433Alt.Ch.O0
public import Certificates.Kernel.B433Alt.Ch.O1
public import Certificates.Kernel.B433Alt.Ch.O2
public import Certificates.Kernel.B433Alt.Ch.O3
public import Certificates.Kernel.B433Alt.Ch.O4
public import Certificates.Kernel.B433Alt.Ch.O5
public import Certificates.Kernel.B433Alt.Ch.O6
public import Certificates.Kernel.B433Alt.Ch.O7
public import Certificates.Kernel.Y442.Model
public import CFSG.YGroups.Y442Twist.Model
public import CFSG.Certificates.Kernel.B433Alt.StLen

set_option maxRecDepth 100000

@[expose] public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration

#kc_forall_tree let_all (fun k => CFSG.KD.B4A.letChk k = true) 320 CFSG.KD.B4A.lt
#kc_forall_tree pair_all (fun k => CFSG.KD.B4A.pairChk k = true) 800 CFSG.KD.B4A.pair
#kc_forall_tree el_all (fun e => CFSG.KD.B4AC.elChk e = true) 2150 CFSG.KD.B4AC.el
#kc_forall_tree orb_all (fun k => CFSG.KD.B4AC.orbChk k = true) 824 CFSG.KD.B4AC.orb

theorem sB_eq (v : ℕ) (k : ℕ → Bool) : sB v k = k v := by cases v <;> rfl

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem ptsOK_spec {f : ℕ → Bool} {a : ℕ} : ∀ {n : ℕ}, CFSG.KD.B4A.ptsOK f a n = true →
    ∀ i < n, a + i < 31671 → f (a + i) = true
  | 0, _, i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi, hlt => by
    change andB (CFSG.KD.B4A.ptsOK f a n) (Bool.rec (motive := fun _ => Bool) true (f (Nat.add a n))
      (Nat.blt (Nat.add a n) 31671)) = true at h
    rw [andB_iff] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ptsOK_spec h.1 i hi hlt
    · have hb : Nat.blt (Nat.add a i) 31671 = true := by rw [Nat.blt_eq]; exact hlt
      rw [hb] at h
      exact h.2

section

theorem tables : Tables rho432F CFSG.KD.B4A.LP where
  letter c hc x := by
    have hx := x.2
    have hk : 32 * c + (x : ℕ) / 1000 < 320 := by omega
    have h := let_all (32 * c + x / 1000) hk
    unfold CFSG.KD.B4A.letChk at h
    rw [sB_eq, sB_eq, andB_iff] at h
    have hd : Nat.div (32 * c + x / 1000) 32 = c := by
      change (32 * c + (x : ℕ) / 1000) / 32 = c
      omega
    have hm : Nat.mod (32 * c + x / 1000) 32 = x / 1000 := by
      change (32 * c + (x : ℕ) / 1000) % 32 = x / 1000
      omega
    rw [hd, hm] at h
    have h2 := ptsOK_spec h.2 (x % 1000) (Nat.mod_lt _ (by norm_num))
      (by change 1000 * ((x : ℕ) / 1000) + x % 1000 < 31671; omega)
    have e : Nat.mul 1000 ((x : ℕ) / 1000) + x % 1000 = x := by
      change 1000 * ((x : ℕ) / 1000) + x % 1000 = x
      omega
    rw [e] at h2
    rw [CertificateChecks.KernelY442.rho_yGen_apply hc]
    exact (Nat.eq_of_beq_eq_true h2).symm
  pair p hp q hq x hx := by
    have hk : 8 * (10 * p + q) + x / 4000 < 800 := by omega
    have h := pair_all (8 * (10 * p + q) + x / 4000) hk
    unfold CFSG.KD.B4A.pairChk at h
    rw [sB_eq, sB_eq, sB_eq, sB_eq, andB_iff] at h
    have hd : Nat.div (8 * (10 * p + q) + x / 4000) 8 = 10 * p + q := by
      change (8 * (10 * p + q) + x / 4000) / 8 = 10 * p + q
      omega
    have hm : Nat.mod (8 * (10 * p + q) + x / 4000) 8 = x / 4000 := by
      change (8 * (10 * p + q) + x / 4000) % 8 = x / 4000
      omega
    have hp' : Nat.div (10 * p + q) 10 = p := by
      change (10 * p + q) / 10 = p
      omega
    have hq' : Nat.mod (10 * p + q) 10 = q := by
      change (10 * p + q) % 10 = q
      omega
    rw [hd, hm, hp', hq'] at h
    have h2 := ptsOK_spec h.2 (x % 4000) (Nat.mod_lt _ (by norm_num))
      (by change 4000 * (x / 4000) + x % 4000 < 31671; omega)
    have e : Nat.mul 4000 (x / 4000) + x % 4000 = x := by
      change 4000 * (x / 4000) + x % 4000 = x
      omega
    rw [e] at h2
    exact Nat.eq_of_beq_eq_true h2

end

theorem land_land (i m : ℕ) : Nat.land (Nat.land i m) m = Nat.land i m := by
  change (i &&& m) &&& m = i &&& m
  rw [Nat.and_assoc, Nat.and_self]

theorem mod_4096 (e : ℕ) : e % 4096 = Nat.land e 4095 := (Nat.and_two_pow_sub_one_eq_mod e 12).symm
theorem mod_8192 (e : ℕ) : e % 8192 = Nat.land e 8191 := (Nat.and_two_pow_sub_one_eq_mod e 13).symm

theorem EL_per (e : ℕ) : CFSG.KD.B4AC.EL e = CFSG.KD.B4AC.EL (e % 4096) := by
  rw [mod_4096]
  delta CFSG.KD.B4AC.EL
  dsimp only
  rw [land_land]

theorem EW_per (e : ℕ) : CFSG.KD.B4AC.EW e = CFSG.KD.B4AC.EW (e % 4096) := by
  rw [mod_4096]
  delta CFSG.KD.B4AC.EW
  dsimp only
  rw [land_land]

theorem RD_per (g : ℕ) : CFSG.KD.B4A.RD g = CFSG.KD.B4A.RD (g % 8192) := by
  rw [mod_8192]
  delta CFSG.KD.B4A.RD
  dsimp only
  rw [land_land]

theorem RW_per (g : ℕ) : CFSG.KD.B4A.RW g = CFSG.KD.B4A.RW (g % 8192) := by
  rw [mod_8192]
  delta CFSG.KD.B4A.RW
  dsimp only
  rw [land_land]

theorem EL_zero : ∀ e < 4096, 2150 ≤ e → CFSG.KD.B4AC.EL e = 0 := by decide +kernel

theorem RD_tail : ∀ g < 8192, 5965 ≤ g → CFSG.KD.B4A.RD g = 0 := by decide +kernel

theorem rw_stab_lt : ∀ g < 5965, isStab (dKind (CFSG.KD.B4A.RD g)) = true →
    wInH (CFSG.KD.B4A.RW g) = true := by decide +kernel

theorem rw_stab (g : ℕ) (h : isStab (dKind (CFSG.KD.B4A.RD g)) = true) :
    wInH (CFSG.KD.B4A.RW g) = true := by
  rw [RD_per] at h
  rw [RW_per]
  have hg : g % 8192 < 8192 := Nat.mod_lt _ (by norm_num)
  by_cases h5 : g % 8192 < 5965
  · exact rw_stab_lt _ h5 h
  · rw [RD_tail _ hg (by omega)] at h
    exact absurd h (by decide)

theorem rw_len_lt : ∀ g < 8192, wLen (CFSG.KD.B4A.RW g) < 2 ^ 16 := by decide +kernel

theorem rw_len (g : ℕ) : wLen (CFSG.KD.B4A.RW g) < 2 ^ 16 := by
  rw [RW_per]
  exact rw_len_lt _ (Nat.mod_lt _ (by norm_num))

theorem ew_len_lt : ∀ e < 4096, wLen (CFSG.KD.B4AC.EW e) < 2 ^ 16 := by decide +kernel

theorem ew_len (e : ℕ) : wLen (CFSG.KD.B4AC.EW e) < 2 ^ 16 := by
  rw [EW_per]
  exact ew_len_lt _ (Nat.mod_lt _ (by norm_num))

theorem cbOf_eq (b : ℕ → ℕ) : ∀ k, CFSG.KD.B4AC.cbOf b k = cbOf' b k
  | 0 => rfl
  | k + 1 => by
    change CFSG.KD.B4AC.cbOf b k ||| _ = cbOf' b k ||| _
    rw [cbOf_eq b k]

theorem elOK_per {CB : ℕ} (e : ℕ) :
    elOK CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4AC.EL CFSG.KD.B4AC.EW CB e =
      elOK CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4AC.EL CFSG.KD.B4AC.EW CB
        (e % 4096) := by
  unfold elOK
  rw [EL_per e, EW_per e]

theorem el_ok (e : ℕ) (he : CFSG.KD.B4AC.EL e ≠ 0) :
    elOK CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4AC.EL CFSG.KD.B4AC.EW
      (cbOf' (fun l => CFSG.KD.B4AC.LB (16 * elJ (CFSG.KD.B4AC.EL e) + l)) (elL (CFSG.KD.B4AC.EL e)))
      e = true := by
  rw [elOK_per, EL_per e]
  rw [EL_per e] at he
  have hlt : e % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
  by_cases h : e % 4096 < 2150
  · have := el_all _ h
    unfold CFSG.KD.B4AC.elChk CFSG.KD.B4AC.baseOf at this
    rw [sB_eq, cbOf_eq] at this
    exact this
  · exact absurd (EL_zero _ hlt (by omega)) he

open CFSG.KD.B4AC in
theorem lev0_tab : ∀ l < 5,
    (∀ k < LN l, 0 < genW CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW 0 l (LG l) (LN l) k) ∧
    (∀ i < LK l, CL (LC l + i) = l) ∧ LC l + LK l ≤ 824 ∧
    ((0 < LK l → CS (LC l) = orbInit (LB l)) ∧ ∀ i < LK l - 1, CS (LC l + i + 1) = CT (LC l + i)) ∧
    orbCount (if LK l = 0 then orbInit (LB l) else CT (LC l + LK l - 1)) = LO l ∧
    LB l = b5 l := by
  decide +kernel

open CFSG.KD.B4AC in
theorem lev0_prod : ∏ l ∈ Finset.range 5, LO l = 4089470473293004800 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  decide +kernel

theorem shiftRight_four {l : ℕ} (hl : l < 16) : Nat.shiftRight l 4 = 0 := by
  change l >>> 4 = 0
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem land_fifteen {l : ℕ} (hl : l < 16) : Nat.land l 15 = l := by
  change l &&& 15 = l
  have e : (15 : ℕ) = 2 ^ 4 - 1 := by norm_num
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  omega

open CFSG.KD.B4AC in
theorem orb0 {l i : ℕ} (hl : l < 5) (hi : i < LK l) :
    orbRun CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW 0 l (LG l) (LN l) (CN (LC l + i))
      (CR (LC l + i)) (CS (LC l + i)) = CT (LC l + i) := by
  obtain ⟨-, hcl, hb, -⟩ := lev0_tab l hl
  have hk : LC l + i < 824 := by omega
  have h := orb_all (LC l + i) hk
  unfold orbChk at h
  rw [sB_eq, hcl i hi, shiftRight_four (by omega), land_fifteen (by omega)] at h
  exact Nat.eq_of_beq_eq_true h

section

noncomputable def β5 (m : ℕ) : Fin 31671 :=
  if h : m < 5 then ⟨b5 m, b5_lt m h⟩ else 0

theorem cbOf'_congr {b b' : ℕ → ℕ} : ∀ k, (∀ m < k, b m = b' m) → cbOf' b k = cbOf' b' k
  | 0, _ => rfl
  | k + 1, h => by
    change cbOf' b k ||| _ = cbOf' b' k ||| _
    rw [cbOf'_congr k (fun m hm => h m (by omega)), h k (by omega)]

open CFSG.KD.B4AC in
noncomputable def gen0 (l k : ℕ) : ℕ :=
  genWord CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW 0 l (LG l) (LN l) k

open CFSG.KD.B4AC in
theorem lev0 {l : ℕ} (hl : l < 5) :
    (∀ k < LN l, wInH (gen0 l k) = true ∧
      ∀ m (hm : m < l), (rho432F (wVal (yGen 4 3 2) (gen0 l k)) ⟨b5 m, b5_lt m (by omega)⟩ : ℕ) =
        b5 m) ∧
    LO l ≤ (MulAction.orbit (Subgroup.closure ((fun k => rho432F (wVal (yGen 4 3 2) (gen0 l k))) ''
      {k | k < LN l})) (⟨b5 l, b5_lt l hl⟩ : Fin 31671)).ncard := by
  obtain ⟨hgen, -, -, hrun, hcnt, -⟩ := lev0_tab l hl
  have hlb : ∀ m < 5, LB m = b5 m := fun m hm => (lev0_tab m hm).2.2.2.2.2
  exact level_sound (ρ := rho432F) (j := 0) (l := l) (G := LG l) (nG := LN l)
    (bs := b5) (CN := CN) (CR := CR) (CS := CS) (CT := CT)
    (k₀ := LC l) (n := LK l) (o := LO l) tables (b5_lt l hl) rw_stab
    (fun e hj hl' hl0 => by
      have he : EL e ≠ 0 := fun h0 => by
        rw [h0] at hl'
        exact hl0 hl'.symm
      have hc : cbOf' (fun l' => LB (16 * 0 + l')) l = cbOf' b5 l :=
        cbOf'_congr l (fun m hm => by
          rw [Nat.mul_zero, Nat.zero_add]
          exact hlb m (by omega))
      have := el_ok e he
      rw [hj, hl', hc] at this
      exact this)
    hgen (fun i hi => orb0 hl hi) (by rw [← hlb l hl]; exact hrun)
    (by rw [← hlb l hl]; exact hcnt) (fun m hm => b5_lt m (by omega))

theorem base_eq_one {g : Equiv.Perm (Fin 31671)} (hg : g ∈ rho432F.range)
    (hfix : ∀ m < 5, g (β5 m) = β5 m) : g = 1 := by
  have hβ : ∀ m (hm : m < 5), β5 m = ⟨b5 m, b5_lt m hm⟩ := fun m hm => by
    rw [β5, dif_pos hm]
  refine CFSG.YGroups.Y442Tw.eq_one_of_chain rho432F.range 5 β5
    (fun l => (fun k => rho432F (wVal (yGen 4 3 2) (gen0 l k))) '' {k | k < CFSG.KD.B4AC.LN l})
    (fun l _ => by rintro _ ⟨k, -, rfl⟩; exact ⟨_, rfl⟩) ?_ CFSG.KD.B4AC.LO ?_ ?_ hg hfix
  · rintro l hl _ ⟨k, hk, rfl⟩ m hm
    rw [hβ m (by omega)]
    exact Fin.ext ((lev0 hl).1 k hk |>.2 m hm)
  · intro l hl
    rw [hβ l hl]
    exact (lev0 hl).2
  · rw [card_range_rho432F, lev0_prod]

theorem isOne_rho {w : ℕ} (hw : wInH w = true) (h : isOne CFSG.KD.B4A.LP w = true) :
    rho432F (wVal (yGen 4 3 2) w) = 1 := by
  refine base_eq_one ⟨_, rfl⟩ fun m hm => ?_
  rw [β5, dif_pos hm]
  exact Fin.ext (isOne_spec tables hw h m hm)

end

end CertificateChecks.KernelB433

end
