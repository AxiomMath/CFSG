module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagPsiPol
public import CFSG.LocalAnalysis.StandardType.PhanEFlagCut

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2] {n m : ℕ} {d : List ℕ}

@[expose] noncomputable def psiSub (n : ℕ) (d : List ℕ) (pol : List Bool)
    (E : ℕ → Submodule K (Fin n → K)) (b s : ℕ) : Submodule K (Fin n → K) :=
  if pol.getD b false then
    perpB K f n (d.getD b 0) (d.getD (b + 1) 0) (E (d.getD b 0 + (blockSize d b - s))) ⊓
      Vsub n (d.getD (b + 1) 0)
  else sgS K f n (E (d.getD b 0 + s))

variable {f}

private theorem q2cFS_getD_mono {d : List ℕ} (hd : IsCut n d) (i : ℕ) :
    ∀ {j : ℕ}, i ≤ j → j ≤ d.length - 1 → d.getD i 0 ≤ d.getD j 0 := by
  have aux : ∀ k j, j = i + k → j ≤ d.length - 1 → d.getD i 0 ≤ d.getD j 0 := by
    intro k; induction k with
    | zero => intro j hj _; rw [hj, Nat.add_zero]
    | succ k ih =>
      intro j hj hjlen
      have hprev : d.getD (i + k) 0 ≤ d.getD j 0 := by
        have hstep : d.getD (i + k) 0 < d.getD (i + k + 1) 0 := hd.strict (i + k) (by omega)
        rw [show j = i + k + 1 from by omega]; exact hstep.le
      exact le_trans (ih (i + k) rfl (by omega)) hprev
  intro j hij hj
  exact aux (j - i) j (by omega) hj

private theorem q2cFS_getD_le {d : List ℕ} (hd : IsCut n d) {i : ℕ} (hi : i < d.length) :
    d.getD i 0 ≤ n := by
  have h := q2cFS_getD_mono hd i (show i ≤ d.length - 1 by omega) le_rfl
  rwa [hd.last] at h

private def q2cFS_cutBlock (d : List ℕ) (j : ℕ) : ℕ :=
  Nat.findGreatest (fun b => d.getD b 0 ≤ j) (d.length - 1)

private theorem q2cFS_cutBlock_le {d : List ℕ} (hd : IsCut n d) (j : ℕ) :
    d.getD (q2cFS_cutBlock d j) 0 ≤ j :=
  Nat.findGreatest_spec (P := fun b => d.getD b 0 ≤ j) (m := 0) (n := d.length - 1)
    (Nat.zero_le _) (by rw [hd.head]; exact Nat.zero_le j)

private theorem q2cFS_cutBlock_lt_of_lt {d : List ℕ} (hd : IsCut n d) {j : ℕ} (hj : j < n) :
    q2cFS_cutBlock d j < d.length - 1 := by
  have hle := q2cFS_cutBlock_le hd j
  have hbnd : q2cFS_cutBlock d j ≤ d.length - 1 := Nat.findGreatest_le _
  by_contra h
  rw [show q2cFS_cutBlock d j = d.length - 1 from by omega, hd.last] at hle
  omega

private theorem q2cFS_lt_cutBlock_succ {d : List ℕ} (hd : IsCut n d) {j : ℕ} (hj : j < n) :
    j < d.getD (q2cFS_cutBlock d j + 1) 0 := by
  have hb := q2cFS_cutBlock_lt_of_lt hd hj; by_contra h
  exact (Nat.findGreatest_eq_iff (P := fun b => d.getD b 0 ≤ j) (k := d.length - 1)).1 rfl
    |>.2.2 (Nat.lt_succ_self _) (Nat.succ_le_iff.mpr hb) (le_of_not_gt h)

private theorem q2cFS_cutBlock_eq_self {d : List ℕ} (hd : IsCut n d) {b j : ℕ}
    (hb : b + 1 < d.length) (h1 : d.getD b 0 ≤ j) (h2 : j < d.getD (b + 1) 0) :
    q2cFS_cutBlock d j = b := by
  refine (Nat.findGreatest_eq_iff (P := fun b => d.getD b 0 ≤ j) (k := d.length - 1)).2
    ⟨by omega, fun _ => h1, ?_⟩
  intro b' hbb' hb'k hPb'
  have hmono := q2cFS_getD_mono hd (b + 1) (show b + 1 ≤ b' by omega) hb'k
  omega

private theorem q2cFS_Vsub_le_psiSub (hd : IsCut n d) (pol : List Bool) {x : FlagK K n}
    (hx : x ∈ refSet K n d) {b s : ℕ} (hb : b + 1 < d.length) (hs : s ≤ blockSize d b) :
    Vsub n (d.getD b 0) ≤ psiSub f n d pol x.E b s := by
  have hb' : b < d.length := by omega
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := le_of_lt (hd.strict b hb)
  rw [psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp]
    exact le_inf (q2cFS_le_perpB_of_Vsub _) (Vsub_mono hle)
  · rw [if_neg hp]
    calc Vsub n (d.getD b 0) = sgS K f n (Vsub n (d.getD b 0)) := (sgS_Vsub _).symm
      _ = sgS K f n (x.E (d.getD b 0)) := by rw [hx b hb']
      _ ≤ sgS K f n (x.E (d.getD b 0 + s)) := sgS_mono (x.mono (Nat.le_add_right _ _))

private theorem q2cFS_psiSub_le_Vsub (hd : IsCut n d) (pol : List Bool) {x : FlagK K n}
    (hx : x ∈ refSet K n d) {b s : ℕ} (hb : b + 1 < d.length) (hs : s ≤ blockSize d b) :
    psiSub f n d pol x.E b s ≤ Vsub n (d.getD (b + 1) 0) := by
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := le_of_lt (hd.strict b hb)
  have hs' : d.getD b 0 + s ≤ d.getD (b + 1) 0 := by have h := hs; simp only [blockSize] at h; omega
  rw [psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp]; exact inf_le_right
  · rw [if_neg hp]
    calc sgS K f n (x.E (d.getD b 0 + s)) ≤ sgS K f n (x.E (d.getD (b + 1) 0)) :=
          sgS_mono (x.mono hs')
      _ = sgS K f n (Vsub n (d.getD (b + 1) 0)) := by rw [hx (b + 1) hb]
      _ = Vsub n (d.getD (b + 1) 0) := sgS_Vsub _

private theorem q2cFS_psiSub_zero (hd : IsCut n d) (pol : List Bool) {x : FlagK K n}
    (hx : x ∈ refSet K n d) {b : ℕ} (hb : b + 1 < d.length) :
    psiSub f n d pol x.E b 0 = Vsub n (d.getD b 0) := by
  have hb' : b < d.length := by omega
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := le_of_lt (hd.strict b hb)
  rw [psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp]
    have harg : d.getD b 0 + (blockSize d b - 0) = d.getD (b + 1) 0 := by
      simp only [blockSize]; omega
    rw [harg, hx (b + 1) hb, inf_comm, q2cFS_perpB_Vsub_inf hle]
  · rw [if_neg hp, Nat.add_zero, hx b hb', sgS_Vsub]

private theorem q2cFS_psiSub_last (hd : IsCut n d) (pol : List Bool) {x : FlagK K n}
    (hx : x ∈ refSet K n d) {b : ℕ} (hb : b + 1 < d.length) :
    psiSub f n d pol x.E b (blockSize d b) = Vsub n (d.getD (b + 1) 0) := by
  have hb' : b < d.length := by omega
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := le_of_lt (hd.strict b hb)
  rw [psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp, Nat.sub_self]
    change perpB K f n (d.getD b 0) (d.getD (b + 1) 0) (x.E (d.getD b 0)) ⊓
      Vsub n (d.getD (b + 1) 0) = Vsub n (d.getD (b + 1) 0)
    rw [hx b hb', q2cFS_perpB_Vsub_lo_eq_top, top_inf_eq]
  · rw [if_neg hp]
    have harg : d.getD b 0 + blockSize d b = d.getD (b + 1) 0 := by
      simp only [blockSize]; omega
    rw [harg, hx (b + 1) hb, sgS_Vsub]

private theorem q2cFS_finrank_psiSub (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d)
    (pol : List Bool) {x : FlagK K n} (hx : x ∈ refSet K n d) {b s : ℕ}
    (hb : b + 1 < d.length) (hs : s ≤ blockSize d b) :
    finrank K (psiSub f n d pol x.E b s) = d.getD b 0 + s := by
  have hb' : b < d.length := by omega
  have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := le_of_lt (hd.strict b hb)
  have hbn : d.getD (b + 1) 0 ≤ n := q2cFS_getD_le hd hb
  rw [psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp]
    have hlo : Vsub n (d.getD b 0) ≤ x.E (d.getD b 0 + (blockSize d b - s)) :=
      le_trans (hx b hb').ge (x.mono (Nat.le_add_right _ _))
    have hhi : x.E (d.getD b 0 + (blockSize d b - s)) ≤ Vsub n (d.getD (b + 1) 0) :=
      le_trans (x.mono (by simp only [blockSize]; omega)) (hx (b + 1) hb).le
    rw [q2cFS_finrank_perpB_inf_Vsub (hK := hK) (lo := d.getD b 0) (hi := d.getD (b + 1) 0)
        hle hbn hlo hhi,
      x.dim (d.getD b 0 + (blockSize d b - s)) (by simp only [blockSize]; omega)]
    have h := hs; simp only [blockSize] at h ⊢; omega
  · rw [if_neg hp, finrank_sgS hK,
      x.dim (d.getD b 0 + s) (by have h := hs; simp only [blockSize] at h; omega)]

private theorem q2cFS_psiSub_mono (hd : IsCut n d) (pol : List Bool) {x : FlagK K n}
    (hx : x ∈ refSet K n d) {b s s' : ℕ} (hss' : s ≤ s') (hs' : s' ≤ blockSize d b) :
    psiSub f n d pol x.E b s ≤ psiSub f n d pol x.E b s' := by
  rw [psiSub, psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp, if_pos hp]
    exact inf_le_inf (q2cFS_perpB_antitone (x.mono (show d.getD b 0 + (blockSize d b - s') ≤
      d.getD b 0 + (blockSize d b - s) by omega))) (le_refl _)
  · rw [if_neg hp, if_neg hp]
    exact sgS_mono (x.mono (by omega))

theorem exists_flagPsi (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d) (pol : List Bool)
    {x : FlagK K n} (hx : x ∈ refSet K n d) :
    ∃ y : FlagK K n, y ∈ refSet K n d ∧ ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      y.E (d.getD b 0 + s) = psiSub f n d pol x.E b s := by
  let yE : ℕ → Submodule K (Fin n → K) := fun j =>
    if j < n then psiSub f n d pol x.E (q2cFS_cutBlock d j)
      (j - d.getD (q2cFS_cutBlock d j) 0) else Vsub n n
  have hyE : ∀ j, yE j = if j < n then psiSub f n d pol x.E (q2cFS_cutBlock d j)
      (j - d.getD (q2cFS_cutBlock d j) 0) else Vsub n n := fun _ => rfl
  have hyE_cut : ∀ i, i < d.length → yE (d.getD i 0) = Vsub n (d.getD i 0) := by
    intro i hi
    by_cases hin : d.getD i 0 < n
    · have hi1 : i + 1 < d.length := by
        by_contra h
        rw [show i = d.length - 1 from by omega, hd.last] at hin
        omega
      rw [hyE, if_pos hin, q2cFS_cutBlock_eq_self hd hi1 le_rfl (hd.strict i hi1),
        Nat.sub_self, q2cFS_psiSub_zero hd pol hx hi1]
    · rw [show d.getD i 0 = n from by have := q2cFS_getD_le hd hi; omega, hyE,
        if_neg (by omega : ¬ n < n)]
  have hmain : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      yE (d.getD b 0 + s) = psiSub f n d pol x.E b s := by
    intro b s hb hs
    have hb' : b < d.length := by omega
    have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := le_of_lt (hd.strict b hb)
    have hbn : d.getD (b + 1) 0 ≤ n := q2cFS_getD_le hd hb
    by_cases hsm : s = blockSize d b
    · subst hsm
      rw [show d.getD b 0 + blockSize d b = d.getD (b + 1) 0 by
        simp only [blockSize]; omega,
        hyE_cut (b + 1) hb, q2cFS_psiSub_last hd pol hx hb]
    · have hslt : s < blockSize d b := lt_of_le_of_ne hs hsm
      have hjn : d.getD b 0 + s < n := by
        have := hbn; simp only [blockSize] at hslt; omega
      rw [hyE, if_pos hjn,
        q2cFS_cutBlock_eq_self hd hb (j := d.getD b 0 + s) (Nat.le_add_right _ _)
          (by have h := hslt; simp only [blockSize] at h; omega),
        show d.getD b 0 + s - d.getD b 0 = s by omega]
  have hmono : Monotone yE := by
    refine monotone_nat_of_le_succ fun j => ?_
    by_cases hjn : j + 1 < n
    · have hj : j < n := by omega
      rw [hyE, hyE, if_pos hj, if_pos hjn]
      by_cases heq : q2cFS_cutBlock d j = q2cFS_cutBlock d (j + 1)
      · rw [heq]
        have hb1 : q2cFS_cutBlock d (j + 1) + 1 < d.length := by
          have := q2cFS_cutBlock_lt_of_lt hd hjn; omega
        have hlt := q2cFS_lt_cutBlock_succ hd hjn
        have hcle := q2cFS_cutBlock_le hd (j + 1)
        exact q2cFS_psiSub_mono hd pol hx (by omega) (by simp only [blockSize] at hlt ⊢; omega)
      · have hbb' : q2cFS_cutBlock d j ≤ q2cFS_cutBlock d (j + 1) :=
          Nat.le_findGreatest (Nat.findGreatest_le _)
            (le_trans (q2cFS_cutBlock_le hd j) (Nat.le_succ j))
        have hlt : q2cFS_cutBlock d j < q2cFS_cutBlock d (j + 1) := lt_of_le_of_ne hbb' heq
        have hb1 : q2cFS_cutBlock d j + 1 < d.length := by
          have := q2cFS_cutBlock_lt_of_lt hd hj; omega
        have hb2 : q2cFS_cutBlock d (j + 1) + 1 < d.length := by
          have := q2cFS_cutBlock_lt_of_lt hd hjn; omega
        have hcle1 := q2cFS_cutBlock_le hd j
        have hlt1 := q2cFS_lt_cutBlock_succ hd hj
        have hcle2 := q2cFS_cutBlock_le hd (j + 1)
        have hlt2 := q2cFS_lt_cutBlock_succ hd hjn
        refine le_trans (q2cFS_psiSub_le_Vsub hd pol hx hb1 (by
            simp only [blockSize]; omega))
          (le_trans (Vsub_mono (q2cFS_getD_mono hd (q2cFS_cutBlock d j + 1)
              (show q2cFS_cutBlock d j + 1 ≤ q2cFS_cutBlock d (j + 1) by omega)
              (Nat.findGreatest_le _)))
            (q2cFS_Vsub_le_psiSub hd pol hx hb2 (by simp only [blockSize]; omega)))
    · have htop : yE (j + 1) = ⊤ := by
        rw [hyE, if_neg (by omega : ¬ j + 1 < n), Vsub_self]
      rw [htop]
      exact le_top
  have hdim : ∀ j, j ≤ n → finrank K (yE j) = j := by
    intro j hj
    by_cases hjn : j < n
    · rw [hyE, if_pos hjn]
      have hb : q2cFS_cutBlock d j + 1 < d.length := by
        have := q2cFS_cutBlock_lt_of_lt hd hjn; omega
      have hcle := q2cFS_cutBlock_le hd j
      have hlt := q2cFS_lt_cutBlock_succ hd hjn
      rw [q2cFS_finrank_psiSub hK hd pol hx hb (by simp only [blockSize]; omega)]
      omega
    · rw [hyE, if_neg hjn, show j = n from by omega, finrank_Vsub le_rfl]
  refine ⟨⟨yE, hmono, hdim, fun j hj => by
    rw [hyE, if_neg (by omega : ¬ j < n), Vsub_self]⟩, ?_, hmain⟩
  exact hyE_cut

@[expose] noncomputable def flagPsi (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d)
    (pol : List Bool) (x : FlagK K n) : FlagK K n :=
  open Classical in
  if h : x ∈ refSet K n d then Classical.choose (exists_flagPsi hK hd pol h) else x

theorem flagPsi_mem (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d) (pol : List Bool)
    {x : FlagK K n} (hx : x ∈ refSet K n d) : flagPsi hK hd pol x ∈ refSet K n d := by
  rw [flagPsi, dif_pos hx]
  exact (Classical.choose_spec (exists_flagPsi hK hd pol hx)).1

theorem flagPsi_E (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d) (pol : List Bool)
    {x : FlagK K n} (hx : x ∈ refSet K n d) {b s : ℕ} (hb : b + 1 < d.length)
    (hs : s ≤ blockSize d b) :
    (flagPsi hK hd pol x).E (d.getD b 0 + s) = psiSub f n d pol x.E b s := by
  rw [flagPsi, dif_pos hx]
  exact (Classical.choose_spec (exists_flagPsi hK hd pol hx)).2 b s hb hs

@[expose] noncomputable def flagPsi' (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (n : ℕ) (d : List ℕ) (pol : List Bool) (x : FlagK K n) :
    FlagK K n :=
  open Classical in
  if hd : IsCut n d then flagPsi hK hd pol x else x

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
