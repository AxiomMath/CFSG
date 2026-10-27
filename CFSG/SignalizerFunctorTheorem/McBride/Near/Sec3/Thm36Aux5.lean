module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36Aux4
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36Aux3

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36

variable {Γ : Type u} [Group Γ]

theorem not_perfRes_le_of_chief [Finite Γ] {D A X₁ X₂ B : Subgroup Γ}
    (hc : IsChiefFactorOf (X₁ ⊔ D ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂) (hB : B ≤ X₁)
    (hBsup : B ⊔ X₂ = X₁) (hle : perfRes B ≤ X₂) : False := by
  have hn₁ : X₁ ≤ AChief.nrm X₂ := (le_sup_left.trans le_sup_left).trans hc.1.2
  have hBn : B ≤ AChief.nrm X₂ := hB.trans hn₁
  apply hns
  rw [isSolvableSection_iff hn₁]
  have hq : AChief.qimg X₂ X₁ = AChief.qimg X₂ B := by
    rw [← hBsup, SolQuot.qimg_sup hBn Subgroup.le_normalizer, SolQuot.qimg_self, sup_bot_eq]
  rw [hq, ← isSolvableSection_iff hBn]
  obtain ⟨n, hn, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := ↥B)
  refine ⟨n, ?_⟩
  rw [← hn]
  exact Subgroup.map_le_iff_le_comap.mp hle

theorem main_step
    [Finite Γ] {p n : ℕ} (ih : Thm36Below.{u} p n) {A W Y X₁ X₂ : Subgroup Γ}
    (hn : Nat.card ↥W + Nat.card ↥X₁ ≤ n)
    (h : NearAsolvAction p A W) (hY : (iPairsY A W Y).Nonempty)
    (hX₁ : IsDAIn A W X₁) (hX₂ : IsDAIn A W X₂)
    (hc : IsChiefFactorOf (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂)
    (hX₂Y : X₂ ⊓ cenIn W (A : Set Γ) ≤ Y) :
    X₁ ⊓ cenIn W (A : Set Γ) ≤ Y ∨ secCenIn (cenIn W (A : Set Γ)) X₁ X₂ = Y := by
  by_contra hfail
  obtain ⟨hfa, hfb⟩ := not_or.mp hfail
  have hDW : cenIn W (A : Set Γ) ≤ W := inf_le_left
  obtain ⟨⟨P₁, P₂⟩, hP⟩ := hY
  obtain ⟨Z₁, Z₂, -, -, hZ, hZ₂sol, -⟩ := iThm32 h hP
  have hred : ∀ Z₁ Z₂ : Subgroup Γ, (Z₁, Z₂) ∈ iPairsY A W Y →
      W = Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ) := by
    intro Z₁ Z₂ hZ
    by_contra hne
    have hW'W : Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ) ≤ W :=
      sup_le (sup_le (Thm33a.pair_le hZ) hX₁.1) hDW
    have hDW' : cenIn W (A : Set Γ) ≤ Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ) := le_sup_right
    have hAW' : Admits A (Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ)) :=
      Admits.sup (Admits.sup (Thm32.isDAIn_left_of_mem_iPairsY hZ).admits_left hX₁.admits_left)
        (Thm33a.admits_left_cenIn A W)
    have hlt : Nat.card ↥(Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ)) < Nat.card ↥W :=
      Thm211.card_lt_of_ne hW'W fun h' => hne h'.symm
    have hcen : cenIn (Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ)) (A : Set Γ) = cenIn W (A : Set Γ) :=
      Thm211.cenIn_eq_of_le hW'W hDW'
    have hnear' : NearAsolvAction p A (Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ)) :=
      Thm211.nearAsolvAction_of_le h hW'W hAW'
    have hpair' : (iPairsY A (Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ)) Y).Nonempty := by
      refine ⟨(Z₁, Z₂), ?_⟩
      rw [Thm33a.iPairsY_of_le hDW' hW'W]
      exact ⟨hZ, le_sup_left.trans le_sup_left⟩
    have hX₁W' : X₁ ≤ Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ) := le_sup_right.trans le_sup_left
    have hres := ih Γ A (Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ)) Y X₁ X₂ (by omega) hnear' hpair'
      ⟨hX₁W', by rw [hcen]; exact hX₁.2⟩
      ⟨hc.2.2.1.le.trans hX₁W', by rw [hcen]; exact hX₂.2⟩
      (by rw [hcen]; exact hc) hns (by rw [hcen]; exact hX₂Y)
    rw [hcen] at hres
    exact hfail hres
  have hW : W = Z₁ ⊔ X₁ ⊔ cenIn W (A : Set Γ) := hred Z₁ Z₂ hZ
  have key : ∀ N : Subgroup Γ, N ≤ W → Admits W N → Admits A N → N ⊓ Z₁ ≤ Z₂ → N = ⊥ := by
    intro N hNW hWN hAN hN
    by_contra hN1
    rcases quotient_step ih hn h hZ hX₁ hX₂ hc hns hX₂Y hNW hWN hAN hN hN1 with h1 | h1
    · exact hfa h1
    · exact hfb h1
  have hZ₁W : Z₁ ≤ W := Thm33a.pair_le hZ
  have hXne : W ≠ ⊥ := by
    intro h0
    have h1 : Z₁ = ⊥ := le_bot_iff.mp (h0 ▸ hZ₁W)
    have h2 : Z₂ = ⊥ := le_bot_iff.mp (h1 ▸ Thm33a.pair_le₂ hZ)
    exact (Thm33a.pair_lt hZ).ne (h2.trans h1.symm)
  have hsol : sol W = ⊥ := by
    have hHsol : Admits (Z₁ ⊔ cenIn W (A : Set Γ) ⊔ A) (sol W) :=
      sup_le (sup_le (hZ₁W.trans (Nonsolv.SolQuot.le_nrm_sol W))
        (hDW.trans (Nonsolv.SolQuot.le_nrm_sol W)))
        (h.admits.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol W))
    refine key (sol W) (sol_le W) (Nonsolv.SolQuot.le_nrm_sol W)
      (h.admits.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol W)) ?_
    exact Thm33a.le_of_solvable hZ inf_le_right (Admits.inf hHsol (Thm33a.pair_admits_H hZ))
      (Thm211.isSolvable_of_le inf_le_left (isSolvable_sol W))
  have hXK : Admits W (kOf W) := Nonsolv.le_normalizer_kOf W
  have hAK : Admits A (kOf W) := h.admits.trans (Thm211.normalizer_le_normalizer_kOf W)
  have hKZ : ¬ (kOf W ⊓ Z₁ ≤ Z₂) := fun hle =>
    Thm211.kOf_ne_bot hsol hXne (key (kOf W) (kOf_le W) hXK hAK hle)
  obtain ⟨W₀, hW₀B, hW₀perf, hW₀adm, hW₀sup, hW₀inf⟩ :=
    Thm33a.exists_perfect_sup h hsol hXne hZ hZ₂sol hKZ
  have S : TermSetting p A W Y X₁ X₂ Z₁ Z₂ W₀ :=
    ⟨h, hsol, hXne, hZ, key, hW, hX₁, hX₂, hc, hns, hX₂Y, hW₀B.trans inf_le_left, hW₀perf,
      hW₀B.trans inf_le_right, hW₀adm, hW₀sup, hW₀inf⟩
  by_cases hi : kOf W ⊓ X₁ ≤ X₂
  · exact S.false_of_inf_le hi
  · have hHK : X₁ ⊔ cenIn W (A : Set Γ) ⊔ A ≤ Subgroup.normalizer (kOf W : Set Γ) :=
      sup_le (sup_le (hX₁.1.trans hXK) (hDW.trans hXK)) hAK
    have hBadm : Admits (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) (kOf W ⊓ X₁) :=
      Admits.inf hHK hc.2.1.2
    have hBsup : (kOf W ⊓ X₁) ⊔ X₂ = X₁ :=
      (Thm33a.chief_dichotomy hc hBadm inf_le_right).resolve_left hi
    have hLB : perfRes (kOf W ⊓ X₁) ≤ kOf W ⊓ X₁ := Subgroup.map_subtype_le _
    have hLadm : Admits (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) (perfRes (kOf W ⊓ X₁)) :=
      hBadm.trans (Nonsolvable.normalizer_le_normalizer_perfectResidual_map _)
    have hLX₁ : perfRes (kOf W ⊓ X₁) ≤ X₁ := hLB.trans inf_le_right
    have hLsup : perfRes (kOf W ⊓ X₁) ⊔ X₂ = X₁ := by
      rcases Thm33a.chief_dichotomy hc hLadm hLX₁ with h1 | h1
      · exact (not_perfRes_le_of_chief hc hns inf_le_right hBsup h1).elim
      · exact h1
    by_cases hLX : perfRes (kOf W ⊓ X₁) = X₁
    · have hX₁K : X₁ ≤ kOf W := hLX ▸ (hLB.trans inf_le_left)
      have hX₁perf : Group.IsPerfect ↥X₁ :=
        hLX ▸ Nonsolvable.isPerfect_perfectResidual_map (kOf W ⊓ X₁)
      exact hfail (S.concl_of_perfect hX₁K hX₁perf)
    ·
      set L := perfRes (kOf W ⊓ X₁) with hLdef
      have hLlt : Nat.card ↥L < Nat.card ↥X₁ := Thm211.card_lt_of_ne hLX₁ hLX
      have hDAL : Admits (cenIn W (A : Set Γ) ⊔ A) L :=
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right :
          cenIn W (A : Set Γ) ⊔ A ≤ X₁ ⊔ cenIn W (A : Set Γ) ⊔ A).trans hLadm
      have hLW : L ≤ W := hLX₁.trans hX₁.1
      have hih := ih Γ A W Y L (L ⊓ X₂) (by omega) h ⟨(Z₁, Z₂), hZ⟩ ⟨hLW, hDAL⟩
        ⟨inf_le_left.trans hLW, Admits.inf hDAL hX₂.2⟩
        (isChiefFactorOf_subpair hc hLX₁ hDAL hLsup)
        (fun hs => hns (isSolvableSection_of_subpair S.X₁_nor_X₂ hLX₁ hLsup hs))
        ((inf_le_inf_right _ inf_le_right).trans hX₂Y)
      rcases hih with h1 | h1
      · apply hfa
        intro x hx
        obtain ⟨hxX, hxD⟩ := Subgroup.mem_inf.mp hx
        have hcop : Nat.Coprime p (Nat.card ↥L) :=
          h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hLW)
        obtain ⟨m, hm, r, hr, rfl⟩ := exists_mul_of_mem_sup_cen h.prime h.elemAbelian
          (le_sup_right.trans hDAL) hX₂.admits_left (hLX₁.trans S.X₁_nor_X₂) hcop
          (by rw [hLsup]; exact hxX) (Subgroup.mem_inf.mp hxD).2
        exact mul_mem (h1 ⟨hm.1, Subgroup.mem_inf.mpr ⟨hLW hm.1, hm.2⟩⟩)
          (hX₂Y ⟨hr.1, Subgroup.mem_inf.mpr ⟨hX₂.1 hr.1, hr.2⟩⟩)
      · exact hfb ((secCenIn_subpair S.D_nor_X₁ S.D_nor_X₂ (le_sup_left.trans hDAL)
          S.X₁_nor_X₂ hLX₁ hLsup).symm.trans h1)

theorem thm36_below
    (p n : ℕ) : Thm36Below.{u} p n := by
  induction n with
  | zero =>
    intro Γ _ _ A W Y X₁ X₂ hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro Γ _ _ A W Y X₁ X₂ hn h hY hX₁ hX₂ hc hns hX₂Y
    exact main_step ih (Nat.lt_succ_iff.mp hn) h hY hX₁ hX₂ hc hns hX₂Y

theorem iThm36
    [Finite Γ] {p : ℕ} {A W Y X₁ X₂ : Subgroup Γ} (h : NearAsolvAction p A W)
    (hY : (iPairsY A W Y).Nonempty) (hX₁ : IsDAIn A W X₁) (hX₂ : IsDAIn A W X₂)
    (hc : IsChiefFactorOf (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂)
    (hX₂Y : X₂ ⊓ cenIn W (A : Set Γ) ≤ Y) :
    X₁ ⊓ cenIn W (A : Set Γ) ≤ Y ∨ secCenIn (cenIn W (A : Set Γ)) X₁ X₂ = Y :=
  thm36_below p (Nat.card ↥W + Nat.card ↥X₁ + 1) Γ A W Y X₁ X₂ (Nat.lt_succ_self _) h hY hX₁ hX₂
    hc hns hX₂Y

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36
