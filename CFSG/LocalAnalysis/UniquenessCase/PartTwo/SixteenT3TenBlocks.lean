module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenBlocksA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenBlocksB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16t_ten_blocks {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    {X A L : Subgroup (MulAut T)} {g : MulAut T} {p : ℕ} (hp : p = 3 ∨ p = 7)
    (hA : IsElemAbelianOfRank p 3 ↥A) (hAn : ∀ m ∈ X, ∀ a ∈ A, m * a * m⁻¹ ∈ A)
    (hLA : L ≤ A) (hLp : Nat.card ↥L = p) (hrk : rk ↥(commSub ⊤ L) = 2 * dParam p)
    (h2 : S16n9bTwo X L g) :
    ∃ Y : Fin 4 → Subgroup T, S16tTenBlocks X A Y p := by
  classical
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have hoddp : Odd p := by rcases hp with rfl | rfl <;> decide
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (s16t_blk_comm_of_isElemAbelianOfRank hA ⟨a, ha⟩ ⟨b, hb⟩)
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with
    mul_comm := fun x y => Subtype.ext (hAc x x.2 y y.2) }
  have hAp : ∀ a ∈ A, a ^ p = 1 := fun a ha => by
    simpa using congrArg Subtype.val (s16t_blk_pow_of_isElemAbelianOfRank hA ⟨a, ha⟩)
  have hAcard : Nat.card ↥A = p ^ 3 := s16t_blk_card_of_isElemAbelianOfRank hA
  have hAn_map : ∀ m ∈ X, A.map (MulAut.conj m).toMonoidHom = A := by
    intro m hm
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hAn m hm a ha
    · intro a ha
      refine Subgroup.mem_map.2 ⟨m⁻¹ * a * m, hAn m⁻¹ (X.inv_mem hm) a ha, ?_⟩
      simp [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc]
  set Lg : Subgroup (MulAut T) := L.map (MulAut.conj g).toMonoidHom with hLgdef
  set W : Subgroup T := commSub ⊤ L with hWdef
  set Wg : Subgroup T := W.map g.toMonoidHom with hWgdef
  have hLgA : Lg ≤ A := by
    rw [hLgdef, ← hAn_map g h2.mem]
    exact Subgroup.map_mono hLA
  have hLgcard : Nat.card ↥Lg = p := by
    rw [hLgdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hLp]
  have hcommLg : commSub ⊤ Lg = Wg := by
    rw [hLgdef, hWgdef]
    exact s15_Infra_commSub_top_map_conj L g
  have hWinfWg : W ⊓ Wg = ⊥ := by
    have h := h2.inf
    rw [hWdef.symm, ← hWgdef] at h
    exact h
  have hWsupWg : W ⊔ Wg = ⊤ := by
    have h := h2.sup
    rw [hWdef.symm, ← hWgdef] at h
    exact h
  have hdpos : 0 < dParam p := dParam_pos hpp hp2
  have hrkW : rk ↥W = 2 * dParam p := by rw [hWdef]; exact hrk
  have hW_ne_bot : W ≠ ⊥ := by
    intro hbot
    rw [hbot, rk_bot] at hrkW
    omega
  have hLg_ne_L : Lg ≠ L := by
    intro hEq
    have hWeq : Wg = W := by rw [← hcommLg, hEq, hWdef]
    have hbot : W = ⊥ := by
      have h := hWinfWg
      rw [hWeq] at h
      simpa using h
    exact hW_ne_bot hbot
  have hoddL : Odd (Nat.card ↥L) := by rw [hLp]; exact hoddp
  have hoddLg : Odd (Nat.card ↥Lg) := by rw [hLgcard]; exact hoddp
  have hW_le_fixV_Lg : W ≤ fixV Lg := by
    intro w hw b hb
    rw [hLgdef] at hb
    rw [hWdef] at hw
    exact h2.fixB b hb w hw
  have hWg_le_fixV_L : Wg ≤ fixV L := by
    intro w hw a ha
    rw [hWgdef] at hw
    exact h2.fixA a ha w hw
  have hWg_inf_fixV_Lg : Wg ⊓ fixV Lg = ⊥ := by
    have h := (coprime_decomp (P := Lg) hoddLg hT (W := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _)).2
    rw [top_inf_eq] at h
    rwa [hcommLg] at h
  have hW_inf_fixV_L : W ⊓ fixV L = ⊥ := by
    have h := (coprime_decomp (P := L) hoddL hT (W := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _)).2
    rw [top_inf_eq] at h
    rwa [show commSub ⊤ L = W from hWdef] at h
  have hfixV_Lg : fixV Lg = W := by
    apply le_antisymm
    · intro v hv
      have hvsup : v ∈ W ⊔ Wg := by rw [hWsupWg]; exact Subgroup.mem_top v
      obtain ⟨w, hw, w', hw', hww'⟩ := Subgroup.mem_sup.1 hvsup
      have hwfix : w ∈ fixV Lg := hW_le_fixV_Lg hw
      have hw'fix : w' ∈ fixV Lg := by
        have hw'eq : w' = w⁻¹ * v := by rw [← hww']; group
        rw [hw'eq]
        exact (fixV Lg).mul_mem ((fixV Lg).inv_mem hwfix) hv
      have hw'in : w' ∈ Wg ⊓ fixV Lg := ⟨hw', hw'fix⟩
      rw [hWg_inf_fixV_Lg] at hw'in
      have hw'one : w' = 1 := Subgroup.mem_bot.1 hw'in
      have hveq : v = w := by rw [← hww', hw'one, mul_one]
      rw [hveq]
      exact hw
    · exact hW_le_fixV_Lg
  have hfixV_L : fixV L = Wg := by
    apply le_antisymm
    · intro v hv
      have hvsup : v ∈ W ⊔ Wg := by rw [hWsupWg]; exact Subgroup.mem_top v
      obtain ⟨w, hw, w', hw', hww'⟩ := Subgroup.mem_sup.1 hvsup
      have hw'fix : w' ∈ fixV L := hWg_le_fixV_L hw'
      have hwfix : w ∈ fixV L := by
        have hweq : w = v * w'⁻¹ := by rw [← hww']; group
        rw [hweq]
        exact (fixV L).mul_mem hv ((fixV L).inv_mem hw'fix)
      have hwin : w ∈ W ⊓ fixV L := ⟨hw, hwfix⟩
      rw [hW_inf_fixV_L] at hwin
      have hwone : w = 1 := Subgroup.mem_bot.1 hwin
      have hveq : v = w' := by rw [← hww', hwone, one_mul]
      rw [hveq]
      exact hw'
    · exact hWg_le_fixV_L
  have hfixA : fixV A = ⊥ := by
    apply le_bot_iff.1
    intro v hv
    have hvL : v ∈ fixV L := s16t_blk_fixV_anti hLA hv
    have hvLg : v ∈ fixV Lg := s16t_blk_fixV_anti hLgA hv
    rw [hfixV_L] at hvL
    rw [hfixV_Lg] at hvLg
    have hvin : v ∈ W ⊓ Wg := ⟨hvLg, hvL⟩
    rwa [hWinfWg] at hvin
  have hHB := s16t_blk_hyperplane_blocks hT hp2 hAc hAp hfixA
  let Idx := s16t_blk_Hyp A p
  let Yb : Idx → Subgroup T := fun B => fixV (B : Subgroup (MulAut T))
  have hind : iSupIndep Yb := hHB.1
  have hsup_all : (⨆ B : Idx, Yb B) = ⊤ := hHB.2
  haveI : Fintype Idx := Fintype.ofFinite Idx
  have hBspec : ∀ B : Idx, (B : Subgroup (MulAut T)) ≤ A ∧
      Nat.card ↥(B : Subgroup (MulAut T)) * p = Nat.card ↥A ∧
      fixV (B : Subgroup (MulAut T)) ≠ ⊥ := fun B => by
    simpa only [Idx, s16t_blk_Hyp, Set.mem_setOf_eq] using B.2
  have hBcard : ∀ B : Idx, Nat.card ↥(B : Subgroup (MulAut T)) = p ^ 2 := by
    intro B
    have h1 : Nat.card ↥(B : Subgroup (MulAut T)) * p = p ^ 3 := by
      rw [← hAcard]; exact (hBspec B).2.1
    refine Nat.eq_of_mul_eq_mul_right hpp.pos ?_
    rw [h1]
    ring
  have hdvd : ∀ B : Idx, dParam p ∣ rk ↥(Yb B) := by
    intro B
    simpa [dParam] using s16t_blk_dvd_rk_fixV hT hAc hAp hfixA (hBspec B).1 hAcard (hBcard B)
  have hrk_ge : ∀ B : Idx, dParam p ≤ rk ↥(Yb B) := by
    intro B
    obtain ⟨k, hk⟩ := hdvd B
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exfalso
        rw [hk0, mul_zero] at hk
        exact (hBspec B).2.2 ((rk_eq_zero_iff hT).1 hk)
      · exact hkpos
    rw [hk]
    exact Nat.le_mul_of_pos_right (dParam p) hkpos
  let P₁ : Idx → Prop := fun B => Lg ≤ (B : Subgroup (MulAut T))
  let P₂ : Idx → Prop := fun B => L ≤ (B : Subgroup (MulAut T))
  have hdich : ∀ B : Idx, (P₁ B ∧ ¬ P₂ B) ∨ (P₂ B ∧ ¬ P₁ B) := by
    intro B
    have hnotboth : ¬ (P₁ B ∧ P₂ B) := by
      rintro ⟨h1, h2b⟩
      have hleW : Yb B ≤ W := by
        rw [← hfixV_Lg]; exact s16t_blk_fixV_anti h1
      have hleWg : Yb B ≤ Wg := by
        rw [← hfixV_L]; exact s16t_blk_fixV_anti h2b
      exact (hBspec B).2.2 (eq_bot_iff.2 ((le_inf hleW hleWg).trans (le_of_eq hWinfWg)))
    have hexh : P₁ B ∨ P₂ B := by
      by_contra h
      obtain ⟨hnp1, hnp2⟩ := not_or.mp h
      have hBL_bot : (B : Subgroup (MulAut T)) ⊓ L = ⊥ := by
        have hdvd' : Nat.card ↥((B : Subgroup (MulAut T)) ⊓ L) ∣ p := by
          rw [← hLp]; exact Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime hpp).1 hdvd' with h1 | hp'
        · exact Subgroup.card_eq_one.1 h1
        · exfalso
          have hEq : (B : Subgroup (MulAut T)) ⊓ L = L :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hLp, hp'])
          exact hnp2 (by change L ≤ (B : Subgroup (MulAut T)); rw [← hEq]; exact inf_le_left)
      have hBLg_bot : (B : Subgroup (MulAut T)) ⊓ Lg = ⊥ := by
        have hdvd' : Nat.card ↥((B : Subgroup (MulAut T)) ⊓ Lg) ∣ p := by
          rw [← hLgcard]; exact Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime hpp).1 hdvd' with h1 | hp'
        · exact Subgroup.card_eq_one.1 h1
        · exfalso
          have hEq : (B : Subgroup (MulAut T)) ⊓ Lg = Lg :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hLgcard, hp'])
          exact hnp1 (by change Lg ≤ (B : Subgroup (MulAut T)); rw [← hEq]; exact inf_le_left)
      have hBsupL : (B : Subgroup (MulAut T)) ⊔ L = A := by
        refine s16t_blk_eq_top_of_lt_card hpp (hBspec B).1 le_sup_left (sup_le (hBspec B).1 hLA)
          hAcard (hBcard B) ?_
        intro hEq
        exact hnp2 (by change L ≤ (B : Subgroup (MulAut T)); rw [hEq]; exact le_sup_right)
      have hBsupLg : (B : Subgroup (MulAut T)) ⊔ Lg = A := by
        refine s16t_blk_eq_top_of_lt_card hpp (hBspec B).1 le_sup_left (sup_le (hBspec B).1 hLgA)
          hAcard (hBcard B) ?_
        intro hEq
        exact hnp1 (by change Lg ≤ (B : Subgroup (MulAut T)); rw [hEq]; exact le_sup_right)
      have hfixBL : Yb B ⊓ fixV L = ⊥ := by
        have h1 : Yb B ⊓ fixV L ≤ fixV ((B : Subgroup (MulAut T)) ⊔ L) := by
          intro y hy
          exact (s16t_blk_mem_fixV_sup_iff y).2 ⟨hy.1, hy.2⟩
        rw [hBsupL, hfixA] at h1
        exact le_bot_iff.1 h1
      have hfixBLg : Yb B ⊓ fixV Lg = ⊥ := by
        have h1 : Yb B ⊓ fixV Lg ≤ fixV ((B : Subgroup (MulAut T)) ⊔ Lg) := by
          intro y hy
          exact (s16t_blk_mem_fixV_sup_iff y).2 ⟨hy.1, hy.2⟩
        rw [hBsupLg, hfixA] at h1
        exact le_bot_iff.1 h1
      have hY_le_W : Yb B ≤ W := by
        have hcop := (coprime_decomp (P := L) hoddL hT (W := Yb B) (fun y hy w hw => by
          have hmap := s16t_blk_map_fixV_of_comm (B := (B : Subgroup (MulAut T))) (a := y)
            (fun b hb => hAc y (hLA hy) b ((hBspec B).1 hb))
          have hmem : y w ∈ (fixV (B : Subgroup (MulAut T))).map y.toMonoidHom :=
            Subgroup.mem_map.2 ⟨w, hw, rfl⟩
          rw [hmap] at hmem
          exact hmem)).1
        rw [hfixBL, sup_bot_eq] at hcop
        rw [← hcop, hWdef]
        exact commSub_mono le_top le_rfl
      have hY_le_Wg : Yb B ≤ Wg := by
        have hcop := (coprime_decomp (P := Lg) hoddLg hT (W := Yb B) (fun y hy w hw => by
          have hmap := s16t_blk_map_fixV_of_comm (B := (B : Subgroup (MulAut T))) (a := y)
            (fun b hb => hAc y (hLgA hy) b ((hBspec B).1 hb))
          have hmem : y w ∈ (fixV (B : Subgroup (MulAut T))).map y.toMonoidHom :=
            Subgroup.mem_map.2 ⟨w, hw, rfl⟩
          rw [hmap] at hmem
          exact hmem)).1
        rw [hfixBLg, sup_bot_eq] at hcop
        rw [← hcop, ← hcommLg]
        exact commSub_mono le_top le_rfl
      exact (hBspec B).2.2 (eq_bot_iff.2 ((le_inf hY_le_W hY_le_Wg).trans (le_of_eq hWinfWg)))
    rcases hexh with h1 | h2b
    · exact Or.inl ⟨h1, fun h2' => hnotboth ⟨h1, h2'⟩⟩
    · exact Or.inr ⟨h2b, fun h1' => hnotboth ⟨h1', h2b⟩⟩
  let s₁ : Finset Idx := Finset.univ.filter P₁
  let s₂ : Finset Idx := Finset.univ.filter P₂
  have hmem_s1 : ∀ B : Idx, B ∈ s₁ ↔ P₁ B := by intro B; simp [s₁]
  have hmem_s2 : ∀ B : Idx, B ∈ s₂ ↔ P₂ B := by intro B; simp [s₂]
  have hunion : s₁ ∪ s₂ = Finset.univ := by
    ext B
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases hdich B with h | h
    · exact Or.inl ((hmem_s1 B).2 h.1)
    · exact Or.inr ((hmem_s2 B).2 h.1)
  have hdisj : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_left]
    intro B h1 h2
    exact (hdich B).elim (fun h => h.2 ((hmem_s2 B).1 h2)) (fun h => h.2 ((hmem_s1 B).1 h1))
  have hcard_sum : s₁.card + s₂.card = Fintype.card Idx := by
    rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj]
  let S₁ : Subgroup T := ⨆ B ∈ s₁, Yb B
  let S₂ : Subgroup T := ⨆ B ∈ s₂, Yb B
  have hS1_le : S₁ ≤ W := by
    refine iSup_le fun B => iSup_le fun hB => ?_
    rw [← hfixV_Lg]
    exact s16t_blk_fixV_anti ((hmem_s1 B).1 hB)
  have hS2_le : S₂ ≤ Wg := by
    refine iSup_le fun B => iSup_le fun hB => ?_
    rw [← hfixV_L]
    exact s16t_blk_fixV_anti ((hmem_s2 B).1 hB)
  have hS1S2_top : S₁ ⊔ S₂ = ⊤ := by
    rw [eq_top_iff, ← hsup_all]
    refine iSup_le fun B => ?_
    rcases hdich B with h | h
    · exact le_trans (le_iSup₂ (f := fun B (_ : B ∈ s₁) => Yb B) B ((hmem_s1 B).2 h.1))
        le_sup_left
    · exact le_trans (le_iSup₂ (f := fun B (_ : B ∈ s₂) => Yb B) B ((hmem_s2 B).2 h.1))
        le_sup_right
  have hS1_eq_W : S₁ = W := by
    refine le_antisymm hS1_le ?_
    intro w hw
    have hwt : w ∈ S₁ ⊔ S₂ := by rw [hS1S2_top]; exact Subgroup.mem_top w
    obtain ⟨x₁, hx₁, x₂, hx₂, hx12⟩ := Subgroup.mem_sup.1 hwt
    have hx2W : x₂ ∈ W := by
      have h2' : x₂ = x₁⁻¹ * w := by rw [← hx12]; group
      rw [h2']
      exact W.mul_mem (W.inv_mem (hS1_le hx₁)) hw
    have hx2bot : x₂ ∈ (⊥ : Subgroup T) := by
      have : x₂ ∈ W ⊓ Wg := ⟨hx2W, hS2_le hx₂⟩
      rwa [hWinfWg] at this
    have hx2one : x₂ = 1 := Subgroup.mem_bot.1 hx2bot
    have hweq : w = x₁ := by rw [← hx12, hx2one, mul_one]
    rw [hweq]
    exact hx₁
  have hS2_eq_Wg : S₂ = Wg := by
    refine le_antisymm hS2_le ?_
    intro w hw
    have hwt : w ∈ S₁ ⊔ S₂ := by rw [hS1S2_top]; exact Subgroup.mem_top w
    obtain ⟨x₁, hx₁, x₂, hx₂, hx12⟩ := Subgroup.mem_sup.1 hwt
    have hx1Wg : x₁ ∈ Wg := by
      have h1' : x₁ = w * x₂⁻¹ := by rw [← hx12]; group
      rw [h1']
      exact Wg.mul_mem hw (Wg.inv_mem (hS2_le hx₂))
    have hx1bot : x₁ ∈ (⊥ : Subgroup T) := by
      have : x₁ ∈ W ⊓ Wg := ⟨hS1_le hx₁, hx1Wg⟩
      rwa [hWinfWg] at this
    have hx1one : x₁ = 1 := Subgroup.mem_bot.1 hx1bot
    have hweq : w = x₂ := by rw [← hx12, hx1one, one_mul]
    rw [hweq]
    exact hx₂
  have hrkS1 : ∑ B ∈ s₁, rk ↥(Yb B) = 2 * dParam p := by
    have h := rk_iSup_biSup_eq_sum Yb hind s₁
    rw [show (⨆ i ∈ s₁, Yb i) = S₁ from rfl, hS1_eq_W, hrkW] at h
    exact h.symm
  have hrkWg : rk ↥Wg = 2 * dParam p := by
    rw [hWgdef, s16n9b_rk_map, hWdef, hrk]
  have hrkS2 : ∑ B ∈ s₂, rk ↥(Yb B) = 2 * dParam p := by
    have h := rk_iSup_biSup_eq_sum Yb hind s₂
    rw [show (⨆ i ∈ s₂, Yb i) = S₂ from rfl, hS2_eq_Wg, hrkWg] at h
    exact h.symm
  have hcard1_le : s₁.card ≤ 2 := by
    have hle := Finset.card_nsmul_le_sum s₁ (fun B => rk ↥(Yb B)) (dParam p)
      (fun B _ => hrk_ge B)
    rw [hrkS1] at hle
    have h' : s₁.card * dParam p ≤ 2 * dParam p := by simpa [nsmul_eq_mul] using hle
    exact Nat.le_of_mul_le_mul_right h' hdpos
  have hcard2_le : s₂.card ≤ 2 := by
    have hle := Finset.card_nsmul_le_sum s₂ (fun B => rk ↥(Yb B)) (dParam p)
      (fun B _ => hrk_ge B)
    rw [hrkS2] at hle
    have h' : s₂.card * dParam p ≤ 2 * dParam p := by simpa [nsmul_eq_mul] using hle
    exact Nat.le_of_mul_le_mul_right h' hdpos
  have hcard1_pos : 0 < s₁.card := by
    rcases Nat.eq_zero_or_pos s₁.card with h0 | hpos
    · exfalso
      rw [Finset.card_eq_zero.1 h0, Finset.sum_empty] at hrkS1
      omega
    · exact hpos
  have hcard2_pos : 0 < s₂.card := by
    rcases Nat.eq_zero_or_pos s₂.card with h0 | hpos
    · exfalso
      rw [Finset.card_eq_zero.1 h0, Finset.sum_empty] at hrkS2
      omega
    · exact hpos
  have hg2_L : L.map (MulAut.conj (g * g)).toMonoidHom = L := by
    rcases h2.conj (g * g) (X.mul_mem h2.mem h2.mem) with h | h
    · exact h
    · exfalso
      have h3 : L.map (MulAut.conj (g * g)).toMonoidHom =
          L.map (MulAut.conj g).toMonoidHom := h
      have h4 := congrArg (fun B : Subgroup (MulAut T) =>
        B.map (MulAut.conj g⁻¹).toMonoidHom) h3
      rw [s16n9b_map_conj_map_conj, s16n9b_map_conj_map_conj,
        show g⁻¹ * (g * g) = g by group, show g⁻¹ * g = 1 by group,
        s16n9b_map_conj_one] at h4
      exact hLg_ne_L h4
  have hmem_map : ∀ x ∈ X, ∀ B : Idx,
      ((B : Subgroup (MulAut T)).map (MulAut.conj x).toMonoidHom) ∈ Idx := by
    intro x hx B
    simp only [Idx, s16t_blk_Hyp, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact (Subgroup.map_mono (hBspec B).1).trans (le_of_eq (hAn_map x hx))
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hBcard B, hAcard]
      ring
    · rw [s16t_blk_fixV_map_conj]
      exact fun hbot => (hBspec B).2.2
        ((Subgroup.map_eq_bot_iff_of_injective (fixV (B : Subgroup (MulAut T)))
          x.injective).1 hbot)
  let σ : Idx → Idx := fun B =>
    ⟨(B : Subgroup (MulAut T)).map (MulAut.conj g).toMonoidHom, hmem_map g h2.mem B⟩
  let σinv : Idx → Idx := fun B =>
    ⟨(B : Subgroup (MulAut T)).map (MulAut.conj g⁻¹).toMonoidHom,
      hmem_map g⁻¹ (X.inv_mem h2.mem) B⟩
  have hσ_sigma : ∀ B : Idx, σ (σinv B) = B := by
    intro B
    apply Subtype.ext
    simp only [σ, σinv]
    rw [s16n9b_map_conj_map_conj, mul_inv_cancel, s16n9b_map_conj_one]
  have hσinv_sigma : ∀ B : Idx, σinv (σ B) = B := by
    intro B
    apply Subtype.ext
    simp only [σ, σinv]
    rw [s16n9b_map_conj_map_conj, inv_mul_cancel, s16n9b_map_conj_one]
  have hσ_inj : Function.Injective σ := by
    intro B₁ B₂ h
    have := congrArg σinv h
    rwa [hσinv_sigma B₁, hσinv_sigma B₂] at this
  have hLg2 : Lg.map (MulAut.conj g).toMonoidHom = L := by
    rw [hLgdef, s16n9b_map_conj_map_conj, hg2_L]
  have hLg_inv : Lg = L.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h1 : L.map (MulAut.conj g⁻¹).toMonoidHom =
        (L.map (MulAut.conj (g * g)).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hg2_L]
    rw [h1, s16n9b_map_conj_map_conj, show g⁻¹ * (g * g) = g by group, hLgdef]
  have hσ_s1 : ∀ B : Idx, P₁ B → P₂ (σ B) := by
    intro B hB
    change L ≤ (B : Subgroup (MulAut T)).map (MulAut.conj g).toMonoidHom
    rw [← hLg2]
    exact Subgroup.map_mono hB
  have hσinv_s1 : ∀ B : Idx, P₂ B → P₁ (σinv B) := by
    intro B hB
    change Lg ≤ (B : Subgroup (MulAut T)).map (MulAut.conj g⁻¹).toMonoidHom
    rw [hLg_inv]
    exact Subgroup.map_mono hB
  have hcard12 : s₁.card = s₂.card := by
    refine Finset.card_bij (fun B _ => σ B) ?_ ?_ ?_
    · intro B hB
      exact (hmem_s2 (σ B)).2 (hσ_s1 B ((hmem_s1 B).1 hB))
    · intro B₁ _ B₂ _ hEq
      exact hσ_inj hEq
    · intro B hB
      refine ⟨σinv B, ?_, ?_⟩
      · exact (hmem_s1 (σinv B)).2 (hσinv_s1 B ((hmem_s2 B).1 hB))
      · exact hσ_sigma B
  have hinf_card : ∀ B₁' B₂' : Idx, B₁' ≠ B₂' →
      Nat.card ↥((B₁' : Subgroup (MulAut T)) ⊓ (B₂' : Subgroup (MulAut T))) = p := by
    intro B₁' B₂' hne
    have hsupB : (B₁' : Subgroup (MulAut T)) ⊔ (B₂' : Subgroup (MulAut T)) = A := by
      refine s16t_blk_eq_top_of_lt_card hpp (hBspec B₁').1 le_sup_left
        (sup_le (hBspec B₁').1 (hBspec B₂').1) hAcard (hBcard B₁') ?_
      intro h
      apply hne
      have hle : (B₂' : Subgroup (MulAut T)) ≤ (B₁' : Subgroup (MulAut T)) := by
        rw [h]; exact le_sup_right
      exact Subtype.ext (Subgroup.eq_of_le_of_card_ge hle
        (by rw [hBcard B₂', hBcard B₁'])).symm
    let B1a : Subgroup ↥A := (B₁' : Subgroup (MulAut T)).subgroupOf A
    let B2a : Subgroup ↥A := (B₂' : Subgroup (MulAut T)).subgroupOf A
    have hB1a_card : Nat.card ↥B1a = p ^ 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBspec B₁').1).toEquiv).trans
        (hBcard B₁')
    have hB2a_card : Nat.card ↥B2a = p ^ 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBspec B₂').1).toEquiv).trans
        (hBcard B₂')
    have hsup_a : B1a ⊔ B2a = ⊤ := by
      have h := Subgroup.subgroupOf_sup (A := (B₁' : Subgroup (MulAut T)))
        (A' := (B₂' : Subgroup (MulAut T))) (B := A) (hBspec B₁').1 (hBspec B₂').1
      rw [hsupB] at h
      exact h.symm.trans (Subgroup.subgroupOf_self A)
    have hKsub : ((B₁' : Subgroup (MulAut T)) ⊓ (B₂' : Subgroup (MulAut T))).subgroupOf A =
        B1a ⊓ B2a := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, B1a, B2a]
    have hcard_eq : Nat.card ↥(B1a ⊓ B2a) =
        Nat.card ↥((B₁' : Subgroup (MulAut T)) ⊓ (B₂' : Subgroup (MulAut T))) := by
      rw [← hKsub]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left.trans (hBspec B₁').1)).toEquiv
    have h := card_sup_mul_card_inf B1a B2a
    rw [hsup_a, Subgroup.card_top, hAcard, hB1a_card, hB2a_card, hcard_eq] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hpp.pos 3) ?_
    rw [show p ^ 2 * p ^ 2 = p ^ 4 from by ring] at h
    rw [mul_comm (p ^ 3)] at h
    rw [h]
    ring
  have hcard1_ge_two : 2 ≤ s₁.card := by
    by_contra hnot
    have h1 : s₁.card = 1 := by have := not_le.1 hnot; omega
    have h2 : s₂.card = 1 := by omega
    obtain ⟨B₁, hB₁⟩ := Finset.card_eq_one.1 h1
    obtain ⟨B₂, hB₂⟩ := Finset.card_eq_one.1 h2
    have hB1_mem : B₁ ∈ s₁ := by rw [hB₁]; exact Finset.mem_singleton_self B₁
    have hB2_mem : B₂ ∈ s₂ := by rw [hB₂]; exact Finset.mem_singleton_self B₂
    have hB1_not_s2 : B₁ ∉ s₂ := fun hh => (Finset.disjoint_left.1 hdisj) hB1_mem hh
    have hBne : B₁ ≠ B₂ := by
      intro hEq
      exact hB1_not_s2 (by rw [hB₂, hEq]; exact Finset.mem_singleton_self B₂)
    have htwo : (Finset.univ : Finset Idx) = {B₁, B₂} := by
      rw [← hunion, hB₁, hB₂, Finset.singleton_union]
    have htop_le : (⊤ : Subgroup T) ≤ Yb B₁ ⊔ Yb B₂ := by
      rw [← hsup_all]
      refine iSup_le fun B => ?_
      have hBmem : B ∈ ({B₁, B₂} : Finset Idx) := by rw [← htwo]; exact Finset.mem_univ B
      have hBcases : B = B₁ ∨ B = B₂ := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hBmem
      rcases hBcases with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    set K : Subgroup (MulAut T) :=
      (B₁ : Subgroup (MulAut T)) ⊓ (B₂ : Subgroup (MulAut T)) with hKdef
    have hK_card : p ≤ Nat.card ↥K := by
      rw [hKdef, hinf_card B₁ B₂ hBne]
    have hK_ne : K ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hK_card
      omega
    obtain ⟨k, hkne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hK_ne
    have hkB1 : (k : MulAut T) ∈ (B₁ : Subgroup (MulAut T)) :=
      (Subgroup.mem_inf.1 k.2).1
    have hkB2 : (k : MulAut T) ∈ (B₂ : Subgroup (MulAut T)) :=
      (Subgroup.mem_inf.1 k.2).2
    have hk_fix : ∀ v : T, (k : MulAut T) v = v := by
      intro v
      have hv : v ∈ Yb B₁ ⊔ Yb B₂ := htop_le (Subgroup.mem_top v)
      obtain ⟨y₁, hy₁, y₂, hy₂, hy12⟩ := Subgroup.mem_sup.1 hv
      have hk1 : (k : MulAut T) y₁ = y₁ := (mem_fixV.1 hy₁) (k : MulAut T) hkB1
      have hk2 : (k : MulAut T) y₂ = y₂ := (mem_fixV.1 hy₂) (k : MulAut T) hkB2
      rw [← hy12, map_mul, hk1, hk2]
    have hk_one : (k : MulAut T) = 1 := by ext v; exact hk_fix v
    exact hkne (Subtype.ext hk_one)
  have hcard1_eq_two : s₁.card = 2 := by omega
  have hcard2_eq_two : s₂.card = 2 := by omega
  have hcardB4 : Fintype.card Idx = 4 := by omega
  have hrank_s1 : ∀ B : Idx, B ∈ s₁ → rk ↥(Yb B) = dParam p := by
    intro B hB
    have hsplit := Finset.add_sum_erase s₁ (fun C => rk ↥(Yb C)) hB
    rw [hrkS1] at hsplit
    have herase := Finset.card_nsmul_le_sum (s₁.erase B) (fun C => rk ↥(Yb C))
      (dParam p) (fun C _ => hrk_ge C)
    have hcarderase : (s₁.erase B).card = 1 := by
      rw [Finset.card_erase_of_mem hB, hcard1_eq_two]
    rw [hcarderase, one_nsmul] at herase
    have hge := hrk_ge B
    omega
  have hrank_s2 : ∀ B : Idx, B ∈ s₂ → rk ↥(Yb B) = dParam p := by
    intro B hB
    have hsplit := Finset.add_sum_erase s₂ (fun C => rk ↥(Yb C)) hB
    rw [hrkS2] at hsplit
    have herase := Finset.card_nsmul_le_sum (s₂.erase B) (fun C => rk ↥(Yb C))
      (dParam p) (fun C _ => hrk_ge C)
    have hcarderase : (s₂.erase B).card = 1 := by
      rw [Finset.card_erase_of_mem hB, hcard2_eq_two]
    rw [hcarderase, one_nsmul] at herase
    have hge := hrk_ge B
    omega
  have hYb_rank : ∀ B : Idx, rk ↥(Yb B) = dParam p := by
    intro B
    have hBmem : B ∈ s₁ ∪ s₂ := by rw [hunion]; exact Finset.mem_univ B
    rcases Finset.mem_union.1 hBmem with hB | hB
    · exact hrank_s1 B hB
    · exact hrank_s2 B hB
  have hker_eq : ∀ B : Idx, A ⊓ centSub (Yb B) = (B : Subgroup (MulAut T)) := by
    intro B
    apply le_antisymm
    · intro a ha
      obtain ⟨haA, hacent⟩ := Subgroup.mem_inf.1 ha
      by_contra haB
      have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.2 haA
      have hneBC : (B : Subgroup (MulAut T)) ≠ (B : Subgroup (MulAut T)) ⊔
          Subgroup.zpowers a := by
        intro h
        exact haB (by rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
      have hBsup : (B : Subgroup (MulAut T)) ⊔ Subgroup.zpowers a = A :=
        s16t_blk_eq_top_of_lt_card hpp (hBspec B).1 le_sup_left (sup_le (hBspec B).1 hzA) hAcard
          (hBcard B) hneBC
      have hle_fix : Yb B ≤ fixV (Subgroup.zpowers a) := by
        intro y hy
        rw [mem_fixV_zpowers_iff_apply]
        exact (mem_centSub.1 hacent) y hy
      have hle : Yb B ≤ fixV ((B : Subgroup (MulAut T)) ⊔ Subgroup.zpowers a) := by
        intro y hy
        exact (s16t_blk_mem_fixV_sup_iff y).2 ⟨hy, hle_fix hy⟩
      rw [hBsup, hfixA] at hle
      exact (hBspec B).2.2 (eq_bot_iff.2 hle)
    · intro b hb
      refine Subgroup.mem_inf.2 ⟨(hBspec B).1 hb, ?_⟩
      rw [mem_centSub]
      intro y hy
      exact (mem_fixV.1 hy) b hb
  let e : Fin 4 ≃ Idx := (Fintype.equivFinOfCardEq hcardB4).symm
  let Y : Fin 4 → Subgroup T := fun i => Yb (e i)
  refine ⟨Y, ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact hind.comp e.injective
  · intro i j hij
    exact e.injective (hind.injective (fun B => (hBspec B).2.2) hij)
  · show (⨆ i, Yb (e i)) = ⊤
    rw [Equiv.iSup_comp]
    exact hsup_all
  · simp
  · intro i
    exact hYb_rank (e i)
  · intro x hx i
    refine ⟨e.symm ⟨((e i : Subgroup (MulAut T)).map (MulAut.conj x).toMonoidHom),
      hmem_map x hx (e i)⟩, ?_⟩
    change (Yb (e i)).map x.toMonoidHom = Yb (e (e.symm _))
    rw [Equiv.apply_symm_apply]
    exact (s16t_blk_fixV_map_conj (e i : Subgroup (MulAut T)) x).symm
  · intro a ha i
    change (Yb (e i)).map a.toMonoidHom = Yb (e i)
    exact s16t_blk_map_fixV_of_comm (fun b hb => hAc a ha b ((hBspec (e i)).1 hb))
  · intro i
    change Nat.card ↥(A ⊓ centSub (Yb (e i))) = p ^ 2
    rw [hker_eq (e i), hBcard (e i)]
  · intro i j hij
    change Nat.card ↥((A ⊓ centSub (Yb (e i))) ⊓ (A ⊓ centSub (Yb (e j)))) ≤ p
    rw [hker_eq (e i), hker_eq (e j)]
    have hBij : e i ≠ e j := fun h => hij (e.injective h)
    rw [hinf_card (e i) (e j) hBij]
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
