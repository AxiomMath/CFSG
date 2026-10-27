module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Ctx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenModOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1610_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

theorem s16c1610_dParam_seven : dParam 7 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

theorem s16c1610_dParam_le_mParam {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A X : Subgroup (MulAut W)} {p : ℕ} (hp : p = 3 ∨ p = 7)
    (hXA : X ≤ A) (hXn : ∀ g ∈ A, ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hXp : Nat.card X = p)
    (hfix : fixV X = ⊥) (hrk : 2 * dParam p ≤ rk W) : dParam p ≤ E3.mParam A := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : IsCyclic X := isCyclic_of_prime_card hXp
  obtain ⟨⟨a, haX⟩, hgen⟩ := IsCyclic.exists_generator (α := X)
  have ha : orderOf a = p := by
    have h1 : orderOf (⟨a, haX⟩ : X) = Nat.card X := orderOf_eq_card_of_forall_mem_zpowers hgen
    rw [hXp] at h1
    rw [← h1]
    exact (Subgroup.orderOf_mk a haX).symm
  have hX : X = Subgroup.zpowers a := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    · exact Subgroup.zpowers_le.mpr haX
  have hdp : dParam p ≤ dParam p + dParam p := Nat.le_add_right _ _
  refine s16c167_le_mParam A ?_ (le_trans (by omega) hrk)
  intro t htA htt ht1
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one]; exact htt
  have hn : t * a * t ∈ Subgroup.zpowers a := by
    have h1 := hXn t htA a haX
    rw [htinv, hX] at h1
    exact h1
  have hta : t * a * t = a⁻¹ ∨ t * a = a * t := by
    rcases s16c167_conj_eq_or_inv hpp ha htt hn with h | h
    · right
      calc t * a = t * a * (t * t) := by rw [htt, mul_one]
        _ = (t * a * t) * t := by group
        _ = a * t := by rw [h]
    · left; exact h
  have hIa : (⊤ : Subgroup W).map a.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ a.surjective
  have hIt : (⊤ : Subgroup W).map t.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ t.surjective
  have hfixI : (⊤ : Subgroup W) ⊓ fixV (Subgroup.zpowers a) = ⊥ := by
    rw [hX] at hfix
    rw [hfix, inf_bot_eq]
  have hrkI : 2 * dParam p ≤ rk ↥(⊤ : Subgroup W) := by rwa [rk_top]
  have hq : ∀ F : Subgroup W, E3.mQuot (⊤ : Subgroup W) (⊤ ⊓ F) = rkIdx F := by
    intro F
    simp [E3.mQuot, rkIdx, Subgroup.relIndex_top_right]
  have hmain : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers t) ∨
      dParam p ≤ E3.mQuot (⊤ : Subgroup W) (⊤ ⊓ fixV (Subgroup.zpowers t)) := by
    rcases hp with rfl | rfl
    · rw [s16c1610_dParam_three] at hrkI ⊢
      exact s16c167_oe3 hW ha htt hta hIa hIt hfixI (by omega)
    · rw [s16c1610_dParam_seven] at hrkI ⊢
      exact s16c167_oe7 hW ha htt hta hIa hIt hfixI (by omega)
  rcases hmain with h | h
  · exfalso
    apply ht1
    ext x
    exact (mem_fixV_zpowers t x).mp (h (Subgroup.mem_top x))
  · rwa [hq] at h

private lemma s16c1610_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) :=
  fun _ _ hxy =>
    IntMod.val_injective
      (mul_inv_eq_one.1 (Subgroup.mem_bot.1 ((mkTil_eq_iff ⊥ V hV _ _).1 hxy)))

private theorem s16c1610_fixV_invariant {W : Type*} [CommGroup W]
    {A Y : Subgroup (MulAut W)} (hYA : Y ≤ A) (hN : (Y.subgroupOf A).Normal) :
    ∀ φ ∈ A, ∀ u ∈ fixV Y, φ u ∈ fixV Y := by
  intro φ hφ u hu
  rw [mem_fixV] at hu ⊢
  intro y hy
  have hy' : φ⁻¹ * y * φ ∈ Y := by
    have h1 : φ⁻¹ * y * (φ⁻¹)⁻¹ ∈ Y :=
      (Subgroup.normal_subgroupOf_iff hYA).1 hN y (φ⁻¹) hy (inv_mem hφ)
    simpa only [inv_inv] using h1
  calc y (φ u) = (y * φ) u := rfl
    _ = (φ * (φ⁻¹ * y * φ)) u := by rw [show y * φ = φ * (φ⁻¹ * y * φ) by group]
    _ = φ ((φ⁻¹ * y * φ) u) := rfl
    _ = φ u := by rw [hu _ hy']

private lemma s16c1610_commSub_invariant {W : Type*} [CommGroup W]
    {A Y : Subgroup (MulAut W)} (hYA : Y ≤ A) (hN : (Y.subgroupOf A).Normal) :
    ∀ φ ∈ A, ∀ u ∈ commSub (⊤ : Subgroup W) Y, φ u ∈ commSub (⊤ : Subgroup W) Y := by
  intro φ hφ u hu
  have hYconj : Y.map (MulAut.conj φ).toMonoidHom = Y := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      rw [Subgroup.mem_comap]
      simpa [MulAut.conj_apply] using s15_Kbar_conj_mem_of_normal hYA hN hφ hy
    · intro y hy
      refine Subgroup.mem_map.2 ⟨(MulAut.conj φ).symm y, ?_, ?_⟩
      · rw [MulAut.conj_symm_apply]
        simpa using s15_Kbar_conj_mem_of_normal hYA hN (inv_mem hφ) hy
      · exact (MulAut.conj φ).apply_symm_apply y
  have htop : (⊤ : Subgroup W).map φ.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ φ.surjective
  have h := s15_Kbar_commSub_map_conj (⊤ : Subgroup W) Y φ
  rw [htop, hYconj] at h
  exact h.symm ▸ Subgroup.mem_map.2 ⟨u, hu, rfl⟩

private lemma s16c1610_preTil_ne_bot {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V)
    {S : Subgroup (Vtil ⊥ V h.isElemAbelian)} (hS : S ≠ ⊥) :
    preTil ⊥ V h.isElemAbelian S ≠ ⊥ := by
  intro hbot
  apply hS
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V h.isElemAbelian s
  have hxbot : x.val ∈ (⊥ : Subgroup G) := by
    have hxS : x.val ∈ preTil ⊥ V h.isElemAbelian S :=
      (mem_preTil ⊥ V h.isElemAbelian S).2 ⟨x, rfl, hs⟩
    rwa [hbot] at hxS
  have hx1 : x = 1 := IntMod.val_injective (by simpa using Subgroup.mem_bot.1 hxbot)
  rw [hx1, map_one]

private lemma s16c1610_preTil_normalizer {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V)
    {S : Subgroup (Vtil ⊥ V h.isElemAbelian)}
    (hS : ∀ φ ∈ Mbar D.M ⊥ V h.isElemAbelian, ∀ u ∈ S, φ u ∈ S) :
    D.M ≤ normalizer ((preTil ⊥ V h.isElemAbelian S : Subgroup G) : Set G) := by
  have hstep : ∀ {m x : G}, m ∈ D.M → x ∈ preTil ⊥ V h.isElemAbelian S →
      m * x * m⁻¹ ∈ preTil ⊥ V h.isElemAbelian S := by
    intro m x hm hx
    obtain ⟨y, hyx, hyS⟩ := (mem_preTil ⊥ V h.isElemAbelian S).1 hx
    have hxV : x ∈ V := preTil_le ⊥ V h.isElemAbelian S hx
    have hm_st : m ∈ stabTil (⊥ : Subgroup G) V :=
      le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ hm
    have hmv : m * x * m⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (h.pairFacts.le_normalizer hm) x).1 hxV
    refine (mem_preTil ⊥ V h.isElemAbelian S).2
      ⟨IntMod.mk h.isElemAbelian ⟨m * x * m⁻¹, hmv⟩, rfl, ?_⟩
    have hEq : actStab ⊥ V h.isElemAbelian ⟨m, hm_st⟩ y =
        IntMod.mk h.isElemAbelian ⟨m * x * m⁻¹, hmv⟩ :=
      IntMod.val_injective (by rw [actStab_apply_val, hyx]; rfl)
    rw [← hEq, ← actTil_mk ⊥ V h.isElemAbelian ⟨m, hm_st⟩ y]
    exact hS _ (actTil_mem_barSub ⊥ V h.isElemAbelian hm hm_st) _ hyS
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => hstep hm hx, fun hx => by
    have h := hstep (inv_mem hm) hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x by group] at h⟩

theorem s16c1610_fixV_eq_bot (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {Y : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hYM : Y ≤ Mbar D.M V₀ V h.isElemAbelian)
    (hYn : (Y.subgroupOf (Mbar D.M V₀ V h.isElemAbelian)).Normal) (hY : Y ≠ ⊥)
    (hodd : Odd (Nat.card Y)) : fixV Y = ⊥ := by
  rcases eq_or_ne V₀ ⊥ with hV₀ | hV₀
  · subst hV₀
    let S₁ : Subgroup (Vtil ⊥ V h.isElemAbelian) := fixV Y
    let S₂ : Subgroup (Vtil ⊥ V h.isElemAbelian) :=
      commSub (⊤ : Subgroup (Vtil ⊥ V h.isElemAbelian)) Y
    have hS₁def : S₁ = fixV Y := rfl
    have hS₂def : S₂ = commSub (⊤ : Subgroup (Vtil ⊥ V h.isElemAbelian)) Y := rfl
    have hfixInv : ∀ φ ∈ Mbar D.M ⊥ V h.isElemAbelian, ∀ u ∈ S₁, φ u ∈ S₁ :=
      s16c1610_fixV_invariant hYM hYn
    have hcommInv : ∀ φ ∈ Mbar D.M ⊥ V h.isElemAbelian, ∀ u ∈ S₂, φ u ∈ S₂ :=
      s16c1610_commSub_invariant hYM hYn
    have hdec := coprime_decomp (P := Y) hodd (Vtil_pow_two h.isElemAbelian)
      (W := (⊤ : Subgroup (Vtil ⊥ V h.isElemAbelian))) (fun _ _ _ _ => Subgroup.mem_top _)
    have hsup' : S₂ ⊔ S₁ = ⊤ := by simpa [hS₁def, hS₂def, top_inf_eq] using hdec.1
    have hsup : S₁ ⊔ S₂ = ⊤ := by rw [sup_comm]; exact hsup'
    have hinf' : S₂ ⊓ S₁ = ⊥ := by simpa [hS₁def, hS₂def, top_inf_eq] using hdec.2
    have hinf : S₁ ⊓ S₂ = ⊥ := by rw [inf_comm]; exact hinf'
    have hS₂ne : S₂ ≠ ⊥ := by
      intro hbot
      have htop : fixV Y = ⊤ := by
        have hle : (⊤ : Subgroup (Vtil ⊥ V h.isElemAbelian)) ≤ S₁ := by
          rw [← hsup, hbot]
          simp
        exact hS₁def.symm.trans (top_le_iff.1 hle)
      exact hY (by
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        ext u
        exact mem_fixV.1 (htop.symm ▸ Subgroup.mem_top u) y hy)
    let V₁ : Subgroup G := preTil ⊥ V h.isElemAbelian S₁
    let V₂ : Subgroup G := preTil ⊥ V h.isElemAbelian S₂
    by_cases hS₁bot : S₁ = ⊥
    · exact hS₁bot
    · exfalso
      have hV₁ne : V₁ ≠ ⊥ := s16c1610_preTil_ne_bot h hS₁bot
      have hV₂ne : V₂ ≠ ⊥ := s16c1610_preTil_ne_bot h hS₂ne
      have hV₁ : InCalV D.M V₁ :=
        ⟨hV₁ne, (preTil_le ⊥ V h.isElemAbelian S₁).trans h.pairFacts.le_M,
          s16c1610_preTil_normalizer h hfixInv,
          IsElemAbelian.mono h.pairFacts.elemAbelian (preTil_le ⊥ V h.isElemAbelian S₁)⟩
      have hV₂ : InCalV D.M V₂ :=
        ⟨hV₂ne, (preTil_le ⊥ V h.isElemAbelian S₂).trans h.pairFacts.le_M,
          s16c1610_preTil_normalizer h hcommInv,
          IsElemAbelian.mono h.pairFacts.elemAbelian (preTil_le ⊥ V h.isElemAbelian S₂)⟩
      have hVsup : V = V₁ ⊔ V₂ := by
        refine le_antisymm ?_ ?_
        · intro v hv
          have hvtop : mkTil ⊥ V h.isElemAbelian (IntMod.mk h.isElemAbelian ⟨v, hv⟩) ∈
              S₁ ⊔ S₂ := by rw [hsup]; exact Subgroup.mem_top _
          obtain ⟨s₁, hs₁, s₂, hs₂, hss⟩ := Subgroup.mem_sup.1 hvtop
          obtain ⟨x₁, rfl⟩ := mkTil_surjective ⊥ V h.isElemAbelian s₁
          obtain ⟨x₂, rfl⟩ := mkTil_surjective ⊥ V h.isElemAbelian s₂
          have hx12 : x₁ * x₂ = IntMod.mk h.isElemAbelian ⟨v, hv⟩ :=
            s16c1610_mkTil_bot_injective h.isElemAbelian (by rw [map_mul]; exact hss)
          have hx₁ : x₁.val ∈ V₁ :=
            (mem_preTil ⊥ V h.isElemAbelian S₁).2 ⟨x₁, rfl, hs₁⟩
          have hx₂ : x₂.val ∈ V₂ :=
            (mem_preTil ⊥ V h.isElemAbelian S₂).2 ⟨x₂, rfl, hs₂⟩
          have hvval : v = x₁.val * x₂.val := by
            have h := congrArg IntMod.val hx12
            rw [IntMod.val_mul] at h
            exact h.symm
          rw [hvval]
          exact Subgroup.mul_mem_sup hx₁ hx₂
        · exact sup_le (preTil_le ⊥ V h.isElemAbelian S₁)
            (preTil_le ⊥ V h.isElemAbelian S₂)
      rcases twelve_fifteen D hx h61 h127 h1214 h hV₁ hV₂ hVsup with heq | heq
      · have hS₁top : fixV Y = ⊤ := by
          have h1 : preTil ⊥ V h.isElemAbelian S₁ = preTil ⊥ V h.isElemAbelian ⊤ := by
            rw [preTil_top]
            exact heq.symm
          have h2 := congrArg (imgTil ⊥ V h.isElemAbelian) h1
          rw [imgTil_preTil, imgTil_preTil] at h2
          exact hS₁def.symm.trans h2
        exact hY (by
          rw [Subgroup.eq_bot_iff_forall]
          intro y hy
          ext u
          exact mem_fixV.1 (hS₁top.symm ▸ Subgroup.mem_top u) y hy)
      · have hS₂top : S₂ = ⊤ := by
          have h1 : preTil ⊥ V h.isElemAbelian S₂ = preTil ⊥ V h.isElemAbelian ⊤ := by
            rw [preTil_top]
            exact heq.symm
          have h2 := congrArg (imgTil ⊥ V h.isElemAbelian) h1
          rwa [imgTil_preTil, imgTil_preTil] at h2
        refine hS₁bot ?_
        calc S₁ = S₁ ⊓ ⊤ := (inf_top_eq S₁).symm
          _ = S₁ ⊓ S₂ := by rw [hS₂top]
          _ = ⊥ := hinf
  · exact s15_Kbar_fixV_eq_bot_of_ne_bot h hV₀ hYM hYn hY

theorem s16c1610_k_lt_dParam_seven (D : Data G) : D.k < dParam 7 := by
  rw [s16c1610_dParam_seven]
  exact lt_of_le_of_lt (s16c167_k_le_two D) (by norm_num)

theorem s16c1610_k_lt_dParam_three (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h3 : 3 ∈ D.sig) : D.k < dParam 3 := by
  rw [s16c1610_dParam_three, Data.k_eq_one_of_three_mem D hSg h1219 h3]
  norm_num

theorem s16c1610_k_lt_mBar_of_normal_prime (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {p : ℕ}
    (hp : p = 3 ∨ p = 7) (hkp : D.k < dParam p)
    {X : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hXM : X ≤ Mbar D.M V₀ V h.isElemAbelian) (hXcard : Nat.card X = p)
    (hXnorm : ∀ m ∈ Mbar D.M V₀ V h.isElemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hrk : 2 * dParam p ≤ rk (Vtil V₀ V h.isElemAbelian)) :
    D.k < mBar D.M V₀ V h.isElemAbelian := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hXne : X ≠ ⊥ := by
    intro hX
    rw [hX, Subgroup.card_bot] at hXcard
    exact hpp.one_lt.ne hXcard
  have hXn : (X.subgroupOf (Mbar D.M V₀ V h.isElemAbelian)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hXnorm g g.2 n hn⟩
  have hodd : Odd (Nat.card X) := by
    rw [hXcard]
    rcases hp with rfl | rfl <;> decide
  have hfix := s16c1610_fixV_eq_bot D hx h61 h127 h1214 h hXM hXn hXne hodd
  exact lt_of_lt_of_le hkp
    (s16c1610_dParam_le_mParam (Vtil_pow_two h.isElemAbelian) hp hXM hXnorm hXcard hfix hrk)

section Certified


theorem s16c1610_out10_of_normal_prime (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h1214 : F12.R1214 D) (h162 : W3Thm162Ext G)
    (h139 : Hyp139) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {p : ℕ} (hp : p = 3 ∨ p = 7)
    (hkp : D.k < dParam p) {X : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hXM : X ≤ Mbar D.M V₀ V h.isElemAbelian) (hXcard : Nat.card X = p)
    (hXnorm : ∀ m ∈ Mbar D.M V₀ V h.isElemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hrk : 2 * dParam p ≤ rk (Vtil V₀ V h.isElemAbelian))
    (hnot : ¬ Concl614 (Vtil V₀ V h.isElemAbelian) (Mbar D.M V₀ V h.isElemAbelian) X) :
    Out10 D V₀ V h.isElemAbelian := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hkm := s16c1610_k_lt_mBar_of_normal_prime D hx h61 h127 h1214 h hp hkp hXM hXcard
    hXnorm hrk
  have hpk : 2 ^ (D.k + 1) - 1 ≤ p := by
    have hk2 := s16c167_k_le_two D
    rcases hp with rfl | rfl
    · rw [s16c1610_dParam_three] at hkp
      have : D.k = 1 := by
        rcases s16c1610_k_cases D with h1 | h1 <;> omega
      rw [this]
      norm_num
    · rw [s16c1610_dParam_seven] at hkp
      have : D.k + 1 ≤ 3 := by omega
      calc 2 ^ (D.k + 1) - 1 ≤ 2 ^ 3 - 1 :=
            Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) this) 1
        _ = 7 := by norm_num
  exact s16c1610_out10_of_r14 D hx h61 h127 h1114 h162 h139 h hkm hpp hpk hXM hXcard hXnorm hnot

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
