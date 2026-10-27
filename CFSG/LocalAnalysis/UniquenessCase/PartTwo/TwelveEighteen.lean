module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenSetting
public import CFSG.LocalAnalysis.WeakClosure81.FourteenUncond
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveL
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22p
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2Ext
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def XCond1218 (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (j : ℕ)
    (X : Subgroup G) : Prop :=
  rankThreeLayer (barSub V₀ V hV X) = barSub V₀ V hV X ∨
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥(barSub V₀ V hV X) ∧
      ((∃ a ∈ barSub V₀ V hV X, ∃ b ∈ barSub V₀ V hV X, a * b ≠ b * a) ∨ 2 ^ j - 1 < p ∨
        ∃ P : Subgroup G, IsSylowIn p P X ∧ UniqueMax M (P ⊔ centralizer (V : Set G)))

namespace TwelveEighteen

theorem inCalOStar_mono {n n' : ℕ} {M V₀ V : Subgroup G} {g : G} (hnn : n ≤ n')
    (h : InCalOStar n M V₀ V g) : InCalOStar n' M V₀ V g := by
  obtain ⟨⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩, hrest⟩ := h
  exact ⟨⟨⟨h1, h2.trans hnn, h3⟩, ⟨h4, h5.trans hnn, h6⟩⟩, hrest⟩

theorem not_inCalO_zero {M V₀ V : Subgroup G} (hV : IsPGroup 2 V) (g : G) :
    ¬ InCalO 0 M V₀ V g := by
  rintro ⟨⟨-, h0, -⟩, ⟨hVM, -, -⟩⟩
  apply hVM
  have h0' : E3.mQuot V (V ⊓ conjSubgroup M g) = 0 := by
    rw [mQuot_inf_left]
    omega
  have := (E3.mQuot_eq_zero_iff hV inf_le_left).1 h0'
  exact (le_of_eq this.symm).trans inf_le_right

theorem one_le_rMV {M V : Subgroup G} (hV : IsPGroup 2 V) (hM : normalizer (V : Set G) = M) :
    1 ≤ rMV M V := by
  unfold rMV
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hC⟩ := hU
  have hne : E3.mQuot V U ≠ 0 := by
    intro h0
    have hUeq := (E3.mQuot_eq_zero_iff hV hUV).1 h0
    apply hC
    rw [hUeq, ← hM]
    exact Subgroup.centralizer_le_normalizer _
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne

theorem rankThreeLayer_eq_bot_of_comm {Q : Type*} [Group Q] {X : Subgroup Q}
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) : rankThreeLayer X = ⊥ := by
  refine sSup_eq_bot.2 fun L hL => ?_
  obtain ⟨hLX, -, -, hsimp⟩ := hL
  have hcen : ∀ x : ↥L, x ∈ Subgroup.center ↥L := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hX _ (hLX y.2) _ (hLX x.2))
  have hsub : ∀ q : ↥L ⧸ Subgroup.center ↥L, q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => exact (QuotientGroup.eq_one_iff x).2 (hcen x)
  exfalso
  obtain ⟨a, b, hab⟩ := hsimp.toNontrivial.exists_pair_ne
  exact hab ((hsub a).trans (hsub b).symm)

theorem uniqueMax_sup_centralizer_of_isSylowIn {M V X P Q : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hXM : X ≤ M) (hMV : M ≤ normalizer (V : Set G))
    (hP : IsSylowIn p P X) (hQ : IsSylowIn p Q X)
    (hU : UniqueMax M (P ⊔ centralizer (V : Set G))) :
    UniqueMax M (Q ⊔ centralizer (V : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP' : CFSG.ABGLocalTools.IsSylowOf p P X :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hP.1, hP.2.1, hP.2.2⟩
  have hQ' : CFSG.ABGLocalTools.IsSylowOf p Q X :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hQ.1, hQ.2.1, hQ.2.2⟩
  obtain ⟨k, hk, hkQ⟩ := hP'.exists_mem_conj hQ'
  have hkM : k ∈ M := hXM hk
  have hQeq : Q = conjSubgroup P k⁻¹ := by
    ext x
    rw [mem_conjSubgroup_iff, hkQ x, inv_inv]
  have hVk : conjSubgroup V k⁻¹ = V :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hMV (M.inv_mem hkM))
  have hC : conjSubgroup (centralizer (V : Set G)) k⁻¹ = centralizer (V : Set G) := by
    rw [E3.conjSubgroup_centralizer, hVk]
  have hM : conjSubgroup M k⁻¹ = M :=
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (M.inv_mem hkM))
  have hsup : conjSubgroup (P ⊔ centralizer (V : Set G)) k⁻¹ =
      conjSubgroup P k⁻¹ ⊔ conjSubgroup (centralizer (V : Set G)) k⁻¹ := by
    unfold conjSubgroup
    exact Subgroup.map_sup _ _ _
  have h1 := uniqueMax_conjSubgroup hU k⁻¹
  rw [hM, hsup, hC, ← hQeq] at h1
  exact h1

theorem nOf_ne_bot {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g)
    (hone : OneFirst M V₀ V g) : NOf M V g ≠ ⊥ := by
  intro hE
  have hV := h.elemAbelian
  have hM : M ≤ normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hVM : V ≤ M := by rw [← h.normalizer_eq]; exact Subgroup.le_normalizer
  have hBM : BOf M V g ≤ M := inf_le_right
  apply barSub_BOf_ne_bot_uncond h
  rw [barSub_eq_bot_iff hV hM h.le_normalizer₀ hBM]
  refine le_trans ?_ hone
  refine le_inf (le_refl _) ?_
  intro b hb
  rw [mem_centralizer_iff]
  intro u hu
  have huV : u ∈ V := (Subgroup.mem_inf.1 hu).1
  have huMg : u ∈ conjSubgroup M g := (Subgroup.mem_inf.1 hu).2
  have hbVg : b ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hb).1
  have hbM : b ∈ M := (Subgroup.mem_inf.1 hb).2
  set c := u * b * u⁻¹ * b⁻¹ with hc
  have hcV : c ∈ V := by
    have h1 : b * u⁻¹ * b⁻¹ ∈ V :=
      (mem_normalizer_iff.1 (hM hbM) u⁻¹).1 (V.inv_mem huV)
    have e : c = u * (b * u⁻¹ * b⁻¹) := by rw [hc]; group
    rw [e]
    exact V.mul_mem huV h1
  have hcVg : c ∈ conjSubgroup V g := by
    have hMgN : conjSubgroup M g ≤ normalizer (conjSubgroup V g : Set G) := by
      rw [← E3.conjSubgroup_normalizer, h.normalizer_eq]
    have h1 : u * b * u⁻¹ ∈ conjSubgroup V g :=
      (mem_normalizer_iff.1 (hMgN huMg) b).1 hbVg
    exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem hbVg)
  have hcE : c ∈ NOf M V g := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hcV, ?_⟩, Subgroup.mem_inf.2 ⟨hcVg, hVM hcV⟩⟩
    have hVgMg : conjSubgroup V g ≤ conjSubgroup M g := E3.conjSubgroup_mono_left g hVM
    exact hVgMg hcVg
  rw [hE, Subgroup.mem_bot] at hcE
  have : u * b = b * u := by
    have e : u * b = c * (b * u) := by rw [hc]; group
    rw [e, hcE, one_mul]
  exact this

end TwelveEighteen

section Certified

theorem twelve_eighteen_empty (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {j : ℕ}
    {X : Subgroup G} (hXM : X ≤ D.M) (hXn : D.M ≤ normalizer (X : Set G))
    (hX1 : barSub V₀ V h.isElemAbelian X ≠ ⊥)
    (hb : bBar X D.M V₀ V h.isElemAbelian < mBar D.M V₀ V h.isElemAbelian - j)
    (hab : XCond1218 D.M V₀ V h.isElemAbelian j X) :
    ∀ g : G, ¬ InCalO j D.M V₀ V g := by
  intro g hO
  have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀
  have hH := hW.hyp6H
  have hV := h.isElemAbelian
  have hjm : j < mBar D.M V₀ V hV := by omega
  have hM : D.M ≤ normalizer (V : Set G) := hH.normalizer_eq.symm.le
  have hM₀ := hH.le_normalizer₀
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  by_cases hm1 : 1 < mBar D.M V₀ V hV
  swap
  · have hj0 : j = 0 := by omega
    subst hj0
    exact TwelveEighteen.not_inCalO_zero hV2 g hO
  have hr : ((mSub V₀ + j : ℕ) : ℕ∞) < rMV D.M V := by
    have h1 := h162 D V₀ V hW hx h61 hV₀ hm1
    refine lt_of_lt_of_le ?_ h1
    exact_mod_cast (by omega : mSub V₀ + j < mBar D.M V₀ V hV + mSub V₀)
  have hO1 : InCalO1 j D.M V₀ V g := (six_six hV hH.le hM hM₀ hjm g).1 hO
  have hOS : InCalOStar j D.M V₀ V g := (hH.hyp65 hV₀ hO1).inCalOStar_of_lt_rMV hr
  have h64 : Hyp64 j D.M V₀ V g := hH.hyp64 hOS
  have hBA := fourteen_nine_three_uncond h64
  have hpos : 0 < mBar D.M V₀ V hV - j := by omega
  have hXB : ⁅barSub V₀ V hV X, barSub V₀ V hV (BOf D.M V g)⁆ = ⊥ :=
    (bBar_lt_iff hV hpos).1 hb _ hBA
  have hjV : j ≤ mSub V - 1 := by
    have := mBar_le_rk (M := D.M) hV hH.le
    unfold mSub
    omega
  have hOS' : InCalOStar (mSub V - 1) D.M V₀ V g := TwelveEighteen.inCalOStar_mono hjV hOS
  obtain ⟨Y, hY⟩ := hTor D V₀ V hW hV₀ g hOS'
  have hXbM : barSub V₀ V hV X ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hXM
  have hXnorm := TwelveEighteen.conj_mem_barSub (V₀ := V₀) hV hXn
  obtain ⟨hn1, hcomm, hexp⟩ := fourteen_eight_one_uncond h64 (hH.conjGenerated hV₀) hY hX1
    hXbM hXnorm hXB
  have hnj : E3.mQuot V (UOf D.M V g) ≤ j := by
    have := hO.1.2.1
    unfold UOf
    rw [mQuot_inf_left]
    exact this
  rcases hab with hE | ⟨p, hp, hpX, hnab | hpj | ⟨P, hP, hPU⟩⟩
  ·
    apply hX1
    rw [← hE]
    exact TwelveEighteen.rankThreeLayer_eq_bot_of_comm hcomm
  ·
    obtain ⟨a, ha, b, hb', hab'⟩ := hnab
    exact hab' (hcomm a ha b hb')
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hX1
    have hy : (y : MulAut (Vtil V₀ V hV)) ^ (2 ^ E3.mQuot V (UOf D.M V g) - 1) = 1 :=
      hexp y y.2
    have hy' : y ^ (2 ^ E3.mQuot V (UOf D.M V g) - 1) = 1 := Subtype.ext (by simpa using hy)
    obtain ⟨k, hk⟩ := hpX y
    obtain ⟨i, hi, hiy⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk)
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hiy
      exact hy1 hiy
    have hpdvd : p ∣ 2 ^ E3.mQuot V (UOf D.M V g) - 1 := by
      have h1 : p ∣ orderOf y := by rw [hiy]; exact dvd_pow_self p hi0
      exact h1.trans (orderOf_dvd_of_pow_eq_one hy')
    have hpos2 : 0 < 2 ^ E3.mQuot V (UOf D.M V g) - 1 := by
      have : 2 ≤ 2 ^ E3.mQuot V (UOf D.M V g) :=
        le_self_pow₀ (by norm_num) (by omega)
      omega
    have hle1 : p ≤ 2 ^ E3.mQuot V (UOf D.M V g) - 1 := Nat.le_of_dvd hpos2 hpdvd
    have hle2 : 2 ^ E3.mQuot V (UOf D.M V g) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hnj
    omega
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    have hXne : p ∣ Nat.card ↥(barSub V₀ V hV X) := by
      obtain ⟨k, hk⟩ := hpX.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        apply hX1
        exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
      rw [hk]
      exact dvd_pow_self p hk0
    obtain ⟨Phat, hPhat, hPhatN⟩ := h1482 D V₀ V hW hV₀ g hOS' (barSub V₀ V hV X) hX1 hXbM
      hXnorm hXB p hp hXne
    have hXX : X ≤ preBarSub D.M V₀ V hV (barSub V₀ V hV X) :=
      le_preBarSub_barSub hV hXM (hXM.trans (le_stabTil hM hM₀))
    have hpreM : preBarSub D.M V₀ V hV (barSub V₀ V hV X) ≤ D.M := inf_le_left
    have hXnormal : (X.subgroupOf (preBarSub D.M V₀ V hV (barSub V₀ V hV X))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXX).2 (hpreM.trans hXn)
    have hP₁ : IsSylowIn p (Phat ⊓ X) X := hPhat.inf_normal hXX hXnormal
    have hU₁ := TwelveEighteen.uniqueMax_sup_centralizer_of_isSylowIn hp hXM hM hP hP₁ hPU
    have hEne : NOf D.M V g ≠ ⊥ := TwelveEighteen.nOf_ne_bot h64 hO1.2.1
    have hEV : NOf D.M V g ≤ V := inf_le_left.trans inf_le_left
    have hEVg : NOf D.M V g ≤ conjSubgroup V g := inf_le_right.trans inf_le_left
    have hloc : IsTwoLocal (normalizer (NOf D.M V g : Set G)) :=
      ⟨NOf D.M V g, hEne, hV2.to_le hEV, rfl⟩
    have hCV : centralizer (V : Set G) ≤ normalizer (NOf D.M V g : Set G) :=
      (Subgroup.centralizer_le hEV).trans (Subgroup.centralizer_le_normalizer _)
    have hle : Phat ⊓ X ⊔ centralizer (V : Set G) ≤ normalizer (NOf D.M V g : Set G) :=
      sup_le (inf_le_left.trans hPhatN) hCV
    have hNM := uc22p22p_le_of_uniqueMax hU₁ hloc hle
    apply hO.1.1
    have hVg := E3.isElemAbelian_conjSubgroup hV g
    have hVgC : conjSubgroup V g ≤ centralizer (NOf D.M V g : Set G) := by
      intro v hv
      rw [mem_centralizer_iff]
      intro e he
      exact CFSG.Open.IsElemAbelian.comm hVg (hEVg he) hv
    exact (hVgC.trans (Subgroup.centralizer_le_normalizer _)).trans hNM

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
