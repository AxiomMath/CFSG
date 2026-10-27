module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Basic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139CTensor
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundB
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.C1PackBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_conjBy_sup (e : MulAut W) (A B : Subgroup (MulAut W)) :
    conjBy e (A ⊔ B) = conjBy e A ⊔ conjBy e B := by
  simp only [conjBy, Subgroup.map_sup]

private theorem w1369_stableUnder_commSub_self (R : Subgroup (MulAut W)) :
    StableUnder R (commSub ⊤ R) := by
  intro r hr u hu
  rw [commSub] at hu ⊢
  refine Subgroup.closure_induction (p := fun c _ =>
    r c ∈ Subgroup.closure {c | ∃ x ∈ R, ∃ w ∈ (⊤ : Subgroup W), x w * w⁻¹ = c})
    ?_ ?_ ?_ ?_ hu
  · rintro c ⟨x, hx, w, -, rfl⟩
    refine Subgroup.subset_closure ⟨r * x * r⁻¹, R.mul_mem (R.mul_mem hr hx) (R.inv_mem hr),
      r w, Subgroup.mem_top _, ?_⟩
    rw [show (r * x * r⁻¹) (r w) = r (x w) from by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]]
    simp
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact (Subgroup.closure _).mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact (Subgroup.closure _).inv_mem ha

private theorem w1369_stableUnder_iff_le_stabSub {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : StableUnder X U) : X ≤ stabSub U := by
  intro x hx
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by
    have h1 := h x⁻¹ (X.inv_mem hx) (x u) hu
    rwa [MulAut.inv_apply_self] at h1,
    fun hu => h x hx u hu⟩

private theorem w1369_lemmaB_swap (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} {d : MulAut W} (hK : IsComponentOf K G) (hd : d ∈ D)
    (hd1 : d ≠ 1) (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) :
    commSub (commSub ⊤ (swapPair K d)) (Subgroup.zpowers d) = commSub ⊤ (Subgroup.zpowers d) ∧
      commSub ⊤ (Subgroup.zpowers d) ≤ commSub ⊤ (swapPair K d) := by
  have hdG : d ∈ G := S.DG hd
  have hd2pow : d ^ 2 = 1 := S.elem.2 d hd
  have hd2 : d * d = 1 := by rw [← pow_two]; exact hd2pow
  have hswap := swap_comm_eq_self hK hdG hd2pow hKd
  have hRX : ∀ r ∈ swapPair K d, ∀ x ∈ X, r * x = x * r := by
    intro r hr x hx
    have hK_Z : K ≤ Subgroup.centralizer (X : Set (MulAut W)) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Std139.component_commutes_X S hK k hk y hy).symm
    have hKd_Z : K.map (MulAut.conj d).toMonoidHom ≤
        Subgroup.centralizer (X : Set (MulAut W)) := by
      rintro _ ⟨k₀, hk₀, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : Commute k₀ y := Std139.component_commutes_X S hK k₀ hk₀ y hy
      have h2 : Commute d y := S.DX d hd y hy
      have h3 : Commute (MulAut.conj d k₀) y := by
        rw [MulAut.conj_apply]
        exact (h2.mul_left h1).mul_left h2.inv_left
      exact h3.eq.symm
    have hsup := sup_le hK_Z hKd_Z
    exact (Subgroup.mem_centralizer_iff.mp (hsup hr) x hx).symm
  have hR1 : swapPair K d ≠ ⊥ := by
    intro hbot
    have hK1 : K ≠ ⊥ := by
      intro hKbot
      exact hKd (by rw [hKbot, Subgroup.map_bot])
    exact hK1 (le_bot_iff.mp (hbot ▸ le_sup_left))
  have hdR : (swapPair K d).map (MulAut.conj d).toMonoidHom = swapPair K d := by
    change conjBy d (K ⊔ conjBy d K) = K ⊔ conjBy d K
    rw [w1369_conjBy_sup, conjBy_conjBy, hd2, conjBy_one, sup_comm]
  exact Std139.lemmaB hw2 S hd hd1 hRX hswap.2 hR1 hdR hswap.1

theorem Std139.moved_comm_le (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} {d : MulAut W} (hK : IsComponentOf K G) (hd : d ∈ D)
    (hd1 : d ≠ 1) (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) :
    commSub ⊤ (Subgroup.zpowers d) ≤ commSub ⊤ (swapPair K d) :=
  (w1369_lemmaB_swap hw2 S hK hd hd1 hKd).2

theorem Std139.moved_normalized (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} {d : MulAut W} (hK : IsComponentOf K G) (hd : d ∈ D)
    (hd1 : d ≠ 1) (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) (h134 : Conc4_134 G K d) :
    ∀ e ∈ D, (swapPair K d).map (MulAut.conj e).toMonoidHom = swapPair K d := by
  intro e he
  have hdG : d ∈ G := S.DG hd
  have heG : e ∈ G := S.DG he
  have hd2 : d * d = 1 := by rw [← pow_two]; exact S.elem.2 d hd
  have he2 : e * e = 1 := by rw [← pow_two]; exact S.elem.2 e he
  have hde : e * d = d * e := S.elem.1 e he d hd
  by_cases hKeK : K.map (MulAut.conj e).toMonoidHom = K
  · have hKe' : conjBy e K = K := by simpa [conjBy] using hKeK
    have h2 : conjBy e (conjBy d K) = conjBy d K := by
      rw [conjBy_conjBy, hde, ← conjBy_conjBy d e K, hKe']
    have hgoal : (swapPair K d).map (MulAut.conj e).toMonoidHom = swapPair K d := by
      change conjBy e (K ⊔ conjBy d K) = K ⊔ conjBy d K
      rw [w1369_conjBy_sup, hKe', h2]
    exact hgoal
  · by_cases hKeKd : K.map (MulAut.conj e).toMonoidHom =
        K.map (MulAut.conj d).toMonoidHom
    · have hKeKd' : conjBy e K = conjBy d K := by simpa [conjBy] using hKeKd
      have h2 : conjBy e (conjBy d K) = K := by
        rw [conjBy_conjBy, hde, ← conjBy_conjBy d e K, hKeKd', conjBy_conjBy, hd2,
          conjBy_one]
      have hgoal : (swapPair K d).map (MulAut.conj e).toMonoidHom = swapPair K d := by
        change conjBy e (K ⊔ conjBy d K) = K ⊔ conjBy d K
        rw [w1369_conjBy_sup, hKeKd', h2, sup_comm]
      exact hgoal
    · exfalso
      let Y' : Subgroup (MulAut W) := swapPair K d
      let U : Subgroup W := commSub ⊤ Y'
      let Ke : Subgroup (MulAut W) := K.map (MulAut.conj e).toMonoidHom
      let Kd : Subgroup (MulAut W) := K.map (MulAut.conj d).toMonoidHom
      let Ked : Subgroup (MulAut W) := Ke.map (MulAut.conj d).toMonoidHom
      let Ye : Subgroup (MulAut W) := Ke ⊔ Ked
      have hKe_comp : IsComponentOf Ke G :=
        CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK heG
      have hKd_comp : IsComponentOf Kd G :=
        CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK hdG
      have hKed_comp : IsComponentOf Ked G :=
        CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hKe_comp hdG
      have hY'eq : Y' = K ⊔ Kd := rfl
      have hYeeq : conjBy e Y' = Ye := by
        rw [show Y' = K ⊔ Kd from rfl, w1369_conjBy_sup]
        change conjBy e K ⊔ conjBy e (conjBy d K) = Ke ⊔ Ked
        rw [conjBy_conjBy, hde, ← conjBy_conjBy d e K]
        rfl
      have hKe_ne_K : Ke ≠ K := by simpa [Ke] using hKeK
      have hKe_ne_Kd : Ke ≠ Kd := by simpa [Ke, Kd] using hKeKd
      have hKed_ne_K : Ked ≠ K := by
        intro h
        apply hKe_ne_Kd
        have h5 : conjBy d Ked = conjBy d K := by rw [h]
        have h6 : conjBy d Ked = Ke := by
          change conjBy d (conjBy d Ke) = Ke
          rw [conjBy_conjBy, hd2, conjBy_one]
        rw [h6] at h5
        exact h5
      have hKed_ne_Kd : Ked ≠ Kd := by
        intro h
        apply hKe_ne_K
        have h5 : conjBy d Ked = conjBy d Kd := by rw [h]
        have h6 : conjBy d Ked = Ke := by
          change conjBy d (conjBy d Ke) = Ke
          rw [conjBy_conjBy, hd2, conjBy_one]
        have h7 : conjBy d Kd = K := by
          change conjBy d (conjBy d K) = K
          rw [conjBy_conjBy, hd2, conjBy_one]
        rw [h6, h7] at h5
        exact h5
      have hcomm : ⁅Y', Ye⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        rw [show Y' = K ⊔ Kd from hY'eq]
        refine sup_le ?_ ?_
        · rw [Subgroup.le_centralizer_iff]
          rw [show Ye = Ke ⊔ Ked from rfl]
          refine sup_le ?_ ?_
          · intro b hb
            rw [Subgroup.mem_centralizer_iff]
            intro k hk
            exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hK hKe_comp
              (Ne.symm hKe_ne_K) hk hb
          · intro b hb
            rw [Subgroup.mem_centralizer_iff]
            intro k hk
            exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hK hKed_comp
              (Ne.symm hKed_ne_K) hk hb
        · rw [Subgroup.le_centralizer_iff]
          rw [show Ye = Ke ⊔ Ked from rfl]
          refine sup_le ?_ ?_
          · intro b hb
            rw [Subgroup.mem_centralizer_iff]
            intro k hk
            exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hKd_comp hKe_comp
              (Ne.symm hKe_ne_Kd) hk hb
          · intro b hb
            rw [Subgroup.mem_centralizer_iff]
            intro k hk
            exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hKd_comp hKed_comp
              (Ne.symm hKed_ne_Kd) hk hb
      have hYe_perf : ⁅Ye, Ye⁆ = Ye := by
        rw [show Ye = Ke ⊔ Ked from rfl]
        apply le_antisymm
        · simpa [sup_idem] using Subgroup.commutator_le_sup (Ke ⊔ Ked) (Ke ⊔ Ked)
        · refine sup_le ?_ ?_
          · haveI : Group.IsPerfect ↥Ke := ⟨hKe_comp.2.2.1⟩
            calc Ke = ⁅Ke, Ke⁆ := (Subgroup.commutator_eq_self).symm
              _ ≤ ⁅Ke ⊔ Ked, Ke ⊔ Ked⁆ :=
                Subgroup.commutator_mono le_sup_left le_sup_left
          · haveI : Group.IsPerfect ↥Ked := ⟨hKed_comp.2.2.1⟩
            calc Ked = ⁅Ked, Ked⁆ := (Subgroup.commutator_eq_self).symm
              _ ≤ ⁅Ke ⊔ Ked, Ke ⊔ Ked⁆ :=
                Subgroup.commutator_mono le_sup_right le_sup_right
      have hYM : StableUnder Y' U := fun y hy u hu =>
        w1369_stableUnder_commSub_self Y' y hy u hu
      have hcomm' : ∀ y ∈ Y', ∀ b ∈ Ye, y * b = b * y := by
        intro y hy b hb
        have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
        exact (Subgroup.mem_centralizer_iff.mp (hle hy) b hb).symm
      have hYR : StableUnder Ye U :=
        CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := Y') (B := Ye) (M := ⊤)
          hcomm' (fun _ _ _ _ => Subgroup.mem_top _)
      have hsel := Std139.selection hw2 S hK hd hd1 hKd h134
      have hNat : NatTensor Y' U ⊥ 2 2 := by
        change NatTensor (swapPair K d) (commSub ⊤ (swapPair K d)) ⊥ 2 2
        exact hsel.2
      have hirr0 := natTensor_isIrrOn (d := 2) (a := 2) (by norm_num) hNat
      have hirr : IsIrrOn Y' U (U ⊓ fixV Y') := by
        rw [inf_comm, hirr0.2]
        exact hirr0.1
      have hW2 : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hw2 w
      have hschur := s13_schur_perfect hW2 Y' Ye hcomm hYe_perf U hYM hYR hirr
      have hUbot : U ⊓ fixV Y' = ⊥ := by rw [inf_comm]; exact hirr0.2
      have hcommUYe : commSub U Ye = ⊥ :=
        le_bot_iff.mp (hschur.trans (le_of_eq hUbot))
      have hUfixYe : U ≤ fixV Ye := commSub_eq_bot_iff.mp hcommUYe
      have hmoved : commSub ⊤ (Subgroup.zpowers d) ≤ U :=
        (w1369_lemmaB_swap hw2 S hK hd hd1 hKd).2
      have he_inv : ∀ w ∈ commSub ⊤ (Subgroup.zpowers d),
          e w ∈ commSub ⊤ (Subgroup.zpowers d) :=
        CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := Subgroup.zpowers d)
          (B := Subgroup.zpowers e) (M := ⊤)
          (fun y hy b hb => by
            obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
            obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
            exact ((Commute.zpow_left (show Commute d e from hde.symm) i).zpow_right j).eq)
          (fun _ _ _ _ => Subgroup.mem_top _) e (Subgroup.mem_zpowers e)
      have hew_fix : ∀ w ∈ commSub ⊤ (Subgroup.zpowers d), e w ∈ fixV Y' := by
        intro w hw
        have hwU : w ∈ U := hmoved hw
        rw [mem_fixV]
        intro y hy
        have hye : e * y * e⁻¹ ∈ Ye := by
          rw [← hYeeq]
          exact mem_conjBy_of_mem hy
        have h1 : (e * y * e⁻¹) w = w :=
          (mem_fixV.mp (hUfixYe hwU)) (e * y * e⁻¹) hye
        have h1' : e (y (e⁻¹ w)) = w := by
          simpa [MulAut.mul_apply] using h1
        have h2 : y (e⁻¹ w) = e w := by
          have h3 := congrArg e h1'
          have hee : e (e (y (e⁻¹ w))) = y (e⁻¹ w) := by
            rw [← MulAut.mul_apply, he2, MulAut.one_apply]
          rwa [hee] at h3
        rw [show e⁻¹ = e from inv_eq_of_mul_eq_one_right he2] at h2
        exact h2
      have hWd_bot : commSub ⊤ (Subgroup.zpowers d) = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        rw [Subgroup.mem_bot]
        have hew_fix' : e w ∈ fixV Y' := hew_fix w hw
        have hew_mem : e w ∈ commSub ⊤ (Subgroup.zpowers d) := he_inv w hw
        have hew_U : e w ∈ U := hmoved hew_mem
        have hew_inf : e w ∈ U ⊓ fixV Y' := ⟨hew_U, hew_fix'⟩
        rw [hUbot] at hew_inf
        have hew1 : e w = 1 := Subgroup.mem_bot.mp hew_inf
        have hwe : e (e w) = w := by rw [← MulAut.mul_apply, he2, MulAut.one_apply]
        rw [hew1] at hwe
        simpa using hwe.symm
      have hrk : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 2 :=
        (Std139.commSub_axis hw2 S hd hd1).1
      rw [hWd_bot, rk_bot] at hrk
      exact absurd hrk (by norm_num)

theorem Std139.moved_faithful (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} {d : MulAut W} (hK : IsComponentOf K G) (hd : d ∈ D)
    (hd1 : d ≠ 1) (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) (h134 : Conc4_134 G K d) :
    ∀ e ∈ D, (∀ y ∈ swapPair K d, e * y = y * e) → e = 1 := by
  intro e he hcent
  by_contra he1
  have hdG : d ∈ G := S.DG hd
  have hd2 : d ^ 2 = 1 := S.elem.2 d hd
  have hYfix : fixV (Subgroup.zpowers e) = Y := Std139.fixV_eq_axis hw2 S he he1
  have hY'stab : StableUnder (swapPair K d) Y := by
    intro y hy w hw
    rw [← hYfix] at hw ⊢
    rw [mem_fixV_zpowers_iff] at hw ⊢
    calc e (y w) = (e * y) w := rfl
      _ = (y * e) w := by rw [hcent y hy]
      _ = y (e w) := rfl
      _ = y w := by rw [hw]
  have hY'le : swapPair K d ≤ stabSub Y := w1369_stableUnder_iff_le_stabSub hY'stab
  let ρ : ↥(swapPair K d) →* MulAut (W ⧸ Y) :=
    (quotHom Y).comp (Subgroup.inclusion hY'le)
  have hQp : IsPGroup 2 (W ⧸ Y) := (isPGroup_two_of_sq_eq_one hw2).to_quotient Y
  have hcardQ : Nat.card (W ⧸ Y) = Y.index := (Subgroup.index_eq_card (H := Y)).symm
  have hrkQ : rk (W ⧸ Y) = 2 := by
    unfold rk
    rw [hcardQ]
    simpa [rkIdx] using S.Yrk
  have hcard4 : Nat.card (W ⧸ Y) = 4 := by
    rw [card_eq_two_pow_of_isPGroup hQp, hrkQ]
    norm_num
  have hmoved := w1369_lemmaB_swap hw2 S hK hd hd1 hKd
  have hY'perf : ⁅swapPair K d, swapPair K d⁆ = swapPair K d :=
    (swap_comm_eq_self hK hdG hd2 hKd).2
  haveI : Group.IsPerfect ↥(swapPair K d) := Subgroup.isPerfect_iff.mpr hY'perf
  haveI : Group.IsSolvable (Equiv.Perm (W ⧸ Y)) :=
    Equiv.Perm.isSolvable (le_of_eq hcard4)
  haveI : Group.IsSolvable (MulAut (W ⧸ Y)) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm (W ⧸ Y)) (by
      intro a b hab
      exact MulEquiv.ext fun x => congrArg (fun f : Equiv.Perm (W ⧸ Y) => f x) hab)
  haveI : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
  haveI : Group.IsSolvable ↥ρ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective ρ.range)
  have hρ1 : ρ = 1 := by
    have hsub : Subsingleton ↥ρ.range := by
      rw [← not_nontrivial_iff_subsingleton]
      intro hnt
      haveI : Nontrivial ↥ρ.range := hnt
      exact (Group.IsPerfect.not_isSolvable (G := ↥ρ.range)) inferInstance
    haveI : Subsingleton ↥ρ.range := hsub
    ext y x
    have h2 : (⟨ρ y, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ : ↥ρ.range) = 1 :=
      Subsingleton.elim _ _
    have h3 : ρ y = 1 := congrArg Subtype.val h2
    exact congrArg (fun f : MulAut (W ⧸ Y) => f x) h3
  have hUsubY : commSub ⊤ (swapPair K d) ≤ Y := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨y, hy, w, -, rfl⟩
    have hρy : ρ ⟨y, hy⟩ = 1 := by rw [hρ1]; rfl
    have hqh : quotHom Y ⟨y, hY'le hy⟩ = 1 := by
      simpa [ρ, Subgroup.inclusion] using hρy
    have h2 := congrArg (fun ψ : MulAut (W ⧸ Y) => ψ (QuotientGroup.mk w)) hqh
    rw [quotHom_mk, MulAut.one_apply] at h2
    exact (mk_eq_mk_iff (y w) w).mp h2
  have hUfixd : commSub ⊤ (swapPair K d) ≤ fixV (Subgroup.zpowers d) := by
    rw [Std139.fixV_eq_axis hw2 S hd hd1]
    exact hUsubY
  have hcommUd : commSub (commSub ⊤ (swapPair K d)) (Subgroup.zpowers d) = ⊥ :=
    commSub_eq_bot_iff.mpr hUfixd
  have hWdbot : commSub ⊤ (Subgroup.zpowers d) = ⊥ := by
    rw [← hmoved.1, hcommUd]
  have hrk : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 2 :=
    (Std139.commSub_axis hw2 S hd hd1).1
  rw [hWdbot, rk_bot] at hrk
  exact absurd hrk (by norm_num)

theorem Std139.moved_D0 (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} {d : MulAut W} (hK : IsComponentOf K G) (hd : d ∈ D)
    (hd1 : d ≠ 1) (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) (h134 : Conc4_134 G K d) :
    D ⊓ centSub (commSub ⊤ (swapPair K d)) = ⊥ := by
  have hsel := Std139.selection hw2 S hK hd hd1 hKd h134
  have hNat : NatTensor (swapPair K d) (commSub ⊤ (swapPair K d)) ⊥ 2 2 := hsel.2
  have hY'faith : swapPair K d ⊓ centSub (commSub ⊤ (swapPair K d)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    exact eq_one_of_fix_of_natTensor hNat hy.1 (fun u hu => (mem_centSub.mp hy.2) u hu)
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  apply Std139.moved_faithful hw2 S hK hd hd1 hKd h134 e he.1
  intro y hy
  have hnorm : (swapPair K d).map (MulAut.conj e).toMonoidHom = swapPair K d :=
    Std139.moved_normalized hw2 S hK hd hd1 hKd h134 e he.1
  have hmem : e * y * e⁻¹ ∈ swapPair K d := by
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom hy
    rwa [hnorm] at h1
  have hcomm_mem :
      e * y * e⁻¹ * y⁻¹ ∈ swapPair K d ⊓ centSub (commSub ⊤ (swapPair K d)) := by
    constructor
    · exact (swapPair K d).mul_mem hmem ((swapPair K d).inv_mem hy)
    · show e * y * e⁻¹ * y⁻¹ ∈ centSub (commSub ⊤ (swapPair K d))
      rw [mem_centSub]
      intro u hu
      have hyu : y⁻¹ u ∈ commSub ⊤ (swapPair K d) :=
        w1369_stableUnder_commSub_self (swapPair K d) y⁻¹ ((swapPair K d).inv_mem hy) u hu
      have heinv : e⁻¹ ∈ centSub (commSub ⊤ (swapPair K d)) := Subgroup.inv_mem _ he.2
      calc (e * y * e⁻¹ * y⁻¹) u
          = e (y (e⁻¹ (y⁻¹ u))) := by simp [MulAut.mul_apply]
        _ = e (y (y⁻¹ u)) := by rw [mem_centSub.mp heinv (y⁻¹ u) hyu]
        _ = e u := by rw [MulAut.apply_inv_self]
        _ = u := mem_centSub.mp he.2 u hu
  rw [hY'faith] at hcomm_mem
  have h1 : e * y * e⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.mp hcomm_mem
  calc e * y = (e * y * e⁻¹ * y⁻¹) * (y * e) := by group
    _ = y * e := by rw [h1, one_mul]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
