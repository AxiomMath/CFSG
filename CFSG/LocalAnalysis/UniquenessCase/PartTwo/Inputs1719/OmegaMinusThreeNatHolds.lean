module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaMinusThreeNat
public import CFSG.Quasithin.Background.OddInverted
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusOddRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoordsRestrict
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusIrr
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.InvertedAbelian
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.E3
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.RankThreeUC
open scoped Matrix

theorem k_O6m4_ThreeNatM_holds : K_O6m4_ThreeNatM := by
  intro W _ _ hsq X Y hXY hYN hX hsum
  classical
  obtain ⟨I, -, hind, hsup, hNat⟩ := hsum
  have hindI : iSupIndep I := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, ← le_bot_iff]
    simpa using hind i
  have hsupI : (⨆ i : Fin 3, I i) = ⊤ := by simpa using hsup
  have hcomm : Pairwise fun i j : Fin 3 => ∀ x y : W, x ∈ I i → y ∈ I j → Commute x y :=
    fun _ _ _ x y _ _ => mul_comm x y
  let e : (∀ i : Fin 3, ↥(I i)) ≃* ↥(⊤ : Subgroup W) :=
    (MonoidHom.ofInjective
      (Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hindI)).trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.noncommPiCoprod_range, hsupI]))
  have he : ∀ f, ((e f : ↥(⊤ : Subgroup W)) : W) = ∏ i, (f i : W) := by
    intro f
    change Subgroup.noncommPiCoprod hcomm f = _
    rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  have hIirr (i : Fin 3) :
      ∀ t : MulAut W, (∀ x ∈ X, x * t = t * x) →
        fixV (Subgroup.zpowers t) ⊓ I i = ⊥ ∨
          fixV (Subgroup.zpowers t) ⊓ I i = I i := by
    obtain ⟨-, K, hKf, hKfin, b, c, hKc, hpoly, hreal⟩ := hNat i
    let _ : Fintype K := Fintype.ofFinite K
    have _ : CharP K 2 :=
      CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 2) hKc
    let Γ := StatedOmega (StatedQuadMinus 3 K b c)
    obtain ⟨π, hπ⟩ := hreal
    let πΓ : ↥Γ →* ↥X := π
    have hπΓ : (FFModel.nat Γ).RealizesVia X (I i) ⊥ πΓ := hπ
    obtain ⟨H', π', hH'eq, hπ'val, hπ'real⟩ := exists_realizesVia_restrict hπΓ
    let hKA : ∀ a ∈ X, ∀ w ∈ I i, a w ∈ I i :=
      fun a ha w hw => hπ.2.2.2.1 ⟨a, ha⟩ w hw
    let f : ↥X →* MulAut ↥(I i) :=
      CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hKA
    have hH'eq' : H' = f.range := hH'eq
    have hπ'val' : ∀ γ : ↥Γ, ((π' γ : ↥H') : MulAut ↥(I i)) = f (πΓ γ) := hπ'val
    have hN' : NatOmegaMinus H' ⊤ ⊥ 6 2 :=
      ⟨⟨3, by norm_num⟩, K, hKf, hKfin, b, c, hKc, hpoly, ⟨π', hπ'real⟩⟩
    have hirrOn : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn H' :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.k_Omega6Minus_irr H' 2 hN'
    intro t htc
    let U : Subgroup W := fixV (Subgroup.zpowers t) ⊓ I i
    have hUle : U ≤ I i := inf_le_right
    let U' : Subgroup ↥(I i) := U.subgroupOf (I i)
    have hU'inv : ∀ h ∈ H', ∀ u ∈ U', h u ∈ U' := by
      intro h hh u hu
      rw [hH'eq'] at hh
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hh
      rw [Subgroup.mem_subgroupOf] at hu ⊢
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
        have hcomm : (a : MulAut W) * t = t * (a : MulAut W) := htc a a.2
        change t ((a : MulAut W) ((u : ↥(I i)) : W)) =
          (a : MulAut W) ((u : ↥(I i)) : W)
        calc t ((a : MulAut W) ((u : ↥(I i)) : W))
            = (t * (a : MulAut W)) ((u : ↥(I i)) : W) := by rw [MulAut.mul_apply]
          _ = ((a : MulAut W) * t) ((u : ↥(I i)) : W) := by rw [← hcomm]
          _ = (a : MulAut W) (t ((u : ↥(I i)) : W)) := by rw [MulAut.mul_apply]
          _ = (a : MulAut W) ((u : ↥(I i)) : W) := by
              rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp hu.1]
      · rw [CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply hKA a u]
        exact hπ.2.2.2.1 a (u : W) hu.2
    rcases hirrOn U' hU'inv with h | h
    · left
      have hdisj : Disjoint U (I i) := (Subgroup.subgroupOf_eq_bot).mp h
      have hinf : U ⊓ I i = ⊥ := disjoint_iff.mp hdisj
      rwa [inf_eq_left.mpr hUle] at hinf
    · right
      have hle : I i ≤ U := (Subgroup.subgroupOf_eq_top).mp h
      exact le_antisymm hUle hle
  have hIbasic (i : Fin 3) :
      Nat.card (I i) = 2 ^ 12 ∧
        (∀ y ∈ X, y ≠ 1 → Odd (orderOf y) →
          rk ↥(fixV (Subgroup.zpowers y) ⊓ I i) + 4 ≤ rk ↥(I i)) := by
    obtain ⟨-, K, hKf, hKfin, b, c, hKc, hpoly, hreal⟩ := hNat i
    let _ : Fintype K := Fintype.ofFinite K
    have _ : CharP K 2 :=
      CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 2) hKc
    let ι := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2
    let Γ := StatedOmega (StatedQuadMinus 3 K b c)
    obtain ⟨π, hπ⟩ := hreal
    let πΓ : ↥Γ →* ↥X := π
    have hπΓ : (FFModel.nat Γ).RealizesVia X (I i) ⊥ πΓ := hπ
    obtain ⟨H', π', hH'eq, hπ'val, hπ'real⟩ := exists_realizesVia_restrict hπΓ
    let π'Γ : ↥Γ →* ↥H' := π'
    let hKA : ∀ a ∈ X, ∀ w ∈ I i, a w ∈ I i :=
      fun a ha w hw => hπ.2.2.2.1 ⟨a, ha⟩ w hw
    let f : ↥X →* MulAut ↥(I i) :=
      CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hKA
    have hπ'val' : ∀ γ : ↥Γ, ((π'Γ γ : ↥H') : MulAut ↥(I i)) = f (πΓ γ) := hπ'val
    obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia Γ hπ'real
    have he' : ∀ (γ : ↥Γ) (v : ↥(I i)),
        e (((π'Γ γ : ↥H') : MulAut ↥(I i)) v) = natAct Γ γ (e v) := fun γ v =>
      he γ v
    have hcard : Nat.card (I i) = 2 ^ 12 := by
      have h1 : Nat.card ↥(I i) = Nat.card (StdMod ι K) := Nat.card_congr e.toEquiv
      rw [h1, CFSG.Quasithin.H.card_stdMod, hKc,
        show Fintype.card ι = 6 by simp [ι]]
      norm_num
    refine ⟨hcard, ?_⟩
    intro y hyX hy1 hyodd
    have hπΓinj : Function.Injective πΓ := by
      have hinj' : Function.Injective π'Γ :=
        CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful
          (CFSG.Quasithin.FFModel.nat_faithful Γ) hπ'real
      intro a b hab
      apply hinj'
      apply Subtype.ext
      rw [hπ'val' a, hπ'val' b, hab]
    obtain ⟨γ, hγ⟩ := hπ.1 ⟨y, hyX⟩
    let γΓ : ↥Γ := γ
    have hγΓ : πΓ γΓ = ⟨y, hyX⟩ := hγ
    let g : GL ι K := (γΓ : GL ι K)
    have hg1 : g ≠ 1 := by
      intro hg
      have hγ1 : γΓ = 1 := Subtype.ext hg
      have hyeq : (⟨y, hyX⟩ : ↥X) = 1 := by
        rw [← hγΓ, hγ1, map_one]
      exact hy1 (congrArg Subtype.val hyeq)
    have hg_ord : orderOf g = orderOf y := by
      have h1 : orderOf g = orderOf γΓ := Subgroup.orderOf_coe γΓ
      have h2 : orderOf γΓ = orderOf (⟨y, hyX⟩ : ↥X) :=
        (orderOf_injective πΓ hπΓinj γΓ).symm.trans (by rw [hγΓ])
      have h3 : orderOf (⟨y, hyX⟩ : ↥X) = orderOf y :=
        (Subgroup.orderOf_coe ⟨y, hyX⟩).symm
      rw [h1, h2, h3]
    have hoddg : Odd (orderOf g) := hg_ord ▸ hyodd
    have hbound :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.two_mul_le_rkIdx_of_odd_omegaMinus
        hpoly hKc γΓ.2 hg1 hoddg
    let y_i : MulAut ↥(I i) := (π'Γ γΓ : ↥H')
    have hcongr : rkIdx (fixV (Subgroup.zpowers (matAut g))) =
        rkIdx (fixV (Subgroup.zpowers y_i)) := by
      have hmap : (Subgroup.zpowers y_i).map (CFSG.Quasithin.H.congrHom e) =
          Subgroup.zpowers (matAut g) := by
        rw [MonoidHom.map_zpowers]
        congr 1
        ext x
        rw [CFSG.Quasithin.H.congrHom_apply, he' γΓ (e.symm x),
          MulEquiv.apply_symm_apply]
        rfl
      rw [← hmap]
      exact CFSG.Quasithin.H.rkIdx_fixV_map_congrHom e (Subgroup.zpowers y_i)
    have hyi_apply : ∀ u : ↥(I i), ((y_i u : ↥(I i)) : W) = y (u : W) := by
      intro u
      have h1 : y_i = f (πΓ γΓ) := hπ'val' γΓ
      rw [h1, hγΓ]
      exact CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply
        hKA ⟨y, hyX⟩ u
    have hmapfix : (fixV (Subgroup.zpowers y_i)).map (I i).subtype =
        fixV (Subgroup.zpowers y) ⊓ I i := by
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine Subgroup.mem_inf.mpr ⟨?_, u.2⟩
        exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr (by
          have hu' : y_i u = u :=
            CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp hu
          calc y (u : W) = ((y_i u : ↥(I i)) : W) := (hyi_apply u).symm
            _ = (u : W) := by rw [hu'])
      · intro hw
        rw [Subgroup.mem_inf] at hw
        refine ⟨⟨w, hw.2⟩, ?_, rfl⟩
        exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr (by
          apply Subtype.ext
          rw [hyi_apply]
          exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp hw.1)
    have hrkfix : rk ↥(fixV (Subgroup.zpowers y_i)) =
        rk ↥(fixV (Subgroup.zpowers y) ⊓ I i) := by
      rw [← hmapfix]
      unfold rk
      rw [Subgroup.card_map_of_injective (I i).subtype_injective]
    have hri := rk_add_rkIdx (G := ↥(I i))
      (H := fixV (Subgroup.zpowers y_i))
    have hb : 4 ≤ rkIdx (fixV (Subgroup.zpowers y_i)) := by
      rw [← hcongr]
      exact hbound
    omega
  have hO2 : ∀ P : Subgroup (MulAut W), P ≤ X →
      (∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P) → IsPGroup 2 P → P = ⊥ := by
    obtain ⟨-, K, hKf, hKfin, b, c, hKc, hpoly, hreal⟩ := hNat 0
    have _ : CharP K 2 :=
      CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 2) hKc
    let Γ := StatedOmega (StatedQuadMinus 3 K b c)
    obtain ⟨π, hπ⟩ := hreal
    let πΓ : ↥Γ →* ↥X := π
    have hπΓ : (FFModel.nat Γ).RealizesVia X (I 0) ⊥ πΓ := hπ
    obtain ⟨H', π', hH'eq, hπ'val, hπ'real⟩ := exists_realizesVia_restrict hπΓ
    let π'Γ : ↥Γ →* ↥H' := π'
    let hKA : ∀ a ∈ X, ∀ w ∈ I 0, a w ∈ I 0 :=
      fun a ha w hw => hπ.2.2.2.1 ⟨a, ha⟩ w hw
    let f : ↥X →* MulAut ↥(I 0) :=
      CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hKA
    have hπ'val' : ∀ γ : ↥Γ, ((π'Γ γ : ↥H') : MulAut ↥(I 0)) = f (πΓ γ) := hπ'val
    have hinj' : Function.Injective π'Γ :=
      CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful
        (CFSG.Quasithin.FFModel.nat_faithful Γ) hπ'real
    have hinj : Function.Injective πΓ := by
      intro a b hab
      apply hinj'
      apply Subtype.ext
      rw [hπ'val' a, hπ'val' b, hab]
    let eΓ : ↥Γ ≃* ↥X := MulEquiv.ofBijective πΓ ⟨hinj, hπ.1⟩
    obtain ⟨hΓsimple, -, hΓnonab⟩ :=
      CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
        (n := 3) (Or.inr rfl) hpoly
    have _ : IsSimpleGroup ↥X :=
      @MulEquiv.isSimpleGroup ↥X _ ↥Γ _ hΓsimple eΓ.symm
    have hXnonab : ¬ ∀ x y : ↥X, x * y = y * x := by
      intro h
      apply hΓnonab
      intro a b
      have h' : eΓ a * eΓ b = eΓ b * eΓ a := h (eΓ a) (eΓ b)
      exact eΓ.injective (by rw [map_mul, map_mul, h'])
    intro P hPX hPnorm hP2
    have hXleN : X ≤ Subgroup.normalizer (P : Set (MulAut W)) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro p
      constructor
      · intro hp
        exact hPnorm x hx p hp
      · intro hp
        have h := hPnorm x⁻¹ (X.inv_mem hx) (x * p * x⁻¹) hp
        have h2 : x⁻¹ * (x * p * x⁻¹) * x⁻¹⁻¹ = p := by group
        rwa [h2] at h
    have hPn : (P.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPX).mpr hXleN
    have hP2' : IsPGroup 2 (P.subgroupOf X) := hP2.comap_subtype
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf X) with h | h
    · have hdisj : Disjoint P X := (Subgroup.subgroupOf_eq_bot).mp h
      have hinf : P ⊓ X = ⊥ := disjoint_iff.mp hdisj
      rwa [inf_eq_left.mpr hPX] at hinf
    · exfalso
      have hXP : X ≤ P := (Subgroup.subgroupOf_eq_top).mp h
      have hPXeq : P = X := le_antisymm hPX hXP
      have hX2 : IsPGroup 2 X := hPXeq ▸ hP2
      have _ : Group.IsNilpotent ↥X := IsPGroup.isNilpotent hX2
      have hsolv : Group.IsSolvable ↥X := IsNilpotent.to_isSolvable
      exact hXnonab fun x y => IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y
  have hrkI : ∀ i : Fin 3, rk ↥(I i) = 12 := by
    intro i
    unfold rk
    rw [(hIbasic i).1, padicValNat.prime_pow]
  have hinv : ∀ t ∈ Y, orderOf t = 2 →
      6 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    intro t htY ht2
    by_cases htc : t ∈ Subgroup.centralizer (X : Set (MulAut W))
    · rw [Subgroup.mem_centralizer_iff] at htc
      have hex : ∃ i : Fin 3, fixV (Subgroup.zpowers t) ⊓ I i = ⊥ := by
        by_contra hcon
        push Not at hcon
        have hall : ∀ i : Fin 3, I i ≤ fixV (Subgroup.zpowers t) := by
          intro i
          rcases hIirr i t (fun x hx => htc x hx) with h | h
          · exact absurd h (hcon i)
          · rw [← h]
            exact inf_le_left
        have htop : ⊤ ≤ fixV (Subgroup.zpowers t) := by
          rw [← hsupI]
          exact iSup_le hall
        have ht1 : t = 1 := by
          ext w
          exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp
            (htop (Subgroup.mem_top w))
        have h1 : orderOf (1 : MulAut W) = 2 := by rw [← ht1]; exact ht2
        simp at h1
      obtain ⟨i, hi⟩ := hex
      have hI12 : (12 : ℕ) ≤ rk ↥(I i) := by rw [hrkI i]
      have hle : rk ↥(fixV (Subgroup.zpowers t)) + rk ↥(I i) ≤ rk W := by
        have h1 : rk ↥(fixV (Subgroup.zpowers t) ⊔ I i) =
            rk ↥(fixV (Subgroup.zpowers t)) + rk ↥(I i) := by
          have h2 := rk_sup_add_rk_inf (fixV (Subgroup.zpowers t)) (I i)
          rw [hi, rk_bot, add_zero] at h2
          exact h2
        rw [← h1]
        have htop := rk_mono (G := W) (H := fixV (Subgroup.zpowers t) ⊔ I i) (K := ⊤) le_top
        rwa [rk_top] at htop
      have h3 := rk_add_rkIdx (G := W) (H := fixV (Subgroup.zpowers t))
      omega
    · have htN : t ∈ Subgroup.normalizer (X : Set (MulAut W)) := hYN htY
      obtain ⟨y, hyX, hy1, hyodd, hbnd⟩ :=
        CFSG.Quasithin.exists_odd_of_not_mem_centralizer hsq hO2 htN ht2 htc
      have hyinv : ∀ i, ∀ w ∈ I i, y w ∈ I i := by
        intro i
        obtain ⟨-, K, hKf, hKfin, b, c, hKc, hpoly, hreal⟩ := hNat i
        obtain ⟨π, hπ⟩ := hreal
        exact hπ.2.2.2.1 ⟨y, hyX⟩
      have hfixcard : Nat.card ↥(fixV (Subgroup.zpowers y)) =
          ∏ i, Nat.card ↥(fixV (Subgroup.zpowers y) ⊓ I i) := by
        rw [← CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.card_fixV_inf_eq_prod e he hyinv,
          inf_top_eq]
      have hWcard : Nat.card W = ∏ i, Nat.card (I i) := by
        rw [← Subgroup.card_top (G := W)]
        exact CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.card_eq_prod_of_equiv e
      have hrkfix : rk ↥(fixV (Subgroup.zpowers y)) =
          rk ↥(fixV (Subgroup.zpowers y) ⊓ I 0) +
            rk ↥(fixV (Subgroup.zpowers y) ⊓ I 1) +
              rk ↥(fixV (Subgroup.zpowers y) ⊓ I 2) := by
        unfold rk
        rw [hfixcard, Fin.prod_univ_three]
        rw [padicValNat.mul
          (Nat.mul_ne_zero (card_subgroup_pos _).ne' (card_subgroup_pos _).ne')
          (card_subgroup_pos _).ne']
        rw [padicValNat.mul (card_subgroup_pos _).ne' (card_subgroup_pos _).ne']
      have h4096 : padicValNat 2 (2 ^ 12) = 12 := padicValNat.prime_pow 12
      have hrkW : rk W = 12 + 12 + 12 := by
        unfold rk
        rw [hWcard, Fin.prod_univ_three, (hIbasic 0).1, (hIbasic 1).1, (hIbasic 2).1]
        rw [padicValNat.mul (by norm_num) (by norm_num),
          padicValNat.mul (by norm_num) (by norm_num)]
        rw [h4096]
      have hb0 := (hIbasic 0).2 y hyX hy1 hyodd
      have hb1 := (hIbasic 1).2 y hyX hy1 hyodd
      have hb2 := (hIbasic 2).2 y hyX hy1 hyodd
      have h12 : 12 ≤ rkIdx (fixV (Subgroup.zpowers y)) := by
        have h3 := rk_add_rkIdx (G := W) (H := fixV (Subgroup.zpowers y))
        rw [hrkI 0] at hb0
        rw [hrkI 1] at hb1
        rw [hrkI 2] at hb2
        omega
      omega
  unfold E3.mParam
  by_cases hev : Even (Nat.card Y)
  · rw [if_pos hev]
    have hne : {n : ℕ | ∃ t ∈ Y, orderOf t = 2 ∧
        n = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty := by
      obtain ⟨t, ht⟩ :=
        exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.mp hev)
      exact ⟨_, (t : MulAut W), t.2, (Subgroup.orderOf_coe t).trans ht, rfl⟩
    refine le_csInf hne ?_
    rintro n ⟨t, htY, ht2, rfl⟩
    exact hinv t htY ht2
  · rw [if_neg hev]
    have hle : rk ↥(I 0) ≤ rk W := by
      have h := rk_mono (G := W) (H := I 0) (K := ⊤) (le_top : I 0 ≤ ⊤)
      rwa [rk_top] at h
    have h12 : (12 : ℕ) ≤ rk W := by rw [← hrkI 0]; exact hle
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
