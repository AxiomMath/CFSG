module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBGam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def s16n9bCommOn {W : Type*} [CommGroup W] (U : Subgroup W) (φ : MulAut W) :
    Subgroup W :=
  Subgroup.closure {x | ∃ u ∈ U, x = φ u * u⁻¹}

@[expose] def s16n9bGood {W : Type*} [CommGroup W] (X : Subgroup (MulAut W)) (p n N : ℕ) : Prop :=
  ∀ φ ∈ X, (∃ a : ℕ, orderOf φ = 2 ^ a) → rkIdx (fixV (Subgroup.zpowers φ)) ≤ N →
    ∀ U : Subgroup W, rkIdx U ≤ n → ¬ U ≤ fixV (Subgroup.zpowers φ) →
      ∃ z ∈ s16n9bCommOn U φ, z ≠ 1 ∧ ∃ ψ ∈ X, orderOf ψ = p ∧ ψ z = z

@[expose] def s16n9bInvFix {W : Type*} [CommGroup W] (X : Subgroup (MulAut W)) (p N : ℕ) : Prop :=
  ∀ φ ∈ X, (∃ a : ℕ, orderOf φ = 2 ^ a) → rkIdx (fixV (Subgroup.zpowers φ)) ≤ N →
    ∀ z ∈ commV (Subgroup.zpowers φ), z ≠ 1 → ∃ ψ ∈ X, orderOf ψ = p ∧ ψ z = z

section Forms

variable {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)} {p n N : ℕ}

theorem s16n9bGood_mono {n' N' : ℕ} (h : s16n9bGood X p n' N') (hn : n ≤ n') (hN : N ≤ N') :
    s16n9bGood X p n N :=
  fun φ hφ h2 hrk U hU hUφ => h φ hφ h2 (hrk.trans hN) U (hU.trans hn) hUφ

theorem s16n9b_exists_commOn {φ : MulAut W} {U : Subgroup W}
    (h : ¬ U ≤ fixV (Subgroup.zpowers φ)) :
    ∃ z ∈ s16n9bCommOn U φ, z ≠ 1 := by
  by_contra hne
  push Not at hne
  apply h
  intro u hu
  rw [mem_fixV_zpowers_iff_apply]
  have h1 : φ u * u⁻¹ = 1 := hne _ (Subgroup.subset_closure ⟨u, hu, rfl⟩)
  exact mul_inv_eq_one.1 h1

theorem s16n9bGood_of_forall_fix
    (h : ∀ z : W, z ≠ 1 → ∃ ψ ∈ X, orderOf ψ = p ∧ ψ z = z) : s16n9bGood X p n N := by
  intro φ _ _ _ U _ hUφ
  obtain ⟨z, hz, hz1⟩ := s16n9b_exists_commOn hUφ
  exact ⟨z, hz, hz1, h z hz1⟩

theorem s16n9bCommOn_le_commV (φ : MulAut W) (U : Subgroup W) :
    s16n9bCommOn U φ ≤ commV (Subgroup.zpowers φ) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨u, -, rfl⟩
  exact Subgroup.subset_closure ⟨φ, Subgroup.mem_zpowers φ, u, rfl⟩

theorem s16n9bGood_of_invFix (h : s16n9bInvFix X p N) : s16n9bGood X p n N := by
  intro φ hφ h2 hrk U _ hUφ
  obtain ⟨z, hz, hz1⟩ := s16n9b_exists_commOn hUφ
  exact ⟨z, hz, hz1, h φ hφ h2 hrk z (s16n9bCommOn_le_commV φ U hz) hz1⟩

end Forms


section Bridge

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_rkIdx_fixV_le (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : ↥(stabTil V₀ V)) :
    rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹))) ≤
      E3.mQuot V (V ⊓ centralizer ({(g : G)} : Set G)) := by
  classical
  have hKle : intSub V hV (V ⊓ centralizer ({(g : G)} : Set G)) ≤
      (fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹))).comap (mkTil V₀ V hV) := by
    intro x hx
    have hx' : x.val ∈ V ⊓ centralizer ({(g : G)} : Set G) := hx
    have hcomm : x.val * (g : G) = (g : G) * x.val :=
      Subgroup.mem_centralizer_singleton_iff.1 hx'.2
    rw [Subgroup.mem_comap, mem_fixV_zpowers_iff_apply, actTil_mk]
    congr 1
    refine IntMod.val_injective ?_
    rw [actStab_apply_val]
    show (g : G)⁻¹ * x.val * ((g : G)⁻¹)⁻¹ = x.val
    calc (g : G)⁻¹ * x.val * ((g : G)⁻¹)⁻¹ = (g : G)⁻¹ * (x.val * (g : G)) := by group
      _ = (g : G)⁻¹ * ((g : G) * x.val) := by rw [hcomm]
      _ = x.val := by group
  have h1 : (fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹))).index =
      ((fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹))).comap (mkTil V₀ V hV)).index :=
    (Subgroup.index_comap_of_surjective _ (mkTil_surjective V₀ V hV)).symm
  have h2 := Subgroup.index_dvd_of_le hKle
  unfold rkIdx E3.mQuot
  rw [h1]
  exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite h2

theorem s16n9b_rkIdx_imgTil_le (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (W : Subgroup G) :
    rkIdx (imgTil V₀ V hV W) ≤ E3.mQuot V W := by
  have h1 : (imgTil V₀ V hV W).index ∣ (intSub V hV W).index :=
    Subgroup.index_map_dvd _ (mkTil_surjective V₀ V hV)
  unfold rkIdx E3.mQuot
  exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite h1

theorem s16n9b_commOn_le_imgTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (W : Subgroup G)
    (g : ↥(stabTil V₀ V)) :
    s16n9bCommOn (imgTil V₀ V hV W) (actTil V₀ V hV g⁻¹) ≤
      imgTil V₀ V hV (commElt W (g : G)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨y, hyW, rfl⟩ := (mem_imgTil V₀ V hV W u).1 hu
  rw [actTil_mk, ← map_inv, ← map_mul]
  refine (mem_imgTil V₀ V hV _ _).2 ⟨actStab V₀ V hV g⁻¹ y * y⁻¹, ?_, rfl⟩
  have hc := IntMod.val_comm (y⁻¹) (actStab V₀ V hV g⁻¹ y)
  have hmem : (y.val)⁻¹ * (g : G)⁻¹ * y.val * (g : G) ∈ commElt W (g : G) :=
    Subgroup.subset_closure ⟨y.val, hyW, rfl⟩
  have hval : (actStab V₀ V hV g⁻¹ y * y⁻¹).val = (y.val)⁻¹ * (g : G)⁻¹ * y.val * (g : G) := by
    rw [IntMod.val_mul, IntMod.val_inv] at *
    rw [← hc, actStab_apply_val]
    show (y.val)⁻¹ * ((g : G)⁻¹ * y.val * ((g : G)⁻¹)⁻¹) = _
    group
  rw [hval]
  exact hmem

theorem s16n9b_not_le_fixV_of_commutator (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {W : Subgroup G} (g : ↥(stabTil V₀ V)) {w : G} (hwW : w ∈ W) (hwV : w ∈ V)
    (hw0 : w⁻¹ * (g : G)⁻¹ * w * (g : G) ∉ V₀) :
    ¬ imgTil V₀ V hV W ≤ fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹)) := by
  intro hle
  have hmem : mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈ imgTil V₀ V hV W :=
    (mem_imgTil V₀ V hV W _).2 ⟨IntMod.mk hV ⟨w, hwV⟩, hwW, rfl⟩
  have hfix := mem_fixV_zpowers_iff_apply.1 (hle hmem)
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
  apply hw0
  have hc := IntMod.val_comm (IntMod.mk hV ⟨w, hwV⟩)⁻¹ (actStab V₀ V hV g⁻¹ (IntMod.mk hV ⟨w, hwV⟩))
  rw [IntMod.val_inv, actStab_apply_val] at hc
  have h2 : (g : G)⁻¹ * w * ((g : G)⁻¹)⁻¹ * w⁻¹ = w⁻¹ * (g : G)⁻¹ * w * (g : G) := by
    have hc' : w⁻¹ * ((g : G)⁻¹ * w * ((g : G)⁻¹)⁻¹) =
        (g : G)⁻¹ * w * ((g : G)⁻¹)⁻¹ * w⁻¹ := hc
    rw [← hc']
    group
  rw [← h2]
  exact hfix

end Bridge


section Transfer

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_lt_gammaN_of_bar {D : Data G} {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V)
    (hV : IsElemAbelian 2 V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsp : IsStronglyPEmbedded p D.M) (hrk : 2 ≤ CFSG.Open.pRank p D.M) (n N : ℕ)
    (hgood : s16n9bGood (Mbar D.M V₀ V hV) p n N) : (N : ℕ∞) < gammaN n D.M V := by
  have hMV : D.M ≤ normalizer (V : Set G) := h16.hyp125.pairFacts.le_normalizer
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) := h16.hyp125.pairFacts.le_normalizer₀
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  refine s16n9b_lt_gammaN_of_good (P := {p}) hV hMV ?_ n N ?_
  · intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨hp, hsp⟩
  · intro t htM ht2 hrank W hWV hWn hWt
    obtain ⟨w, hwW, hw1⟩ := s16n9b_exists_commutator_ne_one hWt
    have hwmem : w⁻¹ * t⁻¹ * w * t ∈ commElt W t := Subgroup.subset_closure ⟨w, hwW, rfl⟩
    by_cases hw0 : w⁻¹ * t⁻¹ * w * t ∈ V₀
    · exact ⟨_, hwmem, hw1, p, Set.mem_singleton p,
        Sixteen21.one_le_pRank_of_mem_small hMV₀ (Sixteen21.card_le_four_of_hyp16 h16) hp hrk
          hw0 hw1⟩
    · let g : ↥(stabTil V₀ V) := ⟨t, hMs htM⟩
      have hφM : actTil V₀ V hV g⁻¹ ∈ Mbar D.M V₀ V hV :=
        actTil_mem_barSub V₀ V hV (D.M.inv_mem htM) ((stabTil V₀ V).inv_mem g.2)
      have hφ2 : ∃ a : ℕ, orderOf (actTil V₀ V hV g⁻¹) = 2 ^ a := by
        obtain ⟨a, ha⟩ := ht2
        have hdvd : orderOf (actTil V₀ V hV g⁻¹) ∣ 2 ^ a := by
          refine (orderOf_map_dvd (actTil V₀ V hV) g⁻¹).trans ?_
          rw [orderOf_inv, ← ha]
          exact (Subgroup.orderOf_coe g).symm.dvd
        obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        exact ⟨b, hb⟩
      have hrank' : rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹))) ≤ N :=
        (s16n9b_rkIdx_fixV_le V₀ V hV g).trans hrank
      have hU : rkIdx (imgTil V₀ V hV W) ≤ n :=
        (s16n9b_rkIdx_imgTil_le V₀ V hV W).trans hWn
      have hUφ : ¬ imgTil V₀ V hV W ≤ fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹)) :=
        s16n9b_not_le_fixV_of_commutator V₀ V hV g hwW (hWV hwW) hw0
      obtain ⟨zt, hzt, hzt1, ψ, hψ, hord, hfix⟩ := hgood _ hφM hφ2 hrank' _ hU hUφ
      obtain ⟨x, hxmem, hxz⟩ :=
        (mem_imgTil V₀ V hV (commElt W t) zt).1 (s16n9b_commOn_le_imgTil V₀ V hV W g hzt)
      have hx1 : x.val ≠ 1 := by
        intro h1
        have hx1' : x = 1 := IntMod.val_injective (by rw [IntMod.val_one]; exact h1)
        apply hzt1
        rw [← hxz, hx1', map_one]
      have hxmk : IntMod.mk hV ⟨x.val, x.val_mem⟩ = x := IntMod.val_injective rfl
      refine ⟨x.val, hxmem, hx1, p, Set.mem_singleton p, ?_⟩
      refine Sixteen21.one_le_pRank_of_fix_mod (M := D.M) (T := D.T) (V₀ := V₀) (V := V)
        (V' := V₀) (X := D.M) h16.hyp125.1 hV (Sixteen21.card_le_four_of_hyp16 h16) le_rfl
        (Or.inl rfl) hp hp2 hrk hψ hord x.val_mem hx1 ?_
      rw [hxmk, hxz]
      exact hfix

theorem s16n9b_exists_mem_cTilde_of_pRank_lt {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil V₀ V) {p k : ℕ} (hp : p.Prime) (hrk : k ≤ CFSG.Open.pRank p M)
    (hlt : CFSG.Open.pRank p (Mbar M V₀ V hV) < k) :
    ∃ y ∈ F11.CTilde M V₀ V, orderOf y = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
  by_contra hno
  let φ : ↥E →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion (hEM.trans hMs))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    have hord : orderOf (e : G) = p := by
      refine orderOf_eq_prime (hE.2 e e.2) ?_
      intro h1
      exact hne (Subtype.ext h1)
    refine hno ⟨(e : G), ?_, hord⟩
    have hker : actTil V₀ V hV ⟨(e : G), hMs (hEM e.2)⟩ = 1 := he
    have hcomm := (actTil_eq_one_iff V₀ V hV ⟨(e : G), hMs (hEM e.2)⟩).1 hker
    refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
    exact ⟨hEM e.2, stabTil_le_normalizer₀ V₀ V (hMs (hEM e.2)), hcomm v hv⟩
  have hle : CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (Mbar M V₀ V hV) := by
    haveI := hE.1
    refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm' a b)
      (fun a => Subtype.ext ?_) hEcard φ hinj ?_
    · rw [Subgroup.coe_pow, hE.2 a a.2]
      rfl
    · rintro _ ⟨e, rfl⟩
      exact actTil_mem_barSub V₀ V hV (hEM e.2) (hMs (hEM e.2))
  omega

theorem s16n9b_lt_gammaN_of_pRank_lt {D : Data G} {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V)
    (hV : IsElemAbelian 2 V) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsp : IsStronglyPEmbedded p D.M) (hrk : 2 ≤ CFSG.Open.pRank p D.M)
    (hk : k ≤ CFSG.Open.pRank p D.M) (hlt : CFSG.Open.pRank p (Mbar D.M V₀ V hV) < k)
    (n N : ℕ) : (N : ℕ∞) < gammaN n D.M V := by
  have hMV : D.M ≤ normalizer (V : Set G) := h16.hyp125.pairFacts.le_normalizer
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) := h16.hyp125.pairFacts.le_normalizer₀
  obtain ⟨y, hy, hord⟩ :=
    s16n9b_exists_mem_cTilde_of_pRank_lt hV (le_stabTil hMV hMV₀) hp hk hlt
  have hfix := Sixteen21.one_le_pRank_of_mem_cTilde h16.hyp125.1
    (Sixteen21.card_le_four_of_hyp16 h16) hp hp2 hrk hy hord
  refine s16n9b_lt_gammaN_of_fixAll (P := {p}) hV hMV ?_ n N ?_
  · intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨hp, hsp⟩
  · intro v hv hv1
    exact ⟨p, Set.mem_singleton p, hfix v hv hv1⟩

theorem s16n9b_pRank_lt_of_not_dvd {Q : Type*} [Group Q] [Finite Q] {H : Subgroup Q} {p k : ℕ}
    (hp : p.Prime) (h : ¬ p ^ k ∣ Nat.card H) : CFSG.Open.pRank p H < k := by
  by_contra hge
  push Not at hge
  obtain ⟨E, hEH, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  apply h
  exact (pow_dvd_pow p hge).trans (hEcard ▸ Subgroup.card_dvd_of_le hEH)

end Transfer

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
