module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s15_Twelve_conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  unfold conjSubgroup
  rw [Subgroup.map_sup]

private theorem s15_Twelve_mem_sup_of_commute {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {x : G} :
    x ∈ H ⊔ K ↔ ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  constructor
  · intro h
    rw [Subgroup.sup_eq_closure] at h
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ h
    · rintro w (hw | hw)
      · exact ⟨w, hw, 1, K.one_mem, by simp⟩
      · exact ⟨1, H.one_mem, w, hw, by simp⟩
    · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      refine ⟨y₁ * y₂, H.mul_mem hy₁ hy₂, z₁ * z₂, K.mul_mem hz₁ hz₂, ?_⟩
      calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
        _ = y₁ * (z₁ * y₂) * z₂ := by rw [hcomm y₂ hy₂ z₁ hz₁]
        _ = y₁ * z₁ * (y₂ * z₂) := by group
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      refine ⟨y⁻¹, H.inv_mem hy, z⁻¹, K.inv_mem hz, ?_⟩
      simpa [mul_inv_rev] using (congrArg Inv.inv (hcomm y hy z hz)).symm
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact H.mul_mem_sup hy hz

private theorem s15_Twelve_eq_of_imgTil_eq {V₁ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {U U' : Subgroup G} (hU : U ≤ V) (hU' : U' ≤ V) (hV₁U : V₁ ≤ U) (hV₁U' : V₁ ≤ U')
    (h : imgTil V₁ V hV U = imgTil V₁ V hV U') : U = U' := by
  apply le_antisymm
  · intro x hx
    have hxV : x ∈ V := hU hx
    have hq : mkTil V₁ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ imgTil V₁ V hV U' := by
      rw [← h]
      exact (mem_imgTil V₁ V hV U _).2 ⟨IntMod.mk hV ⟨x, hxV⟩, hx, rfl⟩
    obtain ⟨y, hyU', hyq⟩ := (mem_imgTil V₁ V hV U' _).1 hq
    have hmem : x * (y.val)⁻¹ ∈ V₁ :=
      (mkTil_eq_iff V₁ V hV (IntMod.mk hV ⟨x, hxV⟩) y).1 hyq.symm
    have hxy : x = (x * (y.val)⁻¹) * y.val := by group
    rw [hxy]
    exact U'.mul_mem (hV₁U' hmem) hyU'
  · intro x hx
    have hxV : x ∈ V := hU' hx
    have hq : mkTil V₁ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ imgTil V₁ V hV U := by
      rw [h]
      exact (mem_imgTil V₁ V hV U' _).2 ⟨IntMod.mk hV ⟨x, hxV⟩, hx, rfl⟩
    obtain ⟨y, hyU, hyq⟩ := (mem_imgTil V₁ V hV U _).1 hq
    have hmem : x * (y.val)⁻¹ ∈ V₁ :=
      (mkTil_eq_iff V₁ V hV (IntMod.mk hV ⟨x, hxV⟩) y).1 hyq.symm
    have hxy : x = (x * (y.val)⁻¹) * y.val := by group
    rw [hxy]
    exact U.mul_mem (hV₁U hmem) hyU

private theorem s15_Twelve_normalizes_of_mem_centralizer (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) {u w : G} (hu : u ∈ D.M)
    (hw : w ∈ wSub V₀ V hV L) (hw1 : w ∉ v1Sub D.M V₀ V hV L)
    (hcomm : u * w * u⁻¹ = w) :
    u ∈ normalizer (wSub V₀ V hV L : Set G) := by
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have hu_st : u ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub h.hyp125 hV) hu
  have hγ : 0 < gamma15 D.M V₀ V hV L := by
    have := two_le_gamma15 D h hV hL
    omega
  have hwV : w ∈ V := hWV hw
  have hw_conj : w ∈ conjSubgroup (wSub V₀ V hV L) u :=
    mem_conjSubgroup_iff.2 (by rw [hcomm]; exact hw)
  have hWu_le : conjSubgroup (wSub V₀ V hV L) u ≤ V := by
    have hVu : conjSubgroup V u = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (h.hyp125.pairFacts.le_normalizer hu)
    calc conjSubgroup (wSub V₀ V hV L) u ≤ conjSubgroup V u :=
          E3.conjSubgroup_mono_left u hWV
      _ = V := hVu
  have hWu_mem : conjSubgroup (wSub V₀ V hV L) u ∈ wConj D.M V₀ V hV L := ⟨u, hu, rfl⟩
  have hW_mem : wSub V₀ V hV L ∈ wConj D.M V₀ V hV L :=
    ⟨1, D.M.one_mem, by simp [conjSubgroup_one]⟩
  have hq_mem : mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
      wStar D.M V₀ V hV L :=
    (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (wSub V₀ V hV L) _).2
      ⟨IntMod.mk hV ⟨w, hwV⟩, hw, rfl⟩
  have hq_u : mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
      imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) u) :=
    (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) u) _).2
      ⟨IntMod.mk hV ⟨w, hwV⟩, hw_conj, rfl⟩
  have hq1 : mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨w, hwV⟩) ≠ 1 := by
    intro h1
    apply hw1
    have hx : IntMod.mk hV ⟨w, hwV⟩ ∈ modNull (v1Sub D.M V₀ V hV L) V hV := by
      rw [← QuotientGroup.eq_one_iff]
      exact h1
    exact hx
  have hspan_mem : imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) u) ∈
      wStarConj D.M V₀ V hV L := ⟨u, hu, rfl⟩
  have hWs_mem : wStar D.M V₀ V hV L ∈ wStarConj D.M V₀ V hV L :=
    ⟨1, D.M.one_mem, by unfold wStar; rw [conjSubgroup_one]⟩
  have himg : imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) u) =
      wStar D.M V₀ V hV L := by
    by_contra hne
    have hdis := (sSupIndep_wStarConj D h hV hL).pairwiseDisjoint hWs_mem hspan_mem
      (Ne.symm hne)
    exact hq1 (Subgroup.mem_bot.1 (hdis.le_bot ⟨hq_mem, hq_u⟩))
  have hU : conjSubgroup (wSub V₀ V hV L) u ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le hWu_le hV₁V
  have hU' : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V := sup_le hWV hV₁V
  have himg' : imgTil (v1Sub D.M V₀ V hV L) V hV
        (conjSubgroup (wSub V₀ V hV L) u ⊔ v1Sub D.M V₀ V hV L) =
      imgTil (v1Sub D.M V₀ V hV L) V hV
        (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) := by
    rw [s15_Infra_imgTil_sup_left hV hWu_le hV₁V,
      s15_Infra_imgTil_sup_left hV hWV hV₁V]
    exact himg
  have hF : conjSubgroup (wSub V₀ V hV L) u ⊔ v1Sub D.M V₀ V hV L =
      wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L :=
    s15_Twelve_eq_of_imgTil_eq hV hU hU' le_sup_right le_sup_right himg'
  have hWeq : conjSubgroup (wSub V₀ V hV L) u = wSub V₀ V hV L :=
    s15_Twelve_fSub_inj D h1217 h hV hL hγ hWu_mem hW_mem hF
  exact conjSubgroup_eq_iff_mem_normalizer.1 hWeq

theorem s15_Twelve_inner_fixes (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hs : s15 D.M V₀ V hV L ≤ 3) {Z : Subgroup G}
    (hZ : Z ∈ wConj D.M V₀ V hV L)
    (hin : conjSubgroup (fSub15 D.M V₀ V hV L Z) k⁻¹ ≤ D.M) {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) :
    conjSubgroup (fSub15 D.M V₀ V hV L Z) k⁻¹ ≤ normalizer (X : Set G) := by
  obtain ⟨m, hm, rfl⟩ := hX
  obtain ⟨m', hm', hZeq⟩ := hZ
  have h151 := h.hyp151
  have h125 := h151.hyp125
  have hM : D.M ≤ normalizer (V : Set G) := h125.pairFacts.le_normalizer
  have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub h125 hV
  have hV₁m' : conjSubgroup (v1Sub D.M V₀ V hV L) m' = v1Sub D.M V₀ V hV L :=
    s15_Infra_conjSubgroup_v1Sub h125 hV hm'
  have hFZ : fSub15 D.M V₀ V hV L Z = conjSubgroup
      (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m' := by
    show Z ⊔ v1Sub D.M V₀ V hV L = conjSubgroup
      (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m'
    calc Z ⊔ v1Sub D.M V₀ V hV L = conjSubgroup (wSub V₀ V hV L) m' ⊔
          v1Sub D.M V₀ V hV L := by rw [hZeq]
      _ = conjSubgroup (wSub V₀ V hV L) m' ⊔
          conjSubgroup (v1Sub D.M V₀ V hV L) m' := by rw [hV₁m']
      _ = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m' :=
          (s15_Twelve_conjSubgroup_sup (wSub V₀ V hV L) (v1Sub D.M V₀ V hV L) m').symm
  set E : Subgroup G := conjSubgroup (fSub15 D.M V₀ V hV L Z) k⁻¹ with hE
  set A : Subgroup G := conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L)
      (m' * k⁻¹ * m⁻¹) with hA
  change E ≤ normalizer (conjSubgroup (wSub V₀ V hV L) m)
  have hEM : E ≤ D.M := by rw [hE]; exact hin
  have hAeq : conjSubgroup E m⁻¹ = A := by
    rw [hA, hE, hFZ]
    rw [conjSubgroup_conjSubgroup (conjSubgroup
          (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m') k⁻¹ m⁻¹,
        conjSubgroup_conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L)
          m' (k⁻¹ * m⁻¹),
        mul_assoc]
  have hAM : A ≤ D.M := by
    rw [← hAeq]
    calc conjSubgroup E m⁻¹ ≤ conjSubgroup D.M m⁻¹ :=
          E3.conjSubgroup_mono_left m⁻¹ hEM
      _ = D.M := s15_Tools_conjSubgroup_M D (D.M.inv_mem hm)
  have hA2 : IsPGroup 2 A := by
    have hWV₁ : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
      sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h125 hV)
    have hAle : A ≤ conjSubgroup V (m' * k⁻¹ * m⁻¹) := by
      rw [hA]
      exact E3.conjSubgroup_mono_left (m' * k⁻¹ * m⁻¹) hWV₁
    exact (E3.isElemAbelian_conjSubgroup hV (m' * k⁻¹ * m⁻¹)).isPGroup.to_le hAle
  have hk' : Cond1512 n D.M V k⁻¹ := cond1512_inv hk
  have hVm : conjSubgroup V m = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hM hm)
  have hVm' : conjSubgroup V m' = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hM hm')
  have hVg : ¬ V ≤ conjSubgroup D.M (m' * k⁻¹ * m⁻¹) := by
    intro hle
    have h1 : conjSubgroup (conjSubgroup D.M (m' * k⁻¹ * m⁻¹)) m =
        conjSubgroup D.M k⁻¹ := by
      rw [conjSubgroup_conjSubgroup,
        show (m' * k⁻¹ * m⁻¹) * m = m' * k⁻¹ by group,
        ← conjSubgroup_conjSubgroup D.M m' k⁻¹, s15_Tools_conjSubgroup_M D hm']
    have h2 : V ≤ conjSubgroup D.M k⁻¹ := by
      have h3 := E3.conjSubgroup_mono_left m hle
      rw [hVm, h1] at h3
      exact h3
    exact hk'.2.1 h2
  have hgV : ¬ conjSubgroup V (m' * k⁻¹ * m⁻¹) ≤ D.M := by
    intro hle
    have h1 : conjSubgroup (conjSubgroup V (m' * k⁻¹ * m⁻¹)) m =
        conjSubgroup V k⁻¹ := by
      rw [conjSubgroup_conjSubgroup,
        show (m' * k⁻¹ * m⁻¹) * m = m' * k⁻¹ by group,
        ← conjSubgroup_conjSubgroup V m' k⁻¹, hVm']
    have h2 : conjSubgroup V k⁻¹ ≤ D.M := by
      have h3 := E3.conjSubgroup_mono_left m hle
      rw [h1, s15_Tools_conjSubgroup_M D hm] at h3
      exact h3
    exact hk'.1 h2
  have hrel : (A ⊓ normalizer (wSub V₀ V hV L : Set G)).relIndex A ≤
      s15 D.M V₀ V hV L :=
    s15_Glue_relIndex_inf_normalizer_le D h151 hV hAM
  have hmq : E3.mQuot A (A ⊓ normalizer (wSub V₀ V hV L : Set G)) ≤ 1 := by
    have hpow : 2 ^ E3.mQuot A (A ⊓ normalizer (wSub V₀ V hV L : Set G)) ≤ 3 := by
      rw [← E3.relIndex_eq_two_pow hA2]
      exact le_trans hrel hs
    by_contra hk1
    have h2 : 2 ≤ E3.mQuot A (A ⊓ normalizer (wSub V₀ V hV L : Set G)) := by omega
    have h3 : 2 ^ 2 ≤ 2 ^ E3.mQuot A
        (A ⊓ normalizer (wSub V₀ V hV L : Set G)) :=
      Nat.pow_le_pow_right (by norm_num) h2
    have h4 : 4 ≤ 2 ^ E3.mQuot A (A ⊓ normalizer (wSub V₀ V hV L : Set G)) := by
      simpa using h3
    omega
  have hlt : E3.mQuot A (A ⊓ normalizer (wSub V₀ V hV L : Set G)) <
      gamma15 D.M V₀ V hV L := by
    have := two_le_gamma15 D h151 hV hL
    omega
  obtain ⟨hfixc, hcommc⟩ := fifteen_ten D h hV hA rfl
    (le_inf inf_le_left (inf_le_left.trans hAM)) hlt hVg hgV
  have hW0 : wStar D.M V₀ V hV L ≠ ⊥ := by
    intro hbot
    have hγ := two_le_gamma15 D h151 hV hL
    rw [show gamma15 D.M V₀ V hV L = rk ↥(wStar D.M V₀ V hV L) from rfl, hbot,
      rk_bot] at hγ
    omega
  have hB_st : A ⊓ normalizer (wSub V₀ V hV L : Set G) ≤
      stabTil (v1Sub D.M V₀ V hV L) V :=
    le_trans inf_le_left (le_trans hAM (le_stabTil hM hM₁))
  have hstab : barSub (v1Sub D.M V₀ V hV L) V hV
      (A ⊓ normalizer (wSub V₀ V hV L : Set G)) ≤ stabSub (wStar D.M V₀ V hV L) :=
    s15_LP_barSub_le_stabSub_imgTil hV hB_st inf_le_right
  have hE₀_2 : IsPGroup 2 ↥(A ⊓ normalizer (wSub V₀ V hV L : Set G)) :=
    hA2.to_le inf_le_left
  have hPU : ∀ x ∈ barSub (v1Sub D.M V₀ V hV L) V hV
        (A ⊓ normalizer (wSub V₀ V hV L : Set G)),
      ∀ u ∈ wStar D.M V₀ V hV L, x u ∈ wStar D.M V₀ V hV L :=
    fun x hx u hu => (mem_stabSub.1 (hstab hx) u).mpr hu
  obtain ⟨q, hqU, hq1, hqfix⟩ := s15_Lin_exists_ne_one_mem_fixV
    (s15_LP_isPGroup_barSub hV hE₀_2)
    (s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV) hW0 hPU
  have hqfixc : q ∈ wStar D.M V₀ V hV L ⊓
      fixV (barSub (v1Sub D.M V₀ V hV L) V hV
        (A ⊓ normalizer (wSub V₀ V hV L : Set G))) := ⟨hqU, hqfix⟩
  rw [hfixc] at hqfixc
  obtain ⟨x, hx, hxq⟩ := (mem_imgTil (v1Sub D.M V₀ V hV L) V hV
    (wSub V₀ V hV L ⊓ centralizer
      ((A ⊓ normalizer (wSub V₀ V hV L : Set G)) : Set G)) _).1 hqfixc
  obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.1 hx
  have hxV1 : x.val ∉ v1Sub D.M V₀ V hV L := by
    intro hx1
    apply hq1
    rw [← hxq, ← map_one (mkTil (v1Sub D.M V₀ V hV L) V hV)]
    exact (mkTil_eq_iff (v1Sub D.M V₀ V hV L) V hV x (1 : IntMod V hV)).2
      (by simpa using hx1)
  have hcentral : wSub V₀ V hV L ⊓
      centralizer ((A ⊓ normalizer (wSub V₀ V hV L : Set G)) : Set G) ≤
      centralizer ((A ⊓ D.M : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcommc
  have hcent_b : ∀ b ∈ A ⊓ D.M,
      b * x.val = x.val * b :=
    fun b hb => Subgroup.mem_centralizer_iff.1 (hcentral ⟨hwW, hwC⟩) b hb
  have hAN : A ≤ normalizer (wSub V₀ V hV L : Set G) := by
    intro a ha
    apply s15_Twelve_normalizes_of_mem_centralizer D h1217 h151 hV hL
      (hAM ha) hwW hxV1
    have hb : a ∈ A ⊓ D.M := Subgroup.mem_inf.2 ⟨ha, hAM ha⟩
    have hc := hcent_b a hb
    calc a * x.val * a⁻¹ = (x.val * a) * a⁻¹ := by rw [hc]
      _ = x.val := by group
  have hEA : E = conjSubgroup A m := by
    rw [← hAeq, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  rw [hEA, ← E3.conjSubgroup_normalizer (wSub V₀ V hV L) m]
  exact E3.conjSubgroup_mono_left m hAN

theorem s15_Twelve_modular (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 3) {Z₁ Z₂ Z₃ : Subgroup G} (h₁ : Z₁ ∈ wConj D.M V₀ V hV L)
    (h₂ : Z₂ ∈ wConj D.M V₀ V hV L) (h₃ : Z₃ ∈ wConj D.M V₀ V hV L) (h12 : Z₁ ≠ Z₂)
    (h13 : Z₁ ≠ Z₃) (h23 : Z₂ ≠ Z₃) (g : G)
    (hin₁ : conjSubgroup (fSub15 D.M V₀ V hV L Z₁) g ≤ D.M)
    (hin₂ : conjSubgroup (fSub15 D.M V₀ V hV L Z₂) g ≤ D.M) :
    conjSubgroup V g ⊓ D.M ≤ conjSubgroup (fSub15 D.M V₀ V hV L Z₁) g ⊔
      conjSubgroup (fSub15 D.M V₀ V hV L Z₂) g ⊔
      (conjSubgroup (fSub15 D.M V₀ V hV L Z₃) g ⊓ D.M) := by
  classical
  have hncard3 : ({Z₁, Z₂, Z₃} : Set (Subgroup G)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [h12, h13]),
        Set.ncard_insert_of_notMem (by simp [h23]), Set.ncard_singleton]
  have hmemall : wConj D.M V₀ V hV L = ({Z₁, Z₂, Z₃} : Set (Subgroup G)) := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
    · intro Z hZ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
      rcases hZ with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact h₃
    · rw [ncard_wConj D h hV, hs, hncard3]
  have hspan3 : (⨆ X ∈ ({Z₁, Z₂, Z₃} : Set (Subgroup G)), X) = V := by
    rw [← hmemall]
    exact iSup_wConj_eq D h1217 h hV hL
  have hVeq3 : Z₁ ⊔ Z₂ ⊔ Z₃ = V := by
    have h1 : sSup ({Z₁, Z₂, Z₃} : Set (Subgroup G)) = Z₁ ⊔ Z₂ ⊔ Z₃ := by
      rw [sSup_insert, sSup_insert, sSup_singleton, sup_assoc]
    have h2 : sSup ({Z₁, Z₂, Z₃} : Set (Subgroup G)) = V := by
      rw [sSup_eq_iSup]
      exact hspan3
    rw [h1] at h2
    exact h2
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have hZ₁V : Z₁ ≤ V := by
    obtain ⟨m, hm, rfl⟩ := h₁
    exact s15_Tools_conj_wSub_le D h.hyp125 hV hm
  have hZ₂V : Z₂ ≤ V := by
    obtain ⟨m, hm, rfl⟩ := h₂
    exact s15_Tools_conj_wSub_le D h.hyp125 hV hm
  have hZ₃V : Z₃ ≤ V := by
    obtain ⟨m, hm, rfl⟩ := h₃
    exact s15_Tools_conj_wSub_le D h.hyp125 hV hm
  have hF₁V : fSub15 D.M V₀ V hV L Z₁ ≤ V := sup_le hZ₁V hV₁V
  have hF₂V : fSub15 D.M V₀ V hV L Z₂ ≤ V := sup_le hZ₂V hV₁V
  have hF₃V : fSub15 D.M V₀ V hV L Z₃ ≤ V := sup_le hZ₃V hV₁V
  have hF₁₂V : fSub15 D.M V₀ V hV L Z₁ ⊔ fSub15 D.M V₀ V hV L Z₂ ≤ V :=
    sup_le hF₁V hF₂V
  have hVF : V ≤ fSub15 D.M V₀ V hV L Z₁ ⊔ fSub15 D.M V₀ V hV L Z₂ ⊔
      fSub15 D.M V₀ V hV L Z₃ := by
    have h3 : Z₁ ⊔ Z₂ ⊔ Z₃ ≤ fSub15 D.M V₀ V hV L Z₁ ⊔ fSub15 D.M V₀ V hV L Z₂ ⊔
        fSub15 D.M V₀ V hV L Z₃ := by
      show Z₁ ⊔ Z₂ ⊔ Z₃ ≤ (Z₁ ⊔ v1Sub D.M V₀ V hV L) ⊔
        (Z₂ ⊔ v1Sub D.M V₀ V hV L) ⊔ (Z₃ ⊔ v1Sub D.M V₀ V hV L)
      exact sup_le_sup (sup_le_sup le_sup_left le_sup_left) le_sup_left
    rwa [hVeq3] at h3
  have hcomm₁₃ : ∀ a ∈ fSub15 D.M V₀ V hV L Z₁ ⊔ fSub15 D.M V₀ V hV L Z₂,
      ∀ b ∈ fSub15 D.M V₀ V hV L Z₃, a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hV (hF₁₂V ha) (hF₃V hb)
  have hcomm₁₂ : ∀ a ∈ fSub15 D.M V₀ V hV L Z₁,
      ∀ b ∈ fSub15 D.M V₀ V hV L Z₂, a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hV (hF₁V ha) (hF₂V hb)
  intro x hx
  obtain ⟨hxVg, hxM⟩ := Subgroup.mem_inf.1 hx
  have hyV : g * x * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hxVg
  have hyF : g * x * g⁻¹ ∈ fSub15 D.M V₀ V hV L Z₁ ⊔ fSub15 D.M V₀ V hV L Z₂ ⊔
      fSub15 D.M V₀ V hV L Z₃ := hVF hyV
  obtain ⟨u, hu, f₃, hf₃, huf₃⟩ :=
    (s15_Twelve_mem_sup_of_commute (H := fSub15 D.M V₀ V hV L Z₁ ⊔
      fSub15 D.M V₀ V hV L Z₂) (K := fSub15 D.M V₀ V hV L Z₃) hcomm₁₃).1 hyF
  obtain ⟨f₁, hf₁, f₂, hf₂, hf₁₂⟩ :=
    (s15_Twelve_mem_sup_of_commute (H := fSub15 D.M V₀ V hV L Z₁)
      (K := fSub15 D.M V₀ V hV L Z₂) hcomm₁₂).1 hu
  have hprod : f₁ * f₂ * f₃ = g * x * g⁻¹ := by rw [hf₁₂, huf₃]
  have hxeq : x = (g⁻¹ * f₁ * g) * (g⁻¹ * f₂ * g) * (g⁻¹ * f₃ * g) := by
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (f₁ * f₂ * f₃) * g := by rw [← hprod]
      _ = (g⁻¹ * f₁ * g) * (g⁻¹ * f₂ * g) * (g⁻¹ * f₃ * g) := by group
  have he₁mem : g⁻¹ * f₁ * g ∈ conjSubgroup (fSub15 D.M V₀ V hV L Z₁) g := by
    rw [mem_conjSubgroup_iff]
    convert hf₁ using 1
    group
  have he₂mem : g⁻¹ * f₂ * g ∈ conjSubgroup (fSub15 D.M V₀ V hV L Z₂) g := by
    rw [mem_conjSubgroup_iff]
    convert hf₂ using 1
    group
  have he₃mem : g⁻¹ * f₃ * g ∈ conjSubgroup (fSub15 D.M V₀ V hV L Z₃) g := by
    rw [mem_conjSubgroup_iff]
    convert hf₃ using 1
    group
  have he₁M : g⁻¹ * f₁ * g ∈ D.M := hin₁ he₁mem
  have he₂M : g⁻¹ * f₂ * g ∈ D.M := hin₂ he₂mem
  have he₃M : g⁻¹ * f₃ * g ∈ D.M := by
    have h1 : g⁻¹ * f₃ * g =
        ((g⁻¹ * f₁ * g) * (g⁻¹ * f₂ * g))⁻¹ * x := by
      rw [hxeq]
      group
    rw [h1]
    exact D.M.mul_mem (D.M.inv_mem (D.M.mul_mem he₁M he₂M)) hxM
  have h12mem : (g⁻¹ * f₁ * g) * (g⁻¹ * f₂ * g) ∈
      conjSubgroup (fSub15 D.M V₀ V hV L Z₁) g ⊔
        conjSubgroup (fSub15 D.M V₀ V hV L Z₂) g :=
    Subgroup.mul_mem_sup he₁mem he₂mem
  have h123mem : (g⁻¹ * f₁ * g) * (g⁻¹ * f₂ * g) * (g⁻¹ * f₃ * g) ∈
      (conjSubgroup (fSub15 D.M V₀ V hV L Z₁) g ⊔
        conjSubgroup (fSub15 D.M V₀ V hV L Z₂) g) ⊔
        (conjSubgroup (fSub15 D.M V₀ V hV L Z₃) g ⊓ D.M) :=
    Subgroup.mul_mem_sup h12mem (Subgroup.mem_inf.2 ⟨he₃mem, he₃M⟩)
  rw [hxeq]
  exact h123mem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
