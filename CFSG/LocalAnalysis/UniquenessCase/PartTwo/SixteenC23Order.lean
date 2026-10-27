module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.Dihedral.PerfectDihedralFourgroupAction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem c23_mSub_mono {U U' : Subgroup G} (h : U ≤ U') (hU' : IsPGroup 2 U') :
    mSub U ≤ mSub U' := by
  have hU : IsPGroup 2 U := hU'.to_le h
  have hdvd : Nat.card U ∣ Nat.card U' := Subgroup.card_dvd_of_le h
  rw [card_eq_two_pow_mSub hU, card_eq_two_pow_mSub hU'] at hdvd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 hdvd

private theorem c23_isKleinFour_of_card_four {U : Type*} [CommGroup U] {A : Subgroup U}
    (hcard : Nat.card A = 4) (hsq : ∀ a : A, a * a = 1) : IsKleinFour ↥A := by
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent ↥A ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      rw [pow_two]
      exact hsq x
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exfalso
    have hsub : Subsingleton ↥A := Monoid.exp_eq_one_iff.mp h1
    have h := Nat.card_unique (α := ↥A)
    rw [hcard] at h
    omega
  · exact h1

theorem c23_card_mbar_v1Sub_eq (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) = Nat.card (Mbar D.M V₀ V hV) := by
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hM₀ : D.M ≤ normalizer (V₀ : Set G) := h.hyp125.pairFacts.le_normalizer₀
  have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub h.hyp125 hV
  have h0 := s16c7_card_mul_card_preBarSub (V₀ := V₀) (V := V) (E := D.M) hV
    (le_stabTil hM hM₀) (Q := ⊥) bot_le
  have h1 := s16c7_card_mul_card_preBarSub (V₀ := v1Sub D.M V₀ V hV L) (V := V) (E := D.M)
    hV (le_stabTil hM hM₁) (Q := ⊥) bot_le
  simp only [Subgroup.card_bot, mul_one] at h0 h1
  have hcent : preBarSub D.M (v1Sub D.M V₀ V hV L) V hV ⊥ =
      preBarSub D.M V₀ V hV ⊥ := by
    rw [← cTilde_eq_preBarSub_bot (M := D.M) (V₀ := v1Sub D.M V₀ V hV L) hV hM,
      ← cTilde_eq_preBarSub_bot (M := D.M) (V₀ := V₀) hV hM]
    exact fifteen_two_cent D h1217 h hV
  rw [hcent] at h1
  have hCpos : 0 < Nat.card (preBarSub D.M V₀ V hV ⊥) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hCpos ?_
  rw [← h1, ← h0]

theorem c23_gamma15_le_rk_wTil (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) : gamma15 D.M V₀ V hV L ≤ rk ↥(wTil V₀ V hV L) := by
  set W : Subgroup G := wSub V₀ V hV L with hW
  have hWle : W ≤ V := by
    rw [hW]
    unfold wSub
    exact preTil_le V₀ V hV (wTil V₀ V hV L)
  have himg : imgTil V₀ V hV W = wTil V₀ V hV L := by
    rw [hW]
    unfold wSub
    exact imgTil_preTil V₀ V hV (wTil V₀ V hV L)
  have hV₀W : V₀ ≤ W := by
    rw [hW]
    exact s15_Two_le_wSub hV h.pairFacts.le L
  have h1 : mSub W = rk ↥(wTil V₀ V hV L) + mSub V₀ := by
    have hmain := s15_Infra_mSub_eq_rk_imgTil_add V₀ V W hV hWle
    rw [himg, inf_eq_right.2 hV₀W] at hmain
    exact hmain
  have h2 : mSub W = gamma15 D.M V₀ V hV L + mSub (v1Sub D.M V₀ V hV L ⊓ W) := by
    rw [hW]
    exact mSub_wSub D h hV
  have hleV : v1Sub D.M V₀ V hV L ⊓ W ≤ V :=
    le_trans inf_le_left (s15_Infra_v1Sub_le h hV)
  have hmono : mSub V₀ ≤ mSub (v1Sub D.M V₀ V hV L ⊓ W) :=
    c23_mSub_mono (le_inf (s15_Infra_le_v1Sub D.M V₀ V hV L) hV₀W)
      ((hV.isPGroup).to_le hleV)
  omega

theorem c23_card_dvd_of_two_summands_four {U : Type} [CommGroup U] [Finite U]
    (hsq : ∀ a : U, a * a = 1) {A B : Subgroup U}
    (hA : Nat.card A = 4) (hB : Nat.card B = 4) (hinf : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤)
    {X : Subgroup (MulAut U)}
    (hperm : ∀ φ ∈ X, (A.map φ.toMonoidHom = A ∨ A.map φ.toMonoidHom = B) ∧
      (B.map φ.toMonoidHom = A ∨ B.map φ.toMonoidHom = B)) :
    Nat.card X ∣ 2 * 6 ^ 2 := by
  have hAB : A ≠ B := by
    rintro rfl
    rw [inf_idem] at hinf
    rw [hinf, Subgroup.card_bot] at hA
    omega
  set S : Subgroup X := MulAction.stabilizer X A with hS
  have hSA : ∀ φ : S, A.map (φ.1 : MulAut U).toMonoidHom = A := fun φ =>
    (Subgroup.pointwise_smul_def A).symm.trans (MulAction.mem_stabilizer_iff.1 φ.2)
  have hSB : ∀ φ : S, B.map (φ.1 : MulAut U).toMonoidHom = B := fun φ => by
    rcases (hperm φ.1.1 φ.1.2).2 with h | h
    · exact absurd (Subgroup.map_injective (φ.1 : MulAut U).injective (h.trans (hSA φ).symm)).symm
        hAB
    · exact h
  let f₁ : S →* stabSub A := ((X.subtype).comp S.subtype).codRestrict (stabSub A)
    fun φ => s15_Six_mem_stabSub_of_map (hSA φ)
  let f₂ : S →* stabSub B := ((X.subtype).comp S.subtype).codRestrict (stabSub B)
    fun φ => s15_Six_mem_stabSub_of_map (hSB φ)
  let ι : S →* MulAut A × MulAut B := ((resHom A).comp f₁).prod ((resHom B).comp f₂)
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    have h1 : resHom A (f₁ φ) = 1 := congrArg Prod.fst hφ
    have h2 : resHom B (f₂ φ) = 1 := congrArg Prod.snd hφ
    have hfixA : ∀ a ∈ A, (φ.1 : MulAut U) a = a := fun a ha =>
      congrArg (fun ψ : MulAut A => (ψ ⟨a, ha⟩ : U)) h1
    have hfixB : ∀ b ∈ B, (φ.1 : MulAut U) b = b := fun b hb =>
      congrArg (fun ψ : MulAut B => (ψ ⟨b, hb⟩ : U)) h2
    refine Subtype.ext (Subtype.ext (MulEquiv.ext fun u => ?_))
    have hu : u ∈ A ⊔ B := hsup ▸ Subgroup.mem_top u
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    show (φ.1 : MulAut U) (a * b) = a * b
    rw [map_mul, hfixA a ha, hfixB b hb]
  have hcomm : ∀ (C : Subgroup U) (a b : C), a * b = b * a := fun C a b =>
    Subtype.ext (mul_comm a.1 b.1)
  have hsqC : ∀ (C : Subgroup U) (a : C), a * a = 1 := fun C a => Subtype.ext (hsq a.1)
  have hS6 : Nat.card S ∣ 6 ^ 2 := by
    haveI : IsKleinFour ↥A := c23_isKleinFour_of_card_four hA (hsqC A)
    haveI : IsKleinFour ↥B := c23_isKleinFour_of_card_four hB (hsqC B)
    have h := Subgroup.card_dvd_of_injective ι hinj
    rwa [Nat.card_prod, CFSG.GorensteinWalter.kleinFourAut_card ↥A,
      CFSG.GorensteinWalter.kleinFourAut_card ↥B, ← pow_two] at h
  have hidx : S.index ≤ 2 := by
    rw [hS, MulAction.index_stabilizer]
    have hsub : MulAction.orbit X A ⊆ {A, B} := by
      rintro _ ⟨φ, rfl⟩
      have h1 := (hperm φ.1 φ.2).1
      have h2 : φ • A = A.map (φ : MulAut U).toMonoidHom := Subgroup.pointwise_smul_def A
      show φ • A ∈ ({A, B} : Set (Subgroup U))
      rw [h2]
      simpa using h1
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_pair hAB ▸ le_rfl)
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [← Subgroup.card_mul_index S]
  obtain h | h : S.index = 1 ∨ S.index = 2 := by omega
  · rw [h, mul_one]
    exact hS6.trans (Dvd.intro_left 2 rfl)
  · rw [h, mul_comm]
    exact mul_dvd_mul_left 2 hS6

theorem c23_card_mbar_dvd_of_gamma_two (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hγ : gamma15 D.M V₀ V hV L = 2) (hs : s15 D.M V₀ V hV L = 2) :
    Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 2 * 6 ^ 2 := by
  obtain ⟨hind, hsup⟩ := fifteen_two_directSum D h1217 h hV hL
  obtain ⟨x, y, hxy, hP⟩ := Set.ncard_eq_two.1 ((ncard_wStarConj D h hV).trans hs)
  have hx : x ∈ wStarConj D.M V₀ V hV L := hP ▸ Set.mem_insert x {y}
  have hy : y ∈ wStarConj D.M V₀ V hV L := hP ▸ Set.mem_insert_of_mem x rfl
  rw [hP] at hind hsup
  have hdisj : x ⊓ y = ⊥ := disjoint_iff.1 ((sSupIndep_pair hxy).1 hind)
  rw [sSup_pair] at hsup
  have hsq : ∀ a : vStar D.M V₀ V hV L, a * a = 1 := fun a => by
    rw [← pow_two]
    exact s15_Infra_vtil_sq_eq_one _ V hV a
  have hpg : ∀ Z : Subgroup (vStar D.M V₀ V hV L), IsPGroup 2 Z := fun Z =>
    isPGroup_two_of_sq_eq_one fun a => Subtype.ext (by simpa [pow_two] using hsq a.1)
  have hcard : ∀ Z ∈ wStarConj D.M V₀ V hV L, Nat.card Z = 4 := fun Z hZ => by
    rw [card_eq_two_pow_mSub (hpg Z)]
    show 2 ^ rk ↥Z = 4
    rw [s15_Two_rk_wStarConj h hV hZ, hγ]
    norm_num
  refine c23_card_dvd_of_two_summands_four hsq (hcard x hx) (hcard y hy) hdisj hsup
    fun φ hφ => ?_
  have h1 := fun Z (hZ : Z ∈ wStarConj D.M V₀ V hV L) => by
    have := s15_Six_map_mem_wStarConj (L := L) h.hyp125 hV hφ hZ
    rwa [hP] at this
  refine ⟨?_, ?_⟩
  · simpa using h1 x hx
  · simpa using h1 y hy

theorem c23_not_dvd_card_mbar_case2 (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_2 D V₀ V hV L) :
    ¬ 7 ^ 3 ∣ Nat.card (Mbar D.M V₀ V hV) := by
  have h := hS.setting.hyp151
  have hL := hS.ne_bot
  have hs : s15 D.M V₀ V hV L = 2 := hc.2.2.1
  have hγ : gamma15 D.M V₀ V hV L = 3 := by
    unfold gamma15
    exact s15_T7_rk_binaryNatural hc.2.1
  have hcard : Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 2 * 168 ^ 2 :=
    s15_Six_card_mbar_dvd D h1217 h hV hL hγ hs
  rw [c23_card_mbar_v1Sub_eq D h1217 h hV] at hcard
  intro h7
  have h343 : 7 ^ 3 ∣ 2 * 168 ^ 2 := dvd_trans h7 hcard
  norm_num at h343

theorem c23_not_dvd_card_mbar_case3 (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_3 D V₀ V hV L) :
    ¬ 3 ^ 3 ∣ Nat.card (Mbar D.M V₀ V hV) := by
  have h := hS.setting.hyp151
  have hL := hS.ne_bot
  have hs : s15 D.M V₀ V hV L = 2 := hc.2.2.1
  have hγ : gamma15 D.M V₀ V hV L = 2 := by
    have h1 := two_le_gamma15 D h hV hL
    have h2 := c23_gamma15_le_rk_wTil D (L := L) h.hyp125 hV
    rw [hc.2.1] at h2
    omega
  have hcard : Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 2 * 6 ^ 2 :=
    c23_card_mbar_dvd_of_gamma_two D h1217 h hV hL hγ hs
  rw [c23_card_mbar_v1Sub_eq D h1217 h hV] at hcard
  intro h3
  have h27 : 3 ^ 3 ∣ 2 * 6 ^ 2 := dvd_trans h3 hcard
  norm_num at h27

theorem c23_exists_prime (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_2 D V₀ V hV L ∨ Case167_3 D V₀ V hV L) :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ∈ D.sig ∧ p ∣ Nat.card (lBar V₀ V hV L) ∧
      ¬ p ^ 3 ∣ Nat.card (Mbar D.M V₀ V hV) := by
  rcases hc with hc | hc
  · refine ⟨7, by norm_num, by norm_num, ?_, ?_,
      c23_not_dvd_card_mbar_case2 D h1217 hS hc⟩
    · rw [hc.2.2.2]
      exact Set.mem_singleton 7
    · rw [card_eq_of_isL3 hc.1]
      norm_num
  · refine ⟨3, by norm_num, by norm_num, ?_, ?_,
      c23_not_dvd_card_mbar_case3 D h1217 hS hc⟩
    · rw [hc.2.2.2]
      exact Set.mem_singleton 3
    · simpa [hc.1.2] using (dvd_rfl : 3 ∣ 3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
