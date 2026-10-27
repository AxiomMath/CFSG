module

public import CFSG.RankThree.PartTwo.Sec17.Item17Setup
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofPerm
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
import CFSG.RankThree.PartTwo.KFacts.K412Conjugacy
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof171Gen

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.KFacts.KP2

section Action

variable {G : Type} [Group G]

@[expose] noncomputable def quotAutTwo (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ CFSG.pCore 2 Y) where
  toFun σ := QuotientGroup.congr _ _ σ
    ((Subgroup.characteristic_iff_map_eq.mp CFSG.pCore_characteristic) σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

noncomputable def conjEquivTen : Perm (Fin 10) ≃* MulAut (alternatingGroup (Fin 10)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10 (by norm_num)
      (by norm_num))

variable (Y : Subgroup G) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))

@[expose] noncomputable def projTen : ↥Y →* Perm (Fin 10) :=
  (alternatingGroup (Fin 10)).subtype.comp (φ.toMonoidHom.comp (QuotientGroup.mk' _))

@[expose] noncomputable def actTen : Subgroup.normalizer (Y : Set G) →* Perm (Fin 10) :=
  conjEquivTen.symm.toMonoidHom.comp
    ((MulAut.congr φ).toMonoidHom.comp ((quotAutTwo ↥Y).comp Y.normalizerMonoidHom))

theorem projTen_conj (m : Subgroup.normalizer (Y : Set G)) (y : ↥Y) :
    projTen Y φ (Y.normalizerMonoidHom m y) =
      actTen Y φ m * projTen Y φ y * (actTen Y φ m)⁻¹ := by
  have h1 : conjEquivTen (actTen Y φ m) =
      MulAut.congr φ (quotAutTwo ↥Y (Y.normalizerMonoidHom m)) := by
    simp only [actTen, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have h2 := congrArg (fun τ : MulAut (alternatingGroup (Fin 10)) =>
    ((τ (φ (QuotientGroup.mk' _ y)) : alternatingGroup (Fin 10)) : Perm (Fin 10))) h1
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
  rw [show conjEquivTen (actTen Y φ m) = MulAut.conjNormal (actTen Y φ m) from rfl,
    MulAut.conjNormal_apply] at h2
  have hL : projTen Y φ (Y.normalizerMonoidHom m y) =
      ((φ (quotAutTwo ↥Y (Y.normalizerMonoidHom m) (QuotientGroup.mk' _ y)) :
        alternatingGroup (Fin 10)) : Perm (Fin 10)) := rfl
  have hR : projTen Y φ y =
      ((φ (QuotientGroup.mk' _ y) : alternatingGroup (Fin 10)) : Perm (Fin 10)) := rfl
  rw [hL, hR, ← h2]

theorem projTen_eq_one_iff (y : ↥Y) : projTen Y φ y = 1 ↔ y ∈ CFSG.pCore 2 ↥Y := by
  rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Y) y]
  constructor
  · intro h
    have h' : φ (QuotientGroup.mk' _ y) = 1 := Subtype.val_injective h
    exact (map_eq_one_iff φ φ.injective).mp h'
  · intro h
    change ((φ (QuotientGroup.mk' _ y) : alternatingGroup (Fin 10)) : Perm (Fin 10)) = 1
    rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) = 1 from h, map_one]
    rfl

theorem projTen_mem_alternatingGroup (y : ↥Y) : projTen Y φ y ∈ alternatingGroup (Fin 10) :=
  (φ (QuotientGroup.mk' _ y)).2

@[expose] noncomputable def imgTen (K : Subgroup G) : Subgroup (Perm (Fin 10)) :=
  (K.subgroupOf Y).map (projTen Y φ)

theorem mem_imgTen {K : Subgroup G} {z : Perm (Fin 10)} :
    z ∈ imgTen Y φ K ↔ ∃ y : ↥Y, (y : G) ∈ K ∧ projTen Y φ y = z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem le_sup_of_imgTen_le {K Q : Subgroup G} (hQY : Q ≤ Y)
    (h : imgTen Y φ Q ≤ imgTen Y φ K) : Q ≤ K ⊔ CFSG.Open.pCoreOf 2 Y := by
  intro q hq
  obtain ⟨y, hyK, hy⟩ := (mem_imgTen Y φ).mp
    (h ((mem_imgTen Y φ).mpr ⟨⟨q, hQY hq⟩, hq, rfl⟩))
  have h1 : y⁻¹ * ⟨q, hQY hq⟩ ∈ CFSG.pCore 2 ↥Y :=
    (projTen_eq_one_iff Y φ _).mp (by rw [map_mul, map_inv, hy, inv_mul_cancel])
  have h2 : ((y⁻¹ * ⟨q, hQY hq⟩ : ↥Y) : G) ∈ CFSG.Open.pCoreOf 2 Y := by
    rw [CFSG.Open.pCoreOf]
    exact ⟨_, h1, rfl⟩
  have hq' : q = (y : G) * ((y⁻¹ * ⟨q, hQY hq⟩ : ↥Y) : G) := by simp
  rw [hq']
  exact mul_mem (Subgroup.mem_sup_left hyK) (Subgroup.mem_sup_right h2)

theorem imgTen_map_conj {K : Subgroup G} (hKY : K ≤ Y) {w : G}
    (hw : w ∈ Subgroup.normalizer (Y : Set G)) :
    imgTen Y φ (K.map (MulAut.conj w).toMonoidHom) =
      (imgTen Y φ K).map (MulAut.conj (actTen Y φ ⟨w, hw⟩)).toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, ⟨k, hk, hky⟩, rfl⟩ := (mem_imgTen Y φ).mp hz
    have hy : y = Y.normalizerMonoidHom ⟨w, hw⟩ ⟨k, hKY hk⟩ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hky.symm
    refine ⟨projTen Y φ ⟨k, hKY hk⟩, (mem_imgTen Y φ).mpr ⟨_, hk, rfl⟩, ?_⟩
    rw [hy, projTen_conj]
    rfl
  · rintro ⟨z', hz', rfl⟩
    obtain ⟨y, hyK, rfl⟩ := (mem_imgTen Y φ).mp hz'
    refine (mem_imgTen Y φ).mpr ⟨Y.normalizerMonoidHom ⟨w, hw⟩ y, ?_, ?_⟩
    · rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact ⟨y, hyK, rfl⟩
    · rw [projTen_conj]
      rfl

theorem card_imgTen_dvd [Finite G] {K : Subgroup G} (hKY : K ≤ Y) :
    Nat.card (imgTen Y φ K) ∣ Nat.card K := by
  have h := Subgroup.card_map_dvd (H := K.subgroupOf Y) (projTen Y φ)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv] at h

theorem actTen_mem_normalizer_imgTen {K : Subgroup G} {m : G}
    (hmY : m ∈ Subgroup.normalizer (Y : Set G)) (hmK : m ∈ Subgroup.normalizer (K : Set G)) :
    actTen Y φ ⟨m, hmY⟩ ∈ Subgroup.normalizer (imgTen Y φ K : Set (Perm (Fin 10))) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨y, hyK, rfl⟩ := (mem_imgTen Y φ).mp hz
  refine (mem_imgTen Y φ).mpr ⟨Y.normalizerMonoidHom ⟨m, hmY⟩ y, ?_, ?_⟩
  · rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hmK y).mp hyK
  · rw [projTen_conj]

end Action

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

omit [Finite G] in
theorem commutator_map_conj_self {H : Subgroup (Perm (Fin 10))} (hH : ⁅H, H⁆ = H)
    (σ : Perm (Fin 10)) :
    ⁅H.map (MulAut.conj σ).toMonoidHom, H.map (MulAut.conj σ).toMonoidHom⁆ =
      H.map (MulAut.conj σ).toMonoidHom := by
  rw [← Subgroup.map_commutator, hH]

theorem le_iSup_sup_pCoreOf_of_a10 (h : Sec17Std G A c L Y₀)
    (hA10 : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)))
    (hA7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hT : TransOmegaThree A c) :
    Y₀ ≤ (⨆ (w : G) (_ : w ∈ Subgroup.normalizer (A : Set G)),
        L.map (MulAut.conj w).toMonoidHom) ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  classical
  obtain ⟨φ⟩ := hA10
  obtain ⟨φ7⟩ := hA7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  set W := Subgroup.normalizer (A : Set G) with hW
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set V := CFSG.Open.pCoreOf 2 Y₀ with hV
  have hWM : W ≤ M := h.normalizer_le
  have hAM : A ≤ M := h.le_normalizer_y0
  have hLY : L ≤ Y₀ := h.le_y0
  have hcA : c ∈ A := hD.mem_A
  set T := (⨆ (w : G) (_ : w ∈ W), L.map (MulAut.conj w).toMonoidHom) ⊔ V with hTdef
  have hLwT : ∀ w ∈ W, L.map (MulAut.conj w).toMonoidHom ⊔ V ≤ T := fun w hw =>
    sup_le_sup_right (show L.map (MulAut.conj w).toMonoidHom ≤
      ⨆ (w : G) (_ : w ∈ W), L.map (MulAut.conj w).toMonoidHom from
        le_iSup_of_le w (le_iSup_of_le hw le_rfl)) _
  have hLT : L ⊔ V ≤ T := by
    have := hLwT 1 (one_mem W)
    rwa [Late.map_conj_one] at this
  obtain ⟨hT3, hTw⟩ := hT
  obtain ⟨F, hF, hFne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by rw [hT3]; norm_num) (Subgroup.zpowers c)
  obtain ⟨w, hw, hFw⟩ := hTw F hF
  set c' := w * c * w⁻¹ with hc'
  have hFc' : F = Subgroup.zpowers c' := by
    rw [hFw, MonoidHom.map_zpowers]
    rfl
  have hne : Subgroup.zpowers c' ≠ Subgroup.zpowers c := hFc' ▸ hFne
  have hc'A : c' ∈ A := (Subgroup.mem_normalizer_iff.mp hw c).mp hcA
  set f : ↥L →* Perm (Fin 10) := (projTen Y₀ φ).comp (Subgroup.inclusion hLY) with hf
  have himgL : imgTen Y₀ φ L = f.range := by
    ext z
    rw [mem_imgTen, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLY l, l.2, rfl⟩
  have hker2 : IsPGroup 2 f.ker := by
    intro k
    have hk : Subgroup.inclusion hLY (k : ↥L) ∈ CFSG.pCore 2 ↥Y₀ :=
      (projTen_eq_one_iff Y₀ φ _).mp (MonoidHom.mem_ker.mp k.2)
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀) ⟨_, hk⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : CFSG.pCore 2 ↥Y₀ => ((y : ↥Y₀) : G)) hn
    simpa using this
  have hkerθ : f.ker ≤ aschbacherSolvableCore 3 ↥L := by
    have := hker2.isNilpotent
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.2.1
      f.ker inferInstance inferInstance (Proof171.not_three_dvd_of_isPGroup_two hker2)
  have hcardL : 2520 ≤ Nat.card (imgTen Y₀ φ L) := by
    rw [himgL]
    have h1 := Subgroup.card_ker_mul_card_range f
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)
    rw [Nat.card_congr φ7.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at h2
    have h3 : Nat.card f.ker ≤ Nat.card (aschbacherSolvableCore 3 ↥L) :=
      Subgroup.card_le_of_le hkerθ
    have h4 : 0 < Nat.card (aschbacherSolvableCore 3 ↥L) := Nat.card_pos
    have h5 : 2520 * Nat.card (aschbacherSolvableCore 3 ↥L) ≤
        Nat.card (aschbacherSolvableCore 3 ↥L) * Nat.card f.range := by
      calc 2520 * Nat.card (aschbacherSolvableCore 3 ↥L) = Nat.card f.ker * Nat.card f.range := by
            rw [h1, h2]
        _ ≤ Nat.card (aschbacherSolvableCore 3 ↥L) * Nat.card f.range :=
            Nat.mul_le_mul_right _ h3
    rw [mul_comm] at h5
    exact Nat.le_of_mul_le_mul_left h5 h4
  have hperfL : ⁅imgTen Y₀ φ L, imgTen Y₀ φ L⁆ = imgTen Y₀ φ L := by
    have hLp : Group.IsPerfect ↥L :=
      Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
    have : Group.IsPerfect ↥f.range :=
      Group.IsPerfect.ofSurjective (f := f.rangeRestrict) (MonoidHom.rangeRestrict_surjective f)
    rw [himgL]
    exact Subgroup.isPerfect_iff.mp this
  set ψc := actTen Y₀ φ ⟨c, hAM hcA⟩ with hψc
  have hLc : imgTen Y₀ φ L ≤ Subgroup.centralizer ({ψc} : Set (Perm (Fin 10))) ⊓
      alternatingGroup (Fin 10) := by
    intro z hz
    obtain ⟨y, hyL, rfl⟩ := (mem_imgTen Y₀ φ).mp hz
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, projTen_mem_alternatingGroup Y₀ φ y⟩
    have hy : Y₀.normalizerMonoidHom ⟨c, hAM hcA⟩ y = y := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hyL)
      change c * (y : G) * c⁻¹ = y
      rw [← this, mul_inv_cancel_right]
    have h1 := projTen_conj Y₀ φ ⟨c, hAM hcA⟩ y
    rw [hy] at h1
    calc projTen Y₀ φ y * ψc = (ψc * projTen Y₀ φ y * ψc⁻¹) * ψc := by rw [← h1]
      _ = ψc * projTen Y₀ φ y := by group
  have hfaith0 : ∀ a ∈ A, ∀ haM : a ∈ M, actTen Y₀ φ ⟨a, haM⟩ = 1 → a ∈ Subgroup.zpowers c := by
    intro a haA haM h1
    have hsc : a ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 ↥L).map L.subtype) := by
      refine ⟨haA, fun l hl => ?_⟩
      have hal : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer haA) l).mp hl
      have hℓ : (⟨a * l * a⁻¹ * l⁻¹, mul_mem hal (inv_mem hl)⟩ : ↥L) ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        have he : Subgroup.inclusion hLY ⟨a * l * a⁻¹ * l⁻¹, mul_mem hal (inv_mem hl)⟩ =
            Y₀.normalizerMonoidHom ⟨a, haM⟩ ⟨l, hLY hl⟩ * (⟨l, hLY hl⟩ : ↥Y₀)⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv,
            Subgroup.normalizerMonoidHom_apply_apply_coe]
        change projTen Y₀ φ (Subgroup.inclusion hLY _) = 1
        rw [he, map_mul, map_inv, projTen_conj, h1, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact ⟨_, hkerθ hℓ, rfl⟩
    rw [hD.sectionCentralizer_eq] at hsc
    exact hsc
  have hcc' : Subgroup.zpowers c' ⊓ Subgroup.zpowers c = ⊥ := by
    refine Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq fun hcc => ?_
    apply hne
    have hcard : Nat.card (Subgroup.zpowers c') = 3 := by
      rw [Nat.card_zpowers, hc', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hD.orderOf_eq]
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcc) ?_).symm
    rw [hcard, hD.card_zpowers]
  have hfaith : ∀ a ∈ A, ∀ haM : a ∈ M, actTen Y₀ φ ⟨a, haM⟩ = 1 → a = 1 := by
    intro a haA haM h1
    have h0 := hfaith0 a haA haM h1
    have hawA : w⁻¹ * a * w ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hw) a).mp haA
      simpa [mul_assoc] using this
    have hawM : w⁻¹ * a * w ∈ M := mul_mem (mul_mem (inv_mem (hWM hw)) haM) (hWM hw)
    have h1' : actTen Y₀ φ ⟨w⁻¹ * a * w, hawM⟩ = 1 := by
      have he : (⟨w⁻¹ * a * w, hawM⟩ : M) = (⟨w, hWM hw⟩ : M)⁻¹ * ⟨a, haM⟩ * ⟨w, hWM hw⟩ :=
        Subtype.ext rfl
      rw [he, map_mul, map_mul, h1, mul_one, map_inv, inv_mul_cancel]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hfaith0 _ hawA hawM h1')
    have ha' : a ∈ Subgroup.zpowers c' := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [hc', conj_zpow, hk]
      group
    have hmem : a ∈ Subgroup.zpowers c' ⊓ Subgroup.zpowers c := ⟨ha', h0⟩
    rw [hcc'] at hmem
    exact hmem
  set ψA : ↥A →* Perm (Fin 10) := (actTen Y₀ φ).comp (Subgroup.inclusion hAM) with hψA
  have hψAinj : Function.Injective ψA := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    exact Subgroup.mem_bot.mpr (Subtype.ext (hfaith a a.2 (hAM a.2) ha))
  have hcard27 : Nat.card ψA.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψAinj).toEquiv, hD.card_eq]
  have hcomm : ∀ x ∈ ψA.range, ∀ y ∈ ψA.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul,
      show a * b = b * a from Subtype.ext (hD.commute a.2 b.2)]
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eTwentySeven hcard27 hcomm
  have hψmem : ∀ (a : G) (ha : a ∈ A), g * actTen Y₀ φ ⟨a, hAM ha⟩ * g⁻¹ ∈ eTwentySeven := by
    intro a ha
    rw [← hg]
    exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  have hψc3 : ψc.IsThreeCycle := by
    refine isThreeCycle_of_card_centralizer ?_ ?_ ?_
    · rw [hψc, ← map_pow]
      have : (⟨c, hAM hcA⟩ : M) ^ 3 = 1 := Subtype.ext (HeadProof.pow_three_of_std h hcA)
      rw [this, map_one]
    · intro h1
      exact hD.ne_one (hfaith c hcA (hAM hcA) h1)
    · exact hcardL.trans (Subgroup.card_le_of_le (hLc.trans inf_le_left))
  set ψw := actTen Y₀ φ ⟨w, hWM hw⟩ with hψw
  have hψc' : actTen Y₀ φ ⟨c', hAM hc'A⟩ = ψw * ψc * ψw⁻¹ := by
    have he : (⟨c', hAM hc'A⟩ : M) = (⟨w, hWM hw⟩ : M) * ⟨c, hAM hcA⟩ * (⟨w, hWM hw⟩ : M)⁻¹ :=
      Subtype.ext rfl
    rw [he, map_mul, map_mul, map_inv]
  have haxis : ∀ x : Perm (Fin 10), x ∈ eTwentySeven → x.IsThreeCycle → ∃ e : Fin 6,
      x = axisElt e := by
    rintro _ ⟨i, j, k, rfl⟩ hx
    exact axisElt_of_support_card i j k hx.card_support
  obtain ⟨ea, hea⟩ := haxis _ (hψmem c hcA) (by
    rw [Equiv.Perm.IsThreeCycle, cycleType_conj]
    exact hψc3)
  obtain ⟨eb, heb⟩ := haxis _ (hψmem c' hc'A) (by
    rw [Equiv.Perm.IsThreeCycle, hψc', cycleType_conj, cycleType_conj]
    exact hψc3)
  have hab : ea.val / 2 ≠ eb.val / 2 := by
    intro hab
    have hcases := axisElt_same_axis ea eb hab
    rw [← hea, ← heb] at hcases
    apply hne
    rcases hcases with h1 | h1
    · have h2 : actTen Y₀ φ ⟨c', hAM hc'A⟩ = ψc := by
        have := congrArg (fun z => g⁻¹ * z * g) h1
        simpa [mul_assoc] using this
      have h3 : c' * c⁻¹ = 1 := by
        refine hfaith _ (mul_mem hc'A (inv_mem hcA)) (mul_mem (hAM hc'A) (inv_mem (hAM hcA))) ?_
        have he : (⟨c' * c⁻¹, mul_mem (hAM hc'A) (inv_mem (hAM hcA))⟩ : M) =
            ⟨c', hAM hc'A⟩ * (⟨c, hAM hcA⟩ : M)⁻¹ := Subtype.ext rfl
        rw [he, map_mul, map_inv, h2, mul_inv_cancel]
      rw [mul_inv_eq_one.mp h3]
    · have h2 : actTen Y₀ φ ⟨c', hAM hc'A⟩ = ψc⁻¹ := by
        have := congrArg (fun z => g⁻¹ * z * g) h1
        simpa [mul_assoc] using this
      have h3 : c' * c = 1 := by
        refine hfaith _ (mul_mem hc'A hcA) (mul_mem (hAM hc'A) (hAM hcA)) ?_
        have he : (⟨c' * c, mul_mem (hAM hc'A) (hAM hcA)⟩ : M) =
            ⟨c', hAM hc'A⟩ * (⟨c, hAM hcA⟩ : M) := Subtype.ext rfl
        rw [he, map_mul, h2, inv_mul_cancel]
      rw [eq_inv_of_mul_eq_one_left h3, Subgroup.zpowers_inv]
  have hclaim : ∀ (σ : Perm (Fin 10)) (R : Subgroup (Perm (Fin 10))),
      R ≤ Subgroup.centralizer ({σ * ψc * σ⁻¹} : Set (Perm (Fin 10))) ⊓
        alternatingGroup (Fin 10) → ¬ 3 ∣ Nat.card R →
      R ≤ (imgTen Y₀ φ L).map (MulAut.conj σ).toMonoidHom := by
    intro σ R hR hR3
    refine le_of_le_centralizer_of_isThreeCycle (x := σ * ψc * σ⁻¹)
      (by rw [Equiv.Perm.IsThreeCycle, cycleType_conj]; exact hψc3) ?_
      (commutator_map_conj_self hperfL σ)
      (by rwa [Subgroup.card_map_of_injective (MulAut.conj σ).injective]) hR hR3
    rintro _ ⟨z, hz, rfl⟩
    have hz' := hLc hz
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · have hzc : z * ψc = ψc * z := Subgroup.mem_centralizer_singleton_iff.mp hz'.1
      change σ * z * σ⁻¹ * (σ * ψc * σ⁻¹) = σ * ψc * σ⁻¹ * (σ * z * σ⁻¹)
      calc σ * z * σ⁻¹ * (σ * ψc * σ⁻¹) = σ * (z * ψc) * σ⁻¹ := by group
        _ = σ * (ψc * z) * σ⁻¹ := by rw [hzc]
        _ = σ * ψc * σ⁻¹ * (σ * z * σ⁻¹) := by group
    · exact Subgroup.Normal.conj_mem inferInstance z hz'.2 σ
  have hΔ : Y₀ = delta A (lB A) Y₀ := h.mem_y0Star.prop.1.2.2.1
  refine hΔ.le.trans (sSup_le fun Q hQ => ?_)
  obtain ⟨hQQ, hQY⟩ := hQ
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQQ.1.2.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQQ.1.2.2
  set R := (imgTen Y₀ φ Q).map (MulAut.conj g).toMonoidHom with hR
  have hR3 : ¬ 3 ∣ Nat.card R := by
    rw [hR, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact fun h3 => hQ3 (h3.trans (card_imgTen_dvd Y₀ φ hQY))
  have hER : eTwentySeven ≤ Subgroup.normalizer (R : Set (Perm (Fin 10))) := by
    rw [← hg]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    have hn : ψA a ∈ Subgroup.normalizer (imgTen Y₀ φ Q : Set (Perm (Fin 10))) :=
      actTen_mem_normalizer_imgTen Y₀ φ (hAM a.2) (hAQ a.2)
    refine Proof171Steps.mem_normalizer_of_map_conj_eq'' ?_
    rw [hR, Late.map_conj_map_conj, show (MulAut.conj g).toMonoidHom (ψA a) * g =
        g * ψA a from by simp [MulAut.conj_apply], ← Late.map_conj_map_conj,
      Proof171Steps.map_conj_eq_of_mem_normalizer' hn]
  have hRK : ∃ K : Subgroup (Perm (Fin 10)), (K = kOne ∨ K = kTwo ∨ K = kThree) ∧ R ≤ K := by
    rcases le_kOne_or_le_kTwo_or_le_kThree hR3 hER with h1 | h1 | h1
    · exact ⟨kOne, Or.inl rfl, h1⟩
    · exact ⟨kTwo, Or.inr (Or.inl rfl), h1⟩
    · exact ⟨kThree, Or.inr (Or.inr rfl), h1⟩
  obtain ⟨K, hK, hRK⟩ := hRK
  rcases le_centralizer_axisElt_or hab hK with hKa | hKb
  ·
    rw [← hea] at hKa
    have h1 := hclaim g R (hRK.trans hKa) hR3
    rw [hR, Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective] at h1
    exact (le_sup_of_imgTen_le Y₀ φ hQY h1).trans hLT
  ·
    rw [← heb, hψc', show g * (ψw * ψc * ψw⁻¹) * g⁻¹ = (g * ψw) * ψc * (g * ψw)⁻¹ by group]
      at hKb
    have h1 := hclaim (g * ψw) R (hRK.trans hKb) hR3
    rw [hR, ← Late.map_conj_map_conj, Subgroup.map_le_map_iff_of_injective
      (MulAut.conj g).injective, ← imgTen_map_conj Y₀ φ hLY (hWM hw)] at h1
    exact (le_sup_of_imgTen_le Y₀ φ hQY h1).trans (hLwT w hw)

end Main

end CFSG.RankThree.PartTwo.Sec17.Proof171Gen
