module

public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.H13.VolII16Restrict
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixHyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr
public import CFSG.Quasithin.Background.B1MoreIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Helpers

variable {W : Type} [CommGroup W]

private theorem s1611e3_comm_ident {V : Type} [CommGroup V] (p q s c : V) :
    (p * q * s⁻¹)⁻¹ * (q * s⁻¹ * c) = (p * c⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem s1611e3_stable_commSub {A : Subgroup (MulAut W)} {Y : Subgroup W}
    (hY : StableUnder A Y) : StableUnder A (commSub Y A) := by
  intro l hl r hr
  induction hr using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hc
    refine Subgroup.subset_closure ⟨l * x * l⁻¹, A.mul_mem (A.mul_mem hl hx) (A.inv_mem hl),
      l w, hY l hl w hw, ?_⟩
    simp [MulAut.mul_apply]
  | one => simpa using (commSub Y A).one_mem
  | mul a b ha hb iha ihb => simpa [map_mul] using (commSub Y A).mul_mem iha ihb
  | inv a ha ih => simpa [map_inv] using (commSub Y A).inv_mem ih

private theorem s1611e3_commSub_commSub {A : Subgroup (MulAut W)} (hperf : ⁅A, A⁆ = A)
    {Y : Subgroup W} (hY : StableUnder A Y) : commSub (commSub Y A) A = commSub Y A := by
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  apply le_antisymm
  · exact commSub_le_of_invariant fun l hl r hr => s1611e3_stable_commSub hY l hl r hr
  · refine (Subgroup.closure_le (commSub (commSub Y A) A)).mpr ?_
    rintro _ ⟨x, hx, s, hs, rfl⟩
    set R := commSub Y A with hR
    set E := commSub R A with hE
    let Ψ : ↥A →* W ⧸ E :=
      { toFun := fun y => QuotientGroup.mk (((y : MulAut W) s) * s⁻¹)
        map_one' := by simp
        map_mul' := fun y z => by
          show (QuotientGroup.mk ((((y * z : ↥A)) : MulAut W) s * s⁻¹) : W ⧸ E) =
            QuotientGroup.mk (((y : MulAut W) s) * s⁻¹) *
              QuotientGroup.mk (((z : MulAut W) s) * s⁻¹)
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
          have hc : ((z : MulAut W) s * s⁻¹ : W) ∈ R :=
            Subgroup.subset_closure ⟨z, z.2, s, hs, rfl⟩
          have hgen : ((y : MulAut W) ((z : MulAut W) s * s⁻¹)) *
              ((z : MulAut W) s * s⁻¹)⁻¹ ∈ E :=
            Subgroup.subset_closure ⟨y, y.2, _, hc, rfl⟩
          have e0 : (((y * z : ↥A)) : MulAut W) s = (y : MulAut W) ((z : MulAut W) s) :=
            rfl
          have e1 : (((y * z : ↥A)) : MulAut W) s =
              (y : MulAut W) ((z : MulAut W) s * s⁻¹) * (y : MulAut W) s := by
            rw [e0, map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
          rw [e1, s1611e3_comm_ident]
          exact E.inv_mem hgen }
    have hker : Ψ.ker = ⊤ := by
      have := Abelianization.commutator_subset_ker Ψ
      rw [Group.IsPerfect.commutator_eq_top] at this
      exact top_le_iff.mp this
    have h1 : Ψ ⟨x, hx⟩ = 1 := by
      have : (⟨x, hx⟩ : ↥A) ∈ Ψ.ker := hker ▸ Subgroup.mem_top _
      exact this
    exact (QuotientGroup.eq_one_iff _).mp h1

private theorem s1611e3_commSub_map {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]
    {κ : W₁ →* W₂} {A : Subgroup (MulAut W₁)} {B : Subgroup (MulAut W₂)}
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w, κ (a w) = b (κ w))
    (hBA : ∀ b ∈ B, ∃ a ∈ A, ∀ w, κ (a w) = b (κ w)) (S : Subgroup W₁) :
    (commSub S A).map κ = commSub (S.map κ) B := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨a, ha, w, hw, rfl⟩, rfl⟩
    obtain ⟨b, hb, hab⟩ := hAB a ha
    exact ⟨b, hb, κ w, ⟨w, hw, rfl⟩, by rw [map_mul, map_inv, hab w]⟩
  · rintro ⟨b, hb, _, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨a, ha, hab⟩ := hBA b hb
    exact ⟨a w * w⁻¹, ⟨a, ha, w, hw, rfl⟩, by rw [map_mul, map_inv, hab w]⟩

end Helpers

variable {W W' : Type} [CommGroup W] [Finite W] [CommGroup W'] [Finite W']
  {M L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')} {κ : W →* W'} {e : ↥L' →* ↥L}

theorem s1611e3_six_cover (h : SixHyp M L L' κ e) {I : Subgroup W'}
    (hI : AlternatingNatural L' I ⊥ 6) :
    ∃ (Wj : Subgroup W) (hW : ∀ ℓ ∈ L, ∀ w ∈ Wj, (ℓ : MulAut W) w ∈ Wj),
      Wj = commSub (I.comap κ) L ∧ (∀ i ∈ I, ∃ w ∈ Wj, κ w = i) ∧ (∀ w ∈ Wj, κ w ∈ I) ∧
      (Wj ⊓ κ.ker = ⊥ ∨ (Nat.card ↥(Wj ⊓ κ.ker) = 2 ∧ Nat.card ↥Wj = 2 ^ 5 ∧
        FFModel.Realizes (CFSG.Quasithin.H13.altCoreModel 6)
          (CFSG.Quasithin.H13.VolI.resHom L Wj hW).range ⊤ ⊥)) := by
  classical
  have hIinv : ∀ (b : ↥L') (u : W'), u ∈ I → (b : MulAut W') u ∈ I := by
    obtain ⟨π, hπ⟩ := hI
    exact hπ.2.2.2.1
  let U : Subgroup W := I.comap κ
  let Wj : Subgroup W := commSub U L
  have hUi : StableUnder L U := by
    intro ℓ hℓ w hw
    obtain ⟨b, hb⟩ := h.esurj ⟨ℓ, hℓ⟩
    have hb' : (e b : MulAut W) = ℓ := congrArg Subtype.val hb
    have hmem : (b : MulAut W') (κ w) ∈ I := hIinv b (κ w) hw
    have heq : κ ((ℓ : MulAut W) w) = (b : MulAut W') (κ w) := by
      rw [← hb']
      exact h.equiv b w
    show κ ((ℓ : MulAut W) w) ∈ I
    rw [heq]
    exact hmem
  have hW : StableUnder L Wj := s1611e3_stable_commSub hUi
  have hle : Wj ≤ U := commSub_le_of_invariant hUi
  have hperf : ⁅L, L⁆ = L := by
    obtain ⟨eL⟩ := h.isAlt
    haveI : Group.IsPerfect ↥(alternatingGroup (Fin 6)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (α := Fin 6) (by simp))
    haveI : Group.IsPerfect ↥L :=
      Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
    exact Subgroup.isPerfect_iff.mp inferInstance
  have hWj_eq : commSub Wj L = Wj := by
    simpa [Wj] using s1611e3_commSub_commSub (A := L) hperf (Y := U) hUi
  have hmap : Wj.map κ = I := by
    have hAB : ∀ a ∈ L, ∃ b ∈ L', ∀ w, κ (a w) = b (κ w) := by
      intro a ha
      obtain ⟨b, hb⟩ := h.esurj ⟨a, ha⟩
      refine ⟨(b : MulAut W'), b.2, ?_⟩
      have hb' : (e b : MulAut W) = a := congrArg Subtype.val hb
      intro w
      rw [← hb']
      exact h.equiv b w
    have hBA : ∀ b ∈ L', ∃ a ∈ L, ∀ w, κ (a w) = b (κ w) := by
      intro b hb
      refine ⟨((e ⟨b, hb⟩ : ↥L) : MulAut W), (e ⟨b, hb⟩).2, ?_⟩
      intro w
      exact h.equiv ⟨b, hb⟩ w
    have h1 := s1611e3_commSub_map (κ := κ) hAB hBA U
    have hUm : U.map κ = I := Subgroup.map_comap_eq_self_of_surjective h.surj I
    rw [hUm, (s16c167_mem_irrSet_alt (n := 6) (by norm_num) hI).1] at h1
    simpa [Wj] using h1
  have honto : ∀ i ∈ I, ∃ w ∈ Wj, κ w = i := by
    intro i hi
    have hi' : i ∈ Wj.map κ := by rw [hmap]; exact hi
    obtain ⟨w, hw, hwκ⟩ := Subgroup.mem_map.mp hi'
    exact ⟨w, hw, hwκ⟩
  have hinto : ∀ w ∈ Wj, κ w ∈ I := fun w hw => hle hw
  let q : ↥Wj →* ↥I := ((κ.comp Wj.subtype).codRestrict I) fun w => hle w.2
  have hs : Function.Surjective q := by
    intro i
    have hi' : (i : W') ∈ Wj.map κ := by rw [hmap]; exact i.2
    obtain ⟨w, hw, hwκ⟩ := Subgroup.mem_map.mp hi'
    refine ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    show κ w = (i : W')
    exact hwκ
  have hqker : q.ker = (Wj ⊓ κ.ker).subgroupOf Wj := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hu
      refine ⟨u.2, ?_⟩
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
    · intro hu
      exact MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp hu.2))
  have hqker_map : (q.ker).map Wj.subtype = Wj ⊓ κ.ker := by
    rw [hqker, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have hequiv : ∀ (b : ↥L') (u : ↥Wj),
      ((q ⟨((e b : ↥L) : MulAut W) (u : W), hW _ (e b).2 (u : W) u.2⟩ : ↥I) : W') =
        (b : MulAut W') ((q u : ↥I) : W') := by
    intro b u
    show κ (((e b : ↥L) : MulAut W) (u : W)) = (b : MulAut W') (κ (u : W))
    exact h.equiv b (u : W)
  have hcomp : (FFModel.altDn 6).Realizes L Wj (Wj ⊓ κ.ker) := by
    have hR := s16c11_v1_realizes_comp (A := L) (B := L') e h.esurj (U := Wj) hW q hs hequiv hI
    rwa [hqker_map] at hR
  have hker_le : κ.ker ≤ fixV L := fun w hw => h.ker w (MonoidHom.mem_ker.mp hw)
  have hfixZ : Wj ⊓ κ.ker ≤ fixV L := inf_le_right.trans hker_le
  have hZ' : (Wj ⊓ κ.ker).subgroupOf Wj ≤
      fixV (CFSG.Quasithin.H13.VolI.resHom L Wj hW).range :=
    CFSG.Quasithin.H13.VolI.subgroupOf_le_fixV_resHom_range (L := L) (U := Wj) hW
      (Z := Wj ⊓ κ.ker) hfixZ
  have hcommOf : XMod.commOf ↥L Wj = Wj := by
    rw [commOf_eq_commSub]
    exact hWj_eq
  have hcommV : commV (CFSG.Quasithin.H13.VolI.resHom L Wj hW).range = ⊤ :=
    CFSG.Quasithin.H13.VolI.commV_resHom_range (L := L) (U := Wj) hW hcommOf
  have hcomp_res : (FFModel.altDn 6).Realizes
      (CFSG.Quasithin.H13.VolI.resHom L Wj hW).range ⊤
      ((Wj ⊓ κ.ker).subgroupOf Wj) :=
    CFSG.Quasithin.H13.VolI.realizes_resHom_range (L := L) (U := Wj) hW (D := FFModel.altDn 6)
      (Z := Wj ⊓ κ.ker) hcomp
  have hdich := CFSG.Quasithin.H13.VolI.altNaturalCoverSix_holds (V := ↥Wj)
    (fun v : ↥Wj => CFSG.Quasithin.H13.VolI.sq_eq_one_of_subgroup (V := W) (U := Wj) h.sq v)
    (CFSG.Quasithin.H13.VolI.resHom L Wj hW).range ((Wj ⊓ κ.ker).subgroupOf Wj)
    hZ' hcommV hcomp_res
  refine ⟨Wj, hW, rfl, honto, hinto, ?_⟩
  rcases hdich with hZbot | ⟨hZcard, hWjcard, hreal⟩
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥Wj) ∈ (Wj ⊓ κ.ker).subgroupOf Wj :=
      (Subgroup.mem_subgroupOf).2 hx
    rw [hZbot, Subgroup.mem_bot] at hx'
    exact Subtype.ext_iff.mp hx'
  · right
    refine ⟨?_, hWjcard, hreal⟩
    have h := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Wj ⊓ κ.ker ≤ Wj)).toEquiv
    rw [hZcard] at h
    exact h.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
