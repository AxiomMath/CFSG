module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN4
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN6a

public section

namespace CFSG.Quasithin.H13.L829N

open Module

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private theorem fix_of_finrank_one6 {L : Submodule (ZMod 2) W} (hL : Module.finrank (ZMod 2) L = 1)
    {s : W ≃ₗ[ZMod 2] W} (hs : ∀ w ∈ L, s w ∈ L) : ∀ w ∈ L, s w = w := by
  obtain ⟨v, hvL, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := L) (by
    intro h
    subst h
    simp at hL)
  have hspan : ∀ w ∈ L, ∃ c : ZMod 2, c • v = w := by
    intro w hw
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hvL⟩ : L)
      (fun h => hv0 (congrArg Subtype.val h))).mp hL ⟨w, hw⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have key : ∀ d : ZMod 2, d ≠ 0 → d = 1 := by decide
  have hsv : s v = v := by
    obtain ⟨d, hd⟩ := hspan (s v) (hs v hvL)
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hd
      exact hv0 (s.map_eq_zero_iff.mp hd.symm)
    rw [key d hd0, one_smul] at hd
    exact hd.symm
  intro w hw
  obtain ⟨c, rfl⟩ := hspan w hw
  rw [map_smul, hsv]

private def ScL6 (P1 P2 : Submodule (ZMod 2) W) (a : Module.End (ZMod 2) W) : Prop :=
  ∃ c : ZMod 2, (∀ x ∈ P1, a x = c • x) ∧ (∀ y ∈ P2, a y = c • y)

private theorem scL6_algOf (S : Subgroup (W ≃ₗ[ZMod 2] W)) (P1 P2 : Submodule (ZMod 2) W)
    (h1 : ∀ s ∈ S, ∀ x ∈ P1, s x = x) (h2 : ∀ s ∈ S, ∀ y ∈ P2, s y = y) :
    ∀ a ∈ algOf S, ScL6 P1 P2 a := by
  intro a ha
  unfold algOf at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact ⟨1, fun x hx => by rw [one_smul]; exact h1 s s.2 x hx,
      fun y hy => by rw [one_smul]; exact h2 s s.2 y hy⟩
  | algebraMap r =>
    exact ⟨r, fun x _ => by rw [Module.algebraMap_end_apply],
      fun y _ => by rw [Module.algebraMap_end_apply]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc1, hc2⟩ := hx
    obtain ⟨d, hd1, hd2⟩ := hy
    exact ⟨c + d, fun z hz => by rw [LinearMap.add_apply, hc1 z hz, hd1 z hz, add_smul],
      fun z hz => by rw [LinearMap.add_apply, hc2 z hz, hd2 z hz, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc1, hc2⟩ := hx
    obtain ⟨d, hd1, hd2⟩ := hy
    exact ⟨d * c, fun z hz => by
        rw [Module.End.mul_apply, hd1 z hz, hc1 (d • z) (P1.smul_mem d hz), smul_smul, mul_comm],
      fun z hz => by
        rw [Module.End.mul_apply, hd2 z hz, hc2 (d • z) (P2.smul_mem d hz), smul_smul, mul_comm]⟩

private theorem alin_of_sc6 {P1 P2 : Submodule (ZMod 2) W} (α : ↥P1 ≃ₗ[ZMod 2] ↥P2)
    (a : Module.End (ZMod 2) W) (hsc : ScL6 P1 P2 a) (x : ↥P1) (hax : a x.1 ∈ P1) :
    ((α ⟨a x.1, hax⟩ : ↥P2) : W) = a ((α x : ↥P2) : W) := by
  obtain ⟨c, h1, h2⟩ := hsc
  have hx : (⟨a x.1, hax⟩ : ↥P1) = c • x := Subtype.ext (h1 x.1 x.2)
  rw [hx, map_smul, h2 _ (α x).2]
  rfl

private noncomputable def linEquivOfF2 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) {M N : Submodule A W}
    (β : ↥(toF2L6 A M) ≃ₗ[ZMod 2] ↥(toF2L6 A N))
    (hβ : ∀ (a : A) (x : ↥(toF2L6 A M)) (hax : a • (x : W) ∈ M),
      ((β ⟨a • (x : W), hax⟩ : ↥(toF2L6 A N)) : W) = a • ((β x : ↥(toF2L6 A N)) : W)) :
    M ≃ₗ[A] N :=
  LinearEquiv.ofBijective
    { toFun := fun x => ⟨((β ⟨x.1, x.2⟩ : ↥(toF2L6 A N)) : W), (β ⟨x.1, x.2⟩).2⟩
      map_add' := fun x y => Subtype.ext (by
        have hadd : β ⟨(x + y).1, (x + y).2⟩ = β ⟨x.1, x.2⟩ + β ⟨y.1, y.2⟩ := by
          rw [← map_add]
          rfl
        rw [hadd]
        rfl)
      map_smul' := fun a x => Subtype.ext (hβ a ⟨x.1, x.2⟩ (a • x).2) }
    ⟨fun x y hxy => by
      have h1 : β ⟨x.1, x.2⟩ = β ⟨y.1, y.2⟩ := Subtype.ext (congrArg Subtype.val hxy)
      exact Subtype.ext (congrArg Subtype.val (β.injective h1)),
     fun y => ⟨⟨((β.symm ⟨y.1, y.2⟩ : ↥(toF2L6 A M)) : W), (β.symm ⟨y.1, y.2⟩).2⟩,
        Subtype.ext (congrArg Subtype.val (β.apply_symm_apply ⟨y.1, y.2⟩))⟩⟩

private theorem invUnder_toF2_6 {Sg : Subgroup (W ≃ₗ[ZMod 2] W)}
    (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (hA : A = algOf Sg) (X : Submodule A W) :
    InvUnder Sg (toF2L6 A X) := by
  intro s hs w hw
  have hsA : ((s : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) ∈ A := by
    rw [hA]
    exact mem_algOf_of_mem Sg hs
  exact X.smul_mem (⟨_, hsA⟩ : A) hw

private theorem minimal_X6 {Sg : Subgroup (W ≃ₗ[ZMod 2] W)}
    (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (hA : A = algOf Sg) (X : Submodule A W)
    [IsSimpleModule A X] (Q : Submodule (ZMod 2) W) (hQ : Q ≤ toF2L6 A X)
    (hQi : InvUnder Sg Q) : Q = ⊥ ∨ Q = toF2L6 A X := by
  have hQA : ∀ a ∈ A, ∀ w ∈ Q, a w ∈ Q := by
    intro a ha
    rw [hA] at ha
    exact invUnder_algOf Sg hQi a ha
  let QA : Submodule A W :=
    { carrier := {w | w ∈ Q}
      add_mem' := fun hx hy => Q.add_mem hx hy
      zero_mem' := Q.zero_mem
      smul_mem' := fun a {w} hw => hQA a a.2 w hw }
  have hle : QA ≤ X := fun w hw => hQ hw
  rcases (isSimpleModule_iff_isAtom.mp (inferInstance : IsSimpleModule A X)).le_iff.mp hle with
    h | h
  · left
    ext w
    constructor
    · intro hw
      have hw' : w ∈ QA := hw
      rw [h] at hw'
      simpa using hw'
    · intro hw
      rw [Submodule.mem_bot] at hw
      rw [hw]
      exact Q.zero_mem
  · right
    ext w
    constructor
    · intro hw
      exact hQ hw
    · intro hw
      have hw' : w ∈ QA := by
        rw [h]
        exact hw
      exact hw'

private theorem invUnder_tY6 {Sg : Subgroup (W ≃ₗ[ZMod 2] W)}
    (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (hA : A = algOf Sg) (X : Submodule A W)
    (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t)
    (hT' : ∀ s ∈ Sg, (t⁻¹ : W ≃ₗ[ZMod 2] W) * s * (t⁻¹)⁻¹ ∈ Sg) :
    InvUnder Sg (toF2L6 A (twA6 A t hc X)) := by
  intro s hs w hw
  have h1 : (t⁻¹ : W ≃ₗ[ZMod 2] W) w ∈ X := hw
  have h2 : ((t⁻¹ : W ≃ₗ[ZMod 2] W) * s * (t⁻¹)⁻¹) ((t⁻¹ : W ≃ₗ[ZMod 2] W) w) ∈
      toF2L6 A X := (invUnder_toF2_6 A hA X) _ (hT' s hs) _ h1
  have h3 : ((t⁻¹ : W ≃ₗ[ZMod 2] W) * s * (t⁻¹)⁻¹) ((t⁻¹ : W ≃ₗ[ZMod 2] W) w) =
      (t⁻¹ : W ≃ₗ[ZMod 2] W) (s w) := by
    simp
  rw [h3] at h2
  exact h2

private theorem twist_eq_map6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) (X : Submodule A W) :
    toF2L6 A (twA6 A t hc X) = (toF2L6 A X).map (t : W →ₗ[ZMod 2] W) := by
  ext w
  rw [Submodule.mem_map_equiv]
  exact Iff.rfl

private theorem finrank_twist6 (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t) (X : Submodule A W) :
    Module.finrank (ZMod 2) (toF2L6 A (twA6 A t hc X)) =
      Module.finrank (ZMod 2) (toF2L6 A X) := by
  rw [twist_eq_map6 A t hc X, LinearEquiv.finrank_map_eq]

private theorem minimal_Y6 {Sg : Subgroup (W ≃ₗ[ZMod 2] W)}
    (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (hA : A = algOf Sg) (X : Submodule A W)
    [IsSimpleModule A X] (t : W ≃ₗ[ZMod 2] W)
    (hc : ConjOK6 A t)
    (hT : ∀ s ∈ Sg, t * s * t⁻¹ ∈ Sg) (Q : Submodule (ZMod 2) W)
    (hQ : Q ≤ toF2L6 A (twA6 A t hc X)) (hQi : InvUnder Sg Q) :
    Q = ⊥ ∨ Q = toF2L6 A (twA6 A t hc X) := by
  let R0 : Submodule (ZMod 2) W := Q.comap (t : W →ₗ[ZMod 2] W)
  have hR0le : R0 ≤ toF2L6 A X := by
    intro v hv
    have hQv : t v ∈ Q := hv
    have h1 : (t⁻¹ : W ≃ₗ[ZMod 2] W) (t v) ∈ X := hQ hQv
    show v ∈ X
    simpa using h1
  have hR0inv : InvUnder Sg R0 := by
    intro s hs v hv
    have hv' : t v ∈ Q := hv
    have h1 := hQi _ (hT s hs) (t v) hv'
    have e : (t * s * t⁻¹ : W ≃ₗ[ZMod 2] W) (t v) = t (s v) := by
      simp
    show t (s v) ∈ Q
    rw [← e]
    exact h1
  rcases minimal_X6 A hA X R0 hR0le hR0inv with h0 | h0
  · left
    ext w
    constructor
    · intro hw
      have hvR0 : (t⁻¹ : W ≃ₗ[ZMod 2] W) w ∈ R0 := by
        show t ((t⁻¹ : W ≃ₗ[ZMod 2] W) w) ∈ Q
        simpa using hw
      rw [h0] at hvR0
      have h0' : (t⁻¹ : W ≃ₗ[ZMod 2] W) w = 0 := (Submodule.mem_bot _).mp hvR0
      have hw0 : w = 0 := by simpa using congrArg t h0'
      rw [hw0]
      exact Submodule.zero_mem _
    · intro hw
      rw [Submodule.mem_bot] at hw
      rw [hw]
      exact Q.zero_mem
  · right
    ext w
    constructor
    · intro hw
      exact hQ hw
    · intro hw
      have hv : (t⁻¹ : W ≃ₗ[ZMod 2] W) w ∈ R0 := by
        rw [h0]
        exact hw
      have hv' : t ((t⁻¹ : W ≃ₗ[ZMod 2] W) w) ∈ Q := hv
      simpa using hv'

private theorem hc6_of_Tg {Sg Tg : Subgroup (W ≃ₗ[ZMod 2] W)}
    (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (hA : A = algOf Sg)
    (hT : ∀ t ∈ Tg, ∀ s ∈ Sg, t * s * t⁻¹ ∈ Sg) (t : W ≃ₗ[ZMod 2] W) (ht : t ∈ Tg) :
    ConjOK6 A t := by
  intro a ha
  rw [hA] at ha ⊢
  have h1 := conj_mem_algOf Sg (t := t⁻¹) (fun s hs => hT t⁻¹ (inv_mem ht) s hs) a ha
  rw [inv_inv] at h1
  exact h1

private theorem twist_iso6 {Sg Gg Tg Vg : Subgroup (W ≃ₗ[ZMod 2] W)}
    {WB : Submodule (ZMod 2) W} [Finite W]
    (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (hA : A = algOf Sg)
    (h : TransvConfig Sg Gg Tg Vg WB) (X : Submodule A W) [IsSimpleModule A X]
    (hXWB : ∀ x ∈ X, x ∈ WB) (t : W ≃ₗ[ZMod 2] W) (ht : t ∈ Tg)
    (hc : ConjOK6 A t) :
    Nonempty (twA6 A t hc X ≃ₗ[A] X) := by
  have hT : ∀ s ∈ Sg, t * s * t⁻¹ ∈ Sg := fun s hs => h.T_norm_S t ht s hs
  have hT' : ∀ s ∈ Sg, (t⁻¹ : W ≃ₗ[ZMod 2] W) * s * (t⁻¹)⁻¹ ∈ Sg :=
    fun s hs => h.T_norm_S t⁻¹ (inv_mem ht) s hs
  have hXinv := invUnder_toF2_6 A hA X
  have hYinv := invUnder_tY6 A hA X t hc hT'
  have hXle : toF2L6 A X ≤ WB := fun w hw => hXWB w hw
  have hYle : toF2L6 A (twA6 A t hc X) ≤ WB := fun w hw => by
    have h1 : (t⁻¹ : W ≃ₗ[ZMod 2] W) w ∈ X := hw
    have h2 := h.WB_T t ht _ (hXWB _ h1)
    simpa using h2
  have hXne : toF2L6 A X ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff X).mp
      (isSimpleModule_iff_isAtom.mp (inferInstance : IsSimpleModule A X)).ne_bot
    exact (Submodule.ne_bot_iff _).mpr ⟨x, hx, hx0⟩
  have hYne : toF2L6 A (twA6 A t hc X) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hXne
    refine (Submodule.ne_bot_iff _).mpr ⟨t x, ?_, fun h0 => hx0 ?_⟩
    · have e1 : (t⁻¹ : W ≃ₗ[ZMod 2] W) (t x) = x := by simp
      show (t⁻¹ : W ≃ₗ[ZMod 2] W) (t x) ∈ X
      rw [e1]
      exact hx
    · have e2 := congrArg (t⁻¹ : W ≃ₗ[ZMod 2] W) h0
      simpa using e2
  have hfin := finrank_twist6 A t hc X
  rcases h.hb.irr (toF2L6 A X) hXle hXne hXinv (minimal_X6 A hA X) with h1 | ⟨h4, _⟩
  · have hfixX : ∀ s ∈ Sg, ∀ w ∈ toF2L6 A X, s w = w :=
      fun s hs => fix_of_finrank_one6 h1 (hXinv s hs)
    have hfixY : ∀ s ∈ Sg, ∀ w ∈ toF2L6 A (twA6 A t hc X), s w = w :=
      fun s hs => fix_of_finrank_one6 (hfin.trans h1) (hYinv s hs)
    have hsc : ∀ a ∈ A, ScL6 (toF2L6 A (twA6 A t hc X)) (toF2L6 A X) a := by
      intro a ha
      rw [hA] at ha
      exact scL6_algOf Sg _ _ hfixY hfixX a ha
    let α : ↥(toF2L6 A (twA6 A t hc X)) ≃ₗ[ZMod 2] ↥(toF2L6 A X) :=
      LinearEquiv.ofFinrankEq _ _ hfin
    have hα : ∀ (a : A) (x : ↥(toF2L6 A (twA6 A t hc X)))
        (hax : a • (x : W) ∈ twA6 A t hc X),
        ((α ⟨a • (x : W), hax⟩ : ↥(toF2L6 A X)) : W) = a • ((α x : ↥(toF2L6 A X)) : W) :=
      fun a x hax => alin_of_sc6 α (a : Module.End (ZMod 2) W)
        (hsc (a : Module.End (ZMod 2) W) a.2) x hax
    exact ⟨linEquivOfF2 A α hα⟩
  · have hsup : Module.finrank (ZMod 2) ↥(toF2L6 A X ⊔ toF2L6 A (twA6 A t hc X)) ≤ 5 :=
      le_trans (Submodule.finrank_mono (sup_le hXle hYle)) h.hb.dim_le
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (toF2L6 A X)
      (toF2L6 A (twA6 A t hc X))
    have hinf_ne : toF2L6 A X ⊓ toF2L6 A (twA6 A t hc X) ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hsum
      omega
    have hinf_inv : InvUnder Sg (toF2L6 A X ⊓ toF2L6 A (twA6 A t hc X)) :=
      fun s hs w hw => ⟨hXinv s hs w hw.1, hYinv s hs w hw.2⟩
    have hXY1 : toF2L6 A X ⊓ toF2L6 A (twA6 A t hc X) = toF2L6 A X := by
      rcases minimal_X6 A hA X _ inf_le_left hinf_inv with h' | h'
      · exact absurd h' hinf_ne
      · exact h'
    have hXY2 : toF2L6 A X ⊓ toF2L6 A (twA6 A t hc X) = toF2L6 A (twA6 A t hc X) := by
      rcases minimal_Y6 A hA X t hc hT _ inf_le_right hinf_inv with h' | h'
      · exact absurd h' hinf_ne
      · exact h'
    have hXY : toF2L6 A X ≤ toF2L6 A (twA6 A t hc X) := inf_eq_left.mp hXY1
    have hYX : toF2L6 A (twA6 A t hc X) ≤ toF2L6 A X := inf_eq_right.mp hXY2
    exact ⟨LinearEquiv.ofEq (twA6 A t hc X) X
      (le_antisymm (show twA6 A t hc X ≤ X from fun w hw => hYX hw)
        (show X ≤ twA6 A t hc X from fun w hw => hXY hw))⟩

theorem isotypicComponent_eq_top [Finite W]
    {Sg Gg Tg Vg : Subgroup (W ≃ₗ[ZMod 2] W)} {WB : Submodule (ZMod 2) W}
    (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)) (hA : A = algOf Sg)
    (h : TransvConfig Sg Gg Tg Vg WB)
    (X : Submodule A W) [IsSimpleModule A X] (hXWB : ∀ x ∈ X, x ∈ WB) :
    isotypicComponent A W X = ⊤ := by
  have hPinv : InvUnder (Sg ⊔ Gg ⊔ Tg) (toF2L6 A (isotypicComponent A W X)) := by
    refine invUnder_sup ?_ ?_ ?_
    · intro s hs w hw
      have hsA : ((s : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) ∈ A := by
        rw [hA]
        exact mem_algOf_of_mem Sg hs
      exact (isotypicComponent A W X).smul_mem (⟨_, hsA⟩ : A) hw
    · intro g hg w hw
      have hf : ∀ s ∈ Sg, ((g : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) *
          (s : Module.End (ZMod 2) W) = (s : Module.End (ZMod 2) W) *
            ((g : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) := by
        intro s hs
        ext y
        exact congrArg (fun e : W ≃ₗ[ZMod 2] W => e y) (h.comm g hg s hs)
      have hgA : ∀ a ∈ A, ((g : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) * a =
          a * ((g : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) := by
        rw [hA]
        exact commute_of_commute_gens Sg hf
      let gA : W →ₗ[A] W :=
        { toFun := fun x => g x
          map_add' := fun x y => map_add g x y
          map_smul' := fun a x => congrArg (fun F : Module.End (ZMod 2) W => F x) (hgA a a.2) }
      exact (LinearMap.le_comap_isotypicComponent (↥X) gA) hw
    · intro t ht w hw
      have hc := hc6_of_Tg A hA h.T_norm_S t ht
      have hK : ∀ Q : Submodule A W, Nonempty (↥Q ≃ₗ[A] ↥X) →
          ∀ x ∈ Q, t x ∈ isotypicComponent A W X := by
        intro Q hQ x hx
        obtain ⟨e⟩ := hQ
        obtain ⟨κ⟩ := twist_iso6 A hA h X hXWB t ht hc
        have hmem : twA6 A t hc Q ∈ {m : Submodule A W | Nonempty (↥m ≃ₗ[A] ↥X)} :=
          ⟨(twA6Equiv A t hc e).trans κ⟩
        have hle : twA6 A t hc Q ≤ isotypicComponent A W X := le_sSup hmem
        apply hle
        show (t⁻¹ : W ≃ₗ[ZMod 2] W) (t x) ∈ Q
        simpa using hx
      have key : ∀ y ∈ (⨆ a : {m : Submodule A W | Nonempty (↥m ≃ₗ[A] ↥X)},
          (a : Submodule A W)), t y ∈ isotypicComponent A W X := by
        intro y hy
        refine Submodule.iSup_induction (motive := fun z => t z ∈ isotypicComponent A W X)
          (fun a : {m : Submodule A W | Nonempty (↥m ≃ₗ[A] ↥X)} => (a : Submodule A W))
          hy ?_ ?_ ?_
        · intro a z hz
          exact hK (a : Submodule A W) a.2 z hz
        · simp only [map_zero]
          exact (isotypicComponent A W X).zero_mem
        · intro z z' hz hz'
          show t (z + z') ∈ isotypicComponent A W X
          rw [map_add]
          exact (isotypicComponent A W X).add_mem hz hz'
      have hw' : w ∈ ⨆ a : {m : Submodule A W | Nonempty (↥m ≃ₗ[A] ↥X)},
          (a : Submodule A W) := by
        rw [← sSup_eq_iSup']
        exact hw
      exact key w hw'
  have hXbot : X ≠ ⊥ :=
    (isSimpleModule_iff_isAtom.mp (inferInstance : IsSimpleModule A X)).ne_bot
  have hPne : toF2L6 A (isotypicComponent A W X) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff X).mp hXbot
    exact (Submodule.ne_bot_iff _).mpr ⟨x, Submodule.le_isotypicComponent X hx, hx0⟩
  rcases h.irreducible (toF2L6 A (isotypicComponent A W X)) hPinv with h' | h'
  · exact absurd h' hPne
  · apply eq_top_iff.mpr
    intro w _
    have hw : w ∈ toF2L6 A (isotypicComponent A W X) := by
      rw [h']
      exact Submodule.mem_top
    exact hw

end CFSG.Quasithin.H13.L829N
