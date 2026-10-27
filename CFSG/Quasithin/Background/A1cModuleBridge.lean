module

public import CFSG.Quasithin.Background.A1cModuleAut
public import CFSG.Quasithin.Background.A1cModuleSemisimple

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace XMod

@[expose] def Normalizes (A : Type*) [Group A] (T : Type*) [Group T] (Q : Type*) [CommGroup Q]
    [MulDistribMulAction A Q] [MulDistribMulAction T Q] : Prop :=
  ∀ (t : T) (a : A), ∃ a' : A, ∀ q : Q, t • a • q = a' • t • q

variable (A : Type*) [Group A] (Q : Type*) [CommGroup Q] [MulDistribMulAction A Q]

@[expose] def opRing : Subring (AddMonoid.End (Additive Q)) :=
  Subring.closure (Set.range (actEnd A Q))

variable {A Q}

theorem actEnd_mem_opRing (a : A) : actEnd A Q a ∈ opRing A Q :=
  Subring.subset_closure ⟨a, rfl⟩

theorem opRing_smul_def (r : ↥(opRing A Q)) (p : Additive Q) :
    r • p = (r : AddMonoid.End (Additive Q)) p := rfl

@[expose] def opStab (L : Subgroup Q) : Subring (AddMonoid.End (Additive Q)) where
  carrier := {f | ∀ p : Additive Q, Additive.toMul p ∈ L → Additive.toMul (f p) ∈ L}
  mul_mem' := fun {_ _} hf hg p hp => hf _ (hg p hp)
  one_mem' := fun _ hp => hp
  add_mem' := fun {_ _} hf hg p hp => L.mul_mem (hf p hp) (hg p hp)
  zero_mem' := fun _ _ => L.one_mem
  neg_mem' := fun {_} hf p hp => L.inv_mem (hf p hp)

theorem opRing_le_opStab {L : Subgroup Q} (hL : IsInv A L) : opRing A Q ≤ opStab L := by
  rw [opRing, Subring.closure_le]
  rintro _ ⟨a, rfl⟩ p hp
  exact hL a _ hp

@[expose] def toSubmod {L : Subgroup Q} (hL : IsInv A L) : Submodule ↥(opRing A Q) (Additive Q) where
  carrier := {p | Additive.toMul p ∈ L}
  add_mem' := fun {_ _} hp hp' => L.mul_mem hp hp'
  zero_mem' := L.one_mem
  smul_mem' := fun r _ hp => opRing_le_opStab hL r.2 _ hp

theorem mem_toSubmod {L : Subgroup Q} (hL : IsInv A L) {p : Additive Q} :
    p ∈ toSubmod hL ↔ Additive.toMul p ∈ L := Iff.rfl

@[expose] def ofSubmod (N : Submodule ↥(opRing A Q) (Additive Q)) : Subgroup Q where
  carrier := {q | Additive.ofMul q ∈ N}
  mul_mem' := fun {_ _} hx hy => N.add_mem hx hy
  one_mem' := N.zero_mem
  inv_mem' := fun {_} hx => N.neg_mem hx

theorem isInv_ofSubmod (N : Submodule ↥(opRing A Q) (Additive Q)) : IsInv A (ofSubmod N) :=
  fun a _ hq => N.smul_mem (⟨actEnd A Q a, actEnd_mem_opRing a⟩ : ↥(opRing A Q)) hq

variable (A Q) in
@[expose] def invEquiv : {L : Subgroup Q // IsInv A L} ≃o Submodule ↥(opRing A Q) (Additive Q) where
  toFun L := toSubmod L.2
  invFun N := ⟨ofSubmod N, isInv_ofSubmod N⟩
  left_inv _ := Subtype.ext (Subgroup.ext fun _ => Iff.rfl)
  right_inv _ := Submodule.ext fun _ => Iff.rfl
  map_rel_iff' := by
    intro L L'
    constructor
    · intro h q hq
      exact h hq
    · intro h p hp
      exact h hp

theorem iso_of_nonempty_linearEquiv {L L' : Subgroup Q} (hL : IsInv A L) (hL' : IsInv A L')
    (h : Nonempty (↥(toSubmod hL) ≃ₗ[↥(opRing A Q)] ↥(toSubmod hL'))) : Iso A L L' := by
  obtain ⟨ψ⟩ := h
  let φ : ↥L ≃* ↥L' :=
    { toFun := fun x => ⟨Additive.toMul (ψ ⟨Additive.ofMul (x : Q), x.2⟩).1,
        (ψ ⟨Additive.ofMul (x : Q), x.2⟩).2⟩
      invFun := fun y => ⟨Additive.toMul (ψ.symm ⟨Additive.ofMul (y : Q), y.2⟩).1,
        (ψ.symm ⟨Additive.ofMul (y : Q), y.2⟩).2⟩
      left_inv := fun x => by
        apply Subtype.ext
        have h1 := ψ.symm_apply_apply ⟨Additive.ofMul (x : Q), x.2⟩
        exact congrArg (fun z : ↥(toSubmod hL) => Additive.toMul z.1) h1
      right_inv := fun y => by
        apply Subtype.ext
        have h1 := ψ.apply_symm_apply ⟨Additive.ofMul (y : Q), y.2⟩
        exact congrArg (fun z : ↥(toSubmod hL') => Additive.toMul z.1) h1
      map_mul' := fun x y => by
        apply Subtype.ext
        have h1 := ψ.map_add ⟨Additive.ofMul (x : Q), x.2⟩ ⟨Additive.ofMul (y : Q), y.2⟩
        exact congrArg (fun z : ↥(toSubmod hL') => Additive.toMul z.1) h1 }
  refine ⟨φ, fun a l l' hl => ?_⟩
  let r : ↥(opRing A Q) := ⟨actEnd A Q a, actEnd_mem_opRing a⟩
  have h1 : r • (⟨Additive.ofMul (l : Q), l.2⟩ : ↥(toSubmod hL)) =
      ⟨Additive.ofMul (l' : Q), l'.2⟩ := Subtype.ext (congrArg Additive.ofMul hl)
  have h2 := ψ.map_smul r ⟨Additive.ofMul (l : Q), l.2⟩
  rw [h1] at h2
  exact (congrArg (fun z : ↥(toSubmod hL') => Additive.toMul z.1) h2).symm

theorem nonempty_linearEquiv_of_iso {L L' : Subgroup Q} (hL : IsInv A L) (hL' : IsInv A L')
    (h : Iso A L L') : Nonempty (↥(toSubmod hL) ≃ₗ[↥(opRing A Q)] ↥(toSubmod hL')) := by
  obtain ⟨φ, hφ⟩ := h
  have key : ∀ f ∈ opRing A Q, ∀ x : ↥L,
      ∃ (hx : Additive.toMul (f (Additive.ofMul (x : Q))) ∈ L)
        (hy : Additive.toMul (f (Additive.ofMul ((φ x : ↥L') : Q))) ∈ L'),
        φ ⟨Additive.toMul (f (Additive.ofMul (x : Q))), hx⟩ =
          ⟨Additive.toMul (f (Additive.ofMul ((φ x : ↥L') : Q))), hy⟩ := by
    intro f hf
    induction hf using Subring.closure_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      intro x
      have hx : a • (x : Q) ∈ L := hL a _ x.2
      have hy : a • ((φ x : ↥L') : Q) ∈ L' := hL' a _ (φ x).2
      refine ⟨hx, hy, Subtype.ext ?_⟩
      exact (hφ a x ⟨a • (x : Q), hx⟩ rfl).symm
    | zero =>
      intro x
      refine ⟨L.one_mem, L'.one_mem, Subtype.ext ?_⟩
      exact congrArg Subtype.val (map_one φ)
    | one =>
      intro x
      exact ⟨x.2, (φ x).2, rfl⟩
    | add f g _ _ hf hg =>
      intro x
      obtain ⟨hxf, hyf, hf'⟩ := hf x
      obtain ⟨hxg, hyg, hg'⟩ := hg x
      refine ⟨L.mul_mem hxf hxg, L'.mul_mem hyf hyg, ?_⟩
      have h1 := map_mul φ ⟨_, hxf⟩ ⟨_, hxg⟩
      rw [hf', hg'] at h1
      exact h1
    | neg f _ hf =>
      intro x
      obtain ⟨hxf, hyf, hf'⟩ := hf x
      refine ⟨L.inv_mem hxf, L'.inv_mem hyf, ?_⟩
      have h1 := map_inv φ ⟨_, hxf⟩
      rw [hf'] at h1
      exact h1
    | mul f g _ _ hf hg =>
      intro x
      obtain ⟨hxg, hyg, hg'⟩ := hg x
      obtain ⟨hxf, hyf, hf'⟩ := hf ⟨_, hxg⟩
      have e : ((φ ⟨_, hxg⟩ : ↥L') : Q) = Additive.toMul (g (Additive.ofMul ((φ x : ↥L') : Q))) :=
        congrArg Subtype.val hg'
      refine ⟨hxf, ?_, ?_⟩
      · change Additive.toMul (f (Additive.ofMul (Additive.toMul
          (g (Additive.ofMul ((φ x : ↥L') : Q)))))) ∈ L'
        rw [← e]
        exact hyf
      · apply Subtype.ext
        have h1 := congrArg Subtype.val hf'
        change ((φ ⟨_, hxf⟩ : ↥L') : Q) = _
        rw [h1]
        change _ = Additive.toMul (f (Additive.ofMul (Additive.toMul
          (g (Additive.ofMul ((φ x : ↥L') : Q))))))
        rw [← e]
  let ψ : ↥(toSubmod hL) ≃ₗ[↥(opRing A Q)] ↥(toSubmod hL') :=
    { toFun := fun p => ⟨Additive.ofMul ((φ ⟨Additive.toMul p.1, p.2⟩ : ↥L') : Q), (φ _).2⟩
      invFun := fun p => ⟨Additive.ofMul ((φ.symm ⟨Additive.toMul p.1, p.2⟩ : ↥L) : Q),
        (φ.symm _).2⟩
      map_add' := fun p p' => by
        apply Subtype.ext
        have h1 := map_mul φ ⟨Additive.toMul p.1, p.2⟩ ⟨Additive.toMul p'.1, p'.2⟩
        exact congrArg (fun z : ↥L' => Additive.ofMul (z : Q)) h1
      map_smul' := fun r p => by
        apply Subtype.ext
        obtain ⟨hx, hy, he⟩ := key r.1 r.2 ⟨Additive.toMul p.1, p.2⟩
        exact congrArg (fun z : ↥L' => Additive.ofMul (z : Q)) he
      left_inv := fun p => by
        apply Subtype.ext
        exact congrArg (fun z : ↥L => Additive.ofMul (z : Q)) (φ.symm_apply_apply _)
      right_inv := fun p => by
        apply Subtype.ext
        exact congrArg (fun z : ↥L' => Additive.ofMul (z : Q)) (φ.apply_symm_apply _) }
  exact ⟨ψ⟩

theorem iso_iff {L L' : Subgroup Q} (hL : IsInv A L) (hL' : IsInv A L') :
    Iso A L L' ↔ Nonempty (↥(toSubmod hL) ≃ₗ[↥(opRing A Q)] ↥(toSubmod hL')) :=
  ⟨nonempty_linearEquiv_of_iso hL hL', iso_of_nonempty_linearEquiv hL hL'⟩

instance instOrderBotInv : OrderBot {L : Subgroup Q // IsInv A L} :=
  Subtype.orderBot isInv_bot

theorem isIrr_iff {L : Subgroup Q} (hL : IsInv A L) :
    IsIrr A L ↔ IsSimpleModule ↥(opRing A Q) ↥(toSubmod hL) := by
  rw [isSimpleModule_iff_isAtom]
  have h1 : IsAtom (toSubmod hL) ↔ IsAtom (⟨L, hL⟩ : {L : Subgroup Q // IsInv A L}) :=
    (invEquiv A Q).isAtom_iff ⟨L, hL⟩
  rw [h1]
  constructor
  · rintro ⟨-, hbot, hirr⟩
    refine ⟨fun h => hbot.ne (congrArg Subtype.val h).symm, ?_⟩
    rintro ⟨J, hJ⟩ hlt
    rcases hirr J hJ bot_le hlt.le with h | h
    · exact Subtype.ext h
    · exact absurd (Subtype.ext h) hlt.ne
  · rintro ⟨hne, hmin⟩
    refine ⟨hL, bot_lt_iff_ne_bot.2 fun h => hne (Subtype.ext h), fun J hJ _ hJL => ?_⟩
    rcases hJL.lt_or_eq with h | h
    · left
      exact congrArg Subtype.val (hmin ⟨J, hJ⟩ h)
    · right
      exact h

section Twist

variable (A) {T : Type*} [Group T] [MulDistribMulAction T Q]

variable {A}

theorem isInv_smul_of_normalizes (h : Normalizes A T Q) (t : T) {L : Subgroup Q}
    (hL : IsInv A L) : IsInv A (t • L) := by
  intro a q hq
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq ⊢
  obtain ⟨a', ha'⟩ := h t⁻¹ a
  rw [ha' q]
  exact hL a' _ hq

@[expose] def smulEquiv (t : T) (L : Subgroup Q) : ↥L ≃* ↥(t • L) where
  toFun x := ⟨t • (x : Q), Subgroup.smul_mem_pointwise_smul _ _ _ x.2⟩
  invFun y := ⟨t⁻¹ • (y : Q), Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 y.2⟩
  left_inv _ := Subtype.ext (inv_smul_smul t _)
  right_inv _ := Subtype.ext (smul_inv_smul t _)
  map_mul' _ _ := Subtype.ext (smul_mul' t _ _)

theorem iso_smul (h : Normalizes A T Q) (t : T) {L L' : Subgroup Q} (hi : Iso A L L') :
    Iso A (t • L) (t • L') := by
  obtain ⟨φ, hφ⟩ := hi
  refine ⟨(smulEquiv t L).symm.trans (φ.trans (smulEquiv t L')), fun a y y' hy => ?_⟩
  obtain ⟨a'', ha''⟩ := h t⁻¹ a
  have hxx' : a'' • (((smulEquiv t L).symm y : ↥L) : Q) = (((smulEquiv t L).symm y' : ↥L) : Q) := by
    change a'' • t⁻¹ • (y : Q) = t⁻¹ • (y' : Q)
    rw [← ha'' (y : Q), hy]
  have h1 := hφ a'' _ _ hxx'
  change a • t • ((φ ((smulEquiv t L).symm y) : ↥L') : Q) =
    t • ((φ ((smulEquiv t L).symm y') : ↥L') : Q)
  rw [← h1]
  have h2 : ∀ z : Q, a • t • z = t • a'' • z := fun z => by
    have h3 := ha'' (t • z)
    rw [inv_smul_smul] at h3
    rw [← h3, smul_inv_smul]
  exact h2 _

@[expose, instance_reducible] def invAction (h : Normalizes A T Q) :
    MulAction T {L : Subgroup Q // IsInv A L} where
  smul t L := ⟨t • L.1, isInv_smul_of_normalizes h t L.2⟩
  one_smul L := Subtype.ext (one_smul T L.1)
  mul_smul t t' L := Subtype.ext (mul_smul t t' L.1)

@[expose, instance_reducible] noncomputable def twistAction (h : Normalizes A T Q) :
    MulAction T (Submodule ↥(opRing A Q) (Additive Q)) :=
  letI := invAction h
  Equiv.mulAction T (invEquiv A Q).symm.toEquiv

theorem twistAction_smul_invEquiv (h : Normalizes A T Q) (t : T)
    (L : {L : Subgroup Q // IsInv A L}) :
    (letI := invAction h; letI := twistAction h; t • invEquiv A Q L) =
      invEquiv A Q (letI := invAction h; t • L) := by
  let := invAction h
  let := twistAction h
  rw [Equiv.smul_def]
  simp

theorem isTwist (h : Normalizes A T Q) :
    @Twist.IsTwist ↥(opRing A Q) _ (Additive Q) _ _ T _ (twistAction h) := by
  let := invAction h
  let := twistAction h
  have hsmul := twistAction_smul_invEquiv h
  have hsurj : ∀ N : Submodule ↥(opRing A Q) (Additive Q),
      ∃ L : {L : Subgroup Q // IsInv A L}, invEquiv A Q L = N :=
    fun N => ⟨(invEquiv A Q).symm N, (invEquiv A Q).apply_symm_apply N⟩
  refine ⟨fun t N N' => ?_, fun t N N' hiso => ?_⟩
  · obtain ⟨L, rfl⟩ := hsurj N
    obtain ⟨L', rfl⟩ := hsurj N'
    rw [hsmul, hsmul, (invEquiv A Q).le_iff_le, (invEquiv A Q).le_iff_le]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff
  · obtain ⟨L, rfl⟩ := hsurj N
    obtain ⟨L', rfl⟩ := hsurj N'
    rw [hsmul, hsmul]
    have hi : Iso A L.1 L'.1 := (iso_iff L.2 L'.2).2 hiso
    exact (iso_iff (isInv_smul_of_normalizes h t L.2) (isInv_smul_of_normalizes h t L'.2)).1
      (iso_smul h t hi)

theorem toSubmod_injective {L L' : Subgroup Q} {hL : IsInv A L} {hL' : IsInv A L'}
    (h : toSubmod hL = toSubmod hL') : L = L' :=
  Subgroup.ext fun q => by
    have := congrArg (fun N : Submodule ↥(opRing A Q) (Additive Q) => Additive.ofMul q ∈ N) h
    exact (Iff.of_eq this)

theorem toSubmod_le_iff {L L' : Subgroup Q} {hL : IsInv A L} {hL' : IsInv A L'} :
    toSubmod hL ≤ toSubmod hL' ↔ L ≤ L' := Iff.rfl

theorem toSubmod_iSup {ι : Sort*} {F : ι → Subgroup Q} (hF : ∀ i, IsInv A (F i)) :
    toSubmod (isInv_iSup hF) = ⨆ i, toSubmod (hF i) := by
  apply le_antisymm
  · intro p hp
    exact Subgroup.iSup_induction F
      (C := fun x => Additive.ofMul x ∈ (⨆ i, toSubmod (hF i) : Submodule ↥(opRing A Q) (Additive Q)))
      hp (fun i x hx => Submodule.mem_iSup_of_mem i hx) (Submodule.zero_mem _)
      (fun x y hx hy => Submodule.add_mem _ hx hy)
  · exact iSup_le fun i => toSubmod_le_iff.2 (le_iSup F i)

theorem disjoint_toSubmod_iff {X Y : Subgroup Q} {hX : IsInv A X} {hY : IsInv A Y} :
    Disjoint X Y ↔ Disjoint (toSubmod hX) (toSubmod hY) := by
  rw [Subgroup.disjoint_def, Submodule.disjoint_def]
  exact ⟨fun h p hp hp' => h hp hp', fun h {x} hx hx' => h (Additive.ofMul x) hx hx'⟩

theorem toSubmod_smul (h : Normalizes A T Q) (t : T) {L : Subgroup Q} (hL : IsInv A L) :
    (letI := twistAction h; t • toSubmod hL) = toSubmod (isInv_smul_of_normalizes h t hL) :=
  twistAction_smul_invEquiv h t ⟨L, hL⟩

theorem orbitSup_toSubmod (h : Normalizes A T Q) {L : Subgroup Q} (hL : IsInv A L) :
    (letI := twistAction h; Twist.orbitSup T (toSubmod hL)) =
      toSubmod (isInv_iSup fun t : T => isInv_smul_of_normalizes h t hL) := by
  let := twistAction h
  rw [toSubmod_iSup (fun t : T => isInv_smul_of_normalizes h t hL)]
  unfold Twist.orbitSup
  exact iSup_congr fun t => toSubmod_smul h t hL

theorem isHomComp_iff_forall_le {L S : Subgroup Q} (hL : IsIrr A L) (hS : IsInv A S)
    (hLS : L ≤ S) :
    IsHomComp A S L ↔ ∀ N : Submodule ↥(opRing A Q) (Additive Q), N ≤ toSubmod hS →
      IsSimpleModule ↥(opRing A Q) ↥N →
        Nonempty (↥N ≃ₗ[↥(opRing A Q)] ↥(toSubmod hL.1)) → N ≤ toSubmod hL.1 := by
  constructor
  · rintro ⟨-, -, h⟩ N hN hNs hNiso
    obtain ⟨⟨L'', hL''⟩, rfl⟩ := (invEquiv A Q).surjective N
    change toSubmod hL'' ≤ toSubmod hL.1
    exact (toSubmod_le_iff (hL := hL'') (hL' := hL.1)).2
      (h L'' ((toSubmod_le_iff (hL := hL'') (hL' := hS)).1 hN) ((isIrr_iff hL'').2 hNs)
        ((iso_iff hL'' hL.1).2 hNiso))
  · intro h
    refine ⟨hL, hLS, fun L' hL'S hL'irr hiso => ?_⟩
    exact (toSubmod_le_iff (hL := hL'irr.1) (hL' := hL.1)).1
      (h (toSubmod hL'irr.1) ((toSubmod_le_iff (hL := hL'irr.1) (hL' := hS)).2 hL'S)
        ((isIrr_iff hL'irr.1).1 hL'irr) ((iso_iff hL'irr.1 hL.1).1 hiso))

theorem forall_iso_smul_eq_iff_isHomComp (h : Normalizes A T Q) {L : Subgroup Q}
    (hL : IsIrr A L) :
    (∀ t : T, Iso A (t • L) L → t • L = L) ↔ IsHomComp A (⨆ t : T, t • L) L := by
  let := twistAction h
  have hT := isTwist h
  have hLs : IsSimpleModule ↥(opRing A Q) ↥(toSubmod hL.1) := (isIrr_iff hL.1).1 hL
  have hinvS : IsInv A (⨆ t : T, t • L) := isInv_iSup fun t => isInv_smul_of_normalizes h t hL.1
  have hLS : L ≤ ⨆ t : T, t • L := by
    have := le_iSup (fun t : T => t • L) 1
    rwa [one_smul] at this
  have horb := orbitSup_toSubmod h hL.1
  have hstab : ∀ t : T, t ∈ Twist.IsTwist.stab hT (toSubmod hL.1) ↔ Iso A (t • L) L := by
    intro t
    rw [Twist.IsTwist.mem_stab_iff, toSubmod_smul h t hL.1]
    exact (iso_iff (isInv_smul_of_normalizes h t hL.1) hL.1).symm
  have hfix : ∀ t : T, t • toSubmod hL.1 = toSubmod hL.1 ↔ t • L = L := by
    intro t
    rw [toSubmod_smul h t hL.1]
    exact ⟨fun h' => toSubmod_injective h', fun h' => Submodule.ext fun p => by
      rw [mem_toSubmod, mem_toSubmod, h']⟩
  rw [isHomComp_iff_forall_le hL hinvS hLS]
  constructor
  · intro hS N hN hNs hNiso
    have hN' : N ≤ Twist.orbitSup T (toSubmod hL.1) := by rw [horb]; exact hN
    have _ : IsSimpleModule ↥(opRing A Q) ↥(toSubmod hL.1) := hLs
    exact Twist.IsTwist.le_of_iso_of_stab_smul_eq hT
      (fun s hs => (hfix s).2 (hS s ((hstab s).1 hs))) hN' hNiso
  · intro hH t ht
    have h1 := Twist.IsTwist.smul_eq_of_forall_le hT (L := toSubmod hL.1)
      (fun L' hL' hs hiso => hH L' (by rwa [horb] at hL') hs hiso)
    exact (hfix t).1 (h1 t ((hstab t).2 ht))

theorem eq_of_iso_smul_of_isHomComp (h : Normalizes A T Q) {L : Subgroup Q} (hL : IsIrr A L)
    (hS : IsHomComp A (⨆ t : T, t • L) L) {t r : T} (hi : Iso A (t • L) (r • L)) :
    t • L = r • L := by
  have hfix := (forall_iso_smul_eq_iff_isHomComp h hL).2 hS
  have h1 : Iso A ((r⁻¹ * t) • L) L := by
    have h2 := iso_smul h r⁻¹ hi
    rwa [smul_smul, inv_smul_smul] at h2
  calc t • L = r • (r⁻¹ * t) • L := by rw [smul_smul, mul_inv_cancel_left]
    _ = r • L := by rw [hfix _ h1]

theorem stab_smul_eq_of_forall (h : Normalizes A T Q) {L : Subgroup Q} (hL : IsInv A L)
    (hS : ∀ t : T, Iso A (t • L) L → t • L = L) :
    letI := twistAction h
    ∀ s ∈ Twist.IsTwist.stab (isTwist h) (toSubmod hL), s • toSubmod hL = toSubmod hL := by
  let := twistAction h
  intro s hs
  have hs' : Iso A (s • L) L := by
    rw [Twist.IsTwist.mem_stab_iff, toSubmod_smul h s hL] at hs
    exact (iso_iff (isInv_smul_of_normalizes h s hL) hL).2 hs
  rw [toSubmod_smul h s hL]
  exact Submodule.ext fun p => by rw [mem_toSubmod, mem_toSubmod, hS s hs']

theorem sSupIndep_smul_of_isHomComp (h : Normalizes A T Q) {L : Subgroup Q} (hL : IsIrr A L)
    (hS : IsHomComp A (⨆ t : T, t • L) L) : sSupIndep (Set.range fun t : T => t • L) := by
  rw [Twist.sSupIndep_range_iff]
  intro t
  let := twistAction h
  have hT := isTwist h
  have hLs : IsSimpleModule ↥(opRing A Q) ↥(toSubmod hL.1) := (isIrr_iff hL.1).1 hL
  have hinvr : ∀ r : {r : T // r • L ≠ t • L}, IsInv A (r.1 • L) :=
    fun r => isInv_smul_of_normalizes h r.1 hL.1
  have hY : IsInv A (⨆ r : {r : T // r • L ≠ t • L}, r.1 • L) := isInv_iSup hinvr
  have hdisj := Twist.IsTwist.disjoint_conj_iSup hT
    (stab_smul_eq_of_forall h hL.1 ((forall_iso_smul_eq_iff_isHomComp h hL).2 hS)) t
  rw [disjoint_toSubmod_iff (hX := isInv_smul_of_normalizes h t hL.1) (hY := hY),
    toSubmod_iSup hinvr]
  have hP : ∀ r : T, (r • L ≠ t • L) ↔ (r • toSubmod hL.1 ≠ t • toSubmod hL.1) := by
    intro r
    rw [toSubmod_smul h r hL.1, toSubmod_smul h t hL.1]
    exact ⟨fun hne he => hne (toSubmod_injective he), fun hne he => hne (by
      exact Submodule.ext fun p => by rw [mem_toSubmod, mem_toSubmod, he])⟩
  have hiSup : (⨆ r : {r : T // r • L ≠ t • L}, toSubmod (hinvr r)) =
      ⨆ r : {r : T // r • toSubmod hL.1 ≠ t • toSubmod hL.1}, r.1 • toSubmod hL.1 :=
    Equiv.iSup_congr (Equiv.subtypeEquivRight hP) fun r => toSubmod_smul h r.1 hL.1
  rw [hiSup, ← toSubmod_smul h t hL.1] at *
  exact hdisj

theorem exists_isHomComp_of_isIrr [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) (h : Normalizes A T Q)
    (hp : IsPGroup 2 T) {L : Subgroup Q} (hL : IsIrr A L) :
    ∃ L' : Subgroup Q, L' ≤ ⨆ t : T, t • L ∧ IsIrr A L' ∧ Iso A L' L ∧
      IsHomComp A (⨆ t : T, t • L') L' := by
  let := twistAction h
  have hT := isTwist h
  have hLs : IsSimpleModule ↥(opRing A Q) ↥(toSubmod hL.1) := (isIrr_iff hL.1).1 hL
  have hM : ∀ m : Additive Q, m + m = 0 := fun m => by
    have := hQ (Additive.toMul m)
    rw [sq] at this
    exact this
  have hfin : Finite (Additive Q) := ‹Finite Q›
  obtain ⟨N, hNle, hNs, ⟨hNiso⟩, hNH⟩ := Twist.IsTwist.exists_isHomComp hT hM hp (toSubmod hL.1)
  obtain ⟨⟨L', hL'⟩, rfl⟩ := (invEquiv A Q).surjective N
  have hL'irr : IsIrr A L' := (isIrr_iff hL').2 hNs
  have hinvS : IsInv A (⨆ t : T, t • L) := isInv_iSup fun t => isInv_smul_of_normalizes h t hL.1
  have hinvS' : IsInv A (⨆ t : T, t • L') :=
    isInv_iSup fun t => isInv_smul_of_normalizes h t hL'
  have hLS' : L' ≤ ⨆ t : T, t • L' := by
    have := le_iSup (fun t : T => t • L') 1
    rwa [one_smul] at this
  refine ⟨L', ?_, hL'irr, (iso_iff hL' hL.1).2 ⟨hNiso⟩, ?_⟩
  · have h1 : toSubmod hL' ≤ toSubmod hinvS := by
      rw [← orbitSup_toSubmod h hL.1]
      exact hNle
    exact (toSubmod_le_iff (hL := hL') (hL' := hinvS)).1 h1
  · rw [isHomComp_iff_forall_le hL'irr hinvS' hLS']
    have horb := orbitSup_toSubmod h hL'
    rw [← horb]
    exact hNH

end Twist

end XMod

end CFSG.Quasithin
