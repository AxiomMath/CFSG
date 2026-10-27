module

public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridgeB
public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourFacts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open Subgroup
open scoped MatrixGroups

section Rep

variable (W : Type) [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def lglRep : LGL 2 W →* MulAut (Multiplicative W) where
  toFun y := AddEquiv.toMultiplicative (y : W ≃ₗ[ZMod 2] W).toAddEquiv
  map_one' := by
    ext v
    rfl
  map_mul' f g := by
    ext v
    rfl

variable {W}

theorem lglRep_injective : Function.Injective (lglRep W) := by
  intro y z h
  refine LinearEquiv.ext fun w => ?_
  have := congrArg (fun a : MulAut (Multiplicative W) => a (Multiplicative.ofAdd w)) h
  exact Multiplicative.ofAdd.injective this

theorem multiplicative_sq_eq_one (v : Multiplicative W) : v ^ 2 = 1 := by
  rw [← ofAdd_toAdd v, ← ofAdd_nsmul]
  have : (2 : ℕ) • Multiplicative.toAdd v = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := rfl
    rw [h2, zero_smul]
  rw [this]
  rfl

@[expose] noncomputable def repOf (Y : Subgroup (LGL 2 W)) : ↥Y →* MulAut (Multiplicative W) :=
  (lglRep W).comp Y.subtype

theorem repOf_injective (Y : Subgroup (LGL 2 W)) : Function.Injective (repOf Y) :=
  lglRep_injective.comp Subtype.val_injective

theorem repOf_apply (Y : Subgroup (LGL 2 W)) (y : ↥Y) (v : Multiplicative W) :
    repOf Y y v = Multiplicative.ofAdd ((y : LGL 2 W) (Multiplicative.toAdd v)) :=
  rfl

@[expose] def toSubmodule (I : Subgroup (Multiplicative W)) : Submodule (ZMod 2) W where
  carrier := {w | Multiplicative.ofAdd w ∈ I}
  add_mem' := fun {a b} ha hb => I.mul_mem ha hb
  zero_mem' := I.one_mem
  smul_mem' := fun c w hw => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul]
      exact I.one_mem
    · rw [one_smul]
      exact hw

theorem mem_toSubmodule {I : Subgroup (Multiplicative W)} {w : W} :
    w ∈ toSubmodule I ↔ Multiplicative.ofAdd w ∈ I :=
  Iff.rfl

theorem isQuadraticOn_lglRep {Y A : Subgroup (LGL 2 W)}
    (hq : CFSG.Quasithin.G11.commSpace A (commSub A) = ⊥) :
    IsQuadraticOn (repOf Y) (A.subgroupOf Y) := by
  rintro a ha b hb v
  have hax : (a : LGL 2 W) ∈ A := ha
  have hbx : (b : LGL 2 W) ∈ A := hb
  have hmem : (a : LGL 2 W) (Multiplicative.toAdd v) - Multiplicative.toAdd v ∈ commSub A :=
    Submodule.subset_span ⟨a, hax, Multiplicative.toAdd v, rfl⟩
  have hz : (b : LGL 2 W) ((a : LGL 2 W) (Multiplicative.toAdd v) - Multiplicative.toAdd v) -
      ((a : LGL 2 W) (Multiplicative.toAdd v) - Multiplicative.toAdd v) ∈
      CFSG.Quasithin.G11.commSpace A (commSub A) :=
    Submodule.subset_span ⟨b, hbx, _, hmem, rfl⟩
  rw [hq, Submodule.mem_bot, sub_eq_zero] at hz
  change Multiplicative.ofAdd ((b : LGL 2 W) ((a : LGL 2 W) (Multiplicative.toAdd v) +
      -Multiplicative.toAdd v)) = Multiplicative.ofAdd ((a : LGL 2 W) (Multiplicative.toAdd v) +
      -Multiplicative.toAdd v)
  rw [← sub_eq_add_neg, hz]

theorem IsQuadraticOn.mono {Q : Type} [Group Q] {V : Type} [CommGroup V] {ρ : Q →* MulAut V}
    {A B : Subgroup Q} (h : IsQuadraticOn ρ A) (hBA : B ≤ A) : IsQuadraticOn ρ B :=
  fun a ha b hb v => h a (hBA ha) b (hBA hb) v

end Rep

section Conclusion

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

open scoped commutatorElement

theorem exists_isIrr {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V] [Finite V]
    (ρ : Q →* MulAut V) (hρ : Function.Injective ρ) {L : Subgroup Q} (hperf : ⁅L, L⁆ = L)
    (hL : L ≠ ⊥) : ∃ I : Subgroup V, IsIrr ρ L I :=
  pglb_exists_isIrr ρ hρ hperf hL

theorem exists_subgroup_card_four {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (h2 : IsPGroup 2 ↥A) (h4 : 4 ≤ Nat.card ↥A) : ∃ B ≤ A, Nat.card ↥B = 4 :=
  pglb_exists_subgroup_card_four h2 h4

theorem isPGL2_of_hyp66Shape (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} (hL : F6.IsL2 7 1 ↥L)
    (hs : Hyp66Shape Q L) : F6.IsPGL2 7 Q :=
  pglb_isPGL2_of_hyp66Shape hO hL hs

theorem card_isPGL2_seven {Q : Type} [Group Q] (h : F6.IsPGL2 7 Q) : Nat.card Q = 336 :=
  pglb_card_isPGL2_seven h

theorem isPerfect_of_isL2_seven {Q : Type} [Group Q] {L : Subgroup Q} (hL : F6.IsL2 7 1 ↥L) :
    ⁅L, L⁆ = L :=
  pglb_isPerfect_of_isL2_seven hL

theorem pglConfig_structure {Y : Subgroup (LGL 2 W)} {L : Subgroup ↥Y} (hLn : L.Normal)
    (hidx : L.index = 2) {I : Subgroup (Multiplicative W)}
    (hI : ∀ l ∈ L, ∀ i ∈ I, repOf Y l i ∈ I) {g₀ : ↥Y} (hg₀ : g₀ ∉ L)
    (hdisj : Disjoint I (I.map (repOf Y g₀).toMonoidHom)) :
    (L.map Y.subtype).relIndex Y = 2 ∧
      Disjoint (toSubmodule I) (toSubmodule (I.map (repOf Y g₀).toMonoidHom)) ∧
      (∀ y ∈ Y, y ∉ L.map Y.subtype → ∀ u ∈ toSubmodule I,
        y u ∈ toSubmodule (I.map (repOf Y g₀).toMonoidHom)) ∧
      (∀ y ∈ Y, y ∉ L.map Y.subtype → ∀ u ∈ toSubmodule (I.map (repOf Y g₀).toMonoidHom),
        y u ∈ toSubmodule I) := by
  have hrel : (L.map Y.subtype).relIndex Y = 2 := by
    change ((L.map Y.subtype).subgroupOf Y).index = 2
    rw [show (L.map Y.subtype).subgroupOf Y = L from
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective L, hidx]
  refine ⟨hrel, ?_, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro w hwI hwJ
    exact Multiplicative.ofAdd.injective (by
      simpa using (Subgroup.disjoint_def.mp hdisj) ((mem_toSubmodule).mp hwI)
        ((mem_toSubmodule).mp hwJ))
  · intro y hy hyL u hu
    have hy' : (⟨y, hy⟩ : ↥Y) ∉ L :=
      fun hc => hyL (Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hc, rfl⟩)
    have hmem : g₀⁻¹ * (⟨y, hy⟩ : ↥Y) ∈ L := by
      have hg₀inv : g₀⁻¹ ∉ L := fun h => hg₀ (by simpa using L.inv_mem h)
      exact (Subgroup.mul_mem_iff_of_index_two hidx).mpr
        ⟨fun h => absurd h hg₀inv, fun h => absurd h hy'⟩
    rw [mem_toSubmodule] at hu ⊢
    have hmemI : repOf Y (g₀⁻¹ * (⟨y, hy⟩ : ↥Y)) (Multiplicative.ofAdd u) ∈ I :=
      hI _ hmem _ hu
    have hmemJ : repOf Y g₀ (repOf Y (g₀⁻¹ * (⟨y, hy⟩ : ↥Y)) (Multiplicative.ofAdd u)) ∈
        I.map (repOf Y g₀).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨_, hmemI, rfl⟩
    have hEq : repOf Y g₀ (repOf Y (g₀⁻¹ * (⟨y, hy⟩ : ↥Y)) (Multiplicative.ofAdd u)) =
        Multiplicative.ofAdd (y u) := by
      change (repOf Y g₀ * repOf Y (g₀⁻¹ * (⟨y, hy⟩ : ↥Y))) (Multiplicative.ofAdd u) =
        Multiplicative.ofAdd (y u)
      rw [← map_mul]
      have hc : g₀ * (g₀⁻¹ * (⟨y, hy⟩ : ↥Y)) = (⟨y, hy⟩ : ↥Y) := by group
      rw [hc, repOf_apply]
      rfl
    rwa [hEq] at hmemJ
  · intro y hy hyL u hu
    have hy' : (⟨y, hy⟩ : ↥Y) ∉ L :=
      fun hc => hyL (Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hc, rfl⟩)
    have hmem : (⟨y, hy⟩ : ↥Y) * g₀ ∈ L :=
      (Subgroup.mul_mem_iff_of_index_two hidx).mpr
        ⟨fun h => absurd h hy', fun h => absurd h hg₀⟩
    rw [mem_toSubmodule] at hu ⊢
    obtain ⟨i, hi, hiEq⟩ := Subgroup.mem_map.mp hu
    have hmemI : repOf Y ((⟨y, hy⟩ : ↥Y) * g₀) i ∈ I := hI _ hmem i hi
    have hcomp : repOf Y (⟨y, hy⟩ : ↥Y) (repOf Y g₀ i) =
        repOf Y ((⟨y, hy⟩ : ↥Y) * g₀) i := by
      rw [map_mul]; rfl
    have hEq : repOf Y (⟨y, hy⟩ : ↥Y) (Multiplicative.ofAdd u) =
        Multiplicative.ofAdd (y u) := by
      rw [repOf_apply]; rfl
    have hiEq' : (repOf Y g₀) i = Multiplicative.ofAdd u := hiEq
    rw [← hcomp, hiEq', hEq] at hmemI
    exact hmemI

theorem isNatCoord_of_isNaturalL3Two {Y : Subgroup (LGL 2 W)} {L : Subgroup ↥Y}
    {I : Subgroup (Multiplicative W)} (hI : ∀ l ∈ L, ∀ i ∈ I, repOf Y l i ∈ I)
    (h : IsNaturalL3Two (repOf Y) L I) :
    ∃ (e : ↥(L.map Y.subtype) ≃* GL (Fin 3) (ZMod 2))
      (φ : ↥(toSubmodule I) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      IsNatCoord (L.map Y.subtype) (toSubmodule I) e φ := by
  obtain ⟨e₀, φ₀, hcoord⟩ := h
  let e : ↥(L.map Y.subtype) ≃* GL (Fin 3) (ZMod 2) :=
    (Subgroup.equivMapOfInjective L Y.subtype Y.subtype_injective).symm.trans e₀
  let ψ : ↥(toSubmodule I) ≃+ (Fin 3 → ZMod 2) :=
    { toFun := fun u =>
        Multiplicative.toAdd (φ₀ ⟨Multiplicative.ofAdd u.1, (mem_toSubmodule).mp u.2⟩)
      invFun := fun v =>
        ⟨Multiplicative.toAdd (φ₀.symm (Multiplicative.ofAdd v)),
          (mem_toSubmodule).mpr (by
            rw [ofAdd_toAdd]
            exact (φ₀.symm (Multiplicative.ofAdd v)).2)⟩
      left_inv := by
        intro u
        apply Subtype.ext
        dsimp only
        simp
      right_inv := by
        intro v
        dsimp only
        simp
      map_add' := by
        intro u v
        have h : (⟨Multiplicative.ofAdd u.1, (mem_toSubmodule).mp u.2⟩ : ↥I) *
            ⟨Multiplicative.ofAdd v.1, (mem_toSubmodule).mp v.2⟩ =
            ⟨Multiplicative.ofAdd (u.1 + v.1), (mem_toSubmodule).mp (u + v).2⟩ :=
          Subtype.ext (ofAdd_add u.1 v.1).symm
        exact (congrArg (fun x : ↥I => Multiplicative.toAdd (φ₀ x)) h.symm).trans
          (by rw [map_mul, toAdd_mul]) }
  let φ : ↥(toSubmodule I) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    ψ.toLinearEquiv (by
      intro c x
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · simp
      · simp)
  refine ⟨e, φ, ?_, ?_⟩
  · rintro k hk u hu
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk
    exact (mem_toSubmodule).mpr (by
      change Multiplicative.ofAdd ((l : LGL 2 W) u) ∈ I
      have hiu : Multiplicative.ofAdd u ∈ I := (mem_toSubmodule).mp hu
      have := hI l hl (Multiplicative.ofAdd u) hiu
      rwa [repOf_apply] at this)
  · intro k u v hv
    let l : ↥L := (Subgroup.equivMapOfInjective L Y.subtype Y.subtype_injective).symm k
    have hek : e k = e₀ l := by simp [e, l, MulEquiv.trans_apply]
    have hkval : (k : LGL 2 W) = (l : LGL 2 W) := by
      have hk : k = Subgroup.equivMapOfInjective L Y.subtype Y.subtype_injective l := by
        dsimp only [l]
        exact (MulEquiv.apply_symm_apply _ k).symm
      rw [hk]
      exact Subgroup.coe_equivMapOfInjective_apply L Y.subtype Y.subtype_injective l
    have hIeq : (⟨Multiplicative.ofAdd v.1, (mem_toSubmodule).mp v.2⟩ : ↥I) =
        repOf Y l (⟨Multiplicative.ofAdd u.1, (mem_toSubmodule).mp u.2⟩ : ↥I) := by
      change Multiplicative.ofAdd v.1 = repOf Y l (Multiplicative.ofAdd u.1)
      rw [repOf_apply,
        show Multiplicative.toAdd (Multiplicative.ofAdd u.1) = u.1 from rfl]
      rw [← hkval]
      exact congrArg Multiplicative.ofAdd hv
    rw [hek]
    exact hcoord l ⟨Multiplicative.ofAdd u.1, _⟩ ⟨Multiplicative.ofAdd v.1, _⟩ hIeq

theorem map_invariant {Y : Subgroup (LGL 2 W)} {L : Subgroup ↥Y} (hLn : L.Normal)
    {I : Subgroup (Multiplicative W)} (hI : ∀ l ∈ L, ∀ i ∈ I, repOf Y l i ∈ I) (g₀ : ↥Y) :
    ∀ l ∈ L, ∀ j ∈ I.map (repOf Y g₀).toMonoidHom,
      repOf Y l j ∈ I.map (repOf Y g₀).toMonoidHom := by
  rintro l hl _ ⟨i, hi, rfl⟩
  have hc : g₀⁻¹ * l * g₀ ∈ L := by simpa using hLn.conj_mem l hl g₀⁻¹
  refine ⟨repOf Y (g₀⁻¹ * l * g₀) i, hI _ hc i hi, ?_⟩
  simp [map_mul]

theorem isDualPair_of_isDualPairing {Y : Subgroup (LGL 2 W)} {L : Subgroup ↥Y}
    {I J : Subgroup (Multiplicative W)} (hJ : ∀ l ∈ L, ∀ j ∈ J, repOf Y l j ∈ J)
    (h : IsDualPairing (repOf Y) L I J) :
    IsDualPair (L.map Y.subtype) (toSubmodule I) (toSubmodule J) := by
  obtain ⟨β, h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, fun w w' => β (Multiplicative.ofAdd w) (Multiplicative.ofAdd w'), ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk u hu
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hk
    exact hJ l hl _ hu
  · intro u₁ hu₁ u₂ hu₂ v hv
    exact h1 _ hu₁ _ hu₂ _ hv
  · intro u hu v₁ hv₁ v₂ hv₂
    exact h2 _ hu _ hv₁ _ hv₂
  · intro u hu hz
    have := h3 (Multiplicative.ofAdd u) hu fun j hj => by
      simpa using hz (Multiplicative.toAdd j) (by rw [mem_toSubmodule, ofAdd_toAdd]; exact hj)
    exact Multiplicative.ofAdd.injective this
  · intro v hv hz
    have := h4 (Multiplicative.ofAdd v) hv fun i hi => by
      simpa using hz (Multiplicative.toAdd i) (by rw [mem_toSubmodule, ofAdd_toAdd]; exact hi)
    exact Multiplicative.ofAdd.injective this
  · intro k hk u hu v hv
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hk
    exact h5 l hl _ hu _ hv

theorem pglConfig_of_conclusion {Y : Subgroup (LGL 2 W)} {L : Subgroup ↥Y} (hLn : L.Normal)
    (hidx : L.index = 2) {I : Subgroup (Multiplicative W)} (hI : IsIrr (repOf Y) L I)
    (hnat : IsNaturalL3Two (repOf Y) L I) {g₀ : ↥Y} (hg₀ : g₀ ∉ L)
    (hdisj : Disjoint I (I.map (repOf Y g₀).toMonoidHom))
    (hdual : IsDualPairing (repOf Y) L I (I.map (repOf Y g₀).toMonoidHom)) :
    PGLConfig Y (L.map Y.subtype) (toSubmodule I)
      (toSubmodule (I.map (repOf Y g₀).toMonoidHom)) := by
  have hInv : ∀ l ∈ L, ∀ i ∈ I, repOf Y l i ∈ I := fun l hl i hi => hI.map_mem hl hi
  obtain ⟨hrel, hdis, hs₁, hs₂⟩ := pglConfig_structure hLn hidx hInv hg₀ hdisj
  exact
    { le := Subgroup.map_subtype_le L
      relIndex_eq := hrel
      disjoint := hdis
      swap₁ := hs₁
      swap₂ := hs₂
      coord := isNatCoord_of_isNaturalL3Two hInv hnat
      dual := isDualPair_of_isDualPairing (map_invariant hLn hInv g₀) hdual }

end Conclusion

theorem asch6_6_lgl (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h66 : Asch6_6) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {Y A : Subgroup (LGL 2 W)} (hAY : A ≤ Y) (hshape : Hyp66Shape ↥Y (genFittingFStar ↥Y))
    (hAe : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card ↥A)
    (hq : CFSG.Quasithin.G11.commSpace A (commSub A) = ⊥) :
    F6.IsPGL2 7 ↥Y ∧ Nat.card ↥A = 4 ∧
      ∃ (K : Subgroup (LGL 2 W)) (U₁ U₂ : Submodule (ZMod 2) W),
        A ≤ K ∧ PGLConfig Y K U₁ U₂ := by
  classical
  have hAe' : IsElemAbelian 2 (A.subgroupOf Y) := hAe.subgroupOf Y
  have hcardA : Nat.card ↥(A.subgroupOf Y) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
  obtain ⟨B, hBA, hB4⟩ :=
    exists_subgroup_card_four (X := ↥Y) hAe'.isPGroup (hcardA.symm ▸ hA4)
  have hBe : IsElemAbelian 2 B := hAe'.mono hBA
  have hBq : IsQuadraticOn (repOf Y) B := (isQuadraticOn_lglRep (Y := Y) hq).mono hBA
  obtain ⟨h1, h2, h3⟩ := h66 ↥Y (Multiplicative W) multiplicative_sq_eq_one (repOf Y)
    (repOf_injective Y) (genFittingFStar ↥Y) B rfl hB4 hBe hBq hshape
  have hPGL : F6.IsPGL2 7 ↥Y := isPGL2_of_hyp66Shape hO h1 hshape
  have hA4' : Nat.card ↥A = 4 := le_antisymm (card_le_four_of_isPGL2 hPGL hAY hAe) hA4
  have hBeq : B = A.subgroupOf Y :=
    Subgroup.eq_of_le_of_card_ge hBA (by rw [hB4, hcardA, hA4'])
  have hAL : A.subgroupOf Y ≤ genFittingFStar ↥Y := hBeq ▸ h2
  have hcardY : Nat.card ↥Y = 336 := card_isPGL2_seven hPGL
  have hcardL : Nat.card ↥(genFittingFStar ↥Y) = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven h1
  have hidx : (genFittingFStar ↥Y).index = 2 := by
    have := Subgroup.card_mul_index (genFittingFStar ↥Y)
    rw [hcardY, hcardL] at this
    omega
  have hLn : (genFittingFStar ↥Y).Normal := Subgroup.normal_of_index_eq_two hidx
  have hperf := isPerfect_of_isL2_seven h1
  have hLbot : genFittingFStar ↥Y ≠ ⊥ := by
    intro h
    rw [h] at hcardL
    simp at hcardL
  obtain ⟨I, hI⟩ := exists_isIrr (repOf Y) (repOf_injective Y) hperf hLbot
  obtain ⟨hnat, hrest⟩ := h3 I hI
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ↥Y, g₀ ∉ genFittingFStar ↥Y := by
    by_contra hcon
    push Not at hcon
    have htop : genFittingFStar ↥Y = ⊤ := eq_top_iff.2 fun g _ => hcon g
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨-, hdisj, hdual⟩ := hrest g₀ hg₀
  refine ⟨hPGL, hA4', (genFittingFStar ↥Y).map Y.subtype, toSubmodule I,
    toSubmodule (I.map (repOf Y g₀).toMonoidHom), ?_,
    pglConfig_of_conclusion hLn hidx hI hnat hg₀ hdisj hdual⟩
  intro a ha
  have hmem : (⟨a, hAY ha⟩ : ↥Y) ∈ A.subgroupOf Y := ha
  exact ⟨⟨a, hAY ha⟩, hAL hmem, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81

end
