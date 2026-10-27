module

public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin

namespace Twist

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  {T : Type*} [Group T] [MulAction T (Submodule R M)]

theorem equiv_map_mkQ {N : Submodule R M} (L : Submodule R M) (h : Disjoint N L) :
    Nonempty (N ≃ₗ[R] ↥(N.map L.mkQ)) := by
  have hinj : Function.Injective (L.mkQ ∘ₗ N.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.eq_bot_iff]
    intro x hx
    have : (x : M) ∈ N ⊓ L := ⟨x.2, hx⟩
    have h0 : (x : M) = 0 := by simpa using h.le_bot this
    exact Subtype.ext h0
  refine ⟨(LinearEquiv.ofInjective (L.mkQ ∘ₗ N.subtype) hinj).trans
    (LinearEquiv.ofEq _ _ ?_)⟩
  rw [LinearMap.range_comp, Submodule.range_subtype]

theorem map_mkQ_self (L : Submodule R M) : L.map L.mkQ = ⊥ := by
  rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
  intro x hx
  simp [hx]

theorem exists_card_eq_two_pow {G : Type*} [AddGroup G] [Finite G] (h : ∀ g : G, g + g = 0) :
    ∃ n : ℕ, Nat.card G = 2 ^ n := by
  have hp : IsPGroup 2 (Multiplicative G) := fun g => by
    refine ⟨1, ?_⟩
    rw [pow_one, sq]
    exact congrArg Multiplicative.ofAdd (h (Multiplicative.toAdd g))
  have hfin : Finite (Multiplicative G) := ‹Finite G›
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  exact ⟨n, hn⟩

theorem odd_card_sub_one {G : Type*} [AddGroup G] [Finite G] (h : ∀ g : G, g + g = 0)
    (hne : Nontrivial G) : Odd (Nat.card G - 1) := by
  obtain ⟨n, hn⟩ := exists_card_eq_two_pow h
  have hlt : 1 < Nat.card G := Finite.one_lt_card
  rw [hn] at hlt ⊢
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hlt
    · omega⟩
  rw [pow_succ]
  exact ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩

theorem odd_card_iso_submodules [Finite M] (hM : ∀ m : M, m + m = 0) {L N : Submodule R M}
    [IsSimpleModule R L] (hLN : L ≤ N) :
    Odd (Nat.card {ω : Submodule R M // ω ≤ N ∧ Nonempty (↥ω ≃ₗ[R] ↥L)}) := by
  classical
  have hLfin : Finite ↥L := inferInstance
  have hEfin : Finite (Module.End R ↥L) :=
    Finite.of_injective (fun f : Module.End R ↥L => (f : ↥L → ↥L)) DFunLike.coe_injective
  have hHfin : Finite (↥L →ₗ[R] M) :=
    Finite.of_injective (fun f : ↥L →ₗ[R] M => (f : ↥L → M)) DFunLike.coe_injective
  let : DivisionRing (Module.End R ↥L) := Module.End.instDivisionRing
  have hLnt : Nontrivial ↥L := IsSimpleModule.nontrivial R ↥L
  have hL2 : ∀ x : ↥L, x + x = 0 := fun x => Subtype.ext (hM x)
  let H : AddSubgroup (↥L →ₗ[R] M) :=
    { carrier := {f | ∀ x, f x ∈ N}
      zero_mem' := fun x => by simp
      add_mem' := fun {f g} hf hg x => by simpa using N.add_mem (hf x) (hg x)
      neg_mem' := fun {f} hf x => by simpa using N.neg_mem (hf x) }
  have hH2 : ∀ f : ↥H, f + f = 0 := fun f => Subtype.ext (LinearMap.ext fun x => hM _)
  have hE2 : ∀ f : Module.End R ↥L, f + f = 0 := fun f => LinearMap.ext fun x => hL2 _
  have hι : (L.subtype : ↥L →ₗ[R] M) ∈ H := fun x => hLN x.2
  have hHnt : Nontrivial ↥H := by
    refine ⟨⟨⟨L.subtype, hι⟩, 0, fun h => ?_⟩⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : ↥L)
    have h1 := congrArg (fun f : ↥H => ((f : ↥L →ₗ[R] M) x)) h
    exact hx (Subtype.ext h1)
  have hEnt : Nontrivial (Module.End R ↥L) := inferInstance
  let Ω := {ω : Submodule R M // ω ≤ N ∧ Nonempty (↥ω ≃ₗ[R] ↥L)}
  have hex : ∀ ω : Ω, ∃ _e : ↥L ≃ₗ[R] ↥ω.1, True := fun ω => ⟨ω.2.2.some.symm, trivial⟩
  choose e _ using hex
  have hu_bij : ∀ u : (Module.End R ↥L)ˣ, Function.Bijective (u : Module.End R ↥L) :=
    fun u => (Module.End.isUnit_iff _).1 u.isUnit
  let F : Ω × (Module.End R ↥L)ˣ → (↥L →ₗ[R] M) := fun p =>
    (p.1.1.subtype ∘ₗ (e p.1).toLinearMap) ∘ₗ (p.2 : Module.End R ↥L)
  have hFapply : ∀ p x, F p x = ((e p.1 ((p.2 : Module.End R ↥L) x) : ↥p.1.1) : M) := fun p x => rfl
  have hFmem : ∀ p, F p ∈ H := fun p x => p.1.2.1 (e p.1 ((p.2 : Module.End R ↥L) x)).2
  have hFne : ∀ p, F p ≠ 0 := by
    intro p hp
    obtain ⟨x, hx⟩ := exists_ne (0 : ↥L)
    have h0 : F p x = 0 := by rw [hp]; rfl
    rw [hFapply] at h0
    have h1 : e p.1 ((p.2 : Module.End R ↥L) x) = 0 := Subtype.ext h0
    have h2 : (p.2 : Module.End R ↥L) x = 0 := (e p.1).injective (by rw [h1, map_zero])
    exact hx ((hu_bij p.2).1 (by rw [h2, map_zero]))
  let Φ : Ω × (Module.End R ↥L)ˣ → {h : ↥H // h ≠ 0} := fun p =>
    ⟨⟨F p, hFmem p⟩, fun h => hFne p (congrArg Subtype.val h)⟩
  have hrange : ∀ p, LinearMap.range (F p) = p.1.1 := by
    intro p
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e p.1 ((p.2 : Module.End R ↥L) x)).2
    · intro hy
      obtain ⟨x, hx⟩ := (hu_bij p.2).2 ((e p.1).symm ⟨y, hy⟩)
      refine ⟨x, ?_⟩
      rw [hFapply, hx, LinearEquiv.apply_symm_apply]
  have hinjΦ : Function.Injective Φ := by
    rintro ⟨ω, u⟩ ⟨ω', u'⟩ h
    have hf : F (ω, u) = F (ω', u') :=
      congrArg (fun z : {h : ↥H // h ≠ 0} => ((z.1 : ↥H) : ↥L →ₗ[R] M)) h
    have hω : ω.1 = ω'.1 := by rw [← hrange (ω, u), ← hrange (ω', u'), hf]
    have hωω : ω = ω' := Subtype.ext hω
    subst hωω
    have huu : u = u' := by
      apply Units.ext
      apply LinearMap.ext
      intro x
      have h1 := congrArg (fun f : ↥L →ₗ[R] M => f x) hf
      exact (e ω).injective (Subtype.ext h1)
    rw [huu]
  have hsurjΦ : Function.Surjective Φ := by
    rintro ⟨⟨f, hf⟩, hne⟩
    have hfne : f ≠ 0 := fun h => hne (Subtype.ext h)
    have hfinj : Function.Injective f := LinearMap.injective_of_ne_zero hfne
    let ω : Ω := ⟨LinearMap.range f, by rintro _ ⟨x, rfl⟩; exact hf x,
      ⟨(LinearEquiv.ofInjective f hfinj).symm⟩⟩
    let g : Module.End R ↥L := ((e ω).symm : ↥ω.1 ≃ₗ[R] ↥L).toLinearMap ∘ₗ
      (f.codRestrict ω.1 (fun x => ⟨x, rfl⟩))
    have hgapply : ∀ x, e ω (g x) = ⟨f x, ⟨x, rfl⟩⟩ := fun x => (e ω).apply_symm_apply _
    have hg : g ≠ 0 := by
      intro h0
      obtain ⟨x, hx⟩ := exists_ne (0 : ↥L)
      have h1 : g x = 0 := by rw [h0]; rfl
      have h2 : f x = 0 := by
        have := hgapply x
        rw [h1, map_zero] at this
        exact congrArg Subtype.val this.symm
      exact hx (hfinj (by rw [h2, map_zero]))
    have hgunit : IsUnit g := isUnit_iff_ne_zero.2 hg
    refine ⟨(ω, hgunit.unit), Subtype.ext (Subtype.ext (LinearMap.ext fun x => ?_))⟩
    change ((e ω (g x) : ↥ω.1) : M) = f x
    rw [hgapply]
  have hcardΦ : Nat.card Ω * Nat.card (Module.End R ↥L)ˣ = Nat.card {h : ↥H // h ≠ 0} := by
    rw [← Nat.card_prod]
    exact Nat.card_eq_of_bijective Φ ⟨hinjΦ, hsurjΦ⟩
  have hH : Nat.card {h : ↥H // h ≠ 0} + 1 = Nat.card ↥H := by
    have h1 := Nat.card_congr (Equiv.optionSubtypeNe (0 : ↥H))
    rw [Finite.card_option] at h1
    exact h1
  have hOddH : Odd (Nat.card ↥H - 1) := odd_card_sub_one hH2 hHnt
  have hOddE : Odd (Nat.card (Module.End R ↥L)ˣ) := by
    rw [Nat.card_units]
    exact odd_card_sub_one hE2 hEnt
  have hodd : Odd (Nat.card Ω * Nat.card (Module.End R ↥L)ˣ) := by
    rw [hcardΦ]
    have : Nat.card {h : ↥H // h ≠ 0} = Nat.card ↥H - 1 := by omega
    rw [this]
    exact hOddH
  exact (Nat.odd_mul.1 hodd).1

theorem sSupIndep_range_iff {α : Type*} [CompleteLattice α] {ι : Type*} (f : ι → α) :
    sSupIndep (Set.range f) ↔ ∀ i, Disjoint (f i) (⨆ j : {j : ι // f j ≠ f i}, f j.1) := by
  have key : ∀ i, sSup (Set.range f \ {f i}) = ⨆ j : {j : ι // f j ≠ f i}, f j.1 := by
    intro i
    refine le_antisymm (sSup_le ?_) (iSup_le fun j => le_sSup ⟨⟨j.1, rfl⟩, j.2⟩)
    rintro _ ⟨⟨j, rfl⟩, hj⟩
    exact le_iSup (fun j : {j : ι // f j ≠ f i} => f j.1) ⟨j, hj⟩
  constructor
  · intro h i
    rw [← key i]
    exact h ⟨i, rfl⟩
  · rintro h _ ⟨i, rfl⟩
    rw [key i]
    exact h i

variable (T) in
@[expose] def orbitSup (L : Submodule R M) : Submodule R M := ⨆ t : T, t • L

theorem smul_le_orbitSup (t : T) (L : Submodule R M) : t • L ≤ orbitSup T L :=
  le_iSup (fun r : T => r • L) t

theorem le_orbitSup (L : Submodule R M) : L ≤ orbitSup T L := by
  simpa using smul_le_orbitSup (1 : T) L

variable (R M T) in
structure IsTwist : Prop where
  le_iff : ∀ (t : T) (N N' : Submodule R M), t • N ≤ t • N' ↔ N ≤ N'
  iso : ∀ (t : T) (N N' : Submodule R M),
    Nonempty (N ≃ₗ[R] N') → Nonempty (↥(t • N) ≃ₗ[R] ↥(t • N'))

namespace IsTwist

variable (hT : IsTwist R M T)

include hT

@[expose] def orderIso (t : T) : Submodule R M ≃o Submodule R M where
  toEquiv := MulAction.toPerm t
  map_rel_iff' := hT.le_iff t _ _

theorem isAtom_smul (t : T) {N : Submodule R M} : IsAtom (t • N) ↔ IsAtom N :=
  (hT.orderIso t).isAtom_iff N

theorem isSimple_smul (t : T) {N : Submodule R M} :
    IsSimpleModule R ↥(t • N) ↔ IsSimpleModule R ↥N := by
  rw [isSimpleModule_iff_isAtom, isSimpleModule_iff_isAtom]
  exact hT.isAtom_smul t

theorem smul_iSup (t : T) {ι : Sort*} (N : ι → Submodule R M) :
    t • ⨆ i, N i = ⨆ i, t • N i :=
  (hT.orderIso t).map_iSup N

theorem nonempty_equiv_smul_iff (t : T) {N N' : Submodule R M} :
    Nonempty (↥(t • N) ≃ₗ[R] ↥(t • N')) ↔ Nonempty (N ≃ₗ[R] N') := by
  refine ⟨fun h => ?_, hT.iso t N N'⟩
  have h1 := hT.iso t⁻¹ _ _ h
  rwa [inv_smul_smul, inv_smul_smul] at h1

@[expose] def stab (L : Submodule R M) : Subgroup T where
  carrier := {t | Nonempty (↥(t • L) ≃ₗ[R] ↥L)}
  one_mem' := by
    change Nonempty (↥((1 : T) • L) ≃ₗ[R] ↥L)
    rw [one_smul]
    exact ⟨LinearEquiv.refl R _⟩
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨e1⟩ := ha
    obtain ⟨e2⟩ := hb
    obtain ⟨e3⟩ := hT.iso a _ _ ⟨e2⟩
    change Nonempty (↥((a * b) • L) ≃ₗ[R] ↥L)
    rw [mul_smul]
    exact ⟨e3.trans e1⟩
  inv_mem' := fun {a} ha => by
    obtain ⟨e⟩ := ha
    obtain ⟨e'⟩ := hT.iso a⁻¹ _ _ ⟨e⟩
    rw [inv_smul_smul] at e'
    exact ⟨e'.symm⟩

theorem mem_stab_iff {L : Submodule R M} {t : T} :
    t ∈ stab hT L ↔ Nonempty (↥(t • L) ≃ₗ[R] ↥L) := Iff.rfl

theorem nonempty_equiv_conj_iff {L : Submodule R M} {t r : T} :
    Nonempty (↥(t • L) ≃ₗ[R] ↥(r • L)) ↔ r⁻¹ * t ∈ stab hT L := by
  rw [mem_stab_iff, mul_smul]
  constructor
  · intro h
    have h1 := (hT.nonempty_equiv_smul_iff r⁻¹).2 h
    rwa [inv_smul_smul] at h1
  · intro h
    have h1 := (hT.nonempty_equiv_smul_iff r).2 h
    rwa [smul_inv_smul] at h1

theorem smul_orbitSup (t : T) (L : Submodule R M) : t • orbitSup T L = orbitSup T L := by
  unfold orbitSup
  rw [hT.smul_iSup]
  simp_rw [smul_smul]
  exact (Equiv.mulLeft t).iSup_comp (g := fun r : T => r • L)

theorem le_of_iso_of_stab_smul_eq {L : Submodule R M} [IsSimpleModule R L]
    (hS : ∀ s ∈ stab hT L, s • L = L) {L' : Submodule R M} (hL' : L' ≤ orbitSup T L)
    [IsSimpleModule R L'] (hiso : Nonempty (L' ≃ₗ[R] L)) : L' ≤ L := by
  by_contra hnle
  have hLatom : IsAtom L := isSimpleModule_iff_isAtom.1 inferInstance
  have hL'atom : IsAtom L' := isSimpleModule_iff_isAtom.1 inferInstance
  have hdisj : Disjoint L' L := hL'atom.not_le_iff_disjoint.1 hnle
  let G : Set (Submodule R (M ⧸ L)) := {c | ∃ t : T, t • L ≠ L ∧ c = (t • L).map L.mkQ}
  have hGsimple : ∀ c : G, IsSimpleModule R ↥(c : Submodule R (M ⧸ L)) := by
    rintro ⟨c, t, ht, rfl⟩
    have hat : IsAtom (t • L) := (hT.isAtom_smul t).2 hLatom
    obtain ⟨e⟩ := equiv_map_mkQ L (hat.disjoint_of_ne hLatom ht)
    have : IsSimpleModule R ↥(t • L) := isSimpleModule_iff_isAtom.2 hat
    exact IsSimpleModule.congr e.symm
  obtain ⟨e3⟩ := equiv_map_mkQ L hdisj
  have hsimple' : IsSimpleModule R ↥(L'.map L.mkQ) := IsSimpleModule.congr e3.symm
  have hmap : L'.map L.mkQ ≤ sSup G := by
    refine (Submodule.map_mono hL').trans ?_
    unfold orbitSup
    rw [Submodule.map_iSup]
    refine iSup_le fun t => ?_
    by_cases ht : t • L = L
    · rw [ht, map_mkQ_self]
      exact bot_le
    · exact le_sSup ⟨t, ht, rfl⟩
  obtain ⟨c, ⟨t, ht, rfl⟩, ⟨e2⟩⟩ := Submodule.linearEquiv_of_le_sSup (L'.map L.mkQ) G hmap
  have hat : IsAtom (t • L) := (hT.isAtom_smul t).2 hLatom
  obtain ⟨e1⟩ := equiv_map_mkQ L (hat.disjoint_of_ne hLatom ht)
  have hst : t ∈ stab hT L := ⟨e1.trans (e2.symm.trans (e3.symm.trans hiso.some))⟩
  exact ht (hS t hst)

theorem conj_eq_of_equiv {L : Submodule R M} (hS : ∀ s ∈ stab hT L, s • L = L) {t r : T}
    (h : Nonempty (↥(t • L) ≃ₗ[R] ↥(r • L))) : t • L = r • L := by
  have h1 : r⁻¹ * t ∈ stab hT L := (nonempty_equiv_conj_iff hT).1 h
  have h2 := hS _ h1
  calc t • L = r • (r⁻¹ * t) • L := by rw [smul_smul, mul_inv_cancel_left]
    _ = r • L := by rw [h2]

theorem sSupIndep_conj {L : Submodule R M} [IsSimpleModule R L]
    (hS : ∀ s ∈ stab hT L, s • L = L) : sSupIndep (Set.range fun t : T => t • L) := by
  have hLatom : IsAtom L := isSimpleModule_iff_isAtom.1 inferInstance
  intro c hc
  obtain ⟨t, rfl⟩ := hc
  have hat : IsAtom (t • L) := (hT.isAtom_smul t).2 hLatom
  rw [← hat.not_le_iff_disjoint]
  intro hle
  have hsimple : ∀ m : ↥((Set.range fun t : T => t • L) \ {t • L}),
      IsSimpleModule R ↥(m : Submodule R M) := by
    rintro ⟨_, ⟨r, rfl⟩, -⟩
    exact isSimpleModule_iff_isAtom.2 ((hT.isAtom_smul r).2 hLatom)
  have : IsSimpleModule R ↥(t • L) := isSimpleModule_iff_isAtom.2 hat
  obtain ⟨S, ⟨⟨r, rfl⟩, hne⟩, hiso⟩ :=
    Submodule.linearEquiv_of_le_sSup (t • L) _ hle
  exact hne (conj_eq_of_equiv hT hS hiso).symm

theorem disjoint_conj_iSup {L : Submodule R M} [IsSimpleModule R L]
    (hS : ∀ s ∈ stab hT L, s • L = L) (t : T) :
    Disjoint (t • L) (⨆ r : {r : T // r • L ≠ t • L}, r.1 • L) :=
  (sSupIndep_range_iff (fun t : T => t • L)).1 (sSupIndep_conj hT hS) t

theorem smul_eq_of_forall_le {L : Submodule R M} [IsSimpleModule R L]
    (h : ∀ L' : Submodule R M, L' ≤ orbitSup T L → IsSimpleModule R ↥L' →
      Nonempty (↥L' ≃ₗ[R] ↥L) → L' ≤ L) :
    ∀ s ∈ stab hT L, s • L = L := by
  intro s hs
  have hLatom : IsAtom L := isSimpleModule_iff_isAtom.1 inferInstance
  have hat : IsAtom (s • L) := (hT.isAtom_smul s).2 hLatom
  have hle : s • L ≤ L :=
    h _ (smul_le_orbitSup s L) (isSimpleModule_iff_isAtom.2 hat) hs
  exact (hLatom.le_iff_eq hat.1).1 hle

theorem exists_isHomComp [Finite M] (hM : ∀ m : M, m + m = 0) (hp : IsPGroup 2 T)
    (L : Submodule R M) [IsSimpleModule R L] :
    ∃ L' : Submodule R M, L' ≤ orbitSup T L ∧ IsSimpleModule R ↥L' ∧
      Nonempty (↥L' ≃ₗ[R] ↥L) ∧
      ∀ L'' : Submodule R M, L'' ≤ orbitSup T L' → IsSimpleModule R ↥L'' →
        Nonempty (↥L'' ≃ₗ[R] ↥L') → L'' ≤ L' := by
  classical
  have hfinM : Finite (Submodule R M) :=
    Finite.of_injective (fun N : Submodule R M => (N : Set M)) SetLike.coe_injective
  let Ω := {ω : Submodule R M // ω ≤ orbitSup T L ∧ Nonempty (↥ω ≃ₗ[R] ↥L)}
  have hΩodd : Odd (Nat.card Ω) := odd_card_iso_submodules hM (le_orbitSup L)
  have hsm : ∀ (s : ↥(stab hT L)) (ω : Ω), (s : T) • ω.1 ≤ orbitSup T L ∧
      Nonempty (↥((s : T) • ω.1) ≃ₗ[R] ↥L) := by
    intro s ω
    refine ⟨?_, ?_⟩
    · calc (s : T) • ω.1 ≤ (s : T) • orbitSup T L := (hT.le_iff _ _ _).2 ω.2.1
        _ = orbitSup T L := smul_orbitSup hT _ L
    · obtain ⟨e⟩ := hT.iso (s : T) _ _ ω.2.2
      obtain ⟨e'⟩ := s.2
      exact ⟨e.trans e'⟩
  let act : MulAction ↥(stab hT L) Ω :=
    { smul := fun s ω => ⟨(s : T) • ω.1, hsm s ω⟩
      one_smul := fun ω => Subtype.ext (one_smul T ω.1)
      mul_smul := fun s s' ω => Subtype.ext (mul_smul (s : T) (s' : T) ω.1) }
  have hpS : IsPGroup 2 ↥(stab hT L) := hp.to_subgroup _
  have hmod := @IsPGroup.card_modEq_card_fixedPoints 2 ↥(stab hT L) _ hpS _ Ω act _
  have hfixodd : Nat.card ↑(@MulAction.fixedPoints ↥(stab hT L) Ω _ act) % 2 = 1 := by
    have h1 : Nat.card Ω % 2 = 1 := Nat.odd_iff.1 hΩodd
    have h2 : Nat.card Ω % 2 =
        Nat.card ↑(@MulAction.fixedPoints ↥(stab hT L) Ω _ act) % 2 := hmod
    omega
  have hnonempty : Nonempty ↑(@MulAction.fixedPoints ↥(stab hT L) Ω _ act) := by
    rw [← Finite.card_pos_iff]
    omega
  obtain ⟨⟨ω, hω⟩⟩ := hnonempty
  have hωfix : ∀ s : ↥(stab hT L), (s : T) • ω.1 = ω.1 := fun s =>
    congrArg Subtype.val (@MulAction.mem_fixedPoints ↥(stab hT L) Ω _ act ω |>.1 hω s)
  obtain ⟨hωle, ⟨hωiso⟩⟩ := ω.2
  have hsimple : IsSimpleModule R ↥ω.1 := IsSimpleModule.congr hωiso
  refine ⟨ω.1, hωle, hsimple, ⟨hωiso⟩, ?_⟩
  have hS' : ∀ s ∈ stab hT ω.1, s • ω.1 = ω.1 := by
    intro s hs
    obtain ⟨e1⟩ := hs
    obtain ⟨e2⟩ := hT.iso s _ _ ⟨hωiso⟩
    have hsL : s ∈ stab hT L := ⟨e2.symm.trans (e1.trans hωiso)⟩
    exact hωfix ⟨s, hsL⟩
  intro L'' hL''le hL''simple hL''iso
  exact le_of_iso_of_stab_smul_eq hT hS' hL''le hL''iso

end IsTwist

end Twist

end CFSG.Quasithin
