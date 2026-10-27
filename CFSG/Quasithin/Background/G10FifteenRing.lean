module

public import CFSG.Quasithin.Background.A1cModuleSemisimple
public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def hRing (H : Subgroup (GLV V)) : Subring (Module.End (ZMod 2) V) :=
  Subring.closure (Set.range fun h : H => ((h : GLV V) : V →ₗ[ZMod 2] V))

theorem hRing_apply_mem {H : Subgroup (GLV V)} {h : GLV V} (hh : h ∈ H) :
    ((h : GLV V) : V →ₗ[ZMod 2] V) ∈ hRing H :=
  Subring.subset_closure ⟨⟨h, hh⟩, rfl⟩

@[expose] def stabRing (U : Submodule (ZMod 2) V) : Subring (Module.End (ZMod 2) V) where
  carrier := {f | ∀ u ∈ U, f u ∈ U}
  mul_mem' := fun {f g} hf hg u hu => hf _ (hg u hu)
  one_mem' := fun u hu => hu
  add_mem' := fun {f g} hf hg u hu => by
    rw [LinearMap.add_apply]
    exact U.add_mem (hf u hu) (hg u hu)
  zero_mem' := fun u _ => by
    rw [LinearMap.zero_apply]
    exact U.zero_mem
  neg_mem' := fun {f} hf u hu => by
    rw [LinearMap.neg_apply]
    exact U.neg_mem (hf u hu)

theorem hRing_le_stabRing {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (hU : Invariant H U) :
    hRing H ≤ stabRing U := by
  rw [hRing, Subring.closure_le]
  rintro _ ⟨h, rfl⟩ u hu
  exact hU h h.2 u hu

@[expose] def toR {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (hU : Invariant H U) :
    Submodule (hRing H) V where
  carrier := U
  add_mem' := fun {_ _} ha hb => U.add_mem ha hb
  zero_mem' := U.zero_mem
  smul_mem' := fun r u hu => hRing_le_stabRing hU r.2 u hu

theorem mem_toR {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (hU : Invariant H U) {v : V} :
    v ∈ toR hU ↔ v ∈ U := Iff.rfl

theorem hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

@[expose] def ofR {H : Subgroup (GLV V)} (N : Submodule (hRing H) V) : Submodule (ZMod 2) V where
  carrier := N
  add_mem' := fun {_ _} ha hb => N.add_mem ha hb
  zero_mem' := N.zero_mem
  smul_mem' := fun c v hv => by
    rcases hc2 c with rfl | rfl
    · rw [zero_smul]
      exact N.zero_mem
    · rw [one_smul]
      exact hv

theorem mem_ofR {H : Subgroup (GLV V)} {N : Submodule (hRing H) V} {v : V} :
    v ∈ ofR N ↔ v ∈ N := Iff.rfl

theorem invariant_ofR {H : Subgroup (GLV V)} (N : Submodule (hRing H) V) : Invariant H (ofR N) :=
  fun h hh _ hv =>
    N.smul_mem (⟨((h : GLV V) : V →ₗ[ZMod 2] V), hRing_apply_mem hh⟩ : hRing H) hv

@[simp] theorem ofR_toR {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (hU : Invariant H U) :
    ofR (toR hU) = U := rfl

@[simp] theorem toR_ofR {H : Subgroup (GLV V)} (N : Submodule (hRing H) V) :
    toR (invariant_ofR N) = N := rfl

theorem toR_le_iff {H : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V} (hU : Invariant H U)
    (hU' : Invariant H U') : toR hU ≤ toR hU' ↔ U ≤ U' := Iff.rfl

theorem toR_injective {H : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V} (hU : Invariant H U)
    (hU' : Invariant H U') (h : toR hU = toR hU') : U = U' :=
  le_antisymm ((toR_le_iff hU hU').1 h.le) ((toR_le_iff hU' hU).1 h.ge)

theorem toR_bot (H : Subgroup (GLV V)) : toR (invariant_bot H) = (⊥ : Submodule (hRing H) V) := by
  ext v
  rw [mem_toR, Submodule.mem_bot, Submodule.mem_bot]

theorem toR_eq_bot_iff {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (hU : Invariant H U) :
    toR hU = ⊥ ↔ U = ⊥ := by
  constructor
  · intro h
    have := toR_injective hU (invariant_bot H) (h.trans (toR_bot H).symm)
    exact this
  · rintro rfl
    exact toR_bot H

theorem isIrr_iff_simple {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (hU : Invariant H U) :
    IsIrr H U ↔ IsSimpleModule (hRing H) ↥(toR hU) := by
  rw [isSimpleModule_iff_isAtom]
  constructor
  · rintro ⟨-, hlt, hirr⟩
    refine ⟨fun h => ?_, fun b hb => ?_⟩
    · have := (toR_eq_bot_iff hU).1 h
      exact hlt.ne (this.symm)
    · have hbU : ofR b ≤ U := hb.le
      rcases hirr (ofR b) (invariant_ofR b) bot_le hbU with h | h
      · have : b = toR (invariant_ofR b) := rfl
        rw [this, (toR_eq_bot_iff _)]
        exact h
      · exfalso
        apply hb.ne
        ext v
        rw [← mem_ofR, h]
        rfl
  · rintro ⟨hne, hmin⟩
    refine ⟨hU, bot_lt_iff_ne_bot.2 fun h => hne ((toR_eq_bot_iff hU).2 h), fun J hJ _ hJU => ?_⟩
    rcases hJU.lt_or_eq with h | h
    · left
      have := hmin (toR hJ) ((toR_le_iff hJ hU).2 hJU |>.lt_of_ne fun h' =>
        h.ne (toR_injective hJ hU h'))
      exact (toR_eq_bot_iff hJ).1 this
    · right
      exact h

theorem hiso_of_equiv {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V} (hI : Invariant H I)
    (hJ : Invariant H J) (e : ↥(toR hI) ≃ₗ[hRing H] ↥(toR hJ)) : HIso H I J := by
  refine ⟨{ toFun := fun i => ⟨(e ⟨i.1, i.2⟩).1, (e ⟨i.1, i.2⟩).2⟩
            invFun := fun j => ⟨(e.symm ⟨j.1, j.2⟩).1, (e.symm ⟨j.1, j.2⟩).2⟩
            map_add' := fun a b => Subtype.ext (congrArg Subtype.val (e.map_add ⟨a.1, a.2⟩ ⟨b.1, b.2⟩))
            map_smul' := fun c a => by
              rcases hc2 c with rfl | rfl
              · simp only [zero_smul, RingHom.id_apply]
                exact Subtype.ext (congrArg Subtype.val e.map_zero)
              · simp only [one_smul, RingHom.id_apply]
            left_inv := fun a => Subtype.ext (congrArg Subtype.val (e.symm_apply_apply ⟨a.1, a.2⟩))
            right_inv := fun b => Subtype.ext (congrArg Subtype.val (e.apply_symm_apply ⟨b.1, b.2⟩)) },
    fun k hk i j hkij => ?_⟩
  let r : hRing H := ⟨((k : GLV V) : V →ₗ[ZMod 2] V), hRing_apply_mem hk⟩
  have h1 : r • (⟨i.1, i.2⟩ : ↥(toR hI)) = ⟨j.1, j.2⟩ := Subtype.ext hkij
  have h2 := e.map_smul r ⟨i.1, i.2⟩
  rw [h1] at h2
  exact (congrArg Subtype.val h2).symm

theorem hiso_ring_apply {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V} (hI : Invariant H I)
    {φ : ↥I ≃ₗ[ZMod 2] ↥J}
    (hφ : ∀ k ∈ H, ∀ i j : ↥I, (k : GLV V) (i : V) = (j : V) →
      (k : GLV V) ((φ i : ↥J) : V) = ((φ j : ↥J) : V))
    {f : Module.End (ZMod 2) V} (hf : f ∈ hRing H) (x : ↥I) :
    ((φ ⟨f x, hRing_le_stabRing hI hf x x.2⟩ : ↥J) : V) = f ((φ x : ↥J) : V) := by
  have key : ∀ f ∈ Subring.closure (Set.range fun h : H => ((h : GLV V) : V →ₗ[ZMod 2] V)),
      ∀ (x : ↥I) (hx : f x ∈ I), ((φ ⟨f x, hx⟩ : ↥J) : V) = f ((φ x : ↥J) : V) := by
    intro f hf
    induction hf using Subring.closure_induction with
    | mem f hf =>
      obtain ⟨h, rfl⟩ := hf
      intro x hx
      exact (hφ (h : GLV V) h.2 x ⟨(h : GLV V) (x : V), hx⟩ rfl).symm
    | zero =>
      intro x hx
      have : (⟨(0 : Module.End (ZMod 2) V) x, hx⟩ : ↥I) = 0 := Subtype.ext rfl
      rw [this, map_zero]
      rfl
    | one =>
      intro x hx
      exact rfl
    | add f g hfm hgm hf hg =>
      intro x hx
      have hfx : f x ∈ I := hRing_le_stabRing hI hfm x x.2
      have hgx : g x ∈ I := hRing_le_stabRing hI hgm x x.2
      have : (⟨(f + g) x, hx⟩ : ↥I) = ⟨f x, hfx⟩ + ⟨g x, hgx⟩ := Subtype.ext rfl
      rw [this, map_add]
      show ((φ ⟨f x, hfx⟩ : ↥J) : V) + ((φ ⟨g x, hgx⟩ : ↥J) : V) = _
      rw [hf x hfx, hg x hgx]
      rfl
    | neg f hfm hf =>
      intro x hx
      have hfx : f x ∈ I := hRing_le_stabRing hI hfm x x.2
      have : (⟨(-f) x, hx⟩ : ↥I) = -⟨f x, hfx⟩ := Subtype.ext rfl
      rw [this, map_neg]
      show -((φ ⟨f x, hfx⟩ : ↥J) : V) = _
      rw [hf x hfx]
      rfl
    | mul f g hfm hgm hf hg =>
      intro x hx
      have hgx : g x ∈ I := hRing_le_stabRing hI hgm x x.2
      have h1 := hg x hgx
      have h2 := hf ⟨g x, hgx⟩ hx
      show ((φ ⟨f (g x), hx⟩ : ↥J) : V) = f (g ((φ x : ↥J) : V))
      rw [← h1]
      exact h2
  exact key f hf x _

theorem equiv_of_hiso {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V} (hI : Invariant H I)
    (hJ : Invariant H J) (h : HIso H I J) :
    Nonempty (↥(toR hI) ≃ₗ[hRing H] ↥(toR hJ)) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨{ toFun := fun x => ⟨((φ ⟨x.1, x.2⟩ : ↥J) : V), (φ ⟨x.1, x.2⟩).2⟩
            invFun := fun y => ⟨((φ.symm ⟨y.1, y.2⟩ : ↥I) : V), (φ.symm ⟨y.1, y.2⟩).2⟩
            map_add' := fun a b => Subtype.ext (congrArg Subtype.val (φ.map_add ⟨a.1, a.2⟩ ⟨b.1, b.2⟩))
            map_smul' := fun r a => ?_
            left_inv := fun a => Subtype.ext (congrArg Subtype.val (φ.symm_apply_apply ⟨a.1, a.2⟩))
            right_inv := fun b => Subtype.ext (congrArg Subtype.val (φ.apply_symm_apply ⟨b.1, b.2⟩)) }⟩
  apply Subtype.ext
  have hra : (r • a : ↥(toR hI)).1 = (r : Module.End (ZMod 2) V) a.1 := rfl
  have := hiso_ring_apply hI hφ r.2 ⟨a.1, a.2⟩
  show ((φ ⟨(r • a).1, (r • a).2⟩ : ↥J) : V) = (r : Module.End (ZMod 2) V) ((φ ⟨a.1, a.2⟩ : ↥J) : V)
  exact this

theorem hiso_iff {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V} (hI : Invariant H I)
    (hJ : Invariant H J) :
    HIso H I J ↔ Nonempty (↥(toR hI) ≃ₗ[hRing H] ↥(toR hJ)) :=
  ⟨equiv_of_hiso hI hJ, fun ⟨e⟩ => hiso_of_equiv hI hJ e⟩

theorem hiso_refl {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} (_hI : Invariant H I) :
    HIso H I I :=
  ⟨LinearEquiv.refl (ZMod 2) ↥I, fun _ _ _ _ h => h⟩

theorem hiso_symm {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V} (hI : Invariant H I)
    (hJ : Invariant H J) (h : HIso H I J) : HIso H J I := by
  obtain ⟨e⟩ := equiv_of_hiso hI hJ h
  exact hiso_of_equiv hJ hI e.symm

theorem hiso_trans {H : Subgroup (GLV V)} {I J K : Submodule (ZMod 2) V} (hI : Invariant H I)
    (hJ : Invariant H J) (hK : Invariant H K) (h : HIso H I J) (h' : HIso H J K) :
    HIso H I K := by
  obtain ⟨e⟩ := equiv_of_hiso hI hJ h
  obtain ⟨e'⟩ := equiv_of_hiso hJ hK h'
  exact hiso_of_equiv hI hK (e.trans e')

theorem centralizerOn_eq_of_hiso {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V}
    (hI : Invariant H I) (hJ : Invariant H J) (h : HIso H I J) :
    centralizerOn H I = centralizerOn H J := by
  have key : ∀ {I J : Submodule (ZMod 2) V}, HIso H I J → ∀ k ∈ centralizerOn H I,
      k ∈ centralizerOn H J := by
    intro I J h k hk
    obtain ⟨φ, hφ⟩ := h
    refine ⟨hk.1, fun j hj => ?_⟩
    obtain ⟨i, hi⟩ := φ.surjective ⟨j, hj⟩
    have h1 := hφ k hk.1 i i (hk.2 i i.2)
    have h2 : ((φ i : ↥J) : V) = j := congrArg Subtype.val hi
    rw [h2] at h1
    exact h1
  ext k
  exact ⟨key h k, key (hiso_symm hI hJ h) k⟩

@[expose] def linEquivOfAdd {U U' : Submodule (ZMod 2) V} (f : ↥U → ↥U') (g : ↥U' → ↥U)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hl : ∀ a, g (f a) = a) (hr : ∀ b, f (g b) = b) :
    ↥U ≃ₗ[ZMod 2] ↥U' where
  toFun := f
  invFun := g
  map_add' := hadd
  map_smul' := fun c a => by
    rcases hc2 c with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      have h0 := hadd 0 0
      rw [add_zero] at h0
      simpa using h0
    · simp
  left_inv := hl
  right_inv := hr

theorem hiso_conj {Γ H : Subgroup (GLV V)} (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    {x : GLV V} (hx : x ∈ Γ) {I J : Submodule (ZMod 2) V} (h : HIso H I J) :
    HIso H (conjSub x I) (conjSub x J) := by
  obtain ⟨φ, hφ⟩ := h
  have hmem : ∀ {U : Submodule (ZMod 2) V} (w : ↥(conjSub x U)), x.symm (w : V) ∈ U :=
    fun w => mem_conjSub.1 w.2
  have hmem' : ∀ {U : Submodule (ZMod 2) V} (u : ↥U), x (u : V) ∈ conjSub x U :=
    fun u => apply_mem_conjSub u.2
  let f : ↥(conjSub x I) → ↥(conjSub x J) := fun w =>
    ⟨x ((φ ⟨x.symm (w : V), hmem w⟩ : ↥J) : V), hmem' _⟩
  let g : ↥(conjSub x J) → ↥(conjSub x I) := fun w =>
    ⟨x ((φ.symm ⟨x.symm (w : V), hmem w⟩ : ↥I) : V), hmem' _⟩
  have hf : ∀ w, ((f w : ↥(conjSub x J)) : V) = x ((φ ⟨x.symm (w : V), hmem w⟩ : ↥J) : V) :=
    fun w => rfl
  refine ⟨linEquivOfAdd f g (fun a b => ?_) (fun a => ?_) (fun b => ?_),
    fun k hk w w' hkw => ?_⟩
  · apply Subtype.ext
    have : (⟨x.symm ((a + b : ↥(conjSub x I)) : V), hmem _⟩ : ↥I) =
        ⟨x.symm (a : V), hmem a⟩ + ⟨x.symm (b : V), hmem b⟩ := Subtype.ext (by simp)
    show x ((φ ⟨x.symm ((a + b : ↥(conjSub x I)) : V), hmem _⟩ : ↥J) : V) = _
    rw [this, φ.map_add]
    simp only [Submodule.coe_add, map_add]
    rfl
  · apply Subtype.ext
    show x ((φ.symm ⟨x.symm (x ((φ ⟨x.symm (a : V), hmem a⟩ : ↥J) : V)), _⟩ : ↥I) : V) = _
    have : (⟨x.symm (x ((φ ⟨x.symm (a : V), hmem a⟩ : ↥J) : V)), hmem (f a)⟩ : ↥J) =
        φ ⟨x.symm (a : V), hmem a⟩ := Subtype.ext (by simp)
    rw [this, φ.symm_apply_apply]
    simp
  · apply Subtype.ext
    show x ((φ ⟨x.symm (x ((φ.symm ⟨x.symm (b : V), hmem b⟩ : ↥I) : V)), _⟩ : ↥J) : V) = _
    have : (⟨x.symm (x ((φ.symm ⟨x.symm (b : V), hmem b⟩ : ↥I) : V)), hmem (g b)⟩ : ↥I) =
        φ.symm ⟨x.symm (b : V), hmem b⟩ := Subtype.ext (by simp)
    rw [this, φ.apply_symm_apply]
    simp
  · have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ H := hN x⁻¹ (Γ.inv_mem hx) k hk
    simp only [inv_inv] at hk'
    have h1 : (x⁻¹ * k * x : GLV V) ((⟨x.symm (w : V), hmem w⟩ : ↥I) : V) =
        ((⟨x.symm (w' : V), hmem w'⟩ : ↥I) : V) := by
      show x.symm (k (x (x.symm (w : V)))) = x.symm (w' : V)
      rw [LinearEquiv.apply_symm_apply, hkw]
    have h2 := hφ _ hk' ⟨x.symm (w : V), hmem w⟩ ⟨x.symm (w' : V), hmem w'⟩ h1
    show k ((f w : ↥(conjSub x J)) : V) = ((f w' : ↥(conjSub x J)) : V)
    rw [hf w, hf w']
    have h3 : (x⁻¹ * k * x : GLV V) ((φ ⟨x.symm (w : V), hmem w⟩ : ↥J) : V) =
        x.symm (k (x ((φ ⟨x.symm (w : V), hmem w⟩ : ↥J) : V))) := rfl
    rw [h3] at h2
    show k (x ((φ ⟨x.symm (w : V), hmem w⟩ : ↥J) : V)) = x ((φ ⟨x.symm (w' : V), hmem w'⟩ : ↥J) : V)
    rw [← h2]
    simp

theorem irr_le_sSup {H : Subgroup (GLV V)} {K : Submodule (ZMod 2) V} (hK : IsIrr H K)
    {S : Set (Submodule (ZMod 2) V)} (hS : ∀ J ∈ S, IsIrr H J) (hKS : K ≤ sSup S) :
    ∃ J ∈ S, HIso H K J := by
  let S' : Set (Submodule (hRing H) V) := {N | ofR N ∈ S}
  have hsimple : ∀ m : S', IsSimpleModule (hRing H) ↥(m : Submodule (hRing H) V) := by
    rintro ⟨N, hN⟩
    exact (isIrr_iff_simple (invariant_ofR N)).1 (hS _ hN)
  have hle : toR hK.1 ≤ sSup S' := by
    have h1 : sSup S ≤ ofR (sSup S') := by
      refine sSup_le fun J hJ v hv => ?_
      have hN : toR (hS J hJ).1 ∈ S' := by
        show ofR (toR (hS J hJ).1) ∈ S
        exact hJ
      exact le_sSup hN hv
    exact fun v hv => h1 (hKS hv)
  have : IsSimpleModule (hRing H) ↥(toR hK.1) := (isIrr_iff_simple hK.1).1 hK
  obtain ⟨N, hN, ⟨e⟩⟩ := Submodule.linearEquiv_of_le_sSup (toR hK.1) S' (simple := hsimple) hle
  exact ⟨ofR N, hN, hiso_of_equiv hK.1 (invariant_ofR N) e⟩

theorem sSup_irr_le_eq [Finite V] {H : Subgroup (GLV V)}
    (hV : sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤) {U : Submodule (ZMod 2) V}
    (hU : Invariant H U) : sSup {J | IsIrr H J ∧ J ≤ U} = U := by
  set U₀ := sSup {J | IsIrr H J ∧ J ≤ U} with hU₀
  have hU₀le : U₀ ≤ U := sSup_le fun J hJ => hJ.2
  have hU₀inv : Invariant H U₀ := invariant_sSup fun J hJ => hJ.1.1
  refine le_antisymm hU₀le ?_
  obtain ⟨U₀', hU₀'inv, hcompl⟩ := exists_invariant_compl hV hU₀inv
  by_cases hZ : U ⊓ U₀' = ⊥
  · intro u hu
    have hu' : u ∈ U₀ ⊔ U₀' := by
      rw [codisjoint_iff.1 hcompl.codisjoint]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hu'
    have hbU : b ∈ U := by
      have : b = (a + b) - a := by abel
      rw [this]
      exact U.sub_mem hu (hU₀le ha)
    have : b ∈ U ⊓ U₀' := ⟨hbU, hb⟩
    rw [hZ, Submodule.mem_bot] at this
    rw [this, add_zero]
    exact ha
  · exfalso
    have hne : U ⊓ U₀' ≠ ⊥ := hZ
    obtain ⟨J, hJle, hJ⟩ := exists_isIrr_le (hU.inf hU₀'inv) hne
    have h1 : J ≤ U₀ := le_sSup ⟨hJ, hJle.trans inf_le_left⟩
    have h2 : J ≤ U₀ ⊓ U₀' := le_inf h1 (hJle.trans inf_le_right)
    rw [hcompl.disjoint.eq_bot] at h2
    exact hJ.ne_bot (le_bot_iff.1 h2)

@[expose] def homComp (H : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  sSup {J | IsIrr H J ∧ HIso H J I}

theorem invariant_homComp (H : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) :
    Invariant H (homComp H I) :=
  invariant_sSup fun _ hJ => hJ.1.1

theorem le_homComp_of_hiso {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V} (hJ : IsIrr H J)
    (h : HIso H J I) : J ≤ homComp H I :=
  le_sSup ⟨hJ, h⟩

theorem le_homComp {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} (hI : IsIrr H I) :
    I ≤ homComp H I :=
  le_homComp_of_hiso hI (hiso_refl hI.1)

theorem hiso_of_le_homComp {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V} (hI : IsIrr H I)
    (hJ : IsIrr H J) (h : J ≤ homComp H I) : HIso H J I := by
  obtain ⟨K, ⟨hK, hKI⟩, hJK⟩ := irr_le_sSup hJ (S := {J | IsIrr H J ∧ HIso H J I})
    (fun _ hJ => hJ.1) h
  exact hiso_trans hJ.1 hK.1 hI.1 hJK hKI

theorem homComp_eq_of_hiso {H : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V} (hI : IsIrr H I)
    (hI' : IsIrr H I') (h : HIso H I I') : homComp H I = homComp H I' := by
  unfold homComp
  congr 1
  ext J
  constructor
  · rintro ⟨hJ, hJI⟩
    exact ⟨hJ, hiso_trans hJ.1 hI.1 hI'.1 hJI h⟩
  · rintro ⟨hJ, hJI⟩
    exact ⟨hJ, hiso_trans hJ.1 hI'.1 hI.1 hJI (hiso_symm hI.1 hI'.1 h)⟩

@[expose] def conjOrderIso (x : GLV V) : Submodule (ZMod 2) V ≃o Submodule (ZMod 2) V where
  toFun := conjSub x
  invFun := conjSub x⁻¹
  left_inv := conjSub_inv_conjSub x
  right_inv := conjSub_conjSub_inv x
  map_rel_iff' := conjSub_le_iff x

theorem conjSub_sSup (x : GLV V) (S : Set (Submodule (ZMod 2) V)) :
    conjSub x (sSup S) = sSup (conjSub x '' S) := by
  have := (conjOrderIso x).map_sSup S
  rw [sSup_image]
  exact this

theorem conjSub_homComp {Γ H : Subgroup (GLV V)} (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    {x : GLV V} (hx : x ∈ Γ) (I : Submodule (ZMod 2) V) :
    conjSub x (homComp H I) = homComp H (conjSub x I) := by
  unfold homComp
  rw [conjSub_sSup]
  congr 1
  ext J
  constructor
  · rintro ⟨K, ⟨hK, hKI⟩, rfl⟩
    exact ⟨hK.conj_of_normal hN hx, hiso_conj hN hx hKI⟩
  · rintro ⟨hJ, hJI⟩
    refine ⟨conjSub x⁻¹ J, ⟨hJ.conj_of_normal hN (Γ.inv_mem hx), ?_⟩, conjSub_conjSub_inv x J⟩
    have := hiso_conj hN (Γ.inv_mem hx) hJI
    rwa [conjSub_inv_conjSub] at this

theorem homComp_inf_eq_bot [Finite V] {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hI : IsIrr H I) (S : Set (Submodule (ZMod 2) V)) (hS : ∀ J ∈ S, IsIrr H J) (hSI : ∀ J ∈ S, ¬ HIso H J I) :
    homComp H I ⊓ sSup S = ⊥ := by
  by_contra hne
  have hinv : Invariant H (homComp H I ⊓ sSup S) :=
    (invariant_homComp H I).inf (invariant_sSup fun J hJ => (hS J hJ).1)
  obtain ⟨K, hKle, hK⟩ := exists_isIrr_le hinv hne
  have hK1 : K ≤ homComp H I := hKle.trans inf_le_left
  have hK2 : K ≤ sSup S := hKle.trans inf_le_right
  have hKI : HIso H K I := by
    obtain ⟨K', ⟨hK', hK'I⟩, hKK'⟩ := irr_le_sSup hK (S := {J | IsIrr H J ∧ HIso H J I})
      (fun _ hJ => hJ.1) hK1
    exact hiso_trans hK.1 hK'.1 hI.1 hKK' hK'I
  obtain ⟨J, hJ, hKJ⟩ := irr_le_sSup hK hS hK2
  exact hSI J hJ (hiso_trans (hS J hJ).1 hK.1 hI.1
    (hiso_symm hK.1 (hS J hJ).1 hKJ) hKI)

theorem add_self_eq_zero_of_zmod2 (v : V) : v + v = 0 := by
  have h : v + v = (2 : ZMod 2) • v := by rw [two_smul]
  rw [h, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem exists_irr_fixed [Finite V] {Γ H X : Subgroup (GLV V)} (hXΓ : X ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hX2 : ∀ x ∈ X, x * x = 1)
    {J₀ : Submodule (ZMod 2) V} (hJ₀ : IsIrr H J₀) :
    ∃ I, IsIrr H I ∧ HIso H I J₀ ∧ ∀ x ∈ X, HIso H I (conjSub x I) → conjSub x I = I := by
  classical
  set c := homComp H J₀ with hc
  have hcinv : Invariant H c := invariant_homComp H J₀
  have hsimple : IsSimpleModule (hRing H) ↥(toR hJ₀.1) := (isIrr_iff_simple hJ₀.1).1 hJ₀
  have hodd : Odd (Nat.card {ω : Submodule (hRing H) V //
      ω ≤ toR hcinv ∧ Nonempty (↥ω ≃ₗ[hRing H] ↥(toR hJ₀.1))}) :=
    @Twist.odd_card_iso_submodules (hRing H) _ V _ _ _ (fun m => add_self_eq_zero_of_zmod2 m)
      (toR hJ₀.1) (toR hcinv) hsimple ((toR_le_iff hJ₀.1 hcinv).2 (le_homComp hJ₀))
  let Ω := {J : Submodule (ZMod 2) V // IsIrr H J ∧ J ≤ c}
  have hirr : ∀ ω : {ω : Submodule (hRing H) V // ω ≤ toR hcinv ∧
      Nonempty (↥ω ≃ₗ[hRing H] ↥(toR hJ₀.1))}, IsIrr H (ofR ω.1) := by
    intro ω
    obtain ⟨e⟩ := ω.2.2
    have : IsSimpleModule (hRing H) ↥ω.1 := IsSimpleModule.congr e
    exact (isIrr_iff_simple (invariant_ofR ω.1)).2 this
  let eΩ : Ω ≃ {ω : Submodule (hRing H) V // ω ≤ toR hcinv ∧
      Nonempty (↥ω ≃ₗ[hRing H] ↥(toR hJ₀.1))} :=
    { toFun := fun J => ⟨toR J.2.1.1, (toR_le_iff _ hcinv).2 J.2.2,
        (hiso_iff J.2.1.1 hJ₀.1).1 (hiso_of_le_homComp hJ₀ J.2.1 J.2.2)⟩
      invFun := fun ω => ⟨ofR ω.1, hirr ω, fun v hv => ω.2.1 hv⟩
      left_inv := fun J => Subtype.ext rfl
      right_inv := fun ω => Subtype.ext rfl }
  have hcard : Nat.card Ω = Nat.card {ω : Submodule (hRing H) V //
      ω ≤ toR hcinv ∧ Nonempty (↥ω ≃ₗ[hRing H] ↥(toR hJ₀.1))} := Nat.card_congr eΩ
  let Y := stabilizerOf X c
  have hY2 : IsPGroup 2 ↥Y := fun y => ⟨1, by
    apply Subtype.ext
    show (y : GLV V) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    exact hX2 y y.2.1⟩
  let act : MulAction ↥Y Ω :=
    { smul := fun y J => ⟨conjSub (y : GLV V) J.1, J.2.1.conj_of_normal hN (hXΓ y.2.1), by
        have := conjSub_mono (y : GLV V) J.2.2
        rwa [y.2.2] at this⟩
      one_smul := fun J => Subtype.ext (conjSub_one J.1)
      mul_smul := fun a b J => Subtype.ext (conjSub_mul (a : GLV V) (b : GLV V) J.1) }
  have hfin : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun N : Submodule (ZMod 2) V => (N : Set V)) SetLike.coe_injective
  have hfinΩ : Finite Ω := inferInstance
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := @IsPGroup.card_modEq_card_fixedPoints 2 ↥Y _ hY2 hp2 Ω act hfinΩ
  have hfixodd : Nat.card ↑(@MulAction.fixedPoints ↥Y Ω _ act) % 2 = 1 := by
    have h1 : Nat.card Ω % 2 = 1 := Nat.odd_iff.1 (hcard ▸ hodd)
    have h2 : Nat.card Ω % 2 = Nat.card ↑(@MulAction.fixedPoints ↥Y Ω _ act) % 2 := hmod
    omega
  have hnonempty : Nonempty ↑(@MulAction.fixedPoints ↥Y Ω _ act) := by
    rw [← Finite.card_pos_iff]
    omega
  obtain ⟨⟨I, hI⟩⟩ := hnonempty
  have hIfix : ∀ y : ↥Y, conjSub (y : GLV V) I.1 = I.1 := fun y =>
    congrArg Subtype.val (@MulAction.mem_fixedPoints ↥Y Ω _ act I |>.1 hI y)
  have hIJ : HIso H I.1 J₀ := hiso_of_le_homComp hJ₀ I.2.1 I.2.2
  refine ⟨I.1, I.2.1, hIJ, fun x hx hiso => ?_⟩
  have hcx : conjSub x c = c := by
    have h1 : homComp H I.1 = c := homComp_eq_of_hiso I.2.1 hJ₀ hIJ
    have h2 : homComp H I.1 = homComp H (conjSub x I.1) :=
      homComp_eq_of_hiso I.2.1 (I.2.1.conj_of_normal hN (hXΓ hx)) hiso
    calc conjSub x c = conjSub x (homComp H I.1) := by rw [h1]
      _ = homComp H (conjSub x I.1) := conjSub_homComp hN (hXΓ hx) I.1
      _ = c := by rw [← h2, h1]
  exact hIfix ⟨x, hx, hcx⟩

end G11

end CFSG.Quasithin
