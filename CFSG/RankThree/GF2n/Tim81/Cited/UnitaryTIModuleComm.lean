module

public import Mathlib.RepresentationTheory.Subrepresentation
public import CFSG.RankThree.FFModules.Offenders
public import CFSG.Timmesfeld.ARS.Defs
import CFSG.RankThree.OddKernel.SectionRep
import CFSG.Timmesfeld.Bridge.RootStructR2ManyModule
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.GF2n.Tim81.TIModule

open CFSG.RankThree.FFModules CFSG.Timmesfeld.ARS

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

abbrev commSpan (σ : Representation (ZMod 2) G W) (T : Subgroup G) : Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) {u | ∃ t ∈ T, ∃ w, u = σ t w - w}

abbrev commSpanOn (σ : Representation (ZMod 2) G W) (T : Subgroup G) (U : Submodule (ZMod 2) W) :
    Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) {x | ∃ t ∈ T, ∃ u ∈ U, x = σ t u - u}

variable {σ : Representation (ZMod 2) G W}

theorem sub_mem_commSpan {T : Subgroup G} {t : G} (ht : t ∈ T) (w : W) :
    σ t w - w ∈ commSpan σ T :=
  Submodule.subset_span ⟨t, ht, w, rfl⟩

theorem sub_mem_commSpanOn {T : Subgroup G} {U : Submodule (ZMod 2) W} {t : G} (ht : t ∈ T)
    {u : W} (hu : u ∈ U) : σ t u - u ∈ commSpanOn σ T U :=
  Submodule.subset_span ⟨t, ht, u, hu, rfl⟩

theorem commSpan_le_iff {T : Subgroup G} {U : Submodule (ZMod 2) W} :
    commSpan σ T ≤ U ↔ ∀ t ∈ T, ∀ w, σ t w - w ∈ U := by
  rw [Submodule.span_le]
  constructor
  · intro h t ht w
    exact h ⟨t, ht, w, rfl⟩
  · rintro h _ ⟨t, ht, w, rfl⟩
    exact h t ht w

theorem commSpanOn_le_iff {T : Subgroup G} {U U' : Submodule (ZMod 2) W} :
    commSpanOn σ T U ≤ U' ↔ ∀ t ∈ T, ∀ u ∈ U, σ t u - u ∈ U' := by
  rw [Submodule.span_le]
  constructor
  · intro h t ht u hu
    exact h ⟨t, ht, u, hu, rfl⟩
  · rintro h _ ⟨t, ht, u, hu, rfl⟩
    exact h t ht u hu

theorem commSpan_mono {T T' : Subgroup G} (h : T ≤ T') : commSpan σ T ≤ commSpan σ T' :=
  commSpan_le_iff.2 fun _ ht w => sub_mem_commSpan (h ht) w

private theorem apply_conj (g t : G) (w : W) : σ (g * t * g⁻¹) (σ g w) = σ g (σ t w) := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]

theorem apply_mem_commSpan {T : Subgroup G} {g : G} (hg : ∀ t ∈ T, g * t * g⁻¹ ∈ T) {v : W}
    (hv : v ∈ commSpan σ T) : σ g v ∈ commSpan σ T := by
  have hle : commSpan σ T ≤ (commSpan σ T).comap (σ g) := by
    refine commSpan_le_iff.2 fun t ht w => ?_
    rw [Submodule.mem_comap, map_sub, ← apply_conj]
    exact sub_mem_commSpan (hg t ht) _
  exact hle hv

theorem apply_mem_commSpanOn {T : Subgroup G} {U : Submodule (ZMod 2) W} {g : G}
    (hg : ∀ t ∈ T, g * t * g⁻¹ ∈ T) (hgU : ∀ u ∈ U, σ g u ∈ U) {v : W}
    (hv : v ∈ commSpanOn σ T U) : σ g v ∈ commSpanOn σ T U := by
  have hle : commSpanOn σ T U ≤ (commSpanOn σ T U).comap (σ g) := by
    refine commSpanOn_le_iff.2 fun t ht u hu => ?_
    rw [Submodule.mem_comap, map_sub, ← apply_conj]
    exact sub_mem_commSpanOn (hg t ht) (hgU u hu)
  exact hle hv

theorem map_commSpan_conjSub (T : Subgroup G) (g : G) :
    (commSpan σ T).map (σ g) = commSpan σ (conjSub T g) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine commSpan_le_iff.2 fun t ht w => ?_
    rw [Submodule.mem_comap, map_sub, ← apply_conj]
    exact sub_mem_commSpan (Subgroup.mem_map.2 ⟨t, ht, rfl⟩) _
  · refine commSpan_le_iff.2 fun t' ht' w => ?_
    obtain ⟨t, ht, rfl⟩ := ht'
    refine ⟨σ t (σ g⁻¹ w) - σ g⁻¹ w, sub_mem_commSpan ht _, ?_⟩
    have hgg : σ g (σ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    change σ g (σ t (σ g⁻¹ w) - σ g⁻¹ w) = σ (g * t * g⁻¹) w - w
    rw [map_sub, ← apply_conj, hgg]

theorem map_commSpanOn_conjSub (T : Subgroup G) (U : Submodule (ZMod 2) W) (g : G) :
    (commSpanOn σ T U).map (σ g) = commSpanOn σ (conjSub T g) (U.map (σ g)) := by
  have hgg : ∀ w : W, σ g (σ g⁻¹ w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine commSpanOn_le_iff.2 fun t ht u hu => ?_
    rw [Submodule.mem_comap, map_sub, ← apply_conj]
    exact sub_mem_commSpanOn (Subgroup.mem_map.2 ⟨t, ht, rfl⟩) ⟨u, hu, rfl⟩
  · refine commSpanOn_le_iff.2 fun t' ht' u' hu' => ?_
    obtain ⟨t, ht, rfl⟩ := ht'
    obtain ⟨u, hu, rfl⟩ := hu'
    refine ⟨σ t u - u, sub_mem_commSpanOn ht hu, ?_⟩
    change σ g (σ t u - u) = σ (g * t * g⁻¹) (σ g u) - σ g u
    rw [map_sub, apply_conj]

private def subMemSubgroup (σ : Representation (ZMod 2) G W) (M : Submodule (ZMod 2) W) :
    Subgroup G where
  carrier := {x | ∀ w, σ x w - w ∈ M}
  mul_mem' {x y} hx hy w := by
    have h : σ (x * y) w - w = (σ x (σ y w) - σ y w) + (σ y w - w) := by
      rw [map_mul, Module.End.mul_apply]
      abel
    rw [h]
    exact M.add_mem (hx _) (hy w)
  one_mem' w := by simp
  inv_mem' {x} hx w := by
    have h : σ x⁻¹ w - w = -(σ x (σ x⁻¹ w) - σ x⁻¹ w) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      abel
    rw [h]
    exact M.neg_mem (hx _)

theorem commSpan_le_iSup_of_le {ι : Sort*} (T : ι → Subgroup G) {H : Subgroup G}
    (hH : H ≤ ⨆ i, T i) : commSpan σ H ≤ ⨆ i, commSpan σ (T i) := by
  have hle : (⨆ i, T i) ≤ subMemSubgroup σ (⨆ i, commSpan σ (T i)) :=
    iSup_le fun i t ht w =>
      (le_iSup (fun i => commSpan σ (T i)) i) (sub_mem_commSpan ht w)
  exact commSpan_le_iff.2 fun t ht w => hle (hH ht) w

theorem commSpan_le_biSup_of_le {ι : Type*} (s : Set ι) (T : ι → Subgroup G) {H : Subgroup G}
    (hH : H ≤ ⨆ i ∈ s, T i) : commSpan σ H ≤ ⨆ i ∈ s, commSpan σ (T i) := by
  have hle : (⨆ i ∈ s, T i) ≤ subMemSubgroup σ (⨆ i ∈ s, commSpan σ (T i)) :=
    iSup₂_le fun i hi t ht w =>
      (le_iSup₂ (f := fun i (_ : i ∈ s) => commSpan σ (T i)) i hi) (sub_mem_commSpan ht w)
  exact commSpan_le_iff.2 fun t ht w => hle (hH ht) w

theorem commSpan_sup (T T' : Subgroup G) :
    commSpan σ (T ⊔ T') = commSpan σ T ⊔ commSpan σ T' := by
  apply le_antisymm
  · have hle : T ⊔ T' ≤ subMemSubgroup σ (commSpan σ T ⊔ commSpan σ T') :=
      sup_le (fun t ht w => Submodule.mem_sup_left (sub_mem_commSpan ht w))
        (fun t ht w => Submodule.mem_sup_right (sub_mem_commSpan ht w))
    exact commSpan_le_iff.2 fun t ht w => hle ht w
  · exact sup_le (commSpan_mono le_sup_left) (commSpan_mono le_sup_right)

theorem commSpanOn_le_of_le {ι : Sort*} (T : ι → Subgroup G) {H : Subgroup G}
    (hH : H ≤ ⨆ i, T i) {U M : Submodule (ZMod 2) W} (hU : ∀ x ∈ ⨆ i, T i, ∀ u ∈ U, σ x u ∈ U)
    (hM : ∀ i, commSpanOn σ (T i) U ≤ M) : commSpanOn σ H U ≤ M := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ ⨆ i, T i ∧ ∀ u ∈ U, σ x u - u ∈ M}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨Subgroup.mul_mem _ hx.1 hy.1, fun u hu => ?_⟩
        have h : σ (x * y) u - u = (σ x (σ y u) - σ y u) + (σ y u - u) := by
          rw [map_mul, Module.End.mul_apply]
          abel
        rw [h]
        exact M.add_mem (hx.2 _ (hU y hy.1 u hu)) (hy.2 u hu)
      one_mem' := ⟨Subgroup.one_mem _, fun u _ => by simp⟩
      inv_mem' := fun {x} hx => by
        refine ⟨Subgroup.inv_mem _ hx.1, fun u hu => ?_⟩
        have h : σ x⁻¹ u - u = -(σ x (σ x⁻¹ u) - σ x⁻¹ u) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
          abel
        rw [h]
        exact M.neg_mem (hx.2 _ (hU _ (Subgroup.inv_mem _ hx.1) u hu)) }
  have hle : (⨆ i, T i) ≤ S := iSup_le fun i t ht =>
    ⟨le_iSup T i ht, fun u hu => hM i (sub_mem_commSpanOn ht hu)⟩
  exact commSpanOn_le_iff.2 fun t ht u hu => (hle (hH ht)).2 u hu

theorem le_fixSub_of_inf_eq_bot {T T' : Subgroup G}
    (hinv : ∀ t ∈ T', ∀ v ∈ commSpan σ T, σ t v ∈ commSpan σ T)
    (hinf : commSpan σ T ⊓ commSpan σ T' = ⊥) : commSpan σ T ≤ fixSub σ T' := by
  intro v hv t ht
  have h1 : σ t v - v ∈ commSpan σ T ⊓ commSpan σ T' :=
    ⟨Submodule.sub_mem _ (hinv t ht v hv) hv, sub_mem_commSpan ht v⟩
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at h1
  exact h1

theorem commSpanOn_commSpan_comm {T T' : Subgroup G} (hc : ∀ t ∈ T, ∀ t' ∈ T', t * t' = t' * t) :
    commSpanOn σ T' (commSpan σ T) = commSpanOn σ T (commSpan σ T') := by
  have key : ∀ {A B : Subgroup G}, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      commSpanOn σ B (commSpan σ A) ≤ commSpanOn σ A (commSpan σ B) := by
    intro A B hAB
    refine commSpanOn_le_iff.2 fun b hb u hu => ?_
    have hle : commSpan σ A ≤ (commSpanOn σ A (commSpan σ B)).comap (σ b - 1) := by
      refine commSpan_le_iff.2 fun a ha w => ?_
      rw [Submodule.mem_comap]
      have h : (σ b - 1) (σ a w - w) = σ a (σ b w - w) - (σ b w - w) := by
        simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
        rw [← Module.End.mul_apply (σ b), ← map_mul, ← hAB a ha b hb, map_mul,
          Module.End.mul_apply]
      rw [h]
      exact sub_mem_commSpanOn ha (sub_mem_commSpan hb w)
    have := hle hu
    rwa [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply] at this
  exact le_antisymm (key hc) (key fun t' ht' t ht => (hc t ht t' ht').symm)

theorem commSpanOn_ne_of_isPGroup [Finite W] {P : Subgroup G} [Finite P] (hP : IsPGroup 2 P)
    {E : Submodule (ZMod 2) W} (hE : ∀ p ∈ P, ∀ e ∈ E, σ p e ∈ E) (hne : E ≠ ⊥) :
    commSpanOn σ P E ≠ E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Submodule (ZMod 2) W) :=
    Finite.of_injective (fun M : Submodule (ZMod 2) W => (M : Set W)) SetLike.coe_injective
  let S : Set (Submodule (ZMod 2) W) := {M | (∀ p ∈ P, ∀ m ∈ M, σ p m ∈ M) ∧ M < E}
  have hS : (⊥ : Submodule (ZMod 2) W) ∈ S := by
    refine ⟨fun p _ m hm => ?_, bot_lt_iff_ne_bot.2 hne⟩
    rw [(Submodule.mem_bot _).1 hm, map_zero]
    exact zero_mem _
  obtain ⟨M, hMmax⟩ := S.toFinite.exists_maximal ⟨⊥, hS⟩
  obtain ⟨hMinv, hME⟩ := hMmax.prop
  let τ : Representation (ZMod 2) P W := σ.comp P.subtype
  let Xm : Subrepresentation τ :=
    { toSubmodule := M, apply_mem_toSubmodule := fun p m hm => hMinv p p.2 m hm }
  let Ebar : Submodule (ZMod 2) (W ⧸ M) := E.map M.mkQ
  have hmk : ∀ (p : P) (w : W), Xm.quotient p (Submodule.Quotient.mk (p := M) w) =
      (Submodule.Quotient.mk (p := M) (σ p w) : W ⧸ M) :=
    fun p w => Subrepresentation.quotient_apply_mk Xm p w
  have hEbar : ∀ (p : P) (v : W ⧸ M), v ∈ Ebar → Xm.quotient p v ∈ Ebar := by
    rintro p _ ⟨e, he, rfl⟩
    change Xm.quotient p (Submodule.Quotient.mk e) ∈ Ebar
    rw [hmk]
    exact ⟨σ p e, hE p p.2 e he, rfl⟩
  let Xe : Subrepresentation Xm.quotient :=
    { toSubmodule := Ebar, apply_mem_toSubmodule := hEbar }
  have hEbar0 : Ebar ≠ ⊥ := by
    intro h
    obtain ⟨e, he, heM⟩ := SetLike.exists_of_lt hME
    have : (Submodule.Quotient.mk e : W ⧸ M) ∈ Ebar := ⟨e, he, rfl⟩
    rw [h, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at this
    exact heM this
  haveI : Nontrivial Ebar := Submodule.nontrivial_iff_ne_bot.mpr hEbar0
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨v, hv0, hvfix⟩ := CFSG.RankThree.OddKernel.exists_ne_zero_fixed hP Xe.toRepresentation
  obtain ⟨e, he, hev⟩ := v.2
  have heM : e ∉ M := by
    intro h
    apply hv0
    refine Subtype.ext ?_
    rw [← hev]
    exact (Submodule.Quotient.mk_eq_zero M).2 h
  have hefix : ∀ p ∈ P, σ p e - e ∈ M := by
    intro p hp
    have h := (Subrepresentation.toRepresentation_apply_coe).mp (hvfix ⟨p, hp⟩)
    rw [← hev] at h
    change Xm.quotient ⟨p, hp⟩ (Submodule.Quotient.mk e) = Submodule.Quotient.mk e at h
    rw [hmk, Submodule.Quotient.eq] at h
    exact h
  set M' := M ⊔ Submodule.span (ZMod 2) {e} with hM'
  have hM'inv : ∀ p ∈ P, ∀ m ∈ M', σ p m ∈ M' := by
    intro p hp m hm
    obtain ⟨m₀, hm₀, y, hy, rfl⟩ := Submodule.mem_sup.1 hm
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [map_add, map_smul]
    have h1 : σ p e = e + (σ p e - e) := by abel
    rw [h1, smul_add]
    refine M'.add_mem (Submodule.mem_sup_left (hMinv p hp m₀ hm₀)) (M'.add_mem ?_ ?_)
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e))
    · exact Submodule.mem_sup_left (M.smul_mem c (hefix p hp))
  have hM'E : M' ≤ E := sup_le hME.le
    ((Submodule.span_singleton_le_iff_mem e E).2 he)
  have hMM' : M < M' := lt_of_le_of_ne le_sup_left fun h =>
    heM (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self e))
  have hM'eq : M' = E := by
    by_contra hne'
    exact absurd (hMmax.2 ⟨hM'inv, lt_of_le_of_ne hM'E hne'⟩ hMM'.le) (not_le_of_gt hMM')
  intro heq
  have hle : commSpanOn σ P E ≤ M := by
    refine commSpanOn_le_iff.2 fun p hp x hx => ?_
    rw [← hM'eq] at hx
    obtain ⟨m₀, hm₀, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have h1 : σ p (m₀ + c • e) - (m₀ + c • e) = (σ p m₀ - m₀) + c • (σ p e - e) := by
      rw [map_add, map_smul, smul_sub]
      abel
    rw [h1]
    exact M.add_mem (M.sub_mem (hMinv p hp m₀ hm₀) hm₀) (M.smul_mem c (hefix p hp))
  rw [heq] at hle
  exact (not_le_of_gt hME) hle

theorem commSpanOn_commSpan_of_perfect (hG : commutator G = ⊤) :
    commSpanOn σ ⊤ (commSpan σ ⊤) = commSpan σ ⊤ := by
  set N := commSpan σ (⊤ : Subgroup G) with hN
  set N₂ := commSpanOn σ ⊤ N with hN₂
  have hNinv : ∀ (g : G), ∀ v ∈ N, σ g v ∈ N := fun g v hv =>
    apply_mem_commSpan (fun _ _ => Subgroup.mem_top _) hv
  have hN₂inv : ∀ (g : G), ∀ v ∈ N₂, σ g v ∈ N₂ := fun g v hv =>
    apply_mem_commSpanOn (fun _ _ => Subgroup.mem_top _) (hNinv g) hv
  apply le_antisymm
  · exact commSpanOn_le_iff.2 fun t _ u hu => N.sub_mem (hNinv t u hu) hu
  let Xs : Subrepresentation σ :=
    { toSubmodule := N₂, apply_mem_toSubmodule := fun g v hv => hN₂inv g v hv }
  have hmk : ∀ (g : G) (w : W), Xs.quotient g (Submodule.Quotient.mk (p := N₂) w) =
      (Submodule.Quotient.mk (p := N₂) (σ g w) : W ⧸ N₂) :=
    fun g w => Subrepresentation.quotient_apply_mk Xs g w
  have h1 : ∀ g, ∀ x ∈ N.map N₂.mkQ, Xs.quotient g x = x := by
    rintro g _ ⟨n, hn, rfl⟩
    change Xs.quotient g (Submodule.Quotient.mk n) = Submodule.Quotient.mk n
    rw [hmk, Submodule.Quotient.eq]
    exact sub_mem_commSpanOn (Subgroup.mem_top g) hn
  have h2 : ∀ g u, Xs.quotient g u - u ∈ N.map N₂.mkQ := by
    intro g u
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective N₂ u
    rw [hmk, ← Submodule.Quotient.mk_sub]
    exact ⟨σ g w - w, sub_mem_commSpan (Subgroup.mem_top g) w, rfl⟩
  refine commSpan_le_iff.2 fun g _ w => ?_
  have h := LinearMap.congr_fun
    (CFSG.Timmesfeld.Bridge.RootMany.eq_one_of_trivial_of_perfect hG Xs.quotient _ h1 h2 g)
    (Submodule.Quotient.mk w)
  rw [hmk, Module.End.one_apply, Submodule.Quotient.eq] at h
  exact h

section Card

variable [Finite W]

private theorem natCard_submodule (P : Submodule (ZMod 2) W) :
    Nat.card P = 2 ^ Module.finrank (ZMod 2) P := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem natCard_sup_of_inf_eq_bot {P Q : Submodule (ZMod 2) W} (h : P ⊓ Q = ⊥) :
    Nat.card ↥(P ⊔ Q) = Nat.card P * Nat.card Q := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hr := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [h, finrank_bot, add_zero] at hr
  rw [natCard_submodule, natCard_submodule, natCard_submodule, hr, pow_add]

theorem natCard_sup_le (P Q : Submodule (ZMod 2) W) :
    Nat.card ↥(P ⊔ Q) ≤ Nat.card P * Nat.card Q := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hr := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [natCard_submodule, natCard_submodule, natCard_submodule, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem natCard_mono {P Q : Submodule (ZMod 2) W} (h : P ≤ Q) : Nat.card P ≤ Nat.card Q := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  rw [natCard_submodule, natCard_submodule]
  exact Nat.pow_le_pow_right (by norm_num) (Submodule.finrank_mono h)

theorem eq_of_le_of_natCard_le {P Q : Submodule (ZMod 2) W} (h : P ≤ Q)
    (hc : Nat.card Q ≤ Nat.card P) : P = Q := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  rw [natCard_submodule, natCard_submodule] at hc
  exact Submodule.eq_of_le_of_finrank_le h
    ((Nat.pow_le_pow_iff_right (by norm_num)).1 hc)

private theorem natCard_map_mul_natCard_inf_ker (f : W →ₗ[ZMod 2] W) (V₀ : Submodule (ZMod 2) W) :
    Nat.card ↥(V₀.map f) * Nat.card ↥(V₀ ⊓ LinearMap.ker f) = Nat.card V₀ := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.domRestrict V₀)
  have hrange : Module.finrank (ZMod 2) (LinearMap.range (f.domRestrict V₀)) =
      Module.finrank (ZMod 2) (V₀.map f) := by
    rw [LinearMap.range_domRestrict]
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (f.domRestrict V₀)) =
      Module.finrank (ZMod 2) ↥(V₀ ⊓ LinearMap.ker f) := by
    rw [LinearMap.ker_domRestrict]
    have h : (LinearMap.ker f).comap V₀.subtype = (V₀ ⊓ LinearMap.ker f).comap V₀.subtype := by
      rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
    rw [h]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  rw [natCard_submodule, natCard_submodule, natCard_submodule, ← pow_add, ← hrange, ← hker, hrn]

theorem natCard_map_apply (U : Submodule (ZMod 2) W) (g : G) :
    Nat.card ↥(U.map (σ g)) = Nat.card U := by
  have hinj : Function.Injective (σ g) := fun v w h => by
    have := congrArg (σ g⁻¹) h
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, Module.End.one_apply] at this
  exact (Nat.card_congr (Submodule.equivMapOfInjective (σ g) hinj U).toEquiv).symm

@[expose] def stabSub (σ : Representation (ZMod 2) G W) (U : Submodule (ZMod 2) W) :
    Subgroup G where
  carrier := {g | U.map (σ g) = U}
  mul_mem' {g h} hg hh := by
    change U.map (σ (g * h)) = U
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
    change (U.map (σ h)).map (σ g) = U
    rw [hh]
    exact hg
  one_mem' := by
    change U.map (σ 1) = U
    rw [map_one]
    exact Submodule.map_id U
  inv_mem' {g} hg := by
    change U.map (σ g⁻¹) = U
    conv_lhs => rw [← hg]
    change (U.map (σ g)).map (σ g⁻¹) = U
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    exact Submodule.map_id U

theorem mem_stabSub {U : Submodule (ZMod 2) W} {g : G} : g ∈ stabSub σ U ↔ U.map (σ g) = U :=
  Iff.rfl

theorem mem_stabSub_of_forall {U : Submodule (ZMod 2) W} {g : G} (h : ∀ u ∈ U, σ g u ∈ U) :
    g ∈ stabSub σ U := by
  have hle : U.map (σ g) ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  exact (eq_of_le_of_natCard_le hle (natCard_map_apply U g).ge)

theorem apply_mem_of_mem_stabSub {U : Submodule (ZMod 2) W} {g : G} (hg : g ∈ stabSub σ U)
    {u : W} (hu : u ∈ U) : σ g u ∈ U := by
  rw [← mem_stabSub.1 hg]
  exact ⟨u, hu, rfl⟩

theorem natCard_biSup_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (X : ι → Submodule (ZMod 2) W) :
    Nat.card ↥(⨆ i ∈ s, X i) ≤ ∏ i ∈ s, Nat.card (X i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.prod_insert ha]
    exact (natCard_sup_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem natCard_biSup_eq_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (X Fx : ι → Submodule (ZMod 2) W) (hXF : ∀ i ∈ s, X i ⊓ Fx i = ⊥)
    (hle : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → X i ≤ Fx j) :
    Nat.card ↥(⨆ i ∈ s, X i) = ∏ i ∈ s, Nat.card (X i) ∧
      (⨆ i ∈ s, X i) ⊓ (⨅ i ∈ s, Fx i) = ⊥ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hXF i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hle i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
        hij)
    have hGa : (⨆ i ∈ s, X i) ≤ Fx a := iSup₂_le fun i hi =>
      hle i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)
        (fun h => ha (h ▸ hi))
    have hXa := hXF a (Finset.mem_insert_self a s)
    have hdis : X a ⊓ (⨆ i ∈ s, X i) = ⊥ :=
      eq_bot_iff.2 ((inf_le_inf_left _ hGa).trans hXa.le)
    rw [Finset.iSup_insert, Finset.prod_insert ha, Finset.iInf_insert,
      natCard_sup_of_inf_eq_bot hdis, ih1]
    refine ⟨rfl, eq_bot_iff.2 ?_⟩
    rintro v ⟨hv, hvF, hvFs⟩
    obtain ⟨x, hx, g, hg, rfl⟩ := Submodule.mem_sup.1 hv
    have hxF : x ∈ Fx a := by
      have := (Fx a).sub_mem hvF (hGa hg)
      rwa [add_sub_cancel_right] at this
    have hx0 : x = 0 := by
      have : x ∈ X a ⊓ Fx a := ⟨hx, hxF⟩
      rwa [hXa, Submodule.mem_bot] at this
    subst hx0
    rw [zero_add] at hvFs ⊢
    have : g ∈ (⨆ i ∈ s, X i) ⊓ (⨅ i ∈ s, Fx i) := ⟨hg, hvFs⟩
    rwa [ih2] at this

theorem fix_of_sub_mem_of_inf_eq_bot {x : G} (hx : x * x = 1) {A₀ B₀ : Submodule (ZMod 2) W}
    (hAB : A₀ ⊓ B₀ = ⊥) (hcard : Nat.card A₀ = Nat.card B₀) (hsub : ∀ w, σ x w - w ∈ A₀)
    (hfix : ∀ b ∈ B₀, σ x b = b → b = 0) : ∀ a ∈ A₀, σ x a = a := by
  set f : W →ₗ[ZMod 2] W := σ x - 1 with hf
  set V₀ := A₀ ⊔ B₀ with hV₀
  have hfw : ∀ w, f w = σ x w - w := fun w => by simp [hf]
  have hff : ∀ w, f (f w) = 0 := by
    intro w
    have hxx : σ x (σ x w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, hx, map_one, Module.End.one_apply]
    calc f (f w) = (σ x (σ x w) - σ x w) - (σ x w - w) := by rw [hfw, hfw, map_sub]
      _ = (w + w) - (σ x w + σ x w) := by rw [hxx]; abel
      _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, sub_zero]
  have hrange : V₀.map f ≤ A₀ := by
    rintro _ ⟨w, -, rfl⟩
    rw [hfw]
    exact hsub w
  have hK : (V₀ ⊓ LinearMap.ker f) ⊓ B₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨⟨-, hb⟩, hbB⟩
    have hb' : f b = 0 := LinearMap.mem_ker.mp hb
    rw [hfw, sub_eq_zero] at hb'
    exact (Submodule.mem_bot _).2 (hfix b hbB hb')
  have hKle : (V₀ ⊓ LinearMap.ker f) ⊔ B₀ ≤ V₀ := sup_le inf_le_left le_sup_right
  have h1 := natCard_map_mul_natCard_inf_ker f V₀
  have h2 : Nat.card ↥V₀ = Nat.card A₀ * Nat.card B₀ := natCard_sup_of_inf_eq_bot hAB
  have h3 : Nat.card ↥(V₀ ⊓ LinearMap.ker f) * Nat.card B₀ ≤ Nat.card ↥V₀ := by
    rw [← natCard_sup_of_inf_eq_bot hK]
    exact natCard_mono hKle
  have hB0 : 0 < Nat.card B₀ := Nat.card_pos
  have h4 : Nat.card A₀ ≤ Nat.card ↥(V₀.map f) := by
    rw [h2, ← hcard] at h3 h1
    rw [← hcard] at hB0
    have h5 : Nat.card ↥(V₀ ⊓ LinearMap.ker f) ≤ Nat.card A₀ :=
      Nat.le_of_mul_le_mul_right h3 hB0
    by_contra hlt
    push Not at hlt
    have h6 : Nat.card ↥(V₀.map f) * Nat.card ↥(V₀ ⊓ LinearMap.ker f) <
        Nat.card A₀ * Nat.card A₀ :=
      calc _ ≤ Nat.card ↥(V₀.map f) * Nat.card A₀ := Nat.mul_le_mul_left _ h5
        _ < Nat.card A₀ * Nat.card A₀ := Nat.mul_lt_mul_of_pos_right hlt hB0
    omega
  have heq : V₀.map f = A₀ := eq_of_le_of_natCard_le hrange h4
  intro a ha
  rw [← heq] at ha
  obtain ⟨w, -, rfl⟩ := ha
  have := hff w
  rw [hfw (f w), sub_eq_zero] at this
  exact this

end Card

end CFSG.RankThree.GF2n.Tim81.TIModule
