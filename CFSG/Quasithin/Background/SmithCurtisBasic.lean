module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.Quasithin.SmithCurtis

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

theorem act_mul (g h : G) (v : V) : ρ g (ρ h v) = ρ (g * h) v := by
  rw [map_mul, Module.End.mul_apply]

@[expose] def fixSub (S : Subgroup G) : Submodule k V where
  carrier := {v | ∀ g ∈ S, ρ g v = v}
  add_mem' {a b} ha hb g hg := by rw [map_add, ha g hg, hb g hg]
  zero_mem' g _ := map_zero (ρ g)
  smul_mem' c v hv g hg := by rw [map_smul, hv g hg]

theorem mem_fixSub {S : Subgroup G} {v : V} : v ∈ fixSub ρ S ↔ ∀ g ∈ S, ρ g v = v := Iff.rfl

theorem fixSub_anti {S T : Subgroup G} (h : S ≤ T) : fixSub ρ T ≤ fixSub ρ S :=
  fun _ hv g hg => hv g (h hg)

theorem act_mem_fixSub {S : Subgroup G} {g : G} (hg : ∀ s ∈ S, g⁻¹ * s * g ∈ S) {v : V}
    (hv : v ∈ fixSub ρ S) : ρ g v ∈ fixSub ρ S := by
  intro s hs
  have e : s * g = g * (g⁻¹ * s * g) := by group
  rw [act_mul, e, ← act_mul, hv _ (hg s hs)]

theorem act_eq_of_mem {S : Subgroup G} {x y : G} (hxy : y⁻¹ * x ∈ S) {v : V}
    (hv : v ∈ fixSub ρ S) : ρ x v = ρ y v := by
  have e : x = y * (y⁻¹ * x) := by group
  rw [e, ← act_mul, hv _ hxy]

@[expose] def augSub (S : Subgroup G) : Submodule k V :=
  Submodule.span k {z | ∃ g ∈ S, ∃ v : V, z = ρ g v - v}

theorem sub_mem_augSub {S : Subgroup G} {g : G} (hg : g ∈ S) (v : V) :
    ρ g v - v ∈ augSub ρ S :=
  Submodule.subset_span ⟨g, hg, v, rfl⟩

theorem augSub_mono {S T : Subgroup G} (h : S ≤ T) : augSub ρ S ≤ augSub ρ T :=
  Submodule.span_mono fun _ ⟨g, hg, v, e⟩ => ⟨g, h hg, v, e⟩

theorem act_mem_augSub {S T : Subgroup G} {g : G} (hg : ∀ s ∈ S, g * s * g⁻¹ ∈ T) {z : V}
    (hz : z ∈ augSub ρ S) : ρ g z ∈ augSub ρ T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, hs, v, rfl⟩ := hz
    have e : ρ g (ρ s v - v) = ρ (g * s * g⁻¹) (ρ g v) - ρ g v := by
      rw [map_sub, act_mul, act_mul, inv_mul_cancel_right]
    rw [e]
    exact sub_mem_augSub ρ (hg s hs) _
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem act_mem_augSub_self {S : Subgroup G} {g : G} (hg : g ∈ S) {z : V}
    (hz : z ∈ augSub ρ S) : ρ g z ∈ augSub ρ S :=
  act_mem_augSub ρ (fun _ hs => mul_mem (mul_mem hg hs) (inv_mem hg)) hz

theorem act_sub_mem_augSub {S : Subgroup G} {x : G} (hx : x ∈ S) (v : V) {w : V}
    (hw : w - v ∈ augSub ρ S) : ρ x w - v ∈ augSub ρ S := by
  have e : ρ x w - v = (ρ x w - w) + (w - v) := by abel
  rw [e]
  exact add_mem (sub_mem_augSub ρ hx w) hw

theorem augSub_sup_le (S T : Subgroup G) : augSub ρ (S ⊔ T) ≤ augSub ρ S ⊔ augSub ρ T := by
  suffices h : ∀ g ∈ S ⊔ T, ∀ v : V, ρ g v - v ∈ augSub ρ S ⊔ augSub ρ T by
    rw [augSub, Submodule.span_le]
    rintro _ ⟨g, hg, v, rfl⟩
    exact h g hg v
  intro g hg
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    intro v
    rcases hx with hx | hx
    · exact Submodule.mem_sup_left (sub_mem_augSub ρ hx v)
    · exact Submodule.mem_sup_right (sub_mem_augSub ρ hx v)
  | one => intro v; rw [map_one, Module.End.one_apply, sub_self]; exact zero_mem _
  | mul x y _ _ hx hy =>
    intro v
    have e : ρ (x * y) v - v = (ρ x (ρ y v) - ρ y v) + (ρ y v - v) := by
      rw [act_mul]; abel
    rw [e]
    exact add_mem (hx _) (hy v)
  | inv x _ hx =>
    intro v
    have e : ρ x⁻¹ v - v = -(ρ x (ρ x⁻¹ v) - ρ x⁻¹ v) := by
      rw [act_mul, mul_inv_cancel, map_one, Module.End.one_apply]; abel
    rw [e]
    exact neg_mem (hx _)

theorem sum_act_eq_zero {Y : Subgroup G} [Fintype Y] {z : V} (hz : z ∈ augSub ρ Y) :
    ∑ y : Y, ρ y z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, hg, v, rfl⟩ := hz
    simp only [map_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    refine Fintype.sum_equiv (Equiv.mulRight ⟨g, hg⟩) _ _ fun y => ?_
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, act_mul]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, Finset.sum_add_distrib, ha, hb, add_zero]
  | smul c a _ ha => simp only [map_smul, ← Finset.smul_sum, ha, smul_zero]

theorem nsmul_char_eq_zero (p : ℕ) [CharP k p] (x : V) : p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]

theorem exists_fixed_ne_of_zmod {p : ℕ} [Fact p.Prime] {M S : Type*} [AddCommGroup M]
    [hM : Module (ZMod p) M] [Group S] [Finite S] [DistribMulAction S M] (hS : IsPGroup p S)
    [Nontrivial M] : ∃ v : M, v ≠ 0 ∧ ∀ s : S, s • v = v := by
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : M)
  set W : Submodule (ZMod p) M := Submodule.span (ZMod p) (Set.range fun s : S => s • v₀)
  have hfin : Module.Finite (ZMod p) W :=
    Module.Finite.span_of_finite (ZMod p) (Set.finite_range _)
  have hWfin : Finite W := Module.finite_of_finite (ZMod p)
  have hstab : ∀ s : S, ∀ w ∈ W, s • w ∈ W := by
    intro s w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨t, rfl⟩ := hw
      exact Submodule.subset_span ⟨s * t, mul_smul s t v₀⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : s • (c • a) = c • (s • a) :=
        ((DistribSMul.toAddMonoidHom M s).toZModLinearMap p).map_smul c a
      rw [e]
      exact Submodule.smul_mem _ c ha
  let _ : MulAction S W :=
    { smul := fun s w => ⟨s • (w : M), hstab s w w.2⟩
      one_smul := fun w => Subtype.ext (one_smul S (w : M))
      mul_smul := fun a b w => Subtype.ext (mul_smul a b (w : M)) }
  have hW0 : Nontrivial W :=
    ⟨⟨⟨v₀, Submodule.subset_span ⟨1, one_smul S v₀⟩⟩, 0,
      fun h => hv₀ (congrArg Subtype.val h)⟩⟩
  have hcard : p ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p (Module.finrank_pos (R := ZMod p) (M := W)).ne'
  have h0 : (0 : W) ∈ MulAction.fixedPoints S W := fun s => Subtype.ext (smul_zero s)
  obtain ⟨b, hb, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hcard h0
  exact ⟨b, fun h => hne (Subtype.ext h.symm), fun s => congrArg Subtype.val (hb s)⟩

theorem exists_fixed_ne {p : ℕ} [hp : Fact p.Prime] [CharP k p] {S : Subgroup G} [Finite S]
    (hS : IsPGroup p S) [Nontrivial V] : ∃ v : V, v ≠ 0 ∧ ∀ g ∈ S, ρ g v = v := by
  let _ : DistribMulAction S V :=
    { smul := fun s v => ρ s v
      one_smul := fun v => by
        change ρ ((1 : S) : G) v = v
        rw [Subgroup.coe_one, map_one, Module.End.one_apply]
      mul_smul := fun a b v => by
        change ρ ((a * b : S) : G) v = ρ a (ρ b v)
        rw [Subgroup.coe_mul, act_mul]
      smul_zero := fun s => map_zero (ρ s)
      smul_add := fun s a b => map_add (ρ s) a b }
  obtain ⟨v, hv, hfix⟩ := exists_fixed_ne_of_zmod (M := V) (S := S)
    (hM := AddCommGroup.zmodModule (nsmul_char_eq_zero (k := k) p)) hS
  exact ⟨v, hv, fun g hg => hfix ⟨g, hg⟩⟩

theorem augSub_ne_top {p : ℕ} [Fact p.Prime] [CharP k p] {S : Subgroup G} [Finite S]
    (hS : IsPGroup p S) [Nontrivial V] : augSub ρ S ≠ ⊤ := by
  intro htop
  obtain ⟨f, hf, hfix⟩ := exists_fixed_ne ρ.dual hS
  apply hf
  have key : ∀ z ∈ augSub ρ S, f z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, v, rfl⟩ := hz
      have h := congrArg (fun φ : Module.Dual k V => φ v) (hfix g⁻¹ (S.inv_mem hg))
      simp only [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
        LinearMap.coe_comp, Function.comp_apply] at h
      rw [map_sub, h, sub_self]
    | zero => exact map_zero f
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, ha, smul_zero]
  ext v
  exact key v (htop ▸ Submodule.mem_top)

@[expose] def IsSimpleRep : Prop :=
  Nontrivial V ∧ ∀ W : Submodule k V, (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def orbitSpan (x : V) : Submodule k V :=
  Submodule.span k (Set.range fun g => ρ g x)

theorem orbitSpan_stable (x : V) (g : G) {w : V} (hw : w ∈ orbitSpan ρ x) :
    ρ g w ∈ orbitSpan ρ x := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨h, rfl⟩ := hw
    rw [act_mul]
    exact Submodule.subset_span ⟨g * h, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem mem_orbitSpan_self (x : V) : x ∈ orbitSpan ρ x :=
  Submodule.subset_span ⟨1, by
    show ρ 1 x = x
    rw [map_one, Module.End.one_apply]⟩

theorem orbitSpan_eq_top {ρ : Representation k G V} (hρ : IsSimpleRep ρ) {x : V} (hx : x ≠ 0) :
    orbitSpan ρ x = ⊤ := by
  rcases hρ.2 _ fun g w hw => orbitSpan_stable ρ x g hw with h | h
  · exfalso
    apply hx
    have h' := mem_orbitSpan_self ρ x
    rw [h] at h'
    exact (Submodule.mem_bot _).mp h'
  · exact h

@[expose] def restrictRep (W : Submodule k V) (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W) :
    Representation k G W where
  toFun g := (ρ g).restrict (hW g)
  map_one' := by
    ext w
    simp only [LinearMap.restrict_apply, map_one, Module.End.one_apply]
  map_mul' g h := by
    ext w
    simp only [LinearMap.restrict_apply, map_mul, Module.End.mul_apply]

theorem restrictRep_apply (W : Submodule k V) (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W) (g : G)
    (w : W) : ((restrictRep ρ W hW g w : W) : V) = ρ g w := rfl

theorem exists_fixed_mem {p : ℕ} [Fact p.Prime] [CharP k p] {S : Subgroup G} [Finite S]
    (hS : IsPGroup p S) {W : Submodule k V} (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W) (hne : W ≠ ⊥) :
    ∃ x ∈ W, x ≠ 0 ∧ x ∈ fixSub ρ S := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨x, hx, hfix⟩ := exists_fixed_ne (restrictRep ρ W hW) hS
  exact ⟨x.1, x.2, fun h => hx (Subtype.ext h), fun g hg => congrArg Subtype.val (hfix g hg)⟩

theorem isSimpleRep_comp_iff {G' : Type*} [Group G'] (ρ' : Representation k G' V) {f : G →* G'}
    (hf : Function.Surjective f) : IsSimpleRep (ρ'.comp f) ↔ IsSimpleRep ρ' := by
  constructor
  · rintro ⟨hnt, h⟩
    refine ⟨hnt, fun W hW => h W fun g w hw => hW (f g) w hw⟩
  · rintro ⟨hnt, h⟩
    refine ⟨hnt, fun W hW => h W fun g' w hw => ?_⟩
    obtain ⟨g, rfl⟩ := hf g'
    exact hW g w hw

theorem intertwines_of_comp {G' V' : Type*} [Group G'] [AddCommGroup V'] [Module k V']
    {ρ' : Representation k G' V} {σ' : Representation k G' V'} {f : G →* G'}
    (hf : Function.Surjective f) {β : V →ₗ[k] V'}
    (hβ : ∀ (g : G) (v : V), β ((ρ'.comp f) g v) = (σ'.comp f) g (β v)) (g' : G') (v : V) :
    β (ρ' g' v) = σ' g' (β v) := by
  obtain ⟨g, rfl⟩ := hf g'
  exact hβ g v

theorem exists_eigen_of_prod_eq_zero {M : Type*} [AddCommGroup M] [Module k M] [Nontrivial M]
    (A : Module.End k M) (s : List k)
    (hA : (s.map fun a => A - algebraMap k (Module.End k M) a).prod = 0) :
    ∃ a ∈ s, ∃ v : M, v ≠ 0 ∧ A v = a • v := by
  by_contra hcon
  push Not at hcon
  have hinj : ∀ a ∈ s, Function.Injective (A - algebraMap k (Module.End k M) a) := by
    intro a ha
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    refine hcon a ha v hv0 ?_
    rw [LinearMap.sub_apply, sub_eq_zero] at hv
    simpa [Module.algebraMap_end_apply] using hv
  have hprod : ∀ t : List k, (∀ a ∈ t, a ∈ s) →
      Function.Injective (t.map fun a => A - algebraMap k (Module.End k M) a).prod := by
    intro t
    induction t with
    | nil =>
      intro _ a b hab
      simpa using hab
    | cons a t ih =>
      intro hts
      rw [List.map_cons, List.prod_cons, Module.End.coe_mul]
      exact (hinj a (hts a List.mem_cons_self)).comp
        (ih fun b hb => hts b (List.mem_cons_of_mem a hb))
  have h := hprod s fun _ ha => ha
  rw [hA] at h
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  exact hv (h (by simp))

variable (k) in
@[expose] def SplitOver (H : Subgroup G) : Prop :=
  ∀ h ∈ H, ∃ e : ℕ, h ^ e = 1 ∧ ∃ s : List k,
    (Polynomial.X ^ e - 1 : Polynomial k) = (s.map fun a => Polynomial.X - Polynomial.C a).prod

theorem exists_weight_vector {H : Subgroup G} [Finite H]
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hsplit : SplitOver k H)
    {M : Submodule k V} (hM : M ≠ ⊥) (hst : ∀ h ∈ H, ∀ v ∈ M, ρ h v ∈ M) :
    ∃ y ∈ M, y ≠ 0 ∧ ∃ χ : G → k, ∀ h ∈ H, ρ h y = χ h • y := by
  classical
  suffices hF : ∀ F : Finset G, (∀ h ∈ F, h ∈ H) → ∃ M' : Submodule k V, M' ≤ M ∧ M' ≠ ⊥ ∧
      (∀ h ∈ H, ∀ v ∈ M', ρ h v ∈ M') ∧ ∀ h ∈ F, ∃ c : k, ∀ v ∈ M', ρ h v = c • v by
    obtain ⟨M', hM'M, hM'0, -, hsc⟩ := hF (Set.toFinite (H : Set G)).toFinset (by simp)
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM'0
    have hmem : ∀ h ∈ H, h ∈ (Set.toFinite (H : Set G)).toFinset := by simp
    refine ⟨y, hM'M hy, hy0, fun h => if hh : h ∈ H then (hsc h (hmem h hh)).choose else 0,
      fun h hh => ?_⟩
    simp only [hh, ↓reduceDIte]
    exact (hsc h (hmem h hh)).choose_spec y hy
  intro F
  induction F using Finset.induction_on with
  | empty => exact fun _ => ⟨M, le_rfl, hM, hst, by simp⟩
  | insert h F _ ih =>
    intro hF
    obtain ⟨M', hM'M, hM'0, hM'st, hsc⟩ := ih fun g hg => hF g (Finset.mem_insert_of_mem hg)
    have hh : h ∈ H := hF h (Finset.mem_insert_self h F)
    obtain ⟨e, he, s, hs⟩ := hsplit h hh
    have : Nontrivial M' := Submodule.nontrivial_iff_ne_bot.mpr hM'0
    set A : Module.End k M' := (ρ h).restrict (hM'st h hh)
    have hpow : ∀ (n : ℕ) (v : M'), ((A ^ n) v : V) = ρ (h ^ n) v := by
      intro n
      induction n with
      | zero => intro v; rw [pow_zero, pow_zero, map_one]; rfl
      | succ n ih =>
        intro v
        rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← act_mul]
        rfl
    have hAe : A ^ e = 1 := by
      ext v
      rw [hpow, he, map_one, Module.End.one_apply, Module.End.one_apply]
    have hA : (s.map fun a => A - algebraMap k (Module.End k M') a).prod = 0 := by
      have h1 := congrArg (Polynomial.aeval A) hs
      rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hAe, sub_self, map_list_prod,
        List.map_map] at h1
      rw [h1]
      congr 1
      refine List.map_congr_left fun a _ => ?_
      simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    obtain ⟨a, -, v, hv0, hv⟩ := exists_eigen_of_prod_eq_zero A s hA
    refine ⟨M' ⊓ LinearMap.ker (ρ h - a • LinearMap.id), inf_le_left.trans hM'M, ?_, ?_, ?_⟩
    · rw [Submodule.ne_bot_iff]
      refine ⟨v, Submodule.mem_inf.mpr ⟨v.2, ?_⟩, fun h0 => hv0 (Subtype.ext h0)⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero]
      exact congrArg Subtype.val hv
    · intro h' hh' w hw
      obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hw2
      refine Submodule.mem_inf.mpr ⟨hM'st h' hh' w hw1, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero, act_mul, hcomm h hh h' hh', ← act_mul, hw2, map_smul]
    · intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · refine ⟨a, fun w hw => ?_⟩
        have hw2 := (Submodule.mem_inf.mp hw).2
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          sub_eq_zero] at hw2
        exact hw2
      · obtain ⟨c, hc⟩ := hsc g hg
        exact ⟨c, fun w hw => hc w (Submodule.mem_inf.mp hw).1⟩

end CFSG.Quasithin.SmithCurtis
