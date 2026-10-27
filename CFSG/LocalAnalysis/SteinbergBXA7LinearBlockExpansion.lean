module

public import CFSG.LocalAnalysis.SteinbergBVA7TransvectionCenters

public section

namespace CFSG.LocalAnalysis.SteinbergBX

open Module CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBV.BinaryTransvection

namespace LinearBlock

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem tv_sq {u : V} {f : Dual (ZMod 2) V} (hf : f u = 0) :
    (LinearMap.id + f.smulRight u) * (LinearMap.id + f.smulRight u) =
      (1 : Module.End (ZMod 2) V) := by
  rw [id_add_smulRight_mul hf, BinaryTransvection.add_self_eq_zero, LinearMap.zero_smulRight,
    add_zero]
  rfl

@[expose] def tv (u : V) (f : Dual (ZMod 2) V) (hf : f u = 0) :
    LinearMap.GeneralLinearGroup (ZMod 2) V :=
  ⟨LinearMap.id + f.smulRight u, LinearMap.id + f.smulRight u, tv_sq hf, tv_sq hf⟩

theorem coe_tv (u : V) (f : Dual (ZMod 2) V) (hf : f u = 0) :
    (tv u f hf : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u :=
  rfl

theorem tv_inv (u : V) (f : Dual (ZMod 2) V) (hf : f u = 0) : (tv u f hf)⁻¹ = tv u f hf :=
  inv_eq_of_mul_eq_one_right (Units.ext (tv_sq hf))

theorem tv_apply (u : V) (f : Dual (ZMod 2) V) (hf : f u = 0) (x : V) :
    (tv u f hf : Module.End (ZMod 2) V) x = x + f x • u := by
  rw [coe_tv, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply]

theorem exists_functional {p : Submodule (ZMod 2) V} {x : V} (hx : x ∉ p) :
    ∃ f : Dual (ZMod 2) V, f x = 1 ∧ ∀ y ∈ p, f y = 0 := by
  obtain ⟨f, hfx, hf⟩ := p.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨f, zmodTwo_eq_one_of_ne_zero hfx, fun y hy => ?_⟩
  have h1 : f y ∈ p.map f := ⟨y, hy, rfl⟩
  rw [hf] at h1
  exact (Submodule.mem_bot _).mp h1

theorem gl_inv_apply_apply (m : LinearMap.GeneralLinearGroup (ZMod 2) V) (x : V) :
    ((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V)
      ((m : Module.End (ZMod 2) V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem gl_apply_inv_apply (m : LinearMap.GeneralLinearGroup (ZMod 2) V) (x : V) :
    (m : Module.End (ZMod 2) V)
      (((m⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply]

variable {N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}

@[expose] def ContainsBlock (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (S C : Submodule (ZMod 2) V) : Prop :=
  ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) V,
    (∀ s ∈ S, (g : Module.End (ZMod 2) V) s ∈ S) →
      (∀ c ∈ C, (g : Module.End (ZMod 2) V) c = c) → g ∈ N

theorem tv_mem {S C : Submodule (ZMod 2) V} (hL : ContainsBlock N S C) {u : V} (hu : u ∈ S)
    {f : Dual (ZMod 2) V} (hf : f u = 0) (hfC : ∀ c ∈ C, f c = 0) : tv u f hf ∈ N := by
  refine hL _ (fun s hs => ?_) (fun c hc => ?_)
  · rw [tv_apply]
    exact S.add_mem hs (S.smul_mem _ hu)
  · rw [tv_apply, hfC c hc, zero_smul, add_zero]

theorem mem_centerFunctionals_of_block {S C : Submodule (ZMod 2) V} (hL : ContainsBlock N S C)
    {u : V} (hu : u ∈ S) {f : Dual (ZMod 2) V} (hf : f u = 0) (hfC : ∀ c ∈ C, f c = 0) :
    f ∈ centerFunctionals N u :=
  ⟨hf, tv u f hf, tv_mem hL hu hf hfC, rfl⟩

theorem exists_transvection_not_preserving
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure {n | n ∈ N ∧ IsBinaryTransvection n})
    {S : Submodule (ZMod 2) V} (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) :
    ∃ t ∈ N, IsBinaryTransvection t ∧ ∃ s ∈ S, (t : Module.End (ZMod 2) V) s ∉ S := by
  by_contra hcon
  push Not at hcon
  let H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    { carrier := {g | ∀ x, x ∈ S ↔ (g : Module.End (ZMod 2) V) x ∈ S}
      one_mem' := fun x => Iff.rfl
      mul_mem' := fun {a b} ha hb x => by
        rw [Units.val_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha x => by
        rw [ha (((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) x),
          gl_apply_inv_apply] }
  have hle : N ≤ H := by
    rw [hgen, Subgroup.closure_le]
    rintro t ⟨htN, ht⟩
    have hpres := hcon t htN ht
    obtain ⟨u, f, -, -, hfu, htuf⟩ := ht
    intro x
    refine ⟨fun hx => hpres x hx, fun hx => ?_⟩
    have h1 := hpres _ hx
    have h2 : (t : Module.End (ZMod 2) V) ((t : Module.End (ZMod 2) V) x) = x := by
      rw [← Module.End.mul_apply, htuf, id_add_smulRight_mul hfu,
        BinaryTransvection.add_self_eq_zero, LinearMap.zero_smulRight, add_zero, LinearMap.id_apply]
    rwa [h2] at h1
  rcases hirr S fun n hn u hu => (hle hn u).mp hu with h | h
  · exact hS0 h
  · exact hS1 h

theorem notMem_sup_of_isCompl {S C p : Submodule (ZMod 2) V} (hSC : IsCompl S C) (hpS : p ≤ S)
    {x : V} (hxS : x ∈ S) (hxp : x ∉ p) : x ∉ p ⊔ C := by
  intro hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  have hbS : b ∈ S := by
    rw [show b = x - a by rw [← hab]; abel]
    exact S.sub_mem hxS (hpS ha)
  have hb0 : b = 0 := (Submodule.disjoint_def.mp hSC.disjoint) b hbS hb
  apply hxp
  rw [← hab, hb0, add_zero]
  exact ha

theorem exists_mem_notMem_span_pair [FiniteDimensional (ZMod 2) V] {S : Submodule (ZMod 2) V}
    (hS : 3 ≤ finrank (ZMod 2) S) (y z : V) :
    ∃ x ∈ S, x ∉ Submodule.span (ZMod 2) {y, z} := by
  classical
  by_contra h
  push Not at h
  have h1 := Submodule.finrank_mono (show S ≤ Submodule.span (ZMod 2) {y, z} from h)
  have h2 := finrank_span_le_card (R := ZMod 2) ({y, z} : Set V)
  have h3 : ({y, z} : Set V).toFinset.card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact Finset.card_le_two
  omega

theorem notMem_of_mem_of_ne_zero {S C : Submodule (ZMod 2) V} (hSC : IsCompl S C) {x : V}
    (hxS : x ∈ S) (hx0 : x ≠ 0) : x ∉ C := fun hxC =>
  hx0 ((Submodule.disjoint_def.mp hSC.disjoint) x hxS hxC)

theorem step_center [FiniteDimensional (ZMod 2) V]
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure {n | n ∈ N ∧ IsBinaryTransvection n})
    {S C : Submodule (ZMod 2) V} (hSC : IsCompl S C) (hS : 3 ≤ finrank (ZMod 2) S)
    (hL : ContainsBlock N S C) (hC : C ≠ ⊥) :
    ∃ c ∈ C, c ≠ 0 ∧ ∀ h : Dual (ZMod 2) V, (∀ y ∈ C, h y = 0) →
      h ∈ centerFunctionals N c := by
  classical
  have hS0 : S ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hS
    omega
  have hS1 : S ≠ ⊤ := by
    intro h
    apply hC
    have h1 := hSC.inf_eq_bot
    rwa [h, top_inf_eq] at h1
  obtain ⟨t, htN, ht, s, hs, hts⟩ := exists_transvection_not_preserving hirr hgen hS0 hS1
  obtain ⟨w, g, -, -, hgw, htwg⟩ := ht
  have hts' : (t : Module.End (ZMod 2) V) s = s + g s • w := by
    rw [htwg, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
  have hgs : g s = 1 := by
    by_contra h
    rw [zmodTwo_eq_zero_of_ne_one h, zero_smul, add_zero] at hts'
    exact hts (by rw [hts']; exact hs)
  have hwS : w ∉ S := by
    intro hw
    rw [hgs, one_smul] at hts'
    exact hts (by rw [hts']; exact S.add_mem hs hw)
  have hvS : S.projection C hSC w ∈ S := Submodule.projection_apply_mem hSC w
  have hcC : C.projection S hSC.symm w ∈ C := Submodule.projection_apply_mem hSC.symm w
  have hwvc : S.projection C hSC w + C.projection S hSC.symm w = w :=
    Submodule.projection_add_projection_eq_self hSC w
  set v := S.projection C hSC w with hv
  set c := C.projection S hSC.symm w with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hwS
    rw [← hwvc, h0, add_zero]
    exact hvS
  obtain ⟨x, hxS, hxsv⟩ := exists_mem_notMem_span_pair hS s v
  have hspan : Submodule.span (ZMod 2) {s, v} ≤ S := by
    rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · exact hs
    · exact hvS
  obtain ⟨f, hfx, hf⟩ := exists_functional (notMem_sup_of_isCompl hSC hspan hxS hxsv)
  have hfs : f s = 0 := hf s (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
  have hfv : f v = 0 := hf v (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
  have hfC : ∀ y ∈ C, f y = 0 := fun y hy => hf y (Submodule.mem_sup_right hy)
  have hfw : f w = 0 := by rw [← hwvc, map_add, hfv, hfC c hcC, add_zero]
  have hfsF := mem_centerFunctionals_of_block hL hs hfs hfC
  have hgF : g ∈ centerFunctionals N w := ⟨hgw, t, htN, htwg⟩
  have hfwF := mem_of_incidence hgF hgs hfsF hfw
  have hfvF := mem_centerFunctionals_of_block hL hvS hfv hfC
  have hfcF : f ∈ centerFunctionals N c := by
    obtain ⟨-, n, hn, hnf⟩ := hfvF
    obtain ⟨-, m, hm, hmf⟩ := hfwF
    refine ⟨hfC c hcC, n * m, mul_mem hn hm, ?_⟩
    rw [Units.val_mul, hnf, hmf, id_add_smulRight_mul_same hfw,
      show v + w = c by rw [← hwvc, ← add_assoc, BinaryTransvection.add_self_eq_zero, zero_add]]
  refine ⟨c, hcC, hc0, ?_⟩
  have hphi : ∀ φ : Dual (ZMod 2) V, ∀ hφx : φ x = 0, (∀ y ∈ C, φ y = 0) →
      φ ∈ centerFunctionals N c := by
    intro φ hφx hφC
    have hℓ := tv_mem hL hxS hφx hφC
    have hℓc : (tv x φ hφx : Module.End (ZMod 2) V) c = c := by
      rw [tv_apply, hφC c hcC, zero_smul, add_zero]
    have hcomp : f.comp (((tv x φ hφx)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        Module.End (ZMod 2) V) = f + φ := by
      rw [tv_inv]
      ext y
      rw [LinearMap.comp_apply, tv_apply, map_add, map_smul, hfx, smul_eq_mul, mul_one,
        LinearMap.add_apply]
    have hfφ : f + φ ∈ centerFunctionals N c := by
      obtain ⟨-, n, hn, hnf⟩ := hfcF
      refine ⟨by rw [LinearMap.add_apply, hfC c hcC, hφC c hcC, add_zero],
        tv x φ hφx * n * (tv x φ hφx)⁻¹, mul_mem (mul_mem hℓ hn) (inv_mem hℓ), ?_⟩
      rw [Units.val_mul, Units.val_mul, hnf, conj_id_add_smulRight, hcomp, hℓc]
    have h1 := (centerFunctionals N c).sub_mem hfφ hfcF
    rwa [add_sub_cancel_left] at h1
  intro h hhC
  have h1 : h - h x • f ∈ centerFunctionals N c := hphi _
    (by rw [LinearMap.sub_apply, LinearMap.smul_apply, hfx, smul_eq_mul, mul_one, sub_self])
    (fun y hy => by rw [LinearMap.sub_apply, LinearMap.smul_apply, hhC y hy, hfC y hy,
      smul_zero, sub_zero])
  have h2 : h x • f ∈ centerFunctionals N c := (centerFunctionals N c).smul_mem _ hfcF
  have h3 := (centerFunctionals N c).add_mem h1 h2
  rwa [sub_add_cancel] at h3

theorem mem_centerFunctionals_zero (f : Dual (ZMod 2) V) : f ∈ centerFunctionals N 0 :=
  ⟨map_zero f, 1, one_mem N, by
    rw [LinearMap.smulRight_zero, add_zero, Units.val_one]
    rfl⟩

theorem step_lambda [FiniteDimensional (ZMod 2) V]
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure {n | n ∈ N ∧ IsBinaryTransvection n})
    {S C : Submodule (ZMod 2) V} (hSC : IsCompl S C) (hS : 3 ≤ finrank (ZMod 2) S)
    (hL : ContainsBlock N S C) {c : V} (hcC : c ∈ C) (hc0 : c ≠ 0)
    (hcF : ∀ h : Dual (ZMod 2) V, (∀ y ∈ C, h y = 0) → h ∈ centerFunctionals N c) :
    ∃ μ : Dual (ZMod 2) V, (∀ s ∈ S, μ s = 0) ∧ μ c = 1 ∧
      ∀ s ∈ S, μ ∈ centerFunctionals N s := by
  classical
  have hS0 : S ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hS
    omega
  obtain ⟨u, huS, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have huC := notMem_of_mem_of_ne_zero hSC huS hu0
  obtain ⟨h₀, hh₀u, hh₀C⟩ := exists_functional huC
  have hh₀F := hcF h₀ hh₀C
  obtain ⟨x, hxS, hxu⟩ := exists_mem_notMem_span_pair hS u u
  have hspan : Submodule.span (ZMod 2) {u, u} ≤ S := by
    rw [Submodule.span_le]
    rintro y (rfl | rfl) <;> exact huS
  obtain ⟨φ₀, hφ₀x, hφ₀⟩ := exists_functional (notMem_sup_of_isCompl hSC hspan hxS hxu)
  have hφ₀F := mem_centerFunctionals_of_block hL huS
    (hφ₀ u (Submodule.mem_sup_left (Submodule.subset_span (by simp))))
    (fun y hy => hφ₀ y (Submodule.mem_sup_right hy))
  have hφ₀ne : φ₀ ≠ 0 := fun h => by
    rw [h, LinearMap.zero_apply] at hφ₀x
    exact zero_ne_one hφ₀x
  have hh₀ne : h₀ ≠ 0 := fun h => by
    rw [h, LinearMap.zero_apply] at hh₀u
    exact zero_ne_one hh₀u
  obtain ⟨-, -, -, hrec, -⟩ := binary_transvection_center_reciprocity
    (by have := Submodule.finrank_le S; omega) N hirr hgen
  have hcΔ : c ∈ transvectionCenters N :=
    ⟨hc0, fun h => hh₀ne (by rw [h] at hh₀F; exact (Submodule.mem_bot _).mp hh₀F)⟩
  have huΔ : u ∈ transvectionCenters N :=
    ⟨hu0, fun h => hφ₀ne (by rw [h] at hφ₀F; exact (Submodule.mem_bot _).mp hφ₀F)⟩
  obtain ⟨k, hkF, hkc⟩ := (hrec c hcΔ u huΔ (fun h => huC (h ▸ hcC))).mp ⟨h₀, hh₀F, hh₀u⟩
  set kS := k.comp (S.projection C hSC) with hkS
  have hkS_S : ∀ s ∈ S, kS s = k s := fun s hs => by
    rw [hkS, LinearMap.comp_apply, Submodule.projection_apply_of_mem_left hSC hs]
  have hkS_C : ∀ y ∈ C, kS y = 0 := fun y hy => by
    rw [hkS, LinearMap.comp_apply, Submodule.projection_apply_of_mem_right hSC hy, map_zero]
  have hkSF : kS ∈ centerFunctionals N u :=
    mem_centerFunctionals_of_block hL huS (by rw [hkS_S u huS]; exact hkF.1) hkS_C
  have hμS : ∀ s ∈ S, (k + kS) s = 0 := fun s hs => by
    rw [LinearMap.add_apply, hkS_S s hs, BinaryTransvection.add_self_eq_zero]
  refine ⟨k + kS, hμS, by rw [LinearMap.add_apply, hkc, hkS_C c hcC, add_zero], ?_⟩
  have hμu : k + kS ∈ centerFunctionals N u := (centerFunctionals N u).add_mem hkF hkSF
  intro s hs
  by_cases hs0 : s = 0
  · rw [hs0]
    exact mem_centerFunctionals_zero _
  by_cases hsu : s = u
  · rw [hsu]
    exact hμu
  have husp : u ∉ Submodule.span (ZMod 2) {s, s} := by
    intro h
    rw [Set.pair_eq_singleton, Submodule.mem_span_singleton] at h
    obtain ⟨a, ha⟩ := h
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) a with rfl | rfl
    · rw [zero_smul] at ha
      exact hu0 ha.symm
    · rw [one_smul] at ha
      exact hsu ha
  have hspan' : Submodule.span (ZMod 2) {s, s} ≤ S := by
    rw [Submodule.span_le]
    rintro y (rfl | rfl) <;> exact hs
  obtain ⟨φ, hφu, hφ⟩ := exists_functional (notMem_sup_of_isCompl hSC hspan' huS husp)
  have hφs : φ s = 0 := hφ s (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
  have hφC : ∀ y ∈ C, φ y = 0 := fun y hy => hφ y (Submodule.mem_sup_right hy)
  have hℓ := tv_mem hL hs hφs hφC
  have hμus : (k + kS) (u + s) = 0 := by rw [map_add, hμS u huS, hμS s hs, add_zero]
  have hcomp : (k + kS).comp (((tv s φ hφs)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      Module.End (ZMod 2) V) = k + kS := by
    rw [tv_inv]
    ext y
    rw [LinearMap.comp_apply, tv_apply, map_add, map_smul, hμS s hs, smul_zero, add_zero]
  have hℓu : (tv s φ hφs : Module.End (ZMod 2) V) u = u + s := by
    rw [tv_apply, hφu, one_smul]
  have hμusF : k + kS ∈ centerFunctionals N (u + s) := by
    obtain ⟨-, n, hn, hnf⟩ := hμu
    refine ⟨hμus, tv s φ hφs * n * (tv s φ hφs)⁻¹, mul_mem (mul_mem hℓ hn) (inv_mem hℓ), ?_⟩
    rw [Units.val_mul, Units.val_mul, hnf, conj_id_add_smulRight, hcomp, hℓu]
  obtain ⟨-, n, hn, hnf⟩ := hμu
  obtain ⟨-, m, hm, hmf⟩ := hμusF
  refine ⟨hμS s hs, n * m, mul_mem hn hm, ?_⟩
  rw [Units.val_mul, hnf, hmf, id_add_smulRight_mul_same hμus, ← add_assoc,
    BinaryTransvection.add_self_eq_zero, zero_add]

theorem exists_mover {S C : Submodule (ZMod 2) V} (hSC : IsCompl S C) {c : V}
    (hcF : ∀ h : Dual (ZMod 2) V, (∀ y ∈ C, h y = 0) → h ∈ centerFunctionals N c)
    {μ : Dual (ZMod 2) V} (hμS : ∀ s ∈ S, μ s = 0) (hμc : μ c = 1)
    (hμF : ∀ s ∈ S, μ ∈ centerFunctionals N s) {z : V}
    (hz : z ∈ S ⊔ Submodule.span (ZMod 2) {c}) (hz0 : z ≠ 0) :
    ∃ n ∈ N, (n : Module.End (ZMod 2) V) z = c ∧
      (∀ x ∈ S ⊔ Submodule.span (ZMod 2) {c},
        (n : Module.End (ZMod 2) V) x ∈ S ⊔ Submodule.span (ZMod 2) {c}) ∧
      ∀ y ∈ C, μ y = 0 → (n : Module.End (ZMod 2) V) y = y := by
  obtain ⟨s₀, hs₀, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hS₁ : ∀ x ∈ S, x ∈ S ⊔ Submodule.span (ZMod 2) {c} := fun x hx =>
    Submodule.mem_sup_left hx
  have hc₁ : c ∈ S ⊔ Submodule.span (ZMod 2) {c} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
  obtain ⟨-, n, hn, hnf⟩ := hμF s₀ hs₀
  have hn_apply : ∀ x, (n : Module.End (ZMod 2) V) x = x + μ x • s₀ := fun x => by
    rw [hnf, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
  have hn_pres : ∀ x ∈ S ⊔ Submodule.span (ZMod 2) {c},
      (n : Module.End (ZMod 2) V) x ∈ S ⊔ Submodule.span (ZMod 2) {c} := fun x hx => by
    rw [hn_apply]
    exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ (hS₁ s₀ hs₀))
  have hn_fix : ∀ y ∈ C, μ y = 0 → (n : Module.End (ZMod 2) V) y = y := fun y _ hy => by
    rw [hn_apply, hy, zero_smul, add_zero]
  have hn_move : (n : Module.End (ZMod 2) V) (s₀ + c) = c := by
    rw [hn_apply, map_add, hμS s₀ hs₀, hμc, zero_add, one_smul, add_comm s₀ c, add_assoc,
      BinaryTransvection.add_self_eq_zero, add_zero]
  rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) a with rfl | rfl
  · rw [zero_smul, add_zero] at hz0 ⊢
    obtain ⟨h, hhs, hhC⟩ := exists_functional (notMem_of_mem_of_ne_zero hSC hs₀ hz0)
    obtain ⟨-, m, hm, hmf⟩ := hcF h hhC
    have hm_apply : ∀ x, (m : Module.End (ZMod 2) V) x = x + h x • c := fun x => by
      rw [hmf, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
    refine ⟨n * m, mul_mem hn hm, ?_, fun x hx => ?_, fun y hyC hy => ?_⟩
    · rw [Units.val_mul, Module.End.mul_apply, hm_apply, hhs, one_smul, hn_move]
    · rw [Units.val_mul, Module.End.mul_apply]
      apply hn_pres
      rw [hm_apply]
      exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ hc₁)
    · rw [Units.val_mul, Module.End.mul_apply, hm_apply, hhC y hyC, zero_smul, add_zero,
        hn_fix y hyC hy]
  · rw [one_smul]
    exact ⟨n, hn, hn_move, hn_pres, hn_fix⟩

theorem mem_of_fixes {S C : Submodule (ZMod 2) V} (hSC : IsCompl S C) (hL : ContainsBlock N S C)
    {c : V} (hcC : c ∈ C)
    (hcF : ∀ h : Dual (ZMod 2) V, (∀ y ∈ C, h y = 0) → h ∈ centerFunctionals N c)
    {μ : Dual (ZMod 2) V} (hμS : ∀ s ∈ S, μ s = 0) (hμc : μ c = 1)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : ∀ x ∈ S ⊔ Submodule.span (ZMod 2) {c},
      (g : Module.End (ZMod 2) V) x ∈ S ⊔ Submodule.span (ZMod 2) {c})
    (hgC : ∀ y ∈ C, (g : Module.End (ZMod 2) V) y = y) : g ∈ N := by
  set h : Dual (ZMod 2) V := μ.comp ((g : Module.End (ZMod 2) V).comp (S.projection C hSC))
    with hh
  have hhC : ∀ y ∈ C, h y = 0 := fun y hy => by
    rw [hh, LinearMap.comp_apply, LinearMap.comp_apply,
      Submodule.projection_apply_of_mem_right hSC hy, map_zero, map_zero]
  obtain ⟨-, m, hm, hmf⟩ := hcF h hhC
  have hm_apply : ∀ x, (m : Module.End (ZMod 2) V) x = x + h x • c := fun x => by
    rw [hmf, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
  have hℓ : g * m ∈ N := by
    refine hL _ (fun s hs => ?_) (fun y hy => ?_)
    · have h1 : h s = μ ((g : Module.End (ZMod 2) V) s) := by
        rw [hh, LinearMap.comp_apply, LinearMap.comp_apply,
          Submodule.projection_apply_of_mem_left hSC hs]
      obtain ⟨s', hs', y, hy, hxy⟩ := Submodule.mem_sup.mp (hg s (Submodule.mem_sup_left hs))
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [Units.val_mul, Module.End.mul_apply, hm_apply, map_add, map_smul, hgC c hcC, h1,
        ← hxy, map_add, map_smul, hμS s' hs', hμc, smul_eq_mul, mul_one, zero_add, add_assoc,
        BinaryTransvection.add_self_eq_zero, add_zero]
      exact hs'
    · rw [Units.val_mul, Module.End.mul_apply, hm_apply, hhC y hy, zero_smul, add_zero, hgC y hy]
  have h2 := mul_mem hℓ (inv_mem hm)
  rwa [mul_inv_cancel_right] at h2

theorem enlarge_block [FiniteDimensional (ZMod 2) V]
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure {n | n ∈ N ∧ IsBinaryTransvection n})
    {S C : Submodule (ZMod 2) V} (hSC : IsCompl S C) (hS : 3 ≤ finrank (ZMod 2) S)
    (hL : ContainsBlock N S C) (hC : C ≠ ⊥) :
    ∃ S₁ C₁ : Submodule (ZMod 2) V, IsCompl S₁ C₁ ∧ S ≤ S₁ ∧
      finrank (ZMod 2) C₁ < finrank (ZMod 2) C ∧ ContainsBlock N S₁ C₁ := by
  obtain ⟨c, hcC, hc0, hcF⟩ := step_center hirr hgen hSC hS hL hC
  obtain ⟨μ, hμS, hμc, hμF⟩ := step_lambda hirr hgen hSC hS hL hcC hc0 hcF
  have hc₁ : c ∈ S ⊔ Submodule.span (ZMod 2) {c} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
  have hμ₁ : ∀ y ∈ C, y - μ y • c ∈ C ⊓ LinearMap.ker μ := fun y hy =>
    Submodule.mem_inf.mpr ⟨C.sub_mem hy (C.smul_mem _ hcC), by
      rw [LinearMap.mem_ker, map_sub, map_smul, hμc, smul_eq_mul, mul_one, sub_self]⟩
  refine ⟨S ⊔ Submodule.span (ZMod 2) {c}, C ⊓ LinearMap.ker μ, ⟨?_, ?_⟩, le_sup_left, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨s, hs, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨hxC, hxμ⟩ := Submodule.mem_inf.mp hx'
    rw [LinearMap.mem_ker, map_add, map_smul, hμS s hs, hμc, zero_add, smul_eq_mul,
      mul_one] at hxμ
    rw [hxμ, zero_smul, add_zero] at hxC ⊢
    exact (Submodule.disjoint_def.mp hSC.disjoint) s hs hxC
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv := Submodule.projection_add_projection_eq_self hSC v
    have hp : S.projection C hSC v ∈ S := Submodule.projection_apply_mem hSC v
    have hq : C.projection S hSC.symm v ∈ C := Submodule.projection_apply_mem hSC.symm v
    rw [← hv, show S.projection C hSC v + C.projection S hSC.symm v =
      (S.projection C hSC v + μ (C.projection S hSC.symm v) • c) +
        (C.projection S hSC.symm v - μ (C.projection S hSC.symm v) • c) by abel]
    exact Submodule.add_mem_sup
      (Submodule.add_mem _ (Submodule.mem_sup_left hp) (Submodule.smul_mem _ _ hc₁)) (hμ₁ _ hq)
  · apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h1 : c ∈ C ⊓ LinearMap.ker μ := by
      rw [h]
      exact hcC
    have h2 := (Submodule.mem_inf.mp h1).2
    rw [LinearMap.mem_ker, hμc] at h2
    exact one_ne_zero h2
  · intro g hg hgC₁
    have hgc0 : (g : Module.End (ZMod 2) V) c ≠ 0 := fun h => hc0 (by
      rw [← gl_inv_apply_apply g c, h, map_zero])
    obtain ⟨n, hn, hnc, hnS, hnC⟩ := exists_mover hSC hcF hμS hμc hμF (hg c hc₁) hgc0
    have hfix : ∀ y ∈ C, ((n * g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        Module.End (ZMod 2) V) y = y := by
      intro y hy
      have hy₁ := hμ₁ y hy
      have hy' : y = (y - μ y • c) + μ y • c := by abel
      conv_lhs => rw [hy']
      rw [Units.val_mul, Module.End.mul_apply, map_add, map_smul, hgC₁ _ hy₁, map_add, map_smul,
        hnc, hnC _ (Submodule.mem_inf.mp hy₁).1 (Submodule.mem_inf.mp hy₁).2, sub_add_cancel]
    have hg' : n * g ∈ N := mem_of_fixes hSC hL hcC hcF hμS hμc (fun x hx => by
      rw [Units.val_mul, Module.End.mul_apply]
      exact hnS _ (hg x hx)) hfix
    have h1 := mul_mem (inv_mem hn) hg'
    rwa [inv_mul_cancel_left] at h1

end LinearBlock

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

end CFSG.LocalAnalysis.SteinbergBX
