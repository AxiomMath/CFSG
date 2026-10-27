module

public import CFSG.LocalAnalysis.SteinbergBVA7TransvectionPairingForm
public import CFSG.LocalAnalysis.SteinbergBXA7LinearBlockExpansion

public section

namespace CFSG.LocalAnalysis

open Module SteinbergBV SteinbergBV.BinaryTransvection SteinbergBV.PairingForm
  SteinbergBX.LinearBlock

namespace SteinbergBQ.RepeatedCenter

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}

theorem mem_centerFunctionals_add {f : Dual (ZMod 2) V} {s t : V}
    (hs : f ∈ centerFunctionals N s) (ht : f ∈ centerFunctionals N t) :
    f ∈ centerFunctionals N (s + t) := by
  obtain ⟨hfs, n, hn, hnf⟩ := mem_centerFunctionals.1 hs
  obtain ⟨hft, m, hm, hmf⟩ := mem_centerFunctionals.1 ht
  refine mem_centerFunctionals.2 ⟨by rw [map_add, hfs, hft, add_zero], n * m, mul_mem hn hm, ?_⟩
  rw [Units.val_mul, hnf, hmf, id_add_smulRight_mul_same hft]

theorem mem_centerFunctionals_smul {f : Dual (ZMod 2) V} {s : V}
    (hs : f ∈ centerFunctionals N s) (c : ZMod 2) : f ∈ centerFunctionals N (c • s) := by
  rcases zmodTwo_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul]
    exact mem_centerFunctionals_zero f
  · rwa [one_smul]

theorem mem_centerFunctionals_of_mem_sup {f : Dual (ZMod 2) V} {s s' x : V}
    (hs : f ∈ centerFunctionals N s) (hs' : f ∈ centerFunctionals N s')
    (hx : x ∈ Submodule.span (ZMod 2) {s} ⊔ Submodule.span (ZMod 2) {s'}) :
    f ∈ centerFunctionals N x := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact mem_centerFunctionals_add (mem_centerFunctionals_smul hs c)
    (mem_centerFunctionals_smul hs' d)

theorem isCompl_span_ker {w : V} {h : Dual (ZMod 2) V} (hw : h w = 1) :
    IsCompl (Submodule.span (ZMod 2) {w}) (LinearMap.ker h) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxk
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.mem_ker, map_smul, hw, smul_eq_mul, mul_one] at hxk
    rw [hxk, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = h x • w + (x - h x • w) := by abel
    rw [hx]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)) ?_
    rw [LinearMap.mem_ker, map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]

theorem containsBlock_span_ker {w : V} {h : Dual (ZMod 2) V} (hw : h w = 1) :
    ContainsBlock N (Submodule.span (ZMod 2) {w}) (LinearMap.ker h) := by
  intro g hgS hgC
  have hw0 : w ≠ 0 := fun e => by rw [e, map_zero] at hw; exact zero_ne_one hw
  have hgw : (g : Module.End (ZMod 2) V) w = w := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hgS w (Submodule.mem_span_singleton_self w))
    rcases zmodTwo_eq_zero_or_eq_one c with rfl | rfl
    · exfalso
      apply hw0
      rw [← gl_inv_apply_apply g w, ← hc, zero_smul, map_zero]
    · rw [← hc, one_smul]
  have hg1 : g = 1 := by
    refine Units.ext (LinearMap.ext fun x => ?_)
    have hx : x = h x • w + (x - h x • w) := by abel
    have hk : x - h x • w ∈ LinearMap.ker h := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]
    rw [Units.val_one, Module.End.one_apply, hx, map_add, map_smul, hgw, hgC _ hk]
  rw [hg1]
  exact one_mem N

theorem enlarge_by {S C : Submodule (ZMod 2) V} (hSC : IsCompl S C) (hL : ContainsBlock N S C)
    {c : V} (hcC : c ∈ C)
    (hcF : ∀ h : Dual (ZMod 2) V, (∀ y ∈ C, h y = 0) → h ∈ centerFunctionals N c)
    {μ : Dual (ZMod 2) V} (hμS : ∀ s ∈ S, μ s = 0) (hμc : μ c = 1)
    (hμF : ∀ s ∈ S, μ ∈ centerFunctionals N s) :
    IsCompl (S ⊔ Submodule.span (ZMod 2) {c}) (C ⊓ LinearMap.ker μ) ∧
      ContainsBlock N (S ⊔ Submodule.span (ZMod 2) {c}) (C ⊓ LinearMap.ker μ) := by
  have hc0 : c ≠ 0 := fun e => by rw [e, map_zero] at hμc; exact zero_ne_one hμc
  have hc₁ : c ∈ S ⊔ Submodule.span (ZMod 2) {c} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
  have hμ₁ : ∀ y ∈ C, y - μ y • c ∈ C ⊓ LinearMap.ker μ := fun y hy =>
    Submodule.mem_inf.mpr ⟨C.sub_mem hy (C.smul_mem _ hcC), by
      rw [LinearMap.mem_ker, map_sub, map_smul, hμc, smul_eq_mul, mul_one, sub_self]⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
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

theorem eq_top_of_containsBlock [FiniteDimensional (ZMod 2) V]
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure {n | n ∈ N ∧ IsBinaryTransvection n})
    {S C : Submodule (ZMod 2) V} (hSC : IsCompl S C) (hS : 3 ≤ finrank (ZMod 2) S)
    (hL : ContainsBlock N S C) : N = ⊤ := by
  have key : ∀ k : ℕ, ∀ S C : Submodule (ZMod 2) V, IsCompl S C → 3 ≤ finrank (ZMod 2) S →
      finrank (ZMod 2) C = k → ContainsBlock N S C → N = ⊤ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro S C hSC hS hk hL
      by_cases hC : C = ⊥
      · have hS' : S = ⊤ := by
          have h1 := hSC.sup_eq_top
          rwa [hC, sup_bot_eq] at h1
        refine eq_top_iff.mpr fun g _ => hL g (fun s _ => by rw [hS']; exact Submodule.mem_top)
          fun c hc => ?_
        rw [hC, Submodule.mem_bot] at hc
        rw [hc, map_zero]
      · obtain ⟨S₁, C₁, hSC₁, hSS₁, hlt, hL₁⟩ := enlarge_block hirr hgen hSC hS hL hC
        exact ih _ (hk ▸ hlt) S₁ C₁ hSC₁ (hS.trans (Submodule.finrank_mono hSS₁)) rfl hL₁
  exact key _ S C hSC hS rfl hL

theorem exists_center_eq_one {φ : Dual (ZMod 2) V}
    (hspan : Submodule.span (ZMod 2) (transvectionCenters N) = ⊤) (hφ : φ ≠ 0) :
    ∃ v ∈ transvectionCenters N, φ v = 1 := by
  by_contra hcon
  push Not at hcon
  exact hφ (LinearMap.ext_on hspan fun v hv => by
    rw [LinearMap.zero_apply]
    exact zmodTwo_eq_zero_of_ne_one (hcon v hv))

theorem mem_transvectionCenters_of {u : V} {f : Dual (ZMod 2) V} (hu : u ≠ 0) (hf : f ≠ 0)
    (hfF : f ∈ centerFunctionals N u) : u ∈ transvectionCenters N := by
  refine mem_transvectionCenters.2 ⟨hu, fun h => hf ?_⟩
  rw [h] at hfF
  exact (Submodule.mem_bot _).1 hfF

theorem eq_top_of_two_functionals [FiniteDimensional (ZMod 2) V] (hV : 2 ≤ finrank (ZMod 2) V)
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure {n | n ∈ N ∧ IsBinaryTransvection n}) {u : V}
    {f g : Dual (ZMod 2) V} (hu : u ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f ≠ g)
    (hfF : f ∈ centerFunctionals N u) (hgF : g ∈ centerFunctionals N u) : N = ⊤ := by
  obtain ⟨-, hspan, -, hrecip, r, -, -, hinter⟩ :=
    binary_transvection_center_reciprocity hV N hirr hgen
  have huΔ := mem_transvectionCenters_of hu hf hfF
  obtain ⟨v, hvΔ, hfv⟩ := exists_center_eq_one hspan hf
  obtain ⟨h, hhF, hhv, hh0⟩ : ∃ h ∈ centerFunctionals N u, h v = 0 ∧ h ≠ 0 := by
    rcases zmodTwo_eq_zero_or_eq_one (g v) with hgv | hgv
    · exact ⟨g, hgF, hgv, hg⟩
    · refine ⟨f + g, (centerFunctionals N u).add_mem hfF hgF, ?_, fun h0 => hfg ?_⟩
      · rw [LinearMap.add_apply, hfv, hgv]
        rfl
      · calc f = f + g + g := by rw [add_assoc, BinaryTransvection.add_self_eq_zero, add_zero]
          _ = g := by rw [h0, zero_add]
  have hhuv : h ∈ centerFunctionals N u ⊓ LinearMap.ker (Dual.eval (ZMod 2) V v) :=
    Submodule.mem_inf.2 ⟨hhF, by rw [LinearMap.mem_ker, Dual.eval_apply]; exact hhv⟩
  rw [(hinter u huΔ v hvΔ ⟨f, hfF, hfv⟩).1] at hhuv
  have hhFv : h ∈ centerFunctionals N v := (Submodule.mem_inf.1 hhuv).1
  have hhu : h u = 0 := (mem_centerFunctionals.1 hhF).1
  have huv : u ≠ v := fun e => by
    have h1 := (mem_centerFunctionals.1 hfF).1
    rw [e, hfv] at h1
    exact one_ne_zero h1
  obtain ⟨w, hwΔ, hhw⟩ := exists_center_eq_one hspan hh0
  have hFuv : h ∈ centerFunctionals N (u + v) := mem_centerFunctionals_add hhF hhFv
  have huvΔ : u + v ∈ transvectionCenters N := by
    refine mem_transvectionCenters_of (fun e => huv ?_) hh0 hFuv
    calc u = u + v + v := by rw [add_assoc, BinaryTransvection.add_self_eq_zero, add_zero]
      _ = v := by rw [e, zero_add]
  have hne : ∀ x, h x = 0 → x ≠ w := fun x hx e => by
    rw [e, hhw] at hx
    exact one_ne_zero hx
  obtain ⟨φ₁, hφ₁F, hφ₁u⟩ := (hrecip u huΔ w hwΔ (hne u hhu)).1 ⟨h, hhF, hhw⟩
  obtain ⟨φ₂, hφ₂F, hφ₂v⟩ := (hrecip v hvΔ w hwΔ (hne v hhv)).1 ⟨h, hhFv, hhw⟩
  obtain ⟨φ₃, hφ₃F, hφ₃uv⟩ := (hrecip (u + v) huvΔ w hwΔ
    (hne (u + v) (by rw [map_add, hhu, hhv, add_zero]))).1 ⟨h, hFuv, hhw⟩
  rw [map_add] at hφ₃uv
  obtain ⟨a, haF, hau, hav, b, hbF, hbu, hbv⟩ : ∃ a ∈ centerFunctionals N w, a u = 1 ∧ a v = 0 ∧
      ∃ b ∈ centerFunctionals N w, b u = 0 ∧ b v = 1 := by
    have hadd := fun (φ ψ : Dual (ZMod 2) V) (hφ : φ ∈ centerFunctionals N w)
      (hψ : ψ ∈ centerFunctionals N w) => (centerFunctionals N w).add_mem hφ hψ
    rcases zmodTwo_eq_zero_or_eq_one (φ₁ v) with h1 | h1 <;>
      rcases zmodTwo_eq_zero_or_eq_one (φ₂ u) with h2 | h2
    · exact ⟨φ₁, hφ₁F, hφ₁u, h1, φ₂, hφ₂F, h2, hφ₂v⟩
    · refine ⟨φ₁, hφ₁F, hφ₁u, h1, φ₁ + φ₂, hadd _ _ hφ₁F hφ₂F, ?_, ?_⟩ <;>
        simp only [LinearMap.add_apply, hφ₁u, h1, h2, hφ₂v] <;> rfl
    · refine ⟨φ₁ + φ₂, hadd _ _ hφ₁F hφ₂F, ?_, ?_, φ₂, hφ₂F, h2, hφ₂v⟩ <;>
        simp only [LinearMap.add_apply, hφ₁u, h1, h2, hφ₂v] <;> rfl
    · rcases zmodTwo_eq_zero_or_eq_one (φ₃ u) with h3 | h3
      · have h3' : φ₃ v = 1 := by
          rw [h3, zero_add] at hφ₃uv
          exact hφ₃uv
        refine ⟨φ₁ + φ₃, hadd _ _ hφ₁F hφ₃F, ?_, ?_, φ₃, hφ₃F, h3, h3'⟩ <;>
          simp only [LinearMap.add_apply, hφ₁u, h1, h3, h3'] <;> rfl
      · have h3' : φ₃ v = 0 := by
          rw [h3] at hφ₃uv
          revert hφ₃uv
          generalize φ₃ v = z
          revert z
          decide
        refine ⟨φ₃, hφ₃F, h3, h3', φ₁ + φ₃, hadd _ _ hφ₁F hφ₃F, ?_, ?_⟩ <;>
          simp only [LinearMap.add_apply, hφ₁u, h1, h3, h3'] <;> rfl
  have haw : a w = 0 := (mem_centerFunctionals.1 haF).1
  have hbw : b w = 0 := (mem_centerFunctionals.1 hbF).1
  have haFv : a ∈ centerFunctionals N v := mem_of_incidence hhFv hhw haF hav
  have hbFu : b ∈ centerFunctionals N u := mem_of_incidence hhF hhw hbF hbu
  have hSC₀ := isCompl_span_ker (V := V) hhw
  have hL₀ : ContainsBlock N (Submodule.span (ZMod 2) {w}) (LinearMap.ker h) :=
    containsBlock_span_ker hhw
  obtain ⟨hSC₁, hL₁⟩ := enlarge_by hSC₀ hL₀ (c := u) (μ := a) hhu
    (fun h' hh' => by
      have heq : h' = h' w • h := by
        ext x
        have hk : x - h x • w ∈ LinearMap.ker h := by
          rw [LinearMap.mem_ker, map_sub, map_smul, hhw, smul_eq_mul, mul_one, sub_self]
        have h1 := hh' _ hk
        rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h1
        rw [LinearMap.smul_apply, h1, smul_eq_mul, mul_comm]
      rw [heq]
      exact (centerFunctionals N u).smul_mem _ hhF)
    (fun s hs => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
      rw [map_smul, haw, smul_zero])
    hau
    (fun s hs => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
      exact mem_centerFunctionals_smul haF c)
  obtain ⟨hSC₂, hL₂⟩ := enlarge_by hSC₁ hL₁ (c := v) (μ := b)
    (Submodule.mem_inf.2 ⟨hhv, hav⟩)
    (fun h' hh' => by
      have heq : h' = h' w • h + h' u • a := by
        ext x
        have hk : x - h x • w - a x • u ∈ LinearMap.ker h ⊓ LinearMap.ker a := by
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩
          · rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, hhw, hhu,
              smul_eq_mul, smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
          · rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, haw, hau,
              smul_eq_mul, smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
        have h1 := hh' _ hk
        rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, sub_sub,
          sub_eq_zero] at h1
        rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, h1, smul_eq_mul,
          smul_eq_mul, mul_comm (h' w), mul_comm (h' u)]
      rw [heq]
      exact (centerFunctionals N v).add_mem ((centerFunctionals N v).smul_mem _ hhFv)
        ((centerFunctionals N v).smul_mem _ haFv))
    (fun s hs => by
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hs
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [map_add, map_smul, map_smul, hbw, hbu, smul_zero, smul_zero, add_zero])
    hbv
    (fun s hs => mem_centerFunctionals_of_mem_sup hbF hbFu hs)
  have hli : LinearIndependent (ZMod 2) ![w, u, v] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [Fin.sum_univ_three] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at hc
    have e1 := congrArg h hc
    have e2 := congrArg a hc
    have e3 := congrArg b hc
    simp only [map_add, map_smul, map_zero, smul_eq_mul, hhw, hhu, hhv, haw, hau, hav, hbw, hbu,
      hbv, mul_one, mul_zero, add_zero, zero_add] at e1 e2 e3
    fin_cases i
    · exact e1
    · exact e2
    · exact e3
  have hdim : 3 ≤ finrank (ZMod 2)
      ↥(Submodule.span (ZMod 2) {w} ⊔ Submodule.span (ZMod 2) {u} ⊔
        Submodule.span (ZMod 2) {v}) := by
    have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range ![w, u, v])) = 3 := by
      rw [finrank_span_eq_card hli]
      simp
    have hle : Submodule.span (ZMod 2) (Set.range ![w, u, v]) ≤
        Submodule.span (ZMod 2) {w} ⊔ Submodule.span (ZMod 2) {u} ⊔
          Submodule.span (ZMod 2) {v} := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.mem_sup_left
          (Submodule.mem_sup_left (Submodule.mem_span_singleton_self w))
      · exact Submodule.mem_sup_left
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
      · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
    calc 3 = _ := h1.symm
      _ ≤ _ := Submodule.finrank_mono hle
  exact eq_top_of_containsBlock hirr hgen hSC₂ hdim hL₂

end SteinbergBQ.RepeatedCenter

open SteinbergBQ.RepeatedCenter

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem repeated_transvection_center_forces_full_binary_linear_group
    [FiniteDimensional (ZMod 2) V] (hV : 2 ≤ finrank (ZMod 2) V)
    (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure {n | n ∈ N ∧ IsBinaryTransvection n}) :
    ((∃ (u : V) (f g : Dual (ZMod 2) V), u ≠ 0 ∧ f ≠ 0 ∧ g ≠ 0 ∧ f ≠ g ∧ f u = 0 ∧ g u = 0 ∧
        (∃ n ∈ N, (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u) ∧
        ∃ n ∈ N, (n : Module.End (ZMod 2) V) = LinearMap.id + g.smulRight u) → N = ⊤) ∧
    (N ≠ ⊤ → ∃! β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt ∧ β.Nondegenerate ∧
      N ≤ Quasithin.SteinbergBN.isometryGroup β) := by
  classical
  have hfull : (∃ (u : V) (f g : Dual (ZMod 2) V), u ≠ 0 ∧ f ≠ 0 ∧ g ≠ 0 ∧ f ≠ g ∧ f u = 0 ∧
      g u = 0 ∧ (∃ n ∈ N, (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u) ∧
      ∃ n ∈ N, (n : Module.End (ZMod 2) V) = LinearMap.id + g.smulRight u) → N = ⊤ := by
    rintro ⟨u, f, g, hu, hf, hg, hfg, hfu, hgu, ⟨n, hn, hnf⟩, ⟨m, hm, hmg⟩⟩
    exact eq_top_of_two_functionals hV hirr hgen hu hf hg hfg ⟨hfu, n, hn, hnf⟩
      ⟨hgu, m, hm, hmg⟩
  refine ⟨hfull, fun hN => ?_⟩
  have hdata : ∀ t : LinearMap.GeneralLinearGroup (ZMod 2) V, ∃ (x : V) (φ : Dual (ZMod 2) V),
      t ∈ transvectionSet N → x ≠ 0 ∧ φ ≠ 0 ∧ φ x = 0 ∧
        (t : Module.End (ZMod 2) V) = LinearMap.id + φ.smulRight x := by
    intro t
    by_cases ht : t ∈ transvectionSet N
    · obtain ⟨x, φ, hx, hφ, hφx, htx⟩ := (mem_transvectionSet.1 ht).2
      exact ⟨x, φ, fun _ => ⟨hx, hφ, hφx, htx⟩⟩
    · exact ⟨0, 0, fun h => absurd h ht⟩
  choose vt φt hvφ using hdata
  obtain ⟨-, huniq, -, hfour, -⟩ :=
    binary_transvection_pairing_form_dichotomy hV N hirr hgen vt φt hvφ
  by_cases hpair : ∀ s ∈ transvectionSet N, ∀ t ∈ transvectionSet N, φt s (vt t) = φt t (vt s)
  · exact huniq hpair
  · exfalso
    obtain ⟨u, f, g, hu, hli, hfu, hgu, Q, hQ, hQN, -, -⟩ := hfour hpair
    have hf0 : f ≠ 0 := by simpa using hli.ne_zero 0
    have hg0 : g ≠ 0 := by simpa using hli.ne_zero 1
    have hfg : f ≠ g := by simpa using hli.injective.ne (show (0 : Fin 2) ≠ 1 by decide)
    have hmemN : ∀ φ ∈ ({f, g} : Set (Dual (ZMod 2) V)), φ u = 0 →
        ∃ n ∈ N, (n : Module.End (ZMod 2) V) = LinearMap.id + φ.smulRight u := by
      intro φ hφ hφu
      obtain ⟨n, hn⟩ := exists_unit_eq_id_add_smulRight hφu
      have hnQ : n ∈ Q := by
        rw [← SetLike.mem_coe, hQ]
        exact ⟨φ, Submodule.subset_span hφ, hn⟩
      exact ⟨n, hQN hnQ, hn⟩
    exact hN (hfull ⟨u, f, g, hu, hf0, hg0, hfg, hfu, hgu, hmemN f (by simp) hfu,
      hmemN g (by simp) hgu⟩)

end CFSG.LocalAnalysis
