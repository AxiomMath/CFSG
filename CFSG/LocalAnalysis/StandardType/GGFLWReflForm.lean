module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6w1_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle hpge)

private lemma l6w1_smul_cancel {p : ℕ} [Fact p.Prime] {T : Type} [AddCommGroup T]
    [Module (ZMod p) T] {c : T} (hc : c ≠ 0) {a b : ZMod p} (h : a • c = b • c) : a = b := by
  by_contra hab
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h' : (a - b) • c = 0 := by rw [sub_smul, h, sub_self]
  have hc0 : c = 0 := by
    calc c = 1 • c := (one_smul (ZMod p) c).symm
      _ = ((a - b)⁻¹ * (a - b)) • c := by rw [← inv_mul_cancel₀ hne]
      _ = (a - b)⁻¹ • ((a - b) • c) := by rw [← smul_smul]
      _ = (a - b)⁻¹ • 0 := by rw [h']
      _ = 0 := smul_zero _
  exact hc hc0

theorem ggFLW_isRefl_form {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {T : Type} [AddCommGroup T]
    [Module (ZMod p) T] {t : T ≃ₗ[ZMod p] T} (ht : ZS.IsRefl p t) :
    ∃ (c : T) (β : Module.Dual (ZMod p) T), c ≠ 0 ∧ β c = 2 ∧ ∀ v, t v = v - β v • c := by
  let f : T →ₗ[ZMod p] T := (t : T →ₗ[ZMod p] T) - LinearMap.id
  have hfin : Module.finrank (ZMod p) ↥f.range = 1 := ht.2
  haveI : Module.Free (ZMod p) ↥f.range := Module.Free.of_divisionRing (ZMod p) ↥f.range
  obtain ⟨c0, hc0ne, hspan0⟩ := (finrank_eq_one_iff' (K := ZMod p) (V := ↥f.range)).mp hfin
  have hc : (c0 : T) ≠ 0 := fun h => hc0ne (Subtype.ext h)
  have h_range : f.range = Submodule.span (ZMod p) {(c0 : T)} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha⟩ := hspan0 ⟨x, hx⟩
      exact Submodule.mem_span_singleton.mpr ⟨a, congrArg Subtype.val ha⟩
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact c0.2
  have hex : ∀ v : T, ∃ a : ZMod p, a • (c0 : T) = f v := fun v =>
    Submodule.mem_span_singleton.mp (h_range ▸ LinearMap.mem_range.mpr ⟨v, rfl⟩)
  let βfun : T → ZMod p := fun v => -Classical.choose (hex v)
  have hβfun : ∀ v : T, βfun v • (c0 : T) = -(f v) := by
    intro v
    have hspec : Classical.choose (hex v) • (c0 : T) = f v := Classical.choose_spec (hex v)
    show (-Classical.choose (hex v)) • (c0 : T) = -(f v)
    rw [neg_smul, hspec]
  have hβadd : ∀ v w : T, βfun (v + w) = βfun v + βfun w := by
    intro v w
    apply l6w1_smul_cancel hc
    rw [hβfun (v + w), add_smul, hβfun v, hβfun w, map_add, neg_add]
  have hβsmul : ∀ (r : ZMod p) (v : T), βfun (r • v) = r * βfun v := by
    intro r v
    apply l6w1_smul_cancel hc
    rw [hβfun (r • v), map_smul, ← smul_smul, hβfun v, smul_neg]
  let β : Module.Dual (ZMod p) T :=
    { toFun := βfun
      map_add' := hβadd
      map_smul' := fun r v => by simpa [smul_eq_mul] using hβsmul r v }
  have hβform : ∀ v : T, t v = v - β v • (c0 : T) := by
    intro v
    have h := hβfun v
    have hfv : f v = t v - v := rfl
    rw [hfv] at h
    change t v = v - βfun v • (c0 : T)
    rw [h]
    abel
  have hβne : β ≠ 0 := by
    intro hβ0
    have ht1 : t = 1 := by
      ext v
      rw [hβform v, hβ0]
      simp
    have hf0 : f = 0 := by
      ext v
      have hv : t v = v := by rw [ht1]; rfl
      simp [f, hv]
    have hbot : f.range = ⊥ := by rw [hf0, LinearMap.range_zero]
    have h1 : Module.finrank (ZMod p) (⊥ : Submodule (ZMod p) T) = 1 := by
      rw [← hbot]; exact ht.2
    have h0 : Module.finrank (ZMod p) (⊥ : Submodule (ZMod p) T) = 0 := finrank_bot (ZMod p) T
    rw [h0] at h1
    exact Nat.zero_ne_one h1
  have hrel : ∀ v : T, β v * (2 - β (c0 : T)) = 0 := by
    intro v
    have ht2 : t (t v) = v := by
      have h := congr_fun (congrArg (fun e : T ≃ₗ[ZMod p] T => (e : T → T)) ht.1) v
      simpa [LinearEquiv.mul_apply] using h
    have hβlin : β (t v) = β v - β v * β (c0 : T) := by
      rw [hβform v, map_sub, map_smul, smul_eq_mul]
    have h1 : β (t v) • (c0 : T) = t v - v := by
      have hform := hβform (t v)
      rw [ht2] at hform
      have hsum : v + β (t v) • (c0 : T) = t v := eq_sub_iff_add_eq.mp hform
      exact eq_sub_iff_add_eq.mpr (by rwa [add_comm] at hsum)
    have h1b : (-β v) • (c0 : T) = t v - v := by
      rw [hβform v, neg_smul]
      abel
    have hβtv_eq : β (t v) = -β v := l6w1_smul_cancel hc (h1.trans h1b.symm)
    have h := hβtv_eq.symm.trans hβlin
    calc β v * (2 - β (c0 : T)) = β v - β v * β (c0 : T) + β v := by ring
      _ = -β v + β v := by rw [← h]
      _ = 0 := by ring
  have hβc0 : β (c0 : T) = 2 := by
    obtain ⟨v, hv⟩ : ∃ v : T, β v ≠ 0 := by
      have hnf : ¬∀ v : T, β v = 0 := fun h => hβne (LinearMap.ext (fun v => by simpa using h v))
      exact not_forall.mp hnf
    have h := hrel v
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hv
    · exact (sub_eq_zero.mp h0).symm
  exact ⟨(c0 : T), β, hc, hβc0, hβform⟩

theorem ggFLW_invariantForm {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {T : Type} [AddCommGroup T]
    [Module (ZMod p) T] {κ : Type} [Finite κ] (c : κ → T) (β : κ → Module.Dual (ZMod p) T)
    (g : κ → (T ≃ₗ[ZMod p] T)) (hg : ∀ i v, g i v = v - β i v • c i) (hβ : ∀ i, β i (c i) = 2)
    (hspan : Submodule.span (ZMod p) (Set.range c) = ⊤)
    (hker : ∀ v, (∀ i, β i v = 0) → v = 0) (d : κ → ZMod p) (hd : ∀ i, d i ≠ 0)
    (hsym : ∀ i j, d i * β i (c j) = d j * β j (c i)) :
    ∃ B : LinearMap.BilinForm (ZMod p) T, (∀ w, (∀ u, B w u = 0) → w = 0) ∧
      ∀ i u v, B (g i u) (g i v) = B u v := by
  have h2 : (2 : ZMod p) ≠ 0 := l6w1_two_ne_zero hp2
  let e : κ → ZMod p := fun i => d i / 2
  have he : ∀ i, e i ≠ 0 := fun i => div_ne_zero (hd i) h2
  have hkey : ∀ i j, e i * β i (c j) = e j * β j (c i) := by
    intro i j
    apply mul_left_cancel₀ h2
    calc (2 : ZMod p) * (e i * β i (c j))
        = d i * β i (c j) := by
          show (2 : ZMod p) * ((d i / 2) * β i (c j)) = d i * β i (c j)
          rw [← mul_assoc, mul_comm (2 : ZMod p) (d i / 2), div_mul_cancel₀ (d i) h2]
      _ = d j * β j (c i) := hsym i j
      _ = (2 : ZMod p) * (e j * β j (c i)) := by
          show d j * β j (c i) = (2 : ZMod p) * ((d j / 2) * β j (c i))
          rw [← mul_assoc, mul_comm (2 : ZMod p) (d j / 2), div_mul_cancel₀ (d j) h2]
  let E : (κ →₀ ZMod p) →ₗ[ZMod p] T := Finsupp.linearCombination (ZMod p) c
  let Φ : (κ →₀ ZMod p) →ₗ[ZMod p] Module.Dual (ZMod p) T :=
    Finsupp.linearCombination (ZMod p) (fun i => e i • β i)
  have hE : Function.Surjective E := by
    have hr : E.range = Submodule.span (ZMod p) (Set.range c) :=
      Finsupp.range_linearCombination (ZMod p) (v := c)
    rw [← LinearMap.range_eq_top, hr, hspan]
  have hΦsingle : ∀ (i : κ) (b : ZMod p), Φ (Finsupp.single i b) = b • (e i • β i) := by
    intro i b
    show (Finsupp.linearCombination (ZMod p) (fun i => e i • β i)) (Finsupp.single i b) =
      b • (e i • β i)
    rw [Finsupp.linearCombination_single]
  have hEsingle : ∀ (i : κ) (b : ZMod p), E (Finsupp.single i b) = b • c i := by
    intro i b
    show (Finsupp.linearCombination (ZMod p) c) (Finsupp.single i b) = b • c i
    rw [Finsupp.linearCombination_single]
  have hΦE : ∀ (a : κ →₀ ZMod p) (k : κ), Φ a (c k) = e k * β k (E a) := by
    intro a
    refine Finsupp.induction (motive := fun a => ∀ k, Φ a (c k) = e k * β k (E a)) a ?_ ?_
    · intro k
      rw [map_zero Φ, map_zero E, LinearMap.zero_apply, map_zero (β k), mul_zero]
    · intro i b l _hi _hb ih k
      rw [map_add, map_add]
      change Φ (Finsupp.single i b) (c k) + Φ l (c k) =
        e k * β k (E (Finsupp.single i b) + E l)
      rw [hΦsingle i b, hEsingle i b, ih k]
      simp only [LinearMap.smul_apply, map_add, map_smul, smul_eq_mul]
      rw [hkey i k]
      ring
  have hker_le : LinearMap.ker E ≤ LinearMap.ker Φ := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    apply LinearMap.ext_on_range (v := c) hspan
    intro k
    rw [hΦE a k, ha]
    simp
  let B' : T →ₗ[ZMod p] Module.Dual (ZMod p) T :=
    (Submodule.liftQ (LinearMap.ker E) Φ hker_le).comp
      (LinearMap.quotKerEquivOfSurjective E hE).symm.toLinearMap
  have hb' : ∀ a : κ →₀ ZMod p, B' (E a) = Φ a := by
    intro a
    change (Submodule.liftQ (LinearMap.ker E) Φ hker_le)
        ((LinearMap.quotKerEquivOfSurjective E hE).symm (E a)) = Φ a
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have hBci : ∀ (u : T) (i : κ), (LinearMap.flip B') u (c i) = e i * β i u := by
    intro u i
    have hci : c i = E (Finsupp.single i 1) := by rw [hEsingle i 1, one_smul]
    rw [hci, LinearMap.flip_apply, hb', hΦsingle i 1]
    simp [LinearMap.smul_apply, smul_eq_mul]
  refine ⟨LinearMap.flip B', ?_, ?_⟩
  · intro w hw
    apply hker w
    intro i
    have h1 : (LinearMap.flip B') w (c i) = e i * β i w := hBci w i
    have h2 : (LinearMap.flip B') w (c i) = 0 := hw (c i)
    have h3 : e i * β i w = 0 := by rw [← h1, h2]
    exact (mul_eq_zero.mp h3).resolve_left (he i)
  · intro i u v
    have hF : ((LinearMap.flip B') (g i u)).comp (g i : T →ₗ[ZMod p] T) =
        (LinearMap.flip B') u := by
      apply LinearMap.ext_on_range (v := c) hspan
      intro j
      simp only [LinearMap.comp_apply]
      change (B'.flip ((g i) u)) ((g i) (c j)) = (B'.flip u) (c j)
      rw [hg i (c j), map_sub, map_smul, hBci (g i u) j, hBci (g i u) i, hBci u j]
      have hβgi : β i (g i u) = -β i u := by
        rw [hg i u, map_sub, map_smul, hβ i, smul_eq_mul]
        ring
      have hβgj : β j (g i u) = β j u - β i u * β j (c i) := by
        rw [hg i u, map_sub, map_smul, smul_eq_mul]
      rw [hβgi, hβgj]
      simp only [smul_eq_mul]
      rw [show β i (c j) * (e i * (-β i u)) = -(e i * β i (c j)) * β i u by ring]
      rw [hkey i j]
      ring
    change (LinearMap.flip B') (g i u) ((↑(g i) : T →ₗ[ZMod p] T) v) =
      (LinearMap.flip B') u v
    simpa only [LinearMap.comp_apply] using
      congrArg (fun L : T →ₗ[ZMod p] ZMod p => L v) hF

end CFSG.StandardType

end
