module

public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.PUMul
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Schur

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

private lemma s168e3_cyc3_map_zpowers_conj_eq {x y : MulAut W} (hxy : x * y = y * x) :
    (Subgroup.zpowers y).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers y := by
  rw [MonoidHom.map_zpowers]
  congr 1
  change (MulAut.conj x) y = y
  rw [MulAut.conj_apply, hxy]
  group

private lemma s168e3_cyc3_x_stable_commSub {x y : MulAut W} (hxy : x * y = y * x) :
    ∀ z ∈ commSub ⊤ (Subgroup.zpowers y), x z ∈ commSub ⊤ (Subgroup.zpowers y) := by
  have hmapY := s168e3_cyc3_map_zpowers_conj_eq hxy
  have h := CFSG.Quasithin.Asc81c.commSub_map_conj (Subgroup.zpowers y) x
  rw [hmapY] at h
  intro z hz
  rw [h]
  exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩

private lemma s168e3_cyc3_ext_of_eq_on {Z₁ Z₂ : Subgroup W} (hZtop : Z₁ ⊔ Z₂ = ⊤)
    {g h : MulAut W} (h₁ : ∀ z ∈ Z₁, g z = h z) (h₂ : ∀ z ∈ Z₂, g z = h z) : g = h := by
  refine MulEquiv.ext fun w => ?_
  have hw : w ∈ Z₁ ⊔ Z₂ := by rw [hZtop]; exact Subgroup.mem_top w
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Subgroup.mem_sup.mp hw
  rw [map_mul, map_mul, h₁ z₁ hz₁, h₂ z₂ hz₂]

private lemma s168e3_cyc3_pow_apply_eq {g ξ : MulAut W} {Z : Subgroup W} {e : ℕ}
    (hstab : ∀ z ∈ Z, g z ∈ Z) (hg : ∀ z ∈ Z, g z = (ξ ^ e) z) :
    ∀ n : ℕ, ∀ z ∈ Z, (g ^ n) z = ((ξ ^ e) ^ n) z := by
  intro n
  induction n with
  | zero => intro z _; rw [pow_zero, pow_zero, MulAut.one_apply]
  | succ n ih =>
      intro z hz
      calc (g ^ (n + 1)) z = (g ^ n) (g z) := by rw [pow_succ, MulAut.mul_apply]
        _ = ((ξ ^ e) ^ n) (g z) := ih (g z) (hstab z hz)
        _ = ((ξ ^ e) ^ n) ((ξ ^ e) z) := by rw [hg z hz]
        _ = ((ξ ^ e) ^ (n + 1)) z := by rw [pow_succ, MulAut.mul_apply]

private lemma s168e3_cyc3_pow_three_eq {Z : Subgroup W} {x b : MulAut W} {e : ℕ}
    (hbZ : ∀ z ∈ Z, b z ∈ Z) (hb : ∀ z ∈ Z, b z = (x ^ e) z) (hx3 : x ^ 3 = 1) :
    ∀ z ∈ Z, (b ^ 3) z = z := by
  intro z hz
  rw [s168e3_cyc3_pow_apply_eq hbZ hb 3 z hz,
    show (x ^ e) ^ 3 = 1 by rw [← pow_mul, Nat.mul_comm, pow_mul, hx3, one_pow],
    MulAut.one_apply]

private lemma s168e3_cyc3_pow_fix {y : MulAut W} {Z : Subgroup W} (hy : ∀ z ∈ Z, y z = z) :
    ∀ n : ℕ, ∀ z ∈ Z, (y ^ n) z = z := by
  intro n
  induction n with
  | zero => intro z _; rw [pow_zero, MulAut.one_apply]
  | succ n ih =>
      intro z hz
      rw [pow_succ, MulAut.mul_apply, ih (y z) (by rw [hy z hz]; exact hz), hy z hz]

private lemma s168e3_cyc3_zpowers_fix {y : MulAut W} {z : W} (h : y z = z) :
    ∀ m ∈ Subgroup.zpowers y, m z = z := by
  intro m hm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  exact CFSG.HardMathSupport.Meierfrankenfeld.Proving.zpow_apply_eq_of_apply_eq h k

private lemma s168e3_cyc3_schur_coord {Z : Subgroup W} (hZ : Nat.card ↥Z = 4)
    {x b : MulAut W} (hx3 : x ^ 3 = 1) (hfpf : ∀ w : W, x w = w → w = 1)
    (hxZ : ∀ z ∈ Z, x z ∈ Z) (hbZ : ∀ z ∈ Z, b z ∈ Z) (hbx : x * b = b * x) :
    ∃ e : ℕ, e < 3 ∧ ∀ z ∈ Z, b z = (x ^ e) z := by
  refine s16e_d5_schur_local hZ hx3 hxZ (fun z hz h => hfpf z h) hbZ ?_
  intro z hz
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, hbx]

private lemma s168e3_cyc3_mul_apply_pow {Z : Subgroup W} {x a b : MulAut W} {ea eb : ℕ}
    (hax : a * x = x * a) (ha : ∀ z ∈ Z, a z = (x ^ ea) z)
    (hb : ∀ z ∈ Z, b z = (x ^ eb) z) :
    ∀ z ∈ Z, (a * b) z = (x ^ (ea + eb)) z := by
  intro z hz
  have hcomm : a * (x ^ eb) = (x ^ eb) * a :=
    (show Commute a x from hax).pow_right eb |>.eq
  calc (a * b) z = a (b z) := by rw [MulAut.mul_apply]
    _ = a ((x ^ eb) z) := by rw [hb z hz]
    _ = (a * (x ^ eb)) z := by rw [← MulAut.mul_apply]
    _ = ((x ^ eb) * a) z := by rw [hcomm]
    _ = (x ^ eb) (a z) := by rw [MulAut.mul_apply]
    _ = (x ^ eb) ((x ^ ea) z) := by rw [ha z hz]
    _ = ((x ^ eb) * (x ^ ea)) z := by rw [← MulAut.mul_apply]
    _ = (x ^ (eb + ea)) z := by rw [← pow_add]
    _ = (x ^ (ea + eb)) z := by rw [Nat.add_comm]

private lemma s168e3_cyc3_mul_apply_pow' {Z : Subgroup W} {x a b : MulAut W} {ea eb : ℕ}
    (hbx : b * x = x * b) (ha : ∀ z ∈ Z, a z = (x ^ ea) z)
    (hb : ∀ z ∈ Z, b z = (x ^ eb) z) :
    ∀ z ∈ Z, (b * a) z = (x ^ (ea + eb)) z := by
  intro z hz
  have hcomm : b * (x ^ ea) = (x ^ ea) * b :=
    (show Commute b x from hbx).pow_right ea |>.eq
  calc (b * a) z = b (a z) := by rw [MulAut.mul_apply]
    _ = b ((x ^ ea) z) := by rw [ha z hz]
    _ = (b * (x ^ ea)) z := by rw [← MulAut.mul_apply]
    _ = ((x ^ ea) * b) z := by rw [hcomm]
    _ = (x ^ ea) (b z) := by rw [MulAut.mul_apply]
    _ = (x ^ ea) ((x ^ eb) z) := by rw [hb z hz]
    _ = ((x ^ ea) * (x ^ eb)) z := by rw [← MulAut.mul_apply]
    _ = (x ^ (ea + eb)) z := by rw [← pow_add]

private lemma s168e3_cyc3_pow_apply_eq_pow {Z : Subgroup W} {x y : MulAut W} {e a m : ℕ}
    (hyZ : ∀ z ∈ Z, y z ∈ Z) (hy : ∀ z ∈ Z, y z = (x ^ e) z)
    (hp : x ^ (e * m) = x ^ a) : ∀ z ∈ Z, (y ^ m) z = (x ^ a) z := by
  intro z hz
  rw [s168e3_cyc3_pow_apply_eq hyZ hy m z hz, ← pow_mul, hp]

private lemma s168e3_cyc3_pow_eq_of_coord {Z₁ Z₂ : Subgroup W} (hZtop : Z₁ ⊔ Z₂ = ⊤)
    {x y k : MulAut W} {e a m : ℕ}
    (hyZ₁ : ∀ z ∈ Z₁, y z ∈ Z₁) (hy₁ : ∀ z ∈ Z₁, y z = (x ^ e) z)
    (hp : x ^ (e * m) = x ^ a) (hk₁ : ∀ z ∈ Z₁, k z = (x ^ a) z)
    (hyfix₂ : ∀ z ∈ Z₂, y z = z) (hkfix₂ : ∀ z ∈ Z₂, k z = z) :
    y ^ m = k := by
  refine s168e3_cyc3_ext_of_eq_on hZtop (g := y ^ m) (h := k) ?_ ?_
  · intro z hz
    rw [s168e3_cyc3_pow_apply_eq_pow hyZ₁ hy₁ hp z hz, hk₁ z hz]
  · intro z hz
    rw [s168e3_cyc3_pow_fix hyfix₂ m z hz, hkfix₂ z hz]

theorem s168e3_cyc3_coord [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {A E : Subgroup (MulAut W)}
    {x y₂ : MulAut W} {Z₁ Z₂ : Subgroup W} (hEA : E ≤ A)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hxE : x ∈ E)
    (hy₂E : y₂ ∈ E) (hy₂ : y₂ ≠ 1) (hfpf : ∀ w : W, x w = w → w = 1)
    (hfix₂ : fixV (Subgroup.zpowers y₂) = Z₂) (hcom₂ : commSub ⊤ (Subgroup.zpowers y₂) = Z₁)
    (hZ₁ : Nat.card ↥Z₁ = 4) (hZ₂ : Nat.card ↥Z₂ = 4) (hZtop : Z₁ ⊔ Z₂ = ⊤)
    {B K : Subgroup (MulAut W)}
    (hB : B = A ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup (MulAut W)) :
      Set (MulAut W)) ⊓ stabSub Z₁ ⊓ stabSub Z₂)
    (hK : K = B ⊓ centSub Z₂) :
    IsPGroup 3 ↥B ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ K = Subgroup.zpowers y₂ := by
  have hx3 : x ^ 3 = 1 := hE3 x hxE
  have hxy : x * y₂ = y₂ * x := hEc x hxE y₂ hy₂E
  have hxZ₁ : ∀ z ∈ Z₁, x z ∈ Z₁ := by
    intro z hz
    rw [← hcom₂] at hz ⊢
    exact s168e3_cyc3_x_stable_commSub hxy z hz
  have hxZ₂ : ∀ z ∈ Z₂, x z ∈ Z₂ := by
    intro z hz
    rw [← hfix₂] at hz ⊢
    exact CFSG.HardMathSupport.Meierfrankenfeld.Proving.apply_mem_fixV_zpowers_of_commute hxy hz
  have hBmem : ∀ b ∈ B, b ∈ A ∧
      b ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup (MulAut W)) : Set (MulAut W)) ∧
      b ∈ stabSub Z₁ ∧ b ∈ stabSub Z₂ := by
    intro b hb
    rw [hB] at hb
    exact ⟨hb.1.1.1, hb.1.1.2, hb.1.2, hb.2⟩
  have hcoord : ∀ b ∈ B, ∃ e₁ e₂ : ℕ, e₁ < 3 ∧ e₂ < 3 ∧
      (∀ z ∈ Z₁, b z = (x ^ e₁) z) ∧ (∀ z ∈ Z₂, b z = (x ^ e₂) z) := by
    intro b hb
    obtain ⟨hbA, hbC, hbS₁, hbS₂⟩ := hBmem b hb
    have hbx : x * b = b * x := (Subgroup.mem_centralizer_iff.mp hbC) x (Subgroup.mem_zpowers x)
    have hb₁ : ∀ z ∈ Z₁, b z ∈ Z₁ := fun z hz => (mem_stabSub.mp hbS₁ z).2 hz
    have hb₂ : ∀ z ∈ Z₂, b z ∈ Z₂ := fun z hz => (mem_stabSub.mp hbS₂ z).2 hz
    obtain ⟨e₁, he₁, h₁⟩ := s168e3_cyc3_schur_coord hZ₁ hx3 hfpf hxZ₁ hb₁ hbx
    obtain ⟨e₂, he₂, h₂⟩ := s168e3_cyc3_schur_coord hZ₂ hx3 hfpf hxZ₂ hb₂ hbx
    exact ⟨e₁, e₂, he₁, he₂, h₁, h₂⟩
  have hpow : ∀ b ∈ B, b ^ 3 = 1 := by
    intro b hb
    obtain ⟨e₁, e₂, he₁, he₂, h₁, h₂⟩ := hcoord b hb
    obtain ⟨hbA, hbC, hbS₁, hbS₂⟩ := hBmem b hb
    have hb₁ : ∀ z ∈ Z₁, b z ∈ Z₁ := fun z hz => (mem_stabSub.mp hbS₁ z).2 hz
    have hb₂ : ∀ z ∈ Z₂, b z ∈ Z₂ := fun z hz => (mem_stabSub.mp hbS₂ z).2 hz
    refine s168e3_cyc3_ext_of_eq_on hZtop (g := b ^ 3) (h := 1) ?_ ?_
    · intro z hz
      rw [s168e3_cyc3_pow_three_eq hb₁ h₁ hx3 z hz, MulAut.one_apply]
    · intro z hz
      rw [s168e3_cyc3_pow_three_eq hb₂ h₂ hx3 z hz, MulAut.one_apply]
  have hpg : IsPGroup 3 ↥B := by
    intro b
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by simpa using hpow (b : MulAut W) b.2)
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ea₁, ea₂, hea₁, hea₂, ha₁, ha₂⟩ := hcoord a ha
    obtain ⟨eb₁, eb₂, heb₁, heb₂, hb₁, hb₂⟩ := hcoord b hb
    obtain ⟨haA, haC, haS₁, haS₂⟩ := hBmem a ha
    obtain ⟨hbA, hbC, hbS₁, hbS₂⟩ := hBmem b hb
    have hax : a * x = x * a :=
      ((Subgroup.mem_centralizer_iff.mp haC) x (Subgroup.mem_zpowers x)).symm
    have hbx : b * x = x * b :=
      ((Subgroup.mem_centralizer_iff.mp hbC) x (Subgroup.mem_zpowers x)).symm
    refine s168e3_cyc3_ext_of_eq_on hZtop (g := a * b) (h := b * a) ?_ ?_
    · intro z hz
      rw [s168e3_cyc3_mul_apply_pow hax ha₁ hb₁ z hz,
        s168e3_cyc3_mul_apply_pow' hbx ha₁ hb₁ z hz]
    · intro z hz
      rw [s168e3_cyc3_mul_apply_pow hax ha₂ hb₂ z hz,
        s168e3_cyc3_mul_apply_pow' hbx ha₂ hb₂ z hz]
  have hy₂C : y₂ ∈ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (show Commute x y₂ from hxy).zpow_left k |>.eq
  have hy₂S₁ : y₂ ∈ stabSub Z₁ := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      rw [← hcom₂] at hu ⊢
      have hyinv : y₂⁻¹ ∈ Subgroup.zpowers y₂ :=
        (Subgroup.zpowers y₂).inv_mem (Subgroup.mem_zpowers y₂)
      have h := CFSG.Quasithin.Asc81c.commSub_stable' hyinv hu
      rwa [MulAut.inv_apply_self] at h
    · intro hu
      rw [← hcom₂] at hu ⊢
      exact CFSG.Quasithin.Asc81c.commSub_stable' (Subgroup.mem_zpowers y₂) hu
  have hy₂S₂ : y₂ ∈ stabSub Z₂ := by
    rw [mem_stabSub, ← hfix₂]
    intro u
    constructor
    · intro hu
      have h2 : y₂ u = u := by
        have h := (mem_fixV.mp hu) y₂ (Subgroup.mem_zpowers y₂)
        exact y₂.injective h
      rw [mem_fixV]
      intro m hm
      exact s168e3_cyc3_zpowers_fix h2 m hm
    · intro hu
      rw [mem_fixV] at hu ⊢
      intro m hm
      have hcomm : m * y₂ = y₂ * m := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
        exact (Commute.refl y₂).zpow_left k |>.eq
      calc m (y₂ u) = (m * y₂) u := by rw [← MulAut.mul_apply]
        _ = (y₂ * m) u := by rw [hcomm]
        _ = y₂ (m u) := by rw [MulAut.mul_apply]
        _ = y₂ u := by rw [hu m hm]
  have hy₂B : y₂ ∈ B := by
    rw [hB]
    exact ⟨⟨⟨hEA hy₂E, hy₂C⟩, hy₂S₁⟩, hy₂S₂⟩
  have hy₂cent : y₂ ∈ centSub Z₂ := by
    rw [mem_centSub, ← hfix₂]
    intro u hu
    rw [mem_fixV] at hu
    exact hu y₂ (Subgroup.mem_zpowers y₂)
  have hy₂K : y₂ ∈ K := by
    rw [hK]
    exact ⟨hy₂B, hy₂cent⟩
  have hKle : K ≤ Subgroup.zpowers y₂ := by
    intro k hk
    rw [hK] at hk
    obtain ⟨hkB, hkcent⟩ := hk
    obtain ⟨e₁, e₂, he₁, he₂, hk₁, hk₂⟩ := hcoord k hkB
    obtain ⟨e', e'₂, he', he'₂, hy₁, hy₂'⟩ := hcoord y₂ hy₂B
    have hyZ₁ : ∀ z ∈ Z₁, y₂ z ∈ Z₁ := fun z hz => (mem_stabSub.mp hy₂S₁ z).2 hz
    have hyfix₂ : ∀ z ∈ Z₂, y₂ z = z := by
      intro z hz
      rw [← hfix₂, mem_fixV] at hz
      exact hz y₂ (Subgroup.mem_zpowers y₂)
    have hkfix₂ : ∀ z ∈ Z₂, k z = z := fun z hz => (mem_centSub.mp hkcent) z hz
    have he'0 : e' ≠ 0 := by
      intro h0
      apply hy₂
      refine s168e3_cyc3_ext_of_eq_on hZtop (g := y₂) (h := 1) ?_ ?_
      · intro z hz
        rw [hy₁ z hz, h0, pow_zero, MulAut.one_apply]
      · intro z hz
        rw [hyfix₂ z hz, MulAut.one_apply]
    have hmem : ∀ m : ℕ, y₂ ^ m = k → k ∈ Subgroup.zpowers y₂ := by
      intro m hm
      rw [← hm]
      exact (Subgroup.zpowers y₂).pow_mem (Subgroup.mem_zpowers y₂) m
    rcases (by omega : e' = 1 ∨ e' = 2) with he'1 | he'2
    · have hy₁' : ∀ z ∈ Z₁, y₂ z = (x ^ 1) z := by
        intro z hz; rw [hy₁ z hz, he'1]
      have hp : x ^ (1 * e₁) = x ^ e₁ := by rw [Nat.one_mul]
      have hm : y₂ ^ e₁ = k :=
        s168e3_cyc3_pow_eq_of_coord (e := 1) (a := e₁) (m := e₁)
          hZtop hyZ₁ hy₁' hp hk₁ hyfix₂ hkfix₂
      exact hmem e₁ hm
    · have hy₁' : ∀ z ∈ Z₁, y₂ z = (x ^ 2) z := by
        intro z hz; rw [hy₁ z hz, he'2]
      rcases (by omega : e₁ = 0 ∨ e₁ = 1 ∨ e₁ = 2) with he₁0 | he₁1 | he₁2
      · have hk₁' : ∀ z ∈ Z₁, k z = (x ^ 0) z := by
          intro z hz; rw [hk₁ z hz, he₁0]
        have hp : x ^ (2 * 0) = x ^ 0 := by
          rw [show (2 : ℕ) * 0 = 0 by norm_num]
        have hm : y₂ ^ 0 = k :=
          s168e3_cyc3_pow_eq_of_coord (e := 2) (a := 0) (m := 0)
            hZtop hyZ₁ hy₁' hp hk₁' hyfix₂ hkfix₂
        exact hmem 0 hm
      · have hk₁' : ∀ z ∈ Z₁, k z = (x ^ 1) z := by
          intro z hz; rw [hk₁ z hz, he₁1]
        have hp : x ^ (2 * 2) = x ^ 1 := by
          rw [show (2 : ℕ) * 2 = 4 by norm_num,
            show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hx3, one_mul]
        have hm : y₂ ^ 2 = k :=
          s168e3_cyc3_pow_eq_of_coord (e := 2) (a := 1) (m := 2)
            hZtop hyZ₁ hy₁' hp hk₁' hyfix₂ hkfix₂
        exact hmem 2 hm
      · have hk₁' : ∀ z ∈ Z₁, k z = (x ^ 2) z := by
          intro z hz; rw [hk₁ z hz, he₁2]
        have hp : x ^ (2 * 1) = x ^ 2 := by
          rw [show (2 : ℕ) * 1 = 2 by norm_num]
        have hm : y₂ ^ 1 = k :=
          s168e3_cyc3_pow_eq_of_coord (e := 2) (a := 2) (m := 1)
            hZtop hyZ₁ hy₁' hp hk₁' hyfix₂ hkfix₂
        exact hmem 1 hm
  exact ⟨hpg, hcommB, le_antisymm hKle (Subgroup.zpowers_le.mpr hy₂K)⟩

theorem s168e3_cyc3_not_commute [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {E : Subgroup (MulAut W)}
    {x y₂ t : MulAut W} {Z₁ : Subgroup W} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hxE : x ∈ E) (hy₂E : y₂ ∈ E)
    (hfpf : ∀ w : W, x w = w → w = 1) (hinv : t * x * t⁻¹ = x⁻¹)
    (hcom₂ : commSub ⊤ (Subgroup.zpowers y₂) = Z₁) (hZ₁ : Nat.card ↥Z₁ = 4) :
    ⁅Subgroup.zpowers y₂, Subgroup.zpowers t⁆ ≠ ⊥ := by
  intro hbot
  have hx3 : x ^ 3 = 1 := hE3 x hxE
  have hy3 : y₂ ^ 3 = 1 := hE3 y₂ hy₂E
  have hxy : x * y₂ = y₂ * x := hEc x hxE y₂ hy₂E
  have hYodd : Odd (Nat.card ↥(Subgroup.zpowers y₂)) := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf y₂ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hy3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · rw [h]; decide
    · rw [h]; decide
  have hZbot : Z₁ ⊓ fixV (Subgroup.zpowers y₂) = ⊥ := by
    have h := CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' (Y := Subgroup.zpowers y₂) hW hYodd
    rw [inf_comm] at h
    rw [hcom₂] at h
    exact h
  have hxZ₁ : ∀ z ∈ Z₁, x z ∈ Z₁ := by
    intro z hz
    rw [← hcom₂] at hz ⊢
    exact s168e3_cyc3_x_stable_commSub hxy z hz
  have hyZ₁ : ∀ z ∈ Z₁, y₂ z ∈ Z₁ := by
    intro z hz
    rw [← hcom₂] at hz ⊢
    exact CFSG.Quasithin.Asc81c.commSub_stable' (Subgroup.mem_zpowers y₂) hz
  have hcommxy : ∀ z ∈ Z₁, y₂ (x z) = x (y₂ z) := by
    intro z hz
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hxy]
  obtain ⟨e, he, hye⟩ :=
    s16e_d5_schur_local hZ₁ hx3 hxZ₁ (fun z hz h => hfpf z h) hyZ₁ hcommxy
  have he0 : e ≠ 0 := by
    intro h0
    have hle : Z₁ ≤ fixV (Subgroup.zpowers y₂) := by
      intro z hz
      rw [mem_fixV]
      intro m hm
      have hzfix : y₂ z = z := by rw [hye z hz, h0, pow_zero, MulAut.one_apply]
      exact s168e3_cyc3_zpowers_fix hzfix m hm
    have hle' : Z₁ ≤ Z₁ ⊓ fixV (Subgroup.zpowers y₂) := le_inf le_rfl hle
    rw [hZbot] at hle'
    have hZb : Z₁ = ⊥ := le_bot_iff.mp hle'
    rw [hZb, Subgroup.card_bot] at hZ₁
    omega
  have htcomm : t * y₂ = y₂ * t := by
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
    exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_zpowers y₂))) t
      (Subgroup.mem_zpowers t)
  have htZ₁ : ∀ z ∈ Z₁, t z ∈ Z₁ := by
    have hmapY := s168e3_cyc3_map_zpowers_conj_eq htcomm
    have h := CFSG.Quasithin.Asc81c.commSub_map_conj (Subgroup.zpowers y₂) t
    rw [hmapY, hcom₂] at h
    intro z hz
    rw [h]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have htZ₁inv : ∀ z ∈ Z₁, t⁻¹ z ∈ Z₁ := by
    have hmapY : (Subgroup.zpowers y₂).map (MulAut.conj t⁻¹).toMonoidHom =
        Subgroup.zpowers y₂ := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change (MulAut.conj t⁻¹) y₂ = y₂
      rw [MulAut.conj_apply]
      calc t⁻¹ * y₂ * (t⁻¹)⁻¹ = t⁻¹ * y₂ * t := by rw [inv_inv]
        _ = t⁻¹ * (y₂ * t) := by rw [mul_assoc]
        _ = t⁻¹ * (t * y₂) := by rw [← htcomm]
        _ = y₂ := by group
    have h := CFSG.Quasithin.Asc81c.commSub_map_conj (Subgroup.zpowers y₂) t⁻¹
    rw [hmapY, hcom₂] at h
    intro z hz
    rw [h]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have htxe : t * x ^ e * t⁻¹ = (x ^ e)⁻¹ := by
    calc t * x ^ e * t⁻¹ = (MulAut.conj t) (x ^ e) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj t) x) ^ e := by rw [map_pow]
      _ = (x⁻¹) ^ e := by rw [MulAut.conj_apply, hinv]
      _ = (x ^ e)⁻¹ := by rw [inv_pow]
  have htxe' : t * x ^ e = (x ^ e)⁻¹ * t := by
    calc t * x ^ e = (t * x ^ e * t⁻¹) * t := by group
      _ = (x ^ e)⁻¹ * t := by rw [htxe]
  have key2 : ∀ u ∈ Z₁, t u = (x ^ (2 * e)) (t u) := by
    intro u hu
    have hu' : t u ∈ Z₁ := htZ₁ u hu
    have h1 : y₂ (t u) = (x ^ e) (t u) := hye (t u) hu'
    have h2 : y₂ (t u) = t (y₂ u) := by
      have h := congrArg (fun f : MulAut W => f u) htcomm
      rw [MulAut.mul_apply, MulAut.mul_apply] at h
      exact h.symm
    have h3 : t (y₂ u) = (x ^ e)⁻¹ (t u) := by
      rw [hye u hu]
      have h := congrArg (fun f : MulAut W => f u) htxe'
      rw [MulAut.mul_apply, MulAut.mul_apply] at h
      exact h
    have hkey : (x ^ e) (t u) = (x ^ e)⁻¹ (t u) := h1.symm.trans (h2.trans h3)
    have hL : (x ^ e) ((x ^ e) (t u)) = (x ^ (2 * e)) (t u) := by
      rw [← MulAut.mul_apply, ← pow_two, ← pow_mul, Nat.mul_comm]
    have hR : (x ^ e) ((x ^ e)⁻¹ (t u)) = t u := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    have h := congrArg (fun w => (x ^ e) w) hkey
    rw [hL, hR] at h
    exact h.symm
  have hfixall : ∀ u ∈ Z₁, u = (x ^ (2 * e)) u := by
    intro u hu
    have hu' : t⁻¹ u ∈ Z₁ := htZ₁inv u hu
    have h := key2 (t⁻¹ u) hu'
    rwa [MulAut.apply_inv_self] at h
  have hZle : Z₁ ≤ ⊥ := by
    intro u hu
    have h1 : u = (x ^ (2 * e)) u := hfixall u hu
    rcases (by omega : e = 1 ∨ e = 2) with he1 | he2
    · have hx2 : x ^ (2 * 1) = x ^ 2 := by
        rw [show (2 : ℕ) * 1 = 2 by norm_num]
      rw [he1, hx2] at h1
      exact s16e_d5_pow_fix hx3 (Z := Z₁) (fun z hz h => hfpf z h) (e := 2)
        (by norm_num) (by norm_num) u hu h1.symm
    · have hx4 : x ^ (2 * 2) = x := by
        rw [show (2 : ℕ) * 2 = 4 by norm_num,
          show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
      rw [he2, hx4] at h1
      exact s16e_d5_pow_fix hx3 (Z := Z₁) (fun z hz h => hfpf z h) (e := 1)
        (by norm_num) (by norm_num) u hu (by simpa using h1.symm)
  have hZb : Z₁ = ⊥ := le_bot_iff.mp hZle
  rw [hZb, Subgroup.card_bot] at hZ₁
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
