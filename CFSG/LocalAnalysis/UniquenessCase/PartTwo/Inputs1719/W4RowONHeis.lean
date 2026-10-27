module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def IsHeisCenter7 (z : G) : Prop :=
  ∃ x y : G, HeisCfg 7 1 (fun _ => x) (fun _ => y) z ∧ y ^ 7 = 1

theorem IsHeisCenter7.conj {z : G} (h : IsHeisCenter7 z) (g : G) :
    IsHeisCenter7 (g * z * g⁻¹) := by
  obtain ⟨x, y, hc, hy⟩ := h
  have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hfz : (MulAut.conj g).toMonoidHom z ≠ 1 := fun h0 =>
    hc.z1 (hf (by simpa using h0))
  have h' : IsHeisCenter7 ((MulAut.conj g).toMonoidHom z) :=
    ⟨(MulAut.conj g).toMonoidHom x, (MulAut.conj g).toMonoidHom y,
      HeisCfg.map _ hc hfz, by rw [← map_pow, hy, map_one]⟩
  simpa [MulAut.conj_apply] using h'

theorem IsHeisCenter7.pow {z : G} (h : IsHeisCenter7 z) {k : ℕ} (hk : ¬ 7 ∣ k) :
    IsHeisCenter7 (z ^ k) := by
  obtain ⟨x, y, hc, hy⟩ := h
  have hord : orderOf z = 7 := by
    rcases (Nat.dvd_prime Nat.prime_seven).mp (orderOf_dvd_of_pow_eq_one hc.zp) with h | h
    · rw [orderOf_eq_one_iff] at h
      exact absurd h hc.z1
    · exact h
  have hzk : z ^ k ≠ 1 := by
    intro h0
    exact hk (hord ▸ orderOf_dvd_of_pow_eq_one h0)
  have hyx : ∀ n : ℕ, (y ^ n)⁻¹ * x * y ^ n = x * z ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hzy : z * y ^ n = y ^ n * z :=
        (Commute.pow_left (show Commute y z from hc.zy 0) n).symm
      calc (y ^ (n + 1))⁻¹ * x * y ^ (n + 1)
          = (y ^ n)⁻¹ * (y⁻¹ * x * y) * y ^ n := by group
        _ = (y ^ n)⁻¹ * (x * z) * y ^ n := by rw [hc.yx 0]
        _ = (y ^ n)⁻¹ * x * (z * y ^ n) := by group
        _ = (y ^ n)⁻¹ * x * (y ^ n * z) := by rw [hzy]
        _ = ((y ^ n)⁻¹ * x * y ^ n) * z := by group
        _ = (x * z ^ n) * z := by rw [ih]
        _ = x * z ^ (n + 1) := by rw [pow_succ]; group
  refine ⟨x, y ^ k, ?_, ?_⟩
  · refine ⟨fun _ => hc.xp 0, ?_, fun _ => Commute.pow_right (show Commute x z from hc.zx 0) k,
      fun _ => Commute.pow_pow (show Commute y z from hc.zy 0) k k, fun _ => hyx k,
      fun _ _ => hc.xx 0 0,
      fun i j hij => absurd (Subsingleton.elim i j) hij,
      fun i j hij => absurd (Subsingleton.elim i j) hij, hzk⟩
    rw [← pow_mul, mul_comm k 7, pow_mul, hc.zp, one_pow]
  · rw [← pow_mul, mul_comm k 7, pow_mul, hy, one_pow]

theorem IsHeisCenter7.map {H : Type*} [Group H] {z : G} (h : IsHeisCenter7 z) (f : G →* H)
    (hf : Function.Injective f) : IsHeisCenter7 (f z) := by
  obtain ⟨x, y, hc, hy⟩ := h
  have hfz : f z ≠ 1 := fun h0 => hc.z1 (hf (by simpa using h0))
  exact ⟨f x, f y, HeisCfg.map f hc hfz, by rw [← map_pow, hy, map_one]⟩

theorem isHeisCenter7_of_commutator {a b : G} (ha : a ^ 7 = 1) (hb : b ^ 7 = 1)
    (h1 : ⁅a, b⁆ ≠ 1) (hca : Commute ⁅a, b⁆ a) (hcb : Commute ⁅a, b⁆ b) :
    IsHeisCenter7 ⁅a, b⁆ := by
  set c : G := ⁅a, b⁆ with hcdef
  have hab : a * b = c * b * a := by
    rw [hcdef, commutatorElement_def]
    group
  have hcab : c * b * a = b * a * c := by
    calc c * b * a = b * (c * a) := by rw [hcb.eq]; group
      _ = b * (a * c) := by rw [hca.eq]
      _ = b * a * c := by group
  have hyx : b⁻¹ * a * b = a * c := by
    calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
      _ = b⁻¹ * (c * b * a) := by rw [hab]
      _ = a * c := by rw [hcab]; group
  have hconj : (b⁻¹ * a * b) ^ 7 = 1 := by
    rw [show b⁻¹ * a * b = b⁻¹ * a * (b⁻¹)⁻¹ by group, conj_pow, ha]
    simp
  have hc7 : c ^ 7 = 1 := by
    have h2 : (a * c) ^ 7 = 1 := by
      rw [← hyx]
      exact hconj
    rw [hca.symm.mul_pow, ha, one_mul] at h2
    exact h2
  exact ⟨a, b, ⟨fun _ => ha, hc7, fun _ => hca.eq.symm, fun _ => hcb.eq.symm, fun _ => hyx,
    fun _ _ => rfl, fun i j hij => absurd (Subsingleton.elim i j) hij,
    fun i j hij => absurd (Subsingleton.elim i j) hij, h1⟩, hb⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
