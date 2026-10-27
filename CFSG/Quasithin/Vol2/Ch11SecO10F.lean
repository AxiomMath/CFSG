module

public import CFSG.Quasithin.Vol2.Ch11SecO10D
public import CFSG.Quasithin.Vol2.Ch11SecO10E
public import CFSG.Quasithin.Vol2.Ch11SecO10C

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Quasithin Matrix
open Ch11.SecA (stabW IsFlagW)

variable {W : Type*} [CommGroup W] [Finite W]

theorem le_normalizer_inf_centralizer {Y : Type*} [Group Y] {P B : Subgroup Y}
    (hPB : P ≤ Subgroup.normalizer (B : Set Y)) :
    P ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (B : Set Y) : Subgroup Y) : Set Y) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ x ∈ P, x ∈ Subgroup.normalizer (B : Set Y) → ∀ h,
      h ∈ P ⊓ Subgroup.centralizer (B : Set Y) → x * h * x⁻¹ ∈ P ⊓ Subgroup.centralizer B := by
    intro x hx hxB h hh
    refine ⟨P.mul_mem (P.mul_mem hx hh.1) (P.inv_mem hx), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro b hb
    have hb' : x⁻¹ * b * x⁻¹⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxB) b).mp hb
    have hc := Subgroup.mem_centralizer_iff.mp hh.2 _ hb'
    rw [inv_inv] at hc
    calc b * (x * h * x⁻¹) = x * ((x⁻¹ * b * x) * h) * x⁻¹ := by group
      _ = x * (h * (x⁻¹ * b * x)) * x⁻¹ := by rw [hc]
      _ = x * h * x⁻¹ * b := by group
  intro h
  refine ⟨key p hp (hPB hp) h, fun h' => ?_⟩
  have := key p⁻¹ (P.inv_mem hp) (Subgroup.inv_mem _ (hPB hp)) _ h'
  simpa [mul_assoc] using this

theorem le_normalizer_inf_centralizer' {Y : Type*} [Group Y] (P B : Subgroup Y) :
    B ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (B : Set Y) : Subgroup Y) : Set Y) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hc := Subgroup.mem_centralizer_iff.mp hh.2 b hb
    have e : b * h * b⁻¹ = h := by rw [hc, mul_inv_cancel_right]
    rwa [e]
  · intro hh
    have hc := Subgroup.mem_centralizer_iff.mp hh.2 b hb
    have e : b * h * b⁻¹ = h := by
      calc b * h * b⁻¹ = b⁻¹ * (b * (b * h * b⁻¹)) := by group
        _ = b⁻¹ * ((b * h * b⁻¹) * b) := by rw [hc]
        _ = h := by group
    rwa [e] at hh

theorem levi_ident (hW : ∀ w : W, w ^ 2 = 1) {H P B : Subgroup (MulAut W)} {n : ℕ}
    (hn : 2 ≤ n) (hN : NatFactsW H P n) (hP : QuasithinUnique.IsSylowTwoOf P H) (hBH : B ≤ H)
    (hPB : P ≤ Subgroup.normalizer (B : Set (MulAut W))) {F : Type*} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2 ^ n)
    (hSL : pCoreOf 2 B = ⊥ → Nonempty (↥B ≃* SpecialLinearGroup (Fin 2) F)) :
    ∃ d : ℕ, (d = 1 ∨ d = 2 ∨ d = 3) ∧
      ∃ U : Subgroup W, IsFlagW H P ⊥ (2 ^ n) d U ∧ U ≠ ⊤ ∧ B ≤ stabW U := by
  obtain ⟨hpow, hcard, hW1, ⟨Z₀, hZP, hZc, hZq⟩, hPq⟩ := hN
  have hq : 2 ≤ 2 ^ n := le_self_pow₀ (by norm_num) (by omega)
  have key : ∀ Q : Subgroup (MulAut W), IsPGroup 2 Q → Q ≠ ⊥ → Q ≤ H →
      P ≤ Subgroup.normalizer (Q : Set (MulAut W)) →
      B ≤ Subgroup.normalizer (Q : Set (MulAut W)) →
      ∃ d : ℕ, (d = 1 ∨ d = 2 ∨ d = 3) ∧
        ∃ U : Subgroup W, IsFlagW H P ⊥ (2 ^ n) d U ∧ U ≠ ⊤ ∧ B ≤ stabW U := by
    intro Q hQ hQ1 hQH hPQ hBQ
    obtain ⟨d, hd, hflag⟩ := exists_isFlagW_fixW hW hW1 hq hpow hcard hQ hQ1 hQH hPQ
    exact ⟨d, hd, fixW Q, hflag, fixW_ne_top hQ1, fun b hb => mem_stabW_fixW (hBQ hb)⟩
  by_cases h1 : pCoreOf 2 B = ⊥
  · by_cases h2 : P ⊓ Subgroup.centralizer (B : Set (MulAut W)) = ⊥
    · obtain ⟨θ⟩ := hSL h1
      exact (false_of_sl2 (by omega) hF hP hBH hPB θ h2 hZP hZc hZq hPq).elim
    · exact key _ hP.2.1.to_inf_left h2 (inf_le_left.trans hP.1)
        (le_normalizer_inf_centralizer hPB) (le_normalizer_inf_centralizer' P B)
  · exact key _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B) h1
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 B).trans hBH)
      (hPB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B)

end CFSG.Quasithin.Vol2.Ch11.O10
