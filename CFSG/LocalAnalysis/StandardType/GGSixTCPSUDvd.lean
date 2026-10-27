module

public import CFSG.LocalAnalysis.StandardType.GGSixTCBlockField
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUBlock

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section SplitBlock

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [CharP F 2]

theorem blockDegree_eq_one_of_pow_eq_pow {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card Fˣ)
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hpow : ∀ s ∈ S, ∃ b : F, (s : Matrix ι ι F) ^ p = Matrix.scalar ι (b ^ p)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    blockDegree (Algebra.adjoin F (Units.val '' S)) e = 1 := by
  obtain ⟨K, hKf, hKa, -, π, hπs, -, hπd⟩ := exists_blockField hS hodd he
  let : Field K := hKf
  let : Algebra F K := hKa
  have key : ∀ (x : Matrix ι ι F) (hx : x ∈ Algebra.adjoin F (Units.val '' S)),
      ∃ c : F, π (⟨x, hx⟩ : Algebra.adjoin F (Units.val '' S)) = algebraMap F K c := by
    intro x hx
    refine Algebra.adjoin_induction
      (p := fun x hx => ∃ c : F,
        π (⟨x, hx⟩ : Algebra.adjoin F (Units.val '' S)) = algebraMap F K c) ?_ ?_ ?_ ?_ hx
    ·
      rintro x ⟨s, hs, rfl⟩
      obtain ⟨b, hb⟩ := hpow s hs
      let y : Algebra.adjoin F (Units.val '' S) :=
        ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
      have hyp : y ^ p = algebraMap F (Algebra.adjoin F (Units.val '' S)) (b ^ p) := by
        apply Subtype.ext
        change (s : Matrix ι ι F) ^ p = algebraMap F (Matrix ι ι F) (b ^ p)
        exact hb
      have hπy : π y ^ p = algebraMap F K b ^ p := by
        rw [← map_pow, hyp, AlgHom.commutes, map_pow]
      obtain ⟨c, hc⟩ := RingHom.mem_range.mp (mem_range_algebraMap_of_pow_eq_pow hp hpF hπy)
      exact ⟨c, hc.symm⟩
    · intro r
      exact ⟨r, π.commutes r⟩
    · rintro x y hx hy ⟨c1, h1⟩ ⟨c2, h2⟩
      refine ⟨c1 + c2, ?_⟩
      change π ((⟨x, hx⟩ : Algebra.adjoin F (Units.val '' S)) + ⟨y, hy⟩) =
        algebraMap F K (c1 + c2)
      rw [map_add, h1, h2, map_add]
    · rintro x y hx hy ⟨c1, h1⟩ ⟨c2, h2⟩
      refine ⟨c1 * c2, ?_⟩
      change π ((⟨x, hx⟩ : Algebra.adjoin F (Units.val '' S)) * ⟨y, hy⟩) =
        algebraMap F K (c1 * c2)
      rw [map_mul, h1, h2, map_mul]
  have hK1 : Module.finrank F K = 1 := by
    rw [finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero]
    intro w
    obtain ⟨a, rfl⟩ := hπs w
    obtain ⟨c, hc⟩ := key a.1 a.2
    exact ⟨c, by rw [Algebra.smul_def, mul_one]; exact hc.symm⟩
  rw [← hπd]
  exact hK1

end SplitBlock

section DvdCase

variable {X : Type} [Group X] {n g p : ℕ} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}
  {S : Set (GL (Fin n) (PSUF g))} {ε e : Matrix (Fin n) (Fin n) (PSUF g)}

theorem PSUBlock.false_of_dvd [Finite X] (hH : PSULiftHyp n g ψ p B) (hb : PSUBlock ψ B S ε e)
    (hpq : p ∣ 2 ^ (g + 1) + 1)
    (hd : 2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e) : False := by
  classical
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  have hpF : p ∣ Nat.card (PSUF g)ˣ := by
    rw [Nat.card_units, card_PSUF]
    have h : (2 ^ (g + 1)) ^ 2 - 1 = (2 ^ (g + 1) + 1) * (2 ^ (g + 1) - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (2 ^ (g + 1)) 1
      rw [pow_two]
      simpa using this
    rw [h]
    exact Dvd.dvd.mul_right hpq _
  by_cases hall : ∀ s ∈ S, ∃ b : PSUF g,
      (s : Matrix (Fin n) (Fin n) (PSUF g)) ^ p = Matrix.scalar (Fin n) (b ^ p)
  · have h1 := blockDegree_eq_one_of_pow_eq_pow hH.prime hpF (hb.S_comm hH) (hb.S_odd hH) hall
      hb.e_prim
    omega
  · push Not at hall
    obtain ⟨s, hs, hno⟩ := hall
    obtain ⟨-, c, -, hsc⟩ := hH.psuE_pow_scalar_odd (hb.subE s hs)
    refine hH.false_of_not_pow hpq (hb.subE s hs) hsc ?_
    intro b hbc
    exact hno b (by rw [hbc]; exact hsc)

end DvdCase

end CFSG.StandardType.TableCRes
