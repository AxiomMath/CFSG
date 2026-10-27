module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Skeleton
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L3Group
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Outer
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411J1
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem not_dvd_fifteen_of_ppd {n r : ℕ} (hn : Odd n) (hr : r.Prime)
    (hr3 : r ∣ 2 ^ (3 * n) - 1) (hrk : ∀ k : ℕ, 0 < k → k < 3 * n → ¬ r ∣ 2 ^ k - 1) :
    ¬ r ∣ 15 := by
  intro h15
  have hn1 : 1 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  have hr15 : r = 3 ∨ r = 5 := by
    have h : r ∣ 3 * 5 := by norm_num; exact h15
    rcases (Nat.Prime.dvd_mul hr).mp h with h3 | h5
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h5)
  rcases hr15 with rfl | rfl
  · exact hrk 2 (by norm_num) (by omega) (by norm_num)
  · by_cases hn3 : n = 1
    · subst hn3
      norm_num at hr3
    · have : 3 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
      exact hrk 4 (by norm_num) (by omega) (by norm_num)

theorem noSmall1411_of_L3graph (h : Hyp1411 X L S) {n : ℕ} (hn : Odd n)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)))
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    NoSmall1411 X L S := by
  obtain ⟨e⟩ := hL
  intro I hIn hI hLI t htS htQ htt
  by_contra hle
  push Not at hle
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  set α : MulAut ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) :=
    e.symm.trans (ψ.trans e) with hα
  have hψ2 : ψ * ψ = 1 := by
    rw [hψ, ← map_mul, ← map_mul, htt, map_one, map_one]
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun x => ?_
    have := congrArg (fun f : MulAut ↥(L.map π) => e (f (e.symm x))) hψ2
    simpa [hα] using this
  have hinner : ∀ g, α ≠ MulAut.conj g := by
    intro g hg
    obtain ⟨y, hyL, hy⟩ := not_inner_of_inf_eq_bot_of_hyp1411 h hSL htS htQ
      ((e.symm g : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) (e.symm g).2
    apply hy
    have h1 := congrArg (fun f : MulAut ↥(CFSG.Assembly.RankThreeEven.projSL 3
      (GaloisField 2 n)) => e.symm (f (e ⟨y, hyL⟩))) hg
    simp only [hα, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
      map_mul, map_inv] at h1
    have h2 := congrArg Subtype.val h1
    rw [hψ, MulAut.conjNormal_apply] at h2
    rw [h2]
    rfl
  obtain ⟨r, x, hr, hr3, hrk, hxr, hαx⟩ := exists_inverted_ppd_projSL3_odd hn α hα2 hinner
  have hsimp : IsSimpleGroup ↥(L.map π) := by
    have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 n)
    exact e.isSimpleGroup
  have hbot := map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ (3 * n) := dvd_pow_self 2 (by obtain ⟨k, rfl⟩ := hn; omega)
    have h2 : 1 ≤ 2 ^ (3 * n) := Nat.one_le_two_pow
    omega
  have hdvd_ord : r ∣ orderOf (α x * x⁻¹) := by
    have hx2 : α x * x⁻¹ = (x ^ 2)⁻¹ := by rw [hαx, pow_two, mul_inv_rev]
    rw [hx2, orderOf_inv, Nat.Coprime.orderOf_pow (by
      rw [hxr]; exact (Nat.coprime_primes hr Nat.prime_two).mpr hr2), hxr]
  have hord : orderOf (α x * x⁻¹) = orderOf (ψ (e.symm x) * (e.symm x)⁻¹) := by
    rw [← MulEquiv.orderOf_eq e, map_mul, map_inv]
    simp [hα]
  obtain ⟨ℓ, -, hℓ⟩ := (e.symm x).2
  have hu : t ∈ normalizer (I : Set X) := by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top t
  have hv : ℓ * t⁻¹ * ℓ⁻¹ ∈ normalizer (I : Set X) := by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have hvv : ℓ * t⁻¹ * ℓ⁻¹ * (ℓ * t⁻¹ * ℓ⁻¹) = 1 := by
    rw [inv_eq_of_mul_eq_one_right htt]
    calc ℓ * t * ℓ⁻¹ * (ℓ * t * ℓ⁻¹) = ℓ * (t * t) * ℓ⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hvb : (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 4 := by
    rw [relIndex_centralizer_conj hIn, inv_eq_of_mul_eq_one_right htt]
    exact hle
  obtain ⟨N, -, hpow, h15⟩ := exists_pow_mem_centralizer_odd_dvd_15 hI hu hv htt hvv hle hvb
  have himg : π (t * (ℓ * t⁻¹ * ℓ⁻¹)) =
      ((ψ (e.symm x) * (e.symm x)⁻¹ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ]
    simp only [map_mul, map_inv]
    group
  have h1 : (ψ (e.symm x) * (e.symm x)⁻¹) ^ (2 * N) = 1 := by
    apply Subtype.ext
    have hmem : ((((ψ (e.symm x) * (e.symm x)⁻¹) ^ (2 * N) : ↥(L.map π))) :
        X ⧸ CFSG.pPrimeCore 3 X) ∈ (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, hpow, ?_⟩, Subtype.mem _⟩
      rw [map_pow, himg, Subgroup.coe_pow]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd : r ∣ 2 * N := (hdvd_ord.trans (hord ▸ dvd_refl _)).trans
    (orderOf_dvd_of_pow_eq_one h1)
  have hodd : Odd r := hr.odd_of_ne_two hr2
  have hdvdN : r ∣ N := Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd) hdvd
  exact not_dvd_fifteen_of_ppd hn hr hr3 hrk (h15 r hodd hdvdN)

theorem asc82Item1411_L3graph (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S) {n : ℕ} (hn : Odd n)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
      Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)))
    (hS : Nat.card (S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = 2)
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  have hL' : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) := by
    rcases hL with he | he
    · obtain ⟨e⟩ := he
      exact ⟨e.trans (slThreeEquivProjSL hn)⟩
    · exact he
  exact asc82Item1411_of_noSmall h
    (fun _ hAS _ => (relIndex_pCore_le_card_map_of_hyp1411 h hAS).trans hS.le)
    (noSmall1411_of_L3graph h hn hL' hSL)

end CFSG.RankThree.PartTwo.Sec20
