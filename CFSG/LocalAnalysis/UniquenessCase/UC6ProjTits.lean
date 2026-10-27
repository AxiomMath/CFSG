module

public import CFSG.LocalAnalysis.UniquenessCase.UC6ProjFive
public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsAut
public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.ProjTits

open Subgroup

theorem exists_basis_of_card_25 {Q : Type*} [Group Q] [Finite Q] {R : Subgroup Q} (hR : Nat.card R = 25)
    (h5 : ∀ x ∈ R, x ^ 5 = 1) :
    ∃ a ∈ R, ∃ b ∈ R, ∀ s t : ℕ, s < 5 → t < 5 → (s ≠ 0 ∨ t ≠ 0) → a ^ s * b ^ t ≠ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨a, haR, ha1⟩ := UC6.exists_ne_one_of_card_eq_25 hR
  have hao : orderOf a = 5 := orderOf_eq_prime (h5 a haR) ha1
  obtain ⟨b, hbR, hba⟩ : ∃ b ∈ R, b ∉ zpowers a := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show R ≤ zpowers a from fun x hx => h x hx)
    rw [hR, Nat.card_zpowers, hao] at hle
    norm_num at hle
  refine ⟨a, haR, b, hbR, fun s t hs ht hst h => ?_⟩
  by_cases ht0 : t = 0
  · subst ht0
    rw [pow_zero, mul_one] at h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hao] at hdvd
    omega
  · have hbt : b ^ t ∈ zpowers a := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem (pow_mem (mem_zpowers a) s)
    have ht1 : t * t ^ 3 % 5 = 1 := by interval_cases t <;> simp_all
    have hb : (b ^ t) ^ (t ^ 3) = b := by
      rw [← pow_mul, pow_eq_pow_mod _ (h5 b hbR), ht1, pow_one]
    exact hba (hb ▸ pow_mem hbt _)

end CFSG.LocalAnalysis.UniquenessCase.UC6.ProjTits

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.Sporadic.Schreier.Tits (titsD)

section Tits


theorem kProjRep_Tits (J : Type) [Group J] (hq : CFSG.Open.IsQuasisimple J) (N : Subgroup J) [N.Normal]
    (hN : N ≤ center J) (hT : CFSG.Blueprint.LieModel (J ⧸ N) .Tits 0 2 1) (q : ℕ) (hqp : q.Prime)
    (hq5 : q ≠ 5) (d : ℕ) (hd : d ≤ 6)
    (f : J →* (Matrix.GeneralLinearGroup (Fin d) (ZMod q)) ⧸
      center (Matrix.GeneralLinearGroup (Fin d) (ZMod q))) : f = 1 := by
  obtain ⟨e⟩ := TitsAut.lieModel_equiv hT
  haveI : Fact q.Prime := ⟨hqp⟩
  have h5 : (5 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((5 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod q) q] at h'
    exact hq5 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_five).1 h')
  have hZ : center (J ⧸ N) = ⊥ := by
    obtain ⟨hs, x, y, hxy⟩ := TitsAut.simple_of_lieModel hT
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (J ⧸ N)) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top x) y).symm hxy
  obtain ⟨-, hRcard, -, -, -, t, ht, ht3, -, hline⟩ := TitsCore.localData_L
  have hR25 : Nat.card TitsCore.Rt = 25 := by rw [hRcard]; norm_num
  have htN : t ∈ normalizer (TitsCore.Rt : Set (Equiv.Perm (Fin 1755))) := (Subgroup.mem_inf.1 ht).1
  have h5R : ∀ x ∈ TitsCore.Rt, x ^ 5 = 1 := fun x hx =>
    pow_five_of_torus hR25 htN (fun Y₀ hY hc => by simpa using hline 1 one_pos (by norm_num) Y₀ hY hc) hx
  obtain ⟨a, haR, b, hbR, hab⟩ := ProjTits.exists_basis_of_card_25 hR25 h5R
  have hLD : TitsCore.Lt ≤ titsD :=
    TitsCore.pairG_eq ▸ CFSG.StandardType.TitsOvergroup.pairSide_le_pairG 0
  have htD : t ^ 3 ∈ titsD := pow_mem (hLD (Subgroup.mem_inf.1 ht).2) 3
  let a' : titsD := ⟨a, TitsCore.R_le_D haR⟩
  let b' : titsD := ⟨b, TitsCore.R_le_D hbR⟩
  let ν' : titsD := ⟨t ^ 3, htD⟩
  refine projRep_eq_one_of_five J hq N hN hZ (a := e.symm a') (b := e.symm b') (ν := e.symm ν') ?_ ?_ ?_ ?_ ?_
    ?_ h5 (by omega) f
  · rw [← map_mul, ← map_mul]
    exact congrArg e.symm (Subtype.ext (comm_of_card_eq_25 hR25 haR hbR))
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    exact congrArg e.symm (Subtype.ext (ht3 a haR))
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    exact congrArg e.symm (Subtype.ext (ht3 b hbR))
  · rw [← map_pow, MulEquiv.map_eq_one_iff]
    exact Subtype.ext (h5R a haR)
  · rw [← map_pow, MulEquiv.map_eq_one_iff]
    exact Subtype.ext (h5R b hbR)
  · intro s u hs hu hsu h
    rw [← map_pow, ← map_pow, ← map_mul, MulEquiv.map_eq_one_iff] at h
    exact hab s u hs hu hsu (congrArg Subtype.val h)

end Tits

end CFSG.LocalAnalysis.UniquenessCase.UCK
