module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Diag

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Aut
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Core
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation
  slConjugation_matrix toGL_slConjugation)

namespace Item224KFactsProof

variable {K : Type} [Field K]

theorem autElliptic_of_inndiag [Finite K] [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))}
    (hE3 : ∀ α ∈ E, α ^ 3 = 1) (hE9 : Nat.card E = 9)
    (hdiag : ∀ α ∈ E, ∃ A : GL (Fin 3) K, α = slConjugation 3 K A)
    {x : SpecialLinearGroup (Fin 3) K} (hx3 : x ^ 3 = 1)
    (hxZ : x ∉ Subgroup.center (SpecialLinearGroup (Fin 3) K)) (hxE : ∀ α ∈ E, α x = x)
    {T : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hT : IsPGroup 2 T)
    (hTE : T ≤ Subgroup.centralizer (E : Set (MulAut (SpecialLinearGroup (Fin 3) K)))) :
    AutElliptic (SpecialLinearGroup (Fin 3) K) T := by
  have hω1 := ne_one_of_sq_add hω
  obtain ⟨g, hg⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_diagonalizing_of_commuting_cube_one ω
    hω hω1 (Subgroup.zpowers x)
    (fun z hz => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx3,
        _root_.one_zpow])
    (fun z hz w hw => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact zpow_mul_comm x k l)
  set φ : MulAut (SpecialLinearGroup (Fin 3) K) := MulAut.conj g with hφ
  set Φ := MulAut.congr φ with hΦ
  have hx' : ((φ x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun i => ((φ x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]
      exact hg x (Subgroup.mem_zpowers x) i j hij
  refine autElliptic_of_map_congr φ (autElliptic_of_diag hω (E := E.map Φ.toMonoidHom) ?_ ?_ ?_
    hx' ?_ ?_ ?_ (hT.map _) ?_)
  · rintro _ ⟨α, hα, rfl⟩
    change Φ α ^ 3 = 1
    rw [← map_pow, hE3 α hα, map_one]
  · rw [Subgroup.card_map_of_injective Φ.injective]
    exact hE9
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨A, rfl⟩ := hdiag α hα
    exact ⟨_, congr_conj_slConjugation g A⟩
  · rw [← map_pow, hx3, map_one]
  · intro h
    exact hxZ ((Item224KFactsProof.mem_center_iff_of_mulEquiv φ x).mp h)
  · exact (fixed_map_congr_iff φ E x).mpr hxE
  · rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨α, hα, rfl⟩
    change Φ α * Φ t = Φ t * Φ α
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hTE ht)) α hα]

theorem exists_cube_root_galoisField {n : ℕ} (hn : 0 < n) (he : Even n) :
    ∃ ω : GaloisField 2 n, ω ^ 2 + ω + 1 = 0 := by
  have h3 : 3 ∣ Nat.card (GaloisField 2 n)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 n hn.ne']
    obtain ⟨m, rfl⟩ := he
    have hmod : 2 ^ (m + m) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (by rw [hmod]))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 n)ˣ) 3 h3
  have hu3 : (u : GaloisField 2 n) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : GaloisField 2 n) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    norm_num at hu
  refine ⟨u, ?_⟩
  have h : ((u : GaloisField 2 n) - 1) * ((u : GaloisField 2 n) ^ 2 + u + 1) = 0 := by
    linear_combination hu3
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hu1)

end Item224KFactsProof

open Item224KFactsProof

end CFSG.RankThree.PartTwo.Sec21
