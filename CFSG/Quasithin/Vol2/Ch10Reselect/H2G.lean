module

public import CFSG.Quasithin.Vol2.Ch10Reselect.H2GA
public import CFSG.Quasithin.Vol2.Ch10Reselect.H2GB
public import CFSG.Quasithin.Vol2.Ch10Reselect.H2GC
public import CFSG.Quasithin.Vol2.Ch10Reselect.ScalarPow

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

theorem hH2_of (hAut : AutSL2Exists)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) (hA : Concl326A T L I) [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hL3 : ∀ k ∈ fsuM T L, (∀ l ∈ fsuL0 T L,
        ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) →
      k ∈ Subgroup.centralizer (fsuVM T L I : Set G))
    (M : RModel T L I K) (γ : ↥(fsuML T L)) (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (B : GL (Fin 2) K) (hφ : actML M γ = phi K g 1 B) :
    ∃ (k : ℕ) (c : K), (B : Matrix (Fin 2) (Fin 2) K) ^ (2 ^ k) = Matrix.scalar (Fin 2) c := by
  classical
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp (not_le_normalizer_of_lt hlt)
  obtain ⟨z, hz, σ, B₂, h1, h2⟩ :=
    exists_corrector hAut h37 h38 hfsu hlt hA hK M ht htn (γ := (γ : G)) γ.2 hφ
  obtain ⟨hzm, hBm⟩ := pow_eq_one_of_corrector h37 h38 hfsu hlt hA hL3 M ht htn hz h1 h2
  refine exists_two_pow_scalar_of_pow_eq_one B (orderOf_pos σ) hBm ?_
  intro r hr hr2 hrm hrSL
  haveI : Fact r.Prime := ⟨hr⟩
  exact false_of_odd_prime_dvd h37 h38 hfsu hlt hA M ht htn hz h2 hzm hr2 hrm
    (hrSL.trans (card_SL_dvd_card_L M))

end CFSG.Quasithin.Vol2.Ch10Reselect
