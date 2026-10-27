module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Input
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeOC

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree (gammaCore)

variable {X : Type} [Group X]

theorem inf_eq_of_maximal {N K Γ : Subgroup X} (hΓN : Γ ≤ N) (hΓK : Γ ≤ K) (hKN : ¬ K ≤ N)
    (hmax : ∀ H : Subgroup X, Γ < H → H ≤ K → H = K) : N ⊓ K = Γ := by
  refine le_antisymm ?_ (le_inf hΓN hΓK)
  by_contra h
  exact hKN ((hmax _ (lt_of_le_of_ne (le_inf hΓN hΓK) fun h' => h h'.ge)
    inf_le_right).symm.le.trans inf_le_left)

theorem eq_of_isPGroup_of_le {p : ℕ} {K Q R : Subgroup X} (hQK : Q ≤ K) (T : Sylow p ↥K)
    (hT : (T : Subgroup ↥K) = Q.subgroupOf K) (hR : IsPGroup p R) (hQR : Q ≤ R) (hRK : R ≤ K) :
    R = Q := by
  have h : R.subgroupOf K = (T : Subgroup ↥K) := T.is_maximal' hR.comap_subtype
    (hT.le.trans fun x hx => Subgroup.mem_subgroupOf.2 (hQR (Subgroup.mem_subgroupOf.1 hx)))
  rw [hT] at h
  simpa only [inf_of_le_left hRK, inf_of_le_left hQK] using Subgroup.subgroupOf_inj.1 h

theorem le_normalizer_of_inf_le [Finite X] {p : ℕ} {N K Q : Subgroup X} [K.Normal] (hQN : Q ≤ N)
    (hQK : Q ≤ K) (hQ : IsPGroup p Q)
    (hmax : ∀ R : Subgroup X, IsPGroup p R → Q ≤ R → R ≤ K → R = Q)
    (hNK : N ⊓ K ≤ Subgroup.normalizer (Q : Set X)) : N ≤ Subgroup.normalizer (Q : Set X) := by
  intro n hn
  have hQ'N : Q.map (MulAut.conj n).toMonoidHom ≤ N ⊓ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨N.mul_mem (N.mul_mem hn (hQN hx)) (N.inv_mem hn), ‹K.Normal›.conj_mem x (hQK hx) n⟩
  have hR := hmax _ (hQ.to_sup_of_normal_left' (hQ.map _) (hQ'N.trans hNK)) le_sup_left
    (sup_le hQK (hQ'N.trans inf_le_right))
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (Subgroup.eq_of_le_of_card_ge
    (le_sup_right.trans hR.le) (Subgroup.card_map_of_injective (MulAut.conj n).injective).ge)

theorem inf_eq_and_le_normalizer [Finite X] {N K : Subgroup X} [K.Normal]
    (hN : IsStronglyPEmbedded 3 N) (P : Sylow 3 X) (hPN : (P : Subgroup X) ≤ N)
    (hPK : (P : Subgroup X) ⊓ K ≠ ⊥) (T : Sylow 3 ↥K)
    (hT : (T : Subgroup ↥K) = ((P : Subgroup X) ⊓ K).subgroupOf K)
    (hmax : ∀ H : Subgroup X, gammaCore 3 1 K ((P : Subgroup X) ⊓ K) < H → H ≤ K → H = K)
    (hΓ : gammaCore 3 1 K ((P : Subgroup X) ⊓ K) =
      K ⊓ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X)) :
    N ⊓ K = K ⊓ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) ∧
      N ≤ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQN : (P : Subgroup X) ⊓ K ≤ N := inf_le_left.trans hPN
  have hΓN := CFSG.LocalAnalysis.UniquenessCase.UCK.gammaCore_le_of_isStronglyPEmbedded (A := K) hN
    P.isPGroup'.to_inf_left hQN
  have hKN := CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
  have hNK : N ⊓ K = K ⊓ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) := by
    rw [← hΓ]
    exact inf_eq_of_maximal hΓN (hΓ.le.trans inf_le_left) hKN hmax
  exact ⟨hNK, le_normalizer_of_inf_le hQN inf_le_right P.isPGroup'.to_inf_left
    (fun R hR hQR hRK => eq_of_isPGroup_of_le inf_le_right T hT hR hQR hRK)
    (hNK.le.trans inf_le_right)⟩

theorem commute_of_mem_pPrimeCore [Finite X] {p : ℕ} [Fact p.Prime] {N Q : Subgroup X}
    (hQN : Q ≤ N) (hQ : IsPGroup p Q) (hnorm : N ≤ Subgroup.normalizer (Q : Set X)) {y : ↥N}
    (hy : y ∈ CFSG.pPrimeCore p ↥N) {x : X} (hx : x ∈ Q) : (y : X) * x = x * y := by
  have hQn : (Q.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).2 hnorm
  have hcop : Nat.Coprime (Nat.card (CFSG.pPrimeCore p ↥N)) (Nat.card (Q.subgroupOf N)) := by
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv, hn]
    exact (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥N)).symm.pow_right n
  exact congrArg Subtype.val (Subgroup.commute_of_normal_of_disjoint _ _ inferInstance hQn
    (Subgroup.disjoint_of_coprime_natCard hcop) y ⟨x, hQN hx⟩ hy (Subgroup.mem_subgroupOf.2 hx))

theorem pow_index_mul_card_eq_one {N K : Subgroup X} [K.Normal] {y : X} (hy : y ∈ N) :
    y ^ (K.index * Nat.card ↥(N ⊓ K)) = 1 := by
  have hmem : y ^ K.index ∈ N ⊓ K := ⟨N.pow_mem hy _, K.pow_index_mem y⟩
  rw [pow_mul]
  exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, hmem⟩ : ↥(N ⊓ K))))

theorem centralizerHasPElementOutside_of_pow_eq_one {p : ℕ} (hp : p.Prime) {N : Subgroup X}
    (a b : ℕ) (h : ∀ y ∈ N, y ^ (2 ^ a * p ^ b) = 1) : CentralizerHasPElementOutside p N := by
  intro x y _ hy _ _ hyp hy2 hyq _
  exfalso
  rcases (Nat.Prime.dvd_mul hyp).1 (orderOf_dvd_of_pow_eq_one (h y hy)) with h2 | h3
  · exact hy2 ((Nat.prime_dvd_prime_iff_eq hyp Nat.prime_two).1 (hyp.dvd_of_dvd_pow h2))
  · exact hyq ((Nat.prime_dvd_prime_iff_eq hyp hp).1 (hyp.dvd_of_dvd_pow h3))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeOC
