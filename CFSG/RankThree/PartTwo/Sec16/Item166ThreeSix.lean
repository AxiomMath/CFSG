module

public import CFSG.RankThree.PartTwo.Sec16.Item166ThreePerp
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Three

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_factorization_le {p : ℕ} [Fact p.Prime] {S P R P' : Subgroup G}
    (hSP : S ≤ P) (hS : IsPGroup p S) (hSyl : ¬ p ∣ S.relIndex P)
    (hRP' : R ≤ P') (hR : IsPGroup p R)
    (hv : (Nat.card P').factorization p ≤ (Nat.card P).factorization p) :
    Nat.card R ≤ Nat.card S := by
  have hp : p.Prime := Fact.out
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hrelpos : S.relIndex P ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := S) (K := P)
    rw [h0, zero_mul] at h
    exact hPpos.ne' h.symm
  have hcardP : Nat.card P = S.relIndex P * Nat.card S := by
    rw [← Subgroup.relIndex_mul_card (H := S) (K := P), inf_eq_left.mpr hSP]
  have hfac : (Nat.card P).factorization p = (Nat.card S).factorization p := by
    rw [hcardP, Nat.factorization_mul hrelpos hSpos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hSyl]
  obtain ⟨a, ha⟩ := hS.exists_card_eq
  obtain ⟨b, hb⟩ := hR.exists_card_eq
  have hfacS : (Nat.card S).factorization p = a := by
    rw [ha, Nat.factorization_pow_self hp]
  have hfacR : (Nat.card R).factorization p = b := by
    rw [hb, Nat.factorization_pow_self hp]
  have hb_le_a : b ≤ a := by
    rw [← hfacR, ← hfacS, ← hfac]
    calc (Nat.card R).factorization p
        ≤ (Nat.card P').factorization p :=
          ((Nat.factorization_le_iff_dvd hRpos.ne'
            (Nat.card_pos (α := P')).ne').mpr (Subgroup.card_dvd_of_le hRP')) p
      _ ≤ (Nat.card P).factorization p := hv
  rw [hb, ha]
  exact pow_le_pow_right' hp.one_le hb_le_a

theorem le_perpOf_of_le_of_isPGroup {Z E Q T : Subgroup G} (hQ : IsPGroup 2 Q)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G)) (hTZ : T ≤ Z)
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) (hTQ : T ≤ Q) : T ≤ perpOf Z E := by
  have hN2 : IsPGroup 2 ↥(E ⊓ Q) := hQ.to_inf_right
  have hnorm : E ≤ Subgroup.normalizer ((E ⊓ Q : Subgroup G) : Set G) := by
    rw [inf_comm]
    exact (le_inf hEQ Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcore : E ⊓ Q ≤ CFSG.Open.pCoreOf 2 E :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm hN2
  intro t ht
  refine mem_perpOf_iff.mpr ⟨hTZ ht, hTE ht, ?_⟩
  intro e he
  have htQ : t ∈ Q := hTQ ht
  have hcommE : t * e * t⁻¹ * e⁻¹ ∈ E := by
    have h1 : t * e * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hTE ht) e).mp he
    exact E.mul_mem h1 (E.inv_mem he)
  have hcommQ : t * e * t⁻¹ * e⁻¹ ∈ Q := by
    have h2 : e * t * e⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hEQ he) t).mp htQ
    have h3 : (e * t * e⁻¹)⁻¹ ∈ Q := Q.inv_mem h2
    have heq : t * e * t⁻¹ * e⁻¹ = t * (e * t * e⁻¹)⁻¹ := by group
    rw [heq]
    exact Q.mul_mem htQ h3
  exact hcore ⟨hcommE, hcommQ⟩

theorem perpOf_inf_le (Z Z' E : Subgroup G) : perpOf Z E ⊓ Z' ≤ perpOf Z' E := by
  intro z hz
  obtain ⟨-, hzE, hzc⟩ := mem_perpOf_iff.mp hz.1
  exact mem_perpOf_iff.mpr ⟨hz.2, hzE, hzc⟩

theorem perpOf_le_normalizer (Z E : Subgroup G) :
    perpOf Z E ≤ Subgroup.normalizer (E : Set G) := fun _ hz =>
  (mem_perpOf_iff.mp hz).2.1

theorem exists_sylow_perpOf {A Z E : Subgroup G} (hA : IsPGroup 3 A)
    (hZ3 : ¬ 3 ∣ Nat.card Z) (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) :
    ∃ S : Subgroup G, S ≤ perpOf Z E ∧ IsPGroup 2 S ∧ ¬ 2 ∣ S.relIndex (perpOf Z E) ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
  have hAnorm : A ≤ Subgroup.normalizer (perpOf Z E : Set G) := fun a ha =>
    mem_normalizer_perpOf (hAZ ha) (hAE ha)
  have hcop : Nat.Coprime 3 (Nat.card (perpOf Z E)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le (perpOf_le Z E))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3)
  obtain ⟨P, hAP⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow
    3 2 Nat.prime_three Nat.prime_two A (perpOf Z E) hA hAnorm hcop
  have htop : (⊤ : Subgroup ↥(perpOf Z E)).map (perpOf Z E).subtype = perpOf Z E := by
    simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) (perpOf Z E)
  refine ⟨(P : Subgroup ↥(perpOf Z E)).map (perpOf Z E).subtype,
    Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_, hAP⟩
  have hrel : ((P : Subgroup ↥(perpOf Z E)).map (perpOf Z E).subtype).relIndex
      (perpOf Z E) = (P : Subgroup ↥(perpOf Z E)).index := by
    have h := Subgroup.relIndex_map_map_of_injective
      (P : Subgroup ↥(perpOf Z E)) ⊤ (perpOf Z E).subtype_injective
    rw [htop, Subgroup.relIndex_top_right] at h
    exact h
  rw [hrel]
  exact P.not_dvd_index

end CFSG.RankThree.PartTwo.Sec16.Proof166Three
