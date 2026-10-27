module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143RowGen
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerA6
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerCard
public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Schreier.PairJ3CertBase

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open Equiv Equiv.Perm

variable {S : Type*} [Group S]

private theorem alt_six_data :
    ∃ u s v : alternatingGroup (Fin 6), u ^ 3 = 1 ∧ s * u * s⁻¹ = u⁻¹ ∧ v * u ≠ u * v := by
  refine ⟨⟨c[0, 1, 2], mem_alternatingGroup.mpr (by decide)⟩,
    ⟨swap 0 1 * swap 3 4, mem_alternatingGroup.mpr (by decide)⟩,
    ⟨c[0, 1, 3], mem_alternatingGroup.mpr (by decide)⟩, ?_, ?_, ?_⟩
  · exact Subtype.ext (by decide)
  · exact Subtype.ext (by decide)
  · intro h
    exact absurd (congrArg Subtype.val h) (by decide)

theorem L143Row.of_alt_six_le_centralizer {x : S} (I : Subgroup S)
    (hI : I ≤ Subgroup.centralizer ({x} : Set S)) (e : I ≃* alternatingGroup (Fin 6)) :
    L143Row x := by
  obtain ⟨u₀, s₀, v₀, hu₀, hs₀, hv₀⟩ := alt_six_data
  have hcomm : ∀ w : I, Commute (w : S) x := fun w =>
    Subgroup.mem_centralizer_singleton_iff.mp (hI w.2)
  refine Or.inl ⟨(e.symm u₀ : S), (e.symm s₀ : S), (hcomm _).eq, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hu₀, map_one, Subgroup.coe_one]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hv₀
    apply e.symm.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← hk]
    exact ((hcomm (e.symm v₀)).zpow_right k).eq
  · have h := congrArg (fun g : alternatingGroup (Fin 6) => ((e.symm g : I) : S)) hs₀
    simpa [map_mul, map_inv] using h

theorem L143Row.of_card_centralizer_eq_sylow [Finite S] {x : S}
    (hC : Nat.card (Subgroup.centralizer ({x} : Set S)) = 3 ^ (Nat.card S).factorization 3)
    (E : Subgroup S) (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hE : 27 ≤ Nat.card E) : L143Row x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 S := Sylow.ofCard (Subgroup.centralizer ({x} : Set S)) hC
  have hP : (P : Subgroup S) = Subgroup.centralizer ({x} : Set S) := Sylow.coe_ofCard _ _
  have hEp : IsPGroup 3 E := fun e => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE3 e e.2)⟩
  obtain ⟨Q, hQ⟩ := hEp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq S P Q
  refine L143Row.of_conj c (Or.inr ⟨E, fun e he => ?_, hEc, hE3, hE⟩)
  have heQ : e ∈ (Q : Subgroup S) := hQ he
  rw [← hc, Sylow.coe_subgroup_smul] at heQ
  obtain ⟨p, hp, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp heQ
  rw [hP] at hp
  have hpx : p * x = x * p := Subgroup.mem_centralizer_singleton_iff.mp hp
  show c * p * c⁻¹ * (c * x * c⁻¹) = c * x * c⁻¹ * (c * p * c⁻¹)
  calc c * p * c⁻¹ * (c * x * c⁻¹) = c * (p * x) * c⁻¹ := by group
    _ = c * (x * p) * c⁻¹ := by rw [hpx]
    _ = c * x * c⁻¹ * (c * p * c⁻¹) := by group

private theorem l143Row_of_mulEquiv_J3
    (hE : ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.J3, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a ^ 3 = 1) ∧ 27 ≤ Nat.card E)
    {Q : Type} [Group Q] (e : Q ≃* CFSG.Blueprint.NativeSporadic.J3) {x : Q} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : L143Row x := by
  rcases CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_centralizer_of_equiv_J3_dichotomy
    e hx3 hx1 with h | h
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    let ψ : Q ≃* ↥CFSG.Sporadic.Schreier.j3P :=
      e.trans CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.j3CarrierEquiv
    have hy3 : orderOf ((ψ x : CFSG.Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156)) = 3 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hx
    have hcard := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv ψ x
    have h5 : 5 ∣ Nat.card (Subgroup.centralizer
        ({((ψ x : CFSG.Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156))} :
          Set (Equiv.Perm (Fin 6156))) ⊓ CFSG.Sporadic.Schreier.j3P :
        Subgroup (Equiv.Perm (Fin 6156))) := by
      rw [← hcard, h]
      norm_num
    obtain ⟨Dy, hDyC, -, -, ⟨eD⟩⟩ :=
      CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.exists_A6_in_centralizer_j3P (ψ x).2 hy3 h5
    let I : Subgroup Q := (Dy.subgroupOf CFSG.Sporadic.Schreier.j3P).map ψ.symm.toMonoidHom
    let eI : ↥I ≃* alternatingGroup (Fin 6) :=
      ((MulEquiv.subgroupMap ψ.symm (Dy.subgroupOf CFSG.Sporadic.Schreier.j3P)).symm.trans
        (Subgroup.subgroupOfEquivOfLe (hDyC.trans inf_le_right))).trans eD
    have hIC : I ≤ Subgroup.centralizer {x} := by
      rintro _ ⟨d, hd, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm := Subgroup.mem_centralizer_singleton_iff.1
        (Subgroup.mem_inf.1 (hDyC (Subgroup.mem_subgroupOf.1 hd))).1
      change ψ.symm d * x = x * ψ.symm d
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hcomm
    exact L143Row.of_alt_six_le_centralizer I hIC eI
  ·
    haveI : Finite CFSG.Blueprint.NativeSporadic.J3 := (CFSG.Sporadic.J3.fam_j3_simplicity).1
    haveI : Finite Q := Finite.of_equiv _ e.symm.toEquiv
    have hQ : (Nat.card Q).factorization 3 = 5 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.factorization_card_J3_three
    have h3 : Nat.card (Subgroup.centralizer ({x} : Set Q)) =
        3 ^ (Nat.card Q).factorization 3 := by
      rw [h, hQ]
      norm_num
    obtain ⟨E, hEc, hE3, hE27⟩ := hE
    refine L143Row.of_card_centralizer_eq_sylow h3
      (E.map (e.symm : CFSG.Blueprint.NativeSporadic.J3 →* Q)) ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      change e.symm a * e.symm b = e.symm b * e.symm a
      rw [← map_mul, ← map_mul, hEc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      change e.symm a ^ 3 = 1
      rw [← map_pow, hE3 a ha, map_one]
    · rwa [Subgroup.card_map_of_injective (f := (e.symm : CFSG.Blueprint.NativeSporadic.J3 →* Q))
        (fun a b h => e.symm.injective h)]

theorem l143RowsT_J3
    (T : Type) [Group T]
    (hT : Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.J3)) : L143Rows T := by
  obtain ⟨e⟩ := hT
  obtain ⟨E, hE, hEcard⟩ := CFSG.SectionRank.J3_elementary_three_rank_three
  refine fun x hx3 hx1 => l143Row_of_mulEquiv_J3
    ⟨E, fun a ha b hb => ?_, hE.2, by rw [hEcard]; norm_num⟩ e hx3 hx1
  simpa using congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
