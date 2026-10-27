module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

open CFSG.ComponentClassification.AutL2Facts in
private theorem s16e_omc_simpleCentreless_five :
    SimpleCentreless (alternatingGroup (Fin 5)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  refine ⟨fun N hN => ?_, fun z hz => ?_, ?_⟩
  · haveI := hN
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
  · have hc : z ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hz g).symm
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    exact hc
  · exact exists_ne 1

private theorem s16e_omc_card_aut_five : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_eq_of_bijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num))]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

open CFSG.ComponentClassification.AutL2Facts in
theorem s16e_omc_card_dvd_nine
    {P : Subgroup (MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))}
    (hP : IsPGroup 3 P) : Nat.card P ∣ 9 := by
  have hSC := s16e_omc_simpleCentreless_five
  have hPle : P ≤ presSub (alternatingGroup (Fin 5)) := by
    intro φ hφ
    have hodd : Odd (orderOf φ) := by
      obtain ⟨k, hk⟩ := hP ⟨φ, hφ⟩
      have h1 : orderOf (⟨φ, hφ⟩ : P) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
      have h2 : orderOf φ = orderOf (⟨φ, hφ⟩ : P) := Subgroup.orderOf_coe ⟨φ, hφ⟩
      rw [h2]
      exact Odd.of_dvd_nat (Odd.pow (by decide)) h1
    have h1 := hSC.presFst_of_odd hodd
    exact ⟨h1, hSC.snd_of_fst h1⟩
  let ψ : ↥(presSub (alternatingGroup (Fin 5))) →*
      MulAut (alternatingGroup (Fin 5)) × MulAut (alternatingGroup (Fin 5)) :=
    fstHom.prod sndHom
  have hψ : Function.Injective ψ := fun a b h =>
    presSub_ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have h1 : Nat.card (P.subgroupOf (presSub (alternatingGroup (Fin 5)))) ∣
      Nat.card (MulAut (alternatingGroup (Fin 5)) × MulAut (alternatingGroup (Fin 5))) :=
    Subgroup.card_dvd_of_injective
      (ψ.comp (P.subgroupOf (presSub (alternatingGroup (Fin 5)))).subtype)
      (hψ.comp Subtype.val_injective)
  have h2 : Nat.card (P.subgroupOf (presSub (alternatingGroup (Fin 5)))) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv
  rw [h2, Nat.card_prod, s16e_omc_card_aut_five] at h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk] at h1 ⊢
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h3 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := Nat.dvd_trans h3 h1
    omega
  exact pow_dvd_pow 3 hk2

theorem s16e_omc_not_injective_of_dvd_card {H : Type} [Group H] [Finite H]
    (h27 : 27 ∣ Nat.card H)
    (f : H →* MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :
    ¬ Function.Injective f := by
  intro hf
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  have hP27 : 27 ∣ Nat.card P := by
    rw [P.card_eq_multiplicity]
    have h4 : 3 ≤ (Nat.card H).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1
        (by norm_num; exact h27)
    exact Nat.pow_dvd_pow 3 h4
  have hmap : Nat.card (P.map f) = Nat.card P := Subgroup.card_map_of_injective hf
  have hdvd : Nat.card (P.map f) ∣ 9 := s16e_omc_card_dvd_nine (P.isPGroup'.map f)
  rw [hmap] at hdvd
  have := Nat.le_of_dvd (by norm_num) (hP27.trans hdvd)
  omega

theorem s16e_omc_centralizer_ne_bot {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (e : ↥N ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))
    (h27 : 27 ∣ Nat.card H) : Subgroup.centralizer (N : Set H) ≠ ⊥ := by
  intro hC
  refine s16e_omc_not_injective_of_dvd_card h27
    ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal) ?_
  rw [injective_iff_map_eq_one]
  intro h hh
  have h1 : (MulAut.conjNormal (H := N)) h = 1 := (MulAut.congr e).map_eq_one_iff.1 hh
  have hmem : h ∈ Subgroup.centralizer (N : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have := congrArg (fun φ : MulAut ↥N => ((φ ⟨n, hn⟩ : ↥N) : H)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc n * h = (h * n * h⁻¹) * h := by rw [this]
      _ = h * n := by group
  rw [hC, Subgroup.mem_bot] at hmem
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
