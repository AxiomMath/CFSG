module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransferDerived

public section

namespace CFSG.Sporadic.Recognition.CoverRecipe

open Subgroup

theorem ker_eq_bot_of_sylow_subgroup {E S : Type} [Group E] [Finite E] [Group.IsPerfect E]
    [Group S] (π : E →* S) (hC : π.ker ≤ center E) (hp : IsPGroup 3 π.ker)
    (N : Subgroup S) (hNle : N ≤ π.range)
    (hsyl : (Nat.card π.range).factorization 3 ≤ (Nat.card N).factorization 3)
    (key : ∀ (M : Type) [Group M] [Finite M] (φ : M →* N), Function.Surjective φ →
      φ.ker ≤ center M → IsPGroup 3 φ.ker → φ.ker ≤ commutator M → φ.ker = ⊥) :
    π.ker = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := π.ker with hK
  set M : Subgroup E := N.comap π with hM
  have hKM : K ≤ M := fun k hk => by
    rw [hM, Subgroup.mem_comap, MonoidHom.mem_ker.mp hk]
    exact N.one_mem
  let φ : M →* N := (π.comp M.subtype).codRestrict N fun m => m.2
  have hφs : Function.Surjective φ := fun y => by
    obtain ⟨e, he⟩ := hNle y.2
    exact ⟨⟨e, by rw [hM, Subgroup.mem_comap, he]; exact y.2⟩, Subtype.ext he⟩
  have hφker : ∀ m : M, m ∈ φ.ker ↔ (m : E) ∈ K := fun m => by
    rw [MonoidHom.mem_ker, hK, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have : Finite π.range := Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  have : Finite N := Finite.of_injective (fun x : N => (⟨x.1, hNle x.2⟩ : π.range))
    (fun a b h => Subtype.ext (congrArg (fun y : π.range => (y : S)) h))
  have hcardE : Nat.card E = Nat.card π.range * Nat.card K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv]
  have hkerφ : Nat.card φ.ker = Nat.card K := by
    refine Nat.card_congr ⟨fun m => ⟨m.1.1, (hφker m.1).1 m.2⟩,
      fun k => ⟨⟨k.1, hKM k.2⟩, (hφker ⟨k.1, hKM k.2⟩).2 k.2⟩, fun m => ?_, fun k => ?_⟩
    · rfl
    · rfl
  have hcardM : Nat.card M = Nat.card N * Nat.card K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv, hkerφ]
  have hMdvd : Nat.card M ∣ Nat.card E := Subgroup.card_subgroup_dvd_card M
  have hE0 : Nat.card E ≠ 0 := Nat.card_pos.ne'
  have hM0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hR0 : Nat.card π.range ≠ 0 := Nat.card_pos.ne'
  have hfM : (Nat.card M).factorization 3 = (Nat.card E).factorization 3 := by
    have h1 : (Nat.card M).factorization 3 ≤ (Nat.card E).factorization 3 :=
      (Nat.factorization_le_iff_dvd hM0 hE0).2 hMdvd 3
    have h2 : (Nat.card E).factorization 3 ≤ (Nat.card M).factorization 3 := by
      rw [hcardE, hcardM, Nat.factorization_mul hR0 hK0, Nat.factorization_mul hN0 hK0,
        Finsupp.add_apply, Finsupp.add_apply]
      omega
    omega
  obtain ⟨P⟩ : Nonempty (Sylow 3 M) := inferInstance
  set T' : Subgroup E := (P : Subgroup M).map M.subtype with hT'
  have hT'M : T' ≤ M := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hT'card : Nat.card T' = 3 ^ (Nat.card E).factorization 3 := by
    rw [hT', ← hfM, ← P.card_eq_multiplicity]
    exact (Nat.card_congr ((P : Subgroup M).equivMapOfInjective M.subtype
      M.subtype_injective).toEquiv).symm
  let T : Sylow 3 E := Sylow.ofCard T' hT'card
  have hT : (T : Subgroup E) = T' := Sylow.coe_ofCard T' hT'card
  have hKT := (CFSG.ShultStronglyClosedTI.MiscAlgebra.central_sylow_transfer_derived T K hC hp).1
  rw [hT] at hKT
  have hKMM : K ≤ ⁅M, M⁆ := hKT.trans (Subgroup.commutator_mono hT'M hT'M)
  have hder : ∀ m : M, (m : E) ∈ K → m ∈ commutator M := fun m hm => by
    have h1 : (m : E) ∈ ⁅M, M⁆ := hKMM hm
    have h2 : ⁅M, M⁆ = (commutator M).map M.subtype := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [h2] at h1
    obtain ⟨c, hc, hcm⟩ := h1
    have : c = m := Subtype.ext hcm
    rwa [this] at hc
  have hbot := key M φ hφs
    (fun m hm => Subgroup.mem_center_iff.2 fun n => Subtype.ext (by
      have := Subgroup.mem_center_iff.mp (hC ((hφker m).1 hm)) n
      simpa using this))
    (fun x => by
      obtain ⟨k, hk⟩ := hp ⟨(x.1 : E), (hφker x.1).1 x.2⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩)
    (fun m hm => hder m ((hφker m).1 hm))
  refine eq_bot_iff.2 fun k hk => ?_
  have : (⟨k, hKM hk⟩ : M) ∈ φ.ker := (hφker _).2 hk
  rw [hbot, Subgroup.mem_bot] at this
  simpa using congrArg Subtype.val this

end CFSG.Sporadic.Recognition.CoverRecipe
