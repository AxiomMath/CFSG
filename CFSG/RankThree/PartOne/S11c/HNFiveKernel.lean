module

public import CFSG.RankThree.PartOne.S11c.HNProps
public import CFSG.RankThree.CentralExtension.PrimeToPKernel

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG.RankThree.CentralExtension CFSG.Blueprint.NativeSporadic

@[expose] def HNFiveLocalInterface : Prop :=
  ∃ (H Q : Subgroup (Carrier .HN)) (hQH : Q ≤ H) (_ : (Q.subgroupOf H).Normal)
    (_ : Module (ZMod 5) (Additive (Abelianization Q)))
    (R : Subgroup (H ⧸ Q.subgroupOf H)) (_ : R.Normal),
    (∃ P : Sylow 5 (Carrier .HN), (P : Subgroup (Carrier .HN)) ≤ H) ∧ (∀ q ∈ Q, q ^ 5 = 1) ∧
    center Q = commutator Q ∧ Nat.card (center Q) = 5 ∧
    (∀ P : Sylow 5 (H ⧸ Q.subgroupOf H), IsCyclic P) ∧ (Nat.card R).Coprime 5 ∧
    (∀ h : H, (h : H ⧸ Q.subgroupOf H) ∈ R → ∀ z ∈ center Q, conjOnNormal hQH h z = z) ∧
    (∃ h : H, (h : H ⧸ Q.subgroupOf H) ∈ R ∧
      ∀ q : Q, Abelianization.of (conjOnNormal hQH h q) = (Abelianization.of q)⁻¹) ∧
    Module.finrank (ZMod 5) (conjInvariantAltForms 5 hQH R) = 1

theorem hnFiveKernelTrivial_of_interface (hI : HNFiveLocalInterface) : HNFiveKernelTrivial := by
  classical
  obtain ⟨H, Q, hQH, hQn, hmod, R, hRn, hsyl, hexp, hZ, hZc, hcyc, hRc, hRZ, hneg, hdim⟩ := hI
  intro X _ _ hXp S _ f hf hS hC
  have : Group.IsPerfect X := hXp
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := hS
  let eh : S →* Carrier .HN := e.toMonoidHom
  have key : ∀ (E' : Type) [Group E'] [Finite E'] [Group.IsPerfect E'] (π : E' →* S),
      Function.Surjective π → π.ker ≤ center E' → IsPGroup 5 π.ker → π.ker = ⊥ := by
    intro E' _ _ _ π hπ hC' hCp
    have hker : (eh.comp π).ker = π.ker := by
      ext g
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact map_eq_one_iff e e.injective
    have hs : Function.Surjective (eh.comp π) := e.surjective.comp hπ
    have : Finite (Carrier .HN) := Finite.of_surjective _ hs
    rw [← hker] at hC' hCp ⊢
    exact central_cover_extraspecial_normal_prime_to_p_kernel_trivial (by norm_num)
      hsyl hQH hexp hZ hZc hcyc R hRc hRZ hneg hdim (eh.comp π) hs hC' hCp
  intro h5
  obtain ⟨Cp⟩ : Nonempty (Sylow 5 f.ker) := inferInstance
  have h1 := sylow_ker_eq_bot_of_pKernel f hf hC key Cp
  have h2 : Nat.card (Cp : Subgroup f.ker) = 5 ^ (Nat.card f.ker).factorization 5 :=
    Cp.card_eq_multiplicity
  have h3 : 1 ≤ (Nat.card f.ker).factorization 5 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_five Nat.card_pos.ne').1 h5
  have h4 : Nat.card (Cp : Subgroup f.ker) = 1 := by rw [h1, Subgroup.card_bot]
  have h6 : 5 ^ 1 ≤ 5 ^ (Nat.card f.ker).factorization 5 := Nat.pow_le_pow_right (by norm_num) h3
  omega

end CFSG.RankThree.PartOne.HNRed
