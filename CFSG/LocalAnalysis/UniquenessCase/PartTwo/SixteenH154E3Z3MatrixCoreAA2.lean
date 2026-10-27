module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import TauCeti.GroupTheory.Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Subgroup
  CFSG.Open

private theorem s16h_e3_Z3MatrixCoreAA2_mem_of_orderOf_dvd_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hPnorm : P.Normal) (hPcard : Nat.card ↥P = p)
    (hsq : ¬ p ^ 2 ∣ Nat.card G) {x : G} (hx : orderOf x ∣ p) : x ∈ P := by
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hx with hx1 | hxp
  · rw [orderOf_eq_one_iff.mp hx1]
    exact P.one_mem
  · haveI : P.Normal := hPnorm
    have hPp : IsPGroup p P :=
      IsPGroup.of_card (G := ↥P) (n := 1) (by rw [hPcard, pow_one])
    have hKp : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (G := ↥(Subgroup.zpowers x)) (n := 1)
        (by rw [Nat.card_zpowers, hxp, pow_one])
    obtain ⟨Q, hKQ⟩ := hKp.exists_le_sylow
    have hPQ : P ≤ Q := hPp.le_sylow_of_normal Q
    have hdvd : p ∣ Nat.card G := by
      have h := Subgroup.card_dvd_of_le (le_top : P ≤ (⊤ : Subgroup G))
      rw [Subgroup.card_top] at h
      exact hPcard ▸ h
    have hQcard : Nat.card ↥(Q : Subgroup G) = p :=
      Sylow.card_eq_of_dvd_of_not_sq_dvd Q hdvd hsq
    have hPeqQ : (P : Subgroup G) = (Q : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hPQ (by simp [hPcard, hQcard])
    have hKP : Subgroup.zpowers x ≤ P := by
      rw [hPeqQ]
      exact hKQ
    exact hKP (Subgroup.mem_zpowers x)

theorem s16h_e3_z3_normal_five_of_closure
    (N K : Subgroup (coordinateSemilinearGroup 3 OmegaField))
    (D : Subgroup (coordinateSemilinearGroup 3 OmegaField))
    (hDK : D ≤ K) (hDN : (D.subgroupOf N).Normal)
    (hDrange : D ≤ MonoidHom.range (SemidirectProduct.inl :
      Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
        coordinateSemilinearGroup 3 OmegaField))
    (hcard : Nat.card ↥D ∣ 2 ^ 6 * 3 ^ 3 * 5 * 7)
    (F : Subgroup ↥D) (hFnorm : F.Normal) (hFcard : Nat.card ↥F = 5) :
    ∃ F' : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField),
      Nat.card ↥F' = 5 ∧
      ((Subgroup.map (SemidirectProduct.inl :
        Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
          coordinateSemilinearGroup 3 OmegaField) F').subgroupOf N).Normal ∧
      Subgroup.map (SemidirectProduct.inl :
        Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
          coordinateSemilinearGroup 3 OmegaField) F' ≤ K := by
  haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  haveI : Finite OmegaField := Module.finite_of_finite (ZMod 2)
  haveI : Finite (OmegaField ≃+* OmegaField) :=
    Finite.of_injective (fun σ : OmegaField ≃+* OmegaField => (σ : OmegaField → OmegaField))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  haveI : Finite (coordinateSemilinearGroup 3 OmegaField) :=
    Finite.of_injective
      (fun g : coordinateSemilinearGroup 3 OmegaField => (g.left, g.right))
      (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  haveI : Finite ↥D :=
    Finite.of_injective (fun x : ↥D => (x : coordinateSemilinearGroup 3 OmegaField))
      (fun _ _ h => Subtype.ext h)
  let P : Subgroup (coordinateSemilinearGroup 3 OmegaField) :=
    F.map (D.subtype : ↥D →* coordinateSemilinearGroup 3 OmegaField)
  let F' : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField) :=
    P.comap (SemidirectProduct.inl :
      Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
        coordinateSemilinearGroup 3 OmegaField)
  have hPleD : P ≤ D := Subgroup.map_subtype_le F
  have hPleRange : P ≤ MonoidHom.range (SemidirectProduct.inl :
      Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
        coordinateSemilinearGroup 3 OmegaField) := le_trans hPleD hDrange
  have hmapF' : Subgroup.map (SemidirectProduct.inl :
      Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
        coordinateSemilinearGroup 3 OmegaField) F' = P := by
    dsimp only [F']
    exact Subgroup.map_comap_eq_self hPleRange
  have hcardP : Nat.card ↥P = 5 := by
    dsimp only [P]
    rw [Subgroup.card_subtype D F, hFcard]
  have hF'card : Nat.card ↥F' = 5 := by
    have h := Subgroup.card_map_of_injective (f := (SemidirectProduct.inl :
      Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
        coordinateSemilinearGroup 3 OmegaField)) (K := F') SemidirectProduct.inl_injective
    rw [hmapF'] at h
    exact h.symm.trans hcardP
  have hsqD : ¬ 5 ^ 2 ∣ Nat.card ↥D := by
    have hN0 : ¬ (5 : ℕ) ^ 2 ∣ 2 ^ 6 * 3 ^ 3 * 5 * 7 := by decide
    intro h
    exact hN0 (h.trans hcard)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hPsubN : (P.subgroupOf N).Normal := by
    refine ⟨fun n hn k => ?_⟩
    have hnP : (n : coordinateSemilinearGroup 3 OmegaField) ∈ P := hn
    have hnD : (n : coordinateSemilinearGroup 3 OmegaField) ∈ D := hPleD hnP
    have hconjD : (k : coordinateSemilinearGroup 3 OmegaField) *
        (n : coordinateSemilinearGroup 3 OmegaField) *
        (k : coordinateSemilinearGroup 3 OmegaField)⁻¹ ∈ D := by
      have hmem := hDN.conj_mem
        ⟨(n : coordinateSemilinearGroup 3 OmegaField), n.2⟩ hnD
        ⟨(k : coordinateSemilinearGroup 3 OmegaField), k.2⟩
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa using hmem
    have hconjord : orderOf ((k : coordinateSemilinearGroup 3 OmegaField) *
        (n : coordinateSemilinearGroup 3 OmegaField) *
        (k : coordinateSemilinearGroup 3 OmegaField)⁻¹) =
        orderOf (n : coordinateSemilinearGroup 3 OmegaField) := by
      rw [← MulAut.conj_apply]
      exact (MulAut.conj (k : coordinateSemilinearGroup 3 OmegaField)).orderOf_eq
        (n : coordinateSemilinearGroup 3 OmegaField)
    have hordc : orderOf (⟨(k : coordinateSemilinearGroup 3 OmegaField) *
        (n : coordinateSemilinearGroup 3 OmegaField) *
        (k : coordinateSemilinearGroup 3 OmegaField)⁻¹, hconjD⟩ : ↥D) ∣ 5 := by
      rw [Subgroup.orderOf_mk, hconjord]
      have h := Subgroup.orderOf_dvd_natCard P hnP
      rwa [hcardP] at h
    have hcF : (⟨(k : coordinateSemilinearGroup 3 OmegaField) *
        (n : coordinateSemilinearGroup 3 OmegaField) *
        (k : coordinateSemilinearGroup 3 OmegaField)⁻¹, hconjD⟩ : ↥D) ∈ F :=
      s16h_e3_Z3MatrixCoreAA2_mem_of_orderOf_dvd_prime hFnorm hFcard hsqD hordc
    have hmemP : (k : coordinateSemilinearGroup 3 OmegaField) *
        (n : coordinateSemilinearGroup 3 OmegaField) *
        (k : coordinateSemilinearGroup 3 OmegaField)⁻¹ ∈ P := by
      dsimp only [P]
      exact Subgroup.mem_map.mpr ⟨⟨_, hconjD⟩, hcF, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    simpa using hmemP
  have hPK : P ≤ K := le_trans hPleD hDK
  refine ⟨F', hF'card, ?_, ?_⟩
  · rw [hmapF']
    exact hPsubN
  · rw [hmapF']
    exact hPK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
