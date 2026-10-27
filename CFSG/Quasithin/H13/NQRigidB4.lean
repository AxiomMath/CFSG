module

public import CFSG.Quasithin.H13.NQRigidCoreQuot
public import CFSG.Quasithin.H13.NQTermEvenSymplecticFourImage
public import CFSG.Quasithin.H13.NQRigidInputs

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup Matrix
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj frattiniQuotConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Assembly.LowTwoRank

section Form

variable (k : Type) [Field k]

@[expose] noncomputable def spBilin : LinearMap.BilinForm k (Fin 2 ⊕ Fin 2 → k) :=
  LinearMap.mk₂ k (fun u v => u ⬝ᵥ (LieType.BorelTits.spJ 2 k *ᵥ v))
    (fun u u' v => add_dotProduct u u' _)
    (fun c u v => smul_dotProduct c u _)
    (fun u v v' => by rw [mulVec_add, dotProduct_add])
    (fun c u v => by rw [mulVec_smul, dotProduct_smul])

theorem spBilin_apply (u v : Fin 2 ⊕ Fin 2 → k) :
    spBilin k u v = (LieType.BorelTits.spForm 2 k).β u v :=
  rfl

theorem spBilin_nondegenerate : (spBilin k).Nondegenerate := by
  refine ⟨fun u hu => (LieType.BorelTits.spForm 2 k).nondeg u hu, fun v hv => ?_⟩
  exact (LieType.BorelTits.spForm 2 k).nondeg v fun u =>
    (LieType.BorelTits.spForm 2 k).refl u v (hv u)

theorem spBilin_isAlt : (spBilin k).IsAlt := fun v =>
  LieType.BorelTits.spForm_self 2 k v

theorem toLin_mem_bilinIsometryGroup (g : StatedSp 2 k) :
    Matrix.GeneralLinearGroup.toLin (g : GL (Fin 2 ⊕ Fin 2) k) ∈
      NQTerm.bilinIsometryGroup (spBilin k) := by
  rw [NQTerm.mem_bilinIsometryGroup]
  intro v w
  rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
    spBilin_apply, spBilin_apply]
  have h := LieType.BorelTits.isIsometric_natRep_statedSp 2 k g v w
  rw [LieType.BorelTits.natRep_apply, LieType.BorelTits.natRep_apply] at h
  exact h

@[expose] noncomputable def spToIsometry : StatedSp 2 k →* NQTerm.bilinIsometryGroup (spBilin k) :=
  (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (StatedSp 2 k).subtype).codRestrict _
    (toLin_mem_bilinIsometryGroup k)

theorem spToIsometry_injective : Function.Injective (spToIsometry k) := by
  intro g h hgh
  have h1 := congrArg Subtype.val hgh
  exact (StatedSp 2 k).subtype_injective (Matrix.GeneralLinearGroup.toLin.injective h1)

theorem finrank_spSpace : Module.finrank k (Fin 2 ⊕ Fin 2 → k) = 4 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

end Form

theorem original_perfect_plane_excludes_ordinary_even_symplectic_four_quotient {G : Type}
    [Group G] [Finite G] (L K X : Subgroup G) (hL : Group.IsPerfect L)
    (hKq : CFSG.IsQuasisimple K) (hXL : X ≤ L) (hXK : X ≤ K) (hXn : (X.subgroupOf L).Normal)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hO2 : CFSG.pCore 2 X ≠ ⊥)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : IsFrattiniIrreducible X L) (hX2 : NoPQuotient 2 X)
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) {f : ℕ} (hf : 2 ≤ f) :
    ¬ StatedClassicalModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSp 2 2 f := by
  classical
  rintro ⟨-, k, hkf, hkfin, hk, ⟨e⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have := hXn
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ f) hk
  set ψ : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* StatedSp 2 k :=
    e.trans (LieType.SteinbergBR.EvenSp.projEquiv (by norm_num)) with hψ
  set ι : X.subgroupOf L →* K := (inclusion hXK).comp (subgroupOfEquivOfLe hXL).toMonoidHom
    with hι
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h1 : ((ι a : K) : G) = ((ι b : K) : G) := congrArg (fun z : K => (z : G)) hab
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  set φ : X.subgroupOf L →* NQTerm.bilinIsometryGroup (spBilin k) :=
    (spToIsometry k).comp (ψ.toMonoidHom.comp ((coreCenterQuot K).comp ι)) with hφ
  have hker : ∀ x, x ∈ φ.ker ↔ ι x ∈ (coreCenterQuot K).ker := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change spToIsometry k (ψ (coreCenterQuot K (ι x))) = 1 ↔ coreCenterQuot K (ι x) = 1
    rw [(injective_iff_map_eq_one' _).mp (spToIsometry_injective k), MulEquiv.map_eq_one_iff]
  have hσZ := ker_coreCenterQuot_of_quasisimple hKq
  have hcen : φ.ker ≤ center (X.subgroupOf L) := by
    intro x hx
    rw [mem_center_iff]
    intro y
    have hxZ : ι x ∈ center K := hσZ ▸ (hker x).mp hx
    apply hιinj
    rw [map_mul, map_mul]
    exact (mem_center_iff.mp hxZ (ι y))
  have hσp := not_dvd_card_ker_coreCenterQuot hp hp2 hZ
  have hX'A : IsPGroup p (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) :=
    hXA.of_equiv (coreQuotEquivSubgroupOf hXL).symm
  obtain ⟨a, b, hab⟩ := card_eq_two_pow_mul_prime_pow hX'A
  have h2 : IsPGroup 2 φ.ker := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx1 : orderOf (x : X.subgroupOf L) ∣ 2 ^ a * p ^ b := by
      rw [← hab]
      exact orderOf_dvd_natCard _
    have hx2 : ¬ p ∣ orderOf (x : X.subgroupOf L) := by
      intro hdvd
      apply hσp
      have h3 : orderOf (⟨ι x, (hker x).mp x.2⟩ : (coreCenterQuot K).ker) =
          orderOf (x : X.subgroupOf L) := by
        rw [← Subgroup.orderOf_coe, orderOf_injective ι hιinj]
      exact hdvd.trans (h3 ▸ orderOf_dvd_natCard _)
    have hx3 : orderOf (x : X.subgroupOf L) ∣ 2 ^ a := by
      have hcop : Nat.Coprime (orderOf (x : X.subgroupOf L)) (p ^ b) :=
        Nat.Coprime.pow_right b ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
          hx2)))
      exact hcop.dvd_of_dvd_mul_right hx1
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx3
    exact ⟨m, by rw [← hm, Subgroup.orderOf_coe]⟩
  have hA1 : CFSG.pCore 2 (X.subgroupOf L) ≠ ⊥ := by
    intro h0
    apply hO2
    rw [← CFSG.pCore_map_iso 2 (subgroupOfEquivOfLe hXL), h0, Subgroup.map_bot]
  have hexp' : Monoid.exponent (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) = p := by
    rw [Monoid.exponent_eq_of_mulEquiv (coreQuotEquivSubgroupOf hXL), hexp]
  have hW' := card_frattini_subgroupOf hXL
  rw [hW] at hW'
  have hX2' : NoPQuotient 2 (X.subgroupOf L) :=
    NoPQuotient.of_surjective (subgroupOfEquivOfLe hXL).symm.toMonoidHom
      (subgroupOfEquivOfLe hXL).symm.surjective hX2
  exact NQTerm.original_perfect_plane_excludes_central_even_symplectic_four_image hL hp hp5 hA1
    hexp' hW' (frattiniQuotConj_irreducible_of hXL hirr) hX2' k (Fin 2 ⊕ Fin 2 → k)
    (finrank_spSpace k) (spBilin k) (spBilin_nondegenerate k) (spBilin_isAlt k) ⟨φ, h2, hcen⟩

theorem stmtOrdinaryEvenSymplecticFour_holds : StmtOrdinaryEvenSymplecticFour :=
  fun _ _ _ L K X hL hKq hXL hXK hXn _ hp hp5 hO2 hXA hexp hW hirr hX2 hZ _ hf =>
    original_perfect_plane_excludes_ordinary_even_symplectic_four_quotient L K X hL hKq hXL hXK
      hXn hp hp5 hO2 hXA hexp hW hirr hX2 hZ hf

end CFSG.Quasithin.H13.NQRigid
