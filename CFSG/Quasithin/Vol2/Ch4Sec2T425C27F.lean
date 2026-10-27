module

public import CFSG.Quasithin.EmptyFaithful.S153QPA1
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27B
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.SBc17
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

section Transport

variable {Γ H : Type} [Group Γ] [Group H]

theorem isParabolic2_top_of_mulEquiv {L P : Subgroup Γ} (h : IsParabolic2 L P) (e : ↥L ≃* H) :
    IsParabolic2 (⊤ : Subgroup H) ((P.subgroupOf L).map e.toMonoidHom) := by
  have h1 : IsParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
    rw [A312.isParabolic2_top_iff, Subgroup.map_subgroupOf_eq_of_le h.1]
    exact h
  have h2 := (SBd3T.isParabolic2_map_iff e.toMonoidHom e.injective ⊤ (P.subgroupOf L)).2 h1
  rwa [Subgroup.map_top_of_surjective _ e.surjective] at h2

theorem map_subgroupOf_le_normalizer {L X Y : Subgroup Γ}
    (hYX : Y ≤ Subgroup.normalizer (X : Set Γ)) (φ : ↥L →* H) (hφ : Function.Injective φ) :
    (Y.subgroupOf L).map φ ≤
      Subgroup.normalizer (((X.subgroupOf L).map φ : Subgroup H) : Set H) := by
  rw [SBd3T.map_le_normalizer_map_iff φ hφ]
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have := Subgroup.mem_normalizer_iff.mp (hYX (Subgroup.mem_subgroupOf.mp hy)) (x : Γ)
  simpa using this

theorem card_sup_eq_of_le_normalizer {A B : Subgroup Γ}
    (h : A ≤ Subgroup.normalizer (B : Set Γ)) :
    Nat.card ↥(A ⊔ B) = B.relIndex A * Nat.card B := by
  have hrel : B.relIndex (A ⊔ B) = B.relIndex A := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer h
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  rw [inf_eq_left.mpr le_sup_right, hrel] at h1
  exact h1.symm

noncomputable def subgroupOfMapEquiv {L X : Subgroup Γ} (hXL : X ≤ L) (φ : ↥L →* H)
    (hφ : Function.Injective φ) : ↥X ≃* ↥((X.subgroupOf L).map φ) :=
  (Subgroup.subgroupOfEquivOfLe hXL).symm.trans ((X.subgroupOf L).equivMapOfInjective φ hφ)

end Transport

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {H R M K J : Subgroup G} (c : Ctx H R M K J)
include c

theorem autOn_le_normalizer :
    autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ≤
      Subgroup.normalizer
        (autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) : Set (MulAut ↥(omegaOneCenterOf
          (pCoreOf 2 (K ⊔ R))))) := by
  refine le_trans ?_ (Subgroup.le_normalizer_map (conjAct _))
  apply Subgroup.map_mono
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have := Subgroup.mem_normalizer_iff.mp (c.J_norm (Subgroup.mem_subgroupOf.mp hx)) (y : G)
  simpa using this

variable (hC27 : ASC27Statement G)
include hC27

theorem three_dvd_of_binary {m : ℕ} (hm : 3 ≤ m)
    (e₀ : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)))
    (hpar : IsParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
      (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) :
    3 ∣ Nat.card (autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) := by
  classical
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hV
  set e : ↥(autOn K V) ≃* SpecialLinearGroup (Fin m) (ZMod 2) :=
    e₀.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m (ZMod 2)).symm
  obtain ⟨-, S, hS, hNS⟩ := isParabolic2_top_of_mulEquiv hpar e
  obtain ⟨g, hg⟩ := QP.exists_conj_normalizer_of_isSylowTwoOf (by omega : 1 ≤ m) hS
  set φ : ↥(autOn K V) →* SpecialLinearGroup (Fin m) (ZMod 2) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom with hφdef
  have hφ : Function.Injective φ := (MulAut.conj g⁻¹).injective.comp e.injective
  have hJL : autOn J V ≤ autOn K V := autOn_mono' c.J_le_K
  set J' := ((autOn J V).subgroupOf (autOn K V)).map φ with hJ'
  set U := unitriangular m (ZMod 2) with hU
  have hUP : U ≤ ((autOn (M ⊓ K) V).subgroupOf (autOn K V)).map φ := by
    rw [hU, ← BinaryParabolic.upperTriangular_eq_unitriangular]
    intro b hb
    have h1 : (MulAut.conj g) b ∈ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin m) _)) := by
      rw [hg]
      exact ⟨b, hb, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hNS ⟨Subgroup.mem_top _, h1⟩
    refine ⟨x, hx, ?_⟩
    show (MulAut.conj g⁻¹) (e x) = b
    rw [show e x = (MulAut.conj g) b from hxe]
    simp only [MulAut.conj_apply]
    group
  have hUJ : U ≤ Subgroup.normalizer (J' : Set (SpecialLinearGroup (Fin m) (ZMod 2))) :=
    hUP.trans (map_subgroupOf_le_normalizer c.autOn_le_normalizer φ hφ)
  have hcard : Nat.card J' = Nat.card (autOn J V) :=
    (Nat.card_congr (subgroupOfMapEquiv hJL φ hφ).toEquiv).symm
  set A := U ⊔ J' with hA
  obtain ⟨hAI, -⟩ := borel_overgroups A
    (BinaryParabolic.upperTriangular_eq_unitriangular ▸ (le_sup_left : U ≤ A))
  by_cases hex : ∃ j, 1 ≤ j ∧ j < m ∧ j ∉ borelOvergroupCuts A
  · obtain ⟨j, hj, hjm, hjI⟩ := hex
    have hMA : flagStabilizer m (ZMod 2) (Set.Icc 1 (m - 1) \ {j}) ≤ A := by
      rw [hAI]
      refine BinaryParabolic.flagStabilizer_anti fun i hi => ?_
      obtain ⟨hi1, hin, hr⟩ := hi
      exact BinaryParabolic.mem_cuts.2 ⟨hi1, by omega, fun hij => hjI (by
        subst hij
        exact ⟨hi1, hin, hr⟩)⟩
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _
      (BinaryParabolic.unitriangular_le_flagStabilizer _) hMA
    rw [BinaryParabolic.relIndex_parabolic hj hjm] at hmul
    have h3A : 3 ∣ Nat.card A := by
      rw [← Subgroup.relIndex_mul_card (H := U) (K := A), ← hmul, mul_assoc]
      exact Dvd.intro _ rfl
    rw [hA, card_sup_eq_of_le_normalizer hUJ] at h3A
    have hrel : J'.relIndex U ∣ 2 ^ (m * (m - 1) / 2) := by
      have := Subgroup.relIndex_mul_card (H := J') (K := U)
      rw [hU, card_unitriangular, Nat.card_zmod] at this
      exact ⟨_, this.symm⟩
    have hcop : Nat.Coprime 3 (J'.relIndex U) :=
      Nat.Coprime.coprime_dvd_right hrel (Nat.Coprime.pow_right _ (by norm_num))
    rw [← hcard]
    exact hcop.dvd_of_dvd_mul_left h3A
  · exfalso
    push Not at hex
    have hI : borelOvergroupCuts A = Set.Icc 1 (m - 1) := by
      ext i
      constructor
      · rintro ⟨hi, hin, -⟩
        exact ⟨hi, by omega⟩
      · rintro ⟨hi, hin⟩
        exact hex i hi (by omega)
    have hAU : A = U := by rw [hAI, hI, BinaryParabolic.flagStabilizer_Icc]
    have hJU : J' ≤ U := hAU ▸ (le_sup_right : J' ≤ A)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hU2 : IsPGroup 2 U := IsPGroup.of_card (by rw [hU, card_unitriangular, Nat.card_zmod])
    have : Group.IsNilpotent J' := (hU2.to_le hJU).isNilpotent
    exact c.not_isSolvable_autOn hC27 (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfMapEquiv hJL φ hφ).toMonoidHom) (subgroupOfMapEquiv hJL φ hφ).injective)

theorem false_of_l45 (h : C27L45 H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) : False := by
  obtain ⟨he, hpar, -⟩ := h
  have hs := c.star hC27
  have key : ∀ m : ℕ, 4 ≤ m → Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2))) → False := by
    rintro m hm ⟨e₀⟩
    have hle := c.rank_three (c.three_dvd_of_binary hC27 (by omega) e₀ hpar)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let f : ↥K →*
        CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) :=
      (QuotientGroup.mk' _).comp (e₀.toMonoidHom.comp (InternalSec.autOnHom hs.K_le_normalizer_V))
    have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
      (e₀.surjective.comp (InternalSec.autOnHom_surjective _))
    have hge := two_le_pRank_of_surjective f hf (p := 3) (by norm_num)
      (CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psl (K := ZMod 2) hm)
    omega
  rcases he with h4 | h5
  · exact key 4 le_rfl h4
  · exact key 5 (by norm_num) h5

end Ctx

end CFSG.Quasithin.H13.Ch4.T425C27
