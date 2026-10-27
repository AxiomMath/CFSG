module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructStab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin.H13.F431.D4q.Struct
open CFSG.Quasithin.H13.F431.D4q.Hex

theorem subgroup_map_mul_mulAut {G : Type*} [Group G] (H : Subgroup G) (φ ψ : MulAut G) :
    H.map (φ * ψ).toMonoidHom = (H.map ψ.toMonoidHom).map φ.toMonoidHom := by
  have h : (φ * ψ).toMonoidHom = φ.toMonoidHom.comp ψ.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [h, ← Subgroup.map_map]

theorem kDiag_transport_strong {X Y : Type} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y)
    (hY : ∀ (θ : MulAut Y),
      ∀ S : Sylow 2 Y, (∀ x ∈ (S : Subgroup Y), θ x ∈ (S : Subgroup Y)) →
      ∀ P : Subgroup Y, IsParabolicTwo Y P →
        (S : Subgroup Y) ≤ Subgroup.normalizer (P : Set Y) →
        ∀ x ∈ P, θ x ∈ P) :
    ∀ (θ : MulAut X),
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Y := Finite.of_surjective e e.surjective
  intro θ S hSθ P hP hSP x hx
  let θ' : MulAut Y := MulAut.congr e θ
  let S' : Sylow 2 Y := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS'coe : (S' : Subgroup Y) = (S : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have hS'θ : ∀ y ∈ (S' : Subgroup Y), θ' y ∈ (S' : Subgroup Y) := by
    intro y hy
    rw [hS'coe] at hy ⊢
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    have happ : θ' (e.toMonoidHom s) = e.toMonoidHom (θ s) := by
      simp [θ', MulAut.congr_apply]
    rw [happ]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hSθ s hs)
  have hP' : IsParabolicTwo Y (P.map e.toMonoidHom) :=
    IsParabolicTwo.map hP e.toMonoidHom e.surjective
  have hSP' : (S' : Subgroup Y) ≤
      Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup Y) : Set Y) := by
    rw [hS'coe]
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.le_normalizer_map (f := e.toMonoidHom) (H := P)
      (Subgroup.mem_map_of_mem e.toMonoidHom (hSP hs))
  have hmem : θ' (e x) ∈ (P.map e.toMonoidHom : Subgroup Y) :=
    hY θ' S' hS'θ (P.map e.toMonoidHom) hP' hSP' (e x)
      (Subgroup.mem_map_of_mem e.toMonoidHom hx)
  have happx : θ' (e x) = e (θ x) := by
    simp [θ', MulAut.congr_apply]
  rw [happx] at hmem
  exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hmem

section Model

variable {K : Type} [Field K] [Finite K]

theorem kDiag_graphFixedRootGroup_strong (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ∀ (θ : MulAut (Cm σ)),
    ∀ S : Sylow 2 (Cm σ),
      (∀ x ∈ (S : Subgroup (Cm σ)), θ x ∈ (S : Subgroup (Cm σ))) →
    ∀ P : Subgroup (Cm σ), IsParabolicTwo (Cm σ) P →
      (S : Subgroup (Cm σ)) ≤ Subgroup.normalizer (P : Set (Cm σ)) →
      ∀ x ∈ P, θ x ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK3
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ' : ∀ c, σ.toRingHom c = c ^ (2 ^ f) := fun c => hσ c
  intro θ S hSθ P hPpar hSP x hx
  have hSP' : (S : Subgroup (Cm σ)) ≤ P := hPpar.le_of_le_normalizer S.isPGroup' hSP
  have hNSP : Subgroup.normalizer ((S : Subgroup (Cm σ)) : Set (Cm σ)) ≤ P :=
    hPpar.normalizer_le S hSP'
  have hUsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Ust σ) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1
      (CFSG.Quasithin.H13.Sec53F.TriD4.d4_sylow σ)
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 ((S : Subgroup (Cm σ))) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := hSsyl.exists_mem_conj hUsyl
  have hSmap : ((S : Subgroup (Cm σ))).map θ.toMonoidHom = (S : Subgroup (Cm σ)) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  let e : Cm σ ≃* Cm σ := MulAut.conj k
  let θ' : MulAut (Cm σ) := MulAut.congr e θ
  have hcomp : θ'.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp θ.toMonoidHom := by
    ext y
    simp [θ', MulAut.congr_apply]
  have hconj : ((S : Subgroup (Cm σ))).map e.toMonoidHom = Ust σ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
      refine (hk (k * (s : Cm σ) * k⁻¹)).2 ?_
      rw [show k⁻¹ * (k * (s : Cm σ) * k⁻¹) * k = s by group]
      exact hs
    · rw [Subgroup.card_map_of_injective e.injective, hUsyl.card_eq, hSsyl.card_eq]
  have hUθ' : (Ust σ).map θ'.toMonoidHom = Ust σ := by
    rw [← hconj, Subgroup.map_map, hcomp, ← Subgroup.map_map, hSmap, hconj]
  obtain ⟨-, hform, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  obtain ⟨⟨h, ε⟩, hθ'e, -⟩ := hform θ'
  have hmul : (Ust σ).map θ'.toMonoidHom =
      ((Ust σ).map (fieldActor σ ε).toMonoidHom).map (MulAut.conj h).toMonoidHom := by
    rw [hθ'e, subgroup_map_mul_mulAut]
  have hconjhU : (Ust σ).map (MulAut.conj h).toMonoidHom = Ust σ := by
    rw [hmul, fieldActor_map_Ust σ ε] at hUθ'
    exact hUθ'
  have hmemN : h ∈ Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconjhU
  have hNSe : (Subgroup.normalizer ((S : Subgroup (Cm σ)) : Set (Cm σ))).map e.toMonoidHom =
      Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) := by
    rw [Subgroup.map_equiv_normalizer_eq, hconj]
  have hNA : Subgroup.normalizer ((Ust σ : Subgroup (Cm σ)) : Set (Cm σ)) ≤
      P.map e.toMonoidHom := by
    rw [← hNSe]
    exact Subgroup.map_mono hNSP
  have hAmem : h ∈ P.map e.toMonoidHom := hNA hmemN
  have hconjhA : (P.map e.toMonoidHom).map (MulAut.conj h).toMonoidHom =
      P.map e.toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      change (MulAut.conj h) a ∈ P.map e.toMonoidHom
      rw [MulAut.conj_apply]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hAmem ha) (Subgroup.inv_mem _ hAmem)
    · exact le_of_eq (Subgroup.card_map_of_injective
        (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective).symm
  have hFA : (P.map e.toMonoidHom).map (fieldActor σ ε).toMonoidHom = P.map e.toMonoidHom := by
    rcases d4_overgroups_normalizer σ (P.map e.toMonoidHom) hNA with hA | hA | hA | hA
    · rw [hA]
      exact fieldActor_map_normalizer σ ε
    · rw [hA]
      exact (fieldActor_map_Pst σ hf hK hσ' ε).1
    · rw [hA]
      exact (fieldActor_map_Pst σ hf hK hσ' ε).2
    · rw [hA]
      exact Subgroup.map_top_of_surjective _ (fieldActor σ ε).surjective
  have key : (P.map e.toMonoidHom).map θ'.toMonoidHom = P.map e.toMonoidHom := by
    rw [hθ'e, subgroup_map_mul_mulAut, hFA, hconjhA]
  have hPe : (P.map e.toMonoidHom).map θ'.toMonoidHom =
      (P.map θ.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hPe] at key
  have hPeq : P.map θ.toMonoidHom = P :=
    Subgroup.map_injective (f := e.toMonoidHom) e.injective key
  rw [← hPeq]
  exact Subgroup.mem_map_of_mem θ.toMonoidHom hx

end Model

theorem kDiag_of_is3D4_strong {n : ℕ} {X : Type} [Group X] [Finite X] (hX : Is3D4 X n) :
    ∀ (θ : MulAut X),
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have hX' : CFSG.Blueprint.LieModel X .trialityD4 0 2 n := hX
  have ht : (CFSG.Open.StatedLieTag.trialityD4) ∈
      CFSG.Blueprint.chevalleyExceptionalTags := by decide
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX' ht
  obtain ⟨hf, K, hfield, hfinite, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hm
  letI : Field K := hfield
  letI : Finite K := hfinite
  exact kDiag_transport_strong e (kDiag_graphFixedRootGroup_strong σ hf hK hσ)

theorem kDiag_of_is3D4 {n : ℕ} {X : Type} [Group X] [Finite X] (hX : Is3D4 X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P :=
  fun θ _ => kDiag_of_is3D4_strong hX θ

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
