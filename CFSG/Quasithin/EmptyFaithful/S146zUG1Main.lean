module

public import CFSG.Quasithin.EmptyFaithful.S146zUG1Dict
public import CFSG.Quasithin.EmptyFaithful.S146zUBFive
public import CFSG.Quasithin.EmptyFaithful.S146zUAOdd

public section

namespace CFSG.Quasithin.S146zU

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

namespace UG1

attribute [local instance] commGroupOfFact

section Defs

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

@[expose] noncomputable def F5CaseOne (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) : Prop :=
  haveI := factElem h hIU
  subM V₁ (conjClosure I H) I = ⊤ ∧
    ∃ n, IsPSL 2 2 n ↥(autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ∧
      Omega4PlusModule (autSub (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) n

@[expose] noncomputable def F5Split (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T) : Prop :=
  haveI := factElem h hIU
  UB.ModSplit (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H K)
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩) ∨
    UB.ModSplit (autIH V₁ I H (conjClosure K T))
      (conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)
        (autIH V₁ I H K))
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)⁻¹

theorem f5Split_of_not_caseOne (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T) (hcases : UB.F5Cases h hIU ht)
    (hn : ¬ F5CaseOne h hIU) : F5Split h hIU ht :=
  hcases.resolve_left hn

end Defs

section Comm

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem actH_comm_of_compPair (h : HypF918 T V L V₁ Vp H K) {A B : Subgroup G}
    (P : UA.CompPair H A B) (a b : ↥H) (ha : (a : G) ∈ A) (hb : (b : G) ∈ B) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a *
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b *
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a := by
  have : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))) :=
    ⟨h.toHypF98.toHypF91.isElemAbelian_tilde⟩
  have h1 : qPi H a * qPi H b = qPi H b * qPi H a :=
    P.comm _ (UA.qPi_mem_image ha a.2) _ (UA.qPi_mem_image hb b.2)
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ CFSG.Open.pCore 2 ↥H := by
    have h3 : qPi H (a * b * a⁻¹ * b⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h1]
      group
    exact (QuotientGroup.eq_one_iff _).mp h3
  have hpc : ((a * b * a⁻¹ * b⁻¹ : ↥H) : G) ∈ pCoreOf 2 H := ⟨_, h2, rfl⟩
  have h4 := S153M.actE_eq_one_of_mem_pCoreOf h le_rfl h.H_le_normalizer_V₁
    (h.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)) hpc
  simp only [map_mul, map_inv] at h4
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h4)

end Comm

section Main

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem hD_of_f5Split (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H)
    (hclaim : tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆)
    {s : G} (hsT : s ∈ T) (hK₂ : conjSub s K ∈ cComp H)
    (hsN : s ∉ Subgroup.normalizer (K : Set G)) (hs : IsSimpleGroup ↥(imageOTwoQuot H K))
    (hsplit : F5Split h hIU hsT) : ⁅⁅conjClosure Vp H, K⁆, conjSub s K⁆ ≤ V₁ := by
  have : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))) := factElem h hIU
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hK₂H : conjSub s K ≤ H := le_of_mem_cComp hK₂
  have hsH : s ∈ H := h.T_le_H hsT
  have hKK₀ : K ≤ conjClosure K T := le_conjClosure K T
  have hK₂K₀ : conjSub s K ≤ conjClosure K T := fun x hx => by
    have := mem_conjClosure hsT (mem_conjSub.mp hx)
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at this
  have hD : ∀ (a b : ↥H), (a : G) ∈ K → (b : G) ∈ conjSub s K →
      ∀ y : ↥(tildeOf V₁ (conjClosure Vp H)),
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b
            (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹) =
          actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹ := by
    rcases hsplit with ⟨-, hs2⟩ | ⟨-, hs2⟩
    · rw [UB.conjAutSub_autIH h hKH hsH] at hs2
      exact fun a b ha hb y => dmod_of_split h hIU hclaim (perfect_of_mem_cComp h.K_cComp) hKH
        hKK₀ hK₂H hs2 a b ha hb y
    · rw [conjAutSub_inv_conjAutSub, UB.conjAutSub_autIH h hKH hsH] at hs2
      have hne : K ≠ conjSub s K := fun h' =>
        hsN (CosetGeom.mem_normalizer_of_conjSub_eq h'.symm)
      have P : UA.CompPair H K (conjSub s K) := UA.CompPair.of_cComp h.K_cComp hK₂ hne hs
      have hcomm := fun (a b : ↥H) (ha : (a : G) ∈ conjSub s K) (hb : (b : G) ∈ K) =>
        actH_comm_of_compPair h P.symm a b ha hb
      have hD₂ := fun (a b : ↥H) (ha : (a : G) ∈ conjSub s K) (hb : (b : G) ∈ K)
          (y : ↥(tildeOf V₁ (conjClosure Vp H))) =>
        dmod_of_split h hIU hclaim (perfect_of_mem_cComp hK₂) hK₂H hK₂K₀ hKH hs2 a b ha hb y
      exact fun a b ha hb y => dmod_swap h hcomm hD₂ a b ha hb y
  exact commutator_commutator_le_of_dmod h hKH hK₂H hD

end Main

section Headline

variable {G : Type} [Group G] [Finite G]

theorem hD_of_modSplit {T M : Subgroup G} {K₁ : Subgroup G} {s : G}
    (hK₂ : conjSub s K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁)
    {I : Subgroup G} (hIU : I ≤ conjClosure (VZ T M) (mcOf T))
    (hclaim : tildeOf (quasithinOmegaOneCenter T) (conjClosure I (mcOf T)) =
      tildeOf (quasithinOmegaOneCenter T)
        ⁅conjClosure (VZ T M) (mcOf T), conjClosure K₁ T⁆)
    (hsplit : F5Split hF hIU hsT) :
    ⁅⁅uOfL22 T M, K₁⁆, conjSub s K₁⁆ ≤ quasithinOmegaOneCenter T := by
  obtain ⟨e₁⟩ := e
  obtain ⟨e₂⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hF.K_cComp)
  have := SBc16.isSimpleGroup_L216
  exact hD_of_f5Split hF hIU hclaim hsT hK₂ hsN (e₂.symm.trans e₁).isSimpleGroup hsplit

end Headline

end UG1

end CFSG.Quasithin.S146zU
