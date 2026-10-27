module

public import CFSG.Milestones.ASVolI.F431.BCoreGenQ
public import CFSG.Quasithin.H13.NQCatParabolicSp4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F431.BCoreGen

public section

namespace CFSG.ASVolI

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

section OddIndex

variable {E : Type} [Group E] [Finite E]

theorem burnsideF4m_core_mem_of_odd (Gp : Subgroup E) [Gp.Normal] (hodd : Odd Gp.index)
    {x : E} {k : ℕ} (hx : x ^ 2 ^ k = 1) : x ∈ Gp := by
  have h1 : orderOf (x : E ⧸ Gp) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one])
  have h2 : orderOf (x : E ⧸ Gp) ∣ Gp.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) Gp.index :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 : orderOf (x : E ⧸ Gp) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem burnsideF4m_core_pCoreOf_le_of_odd (Gp : Subgroup E) [Gp.Normal] (hodd : Odd Gp.index)
    (M : Subgroup E) : pCoreOf 2 M ≤ Gp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact burnsideF4m_core_mem_of_odd Gp hodd hk'

end OddIndex

section Model

theorem burnsideF4m_core_oPPrime_Q2_le {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    oPPrime 2 (Q2 K j) ≤ perfectCore (Q2 K j) := by
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 2
  have hU0 : IsSylowTwoOf (unipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyP, k, hk⟩
  have hy : y ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  exact CFSG.Quasithin.H13.U4Par.le_of_isPGroup_of_sylow_le (perfectCore_le _)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _))
    (CFSG.Quasithin.H13.NQCat.Sp4.unipotent_le_perfectCore hK4 j) hU0
    (CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow hy)
    ((Subgroup.zpowers_le (H := Q2 K j)).mpr hyP) (Subgroup.mem_zpowers y)

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_core_spModel (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (θ : StatedSp 2 K →* E),
      Nat.card K = 2 ^ f ∧ Function.Injective θ ∧ θ.range = Gp ∧
        Gp ⊓ M₁ = (Q2 K 0).map θ ∧ Gp ⊓ M₂ = (Q2 K 1).map θ := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp.toHypF_4_4g
  have hK : Nat.card marking.field = 2 ^ f := by
    have := marking.field_card
    simpa using this
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have hinj : Function.Injective marking.transport := by
    refine (injective_iff_map_eq_one marking.transport).2 fun a ha => ?_
    have h3 := (burnsideF4f_transport_eq_one_iff marking a).1 ha
    exact Subtype.ext (burnsideF4gSpInv_scalar_eq_one h3 a.2)
  have hsurj := burnsideF4f_transport_surjective marking
  have keyS : ∀ (S : Set (Fin 2 ⊕ Fin 2))
      (W : Submodule marking.field (Fin 2 ⊕ Fin 2 → marking.field))
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) marking.field),
      (∀ v, v ∈ coordinateSpace S ↔ v ∈ W) →
      ((∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ W ↔ v ∈ W) := by
    intro S W A hS
    simp only [hS]
  have key : ∀ b : Bool, nativeParabolic .Sp4 (2 ^ f) marking.field marking.basis b =
      Q2 marking.field (if b then 1 else 0) := by
    intro b
    rw [hbasis]
    ext g
    have h1 : g ∈ nativeParabolic .Sp4 (2 ^ f) marking.field 1 b ↔
        (g : GL (Coord .Sp4) marking.field) ∈ rawStabilizer ((fun vector =>
            ((1 : GL (Coord .Sp4) marking.field) : Matrix (Coord .Sp4) (Coord .Sp4)
              marking.field).mulVec vector) ''
          coordinateSpace (if b then flagTwo .Sp4 else flagOne .Sp4 : Set (Coord .Sp4))) :=
      Iff.rfl
    rw [h1, burnsideF4gSp_mem_rawStabilizer, burnsideF4gSp_image_one, Q2]
    refine Iff.trans ?_
      (burnsideF4gSp_mem_stabilizer_iff (r := 2) (K := marking.field) _ g).symm
    cases b
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).1)
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).2)
  let θ : StatedSp 2 marking.field →* E := Gp.subtype.comp marking.transport
  have hθinj : Function.Injective θ := Gp.subtype_injective.comp hinj
  have hrange : θ.range = Gp := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (marking.transport y).2
    · intro hx
      obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  have hpar : ∀ (b : Bool) (M : Subgroup E), M.subgroupOf Gp = marking.parabolic b →
      Gp ⊓ M = (Q2 marking.field (if b then 1 else 0)).map θ := by
    intro b M hM
    have e1 : marking.parabolic b =
        (Q2 marking.field (if b then 1 else 0)).map marking.transport :=
      congrArg (Subgroup.map marking.transport) (key b)
    calc Gp ⊓ M = (M.subgroupOf Gp).map Gp.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      _ = ((Q2 marking.field (if b then 1 else 0)).map marking.transport).map Gp.subtype := by
          rw [hM, e1]
      _ = (Q2 marking.field (if b then 1 else 0)).map θ := Subgroup.map_map _ _ _
  exact ⟨marking.field, inferInstance, inferInstance, inferInstance, θ, hK, hθinj, hrange,
    by simpa using hpar false M₁ h1, by simpa using hpar true M₂ h2⟩

end Model

section Sp4Odd

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_sp4_core_odd [Finite E] (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    (hodd : Odd Gp.index) :
    (∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
    (∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      GLKind.Sp4 = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) ∧
    pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁) ∧ pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) ∧
    pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
  haveI := hyp.normal
  obtain ⟨K, _, _, _, θ, hKc, hθ, -, h1, h2⟩ := burnsideF4m_core_spModel hyp
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hKc]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
    exact ⟨s, hs⟩
  have hO : ∀ (j : Fin 2) {M : Subgroup E}, Gp ⊓ M = (Q2 K j).map θ →
      oPPrime 2 (Gp ⊓ M) ≤ perfectCore M := by
    intro j M hM
    have h3 : oPPrime 2 (Gp ⊓ M) ≤ perfectCore (Gp ⊓ M) := by
      rw [hM, burnsideF4gD4Inv_map_oPPrime θ hθ, burnsideF4m_perfectCore_map θ hθ]
      exact Subgroup.map_mono (burnsideF4m_core_oPPrime_Q2_le hK4 j)
    exact h3.trans (perfectCore_mono inf_le_right)
  have hZ : ∀ (j : Fin 2) {M : Subgroup E}, Gp ⊓ M = (Q2 K j).map θ →
      ∀ x ∈ centerOf (perfectCore M), x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M)) := by
    intro j M hM x hx hx2
    have hx2' : x ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hx2
    have hxG : x ∈ Gp := burnsideF4m_core_mem_of_odd Gp hodd hx2'
    have hxM : x ∈ M := perfectCore_le M hx.1
    refine ⟨burnsideF4gU4Inv_mem_oPPrime ⟨hxG, hxM⟩ hx2',
      Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hx.2 g (hO j hM hg)
  have hQ : ∀ M : Subgroup E, pCoreOf 2 M = pCoreOf 2 (Gp ⊓ M) := fun M =>
    burnsideF4m_pCoreOf_eq_inf_of_le Gp M (burnsideF4m_core_pCoreOf_le_of_odd Gp hodd M)
  exact ⟨fun x hx _ hx2 => hZ 0 h1 x hx hx2, fun x hx _ hx2 => ⟨rfl, hZ 1 h2 x hx hx2⟩,
    hQ M₁, hQ M₂, hQ (M₁ ⊓ M₂)⟩

end Sp4Odd

end CFSG.ASVolI
