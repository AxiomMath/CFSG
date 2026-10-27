module

public import CFSG.Quasithin.Background.C35Setup
public import CFSG.Quasithin.Background.C41PfK
public import CFSG.Quasithin.H13.InspC33Holds
public import CFSG.Quasithin.H13.L32NA3SQTK
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI.ChC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure SetC31 (H R M L V T K : Subgroup G) : Prop where
  hyp : HypC28 H R M L V
  comp : CFSG.Open.IsComponentOf K H
  sylow : IsSylowTwoOf T M
  le_T : R ≤ T
  norm : conjClosure L M ≤ Subgroup.normalizer (K : Set G)
  red : H = conjClosure L M ⊔ conjClosure K T ⊔ T

end CFSG.ASVolI.ChC

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def C_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V K : Subgroup G), HypC28 H R M L V →
    CFSG.Open.IsComponentOf K H →
    L = conjClosure L M ∧ ((conjClosure L M).subgroupOf M).Normal ∧ conjClosure L M ≤ K ∧
      M ≤ Subgroup.normalizer (K : Set G) ∧ IsPGroup 2 ↥(centerOf K) ∧
      (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case3 H R M L V K ∨
        C31Case4 H R M L V K ∨ C31Case5 H R M L V K ∨ C31Case6 H R M L V K ∨
        C31Case7 H R M L V K ∨ C31Case8 H R M L V K ∨ C31Case9 H R M L V K ∨
        C31Case10 H R M L V K)

@[expose] def C_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC31 H R M L V T K →
    ∃ K' : Subgroup G, (∃ h ∈ H, K' = conjByElt h K) ∧ L ≤ K' ∧
      conjClosure L M ≤ conjClosure K' T

section BurnsideC33

private theorem burnsideC33_le_normalizer_of_eq_conjClosure {G : Type} [Group G] {K T : Subgroup G}
    (h : K = CFSG.Quasithin.conjClosure K T) : T ≤ Subgroup.normalizer (K : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ K, t * x * t⁻¹ ∈ K := by
    intro t ht x hx
    have h1 : t * x * t⁻¹ ∈ CFSG.Quasithin.conjClosure K T :=
      CFSG.Quasithin.mem_conjClosure ht hx
    rwa [← h] at h1
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key t ht x hx, fun hx => ?_⟩
  have h2 := key t⁻¹ (T.inv_mem ht) _ hx
  have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
  rwa [e] at h2

end BurnsideC33

section

theorem as_C_3_2
    : C_3_2 := by
  intro G _ _ H R M L V T K hS
  have hA37 := CFSG.Quasithin.H13.a3ForSQTK_holds.1
  have hA38 := CFSG.Quasithin.H13.a3ForSQTK_holds.2.1
  have hA3 : CFSG.Quasithin.A3Orbits G := CFSG.Quasithin.a3Orbits_of_a37_a38 hA37 hA38
  have hSch : ∀ K : Subgroup G, CFSG.Quasithin.IsSQTKIn K →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      CFSG.Quasithin.OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
    fun K hK hq => CFSG.Quasithin.C41Pf.outSolvable_of_isSQTKIn K hK hq
  have hbasic := CFSG.Quasithin.C31B.c31BasicStep_of CFSG.Quasithin.H13.VolI.a36ForSQTK_holds
    hA38 hA3 hSch CFSG.Quasithin.H13.InspC33P.inspC33_holds H R M L V K hS.hyp hS.comp
  refine ⟨K, ⟨1, H.one_mem, ?_⟩, (CFSG.Quasithin.le_conjClosure L M).trans hbasic.1,
    hbasic.1.trans (CFSG.Quasithin.le_conjClosure K T)⟩
  ext x
  rw [CFSG.Quasithin.mem_conjByElt]
  simp

end

@[expose] def C_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC31 H R M L V T K →
    L ≤ K → conjClosure L M ≤ conjClosure K T → K = conjClosure K T

section

theorem as_C_3_3
    : C_3_3 := by
  intro G _ _ H _ _ _ _ T K hS _ _
  have hA37 := CFSG.Quasithin.H13.a3ForSQTK_holds.1
  have hA38 := CFSG.Quasithin.H13.a3ForSQTK_holds.2.1
  have hA3 : CFSG.Quasithin.A3Orbits G := CFSG.Quasithin.a3Orbits_of_a37_a38 hA37 hA38
  have hSch : ∀ K : Subgroup G, CFSG.Quasithin.IsSQTKIn K →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      CFSG.Quasithin.OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
    fun K hK hq => CFSG.Quasithin.C41Pf.outSolvable_of_isSQTKIn K hK hq
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.Quasithin.C31B.le_normalizer CFSG.Quasithin.H13.VolI.a36ForSQTK_holds hA38 hA3 hSch
      CFSG.Quasithin.H13.InspC33P.inspC33_holds hS.hyp hS.comp
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := hS.sylow.1.trans (hS.hyp.le_H.trans hHN)
  refine le_antisymm (CFSG.Quasithin.le_conjClosure K T) ?_
  exact CFSG.Quasithin.conjClosure_le fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (hTN ht) x).mp hx

end

@[expose] def C_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC31 H R M L V T K →
    L ≤ K → K = conjClosure K T →
    V ≤ R ⊓ K ∧ ¬ V ≤ Subgroup.centralizer (K : Set G)

theorem as_C_3_4 : C_3_4 := by
  intro G _ _ H _ M L _ T K hS hLK hKT
  have hTN := burnsideC33_le_normalizer_of_eq_conjClosure hKT
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hS.red]
    refine sup_le (sup_le hS.norm ?_) hTN
    rw [← hKT]
    exact Subgroup.le_normalizer
  have hMN : M ≤ Subgroup.normalizer (K : Set G) := hS.hyp.le_H.trans hHN
  have hM0K : CFSG.Quasithin.conjClosure L M ≤ K :=
    CFSG.Quasithin.conjClosure_le fun m hm l hl =>
      (Subgroup.mem_normalizer_iff.mp (hMN hm) l).mp (hLK hl)
  exact ⟨le_inf (CFSG.Quasithin.C35.V_le_R hS.hyp) (hS.hyp.V_le.trans hM0K),
    CFSG.Quasithin.C31B.not_le_centralizer hS.hyp hS.comp⟩

@[expose] def C_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC31 H R M L V T K →
    L ≤ K → K = conjClosure K T →
    (CFSG.Blueprint.EvenLieType (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 6 (↥K ⧸ Subgroup.center ↥K) ∨
      IsPSU 3 3 1 (↥K ⧸ Subgroup.center ↥K)) →
    (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case10 H R M L V K)

end CFSG.ASVolI
