module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinB
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Quasithin.Background.E2TwoProofBar
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.EmptyFaithful.E22PTypeII

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem isTwoClosed_pCore (H : Subgroup G) : E1.IsTwoClosed (CFSG.pCore 2 ↥H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(CFSG.pCore 2 ↥H) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup (r := 2)
  refine ⟨CFSG.pCore 2 ↥H, ⟨le_rfl, hP, ?_⟩, ?_⟩
  · rw [Subgroup.relIndex_self]
    norm_num
  · rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top

theorem isE_two {H T A H₁ : Subgroup G} (hH₁ : H₁ ≤ H) (hAT : A ≤ T) (hAH₁ : A ≤ H₁)
    (hT₁ : IsSylowIn 2 (T ⊓ H₁) H₁) (hτ : E1.tauOf H T A ≤ H₁)
    (hpsl : IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H₁ ⧸ CFSG.pCore 2 ↥H₁))))
    (hA : ¬ A ≤ pCoreOf 2 H₁)
    (hA4 : Nat.card ↥((A.subgroupOf H₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H₁))) ≤ 4) :
    E1.IsE 2 H T A H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥H₁) with hφdef
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  set K := oTwoUpper (⊤ : Subgroup (↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) with hKdef
  have hKn : K.Normal := oTwoUpper_top_normal
  have hs : IsSimpleGroup ↥K := isSimpleGroup_of_isPSL hpsl
  have hnc := nonabelian_of_isPSL hpsl
  have hO := E2P.open_pCore_bar H₁
  have hC := centralizer_oTwoUpper_eq_bot hO hs hnc
  set S := (T ⊓ H₁).subgroupOf H₁ with hSdef
  set B := A.subgroupOf H₁ with hBdef
  have hS : IsSylowIn 2 S ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) inf_le_right le_rfl).2 hT₁
    rwa [Subgroup.subgroupOf_self] at h
  have hBS : B ≤ S := fun x hx => ⟨hAT hx, x.2⟩
  have hker : φ.ker = CFSG.pCore 2 ↥H₁ := QuotientGroup.ker_mk' _
  have hPS : CFSG.pCore 2 ↥H₁ ≤ S := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 H₁ := ⟨x, by exact hx, rfl⟩
    have hT₁' : QuasithinUnique.IsSylowTwoOf (T ⊓ H₁) H₁ := ⟨hT₁.le, hT₁.isPGroup, hT₁.2.2⟩
    exact pCoreOf_two_le_of_isSylowTwoOf hT₁' hx'
  have hZ : E1.IsTwoClosed ((CFSG.Open.pCore 2 (↥H₁ ⧸ CFSG.pCore 2 ↥H₁)).comap φ) := by
    rw [hO, MonoidHom.comap_bot, hker]
    exact isTwoClosed_pCore H₁
  have hres : twoResidual (⊤ : Subgroup ↥H₁) = perfectCore (⊤ : Subgroup ↥H₁) := by
    refine E1.twoResidual_eq_perfectCore_of_surjective φ hφ hS (fun M hSM hM => ?_)
      (twoResidual_eq_perfectCore_of_simple hs hnc)
    rw [hker, sup_of_le_left (hPS.trans hSM)] at hM
    exact hM
  have hBne : B.map φ ≠ ⊥ := by
    intro hB
    apply hA
    intro a ha
    have hmem : (⟨a, hAH₁ ha⟩ : ↥H₁) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have : φ ⟨a, hAH₁ ha⟩ ∈ B.map φ := ⟨⟨a, hAH₁ ha⟩, ha, rfl⟩
      rwa [hB, Subgroup.mem_bot] at this
    rw [hker] at hmem
    exact ⟨_, by exact hmem, rfl⟩
  have hE2 : E1.ETwo ↥H₁ S B :=
    E1.eTwo_of_surjective φ hφ hZ hS.isPGroup hBS hres
      (E1.eTwo_of_normal_simple K (S.map φ) (B.map φ) hnc hC (E1.isSylowIn_two_map_top hφ hS)
        (oTwoUpper_top_sup_eq_top (E1.isSylowIn_two_map_top hφ hS)) hBne)
  have hcard : Nat.card ↥(E1.barRad ↥H₁ B) ≤ 2 ^ 2 := by
    have hR := E1.solvableRadical_eq_bot_of_normal_simple K hnc hC
    have hP2 : IsPGroup 2 ↥(φ.ker) := by
      rw [hker]
      exact CFSG.LieType.BorelTits.pCore_isPGroup (r := 2)
    have h1 := E1.card_barRad_eq_of_surjective φ hφ (E1.isSolvable_of_isPGroup_two hP2) B
    rw [← h1]
    have hinj : Function.Injective
        (QuotientGroup.mk' (CFSG.solvableRadical (↥H₁ ⧸ CFSG.pCore 2 ↥H₁))) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hR])
    have h2 : Nat.card ↥(E1.barRad (↥H₁ ⧸ CFSG.pCore 2 ↥H₁) (B.map φ)) =
        Nat.card ↥(B.map φ) :=
      Subgroup.card_map_of_injective hinj
    rw [h2]
    exact hA4.trans (by norm_num)
  exact ⟨hH₁, le_inf (E1.tauOf_le H T A) hτ, hT₁, Or.inr ⟨hE2, hcard⟩⟩

end S127

end CFSG.Quasithin.H13
