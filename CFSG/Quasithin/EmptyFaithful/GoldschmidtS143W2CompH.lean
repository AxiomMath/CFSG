module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompG
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompAbs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

section Gen

variable {G : Type*} [Group G] {H L : Subgroup G}

theorem conj_mem_inf_centralizer (hLN : H ≤ Subgroup.normalizer (L : Set G)) {u k : G} (hu : u ∈ H)
    (hk : k ∈ H ⊓ Subgroup.centralizer (L : Set G)) :
    u * k * u⁻¹ ∈ H ⊓ Subgroup.centralizer (L : Set G) := by
  refine ⟨H.mul_mem (H.mul_mem hu hk.1) (H.inv_mem hu), Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro l hl
  have hl' : u⁻¹ * l * u ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hLN (H.inv_mem hu)) l).mp hl
    simpa using this
  have := Subgroup.mem_centralizer_iff.mp hk.2 _ hl'
  calc l * (u * k * u⁻¹) = u * ((u⁻¹ * l * u) * k) * u⁻¹ := by group
    _ = u * (k * (u⁻¹ * l * u)) * u⁻¹ := by rw [this]
    _ = (u * k * u⁻¹) * l := by group

end Gen

section Gw

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {L : Subgroup G}

theorem not_mem_centralizer_z (h : Ctx T M g A t d x) (hL : IsComponentIn L (Gw d x)) :
    d * d ∉ Subgroup.centralizer (L : Set G) := by
  intro hzc
  have hact := (lemma115Hyp_Gw h).component_action hL
  have hcomm : ⁅L, Subgroup.zpowers (d * d)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_left (show Commute (d * d) l from
      (Subgroup.mem_centralizer_iff.mp hzc l hl).symm) k).eq
  rw [hcomm] at hact
  exact ne_bot_of_isComponentIn hL hact.2.1.symm

theorem inf_centralizer_eq_pCoreOf (h : Ctx T M g A t d x) (hf : LocalFacts T d x)
    (hL : IsComponentIn L (Gw d x)) (hLN : Gw d x ≤ Subgroup.normalizer (L : Set G)) :
    Gw d x ⊓ Subgroup.centralizer (L : Set G) = pCoreOf 2 (Gw d x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf (pCoreOf_le 2 _) (pCoreOf_le_centralizer_of_isComponentIn hL))
  set Z : Subgroup G := Gw d x ⊓ Subgroup.centralizer (L : Set G) with hZdef
  have hZGw : Z ≤ Gw d x := inf_le_left
  have hZn : ∀ u ∈ Gw d x, ∀ k ∈ Z, u * k * u⁻¹ ∈ Z := fun u hu k hk =>
    conj_mem_inf_centralizer hLN hu hk
  have hz : d * d ∉ Z := fun hzZ => not_mem_centralizer_z h hL hzZ.2
  have hwZ : wOfX d x ∈ Z := ⟨h.w_mem_Gw, Subgroup.mem_centralizer_iff.mpr fun l hl =>
    mem_Gw_iff.mp (hL.1 hl)⟩
  have hZnorm : (Z.subgroupOf (Gw d x)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZGw]
    intro k u hk hu
    exact hZn u hu k hk
  have hO : CFSG.pPrimeCore 2 ↥(Gw d x) = ⊥ := by
    have := oddCore_Gw h
    rw [oddCoreIn_eq_map] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Gw d x).subtype_injective).mp this
  have hno : ∀ K : Subgroup ↥(Gw d x), CFSG.IsComponent K → ¬ K ≤ Z.subgroupOf (Gw d x) := by
    intro K hK hKZ
    refine not_component_le h hf.wp0 hZGw hZn hz hwZ (isComponentIn_map hK) ?_
    calc K.map (Gw d x).subtype ≤ (Z.subgroupOf (Gw d x)).map (Gw d x).subtype :=
          Subgroup.map_mono hKZ
      _ = Z := Subgroup.map_subgroupOf_eq_of_le hZGw
  have hwP : (⟨wOfX d x, h.w_mem_Gw⟩ : ↥(Gw d x)) ∈ CFSG.pCore 2 ↥(Gw d x) := by
    have := hf.wp1.w_mem_P (Subgroup.mem_zpowers (wOfX d x))
    rw [pCoreOf_eq_map_pCore] at this
    obtain ⟨p, hp, hpw⟩ := this
    have : p = ⟨wOfX d x, h.w_mem_Gw⟩ := Subtype.ext hpw
    rwa [← this]
  have hPcard : Nat.card (CFSG.pCore 2 ↥(Gw d x)) ≤ 4 := by
    have := hf.wp1.card_P
    rw [pCoreOf_eq_map_pCore, Subgroup.card_map_of_injective (Gw d x).subtype_injective] at this
    exact this
  have hle := le_pCore_of_no_component (Z := Z.subgroupOf (Gw d x)) hO hno
    (w := ⟨wOfX d x, h.w_mem_Gw⟩) (fun g' => Subtype.ext (mem_Gw_iff.mp g'.2))
    (fun h1 => h.w_ne (congrArg Subtype.val h1)) hwP hPcard
  intro k hk
  rw [pCoreOf_eq_map_pCore]
  exact ⟨⟨k, hZGw hk⟩, hle (Subgroup.mem_subgroupOf.mpr hk), rfl⟩

end Gw

end InspW2

end S143

end CFSG.Quasithin
