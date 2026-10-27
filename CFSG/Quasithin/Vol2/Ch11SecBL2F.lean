module

public import CFSG.Quasithin.Vol2.Ch11SecBDerived35L2
public import CFSG.Quasithin.Vol2.Ch11SecBNPStar
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_centralizer_of_isTwoReducedIn {H K T V : Subgroup G} (hV : IsTwoReducedIn H V)
    (hHK : H = K ⊔ T) (hT : IsPGroup 2 T) (hKV : K ≤ Subgroup.centralizer (V : Set G)) :
    H ≤ Subgroup.centralizer (V : Set G) := by
  have hKH : K ≤ H := by rw [hHK]; exact le_sup_left
  have hTH : T ≤ H := by rw [hHK]; exact le_sup_right
  refine hV.2.2.2 H le_rfl Subgroup.le_normalizer fun h hh => ?_
  set N : Subgroup ↥H := (H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H with hN
  have hNn : N.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨H.mul_mem (H.mul_mem g.2 hx.1) (H.inv_mem g.2), ?_⟩
    show (g : G) * (x : G) * (g : G)⁻¹ ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : (g : G)⁻¹ * v * (g : G) ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hV.2.1 (H.inv_mem g.2)) v).mp hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
    calc v * ((g : G) * x * (g : G)⁻¹) = (g : G) * (((g : G)⁻¹ * v * (g : G)) * x) * (g : G)⁻¹ := by
          group
      _ = (g : G) * (x * ((g : G)⁻¹ * v * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = (g : G) * x * (g : G)⁻¹ * v := by group
  set T' : Subgroup ↥H := T.subgroupOf H with hT'
  have hT'2 : IsPGroup 2 ↥T' := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hKN : K.subgroupOf H ≤ N := fun x hx => by
    rw [hN, Subgroup.mem_subgroupOf]
    exact ⟨x.2, hKV (Subgroup.mem_subgroupOf.mp hx)⟩
  have htop : (⊤ : Subgroup ↥H) ≤ N ⊔ T' := by
    have h1 : K.subgroupOf H ⊔ T' = ⊤ := by
      rw [hT', ← Subgroup.subgroupOf_sup hKH hTH, ← hHK, Subgroup.subgroupOf_self]
    rw [← h1]
    exact sup_le_sup_right hKN T'
  obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal hT'2 (⟨h, hh⟩ : ↥H) (htop trivial)
  refine ⟨e, ?_⟩
  rw [hN, Subgroup.mem_subgroupOf] at he
  simpa using he.2

theorem l2Faithful_holds : L2Faithful := by
  intro G _ _ T L I n H K k hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hST⟩ := exists_sylow_coe_eq hS.hyp.fsu.sylow
  subst hST
  have hEven := hS.hyp.fsu.qtke.2.1
  have hH : InH (S : Subgroup G) H := hS.hstar.1
  have hTS : IsSylowTwoOf (S : Subgroup G) H := isSylowTwoOf_of_sylow_le S hH.1
  have hF : CharTwo H := charTwo_of_inH hEven S hH
  set Z := quasithinOmegaOneCenter (S : Subgroup G) with hZ
  obtain ⟨-, -, hV⟩ := conjClosure_isTwoReducedIn_of_charTwo hTS hF (le_refl Z)
  refine isFaithfulLocal_of_commutator_ne_bot hEven S hH hS.comp hV fun hVK => hS.moves ?_
  have hKV : K ≤ Subgroup.centralizer (conjClosure Z H : Set G) := by
    rw [Subgroup.commutator_comm] at hVK
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVK
  have hHV := le_centralizer_of_isTwoReducedIn hV hS.gen S.isPGroup' hKV
  have hZH : Z ≤ Subgroup.centralizer (H : Set G) :=
    (le_conjClosure Z H).trans (Subgroup.le_centralizer_iff.mp hHV)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZH

end CFSG.Quasithin.Vol2.Ch11.SecB
