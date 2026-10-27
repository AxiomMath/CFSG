module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecAVi
public import CFSG.Quasithin.Vol2.Ch11SecBFacts21

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

theorem exists_coord_G2 {G : Type} [Group G] [Finite G] {L V T : Subgroup G} {n : ℕ}
    (hV : IsElemAbelian 2 V) (hn : 2 ≤ n) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hnat : SecB.NatModuleOf L V n) (hkind : KindG2 L V n)
    (hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (_ : IsMulCommutative ↥V) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧
      ∃ (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)) (f : ↥V → (Ix3 → K))
        (hf : IsCoord (lmG K) (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
        (c₀ : K) (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (g : ↥(cayleyGroup K)),
        (∀ x : MulAut ↥V, x ∈ autOn (T ⊓ L) V ↔
          ∃ u ∈ U0 K, x = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥(autOn L V)) : MulAut ↥V)) ∧
        ∀ {i : ℕ} {U : Subgroup G}, U ≤ V → V ⊓ Subgroup.centralizer (L : Set G) ≤ U →
          IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U →
          (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ (n * i) →
          T ≤ Subgroup.normalizer (U : Set G) →
          U.subgroupOf V = hf.pre (gmapG g (stdF K i)).toAddSubgroup := by
  obtain ⟨hcomm, hnat⟩ := hnat
  refine ⟨hcomm, ?_⟩
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  obtain ⟨K, _, _, hK, π, hπ⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V),
        (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π := by
    rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | hG2
    · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
      have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
      exact (SecA.kind_not_SL3_G2 KGNat.factG2DerivedOrder_holds hn
        ⟨K, inferInstance, inferInstance, hK,
          ⟨(MulEquiv.ofBijective π hbij).symm.trans
            (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩ hkind).elim
    · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
      have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
      exact (SecA.kind_not_Sp4_G2 KGNat.factG2DerivedOrder_holds hn
        ⟨K, inferInstance, inferInstance, hK, ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩
        hkind).elim
    · exact hG2
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1
    (SecA.isSylowTwoOf_autOn hLV hTL')
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, π, f, hf, c₀, hc0, hc1, g, hg, ?_⟩
  intro i U hUV hCU hst hidx hTU
  have hFW : SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) (Nat.card K) i (U.subgroupOf V) := by
    refine ⟨fun z hz => hCU ⟨z.2, hz⟩, ?_, ?_, fun x hx => ?_⟩
    · have := (SecA.isEndStable_iff hLV _ U).mp hst
      rwa [SecA.inf_centralizer_subgroupOf] at this
    · rw [← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hUV, hidx, hK,
        pow_mul]
    · obtain ⟨y, hy, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hx
      exact (SecA.conjV_mem_stabW_iff hUV hyV).mpr (hTU hy.1)
  obtain ⟨S, hS, hc, hU⟩ := exists_eq_preG_of_isFlagW hsq hf hc0 hc1 hg hFW
  rw [hU, eq_stdF_of_card hS hc]

end CFSG.Quasithin.Vol2.Ch11.G2Q8
