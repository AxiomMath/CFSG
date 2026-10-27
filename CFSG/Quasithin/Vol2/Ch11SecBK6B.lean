module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartF
public import CFSG.Quasithin.Vol2.Ch11SecAKA15
public import CFSG.Quasithin.Vol2.Ch10SecKHK3B
public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.Ch11SecAVi
public import CFSG.Quasithin.Vol2.Ch11SecBFacts24

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usl uSL qSp)
open CFSG.Open (pCoreOf quasithinG2)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open scoped IsMulCommutative

namespace BK6

variable {G : Type} [Group G] {L V : Subgroup G}

theorem exists_real_sl3 [Finite G] {X T V₁ V₂ : Subgroup G} {n : ℕ}
    (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSL3 L V n) :
    ∃ (_ : IsMulCommutative ↥V) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧ ∃ π : ↥(StatedSL 3 K) →* ↥(autOn L V),
        (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π := by
  obtain ⟨hcomm, hnat⟩ := hfl.nat
  refine ⟨hcomm, ?_⟩
  have hn := hfl.two_le
  rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · exact ⟨K, inferInstance, inferInstance, KGNat.charP_two_of_card (by omega) hK, hK, π, hπ⟩
  · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
    have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
    exact (SecA.kind_not_SL3_Sp4 (by omega) hk ⟨K, inferInstance, inferInstance, hK,
      ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩).elim
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
    obtain ⟨f, hf⟩ := exists_isCoord (G2Q8.lmG K) hπ
    have hbij : Function.Bijective π := by
      refine ⟨fun a b hab => ?_, hf.onto⟩
      set e := MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm with he
      obtain ⟨a', rfl⟩ := e.surjective a
      obtain ⟨b', rfl⟩ := e.surjective b
      exact congrArg e ((G2Q8.rhoG_bijective hf hc0 hc1).1
        (show G2Q8.rhoG hc0 hc1 π a' = G2Q8.rhoG hc0 hc1 π b' from hab))
    exact (SecA.kind_not_SL3_G2 KGNat.factG2DerivedOrder_holds hn hk
      ⟨K, inferInstance, inferInstance, hK, ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩).elim

theorem exists_real_sp4 [Finite G] {X T V₁ V₂ : Subgroup G} {n : ℕ}
    (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSp4 L V n) :
    ∃ (_ : IsMulCommutative ↥V) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧ ∃ π : ↥(StatedSp 2 K) →* ↥(autOn L V),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π := by
  obtain ⟨hcomm, hnat⟩ := hfl.nat
  refine ⟨hcomm, ?_⟩
  have hn := hfl.two_le
  rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
    have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
    exact (SecA.kind_not_SL3_Sp4 (by omega) ⟨K, inferInstance, inferInstance, hK,
      ⟨(MulEquiv.ofBijective π hbij).symm.trans
        (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩ hk).elim
  · exact ⟨K, inferInstance, inferInstance, KGNat.charP_two_of_card (by omega) hK, hK, π, hπ⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
    obtain ⟨f, hf⟩ := exists_isCoord (G2Q8.lmG K) hπ
    have hbij : Function.Bijective π := by
      refine ⟨fun a b hab => ?_, hf.onto⟩
      set e := MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm with he
      obtain ⟨a', rfl⟩ := e.surjective a
      obtain ⟨b', rfl⟩ := e.surjective b
      exact congrArg e ((G2Q8.rhoG_bijective hf hc0 hc1).1
        (show G2Q8.rhoG hc0 hc1 π a' = G2Q8.rhoG hc0 hc1 π b' from hab))
    exact (SecA.kind_not_Sp4_G2 KGNat.factG2DerivedOrder_holds hn hk
      ⟨K, inferInstance, inferInstance, hK, ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩).elim

theorem isFlagW_of_flag24 {X T V₁ V₂ : Subgroup G} {n : ℕ} (hfl : Flag24 L V X T V₁ V₂ n)
    {i : ℕ} {U : Subgroup G} (hUV : U ≤ V) (hCU : V ⊓ Subgroup.centralizer (L : Set G) ≤ U)
    (hst : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U)
    (hidx : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ (n * i))
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) (2 ^ n) i (U.subgroupOf V) := by
  refine ⟨fun z hz => hCU ⟨z.2, hz⟩, ?_, ?_, fun x hx => ?_⟩
  · have := (SecA.isEndStable_iff hfl.le_normalizer _ U).mp hst
    rwa [SecA.inf_centralizer_subgroupOf] at this
  · rw [← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hUV, hidx, pow_mul]
  · obtain ⟨y, hy, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hx
    exact (SecA.conjV_mem_stabW_iff hUV hyV).mpr (hTU hy.1)

variable {K : Type} [Field K] [Finite K] {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem mem_pCoreOf_of_rad2 [Finite W] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    (b c : K) :
    ((rho3 π (g * uSL 0 b c * g⁻¹) : ↥H) : MulAut W) ∈
      pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup))) := by
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hψ := Ch11.SecS.C11P9A.psiW_injective hf g
  rw [show perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)) =
      Ch11.SecS.gammaW H (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup) from rfl,
    Ch11.SecS.C11P9A.gammaW_two_eq hSL hf, Ch11.SecS.C11P9A.pCoreOf_map_of_injective _ hψ,
    Ch11.SecS.C11P9A.pCoreOf_stabRow2]
  exact ⟨uSL 0 b c, Ch11.SecS.C11P9A.mem_rad2_iff_uSL.mpr ⟨b, c, rfl⟩, rfl⟩

theorem mem_pCoreOf_of_qSp [Finite W] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) (x y z : K) :
    ((π (g * qSp x y z * g⁻¹) : ↥H) : MulAut W) ∈
      pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmapSp g (spPlane K)).toAddSubgroup))) := by
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  rw [KA.pCoreOf_gamma2_eq hf g]
  refine ⟨qSp x y z, (Ch10.SecC.C10KH.mem_pCoreOf_N1_iff hK4).mpr
    ⟨_, CFSG.ClassicalInvolution.ModelFacts.OddCover.symm3_transpose x y z, ?_⟩, rfl⟩
  apply Subtype.ext
  apply Units.ext
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.coe_tau]
  rfl

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
