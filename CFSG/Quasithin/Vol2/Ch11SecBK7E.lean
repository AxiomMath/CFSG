module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts24
public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Vol2.Ch11SecAVi
public import CFSG.Quasithin.Vol2.KGNatSp4Flag

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp specialLinearGroupEquivStatedSL)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usp)
open scoped IsMulCommutative

namespace K7

variable {G : Type} [Group G] {L V : Subgroup G}

theorem fix_of_autOn : ∀ h ∈ autOn L V,
    ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, h z = z := by
  intro h hh z hz
  obtain ⟨y, hyL, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hh
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hz
  apply Subtype.ext
  rw [SecA.conjV_apply_coe, hz y hyL, mul_inv_cancel_right]

theorem commV_autOn_eq_top [IsMulCommutative ↥V] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hc : ⁅V, L⁆ = V) : commV (autOn L V) = ⊤ := by
  rw [Ch10.SecA.commV_autOn_eq hLV, hc, Subgroup.subgroupOf_self]

theorem exists_coord_flag24 [Finite G] {X T V₁ V₂ : Subgroup G} {n : ℕ}
    (hfl : Flag24 L V X T V₁ V₂ n) (hk : KindSp4 L V n) :
    ∃ (_ : IsMulCommutative ↥V) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(StatedSp 2 K) →* ↥(autOn L V)) (f : ↥V → (Fin 2 ⊕ Fin 2 → K))
        (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L V)
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) (g : StatedSp 2 K),
        (∀ x : MulAut ↥V, x ∈ autOn (T ⊓ L) V ↔
          ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L V)) : MulAut ↥V)) ∧
        V₁.subgroupOf V = hf.pre (gmapSp g (spLine K)).toAddSubgroup ∧
        V₂.subgroupOf V = hf.pre (gmapSp g (spPlane K)).toAddSubgroup := by
  obtain ⟨hcomm, hnat⟩ := hfl.nat
  refine ⟨hcomm, ?_⟩
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hn := hfl.two_le
  have hLV := hfl.le_normalizer
  have h₁ : V₁ ≤ V := hfl.le₁₂.trans hfl.le₂
  obtain ⟨K, _, _, hK, π, hπ⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥(StatedSp 2 K) →* ↥(autOn L V),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π := by
    rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | h | ⟨K, _, _, hK, π, hπ⟩
    · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
      have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
      exact (SecA.kind_not_SL3_Sp4 (by omega) ⟨K, inferInstance, inferInstance, hK,
        ⟨(MulEquiv.ofBijective π hbij).symm.trans
          (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩ hk).elim
    · exact h
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
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hTL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hfl.sylow le_sup_left (sup_le Subgroup.le_normalizer hfl.T_le_L)
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf
    (SecA.isSylowTwoOf_autOn hLV hTL)
  have hflag : ∀ {i : ℕ} {U : Subgroup G}, U ≤ V →
      V ⊓ Subgroup.centralizer (L : Set G) ≤ U →
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U →
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ (n * i) →
      T ≤ Subgroup.normalizer (U : Set G) →
      ∃ S : Submodule K (Fin 2 ⊕ Fin 2 → K), UStableSp S ∧ Nat.card S = Nat.card K ^ i ∧
        U.subgroupOf V = hf.pre (gmapSp g S).toAddSubgroup := by
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
    exact exists_eq_pre_of_isFlagW_sp hsq hf hg hFW
  obtain ⟨S₁, hS₁, hc₁, hV₁⟩ := hflag h₁ hfl.cV_le hfl.stable₁ (by rw [hfl.index₁, mul_one])
    hfl.T_le_V₁
  obtain ⟨S₂, hS₂, hc₂, hV₂⟩ := hflag hfl.le₂ (hfl.cV_le.trans hfl.le₁₂) hfl.stable₂
    hfl.index₂ hfl.T_le_V₂
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, π, f, hf, g, hg, ?_, ?_⟩
  · rw [hV₁, (eq_std_of_stable_sp hS₁).1 (by rw [hc₁, pow_one])]
  · rw [hV₂, (eq_std_of_stable_sp hS₂).2.1 hc₂]

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
