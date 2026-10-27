module

public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.AlternatingBranch
public import CFSG.OddTranspositions.TheoremTwo.ThirdKindExclusion
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.LinearBranches

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]
variable {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem Config.exists_mulEquiv_psl225
    (hQ : Config D u w v z a K₁ S')
    (h48 : S' ⊓ Subgroup.centralizer (thirdK D z : Set G) = Subgroup.zpowers z) :
    ∃ L : Subgroup G, L.Normal ∧ L.index = 2 ∧ z ∉ L ∧ K₁ ≤ L ∧ (∀ d ∈ D, d ∉ L) ∧
      Subgroup.centralizer (L : Set G) = ⊥ ∧ Nonempty (L ≃* PSL225) := by
  classical
  obtain ⟨L, hLn, hL2, hzL, hK₁L, hDL, hdih, hab⟩ := hQ.exists_index_two h48
  haveI := hLn
  obtain ⟨eK⟩ := hQ.K₁_A5
  have hdihL : HasDihedralSylowTwo L := fun S => ⟨2, by norm_num, hdih S⟩
  have hGW := CFSG.GorensteinWalter.gorensteinWalter L hdihL
  have hO := pPrimeCore_eq_bot_of_rad (L := L) hQ.rad
  let eQ : (L ⧸ CFSG.pPrimeCore 2 L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  refine ⟨L, hLn, hL2, hzL, hK₁L, hDL, ?_⟩
  cases hGW with
  | quotientIsTwoGroup _ h =>
    exfalso
    have hL2g : IsPGroup 2 L := h.of_equiv eQ
    obtain ⟨k, hk⟩ := hL2g.exists_card_eq
    have h60 : 60 ∣ Nat.card L := by
      have := Subgroup.card_dvd_of_le hK₁L
      rwa [Nat.card_congr eK.toEquiv,
        show Nat.card (alternatingGroup (Fin 5)) = 60 by rw [Nat.card_eq_fintype_card]; rfl]
        at this
    rw [hk] at h60
    have h3 : 3 ∣ 2 ^ k := (show 3 ∣ 60 by norm_num).trans h60
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  | quotientIsASeven _ he =>
    obtain ⟨e7⟩ := he
    exact (hQ.false_of_A7 hL2 hzL hK₁L hDL (eQ.symm.trans e7)).elim
  | quotientHasLinearNormalSubgroup _ K hK L' hL'n hL'idx hmodel =>
    set N' : Subgroup L := L'.map (eQ : _ →* L)
    have hN'n : N'.Normal := hL'n.map _ eQ.surjective
    have hN'idx : N'.index = L'.index := Subgroup.index_map_equiv L' eQ
    have eN'L' : N' ≃* L' := (Subgroup.equivMapOfInjective L' _ eQ.injective).symm
    set N₀ : Subgroup G := N'.map L.subtype
    have hN₀L : N₀ ≤ L := Subgroup.map_subtype_le N'
    have hsub : N₀.subgroupOf L = N' :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective N'
    have hN₀n : (N₀.subgroupOf L).Normal := hsub ▸ hN'n
    have hodd : Odd (N₀.relIndex L) := by
      rw [Subgroup.relIndex, hsub, hN'idx]; exact hL'idx
    have eN₀N' : N₀ ≃* N' := (Subgroup.equivMapOfInjective N' _ L.subtype_injective).symm
    rcases hmodel with ⟨⟨eP⟩⟩ | ⟨⟨eP⟩⟩
    · obtain ⟨heq, hC, ⟨e25⟩⟩ := hQ.eq_of_normal_psl2 hL2 hK₁L hN₀L hN₀n hodd hK
        ((eN₀N'.trans eN'L').trans eP)
      exact heq ▸ ⟨hC, ⟨e25⟩⟩
    · exact (false_of_normal_pgl2 hab hN₀L hN₀n hodd hK ((eN₀N'.trans eN'L').trans eP) hK₁L
        ⟨eK⟩).elim

theorem Config.isO4Minus5Pair
    (hQ : Config D u w v z a K₁ S')
    (h48 : S' ⊓ Subgroup.centralizer (thirdK D z : Set G) = Subgroup.zpowers z) :
    IsO4Minus5Pair G D := by
  obtain ⟨L, hLn, hL2, hzL, hK₁L, hDL, hCL, ⟨eL⟩⟩ := hQ.exists_mulEquiv_psl225 h48
  obtain ⟨hz2, -, -, -, -, -⟩ := hQ.z_facts
  haveI := hLn
  exact isO4Minus5Pair_of_mulEquiv_psl225 hL2 eL hCL hz2 hzL hK₁L hQ.K₁_A5 hQ.K₁_comm
    hQ.setup.isClass (fun d hd => hQ.mul_self_of_mem_D hd) hDL


theorem theoremFourNineStatement_holds :
    TheoremFourNineStatement :=
  fun _ _ _ _ _ _ _ _ _ _ _ hQ h48 => hQ.isO4Minus5Pair h48

end CFSG.OddTranspositions.QZ
