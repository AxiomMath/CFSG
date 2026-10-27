module

public import CFSG.Quasithin.Background.RonanE43M12
public import CFSG.Quasithin.Background.RonanE43Normal
public import CFSG.Quasithin.Background.RonanE43Central
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12CoverRow
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelTrivialBridge

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.RankThree.PerfectCover
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem conjNormal_mem_center {L : Subgroup G} [L.Normal] (g : G) {z : ↥L}
    (hz : z ∈ Subgroup.center ↥L) : MulAut.conjNormal g z ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro w
  obtain ⟨w', rfl⟩ := (MulAut.conjNormal g).surjective w
  rw [← map_mul, ← map_mul, hz w']


theorem center_eq_bot_of_M12 (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {L : Subgroup G}
    (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (h : IsSporadic .M12 (↥L ⧸ Subgroup.center ↥L)) : Subgroup.center ↥L = ⊥ := by
  haveI hK : L.Normal := normal_of_generalizedFitting hLF
  haveI : Group.IsPerfect ↥L := hLq.1
  obtain ⟨e⟩ := h
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := e
  haveI : Group.IsPerfect (↥L ⧸ Subgroup.center ↥L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ Subgroup.center ↥L :=
    (QuotientGroup.ker_mk' _).le
  have hdvd := card_ker_dvd_card_hopfMultiplier (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _) hker
  have hrow : Nat.card (hopfMultiplier ↥CFSG.Blueprint.NativeSporadic.M12) = 2 := nativeRow_M12
  rw [QuotientGroup.ker_mk', card_hopfMultiplier_congr e', hrow] at hdvd
  have hZpos : 0 < Nat.card (Subgroup.center ↥L) := Nat.card_pos
  have hZle : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 2 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rcases hZle with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (show 2 ∣ Nat.card (Subgroup.center ↥L) by
      rw [h2])
    set z₀ : ↥L := (z : ↥L) with hz₀
    have hzc : z₀ ∈ Subgroup.center ↥L := z.2
    have hzord : orderOf z₀ = 2 := by rw [hz₀, Subgroup.orderOf_coe]; exact hz
    have hZeq : Subgroup.center ↥L = Subgroup.zpowers z₀ := by
      symm
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzc) ?_
      rw [h2, Nat.card_zpowers, hzord]
    have hzG : ((z₀ : ↥L) : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hw : MulAut.conjNormal g z₀ ∈ Subgroup.zpowers z₀ := by
        rw [← hZeq]; exact conjNormal_mem_center g hzc
      have hw1 : MulAut.conjNormal g z₀ ≠ 1 := by
        intro h1
        have : z₀ = 1 := (MulAut.conjNormal g).injective (h1.trans (map_one _).symm)
        rw [this, orderOf_one] at hzord; omega
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hk' : MulAut.conjNormal g z₀ = z₀ := by
        rw [← hk, ← zpow_mod_orderOf, hzord] at hw1 ⊢
        rcases Int.emod_two_eq_zero_or_one k with h0 | h0
        · rw [show k % ((2 : ℕ) : ℤ) = 0 from h0] at hw1
          simp at hw1
        · rw [show k % ((2 : ℕ) : ℤ) = 1 from h0]; simp
      have hval := congrArg (fun x : ↥L => (x : G)) hk'
      simp only [MulAut.conjNormal_apply] at hval
      calc g * ((z₀ : ↥L) : G) = g * ((z₀ : ↥L) : G) * g⁻¹ * g := by group
        _ = ((z₀ : ↥L) : G) * g := by rw [hval]
    have hcop := coprime_card_center_of_pCore_bot hO2
      (K := Subgroup.zpowers ((z₀ : ↥L) : G)) (Subgroup.zpowers_le.mpr hzG)
    have hcard : Nat.card (Subgroup.zpowers ((z₀ : ↥L) : G)) = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hzord]
    rw [hcard] at hcop
    exact absurd hcop (by norm_num)



theorem e43_M12 (V : Type) [CommGroup V] [Finite V] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T L : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hlt : fixV ρ.range < fixV (T.map ρ))
    (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (h : IsSporadic .M12 (↥L ⧸ Subgroup.center ↥L)) : aParam ρ.range ≤ 2 := by
  classical
  haveI : L.Normal := normal_of_generalizedFitting hLF
  have hZ := center_eq_bot_of_M12 hO2 hLF hLq h
  have hLT : L ⊔ T = ⊤ := sup_eq_top_of_index_le_two hT (index_le_two_of_M12 hLF hLq h)
  obtain ⟨e⟩ := h
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := e
  let ε : ↥L ≃* ↥CFSG.Quasithin.E2P.SporB.m12Grp :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e').trans
      (MulEquiv.subgroupCongr
        CFSG.QuasithinUnique.Vol2Native.A312L.M12Lat.mGens_closure).symm
  obtain ⟨U, P, P', hU, hUc, hUP, hUP', hPc, hP'c, hPP', hinv⟩ :=
    CFSG.Quasithin.E2P.SporB.m12_pair_data
  have hmain := aParam_le_of_normal_family V ρ hρ hO2 hT hLF hLq hLT hlt ε hU {P, P'}
    ⟨P, by simp⟩ (by
      intro Y hY
      simp only [Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl
      · exact hUP
      · exact hUP') (by
      intro Y hY
      simp only [Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl
      · rw [hPc, hUc]
      · rw [hP'c, hUc]) (by rw [Finset.iSup_insert, Finset.iSup_singleton]; exact hPP') (by
      intro α hα Y hY
      simp only [Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl
      · exact (hinv α hα).1
      · exact (hinv α hα).2)
  exact hmain.trans Finset.card_le_two

end CFSG.Quasithin.RonanE43
