module

public import CFSG.Quasithin.Vol2.Ch3T326GA
public import CFSG.Quasithin.Vol2.Ch3T326D
public import CFSG.Quasithin.Background.GoldschmidtS146RArith
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
public import CFSG.Quasithin.Vol2.Ch3T326G
public import CFSG.Quasithin.Vol2.Ch3T326H
public import CFSG.Quasithin.Vol2.Ch3T326PM

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SmithD321
open scoped IsMulCommutative
open T325 (V_le_VM)

theorem three_dvd_card_of_d321 {W : Type} [CommGroup W] {Mp L : Subgroup (MulAut W)}
    (h : D321Two L ∨ D321Three Mp L) : 3 ∣ Nat.card ↥L := by
  rcases h with ⟨hpsl, -⟩ | ⟨n, hpsl, -⟩
  · rw [card_eq_168_of_isPSL32 hpsl]
    norm_num
  · rw [GoldS146R.card_isPSL_two_two hpsl]
    apply Dvd.dvd.mul_left
    have e : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 n

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem qhatStar_acts_of_lt (h316 : Theorem316Statement)
    (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat) (hD321 : D321Spelled)
    (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42) (h36 : D36c) (h37 : D37)
    (hB56 : AsB56) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hL38 : D3L38)
    [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hlt : conjClosure V₀ T ≠
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :
    ∀ A ∈ QhatStar (V := ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))),
      ∀ a ∈ A, ∀ u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))),
        (u : G) ∈ ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ →
        ((a u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) : G) ∈
          ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  obtain ⟨s, hs, hsn⟩ := c.exists_t
  have htS : conjAct VM ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩ ∈ autOn T VM :=
    Setup.mem_autOn_iff.2 ⟨⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩, T.inv_mem hs, rfl⟩
  have htn := c.not_mem_normalizer hA37 hs hsn
  have hMp := c.autOn_L₀_eq hA37 hA38 hs hsn
  obtain ⟨_, hq⟩ := qhat_VM h316 c
  have hq' : qhatOf (autOn (Subgroup.normalizer (conjClosure L T : Set G)) VM) ≤
      ((2 : ℚ) : WithTop ℚ) := by exact_mod_cast hq
  have htop : orbSup (autOn T VM) (V₀.subgroupOf VM) ≠ ⊤ := by
    rw [c.orbSup_eq]
    intro h
    exact hlt (le_antisymm (V_le_VM T (conjClosure L T) V₀) (Subgroup.subgroupOf_eq_top.mp h))
  have hD := c.d3Std h316
  rcases hD321 ↥VM _ _ _ _ _ hD _ htS htn hMp hq' with hVT | ⟨-, -, h23⟩
  · exact (htop hVT).elim
  have hB := d321Base_of hL38 hD htS htn hMp
  have h3L := three_dvd_card_of_d321 h23
  intro A hA a ha u hu
  have haN := qhatStar_le_normalizer_of_d321 hA21 hB42 h9 h36 h37 hB56 h38 hA23 hSzF hB htop h3L
    hA ha
  have hU : u ∈ commV (autOn L VM) := by
    rw [Vol2.Ch11.SecC.B51.commV_autOn c.L_le_NVM]
    exact Subgroup.mem_subgroupOf.2 hu
  have h1 := B15P4.map_commV_mem haN u hU
  rw [Vol2.Ch11.SecC.B51.commV_autOn c.L_le_NVM] at h1
  exact Subgroup.mem_subgroupOf.1 h1

end Ctx

end CFSG.Quasithin.H13.T326
