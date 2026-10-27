module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45XGen
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

private theorem kof_pCore_p_eq_bot (h : Base45 p G D) :
    CFSG.pCore p ↥(Kof G) = ⊥ := by
  have hmap : (CFSG.pCore p ↥(Kof G)).map (Kof G).subtype ≤ CFSG.pCore p G := by
    refine CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup ?_ ?_
    · haveI : (CFSG.pCore p ↥(Kof G)).Characteristic := inferInstance
      exact ConjAct.normal_of_characteristic_of_normal
    · exact (CFSG.pCore_isPGroup (p := p) (G := ↥(Kof G))).map (Kof G).subtype
  rw [h.Op] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore p ↥(Kof G))
    (Kof G).subtype_injective).mp (le_bot_iff.mp hmap)

private theorem kof_pPrimeCore_two_eq_bot (h : Base45 p G D)
    (hK22p : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(Kof G) → q = 2 ∨ q = p) :
    CFSG.pPrimeCore 2 ↥(Kof G) = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hpN : IsPGroup p N := by
    rw [IsPGroup.iff_card]
    refine ⟨(Nat.card N).primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := N)).ne' ?_⟩
    intro d hd hdd
    have hdK : d ∣ Nat.card ↥(Kof G) := hdd.trans (Subgroup.card_subgroup_dvd_card N)
    rcases hK22p d hd hdK with h2 | hp
    · exact absurd (h2 ▸ hdd) ((Nat.prime_two.coprime_iff_not_dvd).1 hcop)
    · exact hp
  have hle : N ≤ CFSG.pCore p ↥(Kof G) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hN hpN
  rw [kof_pCore_p_eq_bot h] at hle
  exact le_bot_iff.mp hle

private theorem kof_isSolvable (h : Base45 p G D)
    (hK22p : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(Kof G) → q = 2 ∨ q = p) :
    Group.IsSolvable ↥(Kof G) := by
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := ↥(Kof G))).ne' 2 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcard
    exact (Nat.card_pos (α := ↥(Kof G))).ne' hcard
  have hmp : m = p ^ m.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hm0 (fun {d} hd hdm => by
      have hdK : d ∣ Nat.card ↥(Kof G) := by
        rw [hcard]
        exact Dvd.dvd.mul_left hdm _
      rcases hK22p d hd hdK with h2 | hp
      · exact absurd (h2 ▸ hdm) hm
      · exact hp)
  exact TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow (G := ↥(Kof G))
    (p := 2) (q := p) (a := a) (b := m.primeFactorsList.length) Nat.prime_two h.prime
    (hmp ▸ hcard)

theorem uc45_centralizer_X_le (h : Base45 p G D)
    (hK22p : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(Kof G) → q = 2 ∨ q = p) :
    Kof G ⊓ Subgroup.centralizer (Xof G : Set G) ≤ Xof G := by
  have hsolvK : Group.IsSolvable ↥(Kof G) := kof_isSolvable h hK22p
  have hcoreK : CFSG.pPrimeCore 2 ↥(Kof G) = ⊥ := kof_pPrimeCore_two_eq_bot h hK22p
  have hcharK : CFSG.IsCharacteristicP 2 ↥(Kof G) := by
    have hfit : CFSG.fittingSubgroup ↥(Kof G) = CFSG.pCore 2 ↥(Kof G) :=
      CFSG.Fitting_eq_pcore ↥(Kof G) 2 hcoreK
    change Subgroup.centralizer (CFSG.pCore 2 ↥(Kof G) : Set ↥(Kof G)) ≤
      CFSG.pCore 2 ↥(Kof G)
    rw [← hfit]
    exact CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolvK
  intro c hc
  obtain ⟨hcK, hcC⟩ := Subgroup.mem_inf.1 hc
  let c' : ↥(Kof G) := ⟨c, hcK⟩
  have hcent : c' ∈ Subgroup.centralizer (CFSG.pCore 2 ↥(Kof G) : Set ↥(Kof G)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyX : (y : G) ∈ Xof G := by
      change (y : G) ∈ CFSG.Open.pCoreOf 2 (Kof G)
      rw [CFSG.openPCoreOf_eq_map_pCore]
      exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hcC (y : G) hyX
  have hmem : c' ∈ CFSG.pCore 2 ↥(Kof G) := hcharK hcent
  change c ∈ CFSG.Open.pCoreOf 2 (Kof G)
  rw [CFSG.openPCoreOf_eq_map_pCore]
  exact Subgroup.mem_map.2 ⟨c', hmem, rfl⟩

theorem uc45_T_ne_bot (h : Base45 p G D)
    (hK22p : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(Kof G) → q = 2 ∨ q = p)
    (hK : Kof G ≠ ⊥) : Tof G D ≠ ⊥ := by
  intro hTbot
  have hDcent : D ≤ Subgroup.centralizer (Xof G : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ Subgroup.centralizer (D : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Xof G) (H₂ := D)).mp hTbot hx
    exact (Subgroup.mem_centralizer_iff.mp hx' d hd).symm
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (Xof G : Set G) := by
    rw [← h.gen]
    exact Subgroup.normalClosure_le_normal hDcent
  have hcentral : Subgroup.centralizer (Xof G : Set G) = ⊤ := le_antisymm le_top htop
  have hXZ : Xof G ≤ Subgroup.center G := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (Xof G : Set G) := hcentral ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  have hKleX : Kof G ≤ Xof G := by
    have hle := uc45_centralizer_X_le h hK22p
    rwa [hcentral, inf_top_eq] at hle
  have hXleK : Xof G ≤ Kof G := CFSG.openPCoreOf_le 2 (Kof G)
  have hKX : Kof G = Xof G := le_antisymm hKleX hXleK
  have hKbot : Kof G = ⊥ := by
    have hcommK : ⁅Kof G, (⊤ : Subgroup G)⁆ = Kof G := kof_commutator_top h.card_three h.gen
    rw [← hcommK, hKX, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact Subgroup.mem_center_iff.mp (hXZ hx) g
  exact hK hKbot

private theorem commutator_self_le_ZX
    (hcl : commutator ↥(Xof G) ≤ Subgroup.center ↥(Xof G)) :
    ⁅Xof G, Xof G⁆ ≤ ZXof G := by
  have htop : (⊤ : Subgroup ↥(Xof G)).map (Xof G).subtype = Xof G := by
    ext x
    constructor
    · intro hx; exact Subgroup.map_subtype_le _ hx
    · intro hx; exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hmapcomm : Subgroup.map (Xof G).subtype (commutator ↥(Xof G)) = ⁅Xof G, Xof G⁆ := by
    change Subgroup.map (Xof G).subtype (⁅(⊤ : Subgroup ↥(Xof G)), ⊤⁆) =
      ⁅Xof G, Xof G⁆
    rw [Subgroup.map_commutator, htop]
  rw [← hmapcomm]
  exact Subgroup.map_mono hcl

private theorem uc45_T_center_fixed_mod_ZX
    (hcl : commutator ↥(Xof G) ≤ Subgroup.center ↥(Xof G))
    (hZX : ZXof G ≤ Subgroup.center G) {z : G}
    (hz : z ∈ (Subgroup.center ↥(Tof G D)).map (Tof G D).subtype) :
    ∀ a ∈ D, a * z * a⁻¹ * z⁻¹ ∈ ZXof G := by
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 hz
  have hcz' : (c : G) = z := hcz
  have hzT : z ∈ Tof G D := Subgroup.map_subtype_le _ hz
  have hzX : z ∈ Xof G :=
    Subgroup.commutator_le_left (H₁ := Xof G) (H₂ := D) hzT
  have hzleX : Subgroup.zpowers z ≤ Xof G := Subgroup.zpowers_le.2 hzX
  have hAY : D ≤ Subgroup.normalizer (Xof G : Set G) := Subgroup.le_normalizer_of_normal
  have haux1 : ⁅⁅Xof G, D⁆, Subgroup.zpowers z⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hcw := Subgroup.mem_center_iff.mp hc (⟨w, hw⟩ : ↥(Tof G D))
    have hwz : w * z = z * w := by
      have hthis : w * (c : G) = (c : G) * w :=
        congrArg (fun x : ↥(Tof G D) => (x : G)) hcw
      rw [hcz'] at hthis
      exact hthis
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp he
    rw [← hm]
    exact (Commute.zpow_right hwz m).eq.symm
  have haux2 : ⁅⁅Subgroup.zpowers z, Xof G⁆, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hwZX : w ∈ ZXof G :=
      commutator_self_le_ZX hcl (Subgroup.commutator_mono hzleX le_rfl hw)
    exact Subgroup.mem_center_iff.mp (hZX hwZX) a
  have hrot : ⁅⁅D, Subgroup.zpowers z⁆, Xof G⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := D) (H₂ := Subgroup.zpowers z)
      (H₃ := Xof G) haux2 haux1
  intro a ha
  have hmemX : ⁅a, z⁆ ∈ Xof G := by
    have haz : a * z * a⁻¹ ∈ Xof G := (Subgroup.mem_normalizer_iff.mp (hAY ha) z).1 hzX
    exact (Xof G).mul_mem haz ((Xof G).inv_mem hzX)
  have hmemC : ⁅a, z⁆ ∈ Subgroup.centralizer (Xof G : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hrot)
      (Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers z))
  have hcenter : (⟨⁅a, z⁆, hmemX⟩ : ↥(Xof G)) ∈ Subgroup.center ↥(Xof G) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hmemC (y : G) y.2
  have hmemZX : ⁅a, z⁆ ∈ ZXof G :=
    Subgroup.mem_map.2 ⟨⟨⁅a, z⁆, hmemX⟩, hcenter, rfl⟩
  simpa [commutatorElement_def] using hmemZX

theorem uc45_ZT_le_ZX (h : Base45 p G D)
    (hcl : commutator ↥(Xof G) ≤ Subgroup.center ↥(Xof G))
    (hZX : ZXof G ≤ Subgroup.center G) :
    (Subgroup.center ↥(Tof G D)).map (Tof G D).subtype ≤ ZXof G := by
  intro z hz
  have hZY : ZXof G ≤ Xof G := Subgroup.map_subtype_le _
  have hcomm : ∀ y ∈ Xof G, ∀ y' ∈ Xof G, y * y' * y⁻¹ * y'⁻¹ ∈ ZXof G := by
    intro y hy y' hy'
    have hmem : ⁅(⟨y, hy⟩ : ↥(Xof G)), (⟨y', hy'⟩ : ↥(Xof G))⁆ ∈
        Subgroup.center ↥(Xof G) :=
      hcl (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    refine Subgroup.mem_map.2 ⟨⁅(⟨y, hy⟩ : ↥(Xof G)), (⟨y', hy'⟩ : ↥(Xof G))⁆, hmem, ?_⟩
    simp [commutatorElement_def]
  have hAY : D ≤ Subgroup.normalizer (Xof G : Set G) := Subgroup.le_normalizer_of_normal
  have hAZ : D ≤ Subgroup.normalizer (ZXof G : Set G) := Subgroup.le_normalizer_of_normal
  have hcop : (Nat.card D).Coprime (Nat.card ↥(Xof G)) := by
    obtain ⟨k, hk⟩ := (xof_isPGroup (G := G)).exists_card_eq
    rw [h.card_three, hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hzT : z ∈ Tof G D := Subgroup.map_subtype_le _ hz
  have hx : z ∈ ⁅D, Xof G⁆ ⊔ ZXof G := by
    apply Subgroup.mem_sup_left
    rw [← Subgroup.commutator_comm (Xof G) D]
    exact hzT
  exact CFSG.LocalAnalysis.EvenBN.Common.mem_of_mem_commutator_sup_of_fixed
    (A := D) (Y := Xof G) (Z := ZXof G) hZY hcomm hAY hAZ hcop hx
    (uc45_T_center_fixed_mod_ZX hcl hZX hz)

theorem uc45_T_hyp (h : Base45 p G D)
    (hcl : commutator ↥(Xof G) ≤ Subgroup.center ↥(Xof G))
    (hZX : ZXof G ≤ Subgroup.center G) :
    IsPGroup 2 (Tof G D) ∧ D ≤ Subgroup.normalizer (Tof G D : Set G) ∧
      ⁅D, Tof G D⁆ = Tof G D ∧ IsCyclic ↥(Subgroup.center ↥(Tof G D)) := by
  have hTX : Tof G D ≤ Xof G := Subgroup.commutator_le_left (H₁ := Xof G) (H₂ := D)
  refine ⟨(xof_isPGroup (G := G)).to_le hTX, ?_, ?_, ?_⟩
  · exact Subgroup.normalizer_commutator_ge_right (Xof G) D
  · have hcop : Nat.Coprime (Nat.card D) (Nat.card ↥(Xof G)) := by
      obtain ⟨k, hk⟩ := (xof_isPGroup (G := G)).exists_card_eq
      rw [h.card_three, hk]
      exact (by decide : Nat.Coprime 3 2).pow_right k
    have hidem := CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime (Xof G) D hcop
      (Subgroup.le_normalizer_of_normal)
    exact (Subgroup.commutator_comm D (Tof G D)).trans hidem
  · have hZT : (Subgroup.center ↥(Tof G D)).map (Tof G D).subtype ≤ ZXof G :=
      uc45_ZT_le_ZX h hcl hZX
    have hZTG : (Subgroup.center ↥(Tof G D)).map (Tof G D).subtype ≤ Subgroup.center G :=
      hZT.trans hZX
    have hcyc : IsCyclic ↥((Subgroup.center ↥(Tof G D)).map (Tof G D).subtype) := by
      haveI : IsCyclic ↥(Subgroup.center G) := h.center_cyclic
      exact Subgroup.isCyclic_of_le hZTG
    exact ((Subgroup.equivMapOfInjective (Subgroup.center ↥(Tof G D)) (Tof G D).subtype
      (Tof G D).subtype_injective).isCyclic).mpr hcyc

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
