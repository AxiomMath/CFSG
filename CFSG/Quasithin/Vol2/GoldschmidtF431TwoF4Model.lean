module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Facts
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Pfl
public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocal
public import Certificates.Certificate7050Base

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47
  CFSG.Quasithin.H13.F45Ru CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


theorem twoF4Lattice_S : twoF4Lattice.S = twoF4TT := by
  ext x
  exact Iff.rfl

theorem twoF4Lattice_P₁' : twoF4Lattice.P₁ = twoF4M1 := twoF4Lattice_P₁

theorem twoF4Lattice_P₂' : twoF4Lattice.P₂ = twoF4M2 := twoF4Lattice_P₂

theorem sylow_model : IsSylowTwoOf twoF4TT ⊤ := by
  have := twoF4Lattice.isSylowTwoOf_top
  rwa [twoF4Lattice_S] at this

theorem orderOf_zM : orderOf zM = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_titsZ

theorem orderOf_tM : orderOf tM = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · have h : tEl.1 ^ 2 = 1 := by
      rw [pow_two]
      exact tEl_invol.1
    exact Subtype.ext h
  · intro h
    exact tEl_invol.2 (congrArg Subtype.val h)

theorem cent_z_model : Subgroup.centralizer ({zM} : Set ↥twoF4M) = twoF4M1 := by
  have hle : twoF4M1 ≤ Subgroup.centralizer ({zM} : Set ↥twoF4M) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (twoF4H_le_centralizer_z hx))
  have hST : twoF4Lattice.S ≤ twoF4M1 := by
    rw [twoF4Lattice_S]
    intro x hx
    exact twoF4S_le_twoF4H hx
  rcases twoF4Lattice.lattice _ (hST.trans hle) with h | h | h | h
  · exact absurd (le_antisymm twoF4Lattice.S_le_P₁ (by rw [twoF4Lattice_P₁', ← h]; exact hle))
      twoF4Lattice.S_ne_P₁
  · rw [h, twoF4Lattice_P₁']
  · exact absurd (by rw [twoF4Lattice_P₁', ← h]; exact hle) twoF4Lattice.P₁_not_le_P₂
  · exfalso
    have hz : ∀ g : ↥twoF4M, g * zM = zM * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.1 (by rw [h]; exact Subgroup.mem_top g)
    have hQn : (Subgroup.zpowers zM).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hc : Commute g (zM ^ k) := Commute.zpow_right (hz g) k
      rw [hc.eq, mul_inv_cancel_right]
      exact hn
    have hQp : IsPGroup 2 (Subgroup.zpowers zM) :=
      BenderStart.isPGroup_zpowers_of_pow_eq_one (k := 1) (by
        rw [pow_one]
        exact orderOf_zM ▸ pow_orderOf_eq_one zM)
    have hzm : zM ∈ Subgroup.zpowers zM := Subgroup.mem_zpowers zM
    rw [twoF4Lattice.O₂ _ hQn hQp, Subgroup.mem_bot] at hzm
    have := orderOf_zM
    rw [hzm, orderOf_one] at this
    omega

theorem classes_model : ∀ x : ↥twoF4M, orderOf x = 2 → IsConj zM x ∨ IsConj tM x := by
  intro x hx
  obtain ⟨m, -, hm⟩ := exists_conj_mem_of_isSylowTwoOf_involution sylow_model
    (Subgroup.mem_top x) hx
  have hconj : IsConj (m⁻¹ * x * m) x := isConj_iff.2 ⟨m, by group⟩
  have ho : orderOf (m⁻¹ * x * m) = 2 := by
    rw [← hx]
    exact CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hconj
  rcases inv_chain_model _ hm ho with h | h
  · exact Or.inl ((reflTransGen_isConj h).trans hconj)
  · exact Or.inr ((reflTransGen_isConj h).trans hconj)

theorem center_T_model : ∀ w ∈ twoF4TT, (∀ y ∈ twoF4TT, y * w = w * y) → w ≠ 1 →
    ∃ m ∈ twoF4M1 ⊓ twoF4M2, m * zM * m⁻¹ = w := by
  intro w hw hc hne
  have h := twoF4S_center (x := w.1) hw fun y hy =>
    congrArg Subtype.val (hc ⟨y, twoF4S_le_twoF4M hy⟩ hy)
  rcases h with h | h
  · exact absurd (Subtype.ext h) hne
  · refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact Subtype.ext h.symm

@[expose] noncomputable def cM : ↥twoF4M := ⟨cEl.1, mem_twoF4M_of_mem_A cEl.2⟩

theorem orderOf_cM : orderOf cM = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · exact Subtype.ext cEl_pow.1
  · intro h
    exact cEl_pow.2 (congrArg Subtype.val h)

theorem three_dvd_card_cent_t : 3 ∣ Nat.card (Subgroup.centralizer ({tM} : Set ↥twoF4M)) := by
  have hc : cM ∈ Subgroup.centralizer ({tM} : Set ↥twoF4M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext cEl_comm
  have ho : orderOf (⟨cM, hc⟩ : Subgroup.centralizer ({tM} : Set ↥twoF4M)) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_cM
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem card_twoF4H : Nat.card twoF4H = 20480 := by
  have h := Subgroup.card_mul_index (titsH.subgroupOf twoF4H)
  have h2 : (titsH.subgroupOf twoF4H).index = 2 :=
    relIndex_extSub (fun hq => tπ_not_mem_D (titsH_le_titsD hq))
  have hle : titsH ≤ twoF4H := le_extSub
  rw [h2, card_subgroupOf_eq hle, (titsQH_facts).2.2.2] at h
  omega

theorem card_twoF4M1 : Nat.card twoF4M1 = 20480 := by
  have e : Nat.card twoF4M1 = Nat.card twoF4H := card_subgroupOf_eq twoF4H_le_twoF4M
  rw [e, card_twoF4H]

theorem twoF4_F431LieI : F431LieI twoF4TT twoF4M1 twoF4M2 zM tM where
  sylow := sylow_model
  T_le₁ := fun _ hx => twoF4S_le_twoF4H hx
  T_le₂ := fun _ hx => twoF4S_le_twoF4N hx
  z_mem := titsZ_mem_S
  t_mem := tEl_mem_S
  hz := orderOf_zM
  ht := orderOf_tM
  not_conj := not_conj_model
  classes := classes_model
  cent_z := cent_z_model
  cent_t := cent_t_model
  center_T := center_T_model
  inv_chain := inv_chain_model

end CFSG.Quasithin.H13.F431.TwoF4
