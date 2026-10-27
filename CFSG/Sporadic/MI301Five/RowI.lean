module

public import CFSG.Sporadic.MI301Five.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Layer
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs

public section

namespace CFSG.Sporadic.MI301Five

open CFSG.Blueprint CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Dickson.I271
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301 Subgroup

variable {G : Type} [Group G] {α d z : G}

section HN


theorem FiveFrame.card_H (F : FiveFrame α d z) :
    Nat.card ↥(cent2 α d) = 273030912000000 := by
  obtain ⟨e⟩ := F.hn
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.HN.card_HN

theorem FiveFrame.isSimpleGroup (F : FiveFrame α d z) : IsSimpleGroup ↥(cent2 α d) := by
  obtain ⟨e⟩ := F.hn
  exact @MulEquiv.isSimpleGroup ↥(cent2 α d) _ NativeSporadic.HN Units.instGroup
    CFSG.Sporadic.HN.isSimpleGroup_HN e

theorem FiveFrame.nonabelian (F : FiveFrame α d z) : ∃ a b : ↥(cent2 α d), a * b ≠ b * a := by
  have hs := F.isSimpleGroup
  have hcard := F.card_H
  by_contra hcon
  push Not at hcon
  letI : CommGroup ↥(cent2 α d) := { (inferInstance : Group ↥(cent2 α d)) with mul_comm := hcon }
  have hpr := IsSimpleGroup.prime_card (α := ↥(cent2 α d))
  rw [hcard] at hpr
  norm_num at hpr

variable [Finite G]

theorem FiveFrame.exists_eq_mul (F : FiveFrame α d z) :
    ∀ x ∈ cent d, ∃ (i : ℕ) (h : G), h ∈ cent2 α d ∧ x = d ^ i * h :=
  TabMFive.eq_prod_of_card_le Nat.prime_five (by norm_num) F.orderOf_d F.inverts inf_le_left
    (Subgroup.mem_centralizer_singleton_iff.2 rfl) inf_le_right
    (by rw [F.card_H]; exact F.card_cent_d)

theorem FiveFrame.conj_mem (F : FiveFrame α d z) :
    ∀ g ∈ cent d, ∀ h ∈ cent2 α d, g * h * g⁻¹ ∈ cent2 α d := by
  intro g hg h hh
  obtain ⟨i, h', hh', rfl⟩ := F.exists_eq_mul g hg
  have hy : h' * h * h'⁻¹ ∈ cent2 α d :=
    (cent2 α d).mul_mem ((cent2 α d).mul_mem hh' hh) ((cent2 α d).inv_mem hh')
  have hyd : Commute (h' * h * h'⁻¹) d := Subgroup.mem_centralizer_singleton_iff.1 hy.2
  have e : d ^ i * h' * h * (d ^ i * h')⁻¹ = d ^ i * (h' * h * h'⁻¹) * (d ^ i)⁻¹ := by group
  rw [e, ← (hyd.pow_right i).eq, mul_inv_cancel_right]
  exact hy

theorem FiveFrame.commutator_inf_le (F : FiveFrame α d z) {Y : Subgroup G} (hdY : d ∈ Y) :
    ⁅cent d ⊓ Y, cent d ⊓ Y⁆ ≤ cent2 α d ⊓ Y := by
  refine commutator_le_of_le_sup_of_commute (A := zpowers d) ?_ ?_ ?_
  · intro x hx
    obtain ⟨i, h, hh, rfl⟩ := F.exists_eq_mul x hx.1
    have hhY : h ∈ Y := by
      have h1 := Y.mul_mem (Y.inv_mem (Y.pow_mem hdY i)) hx.2
      rwa [inv_mul_cancel_left] at h1
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers d i))
      (Subgroup.mem_sup_left ⟨hh, hhY⟩)
  · intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self d m n).eq
  · intro a ha s hs
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hsd : Commute s d := Subgroup.mem_centralizer_singleton_iff.1 hs.1.2
    rw [← (hsd.zpow_right m).eq, mul_inv_cancel_right]
    exact hs

theorem FiveFrame.rowIOf_eq (F : FiveFrame α d z) : rowIOf 5 d = cent2 α d := by
  unfold rowIOf
  have hc := F.commutator_inf_le (Y := ⊤) (Subgroup.mem_top d)
  simp only [inf_top_eq] at hc
  exact glaPLayer_eq_of_isSimple_normal_commutator_le Nat.prime_five inf_le_right F.conj_mem
    F.isSimpleGroup F.nonabelian (by rw [F.card_H]; norm_num) hc

theorem FiveFrame.hI
    (F : FiveFrame α d z) : RowI .m5 5 (rowIOf 5 d) := by
  show IsTypeWithCenter 5 (rowIOf 5 d) (sporIs .HN) 1
  rw [F.rowIOf_eq]
  obtain ⟨e⟩ := F.hn
  exact isTypeWithCenter_of_isSimple Nat.prime_five F.isSimpleGroup F.nonabelian
    (by rw [F.card_H]; norm_num)
    ⟨TauCeti.CFSGIndex.sporadic .HN, rfl, ⟨e.trans CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv.some⟩⟩

end HN

end CFSG.Sporadic.MI301Five
