module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.RankThree.PartOne

open CFSG

namespace Sec1510

section General

variable {Hb : Type} [Group Hb] [Finite Hb]

omit [Finite Hb] in
theorem centralizer_layer_normal : (Subgroup.centralizer (layer Hb : Set Hb)).Normal := by
  have hLc : (layer Hb).Characteristic := LocalCores.layer_characteristic (G := Hb)
  have hL : (layer Hb).Normal := inferInstance
  refine ⟨fun y hy g => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : g⁻¹ * l * g ∈ layer Hb := by
    have := hL.conj_mem l hl g⁻¹
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hy _ hl'
  calc l * (g * y * g⁻¹) = g * ((g⁻¹ * l * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
    _ = (g * y * g⁻¹) * l := by group

omit [Finite Hb] in
theorem normal_map_of_characteristic {Y : Subgroup Hb} [Y.Normal] {C : Subgroup ↥Y}
    [C.Characteristic] : (C.map Y.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hn
  have h1 := Subgroup.characteristic_iff_map_eq.mp ‹C.Characteristic› (MulAut.conjNormal g)
  have hαc : (MulAut.conjNormal g : MulAut ↥Y) c ∈ C := by
    rw [← h1]
    exact Subgroup.mem_map_of_mem _ hc
  exact ⟨_, hαc, by simp [MulAut.conjNormal_apply]⟩

theorem fitting_layer_centralizer (p : ℕ) [Fact p.Prime]
    (hA : ∀ M : Subgroup Hb, M.Normal → Group.IsNilpotent ↥M → ¬ p ∣ Nat.card ↥M → M = ⊥) :
    ∃ Qb : Subgroup Hb,
      Qb ≤ Subgroup.centralizer (layer Hb : Set Hb) ∧
      (∀ y ∈ Subgroup.centralizer (layer Hb : Set Hb), ∀ q ∈ Qb, y * q * y⁻¹ ∈ Qb) ∧
      IsPGroup p ↥Qb ∧
      (∀ y ∈ Subgroup.centralizer (layer Hb : Set Hb), (∀ q ∈ Qb, y * q = q * y) → y ∈ Qb) ∧
      (∀ z ∈ Subgroup.center Hb, z ^ p = 1 → z ∈ Qb) := by
  classical
  have hYn : (Subgroup.centralizer (layer Hb : Set Hb)).Normal := centralizer_layer_normal
  set Yb := Subgroup.centralizer (layer Hb : Set Hb) with hYb
  have hlayer : layer ↥Yb = ⊥ := by
    apply LocalCores.layer_eq_bot_of_forall
    intro K hK
    have hKq : IsQuasisimple (K.map Yb.subtype : Subgroup Hb) :=
      LocalCores.isQuasisimple_of_mulEquiv (K.equivMapOfInjective Yb.subtype Yb.subtype_injective) hK.1
    have hKsn : (K.map Yb.subtype).IsSubnormal := hK.2.trans' hYn.isSubnormal
    have hcomp : IsComponent (K.map Yb.subtype) := ⟨hKq, hKsn⟩
    have hKL : K.map Yb.subtype ≤ layer Hb := LocalCores.component_le_layer hcomp
    have hKY : K.map Yb.subtype ≤ Yb := Subgroup.map_subtype_le K
    obtain ⟨-, -, a, b, hab⟩ := hKq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hcomm := Subgroup.mem_centralizer_iff.1 (hKY a.2) (b : Hb) (hKL b.2)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext hcomm.symm)
  have hFit : fittingSubgroup ↥Yb = pCore p ↥Yb := by
    refine le_antisymm ?_ (pCore_le_fitting _ p)
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    by_cases hq : q.1.1 = p
    · have : pCore q.1.1 ↥Yb = pCore p ↥Yb := by rw [hq]
      exact this.le
    · have hqp : q.1.1.Prime := (Nat.mem_primeFactors.1 q.1.2).1
      have : Fact q.1.1.Prime := ⟨hqp⟩
      have : (pCore q.1.1 ↥Yb).Characteristic := pCore_characteristic
      have hnorm := normal_map_of_characteristic (Y := Yb) (C := pCore q.1.1 ↥Yb)
      have hpg : IsPGroup q.1.1 ↥((pCore q.1.1 ↥Yb).map Yb.subtype) := pCore_isPGroup.map _
      have hnil : Group.IsNilpotent ↥((pCore q.1.1 ↥Yb).map Yb.subtype) := hpg.isNilpotent
      have hndvd : ¬ p ∣ Nat.card ↥((pCore q.1.1 ↥Yb).map Yb.subtype) := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
        rw [hn]
        intro hd
        exact hq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hqp).1
          ((Fact.out : p.Prime).dvd_of_dvd_pow hd)).symm
      have hM := hA _ hnorm hnil hndvd
      have : pCore q.1.1 ↥Yb = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ Yb.subtype_injective).1 hM
      rw [this]; exact bot_le
  have hgf : generalizedFitting ↥Yb = pCore p ↥Yb := by
    rw [generalizedFitting, hlayer, sup_bot_eq, hFit]
  have hBender : Subgroup.centralizer (pCore p ↥Yb : Set ↥Yb) ≤ pCore p ↥Yb := by
    rw [← hgf]
    exact centralizer_generalizedFitting_le ↥Yb
  refine ⟨(pCore p ↥Yb).map Yb.subtype, Subgroup.map_subtype_le _, ?_, pCore_isPGroup.map _, ?_, ?_⟩
  · intro y hy q hq
    obtain ⟨c, hc, rfl⟩ := hq
    exact ⟨⟨y, hy⟩ * c * ⟨y, hy⟩⁻¹, pCore_normal.conj_mem c hc _, by simp⟩
  · intro y hy hcomm
    have : (⟨y, hy⟩ : ↥Yb) ∈ Subgroup.centralizer (pCore p ↥Yb : Set ↥Yb) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact Subtype.ext (hcomm c (Subgroup.mem_map_of_mem _ hc)).symm
    exact ⟨_, hBender this, rfl⟩
  · intro z hz hzp
    have hzY : z ∈ Yb := Subgroup.mem_centralizer_iff.2 fun l _ => Subgroup.mem_center_iff.1 hz l
    set z' : ↥Yb := ⟨z, hzY⟩
    have hcent : ∀ g : ↥Yb, g * z' = z' * g := fun g =>
      Subtype.ext (Subgroup.mem_center_iff.1 hz g)
    have hnormz : (Subgroup.zpowers z').Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have : g * z' ^ k * g⁻¹ = z' ^ k := by
        have h1 : g * z' ^ k = z' ^ k * g := ((Commute.zpow_right (Commute.symm (hcent g).symm) k)).eq
        rw [h1]; group
      rw [this]; exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
    have hpz : IsPGroup p ↥(Subgroup.zpowers z') := by
      intro g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
      refine ⟨1, Subtype.ext ?_⟩
      have hz'p : z' ^ p = 1 := Subtype.ext hzp
      have h1 : (g : ↥Yb) ^ p = 1 := by
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz'p, one_zpow]
      show (g : ↥Yb) ^ (p ^ 1) = 1
      rw [pow_one]; exact h1
    have hle : Subgroup.zpowers z' ≤ pCore p ↥Yb := le_sSup ⟨hnormz, hpz⟩
    exact ⟨z', hle (Subgroup.mem_zpowers z'), rfl⟩

end General

end Sec1510

end CFSG.RankThree.PartOne
