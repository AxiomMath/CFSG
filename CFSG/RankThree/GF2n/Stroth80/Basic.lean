module

public import CFSG.RankThree.GF2n.Statements
import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.RankThree.GF2n.Stroth80.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

private theorem Z_le_Q (H : StrothHyp M Q Z) : Z ≤ Q := by
  rw [H.hZ]
  exact Subgroup.map_subtype_le _

private theorem Z_ne_bot (H : StrothHyp M Q Z) : Z ≠ ⊥ := by
  intro h
  have := H.q4
  rw [h, Subgroup.card_bot] at this
  omega

private theorem Q_ne_bot (H : StrothHyp M Q Z) : Q ≠ ⊥ := by
  intro h
  have hZQ := Z_le_Q H
  rw [h, le_bot_iff] at hZQ
  exact Z_ne_bot H hZQ

private theorem isPGroup_Q (H : StrothHyp M Q Z) : IsPGroup 2 Q := by
  rw [H.hQ]
  exact (inSubgroup_pCore_two M).1

private theorem inf_centralizer_eq (H : StrothHyp M Q Z) :
    Q ⊓ Subgroup.centralizer (Q : Set G) = Z :=
  (cen_eq Q).symm.trans H.hZ.symm

private theorem central_comm (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) {y : G}
    (hy : y ∈ Q) : z * y = y * z := by
  have h : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    rw [inf_centralizer_eq H]
    exact hz
  exact (Subgroup.mem_centralizer_iff.mp h.2 y hy).symm

private theorem sq_eq_one_of_mem_Z (H : StrothHyp M Q Z) : ∀ z ∈ Z, z ^ 2 = 1 := by
  obtain ⟨n, k, -, hcp⟩ := H.cp
  exact sq_eq_one_of_cp hcp

open CFSG.GH74.GLS.Bg.TwoGroups in
private theorem center_map_le_commutator {S E : Subgroup G} {R : Type} [CommRing R]
    (hES : E ≤ S) (e : ↥E ≃* UT3 R) :
    (Subgroup.center ↥E).map E.subtype ≤ ⁅S, S⁆ := by
  rintro _ ⟨w, hw, rfl⟩
  have hey : e w ∈ Subgroup.center (UT3 R) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw y]
  obtain ⟨ha, hb⟩ := (Tim79.ut3_mem_center_iff _).mp hey
  obtain ⟨c, hc⟩ : ∃ c : R, e w = ⟨0, 0, c⟩ := ⟨(e w).c, UT3.ext ha hb rfl⟩
  have hcomm : ⁅e.symm ⟨c, 0, 0⟩, e.symm ⟨0, 1, 0⟩⁆ = w := by
    apply e.injective
    rw [map_commutatorElement, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hc]
    rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    ext <;> simp [UT3.mul_def]
  have h1 : E.subtype w = ⁅E.subtype (e.symm ⟨c, 0, 0⟩), E.subtype (e.symm ⟨0, 1, 0⟩)⁆ := by
    rw [← map_commutatorElement, hcomm]
  rw [h1]
  exact Subgroup.commutator_mem_commutator (hES (e.symm ⟨c, 0, 0⟩).2)
    (hES (e.symm ⟨0, 1, 0⟩).2)

private theorem Z_le_commutator (H : StrothHyp M Q Z) : Z ≤ ⁅Q, Q⁆ := by
  obtain ⟨n, k, -, hcp⟩ := H.cp
  obtain ⟨hk, D, hDQ, hDL, hDZ, -, -⟩ := hcp
  obtain ⟨e⟩ := hDL ⟨0, hk⟩
  rw [← hDZ ⟨0, hk⟩]
  exact center_map_le_commutator (hDQ ⟨0, hk⟩) e

private theorem centralizes_Z (H : StrothHyp M Q Z) {x : G} (hxZ : ∀ y ∈ Q, ⁅x, y⁆ ∈ Z) :
    ∀ z ∈ Z, x * z = z * x := by
  have hZQ : Z ≤ Q := Z_le_Q H
  have L1 : ∀ u ∈ Z, ∀ a ∈ Q, ∀ k ∈ Q, ⁅u * a, k⁆ = ⁅a, k⁆ := by
    intro u hu a ha k hk
    have hw : a * k * a⁻¹ ∈ Q := mul_mem (mul_mem ha hk) (inv_mem ha)
    have hc : u * (a * k * a⁻¹) = a * k * a⁻¹ * u := central_comm H hu hw
    simp only [commutatorElement_def]
    calc u * a * k * (u * a)⁻¹ * k⁻¹ = u * (a * k * a⁻¹) * u⁻¹ * k⁻¹ := by group
      _ = a * k * a⁻¹ * u * u⁻¹ * k⁻¹ := by rw [hc]
      _ = a * k * a⁻¹ * k⁻¹ := by group
  have L2 : ∀ v ∈ Z, ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, v * b⁆ = ⁅a, b⁆ := by
    intro v hv a ha b hb
    have hw : ⁅a, b⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hav : v * a = a * v := central_comm H hv ha
    have hcomm : v * ⁅a, b⁆ = ⁅a, b⁆ * v := central_comm H hv hw
    calc ⁅a, v * b⁆ = a * v * b * a⁻¹ * (b⁻¹ * v⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = v * a * b * a⁻¹ * (b⁻¹ * v⁻¹) := by rw [← hav]
      _ = v * ⁅a, b⁆ * v⁻¹ := by simp only [commutatorElement_def]; group
      _ = ⁅a, b⁆ * v * v⁻¹ := by rw [hcomm]
      _ = ⁅a, b⁆ := by group
  have hcomm' : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Subgroup.centralizer ({x} : Set G) := by
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ha' : x * a * x⁻¹ = ⁅x, a⁆ * a := by
      rw [commutatorElement_def]; group
    have hb' : x * b * x⁻¹ = ⁅x, b⁆ * b := by
      rw [commutatorElement_def]; group
    have hmap : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have hconj : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
      rw [hmap, ha', hb']
      exact (L1 _ (hxZ a ha) a ha _ (mul_mem (hZQ (hxZ b hb)) hb)).trans
        (L2 _ (hxZ b hb) a ha b hb)
    calc ⁅a, b⁆ * x = (x * ⁅a, b⁆ * x⁻¹) * x := by rw [hconj]
      _ = x * ⁅a, b⁆ := by group
  have hle : Z ≤ Subgroup.centralizer ({x} : Set G) :=
    (Z_le_commutator H).trans (Subgroup.commutator_le.mpr hcomm')
  intro z hz
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hz)).symm

private theorem normalizer_eq_of_max {P : Subgroup G} (hmax : IsMaximalTwoLocal M)
    (hMP : M ≤ Subgroup.normalizer (P : Set G)) (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P) :
    Subgroup.normalizer (P : Set G) = M := by
  by_contra hne
  exact hmax.2 _ (lt_of_le_of_ne hMP (Ne.symm hne)) ⟨P, hP, hP2, rfl⟩

theorem StrothHyp.Q_normal (H : StrothHyp M Q Z) :
    Q ≤ M ∧ M ≤ Subgroup.normalizer (Q : Set G) := by
  rw [H.hQ]
  exact ⟨(inSubgroup_pCore_two M).2.1, (inSubgroup_pCore_two M).2.2⟩

theorem StrothHyp.Z_normal (H : StrothHyp M Q Z) :
    Z ≤ Q ∧ M ≤ Subgroup.normalizer (Z : Set G) :=
  ⟨Z_le_Q H, H.maxAb.prop.2.1⟩

theorem StrothHyp.normalizer_Z (H : StrothHyp M Q Z) :
    Subgroup.normalizer (Z : Set G) = M ∧ Subgroup.normalizer (Q : Set G) = M :=
  ⟨normalizer_eq_of_max H.maxLocal H.Z_normal.2 (Z_ne_bot H) ((isPGroup_Q H).to_le (Z_le_Q H)),
    normalizer_eq_of_max H.maxLocal H.Q_normal.2 (Q_ne_bot H) (isPGroup_Q H)⟩

theorem StrothHyp.centralizer_Q (H : StrothHyp M Q Z) :
    Subgroup.centralizer (Q : Set G) = Z := by
  apply le_antisymm
  · have hCN : Subgroup.centralizer (Q : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
      apply le_normalizer_of_comm
      intro x hx y hy
      exact (Subgroup.mem_centralizer_iff.mp hx y (Z_le_Q H hy)).symm
    have hCM : Subgroup.centralizer (Q : Set G) ≤ M := hCN.trans (le_of_eq H.normalizer_Z.1)
    have hfit : M ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
      rw [H.hQ]
      exact Tim78.inf_centralizer_le_of_generalizedFitting_eq H.fitting
    intro x hx
    have hxQ : x ∈ Q := hfit ⟨hCM hx, hx⟩
    have hxQZ : x ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := ⟨hxQ, hx⟩
    rwa [inf_centralizer_eq H] at hxQZ
  · intro z hz
    have hzQC : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
      rw [inf_centralizer_eq H]
      exact hz
    exact hzQC.2

theorem StrothHyp.centralizer_Qt (H : StrothHyp M Q Z) :
    ∀ x ∈ M, (∀ y ∈ Q, ⁅x, y⁆ ∈ Z) → x ∈ Q := by
  have hMZ : ∀ g ∈ M, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hg) z).mp hz
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, ∀ c, c ∈ C ↔ (c ∈ M ∧ ∀ y ∈ Q, ⁅c, y⁆ ∈ Z) := by
    refine ⟨{ carrier := {c | c ∈ M ∧ ∀ y ∈ Q, ⁅c, y⁆ ∈ Z}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun c => Iff.rfl⟩
    · rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
      refine ⟨mul_mem haM hbM, fun y hy => ?_⟩
      have hab : ⁅a * b, y⁆ = (a * ⁅b, y⁆ * a⁻¹) * ⁅a, y⁆ := by
        simp only [commutatorElement_def]; group
      rw [hab]
      exact mul_mem (hMZ a haM _ (hb y hy)) (ha y hy)
    · refine ⟨M.one_mem, fun y _ => ?_⟩
      have h1 : ⁅(1 : G), y⁆ = 1 := by simp [commutatorElement_def]
      rw [h1]
      exact Z.one_mem
    · rintro a ⟨haM, ha⟩
      refine ⟨inv_mem haM, fun y hy => ?_⟩
      have hinv : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [hinv]
      exact hMZ a⁻¹ (inv_mem haM) _ (inv_mem (ha y hy))
  have hCM : C ≤ M := fun c hc => ((hC c).mp hc).1
  have hCnorm : M ≤ Subgroup.normalizer (C : Set G) := by
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun c hc => ?_
    obtain ⟨hcM, hcZ⟩ := (hC c).mp hc
    show m * c * m⁻¹ ∈ C
    refine (hC _).mpr ⟨mul_mem (mul_mem hm hcM) (inv_mem hm), fun y hy => ?_⟩
    have hyQ : m⁻¹ * y * m ∈ Q := by
      refine (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hm) (m⁻¹ * y * m)).mpr ?_
      rw [show m * (m⁻¹ * y * m) * m⁻¹ = y by group]
      exact hy
    have h1 : ⁅m * c * m⁻¹, y⁆ = m * ⁅c, m⁻¹ * y * m⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact hMZ m hm _ (hcZ _ hyQ)
  have hx4 : ∀ c ∈ C, c ^ 4 = 1 := by
    intro x hxC
    obtain ⟨hxM, hxZ⟩ := (hC x).mp hxC
    have hxZc := centralizes_Z H hxZ
    have hsq : ∀ y ∈ Q, y * (x * x) = x * x * y := by
      intro y hy
      have hc : ⁅x, y⁆ ∈ Z := hxZ y hy
      have hxc : x * ⁅x, y⁆ * x⁻¹ = ⁅x, y⁆ := by
        rw [hxZc _ hc]
        group
      have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
        rw [commutatorElement_def]
        group
      have hc2 : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
        rw [← pow_two]
        exact sq_eq_one_of_mem_Z H _ hc
      have hconjy : x * x * y * (x * x)⁻¹ = y := by
        calc x * x * y * (x * x)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by group
          _ = x * (⁅x, y⁆ * y) * x⁻¹ := by rw [hxy]
          _ = (x * ⁅x, y⁆ * x⁻¹) * (x * y * x⁻¹) := by group
          _ = ⁅x, y⁆ * (⁅x, y⁆ * y) := by rw [hxc, hxy]
          _ = (⁅x, y⁆ * ⁅x, y⁆) * y := by rw [mul_assoc]
          _ = y := by rw [hc2, one_mul]
      calc y * (x * x) = (x * x * y * (x * x)⁻¹) * (x * x) := by rw [hconjy]
        _ = x * x * y := by group
    have hx2 : x * x ∈ Z := by
      have h : x * x ∈ Subgroup.centralizer (Q : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => hsq y hy
      rwa [H.centralizer_Q] at h
    have hx4' : (x * x) ^ 2 = 1 := sq_eq_one_of_mem_Z H _ hx2
    calc x ^ 4 = (x * x) ^ 2 := by rw [← sq x, ← pow_mul]
      _ = 1 := hx4'
  have hC2 : IsPGroup 2 C := fun c => ⟨2, Subtype.ext (by simpa using hx4 c.1 c.2)⟩
  have hCQ : C ≤ Q := by
    rw [H.hQ]
    exact Tim78.le_inSubgroup_pCore hCM hCnorm hC2
  intro x hxM hxZ
  exact hCQ ((hC x).mpr ⟨hxM, hxZ⟩)

theorem StrothHyp.special (H : StrothHyp M Q Z) :
    IsSpecialWithCentre Q Z := by
  obtain ⟨h1, -, h3⟩ := H.toHyp79.special
  exact ⟨h1, h3, H.hZ.symm⟩

end CFSG.RankThree.GF2n.Stroth80
