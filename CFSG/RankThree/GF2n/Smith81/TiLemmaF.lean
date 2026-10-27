module

public import CFSG.RankThree.GF2n.Stroth80.Ctx

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z : Subgroup G}

theorem cqt_Q_le_M (H : StrothHyp M Q Z) : Q ≤ M := by
  rw [H.hQ]
  exact (inSubgroup_pCore_two M).2.1

theorem cqt_M_le_normalizer_Q (H : StrothHyp M Q Z) :
    M ≤ Subgroup.normalizer (Q : Set G) := by
  rw [H.hQ]
  exact (inSubgroup_pCore_two M).2.2

theorem cqt_Z_le_Q (H : StrothHyp M Q Z) : Z ≤ Q := by
  rw [H.hZ]
  exact Subgroup.map_subtype_le _

theorem cqt_conj_mem_Z (H : StrothHyp M Q Z) {m : G} (hm : m ∈ M) {z : G} (hz : z ∈ Z) :
    m * z * m⁻¹ ∈ Z :=
  (Subgroup.mem_normalizer_iff.mp (H.maxAb.prop.2.1 hm) z).mp hz

@[expose] def cqtSubgroup (H : StrothHyp M Q Z) (N : Subgroup G) : Subgroup G where
  carrier := CQt Q Z N
  mul_mem' := by
    rintro a b ⟨ha, hat⟩ ⟨hb, hbt⟩
    refine ⟨Q.mul_mem ha hb, fun t ht => ?_⟩
    have e : ⁅t, a * b⁆ = ⁅t, a⁆ * (a * ⁅t, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem (hat t ht) (cqt_conj_mem_Z H (cqt_Q_le_M H ha) (hbt t ht))
  one_mem' := ⟨Q.one_mem, fun t _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro a ⟨ha, hat⟩
    refine ⟨Q.inv_mem ha, fun t ht => ?_⟩
    have e : ⁅t, a⁻¹⁆ = a⁻¹ * ⁅t, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    have h1 : a⁻¹ * ⁅t, a⁆⁻¹ * a ∈ Z := by
      have h := cqt_conj_mem_Z H (cqt_Q_le_M H (Q.inv_mem ha)) (Z.inv_mem (hat t ht))
      rwa [inv_inv] at h
    rw [e]
    exact h1

theorem cqt_eq_of_commute (H : StrothHyp M Q Z) {N : Subgroup G} (hNM : N ≤ M)
    (hN : M ≤ Subgroup.normalizer (N : Set G))
    (hcomm : ∀ c ∈ CQt Q Z N, ∀ d ∈ CQt Q Z N, c * d = d * c) :
    CQt Q Z N = (Z : Set G) := by
  have hfwd : ∀ m ∈ M, ∀ c ∈ cqtSubgroup H N, m * c * m⁻¹ ∈ cqtSubgroup H N := by
    intro m hm c hc
    obtain ⟨hcQ, hcN⟩ := hc
    refine ⟨(Subgroup.mem_normalizer_iff.mp (cqt_M_le_normalizer_Q H hm) c).mp hcQ,
      fun t ht => ?_⟩
    have htm : m⁻¹ * t * m ∈ N := by
      have h := (Subgroup.mem_normalizer_iff.mp (hN (M.inv_mem hm)) t).mp ht
      rwa [inv_inv] at h
    have e : ⁅t, m * c * m⁻¹⁆ = m * ⁅m⁻¹ * t * m, c⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact cqt_conj_mem_Z H hm (hcN _ htm)
  have hMN : M ≤ Subgroup.normalizer ((cqtSubgroup H N : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hfwd m hm c hc
    · intro hc
      have h := hfwd m⁻¹ (M.inv_mem hm) (m * c * m⁻¹) hc
      have e : m⁻¹ * (m * c * m⁻¹) * m⁻¹⁻¹ = c := by group
      rw [e] at h
      exact h
  have hPQ : cqtSubgroup H N ≤ Q := by
    intro x hx
    obtain ⟨hxQ, -⟩ := hx
    exact hxQ
  have hPM : cqtSubgroup H N ≤ M := hPQ.trans (cqt_Q_le_M H)
  have hPc : IsMulCommutative (cqtSubgroup H N) :=
    ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have hZP : Z ≤ cqtSubgroup H N := by
    intro z hz
    refine ⟨cqt_Z_le_Q H hz, fun t ht => ?_⟩
    rw [commutatorElement_def]
    exact Z.mul_mem (cqt_conj_mem_Z H (hNM ht) hz) (Z.inv_mem hz)
  have hPpred : cqtSubgroup H N ≤ M ∧
      M ≤ Subgroup.normalizer ((cqtSubgroup H N : Subgroup G) : Set G) ∧
      IsMulCommutative (cqtSubgroup H N) := ⟨hPM, hMN, hPc⟩
  have hPle : cqtSubgroup H N ≤ Z := H.maxAb.le_of_ge hPpred hZP
  have hPZ : cqtSubgroup H N = Z := le_antisymm hPle hZP
  have hset : ((cqtSubgroup H N : Subgroup G) : Set G) = (Z : Set G) := by
    rw [hPZ]
  exact hset

end CFSG.RankThree.GF2n.Smith81
