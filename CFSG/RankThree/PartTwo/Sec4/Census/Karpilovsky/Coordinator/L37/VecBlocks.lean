module

public import Certificates.Certificate291440

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native
open scoped Pointwise


@[expose] noncomputable def vLab : Fin nPts → Fin 7 :=
  Classical.choose Certificates.certificate291440

theorem vLab_spec : (∀ p q, vLab p = vLab q ↔ ∃ h ∈ lvl 1, h • p = q) ∧
    (∀ i, (Finset.univ.filter (fun p => vLab p = i)).card =
      ![1, 1, 11172, 117306, 52136, 52136, 12768] i) ∧
    vLab root = 0 ∧ vLab ⟨1, by norm_num⟩ = 1 :=
  Classical.choose_spec Certificates.certificate291440

theorem vLab_orb : ∀ p q : Fin nPts, vLab p = vLab q → ∃ h ∈ lvl 1, h • p = q :=
  fun p q => (vLab_spec.1 p q).1

@[expose] def vSubSizesF : Fin 7 → ℕ := ![1, 1, 11172, 117306, 52136, 52136, 12768]

theorem card_vLab (i : Fin 7) :
    (Finset.univ.filter (fun p : Fin nPts => vLab p = i)).card = vSubSizesF i :=
  vLab_spec.2.1 i

noncomputable abbrev negRoot : Fin nPts := ⟨1, by norm_num⟩

theorem vLab_root : vLab root = 0 := vLab_spec.2.2.1

theorem vLab_negRoot : vLab negRoot = 1 := vLab_spec.2.2.2

theorem eq_of_vLab_eq_of_size_one {i : Fin 7} (hi : vSubSizesF i = 1) {p q : Fin nPts}
    (hp : vLab p = i) (hq : vLab q = i) : p = q := by
  classical
  have hc := card_vLab i
  rw [hi, Finset.card_eq_one] at hc
  obtain ⟨a, ha⟩ := hc
  have hp' : p ∈ Finset.univ.filter (fun p : Fin nPts => vLab p = i) := by simp [hp]
  have hq' : q ∈ Finset.univ.filter (fun p : Fin nPts => vLab p = i) := by simp [hq]
  rw [ha, Finset.mem_singleton] at hp' hq'
  rw [hp', hq']

set_option maxRecDepth 20000 in
theorem vSubSizes_blocks : ∀ S : Finset (Fin 7), (0 : Fin 7) ∈ S →
    (∑ i ∈ S, vSubSizesF i) ∣ 245520 → S = {0} ∨ S = {0, 1} ∨ S = Finset.univ := by
  decide

theorem isBlock_root_cases {B : Set (Fin nPts)} (hrB : root ∈ B)
    (hB : MulAction.IsBlock J B) :
    B = {root} ∨ B = {root, negRoot} ∨ B = Set.univ := by
  classical
  have hclosed : ∀ p q : Fin nPts, p ∈ B → vLab p = vLab q → q ∈ B := by
    intro p q hp hpq
    obtain ⟨h, hh, rfl⟩ := vLab_orb p q hpq
    have hhx : h • root ∈ B := by
      rw [lvl_one_fix hh]
      exact hrB
    rw [← hB.smul_eq_of_mem hrB hhx]
    exact Set.smul_mem_smul_set hp
  let S : Finset (Fin 7) := (Finset.univ.filter (· ∈ B)).image vLab
  have hmemS : ∀ p, vLab p ∈ S ↔ p ∈ B := by
    intro p
    constructor
    · intro hp
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
      exact hclosed q p (Finset.mem_filter.mp hq).2 hqp
    · intro hp
      exact Finset.mem_image_of_mem vLab (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)
  have hBS : B = ↑(Finset.univ.filter fun p => vLab p ∈ S) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_filter, hmemS]
    exact ⟨fun hp => ⟨Finset.mem_univ p, hp⟩, fun hp => hp.2⟩
  have hdvd : (∑ i ∈ S, vSubSizesF i) ∣ 245520 := by
    have hsum : (∑ i ∈ S, vSubSizesF i) =
        ∑ i ∈ S, (Finset.univ.filter (fun p : Fin nPts => vLab p = i)).card :=
      Finset.sum_congr rfl fun i _ => by rw [card_vLab]
    rw [hsum, Finset.sum_card_fiberwise_eq_card_filter, ← Set.ncard_coe_finset, ← hBS]
    have h := hB.ncard_dvd_card ⟨root, hrB⟩
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have h0S : (0 : Fin 7) ∈ S := by rw [← vLab_root]; exact (hmemS root).mpr hrB
  have hroot : ∀ p, vLab p = 0 → p = root := fun p hp =>
    eq_of_vLab_eq_of_size_one (i := 0) rfl hp vLab_root
  have hneg : ∀ p, vLab p = 1 → p = negRoot := fun p hp =>
    eq_of_vLab_eq_of_size_one (i := 1) rfl hp vLab_negRoot
  rcases vSubSizes_blocks S h0S hdvd with hS | hS | hS
  · left
    ext p
    rw [Set.mem_singleton_iff, ← hmemS, hS, Finset.mem_singleton]
    exact ⟨hroot p, fun h => h ▸ vLab_root⟩
  · right; left
    ext p
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, ← hmemS, hS, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (hroot p h)
      · exact Or.inr (hneg p h)
    · rintro (h | h)
      · exact Or.inl (h ▸ vLab_root)
      · exact Or.inr (h ▸ vLab_negRoot)
  · right; right
    ext p
    refine ⟨fun _ => Set.mem_univ p, fun _ => (hmemS p).mp ?_⟩
    rw [hS]
    exact Finset.mem_univ (vLab p)

theorem stabilizer_root_le_cases {K : Subgroup J} (hK : MulAction.stabilizer J root ≤ K) :
    K = MulAction.stabilizer J root ∨
      K = MulAction.stabilizer J ({root, negRoot} : Set (Fin nPts)) ∨ K = ⊤ := by
  have hB := MulAction.IsBlock.of_orbit hK
  have hst := MulAction.stabilizer_orbit_eq hK
  rcases isBlock_root_cases (MulAction.mem_orbit_self root) hB with h | h | h
  · left
    rw [← hst, h, MulAction.stabilizer_singleton]
  · right; left
    rw [← hst, h]
  · right; right
    rw [← hst, h, MulAction.stabilizer_univ]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
