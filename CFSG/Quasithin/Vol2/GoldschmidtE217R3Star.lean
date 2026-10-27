module

public import CFSG.Quasithin.Vol2.GoldschmidtE217Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtE217L2Dih
public import CFSG.Quasithin.Background.E2TwoProofY

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E217R3

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

structure Hyp2 (H T M V : Subgroup G) : Prop where
  hyp : E2.Hyp28 H T M V
  charTwo : CharTwo H
  two : (V ⊓ pCoreOf 2 H).relIndex V = 2
  V16 : Nat.card V = 2 ^ 4
  q32 : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hyp.elem H)
  res : twoResidual M ≤ Subgroup.centralizer (V : Set G)

theorem exists_vbar_aux (h : Hyp2 H T M V) :
    ∃ (x : G) (hxH : x ∈ H), x ∈ V ∧ x ∉ pCoreOf 2 H ∧
      E2P.starMap M H ⟨x, hxH⟩ * E2P.starMap M H ⟨x, hxH⟩ = 1 ∧
      E2P.starMap M H ⟨x, hxH⟩ ≠ 1 ∧ E2P.starMap M H ⟨x, hxH⟩ ∈ E2.star M H T ∧
      (∀ m ∈ E2.star M H M, m * E2P.starMap M H ⟨x, hxH⟩ = E2P.starMap M H ⟨x, hxH⟩ * m) ∧
      OddCube (E2P.starMap M H ⟨x, hxH⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := h.hyp.minParabolic
  have hHT : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := h.hyp.le_H
  obtain ⟨x, hxV, hxQ⟩ : ∃ x ∈ V, x ∉ pCoreOf 2 H := by
    by_contra hcon
    push Not at hcon
    exact h.hyp.not_le_pCoreOf hcon
  have hxH : x ∈ H := hVH hxV
  have hx2 : x * x = 1 := by simpa [pow_two] using h.hyp.elem.2 x hxV
  set π := E2P.starMap M H with hπ
  have hker : ∀ w : ↥H, π w = 1 ↔ (w : G) ∈ kerIn M H := fun w => by
    rw [hπ, E2P.starMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hQJ : pCoreOf 2 H ≤ kerIn M H := hmp.pCoreOf_le_kerIn
  have hVJ : kerIn M H ⊓ V ≤ pCoreOf 2 H := hmp.le_pCoreOf_of_isPGroup_of_le_kerIn
    ((B6.isPGroup_of_isElemAbelian h.hyp.elem).to_le inf_le_right) inf_le_left
  set v : E2.StarQuot M H := π ⟨x, hxH⟩ with hv
  have hv2 : v * v = 1 := by
    rw [hv, ← map_mul]
    have : (⟨x, hxH⟩ * ⟨x, hxH⟩ : ↥H) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hv1 : v ≠ 1 := by
    intro h1
    have := (hker ⟨x, hxH⟩).1 h1
    exact hxQ (hVJ ⟨this, hxV⟩)
  have hvT : v ∈ E2.star M H T := ⟨⟨x, hxH⟩, h.hyp.le_T hxV, rfl⟩
  have hTc : ∀ t : ↥H, (t : G) ∈ T → π t * v = v * π t := by
    intro t ht
    have htx : (t : G) * x * (t : G)⁻¹ ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (h.hyp.normal_T ht) x).mp hxV
      exact this
    have hdec := E2.forall_mem_or_mul_mem_of_relIndex_eq_two h.hyp.elem h.two hxV hxQ _ htx
    have hnQ : (t : G) * x * (t : G)⁻¹ ∉ pCoreOf 2 H := by
      intro hq
      apply hxQ
      have hQn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
      have := (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem t.2)) _).mp hq
      simpa [mul_assoc] using this
    rcases hdec with hd | hd
    · exact absurd hd.2 hnQ
    · have hq : x * ((t : G) * x * (t : G)⁻¹) ∈ pCoreOf 2 H := hd.2
      have e : π (t * ⟨x, hxH⟩ * t⁻¹) = π ⟨x, hxH⟩ := by
        have h1 : π (⟨x, hxH⟩⁻¹ * (t * ⟨x, hxH⟩ * t⁻¹)) = 1 := by
          rw [hker]
          have : ((⟨x, hxH⟩⁻¹ * (t * ⟨x, hxH⟩ * t⁻¹) : ↥H) : G) =
              x * ((t : G) * x * (t : G)⁻¹) := by
            have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
            simp [hxi]
          rw [this]
          exact hQJ hq
        rw [map_mul, map_inv] at h1
        exact (inv_mul_eq_one.1 h1).symm
      calc π t * v = π (t * ⟨x, hxH⟩) := by rw [hv, map_mul]
        _ = π ((t * ⟨x, hxH⟩ * t⁻¹) * t) := by rw [inv_mul_cancel_right]
        _ = π ⟨x, hxH⟩ * π t := by rw [map_mul, e]
        _ = v * π t := rfl
  have hOc : ∀ o : ↥H, (o : G) ∈ twoResidual M → π o * v = v * π o := by
    intro o ho
    have hox : (o : G) * x = x * (o : G) :=
      (Subgroup.mem_centralizer_iff.1 (h.res ho) x hxV).symm
    rw [hv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hox
  have hMc : ∀ m ∈ E2.star M H M, m * v = v * m := by
    set C : Subgroup G := M ⊓ ((Subgroup.centralizer ({v} : Set (E2.StarQuot M H))).comap π).map
      H.subtype with hC
    have hTC : T ≤ C := fun t ht => by
      refine ⟨hmp.le ht, ⟨⟨t, hHT ht⟩, ?_, rfl⟩⟩
      show π ⟨t, hHT ht⟩ ∈ Subgroup.centralizer ({v} : Set (E2.StarQuot M H))
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hTc ⟨t, hHT ht⟩ ht
    have hOC : twoResidual M ≤ C := fun o ho => by
      have hoH : o ∈ H := hMH (twoResidual_le M ho)
      refine ⟨twoResidual_le M ho, ⟨⟨o, hoH⟩, ?_, rfl⟩⟩
      show π ⟨o, hoH⟩ ∈ Subgroup.centralizer ({v} : Set (E2.StarQuot M H))
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hOc ⟨o, hoH⟩ ho
    have hMC : M ≤ C := by
      have hsyl : IsSylowTwoOf T M := B6.isSylowTwoOf_mono hmp.isSylow hmp.le hMH
      calc M = T ⊔ twoResidual M := (sup_twoResidual_eq hsyl).symm
        _ ≤ C := sup_le hTC hOC
    rintro _ ⟨m, hm, rfl⟩
    have hmC : (m : G) ∈ C := hMC hm
    obtain ⟨-, ⟨m', hm', hmm'⟩⟩ := hmC
    have hm'eq : m' = m := Subtype.ext hmm'
    rw [hm'eq] at hm'
    exact Subgroup.mem_centralizer_singleton_iff.mp hm'
  refine ⟨x, hxH, hxV, hxQ, hv2, hv1, hvT, hMc, ?_⟩
  intro g' n hn h1
  obtain ⟨g, rfl⟩ := E2P.starMap_surjective M H g'
  have e : v * (π g * v * (π g)⁻¹) = π (⟨x, hxH⟩ * (g * ⟨x, hxH⟩ * g⁻¹)) := by
    rw [hv, map_mul, map_mul, map_mul, map_inv]
  rw [e, ← map_pow] at h1 ⊢
  have hcoe : ∀ k : ℕ, (((⟨x, hxH⟩ * (g * ⟨x, hxH⟩ * g⁻¹)) ^ k : ↥H) : G) =
      (x * ((g : G) * x * (g : G)⁻¹)) ^ k := fun k => by
    simp
  have h2 := (hker _).1 h1
  rw [hcoe] at h2
  have h3 := E2.cube_mem_kerIn_of_relIndex_eq_two h.hyp h.charTwo h.V16 h.q32 h.two hxV hxQ g.2
    hn h2
  rw [hker, hcoe]
  exact h3

theorem exists_vbar (h : Hyp2 H T M V) :
    ∃ v : E2.StarQuot M H, v * v = 1 ∧ v ≠ 1 ∧ v ∈ E2.star M H T ∧
      (∀ m ∈ E2.star M H M, m * v = v * m) ∧ OddCube v := by
  obtain ⟨x, hxH, -, -, h2, h1, hT, hM, hO⟩ := exists_vbar_aux h
  exact ⟨_, h2, h1, hT, hM, hO⟩

end E217R3
