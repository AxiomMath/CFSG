module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442QCount
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442QSyl

public section

namespace CFSG.Quasithin.Loc442Q

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431

universe u v

section Defs

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M] {M2 : Subgroup Mb}

@[expose] def xt (b2 : M2 →* M) (t : Mb) : Subgroup M :=
  ((Subgroup.centralizer ({t} : Set Mb)).subgroupOf M2).map b2

theorem mem_xt {b2 : M2 →* M} {t : Mb} {y : M} :
    y ∈ xt b2 t ↔ ∃ x : M2, (x : Mb) * t = t * (x : Mb) ∧ b2 x = y := by
  unfold xt
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hx), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hx), rfl⟩

end Defs

section Transfer

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

omit [Finite Mb] [Finite M] in
theorem xt_le_centralizer (C : F431Comp M1 M2 b1 b2) (htM2 : t ∈ M2) :
    xt b2 t ≤ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_xt.mp hy
  rw [Subgroup.mem_centralizer_singleton_iff, amalgamMap_of_mem₂ b1 b2 C.agree htM2, ← map_mul,
    ← map_mul]
  exact congrArg b2 (Subtype.ext hx)

omit [Finite Mb] [Finite M] in
theorem hnfI_of_zt (hI : ∀ i ∈ I, i = z ∨ i = t)
    (hnf : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  intro i hi j hj hij
  rcases hI i hi with rfl | rfl <;> rcases hI j hj with rfl | rfl
  · exact absurd rfl hij
  · exact hnf
  · exact fun h => hnf h.symm
  · exact absurd rfl hij

omit [Finite Mb] [Finite M] in
theorem hnf_of_hnfI (D : F431LieK T M1 M2 I z) (hI : ∀ i ∈ I, i = z ∨ i = t) (ht : t ∈ I)
    (hnfI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j)) :
    ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t) := by
  refine hnfI z D.z_mem t ht fun h => ?_
  have hsub : I ⊆ {z} := fun i hi => by
    rcases hI i hi with rfl | rfl
    · exact Finset.mem_singleton_self _
    · rw [← h]; exact Finset.mem_singleton_self _
  have := Finset.card_le_card hsub
  have h2 := D.two_le
  rw [Finset.card_singleton] at this
  omega

end Transfer

section Swap

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem swapComp (C : F431Comp M1 M2 b1 b2) : F431Comp M2 M1 b2 b1 :=
  ⟨C.inj₂, C.inj₁, fun g h2 h1 => (C.agree g h1 h2).symm⟩

theorem amalgamMap_swap (C : F431Comp M1 M2 b1 b2) :
    amalgamMap b2 b1 = amalgamMap b1 b2 := by
  funext g
  by_cases h1 : g ∈ M1
  · rw [amalgamMap_of_mem₁ b1 b2 h1]
    by_cases h2 : g ∈ M2
    · rw [amalgamMap_of_mem₁ b2 b1 h2, C.agree g h1 h2]
    · unfold amalgamMap
      simp [h1, h2]
  · by_cases h2 : g ∈ M2
    · rw [amalgamMap_of_mem₁ b2 b1 h2, amalgamMap_of_mem₂ b1 b2 C.agree h2]
    · unfold amalgamMap
      simp [h1, h2]

theorem swapLieK [Finite Mb] (D : F431LieK T M1 M2 I z) : F431LieK T M2 M1 I z where
  sylow := D.sylow
  T_le₁ := D.T_le₂
  T_le₂ := D.T_le₁
  mem_T := D.mem_T
  order_two := D.order_two
  z_mem := D.z_mem
  two_le := D.two_le
  rep := D.rep
  cent i hi := (D.cent i hi).symm
  cent_z := D.cent_z.symm
  center_T w hw hc h1 := by
    obtain ⟨m, hm, e⟩ := D.center_T w hw hc h1
    exact ⟨m, by rwa [inf_comm], e⟩
  ag D' hD' := (D.ag D' hD').symm

end Swap

section Count

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

omit [Finite M] in
theorem card_orb₁ (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hnfI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    (ht : t ∈ I) (cent_z : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range) :
    Nat.card (OrbSet (Subgroup.centralizer ({z} : Set Mb)) (sig z t)) =
      Nat.card (OrbSet (Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M))
        (sig (amalgamMap b1 b2 z) (amalgamMap b1 b2 t))) := by
  have hzT : z ∈ T := D.mem_T z D.z_mem
  have htT : t ∈ T := D.mem_T t ht
  have hz1 : z ∈ M1 := D.T_le₁ hzT
  have hφz : amalgamMap b1 b2 z = b1 ⟨z, hz1⟩ := amalgamMap_of_mem₁ b1 b2 hz1
  have hSyl1 : IsSylowTwoOf T M1 := F7.isSylowTwoOf_mono_right D.sylow D.T_le₁ le_top
  have hfus : ∀ {x : Mb}, x ∈ M1 → orderOf x = 2 →
      (IsConj t x ↔ IsConj (amalgamMap b1 b2 t) (amalgamMap b1 b2 x)) := fun hx hxo =>
    D.fusion_in C hnfI hSyl1 (fun a ha b hb => amalgamMap_mul₁ b1 b2 ha hb) htT
      (D.order_two t ht) hx hxo
  have hto : orderOf (amalgamMap b1 b2 t) = 2 := by
    rw [orderOf_phi_of_mem₁ C (D.T_le₁ htT)]
    exact D.order_two t ht
  have hS : sig z t ⊆ (M1 : Set Mb) := fun c hc =>
    cent_z (Subgroup.mem_centralizer_singleton_iff.mpr hc.2)
  refine Nat.card_congr (OrbSet.congrHom b1 C.inj₁ cent_z ?_ hS ?_ ?_)
  · intro y
    constructor
    · intro hy
      obtain ⟨w, rfl⟩ := hb hy
      refine ⟨w, ?_, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.mp hy
      rw [hφz, ← map_mul, ← map_mul] at h
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (C.inj₁ h))
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hφz, ← map_mul, ← map_mul]
      exact congrArg b1 (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx))
  · intro c hc
    have hc1 : c ∈ M1 := hS hc
    have hco : orderOf c = 2 := by
      rw [← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hc.1]
      exact D.order_two t ht
    refine ⟨?_, ?_⟩
    · have := (hfus hc1 hco).mp hc.1
      rwa [amalgamMap_of_mem₁ b1 b2 hc1] at this
    · rw [hφz, ← map_mul, ← map_mul]
      exact congrArg b1 (Subtype.ext hc.2)
  · intro c' hc'
    obtain ⟨w, hw⟩ := hb (Subgroup.mem_centralizer_singleton_iff.mpr hc'.2)
    have hwz : (w : Mb) * z = z * (w : Mb) := by
      have h := hc'.2
      rw [← hw, hφz, ← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (C.inj₁ h)
    have hwo : orderOf (w : Mb) = 2 := by
      rw [Subgroup.orderOf_coe, ← orderOf_injective b1 C.inj₁ w, hw,
        ← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hc'.1, hto]
    have hconj : IsConj t (w : Mb) := by
      refine (hfus w.2 hwo).mpr ?_
      rw [amalgamMap_of_mem₁ b1 b2 w.2]
      have : b1 ⟨(w : Mb), w.2⟩ = c' := hw
      rw [this]
      exact hc'.1
    exact ⟨(w : Mb), ⟨hconj, hwz⟩, hw⟩

omit [Finite M] in
theorem card_orb₂ (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hnfI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    (cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2) :
    Nat.card (OrbSet (Subgroup.centralizer ({t} : Set Mb)) (sig t z)) =
      Nat.card (OrbSet (xt b2 t)
        {c : M | IsConj (amalgamMap b1 b2 z) c ∧ c ∈ xt b2 t}) := by
  have hzT : z ∈ T := D.mem_T z D.z_mem
  have hSyl2 : IsSylowTwoOf T M2 := F7.isSylowTwoOf_mono_right D.sylow D.T_le₂ le_top
  have hfus : ∀ {x : Mb}, x ∈ M2 → orderOf x = 2 →
      (IsConj z x ↔ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 x)) := fun hx hxo =>
    D.fusion_in C hnfI hSyl2 (fun a ha b hb => amalgamMap_mul₂ b1 b2 C.agree ha hb) hzT
      (D.order_two z D.z_mem) hx hxo
  have hzo : orderOf (amalgamMap b1 b2 z) = 2 := by
    rw [orderOf_phi_of_mem₁ C (D.T_le₁ hzT)]
    exact D.order_two z D.z_mem
  have hS : sig t z ⊆ (M2 : Set Mb) := fun c hc =>
    cent_t (Subgroup.mem_centralizer_singleton_iff.mpr hc.2)
  refine Nat.card_congr (OrbSet.congrHom b2 C.inj₂ cent_t ?_ hS ?_ ?_)
  · intro y
    rw [mem_xt]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_centralizer_singleton_iff.mp hx, rfl⟩
  · intro c hc
    have hc2 : c ∈ M2 := hS hc
    have hco : orderOf c = 2 := by
      rw [← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hc.1]
      exact D.order_two z D.z_mem
    refine ⟨?_, mem_xt.mpr ⟨⟨c, hc2⟩, hc.2, rfl⟩⟩
    have := (hfus hc2 hco).mp hc.1
    rwa [amalgamMap_of_mem₂ b1 b2 C.agree hc2] at this
  · intro c' hc'
    obtain ⟨x, hx, hxc⟩ := mem_xt.mp hc'.2
    have hxo : orderOf (x : Mb) = 2 := by
      rw [Subgroup.orderOf_coe, ← orderOf_injective b2 C.inj₂ x, hxc,
        ← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hc'.1, hzo]
    have hconj : IsConj z (x : Mb) := by
      refine (hfus x.2 hxo).mpr ?_
      rw [amalgamMap_of_mem₂ b1 b2 C.agree x.2]
      have : b2 ⟨(x : Mb), x.2⟩ = c' := hxc
      rw [this]
      exact hc'.1
    exact ⟨(x : Mb), ⟨hconj, hx⟩, hxc⟩

omit [Finite M] in
theorem card_orb_xt (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hnfI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    (ht : t ∈ I) (cent_z : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range) :
    Nat.card (OrbSet (xt b2 t) {c : M | IsConj (amalgamMap b1 b2 z) c ∧ c ∈ xt b2 t}) =
      Nat.card (OrbSet (Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M))
        (sig (amalgamMap b1 b2 t) (amalgamMap b1 b2 z))) := by
  rw [← card_orb₂ D C hnfI cent_t, card_orbSet_comm t z, card_orb₁ D C hnfI ht cent_z hb,
    card_orbSet_comm]

end Count

end CFSG.Quasithin.Loc442Q
