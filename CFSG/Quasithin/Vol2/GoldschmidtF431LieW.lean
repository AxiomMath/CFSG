module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Endgame

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.F7

universe u v

section Lie

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M]

structure F431LieW (T M1 M2 : Subgroup Mb) (I : Finset Mb) : Prop where
  sylow : IsSylowTwoOf T ⊤
  T_le₁ : T ≤ M1
  T_le₂ : T ≤ M2
  mem_T : ∀ i ∈ I, i ∈ T
  order_two : ∀ i ∈ I, orderOf i = 2
  two_le : 2 ≤ I.card
  rep : ∀ x : Mb, orderOf x = 2 → ∃! i, i ∈ I ∧ IsConj i x
  fusion : ∀ x ∈ T, orderOf x = 2 → ∃ i ∈ I,
    (∃ m ∈ M1, m * x * m⁻¹ = i) ∨ (∃ m ∈ M2, m * x * m⁻¹ = i)

variable {T M1 M2 : Subgroup Mb} {I : Finset Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431LieW.exists_conj (D : F431LieW T M1 M2 I) (C : F431Comp M1 M2 b1 b2) {x : Mb}
    (hx : x ∈ T) (hxo : orderOf x = 2) :
    ∃ i ∈ I, IsConj i x ∧ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 x) := by
  obtain ⟨i, hiI, ⟨m, hm, hmx⟩ | ⟨m, hm, hmx⟩⟩ := D.fusion x hx hxo
  · refine ⟨i, hiI, isConj_iff.mpr ⟨m⁻¹, ?_⟩, ?_⟩
    · rw [← hmx]
      group
    · have hxM : x ∈ M1 := D.T_le₁ hx
      have hmxM : m * x * m⁻¹ ∈ M1 := M1.mul_mem (M1.mul_mem hm hxM) (M1.inv_mem hm)
      refine isConj_iff.mpr ⟨(b1 ⟨m, hm⟩)⁻¹, ?_⟩
      rw [← hmx, amalgamMap_of_mem₁ b1 b2 hmxM, amalgamMap_of_mem₁ b1 b2 hxM]
      have : (⟨m * x * m⁻¹, hmxM⟩ : M1) = ⟨m, hm⟩ * ⟨x, hxM⟩ * ⟨m, hm⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      group
  · refine ⟨i, hiI, isConj_iff.mpr ⟨m⁻¹, ?_⟩, ?_⟩
    · rw [← hmx]
      group
    · have hxM : x ∈ M2 := D.T_le₂ hx
      have hmxM : m * x * m⁻¹ ∈ M2 := M2.mul_mem (M2.mul_mem hm hxM) (M2.inv_mem hm)
      refine isConj_iff.mpr ⟨(b2 ⟨m, hm⟩)⁻¹, ?_⟩
      rw [← hmx, amalgamMap_of_mem₂ b1 b2 C.agree hmxM, amalgamMap_of_mem₂ b1 b2 C.agree hxM]
      have : (⟨m * x * m⁻¹, hmxM⟩ : M2) = ⟨m, hm⟩ * ⟨x, hxM⟩ * ⟨m, hm⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      group

theorem F431LieW.lemma_F435 (D : F431LieW T M1 M2 I) (C : F431Comp M1 M2 b1 b2)
    (hnf : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    {i j : Mb} (hi : i ∈ T) (hj : j ∈ T) (hio : orderOf i = 2) (hjo : orderOf j = 2) :
    IsConj i j ↔ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  obtain ⟨i₀, hi₀I, hi₀c, hi₀φ⟩ := D.exists_conj C hi hio
  obtain ⟨j₀, hj₀I, hj₀c, hj₀φ⟩ := D.exists_conj C hj hjo
  constructor
  · intro h
    have h1 : IsConj i₀ j₀ := (hi₀c.trans h).trans hj₀c.symm
    have hij : j₀ = i₀ := by
      obtain ⟨w, -, huniq⟩ := D.rep i₀ (D.order_two i₀ hi₀I)
      exact (huniq j₀ ⟨hj₀I, h1.symm⟩).trans (huniq i₀ ⟨hi₀I, IsConj.refl i₀⟩).symm
    rw [hij] at hj₀φ
    exact hi₀φ.symm.trans hj₀φ
  · intro h
    have h1 : IsConj (amalgamMap b1 b2 i₀) (amalgamMap b1 b2 j₀) := (hi₀φ.trans h).trans hj₀φ.symm
    have hij : i₀ = j₀ := by
      by_contra hne
      exact hnf i₀ hi₀I j₀ hj₀I hne h1
    rw [hij] at hi₀c
    exact hi₀c.symm.trans hj₀c

variable [Finite Mb]

theorem F431LieW.fusion_in (D : F431LieW T M1 M2 I) (C : F431Comp M1 M2 b1 b2)
    (hnf : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    {K : Subgroup Mb} (hK : IsSylowTwoOf T K)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, amalgamMap b1 b2 (a * b) = amalgamMap b1 b2 a * amalgamMap b1 b2 b)
    {v x : Mb} (hv : v ∈ T) (hvo : orderOf v = 2) (hx : x ∈ K) (hxo : orderOf x = 2) :
    IsConj v x ↔ IsConj (amalgamMap b1 b2 v) (amalgamMap b1 b2 x) := by
  obtain ⟨m, hm, hi⟩ := exists_conj_mem_of_isSylowTwoOf_involution hK hx hxo
  have hxi : IsConj x (m⁻¹ * x * m) := isConj_iff.mpr ⟨m⁻¹, by simp⟩
  have hio : orderOf (m⁻¹ * x * m) = 2 := by
    rw [← hxo]
    exact (CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hxi).symm
  have hone : amalgamMap b1 b2 1 = 1 := by
    have h11 : amalgamMap b1 b2 (1 * 1) = amalgamMap b1 b2 1 * amalgamMap b1 b2 1 :=
      hmul 1 K.one_mem 1 K.one_mem
    rw [mul_one] at h11
    exact (mul_eq_left.mp h11.symm)
  have hinv : amalgamMap b1 b2 m⁻¹ = (amalgamMap b1 b2 m)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hmul _ (K.inv_mem hm) _ hm, inv_mul_cancel, hone]
  have hφi : amalgamMap b1 b2 (m⁻¹ * x * m) =
      (amalgamMap b1 b2 m)⁻¹ * amalgamMap b1 b2 x * amalgamMap b1 b2 m := by
    rw [hmul _ (K.mul_mem (K.inv_mem hm) hx) _ hm, hmul _ (K.inv_mem hm) _ hx, hinv]
  have hconj : IsConj (amalgamMap b1 b2 x) (amalgamMap b1 b2 (m⁻¹ * x * m)) :=
    isConj_iff.mpr ⟨(amalgamMap b1 b2 m)⁻¹, by rw [hφi]; simp⟩
  have h435 := D.lemma_F435 C hnf hv hi hvo hio
  constructor
  · intro h
    exact (h435.mp (h.trans hxi)).trans hconj.symm
  · intro h
    exact (h435.mpr (h.trans hconj)).trans hxi.symm

omit [Finite Mb] in
theorem F431LieW.exists_conj_image [Finite M] (D : F431LieW T M1 M2 I) (C : F431Comp M1 M2 b1 b2)
    (hSyl : IsSylowTwoOf ((T.subgroupOf M1).map b1) ⊤) {x : M} (hx : orderOf x = 2) :
    ∃ i ∈ I, IsConj (amalgamMap b1 b2 i) x := by
  have h2 : x ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact hx ▸ pow_orderOf_eq_one x
  have hp : IsPGroup 2 (Subgroup.zpowers x) :=
    BenderStart.isPGroup_zpowers_of_pow_eq_one (k := 1) h2
  obtain ⟨g, -, hg⟩ := F7.isSylowTwoOf_exists_conj_le hSyl (le_top : Subgroup.zpowers x ≤ ⊤) hp
  obtain ⟨y, hyT, hyx⟩ := Subgroup.mem_map.mp (mem_conjSub.mp (hg (Subgroup.mem_zpowers x)))
  have hxy : IsConj x (b1 y) := by
    rw [hyx]
    exact isConj_iff.mpr ⟨g⁻¹, by simp⟩
  have hyo : orderOf (y : Mb) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective b1 C.inj₁ y,
      ← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hxy]
    exact hx
  have hyT' : (y : Mb) ∈ T := hyT
  have hφy : amalgamMap b1 b2 (y : Mb) = b1 y := amalgamMap_of_mem₁ b1 b2 y.2
  obtain ⟨i, hiI, -, hiφ⟩ := D.exists_conj C hyT' hyo
  refine ⟨i, hiI, ?_⟩
  rw [hφy] at hiφ
  exact hiφ.trans hxy.symm

theorem F431LieW.card_eq [Finite M] (D : F431LieW T M1 M2 I) (C : F431Comp M1 M2 b1 b2)
    (hSyl : IsSylowTwoOf ((T.subgroupOf M1).map b1) ⊤)
    (hnf : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    (hc : ∀ i ∈ I,
      (Subgroup.centralizer ({i} : Set Mb) ≤ M1 ∧
        Subgroup.centralizer ({amalgamMap b1 b2 i} : Set M) ≤ b1.range) ∨
      (Subgroup.centralizer ({i} : Set Mb) ≤ M2 ∧
        Subgroup.centralizer ({amalgamMap b1 b2 i} : Set M) ≤ b2.range)) :
    Nat.card Mb = Nat.card M := by
  classical
  have hSyl1 : IsSylowTwoOf T M1 := F7.isSylowTwoOf_mono_right D.sylow D.T_le₁ le_top
  have hSyl2 : IsSylowTwoOf T M2 := F7.isSylowTwoOf_mono_right D.sylow D.T_le₂ le_top
  obtain ⟨z, hzI⟩ : I.Nonempty := Finset.card_pos.mp (by have := D.two_le; omega)
  obtain ⟨z', hz'I, hz'ne⟩ := Finset.exists_mem_ne (show 1 < I.card from D.two_le) z
  have hzo := D.order_two z hzI
  have hz'o := D.order_two z' hz'I
  have huz : ¬ IsConj z z' := by
    intro h
    obtain ⟨w, -, huniq⟩ := D.rep z hzo
    exact hz'ne ((huniq z' ⟨hz'I, h.symm⟩).trans (huniq z ⟨hzI, IsConj.refl z⟩).symm)
  have hφord : ∀ i ∈ I, orderOf (amalgamMap b1 b2 i) = 2 := fun i hi => by
    rw [orderOf_amalgamMap_of_mem₁ C (D.T_le₁ (D.mem_T i hi))]
    exact D.order_two i hi
  have hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 z') :=
    hnf z hzI z' hz'I hz'ne.symm
  have hT' : ∀ w ∈ I.image (amalgamMap b1 b2), orderOf w = 2 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact hφord i hi
  have hTrep' : ∀ x : M, orderOf x = 2 →
      ∃! w, w ∈ I.image (amalgamMap b1 b2) ∧ IsConj w x := by
    intro x hx
    obtain ⟨i, hiI, hic⟩ := D.exists_conj_image C hSyl hx
    refine ⟨amalgamMap b1 b2 i, ⟨Finset.mem_image_of_mem _ hiI, hic⟩, ?_⟩
    rintro w ⟨hwT, hwc⟩
    obtain ⟨j, hjI, rfl⟩ := Finset.mem_image.mp hwT
    by_cases hij : i = j
    · rw [hij]
    · exact absurd (hic.trans hwc.symm) (hnf i hiI j hjI hij)
  have hinj : Set.InjOn (amalgamMap b1 b2) (I : Set Mb) := by
    intro i hi j hj hij
    by_contra hne
    exact hnf i hi j hj hne (by rw [hij])
  refine card_eq_of_transversal_data hzo hz'o huz (hφord z hzI) (hφord z' hz'I) hnc I
    D.order_two D.rep (I.image (amalgamMap b1 b2)) hT' hTrep' (amalgamMap b1 b2) hinj
    (fun w' => Finset.mem_image) hzI hz'I rfl rfl ?_
  intro w hw
  rcases hc w hw with ⟨h, hcw⟩ | ⟨h, hcw⟩
  · obtain ⟨ψ, hψi, hψr, hψw, hψx⟩ := exists_centralizer_hom b1 C.inj₁
      (fun a ha => amalgamMap_of_mem₁ b1 b2 ha) h hcw
    refine ⟨ψ, hψi, hψr, hψw, fun x hxo => ?_, fun x hxo => ?_⟩
    · rw [hψx x]
      exact D.fusion_in C hnf hSyl1 (fun a ha b hb => amalgamMap_mul₁ b1 b2 ha hb)
        (D.mem_T z hzI) hzo (h x.2) hxo
    · rw [hψx x]
      exact D.fusion_in C hnf hSyl1 (fun a ha b hb => amalgamMap_mul₁ b1 b2 ha hb)
        (D.mem_T z' hz'I) hz'o (h x.2) hxo
  · obtain ⟨ψ, hψi, hψr, hψw, hψx⟩ := exists_centralizer_hom b2 C.inj₂
      (fun a ha => amalgamMap_of_mem₂ b1 b2 C.agree ha) h hcw
    refine ⟨ψ, hψi, hψr, hψw, fun x hxo => ?_, fun x hxo => ?_⟩
    · rw [hψx x]
      exact D.fusion_in C hnf hSyl2 (fun a ha b hb => amalgamMap_mul₂ b1 b2 C.agree ha hb)
        (D.mem_T z hzI) hzo (h x.2) hxo
    · rw [hψx x]
      exact D.fusion_in C hnf hSyl2 (fun a ha b hb => amalgamMap_mul₂ b1 b2 C.agree ha hb)
        (D.mem_T z' hz'I) hz'o (h x.2) hxo

end Lie

end CFSG.Quasithin.H13.F431
