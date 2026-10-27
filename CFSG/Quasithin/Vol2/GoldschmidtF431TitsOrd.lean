module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsSyl

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open

universe u v

section Lemma443

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

omit [Finite M] in
theorem F431LieI.fusion_in (D : F431LieI T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
    (hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) {K : Subgroup Mb}
    (hK : IsSylowTwoOf T K)
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
  have h435 := D.lemma_F435 C hnc hv hi hvo hio
  constructor
  · intro h
    exact (h435.mp (h.trans hxi)).trans hconj.symm
  · intro h
    exact (h435.mpr (h.trans hconj)).trans hxi.symm

theorem F431LieI.lemma_F443 (D : F431LieI T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t))
    (h442 : Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) ≤ b2.range) :
    Nat.card Mb = Nat.card M := by
  have hzM1 : z ∈ M1 := D.T_le₁ D.z_mem
  have htM2 : t ∈ M2 := D.T_le₂ D.t_mem
  have hφz : amalgamMap b1 b2 z = b1 ⟨z, hzM1⟩ := amalgamMap_of_mem₁ b1 b2 hzM1
  have hφt : amalgamMap b1 b2 t = b2 ⟨t, htM2⟩ := amalgamMap_of_mem₂ b1 b2 C.agree htM2
  have hzo := D.orderOf_amalgamMap₁ C
  have hto := D.orderOf_amalgamMap₂ C
  have hSyl := D.lemma_F433 C hb
  obtain ⟨hcentz, -, -⟩ := D.lemma_F434 C hb
  have hSyl1 : IsSylowTwoOf T M1 := F7.isSylowTwoOf_mono_right D.sylow D.T_le₁ le_top
  have hSyl2 : IsSylowTwoOf T M2 := F7.isSylowTwoOf_mono_right D.sylow D.T_le₂ le_top
  have hclM : ∀ x : M, orderOf x = 2 →
      IsConj (amalgamMap b1 b2 z) x ∨ IsConj (amalgamMap b1 b2 t) x := by
    intro x hx
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
    rcases D.classes _ hyo with h | h
    · left
      have := (D.lemma_F435 C hnc D.z_mem hyT' D.hz hyo).mp h
      rw [hφy] at this
      exact this.trans hxy.symm
    · right
      have := (D.lemma_F435 C hnc D.t_mem hyT' D.ht hyo).mp h
      rw [hφy] at this
      exact this.trans hxy.symm
  let φz : Subgroup.centralizer ({z} : Set Mb) →* M := b1.comp (Subgroup.inclusion D.cent_z.le)
  have hφzinj : Function.Injective φz := C.inj₁.comp (Subgroup.inclusion_injective _)
  have hφzrange : φz.range = Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) := by
    rw [hcentz]
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.1, D.cent_z ▸ y.2⟩, rfl⟩
  let φt : Subgroup.centralizer ({t} : Set Mb) →* M := b2.comp (Subgroup.inclusion D.cent_t)
  have hφtinj : Function.Injective φt := C.inj₂.comp (Subgroup.inclusion_injective _)
  have hφtrange : φt.range = Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hφt]
      have hc : (c : Mb) * t = t * (c : Mb) := Subgroup.mem_centralizer_singleton_iff.mp c.2
      show b2 (Subgroup.inclusion D.cent_t c) * b2 ⟨t, htM2⟩ =
        b2 ⟨t, htM2⟩ * b2 (Subgroup.inclusion D.cent_t c)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hc
    · intro hx
      obtain ⟨y, rfl⟩ := h442 hx
      have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
      rw [hφt, ← map_mul, ← map_mul] at hx'
      have hy := C.inj₂ hx'
      have hy' : (y : Mb) * t = t * (y : Mb) := congrArg Subtype.val hy
      exact ⟨⟨y.1, Subgroup.mem_centralizer_singleton_iff.mpr hy'⟩, rfl⟩
  refine card_eq_of_two_class_data D.hz D.ht D.not_conj D.classes hzo hto hnc hclM φz hφzinj
    hφzrange (fun h => by show b1 ⟨z, _⟩ = _; rw [hφz]) ?_ φt hφtinj hφtrange
    (fun h => by show b2 ⟨t, _⟩ = _; rw [hφt]) ?_
  · intro x hxo
    have hxM1 : (x : Mb) ∈ M1 := D.cent_z ▸ x.2
    have : φz x = amalgamMap b1 b2 (x : Mb) := (amalgamMap_of_mem₁ b1 b2 hxM1).symm
    rw [this]
    exact D.fusion_in C hnc hSyl1 (fun a ha b hb => amalgamMap_mul₁ b1 b2 ha hb) D.z_mem D.hz
      hxM1 hxo
  · intro x hxo
    have hxM2 : (x : Mb) ∈ M2 := D.cent_t x.2
    have : φt x = amalgamMap b1 b2 (x : Mb) := (amalgamMap_of_mem₂ b1 b2 C.agree hxM2).symm
    rw [this]
    exact D.fusion_in C hnc hSyl2 (fun a ha b hb => amalgamMap_mul₂ b1 b2 C.agree ha hb) D.z_mem
      D.hz hxM2 hxo

end Lemma443

section NonFusion

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431LieI.not_conj_of_card (D : F431LieI T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range) {r : ℕ}
    (hr1 : ¬ r ∣ Nat.card M1) (hr2 : r ∣ Nat.card (Subgroup.centralizer ({t} : Set Mb))) :
    ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t) := by
  intro h
  have htM2 : t ∈ M2 := D.T_le₂ D.t_mem
  have hφt : amalgamMap b1 b2 t = b2 ⟨t, htM2⟩ := amalgamMap_of_mem₂ b1 b2 C.agree htM2
  obtain ⟨hcentz, -, -⟩ := D.lemma_F434 C hb
  have e1 : Nat.card (Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M)) = Nat.card M1 := by
    rw [hcentz]
    exact (Nat.card_congr (MonoidHom.ofInjective C.inj₁).toEquiv).symm
  let φt : Subgroup.centralizer ({t} : Set Mb) →* M := b2.comp (Subgroup.inclusion D.cent_t)
  have hK : φt.range ≤ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) := by
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hφt]
    have hc : (c : Mb) * t = t * (c : Mb) := Subgroup.mem_centralizer_singleton_iff.mp c.2
    show b2 (Subgroup.inclusion D.cent_t c) * b2 ⟨t, htM2⟩ =
      b2 ⟨t, htM2⟩ * b2 (Subgroup.inclusion D.cent_t c)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  have hφtinj : Function.Injective φt := fun x y h =>
    Subgroup.inclusion_injective D.cent_t (C.inj₂ h)
  have hKcard : Nat.card φt.range = Nat.card (Subgroup.centralizer ({t} : Set Mb)) :=
    (Nat.card_congr (MonoidHom.ofInjective hφtinj).toEquiv).symm
  have hdvd : r ∣ Nat.card (Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M)) :=
    hr2.trans (hKcard ▸ Subgroup.card_dvd_of_le hK)
  rw [← card_centralizer_eq_of_isConj h, e1] at hdvd
  exact hr1 hdvd

end NonFusion

end CFSG.Quasithin
