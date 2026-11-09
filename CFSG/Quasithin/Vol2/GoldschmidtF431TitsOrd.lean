module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsLie

section

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open

universe u v

section Lemma433

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431LieI.lemma_F433 (D : F431LieI T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range) :
    IsSylowTwoOf ((T.subgroupOf M1).map b1) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup M := (T.subgroupOf M1).map b1 with hP
  have hzM1 : z ∈ M1 := D.T_le₁ D.z_mem
  have hTp : IsPGroup 2 (T.subgroupOf M1) :=
    D.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe D.T_le₁).symm
  have hPp : IsPGroup 2 P := hTp.of_equiv (Subgroup.equivMapOfInjective _ b1 C.inj₁)
  have hSylM1 : IsSylowTwoOf P b1.range := by
    refine F7.isSylowTwoOf_of_relIndex (Subgroup.map_le_range b1 _) hPp ?_
    have h1 : P.relIndex b1.range = (T.subgroupOf M1).relIndex ⊤ := by
      rw [hP, MonoidHom.range_eq_map]
      exact Subgroup.relIndex_map_map_of_injective _ _ C.inj₁
    rw [h1, Subgroup.relIndex_top_right]
    exact (F7.isSylowTwoOf_mono_right D.sylow D.T_le₁ le_top).2.2
  have hzP : b1 ⟨z, hzM1⟩ ∈ P := Subgroup.mem_map.mpr ⟨⟨z, hzM1⟩, D.z_mem, rfl⟩
  have hz1 : b1 ⟨z, hzM1⟩ ≠ 1 := by
    intro h
    have : (⟨z, hzM1⟩ : M1) = 1 := C.inj₁ (by rw [h, map_one])
    have hz1' : z = 1 := congrArg Subtype.val this
    have := D.hz
    rw [hz1', orderOf_one] at this
    omega
  by_contra hnot
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hPneS : P ≠ (S : Subgroup M) := by
    intro h
    apply hnot
    refine F7.isSylowTwoOf_of_relIndex le_top hPp ?_
    rw [Subgroup.relIndex_top_right, h]
    exact S.not_dvd_index
  obtain ⟨n, hnS, hnN, hnP⟩ :=
    exists_mem_normalizer_not_mem_of_isPGroup S.isPGroup' hPS hPneS
  set N : Subgroup M := P ⊔ Subgroup.zpowers n with hN
  have hNS : N ≤ S := sup_le hPS (Subgroup.zpowers_le.2 hnS)
  have hNp : IsPGroup 2 N := S.isPGroup'.to_le hNS
  have hNnorm : N ≤ Subgroup.normalizer (P : Set M) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hnN)
  have hnN' : n ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  have hPN : P ≤ N := le_sup_left
  have : Nontrivial P := ⟨⟨⟨_, hzP⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  have hcentP := hPp.center_nontrivial
  obtain ⟨w0, hw0⟩ := exists_ne (1 : Subgroup.center P)
  have hz0P : ((w0 : P) : M) ∈ P := (w0 : P).2
  have hz0c : ∀ y ∈ P, y * ((w0 : P) : M) = ((w0 : P) : M) * y := fun y hy => by
    have := Subgroup.mem_center_iff.mp w0.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hz0ne : ((w0 : P) : M) ≠ 1 := by
    intro h
    apply hw0
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have : Group.IsNilpotent N := hNp.isNilpotent
  set Z0 : Subgroup N := (P ⊓ Subgroup.centralizer (P : Set M)).subgroupOf N with hZ0
  have hZ0n : Z0.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxP, hxc⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)
    have hgn : (g : M) ∈ Subgroup.normalizer (P : Set M) := hNnorm g.2
    have hgn' : (g : M)⁻¹ ∈ Subgroup.normalizer (P : Set M) :=
      (Subgroup.normalizer (P : Set M)).inv_mem hgn
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact (Subgroup.mem_normalizer_iff.mp hgn _).mp hxP
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (g : M)⁻¹ * y * (g : M) ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp hgn' y).mp hy
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc _ hy'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc y * ((g : M) * (x : M) * (g : M)⁻¹)
          = (g : M) * (((g : M)⁻¹ * y * (g : M)) * (x : M)) * (g : M)⁻¹ := by group
        _ = (g : M) * ((x : M) * ((g : M)⁻¹ * y * (g : M))) * (g : M)⁻¹ := by rw [hcomm]
        _ = (g : M) * (x : M) * (g : M)⁻¹ * y := by group
  have hZ0ne : Z0 ≠ ⊥ := by
    intro h
    have hmem : (⟨((w0 : P) : M), hPN hz0P⟩ : N) ∈ Z0 :=
      Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mpr ⟨hz0P, Subgroup.mem_centralizer_iff.mpr hz0c⟩)
    rw [h, Subgroup.mem_bot] at hmem
    exact hz0ne (congrArg Subtype.val hmem)
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hZ0ne
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf
  have haC : (a : N) ∈ Subgroup.center N := a.2.2
  obtain ⟨hawP, hawc⟩ := Subgroup.mem_inf.mp
    (Subgroup.mem_subgroupOf.mp (a.2.1 : (a : N) ∈ Z0))
  set w : M := ((a : N) : M) with hw
  have hw1 : w ≠ 1 := by
    intro h
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hwN : ∀ x ∈ N, x * w = w * x := fun x hx => by
    have := Subgroup.mem_center_iff.mp haC ⟨x, hx⟩
    exact congrArg Subtype.val this
  obtain ⟨y, hyT, hyw⟩ := Subgroup.mem_map.mp hawP
  have hyTT : (y : Mb) ∈ T := hyT
  have hy1 : (y : Mb) ≠ 1 := by
    intro h
    apply hw1
    have : y = 1 := Subtype.ext h
    rw [← hyw, this, map_one]
  have hcomm : ∀ x ∈ T, x * (y : Mb) = (y : Mb) * x := by
    intro x hx
    have hxP : b1 ⟨x, D.T_le₁ hx⟩ ∈ P := Subgroup.mem_map.mpr ⟨⟨x, D.T_le₁ hx⟩, hx, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hawc _ hxP
    rw [← hyw, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (C.inj₁ h1)
  obtain ⟨m, hm, hmeq⟩ := D.center_T (y : Mb) hyTT hcomm hy1
  have hmM1 : m ∈ M1 := (Subgroup.mem_inf.mp hm).1
  set m' : M := b1 ⟨m, hmM1⟩ with hm'
  set zz : M := b1 ⟨z, hzM1⟩ with hzz
  have hwm : w = m' * zz * m'⁻¹ := by
    rw [← hyw]
    have : y = ⟨m, hmM1⟩ * ⟨z, hzM1⟩ * ⟨m, hmM1⟩⁻¹ := Subtype.ext (by simpa using hmeq.symm)
    rw [this, map_mul, map_mul, map_inv]
  have hzzφ : amalgamMap b1 b2 z = zz := amalgamMap_of_mem₁ b1 b2 hzM1
  have hm'range : m' ∈ b1.range := ⟨_, rfl⟩
  have hCw : Subgroup.centralizer ({w} : Set M) ≤ b1.range := by
    intro x hx
    have hx' : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hcz : m'⁻¹ * x * m' ∈ Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) := by
      rw [hzzφ, Subgroup.mem_centralizer_singleton_iff]
      calc m'⁻¹ * x * m' * zz = m'⁻¹ * (x * (m' * zz * m'⁻¹)) * m' := by group
        _ = m'⁻¹ * ((m' * zz * m'⁻¹) * x) * m' := by rw [← hwm, hx']
        _ = zz * (m'⁻¹ * x * m') := by group
    have := hb hcz
    have hx2 : x = m' * (m'⁻¹ * x * m') * m'⁻¹ := by group
    rw [hx2]
    exact b1.range.mul_mem (b1.range.mul_mem hm'range this) (b1.range.inv_mem hm'range)
  have hNle : N ≤ b1.range := fun x hx => hCw (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hwN x hx)
  have hNeq := eq_of_isSylowTwoOf_of_isPGroup hSylM1 hPN hNle hNp
  exact hnP (hNeq ▸ hnN')

end Lemma433

section Lemma434

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M]
  {T M1 M2 : Subgroup Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431LieI.orderOf_amalgamMap₁ (D : F431LieI T M1 M2 z t) (C : F431Comp M1 M2 b1 b2) :
    orderOf (amalgamMap b1 b2 z) = 2 := by
  rw [amalgamMap_of_mem₁ b1 b2 (D.T_le₁ D.z_mem), orderOf_injective b1 C.inj₁]
  exact (Subgroup.orderOf_coe (⟨z, D.T_le₁ D.z_mem⟩ : M1)).symm.trans D.hz

theorem F431LieI.orderOf_amalgamMap₂ (D : F431LieI T M1 M2 z t) (C : F431Comp M1 M2 b1 b2) :
    orderOf (amalgamMap b1 b2 t) = 2 := by
  rw [amalgamMap_of_mem₂ b1 b2 C.agree (D.T_le₂ D.t_mem), orderOf_injective b2 C.inj₂]
  exact (Subgroup.orderOf_coe (⟨t, D.T_le₂ D.t_mem⟩ : M2)).symm.trans D.ht

theorem F431LieI.lemma_F434 (D : F431LieI T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range) :
    Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) = b1.range ∧
    Subgroup.normalizer (Subgroup.zpowers (amalgamMap b1 b2 z) : Set M) = b1.range ∧
    ∀ g : M, Subgroup.zpowers (amalgamMap b1 b2 z) ⊓
        conjSub g (Subgroup.zpowers (amalgamMap b1 b2 z)) ≠ ⊥ →
      conjSub g (Subgroup.zpowers (amalgamMap b1 b2 z)) =
        Subgroup.zpowers (amalgamMap b1 b2 z) := by
  have hzM1 : z ∈ M1 := D.T_le₁ D.z_mem
  have hcent : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) = b1.range := by
    refine le_antisymm hb ?_
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, amalgamMap_of_mem₁ b1 b2 hzM1]
    have hy : (y : Mb) ∈ Subgroup.centralizer ({z} : Set Mb) := by rw [D.cent_z]; exact y.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hy
  have hord := D.orderOf_amalgamMap₁ C
  refine ⟨hcent, ?_, fun g h => zpowers_involution_ti hord g h⟩
  rw [normalizer_zpowers_eq_centralizer hord, hcent]

end Lemma434

end CFSG.Quasithin

end

end

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
