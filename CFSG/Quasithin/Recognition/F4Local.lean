module

public import CFSG.Quasithin.Recognition.F4Fusion
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open

universe u v

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M]

open Classical in
@[expose] noncomputable def amalgamMap {M1 M2 : Subgroup Mb} (b1 : M1 →* M) (b2 : M2 →* M) :
    Mb → M :=
  fun g => if h : g ∈ M1 then b1 ⟨g, h⟩ else if h2 : g ∈ M2 then b2 ⟨g, h2⟩ else 1

section AmalgamMap

variable {M1 M2 : Subgroup Mb} (b1 : M1 →* M) (b2 : M2 →* M)

theorem amalgamMap_of_mem₁ {g : Mb} (h : g ∈ M1) : amalgamMap b1 b2 g = b1 ⟨g, h⟩ := by
  unfold amalgamMap
  simp [h]

theorem amalgamMap_of_mem₂ (hb12 : ∀ g (h1 : g ∈ M1) (h2 : g ∈ M2), b1 ⟨g, h1⟩ = b2 ⟨g, h2⟩)
    {g : Mb} (h : g ∈ M2) : amalgamMap b1 b2 g = b2 ⟨g, h⟩ := by
  by_cases h1 : g ∈ M1
  · rw [amalgamMap_of_mem₁ b1 b2 h1]
    exact hb12 g h1 h
  · unfold amalgamMap
    simp [h1, h]

theorem amalgamMap_mul₁ {a b : Mb} (ha : a ∈ M1) (hb : b ∈ M1) :
    amalgamMap b1 b2 (a * b) = amalgamMap b1 b2 a * amalgamMap b1 b2 b := by
  rw [amalgamMap_of_mem₁ b1 b2 (M1.mul_mem ha hb), amalgamMap_of_mem₁ b1 b2 ha,
    amalgamMap_of_mem₁ b1 b2 hb]
  exact map_mul b1 ⟨a, ha⟩ ⟨b, hb⟩

theorem amalgamMap_mul₂ (hb12 : ∀ g (h1 : g ∈ M1) (h2 : g ∈ M2), b1 ⟨g, h1⟩ = b2 ⟨g, h2⟩)
    {a b : Mb} (ha : a ∈ M2) (hb : b ∈ M2) :
    amalgamMap b1 b2 (a * b) = amalgamMap b1 b2 a * amalgamMap b1 b2 b := by
  rw [amalgamMap_of_mem₂ b1 b2 hb12 (M2.mul_mem ha hb), amalgamMap_of_mem₂ b1 b2 hb12 ha,
    amalgamMap_of_mem₂ b1 b2 hb12 hb]
  exact map_mul b2 ⟨a, ha⟩ ⟨b, hb⟩

end AmalgamMap

section Lie

variable [Finite Mb] {T M1 M2 : Subgroup Mb} {z t : Mb}

structure F431Lie (T M1 M2 : Subgroup Mb) (z t : Mb) : Prop where
  sylow : IsSylowTwoOf T ⊤
  T_le₁ : T ≤ M1
  T_le₂ : T ≤ M2
  z_mem : z ∈ T
  t_mem : t ∈ T
  hz : orderOf z = 2
  ht : orderOf t = 2
  not_conj : ¬ IsConj z t
  classes : ∀ x : Mb, orderOf x = 2 → IsConj z x ∨ IsConj t x
  cent_z : Subgroup.centralizer ({z} : Set Mb) = M1
  cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2
  center_T : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ M1 ⊓ M2, m * z * m⁻¹ = w
  ag : ∀ D : Subgroup Mb, IsAGMember T D →
    Subgroup.normalizer (D : Set Mb) ≤ M1 ∨ Subgroup.normalizer (D : Set Mb) ≤ M2

structure F431Comp (M1 M2 : Subgroup Mb) (b1 : M1 →* M) (b2 : M2 →* M) : Prop where
  inj₁ : Function.Injective b1
  inj₂ : Function.Injective b2
  agree : ∀ g (h1 : g ∈ M1) (h2 : g ∈ M2), b1 ⟨g, h1⟩ = b2 ⟨g, h2⟩

variable {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431Lie.fusion_forward (D : F431Lie T M1 M2 z t) (C : F431Comp M1 M2 b1 b2) {i j : Mb}
    (hi : i ∈ T) (hj : j ∈ T) (hij : IsConj i j) :
    IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hij
  have hg : c * i * c⁻¹ ∈ T := by rw [hc]; exact hj
  have hg' : (c⁻¹)⁻¹ * i * c⁻¹ ∈ T := by simpa using hg
  obtain ⟨k, -, hk⟩ := fusion_transfer D.sylow D.T_le₁ D.T_le₂ D.ag (amalgamMap b1 b2)
    (b1.range ⊔ b2.range)
    (fun a ha b hb => amalgamMap_mul₁ b1 b2 ha hb)
    (fun a ha b hb => amalgamMap_mul₂ b1 b2 C.agree ha hb)
    (fun a ha => by
      rw [amalgamMap_of_mem₁ b1 b2 ha]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩)
    (fun a ha => by
      rw [amalgamMap_of_mem₂ b1 b2 C.agree ha]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩) hi hg'
  refine isConj_iff.mpr ⟨k⁻¹, ?_⟩
  have : (c⁻¹)⁻¹ * i * c⁻¹ = j := by simpa using hc
  rw [this] at hk
  simpa using hk

theorem F431Lie.lemma_F435 (D : F431Lie T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
    (hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) {i j : Mb} (hi : i ∈ T)
    (hj : j ∈ T) (hio : orderOf i = 2) (hjo : orderOf j = 2) :
    IsConj i j ↔ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  refine ⟨D.fusion_forward C hi hj, fun h => ?_⟩
  rcases D.classes i hio with hzi | hti <;> rcases D.classes j hjo with hzj | htj
  · exact hzi.symm.trans hzj
  · exfalso
    apply hnc
    exact ((D.fusion_forward C D.z_mem hi hzi).trans h).trans
      (D.fusion_forward C hj D.t_mem htj.symm)
  · exfalso
    apply hnc
    exact ((D.fusion_forward C D.z_mem hj hzj).trans h.symm).trans
      (D.fusion_forward C hi D.t_mem hti.symm)
  · exact hti.symm.trans htj

end Lie

section Sylow

variable {X : Type*} [Group X] [Finite X]

theorem exists_mem_normalizer_not_mem_of_isPGroup {Q P : Subgroup X} (hP : IsPGroup 2 P)
    (hQP : Q ≤ P) (hne : Q ≠ P) : ∃ t ∈ P, t ∈ Subgroup.normalizer (Q : Set X) ∧ t ∉ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    exact le_antisymm hQP (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := P) _ hlt
  obtain ⟨t, htN, htQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQP, Subgroup.mem_subgroupOf] at htN
  exact ⟨t, t.2, htN, fun h => htQ (Subgroup.mem_subgroupOf.mpr h)⟩

theorem eq_of_isSylowTwoOf_of_isPGroup {K P N : Subgroup X} (hP : IsSylowTwoOf P K)
    (hPN : P ≤ N) (hNK : N ≤ K) (hN : IsPGroup 2 N) : N = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := F7.isSylowTwoOf_mono_right hP hPN hNK
  obtain ⟨n, hn⟩ := hN.index (P.subgroupOf N)
  have h1 : (P.subgroupOf N).index = 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa using hn
    · exact absurd (hn ▸ dvd_pow_self 2 hpos.ne') h.2.2
  have h2 := Subgroup.index_eq_one.mp h1
  refine le_antisymm (fun x hx => ?_) hPN
  have : (⟨x, hx⟩ : N) ∈ P.subgroupOf N := by rw [h2]; trivial
  exact this

end Sylow

section Lemma433

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431Lie.lemma_F433 (D : F431Lie T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
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
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hz0P, Subgroup.mem_centralizer_iff.mpr hz0c⟩)
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

section Involutions

variable {X : Type*} [Group X]

theorem normalizer_zpowers_eq_centralizer {z : X} (hz : orderOf z = 2) :
    Subgroup.normalizer (Subgroup.zpowers z : Set X) = Subgroup.centralizer ({z} : Set X) := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hmem : ∀ x ∈ Subgroup.zpowers z, x = 1 ∨ x = z := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hz]
    have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases this with h | h <;> rw [h] <;> simp
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    have h1 : g * z * g⁻¹ ∈ Subgroup.zpowers z := (h z).mp (Subgroup.mem_zpowers z)
    have hk' : g * z * g⁻¹ = z := by
      rcases hmem _ h1 with h2 | h2
      · exfalso
        apply hz1
        have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
        rw [this, h2]
        group
      · exact h2
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hk']
  · intro h x
    have hc : g * z * g⁻¹ = z := by rw [h]; group
    have hc' : g⁻¹ * z * g = z := by
      rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← hk, ← conj_zpow, hc]
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [hx', ← hk]
      have := conj_zpow (a := g⁻¹) (b := z) (i := k)
      rw [inv_inv, hc'] at this
      exact this

theorem zpowers_involution_ti {z : X} (hz : orderOf z = 2) (g : X)
    (h : Subgroup.zpowers z ⊓ conjSub g (Subgroup.zpowers z) ≠ ⊥) :
    conjSub g (Subgroup.zpowers z) = Subgroup.zpowers z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hmem : ∀ x ∈ Subgroup.zpowers z, x = 1 ∨ x = z := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hz]
    have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases this with h | h <;> rw [h] <;> simp
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hx1 : (x : X) ≠ 1 := fun h' => hx (Subtype.ext h')
  have hxz : (x : X) = z := (hmem _ x.2.1).resolve_left hx1
  have hxg : g⁻¹ * (x : X) * g ∈ Subgroup.zpowers z := mem_conjSub.mp x.2.2
  rw [hxz] at hxg
  rcases hmem _ hxg with h2 | h2
  · exfalso
    apply hz1
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, h2]
    group
  · have hc' : g⁻¹ * z * g = z := h2
    have hc : g * z * g⁻¹ = z := by
      have : g * z = z * g := by
        calc g * z = g * (g⁻¹ * z * g) := by rw [hc']
          _ = z * g := by group
      rw [this]
      group
    ext y
    rw [mem_conjSub]
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have hy' : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      have := conj_zpow (a := g) (b := z) (i := k)
      rw [hc] at this
      rw [hy', ← hk]
      exact this
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := conj_zpow (a := g⁻¹) (b := z) (i := k)
      rw [inv_inv, hc'] at this
      rw [← hk]
      exact this

end Involutions

section Lemma434

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M]
  {T M1 M2 : Subgroup Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431Lie.orderOf_amalgamMap₁ (D : F431Lie T M1 M2 z t) (C : F431Comp M1 M2 b1 b2) :
    orderOf (amalgamMap b1 b2 z) = 2 := by
  rw [amalgamMap_of_mem₁ b1 b2 (D.T_le₁ D.z_mem), orderOf_injective b1 C.inj₁]
  exact (Subgroup.orderOf_coe (⟨z, D.T_le₁ D.z_mem⟩ : M1)).symm.trans D.hz

theorem F431Lie.orderOf_amalgamMap₂ (D : F431Lie T M1 M2 z t) (C : F431Comp M1 M2 b1 b2) :
    orderOf (amalgamMap b1 b2 t) = 2 := by
  rw [amalgamMap_of_mem₂ b1 b2 C.agree (D.T_le₂ D.t_mem), orderOf_injective b2 C.inj₂]
  exact (Subgroup.orderOf_coe (⟨t, D.T_le₂ D.t_mem⟩ : M2)).symm.trans D.ht

theorem F431Lie.lemma_F434 (D : F431Lie T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
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

section Lemma443

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem exists_conj_mem_of_isSylowTwoOf_involution {K : Subgroup Mb} (hK : IsSylowTwoOf T K)
    {u : Mb} (hu : u ∈ K) (hord : orderOf u = 2) : ∃ m ∈ K, m⁻¹ * u * m ∈ T := by
  have h2 : u ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact hord ▸ pow_orderOf_eq_one u
  have hp : IsPGroup 2 (Subgroup.zpowers u) :=
    BenderStart.isPGroup_zpowers_of_pow_eq_one (k := 1) h2
  obtain ⟨x, hx, hle⟩ := F7.isSylowTwoOf_exists_conj_le hK (Subgroup.zpowers_le.2 hu) hp
  exact ⟨x, hx, mem_conjSub.mp (hle (Subgroup.mem_zpowers u))⟩

omit [Finite M] in
theorem F431Lie.fusion_in (D : F431Lie T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
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

theorem F431Lie.lemma_F443 (D : F431Lie T M1 M2 z t) (C : F431Comp M1 M2 b1 b2)
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
      show b2 (Subgroup.inclusion D.cent_t c) * b2 ⟨t, htM2⟩ = b2 ⟨t, htM2⟩ * b2 (Subgroup.inclusion D.cent_t c)
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
    exact D.fusion_in C hnc hSyl2 (fun a ha b hb => amalgamMap_mul₂ b1 b2 C.agree ha hb) D.z_mem D.hz
      hxM2 hxo

end Lemma443

section NonFusion

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem card_centralizer_eq_of_isConj {a b : M} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set M)) = Nat.card (Subgroup.centralizer ({b} : Set M)) := by
  have h1 := CFSG.ShultStronglyClosedTI.InvolutionCounting.card_centralizer_mul_card_conjugatesOf a
  have h2 := CFSG.ShultStronglyClosedTI.InvolutionCounting.card_centralizer_mul_card_conjugatesOf b
  rw [isConj_iff_conjugatesOf_eq.mp h] at h1
  have hpos : 0 < Nat.card (conjugatesOf b) := by
    rw [Nat.card_pos_iff]
    exact ⟨⟨⟨b, mem_conjugatesOf_self⟩⟩, inferInstance⟩
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

end NonFusion

end CFSG.Quasithin
