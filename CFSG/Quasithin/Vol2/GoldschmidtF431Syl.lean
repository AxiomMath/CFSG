module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Lie

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

universe u v

section Lemma433

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem lemma_F433_aux {KK : Subgroup Mb} (bK : KK →* M) (hbK : Function.Injective bK)
    (hT : IsSylowTwoOf T ⊤) (hTK : T ≤ KK) (hz : z ∈ T) (hzo : orderOf z = 2)
    (hcT : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ KK, m * z * m⁻¹ = w)
    (hb : Subgroup.centralizer ({bK ⟨z, hTK hz⟩} : Set M) ≤ bK.range) :
    IsSylowTwoOf ((T.subgroupOf KK).map bK) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup M := (T.subgroupOf KK).map bK with hP
  have hzK : z ∈ KK := hTK hz
  have hTp : IsPGroup 2 (T.subgroupOf KK) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  have hPp : IsPGroup 2 P := hTp.of_equiv (Subgroup.equivMapOfInjective _ bK hbK)
  have hSylM1 : IsSylowTwoOf P bK.range := by
    refine F7.isSylowTwoOf_of_relIndex (Subgroup.map_le_range bK _) hPp ?_
    have h1 : P.relIndex bK.range = (T.subgroupOf KK).relIndex ⊤ := by
      rw [hP, MonoidHom.range_eq_map]
      exact Subgroup.relIndex_map_map_of_injective _ _ hbK
    rw [h1, Subgroup.relIndex_top_right]
    exact (F7.isSylowTwoOf_mono_right hT hTK le_top).2.2
  have hzP : bK ⟨z, hzK⟩ ∈ P := Subgroup.mem_map.mpr ⟨⟨z, hzK⟩, hz, rfl⟩
  have hz1 : bK ⟨z, hzK⟩ ≠ 1 := by
    intro h
    have : (⟨z, hzK⟩ : KK) = 1 := hbK (by rw [h, map_one])
    have hz1' : z = 1 := congrArg Subtype.val this
    have := hzo
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
    have hxP : bK ⟨x, hTK hx⟩ ∈ P := Subgroup.mem_map.mpr ⟨⟨x, hTK hx⟩, hx, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hawc _ hxP
    rw [← hyw, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hbK h1)
  obtain ⟨m, hmK, hmeq⟩ := hcT (y : Mb) hyTT hcomm hy1
  set m' : M := bK ⟨m, hmK⟩ with hm'
  set zz : M := bK ⟨z, hzK⟩ with hzz
  have hwm : w = m' * zz * m'⁻¹ := by
    rw [← hyw]
    have : y = ⟨m, hmK⟩ * ⟨z, hzK⟩ * ⟨m, hmK⟩⁻¹ := Subtype.ext (by simpa using hmeq.symm)
    rw [this, map_mul, map_mul, map_inv]
  have hm'range : m' ∈ bK.range := ⟨_, rfl⟩
  have hCw : Subgroup.centralizer ({w} : Set M) ≤ bK.range := by
    intro x hx
    have hx' : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hcz : m'⁻¹ * x * m' ∈ Subgroup.centralizer ({zz} : Set M) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc m'⁻¹ * x * m' * zz = m'⁻¹ * (x * (m' * zz * m'⁻¹)) * m' := by group
        _ = m'⁻¹ * ((m' * zz * m'⁻¹) * x) * m' := by rw [← hwm, hx']
        _ = zz * (m'⁻¹ * x * m') := by group
    have := hb hcz
    have hx2 : x = m' * (m'⁻¹ * x * m') * m'⁻¹ := by group
    rw [hx2]
    exact bK.range.mul_mem (bK.range.mul_mem hm'range this) (bK.range.inv_mem hm'range)
  have hNle : N ≤ bK.range := fun x hx => hCw (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hwN x hx)
  have hNeq := eq_of_isSylowTwoOf_of_isPGroup hSylM1 hPN hNle hNp
  exact hnP (hNeq ▸ hnN')
theorem F431LieK.lemma_F433 (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range ∨
      Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b2.range) :
    IsSylowTwoOf ((T.subgroupOf M1).map b1) ⊤ := by
  have hzT := D.mem_T z D.z_mem
  have hcT : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 →
      ∃ m ∈ M1 ⊓ M2, m * z * m⁻¹ = w := D.center_T
  rcases hb with hb | hb
  · refine lemma_F433_aux b1 C.inj₁ D.sylow D.T_le₁ hzT (D.order_two z D.z_mem)
      (fun w hw hc h1 => ?_) ?_
    · obtain ⟨m, hm, hmeq⟩ := hcT w hw hc h1
      exact ⟨m, (Subgroup.mem_inf.mp hm).1, hmeq⟩
    · rw [← amalgamMap_of_mem₁ b1 b2 (D.T_le₁ hzT)]
      exact hb
  · have h := lemma_F433_aux b2 C.inj₂ D.sylow D.T_le₂ hzT (D.order_two z D.z_mem)
      (fun w hw hc h1 => ?_) ?_
    · have heq : (T.subgroupOf M2).map b2 = (T.subgroupOf M1).map b1 := by
        ext x
        simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, D.T_le₁ hy⟩, hy, C.agree y (D.T_le₁ hy) y.2⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, D.T_le₂ hy⟩, hy, (C.agree y y.2 (D.T_le₂ hy)).symm⟩
      rwa [heq] at h
    · obtain ⟨m, hm, hmeq⟩ := hcT w hw hc h1
      exact ⟨m, (Subgroup.mem_inf.mp hm).2, hmeq⟩
    · rw [← amalgamMap_of_mem₂ b1 b2 C.agree (D.T_le₂ hzT)]
      exact hb

end Lemma433

section Lemma435

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431LieK.fusion_in (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
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

theorem F431LieK.exists_conj_image [Finite M] (D : F431LieK T M1 M2 I z)
    (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range ∨
      Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b2.range) {x : M}
    (hx : orderOf x = 2) : ∃ i ∈ I, IsConj (amalgamMap b1 b2 i) x := by
  have hSyl := D.lemma_F433 C hb
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
  obtain ⟨i, ⟨hiI, hic⟩, -⟩ := D.rep (y : Mb) hyo
  refine ⟨i, hiI, ?_⟩
  have := D.fusion_forward C (D.mem_T i hiI) hyT' hic
  rw [hφy] at this
  exact this.trans hxy.symm

end Lemma435

end CFSG.Quasithin.H13.F431
