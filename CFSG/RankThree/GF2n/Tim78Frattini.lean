module

public import CFSG.RankThree.GF2n.Basic
public import CFSG.RankThree.GF2n.Tim78Abelian
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.RankThree.GF2n
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sq_mem_inSubgroup_frattini {S : Subgroup G} (hS : IsPGroup 2 S) {s : G} (hs : s ∈ S) :
    s ^ 2 ∈ inSubgroup frattini S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 S) := ⟨hS⟩
  exact ⟨⟨s, hs⟩ ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) _, rfl⟩

theorem commutatorElement_mem_inSubgroup_frattini {S : Subgroup G} (hS : IsPGroup 2 S) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) : ⁅a, b⁆ ∈ inSubgroup frattini S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 S) := ⟨hS⟩
  refine ⟨⁅⟨a, ha⟩, ⟨b, hb⟩⁆, commutator_le_frattini_of_isPGroup (p := 2)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)), ?_⟩
  simp [commutatorElement_def]

theorem inSubgroup_frattini_mono {H S : Subgroup G} (hS : IsPGroup 2 S) (hHS : H ≤ S) :
    inSubgroup frattini H ≤ inSubgroup frattini S :=
  inSubgroup_frattini_le_of_sq (hS.to_le hHS)
    (fun _ hx => sq_mem_inSubgroup_frattini hS (hHS hx))
    (fun _ hx _ hy => commutatorElement_mem_inSubgroup_frattini hS (hHS hx) (hHS hy))

@[expose] def Hyp22 (x : G) (S : Subgroup G) : Prop :=
  IsPGroup 2 S ∧ inSubgroup frattini S ≤ Subgroup.centralizer (S : Set G) ∧
    x ∈ Subgroup.normalizer (S : Set G) ∧
    S ⊓ Subgroup.centralizer ({x} : Set G) = S ⊓ Subgroup.centralizer ({x ^ 2} : Set G)

theorem Hyp22.mono {x : G} {S H : Subgroup G} (h : Hyp22 x S) (hHS : H ≤ S)
    (hxH : x ∈ Subgroup.normalizer (H : Set G)) : Hyp22 x H := by
  obtain ⟨hS2, hΦ, -, hC⟩ := h
  refine ⟨hS2.to_le hHS, ?_, hxH, ?_⟩
  · exact (inSubgroup_frattini_mono hS2 hHS).trans
      (hΦ.trans (Subgroup.centralizer_le hHS))
  · ext y
    have h1 : y ∈ S ⊓ Subgroup.centralizer ({x} : Set G) ↔
        y ∈ S ⊓ Subgroup.centralizer ({x ^ 2} : Set G) := by rw [hC]
    have h2 := @hHS y
    simp only [Subgroup.mem_inf] at h1 ⊢
    tauto

omit [Finite G] in
theorem conj_mem_of_mem_normalizer {S : Subgroup G} {x : G}
    (hxS : x ∈ Subgroup.normalizer (S : Set G)) {s : G} (hs : s ∈ S) : x * s * x⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp hxS s).mp hs

omit [Finite G] in
theorem center_le_centralizer_of_hyp22 {x : G} {S : Subgroup G} (h : Hyp22 x S)
    (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    S ⊓ Subgroup.centralizer (S : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨hS2, -, hxS, hC⟩ := h
  refine tim78_2_1 ⟨⟨fun a b => Subtype.ext ?_⟩⟩ (hS2.to_le inf_le_left)
    (mem_normalizer_inf hxS (mem_normalizer_centralizer hxS)) hx ?_
  · show (a : G) * b = b * a
    exact Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1
  · ext y
    have h1 : y ∈ S ⊓ Subgroup.centralizer ({x} : Set G) ↔
        y ∈ S ⊓ Subgroup.centralizer ({x ^ 2} : Set G) := by rw [hC]
    simp only [Subgroup.mem_inf] at h1 ⊢
    tauto

omit [Finite G] in
theorem le_normalizer_center (S : Subgroup G) :
    S ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) :=
  fun _ hs => mem_normalizer_inf (Subgroup.le_normalizer hs)
    (mem_normalizer_centralizer (Subgroup.le_normalizer hs))

theorem commute_of_dlt_mem {x : G} {S : Subgroup G} (h : Hyp22 x S) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1)
    {m : G} (hm : m ∈ S) (hδ : dlt x m ∈ S ⊓ Subgroup.centralizer (S : Set G)) :
    x * m = m * x := by
  obtain ⟨hS2, hΦ, hxS, hC⟩ := h
  set Z := S ⊓ Subgroup.centralizer (S : Set G) with hZdef
  set A := Z ⊔ Subgroup.zpowers m with hAdef
  have hZS : Z ≤ S := inf_le_left
  have hAS : A ≤ S := sup_le hZS (Subgroup.zpowers_le.mpr hm)
  have hmZ : Subgroup.zpowers m ≤ Subgroup.normalizer (Z : Set G) := Subgroup.zpowers_le.mpr
    (le_normalizer_center S hm)
  have hcen : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z := fun z hz s hs =>
    (Subgroup.mem_centralizer_iff.mp hz.2 s hs).symm
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨z₁, hz₁, u₁, hu₁, rfl⟩ := exists_mul_of_mem_sup hmZ ha
    obtain ⟨z₂, hz₂, u₂, hu₂, rfl⟩ := exists_mul_of_mem_sup hmZ hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₁
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₂
    have h1 := hcen z₁ hz₁ _ (S.zpow_mem hm j)
    have h2 := hcen z₂ hz₂ _ (S.zpow_mem hm i)
    have h3 := hcen z₁ hz₁ z₂ (hZS hz₂)
    have h4 : m ^ i * m ^ j = m ^ j * m ^ i := (Commute.zpow_zpow_self m i j).eq
    calc z₁ * m ^ i * (z₂ * m ^ j) = z₁ * (m ^ i * z₂) * m ^ j := by group
      _ = z₁ * (z₂ * m ^ i) * m ^ j := by rw [← h2]
      _ = (z₁ * z₂) * (m ^ i * m ^ j) := by group
      _ = (z₂ * z₁) * (m ^ j * m ^ i) := by rw [h3, h4]
      _ = z₂ * (z₁ * m ^ j) * m ^ i := by group
      _ = z₂ * (m ^ j * z₁) * m ^ i := by rw [h1]
      _ = z₂ * m ^ j * (z₁ * m ^ i) := by group
  have hxZ : x ∈ Subgroup.normalizer (Z : Set G) := mem_normalizer_inf hxS
    (mem_normalizer_centralizer hxS)
  have hxA : x ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨z, hz, u, hu, rfl⟩ := exists_mul_of_mem_sup hmZ ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hxz : x * z * x⁻¹ ∈ A :=
      Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hxZ z).mp hz)
    have hxm : x * m * x⁻¹ ∈ A := by
      have : x * m * x⁻¹ = m * dlt x m := by unfold dlt; group
      rw [this]
      exact A.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers m))
        (Subgroup.mem_sup_left hδ)
    have : x * (z * m ^ i) * x⁻¹ = (x * z * x⁻¹) * (x * m * x⁻¹) ^ i := by
      rw [← MulAut.conj_apply, map_mul, map_zpow, MulAut.conj_apply, MulAut.conj_apply]
    rw [this]
    exact A.mul_mem hxz (A.zpow_mem hxm i)
  have hAcomm : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
  have hCA : A ⊓ Subgroup.centralizer ({x} : Set G) =
      A ⊓ Subgroup.centralizer ({x ^ 2} : Set G) :=
    (Hyp22.mono ⟨hS2, hΦ, hxS, hC⟩ hAS hxA).2.2.2
  have hmA : m ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers m)
  have := tim78_2_1 hAcomm (hS2.to_le hAS) hxA hx hCA hmA
  exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm

theorem forall_mem_of_le_centralizer_index_two {x : G} {S H : Subgroup G} (hS2 : IsPGroup 2 S)
    (hxS : x ∈ Subgroup.normalizer (S : Set G)) (hHS : H ≤ S) (hidx : H.relIndex S = 2)
    (hHx : H ≤ Subgroup.centralizer ({x} : Set G)) :
    ∀ s ∈ S, s⁻¹ * (x ^ 2 * s * (x ^ 2)⁻¹) ∈ inSubgroup frattini S := by
  intro s hs
  have hxs : x * s * x⁻¹ ∈ S := conj_mem_of_mem_normalizer hxS hs
  have hxH : ∀ y ∈ H, x * y * x⁻¹ = y := fun y hy => by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hHx hy)).symm]
    group
  have htH : dlt x s ∈ H := by
    have hidx' : (H.subgroupOf S).index = 2 := hidx
    have key := (Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨s⁻¹, S.inv_mem hs⟩)
      (b := ⟨x * s * x⁻¹, hxs⟩))
    simp only [Subgroup.mem_subgroupOf] at key
    have hiff : s⁻¹ ∈ H ↔ x * s * x⁻¹ ∈ H := by
      rw [Subgroup.inv_mem_iff]
      constructor
      · intro h
        rw [hxH s h]
        exact h
      · intro h
        have : s = x * s * x⁻¹ := by
          calc s = x⁻¹ * (x * s * x⁻¹) * x := by group
            _ = x⁻¹ * (x * (x * s * x⁻¹) * x⁻¹) * x := by rw [hxH _ h]
            _ = x * s * x⁻¹ := by group
        rw [this]
        exact h
    exact key.mpr hiff
  have htS : dlt x s ∈ S := hHS htH
  have e : s⁻¹ * (x ^ 2 * s * (x ^ 2)⁻¹) = dlt x s ^ 2 := by
    have h1 : x * s * x⁻¹ = s * dlt x s := by unfold dlt; group
    have h2 : x * dlt x s * x⁻¹ = dlt x s := hxH _ htH
    calc s⁻¹ * (x ^ 2 * s * (x ^ 2)⁻¹) = s⁻¹ * (x * (x * s * x⁻¹) * x⁻¹) := by
          rw [sq]; group
      _ = s⁻¹ * (x * (s * dlt x s) * x⁻¹) := by rw [h1]
      _ = s⁻¹ * ((x * s * x⁻¹) * (x * dlt x s * x⁻¹)) := by group
      _ = s⁻¹ * (s * dlt x s * dlt x s) := by rw [h1, h2]
      _ = dlt x s ^ 2 := by rw [sq]; group
  rw [e]
  exact sq_mem_inSubgroup_frattini hS2 htS

omit [Finite G] in
theorem mem_center_iff_mem_inf {S : Subgroup G} (s : S) :
    s ∈ Subgroup.center S ↔ (s : G) ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    refine ⟨s.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (h ⟨g, hg⟩)
  · intro h g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h.2 g g.2)

omit [Finite G] in
theorem dlt_mul (x a b : G) : dlt x (a * b) = b⁻¹ * dlt x a * b * dlt x b := by
  unfold dlt
  group

theorem exists_dltBar {x : G} {S : Subgroup G} (h : Hyp22 x S) :
    ∃ f : S →* S ⧸ Subgroup.center S, ∀ s : S,
      f s = ((⟨dlt x s, dlt_mem (fun _ ht => conj_mem_of_mem_normalizer h.2.2.1 ht) s.2⟩ : S) :
        S ⧸ Subgroup.center S) := by
  obtain ⟨hS2, hΦ, hxS, -⟩ := h
  have hxS' : ∀ t ∈ S, x * t * x⁻¹ ∈ S := fun t ht => conj_mem_of_mem_normalizer hxS ht
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ S ⊓ Subgroup.centralizer (S : Set G) := fun a ha b hb =>
    ⟨S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb),
      hΦ (commutatorElement_mem_inSubgroup_frattini hS2 ha hb)⟩
  refine ⟨{ toFun := fun s => ((⟨dlt x s, dlt_mem hxS' s.2⟩ : S) : S ⧸ Subgroup.center S)
            map_one' := ?_
            map_mul' := ?_ }, fun s => rfl⟩
  · change ((⟨dlt x 1, _⟩ : S) : S ⧸ Subgroup.center S) = ((1 : S) : S ⧸ Subgroup.center S)
    congr 1
    apply Subtype.ext
    simp [dlt]
  · intro a b
    change ((⟨dlt x (a * b), _⟩ : S) : S ⧸ Subgroup.center S) =
      ((⟨dlt x a, _⟩ : S) : S ⧸ Subgroup.center S) * ((⟨dlt x b, _⟩ : S) : S ⧸ Subgroup.center S)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_center_iff_mem_inf]
    have hda : dlt x a ∈ S := dlt_mem hxS' a.2
    have hdb : dlt x b ∈ S := dlt_mem hxS' b.2
    have hc := hcomm _ (S.inv_mem b.2) _ (S.inv_mem hda)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [dlt_mul]
    have e : ((b : G)⁻¹ * dlt x a * b * dlt x b)⁻¹ * (dlt x a * dlt x b) =
        (dlt x b)⁻¹ * ⁅(b : G)⁻¹, (dlt x a)⁻¹⁆ * dlt x b := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hcen : ⁅(b : G)⁻¹, (dlt x a)⁻¹⁆ * dlt x b = dlt x b * ⁅(b : G)⁻¹, (dlt x a)⁻¹⁆ :=
      (Subgroup.mem_centralizer_iff.mp hc.2 _ hdb).symm
    rw [mul_assoc, hcen, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hc

omit [Finite G] in
theorem card_le_card_ker_mul {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B)
    (K : Subgroup A) (R : Subgroup B) [Finite R] (hR : ∀ a ∈ K, φ a ∈ R) :
    Nat.card K ≤ Nat.card φ.ker * Nat.card R := by
  set φ' := φ.comp K.subtype with hφ'
  have h1 := Subgroup.card_mul_index φ'.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card φ'.ker ≤ Nat.card φ.ker := by
    refine Nat.card_le_card_of_injective (fun a => ⟨(a : K), ?_⟩) ?_
    · have := a.2
      rw [MonoidHom.mem_ker] at this ⊢
      exact this
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun t : φ.ker => ((t : A))) hab))
  have h3 : Nat.card φ'.range ≤ Nat.card R := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨a, rfl⟩
    exact hR a a.2
  rw [← h1]
  exact Nat.mul_le_mul h2 h3

omit [Finite G] in
theorem card_map_mk_mul_card_center {S : Subgroup G} (C : Subgroup S)
    (hC : Subgroup.center S ≤ C) :
    Nat.card (C.map (QuotientGroup.mk' (Subgroup.center S))) * Nat.card (Subgroup.center S) =
      Nat.card C := by
  set φ := (QuotientGroup.mk' (Subgroup.center S)).comp C.subtype with hφ
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  have hrange : φ.range = C.map (QuotientGroup.mk' (Subgroup.center S)) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card (Subgroup.center S) := by
    have : φ.ker = (Subgroup.center S).subgroupOf C := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rfl
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv
  rw [← hrange, ← hker, mul_comm, h1]

theorem dltBar_eq_one_iff {x : G} {S : Subgroup G} (h : Hyp22 x S) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1)
    {f : S →* S ⧸ Subgroup.center S}
    (hf : ∀ s : S, f s = ((⟨dlt x s, dlt_mem (fun _ ht => conj_mem_of_mem_normalizer h.2.2.1 ht)
      s.2⟩ : S) : S ⧸ Subgroup.center S)) (s : S) :
    f s = 1 ↔ x * s = s * x := by
  rw [hf, QuotientGroup.eq_one_iff, mem_center_iff_mem_inf]
  constructor
  · intro hδ
    exact commute_of_dlt_mem h hx s.2 hδ
  · intro hxs
    have : dlt x s = 1 := by
      unfold dlt
      rw [hxs]
      group
    change dlt x (s : G) ∈ S ⊓ Subgroup.centralizer (S : Set G)
    rw [this]
    exact Subgroup.one_mem _

theorem card_relations {x : G} {S : Subgroup G} (h : Hyp22 x S) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1)
    {f : S →* S ⧸ Subgroup.center S}
    (hf : ∀ s : S, f s = ((⟨dlt x s, dlt_mem (fun _ ht => conj_mem_of_mem_normalizer h.2.2.1 ht)
      s.2⟩ : S) : S ⧸ Subgroup.center S)) :
    Nat.card S = Nat.card (S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) *
        Nat.card f.range ∧
      (f.range.comap (QuotientGroup.mk' (Subgroup.center S))).index *
          Nat.card (S ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) =
        Nat.card (S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
  have hker : f.ker = (S ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, dltBar_eq_one_iff h hx hf, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h' => ⟨s.2, h'.symm⟩, fun h' => h'.2.symm⟩
  have hkercard : Nat.card f.ker = Nat.card (S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :=
    by rw [hker]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hkercard] at h1
  have hS : Nat.card S = Nat.card (S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) *
      Nat.card f.range := h1.symm
  refine ⟨hS, ?_⟩
  have hcenter : Nat.card (Subgroup.center S) =
      Nat.card (S ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) := by
    have : Subgroup.center S = (S ⊓ Subgroup.centralizer (S : Set G)).subgroupOf S := by
      ext s
      rw [mem_center_iff_mem_inf, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hidx : (f.range.comap (QuotientGroup.mk' (Subgroup.center S))).index = f.range.index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 := Subgroup.card_mul_index f.range
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
  rw [hidx, ← hcenter]
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have key : f.range.index * Nat.card (Subgroup.center S) * Nat.card f.range =
      Nat.card (S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) * Nat.card f.range := by
    rw [← hS, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

theorem K_props {x : G} {S : Subgroup G} (h : Hyp22 x S) {f : S →* S ⧸ Subgroup.center S}
    (hf : ∀ s : S, f s = ((⟨dlt x s, dlt_mem (fun _ ht => conj_mem_of_mem_normalizer h.2.2.1 ht)
      s.2⟩ : S) : S ⧸ Subgroup.center S)) :
    let K' := f.range.comap (QuotientGroup.mk' (Subgroup.center S))
    let K := K'.map S.subtype
    K ≤ S ∧ S ⊓ Subgroup.centralizer (S : Set G) ≤ K ∧ (∀ s ∈ S, dlt x s ∈ K) ∧
      Nat.card K * K'.index = Nat.card S ∧ S ≤ Subgroup.normalizer (K : Set G) ∧
      x ∈ Subgroup.normalizer (K : Set G) := by
  intro K' K
  have hS2 := h.1
  have hΦ := h.2.1
  have hxS := h.2.2.1
  have hxS' : ∀ t ∈ S, x * t * x⁻¹ ∈ S := fun t ht => conj_mem_of_mem_normalizer hxS ht
  have hmemK : ∀ s : S, (s : G) ∈ K ↔
      QuotientGroup.mk' (Subgroup.center S) s ∈ f.range := by
    intro s
    constructor
    · rintro ⟨t, ht, hts⟩
      have : t = s := Subtype.ext hts
      rw [← this]
      exact ht
    · intro hs
      exact ⟨s, hs, rfl⟩
  have hKS : K ≤ S := Subgroup.map_subtype_le _
  have hZK : S ⊓ Subgroup.centralizer (S : Set G) ≤ K := by
    intro z hz
    rw [show z = ((⟨z, hz.1⟩ : S) : G) from rfl, hmemK]
    have : QuotientGroup.mk' (Subgroup.center S) (⟨z, hz.1⟩ : S) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff_mem_inf]
      exact hz
    rw [this]
    exact Subgroup.one_mem _
  have hδK : ∀ s ∈ S, dlt x s ∈ K := by
    intro s hs
    rw [show dlt x s = ((⟨dlt x s, dlt_mem hxS' hs⟩ : S) : G) from rfl, hmemK]
    exact ⟨⟨s, hs⟩, by rw [hf]; rfl⟩
  have hcard : Nat.card K * K'.index = Nat.card S := by
    rw [Nat.card_congr (K'.equivMapOfInjective S.subtype S.subtype_injective).symm.toEquiv]
    exact Subgroup.card_mul_index K'
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ S ⊓ Subgroup.centralizer (S : Set G) := fun a ha b hb =>
    ⟨S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb),
      hΦ (commutatorElement_mem_inSubgroup_frattini hS2 ha hb)⟩
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := by
    intro t ht
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    have hkS := hKS hk
    have e : t * k * t⁻¹ = ⁅t, k⁆ * k := by simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem (hZK (hcomm t ht k hkS)) hk
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    have e : x * k * x⁻¹ = k * dlt x k := by unfold dlt; group
    rw [e]
    exact K.mul_mem hk (hδK k (hKS hk))
  exact ⟨hKS, hZK, hδK, hcard, hSK, hxK⟩

@[expose] def Concl22 (x : G) (S : Subgroup G) : Prop :=
  ∀ s ∈ S, s⁻¹ * (x ^ 2 * s * (x ^ 2)⁻¹) ∈ inSubgroup frattini S

theorem concl22_of_four_le_index {x : G} {S : Subgroup G} (h : Hyp22 x S)
    {f : S →* S ⧸ Subgroup.center S}
    (hf : ∀ s : S, f s = ((⟨dlt x s, dlt_mem (fun _ ht => conj_mem_of_mem_normalizer h.2.2.1 ht)
      s.2⟩ : S) : S ⧸ Subgroup.center S))
    (hidx : 4 ≤ (f.range.comap (QuotientGroup.mk' (Subgroup.center S))).index)
    (ih : ∀ H < S, Hyp22 x H → Concl22 x H) : Concl22 x S := by
  obtain ⟨hKS, hZK, hδK, hcard, hSK, hxK⟩ := K_props h hf
  set K := (f.range.comap (QuotientGroup.mk' (Subgroup.center S))).map S.subtype with hKdef
  have hS2 := h.1
  have hΦZ : inSubgroup frattini S ≤ S ⊓ Subgroup.centralizer (S : Set G) :=
    le_inf (Subgroup.map_subtype_le _) h.2.1
  intro s hs
  set H := K ⊔ Subgroup.zpowers s with hHdef
  have hsK : Subgroup.zpowers s ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr (hSK hs)
  have hHS : H ≤ S := sup_le hKS (Subgroup.zpowers_le.mpr hs)
  have hprod := PartTwo.Sec6.card_sup_mul_card_inf hsK
  have hs2 : Nat.card (Subgroup.zpowers s) ≤
      2 * Nat.card (Subgroup.zpowers s ⊓ K : Subgroup G) := by
    have hle : Subgroup.zpowers (s ^ 2) ≤ Subgroup.zpowers s ⊓ K := by
      rw [Subgroup.zpowers_le]
      exact ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers s) 2,
        hZK (hΦZ (sq_mem_inSubgroup_frattini hS2 hs))⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    rw [Nat.card_zpowers]
    rw [orderOf_pow' s (by norm_num)] at h1
    have hg : (orderOf s).gcd 2 ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _)
    have hd := Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf s) 2)
    calc orderOf s = orderOf s / (orderOf s).gcd 2 * (orderOf s).gcd 2 := hd.symm
      _ ≤ orderOf s / (orderOf s).gcd 2 * 2 := Nat.mul_le_mul_left _ hg
      _ ≤ Nat.card (Subgroup.zpowers s ⊓ K : Subgroup G) * 2 := Nat.mul_le_mul_right _ h1
      _ = 2 * Nat.card (Subgroup.zpowers s ⊓ K : Subgroup G) := mul_comm _ _
  have hHcard : Nat.card H ≤ 2 * Nat.card K := by
    have hpos : 0 < Nat.card (Subgroup.zpowers s ⊓ K : Subgroup G) := Nat.card_pos
    rw [hHdef, sup_comm]
    have : Nat.card (Subgroup.zpowers s ⊔ K : Subgroup G) *
        Nat.card (Subgroup.zpowers s ⊓ K : Subgroup G) ≤
        2 * Nat.card K * Nat.card (Subgroup.zpowers s ⊓ K : Subgroup G) := by
      rw [hprod]
      calc Nat.card (Subgroup.zpowers s) * Nat.card K
          ≤ 2 * Nat.card (Subgroup.zpowers s ⊓ K : Subgroup G) * Nat.card K :=
            Nat.mul_le_mul_right _ hs2
        _ = 2 * Nat.card K * Nat.card (Subgroup.zpowers s ⊓ K : Subgroup G) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hHlt : H < S := by
    refine lt_of_le_of_ne hHS fun hHS' => ?_
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have : Nat.card S ≤ 2 * Nat.card K := hHS' ▸ hHcard
    have h4 : 4 * Nat.card K ≤ Nat.card S := by
      rw [← hcard, mul_comm]
      exact Nat.mul_le_mul_left _ hidx
    omega
  have hxH : x ∈ Subgroup.normalizer (H : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨k, hk, u, hu, rfl⟩ := exists_mul_of_mem_sup hsK hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hxk : x * k * x⁻¹ ∈ H :=
      Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hxK k).mp hk)
    have hxs : x * s * x⁻¹ ∈ H := by
      have : x * s * x⁻¹ = s * dlt x s := by unfold dlt; group
      rw [this]
      exact H.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
        (Subgroup.mem_sup_left (hδK s hs))
    have : x * (k * s ^ i) * x⁻¹ = (x * k * x⁻¹) * (x * s * x⁻¹) ^ i := by
      rw [← MulAut.conj_apply, map_mul, map_zpow, MulAut.conj_apply, MulAut.conj_apply]
    rw [this]
    exact H.mul_mem hxk (H.zpow_mem hxs i)
  have hH := Hyp22.mono h hHS hxH
  exact inSubgroup_frattini_mono hS2 hHS (ih H hHlt hH s
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)))

theorem isPGroup_sup_zpowers {x : G} {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hxS : x ∈ Subgroup.normalizer (S : Set G)) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    IsPGroup 2 (S ⊔ Subgroup.zpowers x : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hx
  have hprod := PartTwo.Sec6.card_sup_mul_card_inf (Subgroup.zpowers_le.mpr hxS)
  obtain ⟨a, ha⟩ := hS2.exists_card_eq
  have hxo : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hxo
  rw [Nat.card_zpowers, hb, ha, ← pow_add] at hprod
  have hdvd : Nat.card (Subgroup.zpowers x ⊔ S : Subgroup G) ∣ 2 ^ (b + a) :=
    Dvd.intro _ hprod
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [sup_comm] at hc
  exact IsPGroup.of_card hc

theorem false_of_index_eq_one {x : G} {S : Subgroup G} (h : Hyp22 x S)
    (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) {f : S →* S ⧸ Subgroup.center S}
    (hf : ∀ s : S, f s = ((⟨dlt x s, dlt_mem (fun _ ht => conj_mem_of_mem_normalizer h.2.2.1 ht)
      s.2⟩ : S) : S ⧸ Subgroup.center S))
    (hidx : (f.range.comap (QuotientGroup.mk' (Subgroup.center S))).index = 1)
    (hSx : ¬ S ≤ Subgroup.centralizer ({x} : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 := h.1
  have hxS := h.2.2.1
  set Z := S ⊓ Subgroup.centralizer (S : Set G) with hZdef
  set C := S ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  obtain ⟨-, hrel⟩ := card_relations h hx hf
  rw [hidx, one_mul] at hrel
  have hZC : Z ≤ C := le_inf inf_le_left (center_le_centralizer_of_hyp22 h hx)
  have hCZ : C = Z := (Subgroup.eq_of_le_of_card_ge hZC hrel.symm.le).symm
  have hZS : Z < S := by
    refine lt_of_le_of_ne inf_le_left fun hZS => hSx ?_
    intro s hs
    rw [← hZS] at hs
    exact (hCZ ▸ hZC hs : s ∈ C).2
  have hP := isPGroup_sup_zpowers hS2 hxS hx
  have hPZ : (S ⊔ Subgroup.zpowers x : Subgroup G) ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le (le_normalizer_center S) (Subgroup.zpowers_le.mpr
      (mem_normalizer_inf hxS (mem_normalizer_centralizer hxS)))
  have hPS : (S ⊔ Subgroup.zpowers x : Subgroup G) ≤ Subgroup.normalizer (S : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxS)
  obtain ⟨d, hdS, hdZ, hdc⟩ := exists_mem_not_mem_commutator_mem hP hZS le_sup_left hPZ hPS
  have hdx : ⁅d, x⁆ ∈ Z := hdc x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have e : ⁅d, x⁆ = dlt x d⁻¹ := by
    rw [commutatorElement_def, dlt, inv_inv]
    group
  rw [e] at hdx
  have hcomm := commute_of_dlt_mem h hx (S.inv_mem hdS) hdx
  apply hdZ
  rw [← hCZ]
  refine ⟨hdS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  calc d * x = d * (x * d⁻¹) * d := by group
    _ = d * (d⁻¹ * x) * d := by rw [hcomm]
    _ = x * d := by group

theorem eq_sup_zpowers_of_card_eq {A B : Subgroup G} (hBA : B ≤ A)
    (hcard : Nat.card A = 2 * Nat.card B) {b : G} (hbA : b ∈ A) (hbB : b ∉ B) :
    A = B ⊔ Subgroup.zpowers b := by
  have hle : B ⊔ Subgroup.zpowers b ≤ A := sup_le hBA (Subgroup.zpowers_le.mpr hbA)
  have hlt : B < B ⊔ Subgroup.zpowers b :=
    lt_of_le_of_ne le_sup_left fun h => hbB (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hd1 := Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ Subgroup.zpowers b)
  have hd2 := Subgroup.card_dvd_of_le hle
  have hne : Nat.card (B ⊔ Subgroup.zpowers b : Subgroup G) ≠ Nat.card B := fun h =>
    (ne_of_lt hlt) (Subgroup.eq_of_le_of_card_ge hlt.le h.le)
  have hBpos : 0 < Nat.card B := Nat.card_pos
  obtain ⟨k, hk⟩ := hd1
  rw [hk, hcard] at hd2
  have hk2 : k ∣ 2 := (Nat.mul_dvd_mul_iff_left hBpos).mp (by simpa [mul_comm] using hd2)
  have hk1 : k ≠ 1 := fun h => hne (by rw [hk, h, mul_one])
  have : k = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h | h
    · exact absurd h hk1
    · exact h
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hk, this, hcard, mul_comm]

theorem false_of_index_eq_two_of_card_range_eq_four {x : G} {S : Subgroup G} (h : Hyp22 x S)
    (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) {f : S →* S ⧸ Subgroup.center S}
    (hf : ∀ s : S, f s = ((⟨dlt x s, dlt_mem (fun _ ht => conj_mem_of_mem_normalizer h.2.2.1 ht)
      s.2⟩ : S) : S ⧸ Subgroup.center S))
    (hidx : (f.range.comap (QuotientGroup.mk' (Subgroup.center S))).index = 2)
    (hr : Nat.card f.range = 4) : False := by
  have hS2 := h.1
  have hxS := h.2.2.1
  have hxS' : ∀ t ∈ S, x * t * x⁻¹ ∈ S := fun t ht => conj_mem_of_mem_normalizer hxS ht
  set Z := S ⊓ Subgroup.centralizer (S : Set G) with hZdef
  set C := S ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  obtain ⟨hScard, hrel⟩ := card_relations h hx hf
  rw [hidx] at hrel
  have hZC : Z ≤ C := le_inf inf_le_left (center_le_centralizer_of_hyp22 h hx)
  have hΦZ : inSubgroup frattini S ≤ Z := le_inf (Subgroup.map_subtype_le _) h.2.1
  have hcen : ∀ z ∈ Z, ∀ t ∈ S, z * t = t * z := fun z hz t ht =>
    (Subgroup.mem_centralizer_iff.mp hz.2 t ht).symm
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    ⟨S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb),
      h.2.1 (commutatorElement_mem_inSubgroup_frattini hS2 ha hb)⟩
  have hZltC : Z < C := lt_of_le_of_ne hZC fun hZC' => by
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have h1 : Nat.card Z = Nat.card C := by rw [hZC']
    have h2 : 2 * Nat.card Z = Nat.card C := hrel
    omega
  obtain ⟨y, hyC, hyZ⟩ := IsConcreteLE.exists_of_lt hZltC
  have hCeq : C = Z ⊔ Subgroup.zpowers y := eq_sup_zpowers_of_card_eq hZC hrel.symm hyC hyZ
  have hyS : y ∈ S := hyC.1
  have hxy : x * y * x⁻¹ = y := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp hyC.2).symm]
    group
  set D := S ⊓ Subgroup.centralizer ({y} : Set G) with hDdef
  have hyZD : Subgroup.zpowers y ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.zpowers_le.mpr (le_normalizer_center S hyS)
  have hCD : C ≤ D := by
    intro c hc
    rw [hCeq] at hc
    obtain ⟨z, hz, u, hu, rfl⟩ := exists_mul_of_mem_sup hyZD hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine ⟨S.mul_mem hz.1 (S.zpow_mem hyS i), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc z * y ^ i * y = z * (y ^ i * y) := by group
      _ = z * (y * y ^ i) := by rw [(Commute.zpow_left (Commute.refl y) i).eq]
      _ = (z * y) * y ^ i := by group
      _ = (y * z) * y ^ i := by rw [hcen z hz y hyS]
      _ = y * (z * y ^ i) := by group
  have hDC : D = C := by
    by_contra hne
    have hCltD : C < D := lt_of_le_of_ne hCD (Ne.symm hne)
    have hDS : D ≠ S := fun hDS => hyZ ⟨hyS, Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hDS ▸ ht : t ∈ D).2)⟩
    have hDcard : Nat.card D = 2 * Nat.card C := by
      have h1 := Subgroup.card_dvd_of_le hCD
      have h2 := Subgroup.card_dvd_of_le (inf_le_left : D ≤ S)
      have hlt1 := Subgroup.card_lt_of_lt hCltD
      have hlt2 := Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left hDS)
      rw [hScard, hr] at h2 hlt2
      obtain ⟨k, hk⟩ := h1
      have hCpos : 0 < Nat.card C := Nat.card_pos
      rw [hk] at h2 hlt1 hlt2
      have hk4 : k ∣ 4 := (Nat.mul_dvd_mul_iff_left hCpos).mp h2
      have hk2 : 1 < k := by
        by_contra hk1
        push Not at hk1
        interval_cases k <;> simp_all
      have hk3 : k < 4 := by
        by_contra hk3
        push Not at hk3
        nlinarith
      have : k = 2 := by
        have := Nat.le_of_dvd (by norm_num) hk4
        interval_cases k <;> simp_all
      rw [hk, this, mul_comm]
    obtain ⟨w, hwD, hwC⟩ := IsConcreteLE.exists_of_lt hCltD
    have hDeq : D = C ⊔ Subgroup.zpowers w := eq_sup_zpowers_of_card_eq hCD hDcard hwD hwC
    have hwS : w ∈ S := hwD.1
    have hCcen : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c := by
      intro c hc d hd
      rw [hCeq] at hc
      obtain ⟨z, hz, u, hu, rfl⟩ := exists_mul_of_mem_sup hyZD hc
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hdy : y * d = d * y := (Subgroup.mem_centralizer_singleton_iff.mp hd.2).symm
      calc z * y ^ i * d = z * (y ^ i * d) := by group
        _ = z * (d * y ^ i) := by rw [(Commute.zpow_left hdy i).eq]
        _ = (z * d) * y ^ i := by group
        _ = (d * z) * y ^ i := by rw [hcen z hz d hd.1]
        _ = d * (z * y ^ i) := by group
    have hwCn : Subgroup.zpowers w ≤ Subgroup.normalizer (C : Set G) :=
      Subgroup.zpowers_le.mpr (le_normalizer_of_comm (fun a ha b hb =>
        (hCcen b hb a (Subgroup.zpowers_le.mpr hwD ha)).symm) (Subgroup.mem_zpowers w))
    have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
      intro a ha b hb
      rw [hDeq] at ha hb
      obtain ⟨c₁, hc₁, u₁, hu₁, rfl⟩ := exists_mul_of_mem_sup hwCn ha
      obtain ⟨c₂, hc₂, u₂, hu₂, rfl⟩ := exists_mul_of_mem_sup hwCn hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₁
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₂
      have hwi : w ^ i ∈ D := D.zpow_mem hwD i
      have hwj : w ^ j ∈ D := D.zpow_mem hwD j
      have h1 := hCcen c₁ hc₁ _ hwj
      have h2 := hCcen c₂ hc₂ _ hwi
      have h3 := hCcen c₁ hc₁ c₂ (hCD hc₂)
      have h4 : w ^ i * w ^ j = w ^ j * w ^ i := (Commute.zpow_zpow_self w i j).eq
      calc c₁ * w ^ i * (c₂ * w ^ j) = c₁ * (w ^ i * c₂) * w ^ j := by group
        _ = c₁ * (c₂ * w ^ i) * w ^ j := by rw [h2]
        _ = (c₁ * c₂) * (w ^ i * w ^ j) := by group
        _ = (c₂ * c₁) * (w ^ j * w ^ i) := by rw [h3, h4]
        _ = c₂ * (c₁ * w ^ j) * w ^ i := by group
        _ = c₂ * (w ^ j * c₁) * w ^ i := by rw [h1]
        _ = c₂ * w ^ j * (c₁ * w ^ i) := by group
    have hxD : x ∈ Subgroup.normalizer (D : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun d hd => Subgroup.mem_inf.mpr ⟨hxS' d hd.1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hdy : d * y = y * d := Subgroup.mem_centralizer_singleton_iff.mp hd.2
      calc x * d * x⁻¹ * y = x * d * x⁻¹ * (x * y * x⁻¹) := by rw [hxy]
        _ = x * (d * y) * x⁻¹ := by group
        _ = x * (y * d) * x⁻¹ := by rw [hdy]
        _ = (x * y * x⁻¹) * (x * d * x⁻¹) := by group
        _ = y * (x * d * x⁻¹) := by rw [hxy]
    have hDcomm : IsMulCommutative D := ⟨⟨fun a b => Subtype.ext (hDab a a.2 b b.2)⟩⟩
    have hDx := tim78_2_1 hDcomm (hS2.to_le inf_le_left) hxD hx
      (Hyp22.mono h inf_le_left hxD).2.2.2
    exact (ne_of_lt hCltD) (le_antisymm hCD fun d hd => ⟨hd.1, hDx hd⟩)
  have hδC : ∀ z ∈ S, dlt x z ∈ C := by
    intro z hz
    set t := dlt x z with ht
    have htS : t ∈ S := dlt_mem hxS' hz
    rw [← hDC]
    refine ⟨htS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hyz := hcomm y hyS z hz
    have hyt := hcomm y hyS t htS
    have h1 : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp (hZC hyz).2).symm]
      group
    have h2 : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z * t⁆ := by
      have hxz : x * z * x⁻¹ = z * t := by rw [ht]; unfold dlt; group
      have e : x * ⁅y, z⁆ * x⁻¹ = ⁅x * y * x⁻¹, x * z * x⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e, hxy, hxz]
    have h3 : ⁅y, z * t⁆ = ⁅y, z⁆ * ⁅y, t⁆ := by
      have e : ⁅y, z * t⁆ = ⁅y, z⁆ * (z * ⁅y, t⁆ * z⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e, ← hcen _ hyt z hz]
      group
    rw [h1, h3] at h2
    have h4 : ⁅y, t⁆ = 1 := by
      have := congrArg (fun u => ⁅y, z⁆⁻¹ * u) h2
      simpa using this.symm
    rw [commutatorElement_eq_one_iff_mul_comm] at h4
    exact h4.symm
  set C' := C.subgroupOf S with hC'def
  have hZC' : Subgroup.center S ≤ C' := by
    intro s hs
    rw [Subgroup.mem_subgroupOf]
    exact hZC ((mem_center_iff_mem_inf s).mp hs)
  have hmk := card_map_mk_mul_card_center C' hZC'
  have hC'card : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcenter : Nat.card (Subgroup.center S) = Nat.card Z := by
    have : Subgroup.center S = Z.subgroupOf S := by
      ext s
      rw [mem_center_iff_mem_inf, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : f.range ≤ C'.map (QuotientGroup.mk' (Subgroup.center S)) := by
    rintro _ ⟨s, rfl⟩
    rw [hf]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hδC s s.2))
  have hle := Subgroup.card_le_of_le hrange
  rw [hr] at hle
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  rw [hC'card, ← hrel, hcenter] at hmk
  have : Nat.card (C'.map (QuotientGroup.mk' (Subgroup.center S))) = 2 :=
    Nat.eq_of_mul_eq_mul_right hZpos (by rw [hmk])
  omega

theorem false_of_index_eq_two_of_eight_le {x : G} {S : Subgroup G} (h : Hyp22 x S)
    (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) {f : S →* S ⧸ Subgroup.center S}
    (hf : ∀ s : S, f s = ((⟨dlt x s, dlt_mem (fun _ ht => conj_mem_of_mem_normalizer h.2.2.1 ht)
      s.2⟩ : S) : S ⧸ Subgroup.center S))
    (hidx : (f.range.comap (QuotientGroup.mk' (Subgroup.center S))).index = 2)
    (hr : 8 ≤ Nat.card f.range) (ih : ∀ H < S, Hyp22 x H → Concl22 x H) : False := by
  have hS2 := h.1
  have hxS := h.2.2.1
  have hxS' : ∀ t ∈ S, x * t * x⁻¹ ∈ S := fun t ht => conj_mem_of_mem_normalizer hxS ht
  set Z := S ⊓ Subgroup.centralizer (S : Set G) with hZdef
  set C := S ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  obtain ⟨hScard, hrel⟩ := card_relations h hx hf
  rw [hidx] at hrel
  have hZC : Z ≤ C := le_inf inf_le_left (center_le_centralizer_of_hyp22 h hx)
  have hΦZ : inSubgroup frattini S ≤ Z := le_inf (Subgroup.map_subtype_le _) h.2.1
  obtain ⟨hKS, hZK, hδK, hcard, hSK, hxK⟩ := K_props h hf
  set K' := f.range.comap (QuotientGroup.mk' (Subgroup.center S)) with hK'def
  set K := K'.map S.subtype with hKdef
  rw [hidx] at hcard
  have hKlt : K < S := by
    refine lt_of_le_of_ne hKS fun hKS' => ?_
    have hSpos : 0 < Nat.card S := Nat.card_pos
    rw [hKS'] at hcard
    omega
  have hK := Hyp22.mono h hKS hxK
  have hihK := ih K hKlt hK
  have hδC : ∀ k ∈ K, dlt x k ∈ C := by
    intro k hk
    set t := dlt x k with ht
    have htS : t ∈ S := dlt_mem hxS' (hKS hk)
    have h1 := hΦZ (inSubgroup_frattini_mono hS2 hKS (hihK k hk))
    have e : k⁻¹ * (x ^ 2 * k * (x ^ 2)⁻¹) = t ^ 2 * dlt x t := by
      have hxk : x * k * x⁻¹ = k * t := by rw [ht]; unfold dlt; group
      have hxt : x * t * x⁻¹ = t * dlt x t := by unfold dlt; group
      calc k⁻¹ * (x ^ 2 * k * (x ^ 2)⁻¹) = k⁻¹ * (x * (x * k * x⁻¹) * x⁻¹) := by
            rw [sq]; group
        _ = k⁻¹ * (x * (k * t) * x⁻¹) := by rw [hxk]
        _ = k⁻¹ * ((x * k * x⁻¹) * (x * t * x⁻¹)) := by group
        _ = k⁻¹ * ((k * t) * (t * dlt x t)) := by rw [hxk, hxt]
        _ = t ^ 2 * dlt x t := by rw [sq]; group
    rw [e] at h1
    have h2 : dlt x t ∈ Z := by
      have h3 := hΦZ (sq_mem_inSubgroup_frattini hS2 htS)
      have := Z.mul_mem (Z.inv_mem h3) h1
      simpa using this
    exact ⟨htS, Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_dlt_mem h hx htS h2).symm⟩
  set C' := C.subgroupOf S with hC'def
  have hZC' : Subgroup.center S ≤ C' := by
    intro s hs
    rw [Subgroup.mem_subgroupOf]
    exact hZC ((mem_center_iff_mem_inf s).mp hs)
  have hmk := card_map_mk_mul_card_center C' hZC'
  have hC'card : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcenter : Nat.card (Subgroup.center S) = Nat.card Z := by
    have : Subgroup.center S = Z.subgroupOf S := by
      ext s
      rw [mem_center_iff_mem_inf, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hmk2 : Nat.card (C'.map (QuotientGroup.mk' (Subgroup.center S))) = 2 := by
    have h2 : 2 * Nat.card Z = Nat.card C := hrel
    rw [hC'card, ← h2, hcenter] at hmk
    exact Nat.eq_of_mul_eq_mul_right hZpos (by rw [hmk])
  have hfK : ∀ k ∈ K', f k ∈ C'.map (QuotientGroup.mk' (Subgroup.center S)) := by
    intro k hk
    rw [hf]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hδC k ⟨k, hk, rfl⟩))
  have hKle := card_le_card_ker_mul f K' _ hfK
  have hker : Nat.card f.ker = Nat.card C := by
    have : f.ker = C' := by
      ext s
      rw [MonoidHom.mem_ker, dltBar_eq_one_iff h hx hf, hC'def, Subgroup.mem_subgroupOf,
        hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h' => ⟨s.2, h'.symm⟩, fun h' => h'.2.symm⟩
    rw [this, hC'card]
  rw [hker, hmk2] at hKle
  have hK'card : Nat.card K' = Nat.card K :=
    Nat.card_congr (K'.equivMapOfInjective S.subtype S.subtype_injective).toEquiv
  rw [hK'card] at hKle
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have : Nat.card C * 8 ≤ Nat.card C * 4 := by
    calc Nat.card C * 8 ≤ Nat.card C * Nat.card f.range := Nat.mul_le_mul_left _ hr
      _ = Nat.card S := hScard.symm
      _ = Nat.card K * 2 := hcard.symm
      _ ≤ Nat.card C * 2 * 2 := Nat.mul_le_mul_right _ hKle
      _ = Nat.card C * 4 := by ring
  omega

theorem concl22 {x : G} (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    ∀ S : Subgroup G, Hyp22 x S → Concl22 x S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  induction S using WellFoundedLT.induction with
  | _ S ih =>
  intro h
  have hS2 := h.1
  have hxS := h.2.2.1
  obtain ⟨f, hf⟩ := exists_dltBar h
  set C := S ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  by_cases hSx : S ≤ Subgroup.centralizer ({x} : Set G)
  · intro s hs
    have hxs : Commute x s := (Subgroup.mem_centralizer_singleton_iff.mp (hSx hs)).symm
    have : x ^ 2 * s * (x ^ 2)⁻¹ = s := by
      rw [(hxs.pow_left 2).eq]
      group
    rw [this, inv_mul_cancel]
    exact Subgroup.one_mem _
  obtain ⟨hScard, hrel⟩ := card_relations h hx hf
  have hCpos : 0 < Nat.card C := Nat.card_pos
  obtain ⟨a, ha⟩ : ∃ a, Nat.card f.range = 2 ^ a :=
    ((hS2.to_quotient (Subgroup.center S)).to_subgroup f.range).exists_card_eq
  obtain ⟨b, hb⟩ : ∃ b, (f.range.comap (QuotientGroup.mk' (Subgroup.center S))).index = 2 ^ b := by
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    have hdvd : (f.range.comap (QuotientGroup.mk' (Subgroup.center S))).index ∣ 2 ^ n :=
      hn ▸ Subgroup.index_dvd_card _
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨b, hb⟩
  rcases a with _ | _ | a
  ·
    exfalso
    apply hSx
    rw [pow_zero] at ha
    rw [ha, mul_one] at hScard
    have hCS : C = S := Subgroup.eq_of_le_of_card_ge inf_le_left hScard.le
    intro s hs
    exact (hCS ▸ hs : s ∈ C).2
  ·
    have hidx : C.relIndex S = 2 := by
      have h1 := Subgroup.card_mul_index (C.subgroupOf S)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ S)).toEquiv,
        hScard, ha, pow_one] at h1
      exact Nat.eq_of_mul_eq_mul_left hCpos h1
    exact forall_mem_of_le_centralizer_index_two hS2 hxS inf_le_left hidx inf_le_right
  · rcases b with _ | _ | b
    · exact (false_of_index_eq_one h hx hf (by rw [hb, pow_zero]) hSx).elim
    · rcases a with _ | a
      · exact (false_of_index_eq_two_of_card_range_eq_four h hx hf (by rw [hb, pow_one])
          (by rw [ha]; norm_num)).elim
      · refine (false_of_index_eq_two_of_eight_le h hx hf (by rw [hb, pow_one]) ?_ ih).elim
        rw [ha]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (a + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · refine concl22_of_four_le_index h hf ?_ ih
      rw [hb]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (b + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem tim78_2_2 {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hΦ : inSubgroup frattini S ≤ S ⊓ Subgroup.centralizer (S : Set G)) {x : G}
    (hxS : x ∈ Subgroup.normalizer (S : Set G)) (hx : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hC : S ⊓ Subgroup.centralizer ({x} : Set G) = S ⊓ Subgroup.centralizer ({x ^ 2} : Set G)) :
    S ⊓ Subgroup.centralizer (S : Set G) ≤ Subgroup.centralizer ({x} : Set G) ∧
      ∀ s ∈ S, s⁻¹ * (x ^ 2 * s * (x ^ 2)⁻¹) ∈ inSubgroup frattini S := by
  have h : Hyp22 x S := ⟨hS2, hΦ.trans inf_le_right, hxS, hC⟩
  exact ⟨center_le_centralizer_of_hyp22 h hx, concl22 hx S h⟩

end CFSG.RankThree.GF2n.Tim78
