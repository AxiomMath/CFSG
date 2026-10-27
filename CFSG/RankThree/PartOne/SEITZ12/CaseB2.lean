module

public import CFSG.RankThree.PartOne.SEITZ12.CaseB1
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open Subgroup

variable {G : Type*} [Group G]

theorem phi4B_normalizer_grow {S T : Subgroup G} [Finite T] (hST : S ≤ T) (hT : IsPGroup 2 T)
    (hne : ¬ T ≤ S) : ∃ n ∈ T, n ∉ S ∧ ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hlt : S.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥T) ∈ S.subgroupOf T := by rw [htop]; trivial
    exact hx'
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := ↥T) _ hlt
  obtain ⟨n, hn, hnS⟩ := IsConcreteLE.exists_of_lt hnorm
  refine ⟨n.1, n.2, fun hmem => hnS hmem, ?_⟩
  intro s hs
  exact (mem_normalizer_iff.1 hn ⟨s, hST hs⟩).1 hs

theorem phi4B_sylow_conj {D S : Subgroup G} [Finite D] (hSD : S ≤ D) (hSp : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup G, T ≤ D → IsPGroup 2 T → S ≤ T → T ≤ S) {y : G} (hyD : y ∈ D)
    (hy : IsPGroup 2 (Subgroup.zpowers y)) : ∃ d ∈ D, d * y * d⁻¹ ∈ S := by
  have hS₁p : IsPGroup 2 ↥(S.subgroupOf D) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSD).symm
  let P₀ : Sylow 2 D :=
    { toSubgroup := S.subgroupOf D
      isPGroup' := hS₁p
      is_maximal' := by
        intro Q hQ hle
        apply le_antisymm _ hle
        intro x hx
        have hT : IsPGroup 2 (Q.map D.subtype) := hQ.map D.subtype
        have hST : S ≤ Q.map D.subtype := fun s hs => ⟨⟨s, hSD hs⟩, hle hs, rfl⟩
        exact hmax _ (Subgroup.map_subtype_le Q) hT hST ⟨x, hx, rfl⟩ }
  have hY : IsPGroup 2 ↥((Subgroup.zpowers y).subgroupOf D) :=
    hy.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hyD)).symm
  obtain ⟨P₁, hP₁⟩ := hY.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D P₀ P₁
  refine ⟨(g : G)⁻¹, inv_mem g.2, ?_⟩
  have hyP : (⟨y, hyD⟩ : ↥D) ∈ (P₁ : Subgroup D) := hP₁ (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul] at hyP
  have h1 := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hyP
  have h1' : g⁻¹ * ⟨y, hyD⟩ * g ∈ (P₀ : Subgroup D) := by
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h1
  have h2 : ((g⁻¹ * ⟨y, hyD⟩ * g : D) : G) ∈ S := h1'
  simpa using h2

structure phi4B_Ctx (D X₂ S₂ Z₂ : Subgroup G) (t : G) (q : ℕ) (cls : G → Prop) : Prop where
  core : phi4B_Core X₂ S₂ Z₂ t q
  tD : t ∈ D
  X₂D : X₂ ≤ D
  X₁D : conjSub X₂ t ≤ D
  perf : ⁅X₂, X₂⁆ = X₂
  S₂syl : ∀ P : Subgroup G, P ≤ X₂ → IsPGroup 2 P → S₂ ≤ P → P = S₂
  cls_conj : ∀ g ∈ D, ∀ x, cls x → cls (g * x * g⁻¹)
  cls_t : cls t
  cls₂ : ∀ z ∈ Z₂, z ≠ 1 → cls z
  cls₃ : ∀ z₁ ∈ conjSub Z₂ t, ∀ z₂ ∈ Z₂, z₁ ≠ 1 → z₂ ≠ 1 → ¬ cls (z₁ * z₂)
  cls₄ : ∀ x ∈ X₂, x * x = 1 → x ≠ 1 → cls x
  B : ∀ z ∈ conjSub Z₂ t, z ≠ 1 → ∀ x ∈ D, x * z = z * x → x ∈ conjSub S₂ t ⊔ X₂
  N : ∀ n ∈ D, (∃ k : ℕ, orderOf n = 2 ^ k) →
    (∀ z ∈ conjSub Z₂ t, n * z * n⁻¹ ∈ conjSub Z₂ t) → ∀ z ∈ conjSub Z₂ t, n * z = z * n
  sq : ∃ y ∈ D, y * y = t

namespace phi4B_Core

variable {X₂ S₂ Z₂ : Subgroup G} {t : G} {q : ℕ}

theorem Z₁_ne (h : phi4B_Core X₂ S₂ Z₂ t q) : ∃ z ∈ conjSub Z₂ t, z ≠ 1 := by
  obtain ⟨z, hz, hz1⟩ := h.Z₂_ne
  exact ⟨t * z * t, phi4B_tau_mem h.t_sq hz, h.tau_ne_one hz1⟩

theorem comm_SX (h : phi4B_Core X₂ S₂ Z₂ t q) {a b : G} (ha : a ∈ conjSub S₂ t) (hb : b ∈ X₂) :
    a * b = b * a := (h.comm b hb a (h.S₁_le ha)).symm

theorem inter_Z (h : phi4B_Core X₂ S₂ Z₂ t q) {a : G} (ha : a ∈ conjSub Z₂ t) (hb : a ∈ Z₂) :
    a = 1 := by
  have hmem : a ∈ X₂ ⊓ conjSub X₂ t :=
    Subgroup.mem_inf.2 ⟨h.S₂_le (h.suz.Z_le hb), h.S₁_le (h.Z₁_le ha)⟩
  rw [h.inf] at hmem
  exact (Subgroup.mem_bot).1 hmem

end phi4B_Core

namespace phi4B_Ctx

variable {D X₂ S₂ Z₂ : Subgroup G} {t : G} {q : ℕ} {cls : G → Prop}

theorem S_le_D (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) : phi4B_S h.core ≤ D := by
  apply h.core.S_le _ h.tD
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h.core.mem_B0.1 hx
  exact mul_mem (h.X₁D (h.core.S₁_le ha)) (h.X₂D (h.core.S₂_le hb))

theorem cls_Z₁ (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) {z : G} (hz : z ∈ conjSub Z₂ t)
    (hz1 : z ≠ 1) : cls z := by
  have hc := h.core
  have h2 : cls (t * z * t) :=
    h.cls₂ _ (phi4B_tau_mem' hc.t_sq hz) (hc.tau_ne_one hz1)
  have h3 := h.cls_conj t h.tD _ h2
  have e : t * (t * z * t) * t⁻¹ = z := by
    rw [phi4B_inv_eq hc.t_sq]
    exact phi4B_tau_tau hc.t_sq z
  rwa [e] at h3

theorem pure_of_cls (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) {w : G} (hw : w ∈ phi4B_Om Z₂ t)
    (hcw : cls w) : w ∈ conjSub Z₂ t ∨ w ∈ Z₂ := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := h.core.mem_Om.1 hw
  by_cases h1 : w₁ = 1
  · right
    rw [h1, one_mul]
    exact hw₂
  · by_cases h2 : w₂ = 1
    · left
      rw [h2, mul_one]
      exact hw₁
    · exact absurd hcw (h.cls₃ w₁ hw₁ w₂ hw₂ h1 h2)

theorem dichotomy (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) {n : G} (hnD : n ∈ D)
    (hn : ∀ s ∈ phi4B_S h.core, n * s * n⁻¹ ∈ phi4B_S h.core) :
    (∀ z ∈ conjSub Z₂ t, n * z * n⁻¹ ∈ conjSub Z₂ t) ∨
      (∀ z ∈ conjSub Z₂ t, n * z * n⁻¹ ∈ Z₂) := by
  have hc := h.core
  have hpure : ∀ z ∈ conjSub Z₂ t, z ≠ 1 →
      (n * z * n⁻¹ ∈ conjSub Z₂ t ∨ n * z * n⁻¹ ∈ Z₂) ∧ n * z * n⁻¹ ≠ 1 := by
    intro z hz hz1
    refine ⟨?_, ?_⟩
    · have hΩ : n * z * n⁻¹ ∈ phi4B_Om Z₂ t :=
        hc.conj_Om_le hn (mem_sup_left hz)
      exact h.pure_of_cls hΩ (h.cls_conj n hnD z (h.cls_Z₁ hz hz1))
    · intro e
      apply hz1
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [e]; group
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hcon
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply ha'
    simp
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hb'
    simp
  obtain ⟨hA, hA1⟩ := hpure a ha ha1
  obtain ⟨hB, hB1⟩ := hpure b hb hb1
  have hA2 : n * a * n⁻¹ ∈ Z₂ := hA.resolve_left ha'
  have hB2 : n * b * n⁻¹ ∈ conjSub Z₂ t := hB.resolve_right hb'
  have hab : a * b ∈ conjSub Z₂ t := mul_mem ha hb
  have hconj : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
  have hab1 : a * b ≠ 1 := by
    intro e
    rw [e] at hconj
    have e2 : (n * a * n⁻¹) * (n * b * n⁻¹) = 1 := by rw [← hconj]; group
    have e3 : n * b * n⁻¹ = (n * a * n⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right e2
    exact hB1 (hc.inter_Z hB2 (by rw [e3]; exact inv_mem hA2))
  obtain ⟨hC, _⟩ := hpure (a * b) hab hab1
  rw [hconj] at hC
  have hcomm : (n * a * n⁻¹) * (n * b * n⁻¹) = (n * b * n⁻¹) * (n * a * n⁻¹) :=
    (hc.comm_Z hB2 hA2).symm
  rcases hC with hC | hC
  ·
    have : n * a * n⁻¹ ∈ conjSub Z₂ t := by
      have e : n * a * n⁻¹ = ((n * a * n⁻¹) * (n * b * n⁻¹)) * (n * b * n⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem hC (inv_mem hB2)
    exact hA1 (hc.inter_Z this hA2)
  · have : n * b * n⁻¹ ∈ Z₂ := by
      have e : n * b * n⁻¹ = (n * a * n⁻¹)⁻¹ * ((n * a * n⁻¹) * (n * b * n⁻¹)) := by group
      rw [e]
      exact mul_mem (inv_mem hA2) hC
    exact hB1 (hc.inter_Z hB2 this)

theorem B2_fix (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) {T : Subgroup G} (hTD : T ≤ D)
    (hTp : IsPGroup 2 T) (hST : phi4B_S h.core ≤ T) {n : G} (hnT : n ∈ T)
    (hn : ∀ z ∈ conjSub Z₂ t, n * z * n⁻¹ ∈ conjSub Z₂ t) : n ∈ phi4B_S h.core := by
  have hc := h.core
  have hord : ∃ k : ℕ, orderOf n = 2 ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hTp) ⟨n, hnT⟩
    exact ⟨k, by rw [← Subgroup.orderOf_mk n hnT]; exact hk⟩
  have hcent := h.N n (hTD hnT) hord hn
  obtain ⟨z, hz, hz1⟩ := hc.Z₁_ne
  have hmem := h.B z hz hz1 n (hTD hnT) (hcent z hz)
  obtain ⟨a, ha, r, hr, hnr⟩ :=
    (phi4B_mem_sup_iff (fun _ ha _ hb => hc.comm_SX ha hb)).1 hmem
  have haT : a ∈ T := hST (hc.B0_le_S (hc.S₁_le_B0 ha))
  have hrT : r ∈ T := by
    have e : r = a⁻¹ * n := by rw [hnr]; group
    rw [e]
    exact mul_mem (inv_mem haT) hnT
  have hS₂T : S₂ ≤ T := fun x hx => hST (hc.B0_le_S (hc.S₂_le_B0 hx))
  have hP : T ⊓ X₂ = S₂ :=
    h.S₂syl _ inf_le_right hTp.to_inf_left (le_inf hS₂T hc.S₂_le)
  have hrS : r ∈ S₂ := by
    rw [← hP]
    exact Subgroup.mem_inf.2 ⟨hrT, hr⟩
  rw [hnr]
  exact hc.B0_le_S (mul_mem (hc.S₁_le_B0 ha) (hc.S₂_le_B0 hrS))

theorem B2 [Finite D] (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) {T : Subgroup G} (hTD : T ≤ D)
    (hTp : IsPGroup 2 T) (hST : phi4B_S h.core ≤ T) : T ≤ phi4B_S h.core := by
  have hc := h.core
  by_contra hne
  have : Finite T := Finite.of_injective (Subgroup.inclusion hTD) (Subgroup.inclusion_injective hTD)
  obtain ⟨n, hnT, hnS, hnn⟩ := phi4B_normalizer_grow hST hTp hne
  rcases h.dichotomy (hTD hnT) hnn with h1 | h2
  · exact hnS (h.B2_fix hTD hTp hST hnT h1)
  · have htT : t ∈ T := hST hc.t_mem_S
    have hn2 : ∀ z ∈ conjSub Z₂ t, (t * n) * z * (t * n)⁻¹ ∈ conjSub Z₂ t := by
      intro z hz
      have e : (t * n) * z * (t * n)⁻¹ = t * (n * z * n⁻¹) * t := by
        rw [mul_inv_rev, phi4B_inv_eq hc.t_sq]
        simp only [mul_assoc]
      rw [e]
      exact phi4B_tau_mem hc.t_sq (h2 z hz)
    have htn : t * n ∈ phi4B_S h.core := h.B2_fix hTD hTp hST (mul_mem htT hnT) hn2
    apply hnS
    have e : n = t * (t * n) := by rw [← mul_assoc, hc.t_sq, one_mul]
    rw [e]
    exact mul_mem hc.t_mem_S htn

end phi4B_Ctx

end CFSG.RankThree.PartOne.SEITZ12
