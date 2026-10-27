module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

open scoped commutatorElement

private lemma wcgapka_conj_mem_inf_centralizer {G : Type*} [Group G] {S : Subgroup G}
    (hS : S.Normal) {d : G} {z : G} (hz : z ∈ S ⊓ centralizer (S : Set G)) :
    d * z * d⁻¹ ∈ S ⊓ centralizer (S : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨hS.conj_mem z hz.1 d, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hzd : z * (d⁻¹ * s * d) = (d⁻¹ * s * d) * z :=
    ((Subgroup.mem_centralizer_iff.mp hz.2) (d⁻¹ * s * d) (hS.conj_mem' s hs d)).symm
  calc s * (d * z * d⁻¹) = d * ((d⁻¹ * s * d) * z) * d⁻¹ := by group
    _ = d * (z * (d⁻¹ * s * d)) * d⁻¹ := by rw [← hzd]
    _ = (d * z * d⁻¹) * s := by group

private def wcgapka_conjHom {G : Type*} [Group G] {S : Subgroup G} (hS : S.Normal) (d : G) :
    S →* S where
  toFun x := ⟨d * (x : G) * d⁻¹, hS.conj_mem (x : G) x.2 d⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul, Subtype.coe_mk]; group)

private lemma wcgapka_subgroupOf_centralizer_normal {G : Type*} [Group G]
    {S Z : Subgroup G} (hZ : Z ≤ centralizer (S : Set G)) (hZS : Z ≤ S) :
    (Z.subgroupOf S).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  change (g : G) * (n : G) * (g : G)⁻¹ ∈ Z
  have hcomm : (g : G) * (n : G) = (n : G) * (g : G) :=
    (Subgroup.mem_centralizer_iff.mp (hZ hn)) (g : G) g.2
  rw [hcomm]
  simpa using hn

private lemma wcgapka_commutator_mul_central {G : Type*} [Group G] {S : Subgroup G}
    {a b z₁ z₂ : G} (hz₁ : z₁ ∈ centralizer (S : Set G)) (hz₂ : z₂ ∈ centralizer (S : Set G))
    (ha : a ∈ S) (hb : b ∈ S) (hz₂S : z₂ ∈ S) :
    (a * z₁) * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have conj1 : ∀ w ∈ S, z₁ * w * z₁⁻¹ = w := by
    intro w hw
    rw [show z₁ * w = w * z₁ from (Subgroup.mem_centralizer_iff.mp hz₁ w hw).symm]
    group
  have conj2 : z₂ * a⁻¹ * z₂⁻¹ = a⁻¹ := by
    rw [show z₂ * a⁻¹ = a⁻¹ * z₂ from
      (Subgroup.mem_centralizer_iff.mp hz₂ a⁻¹ (S.inv_mem ha)).symm]
    group
  calc (a * z₁) * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹
      = a * (z₁ * b * z₁⁻¹) * (z₁ * z₂ * z₁⁻¹) * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * z₂ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [conj1 b hb, conj1 z₂ hz₂S]
    _ = a * b * (z₂ * a⁻¹ * z₂⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [conj2]

private lemma wcgapka_commutator_div {G : Type*} [Group G] {S : Subgroup G}
    (hS : S.Normal) (d : G) (x y : S) :
    ((wcgapka_conjHom hS d x * x⁻¹ : S) : G) *
        (((wcgapka_conjHom hS d y * y⁻¹ : S) : G))⁻¹ =
      ((wcgapka_conjHom hS d (x / y) * (x / y)⁻¹ : S) : G) *
        ((((x / y) * (wcgapka_conjHom hS d y * y⁻¹) * (x / y)⁻¹ *
          (wcgapka_conjHom hS d y * y⁻¹)⁻¹ : S)) : G) := by
  have hxy : ((x / y : S) : G) * (y : G) = (x : G) := by
    rw [← Subgroup.coe_mul, div_mul_cancel]
  have h := commutatorElement_mul_right_eq_mul_conj d ((x / y : S) : G) (y : G)
  rw [hxy] at h
  show ⁅d, (x : G)⁆ * (⁅d, (y : G)⁆)⁻¹ =
    ⁅d, ((x / y : S) : G)⁆ *
      (((x / y : S) : G) * ⁅d, (y : G)⁆ * ((x / y : S) : G)⁻¹ * (⁅d, (y : G)⁆)⁻¹)
  rw [commutatorElement_def] at h ⊢
  rw [h]
  group

private lemma wcgapka_two_pow_dvd_168_le_eight {n : ℕ} (h : 2 ^ n ∣ 168) : 2 ^ n ≤ 8 := by
  have hcop : Nat.Coprime (2 ^ n) 21 := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; norm_num
    · exact (Nat.coprime_pow_left_iff hnpos 2 21).mpr (by norm_num)
  have hdvd : 2 ^ n ∣ 8 := by
    have h' : 2 ^ n ∣ 8 * 21 := by
      rwa [show (8 * 21 : ℕ) = 168 by norm_num]
    exact (Nat.Coprime.dvd_mul_right hcop).mp h'
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem sylow_le_of_orderFive_aux {B : Type} [Group B] [Finite B] {S N : Subgroup B}
    (hS : S.Normal) (hN : N.Normal) (hidx : N.index ∣ 168) {d : B} (hd : d ^ 5 = 1)
    (hfpf : ∀ x ∈ S, d * x * d⁻¹ * x⁻¹ ∈ S ⊓ centralizer (S : Set B) →
      x ∈ S ⊓ centralizer (S : Set B))
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ centralizer (S : Set B))
    (hcom : ∀ z ∈ S ⊓ centralizer (S : Set B), ∃ x ∈ S, ∃ y ∈ S, z = x * y * x⁻¹ * y⁻¹) :
    S ≤ N := by
  let M : Subgroup B := N ⊓ S
  let Z : Subgroup B := S ⊓ centralizer (S : Set B)
  have hMleN : M ≤ N := inf_le_left
  have hMleS : M ≤ S := inf_le_right
  have hZcent : Z ≤ centralizer (S : Set B) := inf_le_right
  have hdN : d ∈ N := by
    have hpow : (QuotientGroup.mk d : B ⧸ N) ^ 5 = 1 := by
      rw [← QuotientGroup.mk_pow, hd, QuotientGroup.mk_one]
    have h5 : orderOf (QuotientGroup.mk d : B ⧸ N) ∣ 5 := orderOf_dvd_of_pow_eq_one hpow
    have h168 : orderOf (QuotientGroup.mk d : B ⧸ N) ∣ 168 := by
      have h := orderOf_dvd_natCard (QuotientGroup.mk d : B ⧸ N)
      rw [← Subgroup.index_eq_card] at h
      exact h.trans hidx
    have h1 : orderOf (QuotientGroup.mk d : B ⧸ N) = 1 :=
      Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 5 168) h5 h168
    exact (QuotientGroup.eq_one_iff d).mp (orderOf_eq_one_iff.mp h1)
  have hc_mem : ∀ x ∈ S, d * x * d⁻¹ * x⁻¹ ∈ M := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : x * d⁻¹ * x⁻¹ ∈ N := hN.conj_mem d⁻¹ (N.inv_mem hdN) x
      have h2 : d * (x * d⁻¹ * x⁻¹) ∈ N := N.mul_mem hdN h1
      simpa [mul_assoc] using h2
    · have h1 : d * x * d⁻¹ ∈ S := hS.conj_mem x hx d
      exact S.mul_mem h1 (S.inv_mem hx)
  let Zs : Subgroup S := Z.subgroupOf S
  have hZsN : Zs.Normal := wcgapka_subgroupOf_centralizer_normal hZcent inf_le_left
  haveI := hZsN
  have hker : Zs ≤ ((QuotientGroup.mk' Zs).comp (wcgapka_conjHom hS d)).ker := by
    intro z hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show ((wcgapka_conjHom hS d z : S) : B) ∈ S ⊓ centralizer (S : Set B)
    have hzZ : (z : B) ∈ S ⊓ centralizer (S : Set B) := by
      rwa [Subgroup.mem_subgroupOf] at hz
    have hcoe : ((wcgapka_conjHom hS d z : S) : B) = d * (z : B) * d⁻¹ := rfl
    rw [hcoe]
    exact wcgapka_conj_mem_inf_centralizer hS hzZ
  let σ : S ⧸ Zs →* S ⧸ Zs :=
    QuotientGroup.lift Zs ((QuotientGroup.mk' Zs).comp (wcgapka_conjHom hS d)) hker
  let f : S ⧸ Zs → S ⧸ Zs := fun a => σ a * a⁻¹
  have hf_inj : Function.Injective f := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Zs a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Zs b
    have hfx : f (QuotientGroup.mk' Zs x) =
        QuotientGroup.mk' Zs (wcgapka_conjHom hS d x * x⁻¹) := by
      change σ (QuotientGroup.mk' Zs x) * (QuotientGroup.mk' Zs x)⁻¹ = _
      dsimp only [σ]
      change QuotientGroup.lift Zs ((QuotientGroup.mk' Zs).comp (wcgapka_conjHom hS d)) hker
          (x : S ⧸ Zs) * (QuotientGroup.mk' Zs x)⁻¹ = _
      rw [QuotientGroup.lift_mk', MonoidHom.comp_apply, ← map_inv, ← map_mul]
    have hfy : f (QuotientGroup.mk' Zs y) =
        QuotientGroup.mk' Zs (wcgapka_conjHom hS d y * y⁻¹) := by
      change σ (QuotientGroup.mk' Zs y) * (QuotientGroup.mk' Zs y)⁻¹ = _
      dsimp only [σ]
      change QuotientGroup.lift Zs ((QuotientGroup.mk' Zs).comp (wcgapka_conjHom hS d)) hker
          (y : S ⧸ Zs) * (QuotientGroup.mk' Zs y)⁻¹ = _
      rw [QuotientGroup.lift_mk', MonoidHom.comp_apply, ← map_inv, ← map_mul]
    have hab' : QuotientGroup.mk' Zs (wcgapka_conjHom hS d x * x⁻¹) =
        QuotientGroup.mk' Zs (wcgapka_conjHom hS d y * y⁻¹) :=
      hfx.symm.trans (hab.trans hfy)
    have hAB : ((wcgapka_conjHom hS d x * x⁻¹ : S) : B) *
        (((wcgapka_conjHom hS d y * y⁻¹ : S) : B))⁻¹ ∈ Z := by
      have h := hab'
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at h
      simpa [div_eq_mul_inv, mul_inv_rev] using h
    have hsplit := wcgapka_commutator_div hS d x y
    let C : S := (x / y) * (wcgapka_conjHom hS d y * y⁻¹) * (x / y)⁻¹ *
      (wcgapka_conjHom hS d y * y⁻¹)⁻¹
    have hC : (C : B) ∈ Z := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact S.mul_mem (S.mul_mem (S.mul_mem (x / y).2
          (S.mul_mem (hS.conj_mem (y : B) y.2 d) (S.inv_mem y.2))) (S.inv_mem (x / y).2))
          (S.inv_mem (S.mul_mem (hS.conj_mem (y : B) y.2 d) (S.inv_mem y.2)))
      · exact hcomm ((x / y : S) : B) (x / y).2
          (((wcgapka_conjHom hS d y * y⁻¹ : S) : B))
          (S.mul_mem (hS.conj_mem (y : B) y.2 d) (S.inv_mem y.2))
    have hDwZ : ((wcgapka_conjHom hS d (x / y) * (x / y)⁻¹ : S) : B) ∈ Z := by
      have h2 : ((wcgapka_conjHom hS d (x / y) * (x / y)⁻¹ : S) : B) * (C : B) ∈ Z := by
        rw [← hsplit]
        exact hAB
      have h4 : ((wcgapka_conjHom hS d (x / y) * (x / y)⁻¹ : S) : B) * (C : B) * (C : B)⁻¹ ∈ Z :=
        Z.mul_mem h2 (Z.inv_mem hC)
      rw [mul_assoc, mul_inv_cancel, mul_one] at h4
      exact h4
    have hwZ : ((x / y : S) : B) ∈ Z :=
      hfpf ((x / y : S) : B) (x / y).2 hDwZ
    have hwZs : (x / y : S) ∈ Zs := Subgroup.mem_subgroupOf.mpr hwZ
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    exact hwZs
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  have hcover : ∀ s ∈ S, ∃ m ∈ M, ∃ z ∈ Z, s = m * z := by
    intro s hs
    let ss : S := ⟨s, hs⟩
    obtain ⟨a, ha⟩ := hf_surj (QuotientGroup.mk' Zs ss)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Zs a
    have hfx : f (QuotientGroup.mk' Zs x) =
        QuotientGroup.mk' Zs (wcgapka_conjHom hS d x * x⁻¹) := by
      change σ (QuotientGroup.mk' Zs x) * (QuotientGroup.mk' Zs x)⁻¹ = _
      dsimp only [σ]
      change QuotientGroup.lift Zs ((QuotientGroup.mk' Zs).comp (wcgapka_conjHom hS d)) hker
          (x : S ⧸ Zs) * (QuotientGroup.mk' Zs x)⁻¹ = _
      rw [QuotientGroup.lift_mk', MonoidHom.comp_apply, ← map_inv, ← map_mul]
    have hx : QuotientGroup.mk' Zs (wcgapka_conjHom hS d x * x⁻¹) =
        QuotientGroup.mk' Zs ss := hfx.symm.trans ha
    let Dx : S := wcgapka_conjHom hS d x * x⁻¹
    have hxZ : (Dx : B) * (ss : B)⁻¹ ∈ Z := by
      have h := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at h
      simpa [Dx, div_eq_mul_inv] using h
    let z0 : B := (Dx : B) * (ss : B)⁻¹
    have hz0 : z0 ∈ Z := hxZ
    have hz0inv : z0⁻¹ ∈ Z := Z.inv_mem hz0
    have hDxM : (Dx : B) ∈ M := by
      have hcoe : (Dx : B) = d * (x : B) * d⁻¹ * (x : B)⁻¹ := by
        show ((wcgapka_conjHom hS d x * x⁻¹ : S) : B) = d * (x : B) * d⁻¹ * (x : B)⁻¹
        rfl
      rw [hcoe]
      exact hc_mem x x.2
    have hDxS : (Dx : B) ∈ S := (Subgroup.mem_inf.mp hDxM).2
    have hz0invcent : z0⁻¹ ∈ centralizer (S : Set B) := (Subgroup.mem_inf.mp hz0inv).2
    have hcommz : z0⁻¹ * (Dx : B) = (Dx : B) * z0⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp hz0invcent (Dx : B) hDxS).symm
    refine ⟨(Dx : B), hDxM, z0⁻¹, hz0inv, ?_⟩
    rw [← hcommz]
    change (ss : B) = z0⁻¹ * (Dx : B)
    dsimp only [z0]
    group
  have hZleM : Z ≤ M := by
    intro z hz
    obtain ⟨x, hx, y, hy, hxy⟩ := hcom z hz
    obtain ⟨m₁, hm₁, z₁, hz₁, hx'⟩ := hcover x hx
    obtain ⟨m₂, hm₂, z₂, hz₂, hy'⟩ := hcover y hy
    have hz₁S : z₁ ∈ S := (Subgroup.mem_inf.mp hz₁).1
    have hz₂S : z₂ ∈ S := (Subgroup.mem_inf.mp hz₂).1
    have hz₁c : z₁ ∈ centralizer (S : Set B) := (Subgroup.mem_inf.mp hz₁).2
    have hz₂c : z₂ ∈ centralizer (S : Set B) := (Subgroup.mem_inf.mp hz₂).2
    have hm₁S : m₁ ∈ S := (Subgroup.mem_inf.mp hm₁).2
    have hm₂S : m₂ ∈ S := (Subgroup.mem_inf.mp hm₂).2
    have hcommid := wcgapka_commutator_mul_central hz₁c hz₂c hm₁S hm₂S hz₂S
    have hz_eq : z = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by
      rw [hxy, hx', hy']
      exact hcommid
    have hmem : m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
    rwa [hz_eq]
  intro s hs
  obtain ⟨m, hm, z, hz, rfl⟩ := hcover s hs
  exact N.mul_mem (hMleN hm) (hMleN (hZleM hz))

theorem center_le_of_irred_aux {B : Type} [Group B] [Finite B] {S N : Subgroup B}
    (hS : S.Normal) (hN : N.Normal) (hp : IsPGroup 2 S) (hidx : N.index ∣ 168)
    (hbig : 8 * Nat.card ↥(S ⊓ centralizer (S : Set B)) < Nat.card S)
    (hirr : ∀ x ∈ S, x ∉ centralizer (S : Set B) → ∀ Z' : Subgroup B,
      Z' ≤ S ⊓ centralizer (S : Set B) → (∀ b : B, ∀ z ∈ Z', b * z * b⁻¹ ∈ Z') →
      (∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Z') → Z' = S ⊓ centralizer (S : Set B)) :
    S ⊓ centralizer (S : Set B) ≤ N := by
  let M : Subgroup B := N ⊓ S
  let Z : Subgroup B := S ⊓ centralizer (S : Set B)
  let ZM : Subgroup B := M ⊓ Z
  have hMleN : M ≤ N := inf_le_left
  have hMleS : M ≤ S := inf_le_right
  have hZcent : Z ≤ centralizer (S : Set B) := inf_le_right
  have hMN : M.Normal := by
    change (N ⊓ S).Normal
    haveI := hN
    haveI := hS
    infer_instance
  have hMrel : M.relIndex S ∣ 168 := by
    have h1 : M.relIndex S = N.relIndex S := by
      change (N ⊓ S).relIndex S = N.relIndex S
      rw [Subgroup.inf_relIndex_right]
    rw [h1]
    haveI := hN
    exact (Subgroup.relIndex_dvd_index_of_normal (H := N) (K := S)).trans hidx
  obtain ⟨n, hn⟩ := hp.index (M.subgroupOf S)
  have hpow2 : M.relIndex S = 2 ^ n := (rfl : M.relIndex S = (M.subgroupOf S).index).trans hn
  have hle8 : M.relIndex S ≤ 8 := by
    rw [hpow2]
    exact wcgapka_two_pow_dvd_168_le_eight (hpow2 ▸ hMrel)
  have hcard : Nat.card S ≤ 8 * Nat.card M := by
    have h := Subgroup.relIndex_mul_card (H := M) (K := S)
    rw [inf_eq_left.mpr hMleS] at h
    calc Nat.card S = M.relIndex S * Nat.card M := h.symm
      _ ≤ 8 * Nat.card M := Nat.mul_le_mul_right _ hle8
  have hlt : Nat.card Z < Nat.card M := by
    have h : 8 * Nat.card Z < 8 * Nat.card M := lt_of_lt_of_le hbig hcard
    omega
  have hMnotleZ : ¬ M ≤ Z := fun hle =>
    absurd (Subgroup.card_le_of_le hle) (not_le_of_gt hlt)
  by_cases hZM : M ⊓ Z = Z
  · intro z hz
    have hzM : z ∈ M := by
      have : z ∈ M ⊓ Z := by rw [hZM]; exact hz
      exact (Subgroup.mem_inf.mp this).1
    exact hMleN hzM
  · exfalso
    have hMneZM : M ≠ ZM := by
      intro h
      exact hMnotleZ (by rw [h]; exact inf_le_right)
    have hnotle : ¬ M ≤ ZM := fun hle => hMnotleZ (hle.trans inf_le_right)
    obtain ⟨m₀, hm₀M, hm₀ZM⟩ := Set.not_subset.mp hnotle
    have hm₀S : m₀ ∈ S := hMleS hm₀M
    let ZMs : Subgroup S := ZM.subgroupOf S
    have hZMsN : ZMs.Normal :=
      wcgapka_subgroupOf_centralizer_normal (Z := ZM) (inf_le_right.trans hZcent)
        (inf_le_left.trans hMleS)
    haveI := hZMsN
    let Q := S ⧸ ZMs
    have hQp : IsPGroup 2 Q := hp.to_quotient ZMs
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent Q := hQp.isNilpotent
    let H : Subgroup Q := (M.subgroupOf S).map (QuotientGroup.mk' ZMs)
    have hMsubN : (M.subgroupOf S).Normal := hMN.subgroupOf S
    have hHN : H.Normal := hMsubN.map (QuotientGroup.mk' ZMs) (QuotientGroup.mk'_surjective ZMs)
    haveI := hHN
    have hHne : H ≠ ⊥ := by
      intro hbot
      have hmem : QuotientGroup.mk' ZMs ⟨m₀, hm₀S⟩ ∈ H :=
        Subgroup.mem_map.mpr ⟨⟨m₀, hm₀S⟩, Subgroup.mem_subgroupOf.mpr hm₀M, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmem
      exact hm₀ZM hmem
    have hcenter_ne : H ⊓ Subgroup.center Q ≠ ⊥ :=
      Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
    obtain ⟨q, hq, hqne⟩ : ∃ q ∈ H ⊓ Subgroup.center Q, q ≠ 1 := by
      obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter_ne
      exact ⟨(a : Q), a.2, fun h => ha (Subtype.ext h)⟩
    obtain ⟨m, hmM, hmq⟩ : ∃ m : S, (m : B) ∈ M ∧ QuotientGroup.mk' ZMs m = q := by
      obtain ⟨hqH, _⟩ := Subgroup.mem_inf.mp hq
      obtain ⟨s, hs, hsq⟩ := Subgroup.mem_map.mp hqH
      rw [Subgroup.mem_subgroupOf] at hs
      exact ⟨s, hs, hsq⟩
    have hqcenter : q ∈ Subgroup.center Q := (Subgroup.mem_inf.mp hq).2
    have hm_not_ZM : (m : B) ∉ ZM := by
      intro hmZM
      have h1 : QuotientGroup.mk' ZMs m = 1 :=
        (QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_subgroupOf.mpr hmZM)
      exact hqne (hmq.symm.trans h1)
    have hm_not_cent : (m : B) ∉ centralizer (S : Set B) := by
      intro hmc
      exact hm_not_ZM (Subgroup.mem_inf.mpr ⟨hmM, Subgroup.mem_inf.mpr ⟨m.2, hmc⟩⟩)
    have hcommZM : ∀ y ∈ S, (m : B) * y * (m : B)⁻¹ * y⁻¹ ∈ ZM := by
      intro y hy
      let ys : S := ⟨y, hy⟩
      change ((m * ys * m⁻¹ * ys⁻¹ : S) : B) ∈ ZM
      have hqy : QuotientGroup.mk' ZMs ys * q = q * QuotientGroup.mk' ZMs ys :=
        Subgroup.mem_center_iff.mp hqcenter (QuotientGroup.mk' ZMs ys)
      rw [← hmq] at hqy
      have h1 : QuotientGroup.mk' ZMs (ys * m) = QuotientGroup.mk' ZMs (m * ys) := by
        simpa only [← map_mul] using hqy
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h1
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at h1
      have h2 : ((ys * m) / (m * ys) : S) = ys * m * ys⁻¹ * m⁻¹ := by
        rw [div_eq_mul_inv, mul_inv_rev]
        group
      rw [h2] at h1
      have h3 : (m * ys * m⁻¹ * ys⁻¹ : S) = (ys * m * ys⁻¹ * m⁻¹ : S)⁻¹ := by group
      rw [h3]
      simpa using ZM.inv_mem h1
    have hZMleZ : ZM ≤ S ⊓ centralizer (S : Set B) := inf_le_right
    have hinv : ∀ b : B, ∀ z ∈ ZM, b * z * b⁻¹ ∈ ZM := by
      intro b z hz
      exact Subgroup.mem_inf.mpr ⟨hMN.conj_mem z (Subgroup.mem_inf.mp hz).1 b,
        wcgapka_conj_mem_inf_centralizer hS (d := b) (Subgroup.mem_inf.mp hz).2⟩
    have hZM_eq : M ⊓ Z = Z :=
      hirr (m : B) m.2 hm_not_cent ZM hZMleZ hinv hcommZM
    exact hZM hZM_eq

end CFSG.LocalAnalysis.WeakClosure81

end
