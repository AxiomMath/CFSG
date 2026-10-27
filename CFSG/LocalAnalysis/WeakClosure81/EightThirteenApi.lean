module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFrag

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

private def oTwoSetA (N K : Subgroup G) : Set (Subgroup G) :=
  {W | N ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧ ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ N}

private theorem oTwoMod_eq_iSup_A (N K : Subgroup G) :
    oTwoMod N K = ⨆ W ∈ oTwoSetA N K, W := rfl

private theorem le_oTwoMod_of_A {N K W : Subgroup G} (hNW : N ≤ W) (hWK : W ≤ K)
    (hWnorm : (W.subgroupOf K).Normal)
    (hpow : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ N) : W ≤ oTwoMod N K :=
  le_iSup₂ (f := fun W (_ : W ∈ oTwoSetA N K) => W) W ⟨hNW, hWK, hWnorm, hpow⟩

theorem le_oTwoMod_self {N K : Subgroup G} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) : N ≤ oTwoMod N K :=
  le_oTwoMod_of_A le_rfl hNK hN (fun w hw => ⟨0, by simpa using hw⟩)

theorem oTwoMod_le_self {N K : Subgroup G} : oTwoMod N K ≤ K :=
  iSup₂_le fun _ hW => hW.2.1

theorem normal_oTwoMod_of_normal {N K : Subgroup G} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) : ((oTwoMod N K).subgroupOf K).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer oTwoMod_le_self]
  have hle : K ≤ ⨅ x : oTwoSetA N K, Subgroup.normalizer ((x : Subgroup G) : Set G) := by
    intro k hk
    simp only [Subgroup.mem_iInf]
    intro x
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer x.2.2.1).mp x.2.2.2.1 hk
  have hsup : (⨆ x : oTwoSetA N K, (x : Subgroup G)) = oTwoMod N K :=
    (iSup_subtype'' (oTwoSetA N K) id).trans (oTwoMod_eq_iSup_A N K).symm
  intro k hk
  have hk' := Subgroup.iInf_normalizer_le_normalizer_iSup
    (fun x : oTwoSetA N K => (x : Subgroup G)) (hle hk)
  rwa [hsup] at hk'

theorem Sit813.cGrp_normal {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : ((cGrp H T).subgroupOf K).Normal := by
  have hc := h.concl813
  have hCH : cGrp H T ≤ H := hc.comp.2.1.trans hc.comp.2.2.1
  have hKH : K ≤ H := hc.sub_L.trans hc.comp.2.2.1
  have hHnorm : H ≤ Subgroup.normalizer (cGrp H T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mp hc.comp.1
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hc.ge_C).mpr (hKH.trans hHnorm)

theorem Sit813.oTwoMod_normal {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : ((oTwoMod (cGrp H T) K).subgroupOf K).Normal :=
  normal_oTwoMod_of_normal h.concl813.ge_C h.cGrp_normal

theorem Sit813.cGrp_le_oTwoMod {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : cGrp H T ≤ oTwoMod (cGrp H T) K :=
  le_oTwoMod_self h.concl813.ge_C h.cGrp_normal

private theorem sit813_section_simple_A {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    ∃ (X : Type) (_ : Group X) (φ : ↥K →* X), Function.Surjective φ ∧
      (∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoMod (cGrp H T) K) ∧
      IsSimpleGroup X ∧ Nat.card X = 60 ∧ ¬ IsMulCommutative X := by
  obtain ⟨X, hXgrp, φ, hφ, hker, hX⟩ := h.concl813.c_shape
  letI : Group X := hXgrp
  have hX' : CFSG.Blueprint.LieModel X .PSL 2 2 2 := hX
  have hXs : IsSimpleGroup X :=
    CFSG.ComponentClassification.FooteLit.isSimpleGroup_of_lieModel_psl_two hX'
  have hXcard : Nat.card X = 60 := by
    rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hX',
      show CFSG.Open.ordA 1 (2 ^ 2) = 60 by decide]
  refine ⟨X, hXgrp, φ, hφ, hker, hXs, hXcard, ?_⟩
  intro hcomm
  haveI : IsMulCommutative X := hcomm
  have hp := (Group.is_simple_iff_prime_card (α := X)).mp hXs
  rw [hXcard] at hp
  norm_num at hp

theorem Sit813.kn1 {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    ∀ B : Subgroup G, oTwoMod (cGrp H T) K ≤ B → B ≤ K →
      (B.subgroupOf K).Normal → B = oTwoMod (cGrp H T) K ∨ B = K := by
  obtain ⟨X, hXgrp, φ, hφ, hker, hXs, -, -⟩ := sit813_section_simple_A h
  letI : Group X := hXgrp
  intro B hNB hBK hBnorm
  haveI : ((B.subgroupOf K).map φ).Normal := hBnorm.map φ hφ
  rcases hXs.eq_bot_or_eq_top_of_normal ((B.subgroupOf K).map φ) with hbot | htop
  · left
    apply le_antisymm ?_ hNB
    intro b hb
    have hbK : b ∈ K := hBK hb
    have hbX : φ ⟨b, hbK⟩ ∈ (B.subgroupOf K).map φ :=
      Subgroup.mem_map.mpr ⟨⟨b, hbK⟩, by simpa [Subgroup.mem_subgroupOf] using hb, rfl⟩
    have h1 : φ ⟨b, hbK⟩ = 1 := by
      rw [hbot] at hbX
      exact Subgroup.mem_bot.mp hbX
    exact (hker ⟨b, hbK⟩).mp h1
  · right
    apply le_antisymm hBK
    intro b hb
    have hbK : b ∈ K := hb
    have hbX : φ ⟨b, hbK⟩ ∈ (B.subgroupOf K).map φ := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x, hxB, hxeq⟩ := Subgroup.mem_map.mp hbX
    have hker' : φ (x⁻¹ * ⟨b, hbK⟩) = 1 := by
      rw [map_mul, map_inv, hxeq, inv_mul_cancel]
    have hmemN : (x : G)⁻¹ * b ∈ oTwoMod (cGrp H T) K := by
      have := (hker (x⁻¹ * ⟨b, hbK⟩)).mp hker'
      simpa using this
    have hmemB : (x : G)⁻¹ * b ∈ B := hNB hmemN
    have heq : b = (x : G) * ((x : G)⁻¹ * b) := by group
    rw [heq]
    exact B.mul_mem hxB hmemB

theorem Sit813.kn2 {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    ∃ k₁ ∈ K, ∃ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∉ oTwoMod (cGrp H T) K := by
  obtain ⟨X, hXgrp, φ, hφ, hker, -, -, hXnab⟩ := sit813_section_simple_A h
  letI : Group X := hXgrp
  by_contra hcon
  push Not at hcon
  apply hXnab
  refine IsMulCommutative.of_comm fun x y => ?_
  obtain ⟨k₁, rfl⟩ := hφ x
  obtain ⟨k₂, rfl⟩ := hφ y
  have hc : φ (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) = 1 := (hker _).mpr (hcon k₁ k₁.2 k₂ k₂.2)
  have h2 : (φ k₁ * φ k₂) * (φ k₂ * φ k₁)⁻¹ = 1 := by
    simpa [mul_inv_rev, mul_assoc] using hc
  exact mul_inv_eq_one.mp h2

theorem Sit813.kn3 {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    ∀ k ∈ K, (∀ x ∈ K, k * x * k⁻¹ * x⁻¹ ∈ oTwoMod (cGrp H T) K) →
      k ∈ oTwoMod (cGrp H T) K := by
  obtain ⟨X, hXgrp, φ, hφ, hker, hXs, -, hXnab⟩ := sit813_section_simple_A h
  letI : Group X := hXgrp
  intro k hkK hcomm
  have hcenter : Subgroup.center X = ⊥ := by
    rcases hXs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exact absurd ((Subgroup.center_eq_top_iff).mp h) hXnab
  have hz : φ ⟨k, hkK⟩ ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    have hc : φ ⟨k, hkK⟩ * φ x * (φ ⟨k, hkK⟩)⁻¹ * (φ x)⁻¹ = 1 := by
      have := (hker (⟨k, hkK⟩ * x * ⟨k, hkK⟩⁻¹ * x⁻¹)).mpr (by
        simpa using hcomm (x : G) x.2)
      simpa using this
    have h2 : (φ ⟨k, hkK⟩ * φ x) * (φ x * φ ⟨k, hkK⟩)⁻¹ = 1 := by
      simpa [mul_inv_rev, mul_assoc] using hc
    exact (mul_inv_eq_one.mp h2).symm
  have h1 : φ ⟨k, hkK⟩ = 1 := by
    rw [hcenter] at hz
    exact Subgroup.mem_bot.mp hz
  exact (hker ⟨k, hkK⟩).mp h1

theorem Sit813.kn4 {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    (oTwoMod (cGrp H T) K).relIndex K = 60 := by
  obtain ⟨X, hXgrp, φ, hφ, hker, -, hXcard, -⟩ := sit813_section_simple_A h
  letI : Group X := hXgrp
  haveI : ((oTwoMod (cGrp H T) K).subgroupOf K).Normal := h.oTwoMod_normal
  have hker_eq : φ.ker = (oTwoMod (cGrp H T) K).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker x
  have e : (↥K ⧸ φ.ker) ≃* X := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hcard : Nat.card (↥K ⧸ φ.ker) = Nat.card X := Nat.card_congr e.toEquiv
  change ((oTwoMod (cGrp H T) K).subgroupOf K).index = 60
  rw [Subgroup.index_eq_card, ← hker_eq, hcard, hXcard]

theorem Sit813.mem_rGrp_iff {H T K : Subgroup G} {t : G} :
    t ∈ rGrp H T K ↔ t ∈ T ∧ t ∈ normalizer (K : Set G) ∧
      ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K := by
  have hnk : oTwoMod (cGrp H T) K ≤ K := oTwoMod_le_self
  have key : ∀ {x : G}, x ∈ T ∧ x ∈ normalizer (K : Set G) ∧
      (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K) →
      x ∈ normalizer (oTwoMod (cGrp H T) K : Set G) := by
    rintro x ⟨-, -, hx⟩
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have h1 : x * n * x⁻¹ * n⁻¹ ∈ oTwoMod (cGrp H T) K := hx n (hnk hn)
    have h2 : (x * n * x⁻¹ * n⁻¹) * n ∈ oTwoMod (cGrp H T) K :=
      (oTwoMod (cGrp H T) K).mul_mem h1 hn
    have h3 : x * n * x⁻¹ = (x * n * x⁻¹ * n⁻¹) * n := by group
    rw [h3]
    exact h2
  constructor
  · intro ht
    unfold rGrp at ht
    refine Subgroup.closure_induction
      (p := fun t _ => t ∈ T ∧ t ∈ normalizer (K : Set G) ∧
        ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K) ?_ ?_ ?_ ?_ ht
    · rintro t ⟨htT, htK, htC⟩; exact ⟨htT, htK, htC⟩
    · exact ⟨T.one_mem, (Subgroup.normalizer _).one_mem, fun k _ => by simp⟩
    · rintro x y _ _ ⟨hxT, hxK, hxC⟩ ⟨hyT, hyK, hyC⟩
      refine ⟨T.mul_mem hxT hyT, (Subgroup.normalizer _).mul_mem hxK hyK, fun k hk => ?_⟩
      have hxN : x ∈ Subgroup.normalizer (oTwoMod (cGrp H T) K : Set G) :=
        key ⟨hxT, hxK, hxC⟩
      have hyb : y * k * y⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K := hyC k hk
      have heq : (x * y) * k * (x * y)⁻¹ * k⁻¹ =
          (x * (y * k * y⁻¹ * k⁻¹) * x⁻¹) * (x * k * x⁻¹ * k⁻¹) := by group
      rw [heq]
      exact (oTwoMod (cGrp H T) K).mul_mem
        ((Subgroup.mem_normalizer_iff.mp hxN _).1 hyb) (hxC k hk)
    · rintro x _ ⟨hxT, hxK, hxC⟩
      have hxN : x ∈ Subgroup.normalizer (oTwoMod (cGrp H T) K : Set G) := key ⟨hxT, hxK, hxC⟩
      have hxN' : x⁻¹ ∈ Subgroup.normalizer (oTwoMod (cGrp H T) K : Set G) :=
        (Subgroup.normalizer _).inv_mem hxN
      refine ⟨T.inv_mem hxT, (Subgroup.normalizer _).inv_mem hxK, fun k hk => ?_⟩
      have h1 : (x * k * x⁻¹ * k⁻¹)⁻¹ ∈ oTwoMod (cGrp H T) K :=
        (oTwoMod (cGrp H T) K).inv_mem (hxC k hk)
      have heq : x⁻¹ * k * x⁻¹⁻¹ * k⁻¹ = x⁻¹ * (x * k * x⁻¹ * k⁻¹)⁻¹ * x := by group
      rw [heq]
      simpa using (Subgroup.mem_normalizer_iff.mp hxN' _).1 h1
  · rintro ⟨htT, htK, htC⟩
    exact Subgroup.subset_closure ⟨htT, htK, htC⟩

theorem Sit813.card_A_eq_four {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    Nat.card A = 4 := by
  obtain ⟨-, g, hAg, -⟩ := h.mem
  have hV : IsElemAbelian 2 V := h.minCex.hyp.hyp7.1
  have hAab : IsElemAbelian 2 A := (isElemAbelian_conjSubgroup' hV g).mono hAg
  have hA2 : IsPGroup 2 ↥A := CFSG.Open.IsElemAbelian.isPGroup hAab
  rw [card_eq_two_pow_of_isPGroup hA2, h.concl812.2.2.1]
  norm_num

theorem Sit813.isElemAbelian_A {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    IsElemAbelian 2 A := by
  obtain ⟨-, g, hAg, -⟩ := h.mem
  have hV : IsElemAbelian 2 V := h.minCex.hyp.hyp7.1
  exact (isElemAbelian_conjSubgroup' hV g).mono hAg

theorem Sit813.isTI_form {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    ∀ g : G, g ∉ normalizer (V : Set G) → ∀ v ∈ V, g * v * g⁻¹ ∈ V → v = 1 := by
  intro g hg v hv hgv
  have hne : conjSubgroup V g ≠ V := fun hEq => hg (conjSubgroup_eq_iff_mem_normalizer.mp hEq)
  have hbot := inf_conjSubgroup_eq_bot_of_isTI h.minCex.hyp.hyp7.2.2 hne
  have hvg : v ∈ conjSubgroup V g := mem_conjSubgroup_iff.mpr hgv
  have hmem : v ∈ V ⊓ conjSubgroup V g := Subgroup.mem_inf.mpr ⟨hv, hvg⟩
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem Sit813.le_normalizer_T {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    T ≤ normalizer (V : Set G) :=
  h.minCex.hyp.sylow.le.trans inf_le_right

theorem Sit813.a_le_normalizer_V {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    A ≤ normalizer (V : Set G) :=
  h.mem.1.trans h.le_normalizer_T

theorem Sit813.le_normalizer_cGrp {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    H ≤ normalizer (cGrp H T : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (h.concl813.comp.2.1.trans h.concl813.comp.2.2.1)).mp h.concl813.comp.1

theorem Sit813.rGrp_le_T {H T K : Subgroup G} : rGrp H T K ≤ T := fun _ ht =>
  (Sit813.mem_rGrp_iff.mp ht).1

theorem Sit813.mem_rGrp_of_mem_oTwoMod {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) {x : G} (hxN : x ∈ oTwoMod (cGrp H T) K) (hxT : x ∈ T) :
    x ∈ rGrp H T K := by
  have hx : x ∈ T ⊓ oTwoMod (cGrp H T) K := Subgroup.mem_inf.mpr ⟨hxT, hxN⟩
  rw [← h.inf_rGrp_eq] at hx
  exact (Subgroup.mem_inf.mp hx).2

theorem Sit813.oTwoMod_le_inf {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    oTwoMod (cGrp H T) K ≤ K ⊓ normalizer (V : Set G) :=
  le_inf oTwoMod_le_self h.oTwoMod_le_normalizer

theorem Sit813.exists_decomp {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K)
    {a : G} (ha : a ∈ A) :
    ∃ k ∈ K ⊓ normalizer (V : Set G), ∃ t ∈ rGrp H T K, a = k * t := by
  obtain ⟨k, hk, t, ht, c, hc, rfl⟩ := h.exists_mul_of_mem ha
  have htH : t ∈ H := (h.minCex.hyp.sylow.le.trans inf_le_left) (Sit813.rGrp_le_T ht)
  have hc' : t * c * t⁻¹ ∈ cGrp H T :=
    (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_cGrp htH) c).1 hc
  refine ⟨k * (t * c * t⁻¹), (K ⊓ normalizer (V : Set G)).mul_mem hk
    (Subgroup.mem_inf.mpr ⟨h.concl813.ge_C hc', h.cGrp_le_normalizer hc'⟩), t, ht, by group⟩

theorem Sit813.card_V_eq_eight {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    Nat.card V = 8 := by
  have hV : IsElemAbelian 2 V := h.minCex.hyp.hyp7.1
  have hV2 : IsPGroup 2 ↥V := CFSG.Open.IsElemAbelian.isPGroup hV
  rw [card_eq_two_pow_of_isPGroup hV2, h.concl812.1]
  norm_num

private theorem mem_normalizer_conjClosure_of_mem_normalizer_A {V K : Subgroup G} {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htK : t ∈ Subgroup.normalizer (K : Set G)) :
    t ∈ Subgroup.normalizer (conjClosure V K : Set G) := by
  have hS : t ∈ Subgroup.normalizer {x : G | ∃ h ∈ K, ∃ z ∈ V, h * z * h⁻¹ = x} := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨h, hh, z, hz, rfl⟩ := hn
    exact ⟨t * h * t⁻¹, (Subgroup.mem_normalizer_iff.mp htK h).1 hh,
      t * z * t⁻¹, (Subgroup.mem_normalizer_iff.mp htV z).1 hz, by group⟩
  exact Subgroup.normalizer_le_normalizer_closure _ hS

theorem Sit813.a_le_normalizer_uGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : A ≤ normalizer (uGrp V K : Set G) := by
  intro a ha
  obtain ⟨k, hk, t, ht, c, hc, rfl⟩ := h.exists_mul_of_mem ha
  obtain ⟨htT, htK, -⟩ := Sit813.mem_rGrp_iff.mp ht
  have htU : t ∈ normalizer (uGrp V K : Set G) :=
    mem_normalizer_conjClosure_of_mem_normalizer_A (h.le_normalizer_T htT) htK
  have hkU : k ∈ normalizer (uGrp V K : Set G) :=
    le_normalizer_conjClosure V K (Subgroup.mem_inf.mp hk).1
  have hcU : c ∈ normalizer (uGrp V K : Set G) :=
    le_normalizer_conjClosure V K (h.concl813.ge_C hc)
  exact (normalizer (uGrp V K : Set G)).mul_mem ((normalizer (uGrp V K : Set G)).mul_mem hkU htU)
    hcU

theorem Sit813.isElemAbelian_uGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : IsElemAbelian 2 (uGrp V K) := by
  have hyp := h.minCex.hyp
  have hV : IsElemAbelian 2 V := hyp.hyp7.1
  have hTI := hyp.hyp7.2.2
  have hH0 : IsCalH0 V H := h.calH0
  have hH : IsCalH V H := hH0.1
  have hT := hyp.sylow
  have hKH : K ≤ H := h.concl813.sub_L.trans h.concl813.comp.2.2.1
  have hconjM : ∀ k ∈ K, conjSubgroup V k ≤ normalizer (V : Set G) := fun k hk =>
    (conjSubgroup_le_pCoreOf_of_isCalH0 hH0 (hKH hk)).trans
      ((pCoreOf_le_of_isCalH hH hT).trans h.le_normalizer_T)
  have hgen : ∀ g₁ ∈ K, ∀ g₂ ∈ K,
      conjSubgroup V g₁⁻¹ ≤ normalizer (conjSubgroup V g₂⁻¹ : Set G) := by
    intro g₁ hg₁ g₂ hg₂ u hu
    rw [mem_conjSubgroup_iff] at hu
    have hmem : g₂⁻¹ * u * g₂ ∈ conjSubgroup V (g₁⁻¹ * g₂) := by
      rw [mem_conjSubgroup_iff]
      have heq : g₁⁻¹ * g₂ * (g₂⁻¹ * u * g₂) * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * u * g₁⁻¹⁻¹ := by group
      rw [heq]
      exact hu
    have hp : g₂⁻¹ * u * g₂ ∈ normalizer (V : Set G) :=
      hconjM (g₁⁻¹ * g₂) (K.mul_mem (K.inv_mem hg₁) hg₂) hmem
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    have heq : g₂⁻¹ * (u * w * u⁻¹) * g₂⁻¹⁻¹ =
        (g₂⁻¹ * u * g₂) * (g₂⁻¹ * w * g₂⁻¹⁻¹) * (g₂⁻¹ * u * g₂)⁻¹ := by group
    rw [heq]
    exact Subgroup.mem_normalizer_iff.mp hp (g₂⁻¹ * w * g₂⁻¹⁻¹)
  have hc : ∀ a ∈ {x : G | ∃ h ∈ K, ∃ z ∈ V, h * z * h⁻¹ = x},
      ∀ b ∈ {x : G | ∃ h ∈ K, ∃ z ∈ V, h * z * h⁻¹ = x}, a * b = b * a := by
    rintro a ⟨k, hk, z, hz, rfl⟩ b ⟨l, hl, w, hw, rfl⟩
    have hzW : k * z * k⁻¹ ∈ conjSubgroup V k⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have heq : k⁻¹ * (k * z * k⁻¹) * k⁻¹⁻¹ = z := by group
      rw [heq]
      exact hz
    have hwW : l * w * l⁻¹ ∈ conjSubgroup V l⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have heq : l⁻¹ * (l * w * l⁻¹) * l⁻¹⁻¹ = w := by group
      rw [heq]
      exact hw
    exact commute_of_le_normalizer_of_le_normalizer hV hTI ⟨k⁻¹, rfl⟩ ⟨l⁻¹, rfl⟩
      (hgen k hk l hl) (hgen l hl k hk) _ hzW _ hwW
  have hp : ∀ a ∈ {x : G | ∃ h ∈ K, ∃ z ∈ V, h * z * h⁻¹ = x}, a ^ 2 = 1 := by
    rintro a ⟨k, hk, z, hz, rfl⟩
    have hz2 : z * z = 1 := hV.mul_self_eq_one hz
    have heq : (k * z * k⁻¹) ^ 2 = k * (z * z) * k⁻¹ := by rw [pow_two]; group
    rw [heq, hz2]
    group
  exact IsElemAbelian.closure_of_commute hc hp

end CFSG.LocalAnalysis.WeakClosure81

end
