module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroSignedB
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroF4Dual
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem GGCaseZeroData.refl_shape (h : GGCaseZeroData p B Bs x L D J 𝒦) {m : ℕ} (hm : 3 ≤ m)
    (ιV : Additive ↥Bs ≃+ V) {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hF : GGCZFrameD p Bs (ggAutomizer L Bs) ιV e φ) :
    ∀ t ∈ ggAInf p B Bs x L D J, GGIsReflection p t →
      ggLin (p := p) ιV t ∈ ggCZRD e φ ∨ ggLin (p := p) ιV t ∈ ggCZS e φ ∨
        (m = 4 ∧ ggLin (p := p) ιV t ∈ ggCZH e φ) := by
  have : Finite V := Finite.of_equiv _ ιV.toEquiv
  have hp2 := (GGCaseZeroData.basic h).2.1
  obtain ⟨hd, hRD, hAL, hfixC⟩ := hF
  intro t htInf ht
  have htRefl : GGLinRefl (ggLin (p := p) ιV t) :=
    (ggIsReflection_iff_ggLinRefl hp2 ιV t).mp ht
  refine ggCZ_core hp2 hm hd htRefl ?_ ?_
  · intro v hv
    set b : ↥Bs := Additive.toMul (ιV.symm v) with hb
    have hveq : v = ιV (Additive.ofMul b) := by
      rw [hb]
      simp [ofMul_toMul]
    have hbfix : ∀ a ∈ ggAutomizer L Bs, a b = b := by
      intro a ha
      have hvv : ggLin (p := p) ιV a v = v := hfixC a ha v hv
      rw [hveq, ggLin_apply_ofMul] at hvv
      exact Additive.ofMul.injective (ιV.injective hvv)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (h.fixL b hbfix)
    have htb : t b = b := by
      have hbpow : b = ⟨x, h.mem⟩ ^ n := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow, hn]
      rw [hbpow, map_zpow, h.fix t htInf, ← hbpow]
    rw [hveq, ggLin_apply_ofMul]
    exact congrArg (fun z => ιV (Additive.ofMul z)) htb
  · intro r hr_mem
    have hmem := hr_mem
    obtain ⟨i, j, hij, ε, hε, hr'⟩ := hr_mem
    set f : Module.Dual (ZMod p) V := φ i - ε • φ j with hf
    set x' : V := e i - ε • e j with hx'
    have hfx : f x' = 2 := by
      have hii := hd i i
      have hjj := hd j j
      have hij' : φ i (e j) = 0 := by simpa [hij] using hd i j
      have hji : φ j (e i) = 0 := by simpa [hij.symm] using hd j i
      rcases hε with rfl | rfl <;> norm_num [f, x', hii, hjj, hij', hji]
    have hrr : r = reflection hfx := by
      refine LinearEquiv.ext fun v => ?_
      rw [hr', reflection_apply, hf, hx']
      rfl
    obtain ⟨a, ha, hlin⟩ := hAL r hmem
    have haRefl : GGIsReflection p a :=
      ggIsReflection_of_eq_reflection hp2 ιV hfx (hlin.trans hrr)
    have hconj : t * a * t⁻¹ ∈ ggAutomizer L Bs := h.normal t htInf a ha
    have hconjRefl : GGIsReflection p (t * a * t⁻¹) := haRefl.conj t
    have hRD' : ggLin (p := p) ιV (t * a * t⁻¹) ∈ ggCZRD e φ := hRD _ hconj hconjRefl
    rwa [map_mul, map_mul, map_inv, hlin] at hRD'



private lemma ggCZS_commute {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {r r' : V ≃ₗ[ZMod p] V} (hr : r ∈ ggCZS e φ)
    (hr' : r' ∈ ggCZS e φ) : r * r' = r' * r := by
  obtain ⟨i, hi⟩ := hr
  obtain ⟨j, hj⟩ := hr'
  refine LinearEquiv.ext fun v => ?_
  by_cases hij : i = j
  · subst hij
    have hrr : r = r' := by
      ext v
      rw [hi v, hj v]
    rw [hrr]
  · simp only [LinearEquiv.mul_apply, hi, hj, map_sub, map_smul,
      hd i j, hd j i, hij, Ne.symm hij, if_false]
    simp [smul_eq_mul, mul_zero, sub_zero]
    abel

private lemma ggCZRD_commute_of_m2 {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 2 → V} {φ : Fin 2 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {r r' : V ≃ₗ[ZMod p] V} (hr : r ∈ ggCZRD e φ)
    (hr' : r' ∈ ggCZRD e φ) : r * r' = r' * r := by
  obtain ⟨i, j, hij, ε, hε, hr⟩ := hr
  obtain ⟨i', j', hi'j', ε', hε', hr'⟩ := hr'
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp_all only [Fin.isValue, Fin.zero_eta, Fin.mk_one, ne_eq, not_false_eq_true]
  all_goals
    refine LinearEquiv.ext fun v => ?_
    have h00 : φ 0 (e 0) = 1 := by simpa using hd 0 0
    have h01 : φ 0 (e 1) = 0 := by simpa using hd 0 1
    have h10 : φ 1 (e 0) = 0 := by simpa using hd 1 0
    have h11 : φ 1 (e 1) = 1 := by simpa using hd 1 1
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;>
      simp_all [LinearEquiv.mul_apply] <;>
      module

private lemma ggCZGensB_subset_RD_union_S {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} {r : V ≃ₗ[ZMod p] V} (hr : GGCZGensB e φ r) :
    r ∈ ggCZRD e φ ∪ ggCZS e φ := by
  rcases hr with ⟨i, j, hij, hr⟩ | ⟨i, hi, hr⟩
  · left
    refine ⟨i, j, ?_, 1, Or.inl rfl, ?_⟩
    · intro h
      subst h
      omega
    · intro v
      rw [hr]
      simp
  · right
    exact ⟨i, hr⟩

theorem GGCaseZeroData.frameD_of_B (h : GGCaseZeroData p B Bs x L D J 𝒦) {m : ℕ} (hm : 2 ≤ m)
    (ιV : Additive ↥Bs ≃+ V) {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ)
    (hA : Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) = ggCZWB p e φ)
    (hne : ggAutomizerJoin L Bs 𝒦 ≠ ggAutomizer L Bs) :
    3 ≤ m ∧ GGCZFrameD p Bs (ggAutomizer L Bs) ιV e φ := by
  have : Finite V := Finite.of_equiv _ ιV.toEquiv
  have hp2 := (GGCaseZeroData.basic h).2.1
  let RL : Set (V ≃ₗ[ZMod p] V) :=
    { r | ∃ a ∈ ggAutomizer L Bs, GGIsReflection p a ∧ ggLin (p := p) ιV a = r }
  have hRL_sub : RL ⊆ ggCZRD e φ ∪ ggCZS e φ := by
    intro r hr
    obtain ⟨a, ha, haRefl, rfl⟩ := hr
    have hmem : ggLin (p := p) ιV a ∈ ggCZWB p e φ := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) ha)
    have hlin : GGLinRefl (ggLin (p := p) ιV a) :=
      (ggIsReflection_iff_ggLinRefl hp2 ιV a).mp haRefl
    exact ggCZWB_refl hp2 hd hmem hlin
  have hRL_conj : ∀ g ∈ ggCZWB p e φ, ∀ r ∈ RL, g * r * g⁻¹ ∈ RL := by
    intro g hg r hr
    rw [← hA] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    obtain ⟨b, hb, hbRefl, rfl⟩ := hr
    refine ⟨a * b * a⁻¹, h.normal a (h.join_le_ainf ha) b hb, hbRefl.conj a, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hRL_int_RD : RL ∩ ggCZRD e φ = ∅ ∨ ggCZRD e φ ⊆ RL := by
    by_cases h : ∃ r ∈ ggCZRD e φ, r ∈ RL
    · right
      obtain ⟨r₀, hr₀RD, hr₀RL⟩ := h
      intro r hrRD
      obtain ⟨g, hg, hgconj⟩ := ggCZWB_conj_RD hd hr₀RD hrRD
      have hmem := hRL_conj g hg r₀ hr₀RL
      rwa [hgconj] at hmem
    · left
      ext r
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hRL hRD
      exact h ⟨r, hRD, hRL⟩
  have hRL_int_S : RL ∩ ggCZS e φ = ∅ ∨ ggCZS e φ ⊆ RL := by
    by_cases h : ∃ r ∈ ggCZS e φ, r ∈ RL
    · right
      obtain ⟨r₀, hr₀S, hr₀RL⟩ := h
      intro r hrS
      obtain ⟨g, hg, hgconj⟩ := ggCZWB_conj_S hd hr₀S hrS
      have hmem := hRL_conj g hg r₀ hr₀RL
      rwa [hgconj] at hmem
    · left
      ext r
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hRL hS
      exact h ⟨r, hS, hRL⟩
  have hnot_both : ¬ (ggCZRD e φ ⊆ RL ∧ ggCZS e φ ⊆ RL) := by
    rintro ⟨hRD, hS⟩
    have hgen : {r | GGCZGensB e φ r} ⊆
        Subgroup.map (ggLin (p := p) ιV) (ggAutomizer L Bs) := by
      intro r hr
      rcases ggCZGensB_subset_RD_union_S hr with h | h
      · obtain ⟨a, ha, -, rfl⟩ := hRD h
        exact Subgroup.mem_map_of_mem _ ha
      · obtain ⟨a, ha, -, rfl⟩ := hS h
        exact Subgroup.mem_map_of_mem _ ha
    have hle : ggCZWB p e φ ≤ Subgroup.map (ggLin (p := p) ιV) (ggAutomizer L Bs) := by
      rw [ggCZWB]
      exact (Subgroup.closure_le _).mpr hgen
    have hmap_le : Subgroup.map (ggLin (p := p) ιV) (ggAutomizer L Bs) ≤
        Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) :=
      Subgroup.map_mono (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
    have hle' : Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) ≤
        Subgroup.map (ggLin (p := p) ιV) (ggAutomizer L Bs) := by
      rw [hA]
      exact hle
    have hEq : ggAutomizer L Bs = ggAutomizerJoin L Bs 𝒦 :=
      Subgroup.map_injective (ggLin_injective ιV) (le_antisymm hmap_le hle')
    exact hne hEq.symm
  have hnot_S : ¬ (RL ⊆ ggCZS e φ) := by
    intro hRL_S
    obtain ⟨r, hr, r', hr', hrRefl, hr'Refl, hne_comm⟩ := h.AL_noncomm
    have hrS : ggLin (p := p) ιV r ∈ ggCZS e φ := hRL_S ⟨r, hr, hrRefl, rfl⟩
    have hr'S : ggLin (p := p) ιV r' ∈ ggCZS e φ := hRL_S ⟨r', hr', hr'Refl, rfl⟩
    have hcomm : ggLin (p := p) ιV r * ggLin (p := p) ιV r' =
        ggLin (p := p) ιV r' * ggLin (p := p) ιV r :=
      ggCZS_commute hd hrS hr'S
    exact hne_comm (ggLin_injective ιV (by rw [map_mul, map_mul, hcomm]))
  have hRD_sub : ggCZRD e φ ⊆ RL := by
    rcases hRL_int_RD with h | h
    · exfalso
      apply hnot_S
      intro x hx
      rcases hRL_sub hx with hxRD | hxS
      · have hmem : x ∈ RL ∩ ggCZRD e φ := ⟨hx, hxRD⟩
        rw [h] at hmem
        exact hmem.elim
      · exact hxS
    · exact h
  have hRL_eq : RL = ggCZRD e φ := by
    apply le_antisymm _ hRD_sub
    intro x hx
    rcases hRL_sub hx with hxRD | hxS
    · exact hxRD
    · exfalso
      have hS_sub : ggCZS e φ ⊆ RL := by
        intro y hy
        obtain ⟨g, hg, hgconj⟩ := ggCZWB_conj_S hd hxS hy
        have hmem := hRL_conj g hg x hx
        rwa [hgconj] at hmem
      exact hnot_both ⟨hRD_sub, hS_sub⟩
  have hm3 : 3 ≤ m := by
    rcases Nat.lt_or_ge m 3 with hm_lt | hm_ge
    · have hm2 : m = 2 := by omega
      subst hm2
      obtain ⟨r, hr, r', hr', hrRefl, hr'Refl, hne_comm⟩ := h.AL_noncomm
      have hrRD : ggLin (p := p) ιV r ∈ ggCZRD e φ := by
        rw [← hRL_eq]
        exact ⟨r, hr, hrRefl, rfl⟩
      have hr'RD : ggLin (p := p) ιV r' ∈ ggCZRD e φ := by
        rw [← hRL_eq]
        exact ⟨r', hr', hr'Refl, rfl⟩
      have hcomm := ggCZRD_commute_of_m2 hd hrRD hr'RD
      exact absurd (ggLin_injective ιV (by rw [map_mul, map_mul, hcomm])) hne_comm
    · exact hm_ge
  refine ⟨hm3, hd, ?_, ?_, ?_⟩
  · intro a ha haRefl
    rw [← hRL_eq]
    exact ⟨a, ha, haRefl, rfl⟩
  · intro r hr
    obtain ⟨a, ha, hrefl, hlin⟩ := hRD_sub hr
    exact ⟨a, ha, hlin⟩
  · intro a ha v hv
    have hmem : ggLin (p := p) ιV a ∈ ggCZWB p e φ := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) ha)
    exact ggCZWB_fix hmem hv



private lemma ggCZGensF4_subset {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    {i : Fin 4} {r : V ≃ₗ[ZMod p] V} (hr : GGCZGensF4 e φ i r) :
    r ∈ ggCZRD e φ ∪ ggCZS e φ ∪ ggCZH e φ := by
  fin_cases i <;> simp only [GGCZGensF4] at hr
  · left; left
    refine ⟨1, 2, by decide, 1, Or.inl rfl, ?_⟩
    intro v; rw [hr]; simp
  · left; left
    refine ⟨2, 3, by decide, 1, Or.inl rfl, ?_⟩
    intro v; rw [hr]; simp
  · left; right
    exact ⟨3, hr⟩
  · right
    refine ⟨![1, -1, -1, -1], ?_, ?_⟩
    · intro k
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
    · intro v
      rw [hr]
      simp [Fin.sum_univ_four]
      module

theorem GGCaseZeroData.frameD_of_F4 (h : GGCaseZeroData p B Bs x L D J 𝒦)
    (ιV : Additive ↥Bs ≃+ V) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ)
    (hA : Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) = ggCZWF4 p e φ)
    (hne : ggAutomizerJoin L Bs 𝒦 ≠ ggAutomizer L Bs) :
    ∃ (e' : Fin 4 → V) (φ' : Fin 4 → Module.Dual (ZMod p) V),
      GGCZFrameD p Bs (ggAutomizer L Bs) ιV e' φ' ∧
        ggCZRD e' φ' ∪ ggCZS e' φ' ∪ ggCZH e' φ' = ggCZRD e φ ∪ ggCZS e φ ∪ ggCZH e φ := by
  have : Finite V := Finite.of_equiv _ ιV.toEquiv
  have hp2 := (GGCaseZeroData.basic h).2.1
  let RL : Set (V ≃ₗ[ZMod p] V) :=
    { r | ∃ a ∈ ggAutomizer L Bs, GGIsReflection p a ∧ ggLin (p := p) ιV a = r }
  have hRL_sub : RL ⊆ ggCZRD e φ ∪ ggCZS e φ ∪ ggCZH e φ := by
    intro r hr
    obtain ⟨a, ha, haRefl, rfl⟩ := hr
    have hmem : ggLin (p := p) ιV a ∈ ggCZWF4 p e φ := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) ha)
    have hlin : GGLinRefl (ggLin (p := p) ιV a) :=
      (ggIsReflection_iff_ggLinRefl hp2 ιV a).mp haRefl
    exact ggCZWF4_refl hp2 hd hmem hlin
  have hRL_conj : ∀ g ∈ ggCZWF4 p e φ, ∀ r ∈ RL, g * r * g⁻¹ ∈ RL := by
    intro g hg r hr
    rw [← hA] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    obtain ⟨b, hb, hbRefl, rfl⟩ := hr
    refine ⟨a * b * a⁻¹, h.normal a (h.join_le_ainf ha) b hb, hbRefl.conj a, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hRL_int_RD : RL ∩ ggCZRD e φ = ∅ ∨ ggCZRD e φ ⊆ RL := by
    by_cases h : ∃ r ∈ ggCZRD e φ, r ∈ RL
    · right
      obtain ⟨r₀, hr₀RD, hr₀RL⟩ := h
      intro r hrRD
      obtain ⟨g, hg, hgconj⟩ := ggCZWF4_conj_RD hp2 hd hr₀RD hrRD
      have hmem := hRL_conj g hg r₀ hr₀RL
      rwa [hgconj] at hmem
    · left
      ext r
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hRL hRD
      exact h ⟨r, hRD, hRL⟩
  have hRL_int_SH : RL ∩ (ggCZS e φ ∪ ggCZH e φ) = ∅ ∨
      (ggCZS e φ ∪ ggCZH e φ) ⊆ RL := by
    by_cases h : ∃ r ∈ ggCZS e φ ∪ ggCZH e φ, r ∈ RL
    · right
      obtain ⟨r₀, hr₀SH, hr₀RL⟩ := h
      intro r hrSH
      obtain ⟨g, hg, hgconj⟩ := ggCZWF4_conj_short hp2 hd hr₀SH hrSH
      have hmem := hRL_conj g hg r₀ hr₀RL
      rwa [hgconj] at hmem
    · left
      ext r
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hRL hSH
      exact h ⟨r, hSH, hRL⟩
  have hnot_both : ¬ (ggCZRD e φ ⊆ RL ∧ (ggCZS e φ ∪ ggCZH e φ) ⊆ RL) := by
    rintro ⟨hRD, hSH⟩
    have hgen : {r | ∃ i, GGCZGensF4 e φ i r} ⊆
        Subgroup.map (ggLin (p := p) ιV) (ggAutomizer L Bs) := by
      intro r hr
      obtain ⟨i, hi⟩ := hr
      rcases ggCZGensF4_subset hi with (hR | hS) | hH
      · obtain ⟨a, ha, -, rfl⟩ := hRD hR
        exact Subgroup.mem_map_of_mem _ ha
      · obtain ⟨a, ha, -, rfl⟩ := hSH (Or.inl hS)
        exact Subgroup.mem_map_of_mem _ ha
      · obtain ⟨a, ha, -, rfl⟩ := hSH (Or.inr hH)
        exact Subgroup.mem_map_of_mem _ ha
    have hle : ggCZWF4 p e φ ≤ Subgroup.map (ggLin (p := p) ιV) (ggAutomizer L Bs) := by
      rw [ggCZWF4]
      exact (Subgroup.closure_le _).mpr hgen
    have hmap_le : Subgroup.map (ggLin (p := p) ιV) (ggAutomizer L Bs) ≤
        Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) :=
      Subgroup.map_mono (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
    have hle' : Subgroup.map (ggLin (p := p) ιV) (ggAutomizerJoin L Bs 𝒦) ≤
        Subgroup.map (ggLin (p := p) ιV) (ggAutomizer L Bs) := by
      rw [hA]
      exact hle
    have hEq : ggAutomizer L Bs = ggAutomizerJoin L Bs 𝒦 :=
      Subgroup.map_injective (ggLin_injective ιV) (le_antisymm hmap_le hle')
    exact hne hEq.symm
  have hRL_ne : RL.Nonempty := by
    obtain ⟨r, hr, r', hr', hrRefl, hr'Refl, hne_comm⟩ := h.AL_noncomm
    exact ⟨ggLin (p := p) ιV r, ⟨r, hr, hrRefl, rfl⟩⟩
  rcases hRL_int_RD with hRD_empty | hRD_sub
  · have hSH_sub : (ggCZS e φ ∪ ggCZH e φ) ⊆ RL := by
      rcases hRL_int_SH with hSH_empty | hSH_sub
      · exfalso
        obtain ⟨x, hx⟩ := hRL_ne
        rcases hRL_sub hx with (hR | hS) | hH
        · have : x ∈ RL ∩ ggCZRD e φ := ⟨hx, hR⟩
          rw [hRD_empty] at this
          exact this.elim
        · have : x ∈ RL ∩ (ggCZS e φ ∪ ggCZH e φ) := ⟨hx, Or.inl hS⟩
          rw [hSH_empty] at this
          exact this.elim
        · have : x ∈ RL ∩ (ggCZS e φ ∪ ggCZH e φ) := ⟨hx, Or.inr hH⟩
          rw [hSH_empty] at this
          exact this.elim
      · exact hSH_sub
    have hRL_eq_SH : RL = ggCZS e φ ∪ ggCZH e φ := by
      apply le_antisymm _ hSH_sub
      intro x hx
      rcases hRL_sub hx with (hR | hS) | hH
      · have : x ∈ RL ∩ ggCZRD e φ := ⟨hx, hR⟩
        rw [hRD_empty] at this
        exact this.elim
      · exact Or.inl hS
      · exact Or.inr hH
    obtain ⟨e', φ', hd', hC', hRD', hSH'⟩ := ggCZ_F4_dual hp2 hd
    refine ⟨e', φ', ?_, ?_⟩
    · refine ⟨hd', ?_, ?_, ?_⟩
      · intro a ha haRefl
        rw [hRD']
        rw [← hRL_eq_SH]
        exact ⟨a, ha, haRefl, rfl⟩
      · intro r hr
        rw [hRD'] at hr
        rw [← hRL_eq_SH] at hr
        obtain ⟨a, ha, hrefl, hlin⟩ := hr
        exact ⟨a, ha, hlin⟩
      · intro a ha v hv
        have hv' : ∀ k, φ k v = 0 := (hC' v).mp hv
        have hmem : ggLin (p := p) ιV a ∈ ggCZWF4 p e φ := by
          rw [← hA]
          exact Subgroup.mem_map_of_mem _ (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) ha)
        exact ggCZWF4_fix hmem hv'
    · rw [Set.union_assoc, hSH', hRD', Set.union_comm, Set.union_assoc]
  · have hSH_empty : RL ∩ (ggCZS e φ ∪ ggCZH e φ) = ∅ := by
      rcases hRL_int_SH with h | h
      · exact h
      · exfalso
        exact hnot_both ⟨hRD_sub, h⟩
    have hRL_eq_RD : RL = ggCZRD e φ := by
      apply le_antisymm _ hRD_sub
      intro x hx
      rcases hRL_sub hx with (hR | hS) | hH
      · exact hR
      · have : x ∈ RL ∩ (ggCZS e φ ∪ ggCZH e φ) := ⟨hx, Or.inl hS⟩
        rw [hSH_empty] at this
        exact this.elim
      · have : x ∈ RL ∩ (ggCZS e φ ∪ ggCZH e φ) := ⟨hx, Or.inr hH⟩
        rw [hSH_empty] at this
        exact this.elim
    refine ⟨e, φ, ?_, rfl⟩
    refine ⟨hd, ?_, ?_, ?_⟩
    · intro a ha haRefl
      rw [← hRL_eq_RD]
      exact ⟨a, ha, haRefl, rfl⟩
    · intro r hr
      obtain ⟨a, ha, hrefl, hlin⟩ := hRD_sub hr
      exact ⟨a, ha, hlin⟩
    · intro a ha v hv
      have hmem : ggLin (p := p) ιV a ∈ ggCZWF4 p e φ := by
        rw [← hA]
        exact Subgroup.mem_map_of_mem _ (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) ha)
      exact ggCZWF4_fix hmem hv


end

end CFSG.StandardType

end
