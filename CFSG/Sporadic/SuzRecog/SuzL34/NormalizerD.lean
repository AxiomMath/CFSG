module

public import CFSG.Sporadic.SuzRecog.SuzL34.NormalizerL
public import CFSG.Sporadic.SuzRecog.SuzL34.BitAction
public import CFSG.Sporadic.SuzRecog.SuzL34.X16

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34.LocalData

open Subgroup CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0 CFSG.ABGLocalTools
  CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.Open

open scoped Pointwise

variable {G : Type} [Group G] {z : G} (D : LocalData G z)

theorem l1Decs_le_invE (D : LocalData G z) : decSubgroup l1Decs ≤ invE 1 :=
  D.decSubgroup_le_invE (by decide)

@[expose] noncomputable def lEquiv (hF1 : F1Prop) : Fin 16 ≃ ↥(D.pull (decSubgroup l1Decs)) :=
  (l1Equiv hF1).trans (D.pullEquiv D.l1Decs_le_invE).symm.toEquiv

theorem coe_lEquiv (hF1 : F1Prop) (i : Fin 16) :
    ((D.lEquiv hF1 i : ↥(D.pull (decSubgroup l1Decs))) : G) =
      D.elt (l1Elt i) (D.l1Decs_le_invE (l1Elt_mem i)) := rfl

theorem lEquiv_xor (hF1 : F1Prop) (i j : Fin 16) :
    ((D.lEquiv hF1 (xor16 i j) : ↥(D.pull (decSubgroup l1Decs))) : G) =
      D.lEquiv hF1 i * D.lEquiv hF1 j := by
  have h1 : l1Equiv hF1 (xor16 i j) = l1Equiv hF1 i * l1Equiv hF1 j := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_l1Equiv, coe_l1Equiv, coe_l1Equiv, l1Elt_xor hF1]
  have h2 : D.lEquiv hF1 (xor16 i j) = D.lEquiv hF1 i * D.lEquiv hF1 j := by
    change (D.pullEquiv D.l1Decs_le_invE).symm (l1Equiv hF1 (xor16 i j)) =
      (D.pullEquiv D.l1Decs_le_invE).symm (l1Equiv hF1 i) *
        (D.pullEquiv D.l1Decs_le_invE).symm (l1Equiv hF1 j)
    rw [h1, map_mul]
  rw [h2]
  rfl

theorem card_centralizer_L_inf_centralizer_t0 [Finite G] (hF6 : F6Prop)
    (hzL : z ∈ D.pull (decSubgroup l1Decs)) :
    Nat.card ↥(centralizer (D.pull (decSubgroup l1Decs) : Set G) ⊓
      centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G)) = 64 := by
  classical
  let Lg : Subgroup G := D.pull (decSubgroup l1Decs)
  let t0 : G := D.elt (permC 1782 w0T) D.w0_mem
  let L1 : Subgroup (Equiv.Perm (Fin 1782)) := decSubgroup l1Decs
  let V0 : Subgroup (Equiv.Perm (Fin 1782)) := tabSubgroup v0Tabs
  have hL1 : L1 ≤ invE 1 := D.l1Decs_le_invE
  have hV0 : V0 ≤ invE 1 := by
    rw [show V0 = tabSubgroup v0Tabs from rfl, D.tabSubgroup_v0Tabs]
    exact inf_le_right
  have hCL_le : centralizer (Lg : Set G) ≤ centralizer ({z} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hg z hzL).symm
  have h1 : D.pull (centralizer (L1 : Set (Equiv.Perm (Fin 1782)))) =
      centralizer (Lg : Set G) ⊓ centralizer ({z} : Set G) :=
    D.pull_centralizer hL1
  have h2 : D.pull (centralizer ({permC 1782 w0T} : Set (Equiv.Perm (Fin 1782)))) =
      centralizer ({t0} : Set G) ⊓ centralizer ({z} : Set G) :=
    D.pull_centralizer_singleton D.w0_mem
  have h3 : D.pull (centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓
      centralizer ({permC 1782 w0T} : Set (Equiv.Perm (Fin 1782)))) =
      centralizer (Lg : Set G) ⊓ centralizer ({t0} : Set G) := by
    rw [D.pull_inf, h1, h2]
    ext g
    constructor
    · rintro ⟨⟨hgL, -⟩, hgt, -⟩
      exact ⟨hgL, hgt⟩
    · rintro ⟨hgL, hgt⟩
      exact ⟨⟨hgL, hCL_le hgL⟩, hgt, hCL_le hgL⟩
  have h4 : D.pull (centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓ V0) =
      D.pull (centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓
        centralizer ({permC 1782 w0T} : Set (Equiv.Perm (Fin 1782)))) := by
    rw [show V0 = tabSubgroup v0Tabs from rfl, D.tabSubgroup_v0Tabs, ← inf_assoc]
    ext g
    rw [D.mem_pull, D.mem_pull]
    constructor
    · rintro ⟨hg, hH, -⟩
      exact ⟨hg, hH⟩
    · rintro ⟨hg, hH⟩
      exact ⟨hg, hH, (D.σ ⟨g, hg⟩).2⟩
  have hEq : D.pull (centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓ V0) =
      centralizer (Lg : Set G) ⊓ centralizer ({t0} : Set G) := by
    rw [h4, h3]
  have hcardV0 : Nat.card ↥(centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓ V0) = 64 := by
    unfold F6Prop at hF6
    exact hF6.1
  calc Nat.card ↥(centralizer (Lg : Set G) ⊓ centralizer ({t0} : Set G))
      = Nat.card ↥(D.pull (centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓ V0)) := by
        rw [hEq]
    _ = Nat.card ↥(centralizer (L1 : Set (Equiv.Perm (Fin 1782))) ⊓ V0) :=
        D.card_pull (inf_le_right.trans hV0)
    _ = 64 := hcardV0

theorem card_normalizer_L_inf_centralizer_t0 [Finite G]
    (hNLM : normalizer (D.pull (decSubgroup l1Decs) : Set G) =
      normalizer (D.pull (decSubgroup m1Decs) : Set G))
    (hcardN : Nat.card ↥(normalizer (D.pull (decSubgroup l1Decs) : Set G)) = 1105920)
    (ht0M : D.elt (permC 1782 w0T) D.w0_mem ∈ D.pull (decSubgroup m1Decs))
    (ht0L : D.elt (permC 1782 w0T) D.w0_mem ∉ D.pull (decSubgroup l1Decs))
    (hconj : ∀ x ∈ D.pull (decSubgroup m1Decs), x * x = 1 → x ≠ 1 →
      x ∉ D.pull (decSubgroup l1Decs) →
      ∃ n ∈ normalizer (D.pull (decSubgroup l1Decs) : Set G) ⊓ centralizer ({z} : Set G),
        x = n * D.elt (permC 1782 w0T) D.w0_mem * n⁻¹)
    (hcard288 : Nat.card {x : D.pull (decSubgroup m1Decs) //
      x * x = 1 ∧ x ≠ 1 ∧ (x : G) ∉ D.pull (decSubgroup l1Decs)} = 288) :
    Nat.card ↥(normalizer (D.pull (decSubgroup l1Decs) : Set G) ⊓
      centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G)) = 3840 := by
  classical
  let Lg : Subgroup G := D.pull (decSubgroup l1Decs)
  let Mg : Subgroup G := D.pull (decSubgroup m1Decs)
  let t0 : G := D.elt (permC 1782 w0T) D.w0_mem
  let N : Subgroup G := normalizer (Lg : Set G)
  let S : Subgroup G := N ⊓ centralizer ({t0} : Set G)
  let Inv : Type := {x : Mg // x * x = 1 ∧ x ≠ 1 ∧ (x : G) ∉ Lg}
  have ht0M' : t0 ∈ Mg := ht0M
  have ht0L' : t0 ∉ Lg := ht0L
  have ht0_sq : t0 * t0 = 1 := D.t0_mul_self
  have ht0_ne : t0 ≠ 1 := D.t0_ne_one
  let φ : ↥N → Inv := fun n =>
    ⟨⟨(n : G) * t0 * (n : G)⁻¹, by
        have hnM : (n : G) ∈ normalizer (Mg : Set G) := by
          rw [← hNLM]
          exact n.2
        exact ((Subgroup.mem_normalizer_iff.mp hnM) t0).mp ht0M'⟩,
      by
        refine ⟨?_, ?_, ?_⟩
        · apply Subtype.ext
          calc ((n : G) * t0 * (n : G)⁻¹) * ((n : G) * t0 * (n : G)⁻¹)
              = (n : G) * (t0 * t0) * (n : G)⁻¹ := by group
            _ = 1 := by rw [ht0_sq]; group
        · intro h
          have h' : (n : G) * t0 * (n : G)⁻¹ = 1 := congrArg Subtype.val h
          exact ht0_ne (by
            calc t0 = (n : G)⁻¹ * ((n : G) * t0 * (n : G)⁻¹) * (n : G) := by group
              _ = 1 := by rw [h']; group)
        · intro hmem
          exact ht0L' ((Subgroup.mem_normalizer_iff.mp n.2 t0).mpr hmem)⟩
  have φ_surj : Function.Surjective φ := by
    rintro ⟨⟨x, hxM⟩, hx2, hx1, hxL⟩
    obtain ⟨n, hn, hxn⟩ := hconj x hxM (by simpa using hx2) (by
      intro h
      exact hx1 (Subtype.ext h)) (by simpa using hxL)
    refine ⟨⟨n, hn.1⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hxn.symm
  let ψ : Inv → ↥N := fun x => Classical.choose (φ_surj x)
  have ψ_spec : ∀ x : Inv, φ (ψ x) = x := fun x => Classical.choose_spec (φ_surj x)
  have hfib : ∀ a b : ↥N, φ a = φ b ↔
      (b : G)⁻¹ * (a : G) ∈ centralizer ({t0} : Set G) := by
    intro a b
    constructor
    · intro h
      have h' : (a : G) * t0 * (a : G)⁻¹ = (b : G) * t0 * (b : G)⁻¹ := by
        have h2 := congrArg (fun x : Inv => ((x.1 : Mg) : G)) h
        simpa [φ] using h2
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hconj' : ((b : G)⁻¹ * (a : G)) * t0 * ((b : G)⁻¹ * (a : G))⁻¹ = t0 := by
        calc ((b : G)⁻¹ * (a : G)) * t0 * ((b : G)⁻¹ * (a : G))⁻¹
            = (b : G)⁻¹ * ((a : G) * t0 * (a : G)⁻¹) * (b : G) := by group
          _ = (b : G)⁻¹ * ((b : G) * t0 * (b : G)⁻¹) * (b : G) := by rw [h']
          _ = t0 := by group
      calc (b : G)⁻¹ * (a : G) * t0
          = ((b : G)⁻¹ * (a : G)) * t0 * ((b : G)⁻¹ * (a : G))⁻¹ *
              ((b : G)⁻¹ * (a : G)) := by group
        _ = t0 * ((b : G)⁻¹ * (a : G)) := by rw [hconj']
    · intro hk
      rw [Subgroup.mem_centralizer_singleton_iff] at hk
      have hk' : ((b : G)⁻¹ * (a : G)) * t0 * ((b : G)⁻¹ * (a : G))⁻¹ = t0 := by
        calc ((b : G)⁻¹ * (a : G)) * t0 * ((b : G)⁻¹ * (a : G))⁻¹
            = (t0 * ((b : G)⁻¹ * (a : G))) * ((b : G)⁻¹ * (a : G))⁻¹ := by rw [hk]
          _ = t0 := by group
      apply Subtype.ext
      apply Subtype.ext
      calc (a : G) * t0 * (a : G)⁻¹
          = (b : G) * (((b : G)⁻¹ * (a : G)) * t0 *
              ((b : G)⁻¹ * (a : G))⁻¹) * (b : G)⁻¹ := by group
        _ = (b : G) * t0 * (b : G)⁻¹ := by rw [hk']
  have memS : ∀ n : ↥N, (((ψ (φ n))⁻¹ * n : ↥N) : G) ∈ S := by
    intro n
    have hc : (n : G)⁻¹ * (ψ (φ n) : G) ∈ centralizer ({t0} : Set G) :=
      (hfib (ψ (φ n)) n).mp (by rw [ψ_spec])
    have hinv : ((n : G)⁻¹ * (ψ (φ n) : G))⁻¹ ∈ centralizer ({t0} : Set G) :=
      Subgroup.inv_mem _ hc
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem (H := N) (Subgroup.inv_mem (H := N) (ψ (φ n)).2) n.2
    · simpa [mul_assoc] using hinv
  let e : ↥N ≃ Inv × ↥S :=
    { toFun := fun n => (φ n, ⟨(((ψ (φ n))⁻¹ * n : ↥N) : G), memS n⟩)
      invFun := fun p => ψ p.1 * ⟨(p.2 : G), p.2.2.1⟩
      left_inv := by
        intro n
        apply Subtype.ext
        change (ψ (φ n) : G) * (((ψ (φ n) : ↥N)⁻¹ * n : ↥N) : G) = (n : G)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      right_inv := by
        rintro ⟨x, s⟩
        let sN : ↥N := ⟨(s : G), s.2.1⟩
        have hφ : φ (ψ x * sN) = x := by
          have h := (hfib (ψ x * sN) (ψ x)).mpr ?_
          · rwa [ψ_spec x] at h
          · have h1 : ((ψ x : ↥N) : G)⁻¹ * ((ψ x * sN : ↥N) : G) = (s : G) := by
              simp [sN, mul_assoc]
            rw [h1]
            exact s.2.2
        apply Prod.ext
        · exact hφ
        · apply Subtype.ext
          have hψ : ψ (φ (ψ x * sN)) = ψ x := by rw [hφ]
          show (((ψ (φ (ψ x * sN)) : ↥N)⁻¹ * (ψ x * sN) : ↥N) : G) = (s : G)
          rw [hψ]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          change (ψ x : G)⁻¹ * ((ψ x : G) * (s : G)) = (s : G)
          group }
  have hcardInv : Nat.card Inv = 288 := hcard288
  have hcardN' : Nat.card ↥N = 1105920 := hcardN
  have hmain : Nat.card ↥N = Nat.card Inv * Nat.card ↥S := by
    calc Nat.card ↥N = Nat.card (Inv × ↥S) := Nat.card_congr e
      _ = Nat.card Inv * Nat.card ↥S := Nat.card_prod (α := Inv) (β := ↥S)
  rw [hcardInv, hcardN'] at hmain
  have hS : Nat.card ↥S = 3840 := by omega
  exact hS

theorem tbar16_le_map [Finite G] (hF1 : F1Prop) (hF6b : F6bProp) :
    Tbar16 ≤ (((normalizer (D.pull (decSubgroup l1Decs) : Set G) ⊓
      centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G)).subgroupOf
      (normalizer (D.pull (decSubgroup l1Decs) : Set G))).map (bitAction (D.lEquiv hF1))) := by
  classical
  let Lg : Subgroup G := D.pull (decSubgroup l1Decs)
  let L1 : Subgroup (Equiv.Perm (Fin 1782)) := decSubgroup l1Decs
  let t0 : G := D.elt (permC 1782 w0T) D.w0_mem
  let N : Subgroup G := normalizer (Lg : Set G)
  let ND : Subgroup G := N ⊓ centralizer ({t0} : Set G)
  let e := D.lEquiv hF1
  have hL1 : L1 ≤ invE 1 := D.l1Decs_le_invE
  have hV0 : tabSubgroup v0Tabs ≤ invE 1 := by
    rw [D.tabSubgroup_v0Tabs]
    exact inf_le_right
  have gen_mem : ∀ j < 2, tabPerm16 tbarTabs[j]! ∈
      (ND.subgroupOf N).map (bitAction e) := by
    intro j hj
    obtain ⟨y, hyV0, hyconj⟩ := hF6b j hj
    have hyE : y ∈ invE 1 := hV0 hyV0
    have hyW : y * permC 1782 w0T = permC 1782 w0T * y := by
      have hyC : y ∈ centralizer ({permC 1782 w0T} : Set (Equiv.Perm (Fin 1782))) := by
        have h := hyV0
        rw [D.tabSubgroup_v0Tabs] at h
        exact (Subgroup.mem_inf.mp h).1
      exact Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hyNorm : y ∈ normalizer (L1 : Set (Equiv.Perm (Fin 1782))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hmap_le : L1.map (MulAut.conj y) ≤ L1 := by
        rintro _ ⟨x, hxL1, rfl⟩
        obtain ⟨i, hi⟩ : ∃ i : Fin 16,
            ((l1Equiv hF1 i : ↥(decSubgroup l1Decs)) : Equiv.Perm (Fin 1782)) = x :=
          ⟨(l1Equiv hF1).symm ⟨x, hxL1⟩, by simp⟩
        rw [← hi]
        change y * ((l1Equiv hF1 i : ↥(decSubgroup l1Decs)) :
          Equiv.Perm (Fin 1782)) * y⁻¹ ∈ L1
        rw [coe_l1Equiv, hyconj i]
        exact l1Elt_mem _
      apply Subgroup.eq_of_le_of_card_ge hmap_le
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    have hgN : D.elt y hyE ∈ N := by
      have h := (D.elt_mem_pull_iff hyE).mpr hyNorm
      rw [D.pull_normalizer hL1] at h
      exact h.1
    have hgC : D.elt y hyE ∈ centralizer ({t0} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc D.elt y hyE * t0
          = D.elt (y * permC 1782 w0T) (mul_mem hyE D.w0_mem) :=
            (D.elt_mul y (permC 1782 w0T) hyE D.w0_mem).symm
        _ = D.elt (permC 1782 w0T * y) (mul_mem D.w0_mem hyE) :=
            D.elt_eq_of_eq _ _ hyW
        _ = t0 * D.elt y hyE := D.elt_mul (permC 1782 w0T) y D.w0_mem hyE
    have hgND : D.elt y hyE ∈ ND := ⟨hgN, hgC⟩
    have hbit : bitAction e ⟨D.elt y hyE, hgN⟩ = tabPerm16 tbarTabs[j]! := by
      apply Equiv.ext
      intro i
      apply e.injective
      apply Subtype.ext
      rw [coe_bitAction_apply]
      have hei : ((e i : ↥Lg) : G) =
          D.elt (l1Elt i) (hL1 (l1Elt_mem i)) := D.coe_lEquiv hF1 i
      have hek : ((e (tabPerm16 tbarTabs[j]! i) : ↥Lg) : G) =
          D.elt (l1Elt (tabPerm16 tbarTabs[j]! i))
            (hL1 (l1Elt_mem (tabPerm16 tbarTabs[j]! i))) := D.coe_lEquiv hF1 _
      rw [hei, hek]
      have hLHS : D.elt y hyE * D.elt (l1Elt i) (hL1 (l1Elt_mem i)) *
          (D.elt y hyE)⁻¹ =
          D.elt ((y * l1Elt i) * y⁻¹)
            (mul_mem (mul_mem hyE (hL1 (l1Elt_mem i))) (inv_mem hyE)) := by
        rw [← D.elt_mul y (l1Elt i) hyE (hL1 (l1Elt_mem i))]
        rw [← D.elt_inv y hyE]
        rw [← D.elt_mul (y * l1Elt i) y⁻¹
          (mul_mem hyE (hL1 (l1Elt_mem i))) (inv_mem hyE)]
      rw [hLHS]
      exact D.elt_eq_of_eq _ _ (hyconj i)
    rw [Subgroup.mem_map]
    refine ⟨⟨D.elt y hyE, hgN⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hgND
    · exact hbit
  rw [Tbar16, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact gen_mem 0 (by norm_num)
  · exact gen_mem 1 (by norm_num)

theorem exists_map_eq_X16 [Finite G] (hF1 : F1Prop) (hF6 : F6Prop) (hF6b : F6bProp) (hF9 : F9Prop)
    (hF11 : F11Prop) (hzL : z ∈ D.pull (decSubgroup l1Decs))
    (hNLM : normalizer (D.pull (decSubgroup l1Decs) : Set G) =
      normalizer (D.pull (decSubgroup m1Decs) : Set G))
    (hcardN : Nat.card ↥(normalizer (D.pull (decSubgroup l1Decs) : Set G)) = 1105920)
    (ht0M : D.elt (permC 1782 w0T) D.w0_mem ∈ D.pull (decSubgroup m1Decs))
    (ht0L : D.elt (permC 1782 w0T) D.w0_mem ∉ D.pull (decSubgroup l1Decs))
    (hconj : ∀ x ∈ D.pull (decSubgroup m1Decs), x * x = 1 → x ≠ 1 →
      x ∉ D.pull (decSubgroup l1Decs) →
      ∃ n ∈ normalizer (D.pull (decSubgroup l1Decs) : Set G) ⊓ centralizer ({z} : Set G),
        x = n * D.elt (permC 1782 w0T) D.w0_mem * n⁻¹)
    (hcard288 : Nat.card {x : D.pull (decSubgroup m1Decs) //
      x * x = 1 ∧ x ≠ 1 ∧ (x : G) ∉ D.pull (decSubgroup l1Decs)} = 288)
    {f : G} (hfN : f ∈ normalizer (D.pull (decSubgroup l1Decs) : Set G))
    (hf5 : orderOf f = 5)
    (hffix : ∀ l ∈ D.pull (decSubgroup l1Decs), f * l = l * f → l = 1)
    (hft : f * D.elt (permC 1782 w0T) D.w0_mem =
      D.elt (permC 1782 w0T) D.w0_mem * f) :
    ∃ i < 4, (((normalizer (D.pull (decSubgroup l1Decs) : Set G) ⊓
      centralizer ({D.elt (permC 1782 w0T) D.w0_mem} : Set G)).subgroupOf
      (normalizer (D.pull (decSubgroup l1Decs) : Set G))).map
      (bitAction (D.lEquiv hF1))) = X16 i := by
  classical
  let Lg : Subgroup G := D.pull (decSubgroup l1Decs)
  let t0 : G := D.elt (permC 1782 w0T) D.w0_mem
  let N : Subgroup G := normalizer (Lg : Set G)
  let ND : Subgroup G := N ⊓ centralizer ({t0} : Set G)
  let CD : Subgroup G := centralizer (Lg : Set G) ⊓ centralizer ({t0} : Set G)
  let e := D.lEquiv hF1
  let X : Subgroup (Equiv.Perm (Fin 16)) := (ND.subgroupOf N).map (bitAction e)
  have hcardND : Nat.card ↥ND = 3840 :=
    card_normalizer_L_inf_centralizer_t0 D hNLM hcardN ht0M ht0L hconj hcard288
  have hcardCD : Nat.card ↥CD = 64 :=
    card_centralizer_L_inf_centralizer_t0 D hF6 hzL
  have hCD_eq : ND ⊓ centralizer (Lg : Set G) = CD := by
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨-, hgt⟩, hgL⟩
      exact ⟨hgL, hgt⟩
    · rintro ⟨hgL, hgt⟩
      exact ⟨⟨Subgroup.centralizer_le_normalizer (Lg : Set G) hgL, hgt⟩, hgL⟩
  have hcardX : Nat.card ↥X = 60 := by
    have hmul := card_map_bitAction_mul (L := Lg) e (H := ND) inf_le_left
    have hmul' : Nat.card ↥X * 64 = 3840 := by
      simpa [X, hCD_eq, hcardND, hcardCD] using hmul
    omega
  have hT : Tbar16 ≤ X := tbar16_le_map D hF1 hF6b
  have hfND : f ∈ ND :=
    ⟨hfN, Subgroup.mem_centralizer_singleton_iff.mpr hft⟩
  let g : Equiv.Perm (Fin 16) := bitAction e ⟨f, hfN⟩
  have hgX : g ∈ X := by
    change g ∈ (ND.subgroupOf N).map (bitAction e)
    rw [Subgroup.mem_map]
    exact ⟨⟨f, hfN⟩, Subgroup.mem_subgroupOf.mpr hfND, rfl⟩
  have hgadd : ∀ a b, g (xor16 a b) = xor16 (g a) (g b) := by
    intro a b
    exact bitAction_xor e (fun i j => D.lEquiv_xor hF1 i j) ⟨f, hfN⟩ a b
  have hfg : f ^ 5 = 1 := by
    rw [← hf5]
    exact pow_orderOf_eq_one f
  have hg5pow : g ^ 5 = 1 := by
    change bitAction e ⟨f, hfN⟩ ^ 5 = 1
    rw [← map_pow]
    have h : (⟨f, hfN⟩ : ↥N) ^ 5 = 1 := Subtype.ext hfg
    rw [h, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    have hfC : f ∈ centralizer (Lg : Set G) :=
      (bitAction_eq_one_iff e ⟨f, hfN⟩).mp h
    have hLbot : Lg = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro l hl
      exact hffix l hl (Subgroup.mem_centralizer_iff.mp hfC l hl).symm
    have hcardL : Nat.card ↥Lg = 16 := by
      rw [D.card_pull D.l1Decs_le_invE]
      unfold F1Prop at hF1
      exact hF1.2.2.2.2.2.1
    rw [hLbot, Subgroup.card_bot] at hcardL
    norm_num at hcardL
  have hg5 : orderOf g = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime hg5pow hg1
  obtain ⟨i, hi, hXeq⟩ := exists_eq_X16 hF9 hF11 hcardX hT hgX hgadd hg5
  exact ⟨i, hi, hXeq⟩

end CFSG.Sporadic.SuzRecog.SuzL34.LocalData

end
