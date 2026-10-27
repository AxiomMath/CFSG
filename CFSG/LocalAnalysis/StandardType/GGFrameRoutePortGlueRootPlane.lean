module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueRoot
public import CFSG.LocalAnalysis.StandardType.GGFrameE78Root
public import CFSG.LocalAnalysis.StandardType.GGFrameEndModel
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly

variable {G : Type} [Group G]

theorem closure_pair_mul_pow (x z : G) (k : ℕ) :
    Subgroup.closure {x, z * x ^ k} = Subgroup.closure {x, z} := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]
      exact Subgroup.subset_closure (by simp)
    · rw [h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) k)
  · rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]
      exact Subgroup.subset_closure (by simp)
    · rw [h]
      have hz : z = (z * x ^ k) * (x ^ k)⁻¹ := by group
      rw [hz]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) k))

theorem P5Out.of_closure_eq [Finite G] {B Bs : Subgroup G} {x z z' : G} {L D₁ J₁ : Subgroup G}
    (h : P5Out B Bs x z L D₁ J₁)
    (hz : Subgroup.closure {x, z'} = Subgroup.closure {x, z}) :
    P5Out B Bs x z' L D₁ J₁ :=
  { h with plane := h.plane.trans hz.symm }

private lemma gluePlaneAux_swap_apply_eq {m : ℕ} {v : Fin m → ZMod 3} {a c : Fin m}
    (h : v a = v c) (i : Fin m) : v (Equiv.swap a c i) = v i := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1]
    exact h.symm
  · rw [h2]
    exact h
  · rfl

theorem isReflection_ggConjAut_of_swap [Finite G] {Bs : Subgroup G} {x : G}
    (hBs : IsElemAbelian 3 Bs) (hxBs : x ∈ Bs) {m : ℕ} {u : G → Fin m → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c)
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x)
    {a c : Fin m} (hsep : ∃ b ∈ Bs, u b a ≠ u b c)
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) (hg2 : g ^ 2 = 1) (hgx : g * x * g⁻¹ = x)
    (hgu : ∀ b ∈ Bs, ∃ k : ZMod 3, ∀ i, u (g * b * g⁻¹) i = u b (Equiv.swap a c i) + k) :
    GGIsReflection 3 (ggConjAut Bs hgN) ∧
      ∀ b : ↥Bs, ggConjAut Bs hgN b = b ↔ u b a = u b c := by
  classical
  let d : Additive ↥Bs →+ ZMod 3 :=
    AddMonoidHom.mk' (fun b => u ((Additive.toMul b : ↥Bs) : G) a -
        u ((Additive.toMul b : ↥Bs) : G) c) (by
      intro b b'
      obtain ⟨k, hk⟩ := hmul ((Additive.toMul b : ↥Bs)) (Additive.toMul b).2
        ((Additive.toMul b' : ↥Bs)) (Additive.toMul b').2
      show u (((Additive.toMul b : ↥Bs) : G) * ((Additive.toMul b' : ↥Bs) : G)) a -
          u (((Additive.toMul b : ↥Bs) : G) * ((Additive.toMul b' : ↥Bs) : G)) c =
        (u ((Additive.toMul b : ↥Bs) : G) a - u ((Additive.toMul b : ↥Bs) : G) c) +
        (u ((Additive.toMul b' : ↥Bs) : G) a - u ((Additive.toMul b' : ↥Bs) : G) c)
      rw [hk a, hk c]
      ring)
  have hd : ∀ b : ↥Bs, d (Additive.ofMul b) = u (b : G) a - u (b : G) c := fun _ => rfl
  have hφ2 : ggConjAut Bs hgN ^ 2 = 1 := by
    ext b
    rw [ggConjAut_pow_apply Bs hgN 2 b, hg2]
    simp
  have hfix_forward : ∀ b : ↥Bs, ggConjAut Bs hgN b = b → d (Additive.ofMul b) = 0 := by
    intro b hb
    obtain ⟨k, hk⟩ := hgu b b.2
    have hb_eq : (b : G) = g * (b : G) * g⁻¹ := by
      rw [← ggConjAut_apply Bs hgN b, hb]
    have h1 : u (b : G) a = u (b : G) c + k := by
      calc u (b : G) a = u (g * (b : G) * g⁻¹) a := congrArg (fun t => u t a) hb_eq
        _ = u (b : G) (Equiv.swap a c a) + k := hk a
        _ = u (b : G) c + k := by simp
    have h2 : u (b : G) c = u (b : G) a + k := by
      calc u (b : G) c = u (g * (b : G) * g⁻¹) c := congrArg (fun t => u t c) hb_eq
        _ = u (b : G) (Equiv.swap a c c) + k := hk c
        _ = u (b : G) a + k := by simp
    have hkk : k + k = 0 := by
      have hsub : u (b : G) a = (u (b : G) a + k) + k := by
        rw [h2] at h1
        exact h1
      apply add_left_cancel (a := u (b : G) a)
      rw [add_zero]
      calc u (b : G) a + (k + k) = (u (b : G) a + k) + k := by abel
        _ = u (b : G) a := hsub.symm
    have hk0 : k = 0 := by
      have h : ∀ k : ZMod 3, k + k = 0 → k = 0 := by decide
      exact h k hkk
    rw [hd b]
    rw [hk0, add_zero] at h1
    rw [h1, sub_self]
  have hfix_back : ∀ b : ↥Bs, d (Additive.ofMul b) = 0 → ggConjAut Bs hgN b = b := by
    intro b hd0
    have hub : u (b : G) a = u (b : G) c := by
      rw [hd b] at hd0
      exact sub_eq_zero.mp hd0
    set bi : G := (b : G)⁻¹ with hbi_def
    have hbi : bi ∈ Bs := by
      rw [hbi_def]
      exact Subgroup.inv_mem _ b.2
    set b' : G := g * (b : G) * g⁻¹ with hb'_def
    have hb' : b' ∈ Bs := by
      rw [hb'_def]
      exact (Subgroup.mem_normalizer_iff.mp hgN (b : G)).mp b.2
    obtain ⟨c3, hc3⟩ := (hconst (1 : G) Bs.one_mem).mpr (Subgroup.one_mem _)
    obtain ⟨c2, hc2⟩ := hmul (b : G) b.2 bi hbi
    have hc2' : ∀ i, u (1 : G) i = u (b : G) i + u bi i + c2 := by
      intro i
      have h := hc2 i
      rwa [show (b : G) * bi = 1 by simp [hbi_def]] at h
    obtain ⟨k, hk⟩ := hgu b b.2
    obtain ⟨c1, hc1⟩ := hmul b' hb' bi hbi
    have hswap : ∀ i, u (b : G) (Equiv.swap a c i) = u (b : G) i :=
      fun i => gluePlaneAux_swap_apply_eq hub i
    have hwconst : ∃ c, ∀ i, u (b' * bi) i = c := by
      refine ⟨k + c3 - c2 + c1, fun i => ?_⟩
      have hbi_i : u bi i = c3 - c2 - u (b : G) i := by
        have h := hc2' i
        have h3 := hc3 i
        rw [h3] at h
        linear_combination -h
      rw [hc1 i, hb'_def, hk i, hswap i, hbi_i]
      ring
    have hw : b' * bi ∈ Subgroup.zpowers x :=
      (hconst (b' * bi) (Subgroup.mul_mem _ hb' hbi)).mp hwconst
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hb'eq : b' = x ^ n * (b : G) := by
      have h := congrArg (fun t => t * (b : G)) hn
      rw [hbi_def] at h
      simpa [mul_assoc] using h.symm
    have hφb : ggConjAut Bs hgN ⟨b, b.2⟩ = ⟨b', hb'⟩ := by
      apply Subtype.ext
      rw [ggConjAut_apply, ← hb'_def]
    have hφb' : ggConjAut Bs hgN ⟨b', hb'⟩ = ⟨b, b.2⟩ := by
      have h2 := congrArg (fun ψ : MulAut ↥Bs => ψ ⟨b, b.2⟩) hφ2
      simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at h2
      rwa [hφb] at h2
    have hconj : MulAut.conj g x = x := by
      rw [MulAut.conj_apply, hgx]
    have hgxpow : g * x ^ n * g⁻¹ = x ^ n := by
      have h := map_zpow (MulAut.conj g) x n
      rw [hconj] at h
      simpa [MulAut.conj_apply] using h
    have hb_eq2 : (b : G) = x ^ n * b' := by
      have h1 := ggConjAut_apply Bs hgN ⟨b', hb'⟩
      rw [hφb'] at h1
      calc (b : G) = g * b' * g⁻¹ := h1
        _ = g * (x ^ n * (b : G)) * g⁻¹ := by rw [hb'eq]
        _ = (g * x ^ n * g⁻¹) * (g * (b : G) * g⁻¹) := by group
        _ = x ^ n * b' := by rw [hgxpow, hb'_def]
    have h2n : x ^ (2 * n) = 1 := by
      have h : (b : G) = x ^ (2 * n) * (b : G) := by
        calc (b : G) = x ^ n * b' := hb_eq2
          _ = x ^ n * (x ^ n * (b : G)) := by rw [hb'eq]
          _ = x ^ (n + n) * (b : G) := by rw [← mul_assoc, ← zpow_add]
          _ = x ^ (2 * n) * (b : G) := by rw [show n + n = 2 * n by ring]
      exact mul_right_cancel (by rw [one_mul]; exact h.symm)
    have hx3 : x ^ (3 : ℤ) = 1 := by
      simpa using hBs.2 x hxBs
    have hxn : x ^ n = 1 := by
      have h1 : x ^ (2 * (2 * n)) = (x ^ (2 * n)) ^ 2 := by
        rw [show 2 * (2 * n) = (2 * n) * 2 by ring, zpow_mul]
        simp
      have h3 : x ^ (3 * n) = 1 := by
        rw [zpow_mul, hx3, one_zpow]
      calc x ^ n = x ^ (2 * (2 * n) + -(3 * n)) := by
            congr 1
            ring
        _ = x ^ (2 * (2 * n)) * x ^ (-(3 * n)) := zpow_add ..
        _ = (x ^ (2 * n)) ^ 2 * (x ^ (3 * n))⁻¹ := by rw [h1, zpow_neg]
        _ = 1 := by rw [h2n, one_pow, h3, inv_one, mul_one]
    have hb'b : b' = (b : G) := by
      rw [hb'eq, hxn, one_mul]
    have hφbb : ggConjAut Bs hgN b = b := by
      apply Subtype.ext
      rw [ggConjAut_apply]
      change b' = (b : G)
      exact hb'b
    exact hφbb
  have hchar : ∀ b : ↥Bs, ggConjAut Bs hgN b = b ↔ u (b : G) a = u (b : G) c := by
    intro b
    constructor
    · intro hb
      have hd0 := hfix_forward b hb
      rw [hd b] at hd0
      exact sub_eq_zero.mp hd0
    · intro hub
      apply hfix_back b
      rw [hd b, hub, sub_self]
  have hcard :
      Nat.card {b : ↥Bs // ggConjAut Bs hgN b = b} = Nat.card ↥d.ker := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun b => ⟨Additive.ofMul b.1, ?_⟩
        invFun := fun z => ⟨Additive.toMul z.1, ?_⟩
        left_inv := fun b => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
    · rw [AddMonoidHom.mem_ker]
      exact hfix_forward b.1 b.2
    · apply hfix_back
      change d z.1 = 0
      exact AddMonoidHom.mem_ker.mp z.2
  have hker : Nat.card ↥d.ker * 3 = Nat.card ↥Bs := by
    obtain ⟨b0, hb0, hb0ne⟩ := hsep
    have hb0' : d (Additive.ofMul ⟨b0, hb0⟩) ≠ 0 := by
      rw [hd]
      exact sub_ne_zero.mpr hb0ne
    have htop : AddSubgroup.zmultiples (d (Additive.ofMul ⟨b0, hb0⟩)) = ⊤ :=
      zmultiples_eq_top_of_prime_card (Nat.card_zmod 3) hb0'
    have hle : AddSubgroup.zmultiples (d (Additive.ofMul ⟨b0, hb0⟩)) ≤ d.range :=
      AddSubgroup.zmultiples_le_of_mem (AddMonoidHom.mem_range.mpr ⟨_, rfl⟩)
    have hrange : d.range = ⊤ := top_le_iff.mp (htop ▸ hle)
    have h := AddSubgroup.card_ker_mul_card_range d
    rw [hrange, AddSubgroup.card_top, Nat.card_zmod] at h
    rw [Nat.card_congr Additive.toMul] at h
    exact h
  refine ⟨⟨hφ2, ?_⟩, ?_⟩
  · rw [hcard, hker]
  · intro b
    simpa using hchar b

private lemma gluePlaneAux_single_sub_single_swap {m : ℕ} {j j' : Fin m} (h : j ≠ j')
    (i : Fin m) :
    (Pi.single j 1 - Pi.single j' 1 : Fin m → ZMod 3) (Equiv.swap j j' i)
      = -(Pi.single j 1 - Pi.single j' 1 : Fin m → ZMod 3) i := by
  by_cases hij : i = j
  · rw [hij]
    have hswap : Equiv.swap j j' j = j' := by simp
    rw [hswap]
    simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) h,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm h)]
  · by_cases hij' : i = j'
    · rw [hij']
      have hswap : Equiv.swap j j' j' = j := by simp
      rw [hswap]
      simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) h,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm h)]
    · have hswap : Equiv.swap j j' i = i := Equiv.swap_apply_of_ne_of_ne hij hij'
      rw [hswap]
      simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij']

theorem exists_inv_of_single_sub_single [Finite G] {Bs L : Subgroup G} {x z : G}
    (hBs : IsElemAbelian 3 Bs) (hxBs : x ∈ Bs) (hzBs : z ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) {m : ℕ} {u : G → Fin m → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c)
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x)
    {j j' : Fin m} (hjj' : j ≠ j')
    (hz : ∃ c : ZMod 3, ∀ i, u z i = (Pi.single j 1 - Pi.single j' 1 : Fin m → ZMod 3) i + c)
    (hswap : ∃ g ∈ L, g ∈ Subgroup.normalizer (Bs : Set G) ∧ g ^ 2 = 1 ∧
      ∀ b ∈ Bs, ∃ k : ZMod 3, ∀ i, u (g * b * g⁻¹) i = u b (Equiv.swap j j' i) + k) :
    ∃ φ ∈ frameReflSet (ggAutomizer L Bs),
      ((φ ⟨z, hzBs⟩ : ↥Bs) : G) * z ∈ Subgroup.zpowers x := by
  classical
  obtain ⟨g, hgL, hgN, hg2, hgu⟩ := hswap
  obtain ⟨c0, hz0⟩ := hz
  have hgx : g * x * g⁻¹ = x := by
    have hcomm : x * g = g * x :=
      (Subgroup.mem_centralizer_iff.mp (hLx hgL)) x (Set.mem_singleton x)
    rw [← hcomm]
    group
  have hzswap : ∀ i, u z (Equiv.swap j j' i) = -u z i + 2 * c0 := by
    intro i
    have h1 := hz0 (Equiv.swap j j' i)
    have h2 := hz0 i
    have he := gluePlaneAux_single_sub_single_swap hjj' i
    rw [h1, h2, he]
    ring
  have hsep : ∃ b ∈ Bs, u b j ≠ u b j' := by
    refine ⟨z, hzBs, ?_⟩
    have h1 : u z j = 1 + c0 := by
      simpa [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjj'] using hz0 j
    have h2 : u z j' = -1 + c0 := by
      simpa [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hjj')] using hz0 j'
    intro h
    rw [h] at h1
    rw [h2] at h1
    exact absurd (add_right_cancel h1) (by decide)
  have hφ := isReflection_ggConjAut_of_swap hBs hxBs hmul hconst hsep hgN hg2 hgx hgu
  refine ⟨ggConjAut Bs hgN, ⟨ggConjAut_mem_ggAutomizer hgL hgN, hφ.1⟩, ?_⟩
  have hwBs : (((ggConjAut Bs hgN ⟨z, hzBs⟩ : ↥Bs) : G)) * z ∈ Bs :=
    Subgroup.mul_mem _ (ggConjAut Bs hgN ⟨z, hzBs⟩).2 hzBs
  have hconstw : ∃ c, ∀ i, u ((((ggConjAut Bs hgN ⟨z, hzBs⟩ : ↥Bs) : G)) * z) i = c := by
    obtain ⟨k, hk⟩ := hgu z hzBs
    obtain ⟨c1, hc1⟩ := hmul (((ggConjAut Bs hgN ⟨z, hzBs⟩ : ↥Bs) : G))
      (ggConjAut Bs hgN ⟨z, hzBs⟩).2 z hzBs
    refine ⟨2 * c0 + k + c1, fun i => ?_⟩
    have hφzi : u (((ggConjAut Bs hgN ⟨z, hzBs⟩ : ↥Bs) : G)) i =
        u z (Equiv.swap j j' i) + k := by
      rw [ggConjAut_apply]
      exact hk i
    rw [hc1 i, hφzi, hzswap i]
    ring
  exact (hconst _ hwBs).mp hconstw

theorem thirteen_le_of_single [Finite G] {Bs L : Subgroup G} {x z : G}
    (hBs : IsElemAbelian 3 Bs) (hxBs : x ∈ Bs) (hzBs : z ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) {u : G → Fin 7 → ZMod 3}
    (hmul : ∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c)
    (hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x)
    (hsurj : ∀ v : Fin 7 → ZMod 3, ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c)
    {j : Fin 7} (hz : ∃ c : ZMod 3, ∀ i, u z i = (Pi.single j 1 : Fin 7 → ZMod 3) i + c)
    (hswap : ∀ a c : Fin 7, a ≠ c → ∃ g ∈ L, g ∈ Subgroup.normalizer (Bs : Set G) ∧ g ^ 2 = 1 ∧
      ∀ b ∈ Bs, ∃ k : ZMod 3, ∀ i, u (g * b * g⁻¹) i = u b (Equiv.swap a c i) + k) :
    13 ≤ ({φ | φ ∈ frameReflSet (ggAutomizer L Bs) ∧ φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩} :
      Set (MulAut ↥Bs)).ncard := by
  classical
  let P : Finset (Fin 7 × Fin 7) :=
    Finset.univ.filter fun p => p.1 < p.2 ∧ p.1 ≠ j ∧ p.2 ≠ j
  have hPcard : P.card = 15 := by
    fin_cases j <;> decide
  have hex : ∀ p : {p : Fin 7 × Fin 7 // p ∈ P},
      ∃ φ : MulAut ↥Bs, (φ ∈ frameReflSet (ggAutomizer L Bs) ∧
        φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩) ∧
        ∀ b : ↥Bs, φ b = b ↔ u b p.1.1 = u b p.1.2 := by
    rintro ⟨⟨a, c⟩, hp⟩
    obtain ⟨hlt, haj, hcj⟩ := (Finset.mem_filter.mp hp).2
    have hac : a ≠ c := ne_of_lt hlt
    obtain ⟨g, hgL, hgN, hg2, hgu⟩ := hswap a c hac
    have hgx : g * x * g⁻¹ = x := by
      have hcomm : x * g = g * x :=
        (Subgroup.mem_centralizer_iff.mp (hLx hgL)) x (Set.mem_singleton x)
      rw [← hcomm]
      group
    have hsep : ∃ b ∈ Bs, u b a ≠ u b c := by
      obtain ⟨b, hb, c0, hb0⟩ := hsurj (Pi.single a 1)
      refine ⟨b, hb, ?_⟩
      have h1 : u b a = 1 + c0 := by simpa using hb0 a
      have h2 : u b c = 0 + c0 := by
        simpa [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hac)] using hb0 c
      intro h
      rw [h] at h1
      rw [h2] at h1
      exact zero_ne_one (add_right_cancel h1)
    have hφ := isReflection_ggConjAut_of_swap hBs hxBs hmul hconst hsep hgN hg2 hgx hgu
    have hzfix : u z a = u z c := by
      obtain ⟨c0, hz0⟩ := hz
      have ha : (Pi.single j 1 : Fin 7 → ZMod 3) a = 0 :=
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) haj (1 : ZMod 3)
      have hc : (Pi.single j 1 : Fin 7 → ZMod 3) c = 0 :=
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hcj (1 : ZMod 3)
      rw [hz0 a, hz0 c, ha, hc]
    refine ⟨ggConjAut Bs hgN, ⟨⟨ggConjAut_mem_ggAutomizer hgL hgN, hφ.1⟩, ?_⟩, hφ.2⟩
    exact (hφ.2 ⟨z, hzBs⟩).mpr hzfix
  let F : {p : Fin 7 × Fin 7 // p ∈ P} → MulAut ↥Bs := fun p => (hex p).choose
  have hFspec : ∀ p, (F p ∈ frameReflSet (ggAutomizer L Bs) ∧
      F p ⟨z, hzBs⟩ = ⟨z, hzBs⟩) ∧
      ∀ b : ↥Bs, F p b = b ↔ u b p.1.1 = u b p.1.2 := fun p => (hex p).choose_spec
  have hFinj : Function.Injective F := by
    intro p p' hpp'
    obtain ⟨hlt, haj, hcj⟩ := (Finset.mem_filter.mp p.2).2
    obtain ⟨hlt', haj', hcj'⟩ := (Finset.mem_filter.mp p'.2).2
    have hac : p.1.1 ≠ p.1.2 := ne_of_lt hlt
    have hac' : p'.1.1 ≠ p'.1.2 := ne_of_lt hlt'
    have hv : ∀ v : Fin 7 → ZMod 3, v p.1.1 = v p.1.2 ↔ v p'.1.1 = v p'.1.2 := by
      intro v
      obtain ⟨b, hb, c0, hb0⟩ := hsurj v
      have h1 := (hFspec p).2 ⟨b, hb⟩
      have h2 := (hFspec p').2 ⟨b, hb⟩
      rw [hpp'] at h1
      have hiff : u b p.1.1 = u b p.1.2 ↔ u b p'.1.1 = u b p'.1.2 :=
        h1.symm.trans h2
      rw [hb0 p.1.1, hb0 p.1.2, hb0 p'.1.1, hb0 p'.1.2] at hiff
      simpa only [add_right_cancel_iff] using hiff
    have h1 : ¬ ((Pi.single p.1.1 1 : Fin 7 → ZMod 3) p'.1.1 =
        (Pi.single p.1.1 1 : Fin 7 → ZMod 3) p'.1.2) := by
      have hfalse : ¬ ((Pi.single p.1.1 1 : Fin 7 → ZMod 3) p.1.1 =
          (Pi.single p.1.1 1 : Fin 7 → ZMod 3) p.1.2) := by
        simp [hac]
      exact (hv (Pi.single p.1.1 1)).not.mp hfalse
    have hamem : p.1.1 ∈ ({p'.1.1, p'.1.2} : Finset (Fin 7)) := by
      by_contra hmem
      apply h1
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
      obtain ⟨ha', hc'⟩ := hmem
      rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm ha'),
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hc')]
    have hcmem : p.1.2 ∈ ({p'.1.1, p'.1.2} : Finset (Fin 7)) := by
      have h2 : ¬ ((Pi.single p.1.2 1 : Fin 7 → ZMod 3) p'.1.1 =
          (Pi.single p.1.2 1 : Fin 7 → ZMod 3) p'.1.2) := by
        have hfalse : ¬ ((Pi.single p.1.2 1 : Fin 7 → ZMod 3) p.1.1 =
            (Pi.single p.1.2 1 : Fin 7 → ZMod 3) p.1.2) := by
          simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hac]
        exact (hv (Pi.single p.1.2 1)).not.mp hfalse
      by_contra hmem
      apply h2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
      obtain ⟨ha', hc'⟩ := hmem
      rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm ha'),
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hc')]
    have hsub : ({p.1.1, p.1.2} : Finset (Fin 7)) ⊆ {p'.1.1, p'.1.2} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · rw [h]
        exact hamem
      · rw [h]
        exact hcmem
    have hcard1 : ({p.1.1, p.1.2} : Finset (Fin 7)).card = 2 := Finset.card_pair hac
    have hcard2 : ({p'.1.1, p'.1.2} : Finset (Fin 7)).card = 2 := Finset.card_pair hac'
    have hset : ({p.1.1, p.1.2} : Finset (Fin 7)) = {p'.1.1, p'.1.2} :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hmem1 : p'.1.1 ∈ ({p.1.1, p.1.2} : Finset (Fin 7)) := by
      rw [hset]
      simp
    have haeq : p'.1.1 = p.1.1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1
      rcases hmem1 with h | h
      · exact h
      · exfalso
        have hmem2 : p'.1.2 ∈ ({p.1.1, p.1.2} : Finset (Fin 7)) := by
          rw [hset]
          simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem2
        rcases hmem2 with h2 | h2
        · rw [h, h2] at hlt'
          exact absurd hlt' (not_lt.mpr (le_of_lt hlt))
        · rw [h, h2] at hlt'
          exact absurd hlt' (lt_irrefl _)
    have hceq : p'.1.2 = p.1.2 := by
      have hmem2 : p'.1.2 ∈ ({p.1.1, p.1.2} : Finset (Fin 7)) := by
        rw [hset]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem2
      rcases hmem2 with h2 | h2
      · exfalso
        rw [haeq, h2] at hlt'
        exact absurd hlt' (lt_irrefl _)
      · exact h2
    apply Subtype.ext
    exact Prod.ext haeq.symm hceq.symm
  have hsubT : F '' (Set.univ : Set {p : Fin 7 × Fin 7 // p ∈ P}) ⊆
      ({φ | φ ∈ frameReflSet (ggAutomizer L Bs) ∧ φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩} :
        Set (MulAut ↥Bs)) := by
    rintro φ ⟨p, -, rfl⟩
    exact (hFspec p).1
  have himg : (F '' (Set.univ : Set {p : Fin 7 × Fin 7 // p ∈ P})).ncard = 15 := by
    rw [Set.ncard_image_of_injective _ hFinj, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_coe]
    exact hPcard
  have h15 : 15 ≤ ({φ | φ ∈ frameReflSet (ggAutomizer L Bs) ∧
      φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩} : Set (MulAut ↥Bs)).ncard := by
    rw [← himg]
    exact Set.ncard_le_ncard hsubT
  exact le_trans (by norm_num : 13 ≤ 15) h15

namespace GGFrameModelData

private theorem gluePlaneAux_exists_isRoot_mul_pow {Bs : Subgroup G} {n : ℕ}
    (M : GGFrameModelData Bs n) {x z : G} (hxBs : x ∈ Bs) (hzBs : z ∈ Bs)
    (hzx : z ∉ Subgroup.zpowers x) {v y : FEVec n}
    (hv : v = M.ψ (Additive.ofMul ⟨x, hxBs⟩))
    (hy : y = M.ψ (Additive.ofMul ⟨z, hzBs⟩))
    {c : ZMod 3} {t : FEMat n} (ht : t ∈ feT n)
    (h : t.mulVec (y + c • v) = -(y + c • v)) :
    ∃ k : ℕ, M.IsRoot (z * x ^ k) := by
  have hmem : z * x ^ c.val ∈ Bs := Subgroup.mul_mem _ hzBs (Subgroup.pow_mem _ hxBs _)
  refine ⟨c.val, hmem, ?_, ?_⟩
  · intro h1
    apply hzx
    have hz_eq : z = (x ^ c.val)⁻¹ := by
      calc z = (z * x ^ c.val) * (x ^ c.val)⁻¹ := by group
        _ = 1 * (x ^ c.val)⁻¹ := by rw [h1]
        _ = (x ^ c.val)⁻¹ := one_mul _
    rw [hz_eq]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) c.val)
  · refine ⟨t, ht, ?_⟩
    have hψ : M.ψ (Additive.ofMul ⟨z * x ^ c.val, hmem⟩) = y + c • v := by
      have h1 : Additive.ofMul (⟨z * x ^ c.val, hmem⟩ : ↥Bs) =
          Additive.ofMul (⟨z, hzBs⟩ : ↥Bs) +
            Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ c.val) := by
        rw [← ofMul_mul]
        congr 1
      rw [h1, map_add, ofMul_pow, map_nsmul, ← hv, ← hy]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod 3), ZMod.natCast_zmod_val]
    rw [hψ]
    exact h


variable {Bs : Subgroup G} {n : ℕ}

theorem exists_isRoot_mul_pow_of_inv (M : GGFrameModelData Bs n) {L : Subgroup G}
    (hLA : ggAutomizer L Bs ≤ M.A)
    (hrefl : ∀ φ ∈ M.A, GGIsReflection 3 φ → frameRho M.ψ φ ∈ feT n)
    {x z : G} (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hxBs : x ∈ Bs) (hzBs : z ∈ Bs)
    (hzx : z ∉ Subgroup.zpowers x) {φ : MulAut ↥Bs} (hφ : φ ∈ frameReflSet (ggAutomizer L Bs))
    (hφz : ((φ ⟨z, hzBs⟩ : ↥Bs) : G) * z ∈ Subgroup.zpowers x) :
    ∃ k : ℕ, M.IsRoot (z * x ^ k) := by
  classical
  have hφA : φ ∈ M.A := hLA hφ.1
  have ht : frameRho M.ψ φ ∈ feT n := hrefl φ hφA hφ.2
  have hφx : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ :=
    ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxBs⟩) hLx hφ.1
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hφz
  let c : ZMod 3 := (i : ZMod 3)
  let vx : FEVec n := M.ψ (Additive.ofMul ⟨x, hxBs⟩)
  let vz : FEVec n := M.ψ (Additive.ofMul ⟨z, hzBs⟩)
  have htvx : (frameRho M.ψ φ).mulVec vx = vx := by
    rw [frameRho_mulVec, hφx]
  have hφz_eq : φ ⟨z, hzBs⟩ = ⟨x, hxBs⟩ ^ i * ⟨z, hzBs⟩⁻¹ := by
    apply Subtype.ext
    change ((φ ⟨z, hzBs⟩ : ↥Bs) : G) = x ^ i * z⁻¹
    have h := congrArg (fun t => t * z⁻¹) hi
    simpa [mul_assoc] using h.symm
  have hψφz : M.ψ (Additive.ofMul (φ ⟨z, hzBs⟩)) = -vz + c • vx := by
    rw [hφz_eq, ofMul_mul, map_add, ofMul_zpow, map_zsmul, ofMul_inv, map_neg]
    rw [show i • vx = c • vx by
      rw [← Int.cast_smul_eq_zsmul (R := ZMod 3) i vx]]
    abel
  have htvz : (frameRho M.ψ φ).mulVec vz = -vz + c • vx := by
    rw [frameRho_mulVec]
    exact hψφz
  have hcc : c + c = -c := by
    have h : ∀ d : ZMod 3, d + d = -d := by decide
    exact h c
  have htvw : (frameRho M.ψ φ).mulVec (vz + c • vx) = -(vz + c • vx) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, htvz, htvx]
    calc (-vz + c • vx) + c • vx = -vz + (c • vx + c • vx) := by abel
      _ = -vz + (c + c) • vx := by rw [← add_smul]
      _ = -vz + (-c) • vx := by rw [hcc]
      _ = -vz - c • vx := by
        rw [neg_smul]
        abel
      _ = -(vz + c • vx) := by abel
  exact gluePlaneAux_exists_isRoot_mul_pow M hxBs hzBs hzx rfl rfl ht htvw

theorem exists_isRoot_mul_pow_of_thirteen
    (M : GGFrameModelData Bs 7) {L : Subgroup G} (hLA : ggAutomizer L Bs ≤ M.A)
    (hrefl : ∀ φ ∈ M.A, GGIsReflection 3 φ → frameRho M.ψ φ ∈ feT 7)
    {x z : G} (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hxBs : x ∈ Bs) (hzBs : z ∈ Bs)
    (hzx : z ∉ Subgroup.zpowers x)
    (hv : (feTx 7 (M.ψ (Additive.ofMul ⟨x, hxBs⟩))).ncard = 21 ∨
      (feTx 7 (M.ψ (Additive.ofMul ⟨x, hxBs⟩))).ncard = 36)
    (h13 : 13 ≤ ({φ | φ ∈ frameReflSet (ggAutomizer L Bs) ∧ φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩} :
      Set (MulAut ↥Bs)).ncard) :
    ∃ k : ℕ, M.IsRoot (z * x ^ k) := by
  classical
  let vx : FEVec 7 := M.ψ (Additive.ofMul ⟨x, hxBs⟩)
  let vz : FEVec 7 := M.ψ (Additive.ofMul ⟨z, hzBs⟩)
  let T : Set (MulAut ↥Bs) :=
    {φ | φ ∈ frameReflSet (ggAutomizer L Bs) ∧ φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩}
  have h13' : 13 ≤ (feTx 7 vx ∩ feTx 7 vz).ncard := by
    have hsub : frameRho M.ψ '' T ⊆ feTx 7 vx ∩ feTx 7 vz := by
      rintro t ⟨φ, hφ, rfl⟩
      have hφA : φ ∈ M.A := hLA hφ.1.1
      have ht : frameRho M.ψ φ ∈ feT 7 := hrefl φ hφA hφ.1.2
      have hφx : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ :=
        ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxBs⟩) hLx hφ.1.1
      have htx : (frameRho M.ψ φ).mulVec vx = vx := by
        rw [frameRho_mulVec, hφx]
      have htz : (frameRho M.ψ φ).mulVec vz = vz := by
        rw [frameRho_mulVec, hφ.2]
      exact ⟨⟨ht, htx⟩, ⟨ht, htz⟩⟩
    have himg : (frameRho M.ψ '' T).ncard = T.ncard :=
      Set.ncard_image_of_injective T (frameRho_injective M.ψ)
    have hle : T.ncard ≤ (feTx 7 vx ∩ feTx 7 vz).ncard := by
      rw [← himg]
      exact Set.ncard_le_ncard hsub
    exact le_trans h13 hle
  obtain ⟨c, t, ht, htv⟩ := exists_neg_eigen_add_smul_of_feTx (v := vx) (y := vz) hv h13'
  exact gluePlaneAux_exists_isRoot_mul_pow M hxBs hzBs hzx rfl rfl ht htv

end GGFrameModelData

end CFSG.StandardType.FrameRoute

end
