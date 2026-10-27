module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

private lemma ggTBC_decomp_unique {G : Type} [Group G] {A B : Subgroup G}
    (hAB : A ⊓ B = ⊥) {a a' b b' : G}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have hmem : a'⁻¹ * a ∈ A ⊓ B := by
    refine ⟨A.mul_mem (A.inv_mem ha') ha, ?_⟩
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    rw [h1]
    exact B.mul_mem hb' (B.inv_mem hb)
  have h1 : a'⁻¹ * a = 1 := Subgroup.mem_bot.mp (hAB ▸ hmem)
  have hA : a = a' := (inv_mul_eq_one.mp h1).symm
  refine ⟨hA, ?_⟩
  have h2 := h
  rw [hA] at h2
  exact mul_left_cancel h2

private lemma ggTBC_decomp_mem_H {G : Type} [Group G] {H C A B : Subgroup G}
    (hH : CFSG.Open.IsElemAbelian 3 H) (hHC : H ≤ C) (hAC : A ≤ C)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥)
    (hdec : ∀ g ∈ C, ∃ a ∈ A, ∃ b ∈ B, g = a * b)
    (hcent : ∀ g ∈ C, (∀ h ∈ H, g * h = h * g) → g ∈ H)
    {h a b : G} (hh : h ∈ H) (ha : a ∈ A) (hb : b ∈ B) (hdecomp : h = a * b) :
    a ∈ H ∧ b ∈ H := by
  have haH : a ∈ H := by
    refine hcent a (hAC ha) ?_
    intro k hk
    obtain ⟨ka, hka, kb, hkb, hkdecomp⟩ := hdec k (hHC hk)
    have hcomm_hk : h * k = k * h := by
      have h' : (⟨h, hh⟩ : ↥H) * ⟨k, hk⟩ = ⟨k, hk⟩ * ⟨h, hh⟩ :=
        isMulCommutative_iff.mp hH.1 ⟨h, hh⟩ ⟨k, hk⟩
      exact congrArg Subtype.val h'
    have heq : (a * ka) * (b * kb) = (ka * a) * (kb * b) := by
      calc (a * ka) * (b * kb) = a * (ka * b) * kb := by group
        _ = a * (b * ka) * kb := by rw [hcomm ka hka b hb]
        _ = (a * b) * (ka * kb) := by group
        _ = (ka * kb) * (a * b) := by
              rw [hdecomp, hkdecomp] at hcomm_hk
              exact hcomm_hk
        _ = ka * (kb * a) * b := by group
        _ = ka * (a * kb) * b := by rw [← hcomm a ha kb hkb]
        _ = (ka * a) * (kb * b) := by group
    have hfirst := (ggTBC_decomp_unique hAB (A.mul_mem ha hka) (A.mul_mem hka ha)
      (B.mul_mem hb hkb) (B.mul_mem hkb hb) heq).1
    calc a * k = a * (ka * kb) := by rw [hkdecomp]
      _ = (a * ka) * kb := by group
      _ = (ka * a) * kb := by rw [hfirst]
      _ = ka * (a * kb) := by group
      _ = ka * (kb * a) := by rw [hcomm a ha kb hkb]
      _ = (ka * kb) * a := by group
      _ = k * a := by rw [hkdecomp]
  refine ⟨haH, ?_⟩
  have hb_eq : b = a⁻¹ * h := by rw [hdecomp]; group
  rw [hb_eq]
  exact H.mul_mem (H.inv_mem haH) hh

private lemma ggTBC_conj_mem_H_of_decomp {G : Type} [Group G] {H C A B : Subgroup G}
    (hH : CFSG.Open.IsElemAbelian 3 H) (hHC : H ≤ C) (hAC : A ≤ C)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥)
    (hdec : ∀ g ∈ C, ∃ a ∈ A, ∃ b ∈ B, g = a * b)
    (hcent : ∀ g ∈ C, (∀ h ∈ H, g * h = h * g) → g ∈ H)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B)
    (hx : a * b ∈ Subgroup.normalizer (H : Set G)) (h : G) (hh : h ∈ H) :
    a * h * a⁻¹ ∈ H ∧ b * h * b⁻¹ ∈ H := by
  obtain ⟨hA, hA_mem, hB, hB_mem, hdecomp⟩ := hdec h (hHC hh)
  have hconjH : (a * b) * h * (a * b)⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp hx h).mp hh
  have hconj_eq : (a * b) * h * (a * b)⁻¹ = (a * hA * a⁻¹) * (b * hB * b⁻¹) := by
    rw [hdecomp]
    calc (a * b) * (hA * hB) * (a * b)⁻¹
        = a * (b * hA) * hB * b⁻¹ * a⁻¹ := by group
      _ = a * (hA * b) * hB * b⁻¹ * a⁻¹ := by rw [hcomm hA hA_mem b hb]
      _ = a * hA * (b * hB * b⁻¹) * a⁻¹ := by group
      _ = (a * hA * a⁻¹) * (b * hB * b⁻¹) := by
            have hyB : b * hB * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hB_mem) (B.inv_mem hb)
            have hcy : (b * hB * b⁻¹) * a⁻¹ = a⁻¹ * (b * hB * b⁻¹) := by
              have hc : Commute a (b * hB * b⁻¹) := hcomm a ha _ hyB
              exact hc.symm.inv_right.eq
            calc a * hA * (b * hB * b⁻¹) * a⁻¹
                = a * hA * ((b * hB * b⁻¹) * a⁻¹) := by group
              _ = a * hA * (a⁻¹ * (b * hB * b⁻¹)) := by rw [hcy]
              _ = (a * hA * a⁻¹) * (b * hB * b⁻¹) := by group
  have hparts := ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hconjH
    (A.mul_mem (A.mul_mem ha hA_mem) (A.inv_mem ha))
    (B.mul_mem (B.mul_mem hb hB_mem) (B.inv_mem hb)) hconj_eq
  have hABH := ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hh hA_mem hB_mem hdecomp
  refine ⟨?_, ?_⟩
  · have hcomm_inv : hB * a⁻¹ = a⁻¹ * hB := by
      have hc : Commute a hB := hcomm a ha hB hB_mem
      exact hc.symm.inv_right.eq
    have h1 : a * h * a⁻¹ = (a * hA * a⁻¹) * hB := by
      rw [hdecomp]
      calc a * (hA * hB) * a⁻¹ = (a * hA) * (hB * a⁻¹) := by group
        _ = (a * hA) * (a⁻¹ * hB) := by rw [hcomm_inv]
        _ = (a * hA * a⁻¹) * hB := by group
    rw [h1]
    exact H.mul_mem hparts.1 hABH.2
  · have h1 : b * h * b⁻¹ = hA * (b * hB * b⁻¹) := by
      rw [hdecomp]
      calc b * (hA * hB) * b⁻¹ = (b * hA * b⁻¹) * (b * hB * b⁻¹) := by group
        _ = hA * (b * hB * b⁻¹) := by
              rw [show b * hA * b⁻¹ = hA by
                rw [← hcomm hA hA_mem b hb]
                group]
    rw [h1]
    exact H.mul_mem hABH.1 hparts.2

private lemma ggTBC_normalizer_of_decomp {G : Type} [Group G] {H C A B : Subgroup G}
    (hH : CFSG.Open.IsElemAbelian 3 H) (hHC : H ≤ C) (hAC : A ≤ C)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥)
    (hdec : ∀ g ∈ C, ∃ a ∈ A, ∃ b ∈ B, g = a * b)
    (hcent : ∀ g ∈ C, (∀ h ∈ H, g * h = h * g) → g ∈ H)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B)
    (hx : a * b ∈ Subgroup.normalizer (H : Set G)) :
    a ∈ Subgroup.normalizer (H : Set G) ∧ b ∈ Subgroup.normalizer (H : Set G) := by
  have hxinv : a⁻¹ * b⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
    have h1 : (a * b)⁻¹ ∈ Subgroup.normalizer (H : Set G) := Subgroup.inv_mem _ hx
    have hc : Commute a b := hcomm a ha b hb
    have hEq : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
      rw [mul_inv_rev]
      exact hc.symm.inv_left.inv_right.eq
    rwa [hEq] at h1
  have hfa : ∀ h ∈ H, a * h * a⁻¹ ∈ H := fun h hh =>
    (ggTBC_conj_mem_H_of_decomp hH hHC hAC hcomm hAB hdec hcent ha hb hx h hh).1
  have hfai : ∀ h ∈ H, a⁻¹ * h * (a⁻¹)⁻¹ ∈ H := fun h hh =>
    (ggTBC_conj_mem_H_of_decomp hH hHC hAC hcomm hAB hdec hcent
      (A.inv_mem ha) (B.inv_mem hb) hxinv h hh).1
  have hfb : ∀ h ∈ H, b * h * b⁻¹ ∈ H := fun h hh =>
    (ggTBC_conj_mem_H_of_decomp hH hHC hAC hcomm hAB hdec hcent ha hb hx h hh).2
  have hfbi : ∀ h ∈ H, b⁻¹ * h * (b⁻¹)⁻¹ ∈ H := fun h hh =>
    (ggTBC_conj_mem_H_of_decomp hH hHC hAC hcomm hAB hdec hcent
      (A.inv_mem ha) (B.inv_mem hb) hxinv h hh).2
  constructor
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hfa h
    · intro hh
      have h' := hfai (a * h * a⁻¹) hh
      have hEq : a⁻¹ * (a * h * a⁻¹) * (a⁻¹)⁻¹ = h := by group
      rwa [hEq] at h'
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hfb h
    · intro hh
      have h' := hfbi (b * h * b⁻¹) hh
      have hEq : b⁻¹ * (b * h * b⁻¹) * (b⁻¹)⁻¹ = h := by group
      rwa [hEq] at h'

private lemma ggTBC_pow3_eq_one {G : Type} [Group G] {H : Subgroup G}
    (hH : CFSG.Open.IsElemAbelian 3 H) (x : ↥H) : x ^ 3 = 1 := by
  apply Subtype.ext
  simpa using hH.2 (x : G) x.2

private lemma ggTBC_eq_one_of_fixed_of_inv {H : Type} [Group H] {φ : MulAut H}
    (hpow : ∀ x : H, x ^ 3 = 1) {w : H} (hfix : φ w = w) (hinv : φ w = w⁻¹) :
    w = 1 := by
  have hww : w = w⁻¹ := by
    calc w = φ w := hfix.symm
      _ = w⁻¹ := hinv
  have h2 : w ^ 2 = 1 := by
    have h' : w * w⁻¹ = 1 := mul_inv_cancel w
    rw [← hww] at h'
    simpa [pow_two] using h'
  have h3 : w ^ 3 = 1 := hpow w
  calc w = w ^ 3 * (w ^ 2)⁻¹ := by group
    _ = 1 * 1⁻¹ := by rw [h3, h2]
    _ = 1 := by simp


private lemma ggTBC_split_or_fixes {G : Type} [Group G] [Finite G] {H A B : Subgroup G}
    (hH : CFSG.Open.IsElemAbelian 3 H)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥)
    {g a b : G} (ha : a ∈ A) (hb : b ∈ B) (hg : g = a * b)
    {φ : MulAut ↥H} (hφg : ∀ x : ↥H, ((φ x : ↥H) : G) = g * x * g⁻¹)
    (hφr : GGIsReflection 3 φ) :
    (∀ h ∈ H ⊓ A, a * h * a⁻¹ = h) ∨ (∀ h ∈ H ⊓ B, b * h * b⁻¹ = h) := by
  classical
  have hcommH : ∀ a b : ↥H, a * b = b * a :=
    fun a b => isMulCommutative_iff.mp hH.1 a b
  by_contra hsplit
  rw [not_or] at hsplit
  obtain ⟨hI, hII⟩ := hsplit
  obtain ⟨h₁, hnot₁⟩ := not_forall.mp hI
  obtain ⟨hh₁, hm₁⟩ := not_imp.mp hnot₁
  obtain ⟨h₂, hnot₂⟩ := not_forall.mp hII
  obtain ⟨hh₂, hm₂⟩ := not_imp.mp hnot₂
  rw [Subgroup.mem_inf] at hh₁ hh₂
  obtain ⟨hh₁H, hh₁A⟩ := hh₁
  obtain ⟨hh₂H, hh₂B⟩ := hh₂
  let h₁H : ↥H := ⟨h₁, hh₁H⟩
  let h₂H : ↥H := ⟨h₂, hh₂H⟩
  have hφh₁ : ((φ h₁H : ↥H) : G) = a * h₁ * a⁻¹ := by
    rw [hφg h₁H, hg]
    calc (a * b) * h₁ * (a * b)⁻¹ = a * (b * h₁ * b⁻¹) * a⁻¹ := by group
      _ = a * h₁ * a⁻¹ := by
            have hb₁ : b * h₁ * b⁻¹ = h₁ := by
              rw [← hcomm h₁ hh₁A b hb]
              group
            rw [hb₁]
  have hφh₂ : ((φ h₂H : ↥H) : G) = b * h₂ * b⁻¹ := by
    rw [hφg h₂H, hg]
    calc (a * b) * h₂ * (a * b)⁻¹ = a * (b * h₂ * b⁻¹) * a⁻¹ := by group
      _ = b * h₂ * b⁻¹ := by
            have hyB : b * h₂ * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hh₂B) (B.inv_mem hb)
            rw [hcomm a ha _ hyB]
            group
  let u : G := h₁⁻¹ * ((φ h₁H : ↥H) : G)
  let v : G := h₂⁻¹ * ((φ h₂H : ↥H) : G)
  have huH : u ∈ H := by
    dsimp [u]
    exact H.mul_mem (H.inv_mem hh₁H) (φ h₁H).2
  have hvH : v ∈ H := by
    dsimp [v]
    exact H.mul_mem (H.inv_mem hh₂H) (φ h₂H).2
  have huA : u ∈ A := by
    dsimp [u]
    rw [hφh₁]
    exact A.mul_mem (A.inv_mem hh₁A) (A.mul_mem (A.mul_mem ha hh₁A) (A.inv_mem ha))
  have hvB : v ∈ B := by
    dsimp [v]
    rw [hφh₂]
    exact B.mul_mem (B.inv_mem hh₂B) (B.mul_mem (B.mul_mem hb hh₂B) (B.inv_mem hb))
  have hu_ne : u ≠ 1 := by
    intro hu1
    apply hm₁
    have hφu : ((φ h₁H : ↥H) : G) = h₁ := by
      dsimp [u] at hu1
      exact (inv_mul_eq_one.mp hu1).symm
    rw [hφh₁] at hφu
    exact hφu
  have hv_ne : v ≠ 1 := by
    intro hv1
    apply hm₂
    have hφv : ((φ h₂H : ↥H) : G) = h₂ := by
      dsimp [v] at hv1
      exact (inv_mul_eq_one.mp hv1).symm
    rw [hφh₂] at hφv
    exact hφv
  let uH : ↥H := ⟨u, huH⟩
  let vH : ↥H := ⟨v, hvH⟩
  have huH_ne : uH ≠ 1 := by
    intro h
    exact hu_ne (congrArg Subtype.val h)
  have hvH_ne : vH ≠ 1 := by
    intro h
    exact hv_ne (congrArg Subtype.val h)
  have hφ2 : ∀ x : ↥H, φ (φ x) = x := by
    intro x
    have h := congrArg (fun e : MulAut ↥H => e x) hφr.1
    simpa [pow_two] using h
  have hφu : φ uH = uH⁻¹ := by
    have huH_eq : uH = h₁H⁻¹ * φ h₁H := by
      apply Subtype.ext
      rfl
    rw [huH_eq, map_mul, map_inv, hφ2, mul_inv_rev, inv_inv]
  have hφv : φ vH = vH⁻¹ := by
    have hvH_eq : vH = h₂H⁻¹ * φ h₂H := by
      apply Subtype.ext
      rfl
    rw [hvH_eq, map_mul, map_inv, hφ2, mul_inv_rev, inv_inv]
  have huord : orderOf uH = 3 :=
    orderOf_eq_prime (ggTBC_pow3_eq_one hH uH) huH_ne
  have hvord : orderOf vH = 3 :=
    orderOf_eq_prime (ggTBC_pow3_eq_one hH vH) hvH_ne
  let H1 : Subgroup ↥H := Subgroup.zpowers uH
  let H2 : Subgroup ↥H := Subgroup.zpowers vH
  let K : Subgroup ↥H := H1 ⊔ H2
  have hH1A : H1 ≤ A.subgroupOf H := by
    change Subgroup.zpowers uH ≤ A.subgroupOf H
    rw [Subgroup.zpowers_le]
    exact (Subgroup.mem_subgroupOf).mpr huA
  have hH2B : H2 ≤ B.subgroupOf H := by
    change Subgroup.zpowers vH ≤ B.subgroupOf H
    rw [Subgroup.zpowers_le]
    exact (Subgroup.mem_subgroupOf).mpr hvB
  have hdisj : H1 ⊓ H2 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxA : ((x : ↥H) : G) ∈ A := (Subgroup.mem_subgroupOf.mp (hH1A hx.1))
    have hxB : ((x : ↥H) : G) ∈ B := (Subgroup.mem_subgroupOf.mp (hH2B hx.2))
    have hx1 : ((x : ↥H) : G) = 1 :=
      Subgroup.mem_bot.mp (hAB ▸ (show ((x : ↥H) : G) ∈ A ⊓ B from ⟨hxA, hxB⟩))
    exact Subtype.ext hx1
  let H1' : Subgroup ↥K := H1.subgroupOf K
  let H2' : Subgroup ↥K := H2.subgroupOf K
  have hK : K = Subgroup.closure ((H1 : Set ↥H) ∪ (H2 : Set ↥H)) := by
    change H1 ⊔ H2 = Subgroup.closure ((H1 : Set ↥H) ∪ (H2 : Set ↥H))
    rw [Subgroup.sup_eq_closure]
  have hcomp : H1'.IsComplement' H2' := by
    change Function.Bijective
      (fun p : ↥H1' × ↥H2' => ((p.1 : ↥K) * (p.2 : ↥K) : ↥K))
    constructor
    · rintro ⟨p1, p2⟩ ⟨q1, q2⟩ hpq
      have hpqH : ((p1 : ↥K) : ↥H) * ((p2 : ↥K) : ↥H) =
          ((q1 : ↥K) : ↥H) * ((q2 : ↥K) : ↥H) := congrArg Subtype.val hpq
      have hp1 : ((p1 : ↥K) : ↥H) ∈ H1 := Subgroup.mem_subgroupOf.mp p1.2
      have hp2 : ((p2 : ↥K) : ↥H) ∈ H2 := Subgroup.mem_subgroupOf.mp p2.2
      have hq1 : ((q1 : ↥K) : ↥H) ∈ H1 := Subgroup.mem_subgroupOf.mp q1.2
      have hq2 : ((q2 : ↥K) : ↥H) ∈ H2 := Subgroup.mem_subgroupOf.mp q2.2
      have hkey : ((p1 : ↥K) : ↥H)⁻¹ * ((q1 : ↥K) : ↥H) =
          ((p2 : ↥K) : ↥H) * ((q2 : ↥K) : ↥H)⁻¹ := by
        calc ((p1 : ↥K) : ↥H)⁻¹ * ((q1 : ↥K) : ↥H)
            = ((p1 : ↥K) : ↥H)⁻¹ * ((q1 : ↥K) : ↥H) *
                (((q2 : ↥K) : ↥H) * ((q2 : ↥K) : ↥H)⁻¹) := by group
          _ = ((p1 : ↥K) : ↥H)⁻¹ *
                (((q1 : ↥K) : ↥H) * ((q2 : ↥K) : ↥H)) * ((q2 : ↥K) : ↥H)⁻¹ := by group
          _ = ((p1 : ↥K) : ↥H)⁻¹ *
                (((p1 : ↥K) : ↥H) * ((p2 : ↥K) : ↥H)) * ((q2 : ↥K) : ↥H)⁻¹ := by
                rw [← hpqH]
          _ = ((p2 : ↥K) : ↥H) * ((q2 : ↥K) : ↥H)⁻¹ := by group
      have hmem : ((p1 : ↥K) : ↥H)⁻¹ * ((q1 : ↥K) : ↥H) ∈ H1 ⊓ H2 := by
        refine ⟨H1.mul_mem (H1.inv_mem hp1) hq1, ?_⟩
        rw [hkey]
        exact H2.mul_mem hp2 (H2.inv_mem hq2)
      have hone : ((p1 : ↥K) : ↥H)⁻¹ * ((q1 : ↥K) : ↥H) = 1 :=
        Subgroup.mem_bot.mp (hdisj ▸ hmem)
      have hp1q1 : ((p1 : ↥K) : ↥H) = ((q1 : ↥K) : ↥H) :=
        inv_mul_eq_one.mp hone
      have hp2q2 : ((p2 : ↥K) : ↥H) = ((q2 : ↥K) : ↥H) := by
        have h := hpqH
        rw [hp1q1] at h
        exact mul_left_cancel h
      exact Prod.ext (Subtype.ext (Subtype.ext hp1q1)) (Subtype.ext (Subtype.ext hp2q2))
    ·
      have hcover : ∀ x ∈ K, ∃ y ∈ H1, ∃ z ∈ H2, y * z = x := by
        intro x hx
        rw [hK] at hx
        induction hx using Subgroup.closure_induction with
        | mem y hy =>
            rw [Set.mem_union] at hy
            rcases hy with hy1 | hy2
            · exact ⟨y, hy1, 1, H2.one_mem, by simp⟩
            · exact ⟨1, H1.one_mem, y, hy2, by simp⟩
        | one => exact ⟨1, H1.one_mem, 1, H2.one_mem, by simp⟩
        | mul y z hy hz ihy ihz =>
            obtain ⟨y1, hy1, y2, hy2, rfl⟩ := ihy
            obtain ⟨z1, hz1, z2, hz2, rfl⟩ := ihz
            refine ⟨y1 * z1, H1.mul_mem hy1 hz1, y2 * z2, H2.mul_mem hy2 hz2, ?_⟩
            calc y1 * z1 * (y2 * z2) = y1 * (z1 * y2) * z2 := by group
              _ = y1 * (y2 * z1) * z2 := by rw [hcommH z1 y2]
              _ = y1 * y2 * (z1 * z2) := by group
        | inv y hy ihy =>
            obtain ⟨y1, hy1, y2, hy2, rfl⟩ := ihy
            refine ⟨y1⁻¹, H1.inv_mem hy1, y2⁻¹, H2.inv_mem hy2, ?_⟩
            rw [mul_inv_rev]
            exact hcommH y1⁻¹ y2⁻¹
      intro x
      obtain ⟨y, hy1, z, hy2, hyz⟩ := hcover ((x : ↥K) : ↥H) x.2
      refine ⟨(⟨⟨y, Subgroup.mem_sup_left hy1⟩, hy1⟩,
        ⟨⟨z, Subgroup.mem_sup_right hy2⟩, hy2⟩), ?_⟩
      exact Subtype.ext hyz
  have hKcard : Nat.card ↥K = 9 := by
    have hc := Subgroup.IsComplement'.card_mul_card hcomp
    have hc1 : Nat.card ↥H1' = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show H1 ≤ K from le_sup_left)).toEquiv]
      change Nat.card ↥(Subgroup.zpowers uH) = 3
      rw [Nat.card_zpowers, huord]
    have hc2 : Nat.card ↥H2' = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show H2 ≤ K from le_sup_right)).toEquiv]
      change Nat.card ↥(Subgroup.zpowers vH) = 3
      rw [Nat.card_zpowers, hvord]
    rw [hc1, hc2] at hc
    omega
  have hinv_zpow : ∀ (x : ↥H) (n : ℤ), φ x = x⁻¹ → φ (x ^ n) = (x ^ n)⁻¹ := by
    intro x n hx
    rw [map_zpow, hx, inv_zpow]
  have hinvK : ∀ w ∈ K, φ w = w⁻¹ := by
    intro w hw
    rw [hK] at hw
    refine Subgroup.closure_induction (p := fun x _ => φ x = x⁻¹) ?_ ?_ ?_ ?_ hw
    · intro x hx
      rw [Set.mem_union] at hx
      rcases hx with hx1 | hx2
      · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx1
        exact hinv_zpow uH n hφu
      · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx2
        exact hinv_zpow vH n hφv
    · simp
    · intro x y hx hy hxinv hyinv
      rw [map_mul, hxinv, hyinv, mul_inv_rev]
      exact hcommH x⁻¹ y⁻¹
    · intro x hx hxinv
      rw [map_inv, hxinv, inv_inv]
  have hemb : Function.Injective
      (fun p : {x : ↥H // φ x = x} × ↥K => p.1.1 * (p.2 : ↥H)) := by
    rintro ⟨⟨f, hf⟩, w⟩ ⟨⟨f', hf'⟩, w'⟩ heq
    have heq' : f * ((w : ↥K) : ↥H) = f' * ((w' : ↥K) : ↥H) := heq
    have hkey : f'⁻¹ * f = ((w' : ↥K) : ↥H) * (((w : ↥K) : ↥H))⁻¹ := by
      calc f'⁻¹ * f = f'⁻¹ * (f * ((w : ↥K) : ↥H)) * (((w : ↥K) : ↥H))⁻¹ := by group
        _ = f'⁻¹ * (f' * ((w' : ↥K) : ↥H)) * (((w : ↥K) : ↥H))⁻¹ := by rw [heq']
        _ = ((w' : ↥K) : ↥H) * (((w : ↥K) : ↥H))⁻¹ := by group
    have hfix : φ (f'⁻¹ * f) = f'⁻¹ * f := by
      rw [map_mul, map_inv, hf', hf]
    have hinv : φ (f'⁻¹ * f) = (f'⁻¹ * f)⁻¹ := by
      rw [hkey]
      have hw' : φ ((w' : ↥K) : ↥H) = ((w' : ↥K) : ↥H)⁻¹ := hinvK _ w'.2
      have hw : φ ((w : ↥K) : ↥H) = ((w : ↥K) : ↥H)⁻¹ := hinvK _ w.2
      calc φ (((w' : ↥K) : ↥H) * (((w : ↥K) : ↥H))⁻¹)
          = φ ((w' : ↥K) : ↥H) * φ ((((w : ↥K) : ↥H))⁻¹) := by rw [map_mul]
        _ = ((w' : ↥K) : ↥H)⁻¹ * ((((w : ↥K) : ↥H))⁻¹)⁻¹ := by rw [map_inv, hw', hw]
        _ = (((w' : ↥K) : ↥H) * (((w : ↥K) : ↥H))⁻¹)⁻¹ := by
              rw [mul_inv_rev, inv_inv]
              exact hcommH ((w' : ↥K) : ↥H)⁻¹ (((w : ↥K) : ↥H))
    have hone : f'⁻¹ * f = 1 :=
      ggTBC_eq_one_of_fixed_of_inv (fun x => ggTBC_pow3_eq_one hH x) hfix hinv
    have hff : f = f' := (inv_mul_eq_one.mp hone).symm
    have hww : w = w' := by
      apply Subtype.ext
      have h := heq'
      rw [hff] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext hff) hww
  have hpos : 0 < Nat.card {x : ↥H // φ x = x} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have hle := Nat.card_le_card_of_injective
    (fun p : {x : ↥H // φ x = x} × ↥K => p.1.1 * (p.2 : ↥H)) hemb
  rw [Nat.card_prod, hKcard, ← hφr.2] at hle
  omega


theorem ggTBC_refl_split {G : Type} [Group G] [Finite G] {H C A B Ω J : Subgroup G}
    (hH : CFSG.Open.IsElemAbelian 3 H) (hHC : H ≤ C) (hAC : A ≤ C) (hBC : B ≤ C)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥)
    (hdec : ∀ g ∈ C, ∃ a ∈ A, ∃ b ∈ B, g = a * b)
    (hcent : ∀ g ∈ C, (∀ h ∈ H, g * h = h * g) → g ∈ H) (hHΩ : H ≤ Ω)
    (hJ : (J ≤ A ∧ Ω ⊓ A ≤ J) ∨ (J ≤ B ∧ ∀ b ∈ B, b ^ 3 ∈ J))
    {φ : MulAut ↥H} (hφ : φ ∈ ggAutomizer (Ω ⊓ C) H) (hφr : GGIsReflection 3 φ) :
    φ ∈ ggAutomizer J H ∨ ∀ ψ ∈ ggAutomizer J H, φ * ψ = ψ * φ := by
  classical
  obtain ⟨g, hgΩC, hgN, hgconj⟩ := mem_ggAutomizer_iff.mp hφ
  obtain ⟨a₀, ha₀, b₀, hb₀, hg_eq⟩ := hdec g hgΩC.2
  have hx : a₀ * b₀ ∈ Subgroup.normalizer (H : Set G) := by
    rwa [← hg_eq]
  obtain ⟨haN, hbN⟩ :=
    ggTBC_normalizer_of_decomp hH hHC hAC hcomm hAB hdec hcent ha₀ hb₀ hx
  have hsplit := ggTBC_split_or_fixes hH hcomm hAB ha₀ hb₀ hg_eq hgconj hφr
  rcases hJ with ⟨hJA, hJΩA⟩ | ⟨hJB, hJcube⟩
  · rcases hsplit with hI | hII
    ·
      right
      have hφb : ∀ x : ↥H, ((φ x : ↥H) : G) = b₀ * x * b₀⁻¹ := by
        intro x
        rw [hgconj x, hg_eq]
        have haCentH : ∀ h ∈ H, a₀ * h = h * a₀ := by
          intro h hh
          obtain ⟨hA, hA_mem, hB, hB_mem, hdecomp⟩ := hdec h (hHC hh)
          have hAH : hA ∈ H :=
            (ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hh hA_mem hB_mem hdecomp).1
          have hBH : hB ∈ H :=
            (ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hh hA_mem hB_mem hdecomp).2
          have hAfix : a₀ * hA * a₀⁻¹ = hA := hI hA ⟨hAH, hA_mem⟩
          have hAeq : a₀ * hA = hA * a₀ := by
            calc a₀ * hA = (a₀ * hA * a₀⁻¹) * a₀ := by group
              _ = hA * a₀ := by rw [hAfix]
          have hBeq : a₀ * hB = hB * a₀ := hcomm a₀ ha₀ hB hB_mem
          calc a₀ * h = a₀ * (hA * hB) := by rw [hdecomp]
            _ = (a₀ * hA) * hB := by group
            _ = (hA * a₀) * hB := by rw [hAeq]
            _ = hA * (hB * a₀) := by rw [mul_assoc, hBeq]
            _ = hA * hB * a₀ := by group
            _ = h * a₀ := by rw [hdecomp]
        calc (a₀ * b₀) * (x : G) * (a₀ * b₀)⁻¹
            = a₀ * (b₀ * (x : G) * b₀⁻¹) * a₀⁻¹ := by group
          _ = b₀ * (x : G) * b₀⁻¹ := by
                have hyH : b₀ * (x : G) * b₀⁻¹ ∈ H :=
                  (Subgroup.mem_normalizer_iff.mp hbN (x : G)).mp x.2
                rw [haCentH _ hyH]
                group
      intro ψ hψ
      obtain ⟨j, hjJ, _hjN, hjψ⟩ := mem_ggAutomizer_iff.mp hψ
      have hjA : j ∈ A := hJA hjJ
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      have hjb : j * b₀ = b₀ * j := hcomm j hjA b₀ hb₀
      have hjb_inv : j⁻¹ * b₀⁻¹ = b₀⁻¹ * j⁻¹ := by
        calc j⁻¹ * b₀⁻¹ = (b₀ * j)⁻¹ := by rw [mul_inv_rev]
          _ = (j * b₀)⁻¹ := by rw [hjb]
          _ = b₀⁻¹ * j⁻¹ := by rw [mul_inv_rev]
      calc ((φ * ψ) x : G) = (φ (ψ x) : G) := by rw [MulAut.mul_apply]
        _ = b₀ * ((ψ x : ↥H) : G) * b₀⁻¹ := hφb (ψ x)
        _ = b₀ * (j * (x : G) * j⁻¹) * b₀⁻¹ := by rw [hjψ x]
        _ = j * (b₀ * (x : G) * b₀⁻¹) * j⁻¹ := by
              calc b₀ * (j * (x : G) * j⁻¹) * b₀⁻¹
                  = (b₀ * j) * (x : G) * (j⁻¹ * b₀⁻¹) := by group
                _ = (j * b₀) * (x : G) * (j⁻¹ * b₀⁻¹) := by rw [← hjb]
                _ = (j * b₀) * (x : G) * (b₀⁻¹ * j⁻¹) := by rw [hjb_inv]
                _ = j * (b₀ * (x : G) * b₀⁻¹) * j⁻¹ := by group
        _ = j * ((φ x : ↥H) : G) * j⁻¹ := by rw [hφb x]
        _ = ((ψ * φ) x : G) := by rw [MulAut.mul_apply, hjψ (φ x)]
    ·
      have hbCentH : ∀ h ∈ H, b₀ * h = h * b₀ := by
        intro h hh
        obtain ⟨hA, hA_mem, hB, hB_mem, hdecomp⟩ := hdec h (hHC hh)
        have hAH : hA ∈ H :=
          (ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hh hA_mem hB_mem hdecomp).1
        have hBH : hB ∈ H :=
          (ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hh hA_mem hB_mem hdecomp).2
        have hBfix : b₀ * hB * b₀⁻¹ = hB := hII hB ⟨hBH, hB_mem⟩
        have hBeq : b₀ * hB = hB * b₀ := by
          calc b₀ * hB = (b₀ * hB * b₀⁻¹) * b₀ := by group
            _ = hB * b₀ := by rw [hBfix]
        have hAeq : b₀ * hA = hA * b₀ := (hcomm hA hA_mem b₀ hb₀).symm
        calc b₀ * h = b₀ * (hA * hB) := by rw [hdecomp]
          _ = (b₀ * hA) * hB := by group
          _ = (hA * b₀) * hB := by rw [hAeq]
          _ = hA * (hB * b₀) := by rw [mul_assoc, hBeq]
          _ = hA * hB * b₀ := by group
          _ = h * b₀ := by rw [hdecomp]
      have hb₀H : b₀ ∈ H := hcent b₀ (hBC hb₀) hbCentH
      have hφa : ∀ x : ↥H, ((φ x : ↥H) : G) = a₀ * x * a₀⁻¹ := by
        intro x
        rw [hgconj x, hg_eq]
        calc (a₀ * b₀) * (x : G) * (a₀ * b₀)⁻¹
            = a₀ * (b₀ * (x : G) * b₀⁻¹) * a₀⁻¹ := by group
          _ = a₀ * (x : G) * a₀⁻¹ := by
                have hxfix : b₀ * (x : G) * b₀⁻¹ = x := by
                  rw [hbCentH (x : G) x.2]
                  group
                rw [hxfix]
      have ha₀Ω : a₀ ∈ Ω := by
        have hb₀Ω : b₀ ∈ Ω := hHΩ hb₀H
        have hEq : a₀ = g * b₀⁻¹ := by rw [hg_eq]; group
        rw [hEq]
        exact Ω.mul_mem hgΩC.1 (Ω.inv_mem hb₀Ω)
      exact Or.inl (mem_ggAutomizer_iff.mpr
        ⟨a₀, hJΩA ⟨ha₀Ω, ha₀⟩, haN, fun x => hφa x⟩)

  · rcases hsplit with hI | hII
    ·
      left
      have hφb : ∀ x : ↥H, ((φ x : ↥H) : G) = b₀ * x * b₀⁻¹ := by
        intro x
        rw [hgconj x, hg_eq]
        have haCentH : ∀ h ∈ H, a₀ * h = h * a₀ := by
          intro h hh
          obtain ⟨hA, hA_mem, hB, hB_mem, hdecomp⟩ := hdec h (hHC hh)
          have hAH : hA ∈ H :=
            (ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hh hA_mem hB_mem hdecomp).1
          have hBH : hB ∈ H :=
            (ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hh hA_mem hB_mem hdecomp).2
          have hAfix : a₀ * hA * a₀⁻¹ = hA := hI hA ⟨hAH, hA_mem⟩
          have hAeq : a₀ * hA = hA * a₀ := by
            calc a₀ * hA = (a₀ * hA * a₀⁻¹) * a₀ := by group
              _ = hA * a₀ := by rw [hAfix]
          have hBeq : a₀ * hB = hB * a₀ := hcomm a₀ ha₀ hB hB_mem
          calc a₀ * h = a₀ * (hA * hB) := by rw [hdecomp]
            _ = (a₀ * hA) * hB := by group
            _ = (hA * a₀) * hB := by rw [hAeq]
            _ = hA * (hB * a₀) := by rw [mul_assoc, hBeq]
            _ = hA * hB * a₀ := by group
            _ = h * a₀ := by rw [hdecomp]
        calc (a₀ * b₀) * (x : G) * (a₀ * b₀)⁻¹
            = a₀ * (b₀ * (x : G) * b₀⁻¹) * a₀⁻¹ := by group
          _ = b₀ * (x : G) * b₀⁻¹ := by
                have hyH : b₀ * (x : G) * b₀⁻¹ ∈ H :=
                  (Subgroup.mem_normalizer_iff.mp hbN (x : G)).mp x.2
                rw [haCentH _ hyH]
                group
      let t : G := b₀ ^ 3
      have htJ : t ∈ J := hJcube b₀ hb₀
      have htN : t ∈ Subgroup.normalizer (H : Set G) := by
        dsimp [t]
        exact Subgroup.pow_mem _ hbN 3
      have hb₀sq : ∀ x : ↥H, b₀ * (b₀ * (x : G) * b₀⁻¹) * b₀⁻¹ = x := by
        intro x
        calc b₀ * (b₀ * (x : G) * b₀⁻¹) * b₀⁻¹
            = b₀ * ((φ x : ↥H) : G) * b₀⁻¹ := by rw [hφb x]
          _ = ((φ (φ x) : ↥H) : G) := (hφb (φ x)).symm
          _ = x := by
                have h := congrArg (fun e : MulAut ↥H => e x) hφr.1
                simpa [pow_two] using h
      have ht3 : t = b₀ * b₀ * b₀ := by dsimp [t]; rw [pow_three, mul_assoc]
      have htconj : ∀ x : ↥H, t * (x : G) * t⁻¹ = b₀ * (x : G) * b₀⁻¹ := by
        intro x
        rw [ht3]
        calc (b₀ * b₀ * b₀) * (x : G) * (b₀ * b₀ * b₀)⁻¹
            = b₀ * (b₀ * (b₀ * (x : G) * b₀⁻¹) * b₀⁻¹) * b₀⁻¹ := by group
          _ = b₀ * (x : G) * b₀⁻¹ := by rw [hb₀sq x]
      exact mem_ggAutomizer_iff.mpr
        ⟨t, htJ, htN, fun x => by rw [hφb x, htconj x]⟩
    ·
      right
      have hφa : ∀ x : ↥H, ((φ x : ↥H) : G) = a₀ * x * a₀⁻¹ := by
        intro x
        rw [hgconj x, hg_eq]
        have hbCentH : ∀ h ∈ H, b₀ * h = h * b₀ := by
          intro h hh
          obtain ⟨hA, hA_mem, hB, hB_mem, hdecomp⟩ := hdec h (hHC hh)
          have hAH : hA ∈ H :=
            (ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hh hA_mem hB_mem hdecomp).1
          have hBH : hB ∈ H :=
            (ggTBC_decomp_mem_H hH hHC hAC hcomm hAB hdec hcent hh hA_mem hB_mem hdecomp).2
          have hBfix : b₀ * hB * b₀⁻¹ = hB := hII hB ⟨hBH, hB_mem⟩
          have hBeq : b₀ * hB = hB * b₀ := by
            calc b₀ * hB = (b₀ * hB * b₀⁻¹) * b₀ := by group
              _ = hB * b₀ := by rw [hBfix]
          have hAeq : b₀ * hA = hA * b₀ := (hcomm hA hA_mem b₀ hb₀).symm
          calc b₀ * h = b₀ * (hA * hB) := by rw [hdecomp]
            _ = (b₀ * hA) * hB := by group
            _ = (hA * b₀) * hB := by rw [hAeq]
            _ = hA * (hB * b₀) := by rw [mul_assoc, hBeq]
            _ = hA * hB * b₀ := by group
            _ = h * b₀ := by rw [hdecomp]
        calc (a₀ * b₀) * (x : G) * (a₀ * b₀)⁻¹
            = a₀ * (b₀ * (x : G) * b₀⁻¹) * a₀⁻¹ := by group
          _ = a₀ * (x : G) * a₀⁻¹ := by
                have hxfix : b₀ * (x : G) * b₀⁻¹ = x := by
                  rw [hbCentH (x : G) x.2]
                  group
                rw [hxfix]
      intro ψ hψ
      obtain ⟨j, hjJ, _hjN, hjψ⟩ := mem_ggAutomizer_iff.mp hψ
      have hjB : j ∈ B := hJB hjJ
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      have haj : a₀ * j = j * a₀ := hcomm a₀ ha₀ j hjB
      have haj_inv : a₀⁻¹ * j⁻¹ = j⁻¹ * a₀⁻¹ := by
        calc a₀⁻¹ * j⁻¹ = (j * a₀)⁻¹ := by rw [mul_inv_rev]
          _ = (a₀ * j)⁻¹ := by rw [haj]
          _ = j⁻¹ * a₀⁻¹ := by rw [mul_inv_rev]
      calc ((φ * ψ) x : G) = (φ (ψ x) : G) := by rw [MulAut.mul_apply]
        _ = a₀ * ((ψ x : ↥H) : G) * a₀⁻¹ := hφa (ψ x)
        _ = a₀ * (j * (x : G) * j⁻¹) * a₀⁻¹ := by rw [hjψ x]
        _ = j * (a₀ * (x : G) * a₀⁻¹) * j⁻¹ := by
              calc a₀ * (j * (x : G) * j⁻¹) * a₀⁻¹
                  = (a₀ * j) * (x : G) * (j⁻¹ * a₀⁻¹) := by group
                _ = (j * a₀) * (x : G) * (j⁻¹ * a₀⁻¹) := by rw [← haj]
                _ = (j * a₀) * (x : G) * (a₀⁻¹ * j⁻¹) := by rw [haj_inv]
                _ = j * (a₀ * (x : G) * a₀⁻¹) * j⁻¹ := by group
        _ = j * ((φ x : ↥H) : G) * j⁻¹ := by rw [hφa x]
        _ = ((ψ * φ) x : G) := by rw [MulAut.mul_apply, hjψ (φ x)]

end CFSG.StandardType

end
