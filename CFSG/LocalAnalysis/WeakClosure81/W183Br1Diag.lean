module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs3
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Shape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt)

@[expose] def FinG3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal →
    Subgroup.centralizer (L : Set Y) = ⊥ →
    ∀ A : Subgroup Y, Nat.card A = 4 → IsElemAbelian 2 A →
      (∀ t ∈ A, t ≠ 1 → ∀ g ∈ L, g * t = t * g → ∀ a ∈ A, g * a = a * g) →
      ((IsL2 ↥L 2 ∨ IsL3 ↥L 2 ∨ IsU3 ↥L 2 ∨ IsSp4 ↥L 2) →
        A ≤ L ∧ ∃ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ ∀ x ∈ A, x ≠ 1 → n * x * n⁻¹ ≠ x) ∧
      ((IsL3 ↥L 1 ∨ IsAlt ↥L 6) → False)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y L₁ L₂ A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

private theorem w183_diag_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun e f h => LinearEquiv.ext (congrFun h))

private theorem w183_diag_center_eq_bot_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center X := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

private theorem w183_conj_conj {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

private theorem w183_mem_centralizer_of_conj_eq {W : Type*} [Group W] {L : Subgroup W}
    {g h : W} (hg : g ∈ Subgroup.normalizer (L : Set W))
    (hh : h ∈ Subgroup.normalizer (L : Set W))
    (hgh : ∀ l ∈ L, g * l * g⁻¹ = h * l * h⁻¹) :
    g * h⁻¹ ∈ Subgroup.centralizer (L : Set W) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hlin : h⁻¹ * l * h ∈ L := by
    have hh' : h⁻¹ ∈ Subgroup.normalizer (L : Set W) :=
      (Subgroup.normalizer (L : Set W)).inv_mem hh
    simpa using (Subgroup.mem_normalizer_iff.mp hh' l).mp hl
  have h1 : g * (h⁻¹ * l * h) * g⁻¹ = l := by
    rw [hgh (h⁻¹ * l * h) hlin]
    group
  have h2 : g * h⁻¹ * l = l * (g * h⁻¹) := by
    calc g * h⁻¹ * l = (g * (h⁻¹ * l * h) * g⁻¹) * (g * h⁻¹) := by group
      _ = l * (g * h⁻¹) := by rw [h1]
  exact h2.symm

private theorem w183_eq_one_of_mem_inf_centralizer {W : Type*} [Group W] {L : Subgroup W}
    (hZ : Subgroup.center ↥L = ⊥) {c : W} (hcL : c ∈ L)
    (hcC : c ∈ Subgroup.centralizer (L : Set W)) : c = 1 := by
  have hzc : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using Subgroup.mem_centralizer_iff.mp hcC (g : W) g.2
  rw [hZ, Subgroup.mem_bot] at hzc
  exact congrArg Subtype.val hzc

private theorem w183_conj_injective_of_center_bot {X : Type*} [Group X]
    (hZ : Subgroup.center X = ⊥) : Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro x y hxy
  have hmem : y⁻¹ * x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun f : MulAut X => f z) hxy
    simp only [MulAut.conj_apply] at hz
    have h1 : (y⁻¹ * x) * z = z * (y⁻¹ * x) := by
      calc (y⁻¹ * x) * z = y⁻¹ * (x * z * x⁻¹) * x := by group
        _ = y⁻¹ * (y * z * y⁻¹) * x := by rw [hz]
        _ = z * (y⁻¹ * x) := by group
    exact h1.symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact mul_left_cancel (hmem.trans (inv_mul_cancel y).symm)

private theorem w183_mem_centralizer_of_factor {W : Type*} [Group W] {L K : Subgroup W}
    {d p q : W} (hd : d ∈ Subgroup.normalizer (L : Set W)) (hp : p ∈ L) (hq : q ∈ K)
    (hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    (hpconj : ∀ m ∈ L, p⁻¹ * m * p = d⁻¹ * m * d) :
    d * (p * q)⁻¹ ∈ Subgroup.centralizer (L : Set W) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hlinv : d⁻¹ * l * d ∈ L := by
    have hd' : d⁻¹ ∈ Subgroup.normalizer (L : Set W) :=
      (Subgroup.normalizer (L : Set W)).inv_mem hd
    simpa using (Subgroup.mem_normalizer_iff.mp hd' l).mp hl
  have hqcomm : q⁻¹ * (d⁻¹ * l * d) * q = d⁻¹ * l * d := by
    have h := hcomm q hq (d⁻¹ * l * d) hlinv
    have hx : d⁻¹ * l * d = q⁻¹ * (d⁻¹ * l * d) * q := by
      calc d⁻¹ * l * d = q⁻¹ * (q * (d⁻¹ * l * d)) := by group
        _ = q⁻¹ * ((d⁻¹ * l * d) * q) := by rw [h]
        _ = q⁻¹ * (d⁻¹ * l * d) * q := by group
    exact hx.symm
  have hkey : d * (p * q)⁻¹ * l * (d * (p * q)⁻¹)⁻¹ = l := by
    calc d * (p * q)⁻¹ * l * (d * (p * q)⁻¹)⁻¹
        = d * (q⁻¹ * (p⁻¹ * l * p) * q) * d⁻¹ := by group
      _ = d * (q⁻¹ * (d⁻¹ * l * d) * q) * d⁻¹ := by rw [hpconj l hl]
      _ = d * (d⁻¹ * l * d) * d⁻¹ := by rw [hqcomm]
      _ = l := by group
  have hy : d * (p * q)⁻¹ * l = l * (d * (p * q)⁻¹) := by
    calc d * (p * q)⁻¹ * l
        = (d * (p * q)⁻¹ * l * (d * (p * q)⁻¹)⁻¹) * (d * (p * q)⁻¹) := by group
      _ = l * (d * (p * q)⁻¹) := by rw [hkey]
  exact hy.symm

private theorem w183_lieShape_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : IsL2 X 2 ∨ IsL3 X 2 ∨ IsU3 X 2 ∨ IsSp4 X 2 ∨ IsL3 X 1 ∨ IsAlt X 6) :
    IsL2 X' 2 ∨ IsL3 X' 2 ∨ IsU3 X' 2 ∨ IsSp4 X' 2 ∨ IsL3 X' 1 ∨ IsAlt X' 6 := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by obtain ⟨e'⟩ := h; exact ⟨e.symm.trans e'⟩)))))

theorem br1_false_of_diagonal (hfin : FinG3) (h : Assumption131 Y Γ VA i)
    (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B) [IsSimpleGroup ↥L₁] [IsSimpleGroup ↥L₂]
    (hnab₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (hnab₂ : ∃ a ∈ L₂, ∃ b ∈ L₂, a * b ≠ b * a)
    (hL₁Y : L₁ ≤ Y) (hL₂Y : L₂ ≤ Y) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L₁, y * l = l * y) → (∀ l ∈ L₂, y * l = l * y) → y = 1)
    (hshape₁ : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 2 ∨ IsU3 ↥L₁ 2 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 1 ∨
      IsAlt ↥L₁ 6)
    (hshape₂ : IsL2 ↥L₂ 2 ∨ IsL3 ↥L₂ 2 ∨ IsU3 ↥L₂ 2 ∨ IsSp4 ↥L₂ 2 ∨ IsL3 ↥L₂ 1 ∨
      IsAlt ↥L₂ 6)
    (hA : A ∈ Γ) (hr : mRank A ≤ i) (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hAn₂ : A ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)))
    (hC₁ : A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥)
    (hC₂ : A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_diag_finite_lgl
  have hnab₁' : ∃ a b : ↥L₁, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab₁
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hnab₂' : ∃ a b : ↥L₂, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab₂
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hZ₁ : Subgroup.center ↥L₁ = ⊥ := w183_diag_center_eq_bot_of_simple inferInstance hnab₁'
  have hZ₂ : Subgroup.center ↥L₂ = ⊥ := w183_diag_center_eq_bot_of_simple inferInstance hnab₂'
  have hconjinj₁ := w183_conj_injective_of_center_bot hZ₁
  have hconjinj₂ := w183_conj_injective_of_center_bot hZ₂
  haveI : Finite (MulAut ↥L₁) :=
    Finite.of_injective (fun f : MulAut ↥L₁ => (f : ↥L₁ → ↥L₁))
      (fun f g hfg => MulEquiv.ext (congrFun hfg))
  haveI : Finite (MulAut ↥L₂) :=
    Finite.of_injective (fun f : MulAut ↥L₂ => (f : ↥L₂ → ↥L₂))
      (fun f g hfg => MulEquiv.ext (congrFun hfg))
  let c₁ : ↥A →* MulAut ↥L₁ :=
    (Subgroup.normalizerMonoidHom L₁).comp (Subgroup.inclusion hAn₁)
  let c₂ : ↥A →* MulAut ↥L₂ :=
    (Subgroup.normalizerMonoidHom L₂).comp (Subgroup.inclusion hAn₂)
  have hc₁ : ∀ (a : ↥A) (l : ↥L₁),
      ((c₁ a l : ↥L₁) : LGL 2 V) = (a : LGL 2 V) * l * (a : LGL 2 V)⁻¹ := by
    intro a l
    exact Subgroup.normalizerMonoidHom_apply_apply_coe L₁ (Subgroup.inclusion hAn₁ a) l
  have hc₂ : ∀ (a : ↥A) (l : ↥L₂),
      ((c₂ a l : ↥L₂) : LGL 2 V) = (a : LGL 2 V) * l * (a : LGL 2 V)⁻¹ := by
    intro a l
    exact Subgroup.normalizerMonoidHom_apply_apply_coe L₂ (Subgroup.inclusion hAn₂ a) l
  have hc₁inj : Function.Injective c₁ := by
    intro a b hab
    have hker : c₁ (a * b⁻¹) = 1 := by rw [map_mul, hab, map_inv, mul_inv_cancel]
    have hmem : ((a * b⁻¹ : ↥A) : LGL 2 V) ∈
        A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
      refine ⟨(a * b⁻¹).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro l hl
      have h1 : ((c₁ (a * b⁻¹)) ⟨l, hl⟩ : ↥L₁) = ⟨l, hl⟩ := by rw [hker]; rfl
      have h2 := congrArg Subtype.val h1
      rw [hc₁ (a * b⁻¹) ⟨l, hl⟩] at h2
      have h2' : ((a * b⁻¹ : ↥A) : LGL 2 V) * l
          * ((a * b⁻¹ : ↥A) : LGL 2 V)⁻¹ = l := by simpa using h2
      have h3 : ((a * b⁻¹ : ↥A) : LGL 2 V) * l
          = l * ((a * b⁻¹ : ↥A) : LGL 2 V) := by
        calc ((a * b⁻¹ : ↥A) : LGL 2 V) * l
            = (((a * b⁻¹ : ↥A) : LGL 2 V) * l
                * ((a * b⁻¹ : ↥A) : LGL 2 V)⁻¹)
              * ((a * b⁻¹ : ↥A) : LGL 2 V) := by group
          _ = l * ((a * b⁻¹ : ↥A) : LGL 2 V) := by rw [h2']
      exact h3.symm
    rw [hC₁, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp (Subtype.ext hmem)
  have hc₂inj : Function.Injective c₂ := by
    intro a b hab
    have hker : c₂ (a * b⁻¹) = 1 := by rw [map_mul, hab, map_inv, mul_inv_cancel]
    have hmem : ((a * b⁻¹ : ↥A) : LGL 2 V) ∈
        A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
      refine ⟨(a * b⁻¹).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro l hl
      have h1 : ((c₂ (a * b⁻¹)) ⟨l, hl⟩ : ↥L₂) = ⟨l, hl⟩ := by rw [hker]; rfl
      have h2 := congrArg Subtype.val h1
      rw [hc₂ (a * b⁻¹) ⟨l, hl⟩] at h2
      have h2' : ((a * b⁻¹ : ↥A) : LGL 2 V) * l
          * ((a * b⁻¹ : ↥A) : LGL 2 V)⁻¹ = l := by simpa using h2
      have h3 : ((a * b⁻¹ : ↥A) : LGL 2 V) * l
          = l * ((a * b⁻¹ : ↥A) : LGL 2 V) := by
        calc ((a * b⁻¹ : ↥A) : LGL 2 V) * l
            = (((a * b⁻¹ : ↥A) : LGL 2 V) * l
                * ((a * b⁻¹ : ↥A) : LGL 2 V)⁻¹)
              * ((a * b⁻¹ : ↥A) : LGL 2 V) := by group
          _ = l * ((a * b⁻¹ : ↥A) : LGL 2 V) := by rw [h2']
      exact h3.symm
    rw [hC₂, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp (Subtype.ext hmem)
  let A₁ : Subgroup (MulAut ↥L₁) := c₁.range
  let A₂ : Subgroup (MulAut ↥L₂) := c₂.range
  let Inn₁ : Subgroup (MulAut ↥L₁) := (MulAut.conj : ↥L₁ →* MulAut ↥L₁).range
  let Inn₂ : Subgroup (MulAut ↥L₂) := (MulAut.conj : ↥L₂ →* MulAut ↥L₂).range
  have hInn₁Normal : Inn₁.Normal := by
    refine ⟨fun n hn α => ?_⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hn
    change α * MulAut.conj g * α⁻¹ ∈ (MulAut.conj : ↥L₁ →* MulAut ↥L₁).range
    rw [MonoidHom.mem_range]
    exact ⟨α g, (w183_conj_conj α g).symm⟩
  have hInn₂Normal : Inn₂.Normal := by
    refine ⟨fun n hn α => ?_⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hn
    change α * MulAut.conj g * α⁻¹ ∈ (MulAut.conj : ↥L₂ →* MulAut ↥L₂).range
    rw [MonoidHom.mem_range]
    exact ⟨α g, (w183_conj_conj α g).symm⟩
  have hCInn₁ : Subgroup.centralizer (Inn₁ : Set (MulAut ↥L₁)) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    apply MulEquiv.ext
    intro g
    have hcomm : MulAut.conj g * α = α * MulAut.conj g :=
      Subgroup.mem_centralizer_iff.mp hα (MulAut.conj g)
        (show MulAut.conj g ∈ (MulAut.conj : ↥L₁ →* MulAut ↥L₁).range from
          MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    have hconj : MulAut.conj (α g) = MulAut.conj g := by
      rw [← w183_conj_conj α g, ← hcomm]; group
    simpa using hconjinj₁ hconj
  have hCInn₂ : Subgroup.centralizer (Inn₂ : Set (MulAut ↥L₂)) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    apply MulEquiv.ext
    intro g
    have hcomm : MulAut.conj g * α = α * MulAut.conj g :=
      Subgroup.mem_centralizer_iff.mp hα (MulAut.conj g)
        (show MulAut.conj g ∈ (MulAut.conj : ↥L₂ →* MulAut ↥L₂).range from
          MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    have hconj : MulAut.conj (α g) = MulAut.conj g := by
      rw [← w183_conj_conj α g, ← hcomm]; group
    simpa using hconjinj₂ hconj
  let e₁ : ↥L₁ ≃* ↥Inn₁ := MonoidHom.ofInjective hconjinj₁
  let e₂ : ↥L₂ ≃* ↥Inn₂ := MonoidHom.ofInjective hconjinj₂
  have hA₁card : Nat.card ↥A₁ = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hc₁inj).toEquiv, hcard]
  have hA₂card : Nat.card ↥A₂ = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hc₂inj).toEquiv, hcard]
  have hA₁el : IsElemAbelian 2 A₁ := by
    have helTop : IsElemAbelian 2 (⊤ : Subgroup ↥A) := by
      have hh := hel.subgroupOf A
      rwa [Subgroup.subgroupOf_self] at hh
    have hmap : (⊤ : Subgroup ↥A).map c₁ = A₁ := Subgroup.map_top c₁
    rw [← hmap]
    exact IsElemAbelian.map helTop c₁
  have hA₂el : IsElemAbelian 2 A₂ := by
    have helTop : IsElemAbelian 2 (⊤ : Subgroup ↥A) := by
      have hh := hel.subgroupOf A
      rwa [Subgroup.subgroupOf_self] at hh
    have hmap : (⊤ : Subgroup ↥A).map c₂ = A₂ := Subgroup.map_top c₂
    rw [← hmap]
    exact IsElemAbelian.map helTop c₂
  have hTI₁ : ∀ t ∈ A₁, t ≠ 1 → ∀ g ∈ Inn₁, g * t = t * g →
      ∀ a ∈ A₁, g * a = a * g := by
    intro t ht ht1 g hg hgt a ha
    obtain ⟨t₀, rfl⟩ := MonoidHom.mem_range.mp ht
    obtain ⟨x₁, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨a₀, rfl⟩ := MonoidHom.mem_range.mp ha
    have ht0 : t₀ ≠ 1 := fun h0 => ht1 (by rw [h0, map_one])
    have hcomm_xt : (x₁ : LGL 2 V) * (t₀ : LGL 2 V)
        = (t₀ : LGL 2 V) * (x₁ : LGL 2 V) := by
      have hpt : ∀ l ∈ L₁,
          (x₁ : LGL 2 V) * (t₀ : LGL 2 V) * l
              * ((x₁ : LGL 2 V) * (t₀ : LGL 2 V))⁻¹
            = (t₀ : LGL 2 V) * (x₁ : LGL 2 V) * l
              * ((t₀ : LGL 2 V) * (x₁ : LGL 2 V))⁻¹ := by
        intro l hl
        have h1 := congrArg (fun f : MulAut ↥L₁ => f ⟨l, hl⟩) hgt
        have h2 := congrArg Subtype.val h1
        rw [MulAut.mul_apply, MulAut.mul_apply] at h2
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
        rw [hc₁ t₀ ⟨l, hl⟩, hc₁ t₀ (x₁ * ⟨l, hl⟩ * x₁⁻¹)] at h2
        calc (x₁ : LGL 2 V) * (t₀ : LGL 2 V) * l
              * ((x₁ : LGL 2 V) * (t₀ : LGL 2 V))⁻¹
            = (x₁ : LGL 2 V) * ((t₀ : LGL 2 V) * l * (t₀ : LGL 2 V)⁻¹)
                * (x₁ : LGL 2 V)⁻¹ := by group
          _ = (t₀ : LGL 2 V) * ((x₁ : LGL 2 V) * l * (x₁ : LGL 2 V)⁻¹)
                * (t₀ : LGL 2 V)⁻¹ := h2
          _ = (t₀ : LGL 2 V) * (x₁ : LGL 2 V) * l
                * ((t₀ : LGL 2 V) * (x₁ : LGL 2 V))⁻¹ := by group
      have hx₁N : (x₁ : LGL 2 V) ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
        Subgroup.le_normalizer x₁.2
      have hgnorm : (x₁ : LGL 2 V) * (t₀ : LGL 2 V)
          ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
        (Subgroup.normalizer (L₁ : Set (LGL 2 V))).mul_mem hx₁N (hAn₁ t₀.2)
      have hhnorm : (t₀ : LGL 2 V) * (x₁ : LGL 2 V)
          ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
        (Subgroup.normalizer (L₁ : Set (LGL 2 V))).mul_mem (hAn₁ t₀.2) hx₁N
      have hmem := w183_mem_centralizer_of_conj_eq hgnorm hhnorm hpt
      have hx₁t₀ : (t₀ : LGL 2 V) * (x₁ : LGL 2 V)⁻¹ * (t₀ : LGL 2 V)⁻¹ ∈ L₁ :=
        (Subgroup.mem_normalizer_iff.mp (hAn₁ t₀.2) (x₁ : LGL 2 V)⁻¹).mp (L₁.inv_mem x₁.2)
      have hlin : (x₁ : LGL 2 V) * (t₀ : LGL 2 V)
          * ((t₀ : LGL 2 V) * (x₁ : LGL 2 V))⁻¹ ∈ L₁ := by
        have heq : (x₁ : LGL 2 V) * (t₀ : LGL 2 V)
            * ((t₀ : LGL 2 V) * (x₁ : LGL 2 V))⁻¹
            = (x₁ : LGL 2 V)
              * ((t₀ : LGL 2 V) * (x₁ : LGL 2 V)⁻¹ * (t₀ : LGL 2 V)⁻¹) := by group
        rw [heq]
        exact L₁.mul_mem x₁.2 hx₁t₀
      have hone := w183_eq_one_of_mem_inf_centralizer hZ₁ hlin hmem
      rwa [mul_inv_eq_one] at hone
    have hx₁normY : (⟨(x₁ : LGL 2 V), hL₁Y x₁.2⟩ : ↥Y)
        ∈ Subgroup.normalizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
      refine h.isTISub_member hA hr ⟨(t₀ : LGL 2 V), (h.le_G A hA) t₀.2⟩ ?_ ?_
        ⟨(x₁ : LGL 2 V), hL₁Y x₁.2⟩ ?_
      · rw [Subgroup.mem_subgroupOf]; exact t₀.2
      · intro h0
        exact ht0 (Subtype.ext (congrArg (fun z : ↥Y => (z : LGL 2 V)) h0))
      · apply Subtype.ext; exact hcomm_xt
    have hx₁a : ∀ a : ↥A,
        (x₁ : LGL 2 V) * (a : LGL 2 V) * (x₁ : LGL 2 V)⁻¹ ∈ A := by
      intro a
      have haY : (⟨(a : LGL 2 V), (h.le_G A hA) a.2⟩ : ↥Y) ∈ A.subgroupOf Y :=
        Subgroup.mem_subgroupOf.mpr a.2
      have hmem := (Subgroup.mem_normalizer_iff.mp hx₁normY
        (⟨(a : LGL 2 V), (h.le_G A hA) a.2⟩ : ↥Y)).mp haY
      exact Subgroup.mem_subgroupOf.mp hmem
    have hb : (x₁ : LGL 2 V) * (a₀ : LGL 2 V) * (x₁ : LGL 2 V)⁻¹ ∈ A := hx₁a a₀
    have hc₂eq : c₂ ⟨(x₁ : LGL 2 V) * (a₀ : LGL 2 V) * (x₁ : LGL 2 V)⁻¹, hb⟩
        = c₂ a₀ := by
      apply MulEquiv.ext
      intro l
      apply Subtype.ext
      rw [hc₂ _ l, hc₂ a₀ l]
      have hxl : (x₁ : LGL 2 V)⁻¹ * (l : LGL 2 V) * (x₁ : LGL 2 V) = (l : LGL 2 V) := by
        have h := hcomm x₁ x₁.2 l l.2
        calc (x₁ : LGL 2 V)⁻¹ * (l : LGL 2 V) * (x₁ : LGL 2 V)
            = (x₁ : LGL 2 V)⁻¹ * ((x₁ : LGL 2 V) * (l : LGL 2 V)) := by rw [h]; group
          _ = (l : LGL 2 V) := by group
      have hal : (a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹ ∈ L₂ :=
        (Subgroup.mem_normalizer_iff.mp (hAn₂ a₀.2) (l : LGL 2 V)).mp l.2
      have hxal : (x₁ : LGL 2 V)
            * ((a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹)
            * (x₁ : LGL 2 V)⁻¹
          = (a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹ := by
        have h := hcomm x₁ x₁.2 _ hal
        rw [h]; group
      calc (x₁ : LGL 2 V) * (a₀ : LGL 2 V) * (x₁ : LGL 2 V)⁻¹ * (l : LGL 2 V)
            * ((x₁ : LGL 2 V) * (a₀ : LGL 2 V) * (x₁ : LGL 2 V)⁻¹)⁻¹
          = (x₁ : LGL 2 V) * ((a₀ : LGL 2 V)
              * ((x₁ : LGL 2 V)⁻¹ * (l : LGL 2 V) * (x₁ : LGL 2 V))
              * (a₀ : LGL 2 V)⁻¹) * (x₁ : LGL 2 V)⁻¹ := by group
        _ = (x₁ : LGL 2 V) * ((a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹)
              * (x₁ : LGL 2 V)⁻¹ := by rw [hxl]
        _ = (a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹ := hxal
    have hx₁a₀ : (x₁ : LGL 2 V) * (a₀ : LGL 2 V) = (a₀ : LGL 2 V) * (x₁ : LGL 2 V) := by
      have hb_eq : (x₁ : LGL 2 V) * (a₀ : LGL 2 V) * (x₁ : LGL 2 V)⁻¹ = (a₀ : LGL 2 V) :=
        congrArg Subtype.val (hc₂inj hc₂eq)
      calc (x₁ : LGL 2 V) * (a₀ : LGL 2 V)
          = ((x₁ : LGL 2 V) * (a₀ : LGL 2 V) * (x₁ : LGL 2 V)⁻¹) * (x₁ : LGL 2 V) := by
            group
        _ = (a₀ : LGL 2 V) * (x₁ : LGL 2 V) := by rw [hb_eq]
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have hL : ((MulAut.conj x₁ ((c₁ a₀) l) : ↥L₁) : LGL 2 V)
        = (x₁ : LGL 2 V) * (((c₁ a₀) l : ↥L₁) : LGL 2 V) * (x₁ : LGL 2 V)⁻¹ := by
      rw [MulAut.conj_apply]; rfl
    have hR : (((c₁ a₀) (MulAut.conj x₁ l) : ↥L₁) : LGL 2 V)
        = (a₀ : LGL 2 V) * ((MulAut.conj x₁ l : ↥L₁) : LGL 2 V)
            * (a₀ : LGL 2 V)⁻¹ := hc₁ a₀ (MulAut.conj x₁ l)
    rw [hL, hR, hc₁ a₀ l]
    have hx₁l : ((MulAut.conj x₁ l : ↥L₁) : LGL 2 V)
        = (x₁ : LGL 2 V) * l * (x₁ : LGL 2 V)⁻¹ := by
      rw [MulAut.conj_apply]; rfl
    rw [hx₁l]
    calc (x₁ : LGL 2 V) * ((a₀ : LGL 2 V) * l * (a₀ : LGL 2 V)⁻¹) * (x₁ : LGL 2 V)⁻¹
        = ((x₁ : LGL 2 V) * (a₀ : LGL 2 V)) * l
            * ((x₁ : LGL 2 V) * (a₀ : LGL 2 V))⁻¹ := by group
      _ = ((a₀ : LGL 2 V) * (x₁ : LGL 2 V)) * l
            * ((a₀ : LGL 2 V) * (x₁ : LGL 2 V))⁻¹ := by rw [hx₁a₀]
      _ = (a₀ : LGL 2 V) * ((x₁ : LGL 2 V) * l * (x₁ : LGL 2 V)⁻¹)
            * (a₀ : LGL 2 V)⁻¹ := by group
  have hTI₂ : ∀ t ∈ A₂, t ≠ 1 → ∀ g ∈ Inn₂, g * t = t * g →
      ∀ a ∈ A₂, g * a = a * g := by
    intro t ht ht1 g hg hgt a ha
    obtain ⟨t₀, rfl⟩ := MonoidHom.mem_range.mp ht
    obtain ⟨x₂, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨a₀, rfl⟩ := MonoidHom.mem_range.mp ha
    have ht0 : t₀ ≠ 1 := fun h0 => ht1 (by rw [h0, map_one])
    have hcomm_xt : (x₂ : LGL 2 V) * (t₀ : LGL 2 V)
        = (t₀ : LGL 2 V) * (x₂ : LGL 2 V) := by
      have hpt : ∀ l ∈ L₂,
          (x₂ : LGL 2 V) * (t₀ : LGL 2 V) * l
              * ((x₂ : LGL 2 V) * (t₀ : LGL 2 V))⁻¹
            = (t₀ : LGL 2 V) * (x₂ : LGL 2 V) * l
              * ((t₀ : LGL 2 V) * (x₂ : LGL 2 V))⁻¹ := by
        intro l hl
        have h1 := congrArg (fun f : MulAut ↥L₂ => f ⟨l, hl⟩) hgt
        have h2 := congrArg Subtype.val h1
        rw [MulAut.mul_apply, MulAut.mul_apply] at h2
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
        rw [hc₂ t₀ ⟨l, hl⟩, hc₂ t₀ (x₂ * ⟨l, hl⟩ * x₂⁻¹)] at h2
        calc (x₂ : LGL 2 V) * (t₀ : LGL 2 V) * l
              * ((x₂ : LGL 2 V) * (t₀ : LGL 2 V))⁻¹
            = (x₂ : LGL 2 V) * ((t₀ : LGL 2 V) * l * (t₀ : LGL 2 V)⁻¹)
                * (x₂ : LGL 2 V)⁻¹ := by group
          _ = (t₀ : LGL 2 V) * ((x₂ : LGL 2 V) * l * (x₂ : LGL 2 V)⁻¹)
                * (t₀ : LGL 2 V)⁻¹ := h2
          _ = (t₀ : LGL 2 V) * (x₂ : LGL 2 V) * l
                * ((t₀ : LGL 2 V) * (x₂ : LGL 2 V))⁻¹ := by group
      have hx₂N : (x₂ : LGL 2 V) ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
        Subgroup.le_normalizer x₂.2
      have hgnorm : (x₂ : LGL 2 V) * (t₀ : LGL 2 V)
          ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
        (Subgroup.normalizer (L₂ : Set (LGL 2 V))).mul_mem hx₂N (hAn₂ t₀.2)
      have hhnorm : (t₀ : LGL 2 V) * (x₂ : LGL 2 V)
          ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
        (Subgroup.normalizer (L₂ : Set (LGL 2 V))).mul_mem (hAn₂ t₀.2) hx₂N
      have hmem := w183_mem_centralizer_of_conj_eq hgnorm hhnorm hpt
      have hx₂t₀ : (t₀ : LGL 2 V) * (x₂ : LGL 2 V)⁻¹ * (t₀ : LGL 2 V)⁻¹ ∈ L₂ :=
        (Subgroup.mem_normalizer_iff.mp (hAn₂ t₀.2) (x₂ : LGL 2 V)⁻¹).mp (L₂.inv_mem x₂.2)
      have hlin : (x₂ : LGL 2 V) * (t₀ : LGL 2 V)
          * ((t₀ : LGL 2 V) * (x₂ : LGL 2 V))⁻¹ ∈ L₂ := by
        have heq : (x₂ : LGL 2 V) * (t₀ : LGL 2 V)
            * ((t₀ : LGL 2 V) * (x₂ : LGL 2 V))⁻¹
            = (x₂ : LGL 2 V)
              * ((t₀ : LGL 2 V) * (x₂ : LGL 2 V)⁻¹ * (t₀ : LGL 2 V)⁻¹) := by group
        rw [heq]
        exact L₂.mul_mem x₂.2 hx₂t₀
      have hone := w183_eq_one_of_mem_inf_centralizer hZ₂ hlin hmem
      rwa [mul_inv_eq_one] at hone
    have hx₂normY : (⟨(x₂ : LGL 2 V), hL₂Y x₂.2⟩ : ↥Y)
        ∈ Subgroup.normalizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
      refine h.isTISub_member hA hr ⟨(t₀ : LGL 2 V), (h.le_G A hA) t₀.2⟩ ?_ ?_
        ⟨(x₂ : LGL 2 V), hL₂Y x₂.2⟩ ?_
      · rw [Subgroup.mem_subgroupOf]; exact t₀.2
      · intro h0
        exact ht0 (Subtype.ext (congrArg (fun z : ↥Y => (z : LGL 2 V)) h0))
      · apply Subtype.ext; exact hcomm_xt
    have hx₂a : ∀ a : ↥A,
        (x₂ : LGL 2 V) * (a : LGL 2 V) * (x₂ : LGL 2 V)⁻¹ ∈ A := by
      intro a
      have haY : (⟨(a : LGL 2 V), (h.le_G A hA) a.2⟩ : ↥Y) ∈ A.subgroupOf Y :=
        Subgroup.mem_subgroupOf.mpr a.2
      have hmem := (Subgroup.mem_normalizer_iff.mp hx₂normY
        (⟨(a : LGL 2 V), (h.le_G A hA) a.2⟩ : ↥Y)).mp haY
      exact Subgroup.mem_subgroupOf.mp hmem
    have hb : (x₂ : LGL 2 V) * (a₀ : LGL 2 V) * (x₂ : LGL 2 V)⁻¹ ∈ A := hx₂a a₀
    have hc₁eq : c₁ ⟨(x₂ : LGL 2 V) * (a₀ : LGL 2 V) * (x₂ : LGL 2 V)⁻¹, hb⟩
        = c₁ a₀ := by
      apply MulEquiv.ext
      intro l
      apply Subtype.ext
      rw [hc₁ _ l, hc₁ a₀ l]
      have hxl : (x₂ : LGL 2 V)⁻¹ * (l : LGL 2 V) * (x₂ : LGL 2 V) = (l : LGL 2 V) := by
        have h := hcomm l l.2 x₂ x₂.2
        calc (x₂ : LGL 2 V)⁻¹ * (l : LGL 2 V) * (x₂ : LGL 2 V)
            = (x₂ : LGL 2 V)⁻¹ * ((x₂ : LGL 2 V) * (l : LGL 2 V)) := by rw [← h]; group
          _ = (l : LGL 2 V) := by group
      have hal : (a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹ ∈ L₁ :=
        (Subgroup.mem_normalizer_iff.mp (hAn₁ a₀.2) (l : LGL 2 V)).mp l.2
      have hxal : (x₂ : LGL 2 V)
            * ((a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹)
            * (x₂ : LGL 2 V)⁻¹
          = (a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹ := by
        have h := hcomm _ hal x₂ x₂.2
        rw [← h]; group
      calc (x₂ : LGL 2 V) * (a₀ : LGL 2 V) * (x₂ : LGL 2 V)⁻¹ * (l : LGL 2 V)
            * ((x₂ : LGL 2 V) * (a₀ : LGL 2 V) * (x₂ : LGL 2 V)⁻¹)⁻¹
          = (x₂ : LGL 2 V) * ((a₀ : LGL 2 V)
              * ((x₂ : LGL 2 V)⁻¹ * (l : LGL 2 V) * (x₂ : LGL 2 V))
              * (a₀ : LGL 2 V)⁻¹) * (x₂ : LGL 2 V)⁻¹ := by group
        _ = (x₂ : LGL 2 V) * ((a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹)
              * (x₂ : LGL 2 V)⁻¹ := by rw [hxl]
        _ = (a₀ : LGL 2 V) * (l : LGL 2 V) * (a₀ : LGL 2 V)⁻¹ := hxal
    have hx₂a₀ : (x₂ : LGL 2 V) * (a₀ : LGL 2 V) = (a₀ : LGL 2 V) * (x₂ : LGL 2 V) := by
      have hb_eq : (x₂ : LGL 2 V) * (a₀ : LGL 2 V) * (x₂ : LGL 2 V)⁻¹ = (a₀ : LGL 2 V) :=
        congrArg Subtype.val (hc₁inj hc₁eq)
      calc (x₂ : LGL 2 V) * (a₀ : LGL 2 V)
          = ((x₂ : LGL 2 V) * (a₀ : LGL 2 V) * (x₂ : LGL 2 V)⁻¹) * (x₂ : LGL 2 V) := by
            group
        _ = (a₀ : LGL 2 V) * (x₂ : LGL 2 V) := by rw [hb_eq]
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have hL : ((MulAut.conj x₂ ((c₂ a₀) l) : ↥L₂) : LGL 2 V)
        = (x₂ : LGL 2 V) * (((c₂ a₀) l : ↥L₂) : LGL 2 V) * (x₂ : LGL 2 V)⁻¹ := by
      rw [MulAut.conj_apply]; rfl
    have hR : (((c₂ a₀) (MulAut.conj x₂ l) : ↥L₂) : LGL 2 V)
        = (a₀ : LGL 2 V) * ((MulAut.conj x₂ l : ↥L₂) : LGL 2 V)
            * (a₀ : LGL 2 V)⁻¹ := hc₂ a₀ (MulAut.conj x₂ l)
    rw [hL, hR, hc₂ a₀ l]
    have hx₂l : ((MulAut.conj x₂ l : ↥L₂) : LGL 2 V)
        = (x₂ : LGL 2 V) * l * (x₂ : LGL 2 V)⁻¹ := by
      rw [MulAut.conj_apply]; rfl
    rw [hx₂l]
    calc (x₂ : LGL 2 V) * ((a₀ : LGL 2 V) * l * (a₀ : LGL 2 V)⁻¹) * (x₂ : LGL 2 V)⁻¹
        = ((x₂ : LGL 2 V) * (a₀ : LGL 2 V)) * l
            * ((x₂ : LGL 2 V) * (a₀ : LGL 2 V))⁻¹ := by group
      _ = ((a₀ : LGL 2 V) * (x₂ : LGL 2 V)) * l
            * ((a₀ : LGL 2 V) * (x₂ : LGL 2 V))⁻¹ := by rw [hx₂a₀]
      _ = (a₀ : LGL 2 V) * ((x₂ : LGL 2 V) * l * (x₂ : LGL 2 V)⁻¹)
            * (a₀ : LGL 2 V)⁻¹ := by group
  have hfin₁ := hfin (MulAut ↥L₁) Inn₁ hInn₁Normal hCInn₁ A₁ hA₁card hA₁el hTI₁
  have hfin₂ := hfin (MulAut ↥L₂) Inn₂ hInn₂Normal hCInn₂ A₂ hA₂card hA₂el hTI₂
  have hshapeInn₁ : (IsL2 ↥Inn₁ 2 ∨ IsL3 ↥Inn₁ 2 ∨ IsU3 ↥Inn₁ 2 ∨ IsSp4 ↥Inn₁ 2) ∨
      (IsL3 ↥Inn₁ 1 ∨ IsAlt ↥Inn₁ 6) := by
    rcases w183_lieShape_of_mulEquiv e₁ hshape₁ with h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hshapeInn₂ : (IsL2 ↥Inn₂ 2 ∨ IsL3 ↥Inn₂ 2 ∨ IsU3 ↥Inn₂ 2 ∨ IsSp4 ↥Inn₂ 2) ∨
      (IsL3 ↥Inn₂ 1 ∨ IsAlt ↥Inn₂ 6) := by
    rcases w183_lieShape_of_mulEquiv e₂ hshape₂ with h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hshapeInn₁ with hg₁ | hb₁
  · rcases hshapeInn₂ with hg₂ | hb₂
    · obtain ⟨hA₁le, n₁, hn₁Inn, hn₁norm, hn₁fpf⟩ := hfin₁.1 hg₁
      obtain ⟨hA₂le, _, _, _, _⟩ := hfin₂.1 hg₂
      let l₁ : ↥A →* ↥L₁ := MonoidHom.comp (e₁.symm : ↥Inn₁ →* ↥L₁)
        (c₁.codRestrict Inn₁ (fun x => hA₁le (MonoidHom.mem_range.mpr ⟨x, rfl⟩)))
      have hl₁ : ∀ a : ↥A, MulAut.conj (l₁ a) = c₁ a := by
        intro a
        have h1 : ((e₁ (l₁ a) : ↥Inn₁) : MulAut ↥L₁) = MulAut.conj (l₁ a) :=
          MonoidHom.ofInjective_apply hconjinj₁
        rw [← h1]
        simp [l₁]
      have hl₁inj : Function.Injective l₁ := by
        intro a b hab
        apply hc₁inj
        rw [← hl₁ a, ← hl₁ b, hab]
      let l₂ : ↥A →* ↥L₂ := MonoidHom.comp (e₂.symm : ↥Inn₂ →* ↥L₂)
        (c₂.codRestrict Inn₂ (fun x => hA₂le (MonoidHom.mem_range.mpr ⟨x, rfl⟩)))
      have hl₂ : ∀ a : ↥A, MulAut.conj (l₂ a) = c₂ a := by
        intro a
        have h1 : ((e₂ (l₂ a) : ↥Inn₂) : MulAut ↥L₂) = MulAut.conj (l₂ a) :=
          MonoidHom.ofInjective_apply hconjinj₂
        rw [← h1]
        simp [l₂]
      have hl₂inj : Function.Injective l₂ := by
        intro a b hab
        apply hc₂inj
        rw [← hl₂ a, ← hl₂ b, hab]
      let l₁' : ↥A →* LGL 2 V := L₁.subtype.comp l₁
      let l₂' : ↥A →* LGL 2 V := L₂.subtype.comp l₂
      let X₁ : Subgroup (LGL 2 V) := l₁'.range
      let X₂ : Subgroup (LGL 2 V) := l₂'.range
      have hl₁'inj : Function.Injective l₁' := by
        intro a b hab
        exact hl₁inj (Subtype.val_injective hab)
      have hl₂'inj : Function.Injective l₂' := by
        intro a b hab
        exact hl₂inj (Subtype.val_injective hab)
      have hX₁le : X₁ ≤ L₁ := by
        rintro x ⟨a, rfl⟩
        exact (l₁ a).2
      have hX₂le : X₂ ≤ L₂ := by
        rintro x ⟨a, rfl⟩
        exact (l₂ a).2
      have hX₁card : Nat.card ↥X₁ = 4 := by
        rw [← Nat.card_congr (MonoidHom.ofInjective hl₁'inj).toEquiv, hcard]
      have hX₁sq : ∀ x ∈ X₁, x * x = 1 := by
        rintro x ⟨a, rfl⟩
        have haa : a * a = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_one]
          exact IsElemAbelian.mul_self_eq_one hel a.2
        calc l₁' a * l₁' a = l₁' (a * a) := (map_mul l₁' a a).symm
          _ = l₁' 1 := by rw [haa]
          _ = 1 := map_one l₁'
      let eX₁ : ↥A ≃* ↥X₁ := MonoidHom.ofInjective hl₁'inj
      let eX₂ : ↥A ≃* ↥X₂ := MonoidHom.ofInjective hl₂'inj
      let φ : ↥X₁ ≃* ↥X₂ := eX₁.symm.trans eX₂
      have hdiag : ∀ a : ↥A, (a : LGL 2 V) = l₁' a * l₂' a := by
        intro a
        have hdY : (a : LGL 2 V) ∈ Y := h.le_G A hA a.2
        have hpY : l₁' a ∈ Y := hL₁Y (l₁ a).2
        have hqY : l₂' a ∈ Y := hL₂Y (l₂ a).2
        have hyY : (a : LGL 2 V) * (l₁' a * l₂' a)⁻¹ ∈ Y :=
          Y.mul_mem hdY (Y.inv_mem (Y.mul_mem hpY hqY))
        have hpconj₁ : ∀ m ∈ L₁,
            (l₁' a) * m * (l₁' a)⁻¹ = (a : LGL 2 V) * m * (a : LGL 2 V)⁻¹ := by
          intro m hm
          have h2 := congrArg (fun f : MulAut ↥L₁ => f ⟨m, hm⟩) (hl₁ a)
          have h3 := congrArg Subtype.val h2
          rw [MulAut.conj_apply, hc₁ a ⟨m, hm⟩] at h3
          simpa [l₁', Subgroup.coe_mul, Subgroup.coe_inv] using h3
        have hpconj₁inv : ∀ m ∈ L₁,
            (l₁' a)⁻¹ * m * (l₁' a) = (a : LGL 2 V)⁻¹ * m * (a : LGL 2 V) := by
          intro m hm
          have hdm : (a : LGL 2 V)⁻¹ * m * (a : LGL 2 V) ∈ L₁ := by
            have hd' : (a : LGL 2 V)⁻¹ ∈ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
              (Subgroup.normalizer (L₁ : Set (LGL 2 V))).inv_mem (hAn₁ a.2)
            simpa using (Subgroup.mem_normalizer_iff.mp hd' m).mp hm
          have h1 : (l₁' a) * ((a : LGL 2 V)⁻¹ * m * (a : LGL 2 V)) * (l₁' a)⁻¹ = m := by
            rw [hpconj₁ _ hdm]; group
          calc (l₁' a)⁻¹ * m * (l₁' a)
              = (l₁' a)⁻¹
                * ((l₁' a) * ((a : LGL 2 V)⁻¹ * m * (a : LGL 2 V)) * (l₁' a)⁻¹)
                * (l₁' a) := by rw [h1]
            _ = (a : LGL 2 V)⁻¹ * m * (a : LGL 2 V) := by group
        have hycent₁ : (a : LGL 2 V) * (l₁' a * l₂' a)⁻¹
            ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
          w183_mem_centralizer_of_factor (hAn₁ a.2) (l₁ a).2 (l₂ a).2
            (fun k hk l hl => (hcomm l hl k hk).symm) hpconj₁inv
        have hpconj₂ : ∀ m ∈ L₂,
            (l₂' a) * m * (l₂' a)⁻¹ = (a : LGL 2 V) * m * (a : LGL 2 V)⁻¹ := by
          intro m hm
          have h2 := congrArg (fun f : MulAut ↥L₂ => f ⟨m, hm⟩) (hl₂ a)
          have h3 := congrArg Subtype.val h2
          rw [MulAut.conj_apply, hc₂ a ⟨m, hm⟩] at h3
          simpa [l₂', Subgroup.coe_mul, Subgroup.coe_inv] using h3
        have hpconj₂inv : ∀ m ∈ L₂,
            (l₂' a)⁻¹ * m * (l₂' a) = (a : LGL 2 V)⁻¹ * m * (a : LGL 2 V) := by
          intro m hm
          have hdm : (a : LGL 2 V)⁻¹ * m * (a : LGL 2 V) ∈ L₂ := by
            have hd' : (a : LGL 2 V)⁻¹ ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
              (Subgroup.normalizer (L₂ : Set (LGL 2 V))).inv_mem (hAn₂ a.2)
            simpa using (Subgroup.mem_normalizer_iff.mp hd' m).mp hm
          have h1 : (l₂' a) * ((a : LGL 2 V)⁻¹ * m * (a : LGL 2 V)) * (l₂' a)⁻¹ = m := by
            rw [hpconj₂ _ hdm]; group
          calc (l₂' a)⁻¹ * m * (l₂' a)
              = (l₂' a)⁻¹
                * ((l₂' a) * ((a : LGL 2 V)⁻¹ * m * (a : LGL 2 V)) * (l₂' a)⁻¹)
                * (l₂' a) := by rw [h1]
            _ = (a : LGL 2 V)⁻¹ * m * (a : LGL 2 V) := by group
        have hycent₂ : (a : LGL 2 V) * (l₂' a * l₁' a)⁻¹
            ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
          w183_mem_centralizer_of_factor (hAn₂ a.2) (l₂ a).2 (l₁ a).2
            (fun k hk l hl => hcomm k hk l hl) hpconj₂inv
        have hcomm_12 : (l₁' a) * (l₂' a) = (l₂' a) * (l₁' a) :=
          hcomm (l₁ a) (l₁ a).2 (l₂ a) (l₂ a).2
        have hycent₂' : (a : LGL 2 V) * (l₁' a * l₂' a)⁻¹
            ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
          rw [hcomm_12]
          exact hycent₂
        have hy1 : (a : LGL 2 V) * (l₁' a * l₂' a)⁻¹ = 1 :=
          hcent _ hyY
            (fun l hl => (Subgroup.mem_centralizer_iff.mp hycent₁ l hl).symm)
            (fun l hl => (Subgroup.mem_centralizer_iff.mp hycent₂' l hl).symm)
        rwa [mul_inv_eq_one] at hy1
      have hD₀eq : ∀ d : LGL 2 V, d ∈ A ↔
          ∃ x : ↥X₁, d = (x : LGL 2 V) * (φ x : LGL 2 V) := by
        intro d
        constructor
        · intro hd
          refine ⟨eX₁ ⟨d, hd⟩, ?_⟩
          have h1 : ((eX₁ ⟨d, hd⟩ : ↥X₁) : LGL 2 V) = l₁' ⟨d, hd⟩ :=
            MonoidHom.ofInjective_apply hl₁'inj
          have h2 : ((φ (eX₁ ⟨d, hd⟩) : ↥X₂) : LGL 2 V) = l₂' ⟨d, hd⟩ := by
            change ((eX₂ (eX₁.symm (eX₁ ⟨d, hd⟩)) : ↥X₂) : LGL 2 V) = l₂' ⟨d, hd⟩
            rw [MulEquiv.symm_apply_apply]
            exact MonoidHom.ofInjective_apply hl₂'inj
          rw [h1, h2]
          exact hdiag ⟨d, hd⟩
        · rintro ⟨x, rfl⟩
          have h1 : (x : LGL 2 V) = l₁' (eX₁.symm x) := by
            rw [← MonoidHom.ofInjective_apply hl₁'inj (x := eX₁.symm x),
              MulEquiv.apply_symm_apply]
          have h2 : (φ x : LGL 2 V) = l₂' (eX₁.symm x) := by
            change ((eX₂ (eX₁.symm x) : ↥X₂) : LGL 2 V) = l₂' (eX₁.symm x)
            rw [MonoidHom.ofInjective_apply hl₂'inj]
          rw [h1, h2, ← hdiag (eX₁.symm x)]
          exact (eX₁.symm x).2
      let nL : ↥L₁ := e₁.symm ⟨n₁, hn₁Inn⟩
      have hnconj : MulAut.conj nL = n₁ := by
        have h1 : ((e₁ nL : ↥Inn₁) : MulAut ↥L₁) = MulAut.conj nL :=
          MonoidHom.ofInjective_apply hconjinj₁
        have h2 : ((e₁ nL : ↥Inn₁) : MulAut ↥L₁) = n₁ := by
          dsimp only [nL]
          rw [MulEquiv.apply_symm_apply]
        rw [h1] at h2
        exact h2
      have hnX : ∀ x ∈ X₁, (nL : LGL 2 V) * x * (nL : LGL 2 V)⁻¹ ∈ X₁ := by
        rintro x ⟨a, rfl⟩
        have hmem₁ : MulAut.conj (l₁ a) ∈ A₁ := by
          rw [hl₁ a]
          exact ⟨a, rfl⟩
        have hmem₂ : n₁ * MulAut.conj (l₁ a) * n₁⁻¹ ∈ A₁ := hn₁norm _ hmem₁
        have hmem₃ : MulAut.conj (n₁ (l₁ a)) ∈ A₁ := by
          rwa [w183_conj_conj n₁ (l₁ a)] at hmem₂
        obtain ⟨a', ha'⟩ := MonoidHom.mem_range.mp hmem₃
        have ha'' : l₁ a' = n₁ (l₁ a) := by
          apply hconjinj₁
          rw [hl₁ a', ha']
        refine ⟨a', ?_⟩
        have heq : (nL : LGL 2 V) * ((l₁ a : ↥L₁) : LGL 2 V) * (nL : LGL 2 V)⁻¹
            = ((n₁ (l₁ a) : ↥L₁) : LGL 2 V) := by
          have h2 := congrArg (fun f : MulAut ↥L₁ => f (l₁ a)) hnconj
          have h3 := congrArg Subtype.val h2
          rw [MulAut.conj_apply] at h3
          simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h3
        change l₁' a'
          = (nL : LGL 2 V) * ((l₁ a : ↥L₁) : LGL 2 V) * (nL : LGL 2 V)⁻¹
        rw [heq, ← ha'']
        rfl
      have hfpf : ∀ x ∈ X₁, x ≠ 1 →
          (nL : LGL 2 V) * x * (nL : LGL 2 V)⁻¹ ≠ x := by
        rintro x ⟨a, rfl⟩ hxne hfix
        have hfix' : ((n₁ (l₁ a) : ↥L₁) : LGL 2 V) = ((l₁ a : ↥L₁) : LGL 2 V) := by
          have h2 := congrArg (fun f : MulAut ↥L₁ => f (l₁ a)) hnconj
          have h3 := congrArg Subtype.val h2
          rw [MulAut.conj_apply] at h3
          rw [← h3]
          simpa [l₁', MonoidHom.comp_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hfix
        have hne : MulAut.conj (l₁ a) ≠ 1 := by
          intro hconj1
          apply hxne
          have hl1 : l₁ a = 1 := hconjinj₁ (by rw [hconj1, map_one])
          have h2 : (l₁ a : LGL 2 V) = 1 := by rw [hl1]; rfl
          simpa [l₁', MonoidHom.comp_apply] using h2
        have hconjfix : n₁ * MulAut.conj (l₁ a) * n₁⁻¹ = MulAut.conj (l₁ a) := by
          rw [w183_conj_conj]
          exact congrArg MulAut.conj (Subtype.val_injective hfix')
        exact (hn₁fpf (MulAut.conj (l₁ a)) (by rw [hl₁ a]; exact ⟨a, rfl⟩) hne) hconjfix
      exact h.false_of_diagonal_member hVfix hnab₁ hnab₂ hL₁Y hcomm hX₁le hX₂le
        hX₁card hX₁sq φ hA hr hD₀eq (n := (nL : LGL 2 V)) nL.2 hnX hfpf
    · exact hfin₂.2 hb₂
  · exact hfin₁.2 hb₁

end CFSG.LocalAnalysis.WeakClosure81

end
