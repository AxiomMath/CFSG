module

public import CFSG.Quasithin.MS93.S512NS0
public import CFSG.Quasithin.MS93.S512NCoc

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512N

section KerMod

variable {Γ : Type*} [Group Γ] {S : Type} [CommGroup S]

theorem map_mul_mul_inv (φ : MulAut S) (x y : S) :
    φ (x * y) * (x * y)⁻¹ = φ x * x⁻¹ * (φ y * y⁻¹) := by
  rw [map_mul, mul_inv_rev]
  ac_rfl

@[expose] def kerMod (ρ : Γ →* MulAut S) {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) : Subgroup Γ where
  carrier := {g | ∀ s, ρ g s * s⁻¹ ∈ S₀}
  one_mem' s := by
    rw [map_one, MulAut.one_apply, mul_inv_cancel]
    exact S₀.one_mem
  mul_mem' {g g'} hg hg' s := by
    have e : ρ (g * g') s * s⁻¹ = ρ g (ρ g' s * s⁻¹) * (ρ g s * s⁻¹) := by
      simp only [map_mul, MulAut.mul_apply, map_inv]
      group
    rw [e]
    exact S₀.mul_mem (hS₀ g _ (hg' s)) (hg s)
  inv_mem' {g} hg s := by
    have h1 := hg (ρ g⁻¹ s)
    have e : ρ g (ρ g⁻¹ s) = s := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [e] at h1
    have := S₀.inv_mem h1
    rwa [mul_inv_rev, inv_inv] at this

variable {ρ : Γ →* MulAut S} {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀)

theorem kerMod_normal : (kerMod ρ hS₀).Normal := by
  refine ⟨fun g hg x s => ?_⟩
  have e2 : ρ x (ρ x⁻¹ s) = s := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have e : ρ (x * g * x⁻¹) s * s⁻¹ = ρ x (ρ g (ρ x⁻¹ s) * (ρ x⁻¹ s)⁻¹) := by
    rw [map_mul (ρ x), map_inv (ρ x), e2]
    simp only [map_mul, MulAut.mul_apply]
  rw [e]
  exact hS₀ x _ (hg _)

theorem mem_kerMod_of_eq_one {g : Γ} (hg : ρ g = 1) : g ∈ kerMod ρ hS₀ := fun s => by
  rw [hg, MulAut.one_apply, mul_inv_cancel]
  exact S₀.one_mem

end KerMod

section Fix

variable {Γ : Type*} [Group Γ] {S₀ : Type} [CommGroup S₀] {F : Type} [Field F]
  {r : Γ →* MulAut S₀} {a : Γ →* MSP.Sp4 F}

theorem card_fixV_map_eq {θ : S₀ ≃* Multiplicative (MSP.V4 F)}
    (hθ : ∀ (g : Γ) (s : S₀), Multiplicative.toAdd (θ (r g s)) =
      MSP.mat (a g) *ᵥ Multiplicative.toAdd (θ s)) (H : Subgroup Γ) :
    Nat.card (fixV (H.map r)) = Nat.card (MSP.fixSp (H.map a)) := by
  have hiff : ∀ s : S₀, s ∈ fixV (H.map r) ↔
      Multiplicative.toAdd (θ s) ∈ MSP.fixSp (H.map a) := by
    intro s
    rw [mem_fixV, MSP.mem_fixSp]
    constructor
    · rintro hs _ ⟨g, hg, rfl⟩
      rw [← hθ, hs _ ⟨g, hg, rfl⟩]
    · rintro hs _ ⟨g, hg, rfl⟩
      have h1 := hs (a g) ⟨g, hg, rfl⟩
      rw [← hθ] at h1
      exact θ.injective (Multiplicative.toAdd.injective h1)
  exact Nat.card_congr
    { toFun := fun s => ⟨Multiplicative.toAdd (θ s), (hiff s).1 s.2⟩
      invFun := fun v => ⟨θ.symm (Multiplicative.ofAdd v), (hiff _).2 (by simp)⟩
      left_inv := fun s => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }

theorem card_eq_of_coord [Finite F] (θ : S₀ ≃* Multiplicative (MSP.V4 F)) :
    Nat.card S₀ = Nat.card F ^ 4 := by
  rw [Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd), MSP.card_V4]

end Fix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace NatHyp

variable {h : PUHyp M T L} {V E Z Y : Subgroup (puAmalgam h.le).Universal}
  (hn : NatHyp h k V E Z Y)
  {S : Type} [CommGroup S] {p : ↥V →* S}
  {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
  (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
  {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀)

include hn in
theorem exists_mem_E (hk : 1 ≤ k) : ∃ e : ↥(stab (puAmalgam h.le) (baseA _)),
    (e : (puAmalgam h.le).Universal) ∈ E ∧
      (e : (puAmalgam h.le).Universal) ∉ Qv _ (baseA (puAmalgam h.le)) := by
  by_contra hcon
  push Not at hcon
  have hle : E ≤ Qv _ (baseA (puAmalgam h.le)) := fun x hx => hcon ⟨x, hn.es hx⟩ hx
  have h1 := hn.eq
  rw [Subgroup.relIndex_eq_one.2 hle] at h1
  have : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  omega

include hn hs in
theorem card_map_E {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    {F' : Type} [Field F'] {a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F'}
    (hker : ∀ g, a' g = 1 ↔ restrict ρ hS₀ g = 1) :
    Nat.card ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map a') = 2 ^ k := by
  have hk : a'.ker = (restrict ρ hS₀).ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker]
  rw [← Subgroup.relIndex_ker, hk, Subgroup.relIndex_ker]
  exact hn.card_map_restrict hs hS₀ hne hmin

include hn hs in
theorem exists_point (hk : 1 ≤ k) {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    {F' : Type} [Field F'] [Fintype F'] (hcard : Fintype.card F' = 2 ^ k)
    {a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F'}
    {θ : ↥S₀ ≃* Multiplicative (MSP.V4 F')}
    (hθ : ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : ↥S₀),
      Multiplicative.toAdd (θ (restrict ρ hS₀ g s)) =
        MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s))
    (hker : ∀ g, a' g = 1 ↔ restrict ρ hS₀ g = 1) :
    Module.finrank F' (MSP.fixSp ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map a')) = 3 ∧
      ∃ p : Submodule F' (MSP.V4 F'), MSP.IsPoint p ∧
        (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map a' = MSP.xPoint p := by
  set A := (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map a' with hA
  have hF' : Nat.card F' = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcard]
  have hcA : Nat.card A = 2 ^ k := hn.card_map_E hs hS₀ hne hmin hker
  have h1 := hn.card_le_fixV_restrict hs hS₀
  rw [card_fixV_map_eq hθ, card_eq_of_coord θ, MSP.card_fixSp, hF'] at h1
  have hq : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  set d := Module.finrank F' (MSP.fixSp A)
  have hd3 : 3 ≤ d := by
    have h2 : (2 ^ k) ^ 4 ≤ (2 ^ k) ^ (d + 1) := by
      calc (2 ^ k) ^ 4 ≤ 2 ^ k * (2 ^ k) ^ d := h1
        _ = (2 ^ k) ^ (d + 1) := by ring
    have := (Nat.pow_le_pow_iff_right hq).1 h2
    omega
  have hle4 : d ≤ 4 := by
    have := Submodule.finrank_le (MSP.fixSp A)
    simpa using this
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcA
    omega
  have hd : d = 3 := by
    by_contra hd
    have h4 : d = 4 := by omega
    have htop : MSP.fixSp A = ⊤ := Submodule.eq_top_of_finrank_eq (by
      show d = _
      rw [h4]; simp)
    exact hA1 (MSP.fixSp_eq_top_iff.1 htop)
  refine ⟨hd, ?_⟩
  obtain ⟨p, hp, -, hAp⟩ := MSP.exists_point_of_finrank_fixSp_three hd
  refine ⟨p, hp, Subgroup.eq_of_le_of_card_ge hAp ?_⟩
  rw [MSP.card_xPoint hp, hcA, hF']

include hn hs in
theorem fixV_sup_eq_top (hk : 1 ≤ k) {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    {F' : Type} [Field F'] [Fintype F'] (hcard : Fintype.card F' = 2 ^ k)
    {a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F'}
    {θ : ↥S₀ ≃* Multiplicative (MSP.V4 F')}
    (hθ : ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : ↥S₀),
      Multiplicative.toAdd (θ (restrict ρ hS₀ g s)) =
        MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s))
    (hker : ∀ g, a' g = 1 ↔ restrict ρ hS₀ g = 1) :
    fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) ⊔ S₀ = ⊤ := by
  have := hn.toSecHyp.finite_S hs
  set C := fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) with hC
  have hF' : Nat.card F' = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hd3, -⟩ := hn.exists_point hs hk hS₀ hne hmin hcard hθ hker
  have hfix : fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map (restrict ρ hS₀)) =
      C.subgroupOf S₀ := by
    ext s
    rw [Subgroup.mem_subgroupOf, mem_fixV, mem_fixV]
    constructor
    · rintro hsf _ ⟨e, he, rfl⟩
      have := hsf _ ⟨e, he, rfl⟩
      rw [← coe_restrict_apply ρ hS₀, this]
    · rintro hsf _ ⟨e, he, rfl⟩
      apply Subtype.ext
      rw [coe_restrict_apply]
      exact hsf _ ⟨e, he, rfl⟩
  have hcC : Nat.card (C.subgroupOf S₀) = (2 ^ k) ^ 3 := by
    rw [← hfix, card_fixV_map_eq hθ, MSP.card_fixSp, hd3, hF']
  have hC0 : C.relIndex S₀ = 2 ^ k := by
    have h1 := (C.subgroupOf S₀).card_mul_index
    rw [card_eq_of_coord θ, hF', hcC] at h1
    have h2 : (2 ^ k) ^ 3 * (C.subgroupOf S₀).index = (2 ^ k) ^ 3 * 2 ^ k := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hidx := hn.index_fixV_le hs
  have h1 : C.relIndex (S₀ ⊔ C) = 2 ^ k := by
    rw [Subgroup.relIndex_sup_right]
    exact hC0
  have h2 := Subgroup.relIndex_mul_index (le_sup_right : C ≤ S₀ ⊔ C)
  rw [h1] at h2
  have hidx1 : (S₀ ⊔ C).index = 1 := by
    have hpos : 0 < (S₀ ⊔ C).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    have : 2 ^ k * (S₀ ⊔ C).index ≤ 2 ^ k * 1 := by rw [h2, mul_one]; exact hidx
    have := Nat.le_of_mul_le_mul_left this (by positivity)
    omega
  rw [sup_comm]
  exact Subgroup.index_eq_one.1 hidx1

include hn hs in
theorem le_kerMod_E (hk : 1 ≤ k) {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    {F' : Type} [Field F'] [Fintype F'] (hcard : Fintype.card F' = 2 ^ k)
    {a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F'}
    {θ : ↥S₀ ≃* Multiplicative (MSP.V4 F')}
    (hθ : ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : ↥S₀),
      Multiplicative.toAdd (θ (restrict ρ hS₀ g s)) =
        MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s))
    (hker : ∀ g, a' g = 1 ↔ restrict ρ hS₀ g = 1) :
    E.subgroupOf (stab (puAmalgam h.le) (baseA _)) ≤ kerMod ρ hS₀ := by
  intro e he s
  have hs' : s ∈ fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) ⊔ S₀ := by
    rw [hn.fixV_sup_eq_top hs hk hS₀ hne hmin hcard hθ hker]
    exact Subgroup.mem_top s
  obtain ⟨c, hc, t, ht, rfl⟩ := Subgroup.mem_sup.1 hs'
  rw [map_mul_mul_inv, hc _ ⟨e, he, rfl⟩, mul_inv_cancel, one_mul]
  exact S₀.mul_mem (hS₀ e t ht) (S₀.inv_mem ht)

include hn in
theorem mem_kerMod_of_puTrans (hk : 1 ≤ k) {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀)
    (hE : E.subgroupOf (stab (puAmalgam h.le) (baseA _)) ≤ kerMod ρ hS₀)
    {g : ↥(stab (puAmalgam h.le) (baseA _))}
    (hg : (g : (puAmalgam h.le).Universal) ∈ puTrans h.le L (baseA _)) : g ∈ kerMod ρ hS₀ := by
  have hKn := kerMod_normal hS₀ (ρ := ρ)
  set K' : Subgroup ↥M := (kerMod ρ hS₀).comap (eM h.le) with hK'
  have hK'n : K'.Normal := hKn.comap _
  set D : Subgroup G := K'.map M.subtype with hD
  have hDM : D ≤ M := Subgroup.map_subtype_le _
  have hDsub : D.subgroupOf M = K' := Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hDn : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).1 (by rw [hDsub]; exact hK'n)
  have hLD : L ≤ D := by
    by_contra hLD
    obtain ⟨e, heE, heQ⟩ := hn.exists_mem_E hk
    obtain ⟨m, rfl⟩ := eM_surjective h.le e
    have hmD : (m : G) ∈ D := ⟨m, hE (Subgroup.mem_subgroupOf.2 heE), rfl⟩
    have hm2 : ∃ e : ℕ, (m : G) ^ 2 ^ e = 1 := by
      refine ⟨1, ?_⟩
      have h1 : (eM h.le m : (puAmalgam h.le).Universal) ^ 2 = 1 := hn.ee.2 _ heE
      have h2 : eM h.le (m ^ 2) = 1 := by
        apply Subtype.ext
        rw [map_pow, Subgroup.coe_pow]
        exact h1
      have h3 : m ^ 2 = 1 := (eM_injective h.le) (h2.trans (map_one _).symm)
      simpa using congrArg Subtype.val h3
    have hO := h.mem_pCoreOf_of_rel hDn hLD m.2 hm2 fun l hl => by
      have hlm : l * (m : G)⁻¹ * l⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.1 (hDn (h.L_le hl)) _).1 (D.inv_mem hmD)
      have e : ⁅(m : G), l⁆ = (m : G) * (l * (m : G)⁻¹ * l⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact D.mul_mem hmD hlm
    apply heQ
    rw [coe_eM, S5B.qv_baseA_eq h]
    exact (ofA_mem_imM_iff h.le m).2 hO
  rw [S5B.puTrans_L_baseA h] at hg
  obtain ⟨l, hl, hgl⟩ := hg
  have hgl' : g = eM h.le l := Subtype.ext hgl.symm
  obtain ⟨l', hl', hll'⟩ := hLD (Subgroup.mem_subgroupOf.1 hl)
  have : l' = l := Subtype.ext hll'
  rw [hgl', ← this]
  exact hl'

include hn hs in
theorem map_Z_sup_eq_top {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀)
    (hL : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)),
      (g : (puAmalgam h.le).Universal) ∈ puTrans h.le L (baseA _) → g ∈ kerMod ρ hS₀) :
    (Z.subgroupOf V).map p ⊔ S₀ = ⊤ := by
  set P : Subgroup (puAmalgam h.le).Universal := (S₀.comap p).map V.subtype with hP
  have hPV : P ≤ V := Subgroup.map_subtype_le _
  have hVL : ⁅V, puTrans h.le L (baseA _)⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have hlst : l ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hl
    have hlv : l * v⁻¹ * l⁻¹ ∈ V := S36E.conj_mem hn.vn hlst (V.inv_mem hv)
    have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    have hcV : ⁅v, l⁆ ∈ V := by
      rw [e]
      exact V.mul_mem hv hlv
    refine ⟨⟨⁅v, l⁆, hcV⟩, ?_, rfl⟩
    have e2 : (⟨⁅v, l⁆, hcV⟩ : ↥V) = ⟨v, hv⟩ * ⟨l * v⁻¹ * l⁻¹, hlv⟩ := Subtype.ext e
    have h1 : ρ ⟨l, hlst⟩ (p ⟨v⁻¹, V.inv_mem hv⟩) = p ⟨l * v⁻¹ * l⁻¹, hlv⟩ :=
      hs.conj ⟨l, hlst⟩ ⟨v⁻¹, V.inv_mem hv⟩ hlv
    have h1' : p ⟨l * v⁻¹ * l⁻¹, hlv⟩ = (ρ ⟨l, hlst⟩ (p ⟨v, hv⟩))⁻¹ := by
      rw [← h1, ← map_inv (ρ ⟨l, hlst⟩), ← map_inv p]
      rfl
    have h2 := S₀.inv_mem (hL ⟨l, hlst⟩ hl (p ⟨v, hv⟩))
    rw [mul_inv_rev, inv_inv] at h2
    rw [SetLike.mem_coe, Subgroup.mem_comap, e2, map_mul, h1']
    exact h2
  have hle : V ≤ Z ⊔ P := hn.gen.trans (sup_le_sup_left hVL _)
  rw [eq_top_iff]
  intro s _
  obtain ⟨v, rfl⟩ := hs.surj s
  have hv' : v ∈ (Z ⊔ P).subgroupOf V := Subgroup.mem_subgroupOf.2 (hle v.2)
  rw [Subgroup.subgroupOf_sup hn.zv hPV] at hv'
  have h1 := Subgroup.mem_map_of_mem p hv'
  rw [Subgroup.map_sup] at h1
  have hPS : (P.subgroupOf V).map p ≤ S₀ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.1 hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  exact (sup_le_sup_left hPS _) h1

include hn hs in
theorem rho_eq_one_of_restrict {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    (hall : ∀ g, g ∈ kerMod ρ hS₀) {g : ↥(stab (puAmalgam h.le) (baseA _))}
    (hg : restrict ρ hS₀ g = 1) : ρ g = 1 := by
  have := S310.finite_stab_of_isMVtx h (isMVtx_baseA (puAmalgam h.le))
  have hsq : ρ g * ρ g = 1 := by
    refine MulEquiv.ext fun s => ?_
    set d := ρ g s * s⁻¹ with hd
    have hdS : d ∈ S₀ := hall g s
    have hgd : ρ g d = d := by
      have := congrArg (fun φ : MulAut ↥S₀ => ((φ ⟨d, hdS⟩ : ↥S₀) : S)) hg
      simpa [coe_restrict_apply] using this
    have hsd : ρ g s = d * s := by rw [hd, inv_mul_cancel_right]
    calc (ρ g * ρ g) s = ρ g (ρ g s) := rfl
      _ = d * (d * s) := by rw [hsd, map_mul, hgd, hsd]
      _ = s := by rw [← mul_assoc, ← sq, hn.toSecHyp.sq_eq_one hs d, one_mul]
      _ = (1 : MulAut S) s := rfl
  obtain ⟨e, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hgm : restrict ρ hS₀ (g ^ m) = 1 := by rw [map_pow, hg, one_pow]
  have h2 : ∃ e' : ℕ, ((g ^ m : ↥(stab (puAmalgam h.le) (baseA _))) :
      (puAmalgam h.le).Universal) ^ 2 ^ e' = 1 := by
    refine ⟨e, ?_⟩
    rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one, Subgroup.coe_one]
  have hQ := hn.toSecHyp.mem_qv_of_restrict_eq_one hs hS₀ hne hmin hgm h2
  have h3 := hn.rho_eq_one_of_mem_qv hs _ hQ
  obtain ⟨j, rfl⟩ := hm
  rw [map_pow, pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at h3
  exact h3

include hn hs in
theorem eq_top_of_two_le (hd : S5.IsSp4Data M T L k F a) (hk2 : 2 ≤ k) {S₀ : Subgroup S}
    (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    {F' : Type} [Field F'] [Fintype F'] (hcard : Fintype.card F' = 2 ^ k)
    {a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F'} (ha' : Function.Surjective a')
    {θ : ↥S₀ ≃* Multiplicative (MSP.V4 F')}
    (hθ : ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : ↥S₀),
      Multiplicative.toAdd (θ (restrict ρ hS₀ g s)) =
        MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s))
    (hker : ∀ g, a' g = 1 ↔ restrict ρ hS₀ g = 1) : S₀ = ⊤ := by
  have hk1 : 1 ≤ k := by omega
  have := charP_of_card_eq_prime_pow hcard
  have hF : 2 < Nat.card F' := by
    rw [Nat.card_eq_fintype_card, hcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  obtain ⟨-, p', hp', hEp⟩ := hn.exists_point hs hk1 hS₀ hne hmin hcard hθ hker
  have hsup := hn.fixV_sup_eq_top hs hk1 hS₀ hne hmin hcard hθ hker
  have hE := hn.le_kerMod_E hs hk1 hS₀ hne hmin hcard hθ hker
  have hL : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)),
      (g : (puAmalgam h.le).Universal) ∈ puTrans h.le L (baseA _) → g ∈ kerMod ρ hS₀ :=
    fun g hg => hn.mem_kerMod_of_puTrans hk1 hS₀ hE hg
  have hall : ∀ g, g ∈ kerMod ρ hS₀ := by
    intro g
    obtain ⟨m, rfl⟩ := eM_surjective h.le g
    have hLn : (L.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
    have hsup' : L.subgroupOf M ⊔ (pCoreOf 2 M).subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup h.L_le (pCoreOf_le' M), ← S5B.eq_sup_pCoreOf h hd hk2,
        Subgroup.subgroupOf_self]
    have hmem : m ∈ L.subgroupOf M ⊔ (pCoreOf 2 M).subgroupOf M := by
      rw [hsup']; exact Subgroup.mem_top _
    obtain ⟨l, hl, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    rw [map_mul]
    refine (kerMod ρ hS₀).mul_mem (hL _ ?_) (mem_kerMod_of_eq_one hS₀ ?_)
    · rw [S5B.puTrans_L_baseA h]
      exact ⟨l, hl, rfl⟩
    · refine hn.rho_eq_one_of_mem_qv hs _ ?_
      rw [coe_eM, S5B.qv_baseA_eq h]
      exact (ofA_mem_imM_iff h.le o).2 (Subgroup.mem_subgroupOf.1 ho)
  have hfix : ∀ s : S, (∀ g, ρ g s = s) → s = 1 := fun s hs' =>
    hn.toSecHyp.eq_one_of_fixed hs s fun l _ => hs' l
  rw [eq_top_iff]
  intro s _
  have hs' : s ∈ fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) ⊔ S₀ := by
    rw [hsup]
    exact Subgroup.mem_top s
  obtain ⟨c, hc, t, ht, rfl⟩ := Subgroup.mem_sup.1 hs'
  refine S₀.mul_mem ?_ ht
  refine mem_of_rigid hS₀ hcard hk1 ha' hθ hfix (fun g => hall g c)
    (fun g hg => by rw [hn.rho_eq_one_of_restrict hs hS₀ hne hmin hall ((hker g).1 hg)]; rfl)
    (J := E.subgroupOf (stab (puAmalgam h.le) (baseA _))) ?_ (fun j hj => hc _ ⟨j, hj, rfl⟩)
  rw [hEp]
  exact rigid_xPoint hF hp'

end NatHyp

end S512N

end CFSG.Quasithin.MS93
