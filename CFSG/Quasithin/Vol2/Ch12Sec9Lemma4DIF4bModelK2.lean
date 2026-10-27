module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelK1
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelO

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

theorem le_pCore_of_normal {G : Type*} [Group G] {p : ℕ} {N : Subgroup G} (hN : N.Normal)
    (hp : IsPGroup p N) : N ≤ CFSG.pCore p G :=
  le_sSup (show N ∈ {K : Subgroup G | K.Normal ∧ IsPGroup p K} from ⟨hN, hp⟩)

theorem pCoreOf_conj_mem {G : Type*} [Group G] (p : ℕ) (P : Subgroup G) (g : G)
    (hg : ∀ x ∈ P, g * x * g⁻¹ ∈ P) (hg' : ∀ x ∈ P, g⁻¹ * x * g ∈ P) :
    ∀ n ∈ CFSG.Open.pCoreOf p P, g * n * g⁻¹ ∈ CFSG.Open.pCoreOf p P := by
  intro n hn
  rw [CFSG.Open.pCoreOf, Subgroup.mem_map] at hn
  obtain ⟨x, hx, rfl⟩ := hn
  let φ : P →* P :=
    { toFun := fun y => ⟨g * (y : G) * g⁻¹, hg y y.2⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by ext; simp [mul_assoc] }
  let ψ : P →* P :=
    { toFun := fun y => ⟨g⁻¹ * (y : G) * g, hg' y y.2⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by ext; simp [mul_assoc] }
  have hφψ : ∀ y, φ (ψ y) = y := fun y => by
    ext; simp [φ, ψ, mul_assoc]
  have hψφ : ∀ y, ψ (φ y) = y := fun y => by
    ext; simp [φ, ψ, mul_assoc]
  have hφinj : Function.Injective φ := fun a b h => by
    have := congrArg ψ h
    rwa [hψφ, hψφ] at this
  have hN : (CFSG.pCore p P).Normal := CFSG.pCore_normal (p := p) (G := P)
  have hMnorm : ((CFSG.pCore p P).map φ).Normal := by
    constructor
    intro m hm y
    obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.1 hm
    have heq : y * φ n' * y⁻¹ = φ (ψ y * n' * (ψ y)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hφψ]
    rw [heq]
    exact Subgroup.mem_map_of_mem φ (hN.conj_mem n' hn' (ψ y))
  have hMp : IsPGroup p ((CFSG.pCore p P).map φ) :=
    (CFSG.pCore_isPGroup (p := p) (G := P)).of_equiv ((CFSG.pCore p P).equivMapOfInjective φ hφinj)
  have hsub : (CFSG.pCore p P).map φ ≤ CFSG.pCore p P := le_pCore_of_normal hMnorm hMp
  rw [CFSG.Open.pCoreOf, Subgroup.mem_map]
  exact ⟨φ x, hsub (Subgroup.mem_map_of_mem φ hx), rfl⟩

theorem sub_self_VM : ∀ x : VM, x - x = 0 := by decide +kernel

theorem neg_sub_VM : ∀ x y : VM, -(x - y) = y - x := by decide +kernel

@[expose] def Kw : Subgroup (VM ≃ₗ[ZMod 2] VM) where
  carrier := {γ | γ ∈ GM ∧ γ e0 = e0 ∧
    ∀ x, bM x e0 = 0 → γ x - x ∈ Submodule.span (ZMod 2) {e0}}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨GM.mul_mem ha.1 hb.1, ?_, ?_⟩
    · show a (b e0) = e0
      rw [hb.2.1, ha.2.1]
    · intro x hx
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 (hb.2.2 x hx)
      have h1 : (a * b) x - x = a (b x - x) + (a x - x) := by
        show a (b x) - x = a (b x - x) + (a x - x)
        rw [map_sub a (b x) x]
        abel
      rw [h1, ← hs, map_smul, ha.2.1]
      exact Submodule.add_mem _ (Submodule.smul_mem _ s (Submodule.mem_span_singleton_self e0))
        (ha.2.2 x hx)
  one_mem' := ⟨GM.one_mem, rfl, fun x _ => by
    show x - x ∈ _
    rw [sub_self_VM]
    exact Submodule.zero_mem _⟩
  inv_mem' := fun {a} ha => by
    refine ⟨GM.inv_mem ha.1, ?_, ?_⟩
    · show a.symm e0 = e0
      rw [LinearEquiv.symm_apply_eq]
      exact ha.2.1.symm
    · intro x hx
      have hsy : bM (a.symm x) e0 = 0 := by
        have h := bM_of_GM ha.1 (a.symm x) e0
        rw [a.apply_symm_apply, ha.2.1] at h
        rw [← h]
        exact hx
      have h2 := ha.2.2 (a.symm x) hsy
      rw [a.apply_symm_apply] at h2
      show a.symm x - x ∈ _
      rw [← neg_sub_VM]
      exact Submodule.neg_mem _ h2

theorem mem_Kw_iff (γ : VM ≃ₗ[ZMod 2] VM) : γ ∈ Kw ↔
    γ ∈ GM ∧ γ e0 = e0 ∧ ∀ x, bM x e0 = 0 → γ x - x ∈ Submodule.span (ZMod 2) {e0} := Iff.rfl

theorem Kw_conj_mem {h γ : VM ≃ₗ[ZMod 2] VM} (hh : h ∈ Hm) (hγ : γ ∈ Kw) :
    h * γ * h⁻¹ ∈ Kw := by
  refine ⟨GM.mul_mem (GM.mul_mem hh.1 hγ.1) (GM.inv_mem hh.1), ?_, ?_⟩
  · have hs : h.symm e0 = e0 := by
      rw [LinearEquiv.symm_apply_eq]
      exact hh.2.symm
    show h (γ (h.symm e0)) = e0
    rw [hs, hγ.2.1, hh.2]
  · intro x hx
    have hsy : bM (h.symm x) e0 = 0 := by
      have hh' := bM_of_GM hh.1 (h.symm x) e0
      rw [h.apply_symm_apply, hh.2] at hh'
      rw [← hh']
      exact hx
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 (hγ.2.2 (h.symm x) hsy)
    show h (γ (h.symm x)) - x ∈ _
    have h1 : h (γ (h.symm x)) - x = h (γ (h.symm x) - h.symm x) := by
      rw [map_sub h, LinearEquiv.apply_symm_apply] <;> rfl
    rw [h1, ← hs, map_smul, hh.2]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self e0)

theorem EL_mem_Kw (c : VM) (hc : inU c) : EL c hc ∈ Kw := by
  refine ⟨EL_mem_GM c hc, EL_e0 c hc, fun x hx => ?_⟩
  have hx' : x (Sum.inr 0) = 0 := by
    rw [← bM_e0_right x]
    exact hx
  show EL c hc x - x ∈ _
  rw [EL_apply_of_inr c hc x hx']
  have h2 : x + bM x c • e0 - x = bM x c • e0 := by abel
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e0)

theorem Kw_eq_EL {γ : VM ≃ₗ[ZMod 2] VM} (hγ : γ ∈ Kw) :
    ∃ c : VM, ∃ hc : inU c, γ = EL c hc :=
  kw_char γ hγ.1 hγ.2.1 hγ.2.2

theorem EL_inj_aux : ∀ c d : VM, inU c → inU d →
    qM c • e0 + f0 + c = qM d • e0 + f0 + d → c = d := by
  decide +kernel

theorem Kw_card : Nat.card Kw = 16 := by
  let f : {c : VM // inU c} → Kw := fun c => ⟨EL c.1 c.2, EL_mem_Kw c.1 c.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c d h
      have h' : EL c.1 c.2 = EL d.1 d.2 := congrArg Subtype.val h
      have h2 : EL c.1 c.2 f0 = EL d.1 d.2 f0 := by rw [h']
      rw [EL_f0, EL_f0] at h2
      exact Subtype.ext (EL_inj_aux c.1 d.1 c.2 d.2 h2)
    · intro γ
      obtain ⟨c, hc, hγ⟩ := Kw_eq_EL γ.2
      exact ⟨⟨c, hc⟩, Subtype.ext hγ.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  decide +kernel

theorem EL_mem_stabM (c : VM) (hc : inU c) : EL c hc ∈ stabM Sm := by
  have key : ∀ v : VM, v ∈ Sm → EL c hc v ∈ Sm := by
    intro v hv
    rw [mem_Sm_iff] at hv ⊢
    intro i
    have h0 : v (Sum.inr 0) = 0 := hv 0
    rw [EL_apply_of_inr c hc v h0]
    simp [e0, mkV, hv i]
  rw [mem_stabM_iff]
  intro v
  constructor
  · intro hv
    exact key v hv
  · intro hv
    have h := key (EL c hc v) hv
    exact (EL_invol_aux c hc v) ▸ h
where
  EL_invol_aux (c : VM) (hc : inU c) (v : VM) : EL c hc (EL c hc v) = v := Eev_involutive c v hc

theorem Kw_le_Omega {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) : Kw ≤ Ω := by
  intro γ hγ
  obtain ⟨c, hc, rfl⟩ := Kw_eq_EL hγ
  exact stab_le_Omega hΩG hrel (EL_mem_GM c hc) (EL_mem_stabM c hc)

theorem Kw_le_pCoreOf {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) : Kw ≤ CFSG.Open.pCoreOf 2 (Hm ⊓ Ω) := by
  have hKP : Kw ≤ Hm ⊓ Ω := fun γ hγ =>
    Subgroup.mem_inf.2 ⟨⟨hγ.1, hγ.2.1⟩, Kw_le_Omega hΩG hrel hγ⟩
  have hMnorm : (Kw.subgroupOf (Hm ⊓ Ω)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgH : (g : VM ≃ₗ[ZMod 2] VM) ∈ Hm := (Subgroup.mem_inf.1 g.2).1
    exact Kw_conj_mem hgH hn
  have hcard : Nat.card (Kw.subgroupOf (Hm ⊓ Ω)) = 2 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv, Kw_card] <;> norm_num
  have hMp : IsPGroup 2 (Kw.subgroupOf (Hm ⊓ Ω)) := IsPGroup.of_card hcard
  have hle : Kw.subgroupOf (Hm ⊓ Ω) ≤ CFSG.pCore 2 ↥(Hm ⊓ Ω) := le_pCore_of_normal hMnorm hMp
  intro γ hγ
  rw [CFSG.Open.pCoreOf, Subgroup.mem_map]
  exact ⟨⟨γ, hKP hγ⟩, hle (Subgroup.mem_subgroupOf.2 hγ), rfl⟩

end CFSG.Quasithin.H13.C1294.Model

end
