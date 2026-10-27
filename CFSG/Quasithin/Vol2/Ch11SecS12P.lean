module

public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.Quasithin.Vol2.Ch11SecD557NatA
public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open hiding StatedSL
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix
open scoped MatrixGroups

section Centralizer

variable {F : Type} [Field F] [CharP F 2]

theorem eq_one_of_commute_range {y : PGL3 F}
    (hy : ∀ r ∈ (thetaP F).range, y * r = r * y) : y = 1 := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective y
  rw [ProjGenLinGroup.mk_eq_one]
  refine GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    (Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_)
  let s : SpecialLinearGroup (Fin 3) F := ⟨t.toMatrix, t.det⟩
  have hr : ProjGenLinGroup.mk (SpecialLinearGroup.toGL s) ∈ (thetaP F).range :=
    ⟨proj 3 F s, thetaP_proj s⟩
  have h1 := hy _ hr
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h1
  obtain ⟨c, hc⟩ := h1
  have hc' := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar,
    SpecialLinearGroup.coe_GL_coe_matrix] at hc'
  have hs : (s : Matrix (Fin 3) (Fin 3) F) = t.toMatrix := rfl
  rw [hs] at hc'
  have E : t.toMatrix * (g : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • ((g : Matrix (Fin 3) (Fin 3) F) * t.toMatrix) := by
    rw [← hc', Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
  have hs2 : t.toMatrix * t.toMatrix = 1 := by
    show transvection t.i t.j t.c * transvection t.i t.j t.c = 1
    rw [transvection_mul_transvection_same (h := t.hij), CharTwo.add_self_eq_zero,
      transvection_zero]
  have key : (g : Matrix (Fin 3) (Fin 3) F) = ((c : F) * c) • (g : Matrix (Fin 3) (Fin 3) F) :=
    calc (g : Matrix (Fin 3) (Fin 3) F)
        = (t.toMatrix * t.toMatrix) * (g : Matrix (Fin 3) (Fin 3) F) := by rw [hs2, Matrix.one_mul]
      _ = t.toMatrix * (t.toMatrix * (g : Matrix (Fin 3) (Fin 3) F)) := Matrix.mul_assoc _ _ _
      _ = t.toMatrix * ((c : F) • ((g : Matrix (Fin 3) (Fin 3) F) * t.toMatrix)) := by rw [E]
      _ = (c : F) • ((t.toMatrix * (g : Matrix (Fin 3) (Fin 3) F)) * t.toMatrix) := by
          rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (c : F) • (((c : F) • ((g : Matrix (Fin 3) (Fin 3) F) * t.toMatrix)) * t.toMatrix) := by
          rw [E]
      _ = ((c : F) * c) • ((g : Matrix (Fin 3) (Fin 3) F) * (t.toMatrix * t.toMatrix)) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      _ = ((c : F) * c) • (g : Matrix (Fin 3) (Fin 3) F) := by rw [hs2, Matrix.mul_one]
  have hcc : (c : F) * c = 1 := by
    have h4 := congrArg (· * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) key
    simp only [Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one] at h4
    have h5 := congrFun (congrFun h4 0) 0
    simpa using h5.symm
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc1 : (c : F) = 1 := by
    have h6 : ((c : F) + 1) * ((c : F) + 1) = 0 := by linear_combination hcc + ((c : F) + 1) * h2
    have h7 := mul_self_eq_zero.mp h6
    linear_combination h7 - h2
  rw [hc1, one_smul] at E
  exact E

end Centralizer

section Faithful

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def centSec (Γ V Z : Subgroup G) (hΓV : Γ ≤ Subgroup.normalizer (V : Set G))
    (hΓZ : Γ ≤ Subgroup.normalizer (Z : Set G)) : Subgroup ↥Γ where
  carrier := {δ | ∀ v ∈ V, (δ : G) * v * (δ : G)⁻¹ * v⁻¹ ∈ Z}
  one_mem' := fun v _ => by simp
  mul_mem' := fun {δ₁ δ₂} h₁ h₂ v hv => by
    have e : ((δ₁ * δ₂ : ↥Γ) : G) * v * ((δ₁ * δ₂ : ↥Γ) : G)⁻¹ * v⁻¹ =
        (δ₁ : G) * ((δ₂ : G) * v * (δ₂ : G)⁻¹ * v⁻¹) * (δ₁ : G)⁻¹ *
          ((δ₁ : G) * v * (δ₁ : G)⁻¹ * v⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hΓZ δ₁.2) _).mp (h₂ v hv)) (h₁ v hv)
  inv_mem' := fun {δ} h v hv => by
    have hw : (δ : G)⁻¹ * v * (δ : G)⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hΓV (Γ.inv_mem δ.2)) v).mp hv
    have h1 := h _ hw
    have e : ((δ⁻¹ : ↥Γ) : G) * v * ((δ⁻¹ : ↥Γ) : G)⁻¹ * v⁻¹ =
        ((δ : G) * ((δ : G)⁻¹ * v * (δ : G)⁻¹⁻¹) * (δ : G)⁻¹ *
          ((δ : G)⁻¹ * v * (δ : G)⁻¹⁻¹)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]
      group
    rw [e]
    exact Z.inv_mem h1

theorem centSec_normal (Γ V Z : Subgroup G) (hΓV : Γ ≤ Subgroup.normalizer (V : Set G))
    (hΓZ : Γ ≤ Subgroup.normalizer (Z : Set G)) : (centSec Γ V Z hΓV hΓZ).Normal := by
  refine ⟨fun δ h g v hv => ?_⟩
  have hw : (g : G)⁻¹ * v * (g : G)⁻¹⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hΓV (Γ.inv_mem g.2)) v).mp hv
  have h1 := h _ hw
  have e : ((g * δ * g⁻¹ : ↥Γ) : G) * v * ((g * δ * g⁻¹ : ↥Γ) : G)⁻¹ * v⁻¹ =
      (g : G) * ((δ : G) * ((g : G)⁻¹ * v * (g : G)⁻¹⁻¹) * (δ : G)⁻¹ *
        ((g : G)⁻¹ * v * (g : G)⁻¹⁻¹)⁻¹) * (g : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hΓZ g.2) _).mp h1

theorem ker_iff (hF : Nat.card F = 4) {Γ V Z : Subgroup G} (α : ↥Γ →* PGL3 F)
    (hα : Function.Surjective α) (hΓV : Γ ≤ Subgroup.normalizer (V : Set G))
    (hΓZ : Γ ≤ Subgroup.normalizer (Z : Set G))
    (h3 : ∀ γ : ↥Γ, α γ = 1 → ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z)
    (h4 : ∃ γ : ↥Γ, α γ ∈ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆ ∧
      ∃ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∉ Z) (γ : ↥Γ) :
    α γ = 1 ↔ ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z := by
  refine ⟨h3 γ, fun hγ => ?_⟩
  set C := centSec Γ V Z hΓV hΓZ with hC
  have hCn := centSec_normal Γ V Z hΓV hΓZ
  have hD : (C.map α).Normal := Subgroup.Normal.map hCn α hα
  have hR : ((thetaP F).range).Normal := by
    rw [range_thetaP_eq hF]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hDR : C.map α ⊓ (thetaP F).range = ⊥ := by
    have hsimp := isSimpleGroup_projectiveSL_four hF
    have hE : ((C.map α ⊓ (thetaP F).range).comap (thetaP F)).Normal :=
      Subgroup.Normal.comap (Subgroup.normal_inf_normal _ _) _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((C.map α ⊓ (thetaP F).range).comap (thetaP F)) with h | h
    · have hle : C.map α ⊓ (thetaP F).range ≤ (thetaP F).range := inf_le_right
      rw [← Subgroup.map_comap_eq_self hle, h, Subgroup.map_bot]
    · exfalso
      obtain ⟨γ₄, hγ₄R, v, hv, hγ₄v⟩ := h4
      rw [← range_thetaP_eq hF] at hγ₄R
      obtain ⟨u, hu⟩ := hγ₄R
      have hu' : u ∈ (C.map α ⊓ (thetaP F).range).comap (thetaP F) := h ▸ Subgroup.mem_top u
      obtain ⟨⟨c, hcC, hc⟩, -⟩ := hu'
      have hk : α (c⁻¹ * γ₄) = 1 := by rw [map_mul, map_inv, hc, hu, inv_mul_cancel]
      have h5 := h3 _ hk
      apply hγ₄v
      have e : (γ₄ : G) * v * (γ₄ : G)⁻¹ * v⁻¹ = ((c * (c⁻¹ * γ₄) : ↥Γ) : G) * v *
          ((c * (c⁻¹ * γ₄) : ↥Γ) : G)⁻¹ * v⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact C.mul_mem hcC (show c⁻¹ * γ₄ ∈ C from h5) v hv
  refine eq_one_of_commute_range fun r hr => ?_
  have hy : α γ ∈ C.map α := ⟨γ, hγ, rfl⟩
  have hcomm : α γ * r * (α γ)⁻¹ * r⁻¹ ∈ C.map α ⊓ (thetaP F).range := by
    refine ⟨?_, ?_⟩
    · have : α γ * r * (α γ)⁻¹ * r⁻¹ = α γ * (r * (α γ)⁻¹ * r⁻¹) := by group
      rw [this]
      exact (C.map α).mul_mem hy (hD.conj_mem _ ((C.map α).inv_mem hy) r)
    · exact (thetaP F).range.mul_mem (hR.conj_mem r hr (α γ)) ((thetaP F).range.inv_mem hr)
  rw [hDR, Subgroup.mem_bot] at hcomm
  have : α γ * r * (α γ)⁻¹ = r := by
    have h6 := congrArg (· * r) hcomm
    simpa using h6
  calc α γ * r = α γ * r * (α γ)⁻¹ * α γ := by group
    _ = r * α γ := by rw [this]

end Faithful

section Levi

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

theorem isSimpleGroup_statedSL (hF : Nat.card F = 4) : IsSimpleGroup ↥(StatedSL 2 F) :=
  have := SecA.isSimpleGroup_SL2 (K := F) (n := 2) le_rfl (by rw [hF]; norm_num)
  (SecD.statedSLEquiv' 2 F).isSimpleGroup

theorem eq_bot_of_normal_isPGroup (hF : Nat.card F = 4) {N : Subgroup ↥(StatedSL 2 F)}
    (hN : N.Normal) (h2 : IsPGroup 2 ↥N) : N = ⊥ := by
  have := isSimpleGroup_statedSL hF
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 ↥(StatedSL 2 F) :=
      h2.of_equiv ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [Nat.card_congr (SecD.statedSLEquiv' 2 F).toEquiv, C11P9A.card_SL2_four hF] at hk
    have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem exists_levi' (hF : Nat.card F = 4) {Γ L : Subgroup G} (hLΓ : L ≤ Γ)
    (α : ↥Γ →* PGL3 F)
    (hperf : ⁅(L.subgroupOf Γ).map α, (L.subgroupOf Γ).map α⁆ = (L.subgroupOf Γ).map α)
    (hne : (L.subgroupOf Γ).map α ≠ ⊥) (α₀ : ↥L →* ↥(StatedSL 2 F))
    (hα₀ : Function.Surjective α₀) (hker : α₀.ker = (pCoreOf 2 L).subgroupOf L) :
    ∃ α₀' : ↥((L.subgroupOf Γ).map α) →* ↥(StatedSL 2 F), Function.Surjective α₀' ∧
      α₀'.ker = (pCoreOf 2 ((L.subgroupOf Γ).map α)).subgroupOf ((L.subgroupOf Γ).map α) ∧
      ∀ (l : ↥L) (γ : ↥Γ) (p : ↥((L.subgroupOf Γ).map α)), (γ : G) = l →
        (p : PGL3 F) = α γ → α₀ l = α₀' p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := (L.subgroupOf Γ).map α with hA
  let ρ : ↥L →* ↥A := (α.comp (Subgroup.inclusion hLΓ)).codRestrict A fun l =>
    ⟨Subgroup.inclusion hLΓ l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  have hρ : ∀ l : ↥L, (ρ l : PGL3 F) = α (Subgroup.inclusion hLΓ l) := fun _ => rfl
  have hρs : Function.Surjective ρ := by
    rintro ⟨_, ⟨γ, hγ, rfl⟩⟩
    exact ⟨⟨γ, Subgroup.mem_subgroupOf.mp hγ⟩, Subtype.ext rfl⟩
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hρker : ρ.ker ≤ α₀.ker := by
    have hN : (ρ.ker.map α₀).Normal := Subgroup.Normal.map (MonoidHom.normal_ker ρ) α₀ hα₀
    have := isSimpleGroup_statedSL hF
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map α₀) with h | h
    · intro k hk
      have : α₀ k ∈ ρ.ker.map α₀ := ⟨k, hk, rfl⟩
      rwa [h, Subgroup.mem_bot] at this
    · exfalso
      apply hne
      have hle : (⊤ : Subgroup ↥A) ≤ ((pCoreOf 2 L).subgroupOf L).map ρ := by
        intro p _
        obtain ⟨l, rfl⟩ := hρs p
        obtain ⟨n, hn, hnl⟩ : α₀ l ∈ ρ.ker.map α₀ := h ▸ Subgroup.mem_top _
        refine ⟨n⁻¹ * l, ?_, ?_⟩
        · show n⁻¹ * l ∈ (pCoreOf 2 L).subgroupOf L
          rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hnl, inv_mul_cancel]
        · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul]
      have hpA : IsPGroup 2 ↥A := by
        have h1 : IsPGroup 2 ↥(((pCoreOf 2 L).subgroupOf L).map ρ) :=
          (hO2.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).symm).map ρ
        have h2 : IsPGroup 2 ↥(⊤ : Subgroup ↥A) := h1.to_le hle
        exact h2.of_equiv Subgroup.topEquiv
      have hsolv : Group.IsSolvable ↥A := by
        have := hpA.isNilpotent
        infer_instance
      rw [← perfectCore_eq_self_of_perfect hperf]
      exact (isSolvable_iff_perfectCore_eq_bot A).mp hsolv
  let α₀' : ↥A →* ↥(StatedSL 2 F) :=
    ρ.liftOfRightInverseAux (Function.surjInv hρs) (Function.rightInverse_surjInv hρs) α₀ hρker
  have hα₀' : ∀ l, α₀' (ρ l) = α₀ l := fun l =>
    MonoidHom.liftOfRightInverseAux_comp_apply _ _ _ _ _ l
  have hs' : Function.Surjective α₀' := by
    intro y
    obtain ⟨l, rfl⟩ := hα₀ y
    exact ⟨ρ l, hα₀' l⟩
  refine ⟨α₀', hs', ?_, fun l γ p hγ hp => ?_⟩
  · apply le_antisymm
    ·
      intro p hp
      obtain ⟨l, rfl⟩ := hρs p
      have hl : l ∈ α₀.ker := by rw [MonoidHom.mem_ker, ← hα₀']; exact hp
      rw [hker, Subgroup.mem_subgroupOf] at hl
      rw [Subgroup.mem_subgroupOf]
      have hnorm : (((pCoreOf 2 L).subgroupOf L).map ρ).Normal :=
        Subgroup.Normal.map (CFSG.Quasithin.normal_pCoreOf_subgroupOf L) ρ hρs
      have hp2 : IsPGroup 2 ↥(((pCoreOf 2 L).subgroupOf L).map ρ) :=
        (hO2.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).symm).map ρ
      have hN' : (((((pCoreOf 2 L).subgroupOf L).map ρ).map A.subtype).subgroupOf A).Normal := by
        rw [show ((((pCoreOf 2 L).subgroupOf L).map ρ).map A.subtype).subgroupOf A =
            ((pCoreOf 2 L).subgroupOf L).map ρ from
          Subgroup.comap_map_eq_self_of_injective A.subtype_injective _]
        exact hnorm
      exact CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_subtype_le _) hN'
        (hp2.map A.subtype) ⟨ρ l, ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, rfl⟩
    ·
      have hn : (((pCoreOf 2 A).subgroupOf A).map α₀').Normal :=
        Subgroup.Normal.map (CFSG.Quasithin.normal_pCoreOf_subgroupOf A) α₀' hs'
      have h2 : IsPGroup 2 ↥(((pCoreOf 2 A).subgroupOf A).map α₀') :=
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A).of_equiv
          (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).symm).map α₀'
      have hb := eq_bot_of_normal_isPGroup hF hn h2
      intro p hp
      have : α₀' p ∈ ((pCoreOf 2 A).subgroupOf A).map α₀' := ⟨p, hp, rfl⟩
      rwa [hb, Subgroup.mem_bot] at this
  · have : p = ρ l := Subtype.ext (by rw [hp, hρ]; congr 1; exact Subtype.ext hγ)
    rw [this, hα₀']

end Levi

section Eigen

variable {H : Type} [Group H] {K C : Subgroup H} {y : H} {F : Type} [Field F]
  {α₀ : ↥K →* ↥(StatedSL 2 F)} {μ : F}

theorem pow_three_eq_one_of_isNatEig {C₁ : Subgroup H} (h : IsNatEigSection K y α₀ C₁ C μ)
    (hy3 : y ^ 3 = 1) (hyC : y ∈ Subgroup.normalizer (C : Set H)) : μ ^ 3 = 1 := by
  obtain ⟨β, hs, -, -, hx⟩ := h
  obtain ⟨c, hc⟩ := hs (Multiplicative.ofAdd (Pi.single 0 1))
  have hconj : ∀ z ∈ C, y * z * y⁻¹ ∈ C := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp hyC z).mp hz
  set c₁ : ↥C := ⟨_, hconj _ c.2⟩ with hc₁
  set c₂ : ↥C := ⟨_, hconj _ c₁.2⟩ with hc₂
  set c₃ : ↥C := ⟨_, hconj _ c₂.2⟩ with hc₃
  have e1 := hx c c₁ rfl
  have e2 := hx c₁ c₂ rfl
  have e3 := hx c₂ c₃ rfl
  have h33 : c₃ = c := by
    apply Subtype.ext
    show y * (y * (y * (c : H) * y⁻¹) * y⁻¹) * y⁻¹ = c
    have : y * (y * (y * (c : H) * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * c * (y * y * y)⁻¹ := by
      group
    have hy3' : y * y * y = 1 := by rw [← hy3, pow_succ, pow_two]
    rw [this, hy3', one_mul, inv_one, mul_one]
  rw [h33, e2, e1, smul_smul, smul_smul] at e3
  have h0 := congrFun e3 0
  rw [hc, toAdd_ofAdd] at h0
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h0
  linear_combination -h0

end Eigen

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
