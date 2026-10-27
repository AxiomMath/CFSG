module

public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.FLc2VModel
public import CFSG.Quasithin.Background.FLc3Out

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open CFSG.Open CFSG.Quasithin Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G]

theorem mem_autOn_iff {H V : Subgroup G} {a : MulAut ↥V} :
    a ∈ autOn H V ↔ ∃ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ H ∧
      conjAct V ⟨x, hx⟩ = a :=
  CFSG.Quasithin.AutOn.mem_autOn_iff_exists

theorem conjAct_coe {V : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ((conjAct V ⟨x, hx⟩ v : ↥V) : G) = x * v * x⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V _ v

theorem conjAct_conj {V : Subgroup G} {x y : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (hxyx : x * y * x⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨x, hx⟩ * conjAct V ⟨y, hy⟩ * (conjAct V ⟨x, hx⟩)⁻¹ = conjAct V ⟨x * y * x⁻¹, hxyx⟩ := by
  have : (⟨x * y * x⁻¹, hxyx⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

theorem autOn_mono' {H K V : Subgroup G} (h : H ≤ K) : autOn H V ≤ autOn K V :=
  CFSG.Quasithin.AutOn.autOn_mono h

theorem isPGroup_autOn {S V : Subgroup G} (hS : IsPGroup 2 S) : IsPGroup 2 (autOn S V) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hS

theorem stSetting_ctx {U L S Z₂ : Subgroup G} (hU : IsElemAbelian 2 U) {n : ℕ}
    (ρ : SLt n →* MulAut ↥U) (hρinj : Function.Injective ρ)
    (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hSL : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L)
    (hgen : U ≤ conjClosure Z₂ L) (hZ₂ : Z₂ ≤ U) (hSZ : ∀ s ∈ S, ∀ z ∈ Z₂, s * z * s⁻¹ = z)
    (hS2 : IsPGroup 2 S)
    (hrange : ∀ k ∈ autOn L U, ∃ g, ρ g = k) (hrange' : ∀ g, ρ g ∈ autOn L U)
    (hT : ∀ u ∈ Ut n, ρ u ∈ autOn S U) :
    @StSetting ↥U (commGroupOfElemAbelian hU) n ρ (autOn S U) := by
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  refine ⟨hρinj, isPGroup_autOn hS2, hT, ?_, ?_⟩
  ·
    intro s hs y
    obtain ⟨s₀, hs₀, hs₀S, rfl⟩ := mem_autOn_iff.1 hs
    obtain ⟨l, hl, hlL, hρl⟩ := mem_autOn_iff.1 (hrange' y)
    have hc : s₀ * l * s₀⁻¹ ∈ Subgroup.normalizer (U : Set G) := hLU (hSL s₀ hs₀S l hlL)
    obtain ⟨y', hy'⟩ := hrange (conjAct U ⟨s₀ * l * s₀⁻¹, hc⟩)
      (mem_autOn_iff.2 ⟨_, hc, hSL s₀ hs₀S l hlL, rfl⟩)
    refine ⟨y', ?_⟩
    rw [hy', ← hρl]
    exact conjAct_conj hs₀ hl hc
  ·
    intro s hs hcomm
    obtain ⟨s₀, hs₀, hs₀S, rfl⟩ := mem_autOn_iff.1 hs
    have hcent : ∀ l ∈ L, ∀ (hl : l ∈ Subgroup.normalizer (U : Set G)),
        conjAct U ⟨s₀, hs₀⟩ * conjAct U ⟨l, hl⟩ = conjAct U ⟨l, hl⟩ * conjAct U ⟨s₀, hs₀⟩ := by
      intro l hlL hl
      obtain ⟨g, hg⟩ := hrange (conjAct U ⟨l, hl⟩) (mem_autOn_iff.2 ⟨l, hl, hlL, rfl⟩)
      rw [← hg]
      exact (hcomm g)
    have hle : conjClosure Z₂ L ≤ Subgroup.centralizer ({s₀} : Set G) := by
      refine conjClosure_le fun l hl z hz => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hlN : l ∈ Subgroup.normalizer (U : Set G) := hLU hl
      have h1 := congrArg (fun a : MulAut ↥U => ((a (⟨z, hZ₂ hz⟩ : ↥U) : ↥U) : G))
        (hcent l hl hlN)
      simp only [MulAut.mul_apply] at h1
      rw [conjAct_coe hs₀, conjAct_coe hlN, conjAct_coe hlN, conjAct_coe hs₀] at h1
      have h2 : s₀ * (l * z * l⁻¹) * s₀⁻¹ = l * z * l⁻¹ := by
        rw [h1, hSZ s₀ hs₀S z hz]
      refine Eq.symm ?_
      calc s₀ * (l * z * l⁻¹) = (s₀ * (l * z * l⁻¹) * s₀⁻¹) * s₀ := by group
        _ = (l * z * l⁻¹) * s₀ := by rw [h2]
    have hUc : ∀ v : ↥U, s₀ * (v : G) * s₀⁻¹ = v := by
      intro v
      have := Subgroup.mem_centralizer_singleton_iff.1 (hle (hgen v.2))
      calc s₀ * (v : G) * s₀⁻¹ = ((v : G) * s₀) * s₀⁻¹ := by rw [← this]
        _ = v := by group
    ext v
    rw [conjAct_coe hs₀]
    exact hUc v

section Twist

variable {V : Type} [CommGroup V]

@[expose] def _root_.CFSG.Quasithin.FLc.VModel.rtwist {n : ℕ} {ρ : SLt n →* MulAut V} {U' Z' : Subgroup V}
    {X : Type} [CommGroup X] {act : SLt n → X → X} (D : VModel n ρ U' Z' X act) (h : SLt n) :
    VModel n (ρ.comp (MulAut.conj h).toMonoidHom) U' Z' X act where
  β := (MonoidHom.mk' (act h⁻¹) (D.act_hom h⁻¹)).comp D.β
  surj := by
    intro x
    obtain ⟨u, hu⟩ := D.surj (act h x)
    refine ⟨u, ?_⟩
    show act h⁻¹ (D.β u) = x
    rw [hu, ← D.act_mul, inv_mul_cancel, D.act_one]
  inv := fun g u hu => D.inv (h * g * h⁻¹) u hu
  ker := by
    intro u hu
    apply D.ker
    have h1 : act h⁻¹ (D.β u) = 1 := hu
    have h2 : act h 1 = 1 := by
      have h3 := D.act_hom h 1 1
      rw [mul_one] at h3
      exact mul_left_cancel (h3.symm.trans (mul_one _).symm)
    calc D.β u = act h (act h⁻¹ (D.β u)) := by
          rw [← D.act_mul, mul_inv_cancel, D.act_one]
      _ = 1 := by rw [h1, h2]
  equiv := by
    intro g u hu
    have hu' : (ρ (h * g * h⁻¹)) (u : V) ∈ U' := hu
    have h1 := D.equiv (h * g * h⁻¹) u hu'
    show act h⁻¹ (D.β ⟨(ρ (h * g * h⁻¹)) (u : V), hu'⟩) = act g (act h⁻¹ (D.β u))
    rw [h1, ← D.act_mul, ← D.act_mul]
    congr 1
    group
  Zfix := fun g z hz => D.Zfix (h * g * h⁻¹) z hz
  act_hom := D.act_hom
  act_one := D.act_one
  act_mul := D.act_mul

theorem exists_rho_conj [Finite V] {n : ℕ} (hn : 1 ≤ n) {ρ : SLt n →* MulAut V}
    {T : Subgroup (MulAut V)} (hTle : T ≤ ρ.range)
    (hT : ∃ P : Sylow 2 ↥ρ.range, (P : Subgroup ↥ρ.range) = T.subgroupOf ρ.range) :
    ∃ h : SLt n, (Ut n).map (ρ.comp (MulAut.conj h).toMonoidHom) = T := by
  obtain ⟨P, hP⟩ := hT
  let ρ' : SLt n →* ↥ρ.range := ρ.rangeRestrict
  have hρ's : Function.Surjective ρ' := ρ.rangeRestrict_surjective
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 hn
  let R₀ : Sylow 2 ↥ρ.range := Sylow.mapSurjective hρ's Q₀
  have hR₀ : (R₀ : Subgroup ↥ρ.range) = (Ut n).map ρ' := by
    rw [Sylow.coe_mapSurjective, hQ₀]
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (↥ρ.range) R₀ P
  obtain ⟨g, rfl⟩ := hρ's x
  refine ⟨g, ?_⟩
  have hPeq : (P : Subgroup ↥ρ.range) =
      ((Ut n).map ρ').map (MulAut.conj (ρ' g)).toMonoidHom := by
    rw [← hx, ← hR₀]
    rfl
  have hcomp : (MulAut.conj (ρ' g)).toMonoidHom.comp ρ' = ρ'.comp (MulAut.conj g).toMonoidHom := by
    ext u
    simp [map_mul, map_inv]
  have h1 : (T.subgroupOf ρ.range) = (Ut n).map (ρ'.comp (MulAut.conj g).toMonoidHom) := by
    rw [← hP, hPeq, Subgroup.map_map, hcomp]
  have h2 := congrArg (Subgroup.map ρ.range.subtype) h1
  rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hTle] at h2
  rw [h2]
  rfl

end Twist

end CFSG.Quasithin.FLc
