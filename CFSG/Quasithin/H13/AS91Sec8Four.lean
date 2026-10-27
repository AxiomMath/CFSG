module

public import CFSG.Quasithin.H13.AS91Sec8IsoM
public import CFSG.Quasithin.H13.AS91Sec7Inc
public import CFSG.Quasithin.H13.AS91Sec8FixOctHolds
public import CFSG.Quasithin.H13.AS91Sec8KDer
public import CFSG.Quasithin.H13.AS91Sec8Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.ASVolI.ChH
open scoped Pointwise

namespace M24G

theorem exists_smul_trio_sextet {l U l' U' : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hl' : IsTrio l') (hU : IsSextet U) (hU' : IsSextet U') (hlU : TrioIn l U)
    (hlU' : TrioIn l' U') :
    ∃ g ∈ M24g, g • l = l' ∧ g • U = U' := by
  obtain ⟨a, ha, hal⟩ := trio_transitive hl
  obtain ⟨b, hb, hbl⟩ := trio_transitive hl'
  have hc : b⁻¹ * a ∈ M24g := Subgroup.mul_mem M24g (Subgroup.inv_mem M24g hb) ha
  have hcl : (b⁻¹ * a) • l = l' := by
    rw [mul_smul, hal, ← hbl, inv_smul_smul]
  have hUc : IsSextet ((b⁻¹ * a) • U) := (isSextet_smul_iff hc).2 hU
  have hIU : TrioIn ((b⁻¹ * a) • l) ((b⁻¹ * a) • U) := (trioIn_smul_iff (b⁻¹ * a)).2 hlU
  have hIU' : TrioIn l' ((b⁻¹ * a) • U) := hcl ▸ hIU
  obtain ⟨g, hg, hgl, hgU⟩ := exists_smul_fix_trio_sextet hl' hUc hU' hIU' hlU'
  refine ⟨g * (b⁻¹ * a), Subgroup.mul_mem M24g hg hc, ?_, ?_⟩
  · rw [mul_smul, hcl, hgl]
  · rw [mul_smul, hgU]

end M24G

namespace ResM24T

variable {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
  {z : G} {z' : G'} {c : Loc49 G z} {c' : Loc49 G' z'}

theorem mem_G2_of_mulEquiv (r : ResM24T c) (r' : ResM24T c')
    {σ : Equiv.Perm (Fin 24)} {α : ↥c.G1 ≃* ↥c'.G1}
    (hα : ∀ h : ↥c.G1, r'.φ (α h) = σ * r.φ h * σ⁻¹) (hσl : σ • r.l₀ = r'.l₀) :
    ∀ h : ↥c.G1, (h : G) ∈ c.G2 ↔ (α h : G') ∈ c'.G2 := by
  intro h
  rw [r.stab₂ h, r'.stab₂ (α h), hα h, ← hσl]
  have hsimp : (σ * r.φ h * σ⁻¹) • (σ • r.l₀) = σ • (r.φ h • r.l₀) := by
    simp only [mul_smul, inv_smul_smul]
  rw [hsimp]
  exact ⟨fun hh => by rw [hh], fun hh => smul_left_cancel σ hh⟩

theorem mem_G3_of_mulEquiv (r : ResM24T c) (r' : ResM24T c')
    {σ : Equiv.Perm (Fin 24)} {α : ↥c.G1 ≃* ↥c'.G1}
    (hα : ∀ h : ↥c.G1, r'.φ (α h) = σ * r.φ h * σ⁻¹) (hσU : σ • r.U₀ = r'.U₀) :
    ∀ h : ↥c.G1, (h : G) ∈ c.G3 ↔ (α h : G') ∈ c'.G3 := by
  intro h
  rw [r.stab₃ h, r'.stab₃ (α h), hα h, ← hσU]
  have hsimp : (σ * r.φ h * σ⁻¹) • (σ • r.U₀) = σ • (r.φ h • r.U₀) := by
    simp only [mul_smul, inv_smul_smul]
  rw [hsimp]
  exact ⟨fun hh => by rw [hh], fun hh => smul_left_cancel σ hh⟩

theorem mem_preFixOct_of_mulEquiv (r : ResM24T c) (r' : ResM24T c')
    {σ : Equiv.Perm (Fin 24)} {α : ↥c.G1 ≃* ↥c'.G1} (hσ : σ ∈ M24g)
    (hα : ∀ h : ↥c.G1, r'.φ (α h) = σ * r.φ h * σ⁻¹) (hσl : σ • r.l₀ = r'.l₀) :
    ∀ h : ↥c.G1, (h : G) ∈ r.preFixOct ↔ (α h : G') ∈ r'.preFixOct := by
  intro h
  have h1 : (h : G) ∈ r.preFixOct ↔ r.φ h ∈ fixOct r.l₀ := by
    rw [ResM24.mem_preFixOct]
    constructor
    · rintro ⟨_, hx⟩
      simpa using hx
    · intro hx
      exact ⟨h.2, hx⟩
  have h2 : (α h : G') ∈ r'.preFixOct ↔ r'.φ (α h) ∈ fixOct r'.l₀ := by
    rw [ResM24.mem_preFixOct]
    constructor
    · rintro ⟨_, hx⟩
      simpa using hx
    · intro hx
      exact ⟨(α h).2, hx⟩
  rw [h1, h2, hα h, ← hσl]
  exact fixOct_conj_iff hσ

end ResM24T

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem mem_G3_conj_iff {e : G} (he : e ∈ c.E) {w : G} (hw : w ∈ c.G1) :
    w ∈ c.G3 ↔ e * w * e⁻¹ ∈ c.G3 := by
  have hA := c.map_conj_G31 he
  have hw1 : e * w * e⁻¹ ∈ c.G1 := by
    have h := c.map_conj_G1 he
    have hmem : (MulAut.conj e) w ∈ c.G1.map (MulAut.conj e).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hw
    rw [h] at hmem
    simpa [MulAut.conj_apply] using hmem
  constructor
  · intro hw3
    have hmem : e * w * e⁻¹ ∈ (c.G3 ⊓ c.G1).map (MulAut.conj e).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨w, Subgroup.mem_inf.mpr ⟨hw3, hw⟩, rfl⟩
    rw [hA] at hmem
    exact (Subgroup.mem_inf.mp hmem).1
  · intro hw3
    have hmem : e * w * e⁻¹ ∈ (c.G3 ⊓ c.G1).map (MulAut.conj e).toMonoidHom := by
      rw [hA]
      exact Subgroup.mem_inf.mpr ⟨hw3, hw1⟩
    obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hmem
    have hvw' : v = w := (MulAut.conj e).injective hvw
    exact hvw' ▸ (Subgroup.mem_inf.mp hv).1

end Loc49

namespace ResM24T

variable {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
  {z : G} {z' : G'} {c : Loc49 G z} {c' : Loc49 G' z'}

theorem subgroupOf_image_E (r : ResM24T c) (r' : ResM24T c')
    {σ : Equiv.Perm (Fin 24)} {α : ↥c.G1 ≃* ↥c'.G1}
    (hα : ∀ h : ↥c.G1, r'.φ (α h) = σ * r.φ h * σ⁻¹) :
    (c.E.subgroupOf c.G1).map α.toMonoidHom = c'.E.subgroupOf c'.G1 := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (r.exists_mulEquiv_mem_E r' σ hα y).mp hy
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨α.symm x, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf]
    exact (r.exists_mulEquiv_mem_E r' σ hα (α.symm x)).mpr (by simpa using hx)

theorem subgroupOf_image_G12 (r : ResM24T c) (r' : ResM24T c')
    {σ : Equiv.Perm (Fin 24)} {α : ↥c.G1 ≃* ↥c'.G1}
    (hα : ∀ h : ↥c.G1, r'.φ (α h) = σ * r.φ h * σ⁻¹) (hσl : σ • r.l₀ = r'.l₀) :
    ((c.G1 ⊓ c.G2).subgroupOf c.G1).map α.toMonoidHom =
      (c'.G1 ⊓ c'.G2).subgroupOf c'.G1 := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact Subgroup.mem_inf.mpr ⟨(α y).2, (r.mem_G2_of_mulEquiv r' hα hσl y).mp hy.2⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨α.symm x, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨(α.symm x).2,
      (r.mem_G2_of_mulEquiv r' hα hσl (α.symm x)).mpr (by simpa using hx.2)⟩

theorem subgroupOf_image_preFixOct (r : ResM24T c) (r' : ResM24T c')
    {σ : Equiv.Perm (Fin 24)} {α : ↥c.G1 ≃* ↥c'.G1} (hσ : σ ∈ M24g)
    (hα : ∀ h : ↥c.G1, r'.φ (α h) = σ * r.φ h * σ⁻¹) (hσl : σ • r.l₀ = r'.l₀) :
    (r.preFixOct.subgroupOf c.G1).map α.toMonoidHom = r'.preFixOct.subgroupOf c'.G1 := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (r.mem_preFixOct_of_mulEquiv r' hσ hα hσl y).mp hy
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨α.symm x, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf]
    exact (r.mem_preFixOct_of_mulEquiv r' hσ hα hσl (α.symm x)).mpr (by simpa using hx)

theorem subgroupOf_image_K (r : ResM24T c) (r' : ResM24T c')
    (hKeq : c.K = ⁅r.preFixOct, r.preFixOct⁆ ⊔ ⁅c.E, r.preFixOct⁆)
    (hKeq' : c'.K = ⁅r'.preFixOct, r'.preFixOct⁆ ⊔ ⁅c'.E, r'.preFixOct⁆)
    {σ : Equiv.Perm (Fin 24)} {α : ↥c.G1 ≃* ↥c'.G1} (hσ : σ ∈ M24g)
    (hα : ∀ h : ↥c.G1, r'.φ (α h) = σ * r.φ h * σ⁻¹) (hσl : σ • r.l₀ = r'.l₀) :
    (c.K.subgroupOf c.G1).map α.toMonoidHom = c'.K.subgroupOf c'.G1 := by
  have hP := r.subgroupOf_image_preFixOct r' hσ hα hσl
  have hE := r.subgroupOf_image_E r' hα
  have hKK : c.K.subgroupOf c.G1 = ⁅r.preFixOct.subgroupOf c.G1, r.preFixOct.subgroupOf c.G1⁆ ⊔
      ⁅c.E.subgroupOf c.G1, r.preFixOct.subgroupOf c.G1⁆ := by
    apply Subgroup.map_injective c.G1.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le r.preFixOct_le_G1,
      Subgroup.map_subgroupOf_eq_of_le c.E_le_G1,
      Subgroup.map_subgroupOf_eq_of_le c.K_le_G1, ← hKeq]
  have hKK' : c'.K.subgroupOf c'.G1 =
      ⁅r'.preFixOct.subgroupOf c'.G1, r'.preFixOct.subgroupOf c'.G1⁆ ⊔
      ⁅c'.E.subgroupOf c'.G1, r'.preFixOct.subgroupOf c'.G1⁆ := by
    apply Subgroup.map_injective c'.G1.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le r'.preFixOct_le_G1,
      Subgroup.map_subgroupOf_eq_of_le c'.E_le_G1,
      Subgroup.map_subgroupOf_eq_of_le c'.K_le_G1, ← hKeq']
  rw [hKK, Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_commutator, hP, hE, ← hKK']

theorem exists_mulEquiv_stmt8_4 (r : ResM24T c) (r' : ResM24T c')
    (hP : FixOctPerfect) (hS : FixOctSym) (hW : FixOctCommW11)
    {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ M24g) (hσl : σ • r.l₀ = r'.l₀)
    (hσU : σ • r.U₀ = r'.U₀) {y : G ⧸ c.G1} {y' : G' ⧸ c'.G1} (hy : y ∈ c.ptsL)
    (hyx : y ≠ c.x0) (hy' : y' ∈ c'.ptsL) (hyx' : y' ≠ c'.x0)
    (hlu : c.G1 ⊓ stabilizer G y ≤ c.G2) (hlu' : c'.G1 ⊓ stabilizer G' y' ≤ c'.G2) :
    ∃ α : ↥(stabilizer G c.x0) ≃* ↥(stabilizer G' c'.x0),
      (c.G3.subgroupOf (stabilizer G c.x0)).map α.toMonoidHom =
        c'.G3.subgroupOf (stabilizer G' c'.x0) ∧
      ((stabilizer G y).subgroupOf (stabilizer G c.x0)).map α.toMonoidHom =
        (stabilizer G' y').subgroupOf (stabilizer G' c'.x0) := by
  classical
  obtain ⟨α₁, hα₁⟩ := r.exists_mulEquiv r' σ hσ
  have hK : (c.K.subgroupOf c.G1).map α₁.toMonoidHom = c'.K.subgroupOf c'.G1 :=
    r.subgroupOf_image_K r' (ResM24T.K_eq r hP hS hW) (ResM24T.K_eq r' hP hS hW) hσ hα₁ hσl
  have hG12 := r.subgroupOf_image_G12 r' hα₁ hσl
  let f : ↥c.G1 →* G' := c'.G1.subtype.comp α₁.toMonoidHom
  have hfinj : Function.Injective f := fun a b hab => α₁.injective (Subtype.ext hab)
  let M : Subgroup G := c.G1 ⊓ stabilizer G y
  let Msub : Subgroup ↥c.G1 := M.subgroupOf c.G1
  let G12 : Subgroup G := c.G1 ⊓ c.G2
  let G12sub : Subgroup ↥c.G1 := G12.subgroupOf c.G1
  let Uim : Subgroup G' := Msub.map f
  have hMle : M ≤ G12 := by
    show c.G1 ⊓ stabilizer G y ≤ c.G1 ⊓ c.G2
    rw [c.inf_stab_eq_of_lineU hlu]
    exact inf_le_left
  have hMsubG12 : Msub ≤ G12sub := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hMle hx
  have hG12im : G12sub.map f = c'.G1 ⊓ c'.G2 := by
    rw [← Subgroup.map_map, hG12, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have hUle : Uim ≤ c'.G1 ⊓ c'.G2 := by
    rw [← hG12im]
    exact Subgroup.map_mono hMsubG12
  have hUim_card : Nat.card ↥Uim = Nat.card ↥M := by
    have h1 : Nat.card ↥Uim = Nat.card ↥Msub := Subgroup.card_map_of_injective hfinj
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show M ≤ c.G1 from inf_le_left)).toEquiv
  have hG12_card : Nat.card ↥(c'.G1 ⊓ c'.G2) = Nat.card ↥G12 := by
    rw [← hG12im, Subgroup.card_map_of_injective hfinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show G12 ≤ c.G1 from inf_le_left)).toEquiv
  have hMrel : M.relIndex G12 = 4 := by
    rw [show M = G12 ⊓ stabilizer G y from c.inf_stab_eq_of_lineU hlu]
    exact c.relIndex_stab hy hyx
  have h4 : 4 * Nat.card ↥M = Nat.card ↥G12 := by
    have h := Subgroup.relIndex_mul_card M G12
    rw [hMrel, inf_eq_left.mpr hMle] at h
    exact h
  have hUrel : Uim.relIndex (c'.G1 ⊓ c'.G2) = 4 := by
    have h := Subgroup.relIndex_mul_card Uim (c'.G1 ⊓ c'.G2)
    rw [inf_eq_left.mpr hUle, hUim_card, hG12_card, ← h4] at h
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥M)) h
  have hKleM : c.K ≤ M := by
    rw [show M = G12 ⊓ stabilizer G y from c.inf_stab_eq_of_lineU hlu]
    exact c.K_le_G12_stab hy
  have hKsubM : c.K.subgroupOf c.G1 ≤ Msub := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hKleM hx
  have hKim : (c.K.subgroupOf c.G1).map f = c'.K := by
    rw [← Subgroup.map_map, hK, Subgroup.map_subgroupOf_eq_of_le c'.K_le_G1]
  have hKU : c'.K ≤ Uim := by
    rw [← hKim]
    exact Subgroup.map_mono hKsubM
  obtain ⟨y'', hy'', hyx'', hUim⟩ := c'.exists_eq_stab_of_relIndex_four hUle hKU hUrel
  obtain ⟨e', he', he'y⟩ := c'.E_transitive hy'' hy' hyx'' hyx'
  let e1' : ↥c'.G1 := ⟨e', c'.E_le_G1 he'⟩
  let α₂ : ↥c.G1 ≃* ↥c'.G1 := α₁.trans (MulAut.conj e1')
  let α : ↥(stabilizer G c.x0) ≃* ↥(stabilizer G' c'.x0) :=
    (MulEquiv.subgroupCongr c.stab_x0).trans (α₂.trans (MulEquiv.subgroupCongr c'.stab_x0.symm))
  have hG1_mem : ∀ m : ↥(stabilizer G c.x0), (m : G) ∈ c.G1 := fun m =>
    le_of_eq c.stab_x0 m.2
  have hαval : ∀ m : ↥(stabilizer G c.x0),
      (α m : G') = (α₂ ⟨(m : G), hG1_mem m⟩ : G') := by
    intro m
    change (((MulEquiv.subgroupCongr c'.stab_x0.symm)
      (α₂ ((MulEquiv.subgroupCongr c.stab_x0) m))) : G') = _
    rw [MulEquiv.subgroupCongr_apply]
    congr 1
  have hα₂val : ∀ y₁ : ↥c.G1, (α₂ y₁ : G') = e' * (α₁ y₁ : G') * e'⁻¹ := by
    intro y₁
    change (((MulAut.conj e1') (α₁ y₁) : ↥c'.G1) : G') = _
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hMim₁ : (M.subgroupOf c.G1).map α₁.toMonoidHom = Uim.subgroupOf c'.G1 := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, hax⟩
      exact ⟨a, ha, Subtype.ext hax⟩
  have hMim₂ : (M.subgroupOf c.G1).map α₂.toMonoidHom =
      (c'.G1 ⊓ stabilizer G' y').subgroupOf c'.G1 := by
    apply Subgroup.map_injective c'.G1.subtype_injective
    have hcomp2 : c'.G1.subtype.comp α₂.toMonoidHom =
        (MulAut.conj e').toMonoidHom.comp f := by
      ext y₁
      change (α₂ y₁ : G') = e' * (f y₁) * e'⁻¹
      rw [hα₂val y₁]
      rfl
    rw [Subgroup.map_map, hcomp2, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    change Uim.map (MulAut.conj e').toMonoidHom = c'.G1 ⊓ stabilizer G' y'
    rw [hUim, (c'.conj_inf_stab he' hy'').1, he'y, ← c'.inf_stab_eq_of_lineU hlu']
  have hMim₂_mem : ∀ y₁ : ↥c.G1,
      y₁ ∈ M.subgroupOf c.G1 ↔ α₂ y₁ ∈ (c'.G1 ⊓ stabilizer G' y').subgroupOf c'.G1 := by
    intro y₁
    rw [← hMim₂, Subgroup.mem_map]
    constructor
    · exact fun h => ⟨y₁, h, rfl⟩
    · rintro ⟨a, ha, hay⟩
      rwa [α₂.injective hay] at ha
  have hyiff : ∀ m : ↥(stabilizer G c.x0),
      (m : G) ∈ stabilizer G y ↔ (α m : G') ∈ stabilizer G' y' := by
    intro m
    have hmM : (⟨(m : G), hG1_mem m⟩ : ↥c.G1) ∈ M.subgroupOf c.G1 ↔
        (m : G) ∈ stabilizer G y := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨fun h => h.2, fun h => Subgroup.mem_inf.mpr ⟨hG1_mem m, h⟩⟩
    have h2 : α₂ ⟨(m : G), hG1_mem m⟩ ∈ (c'.G1 ⊓ stabilizer G' y').subgroupOf c'.G1 ↔
        (α₂ ⟨(m : G), hG1_mem m⟩ : G') ∈ stabilizer G' y' := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨(α₂ ⟨(m : G), hG1_mem m⟩).2, h⟩⟩
    rw [hαval]
    exact hmM.symm.trans ((hMim₂_mem ⟨(m : G), hG1_mem m⟩).trans h2)
  have hG3iff : ∀ m : ↥(stabilizer G c.x0),
      (m : G) ∈ c.G3 ↔ (α m : G') ∈ c'.G3 := by
    intro m
    rw [hαval, hα₂val]
    rw [r.mem_G3_of_mulEquiv r' hα₁ hσU ⟨(m : G), hG1_mem m⟩]
    exact c'.mem_G3_conj_iff he' (α₁ ⟨(m : G), hG1_mem m⟩).2
  refine ⟨α, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      exact Subgroup.mem_subgroupOf.mpr ((hG3iff m).mp (Subgroup.mem_subgroupOf.mp hm))
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_map.mpr ⟨α.symm x,
        Subgroup.mem_subgroupOf.mpr ((hG3iff (α.symm x)).mpr (by simpa using hx)), by simp⟩
  · ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      exact Subgroup.mem_subgroupOf.mpr ((hyiff m).mp (Subgroup.mem_subgroupOf.mp hm))
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_map.mpr ⟨α.symm x,
        Subgroup.mem_subgroupOf.mpr ((hyiff (α.symm x)).mpr (by simpa using hx)), by simp⟩

end ResM24T

theorem stmt8_4_of_fixOct
    (hP : FixOctPerfect) (hS : FixOctSym) (hW : FixOctCommW11)
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24T c))
    (hlu : Stmt5_LineU) : Stmt8_4 := by
  intro G _ _ z hJ c G' _ _ z' hJ' c' y y' hy hyx hy' hyx'
  obtain ⟨r⟩ := hres G z hJ c
  obtain ⟨r'⟩ := hres G' z' hJ' c'
  obtain ⟨σ, hσ, hσl, hσU⟩ := M24G.exists_smul_trio_sextet r.isTrio_l₀ r'.isTrio_l₀
    r.isSextet_U₀ r'.isSextet_U₀ r.trioIn_l₀_U₀ r'.trioIn_l₀_U₀
  exact r.exists_mulEquiv_stmt8_4 r' hP hS hW hσ hσl hσU hy hyx hy' hyx'
    (hlu G z hJ c y hy hyx) (hlu G' z' hJ' c' y' hy' hyx')

theorem stmt8_4_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24T c))
    (hlu : Stmt5_LineU) : Stmt8_4 :=
  stmt8_4_of_fixOct fixOctPerfect_holds fixOctSym_holds fixOctCommW11_holds hres hlu

end CFSG.Quasithin.H13.AS91
