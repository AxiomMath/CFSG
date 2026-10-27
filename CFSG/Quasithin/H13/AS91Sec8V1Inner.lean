module

public import CFSG.Quasithin.H13.AS91Sec8V1Map
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Quasithin.H.Mathieu
open CFSG.ASVolI.ChH (M24g S24)
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem normal_E_subgroupOf : (c.E.subgroupOf (c.G3 ⊓ c.G1)).Normal :=
  ⟨fun e he g => by
    rw [Subgroup.mem_subgroupOf] at he ⊢
    exact c.conj_mem_E ⟨(g : G), (Subgroup.mem_inf.mp g.2).2⟩ he⟩

theorem isElemAbelian_E_subgroupOf : CFSG.Open.IsElemAbelian 2 (c.E.subgroupOf (c.G3 ⊓ c.G1)) :=
  c.E_elem.subgroupOf (c.G3 ⊓ c.G1)

theorem card_E_subgroupOf : Nat.card ↥(c.E.subgroupOf (c.G3 ⊓ c.G1)) = 2 ^ 11 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.E_le_G3_inf_G1).toEquiv).trans c.card_E

theorem ker_phiS (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) :
    (c.phiS r hU).ker = c.E.subgroupOf (c.G3 ⊓ c.G1) := by
  ext h
  rw [MonoidHom.mem_ker, c.phiS_eq_one_iff r hU h, Subgroup.mem_subgroupOf]

theorem card_eq_card_inf_mul_card_map (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (E' : Subgroup ↥(c.G3 ⊓ c.G1)) :
    Nat.card ↥E' = Nat.card ↥(E' ⊓ c.E.subgroupOf (c.G3 ⊓ c.G1)) *
      Nat.card ↥(E'.map (c.phiS r hU)) := by
  let f : ↥E' →* ↥M24G.sextStab := (c.phiS r hU).comp E'.subtype
  have hker : f.ker = (E' ⊓ c.E.subgroupOf (c.G3 ⊓ c.G1)).subgroupOf E' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change c.phiS r hU (x : ↥(c.G3 ⊓ c.G1)) = 1 ↔
      (x : ↥(c.G3 ⊓ c.G1)) ∈ E' ∧ (x : ↥(c.G3 ⊓ c.G1)) ∈ c.E.subgroupOf (c.G3 ⊓ c.G1)
    rw [c.phiS_eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange : f.range = E'.map (c.phiS r hU) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange] at h
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : E' ⊓ c.E.subgroupOf (c.G3 ⊓ c.G1) ≤ E')).toEquiv] at h
  exact h.symm

theorem card_inf_le_fixed (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    {E' : Subgroup ↥(c.G3 ⊓ c.G1)} (hE' : CFSG.Open.IsElemAbelian 2 E') :
    Nat.card ↥(E' ⊓ c.E.subgroupOf (c.G3 ⊓ c.G1)) ≤
      Nat.card {w : W11 // ∀ b ∈ E'.map (c.phiS r hU),
        rho11 M24G.sextStab M24G.sextStab_le b w = w} := by
  classical
  let eE : ↥(E' ⊓ c.E.subgroupOf (c.G3 ⊓ c.G1)) → ↥c.E := fun e =>
    ⟨((e : ↥(c.G3 ⊓ c.G1)) : G),
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp e.2).2⟩
  have hfix : ∀ e : ↥(E' ⊓ c.E.subgroupOf (c.G3 ⊓ c.G1)),
      ∀ b ∈ E'.map (c.phiS r hU),
        rho11 M24G.sextStab M24G.sextStab_le b (r.todd (eE e)) = r.todd (eE e) := by
    intro e b hb
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp hb
    have hcomm' := hE'.1.is_comm.comm (⟨e', he'⟩ : ↥E')
      (⟨(e : ↥(c.G3 ⊓ c.G1)), (Subgroup.mem_inf.mp e.2).1⟩ : ↥E')
    have hcomm : (e' : ↥(c.G3 ⊓ c.G1)) * (e : ↥(c.G3 ⊓ c.G1)) =
        (e : ↥(c.G3 ⊓ c.G1)) * (e' : ↥(c.G3 ⊓ c.G1)) := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_mk] using
        congrArg (fun x : ↥E' => (x : ↥(c.G3 ⊓ c.G1))) hcomm'
    have hconj := c.todd_conj_phiS r hU e' (eE e)
    have hval : (e' : G) * (eE e : G) * (e' : G)⁻¹ = (eE e : G) := by
      have hc : (e' : G) * (e : G) = (e : G) * (e' : G) := by
        simpa only [Subgroup.coe_mul] using
          congrArg (fun x : ↥(c.G3 ⊓ c.G1) => (x : G)) hcomm
      calc (e' : G) * (eE e : G) * (e' : G)⁻¹
          = (e' : G) * (e : G) * (e' : G)⁻¹ := rfl
        _ = (e : G) * (e' : G) * (e' : G)⁻¹ := by rw [hc]
        _ = (e : G) := by group
    have heq : (⟨(e' : G) * (eE e : G) * (e' : G)⁻¹, c.conj_mem_E
        ⟨(e' : G), (Subgroup.mem_inf.mp e'.2).2⟩ (eE e).2⟩ : ↥c.E) = eE e :=
      Subtype.ext hval
    rw [← hconj, heq]
  let inj : ↥(E' ⊓ c.E.subgroupOf (c.G3 ⊓ c.G1)) →
      {w : W11 // ∀ b ∈ E'.map (c.phiS r hU),
        rho11 M24G.sextStab M24G.sextStab_le b w = w} :=
    fun e => ⟨r.todd (eE e), hfix e⟩
  refine Nat.card_le_card_of_injective inj ?_
  intro a b hab
  have h1 : r.todd (eE a) = r.todd (eE b) := congrArg Subtype.val hab
  have h2 : eE a = eE b := r.todd.injective h1
  apply Subtype.ext
  apply Subtype.ext
  simpa only using congrArg Subtype.val h2

theorem map_E_I_of_aut (hOff : M24G.SextStabOffender) (r : ResM24T c)
    (hU : r.U₀ = M24G.sextFin 0) (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1)) :
    (c.E.subgroupOf (c.G3 ⊓ c.G1)).map θ.toMonoidHom = c.E.subgroupOf (c.G3 ⊓ c.G1) := by
  classical
  set EI : Subgroup ↥(c.G3 ⊓ c.G1) := c.E.subgroupOf (c.G3 ⊓ c.G1) with hEI
  haveI hEnorm : EI.Normal := c.normal_E_subgroupOf
  set E' : Subgroup ↥(c.G3 ⊓ c.G1) := EI.map θ.toMonoidHom with hE'
  set B : Subgroup ↥M24G.sextStab := E'.map (c.phiS r hU) with hB
  have hE'el : CFSG.Open.IsElemAbelian 2 E' := by
    rw [hE']
    exact (c.isElemAbelian_E_subgroupOf).map θ.toMonoidHom
  have hE'card : Nat.card ↥E' = 2 ^ 11 := by
    rw [hE', Subgroup.card_map_of_injective (f := θ.toMonoidHom)
      (by simpa only [MulEquiv.coe_toMonoidHom] using θ.injective), c.card_E_subgroupOf]
  have hBnorm : B.Normal := by
    rw [hB]
    exact (hEnorm.map θ.toMonoidHom
      (by simpa only [MulEquiv.coe_toMonoidHom] using θ.surjective)).map
      (c.phiS r hU) (c.phiS_surjective r hU)
  have hBpg : IsPGroup 2 B := by
    rw [hB]
    exact hE'el.isPGroup.map (c.phiS r hU)
  by_cases hBbot : B = ⊥
  · have hle : E' ≤ EI := by
      have h := (Subgroup.map_eq_bot_iff E' (f := c.phiS r hU)).mp hBbot
      rwa [c.ker_phiS r hU] at h
    have hEq : E' = EI :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [c.card_E_subgroupOf, hE'card])
    exact hEq
  · exfalso
    have hcard := c.card_eq_card_inf_mul_card_map r hU E'
    have hleB : Nat.card ↥(E' ⊓ EI) ≤
        Nat.card {w : W11 // ∀ b ∈ B,
          rho11 M24G.sextStab M24G.sextStab_le b w = w} := by
      simpa only [hB] using c.card_inf_le_fixed r hU hE'el
    have hcardB : Nat.card ↥E' = Nat.card ↥(E' ⊓ EI) * Nat.card ↥B := by
      rw [hcard, ← hB]
    have hlt := hOff B hBnorm hBpg hBbot
    have h1 : Nat.card ↥(E' ⊓ EI) * Nat.card ↥B ≤
        Nat.card {w : W11 // ∀ b ∈ B,
          rho11 M24G.sextStab M24G.sextStab_le b w = w} * Nat.card ↥B :=
      Nat.mul_le_mul_right _ hleB
    have h2 : Nat.card ↥E' < 2 ^ 11 := by
      rw [hcardB]
      exact lt_of_le_of_lt h1 hlt
    omega

noncomputable def quotientEquivS (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    [hEnorm : (c.E.subgroupOf (c.G3 ⊓ c.G1)).Normal] :
    ↥(c.G3 ⊓ c.G1) ⧸ c.E.subgroupOf (c.G3 ⊓ c.G1) ≃* ↥M24G.sextStab := by
  classical
  let θe : ↥(c.G3 ⊓ c.G1) ⧸ c.E.subgroupOf (c.G3 ⊓ c.G1) →* ↥M24G.sextStab :=
    QuotientGroup.lift (c.E.subgroupOf (c.G3 ⊓ c.G1)) (c.phiS r hU) (by rw [c.ker_phiS r hU])
  have hθe_inj : Function.Injective θe := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [Subgroup.mem_bot, MonoidHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
      rw [QuotientGroup.lift_mk, c.phiS_eq_one_iff] at hx
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hx
    · intro hx
      rw [hx, _root_.map_one]
  have hθe_surj : Function.Surjective θe := by
    intro s
    obtain ⟨h, hh⟩ := c.phiS_surjective r hU s
    exact ⟨QuotientGroup.mk h, by rw [QuotientGroup.lift_mk]; exact hh⟩
  exact MulEquiv.ofBijective θe ⟨hθe_inj, hθe_surj⟩

theorem quotientEquivS_mk (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    [hEnorm : (c.E.subgroupOf (c.G3 ⊓ c.G1)).Normal] (h : ↥(c.G3 ⊓ c.G1)) :
    c.quotientEquivS r hU (QuotientGroup.mk h) = c.phiS r hU h := by
  classical
  exact QuotientGroup.lift_mk (c.E.subgroupOf (c.G3 ⊓ c.G1)) (φ := c.phiS r hU)
    (by rw [c.ker_phiS r hU]) h

noncomputable def autQuotient (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) :
    ↥M24G.sextStab ≃* ↥M24G.sextStab := by
  haveI hEnorm : (c.E.subgroupOf (c.G3 ⊓ c.G1)).Normal := c.normal_E_subgroupOf
  exact (c.quotientEquivS r hU).symm.trans
    ((QuotientGroup.congr (c.E.subgroupOf (c.G3 ⊓ c.G1)) (c.E.subgroupOf (c.G3 ⊓ c.G1))
      θ hθ).trans (c.quotientEquivS r hU))

theorem autQuotient_phiS (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) (h : ↥(c.G3 ⊓ c.G1)) :
    c.autQuotient r hU θ hθ (c.phiS r hU h) = c.phiS r hU (θ h) := by
  classical
  haveI hEnorm : (c.E.subgroupOf (c.G3 ⊓ c.G1)).Normal := c.normal_E_subgroupOf
  have hsymm : (c.quotientEquivS r hU).symm (c.phiS r hU h) = QuotientGroup.mk h := by
    rw [← c.quotientEquivS_mk r hU h, MulEquiv.symm_apply_apply]
  unfold autQuotient
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hsymm, QuotientGroup.congr_mk,
    c.quotientEquivS_mk]

end Loc49

namespace Loc49

open Subgroup CFSG.Quasithin.H.Mathieu
open CFSG.ASVolI.ChH (M24g S24)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

noncomputable def conjAut (g : ↥(c.G3 ⊓ c.G1))
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1)) :
    ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1) :=
  θ.trans (MulAut.conj g)⁻¹

theorem conjAut_apply (g : ↥(c.G3 ⊓ c.G1))
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1)) (h : ↥(c.G3 ⊓ c.G1)) :
    c.conjAut g θ h = (g⁻¹ : ↥(c.G3 ⊓ c.G1)) * θ h * g := by
  rw [conjAut, MulEquiv.trans_apply, ← map_inv, MulAut.conj_apply]
  group

theorem phiS_conjAut (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (g : ↥(c.G3 ⊓ c.G1)) (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) (n : ↥M24G.sextStab)
    (hg : c.phiS r hU g = n)
    (hθbar : ∀ s : ↥M24G.sextStab, c.autQuotient r hU θ hθ s = n * s * n⁻¹)
    (h : ↥(c.G3 ⊓ c.G1)) :
    c.phiS r hU (c.conjAut g θ h) = c.phiS r hU h := by
  have hθh : c.phiS r hU (θ h) = n * c.phiS r hU h * n⁻¹ := by
    rw [← c.autQuotient_phiS r hU θ hθ h, hθbar]
  rw [c.conjAut_apply g θ h, map_mul, map_mul, map_inv, hg, hθh]
  group

theorem conjAut_mul_mem_E (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (g : ↥(c.G3 ⊓ c.G1)) (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) (n : ↥M24G.sextStab)
    (hg : c.phiS r hU g = n)
    (hθbar : ∀ s : ↥M24G.sextStab, c.autQuotient r hU θ hθ s = n * s * n⁻¹)
    (h : ↥(c.G3 ⊓ c.G1)) :
    h⁻¹ * c.conjAut g θ h ∈ c.E.subgroupOf (c.G3 ⊓ c.G1) := by
  rw [Subgroup.mem_subgroupOf, ← c.phiS_eq_one_iff r hU]
  change c.phiS r hU (h⁻¹ * c.conjAut g θ h) = 1
  rw [map_mul, map_inv, c.phiS_conjAut r hU g θ hθ n hg hθbar h, inv_mul_cancel]

theorem conjAut_map_E_I (g : ↥(c.G3 ⊓ c.G1))
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) :
    (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑(c.conjAut g θ)) =
      c.E.subgroupOf (c.G3 ⊓ c.G1) := by
  haveI hEnorm : (c.E.subgroupOf (c.G3 ⊓ c.G1)).Normal := c.normal_E_subgroupOf
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyθ : θ y ∈ c.E.subgroupOf (c.G3 ⊓ c.G1) := by
      rw [← hθ]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hconj : g⁻¹ * θ y * g ∈ c.E.subgroupOf (c.G3 ⊓ c.G1) :=
      hEnorm.conj_mem' (θ y) hyθ g
    change c.conjAut g θ y ∈ c.E.subgroupOf (c.G3 ⊓ c.G1)
    rwa [c.conjAut_apply g θ y]
  · rw [← MulEquiv.toMonoidHom_eq_coe]
    rw [Subgroup.card_map_of_injective (f := (c.conjAut g θ).toMonoidHom)
      (by simpa only [MulEquiv.coe_toMonoidHom] using (c.conjAut g θ).injective)]

noncomputable def conjAutEquivE (g : ↥(c.G3 ⊓ c.G1))
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) : ↥c.E ≃* ↥c.E := by
  classical
  have hmap : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑(c.conjAut g θ)) =
      c.E.subgroupOf (c.G3 ⊓ c.G1) := c.conjAut_map_E_I g θ hθ
  let φE : ↥c.E →* ↥c.E :=
    { toFun := fun e => ⟨(c.conjAut g θ ⟨(e : G), c.E_le_G3_inf_G1 e.2⟩ : G), by
        have hmem : c.conjAut g θ ⟨(e : G), c.E_le_G3_inf_G1 e.2⟩ ∈
            c.E.subgroupOf (c.G3 ⊓ c.G1) := by
          rw [← hmap]
          exact Subgroup.mem_map.mpr ⟨⟨(e : G), c.E_le_G3_inf_G1 e.2⟩,
            Subgroup.mem_subgroupOf.mpr e.2, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hmem⟩
      map_one' := by
        apply Subtype.ext
        change ((c.conjAut g θ (1 : ↥(c.G3 ⊓ c.G1)) : ↥(c.G3 ⊓ c.G1)) : G) = 1
        rw [map_one]
        rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        show ((c.conjAut g θ ⟨((a * b : ↥c.E) : G),
            c.E_le_G3_inf_G1 (a * b).2⟩ : ↥(c.G3 ⊓ c.G1)) : G) =
          ((c.conjAut g θ ⟨(a : G), c.E_le_G3_inf_G1 a.2⟩ : ↥(c.G3 ⊓ c.G1)) : G) *
            ((c.conjAut g θ ⟨(b : G), c.E_le_G3_inf_G1 b.2⟩ : ↥(c.G3 ⊓ c.G1)) : G)
        have harg : (⟨((a * b : ↥c.E) : G), c.E_le_G3_inf_G1 (a * b).2⟩ :
              ↥(c.G3 ⊓ c.G1)) =
            ⟨(a : G), c.E_le_G3_inf_G1 a.2⟩ * ⟨(b : G), c.E_le_G3_inf_G1 b.2⟩ :=
          Subtype.ext rfl
        rw [harg, map_mul]
        rfl }
  have hinj : Function.Injective φE := by
    intro a b hab
    have h1 : c.conjAut g θ ⟨(a : G), c.E_le_G3_inf_G1 a.2⟩ =
        c.conjAut g θ ⟨(b : G), c.E_le_G3_inf_G1 b.2⟩ :=
      Subtype.ext (congrArg (fun x : ↥c.E => (x : G)) hab)
    have h2 : (⟨(a : G), c.E_le_G3_inf_G1 a.2⟩ : ↥(c.G3 ⊓ c.G1)) =
        ⟨(b : G), c.E_le_G3_inf_G1 b.2⟩ :=
      (c.conjAut g θ).injective h1
    exact Subtype.ext (congrArg (fun x : ↥(c.G3 ⊓ c.G1) => (x : G)) h2)
  exact MulEquiv.ofBijective φE ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

theorem conjAut_apply_of_mem_E (hEnd : M24G.SextStabEndScalar) (r : ResM24T c)
    (hU : r.U₀ = M24G.sextFin 0) (g : ↥(c.G3 ⊓ c.G1))
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) (n : ↥M24G.sextStab)
    (hg : c.phiS r hU g = n)
    (hθbar : ∀ s : ↥M24G.sextStab, c.autQuotient r hU θ hθ s = n * s * n⁻¹)
    (e : ↥c.E) :
    (c.conjAut g θ ⟨(e : G), c.E_le_G3_inf_G1 e.2⟩ : ↥(c.G3 ⊓ c.G1)) =
      ⟨(e : G), c.E_le_G3_inf_G1 e.2⟩ := by
  classical
  let f : W11 ≃* W11 := r.todd.symm.trans ((c.conjAutEquivE g θ hθ).trans r.todd)
  have hf_apply : ∀ e : ↥c.E, f (r.todd e) = r.todd (c.conjAutEquivE g θ hθ e) := by
    intro e
    simp only [f, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hcomm : ∀ (s : ↥M24G.sextStab) (w : W11),
      f (rho11 M24G.sextStab M24G.sextStab_le s w) =
        rho11 M24G.sextStab M24G.sextStab_le s (f w) := by
    intro s w
    obtain ⟨h, rfl⟩ := c.phiS_surjective r hU s
    obtain ⟨e, rfl⟩ := r.todd.surjective w
    let a : ↥(c.G3 ⊓ c.G1) := c.conjAut g θ h
    let Ee : ↥c.E := c.conjAutEquivE g θ hθ e
    let e' : ↥c.E := ⟨(h : G) * (e : G) * (h : G)⁻¹,
      c.conj_mem_E ⟨(h : G), (Subgroup.mem_inf.mp h.2).2⟩ e.2⟩
    have hEqE : c.conjAutEquivE g θ hθ e' =
        ⟨(a : G) * (Ee : G) * (a : G)⁻¹,
          c.conj_mem_E ⟨(a : G), (Subgroup.mem_inf.mp a.2).2⟩ Ee.2⟩ := by
      apply Subtype.ext
      change (c.conjAut g θ ⟨(e' : G), c.E_le_G3_inf_G1 e'.2⟩ : G) =
        (a : G) * (Ee : G) * (a : G)⁻¹
      have harg : (⟨(e' : G), c.E_le_G3_inf_G1 e'.2⟩ : ↥(c.G3 ⊓ c.G1)) =
          h * ⟨(e : G), c.E_le_G3_inf_G1 e.2⟩ * h⁻¹ := by
        apply Subtype.ext
        exact rfl
      rw [harg, map_mul, map_mul, map_inv]
      rfl
    calc f (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) (r.todd e))
        = f (r.todd e') := by rw [c.todd_conj_phiS r hU h e]
      _ = r.todd (c.conjAutEquivE g θ hθ e') := hf_apply e'
      _ = r.todd ⟨(a : G) * (Ee : G) * (a : G)⁻¹,
            c.conj_mem_E ⟨(a : G), (Subgroup.mem_inf.mp a.2).2⟩ Ee.2⟩ :=
          congrArg r.todd hEqE
      _ = rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU a) (r.todd Ee) :=
          c.todd_conj_phiS r hU a Ee
      _ = rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) (r.todd Ee) := by
          rw [c.phiS_conjAut r hU g θ hθ n hg hθbar h]
      _ = rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h) (f (r.todd e)) := by
          rw [hf_apply e]
  have hfix := hEnd f hcomm
  have hfe : r.todd (c.conjAutEquivE g θ hθ e) = r.todd e := by
    rw [← hf_apply e]
    exact hfix (r.todd e)
  have hEe : c.conjAutEquivE g θ hθ e = e := r.todd.injective hfe
  apply Subtype.ext
  exact congrArg (fun x : ↥c.E => (x : G)) hEe

noncomputable def cocycleFun (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (g : ↥(c.G3 ⊓ c.G1)) (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) (n : ↥M24G.sextStab)
    (hg : c.phiS r hU g = n)
    (hθbar : ∀ s : ↥M24G.sextStab, c.autQuotient r hU θ hθ s = n * s * n⁻¹)
    (h : ↥(c.G3 ⊓ c.G1)) : W11 :=
  r.todd ⟨((h⁻¹ * c.conjAut g θ h : ↥(c.G3 ⊓ c.G1)) : G),
    Subgroup.mem_subgroupOf.mp (c.conjAut_mul_mem_E r hU g θ hθ n hg hθbar h)⟩

theorem cocycleFun_mul_E (hEnd : M24G.SextStabEndScalar) (r : ResM24T c)
    (hU : r.U₀ = M24G.sextFin 0) (g : ↥(c.G3 ⊓ c.G1))
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) (n : ↥M24G.sextStab)
    (hg : c.phiS r hU g = n)
    (hθbar : ∀ s : ↥M24G.sextStab, c.autQuotient r hU θ hθ s = n * s * n⁻¹)
    (h : ↥(c.G3 ⊓ c.G1)) (e : ↥c.E) :
    c.cocycleFun r hU g θ hθ n hg hθbar (h * ⟨(e : G), c.E_le_G3_inf_G1 e.2⟩) =
      c.cocycleFun r hU g θ hθ n hg hθbar h := by
  let eI : ↥(c.G3 ⊓ c.G1) := ⟨(e : G), c.E_le_G3_inf_G1 e.2⟩
  let X : ↥c.E := ⟨((h⁻¹ * c.conjAut g θ h : ↥(c.G3 ⊓ c.G1)) : G),
    Subgroup.mem_subgroupOf.mp (c.conjAut_mul_mem_E r hU g θ hθ n hg hθbar h)⟩
  have hθe : c.conjAut g θ eI = eI :=
    c.conjAut_apply_of_mem_E hEnd r hU g θ hθ n hg hθbar e
  have hcomm : (X : G) * (e : G) = (e : G) * (X : G) :=
    congrArg (fun x : ↥c.E => (x : G)) (c.E_elem.1.is_comm.comm X e)
  change r.todd ⟨(((h * eI)⁻¹ * c.conjAut g θ (h * eI) : ↥(c.G3 ⊓ c.G1)) : G),
      _⟩ = r.todd ⟨((h⁻¹ * c.conjAut g θ h : ↥(c.G3 ⊓ c.G1)) : G), _⟩
  apply congrArg r.todd
  apply Subtype.ext
  have hval : (((h * eI)⁻¹ * c.conjAut g θ (h * eI) : ↥(c.G3 ⊓ c.G1)) : G) =
      (eI : G)⁻¹ * ((h⁻¹ * c.conjAut g θ h : ↥(c.G3 ⊓ c.G1)) : G) * (eI : G) := by
    rw [map_mul, hθe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hval]
  have heI : (eI : G) = (e : G) := rfl
  have hX : ((h⁻¹ * c.conjAut g θ h : ↥(c.G3 ⊓ c.G1)) : G) = (X : G) := rfl
  rw [heI, hX]
  calc (e : G)⁻¹ * (X : G) * (e : G) = (e : G)⁻¹ * ((X : G) * (e : G)) := by group
    _ = (e : G)⁻¹ * ((e : G) * (X : G)) := by rw [hcomm]
    _ = (X : G) := by group

noncomputable def cocycleOfAut (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (g : ↥(c.G3 ⊓ c.G1)) (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) (n : ↥M24G.sextStab)
    (hg : c.phiS r hU g = n)
    (hθbar : ∀ s : ↥M24G.sextStab, c.autQuotient r hU θ hθ s = n * s * n⁻¹) :
    ↥M24G.sextStab → W11 :=
  fun s => c.cocycleFun r hU g θ hθ n hg hθbar
    (Function.surjInv (c.phiS_surjective r hU) s)

theorem cocycleOfAut_phiS (hEnd : M24G.SextStabEndScalar) (r : ResM24T c)
    (hU : r.U₀ = M24G.sextFin 0) (g : ↥(c.G3 ⊓ c.G1))
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) (n : ↥M24G.sextStab)
    (hg : c.phiS r hU g = n)
    (hθbar : ∀ s : ↥M24G.sextStab, c.autQuotient r hU θ hθ s = n * s * n⁻¹)
    (h : ↥(c.G3 ⊓ c.G1)) :
    c.cocycleOfAut r hU g θ hθ n hg hθbar (c.phiS r hU h) =
      c.cocycleFun r hU g θ hθ n hg hθbar h := by
  unfold cocycleOfAut
  let a : ↥(c.G3 ⊓ c.G1) := Function.surjInv (c.phiS_surjective r hU) (c.phiS r hU h)
  have ha : c.phiS r hU a = c.phiS r hU h := Function.surjInv_eq _ _
  have he : a⁻¹ * h ∈ c.E.subgroupOf (c.G3 ⊓ c.G1) := by
    rw [Subgroup.mem_subgroupOf, ← c.phiS_eq_one_iff r hU]
    change c.phiS r hU (a⁻¹ * h) = 1
    rw [map_mul, map_inv, ha, inv_mul_cancel]
  let e : ↥c.E := ⟨((a⁻¹ * h : ↥(c.G3 ⊓ c.G1)) : G), Subgroup.mem_subgroupOf.mp he⟩
  have hh : h = a * ⟨(e : G), c.E_le_G3_inf_G1 e.2⟩ := by
    apply Subtype.ext
    show (h : G) = (a : G) * ((a⁻¹ * h : ↥(c.G3 ⊓ c.G1)) : G)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  change c.cocycleFun r hU g θ hθ n hg hθbar a =
    c.cocycleFun r hU g θ hθ n hg hθbar h
  rw [hh, c.cocycleFun_mul_E hEnd r hU g θ hθ n hg hθbar a e]

theorem isRightCocycle_cocycleOfAut (hEnd : M24G.SextStabEndScalar) (r : ResM24T c)
    (hU : r.U₀ = M24G.sextFin 0) (g : ↥(c.G3 ⊓ c.G1))
    (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1))
    (hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1)) (n : ↥M24G.sextStab)
    (hg : c.phiS r hU g = n)
    (hθbar : ∀ s : ↥M24G.sextStab, c.autQuotient r hU θ hθ s = n * s * n⁻¹) :
    M24G.IsRightCocycle M24G.sextStab M24G.sextStab_le
      (c.cocycleOfAut r hU g θ hθ n hg hθbar) := by
  intro s t
  obtain ⟨h, rfl⟩ := c.phiS_surjective r hU s
  obtain ⟨k, rfl⟩ := c.phiS_surjective r hU t
  rw [← map_mul, c.cocycleOfAut_phiS hEnd r hU g θ hθ n hg hθbar (h * k),
    c.cocycleOfAut_phiS hEnd r hU g θ hθ n hg hθbar h,
    c.cocycleOfAut_phiS hEnd r hU g θ hθ n hg hθbar k]
  let X : ↥c.E := ⟨((h⁻¹ * c.conjAut g θ h : ↥(c.G3 ⊓ c.G1)) : G),
    Subgroup.mem_subgroupOf.mp (c.conjAut_mul_mem_E r hU g θ hθ n hg hθbar h)⟩
  let Y : ↥c.E := ⟨((k⁻¹ * c.conjAut g θ k : ↥(c.G3 ⊓ c.G1)) : G),
    Subgroup.mem_subgroupOf.mp (c.conjAut_mul_mem_E r hU g θ hθ n hg hθbar k)⟩
  let C : ↥c.E := ⟨((k⁻¹ : ↥(c.G3 ⊓ c.G1)) : G) * (X : G) *
      (((k⁻¹ : ↥(c.G3 ⊓ c.G1)) : G))⁻¹,
    c.conj_mem_E (Subgroup.inclusion inf_le_right (k⁻¹)) X.2⟩
  have hX : c.cocycleFun r hU g θ hθ n hg hθbar h = r.todd X := rfl
  have hY : c.cocycleFun r hU g θ hθ n hg hθbar k = r.todd Y := rfl
  have hDhk : c.cocycleFun r hU g θ hθ n hg hθbar (h * k) = r.todd (C * Y) := by
    unfold cocycleFun
    apply congrArg r.todd
    apply Subtype.ext
    change (((h * k)⁻¹ * c.conjAut g θ (h * k) : ↥(c.G3 ⊓ c.G1)) : G) =
      (C : G) * (Y : G)
    have hCval : (C : G) = ((k⁻¹ : ↥(c.G3 ⊓ c.G1)) : G) * (X : G) *
        (((k⁻¹ : ↥(c.G3 ⊓ c.G1)) : G))⁻¹ := rfl
    have hXval : (X : G) = ((h⁻¹ * c.conjAut g θ h : ↥(c.G3 ⊓ c.G1)) : G) := rfl
    have hYval : (Y : G) = ((k⁻¹ * c.conjAut g θ k : ↥(c.G3 ⊓ c.G1)) : G) := rfl
    rw [hCval, hXval, hYval, map_mul]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hX, hY, hDhk, map_mul]
  have hC : r.todd C = rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU k⁻¹) (r.todd X) :=
    c.todd_conj_phiS r hU k⁻¹ X
  rw [hC, map_inv (c.phiS r hU) k,
    ← map_inv (rho11 M24G.sextStab M24G.sextStab_le) (c.phiS r hU k)]

theorem isInnerCocycle_of_aut (hOff : M24G.SextStabOffender)
    (hInn : M24G.SextStabAutInner) (hEnd : M24G.SextStabEndScalar)
    {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z) (r : ResM24T c)
    (hU : r.U₀ = M24G.sextFin 0) (θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1)) :
    c.IsInnerCocycle r hU θ := by
  classical
  have hθ : (c.E.subgroupOf (c.G3 ⊓ c.G1)).map (↑θ) =
      c.E.subgroupOf (c.G3 ⊓ c.G1) := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using c.map_E_I_of_aut hOff r hU θ
  obtain ⟨n, hn⟩ := hInn (c.autQuotient r hU θ hθ)
  obtain ⟨g, hg⟩ := c.phiS_surjective r hU n
  refine ⟨(g : G), c.cocycleOfAut r hU g θ hθ n hg hn, g.2, ?_, ?_⟩
  · exact c.isRightCocycle_cocycleOfAut hEnd r hU g θ hθ n hg hn
  · intro h
    have hθeq : ∀ x : ↥(c.G3 ⊓ c.G1),
        θ x = (MulAut.conj g) (c.conjAut g θ x) := by
      intro x
      rw [c.conjAut_apply g θ x, MulAut.conj_apply]
      group
    have hstep : c.conjAut g θ h =
        h * ⟨(r.todd.symm (c.cocycleOfAut r hU g θ hθ n hg hn (c.phiS r hU h)) : G),
          c.E_le_G3_inf_G1 (r.todd.symm
            (c.cocycleOfAut r hU g θ hθ n hg hn (c.phiS r hU h))).2⟩ := by
      apply Subtype.ext
      rw [c.cocycleOfAut_phiS hEnd r hU g θ hθ n hg hn h]
      unfold cocycleFun
      rw [MulEquiv.symm_apply_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      group
    have h1 : ((θ h : ↥(c.G3 ⊓ c.G1)) : G) =
        (g : G) * ((c.conjAut g θ h : ↥(c.G3 ⊓ c.G1)) : G) * (g : G)⁻¹ := by
      have := congrArg (fun x : ↥(c.G3 ⊓ c.G1) => (x : G)) (hθeq h)
      rw [MulAut.conj_apply] at this
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have h2 : ((c.conjAut g θ h : ↥(c.G3 ⊓ c.G1)) : G) =
        (h : G) * ((r.todd.symm
          (c.cocycleOfAut r hU g θ hθ n hg hn (c.phiS r hU h)) : ↥c.E) : G) := by
      have := congrArg (fun x : ↥(c.G3 ⊓ c.G1) => (x : G)) hstep
      simpa only [Subgroup.coe_mul, Subgroup.coe_mk] using this
    rw [h1, h2]

end Loc49

end CFSG.Quasithin.H13.AS91
