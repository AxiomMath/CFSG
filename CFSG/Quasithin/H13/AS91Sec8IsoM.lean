module

public import CFSG.Quasithin.H13.AS91Sec5Todd
public import CFSG.GroupTheory.InternalSemidirectEquiv
public import CFSG.Quasithin.H13.AS91Sec5Local

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.GroupTheory
open CFSG.ASVolI.ChH (M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

noncomputable def compl : Subgroup G := c.split.choose

theorem compl_le_G1 : c.compl ≤ c.G1 := c.split.choose_spec.1

theorem compl_inf_E : c.compl ⊓ c.E = ⊥ := c.split.choose_spec.2.1

theorem sup_compl_eq_G1 : c.E ⊔ c.compl = c.G1 := by
  change c.E ⊔ c.split.choose = c.G1
  rw [sup_comm]
  exact c.split.choose_spec.2.2

theorem disjoint_E_compl : Disjoint c.E c.compl := by
  rw [disjoint_iff, inf_comm, c.compl_inf_E]

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

theorem exists_mulEquiv_compl {L : Subgroup G} (hL : L ≤ c.G1) (hLE : L ⊓ c.E = ⊥)
    (hsup : L ⊔ c.E = c.G1) :
    ∃ e : ↥L ≃* ↥M24g, ∀ l : ↥L,
      (e l : Equiv.Perm (Fin 24)) = ρ.φ ⟨(l : G), hL l.2⟩ := by
  classical
  let φL : ↥L →* ↥M24g :=
    (ρ.φ.comp (Subgroup.inclusion hL)).codRestrict M24g (fun l => ρ.φ_mem _)
  have hinj : Function.Injective φL := by
    rw [injective_iff_map_eq_one]
    intro l hl
    apply Subtype.ext
    have hker : Subgroup.inclusion hL l ∈ ρ.φ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hl
    rw [ρ.ker_eq, Subgroup.mem_subgroupOf] at hker
    have hmem : (l : G) ∈ L ⊓ c.E := ⟨l.2, hker⟩
    rw [hLE] at hmem
    simpa using hmem
  have hsurj : Function.Surjective φL := by
    intro m
    obtain ⟨g, hg⟩ := ρ.exists_φ_eq m.2
    have hmem : (g : G) ∈ c.E ⊔ L := by
      rw [sup_comm, hsup]
      exact g.2
    change (g : G) ∈ (↑(c.E ⊔ L) : Set G) at hmem
    rw [Subgroup.coe_mul_of_right_le_normalizer_left c.E L hL] at hmem
    obtain ⟨e, he, l, hl, hge⟩ := hmem
    refine ⟨⟨l, hl⟩, ?_⟩
    apply Subtype.ext
    have hφe : ρ.φ ⟨e, c.E_le_G1 he⟩ = 1 := by
      have h1 : (⟨e, c.E_le_G1 he⟩ : ↥c.G1) ∈ ρ.φ.ker := by
        rw [ρ.ker_eq, Subgroup.mem_subgroupOf]
        exact he
      exact h1
    have hφmul : ρ.φ g = ρ.φ ⟨e, c.E_le_G1 he⟩ * ρ.φ ⟨l, hL hl⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      exact hge.symm
    have hm : (m : Equiv.Perm (Fin 24)) = ρ.φ ⟨l, hL hl⟩ := by
      rw [← hg, hφmul, hφe, one_mul]
    exact hm.symm
  let e : ↥L ≃* ↥M24g := MulEquiv.ofBijective φL ⟨hinj, hsurj⟩
  refine ⟨e, fun l => ?_⟩
  change (e l : Equiv.Perm (Fin 24)) = ρ.φ ⟨(l : G), hL l.2⟩
  rw [show e l = φL l from MulEquiv.ofBijective_apply φL ⟨hinj, hsurj⟩ l]
  rfl

end ResM24

namespace ResM24T

variable {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
  {z : G} {z' : G'} {c : Loc49 G z} {c' : Loc49 G' z'}

theorem exists_mulEquiv (r : ResM24T c) (r' : ResM24T c')
    (σ : Equiv.Perm (Fin 24)) (hσ : σ ∈ M24g) :
    ∃ α : ↥c.G1 ≃* ↥c'.G1, ∀ h : ↥c.G1, r'.φ (α h) = σ * r.φ h * σ⁻¹ := by
  classical
  let L : Subgroup G := c.compl
  let L' : Subgroup G' := c'.compl
  have hLle : L ≤ c.G1 := c.compl_le_G1
  have hLE : L ⊓ c.E = ⊥ := c.compl_inf_E
  have hsup : L ⊔ c.E = c.G1 := by
    rw [sup_comm]
    exact c.sup_compl_eq_G1
  have hL'le : L' ≤ c'.G1 := c'.compl_le_G1
  have hL'E : L' ⊓ c'.E = ⊥ := c'.compl_inf_E
  have hsup' : L' ⊔ c'.E = c'.G1 := by
    rw [sup_comm]
    exact c'.sup_compl_eq_G1
  have hd : Disjoint c.E L := c.disjoint_E_compl
  have hd' : Disjoint c'.E L' := c'.disjoint_E_compl
  obtain ⟨eL, heL⟩ := ResM24.exists_mulEquiv_compl r.toResM24 hLle hLE hsup
  obtain ⟨eL', heL'⟩ := ResM24.exists_mulEquiv_compl r'.toResM24 hL'le hL'E hsup'
  let Θ : ↥c.E ≃* ↥c'.E := r.todd.trans r'.todd.symm
  let Λ : ↥L ≃* ↥L' := eL.trans eL'.symm
  have hφlam : ∀ l : ↥L,
      r'.φ ⟨(Λ l : G'), hL'le (Λ l).2⟩ = r.φ ⟨(l : G), hLle l.2⟩ := by
    intro l
    have h1 : eL' (Λ l) = eL l := by
      change eL' (eL'.symm (eL l)) = eL l
      exact MulEquiv.apply_symm_apply eL' (eL l)
    calc r'.φ ⟨(Λ l : G'), hL'le (Λ l).2⟩
        = (eL' (Λ l) : Equiv.Perm (Fin 24)) := (heL' (Λ l)).symm
      _ = (eL l : Equiv.Perm (Fin 24)) := congrArg Subtype.val h1
      _ = r.φ ⟨(l : G), hLle l.2⟩ := heL l
  have hcompat : ∀ (k : ↥L) (q : ↥c.E)
      (hq : (k : G) * q * (k : G)⁻¹ ∈ c.E),
      ((Θ ⟨(k : G) * q * (k : G)⁻¹, hq⟩ : ↥c'.E) : G') =
        (Λ k : G') * (Θ q : G') * (Λ k : G')⁻¹ := by
    intro k q hq
    let hk : ↥c.G1 := ⟨(k : G), hLle k.2⟩
    let hk' : ↥c'.G1 := ⟨(Λ k : G'), hL'le (Λ k).2⟩
    have hmemA : r.φ hk ∈ CFSG.Monster.Code.AutPerm := by
      simpa [M24g] using r.φ_mem hk
    have hmemB : r'.φ hk' ∈ CFSG.Monster.Code.AutPerm := by
      simpa [M24g] using r'.φ_mem hk'
    have hΘ : r'.todd (Θ q) = r.todd q := by
      change r'.todd (r'.todd.symm (r.todd q)) = r.todd q
      exact MulEquiv.apply_symm_apply r'.todd (r.todd q)
    have htodd : r'.todd (Θ ⟨(k : G) * q * (k : G)⁻¹, hq⟩) =
        r'.todd (conjHom c'.E L' hL'le (Λ k) (Θ q)) := by
      calc r'.todd (Θ ⟨(k : G) * q * (k : G)⁻¹, hq⟩)
          = r.todd ⟨(k : G) * q * (k : G)⁻¹, hq⟩ := by
            change r'.todd (r'.todd.symm (r.todd ⟨(k : G) * q * (k : G)⁻¹, hq⟩)) =
              r.todd ⟨(k : G) * q * (k : G)⁻¹, hq⟩
            exact MulEquiv.apply_symm_apply r'.todd _
        _ = CFSG.Quasithin.H.Mathieu.rho11 CFSG.Monster.Code.AutPerm le_rfl
              ⟨r.φ hk, hmemA⟩ (r.todd q) := by
            simpa [hk] using r.todd_equiv hk q
        _ = CFSG.Quasithin.H.Mathieu.rho11 CFSG.Monster.Code.AutPerm le_rfl
              ⟨r'.φ hk', hmemB⟩ (r'.todd (Θ q)) := by
            have hAB : (⟨r.φ hk, hmemA⟩ : ↥CFSG.Monster.Code.AutPerm) =
                ⟨r'.φ hk', hmemB⟩ := by
              apply Subtype.ext
              exact (hφlam k).symm
            rw [← hAB, hΘ]
        _ = r'.todd (conjHom c'.E L' hL'le (Λ k) (Θ q)) := by
            symm
            rw [conjHom_val]
            simpa [hk'] using r'.todd_equiv hk' (Θ q)
    have hEq : Θ ⟨(k : G) * q * (k : G)⁻¹, hq⟩ =
        conjHom c'.E L' hL'le (Λ k) (Θ q) := r'.todd.injective htodd
    calc ((Θ ⟨(k : G) * q * (k : G)⁻¹, hq⟩ : ↥c'.E) : G')
        = ((conjHom c'.E L' hL'le (Λ k) (Θ q) : ↥c'.E) : G') :=
          congrArg Subtype.val hEq
      _ = (Λ k : G') * (Θ q : G') * (Λ k : G')⁻¹ :=
          conjHom_apply hL'le (Λ k) (Θ q)
  obtain ⟨α₀, hα₀E, hα₀L⟩ :=
    exists_mulEquiv_sup_extend hLle hd hL'le hd' Θ Λ hcompat
  let α₁ : ↥c.G1 ≃* ↥c'.G1 :=
    (MulEquiv.subgroupCongr c.sup_compl_eq_G1).symm.trans
      (α₀.trans (MulEquiv.subgroupCongr c'.sup_compl_eq_G1))
  have hα₁E : ∀ (e : G) (he : e ∈ c.E),
      α₁ ⟨e, c.E_le_G1 he⟩ =
        ⟨((Θ ⟨e, he⟩ : ↥c'.E) : G'), c'.E_le_G1 (Θ ⟨e, he⟩).2⟩ := by
    intro e he
    apply Subtype.ext
    calc (α₁ ⟨e, c.E_le_G1 he⟩ : G')
        = (α₀ ((MulEquiv.subgroupCongr c.sup_compl_eq_G1).symm
            ⟨e, c.E_le_G1 he⟩) : G') := by
          change ((MulEquiv.subgroupCongr c'.sup_compl_eq_G1)
            (α₀ ((MulEquiv.subgroupCongr c.sup_compl_eq_G1).symm
              ⟨e, c.E_le_G1 he⟩)) : G') = _
          rw [MulEquiv.subgroupCongr_apply]
      _ = (α₀ ⟨e, Subgroup.mem_sup_left he⟩ : G') := by
          congr 1
      _ = (Θ ⟨e, he⟩ : G') := hα₀E ⟨e, he⟩
  have hα₁L : ∀ (l : G) (hl : l ∈ L),
      α₁ ⟨l, hLle hl⟩ =
        ⟨((Λ ⟨l, hl⟩ : ↥L') : G'), hL'le (Λ ⟨l, hl⟩).2⟩ := by
    intro l hl
    apply Subtype.ext
    calc (α₁ ⟨l, hLle hl⟩ : G')
        = (α₀ ((MulEquiv.subgroupCongr c.sup_compl_eq_G1).symm
            ⟨l, hLle hl⟩) : G') := by
          change ((MulEquiv.subgroupCongr c'.sup_compl_eq_G1)
            (α₀ ((MulEquiv.subgroupCongr c.sup_compl_eq_G1).symm
              ⟨l, hLle hl⟩)) : G') = _
          rw [MulEquiv.subgroupCongr_apply]
      _ = (α₀ ⟨l, Subgroup.mem_sup_right hl⟩ : G') := by
          congr 1
      _ = (Λ ⟨l, hl⟩ : G') := hα₀L ⟨l, hl⟩
  have hφEzero : ∀ e : ↥c.E,
      r'.φ ⟨((Θ e : ↥c'.E) : G'), c'.E_le_G1 (Θ e).2⟩ = 1 := by
    intro e
    have h1 : (⟨((Θ e : ↥c'.E) : G'), c'.E_le_G1 (Θ e).2⟩ : ↥c'.G1) ∈ r'.φ.ker := by
      rw [r'.ker_eq, Subgroup.mem_subgroupOf]
      exact (Θ e).2
    exact h1
  have hα₁ : ∀ h : ↥c.G1, r'.φ (α₁ h) = r.φ h := by
    intro h
    have hmem : (h : G) ∈ c.E ⊔ L := by
      rw [c.sup_compl_eq_G1]
      exact h.2
    change (h : G) ∈ (↑(c.E ⊔ L) : Set G) at hmem
    rw [Subgroup.coe_mul_of_right_le_normalizer_left c.E L hLle] at hmem
    obtain ⟨e, he, l, hl, hhe⟩ := hmem
    have hh : h = ⟨e, c.E_le_G1 he⟩ * ⟨l, hLle hl⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      exact hhe.symm
    have hφe : r.φ ⟨e, c.E_le_G1 he⟩ = 1 := by
      have h1 : (⟨e, c.E_le_G1 he⟩ : ↥c.G1) ∈ r.φ.ker := by
        rw [r.ker_eq, Subgroup.mem_subgroupOf]
        exact he
      exact h1
    calc r'.φ (α₁ h)
        = r'.φ (α₁ (⟨e, c.E_le_G1 he⟩ * ⟨l, hLle hl⟩)) := by rw [hh]
      _ = r'.φ (α₁ ⟨e, c.E_le_G1 he⟩) * r'.φ (α₁ ⟨l, hLle hl⟩) := by
          rw [map_mul, map_mul]
      _ = r'.φ ⟨((Θ ⟨e, he⟩ : ↥c'.E) : G'), c'.E_le_G1 (Θ ⟨e, he⟩).2⟩ *
            r'.φ ⟨((Λ ⟨l, hl⟩ : ↥L') : G'), hL'le (Λ ⟨l, hl⟩).2⟩ := by
          rw [hα₁E e he, hα₁L l hl]
      _ = 1 * r.φ ⟨(l : G), hLle hl⟩ := by
          rw [hφEzero, hφlam]
      _ = r.φ h := by
          rw [one_mul, hh, map_mul, hφe, one_mul]
  obtain ⟨m', hm'⟩ := r'.exists_φ_eq hσ
  refine ⟨α₁.trans (MulAut.conj m'), ?_⟩
  intro h
  rw [MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hm', hα₁ h]

theorem exists_mulEquiv_mem_E (r : ResM24T c) (r' : ResM24T c')
    (σ : Equiv.Perm (Fin 24)) {α : ↥c.G1 ≃* ↥c'.G1}
    (hα : ∀ h : ↥c.G1, r'.φ (α h) = σ * r.φ h * σ⁻¹) :
    ∀ h : ↥c.G1, (h : G) ∈ c.E ↔ (α h : G') ∈ c'.E := by
  intro h
  have hconj : σ * r.φ h * σ⁻¹ = 1 ↔ r.φ h = 1 := by
    constructor
    · intro hh
      have := congrArg (fun x => σ⁻¹ * x * σ) hh
      simpa [mul_assoc] using this
    · intro hh
      simp [hh]
  rw [show (h : G) ∈ c.E ↔ h ∈ r.φ.ker by
        rw [r.ker_eq, Subgroup.mem_subgroupOf],
      show (α h : G') ∈ c'.E ↔ α h ∈ r'.φ.ker by
        rw [r'.ker_eq, Subgroup.mem_subgroupOf],
      MonoidHom.mem_ker, MonoidHom.mem_ker, hα h, hconj]

end ResM24T

end CFSG.Quasithin.H13.AS91
