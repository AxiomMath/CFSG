module

public import CFSG.Timmesfeld.Transvection.ModelRadical
public import CFSG.Timmesfeld.Transvection.ModelSpGen
public import CFSG.Timmesfeld.Transvection.ModelGeometry
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

namespace ModelRank

theorem map_eq_self_of_fix {G : Type*} [Group G] {H : Subgroup G} (α : MulAut G)
    (h : ∀ x ∈ H, α x = x) : H.map α.toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, h y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, h x hx]⟩

theorem map_conjSub_of_map_eq {G : Type*} [Group G] {H : Subgroup G} (α : MulAut G)
    (h : H.map α.toMonoidHom = H) (g : G) :
    (conjSub H g).map α.toMonoidHom = conjSub H (α g) := by
  rw [← conjSub_map, h]
  rfl

theorem spMapTransStmt_holds (n : ℕ) (F : Type) [Field F] : SpMapTransStmt n F := by
  intro a ha T hT α hα v hv X hX
  obtain ⟨A, hA, hAv⟩ := CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq ha hv
  have hX' : X = conjSub T ⟨A, hA⟩ := by
    have h := hT.conjSub ⟨A, hA⟩
    rw [show SpExtras.mat n F ⟨A, hA⟩ *ᵥ a = v from hAv] at h
    exact hX.eq h
  refine ⟨SpExtras.mat n F (α ⟨A, hA⟩) *ᵥ a, mat_mulVec_ne_zero' _ ha, ?_⟩
  rw [hX', map_conjSub_of_map_eq α (map_eq_self_of_fix α hα)]
  exact hT.conjSub _

section CharTwo

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem spForm_comm_charTwo (u v : Fin n ⊕ Fin n → F) : spForm v u = spForm u v := by
  rw [spForm_comm, CharTwo.neg_eq]

theorem mulVec_spTrans_conj (p l : Fin n ⊕ Fin n → F) (c e : F) :
    spTrans p e *ᵥ (spTrans l c *ᵥ (spTrans p e *ᵥ p)) =
      (1 + e * (c * spForm p l * spForm p l)) • p + (c * spForm p l) • l := by
  have h1 : spTrans p e *ᵥ p = p := by
    rw [spTrans_mulVec, spForm_self, mul_zero, zero_smul, add_zero]
  have h2 : spTrans l c *ᵥ p = p + (c * spForm p l) • l := by
    rw [spTrans_mulVec, spForm_comm_charTwo p l]
  rw [h1, h2, spTrans_mulVec, spForm_add_right, spForm_smul_right', spForm_self]
  module

theorem ne_zero_of_spForm_eq_one {a d : Fin n ⊕ Fin n → F} (had : spForm a d = 1) : a ≠ 0 := by
  rintro rfl
  simp [spForm] at had

end CharTwo

theorem fixes_of_stabilizes_opposite {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {p l : Fin n ⊕ Fin n → F} (hpl : spForm p l ≠ 0) {Tp Tl : Subgroup (StatedSp n F)}
    (hTp : IsTransGroup p Tp) (hTl : IsTransGroup l Tl) (β : MulAut (StatedSp n F))
    (hp : ∀ x ∈ Tp, β x = x) (hl : Tl.map β.toMonoidHom = Tl) : ∀ x ∈ Tl, β x = x := by
  intro x hx
  obtain ⟨c, hc⟩ := (hTl.1 x).1 hx
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hpl (by simp [spForm])
  by_cases hc0 : c = 0
  · have hx1 : x = 1 := SpExtras.mat_injective (by rw [hc, hc0, spTrans_zero, map_one])
    rw [hx1, map_one]
  have hcb : c * spForm p l * spForm p l ≠ 0 := mul_ne_zero (mul_ne_zero hc0 hpl) hpl
  obtain ⟨s, hs⟩ := hTp.2 (c * spForm p l * spForm p l)⁻¹
  have hsTp : s ∈ Tp := (hTp.1 s).2 ⟨_, hs⟩
  have hw : SpExtras.mat n F (s * x * s) *ᵥ p = (c * spForm p l) • l := by
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hs, hc, mulVec_spTrans_conj,
      inv_mul_cancel₀ hcb, CharTwo.add_self_eq_zero, zero_smul, zero_add]
  have hconj : conjSub Tp (s * x * s) = Tl := by
    have h1 := hTp.conjSub (s * x * s)
    rw [hw] at h1
    exact (h1.of_smul (mul_ne_zero hc0 hpl)).eq hTl
  have hβw : β (s * x * s) = s * β x * s := by rw [map_mul, map_mul, hp s hsTp]
  have hconj' : conjSub Tp (s * β x * s) = Tl := by
    rw [← hβw, ← map_conjSub_of_map_eq β (map_eq_self_of_fix β hp), hconj, hl]
  have h2 := hTp.conjSub (s * β x * s)
  rw [hconj'] at h2
  obtain ⟨μ, -, hμ⟩ := IsTransGroup.exists_eq_smul h2 hTl (mat_mulVec_ne_zero' _ hp0)
  have hβx : β x ∈ Tl := by
    rw [← hl]
    exact ⟨x, hx, rfl⟩
  obtain ⟨c', hc'⟩ := (hTl.1 (β x)).1 hβx
  rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hs, hc', mulVec_spTrans_conj] at hμ
  have hcoef : (1 + (c * spForm p l * spForm p l)⁻¹ * (c' * spForm p l * spForm p l)) *
      spForm p l = 0 := by
    have h3 := congrArg (fun v => spForm v l) hμ
    simp only [spForm_add_left, spForm_smul_left', spForm_self, mul_zero, add_zero] at h3
    exact h3
  have h4 : (c * spForm p l * spForm p l)⁻¹ * (c' * spForm p l * spForm p l) = 1 := by
    have h5 := (mul_eq_zero.1 hcoef).resolve_right hpl
    linear_combination h5 - (CharTwo.two_eq_zero : (2 : F) = 0)
  have h6 : c * spForm p l * spForm p l = c' * spForm p l * spForm p l :=
    (inv_mul_eq_one₀ hcb).1 h4
  have h7 : c' = c := (mul_right_cancel₀ hpl (mul_right_cancel₀ hpl h6)).symm
  apply SpExtras.mat_injective
  rw [hc', hc, h7]

section Rigid

variable {n : ℕ} {F : Type} [Field F] [CharP F 2] {a d : Fin n ⊕ Fin n → F}
  {Td : Subgroup (StatedSp n F)}

theorem map_eq_of_spForm_ne_zero (had : spForm a d = 1) (hTd : IsTransGroup d Td)
    (β : MulAut (StatedSp n F)) (hβ : ∀ x ∈ spRad a, β x = x)
    (hβd : Td.map β.toMonoidHom = Td) {v : Fin n ⊕ Fin n → F} (hv : spForm a v ≠ 0)
    {X : Subgroup (StatedSp n F)} (hX : IsTransGroup v X) : X.map β.toMonoidHom = X := by
  have hv1 : spForm a ((spForm a v)⁻¹ • v) = 1 := by
    rw [spForm_smul_right', inv_mul_cancel₀ hv]
  have hX1 : IsTransGroup ((spForm a v)⁻¹ • v) X :=
    IsTransGroup.of_smul (l := spForm a v) hv (by rwa [smul_smul, mul_inv_cancel₀ hv, one_smul])
  obtain ⟨x, hx, hxd⟩ := exists_mem_spRad_mulVec_eq had hv1
  have hXx : conjSub Td x = X := by
    have h := hTd.conjSub x
    rw [hxd] at h
    exact h.eq hX1
  rw [← hXx, map_conjSub_of_map_eq β hβd, hβ x hx]

theorem map_eq_of_spForm_eq_zero (had : spForm a d = 1) (hTd : IsTransGroup d Td)
    (β : MulAut (StatedSp n F)) (hβ : ∀ x ∈ spRad a, β x = x)
    (hβd : Td.map β.toMonoidHom = Td) {u : Fin n ⊕ Fin n → F} (hu0 : u ≠ 0)
    (hau : spForm a u = 0) {X : Subgroup (StatedSp n F)} (hX : IsTransGroup u X) :
    X.map β.toMonoidHom = X := by
  have ha := ne_zero_of_spForm_eq_one had
  obtain ⟨T, hT⟩ := exists_isTransGroup a
  have hTfix : ∀ x ∈ T, β x = x := fun x hx => hβ x (le_spRad_of_isTransGroup hT hx)
  by_cases hua : ∃ c : F, u = c • a
  · obtain ⟨c, rfl⟩ := hua
    have hc : c ≠ 0 := by
      rintro rfl
      exact hu0 (zero_smul F a)
    rw [(hX.of_smul hc).eq hT]
    exact map_eq_self_of_fix β hTfix
  obtain ⟨u', hu'0, hX'⟩ := spMapTransStmt_holds n F ha hT β hTfix hu0 hX
  by_cases hu' : ∃ c : F, u' = c • u
  · obtain ⟨c, rfl⟩ := hu'
    have hc : c ≠ 0 := by
      rintro rfl
      exact hu'0 (zero_smul F u)
    exact (hX'.of_smul hc).eq hX
  obtain ⟨z, haz, huz, hu'z⟩ := exists_spForm_separate ha (fun c h => hua ⟨c, h⟩)
    (fun c h => hu' ⟨c, h⟩)
  obtain ⟨Z, hZ⟩ := exists_isTransGroup z
  have hc : Commuting (X.map β.toMonoidHom) Z := by
    have h := ModelRank.commuting_map β.toMonoidHom (hX.commuting hZ huz)
    rwa [map_eq_of_spForm_ne_zero had hTd β hβ hβd haz hZ] at h
  exact absurd (spForm_eq_zero_of_commuting hX' hZ hu'0 hc) hu'z

theorem apply_eq_of_isTransGroup (had : spForm a d = 1) (hTd : IsTransGroup d Td)
    (β : MulAut (StatedSp n F)) (hβ : ∀ x ∈ spRad a, β x = x)
    (hβd : Td.map β.toMonoidHom = Td) {v : Fin n ⊕ Fin n → F} {X : Subgroup (StatedSp n F)}
    (hX : IsTransGroup v X) : ∀ x ∈ X, β x = x := by
  obtain ⟨T, hT⟩ := exists_isTransGroup a
  have hTfix : ∀ x ∈ T, β x = x := fun x hx => hβ x (le_spRad_of_isTransGroup hT hx)
  have hne : ∀ {w : Fin n ⊕ Fin n → F}, spForm a w ≠ 0 → ∀ {W : Subgroup (StatedSp n F)},
      IsTransGroup w W → ∀ x ∈ W, β x = x := fun hw _ hW =>
    fixes_of_stabilizes_opposite hw hT hW β hTfix
      (map_eq_of_spForm_ne_zero had hTd β hβ hβd hw hW)
  intro x hx
  by_cases hv0 : v = 0
  · obtain ⟨c, hc⟩ := (hX.1 x).1 hx
    have hx1 : x = 1 := SpExtras.mat_injective (by rw [hc, hv0, map_one]; simp [spTrans])
    rw [hx1, map_one]
  by_cases hav : spForm a v = 0
  ·
    obtain ⟨z, haz, hvz⟩ := exists_spForm_ne_zero_both (ne_zero_of_spForm_eq_one had) hv0
    obtain ⟨Z, hZ⟩ := exists_isTransGroup z
    exact fixes_of_stabilizes_opposite (by rw [← spForm_comm_charTwo z v]; exact hvz) hZ hX β
      (hne haz hZ) (map_eq_of_spForm_eq_zero had hTd β hβ hβd hv0 hav hX) x hx
  · exact hne hav hX x hx

end Rigid

theorem spRigidStmt_holds (n : ℕ) (F : Type) [Field F] [CharP F 2] : SpRigidStmt n F := by
  intro a d _ had _ Td _ hTd β hβ hβd
  have h : β.toMonoidHom = MonoidHom.id _ := monoidHom_eq_of_forall_spTrans fun x v c hx => by
    obtain ⟨X, hX⟩ := exists_isTransGroup v
    exact apply_eq_of_isTransGroup had hTd β hβ hβd hX x ((hX.1 x).2 ⟨c, hx⟩)
  exact MulEquiv.ext fun x => DFunLike.congr_fun h x

end ModelRank

end CFSG.Timmesfeld.Transvection
