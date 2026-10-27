module

public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.Timmesfeld.Transvection.ModelRadical

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection.ModelRank

section Aut

variable {G : Type*} [Group G]

theorem map_mulAut_eq_self {α : MulAut G} {H : Subgroup G} (h : ∀ x ∈ H, α x = x) :
    H.map α.toMonoidHom = H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change α x ∈ H
    rw [h x hx]
    exact hx
  · intro hy
    exact ⟨y, hy, h y hy⟩

theorem commuting_map_mulAut_iff (α : MulAut G) {X Y : Subgroup G} :
    Commuting (X.map α.toMonoidHom) (Y.map α.toMonoidHom) ↔ Commuting X Y :=
  commuting_map_iff α.injective

theorem map_conjSub_mulAut (α : MulAut G) (H : Subgroup G) (g : G) :
    (conjSub H g).map α.toMonoidHom = conjSub (H.map α.toMonoidHom) (α g) :=
  Subgroup.map_map_conj H α.toMonoidHom g

theorem map_mul_mulAut (α β : MulAut G) (H : Subgroup G) :
    H.map (α * β).toMonoidHom = (H.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem conjSub_conjSub_comm {H : Subgroup G} {g h : G} (hgh : g * h = h * g) :
    conjSub (conjSub H g) h = conjSub (conjSub H h) g := by
  rw [← conjSub_mul, ← conjSub_mul, hgh]

end Aut

theorem rootS2Model_sp {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (hcore : SpCoreStmt n F) (hcomm : SpRadCommStmt n F) (hmap : SpMapTransStmt n F)
    (hrigid : SpRigidStmt n F) {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T : Subgroup (StatedSp n F)} (hT : CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T) :
    RootS2Model (StatedSp n F) T := by
  intro α hfix hrad
  rw [hcore ha hT] at hrad ⊢
  have hTR : T ≤ spRad a := le_spRad_of_isTransGroup hT
  have hRab := hcomm ha
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero ha
  obtain ⟨d, hd1⟩ : ∃ d, spForm a d = 1 :=
    ⟨(spForm a y)⁻¹ • y, by rw [spForm_smul_right', inv_mul_cancel₀ hy]⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp [spForm] at hd1
  have hda : spForm d a = 1 := by rw [spForm_comm, hd1, CharTwo.neg_eq]
  obtain ⟨Td, hTd⟩ := exists_isTransGroup d
  obtain ⟨d', -, hd'⟩ := hmap ha hT α hfix hd0 hTd
  have hTα : T.map α.toMonoidHom = T := map_mulAut_eq_self hfix
  have had' : spForm a d' ≠ 0 := by
    intro h0
    have hc : Commuting (T.map α.toMonoidHom) (Td.map α.toMonoidHom) := by
      rw [hTα]
      exact hT.commuting hd' h0
    have h1 := spForm_eq_zero_of_commuting hT hTd ha ((commuting_map_mulAut_iff α).1 hc)
    rw [hd1] at h1
    exact one_ne_zero h1
  obtain ⟨d'', hd''1, hTd''⟩ :
      ∃ d'', spForm a d'' = 1 ∧ IsTransGroup d'' (Td.map α.toMonoidHom) :=
    ⟨(spForm a d')⁻¹ • d', by rw [spForm_smul_right', inv_mul_cancel₀ had'],
      IsTransGroup.of_smul had' (by rwa [smul_smul, mul_inv_cancel₀ had', one_smul])⟩
  obtain ⟨x₀, hx₀, hx₀d⟩ := exists_mem_spRad_mulVec_eq hd1 hd''1
  have hTdα : Td.map α.toMonoidHom = conjSub Td x₀ := by
    apply hTd''.eq
    have := hTd.conjSub x₀
    rwa [hx₀d] at this
  have hαR : ∀ z ∈ spRad a, α z ∈ spRad a := fun z hz => by
    have e : α z = z * (z⁻¹ * α z) := by group
    rw [e]
    exact (spRad a).mul_mem hz (hTR (hrad z hz))
  have crit : ∀ g : StatedSp n F,
      Commuting Td (conjSub Td g) ↔ spForm d (SpExtras.mat n F g *ᵥ d) = 0 := fun g =>
    ⟨spForm_eq_zero_of_commuting hTd (hTd.conjSub g) hd0, hTd.commuting (hTd.conjSub g)⟩
  have hiff : ∀ z ∈ spRad a, (spForm d (SpExtras.mat n F z *ᵥ d) = 0 ↔
      spForm d (SpExtras.mat n F (α z) *ᵥ d) = 0) := by
    intro z hz
    rw [← crit, ← crit, ← commuting_map_mulAut_iff α (X := Td) (Y := conjSub Td z),
      map_conjSub_mulAut, hTdα, conjSub_conjSub_comm (hRab _ hx₀ _ (hαR z hz))]
    exact commuting_map_mulAut_iff (MulAut.conj x₀)
  have hform : ∀ z ∈ spRad a, ∃ e : F, SpExtras.mat n F (z⁻¹ * α z) = spTrans a e ∧
      spForm d (SpExtras.mat n F (α z) *ᵥ d) = spForm d (SpExtras.mat n F z *ᵥ d) + e := by
    intro z hz
    obtain ⟨e, he⟩ := (hT.1 _).1 (hrad z hz)
    refine ⟨e, he, ?_⟩
    have e1 : α z = z * (z⁻¹ * α z) := by group
    rw [e1, map_mul, ← mulVec_mulVec, he, spTrans_mulVec, hd1, mul_one, mulVec_add, mulVec_smul,
      hz.1, spForm_add_right, spForm_smul_right', hda, mul_one]
  have hfix0 : ∀ z ∈ spRad a, spForm d (SpExtras.mat n F z *ᵥ d) = 0 → α z = z := by
    intro z hz h0
    obtain ⟨e, he, hfe⟩ := hform z hz
    have h1 := (hiff z hz).1 h0
    rw [hfe, h0, zero_add] at h1
    have ht : z⁻¹ * α z = 1 :=
      SpExtras.mat_injective (by rw [he, h1, spTrans_zero, map_one])
    calc α z = z * (z⁻¹ * α z) := by group
      _ = z := by rw [ht, mul_one]
  have hfixR : ∀ z ∈ spRad a, α z = z := by
    intro z hz
    obtain ⟨ta, hta⟩ := hT.2 (spForm d (SpExtras.mat n F z *ᵥ d))
    have htaT : ta ∈ T := (hT.1 ta).2 ⟨_, hta⟩
    have h0 : spForm d (SpExtras.mat n F (z * ta) *ᵥ d) = 0 := by
      rw [map_mul, ← mulVec_mulVec, hta, spTrans_mulVec, hd1, mul_one, mulVec_add, mulVec_smul,
        hz.1, spForm_add_right, spForm_smul_right', hda, mul_one, CharTwo.add_self_eq_zero]
    have h1 := hfix0 _ ((spRad a).mul_mem hz (hTR htaT)) h0
    rw [map_mul, hfix ta htaT] at h1
    exact mul_right_cancel h1
  set β : MulAut (StatedSp n F) := MulAut.conj x₀⁻¹ * α with hβ
  have hβapp : ∀ g, β g = x₀⁻¹ * α g * x₀ := fun g => by
    rw [hβ, MulAut.mul_apply, MulAut.conj_apply, inv_inv]
  have hβR : ∀ x ∈ spRad a, β x = x := fun x hx => by
    rw [hβapp, hfixR x hx, mul_assoc, hRab x hx x₀ hx₀, inv_mul_cancel_left]
  have hβTd : Td.map β.toMonoidHom = Td := by
    rw [hβ, map_mul_mulAut, hTdα]
    change conjSub (conjSub Td x₀) x₀⁻¹ = Td
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have h1 := hrigid ha hd1 hT hTd β hβR hβTd
  refine ⟨x₀, hx₀, MulEquiv.ext fun g => ?_⟩
  have h2 : β g = g := by rw [h1, MulAut.one_apply]
  rw [hβapp] at h2
  calc α g = x₀ * (x₀⁻¹ * α g * x₀) * x₀⁻¹ := by group
    _ = MulAut.conj x₀ g := by rw [h2, MulAut.conj_apply]

end CFSG.RankThree.GF2n.Tim79a
