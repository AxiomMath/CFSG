module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_index_le_four {P : Type*} [Group P] [Finite P] (hP : commutator P = ⊤)
    (K : Subgroup P) (hK : K.index ≤ 4) : K = ⊤ := by
  set φ := MulAction.toPermHom P (P ⧸ K) with hφ
  have hsolv : Group.IsSolvable (Equiv.Perm (P ⧸ K)) :=
    Equiv.Perm.isSolvable (by rw [← Subgroup.index]; exact hK)
  have hR : ⁅φ.range, φ.range⁆ = φ.range := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup P) (⊤ : Subgroup P) φ
    rw [← commutator_def, hP, ← MonoidHom.range_eq_map] at h1
    exact h1.symm
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ↥φ.range := by
      refine ⟨?_⟩
      apply Subgroup.map_injective φ.range.subtype_injective
      rw [Subgroup.map_subtype_commutator, hR, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have : Group.IsSolvable ↥φ.range := subgroup_solvable_of_solvable _
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  rw [eq_top_iff]
  intro x _
  have h1 : φ x = 1 := by
    have : φ x ∈ φ.range := ⟨_, rfl⟩
    rw [hbot] at this
    exact this
  have h2 : x • (QuotientGroup.mk 1 : P ⧸ K) = QuotientGroup.mk 1 := by
    have := congrArg (fun σ : Equiv.Perm (P ⧸ K) => σ (QuotientGroup.mk 1)) h1
    simpa [hφ] using this
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one] at h2
  simpa using K.inv_mem h2

@[reducible] noncomputable def conjSubgroupAction (P : Subgroup G) : MulAction ↥P (Subgroup G) where
  smul p K := K.map (MulAut.conj (p : G)).toMonoidHom
  one_smul K := by
    change K.map (MulAut.conj ((1 : ↥P) : G)).toMonoidHom = K
    ext x
    simp
  mul_smul p q K := by
    change K.map (MulAut.conj ((p * q : ↥P) : G)).toMonoidHom =
      (K.map (MulAut.conj (q : G)).toMonoidHom).map (MulAut.conj (p : G)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]

theorem le_normalizer_of_ncard_le {A P J : Subgroup G} (hPA : P ≤ A) (hP : commutator ↥P = ⊤)
    (hJ : (conjSubgroupsBy A J).ncard ≤ 4) : P ≤ Subgroup.normalizer (J : Set G) := by
  let _ := conjSubgroupAction P
  have horb : MulAction.orbit ↥P J ⊆ conjSubgroupsBy A J := by
    rintro _ ⟨p, rfl⟩
    exact ⟨p, hPA p.2, rfl⟩
  have hidx : (MulAction.stabilizer ↥P J).index ≤ 4 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard horb (Set.toFinite _)).trans hJ
  have htop := eq_top_of_index_le_four hP _ hidx
  intro p hp
  have hst : (⟨p, hp⟩ : ↥P) ∈ MulAction.stabilizer ↥P J := htop ▸ Subgroup.mem_top _
  have hmap : J.map (MulAut.conj p).toMonoidHom = J := hst
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : p * x * p⁻¹ ∈ J.map (MulAut.conj p).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hmap] at this
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    exact this ▸ hy

theorem commutator_eq_bot_of_ne {A J₁ J₂ : Subgroup G}
    (h₁ : CFSG.GorensteinWalter.IsComponentOf J₁ A) (h₂ : CFSG.GorensteinWalter.IsComponentOf J₂ A)
    (hne : J₁ ≠ J₂) : ⁅J₁, J₂⁆ = ⊥ := by
  have key : ∀ {J J' : Subgroup G}, CFSG.GorensteinWalter.IsComponentOf J A →
      CFSG.GorensteinWalter.IsComponentOf J' A → J ≤ J' → ⁅J', J⁆ = ⊥ → False := by
    intro J J' hJ hJ' hle hcomm
    obtain ⟨hnt, hperf, -⟩ := hJ.2.2
    have hab : ⁅J, J⁆ = ⊥ :=
      eq_bot_iff.mpr ((Subgroup.commutator_mono hle le_rfl).trans hcomm.le)
    have hJJ : ⁅J, J⁆ = J := by
      calc ⁅J, J⁆ = (commutator ↥J).map J.subtype := (Subgroup.map_subtype_commutator J).symm
        _ = (⊤ : Subgroup ↥J).map J.subtype := by rw [hperf]
        _ = J := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hbot : J = ⊥ := hJJ.symm.trans hab
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := hnt
    rw [hbot, Subgroup.mem_bot] at hx hy
    exact hxy (Subtype.ext (hx.trans hy.symm))
  rcases CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf
      h₂.1 h₂.2.1 h₁ with h12 | h12
  · rcases CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf
        h₁.1 h₁.2.1 h₂ with h21 | h21
    · exact absurd (le_antisymm h12 h21) hne
    · exact (key h₁ h₂ h12 h21).elim
  · exact h12

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
