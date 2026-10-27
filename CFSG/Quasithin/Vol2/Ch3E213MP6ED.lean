module

public import CFSG.Quasithin.Vol2.Ch3E213MP6EC
public import CFSG.Quasithin.Vol2.Ch3E213MP5H
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Vol2.Ch3E213MP5F

public section

namespace CFSG.Quasithin.Ch3E213M.P6E

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6

theorem exists_conj_of_isSylowTwoOf_top {X : Type} [Group X] [Finite X] {S₁ S₂ : Subgroup X}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : X, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 X := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 X := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem isSylowTwoOf_map_equiv_top {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {S : Subgroup X} (h : IsSylowTwoOf S ⊤) : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  have h' := P5.isSylowTwoOf_map_equiv e h
  rwa [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective] at h'

variable {A : Type} [Group A] {K : Subgroup A}

theorem exists_equiv_D0 {S : Subgroup A} (hS : IsSylowTwoOf (S ⊓ K) K) (hAlt : IsAlt 6 ↥K) :
    ∃ e : ↥K ≃* M6, ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U6 := by
  obtain ⟨e₀⟩ := hAlt
  have h1 := isSylowTwoOf_map_equiv_top e₀ (P5.isSylowTwoOf_subgroupOf_top hS)
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top h1 sylow_U6
  refine ⟨e₀.trans (MulAut.conj g), ?_⟩
  rw [← hg, Subgroup.map_map]
  rfl

variable [K.Normal] {Y : Type*} [Group Y]

theorem map_congr_conj (e : ↥K ≃* Y) (t : A) (X : Subgroup K) :
    (X.map e.toMonoidHom).map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom =
      (X.map (MulAut.conjNormal t).toMonoidHom).map e.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩

theorem map_congr_conj_ne (e : ↥K ≃* Y) {P : Subgroup Y} {t : A}
    (ht : t ∉ Subgroup.normalizer (((P.map e.symm.toMonoidHom).map K.subtype : Subgroup A) :
      Set A)) :
    P.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom ≠ P := by
  intro h
  apply ht
  apply P5.mem_normalizer_of_map_conjNormal
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  have h1 := map_congr_conj e t (P.map e.symm.toMonoidHom)
  rw [P5.map_map_symm] at h1
  rw [← h1, h, P5.map_map_symm]

variable [Finite A]

theorem exists_swap {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) (e : ↥K ≃* M6)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U6)
    (hdiag : ∀ P : Subgroup A, IsMaxParabolic2 K P →
      K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A) ≤ P →
        ¬ S ≤ Subgroup.normalizer (P : Set A)) :
    ∃ t ∈ S, U6.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = U6 ∧
      Ra.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = Rb ∧
      Rb.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = Ra := by
  have hSK : IsSylowTwoOf (S ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hS le_top (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  have hcov : Ka.map e.symm.toMonoidHom ⋖ ⊤ := by
    have h := (apply_covBy_apply_iff e.symm.mapSubgroup).2 Ka_covBy
    rwa [OrderIso.map_top] at h
  have hNP : Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K) ≤
      Ka.map e.symm.toMonoidHom :=
    calc Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K)
        = ((Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K)).map
            e.toMonoidHom).map e.symm.toMonoidHom := (P5.map_symm_map e _).symm
      _ = U6.map e.symm.toMonoidHom := by
          rw [Subgroup.map_equiv_normalizer_eq, he, normalizer_U6]
      _ ≤ Ka.map e.symm.toMonoidHom := Subgroup.map_mono U6_lt_Ka.le
  obtain ⟨hmax, hle⟩ := P5.isMaxParabolic2_of_isCoatom hSK hcov hNP
  obtain ⟨t, htS, ht⟩ := Set.not_subset.mp (hdiag _ hmax hle)
  have hU : U6.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = U6 := by
    rw [← he, map_congr_conj, P5.map_conjNormal_eq (Subgroup.le_normalizer htS)]
  have hK := map_congr_conj_ne e ht
  obtain ⟨h1, h2⟩ := map_Ra_Rb _ hU (swap_of_moves _ hU hK)
  exact ⟨t, htS, hU, h1, h2⟩

omit [Finite A] in
theorem map_inf_le {S E : Subgroup A} (e : ↥K ≃* M6)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U6) {t : A} (htS : t ∈ S)
    (hab : Ra.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = Rb ∧
      Rb.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = Ra)
    (hES : E ≤ S) (hSE : S ≤ Subgroup.normalizer (E : Set A)) (hE2 : ∀ x ∈ E, x * x = 1) :
    ((E ⊓ K).subgroupOf K).map e.toMonoidHom ≤ Ra ⊓ Rb := by
  refine le_Ra_inf_Rb _ hab ?_ ?_ ?_
  · rw [← he]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ (inf_le_inf_right K hES))
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul]
    have h1 : w * w = 1 := Subtype.ext (by simpa using hE2 _ hw.1)
    rw [h1, map_one]
  · rw [map_congr_conj, P5.map_conjNormal_eq (hSE htS)]

end CFSG.Quasithin.Ch3E213M.P6E
