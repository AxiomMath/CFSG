module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H33

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.QuasithinUnique

variable {G H : Type*} [Group G] [Group H]

theorem map_o2G_le (X : Subgroup G) (f : G →* H) : (o2G X).map f ≤ o2G (X.map f) := by
  refine le_o2G (X.map f) (Subgroup.map_mono (o2G_le X)) ?_ ((isPGroup_o2G X).map f)
  refine le_normalizer_of_conj ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨q, hq, rfl⟩
  exact ⟨x * q * x⁻¹, (Subgroup.mem_normalizer_iff.mp (le_normalizer_o2G X hx) q).mp hq,
    by rw [map_mul, map_mul, map_inv]⟩

theorem mem_normalizer_map_conj {X : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (X : Set G)) (g : G) :
    g * s * g⁻¹ ∈
      Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    MulAut.conj_symm_apply,
    show g⁻¹ * (g * s * g⁻¹ * z * (g * s * g⁻¹)⁻¹) * g = s * (g⁻¹ * z * g) * s⁻¹ by group]
  exact Subgroup.mem_normalizer_iff.mp hs _

theorem exists_conj_uniSL {S : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hS : IsSylowTwoOf S ⊤) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2), ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ uniSL 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp, hi⟩ := hS
  have hidx : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [hidx] at hi
  have hiU : ¬ 2 ∣ (uniSL 5).index := by
    have h := (uniSL 5).card_mul_index
    rw [card_uniSL_five, card_SL_five_two] at h
    rw [show (uniSL 5).index = 9765 by omega]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hp.toSylow hi) (isPGroup_uniSL_five.toSylow hiU)
  refine ⟨g, fun s => ?_⟩
  have h := congrArg (fun R : Sylow 2 (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) =>
    (R : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow] at h
  rw [← h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    show g⁻¹ * (g * s * g⁻¹) * g = s by group]

theorem factL5Inv_holds : FactL5Inv := by
  intro X S hS hSX hperf hq y hyN hy3 hyc
  obtain ⟨e⟩ := hq
  have hyc₀ : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ o2G X := fun x hx => pCoreOf_eq_o2G X ▸ hyc x hx
  obtain ⟨g, hg⟩ := exists_conj_uniSL hS
  set σ := MulAut.conj g with hσ
  set X' := X.map σ.toMonoidHom with hX'
  have hU : uniSL 5 ≤ Subgroup.normalizer
      (X' : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) := fun u hu => by
    have hs : g⁻¹ * u * g ∈ S := (hg _).mpr (by rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group])
    have := mem_normalizer_map_conj (hSX hs) g
    rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at this
  have hperf' : ⁅X', X'⁆ = X' := by rw [hX', ← Subgroup.map_commutator, hperf]
  set f := X.equivMapOfInjective σ.toMonoidHom σ.injective
  have e' : ↥X' ⧸ CFSG.pCore 2 ↥X' ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.congr _ _ f (CFSG.pCore_map_iso 2 f)).symm.trans e
  have hyN' := mem_normalizer_map_conj hyN g
  have hy3' : orderOf (g * y * g⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy3]
  have hyc' : ∀ x ∈ X', g * y * g⁻¹ * x * (g * y * g⁻¹)⁻¹ * x⁻¹ ∈ o2G X' := by
    rintro _ ⟨x, hx, rfl⟩
    refine map_o2G_le X σ.toMonoidHom ⟨_, hyc₀ x hx, ?_⟩
    simp only [hσ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨r', hr', k, hk⟩ := concl_of_uniSL hU hperf' e' hyN' hy3' hyc'
  refine ⟨g⁻¹ * r' * g, (hg _).mpr (by rwa [show g * (g⁻¹ * r' * g) * g⁻¹ = r' by group]), k, ?_⟩
  rw [show g⁻¹ * r' * g * y * (g⁻¹ * r' * g)⁻¹ * y =
    g⁻¹ * (r' * (g * y * g⁻¹) * r'⁻¹ * (g * y * g⁻¹)) * g⁻¹⁻¹ by group, conj_pow, hk]
  group

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
