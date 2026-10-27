module

public import CFSG.Quasithin.Background.HSL3S77Model
public import CFSG.Quasithin.Background.HSL3NPrime

public section

namespace CFSG.Quasithin.H.S77

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H.SL3Pair
  CFSG.Quasithin.H.SL3One

section Field

variable {K : Type} [Field K]

@[expose] noncomputable def stdE (ε : K ≃+* ZMod 2) :
    StdMod (Fin 3) K ≃* StdMod (Fin 3) (ZMod 2) :=
  AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => ε.toAddEquiv)

theorem toAdd_stdE_symm (ε : K ≃+* ZMod 2) (x : StdMod (Fin 3) (ZMod 2)) :
    Multiplicative.toAdd ((stdE ε).symm x) = fun i => ε.symm (Multiplicative.toAdd x i) := rfl

@[expose] noncomputable def pairE (ε : K ≃+* ZMod 2) : PairMod K ≃* PairMod (ZMod 2) :=
  MulEquiv.prodCongr (stdE ε) (stdE ε)

theorem coe_dualGL_equiv (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((dualGL (specialLinearGroupEquivStatedSL 3 K g : GL (Fin 3) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ := by
  rw [coe_dualGL]
  have h : ((specialLinearGroupEquivStatedSL 3 K g : GL (Fin 3) K))⁻¹ =
      (specialLinearGroupEquivStatedSL 3 K g⁻¹ : GL (Fin 3) K) := by
    rw [map_inv]
    rfl
  rw [h, specialLinearGroupEquivStatedSL_coe]

theorem rho_apply_snd' (g : Matrix.SpecialLinearGroup (Fin 3) K) (x : PairMod K) :
    Multiplicative.toAdd (rho g x).2 =
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ
        Multiplicative.toAdd x.2 := by
  rw [rho_apply_snd, coe_dualGL_equiv]

theorem congrHom_pairE_rho (ε : K ≃+* ZMod 2) (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    congrHom (pairE ε) (rho g) = rho (Matrix.SpecialLinearGroup.map (ε : K →+* ZMod 2) g) := by
  refine MulEquiv.ext fun p => Prod.ext ?_ ?_
  · apply Multiplicative.toAdd.injective
    funext i
    change ε (Multiplicative.toAdd (rho g ((stdE ε).symm p.1, (stdE ε).symm p.2)).1 i) =
      Multiplicative.toAdd (rho (Matrix.SpecialLinearGroup.map (ε : K →+* ZMod 2) g) p).1 i
    rw [rho_apply_fst, rho_apply_fst]
    simp [Matrix.mulVec, dotProduct, map_sum, toAdd_stdE_symm]
  · apply Multiplicative.toAdd.injective
    funext i
    change ε (Multiplicative.toAdd (rho g ((stdE ε).symm p.1, (stdE ε).symm p.2)).2 i) =
      Multiplicative.toAdd (rho (Matrix.SpecialLinearGroup.map (ε : K →+* ZMod 2) g) p).2 i
    rw [rho_apply_snd', rho_apply_snd', ← map_inv]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, toAdd_stdE_symm,
      Matrix.SpecialLinearGroup.map_apply_coe, Matrix.transpose_apply, RingEquiv.apply_symm_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    rfl

theorem map_surjective (ε : K ≃+* ZMod 2) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 3) (ε : K →+* ZMod 2)) := by
  intro g
  refine ⟨Matrix.SpecialLinearGroup.map (ε.symm : ZMod 2 →+* K) g, ?_⟩
  ext i j
  simp

theorem map_pairSL_pairE (ε : K ≃+* ZMod 2) :
    (pairSL K).map (congrHom (pairE ε)) = pairSL (ZMod 2) := by
  rw [← range_rho, ← range_rho, MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
  apply le_antisymm
  · rintro _ ⟨g, -, rfl⟩
    exact ⟨_, Subgroup.mem_top _, (congrHom_pairE_rho ε g).symm⟩
  · rintro _ ⟨g, -, rfl⟩
    obtain ⟨g', rfl⟩ := map_surjective ε g
    exact ⟨g', Subgroup.mem_top _, congrHom_pairE_rho ε g'⟩

end Field

theorem exists_model {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : BinaryNaturalSL H V₁ ⊥ 3 1) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) :
    ∃ e : V ≃* PairMod (ZMod 2), H.map (congrHom e) = pairSL (ZMod 2) ∧
      (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) = pairNorm (ZMod 2) := by
  classical
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK, pow_one]
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  have he' : H.map (congrHom (e.trans (pairE ε))) = pairSL (ZMod 2) := by
    rw [← map_pairSL_pairE ε, ← he, Subgroup.map_map]
    rfl
  refine ⟨e.trans (pairE ε), he', ?_⟩
  rw [pairNorm, ← he']
  exact Subgroup.map_equiv_normalizer_eq H (MulAut.congr (e.trans (pairE ε)))

theorem rho_fst (g : SL32) (p : PairMod (ZMod 2)) :
    Multiplicative.toAdd (rho g p).1 = act g (Multiplicative.toAdd p.1) := rho_apply_fst g p

theorem rho_snd (g : SL32) (p : PairMod (ZMod 2)) :
    Multiplicative.toAdd (rho g p).2 = dact g (Multiplicative.toAdd p.2) := rho_apply_snd' g p

theorem card_zmod_two : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]

theorem mem_pairNorm_iff {x : MulAut (PairMod (ZMod 2))} :
    x ∈ pairNorm (ZMod 2) ↔ ∃ g : SL32, x = rho g ∨ x = swapAut (ZMod 2) * rho g := by
  constructor
  · intro hx
    rcases mem_pairSub_or hx with h | h
    · obtain ⟨g, hg⟩ := exists_rho_of_mem (mem_pairSL_of_mem_pairSub card_zmod_two hx h)
      exact ⟨g, Or.inl hg.symm⟩
    · have hy : swapAut (ZMod 2) * x ∈ pairNorm (ZMod 2) :=
        Subgroup.mul_mem _ swapAut_mem_pairNorm hx
      obtain ⟨g, hg⟩ := exists_rho_of_mem (mem_pairSL_of_mem_pairSub card_zmod_two hy h)
      refine ⟨g, Or.inr ?_⟩
      rw [hg, ← mul_assoc, swapAut_mul_self, one_mul]
  · rintro ⟨g, rfl | rfl⟩
    · exact pairSL_le_pairNorm (rho_mem_pairSL g)
    · exact Subgroup.mul_mem _ swapAut_mem_pairNorm (pairSL_le_pairNorm (rho_mem_pairSL g))

end CFSG.Quasithin.H.S77
