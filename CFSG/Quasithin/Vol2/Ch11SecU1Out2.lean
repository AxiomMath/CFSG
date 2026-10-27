module

public import CFSG.Quasithin.Vol2.Ch11SecU1Out1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalPSL2ToPGammaL2Apply
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterCent
public import CFSG.Quasithin.Vol2.Ch11SecU1In1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

@[expose] def Adapted (e : L ≃* PSL2 K) (ι : G →* PGammaL2 K) : Prop :=
  Function.Injective ι ∧ ∀ y : L, ι y = SemidirectProduct.inl
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (e y))

theorem exists_adapted [L.Normal] {p f : ℕ} [Fact p.Prime] (hKc : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (e : L ≃* PSL2 K)
    (hC : Subgroup.centralizer (L : Set G) = ⊥) : ∃ ι : G →* PGammaL2 K, Adapted e ι := by
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKc hK hcard
  exact ⟨normalPSL2ToPGammaL2 L K hK hcard e hsurj,
    normalPSL2ToPGammaL2_injective L K hK hcard e hC hsurj,
    normalPSL2ToPGammaL2_apply_subtype L K hK hcard e hsurj⟩

omit [Finite K] in
theorem iota_embL {e : L ≃* PSL2 K} {ι : G →* PGammaL2 K} (h : Adapted e ι) (c : PSL2 K) :
    ι (embL e c) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL c) := by
  have := h.2 (e.symm c)
  simpa [embL] using this

omit [Finite K] in
theorem mem_iff_of_adapted {e : L ≃* PSL2 K} {ι : G →* PGammaL2 K} (h : Adapted e ι) {y : G} :
    y ∈ L ↔ ι y ∈ pGammaL2PSLRange K := by
  constructor
  · intro hy
    exact ⟨e ⟨y, hy⟩, (h.2 ⟨y, hy⟩).symm⟩
  · rintro ⟨c, hc⟩
    have : y = embL e c := h.1 (by rw [iota_embL h]; exact hc.symm)
    exact this ▸ embL_mem e c

omit [Finite K] in
theorem inf_centralizer_eq_map_fix {e : L ≃* PSL2 K} {ι : G →* PGammaL2 K} (h : Adapted e ι)
    {b : G} {t : PGL2 K} (hb : ι b = SemidirectProduct.inl t) :
    L ⊓ Subgroup.centralizer {b} =
      (MonoidHom.eqLocus (pglAction K t).toMonoidHom (MonoidHom.id (PSL2 K))).map (embL e) := by
  have key : ∀ c : PSL2 K, embL e c * b = b * embL e c ↔ pglAction K t c = c := by
    intro c
    rw [← h.1.eq_iff, map_mul, map_mul, iota_embL h, hb, ← map_mul, ← map_mul]
    rw [SemidirectProduct.inl_injective.eq_iff,
      ← Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.eq_iff, toPGL_pglAction]
    constructor
    · intro h1
      calc t * Matrix.ProjectiveSpecialLinearGroup.toPGL c * t⁻¹ =
          (Matrix.ProjectiveSpecialLinearGroup.toPGL c * t) * t⁻¹ := by rw [h1]
        _ = Matrix.ProjectiveSpecialLinearGroup.toPGL c := by group
    · intro h1
      calc Matrix.ProjectiveSpecialLinearGroup.toPGL c * t =
          (t * Matrix.ProjectiveSpecialLinearGroup.toPGL c * t⁻¹) * t := by rw [h1]
        _ = t * Matrix.ProjectiveSpecialLinearGroup.toPGL c := by group
  ext y
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hyL, hyc⟩
    refine ⟨e ⟨y, hyL⟩, (key _).mp ?_, embL_apply e hyL⟩
    rw [embL_apply]
    exact Subgroup.mem_centralizer_singleton_iff.mp hyc
  · rintro ⟨c, hc, rfl⟩
    exact ⟨embL_mem e c, Subgroup.mem_centralizer_singleton_iff.mpr ((key c).mpr hc)⟩

theorem oddTorus_of_adapted [Finite G] (hLn : L.Normal) {e : L ≃* PSL2 K} {ι : G →* PGammaL2 K}
    (h : Adapted e ι) (hK : IsOddPrimePower (Nat.card K)) (h4 : Nat.card K % 4 = 1)
    (h5 : 5 ≤ Nat.card K) {b : G} (hbL : b ∉ L) (hb2 : orderOf b = 2) (hr : (ι b).right = 1) :
    OddTorus L b := by
  set t := (ι b).left with ht
  have hb : ι b = SemidirectProduct.inl t := by
    rw [← SemidirectProduct.inl_left_mul_inr_right (ι b), hr, map_one, mul_one]
  have htt : t * t = 1 := by
    have hbb : b * b = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one b
      rwa [hb2] at this
    have h1 : ι (b * b) = 1 := by rw [hbb, map_one]
    rw [map_mul, hb, ← map_mul] at h1
    exact SemidirectProduct.inl_injective (h1.trans (map_one _).symm)
  have ht1 : t ≠ 1 := fun h1 => by
    have : ι b = ι 1 := by rw [hb, h1, map_one, map_one]
    rw [h.1 this, orderOf_one] at hb2
    omega
  have htr : t ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    rintro ⟨c, hc⟩
    apply hbL
    rw [mem_iff_of_adapted h, hb, ← hc]
    exact ⟨c, rfl⟩
  obtain ⟨d⟩ := CFSG.ComponentClassification.AutL2Facts.psl2_fix_outer_involution hK h4
    (by omega) htt ht1 htr
  set m := (Nat.card K + 1) / 2 with hm
  have hm3 : 3 ≤ m := by omega
  have : NeZero m := ⟨by omega⟩
  have hmodd : Odd m := ⟨(Nat.card K - 1) / 4, by omega⟩
  have heq := inf_centralizer_eq_map_fix h hb
  exact oddTorus_of_dihedral hLn hmodd hm3 ((MulEquiv.subgroupCongr heq).trans
    (((MonoidHom.eqLocus (pglAction K t).toMonoidHom (MonoidHom.id (PSL2 K))).equivMapOfInjective
      _ (embL_injective e)).symm.trans d))

end CFSG.Quasithin.Vol2.Ch11.SecU1
