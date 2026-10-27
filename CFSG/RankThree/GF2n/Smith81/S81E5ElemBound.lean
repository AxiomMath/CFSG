module

public import CFSG.RankThree.GF2n.Smith81.S81TNonfused
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinCard

public section


namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.LieType.Steinberg.Minuscule

theorem card_le_pow_of_isElemAbelian_EAut {K : Type} [Field K] [Finite K] [CharP K 2]
    {A : Subgroup (V K ≃ₗ[K] V K)} (hA : A ≤ EAut K) (hel : IsElemAbelian 2 A) :
    Nat.card A ≤ Nat.card K ^ 27 := by
  set A₀ : Subgroup (e7Data_valid.minGroup K) :=
    A.comap ((vAut K).toMonoidHom.comp (e7Data_valid.minGroup K).subtype) with hA₀
  have hmem : ∀ a : e7Data_valid.minGroup K, a ∈ A₀ ↔ vAut K (a : (Module.End K (V K))ˣ) ∈ A :=
    fun a => Iff.rfl
  let e : A₀ ≃ A :=
    { toFun := fun a => ⟨vAut K ((a : e7Data_valid.minGroup K) : (Module.End K (V K))ˣ),
        (hmem a).mp a.2⟩
      invFun := fun x => ⟨⟨(vAut K).symm x, mem_EAut_iff.mp (hA x.2)⟩,
        (hmem _).mpr (by simpa using x.2)⟩
      left_inv := fun a => by
        apply Subtype.ext
        apply Subtype.ext
        simp
      right_inv := fun x => by
        apply Subtype.ext
        simp }
  have hcard : Nat.card A₀ = Nat.card A := Nat.card_congr e
  have hsq : ∀ a ∈ A₀, a ^ 2 = 1 := by
    intro a ha
    apply Subtype.ext
    apply (vAut K).injective
    have h := hel.2 _ ((hmem a).mp ha)
    rw [← map_pow] at h
    simpa using h
  rw [← hcard]
  exact CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.e7_abelian_card_bound K A₀ hsq

theorem elemBoundE5_of_uniform
    (hFE1 : Smith24E5UniformStatement) : ElemBoundE5Statement := by
  intro G _ _ M Q Z B IH hc h5 _ n hw A hAS hAel
  have hw28 : Width Q Z 28 := by
    obtain ⟨t, -, h⟩ := h5
    exact h.1
  have hn : n = 28 := width_unique hc.ctx.hyp hw hw28
  subst hn
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h5 K γ M₀ hg
  have hLM : Lgen M (LB M Q B) ≤ M := iSup₂_le fun m hm => by
    calc conjSubgroup m (LB M Q B) ≤ conjSubgroup m M := Subgroup.map_mono hc.ctx.LB_le_M
      _ = M := hc.ctx.conj_M_eq hm
  set θ : ↥(Lgen M (LB M Q B)) →* ↥M ⧸ Q.subgroupOf M :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hLM) with hθ
  have hker : θ.ker = φ.ker := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, d.ker s, hθ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hAθ : A ≤ θ.range := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp (hAS ha)
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  let e : θ.range ≃* φ.range := (QuotientGroup.quotientKerEquivRange θ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange φ))
  set A₁ : Subgroup θ.range := A.subgroupOf θ.range with hA₁
  set A₂ : Subgroup (V K ≃ₗ[K] V K) := (A₁.map e.toMonoidHom).map φ.range.subtype with hA₂
  have hA₂le : A₂ ≤ EAut K := by
    rw [← d.range]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hA₁el : IsElemAbelian 2 A₁ := hAel.comap θ.range.subtype_injective
  have hA₂el : IsElemAbelian 2 A₂ := (hA₁el.map _).map _
  have hcard : Nat.card A₂ = Nat.card A := by
    have h2 : Nat.card A₂ = Nat.card A₁ := by
      rw [hA₂, Subgroup.card_map_of_injective φ.range.subtype_injective,
        Subgroup.card_map_of_injective e.injective]
    have h3 : Nat.card A₁ = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAθ).toEquiv
    rw [h2, h3]
  have hbound := card_le_pow_of_isElemAbelian_EAut hA₂le hA₂el
  rw [hcard, hg.card] at hbound
  simpa using hbound

end CFSG.RankThree.GF2n.Smith81
