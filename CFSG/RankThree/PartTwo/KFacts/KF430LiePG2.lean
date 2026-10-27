module

public import CFSG.RankThree.PartTwo.KFacts.KF430LiePCommon
public import CFSG.RankThree.PartTwo.KFacts.KF430LiePG2Act
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Holds

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KF430

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley CFSG.Quasithin.G2U
  CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding CFSG.GH74.GLS.Stage2.Bender.Thm1

section Torsion

variable {L : Type} [Field L]

theorem torus3_move {T : Subgroup (ModGL .G2 L)}
    (hT : ∀ t, t ∈ T ↔ ∃ b : Fin Tag.G2.rank → Lˣ, b ^ 3 = 1 ∧ t = rootDiagUnit .G2 b)
    {ζ : Lˣ} (hζ : orderOf ζ = 3) {n : ModGL .G2 L} (hn : n ∈ monomialSubgroup .G2 L)
    (hw : weylQuotientHom .G2 L ⟨n, hn⟩ = cox) :
    (∀ y, y ∈ T ↔ n * y * n⁻¹ ∈ T) ∧ (∃ y ∈ T, n ^ 2 * y * (n ^ 2)⁻¹ ≠ y) ∧
      (∃ y ∈ T, n ^ 3 * y * (n ^ 3)⁻¹ ≠ y) := by
  have hmem : ∀ u ∈ monomialSubgroup .G2 L, ∀ y ∈ T, u * y * u⁻¹ ∈ T := by
    intro u hu y hy
    obtain ⟨b, hb3, rfl⟩ := (hT y).1 hy
    obtain ⟨b', hb'3, hb'⟩ := exists_conj_cube_one hu hb3
    exact (hT _).2 ⟨b', hb'3, hb'⟩
  have hd : rootDiagUnit .G2 (cubeTuple3 ζ 1 0) ∈ T :=
    (hT _).2 ⟨_, cubeTuple3_pow_three hζ 1 0, rfl⟩
  obtain ⟨m2, m3⟩ := cox_sq_cube_move hζ hn hw
  refine ⟨fun y => ⟨hmem n hn y, fun h => ?_⟩, ⟨_, hd, m2⟩, ⟨_, hd, m3⟩⟩
  have := hmem n⁻¹ (inv_mem hn) _ h
  simpa [mul_assoc] using this

end Torsion

section E9


theorem rootWeyl_pair_mem_adjointGroup {L : Type} [Field L] (c₀ c₁ : Lˣ) :
    rootWeylSL2 .G2 L (vec 1 0) c₀ * rootWeylSL2 .G2 L (vec 0 1) c₁ ∈ adjointGroup .G2 L :=
  mul_mem ((exceptional_Lang_root_rank_one_data .G2 L (vec 1 0)).2.2.2.2.2.2.1 c₀).2
    ((exceptional_Lang_root_rank_one_data .G2 L (vec 0 1)).2.2.2.2.2.2.1 c₁).2

theorem e9Move_adjointG2_of_three_dvd_sub_one {K : Type} [Field K] [Finite K]
    (h31 : 3 ∣ Nat.card K - 1) : E9Move ↥(adjointGroup .G2 K) := by
  intro E hE hE9
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremA.T266.G2Holds.exists_conj_torus_of_elemAbelian
    h31 hE
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one Nat.prime_three h31
  set f : ↥(adjointGroup .G2 K) →* ModGL .G2 K :=
    (MulAut.conj (g : ModGL .G2 K)).toMonoidHom.comp (adjointGroup .G2 K).subtype with hfdef
  have hfx : ∀ x, f x = ((g * x * g⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) := fun x => by
    simp [hfdef]
  have hf : Function.Injective f := fun x y h => by
    rw [hfx, hfx] at h
    exact mul_left_cancel (mul_right_cancel (Subtype.ext h :
      (g * x * g⁻¹ : ↥(adjointGroup .G2 K)) = g * y * g⁻¹))
  have hT : ∀ t, t ∈ E.map f ↔ ∃ b : Fin Tag.G2.rank → Kˣ, b ^ 3 = 1 ∧ t = rootDiagUnit .G2 b := by
    intro t
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨b, hb3, hb⟩ := hg x hx
      exact ⟨b, hb3, by rw [hfx, hb]⟩
    · rintro ⟨b, hb3, rfl⟩
      obtain ⟨x, hx, hxb⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.T266.G2Holds.forall_exists_of_nine_le hg hE9.ge b hb3
      exact ⟨x, hx, by rw [hfx, hxb]⟩
  obtain ⟨hnm, hnw⟩ := rootWeyl_pair_mem_monomial (L := K) 1 1
  obtain ⟨hN, h2, h3⟩ := torus3_move hT hζ hnm hnw
  refine hasMove_of_injective f hf ⟨g⁻¹ * ⟨_, rootWeyl_pair_mem_adjointGroup 1 1⟩ * g, ?_⟩ hN h2 h3
  rw [hfx]
  simp [mul_assoc]

theorem e9Move_adjointG2_of_three_dvd_add_one {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (h3 : 3 ∣ Nat.card K + 1) : E9Move ↥(adjointGroup .G2 K) := by
  intro E hE hE9
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius_all K
  haveI : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  haveI : Finite K₂ := Module.finite_of_finite K
  obtain ⟨M⟩ := QPlusModel.nonempty_of_odd hodd hdeg hσ
  haveI : CFSG.IsElementaryAbelian 3 E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hE.2 g g.2) }
  obtain ⟨y, hyΓ, hy⟩ := M.exists_conj_plane_to_torsion hdeg hσ h3 E (by rw [hE9]; norm_num)
  have h3₂ : 3 ∣ Nat.card K₂ - 1 := by
    rw [natCard_eq_sq_of_finrank_eq_two hdeg]
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      zify [hq1, Nat.one_le_pow 2 _ hq1]
      ring
    rw [this]
    exact Dvd.dvd.mul_left h3 _
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one Nat.prime_three h3₂
  set f : ↥(adjointGroup .G2 K) →* ModGL .G2 K₂ :=
    (MulAut.conj y).toMonoidHom.comp (twistEmb M.g) with hfdef
  have hf : Function.Injective f := (MulAut.conj y).injective.comp (twistEmb_injective M.g)
  have hEf : E.map f = torusTorsion K₂ 3 := by
    rw [hfdef, ← Subgroup.map_map, hy]
  have hT : ∀ t, t ∈ E.map f ↔
      ∃ b : Fin Tag.G2.rank → K₂ˣ, b ^ 3 = 1 ∧ t = rootDiagUnit .G2 b := by
    intro t
    rw [hEf]
    constructor
    · intro ht
      obtain ⟨st, hst, rfl⟩ := ht
      exact ⟨_, (rootDiagUnit_mem_torusTorsion_iff 3 _).1 ⟨st, hst, rfl⟩, rfl⟩
    · rintro ⟨b, hb3, rfl⟩
      exact (rootDiagUnit_mem_torusTorsion_iff 3 b).2 hb3
  obtain ⟨c₀, hc₀Γ, -⟩ := M.exists_fixed_weyl hdeg hσ isRoot_vec10
  obtain ⟨c₁, hc₁Γ, -⟩ := M.exists_fixed_weyl hdeg hσ isRoot_vec01
  obtain ⟨hnm, hnw⟩ := rootWeyl_pair_mem_monomial (L := K₂) c₀ c₁
  obtain ⟨hN, h2, h3'⟩ := torus3_move hT hζ hnm hnw
  have hnΓ : y⁻¹ * (rootWeylSL2 .G2 K₂ (vec 1 0) c₀ * rootWeylSL2 .G2 K₂ (vec 0 1) c₁) * y ∈
      M.gamma :=
    mul_mem (mul_mem (inv_mem hyΓ) (mul_mem hc₀Γ hc₁Γ)) hyΓ
  obtain ⟨m, hm⟩ := M.exists_twistEmb_eq hnΓ
  refine hasMove_of_injective f hf ⟨m, ?_⟩ hN h2 h3'
  rw [hfdef, MonoidHom.comp_apply, hm]
  simp [mul_assoc]

theorem inner_adjointG2 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (hp3 : 3 ≤ p) (σ : MulAut ↥(adjointGroup .G2 K))
    (hσ : orderOf σ = 3) :
    σ ∈ (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range := by
  let q : TauCeti.PrimePower := ⟨p, 1, hp, one_pos⟩
  have hq : q.card = p := by rw [TauCeti.PrimePower.card_def]; exact pow_one p
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime q.p) := ⟨hp⟩
  haveI : CharP K q.p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hK)
  obtain ⟨Q, _, _, Θ, hQ, hker⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_hom_cyclic_G2 q (by rw [hq]; exact hp3) K
      (by rw [hq]; exact hK)
  have h1 : orderOf (Θ σ) ∣ 3 := hσ ▸ orderOf_map_dvd Θ σ
  have h2 : orderOf (Θ σ) ∣ 2 := (orderOf_dvd_natCard (Θ σ)).trans (by simpa [q] using hQ)
  have hord : orderOf (Θ σ) = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2
  rw [← hker]
  exact MonoidHom.mem_ker.2 (orderOf_eq_one_iff.1 hord)

theorem concl_adjointG2 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (hp3 : 3 < p) : Concl ↥(adjointGroup .G2 K) := by
  refine ⟨inner_adjointG2 hp hK hp3.le, center_adjointGroup_eq_bot, ?_⟩
  have hp2 : p % 3 = 1 ∨ p % 3 = 2 := by
    have : p % 3 ≠ 0 := fun h => by
      have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      rcases (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3 with rfl
      omega
    omega
  rcases hp2 with h | h
  · exact e9Move_adjointG2_of_three_dvd_sub_one (by rw [hK]; omega)
  · refine e9Move_adjointG2_of_three_dvd_add_one ?_ (by rw [hK]; omega)
    rw [hK]
    exact hp.odd_of_ne_two (by omega)

@[expose] def adjointQuotientEquivG2 (K : Type) [Field K] [Finite K] :
    AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
  (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot

theorem kf430LiePG2_holds : KF430LiePG2 := by
  intro p _ hp L _ _ hL
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
  rw [pow_one] at hK
  exact Concl.of_mulEquiv (e.trans (adjointQuotientEquivG2 K))
    (concl_adjointG2 Fact.out hK hp)

end E9

end CFSG.RankThree.PartTwo.KFacts.KF430
