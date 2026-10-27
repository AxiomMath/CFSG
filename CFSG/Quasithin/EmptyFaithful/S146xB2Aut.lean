module

public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LieType.SteinbergBRAutGL32
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_le_four_of_twoRank_le_two {N : Type} [Group N] [Finite N] (h : twoRank N ≤ 2)
    {E : Subgroup N} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := isPGroup_of_isElemAbelian hE
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
  have hk2 : k ≤ 2 := (le_pRank Nat.prime_two (le_top : E ≤ ⊤) hE hk).trans h
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

theorem card_le_eight_of_outer_dvd_two {N : Type} [Group N] [Finite N] [IsSimpleGroup N]
    (hout : Nat.card (Outer N) ∣ 2) (hN : twoRank N ≤ 2)
    {E : Subgroup (MulAut N)} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  classical
  let f : ↥E →* Outer N := (QuotientGroup.mk' (inner N)).comp E.subtype
  have hrange : Nat.card f.range ≤ 2 := by
    have h1 : Nat.card f.range ≤ Nat.card (Outer N) := Subgroup.card_le_card_group _
    have h2 : Nat.card (Outer N) ≤ 2 := Nat.le_of_dvd (by norm_num) hout
    omega
  have hmul : f.ker.index * Nat.card f.ker = Nat.card E := Subgroup.index_mul_card f.ker
  rw [Subgroup.index_ker] at hmul
  have hkerinner : ∀ x : ↥E, x ∈ f.ker → (x : MulAut N) ∈ inner N := fun x hx =>
    (QuotientGroup.eq_one_iff _).mp hx
  have hker : Nat.card f.ker ≤ 4 := by
    have hnormal : (Subgroup.center N).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with hc | hc
    ·
      let g : N →* MulAut N := MulAut.conj
      have hg : Function.Injective g := by
        rw [injective_iff_map_eq_one]
        intro x hx
        have : x ∈ Subgroup.center N := by
          rw [Subgroup.mem_center_iff]
          intro m
          have := congrArg (fun φ : MulAut N => φ m) hx
          simp only [g, MulAut.conj_apply, MulAut.one_apply] at this
          calc m * x = x * m * x⁻¹ * x := by rw [this]
            _ = x * m := by group
        rw [hc] at this
        exact Subgroup.mem_bot.mp this
      set W : Subgroup (MulAut N) := f.ker.map E.subtype with hW
      have hWE : ∀ w ∈ W, w ∈ E := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hWinner : ∀ w ∈ W, w ∈ inner N := by
        rintro _ ⟨x, hx, rfl⟩
        exact hkerinner x hx
      set E₁ : Subgroup N := W.comap g with hE₁
      have hcard : Nat.card f.ker = Nat.card E₁ := by
        rw [← Subgroup.card_map_of_injective (f := E.subtype) E.subtype_injective (K := f.ker),
          ← hW]
        have hmap : E₁.map g = W := by
          ext w
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact hx
          · intro hw
            obtain ⟨x, hx⟩ := hWinner w hw
            exact ⟨x, by simpa [hE₁] using
              (show g x ∈ W by rw [show g x = w from hx]; exact hw), hx⟩
        rw [← hmap, Subgroup.card_map_of_injective hg]
      have hE₁ab : IsElemAbelian 2 E₁ := by
        refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
        · apply Subtype.ext
          apply hg
          have ha := hWE _ a.2
          have hb := hWE _ b.2
          have hcomm := hE.1.is_comm.comm (⟨g a, ha⟩ : E) ⟨g b, hb⟩
          have := congrArg Subtype.val hcomm
          simpa [map_mul] using this
        · apply hg
          have hx2 := hE.2 _ (hWE _ hx)
          simpa [map_pow] using hx2
      rw [hcard]
      exact card_le_four_of_twoRank_le_two hN hE₁ab
    ·
      have hinner : inner N = ⊥ := by
        apply eq_bot_iff.mpr
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ Subgroup.center N := by rw [hc]; exact Subgroup.mem_top x
        rw [Subgroup.mem_bot]
        apply MulEquiv.ext
        intro m
        rw [MulAut.conj_apply, MulAut.one_apply]
        have := Subgroup.mem_center_iff.mp hx m
        calc x * m * x⁻¹ = m * x * x⁻¹ := by rw [← this]
          _ = m := by group
      have : f.ker = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h1 := hkerinner x hx
        rw [hinner, Subgroup.mem_bot] at h1
        rw [Subgroup.mem_bot]
        exact Subtype.ext h1
      rw [this]
      simp
  calc Nat.card E = Nat.card f.range * Nat.card f.ker := hmul.symm
    _ ≤ 2 * 4 := Nat.mul_le_mul hrange hker
    _ = 8 := by norm_num

theorem isElementaryAbelian_two_of_isElemAbelian {G : Type*} [Group G] {E : Subgroup G}
    (h : IsElemAbelian 2 E) : CFSG.IsElementaryAbelian 2 E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h

theorem card_le_eight_of_alt_six {N : Type} [Group N] (e : N ≃* alternatingGroup (Fin 6))
    {E : Subgroup (MulAut N)} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hel := isElementaryAbelian_two_of_isElemAbelian hE
  let Φ : MulAut N ≃* CFSG.QuasithinUnique.Setup.X3Aut.AutA6 :=
    (MulAut.congr e).trans CFSG.QuasithinUnique.Setup.X3Aut.thetaEquiv.symm
  let E' : Subgroup CFSG.QuasithinUnique.Setup.X3Aut.AutA6 := E.map Φ.toMonoidHom
  have hE'el : CFSG.IsElementaryAbelian 2 ↥E' :=
    CFSG.IsElementaryAbelian.map (A := E) Φ.toMonoidHom
  have hcard : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective Φ.injective
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).mp (CFSG.IsElementaryAbelian.isPGroup 2 ↥E')
  have := (CFSG.QuasithinUnique.Setup.X3Aut.rank_lemma r E' hE'el hr).1
  rw [← hcard, hr]
  calc 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
    _ = 8 := by norm_num

theorem card_le_four_of_equiv_sl_three_two {N : Type} [Group N]
    (e : N ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {E : Subgroup (MulAut N)} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hel := isElementaryAbelian_two_of_isElemAbelian hE
  let e' : N ≃* CFSG.QuasithinUnique.Setup.Family.GL32 :=
    e.trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3)
  let Φ := MulAut.congr e'
  have : Finite (MulAut N) := Finite.of_equiv _ Φ.symm.toEquiv
  have hcard : Nat.card (MulAut N) = 336 := by
    rw [Nat.card_congr Φ.toEquiv, CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]
  exact CFSG.LieType.SteinbergBR.card_le_sq_of_orderOf
    (g := Φ.symm CFSG.LieType.SteinbergBR.AutGL32.alphaAut) (k := 3)
    (by rw [MulEquiv.orderOf_eq, CFSG.LieType.SteinbergBR.AutGL32.orderOf_alphaAut])
    (by rw [hcard]; norm_num) E

theorem card_le_eight_of_isPSL_two {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : IsPSL 2 p 1 N) {E : Subgroup (MulAut N)} (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 8 := by
  have hsimple : IsSimpleGroup N := (CFSG.LieType.Simplicity.fam_PSL_simplicity N 2 p 1 h).2
  have hrank : twoRank N ≤ 2 :=
    CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2 h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hout := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hp K hK).2 N
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩
  have hout2 : Nat.card (Outer N) ∣ 2 := by
    refine hout.trans ?_
    rw [one_mul]
    exact Nat.gcd_dvd_left 2 _
  exact card_le_eight_of_outer_dvd_two hout2 hrank hE

theorem card_le_eight_of_isPSL_three_three {N : Type} [Group N] [Finite N]
    (h : IsPSL 3 3 1 N) {E : Subgroup (MulAut N)} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  have hsimple : IsSimpleGroup N := (CFSG.LieType.Simplicity.fam_PSL_simplicity N 3 3 1 h).2
  have hrank : twoRank N ≤ 2 :=
    CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_three_three h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  let e' : N ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K))
  have hdvd :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
      (k := K) (p := 3) (f := 1) (n := 3) Nat.prime_three le_rfl le_rfl hK
  have hout : Nat.card (Outer N) ∣ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    refine hdvd.trans ?_
    norm_num
  exact card_le_eight_of_outer_dvd_two hout hrank hE

theorem card_le_eight_of_shape {N : Type} [Group N] [Finite N]
    (hN : (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPSL 2 p 1 N) ∨ IsPSL 3 2 1 N ∨ IsAlt 6 N ∨ IsPSL 3 3 1 N)
    {E : Subgroup (MulAut N)} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  rcases hN with ⟨p, hp, hp2, h⟩ | h | h | h
  · exact card_le_eight_of_isPSL_two hp hp2 h hE
  · obtain ⟨e⟩ := isPSL_three_two_iff.mp h
    exact (card_le_four_of_equiv_sl_three_two e hE).trans (by norm_num)
  · obtain ⟨e⟩ : Nonempty (N ≃* alternatingGroup (Fin 6)) := h
    exact card_le_eight_of_alt_six e hE
  · exact card_le_eight_of_isPSL_three_three h hE

end CFSG.Quasithin
