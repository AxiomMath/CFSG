module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2PerfectSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFF7

open CFSG.Quasithin CFSG.Open CFSG.GorensteinWalter Subgroup

theorem oTwoPTwo_eq_top_of {X : Type} [Group X] {K U M : Subgroup X}
    (hUn : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    (hMn : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hM3 : ∀ m ∈ M, m ^ 3 ∈ U) (hK2 : ∀ k ∈ K, k ^ 2 ∈ M) :
    E1.oTwoPTwo ↥K 3 = ⊤ := by
  have hU'n : (U.subgroupOf K).Normal :=
    ⟨fun u hu k => by
      simp only [mem_subgroupOf, coe_mul, coe_inv] at hu ⊢
      exact hUn k k.2 u hu⟩
  have hM'n : (M.subgroupOf K).Normal :=
    ⟨fun m hm k => by
      simp only [mem_subgroupOf, coe_mul, coe_inv] at hm ⊢
      exact hMn k k.2 m hm⟩
  have h1 : U.subgroupOf K ≤ CFSG.Open.pCore 2 ↥K := by
    refine CFSG.LieType.BorelTits.le_pCore 2 hU'n fun u => ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hU2 _ u.2
  have h2 : M.subgroupOf K ≤ E1.oTwoP ↥K 3 := by
    intro m hm
    show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) m ∈ CFSG.Open.pCore 3 _
    have hN : ((M.subgroupOf K).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K))).Normal :=
      hM'n.map _ (QuotientGroup.mk'_surjective _)
    have hP : IsPGroup 3
        ((M.subgroupOf K).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K))) := by
      rintro ⟨_, m', hm', rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, coe_pow, OneMemClass.coe_one]
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      apply h1
      show ((m' ^ 3 : ↥K) : X) ∈ U
      simpa using hM3 _ hm'
    exact CFSG.LieType.BorelTits.le_pCore 3 hN hP ⟨m, hm, rfl⟩
  have h3 : CFSG.Open.pCore 2 (↥K ⧸ E1.oTwoP ↥K 3) = ⊤ := by
    refine top_le_iff.mp (CFSG.LieType.BorelTits.le_pCore 2 normal_top ?_)
    rintro ⟨q, -⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (E1.oTwoP ↥K 3) q
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, coe_pow, OneMemClass.coe_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    apply h2
    show ((k ^ 2 : ↥K) : X) ∈ M
    simpa using hK2 _ k.2
  unfold E1.oTwoPTwo
  rw [h3, comap_top]

theorem irredOnFrattiniQuot_of_card_prime {X : Type} [Group X] {S Y : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hY : Nat.card Y = p) : IrredOnFrattiniQuot S Y := by
  have hpY : Fact (Nat.card Y).Prime := ⟨hY ▸ hp⟩
  have hYfin : Finite Y := Nat.finite_of_card_ne_zero (hY ▸ hp.ne_zero)
  have hYbot : (⊤ : Subgroup Y) ≠ ⊥ := by
    intro h
    have := congrArg (fun H : Subgroup Y => Nat.card H) h
    simp only [card_top, card_bot] at this
    exact hp.one_lt.ne' (hY ▸ this)
  have hfr : frattini ↥Y = ⊥ := by
    refine le_bot_iff.mp (frattini_le_coatom ⟨hYbot.symm, fun H hH => ?_⟩)
    exact (H.eq_bot_or_eq_top_of_prime_card).resolve_left hH.ne'
  have hnf : nineFrattini Y = ⊥ := by
    unfold nineFrattini
    rw [hfr, Subgroup.map_bot]
  refine ⟨?_, fun Z hZ1 hZ2 _ => ?_⟩
  · rw [hnf, bot_lt_iff_ne_bot]
    intro h
    have := congrArg (fun H : Subgroup X => Nat.card H) h
    simp only [card_bot] at this
    exact hp.one_lt.ne' (hY ▸ this)
  · rw [hnf]
    rcases (Z.subgroupOf Y).eq_bot_or_eq_top_of_prime_card with h | h
    · left
      rw [subgroupOf_eq_bot] at h
      exact le_bot_iff.mp fun z hz => mem_bot.mpr (disjoint_def.mp h hz (hZ2 hz))
    · right
      rw [subgroupOf_eq_top] at h
      exact le_antisymm hZ2 h

theorem exists_ne_one_ne_of_four_le {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (h4 : 4 ≤ Nat.card A) : ∃ a ∈ A, ∃ b ∈ A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hA : (A : Set X).ncard = Nat.card A := (Nat.card_coe_set_eq (A : Set X)).symm
  have h1 : ((A : Set X) \ {1}).ncard = (A : Set X).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem (one_mem A)
  have hlt : 1 < ((A : Set X) \ {1}).ncard := by omega
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff).mp hlt
  exact ⟨a, ha.1, b, hb.1, ha.2, hb.2, hab⟩

theorem lb_facts {X : Type} [Group X] (ψ : X ≃* PGL2 (ZMod 7)) {Lb : Subgroup X}
    (hLn : Lb.Normal) (hL1 : Lb ≠ ⊥) (hLp : ⁅Lb, Lb⁆ = Lb) :
    Nat.card Lb = 168 ∧ IsSimpleGroup Lb ∧ centralizer (Lb : Set X) = ⊥ := by
  have hK : IsOddPrimePower (Nat.card (ZMod 7)) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by simp⟩
  have h7 : 3 < Nat.card (ZMod 7) := by simp
  set J := Lb.map ψ.toMonoidHom with hJdef
  have hJne : J ≠ ⊥ := by
    intro h
    exact hL1 ((map_eq_bot_iff_of_injective _ ψ.injective).mp h)
  have hJperf : Group.IsPerfect J := by
    rw [Subgroup.isPerfect_iff, hJdef, ← map_commutator, hLp]
  have hJn : J.Normal := hLn.map _ ψ.surjective
  have hJ := (pgl2_perfect_subnormal_eq_commutator (ZMod 7) hK J hJne hJperf
    hJn.isSubnormal).2
  rw [pgl2_commutator_eq_psl2_range_of_card_gt_three (ZMod 7) hK h7] at hJ
  set R := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod 7)).range
  have eLR : ↥Lb ≃* PSL2 (ZMod 7) :=
    ((equivMapOfInjective Lb ψ.toMonoidHom ψ.injective).trans (MulEquiv.subgroupCongr hJ)).trans
      (psl2EquivToPGLRange (ZMod 7)).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr eLR.toEquiv, psl2_card_formula (ZMod 7) hK]
    simp
  · have : IsSimpleGroup (PSL2 (ZMod 7)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simp)
    exact eLR.isSimpleGroup
  · have hcent := pgl2_psl2Range_centralizer_eq_bot (ZMod 7) hK
    refine le_bot_iff.mp fun x hx => ?_
    have hψx : ψ x ∈ centralizer (R : Set (PGL2 (ZMod 7))) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [← hJ] at hh
      obtain ⟨l, hl, rfl⟩ := hh
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hx l hl]
    rw [hcent, mem_bot] at hψx
    exact mem_bot.mpr (ψ.injective (by rw [hψx, map_one]))

end CFSG.LocalAnalysis.WeakClosure81.NFF7
