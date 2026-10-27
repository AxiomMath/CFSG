module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocTheta
public import CFSG.Milestones.LR_rank_two_isomorphism_types
import CFSG.Assembly.LowTwoRank
import CFSG.RankThree.SubgroupLists.RationalFiveExclusions
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedM11)

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def autRestrict {E : Subgroup (MulAut X)} {K : Subgroup X}
    (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) (ε : E) : MulAut K :=
  (MulEquiv.subgroupMap (ε : MulAut X) K).trans
    (MulEquiv.subgroupCongr (map_eq_of_invariant hKE ε.2))

@[expose] noncomputable def restrictAut {E : Subgroup (MulAut X)} {K : Subgroup X}
    (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) : E →* MulAut K where
  toFun := autRestrict hKE
  map_one' := by
    ext k
    rfl
  map_mul' a b := by
    ext k
    rfl

theorem restrictAut_apply {E : Subgroup (MulAut X)} {K : Subgroup X}
    (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) (ε : E) (k : K) :
    ((restrictAut hKE ε k : K) : X) = (ε : MulAut X) k :=
  rfl

theorem map_autFix_restrictAut {E : Subgroup (MulAut X)} {K : Subgroup X}
    (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) (ε : E) :
    (Sec4.autFix (restrictAut hKE ε)).map K.subtype = K ⊓ Sec4.autFix (ε : MulAut X) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf, Sec4.mem_autFix]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Sec4.mem_autFix] at hk
    exact ⟨k.2, congrArg Subtype.val hk⟩
  · rintro ⟨hxK, hxε⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [Sec4.mem_autFix]
    exact Subtype.ext hxε

theorem pPrimeCoreOf_map_injective {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (H : Subgroup A) :
    pPrimeCoreOf 3 (H.map f) = (pPrimeCoreOf 3 H).map f := by
  let ψ : ↥H ≃* ↥(H.map f) := Subgroup.equivMapOfInjective H f hf
  have h1 : (pPrimeCore 3 ↥H).map ψ.toMonoidHom = pPrimeCore 3 ↥(H.map f) :=
    pPrimeCore_map_iso 3 ψ
  have h2 : (H.map f).subtype.comp ψ.toMonoidHom = f.comp H.subtype := by
    ext g
    rfl
  unfold pPrimeCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem restrictAut_injective {E : Subgroup (MulAut X)} {K : Subgroup X}
    (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) (hfaith : ∀ ε ∈ E, ε ≠ 1 → ¬ K ≤ Sec4.autFix ε) :
    Function.Injective (restrictAut hKE) := by
  rw [injective_iff_map_eq_one]
  intro ε hε
  by_contra h1
  refine hfaith ε ε.2 (fun h => h1 (Subtype.ext h)) fun k hk => ?_
  rw [Sec4.mem_autFix]
  have h2 := congrArg (fun σ : MulAut K => ((σ ⟨k, hk⟩ : K) : X)) hε
  exact h2

theorem top_le_iSup_restrictAut {E : Subgroup (MulAut X)} {K : Subgroup X}
    (hKE : ∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) (hinj : Function.Injective (restrictAut hKE))
    (hgen : K ≤ ⨆ (ε : MulAut X) (_ : ε ∈ E) (_ : ε ≠ 1), pPrimeCoreOf 3 (K ⊓ Sec4.autFix ε)) :
    (⊤ : Subgroup K) ≤ ⨆ (ε' : MulAut K) (_ : ε' ∈ (restrictAut hKE).range) (_ : ε' ≠ 1),
      pPrimeCoreOf 3 (Sec4.autFix ε') := by
  set S := ⨆ (ε' : MulAut K) (_ : ε' ∈ (restrictAut hKE).range) (_ : ε' ≠ 1),
    pPrimeCoreOf 3 (Sec4.autFix ε') with hS
  have hKS : K ≤ S.map K.subtype := by
    refine hgen.trans (iSup_le fun ε => iSup_le fun hε => iSup_le fun hε1 => ?_)
    have hne : restrictAut hKE ⟨ε, hε⟩ ≠ 1 := by
      intro h
      apply hε1
      have h2 := hinj (h.trans (map_one (restrictAut hKE)).symm)
      exact congrArg Subtype.val h2
    rw [← map_autFix_restrictAut hKE ⟨ε, hε⟩,
      pPrimeCoreOf_map_injective K.subtype K.subtype_injective]
    refine Subgroup.map_mono ?_
    exact le_iSup_of_le (restrictAut hKE ⟨ε, hε⟩)
      (le_iSup_of_le ⟨⟨ε, hε⟩, rfl⟩ (le_iSup_of_le hne le_rfl))
  intro k _
  obtain ⟨k', hk', hkk⟩ := hKS k.2
  have : k' = k := Subtype.ext hkk
  rw [← this]
  exact hk'

theorem isElemAbelian_map_subtype {K : Subgroup X} {P : Subgroup K}
    (hP : CFSG.Assembly.IsElemAbelian 3 P) : CFSG.Assembly.IsElemAbelian 3 (P.map K.subtype) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, a, ha, rfl⟩ := x
    obtain ⟨_, b, hb, rfl⟩ := y
    apply Subtype.ext
    have h := congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    change ((a * b : K) : X) = ((b * a : K) : X)
    rw [show a * b = b * a from h]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hP.2 a ha, map_one]

theorem isPGroup_center_of_theta_eq_bot {K : Type} [Group K] [Finite K]
    (hθ : aschbacherSolvableCore 3 K = ⊥) : IsPGroup 3 (Subgroup.center K) := by
  have hchar := (solvable_prime_complement_core_characterization (H := K) Nat.prime_three)
  intro z
  obtain ⟨a, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 3 (by norm_num)
  refine ⟨a, ?_⟩
  set y : K := (z : K) ^ (3 ^ a) with hy
  have hyZ : y ∈ Subgroup.center K := Subgroup.pow_mem _ z.2 _
  have hyo : orderOf y = m := by
    rw [hy, orderOf_pow' _ (pow_ne_zero _ (by norm_num)), Subgroup.orderOf_coe, hn,
      Nat.gcd_eq_right (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  have hN : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : g * y ^ k = y ^ k * g :=
      ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hyZ k)) g)
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers y k
  have hsol : Group.IsSolvable (Subgroup.zpowers y) :=
    isSolvable_of_comm fun a b => by
      obtain ⟨_, i, rfl⟩ := a
      obtain ⟨_, j, rfl⟩ := b
      apply Subtype.ext
      change y ^ i * y ^ j = y ^ j * y ^ i
      rw [← zpow_add, ← zpow_add, add_comm]
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers, hyo]
    exact hm3
  have hle := hchar.2.2.2.1 _ hN hsol h3
  rw [hθ] at hle
  have hy1 : y = 1 := (Subgroup.mem_bot).mp (hle (Subgroup.mem_zpowers y))
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact hy1

theorem not_eleven_dvd_card_GL_25 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 25) :
    ¬ 11 ∣ Nat.card (GL (Fin 3) F) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num

theorem not_eleven_dvd_of_five [Fact (Nat.Prime 5)] {e : ℕ} (he : 1 ≤ e) (he2 : e ≤ 2)
    (hiso : Sec4.IsoLThreePi X 5 e) : ¬ 11 ∣ Nat.card X := by
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  have hF25 : Nat.card F = 25 := by
    have hc := hF.card
    cases π
    ·
      change (5 ^ e) % 3 = 2 at hq
      have he1 : e = 1 := by
        interval_cases e
        · rfl
        · norm_num at hq
      subst he1
      rw [hc]
      rfl
    · change (5 ^ e) % 3 = 1 at hq
      have he1 : e = 2 := by
        interval_cases e
        · norm_num at hq
        · rfl
      subst he1
      rw [hc]
      rfl
  have := hF.finite
  intro h11
  apply not_eleven_dvd_card_GL_25 hF25
  have h1 : Nat.card X = Nat.card (CFSG.Assembly.RankThreeEven.projImage
      (Sec4.slPi π 3 (5 ^ e) F)) := Nat.card_congr φ.toEquiv
  have h2 : Nat.card (CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (5 ^ e) F)) ∣
      Nat.card (Matrix.ProjGenLinGroup (Fin 3) F) := Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card (Matrix.ProjGenLinGroup (Fin 3) F) ∣ Nat.card (GL (Fin 3) F) := by
    unfold Matrix.ProjGenLinGroup
    exact Subgroup.card_quotient_dvd_card _
  rw [h1] at h11
  exact h11.trans (h2.trans h3)

theorem l325_or_u35 [Fact (Nat.Prime 5)] {e : ℕ} (he : 1 ≤ e) (he2 : e ≤ 2)
    (hiso : Sec4.IsoLThreePi X 5 e) :
    Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2)) ∨
      Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1) := by
  rcases hiso with ⟨hq, hφ⟩ | ⟨hq, hφ⟩
  · interval_cases e
    · norm_num at hq
    · exact Or.inl hφ
  · interval_cases e
    · exact Or.inr hφ
    · norm_num at hq

theorem inspectSig148L3Loc_of_parts (hEven : InspectSig148L3LocEven) (hCF : OddCenterFree)
    (h2R : OddTwoRank) (h3R : OddThreeRank) (hL2 : OddL2Excl) (hL3 : OddL3U3)
    (hU34 : OddU34Excl) (hFive : OddFive) : InspectSig148L3Loc := by
  intro X _ _ hL hlist hq E hE9 hE3 hloc hfix K hKE hKp hK1 hKq hK46 hgen
  obtain ⟨p, e, hp, he, hiso⟩ := hL
  by_cases hp2 : p = 2
  · subst hp2
    exact hEven X e he hiso hlist E hE9 hE3 hloc hfix K hKE hKp hK1 hKq hK46 hgen
  have he2 : e ≤ 2 := (hq p e he hiso).resolve_left hp2
  have hθ := theta_eq_bot_of_loc hE9 hE3 hloc hfix hKE hKp hK1 hgen
  have hKq' : IsQuasisimple K := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot) hKq
  have hZ : Subgroup.center K = ⊥ :=
    hCF X p e hp2 he hiso K hKq' (isPGroup_center_of_theta_eq_bot hθ)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hKq'.2.1
  haveI hKs : IsSimpleGroup K := MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKq'.2.2
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  have hrank : CFSG.Assembly.twoRank K = 2 := by
    refine le_antisymm (h2R X p e hp2 he hiso K) ?_
    refine CFSG.Assembly.LowTwoRank.two_le_twoRank K hnonab ?_
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    haveI := hKp
    have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
    exact Group.IsPerfect.not_isSolvable K hsolv
  rcases CFSG.Milestones.lr_rank_two_isomorphism_types K hnonab hrank with
    ⟨r, f, hr, hr2, hf, hM⟩ | ⟨r, f, hr, hr2, hf, hM⟩ | ⟨r, f, hr, hr2, hf, hM⟩ | hM | hφ | hφ
  ·
    exfalso
    have hfaith : ∀ ε ∈ E, ε ≠ 1 → ¬ K ≤ Sec4.autFix ε := fun ε hε hε1 =>
      faithful_of_loc hE9 hE3 hloc hfix hKE hKp hK1 hgen hε hε1
    have hinj := restrictAut_injective hKE hfaith
    refine hL2 K r f hr hr2 hf hKs hM (fun P hP => ?_) (restrictAut hKE).range ?_ ?_
      (top_le_iSup_restrictAut hKE hinj hgen)
    · rw [← Subgroup.card_map_of_injective K.subtype_injective]
      exact h3R X p e he hiso _ (isElemAbelian_map_subtype hP)
    · rw [← hE9]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    · rintro _ ⟨ε, rfl⟩
      rw [← map_pow, show ε ^ 3 = 1 from Subtype.ext (hE3 ε ε.2), map_one]
  · exact hL3 X p e hp2 he he2 hiso K hKs r f hr hr2 hf (Or.inl hM)
  · exact hL3 X p e hp2 he he2 hiso K hKs r f hr hr2 hf (Or.inr hM)
  · exact (hU34 X p e hp2 he hiso K hM).elim
  ·
    obtain ⟨φ⟩ := hφ
    have hp5 : p = 5 := by
      refine hFive X p e he hiso (K.subtype (φ.symm SubgroupLists.a7Five))
        (K.subtype (φ.symm SubgroupLists.a7Conj)) ?_ ?_ ?_
      · rw [← map_pow, ← map_pow, SubgroupLists.a7Five_pow_five, map_one, map_one]
      · intro h
        apply SubgroupLists.a7Five_ne_one
        apply φ.symm.injective
        rw [map_one]
        exact K.subtype_injective (h.trans (map_one K.subtype).symm)
      · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
          SubgroupLists.a7Conj_conj, map_pow, map_pow]
    subst hp5
    exact Or.inr (Or.inl ⟨⟨hp, l325_or_u35 he he2 hiso⟩, ⟨φ⟩⟩)
  ·
    exfalso
    obtain ⟨φ⟩ := hφ
    have hp5 : p = 5 := by
      refine hFive X p e he hiso (K.subtype (φ.symm SubgroupLists.m11Five))
        (K.subtype (φ.symm SubgroupLists.m11B)) ?_ ?_ ?_
      · rw [← map_pow, ← map_pow, SubgroupLists.m11Five_pow_five, map_one, map_one]
      · intro h
        apply SubgroupLists.m11Five_ne_one
        apply φ.symm.injective
        rw [map_one]
        exact K.subtype_injective (h.trans (map_one K.subtype).symm)
      · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
          SubgroupLists.m11B_conj, map_pow, map_pow]
    subst hp5
    apply not_eleven_dvd_of_five he he2 hiso
    have h11 : 11 ∣ Nat.card K := by
      rw [Nat.card_congr φ.toEquiv, CFSG.Semidihedral.GL2Recognition.card_lowTwoRankStatedM11]
      norm_num
    exact h11.trans (Subgroup.card_subgroup_dvd_card K)

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
