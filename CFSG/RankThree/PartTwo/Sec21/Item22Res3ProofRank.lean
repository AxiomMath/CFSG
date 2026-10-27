module

public import CFSG.RankThree.PartTwo.Sec21.Commute33Rank
public import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofQuasi
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item22Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly (IsElemAbelian)
open scoped commutatorElement

theorem le_three_of_faithful_subgroup {G : Type} [Group G] [Finite G] {s : ℕ} (hs : s.Prime)
    (hs3 : 3 < s) (hloc : localRank s G < 3) {Q V : Subgroup G} (hQ : IsPGroup s Q)
    (hVQ : V ≤ Subgroup.normalizer (Q : Set G)) (hV : IsElemAbelian 2 V) {n : ℕ}
    (hVn : Nat.card V = 2 ^ n)
    (hfaith : ∀ v ∈ V, v ∈ Subgroup.centralizer (Q : Set G) → v = 1) : n ≤ 3 := by
  classical
  have : Fact s.Prime := ⟨hs⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hQnt : Nontrivial Q
  · obtain ⟨D₀, hD₀c, -, hD₀comm, hD₀exp, hD₀fix⟩ :=
      SectionRank.Ccomm.odd_critical_exponent_subgroup (p := s) (P := Q) (by omega) hQ
    have := hD₀c
    set D : Subgroup G := D₀.map Q.subtype with hDdef
    have hWD : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (D : Set G) :=
      SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic Q D₀
    let _ : CommGroup V := { (inferInstance : Group V) with mul_comm := hV.1.is_comm.comm }
    have hDp : IsPGroup s D := (hQ.to_subgroup D₀).map Q.subtype
    have hDexp : ∀ x ∈ D, x ^ s = 1 := by
      rintro _ ⟨d, hd, rfl⟩
      rw [← map_pow, hD₀exp d hd, map_one]
    have hDcl : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, ⁅x, y⁆ * z = z * ⁅x, y⁆ := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, -, rfl⟩ _ ⟨c, hc, rfl⟩
      have h1 : ⁅a, b⁆ ∈ D₀ ⊓ Subgroup.centralizer (D₀ : Set Q) :=
        hD₀comm (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))
      have h2 := Subgroup.mem_centralizer_iff.mp h1.2 c hc
      rw [← map_commutatorElement, ← map_mul, ← map_mul, h2]
    have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hV.2 v v.2)
    refine Sec21.Commute33Steps.le_three_of_faithful (V := V) hs3 hloc hDp hDexp hDcl hV2 hVn
      V.subtype (fun v => hWD (hVQ v.2)) fun v hvD => ?_
    have hT2 : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
      intro g
      obtain ⟨g, hg⟩ := g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hV.2 v v.2, one_zpow]
    have hvQ : (v : G) ∈ Subgroup.centralizer (Q : Set G) :=
      PartOne.le_centralizer_of_centralizes_critical_subgroup hs (by omega)
        (Subgroup.zpowers_le.mpr (hVQ v.2)) hT2 D₀ hD₀fix (Subgroup.zpowers_le.mpr hvD)
        (Subgroup.mem_zpowers _)
    exact Subtype.ext (hfaith v v.2 hvQ)
  · rw [not_nontrivial_iff_subsingleton] at hQnt
    have hV1 : ∀ v ∈ V, v = 1 := fun v hv => hfaith v hv (by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq1 : q = 1 := congrArg Subtype.val (Subsingleton.elim (⟨q, hq⟩ : Q) 1)
      rw [hq1, one_mul, mul_one])
    have hVb : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hV1
    rw [hVb, Subgroup.card_bot] at hVn
    have : n = 0 := Nat.pow_right_injective le_rfl (hVn.symm.trans (pow_zero 2).symm)
    omega

variable {Y : Type} [Group Y] [Finite Y]

theorem theta_le_center_of_rank
    (hloc : ∀ s : ℕ, s.Prime → 3 < s → localRank s Y < 3) [Group.IsPerfect Y]
    (hYq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y))
    (hθodd : Odd (Nat.card (aschbacherSolvableCore 3 Y)))
    (hZ : ∀ z ∈ Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y), z ^ 2 = 1 → z = 1)
    {V : Subgroup Y} (hV : IsElemAbelian 2 V) {n : ℕ} (hn : 4 ≤ n)
    (hVn : Nat.card V = 2 ^ n) :
    aschbacherSolvableCore 3 Y ≤ Subgroup.center Y := by
  classical
  obtain ⟨hTs, hTchar, hT3, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  set T := aschbacherSolvableCore 3 Y with hT
  have hTn : T.Normal := by
    have := hTchar
    infer_instance
  have hA : ∀ s : ℕ, s.Prime → (pCore s T).map T.subtype ≤ Subgroup.center Y := by
    intro s hs
    have : Fact s.Prime := ⟨hs⟩
    set Q : Subgroup Y := (pCore s T).map T.subtype with hQdef
    have hQp : IsPGroup s Q := pCore_isPGroup.map T.subtype
    have hQT : Nat.card Q ∣ Nat.card T := by
      rw [hQdef, Subgroup.card_map_of_injective T.subtype_injective]
      exact Subgroup.card_subgroup_dvd_card _
    by_cases hs3 : 3 < s
    · have hQn : Q.Normal := by
        have h1 : Subgroup.normalizer (T : Set Y) ≤ Subgroup.normalizer (Q : Set Y) :=
          SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic T (pCore s T)
        rw [Subgroup.normalizer_eq_top_iff.mpr hTn] at h1
        exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
      set C := Subgroup.centralizer (Q : Set Y) with hCdef
      have hCn : C.Normal := Subgroup.normal_centralizer
      by_cases hCtop : C = ⊤
      · intro q hq
        rw [Subgroup.mem_center_iff]
        intro y
        have hy : y ∈ C := hCtop ▸ Subgroup.mem_top y
        exact (Subgroup.mem_centralizer_iff.mp hy q hq).symm
      · exfalso
        have hCmap : C.map (QuotientGroup.mk' T) ≤ Subgroup.center (Y ⧸ T) := by
          rcases CFSG.LocalCores.quasisimple_normal_subgroups hYq
              (hCn.map _ (QuotientGroup.mk'_surjective T)) with h | h
          · exfalso
            apply hCtop
            refine Sec4.Census.eq_top_of_isSolvable_quotient ?_
            have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp T.subtype) := by
              intro x
              induction x using QuotientGroup.induction_on with
              | H g =>
                have hg : QuotientGroup.mk' T g ∈ C.map (QuotientGroup.mk' T) := by
                  rw [h]
                  trivial
                obtain ⟨c, hc, hcg⟩ := hg
                have hk : c⁻¹ * g ∈ T := QuotientGroup.eq.mp hcg
                refine ⟨⟨c⁻¹ * g, hk⟩, ?_⟩
                change (QuotientGroup.mk (c⁻¹ * g) : Y ⧸ C) = QuotientGroup.mk g
                rw [QuotientGroup.eq, show (c⁻¹ * g)⁻¹ * g = g⁻¹ * c * g by group]
                exact hCn.conj_mem' c hc g
            exact Group.isSolvable_of_surjective hsurj
          · exact h
        have hfaith : ∀ v ∈ V, v ∈ Subgroup.centralizer (Q : Set Y) → v = 1 := by
          intro v hv hvC
          have h1 : QuotientGroup.mk' T v ∈ Subgroup.center (Y ⧸ T) := hCmap ⟨v, hvC, rfl⟩
          have h2 : (QuotientGroup.mk' T v) ^ 2 = 1 := by rw [← map_pow, hV.2 v hv, map_one]
          have hvT : v ∈ T := (QuotientGroup.eq_one_iff v).mp (hZ _ h1 h2)
          exact Sec21.Commute33Steps.eq_one_of_pow_two_pow hθodd hvT (k := 1)
            (by rw [pow_one]; exact hV.2 v hv)
        have hVQ : V ≤ Subgroup.normalizer (Q : Set Y) := by
          rw [Subgroup.normalizer_eq_top_iff.mpr hQn]
          exact le_top
        have := le_three_of_faithful_subgroup hs hs3 (hloc s hs hs3) hQp hVQ hV hVn hfaith
        omega
    ·
      obtain ⟨k, hk⟩ := hQp.exists_card_eq
      have hk0 : k = 0 := by
        by_contra hk0
        have hsT : s ∣ Nat.card T := (dvd_pow_self s hk0).trans (hk ▸ hQT)
        have hs23 : s = 2 ∨ s = 3 := by
          have := hs.two_le
          interval_cases s <;> simp_all
        rcases hs23 with rfl | rfl
        · exact (Nat.not_even_iff_odd.mpr hθodd) (even_iff_two_dvd.mpr hsT)
        · exact hT3 hsT
      rw [hk0, pow_zero] at hk
      rw [Subgroup.eq_bot_of_card_eq Q hk]
      exact bot_le
  have hF : (fittingSubgroup T).map T.subtype ≤ Subgroup.center Y := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
    exact iSup_le fun p => hA p (Nat.prime_of_mem_primeFactors p.2)
  have hTF : (⊤ : Subgroup T) ≤ fittingSubgroup T := by
    refine le_trans (fun t _ => ?_)
      (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hTs)
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    have := Subgroup.mem_center_iff.mp (hF ⟨f, hf, rfl⟩) (t : Y)
    simpa using this.symm
  intro t ht
  exact hF ⟨⟨t, ht⟩, hTF (Subgroup.mem_top _), rfl⟩

theorem isQuasisimple_of_theta_le_center [Group.IsPerfect Y]
    (hYq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y))
    (hθ : aschbacherSolvableCore 3 Y ≤ Subgroup.center Y) : IsQuasisimple Y := by
  obtain ⟨-, hTchar, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  set T := aschbacherSolvableCore 3 Y with hT
  have : T.Normal := by
    have := hTchar
    infer_instance
  set K₀ := Item21EarlyProof.centerPre T with hK₀
  have : IsSimpleGroup ((Y ⧸ T) ⧸ Subgroup.center (Y ⧸ T)) := hYq.2.1
  have : IsSimpleGroup (Y ⧸ K₀) := (Item21EarlyProof.centerPreEquiv T).isSimpleGroup
  have hnc : ∃ a b : Y ⧸ K₀, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hcomm : IsMulCommutative (Y ⧸ K₀) := ⟨⟨h⟩⟩
    have : Group.IsPerfect (Y ⧸ K₀) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' K₀) (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.not_isMulCommutative (Y ⧸ K₀) hcomm
  have hK₀Z : K₀ ≤ Subgroup.center Y := by
    refine Item21EarlyProof.le_center_of_commutator_le (le_trans ?_ hθ)
    rw [Subgroup.commutator_le]
    intro k hk y _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
    have hk' : QuotientGroup.mk' T k ∈ Subgroup.center (Y ⧸ T) := hk
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hk' (QuotientGroup.mk' T y)).symm
  exact Item21EarlyProof.isQuasisimple_of_le_center hnc hK₀Z

end CFSG.RankThree.PartTwo.Sec21.Item22Res3Proof
