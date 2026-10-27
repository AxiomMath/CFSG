module

public import CFSG.RankThree.PartTwo.Sec4.T444.Step452
public import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven
open scoped Pointwise

section Theta

variable {L : Type} [Group L] [Finite L]

theorem isPGroup_two_aschbacherSolvableCore (hmult : KFacts.L34CenterThreePrimeTwo)
    [Group.IsPerfect L] (hq : IsQuasisimple (L ⧸ CFSG.pCore 2 L)) {K : Subgroup L} [K.Normal]
    (ψ : L ⧸ K ≃* projSL 3 (GaloisField 2 2)) :
    IsPGroup 2 (aschbacherSolvableCore 3 L) := by
  set O := CFSG.pCore 2 L with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) := isSimpleGroup_projSL
  have : IsSimpleGroup (L ⧸ K) := ψ.isSimpleGroup
  have hOK : O ≤ K := Census.pCore_le 2
  set χ : L ⧸ O →* projSL 3 (GaloisField 2 2) :=
    ψ.toMonoidHom.comp (QuotientGroup.map O K (MonoidHom.id L) hOK) with hχ
  have hχs : Function.Surjective χ := by
    intro y
    obtain ⟨q, rfl⟩ := ψ.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    exact ⟨(x : L ⧸ O), rfl⟩
  have hker : χ.ker = Subgroup.center (L ⧸ O) := by
    apply le_antisymm
    · rcases quasisimple_normal_subgroups hq (N := χ.ker) inferInstance with h | h
      · exfalso
        have : Nontrivial (projSL 3 (GaloisField 2 2)) := IsSimpleGroup.toNontrivial
        obtain ⟨y, hy⟩ := exists_ne (1 : projSL 3 (GaloisField 2 2))
        obtain ⟨x, rfl⟩ := hχs y
        exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))
      · exact h
    · intro z hz
      have h1 : χ z ∈ Subgroup.center (projSL 3 (GaloisField 2 2)) :=
        Subgroup.map_center_le_center hχs ⟨z, hz, rfl⟩
      rw [center_projSL_eq_bot] at h1
      exact h1
  set eX : (L ⧸ O) ⧸ Subgroup.center (L ⧸ O) ≃* projSL 3 (GaloisField 2 2) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective χ hχs) with heX
  obtain ⟨hθs, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  set Z := (aschbacherSolvableCore 3 L).map (QuotientGroup.mk' O) with hZ
  have hZn : Z.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  have hZc : Z ≤ Subgroup.center (L ⧸ O) := by
    rcases quasisimple_normal_subgroups hq (N := Z) hZn with h | h
    · exfalso
      have hs : Group.IsSolvable (L ⧸ O) := by
        refine Group.isSolvable_of_surjective
          (f := (QuotientGroup.mk' O).comp (aschbacherSolvableCore 3 L).subtype) ?_
        intro y
        have hy : y ∈ Z := h ▸ Subgroup.mem_top y
        obtain ⟨t, ht, rfl⟩ := hy
        exact ⟨⟨t, ht⟩, rfl⟩
      have : Nontrivial (L ⧸ O) := isQuasisimple_nontrivial hq
      have : Group.IsPerfect (L ⧸ O) := inferInstance
      exact Group.IsPerfect.not_isSolvable (L ⧸ O) hs
    · exact h
  have h3Z : ¬ 3 ∣ Nat.card Z := fun h3 => hθ3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hZ2 := hmult (L ⧸ O) hq ⟨eX⟩ Z hZc h3Z
  intro t
  obtain ⟨k, hk⟩ := hZ2 ⟨QuotientGroup.mk' O t, t, t.2, rfl⟩
  have h1 : ((t : L) ^ 2 ^ k) ∈ O := by
    have h2 : (QuotientGroup.mk' O (t : L)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 O) ⟨_, h1⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have h3 : ((t : L) ^ 2 ^ k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul]
  exact h3

end Theta

section Star

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G}

theorem card_map_eq_two_of_item4_34Sec (h434 : Item4_34Sec) (h : Ctx444 G A M)
    {L R : Subgroup G} (hL : L ∈ thetaComponents 3 G) (hLM : ¬ L ≤ M)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR3 : ¬ 3 ∣ Nat.card R)
    (hs : Group.IsSolvable (A ⊔ R : Subgroup G))
    (hact : ¬ R.map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    Nat.card ((R.subgroupOf (A ⊔ R ⊔ L)).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L)))) = 2 := by
  have hcore := ctx434Core_quotient h hL hLM hAL hRL hAR hR3 hs hact
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L))).ker := by
    rw [QuotientGroup.ker_mk']
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  obtain ⟨-, h2, -⟩ := h434 G h.sectionFourHyp (A ⊔ R ⊔ L) _ _
    (QuotientGroup.mk'_surjective _) hker _ _ _ hcore
  exact h2

theorem Ctx444.sylow_le_centralizer_of_odd (h434 : Item4_34Sec) (h45 : Item4_5)
    (h : Ctx444 G A M) {L Q : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hQ3 : ¬ 3 ∣ Nat.card Q) (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hLM : ¬ L ≤ M) (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2) (T : Sylow r Q)
    (hAT : A ≤ Subgroup.normalizer (((T : Subgroup Q).map Q.subtype : Subgroup G) : Set G)) :
    ((T : Subgroup Q).map Q.subtype).map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
  by_contra hact
  have hAL := h.le_normalizer_of_mem_thetaComponents h45 hL
  have hRQ : (T : Subgroup Q).map Q.subtype ≤ Q := Subgroup.map_subtype_le _
  have hR3 : ¬ 3 ∣ Nat.card ((T : Subgroup Q).map Q.subtype) := fun h3 =>
    hQ3 (h3.trans (Subgroup.card_dvd_of_le hRQ))
  have hRp : IsPGroup r ((T : Subgroup Q).map Q.subtype) := T.isPGroup'.map _
  have hs : Group.IsSolvable (A ⊔ (T : Subgroup Q).map Q.subtype : Subgroup G) :=
    isSolvable_sup_of_le_normalizer (isSolvable_of_isPGroup h.isE27.isPGroup)
      (isSolvable_of_isPGroup hRp) hAT
  have h2 := card_map_eq_two_of_item4_34Sec h434 h hL hLM hAL (hRQ.trans hQL) hAT hR3 hs hact
  set R := (T : Subgroup Q).map Q.subtype with hR
  have hRp' : IsPGroup r ((R.subgroupOf (A ⊔ R ⊔ L)).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(A ⊔ R ⊔ L)))) := by
    have : IsPGroup r (R.subgroupOf (A ⊔ R ⊔ L)) :=
      hRp.of_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_right.trans le_sup_left)).symm
    exact this.map _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp'
  rw [h2] at hk
  rcases k with _ | k
  · norm_num at hk
  · have hr : r ∣ 2 := hk ▸ dvd_pow_self r (Nat.succ_ne_zero k)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp hr)

omit [Finite G] in
theorem sup_sup_comm (A L S : Subgroup G) : A ⊔ L ⊔ S = A ⊔ S ⊔ L := sup_right_comm A L S

theorem inSubgroup_perfectResidual_eq {A R L : Subgroup G} [Group.IsPerfect L]
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hs : Group.IsSolvable (A ⊔ R : Subgroup G)) :
    inSubgroup perfectResidual (A ⊔ R ⊔ L) = L := by
  set H := A ⊔ R ⊔ L with hH
  have hLH : L ≤ H := le_sup_right
  have : (L.subgroupOf H).Normal := ⟨fun x hx h => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_of_sup_le hAL hRL h.2) _).mp hx⟩
  have hsol := isSolvable_quotient_subgroupOf hAL hRL hs
  obtain ⟨-, -, -, -, hiff, -⟩ := perfect_residual_characterization (G := H)
  have hle : perfectResidual H ≤ L.subgroupOf H := (hiff _).mp hsol
  have : Group.IsPerfect (L.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe hLH).symm.toMonoidHom) (MulEquiv.surjective _)
  have hge : L.subgroupOf H ≤ perfectResidual H :=
    (perfect_residual_transport (MonoidHom.id H)).2.2 _ inferInstance
  rw [inSubgroup, le_antisymm hle hge, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLH]

omit [Finite G] in
theorem mem_oTwoComponentsIn {L H : Subgroup G} (hL : L ∈ oTwoComponents G) (hLH : L ≤ H)
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) : L ∈ oTwoComponentsIn H := by
  set e := Subgroup.subgroupOfEquivOfLe hLH with he
  obtain ⟨hperf, -, hq⟩ := hL
  refine ⟨L.subgroupOf H, ⟨?_, ?_, ?_⟩, ?_⟩
  · have : Group.IsPerfect L := hperf
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · refine (⟨fun x hx h => ?_⟩ : (L.subgroupOf H).Normal).isSubnormal
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHL h.2) _).mp hx
  · exact isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (CFSG.pCore_map_iso 2 e.symm)) hq
  · change (L.subgroupOf H).map H.subtype = L
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hLH]

omit [Finite G] in
theorem mem_sup_of_not_three_dvd {S L : Subgroup G} (hA : IsPGroup 3 A)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ A ⊔ S ⊔ L) (hx3 : ¬ 3 ∣ orderOf x) : x ∈ S ⊔ L := by
  have hAN : A ≤ Subgroup.normalizer ((S ⊔ L : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hAS ha),
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hAL ha)]
  rw [sup_assoc] at hx
  exact mem_of_mem_sup_of_not_dvd hA hAN hx hx3

omit [Finite G] in
theorem inf_le_normalizer_inf {Q H : Subgroup G}
    (hQ : M ≤ Subgroup.normalizer (Q : Set G)) :
    H ⊓ M ≤ Subgroup.normalizer ((Q ⊓ H : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h1 := Subgroup.mem_normalizer_iff.mp (hQ hy.2) z
  have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy.1) z
  simp only [Subgroup.mem_inf]
  rw [h1, h2]

omit [Finite G] in
theorem le_normalizer_pCoreOf (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H : Subgroup G) : Set G) := by
  have := CFSG.LieType.BorelTits.pCore_characteristic (G := H) 2
  exact Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.Open.pCore 2 H))

theorem isPGroup_two_inf_of_quotient {Q L : Subgroup G} (hQ3 : ¬ 3 ∣ Nat.card Q)
    [(centralizerStar Q L).Normal] (hQC : IsPGroup 2 (Q ⧸ centralizerStar Q L))
    (hZ3 : Nat.card (Subgroup.center (L.map (starQuot G))) ∣ 3)
    (hLP2 : IsPGroup 2 (L ⊓ CFSG.pPrimeCore 3 G : Subgroup G)) :
    IsPGroup 2 (Q ⊓ L : Subgroup G) := by
  intro y
  obtain ⟨k, m, hm, hy⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  set z : G := (y : G) ^ 2 ^ k with hz
  have hzQ : z ∈ Q := Q.pow_mem y.2.1 _
  have hzL : z ∈ L := L.pow_mem y.2.2 _
  have hyo : orderOf (y : G) = 2 ^ k * m := by rw [Subgroup.orderOf_coe]; exact hy
  have hzo : orderOf z = m := by
    rw [hz, orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) ⟨m, hyo⟩, hyo]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos k)
  have hzC : (⟨z, hzQ⟩ : Q) ∈ centralizerStar Q L := by
    set w : Q ⧸ centralizerStar Q L := ((⟨z, hzQ⟩ : Q) : Q ⧸ centralizerStar Q L) with hw
    obtain ⟨j, hj⟩ := hQC w
    have h1 : orderOf w ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    have h2 : orderOf w ∣ m := by
      rw [← hzo, ← Subgroup.orderOf_mk z hzQ]
      exact orderOf_map_dvd (QuotientGroup.mk' (centralizerStar Q L)) _
    have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
    have hw1 : w = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    exact (QuotientGroup.eq_one_iff _).mp hw1
  have hzc : (⟨starQuot G z, Subgroup.mem_map_of_mem _ hzL⟩ : L.map (starQuot G)) ∈
      Subgroup.center (L.map (starQuot G)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC g g.2)
  have hz1 : starQuot G z = 1 := by
    set c : Subgroup.center (L.map (starQuot G)) := ⟨_, hzc⟩ with hc
    have h1 : orderOf c ∣ 3 := (orderOf_dvd_natCard c).trans hZ3
    have h2 : orderOf c ∣ m := by
      rw [← hzo, hc, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_map_dvd _ _
    have h3m : ¬ 3 ∣ m := fun h3 => hQ3 (h3.trans (by
      rw [← hzo, ← Subgroup.orderOf_mk z hzQ]
      exact orderOf_dvd_natCard _))
    have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3m
    have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    simpa [hc] using congrArg Subtype.val (congrArg Subtype.val hc1)
  have hzP : z ∈ L ⊓ CFSG.pPrimeCore 3 G := ⟨hzL, (QuotientGroup.eq_one_iff z).mp hz1⟩
  obtain ⟨j, hj⟩ := hLP2 ⟨z, hzP⟩
  have hzj : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hz1' : z = 1 := by
    have h1 : orderOf z ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hzj
    have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 (hzo ▸ dvd_rfl))
  exact ⟨k, Subtype.ext (by simpa [hz] using hz1')⟩

theorem le_inSubgroup_aschbacherSolvableCore_of_isPGroup_two {L N : Subgroup G} (hNL : N ≤ L)
    (hn : L ≤ Subgroup.normalizer (N : Set G)) (h2 : IsPGroup 2 N) :
    N ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  set N' := N.subgroupOf L with hN'
  have hN'n : N'.Normal := ⟨fun x hx l => by
    rw [hN', Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hn l.2) _).mp hx⟩
  have hN'2 : IsPGroup 2 N' := h2.of_equiv (Subgroup.subgroupOfEquivOfLe hNL).symm
  have hN's : Group.IsSolvable N' := isSolvable_of_isPGroup hN'2
  have hN'3 : ¬ 3 ∣ Nat.card N' := by
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN'2
    rw [hk] at h3
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)
  have hle := (solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three).2.2.2.1 N' hN'n hN's hN'3
  intro x hx
  exact ⟨⟨x, hNL hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem Ctx444.mem_scriptH₀_of_sylow (h434 : Item4_34Sec) (h45 : Item4_5)
    (hmult : KFacts.L34CenterThreePrimeTwo) (h : Ctx444 G A M) {L Q : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLC : L ∈ oTwoComponents G) (hLM : ¬ L ≤ M)
    (hQ3 : ¬ 3 ∣ Nat.card Q) (hQM : Q ≤ M) (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) (hcomm : ⁅L, Q⁆ = L)
    (hZ : IsZ3L34OrHeisSL34 ((A ⊔ L).map (starQuot G))) (S : Sylow 2 Q)
    (hAS : A ≤ Subgroup.normalizer (((S : Subgroup Q).map Q.subtype : Subgroup G) : Set G)) :
    A ⊔ L ⊔ (S : Subgroup Q).map Q.subtype ∈ Late.scriptH₀ A M := by
  set S' : Subgroup G := (S : Subgroup Q).map Q.subtype with hS'
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  have hAL := h.le_normalizer_of_mem_thetaComponents h45 hL
  have h3L := h.three_dvd_card_of_not_le h45 hL hLM
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := h.le.trans hMQ
  have hS'Q : S' ≤ Q := Subgroup.map_subtype_le _
  have hS'L : S' ≤ Subgroup.normalizer (L : Set G) := hS'Q.trans hQL
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  obtain ⟨-, hZ3⟩ := exists_mulEquiv_projSL_map_starQuot hA3 hL hAL hZ
  obtain ⟨K, _, -, -, ⟨ψ⟩⟩ := exists_solvable_quotient_projSL hA3 hL h3L hAL hZ
  have : Group.IsPerfect L := hL.1
  have hθ2 := isPGroup_two_aschbacherSolvableCore hmult hLC.2.2 ψ
  have hθL := inf_pPrimeCore_eq_of_mem_thetaComponents hL h3L
  have hLP2 : IsPGroup 2 (L ⊓ CFSG.pPrimeCore 3 G : Subgroup G) := by
    rw [hθL]
    exact hθ2.map _
  have hCn := centralizerStar_normal hQL
  have hQC : IsPGroup 2 (Q ⧸ centralizerStar Q L) :=
    isPGroup_two_quotient_centralizer hA3 hQ3 hAQ hQL
      (fun r _ hr2 T hAT => h.sylow_le_centralizer_of_odd h434 h45 hL hQ3 hQL hLM r hr2 T hAT)
  have hQL2 := isPGroup_two_inf_of_quotient hQ3 hQC hZ3 hLP2
  have hs : Group.IsSolvable (A ⊔ S' : Subgroup G) :=
    isSolvable_sup_of_le_normalizer (isSolvable_of_isPGroup hA3) (isSolvable_of_isPGroup hS'2) hAS
  rw [sup_sup_comm]
  set H := A ⊔ S' ⊔ L with hH
  have hres : inSubgroup perfectResidual H = L := inSubgroup_perfectResidual_eq hAL hS'L hs
  have hAH : A ≤ H := le_sup_left.trans le_sup_left
  have hS'H : S' ≤ H := le_sup_right.trans le_sup_left
  have hLH : L ≤ H := le_sup_right
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_sup_le hAL hS'L
  have hQH : Q ⊓ H ≤ S' ⊔ (Q ⊓ L) := by
    rintro x ⟨hxQ, hxH⟩
    have hx := mem_sup_of_not_three_dvd hA3 hAS hAL hxH (not_three_dvd_orderOf_of_mem hxQ hQ3)
    have hx' : x ∈ (S' : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S' L hS'L]
      exact hx
    obtain ⟨s, hs', l, hl, rfl⟩ := hx'
    have hlQ : l ∈ Q := by
      have : s⁻¹ * (s * l) ∈ Q := Q.mul_mem (Q.inv_mem (hS'Q hs')) hxQ
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem_sup hs' ⟨hlQ, hl⟩
  have hS'N : S' ≤ Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) := by
    intro s hs'
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hS'Q hs')) z,
      Subgroup.mem_normalizer_iff.mp (hS'L hs') z]
  have hQH2 : IsPGroup 2 (Q ⊓ H : Subgroup G) :=
    (IsPGroup.to_sup_of_normal_right' hS'2 hQL2 hS'N).to_le hQH
  have hO2 : S' ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) := by
    refine (le_inf hS'Q hS'H).trans ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf inf_le_right (inf_le_left.trans hQM)) (inf_le_normalizer_inf hMQ) hQH2
  have hO2le : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ H :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hSnt : ¬ S'.map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    intro hle
    have hSC : (S : Subgroup Q) ≤ centralizerStar Q L := fun s hs =>
      mem_centralizerStar.mpr (hle ⟨s, ⟨s, hs, rfl⟩, rfl⟩)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQC
    have h2 := not_dvd_index_of_sylow_le hSC
    have hidx : (centralizerStar Q L).index = 2 ^ k := hk
    have hk0 : k = 0 := by
      rcases k with _ | k
      · rfl
      · exact absurd (hidx ▸ dvd_pow_self 2 (Nat.succ_ne_zero k)) h2
    have htop : centralizerStar Q L = ⊤ :=
      Subgroup.index_eq_one.mp (by rw [hidx, hk0, pow_zero])
    refine not_map_le_centralizer_of_commutator_eq hL h3L hcomm ?_
    rintro _ ⟨q, hq, rfl⟩
    exact mem_centralizerStar.mp (htop ▸ Subgroup.mem_top (⟨q, hq⟩ : Q))
  rw [Late.mem_scriptH₀_iff, hres]
  refine ⟨?_, mem_oTwoComponentsIn hLC hLH hHL, ?_⟩
  ·
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_right.trans le_sup_left) (hO2.trans le_sup_right))
        (le_sup_left.trans le_sup_left)
    · exact sup_le (sup_le hLH hAH) hO2le
  ·
    intro heq
    have hS'O : S' ≤ CFSG.Open.pCoreOf 2 H := heq ▸ hO2
    apply hSnt
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have hcO : s * l * s⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
      have h1 : l * s⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf H (hLH hl)) _).mp
          (inv_mem (hS'O hs))
      have h2 := mul_mem (hS'O hs) h1
      simpa [mul_assoc] using h2
    have hcL : s * l * s⁻¹ * l⁻¹ ∈ L :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hS'L hs) l).mp hl) (inv_mem hl)
    have hn : L ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H ⊓ L : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_inf]
      rw [Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf H (hLH hx)) z,
        Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) z]
    have hcθ : s * l * s⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
      le_inSubgroup_aschbacherSolvableCore_of_isPGroup_two inf_le_right hn
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left) ⟨hcO, hcL⟩
    rw [← hθL] at hcθ
    have h1 : starQuot G (s * l * s⁻¹ * l⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hcθ.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm


theorem rank3II_4_53_of (h434 : Item4_34Sec) (h45 : Item4_5) (h452 : Item4_52)
    (hmult : KFacts.L34CenterThreePrimeTwo) : Item4_53 := by
  intro G _ _ A M h hne L hL hQL hcomm hLM S hAS
  exact h.mem_scriptH₀_of_sylow h434 h45 hmult hL (h452 G A M h (Or.inl hne) L hL hQL hcomm hLM)
    hLM (not_three_dvd_card_inSubgroup_pPrimeCore M) (Subgroup.map_subtype_le _)
    (le_normalizer_inSubgroup_pPrimeCore M) hQL hcomm
    (h.isZ3L34OrHeisSL34_map_starQuot h434 h45 hL hQL hcomm hLM) S hAS

end Star

end CFSG.RankThree.PartTwo.Sec4
