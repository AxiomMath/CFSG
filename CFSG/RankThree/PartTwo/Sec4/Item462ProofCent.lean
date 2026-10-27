module

public import CFSG.RankThree.PartTwo.Sec4.Item462ProofUL
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.KFacts.KS10L27
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.Milestones.LC_GL_local_rank_bounds
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_thetaQuotCentralizer_of_le_sup {B U L Y : Subgroup G}
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hUB : U ≤ Subgroup.centralizer (B : Set G)) (hY : Y ≤ U ⊔ thetaQuotCentralizer L) :
    ⁅Y, B⁆ ≤ thetaQuotCentralizer L := by
  have hUB' : ⁅U, B⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUB
  have h := Sec6.commutator_sup_le_of_le_normalizer
    (hUL.trans (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L))
    (hBL.trans (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L)) (Y := U) (Z := B)
  rw [hUB', bot_sup_eq] at h
  exact (Subgroup.commutator_mono hY le_rfl).trans h

theorem commutator_le_theta_of_le_sup_zpowers {B Q L : Subgroup G} {a : G}
    (haZ : a ∈ Subgroup.center G) (hB3 : IsPGroup 3 B) (hQ2 : IsPGroup 2 Q)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G))
    (hQC : ⁅Q, B⁆ ≤ thetaQuotCentralizer L) (hBLa : B ≤ L ⊔ Subgroup.zpowers a) :
    ⁅Q, B⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZ)
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    intro h
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk] at h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  rw [← RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three B Q
    hB3 hQ3 hBQ, Subgroup.commutator_le]
  intro q hq x hx
  obtain ⟨l, hl, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hBLa hx)
  rw [commutatorElement_mul_of_commute q l w
    (Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr haZ) hw) q)]
  have hqC := hQC hq
  have hqN : q ∈ Subgroup.normalizer (L : Set G) := Sec6.thetaQuotCentralizer_le_normalizer L hqC
  have h1 : ⁅l, q⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    ((Sec6.commutator_le_theta_iff (X := Subgroup.zpowers q)
      (Subgroup.zpowers_le.mpr hqN)).mpr (Subgroup.zpowers_le.mpr hqC))
      (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers q))
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ h1

theorem isElemAbelian_map' {X Y : Type*} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian p E) :
    CFSG.Assembly.IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem exists_isElemAbelian_card_of_l27 {X : Type*} [Group X]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 3 3)) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  set P := GorensteinWalter.psl2UpperUnipotentSubgroup (GaloisField 3 3) with hP
  have hPc : Nat.card P = 27 := by
    rw [hP, GorensteinWalter.psl2UpperUnipotentSubgroup_card, hK]
    norm_num
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hPc]; norm_num)
  have hPe := (KFacts.isElemAbelian_of_isPGroup_three_psl2 hK hPp).1
  set f : GorensteinWalter.PSL2 (GaloisField 3 3) ≃* X :=
    (e.trans (projSLEquivPSL (GaloisField 3 3))).symm with hf
  refine ⟨P.map f.toMonoidHom, isElemAbelian_map' _ hPe, ?_⟩
  rw [Subgroup.card_map_of_injective f.injective, hPc]

theorem isElemAbelian_sup_of_commute {X : Type*} [Group X] {E E' : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE' : CFSG.Assembly.IsElemAbelian 3 E')
    (hc : ∀ x ∈ E, ∀ y ∈ E', x * y = y * x) : CFSG.Assembly.IsElemAbelian 3 (E ⊔ E') := by
  have hN : E ≤ Subgroup.normalizer (E' : Set X) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hc x hx y hy).symm)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right E E' hN
  have hmem : ∀ x ∈ E ⊔ E', ∃ u ∈ E, ∃ v ∈ E', u * v = x := fun x hx => by
    have hx' : x ∈ (E : Set X) * (E' : Set X) := by
      rw [← hset]
      exact hx
    obtain ⟨u, hu, v, hv, huv⟩ := hx'
    exact ⟨u, hu, v, hv, huv⟩
  have hcomm : ∀ x ∈ E ⊔ E', ∀ y ∈ E ⊔ E', x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := hmem x hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hmem y hy
    have h1 : u * u' = u' * u := congrArg Subtype.val (hE.1.1.comm ⟨u, hu⟩ ⟨u', hu'⟩)
    have h2 : v * v' = v' * v := congrArg Subtype.val (hE'.1.1.comm ⟨v, hv⟩ ⟨v', hv'⟩)
    calc u * v * (u' * v') = u * (v * u') * v' := by group
      _ = u * (u' * v) * v' := by rw [hc u' hu' v hv]
      _ = (u * u') * (v * v') := by group
      _ = (u' * u) * (v' * v) := by rw [h1, h2]
      _ = u' * (u * v') * v := by group
      _ = u' * (v' * u) * v := by rw [hc u hu v' hv']
      _ = u' * v' * (u * v) := by group
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := hmem x hx
  rw [Commute.mul_pow (hc u hu v hv) 3, hE.2 u hu, hE'.2 v hv, mul_one]

theorem false_of_isElemAbelian_le_normalizer (hS4 : SectionFourHyp G)
    {P F : Subgroup (G ⧸ aschbacherSolvableCore 3 G)} (hP1 : P ≠ ⊥) (hP2 : IsPGroup 2 P)
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hFc : Nat.card F = 3 ^ 4)
    (hFN : F ≤ Subgroup.normalizer (P : Set (G ⧸ aschbacherSolvableCore 3 G))) : False := by
  have hrankX : CFSG.Assembly.RankThreeEven.localRank 3 (G ⧸ aschbacherSolvableCore 3 G) ≤ 3 :=
    (theta_quotient_core_and_ranks (G := G)).2.2.1.2.1.trans
      ((((CFSG.Milestones.lc_gl_local_rank_bounds G).1 3 Nat.prime_three (by norm_num)).2).trans
        hS4.evenRank_le)
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 (G ⧸ aschbacherSolvableCore 3 G) := by
    have h1 : 4 ≤ CFSG.Open.pRank 3
        (Subgroup.normalizer (P : Set (G ⧸ aschbacherSolvableCore 3 G))) := by
      refine le_csSup ⟨Nat.card (G ⧸ aschbacherSolvableCore 3 G), ?_⟩ ⟨F, hFN, hFe, hFc⟩
      rintro _ ⟨Z, -, -, hZ⟩
      calc _ ≤ 3 ^ _ := (Nat.lt_pow_self (by norm_num)).le
        _ = Nat.card Z := hZ.symm
        _ ≤ Nat.card (G ⧸ aschbacherSolvableCore 3 G) := Subgroup.card_le_card_group Z
    refine h1.trans (le_csSup ⟨Nat.card (G ⧸ aschbacherSolvableCore 3 G), ?_⟩
      ⟨_, ⟨_, hP1, hP2, rfl⟩, rfl⟩)
    rintro _ ⟨Z, -, rfl⟩
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card 3 Nat.prime_three Z).trans
      (Subgroup.card_le_card_group Z)
  omega

theorem le_theta_of_le_thetaQuotCentralizer_of_l27 (hS4 : SectionFourHyp G)
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 3 3))
    {a : G} (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3) {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hQC : Q ≤ thetaQuotCentralizer L) :
    Q ≤ aschbacherSolvableCore 3 G := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hQθ
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  obtain ⟨hNs, -, hNp, -⟩ :=
    solvable_prime_complement_core_characterization (H := G) Nat.prime_three
  obtain ⟨-, -, ⟨η, -⟩, -, -, -, -, -, -, -, -⟩ :=
    theta_component_quotient_structure Nat.prime_three hL
  have hQ1 : Q.map ρ ≠ ⊥ := by
    intro h
    apply hQθ
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  have hQ2' : IsPGroup 2 (Q.map ρ) := hQ2.map ρ
  have hQK : Q.map ρ ≤ Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rintro _ ⟨q, hq, rfl⟩
    exact (mem_thetaQuotCentralizer_iff_mk hL q).mp (hQC hq)
  have hKN : L.map ρ ≤ Subgroup.normalizer ((Q.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    (Subgroup.le_centralizer_iff.mp hQK).trans (Subgroup.centralizer_le_normalizer _)
  have hZK : Subgroup.center (L.map ρ) = ⊥ := by
    have h := Subgroup.map_center_eq η
    rw [(center_eq_bot_and_isCyclic_of_l27 e).1, Subgroup.map_bot] at h
    exact h.symm
  obtain ⟨E₀, hE₀, hE₀c⟩ := exists_isElemAbelian_card_of_l27 (η.symm.trans e)
  set E := E₀.map (L.map ρ).subtype with hE
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := isElemAbelian_map' _ hE₀
  have hEc : Nat.card E = 27 := by
    rw [hE, Subgroup.card_map_of_injective (L.map ρ).subtype_injective, hE₀c]
  have hEK : E ≤ L.map ρ := Subgroup.map_subtype_le _
  have haZX : ρ a ∈ Subgroup.center (G ⧸ N) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N) (Subgroup.mem_map_of_mem ρ haZ)
  have hap : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha3, pow_one])
  have ha1 : ρ a ≠ 1 := by
    intro h
    have ha1 : a ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ha3
      norm_num at ha3
    exact ha1 (injOn_mk_of_isPGroup Nat.prime_three hap (Subgroup.mem_zpowers a)
      (Subgroup.one_mem _) (by rw [h, map_one]))
  have ha3' : a ^ 3 = 1 := by
    rw [← ha3]
    exact pow_orderOf_eq_one a
  have hρa3 : ρ a ^ 3 = 1 := by rw [← map_pow, ha3', map_one]
  have ha3X : orderOf (ρ a) = 3 := orderOf_eq_prime hρa3 ha1
  have haE : ρ a ∉ E := by
    intro h
    have hmem : (⟨ρ a, hEK h⟩ : L.map ρ) ∈ Subgroup.center (L.map ρ) :=
      Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp haZX k)
    rw [hZK, Subgroup.mem_bot] at hmem
    exact ha1 (congrArg Subtype.val hmem)
  have hZe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers (ρ a)) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
      change (x : G ⧸ N) * y = y * x
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self (ρ a) i j).eq
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρa3, one_zpow]
  have hFe := isElemAbelian_sup_of_commute hEe hZe fun x _ y hy =>
    (Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr haZX) hy) x)
  have hFc : Nat.card (E ⊔ Subgroup.zpowers (ρ a) : Subgroup (G ⧸ N)) = 3 ^ 4 := by
    rw [card_sup_zpowers_of_not_mem haZX ha3X haE, hEc]
    norm_num
  have hFN : E ⊔ Subgroup.zpowers (ρ a) ≤
      Subgroup.normalizer ((Q.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    sup_le (hEK.trans hKN) ((Subgroup.zpowers_le.mpr haZX).trans
      ((Subgroup.center_le_centralizer _).trans (Subgroup.centralizer_le_normalizer _)))
  exact false_of_isElemAbelian_le_normalizer hS4 hQ1 hQ2' hFe hFc hFN

omit [Finite G] in
theorem le_normalizer_inSubgroup_pCore (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((inSubgroup (CFSG.pCore 2) H : Subgroup G) : Set G) := by
  have hle : inSubgroup (CFSG.pCore 2) H ≤ H := Subgroup.map_subtype_le _
  have hn : ((inSubgroup (CFSG.pCore 2) H).subgroupOf H).Normal := by
    rw [show (inSubgroup (CFSG.pCore 2) H).subgroupOf H = CFSG.pCore 2 H from
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
    exact CFSG.pCore_normal
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hn

theorem commutator_le_theta_of_le_sup
    (hS4 : SectionFourHyp G) {A B U L : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {a : G}
    (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3) (hBA : B ≤ A)
    (hUB : U ≤ Subgroup.centralizer (B : Set G)) (hL : L ∈ thetaComponents 3 G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hUL : U ≤ L)
    (hCA : ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a)
    (hlist : (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12)) ∨
      (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
          CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 3 3)) ∧
        ∃ e ∈ B, InducesOuterTheta e L))
    (hY : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ≤
      U ⊔ thetaQuotCentralizer L) :
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)), B⁆ ≤
      aschbacherSolvableCore 3 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  set Y := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hYdef
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans hAL
  have hUN : U ≤ Subgroup.normalizer (L : Set G) := hUL.trans Subgroup.le_normalizer
  have hQC : ⁅Y, B⁆ ≤ thetaQuotCentralizer L :=
    commutator_le_thetaQuotCentralizer_of_le_sup hBL hUN hUB hY
  have hY2 : IsPGroup 2 Y := CFSG.pCore_isPGroup.map _
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.le_centralizer_iff.mp hUB).trans (le_normalizer_inSubgroup_pCore _)
  have hQ2 : IsPGroup 2 (⁅Y, B⁆ : Subgroup G) :=
    hY2.to_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hBY)
  have hB3 : IsPGroup 3 B :=
    (fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x (hBA x.2))⟩ : IsPGroup 3 B)
  have hθL : inSubgroup (aschbacherSolvableCore 3) L ≤ aschbacherSolvableCore 3 G := by
    rw [(theta_component_quotient_structure Nat.prime_three hL).1]
    exact inf_le_right
  rcases hlist with (he | he) | ⟨he, -⟩
  · obtain ⟨e⟩ := he
    have hBLa : B ≤ L ⊔ Subgroup.zpowers a := fun x hx =>
      mem_sup_zpowers_of_not_inducesOuterTheta hmax hL hAL hCA (center_eq_bot_of_j2 e) (hBA hx)
        (not_inducesOuterTheta_of_j2 e (hAe.2 x (hBA hx)))
    exact (commutator_le_theta_of_le_sup_zpowers haZ hB3 hY2 hBY hQC hBLa).trans hθL
  · obtain ⟨e⟩ := he
    obtain ⟨hZ, hinn⟩ := not_inducesOuterTheta_of_m12 (G := G) e
    have hBLa : B ≤ L ⊔ Subgroup.zpowers a := fun x hx =>
      mem_sup_zpowers_of_not_inducesOuterTheta hmax hL hAL hCA hZ (hBA hx)
        (hinn x (hAe.2 x (hBA hx)))
    exact (commutator_le_theta_of_le_sup_zpowers haZ hB3 hY2 hBY hQC hBLa).trans hθL
  · obtain ⟨e⟩ := he
    exact le_theta_of_le_thetaQuotCentralizer_of_l27 hS4 hL e haZ ha3 hQ2 hQC

end CFSG.RankThree.PartTwo.Sec4.Item462Proof
