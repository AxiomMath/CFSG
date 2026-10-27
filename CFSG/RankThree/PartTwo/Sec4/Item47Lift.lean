module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo
public import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.Asc83Table.E9

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_two_le_normalizer {N Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) (hN3 : ¬ 3 ∣ Nat.card N) :
    ∃ P : Sylow 2 N, Q ≤ Subgroup.normalizer
      (((P : Subgroup N).map N.subtype : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q' : Subgroup (Subgroup.normalizer (N : Set G)) :=
    Q.subgroupOf (Subgroup.normalizer (N : Set G))
  have hQ' : IsPGroup 3 Q' := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  have hcard : ¬ 3 ∣ Nat.card (Sylow 2 N) := by
    obtain ⟨P₀⟩ : Nonempty (Sylow 2 N) := inferInstance
    intro h
    apply hN3
    exact h.trans ((Sylow.card_dvd_index P₀).trans (Subgroup.index_dvd_card _))
  obtain ⟨P, hP⟩ := hQ'.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 N) hcard
  refine ⟨P, fun q hq => ?_⟩
  have key : ∀ g : Q', ∀ y ∈ (P : Subgroup N).map N.subtype,
      ((g : Subgroup.normalizer (N : Set G)) : G) * y *
          ((g : Subgroup.normalizer (N : Set G)) : G)⁻¹ ∈ (P : Subgroup N).map N.subtype := by
    rintro g _ ⟨n, hn, rfl⟩
    have hgP : g • P = P := hP g
    have hmem : (g : Subgroup.normalizer (N : Set G)) • n ∈
        ((g • P : Sylow 2 N) : Subgroup N) := by
      rw [show (g • P : Sylow 2 N) = (g : Subgroup.normalizer (N : Set G)) • P from rfl,
        Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul n _ _ hn
    rw [hgP] at hmem
    exact ⟨_, hmem, Subgroup.smul_coe N _ n⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key ⟨⟨q, hQN hq⟩, hq⟩ y, fun hy => ?_⟩
  simpa [mul_assoc] using key ⟨⟨q, hQN hq⟩, hq⟩⁻¹ _ hy

end Sylow

section Witness

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def thetaPreimage (L : Subgroup G)
    (U : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Subgroup G :=
  (U.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).map L.subtype

theorem mem_thetaPreimage {U : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} {g : G} :
    g ∈ thetaPreimage L U ↔
      ∃ hg : g ∈ L, QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨g, hg⟩ ∈ U := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hg, hU⟩
    exact ⟨⟨g, hg⟩, hU, rfl⟩

theorem thetaPreimage_le (U : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :
    thetaPreimage L U ≤ L := by
  rintro _ ⟨l, -, rfl⟩
  exact l.2

theorem card_comap_mk' {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (U : Subgroup (X ⧸ N)) :
    Nat.card (U.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card U := by
  have h1 := Subgroup.card_mul_index (U.comap (QuotientGroup.mk' N))
  rw [Subgroup.index_comap_of_surjective U (QuotientGroup.mk'_surjective N)] at h1
  have h2 := Subgroup.card_mul_index U
  have h3 := Subgroup.card_mul_index N
  have hU0 : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hU0)
  rw [h1, ← h3, Subgroup.index_eq_card, ← h2]
  ring

theorem card_thetaPreimage [Finite G] (U : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :
    Nat.card (thetaPreimage L U) =
      Nat.card (aschbacherSolvableCore 3 L) * Nat.card U := by
  rw [thetaPreimage, Subgroup.card_map_of_injective L.subtype_injective, card_comap_mk']

end Witness

section Exclusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_local_witness (hG : SectionFourHyp G) {c a : G}
    (hcL : ∀ y ∈ L, c * y = y * c) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hca : c * a = a * c) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (ha3 : a ^ 3 = 1)
    (hout : ¬ IsInnerAut (thetaQuotMulAut L (compAction L ⟨a, ha⟩)))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    {y₁ y₂ : L ⧸ aschbacherSolvableCore 3 L}
    (hy₁ : y₁ ∈ Sec8.barCentralizer (Subgroup.zpowers a) L)
    (hy₂ : y₂ ∈ Sec8.barCentralizer (Subgroup.zpowers a) L) (hy₁3 : y₁ ^ 3 = 1)
    (hy₂3 : y₂ ^ 3 = 1) (hy : y₁ * y₂ = y₂ * y₁) (hy₁1 : y₁ ≠ 1)
    (hy₂₁ : y₂ ∉ Subgroup.zpowers y₁)
    {U : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hUy₁ : ∀ u ∈ U, y₁ * u * y₁⁻¹ ∈ U) (hUy₂ : ∀ u ∈ U, y₂ * u * y₂⁻¹ ∈ U)
    (hUa : ∀ u ∈ U, thetaQuotMulAut L (compAction L ⟨a, ha⟩) u ∈ U) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ebar := Subgroup.closure ({y₁, y₂} : Set (L ⧸ aschbacherSolvableCore 3 L)) with hEbar
  have hEbar9 : Nat.card Ebar = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hy₁3 hy₂3 hy hy₁1 hy₂₁
  have hEbar3 : IsPGroup 3 Ebar := IsPGroup.of_card (n := 2) (by rw [hEbar9]; norm_num)
  have hEbarle : Ebar ≤ Sec8.barCentralizer (Subgroup.zpowers a) L := by
    rw [hEbar, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hy₁
    · exact hy₂
  obtain ⟨E, hEL, hEa, -, himE, hcardE, hinj⟩ :=
    exists_lift_of_le_barCentralizer ha ⟨1, by rw [pow_one]; exact ha3⟩ hEbar3 hEbarle
  have hE9 : Nat.card E = 9 := hcardE.trans hEbar9
  have hqE : ∀ e : L, (e : G) ∈ E →
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) e ∈ Ebar := fun e he => by
    rw [← himE]
    exact ⟨e, he, rfl⟩
  have hE3' : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    have heL := hEL he
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩ ^ 3 = 1 :=
      pow_three_eq_one_of_mem_closure_pair hy hy₁3 hy₂3 (hqE ⟨e, heL⟩ he)
    have h2 : (⟨e, heL⟩ : L) ^ 3 = 1 :=
      hinj _ (by simpa using E.pow_mem he 3) (by rw [map_pow, h1])
    simpa using congrArg Subtype.val h2
  have hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
    intro e he e' he'
    have heL := hEL he
    have he'L := hEL he'
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩ *
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e', he'L⟩ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e', he'L⟩ *
          QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩ :=
      commute_of_mem_closure_pair hy hy₁3 hy₂3 (hqE _ he) (hqE _ he')
    have h2 : (⟨e, heL⟩ : L) * ⟨e', he'L⟩ * (⟨e', he'L⟩ * ⟨e, heL⟩)⁻¹ = 1 := by
      refine hinj _ ?_ ?_
      · show e * e' * (e' * e)⁻¹ ∈ E
        exact E.mul_mem (E.mul_mem he he') (E.inv_mem (E.mul_mem he' he))
      · rw [map_mul, map_inv, map_mul, map_mul, h1, mul_inv_cancel]
    exact congrArg Subtype.val (mul_inv_eq_one.mp h2)
  have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
    ⟨⟨⟨fun x y => Subtype.ext (hEcomm x x.2 y y.2)⟩⟩, hE3'⟩
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcL y hy).symm)
  have hcE : c ∉ E := by
    intro hc
    have hcLm := hEL hc
    have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcLm⟩ ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) z
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (hcL l l.2).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hc1 (congrArg Subtype.val (hinj ⟨c, hcLm⟩ hc hcen))
  have hcEc : ∀ x ∈ E, x * c = c * x := fun x hx => (hcL x (hEL hx)).symm
  set E₁ := E ⊔ Subgroup.zpowers c with hE₁
  have hE₁e : CFSG.Assembly.IsElemAbelian 3 E₁ := isElemAbelian_sup_zpowers hEe hc3 hcEc
  have hE₁27 : Nat.card E₁ = 27 := by
    rw [hE₁, card_sup_zpowers_of_not_mem hc3 hcEc hcE, hE9]
  have haE : ∀ x ∈ E, x * a = a * x := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hEa hx))
  have haC : ∀ x ∈ Subgroup.zpowers c, x * a = a * x := by
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (show Commute c a from hca) k).eq
  have haE₁ : ∀ x ∈ E₁, x * a = a * x := commute_sup_of_commute haE haC
  have haE₁' : a ∉ E₁ := by
    intro h
    have hEN : Subgroup.zpowers c ≤ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun x hx => hcEc x hx)
    have h' : a ∈ ((E ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := h
    rw [Subgroup.coe_mul_of_right_le_normalizer_left E _ hEN] at h'
    obtain ⟨e, he, w, hw, hew⟩ := h'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    apply hout
    have heL := hEL he
    have heN : e ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer heL
    have hckN : c ^ k ∈ Subgroup.normalizer (L : Set G) := zpow_mem hcN k
    have h1 : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) = ⟨e, heN⟩ * ⟨c ^ k, hckN⟩ :=
      Subtype.ext hew.symm
    rw [h1, map_mul, map_mul, thetaQuotMulAut_compAction_of_mem heL heN,
      thetaQuotMulAut_compAction_eq_one hckN fun y hy => ((Commute.zpow_left
        (show Commute c y from hcL y hy) k)).eq, mul_one]
    exact ⟨_, rfl⟩
  set A₀ := E₁ ⊔ Subgroup.zpowers a with hA₀
  have hA₀e : CFSG.Assembly.IsElemAbelian 3 A₀ := isElemAbelian_sup_zpowers hE₁e ha3 haE₁
  have hA₀81 : Nat.card A₀ = 81 := by
    rw [hA₀, card_sup_zpowers_of_not_mem ha3 haE₁ haE₁', hE₁27]
  set H := thetaPreimage L U with hH
  have hEbarN : Ebar ≤ Subgroup.normalizer (U : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
    rw [hEbar, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact mem_normalizer_of_conj_mem hUy₁
    · exact mem_normalizer_of_conj_mem hUy₂
  have hNH : ∀ x : G, ∀ hx : x ∈ Subgroup.normalizer (L : Set G),
      (∀ u ∈ U, thetaQuotMulAut L (compAction L ⟨x, hx⟩) u ∈ U) →
        x ∈ Subgroup.normalizer (H : Set G) := by
    intro x hx hxU
    apply mem_normalizer_of_conj_mem
    intro h hhH
    obtain ⟨hhL, hhU⟩ := mem_thetaPreimage.mp hhH
    have hxh : x * h * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hx h).mp hhL
    refine mem_thetaPreimage.mpr ⟨hxh, ?_⟩
    have h1 := hxU _ hhU
    rw [show (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨h, hhL⟩ :
        L ⧸ aschbacherSolvableCore 3 L) = ((⟨h, hhL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)
        from rfl, thetaQuotMulAut_mk] at h1
    exact h1
  have hA₀H : A₀ ≤ Subgroup.normalizer (H : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro e he
      have heL := hEL he
      refine hNH e (Subgroup.le_normalizer heL) fun u hu => ?_
      rw [thetaQuotMulAut_compAction_of_mem heL, MulAut.conj_apply]
      exact (Subgroup.mem_normalizer_iff.mp (hEbarN (hqE ⟨e, heL⟩ he)) u).mp hu
    · rw [Subgroup.zpowers_le]
      refine hNH c hcN fun u hu => ?_
      rw [thetaQuotMulAut_compAction_eq_one hcN hcL, MulAut.one_apply]
      exact hu
    · rw [Subgroup.zpowers_le]
      exact hNH a ha hUa
  have hcardH : Nat.card H = Nat.card (aschbacherSolvableCore 3 L) * Nat.card U :=
    card_thetaPreimage U
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hU2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hU1 (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
  have hH3 : ¬ 3 ∣ Nat.card H := by
    rw [hcardH, hk]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact not_three_dvd_card_aschbacherSolvableCore L h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      norm_num at this
  have hH2 : 2 ∣ Nat.card H := by
    rw [hcardH, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hA₀3 : IsPGroup 3 A₀ := IsPGroup.of_card (n := 4) (by rw [hA₀81]; norm_num)
  obtain ⟨P, hP⟩ := exists_sylow_two_le_normalizer hA₀3 hA₀H hH3
  set S : Subgroup G := (P : Subgroup H).map H.subtype with hS
  have hS2 : IsPGroup 2 S := P.isPGroup'.map H.subtype
  have hS1 : S ≠ ⊥ := by
    intro h0
    have hcardS : Nat.card S = 2 ^ (Nat.card H).factorization 2 := by
      rw [hS, Subgroup.card_map_of_injective H.subtype_injective, P.card_eq_multiplicity]
    rw [h0, Subgroup.card_bot] at hcardS
    have hpos : 0 < (Nat.card H).factorization 2 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two
        (Nat.pos_iff_ne_zero.mp Nat.card_pos) hH2)
    have : 1 < 2 ^ (Nat.card H).factorization 2 := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hpos)
    omega
  exact false_of_le_normalizer hG hS1 hS2 hA₀e hA₀81 hP

end Exclusion

end CFSG.RankThree.PartTwo.Sec4
