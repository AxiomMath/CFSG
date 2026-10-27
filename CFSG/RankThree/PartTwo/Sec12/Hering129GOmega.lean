module

public import CFSG.RankThree.PartTwo.Sec12.Hering129GStar
public import CFSG.RankThree.PartTwo.Sec12.Hering129GJ2
public import CFSG.RankThree.PartTwo.Sec12.Hering129GHJ
import CFSG.RankThree.PartTwo.KFacts.KS12ClassExp
import CFSG.RankThree.PartTwo.Sec12.KS128BCensus
import CFSG.RankThree.PartTwo.Sec12.Item127
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.KFacts.KS12Moves
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129G

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem theta_le_pCore_two_of_j2 {Y : Type} [Group Y] [Finite Y]
    (e : Y ⧸ CFSG.pCore 2 Y ≃* NativeSporadic.J2) :
    aschbacherSolvableCore 3 Y ≤ CFSG.pCore 2 Y := by
  set θ := aschbacherSolvableCore 3 Y with hθ
  set Q := CFSG.pCore 2 Y with hQ
  obtain ⟨hθsol, hθn, -⟩ := solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  haveI : θ.Characteristic := hθn
  haveI : θ.Normal := inferInstance
  have hsimp : IsSimpleGroup (Y ⧸ Q) :=
    (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  let π := QuotientGroup.mk' Q
  haveI hnorm : (θ.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Q)
  rcases hsimp.eq_bot_or_eq_top_of_normal (θ.map π) with h | h
  · intro y hy
    have : π y ∈ θ.map π := ⟨y, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff y).mp this
  · exfalso
    haveI : Group.IsSolvable θ := hθsol
    haveI hsolv : Group.IsSolvable (Y ⧸ Q) := by
      refine Group.isSolvable_of_surjective (f := π.comp θ.subtype) ?_
      intro z
      have hz : z ∈ θ.map π := h ▸ Subgroup.mem_top z
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨⟨y, hy⟩, rfl⟩
    have hcardX : Nat.card (Y ⧸ Q) = 604800 := by
      rw [Nat.card_congr e.toEquiv]
      exact KFacts.KS14.card_nativeJ2
    haveI hperf : Group.IsPerfect (Y ⧸ Q) :=
      (Sec13.isPerfect_center_of_isSimpleGroup hsimp (by rw [hcardX]; norm_num)).1
    haveI : Nontrivial (Y ⧸ Q) := hsimp.toNontrivial
    exact Group.IsPerfect.not_isSolvable (Y ⧸ Q) hsolv


theorem injOn_mk_pCore_two {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y} (hS : IsPGroup 3 S) :
    Set.InjOn (QuotientGroup.mk' (CFSG.pCore 2 Y)) (S : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx y hy hxy
  have h : x⁻¹ * y ∈ CFSG.pCore 2 Y := QuotientGroup.eq.mp hxy
  have hS' : x⁻¹ * y ∈ S := S.mul_mem (S.inv_mem hx) hy
  have hcop : Nat.Coprime (Nat.card S) (Nat.card (CFSG.pCore 2 Y)) := by
    obtain ⟨m, hm⟩ := hS.exists_card_eq
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
    rw [hm, hn]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have hdisj := Subgroup.disjoint_of_coprime_natCard hcop
  have h1 : x⁻¹ * y ∈ S ⊓ CFSG.pCore 2 Y := ⟨hS', h⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem exists_sylow_three {A L K S : Subgroup G} {c b a : G} (cfg : Cfg129 G A c L b a K S)
    (hHJ : HJType129 L K) :
    ∃ Q : Subgroup G, Q ≤ K ∧ IsPGroup 3 Q ∧ Nat.card Q = 27 ∧ A ⊓ L ≤ Q ∧
      Q ≤ Subgroup.centralizer ({c} : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, -⟩ := cfg.point_facts
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hbB : b ∈ Sec4.thetaQuotCentralizer L := cfg.hb.2
  set I := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hIdef
  have hIL : I ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hALI : A ⊓ L ≤ I := BCensus.inf_le_residual hstd hbA hbB
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hstd.mem_thetaComponentsAt
  have hLeq := Proof128.eq_residual_sup_theta hLq.1 (k := 1) (by simpa using hAe.2 b hbA) hbB
  obtain ⟨eJ⟩ := Sec13.nonempty_quotTheta_equiv_of_eq_sup hIL hLeq
  obtain ⟨m, hm3, hLcard⟩ := KFacts.exists_card_eq_of_isTripleCover (Or.inl hHJ.1)
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := ↥I)
    Nat.prime_three
  have hIcard : Nat.card I = 27 * m * Nat.card (aschbacherSolvableCore 3 ↥I) := by
    rw [← hLcard, ← Nat.card_congr eJ.toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥I)
  have hfact : (Nat.card I).factorization 3 = 3 := by
    have hk : ¬ 3 ∣ m * Nat.card (aschbacherSolvableCore 3 ↥I) := fun h =>
      (Nat.Prime.dvd_mul Nat.prime_three).mp h |>.elim hm3 hθ3
    rw [hIcard, show 27 * m * Nat.card (aschbacherSolvableCore 3 ↥I) =
      3 * (9 * (m * Nat.card (aschbacherSolvableCore 3 ↥I))) by ring]
    exact KFacts.factorization_three_mul_nine_mul hk
  have hS0 : IsPGroup 3 ((A ⊓ L).subgroupOf I) :=
    IsPGroup.comap_subtype (fun y => ⟨1, Subtype.ext (by
      simpa using hAe.2 y (Subgroup.mem_inf.mp y.2).1)⟩)
  obtain ⟨Q', hQ'⟩ := hS0.exists_le_sylow
  have hQ'card : Nat.card Q' = 27 := by
    rw [Sylow.card_eq_multiplicity, hfact]
    norm_num
  refine ⟨(Q' : Subgroup ↥I).map I.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact cfg.hIK q.2
  · exact Q'.isPGroup'.map _
  · rw [Subgroup.card_map_of_injective I.subtype_injective]
    exact hQ'card
  · intro y hy
    exact ⟨⟨y, hALI hy⟩, hQ' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact Sec6.le_centralizer_of_mem_thetaComponentsAt hstd.mem_thetaComponentsAt (hIL q.2)


theorem eq_one_of_pow_three_of_mem_pCore_two {Y : Type} [Group Y] [Finite Y] {y : Y}
    (h3 : y ^ 3 = 1) (hy : y ∈ CFSG.pCore 2 Y) : y = 1 := by
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)) ⟨y, hy⟩
  have hn' : y ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hdvd3 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hdvd2 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hdvd2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd2
    omega

theorem quot_j2_facts {Y : Type} [Group Y] [Finite Y]
    (e : Y ⧸ CFSG.pCore 2 Y ≃* NativeSporadic.J2) :
    IsSimpleGroup (Y ⧸ CFSG.pCore 2 Y) ∧ Subgroup.center (Y ⧸ CFSG.pCore 2 Y) = ⊥ := by
  have hsimp : IsSimpleGroup (Y ⧸ CFSG.pCore 2 Y) :=
    (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hcard : Nat.card (Y ⧸ CFSG.pCore 2 Y) = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.KS14.card_nativeJ2
  exact ⟨hsimp, (Sec13.isPerfect_center_of_isSimpleGroup hsimp (by rw [hcard]; norm_num)).2⟩

theorem mem_normalizer_of_centralizes {A L K S : Subgroup G}
    {c b a : G} (cfg : Cfg129 G A c L b a K S)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* NativeSporadic.J2) {g : G}
    (hga : g ∈ Subgroup.centralizer ({a} : Set G)) (hgb : g ∈ Subgroup.centralizer ({b} : Set G)) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, -⟩ := cfg.point_facts
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := cfg.std.isE27.1
  have hbB : b ∈ Sec4.thetaQuotCentralizer L := cfg.hb.2
  have haK : a ∈ K := (BCensus.inf_le_residual cfg.std hbA hbB).trans cfg.hIK ⟨haA, haL⟩
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  by_contra hgK
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'def
  have hK' : K' ∈ thetaComponentsAt 3 b :=
    Sec13.conj_mem_thetaComponentsAt_of_mem_centralizer hgb cfg.hK
  have hne : K' ≠ K := by
    intro h
    apply hgK
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : g * y * g⁻¹ ∈ K' := ⟨y, hy, by simp [MulAut.conj_apply]⟩
      rwa [h] at this
    · intro hy
      rw [← h] at hy
      obtain ⟨k, hk, hky⟩ := hy
      have : k = y := by
        have h2 : g * k * g⁻¹ = g * y * g⁻¹ := by simpa [MulAut.conj_apply] using hky
        simpa using h2
      exact this ▸ hk
  have hag : g * a * g⁻¹ = a := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hga
    rw [this, mul_inv_cancel_right]
  have haK' : a ∈ K' := ⟨a, haK, by simpa [MulAut.conj_apply] using hag⟩
  have hacent : a ∈ Sec4.thetaQuotCentralizer K :=
    mem_thetaQuotCentralizer_of_ne hK' cfg.hK hne haK' (Subgroup.le_normalizer haK)
  obtain ⟨-, hall⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hacent
  obtain ⟨hsimp, hcenter⟩ := quot_j2_facts e
  have hθQ := theta_le_pCore_two_of_j2 e
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hcentral : π ⟨a, haK⟩ ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
    have h1 := hall (k : G) k.2
    obtain ⟨t, ht, hte⟩ := h1
    have ht2 : t ∈ CFSG.pCore 2 ↥K := hθQ ht
    have hkey : k⁻¹ * (⟨a, haK⟩ * k * ⟨a, haK⟩⁻¹) = t := by
      apply Subtype.ext
      simpa using hte.symm
    have h3 : π (k⁻¹ * (⟨a, haK⟩ * k * ⟨a, haK⟩⁻¹)) = 1 := by
      rw [hkey]; exact (QuotientGroup.eq_one_iff t).mpr ht2
    simp only [map_mul, map_inv] at h3
    have h4 : π k = π ⟨a, haK⟩ * π k * (π ⟨a, haK⟩)⁻¹ := inv_mul_eq_one.mp h3
    calc π k * π ⟨a, haK⟩ = (π ⟨a, haK⟩ * π k * (π ⟨a, haK⟩)⁻¹) * π ⟨a, haK⟩ := by
          rw [← h4]
      _ = π ⟨a, haK⟩ * π k := by group
  rw [hcenter, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcentral
  exact ha1 (congrArg Subtype.val (eq_one_of_pow_three_of_mem_pCore_two (Y := ↥K)
    (y := ⟨a, haK⟩) (Subtype.ext (by simpa using ha3)) hcentral))


theorem card_map_eq_of_injOn' {Y Z : Type} [Group Y] [Group Z] (f : Y →* Z) {S : Subgroup Y}
    (h : Set.InjOn f (S : Set Y)) : Nat.card (S.map f) = Nat.card S := by
  rw [← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn h]
  rfl

theorem exists_normal_two_subgroup (h415 : Sec4.Item4_15)
    {A L K S : Subgroup G} {c b a : G} (cfg : Cfg129 G A c L b a K S) (hHJ : HJType129 L K) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ S ≤ T ∧ T ≤ K ∧ T ≤ Subgroup.centralizer ({a} : Set G) ∧
      ∀ g ∈ Subgroup.centralizer ({a} : Set G), g ∈ Subgroup.centralizer ({b} : Set G) →
        ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hHJ.2
  have hX : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* NativeSporadic.J2) := ⟨e⟩
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, -⟩ := cfg.point_facts
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := cfg.std.isE27.1
  have hbB : b ∈ Sec4.thetaQuotCentralizer L := cfg.hb.2
  have hALK : A ⊓ L ≤ K := (BCensus.inf_le_residual cfg.std hbA hbB).trans cfg.hIK
  have haK : a ∈ K := hALK ⟨haA, haL⟩
  have hcK : c ∈ K := hALK ⟨cfg.std.mem_A, cfg.std.mem_L⟩
  obtain ⟨Q3, hQ3K, hQ3p, hQ3card, hALQ, hQ3c⟩ := exists_sylow_three cfg hHJ
  set Qk : Subgroup ↥K := CFSG.pCore 2 ↥K with hQk
  set π : ↥K →* (↥K ⧸ Qk) := QuotientGroup.mk' Qk with hπ
  set X := ↥K ⧸ Qk with hXdef
  set aK : ↥K := ⟨a, haK⟩ with haKdef
  set cK : ↥K := ⟨c, hcK⟩ with hcKdef
  have haK3 : aK ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 a haA)
  have hcK3 : cK ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 c cfg.std.mem_A)
  set Q3K : Subgroup ↥K := Q3.subgroupOf K with hQ3Kdef
  have hQ3Kp : IsPGroup 3 Q3K := hQ3p.comap_subtype
  have hinj : Set.InjOn π (Q3K : Set ↥K) := injOn_mk_pCore_two hQ3Kp
  set P0 : Subgroup X := Q3K.map π with hP0def
  have hQ3Kcard : Nat.card Q3K = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ3K).toEquiv]
    exact hQ3card
  have hP0card : Nat.card P0 = 27 := (card_map_eq_of_injOn' π hinj).trans hQ3Kcard
  have hP0p : IsPGroup 3 P0 := hQ3Kp.map π
  obtain ⟨Pq, hP0Pq⟩ := hP0p.exists_le_sylow
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X hX Pq _ rfl _ rfl
  have hPq27 : Nat.card (Pq : Subgroup X) = 27 := hHeis.2.1
  have hPqeq : (Pq : Subgroup X) = P0 :=
    (Subgroup.eq_of_le_of_card_ge hP0Pq (by rw [hPq27, hP0card])).symm
  have haQ : aK ∈ Q3K := Subgroup.mem_subgroupOf.mpr (hALQ ⟨haA, haL⟩)
  have hcQ : cK ∈ Q3K := Subgroup.mem_subgroupOf.mpr (hALQ ⟨cfg.std.mem_A, cfg.std.mem_L⟩)
  have hcPq : π cK ∈ (Pq : Subgroup X) := by
    rw [hPqeq]; exact Subgroup.mem_map_of_mem π hcQ
  have hcZ : π cK ∈ (Pq : Subgroup X) ⊓ Subgroup.centralizer ((Pq : Subgroup X) : Set X) := by
    refine ⟨hcPq, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    rw [hPqeq] at hg
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hg
    have hq' : (q : G) ∈ Q3 := Subgroup.mem_subgroupOf.mp hq
    have hqc : q * cK = cK * q :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hQ3c hq'))
    rw [← map_mul, ← map_mul, hqc]
  have hc1 : π cK ≠ 1 := by
    intro h
    have h' : cK ∈ Qk := (QuotientGroup.eq_one_iff cK).mp h
    exact cfg.std.ne_one (congrArg Subtype.val
      (eq_one_of_pow_three_of_mem_pCore_two (Y := ↥K) hcK3 h'))
  have haZ : π aK ∉ (Pq : Subgroup X) ⊓ Subgroup.centralizer ((Pq : Subgroup X) : Set X) := by
    intro hZ
    rcases KFacts.KS14.j2_mem_inf_centralizer_eq h415 hX Pq hcZ hc1 hZ with h | h | h
    · have h' : aK ∈ Qk := (QuotientGroup.eq_one_iff aK).mp h
      exact ha1 (congrArg Subtype.val
        (eq_one_of_pow_three_of_mem_pCore_two (Y := ↥K) haK3 h'))
    · have h' : aK = cK := hinj haQ hcQ h
      apply cfg.ha_not
      rw [show a = c from congrArg Subtype.val h']
      exact Subgroup.mem_zpowers c
    · have h' : aK = cK * cK := hinj haQ (Q3K.mul_mem hcQ hcQ) (by rw [map_mul]; exact h)
      apply cfg.ha_not
      have h'' : a = c * c := congrArg Subtype.val h'
      rw [h'', ← pow_two]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) 2
  set A9 : Subgroup X := ((A ⊓ L).subgroupOf K).map π with hA9def
  have hALQ' : (A ⊓ L).subgroupOf K ≤ Q3K := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hALQ (Subgroup.mem_subgroupOf.mp hy))
  have hA9P : A9 ≤ (Pq : Subgroup X) := by
    rw [hPqeq]
    exact Subgroup.map_mono hALQ'
  have hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_eq_nine_of_list cfg.std cfg.list
  have hA9card : Nat.card A9 = 9 := by
    rw [card_map_eq_of_injOn' π (hinj.mono hALQ'),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALK).toEquiv]
    exact hAL9
  have haA9 : π aK ∈ A9 := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨haA, haL⟩)
  set SX : Subgroup X := (S.subgroupOf K).map π with hSXdef
  have hSX2 : IsPGroup 2 SX := (cfg.hS2.comap_subtype).map π
  have hSXC : SX ≤ Subgroup.centralizer ({π aK} : Set X) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have haD : a ∈ D129 a b := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    exact (Subgroup.mem_centralizer_iff.mp (cfg.hS_cent hsS) a haD).symm
  have hSXT := j2_two_subgroup_le_pCore h415 hX Pq hA9P hA9card haA9 haZ hSX2 hSXC
  set TX : Subgroup X := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({π aK} : Set X))
    with hTXdef
  set TK : Subgroup ↥K := TX.comap π ⊓ Subgroup.centralizer ({aK} : Set ↥K) with hTKdef
  have hTX2 : IsPGroup 2 TX :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.centralizer ({π aK} : Set X)))).map _
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hTK2 : IsPGroup 2 TK :=
    (IsPGroup.comap_of_ker_isPGroup hTX2 π hker).to_le inf_le_left
  have hTXstable : ∀ γ : X ≃* X, γ (π aK) = π aK → ∀ y ∈ TX, γ y ∈ TX := by
    intro γ hγ y hy
    have hγ' : γ.symm (π aK) = π aK := by rw [MulEquiv.symm_apply_eq]; exact hγ.symm
    have h1 : (Subgroup.centralizer ({π aK} : Set X)).map γ.toMonoidHom =
        Subgroup.centralizer ({π aK} : Set X) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' := Subgroup.mem_centralizer_singleton_iff.mp hw
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have := congrArg γ hw'
        rw [map_mul, map_mul, hγ] at this
        exact this
      · intro hz
        refine ⟨γ.symm z, ?_, γ.apply_symm_apply z⟩
        have hz' := Subgroup.mem_centralizer_singleton_iff.mp hz
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have := congrArg γ.symm hz'
        rw [map_mul, map_mul, hγ'] at this
        exact this
    have h2 := KFacts.KS14.map_inSubgroup_pCore_two γ (Subgroup.centralizer ({π aK} : Set X))
    rw [h1] at h2
    have h3 : γ y ∈ (inSubgroup (CFSG.pCore 2)
        (Subgroup.centralizer ({π aK} : Set X))).map γ.toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h2] at h3
  refine ⟨TK.map K.subtype, hTK2.map _, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  ·
    intro s hs
    have hsK : s ∈ K := cfg.hS_le hs
    have hsS : (⟨s, hsK⟩ : ↥K) ∈ S.subgroupOf K := Subgroup.mem_subgroupOf.mpr hs
    have hsT : π ⟨s, hsK⟩ ∈ TX := hSXT (Subgroup.mem_map_of_mem π hsS)
    refine ⟨⟨s, hsK⟩, ⟨hsT, ?_⟩, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    apply Subtype.ext
    have haD : a ∈ D129 a b := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    exact (Subgroup.mem_centralizer_iff.mp (cfg.hS_cent hs) a haD).symm
  ·
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk.2)
  ·
    intro g hga hgb t ht
    have hgK : g ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_centralizes cfg e hga hgb
    obtain ⟨k, hk, rfl⟩ := ht
    set σ : MulAut ↥K := K.normalizerMonoidHom ⟨g, hgK⟩ with hσ
    have hσk : ∀ l : ↥K, (σ l : G) = g * l * g⁻¹ := fun l => rfl
    have hσa : σ aK = aK := by
      apply Subtype.ext
      rw [hσk]
      have := Subgroup.mem_centralizer_singleton_iff.mp hga
      simp only [haKdef]
      rw [this, mul_inv_cancel_right]
    have hQσ : Qk.map σ.toMonoidHom = Qk := CFSG.pCore_map_iso 2 σ
    set γ : X ≃* X := QuotientGroup.congr Qk Qk σ hQσ with hγdef
    have hγ : ∀ l : ↥K, γ (π l) = π (σ l) := fun l => rfl
    refine ⟨σ k, ⟨?_, ?_⟩, rfl⟩
    · have : γ (π k) ∈ TX := hTXstable γ (by rw [hγ, hσa]) _ hk.1
      rwa [hγ] at this
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hk.2
      have h2 := congrArg σ h1
      rw [map_mul, map_mul, hσa] at h2
      exact h2

end CFSG.RankThree.PartTwo.Sec12.Hering129G

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

theorem gap129HJOmega_of :
    Gap129HJOmega := by
  intro G _ _ A c L b a K S cfg hHJ x hxD hxb
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, -⟩ := cfg.point_facts
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := cfg.std.isE27.1
  have hA27 : Nat.card A = 27 := cfg.mem_E.2.1
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  obtain ⟨T, hT2, hST, hTK, hTa, hTn⟩ :=
    Hering129G.exists_normal_two_subgroup Sec4.Sporadic.rank3II_4_15 cfg hHJ
  have hab : a * b = b * a := hAc a haA b hbA
  obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup hab hxD
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  have hai : a ^ i ≠ 1 := by
    intro h
    apply hxb
    rw [hij, h, one_mul]
    exact Subgroup.zpow_mem_zpowers b j
  have haR : a ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers b := by
    refine mem_of_mem_zpowers_of_ne_one ha3 (Subgroup.zpow_mem_zpowers a i) hai ?_
    have h1 : a ^ i = x * (b ^ j)⁻¹ := by rw [hij]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers b j)))
  have hBA : A ⊓ Sec4.thetaQuotCentralizer L ≤ A := inf_le_left
  have hxB : x ∉ A ⊓ Sec4.thetaQuotCentralizer L := by
    intro hxB
    have hRB : Subgroup.zpowers x ⊔ Subgroup.zpowers b ≤ A ⊓ Sec4.thetaQuotCentralizer L :=
      sup_le (Subgroup.zpowers_le.mpr hxB) (Subgroup.zpowers_le.mpr cfg.hb)
    exact haB (hRB haR).2
  have hodd := cfg.mem_S.2.1 x hxA hx1
  have hWb : T ≤ Subgroup.centralizer ({b} : Set G) := fun t ht =>
    Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.hK (hTK ht)
  have hWx : T ≤ Subgroup.centralizer ({x} : Set G) := by
    intro t ht
    have h1 : Commute t a := Subgroup.mem_centralizer_singleton_iff.mp (hTa ht)
    have h2 : Commute t b := Subgroup.mem_centralizer_singleton_iff.mp (hWb ht)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [hij]
    exact ((h1.zpow_right i).mul_right (h2.zpow_right j)).eq
  have hWn : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∈ Subgroup.centralizer ({b} : Set G) →
      ∀ w ∈ T, g * w * g⁻¹ ∈ T := by
    intro g hgx hgb w hw
    have hR : Subgroup.zpowers x ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hgx).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hgb).symm
    have hga : g ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hR haR)).symm
    exact hTn g hga hgb w hw
  have hW1 : ⁅T, A⁆ ≠ ⊥ := by
    intro h
    have h1 : ⁅S, Subgroup.zpowers c⁆ ≤ ⁅T, A⁆ :=
      Subgroup.commutator_mono hST (Subgroup.zpowers_le.mpr cfg.std.mem_A)
    rw [h, le_bot_iff, cfg.hS_comm] at h1
    exact cfg.hS_ne h1
  exact Hering129G.not_starConditionAt_of_normal_two hAe hA27 hxA hx1 hBA cfg.std.card_B hxB
    cfg.hb hb1 hodd hT2 hWx hWb hWn hW1

end CFSG.RankThree.PartTwo.Sec12
