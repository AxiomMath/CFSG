module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypes
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofTransOut
import CFSG.Goldschmidt.Steps.G310TypeID
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1611Res

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

omit [Finite G] in
theorem k142_le_centralizer {LB : Subgroup G → Subgroup G} (hA : IsE27 A) (hcA : c ∈ A) :
    k142 A LB c ≤ Subgroup.centralizer ({c} : Set G) :=
  sSup_le fun _ hQ => le_centralizer_of_le_normalizer_zpowers hA hcA hQ.1 hQ.2

theorem xA_le_k142 {LB : Subgroup G → Subgroup G} (hAab : IsMulCommutative A) (hcA : c ∈ A) :
    xA A ≤ k142 A LB c := by
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab
  have hXc : xA A ≤ Subgroup.centralizer ({c} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA))
  refine le_delta ⟨⟨le_top, ?_, hAC.trans (le_normalizer_pPrimeCoreOf 3 _)⟩, fun B _ => ?_⟩
    (hXc.trans (Sec14.centralizer_singleton_le_normalizer_zpowers c))
  · exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
  · exact inf_le_left.trans (le_sup_right.trans le_sup_left)

omit [Finite G] in
theorem le_kA142_of_mem {LB : Subgroup G → Subgroup G} {S : Subgroup G}
    (hS : S ∈ scriptQPi A LB (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2)) :
    S ≤ kA142 A LB c :=
  (le_delta hS.1.1 hS.1.2).trans le_sup_left

omit [Finite G] in
theorem isPGroup_img142 {LB : Subgroup G → Subgroup G} [(ker142 A LB c).Normal]
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSKA : S ≤ kA142 A LB c) :
    IsPGroup 2 (img142 A LB c S) :=
  (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSKA).symm).map _

omit [Finite G] in
theorem le_centralizer_of_eq_thetaC {LB : Subgroup G → Subgroup G} [(ker142 A LB c).Normal]
    {Q : Subgroup G} {a : G} (ha : a ∈ A)
    (hQα : img142 A LB c Q = thetaC142 A LB c (alpha142 A LB c a ha) ⊔ thetaCA142 A LB c) :
    img142 A LB c Q ≤ Subgroup.centralizer ({alpha142 A LB c a ha} : Set _) := by
  refine (le_of_eq hQα).trans (sup_le ((Subgroup.map_subtype_le _).trans inf_le_right) ?_)
  intro t ht
  have htC : t ∈ Subgroup.centralizer (img142 A LB c A : Set _) :=
    ((Subgroup.map_subtype_le _).trans inf_le_right) ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp htC _
    (Sec15.Proof1513Res3.mk_mem_img142 (g := ⟨a, Subgroup.mem_sup_right ha⟩) ha)).symm

theorem xA_le_normalizer (h : Sec14Std G A c L) : xA A ≤ Subgroup.normalizer (L : Set G) := by
  have hD := h.toSec13Data
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  exact ((pPrimeCoreOf_le 3 _).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A))).trans
    (centralizer_le_normalizer_of_three_dvd h h3L)

theorem not_transOn_of_inf_centralizer {LB : Subgroup G → Subgroup G}
    [(ker142 A LB c).Normal] (hAab : IsMulCommutative A) (hcA : c ∈ A)
    (hXL : xA A ≤ Subgroup.normalizer (L : Set G)) {S T : Subgroup G}
    (hS : S ∈ scriptQPiStar A LB (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2))
    (hT : T ∈ scriptQPiStar A LB (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2))
    {e : G} (he : e ∈ A)
    (hSe : img142 A LB c S ⊓ img142 A LB c L ⊓
      Subgroup.centralizer ({alpha142 A LB c e he} : Set _) = ⊥)
    (hTe : img142 A LB c T ⊓ img142 A LB c L ⊓
      Subgroup.centralizer ({alpha142 A LB c e he} : Set _) ≠ ⊥) :
    ¬ TransOn A LB (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  intro htr
  obtain ⟨x, hx, hxT⟩ := htr S hS T hT
  have hxX : x ∈ xA A := (Subgroup.mem_inf.mp hx).1
  have hxKA : x ∈ kA142 A LB c := Subgroup.mem_sup_left (xA_le_k142 hAab hcA hxX)
  have hSKA : S ≤ kA142 A LB c := le_kA142_of_mem hS.prop
  set xk : ↥(kA142 A LB c) := ⟨x, hxKA⟩ with hxk
  set π := QuotientGroup.mk' (ker142 A LB c) with hπ
  set eα := alpha142 A LB c e he with heα
  have hxe : π xk * eα = eα * π xk := by
    have hxC : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hxX
    have h1 : x * e = e * x := (Subgroup.mem_centralizer_iff.mp hxC e he).symm
    rw [heα, alpha142, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1
  apply hTe
  rw [eq_bot_iff]
  rintro t ⟨⟨htT, htL⟩, htC⟩
  obtain ⟨t₀, ht₀, rfl⟩ := htT
  replace htL : π t₀ ∈ img142 A LB c L := htL
  replace htC : π t₀ ∈ Subgroup.centralizer ({eα} : Set _) := htC
  have ht₀T : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.mp ht₀
  rw [hxT] at ht₀T
  obtain ⟨s₀, hs₀, hs₀t⟩ := ht₀T
  have hs₀KA : s₀ ∈ kA142 A LB c := hSKA hs₀
  set sk : ↥(kA142 A LB c) := ⟨s₀, hs₀KA⟩ with hsk
  have hts : t₀ = xk * sk * xk⁻¹ := by
    apply Subtype.ext
    rw [← hs₀t]
    rfl
  have hsS : π sk ∈ img142 A LB c S := Sec15.Proof1513Res3.mk_mem_img142 hs₀
  have hsdef : π sk = (π xk)⁻¹ * π t₀ * π xk := by
    rw [hts, map_mul, map_mul, map_inv]
    group
  have hsL : π sk ∈ img142 A LB c L := by
    have hN : π xk⁻¹ ∈ Subgroup.normalizer (img142 A LB c L : Set _) :=
      Sec15.Proof1513Res3.mk_mem_normalizer_img142 (hXL (inv_mem hxX))
    have h1 := (Subgroup.mem_normalizer_iff.mp hN (π t₀)).mp htL
    rw [hsdef]
    simpa [map_inv] using h1
  have hsC : π sk ∈ Subgroup.centralizer ({eα} : Set _) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at htC ⊢
    have c1 : Commute (π t₀) eα := htC
    have c2 : Commute (π xk) eα := hxe
    rw [hsdef]
    exact ((c2.inv_left.mul_left c1).mul_left c2).eq
  have hs1 : π sk = 1 := by
    have : π sk ∈ (⊥ : Subgroup _) := hSe ▸ ⟨⟨hsS, hsL⟩, hsC⟩
    exact (Subgroup.mem_bot).mp this
  rw [Subgroup.mem_bot, hts, map_mul, map_mul, hs1, mul_one, map_inv, mul_inv_cancel]

theorem exists_mem_star_ge (hspor : SporadicModels131) (h : Sec14Std G A c L)
    [(ker142 A (lB A) c).Normal] (hLK : L ≤ k142 A (lB A) c)
    (h142 : ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c} : Set G)))
    {Θ : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)} (hΘ2 : IsPGroup 2 Θ)
    (hΘL : Θ ≤ img142 A (lB A) c L)
    (hAΘ : img142 A (lB A) c A ≤ Subgroup.normalizer (Θ : Set _)) :
    ∃ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2),
      Θ ≤ img142 A (lB A) c S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set K := k142 A (lB A) c with hK
  set O := pPrimeCoreOf 3 K with hO
  have hLKA : L ≤ kA142 A (lB A) c := hLK.trans le_sup_left
  set f := Res5Types.toKα hLKA with hf
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := k142_le_centralizer h.isE27 hD.mem_A
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hfx : ∀ l : ↥L, f l = QuotientGroup.mk' (ker142 A (lB A) c) ⟨(l : G), hLKA l.2⟩ :=
    fun _ => rfl
  have hker : f.ker ≤ aschbacherSolvableCore 3 ↥L := by
    intro l hl
    rw [MonoidHom.mem_ker, hfx, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ker142,
      Subgroup.mem_subgroupOf] at hl
    exact Item148PtRes2.inf_le_theta hspor h hO3 (hLK.trans (le_normalizer_pPrimeCoreOf 3 K))
      ((pPrimeCoreOf_le 3 K).trans hKc) (Subgroup.mem_subgroupOf.mpr hl)
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set Y := Θ.comap f with hY
  set Y' := Y.map L.subtype with hY'
  have hY3 : ¬ 3 ∣ Nat.card Y' := by
    rw [hY', Subgroup.card_map_of_injective L.subtype_injective]
    intro h3
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hyL : orderOf (y : ↥L) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
    have hyΘ : f (y : ↥L) ∈ Θ := y.2
    obtain ⟨k, hk⟩ := hΘ2 ⟨_, hyΘ⟩
    have hk' : f (y : ↥L) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : orderOf (f (y : ↥L)) ∣ 3 := hyL ▸ orderOf_map_dvd f _
    have h2 : orderOf (f (y : ↥L)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hf1 : f (y : ↥L) = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num)) h1 h2)
    have hyθ : (y : ↥L) ∈ aschbacherSolvableCore 3 ↥L := hker (MonoidHom.mem_ker.mpr hf1)
    apply hθ3
    have := orderOf_dvd_natCard (⟨(y : ↥L), hyθ⟩ : aschbacherSolvableCore 3 ↥L)
    rwa [Subgroup.orderOf_mk, hyL] at this
  have hAY : A ≤ Subgroup.normalizer (Y' : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := hy
    have haL : a * (l : G) * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha) l).mp l.2
    refine ⟨⟨_, haL⟩, ?_, rfl⟩
    have hval : f ⟨_, haL⟩ = alpha142 A (lB A) c a ha * f l * (alpha142 A (lB A) c a ha)⁻¹ := by
      rw [hfx, hfx, alpha142, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hamem : alpha142 A (lB A) c a ha ∈ img142 A (lB A) c A :=
      Sec15.Proof1513Res3.mk_mem_img142 (g := ⟨a, Subgroup.mem_sup_right ha⟩) ha
    show f ⟨_, haL⟩ ∈ Θ
    rw [hval]
    exact (Subgroup.mem_normalizer_iff.mp (hAΘ hamem) _).mp hl
  have hAbot : A ≤ Subgroup.normalizer (((⊥ : Subgroup G) : Subgroup G) : Set G) := fun a _ =>
    Subgroup.mem_normalizer_fintype fun n hn => by
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hn ⊢
      rw [hn, mul_one, mul_inv_cancel]
  obtain ⟨R, hR, -, hAR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hY3 hAY bot_le IsPGroup.of_bot hAbot
  have hY'L : Y' ≤ L := Subgroup.map_subtype_le _
  have hRL : R ≤ L := hR.1.trans hY'L
  have hLH : L ≤ H := hLK.trans (delta_le _)
  have hRinv : R ∈ invariantPiSubgroups H A (piCompl 3) :=
    ⟨hRL.trans hLH, (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr
      (fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le hR.1))), hAR⟩
  obtain ⟨Q, hRQ, hQ⟩ :=
    Finite.exists_le_maximal (p := (· ∈ invariantPiSubgroups H A (piCompl 3))) hRinv
  have hRpi : R ∈ scriptQPi A (lB A) H (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le (h142 Q hQ).1 hRQ hAR, hRL.trans hLH⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR.2.1⟩
  obtain ⟨S, hRS, hS⟩ :=
    Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) H (piOf 2))) hRpi
  refine ⟨S, hS, ?_⟩
  have hY'KA : Y' ≤ kA142 A (lB A) c := hY'L.trans hLKA
  have himg : img142 A (lB A) c Y' = Θ := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨l, hl, hly⟩ := Subgroup.mem_subgroupOf.mp hy
      have hyl : QuotientGroup.mk' (ker142 A (lB A) c) y = f l := by
        rw [hfx]
        congr 1
        exact Subtype.ext hly.symm
      rw [hyl]
      exact hl
    · intro θ hθ
      have hθL := hΘL hθ
      rw [← Res5Types.range_toKα hLKA] at hθL
      obtain ⟨l, hl⟩ := hθL
      refine ⟨⟨(l : G), hLKA l.2⟩, Subgroup.mem_subgroupOf.mpr ⟨l, ?_, rfl⟩, ?_⟩
      · show f l ∈ Θ
        rw [hl]
        exact hθ
      · rw [← hl]
        rfl
  have hRα : img142 A (lB A) c R = Θ := by
    rw [← himg]
    exact CFSG.Goldschmidt.G310.map_eq_of_fusionIsSylowIn (QuotientGroup.mk' _)
      (CFSG.Goldschmidt.G310.fusionIsSylowIn_subgroupOf hR hY'KA)
      (by change IsPGroup 2 (img142 A (lB A) c Y'); rw [himg]; exact hΘ2)
  rw [← hRα]
  exact Sec15.Proof1513Res3.img142_mono hRS

theorem exists_lbarEquiv (hspor : SporadicModels131) (h : Sec14Std G A c L)
    [(ker142 A (lB A) c).Normal] (hLK : L ≤ k142 A (lB A) c) :
    ∃ ι : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* ↥(img142 A (lB A) c L),
      ∀ l : ↥L, ((ι (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l) :
          ↥(img142 A (lB A) c L)) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) =
        QuotientGroup.mk' (ker142 A (lB A) c) ⟨(l : G), Subgroup.mem_sup_left (hLK l.2)⟩ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  set K := k142 A (lB A) c with hKdef
  set O := pPrimeCoreOf 3 K with hO
  have hLKA : L ≤ kA142 A (lB A) c := hLK.trans le_sup_left
  set f := Res5Types.toKα hLKA with hf
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := k142_le_centralizer h.isE27 hD.mem_A
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hKN : K ≤ Subgroup.normalizer (L : Set G) :=
    hKc.trans (centralizer_le_normalizer_of_three_dvd h h3L)
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hθO : inSubgroup (aschbacherSolvableCore 3) L ≤ O := by
    refine le_pPrimeCoreOf ((Subgroup.map_subtype_le _).trans hLK)
      (hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) ?_
    rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hker : f.ker = aschbacherSolvableCore 3 ↥L := by
    ext l
    rw [MonoidHom.mem_ker, hf, Res5Types.toKα, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ker142, Subgroup.mem_subgroupOf]
    change (l : G) ∈ O ⊔ Subgroup.zpowers c ↔ _
    constructor
    · intro hl
      exact Item148PtRes2.inf_le_theta hspor h hO3
        (hLK.trans (le_normalizer_pPrimeCoreOf 3 K)) ((pPrimeCoreOf_le 3 K).trans hKc)
        (Subgroup.mem_subgroupOf.mpr hl)
    · intro hl
      exact Subgroup.mem_sup_left (hθO ⟨l, hl, rfl⟩)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      (MulEquiv.subgroupCongr (Res5Types.range_toKα hLKA))), fun l => rfl⟩

omit [Finite G] in
theorem centralizer_le_of_mem_zpowers {Γ : Type*} [Group Γ] [Finite Γ] {x y : Γ}
    (hx3 : x ^ 3 = 1) (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) (hyx : y ∈ Subgroup.zpowers x) :
    Subgroup.centralizer ({y} : Set Γ) ≤ Subgroup.centralizer ({x} : Set Γ) := by
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hxo : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo]; exact Nat.le_of_dvd (by norm_num) hxo)
  have hxy : x ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers x
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxy
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  exact ((Commute.zpow_right hg k)).eq

theorem not_transOn_of_points (hspor : SporadicModels131) (h : Sec14Std G A c L)
    [(ker142 A (lB A) c).Normal] (hLK : L ≤ k142 A (lB A) c)
    (h142 : ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c} : Set G)) ∧
        ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
          img142 A (lB A) c Q ≤ Subgroup.centralizer ({alpha142 A (lB A) c a ha} : Set _))
    (hcent : ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A), alpha142 A (lB A) c a ha ≠ 1 →
      alpha142 A (lB A) c b hb ∉ Subgroup.zpowers (alpha142 A (lB A) c a ha) →
      ∀ x ∈ img142 A (lB A) c L,
        x ∈ Subgroup.centralizer ({alpha142 A (lB A) c a ha} : Set _) →
        x ∈ Subgroup.centralizer ({alpha142 A (lB A) c b hb} : Set _) →
        (∃ k : ℕ, x ^ 2 ^ k = 1) → x = 1)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) (ha1 : alpha142 A (lB A) c a ha ≠ 1)
    (hab : alpha142 A (lB A) c b hb ∉ Subgroup.zpowers (alpha142 A (lB A) c a ha))
    {Θa Θb : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (hΘa : IsPGroup 2 Θa ∧ Θa ≤ img142 A (lB A) c L ∧
      Θa ≤ Subgroup.centralizer ({alpha142 A (lB A) c a ha} : Set _) ∧
      img142 A (lB A) c A ≤ Subgroup.normalizer (Θa : Set _) ∧ Θa ≠ ⊥)
    (hΘb : IsPGroup 2 Θb ∧ Θb ≤ img142 A (lB A) c L ∧
      Θb ≤ Subgroup.centralizer ({alpha142 A (lB A) c b hb} : Set _) ∧
      img142 A (lB A) c A ≤ Subgroup.normalizer (Θb : Set _) ∧ Θb ≠ ⊥) :
    ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hAab : IsMulCommutative A := hD.isElemAbelian.1
  have hcA := hD.mem_A
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hXL : xA A ≤ Subgroup.normalizer (L : Set G) := xA_le_normalizer h
  have hα3 : ∀ (e : G) (he : e ∈ A), alpha142 A (lB A) c e he ^ 3 = 1 := by
    intro e he
    rw [alpha142, ← map_pow]
    have h1 : (⟨e, Subgroup.mem_sup_right he⟩ : ↥(kA142 A (lB A) c)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hD.isElemAbelian.2 e he)
    rw [h1, map_one]
  have hpoint : ∀ (e : G) (he : e ∈ A), alpha142 A (lB A) c e he ≠ 1 →
      ∀ Θ : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c), IsPGroup 2 Θ →
        Θ ≤ img142 A (lB A) c L →
        Θ ≤ Subgroup.centralizer ({alpha142 A (lB A) c e he} : Set _) → Θ ≠ ⊥ →
        ∀ S ∈ scriptQPiStar A (lB A) H (piOf 2), Θ ≤ img142 A (lB A) c S →
          img142 A (lB A) c S ≤ Subgroup.centralizer ({alpha142 A (lB A) c e he} : Set _) := by
    intro e he he1 Θ hΘ2 hΘL hΘC hΘ1 S hS hΘS
    have hSinv : S ∈ invariantPiSubgroups H A (piCompl 3) :=
      ⟨hS.prop.1.2, hS.prop.1.1.1.2.1, hS.prop.1.1.1.2.2⟩
    obtain ⟨Q, hSQ, hQ⟩ :=
      Finite.exists_le_maximal (p := (· ∈ invariantPiSubgroups H A (piCompl 3))) hSinv
    obtain ⟨-, a', ha', ha'1, hQC⟩ := h142 Q hQ
    have hSC : img142 A (lB A) c S ≤
        Subgroup.centralizer ({alpha142 A (lB A) c a' ha'} : Set _) :=
      (Sec15.Proof1513Res3.img142_mono hSQ).trans hQC
    by_cases hmem : alpha142 A (lB A) c a' ha' ∈ Subgroup.zpowers (alpha142 A (lB A) c e he)
    · exact hSC.trans (centralizer_le_of_mem_zpowers (hα3 e he) ha'1 (hα3 a' ha') hmem)
    · exfalso
      obtain ⟨⟨t, htΘ⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hΘ1
      obtain ⟨k, hk⟩ := hΘ2 ⟨t, htΘ⟩
      apply ht1
      apply Subtype.ext
      exact hcent e he a' ha' he1 hmem t (hΘL htΘ) (hΘC htΘ) (hSC (hΘS htΘ))
        ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨hΘa2, hΘaL, hΘaC, hΘaA, hΘa1⟩ := hΘa
  obtain ⟨hΘb2, hΘbL, hΘbC, hΘbA, hΘb1⟩ := hΘb
  have h142' : ∀ Q ∈ maxInvariantPiSubgroups H A (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c} : Set G)) :=
    fun Q hQ => (h142 Q hQ).1
  obtain ⟨Sa, hSa, hΘSa⟩ := exists_mem_star_ge hspor h hLK h142' hΘa2 hΘaL hΘaA
  obtain ⟨Sb, hSb, hΘSb⟩ := exists_mem_star_ge hspor h hLK h142' hΘb2 hΘbL hΘbA
  have hb1 : alpha142 A (lB A) c b hb ≠ 1 := fun h1 => hab (h1 ▸ one_mem _)
  have hSbC := hpoint b hb hb1 Θb hΘb2 hΘbL hΘbC hΘb1 Sb hSb hΘSb
  refine not_transOn_of_inf_centralizer hAab hcA hXL hSb hSa ha ?_ ?_
  · rw [eq_bot_iff]
    rintro x ⟨⟨hxS, hxL⟩, hxC⟩
    have hSb2 := isPGroup_img142 (isPGroup_of_mem_scriptQPi Nat.prime_two hSb.prop)
      (le_kA142_of_mem hSb.prop)
    obtain ⟨k, hk⟩ := hSb2 ⟨x, hxS⟩
    exact (Subgroup.mem_bot).mpr (hcent a ha b hb ha1 hab x hxL hxC (hSbC hxS)
      ⟨k, congrArg Subtype.val hk⟩)
  · intro hbot
    apply hΘa1
    rw [eq_bot_iff, ← hbot]
    exact le_inf (le_inf hΘSa hΘaL) hΘaC

end CFSG.RankThree.PartTwo.Sec16.Proof1611Res
