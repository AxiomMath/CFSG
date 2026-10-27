module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJDefs
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Cube
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.Quasithin.Background.C41PfI
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_j2 (hfix : J2AutFixNine) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) (hhyp : IsHyperplane A (A ⊓ L)) (hθ : aschbacherSolvableCore 3 ↥L = ⊥)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {x : G} (hxA : x ∈ Subgroup.centralizer (A : Set G)) (hx3 : Nat.Coprime 3 (orderOf x)) :
    x ∈ Subgroup.centralizer (L : Set G) := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS.toSec13Data.mem_partTwoE
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    have := hhyp.2
    rw [hA.2] at this
    omega
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := by
    refine Sec14.Proof1413Res3.centralizer_le_normalizer_of_mem_lA hS hS.zpowers_mem_omegaA
      hS.mem_lA (Sec14.three_dvd_card_of_thetaQuot_j2 hJ) ?_
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hS.mem_A) hxA
  have hLJ : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    obtain ⟨e⟩ := hJ
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hθ).trans
      (QuotientGroup.quotientBot (G := ↥L))).symm.trans e⟩
  set φ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxN⟩ with hφ
  have hE9 : Nat.card ((A ⊓ L).subgroupOf L : Subgroup ↥L) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hφo : Nat.Coprime 3 (orderOf φ) := by
    have h1 : orderOf φ ∣ orderOf (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) :=
      orderOf_map_dvd L.normalizerMonoidHom _
    rw [Subgroup.orderOf_mk] at h1
    exact hx3.coprime_dvd_right h1
  have hφfix : ∀ e ∈ (A ⊓ L).subgroupOf L, φ e = e := by
    intro e he
    apply Subtype.ext
    rw [hφ, Sec4.normalizerMonoidHom_apply_coe]
    have heA : (e : G) ∈ A := (Subgroup.mem_subgroupOf.mp he).1
    have hc := Subgroup.mem_centralizer_iff.mp hxA (e : G) heA
    change x * (e : G) * x⁻¹ = (e : G)
    rw [← hc, mul_inv_cancel_right]
  have hφ1 : φ = 1 := hfix (X := ↥L) hLJ ((A ⊓ L).subgroupOf L) hE9 φ hφo hφfix
  intro l hl
  have h := congrArg (fun τ : MulAut ↥L => ((τ ⟨l, hl⟩ : ↥L) : G)) hφ1
  simp only [MulAut.one_apply] at h
  rw [hφ, Sec4.normalizerMonoidHom_apply_coe] at h
  change x * l * x⁻¹ = l at h
  show l * x = x * l
  calc l * x = (x * l * x⁻¹) * x := by
        conv_lhs => rw [← h]
    _ = x * l := by group


theorem false_of_pCore_ne_bot {L : Subgroup G} {f : G} {F : Subgroup G}
    (hlr : CFSG.Assembly.RankThreeEven.localRank 5 G < 3)
    (hfN : f ∈ Subgroup.normalizer (L : Set G)) (hf5 : orderOf f = 5)
    (hOne : CFSG.pCore 2 ↥L ≠ ⊥) (hFL : F ≤ L)
    (hFea : CFSG.Open.IsElemAbelian 5 F) (hFcard : Nat.card F = 25)
    (hFcent : f ∈ Subgroup.centralizer (F : Set G)) (hfnotF : f ∉ F) : False := by
  let O : Subgroup G := (CFSG.pCore 2 ↥L).map L.subtype
  have hO2 : IsPGroup 2 O := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  have hOneG : O ≠ ⊥ := by
    intro hbot
    apply hOne
    have hmap : (CFSG.pCore 2 ↥L).map L.subtype = ⊥ := by simpa [O] using hbot
    exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥L) L.subtype_injective).mp hmap
  have hcomm : ∀ a ∈ F, ∀ b ∈ Subgroup.zpowers f, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right ((Subgroup.mem_centralizer_iff.mp hFcent) a ha) k).eq
  have hZea : CFSG.Open.IsElemAbelian 5 (Subgroup.zpowers f) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hf5]; exact pow_orderOf_eq_one f)
  have hAea : CFSG.Open.IsElemAbelian 5 (F ⊔ Subgroup.zpowers f) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hFea hZea hcomm
  have hdisj : F ⊓ Subgroup.zpowers f = ⊥ := by
    have hdvd : Nat.card (F ⊓ Subgroup.zpowers f : Subgroup G) ∣ 5 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : F ⊓ Subgroup.zpowers f ≤ Subgroup.zpowers f)
      rwa [Nat.card_zpowers, hf5] at this
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : F ⊓ Subgroup.zpowers f = Subgroup.zpowers f :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h5, Nat.card_zpowers, hf5])
      exact hfnotF ((heq ▸ Subgroup.mem_zpowers f).1)
  have hA125_card : Nat.card (F ⊔ Subgroup.zpowers f : Subgroup G) = 5 ^ 3 := by
    obtain ⟨hcard, -⟩ :=
      CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F (Subgroup.zpowers f) hcomm
    rw [hdisj, Subgroup.card_bot, mul_one, hFcard, Nat.card_zpowers, hf5] at hcard
    rw [hcard]
    norm_num
  have hLnorm : L ≤ Subgroup.normalizer (O : Set G) := by
    intro l hl
    change l ∈ Subgroup.normalizer (((CFSG.pCore 2 ↥L).map L.subtype : Subgroup G) : Set G)
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic
      (M := L) (C := CFSG.pCore 2 ↥L) (Subgroup.le_normalizer hl)
  have hfnorm : f ∈ Subgroup.normalizer (O : Set G) := by
    change f ∈ Subgroup.normalizer (((CFSG.pCore 2 ↥L).map L.subtype : Subgroup G) : Set G)
    exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic (M := L) (C := CFSG.pCore 2 ↥L) hfN
  have hA125_N : F ⊔ Subgroup.zpowers f ≤ Subgroup.normalizer (O : Set G) :=
    sup_le (hFL.trans hLnorm) (Subgroup.zpowers_le.mpr hfnorm)
  exact Sec13.F135Last.false_of_elemAbelian_cube Nat.prime_five hlr hAea hA125_card hOneG hO2
    hA125_N

theorem exists_elemAbelian_25_preimage (hE25 : J2HasE25)
    {L : Subgroup G} {N : Subgroup ↥L} [N.Normal]
    (hJ : Nonempty (↥L ⧸ N ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ Ebar : Subgroup (↥L ⧸ N), CFSG.Open.IsElemAbelian 5 Ebar ∧ Nat.card Ebar = 25 := by
  obtain ⟨e⟩ := hJ
  obtain ⟨E, hE, hc⟩ := hE25
  obtain ⟨Ebar, hEbar, hcard⟩ :=
    CFSG.Quasithin.C41Pf.exists_elemAbelian_of_mulEquiv e (p := 5) (k := 2)
      ⟨E, hE, by rw [hc]; norm_num⟩
  exact ⟨Ebar, hEbar, by simpa using hcard⟩

theorem mem_center_thetaQuot_of_conj_eq_one {L : Subgroup G} {f : G}
    (hfL : f ∈ L) (hfN : f ∈ Subgroup.normalizer (L : Set G))
    (hquot : ∀ l : ↥L,
      l⁻¹ * (L.normalizerMonoidHom ⟨f, hfN⟩ l) ∈ aschbacherSolvableCore 3 ↥L) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨f, hfL⟩ ∈
      Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  set N : Subgroup ↥L := aschbacherSolvableCore 3 ↥L with hN
  set π := QuotientGroup.mk' N with hπ
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N y
  have h1 : π l = π (L.normalizerMonoidHom ⟨f, hfN⟩ l) := (QuotientGroup.eq).mpr (hquot l)
  have hφsub : L.normalizerMonoidHom ⟨f, hfN⟩ l =
      (⟨f, hfL⟩ : ↥L) * l * (⟨f, hfL⟩ : ↥L)⁻¹ := by
    ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    simp
  have h2 : π (L.normalizerMonoidHom ⟨f, hfN⟩ l) =
      π ⟨f, hfL⟩ * π l * (π ⟨f, hfL⟩)⁻¹ := by
    rw [hφsub]
    simp
  have hcomm : π ⟨f, hfL⟩ * π l = π l * π ⟨f, hfL⟩ := by
    calc π ⟨f, hfL⟩ * π l = (π ⟨f, hfL⟩ * π l * (π ⟨f, hfL⟩)⁻¹) * π ⟨f, hfL⟩ := by group
      _ = π (L.normalizerMonoidHom ⟨f, hfN⟩ l) * π ⟨f, hfL⟩ := by rw [← h2]
      _ = π l * π ⟨f, hfL⟩ := by rw [← h1]
  exact hcomm.symm

theorem centralizer_sup_pCore_eq_top {L : Subgroup G} {f : G}
    (hfN : f ∈ Subgroup.normalizer (L : Set G)) (hf5 : orderOf f = 5)
    (hquot : ∀ l : ↥L,
      l⁻¹ * (L.normalizerMonoidHom ⟨f, hfN⟩ l) ∈ aschbacherSolvableCore 3 ↥L)
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L) :
    (Subgroup.centralizer ({f} : Set G)).subgroupOf L ⊔ CFSG.pCore 2 ↥L = ⊤ := by
  set O : Subgroup ↥L := CFSG.pCore 2 ↥L with hO
  haveI : O.Normal := CFSG.pCore_normal
  have hφcoe : ∀ l : ↥L, ((L.normalizerMonoidHom ⟨f, hfN⟩ l : ↥L) : G) = f * (l : G) * f⁻¹ :=
    fun l => Sec4.normalizerMonoidHom_apply_coe hfN l
  have hN : ∀ n ∈ O.map L.subtype, f * n * f⁻¹ ∈ O.map L.subtype := by
    intro n hn
    obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨L.normalizerMonoidHom ⟨f, hfN⟩ o, ?_, hφcoe o⟩
    change L.normalizerMonoidHom ⟨f, hfN⟩ o ∈ CFSG.pCore 2 ↥L
    have hchar : (CFSG.pCore 2 ↥L).Characteristic := CFSG.pCore_characteristic
    have hmap := Subgroup.characteristic_iff_map_eq.mp hchar (L.normalizerMonoidHom ⟨f, hfN⟩)
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (L.normalizerMonoidHom ⟨f, hfN⟩).toMonoidHom ho
  rw [eq_top_iff]
  intro x _
  have hg : (x : G)⁻¹ * (f * (x : G) * f⁻¹) ∈ O.map L.subtype := by
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * L.normalizerMonoidHom ⟨f, hfN⟩ x, ?_, ?_⟩
    · have hq := hquot x
      rwa [hθ] at hq
    · change ((x⁻¹ : ↥L) : G) * ((L.normalizerMonoidHom ⟨f, hfN⟩ x : ↥L) : G) =
        (x : G)⁻¹ * (f * (x : G) * f⁻¹)
      rw [hφcoe]
      simp [mul_assoc]
  have hcop : Nat.Coprime (orderOf f) (Nat.card (O.map L.subtype)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hf5, hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  obtain ⟨n, hn, hfixn⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime (O.map L.subtype) hN hg hcop
  obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hn
  have hxC : x * o ∈ (Subgroup.centralizer ({f} : Set G)).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have h1 : f * ((x : G) * (o : G)) = ((x : G) * (o : G)) * f := by
      have := congrArg (fun y : G => y * f) hfixn
      simpa [mul_assoc] using this
    exact h1.symm
  refine (Subgroup.mem_sup_of_normal_right
    (s := (Subgroup.centralizer ({f} : Set G)).subgroupOf L) (t := O)).mpr
    ⟨x * o, hxC, o⁻¹, O.inv_mem ho, ?_⟩
  group

theorem exists_elemAbelian_25_of_surjective_two_kernel
    {H E : Type*} [Group H] [Finite H] [Group E]
    {Ebar : Subgroup E} (q : H →* Ebar) (hq : Function.Surjective q)
    (hker2 : IsPGroup 2 q.ker)
    (hEea : CFSG.Open.IsElemAbelian 5 Ebar) (hEcard : Nat.card Ebar = 25) :
    ∃ F : Subgroup H, CFSG.Open.IsElemAbelian 5 F ∧ Nat.card F = 25 := by
  obtain ⟨D⟩ : Nonempty (Sylow 5 H) := inferInstance
  have hE5 : IsPGroup 5 Ebar := hEea.isPGroup
  have htop5 : IsPGroup 5 ↥(⊤ : Subgroup ↥Ebar) :=
    hE5.of_equiv (Subgroup.topEquiv (G := ↥Ebar)).symm
  have hDtop : (Sylow.mapSurjective hq D : Subgroup Ebar) = ⊤ :=
    ((Sylow.mapSurjective hq D).is_maximal' htop5 le_top).symm
  have hDmap : (D : Subgroup H).map q = ⊤ := by
    rw [← Sylow.coe_mapSurjective hq D, hDtop]
  have hD5 : IsPGroup 5 (D : Subgroup H) := Sylow.isPGroup' D
  have hdisj : (D : Subgroup H) ⊓ q.ker = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 5 2 (by norm_num) (D : Subgroup H) q.ker hD5 hker2)
  have hDcard : Nat.card (D : Subgroup H) = 25 := by
    have h1 := CFSG.card_map_eq_card_of_inf_ker_eq_bot q hdisj
    rw [hDmap, Subgroup.card_top, hEcard] at h1
    exact h1.symm
  have hqkerD : (q.comp (D : Subgroup H).subtype).ker = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxker : (x : H) ∈ q.ker := hx
      have hxF : (x : H) ∈ (D : Subgroup H) := x.2
      have : (x : H) ∈ (D : Subgroup H) ⊓ q.ker := ⟨hxF, hxker⟩
      rw [hdisj] at this
      exact Subtype.ext (Subgroup.mem_bot.mp this)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      simp
  have hqinjD : Function.Injective (q.comp (D : Subgroup H).subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp hqkerD
  have hDea : CFSG.Open.IsElemAbelian 5 (D : Subgroup H) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply hqinjD
      rw [map_mul, map_mul]
      exact hEea.1.is_comm.comm (q ((D : Subgroup H).subtype a))
        (q ((D : Subgroup H).subtype b))
    · have h1 : ((⟨x, hx⟩ : ↥(D : Subgroup H))) ^ 5 = 1 := by
        apply hqinjD
        rw [map_pow, map_one]
        apply Subtype.ext
        simpa using hEea.2 (q ((D : Subgroup H).subtype ⟨x, hx⟩))
          (q ((D : Subgroup H).subtype ⟨x, hx⟩)).2
      exact congrArg Subtype.val h1
  exact ⟨(D : Subgroup H), hDea, hDcard⟩

theorem exists_preimage_quotient_data {L : Subgroup G} {N : Subgroup ↥L} [N.Normal]
    (hN : N = aschbacherSolvableCore 3 ↥L)
    (hO : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    (Ebar : Subgroup (↥L ⧸ N)) :
    ∃ (V : Subgroup ↥L) (q : V →* Ebar), CFSG.pCore 2 ↥L ≤ V ∧
      Function.Surjective q ∧
      (∀ v : V, (q v : ↥L ⧸ N) = QuotientGroup.mk' N (v : ↥L)) := by
  set O : Subgroup ↥L := CFSG.pCore 2 ↥L with hOdef
  have hNO : N = O := hN.trans hO
  let π : ↥L →* ↥L ⧸ N := QuotientGroup.mk' N
  let V : Subgroup ↥L := Ebar.comap π
  have hOV : O ≤ V := by
    intro o ho
    refine Subgroup.mem_comap.mpr ?_
    have h1 : π o = 1 := by
      change (o : ↥L ⧸ N) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hNO ▸ ho
    rw [h1]
    exact Ebar.one_mem
  let q : V →* Ebar := (π.comp V.subtype).codRestrict Ebar
    (fun v => Subgroup.mem_comap.mp v.2)
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (y : ↥L ⧸ N)
    have hxV : x ∈ V := by
      refine Subgroup.mem_comap.mpr ?_
      rw [hx]
      exact y.2
    exact ⟨⟨x, hxV⟩, Subtype.ext hx⟩
  exact ⟨V, q, hOV, hqsurj, fun v => rfl⟩

theorem exists_centralizer_preimage_hom
    {L : Subgroup G} {f : G} (hfN : f ∈ Subgroup.normalizer (L : Set G))
    (hf5 : orderOf f = 5)
    (hO : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    {N : Subgroup ↥L} [N.Normal] (hN : N = aschbacherSolvableCore 3 ↥L)
    {Ebar : Subgroup (↥L ⧸ N)} {V : Subgroup ↥L} {q : V →* Ebar}
    (hqsurj : Function.Surjective q) (hOV : CFSG.pCore 2 ↥L ≤ V)
    (hqeq : ∀ v : V, (q v : ↥L ⧸ N) = QuotientGroup.mk' N (v : ↥L))
    (hquot : ∀ l : ↥L,
      l⁻¹ * (L.normalizerMonoidHom ⟨f, hfN⟩ l) ∈ aschbacherSolvableCore 3 ↥L) :
    ∃ (H : Subgroup ↥L) (qH : H →* Ebar),
      H ≤ (Subgroup.centralizer ({f} : Set G)).subgroupOf L ∧
      Function.Surjective qH ∧
      (∀ x : H, (qH x : ↥L ⧸ N) = QuotientGroup.mk' N (x : ↥L)) := by
  set O : Subgroup ↥L := CFSG.pCore 2 ↥L with hOdef
  have hNO : N = O := hN.trans hO
  let π : ↥L →* ↥L ⧸ N := QuotientGroup.mk' N
  let C : Subgroup ↥L := (Subgroup.centralizer ({f} : Set G)).subgroupOf L
  have hCO : C ⊔ O = ⊤ := centralizer_sup_pCore_eq_top hfN hf5 hquot hO
  let H : Subgroup ↥L := V ⊓ C
  let qH : H →* Ebar := q.comp (Subgroup.inclusion (inf_le_left : H ≤ V))
  have hqHval : ∀ x : H, (qH x : ↥L ⧸ N) = QuotientGroup.mk' N (x : ↥L) :=
    fun x => hqeq ⟨(x : ↥L), (inf_le_left : H ≤ V) x.2⟩
  have hqHsurj : Function.Surjective qH := by
    intro y
    obtain ⟨v, hvq⟩ := hqsurj y
    have hvtop : (v : ↥L) ∈ C ⊔ O := by
      rw [hCO]
      exact Subgroup.mem_top _
    rcases (Subgroup.mem_sup_of_normal_right (s := C) (t := O)).mp hvtop with
      ⟨c, hcC, o, hoO, hco⟩
    have hcV : c ∈ V := by
      have hc : c = (v : ↥L) * o⁻¹ := by rw [← hco]; group
      rw [hc]
      exact V.mul_mem v.2 (V.inv_mem (hOV hoO))
    have hqo : q ⟨o, hOV hoO⟩ = 1 := by
      apply Subtype.ext
      rw [hqeq ⟨o, hOV hoO⟩]
      change (o : ↥L ⧸ N) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hNO ▸ hoO
    refine ⟨⟨c, ⟨hcV, hcC⟩⟩, ?_⟩
    change q ⟨c, (inf_le_left : H ≤ V) ⟨hcV, hcC⟩⟩ = y
    have hcoV : (⟨c, (inf_le_left : H ≤ V) ⟨hcV, hcC⟩⟩ : V) * ⟨o, hOV hoO⟩ = v :=
      Subtype.ext hco
    calc q ⟨c, (inf_le_left : H ≤ V) ⟨hcV, hcC⟩⟩ =
        q ⟨c, (inf_le_left : H ≤ V) ⟨hcV, hcC⟩⟩ * q ⟨o, hOV hoO⟩ := by rw [hqo, mul_one]
      _ = q (⟨c, (inf_le_left : H ≤ V) ⟨hcV, hcC⟩⟩ * ⟨o, hOV hoO⟩) := by rw [map_mul]
      _ = q v := by rw [hcoV]
      _ = y := hvq
  exact ⟨H, qH, inf_le_right, hqHsurj, hqHval⟩

theorem centralizer_preimage_hom_kernel
    {L : Subgroup G} {N : Subgroup ↥L} [N.Normal]
    (hN : N = aschbacherSolvableCore 3 ↥L)
    (hO : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    {Ebar : Subgroup (↥L ⧸ N)} {H : Subgroup ↥L} {qH : H →* Ebar}
    (hqHval : ∀ x : H, (qH x : ↥L ⧸ N) = QuotientGroup.mk' N (x : ↥L)) :
    qH.ker = (H ⊓ CFSG.pCore 2 ↥L).subgroupOf H ∧ IsPGroup 2 qH.ker := by
  set O : Subgroup ↥L := CFSG.pCore 2 ↥L with hOdef
  have hNO : N = O := hN.trans hO
  have hqHker : qH.ker = (H ⊓ O).subgroupOf H := by
    ext x
    constructor
    · intro hx
      have h1 : (QuotientGroup.mk' N) (x : ↥L) = 1 := by
        rw [← hqHval x]
        exact congrArg Subtype.val hx
      have hxN : (x : ↥L) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
      refine Subgroup.mem_subgroupOf.mpr ⟨x.2, ?_⟩
      exact hNO ▸ hxN
    · intro hx
      have hxO : (x : ↥L) ∈ O := (Subgroup.mem_subgroupOf.mp hx).2
      have hxN : (x : ↥L) ∈ N := hNO ▸ hxO
      apply Subtype.ext
      rw [hqHval x]
      exact (QuotientGroup.eq_one_iff _).mpr hxN
  refine ⟨hqHker, ?_⟩
  rw [hqHker]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_le inf_le_right |>.of_equiv
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ O ≤ H)).symm

theorem exists_elemAbelian_25_centralizer_of_preimage
    {L : Subgroup G} {f : G} (hfN : f ∈ Subgroup.normalizer (L : Set G))
    (hf5 : orderOf f = 5) (hfnotL : f ∉ L)
    (hO : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    {N : Subgroup ↥L} [N.Normal] (hN : N = aschbacherSolvableCore 3 ↥L)
    {Ebar : Subgroup (↥L ⧸ N)} (hEbar_ea : CFSG.Open.IsElemAbelian 5 Ebar)
    (hEbar_card : Nat.card Ebar = 25)
    (hquot : ∀ l : ↥L,
      l⁻¹ * (L.normalizerMonoidHom ⟨f, hfN⟩ l) ∈ aschbacherSolvableCore 3 ↥L) :
    ∃ F : Subgroup G, F ≤ L ∧ CFSG.Open.IsElemAbelian 5 F ∧ Nat.card F = 25 ∧
      f ∈ Subgroup.centralizer (F : Set G) ∧ f ∉ F := by
  obtain ⟨V, q, hOV, hqsurj, hqeq⟩ := exists_preimage_quotient_data hN hO Ebar
  obtain ⟨H, qH, hHC, hqHsurj, hqHval⟩ :=
    exists_centralizer_preimage_hom hfN hf5 hO hN hqsurj hOV hqeq hquot
  obtain ⟨hqHker, hqHker2⟩ := centralizer_preimage_hom_kernel hN hO hqHval
  obtain ⟨F, hFea_H, hFcard_H⟩ :=
    exists_elemAbelian_25_of_surjective_two_kernel qH hqHsurj hqHker2 hEbar_ea hEbar_card
  let Fg : Subgroup G := ((F : Subgroup H).map H.subtype).map L.subtype
  have hFg_le : Fg ≤ L := Subgroup.map_subtype_le _
  have hFg_card : Nat.card Fg = 25 := by
    dsimp only [Fg]
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective H.subtype_injective, hFcard_H]
  have hFg_ea : CFSG.Open.IsElemAbelian 5 Fg := by
    have h1 : CFSG.Open.IsElemAbelian 5 ((F : Subgroup H).map H.subtype) :=
      hFea_H.map H.subtype
    have h2 : CFSG.Open.IsElemAbelian 5 Fg := by
      have := h1.map L.subtype
      simpa [Fg] using this
    exact h2
  have hFg_cent : f ∈ Subgroup.centralizer (Fg : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    dsimp only [Fg] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hzC : ((z : ↥H) : ↥L) ∈
        (Subgroup.centralizer ({f} : Set G)).subgroupOf L := hHC z.2
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hzC)
  refine ⟨Fg, hFg_le, hFg_ea, hFg_card, hFg_cent, fun h => hfnotL (hFg_le h)⟩

theorem thetaQuot_conj_eq_one_of_order_five (hfix : J2AutFixNine)
    {A L : Subgroup G} {c f : G} (hS : Sec14Std G A c L) (hhyp : IsHyperplane A (A ⊓ L))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hfN : f ∈ Subgroup.normalizer (L : Set G)) (hf5 : orderOf f = 5)
    (hfA : f ∈ Subgroup.centralizer (A : Set G)) :
    ∀ l : ↥L,
      l⁻¹ * (L.normalizerMonoidHom ⟨f, hfN⟩ l) ∈ aschbacherSolvableCore 3 ↥L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS.toSec13Data.mem_partTwoE
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    have := hhyp.2
    rw [hA.2] at this
    omega
  set φ : MulAut ↥L := L.normalizerMonoidHom ⟨f, hfN⟩ with hφ
  set N : Subgroup ↥L := aschbacherSolvableCore 3 ↥L with hN
  set π := QuotientGroup.mk' N with hπ
  set σ : MulAut (↥L ⧸ N) := CFSG.RankThree.mulAutQuotientHom N φ with hσ
  have hσapp : ∀ x : ↥L, σ (π x) = π (φ x) := by
    intro x
    rw [hσ, hπ]
    exact CFSG.RankThree.mulAutQuotientHom_mk N φ x
  have hσo : Nat.Coprime 3 (orderOf σ) := by
    have h1 : orderOf σ ∣ orderOf φ :=
      orderOf_map_dvd (CFSG.RankThree.mulAutQuotientHom N) φ
    have h2 : orderOf φ ∣ orderOf (⟨f, hfN⟩ : Subgroup.normalizer (L : Set G)) :=
      orderOf_map_dvd L.normalizerMonoidHom _
    rw [Subgroup.orderOf_mk, hf5] at h2
    exact Nat.Coprime.coprime_dvd_right (h1.trans h2) (by norm_num)
  let E : Subgroup (↥L ⧸ N) := (A.subgroupOf L).map π
  have hE9 : Nat.card E = 9 := by
    rw [show E = (A.subgroupOf L).map π from rfl, Sec14.card_map_mk_subgroupOf hS.isElemAbelian, h9]
  have hσE : ∀ e ∈ E, σ e = e := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
    rw [hσapp]
    congr 1
    apply Subtype.ext
    rw [hφ, Sec4.normalizerMonoidHom_apply_coe]
    have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
    have hc := Subgroup.mem_centralizer_iff.mp hfA (x : G) hxA
    change f * (x : G) * f⁻¹ = (x : G)
    rw [← hc, mul_inv_cancel_right]
  have hσ1 : σ = 1 := hfix (X := ↥L ⧸ N) hJ E hE9 σ hσo hσE
  intro l
  have h1 : π (φ l) = π l := by
    have := congrArg (fun τ : MulAut (↥L ⧸ N) => τ (π l)) hσ1
    simpa [hσapp] using this
  simpa [mul_assoc] using N.inv_mem (QuotientGroup.eq.mp h1)

theorem pCore_two_eq_bot_of_j2 (hfix : J2AutFixNine) (hE25 : J2HasE25) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) (hhyp : IsHyperplane A (A ⊓ L))
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {f : G} (hfA : f ∈ Subgroup.centralizer (A : Set G)) (hf5 : orderOf f = 5) :
    CFSG.pCore 2 ↥L = ⊥ := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS.toSec13Data.mem_partTwoE
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    have := hhyp.2
    rw [hA.2] at this
    omega
  have hfN : f ∈ Subgroup.normalizer (L : Set G) := by
    refine Sec14.centralizer_le_normalizer_of_j2 hS hJ ?_
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hS.mem_A) hfA
  have hquot := thetaQuot_conj_eq_one_of_order_five hfix hS hhyp hJ hfN hf5 hfA
  set N : Subgroup ↥L := aschbacherSolvableCore 3 ↥L with hN
  have hfnotL : f ∉ L := by
    intro hfL
    have hZ : Subgroup.center (↥L ⧸ N) = ⊥ :=
      KFacts.KS14.center_eq_bot_of_j2 h415 hJ
    have hc : QuotientGroup.mk' N ⟨f, hfL⟩ ∈ Subgroup.center (↥L ⧸ N) :=
      mem_center_thetaQuot_of_conj_eq_one hfL hfN hquot
    rw [hZ, Subgroup.mem_bot] at hc
    have hfNmem : (⟨f, hfL⟩ : ↥L) ∈ N := (QuotientGroup.eq_one_iff _).mp hc
    have hfO : (⟨f, hfL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := hθ ▸ hfNmem
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L)))
      ⟨⟨f, hfL⟩, hfO⟩
    rw [Subgroup.orderOf_mk (H := CFSG.pCore 2 ↥L) ⟨f, hfL⟩ hfO,
      Subgroup.orderOf_mk (H := L) f hfL, hf5] at hk
    rcases k with _ | k
    · norm_num at hk
    · have h2dvd : 2 ∣ 5 := hk ▸ dvd_pow_self 2 (Nat.succ_ne_zero k)
      norm_num at h2dvd
  obtain ⟨Ebar, hEbar_ea, hEbar_card⟩ := exists_elemAbelian_25_preimage hE25 hJ
  obtain ⟨F, hFL, hFea, hFcard, hFcent, hfnotF⟩ :=
    exists_elemAbelian_25_centralizer_of_preimage hfN hf5 hfnotL hθ hN hEbar_ea hEbar_card hquot
  by_contra hOne
  exact false_of_pCore_ne_bot
    (hS.toTheoremFourHyp.localRank_lt 5 Nat.prime_five (by norm_num))
    hfN hf5 hOne hFL hFea hFcard hFcent hfnotF


end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
