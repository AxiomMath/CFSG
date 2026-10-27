module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwoD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs11G
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

private theorem s15_Thirteen_subgroupOf_commutator_self {X : Type*} [Group X] (H : Subgroup X) :
    (⁅H, H⁆).subgroupOf H = ⁅(⊤ : Subgroup ↥H), ⊤⁆ := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← Subgroup.map_subtype_commutator H, ← _root_.commutator_def,
    Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private lemma s15_Thirteen_card_subgroupOf_of_le {A : Type*} [Group A] {E U : Subgroup A}
    (hU : U ≤ E) : Nat.card ↥(U.subgroupOf E) = Nat.card U := by
  rw [← Subgroup.card_subtype E (U.subgroupOf E), Subgroup.map_subgroupOf_eq_of_le hU]

private theorem s15_Thirteen_xbar_abstract {A : Type*} [Group A] [Finite A]
    {Mb E : Subgroup A} {ι : Type*} [Fintype ι] [Nonempty ι] (B : ι → Subgroup A)
    (hEle : E ≤ Mb) (hBle : ∀ i, B i ≤ E) (hEeq : E = ⨆ i, B i)
    (hcard : ∀ i, Nat.card (B i) = 3)
    (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ B i → y ∈ B j → Commute x y)
    (hind : iSupIndep B)
    (hEn : (E.subgroupOf Mb).Normal)
    (htrans : ∀ i j, ∃ q ∈ Mb, B j = (B i).map (MulAut.conj q).toMonoidHom) :
    ∃ N : Subgroup A, N ≤ Mb ∧ (∀ q ∈ Mb, ∀ x ∈ N, q * x * q⁻¹ ∈ N) ∧ IsElemAbelian 3 N ∧
      (∃ n, Fintype.card ι - 1 ≤ n ∧ Nat.card N = 3 ^ n) ∧ N ≤ ⁅Mb, Mb⁆ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommA : ∀ i j, i ≠ j → ∀ x y : A, x ∈ B i → y ∈ B j → Commute x y :=
    fun i j hij => hcomm hij
  let φ : (∀ i, B i) →* A := Subgroup.noncommPiCoprod (H := B) hcommA
  have hφinj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcommA) hind
  have hφrange : φ.range = E := by
    rw [hEeq]
    exact Subgroup.noncommPiCoprod_range (hcomm := hcommA)
  have hdom_comm : ∀ u v : (∀ i, B i), u * v = v * u := by
    intro u v
    funext i
    haveI : IsCyclic (B i) := isCyclic_of_prime_card (hcard i)
    exact mul_comm' (u i) (v i)
  have hE_ab : IsMulCommutative E := by
    refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
    have hx : (x : A) ∈ φ.range := by rw [hφrange]; exact x.2
    have hy : (y : A) ∈ φ.range := by rw [hφrange]; exact y.2
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hx
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 hy
    change (x : A) * (y : A) = (y : A) * (x : A)
    rw [← hu, ← hv, ← map_mul, ← map_mul, hdom_comm u v]
  have hE_exp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ φ.range := by rw [hφrange]; exact hx
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hx'
    have hu3 : u ^ 3 = 1 := by
      funext i
      have h := pow_card_eq_one' (x := u i)
      rwa [hcard i] at h
    rw [← hu, ← map_pow, hu3, map_one]
  have hE_el : IsElemAbelian 3 E := ⟨hE_ab, hE_exp⟩
  have hEcard : Nat.card E = 3 ^ Fintype.card ι := by
    have h1 : Nat.card (∀ i, B i) = Nat.card E := by
      rw [← hφrange]
      exact Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    calc Nat.card E = Nat.card (∀ i, B i) := h1.symm
      _ = ∏ i, Nat.card (B i) := Nat.card_pi
      _ = ∏ _i : ι, 3 := Finset.prod_congr rfl (fun i _ => hcard i)
      _ = 3 ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
  have hMb_norm : Mb ≤ Subgroup.normalizer (E : Set A) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEle).1 hEn
  have hNleE : ⁅E, Mb⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro e he m hm
    have hmem : m * e⁻¹ * m⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.1 (hMb_norm hm) e⁻¹).1 (E.inv_mem he)
    have heq : ⁅e, m⁆ = e * (m * e⁻¹ * m⁻¹) := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact E.mul_mem he hmem
  have hNnormal : ∀ q ∈ Mb, ∀ x ∈ ⁅E, Mb⁆, q * x * q⁻¹ ∈ ⁅E, Mb⁆ := by
    intro q hq x hx
    have hmem : q ∈ Subgroup.normalizer ((⁅E, Mb⁆ : Subgroup A) : Set A) :=
      Subgroup.normalizer_commutator_ge_right (H₁ := E) (H₂ := Mb) hq
    exact (Subgroup.mem_normalizer_iff.mp hmem x).mp hx
  have hNleMbMb : ⁅E, Mb⁆ ≤ ⁅Mb, Mb⁆ := Subgroup.commutator_mono hEle le_rfl
  have hN_el : IsElemAbelian 3 ⁅E, Mb⁆ := by
    refine ⟨?_, fun x hx => hE_exp x (hNleE hx)⟩
    refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
    change (x : A) * (y : A) = (y : A) * (x : A)
    exact congrArg Subtype.val
      (hE_ab.is_comm.comm ⟨x, hNleE x.2⟩ ⟨y, hNleE y.2⟩)
  have hN_isPGroup : IsPGroup 3 ↥⁅E, Mb⁆ := fun x =>
    ⟨1, by simpa using Subtype.ext (hN_el.2 x.1 x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN_isPGroup
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hBne : B i₀ ≠ ⊥ := by
    intro hbot
    have h := hcard i₀
    rw [hbot, Subgroup.card_bot] at h
    norm_num at h
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hbgen : Subgroup.zpowers b = B i₀ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB) ?_
    rw [Nat.card_zpowers, hcard i₀]
    have hdvd : orderOf b ∣ 3 := by
      rw [← hcard i₀]
      exact Subgroup.orderOf_dvd_natCard (B i₀) hbB
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h (orderOf_eq_one_iff.not.mpr (fun hb => hb1 (Subtype.ext hb)))
    · omega
  have hgen : ∀ i, B i ≤ ⁅E, Mb⁆ ⊔ Subgroup.zpowers b := by
    intro i
    obtain ⟨q, hq, hqB⟩ := htrans i₀ i
    rw [hqB]
    rw [show (B i₀).map (MulAut.conj q).toMonoidHom = Subgroup.zpowers (q * b * q⁻¹) by
      rw [← hbgen, MonoidHom.map_zpowers]; rfl]
    rw [Subgroup.zpowers_le]
    have hmem : ⁅q, b⁆ ∈ ⁅E, Mb⁆ := by
      have hmem : ⁅q, b⁆ ∈ ⁅Mb, E⁆ :=
        Subgroup.commutator_mem_commutator (H₁ := Mb) (H₂ := E) hq (hBle i₀ hbB)
      rwa [Subgroup.commutator_comm] at hmem
    have hqbz : q * b * q⁻¹ = ⁅q, b⁆ * b := by
      rw [commutatorElement_def]; group
    rw [hqbz]
    exact (⁅E, Mb⁆ ⊔ Subgroup.zpowers b).mul_mem (Subgroup.mem_sup_left hmem)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hE_eq_sup : E = ⁅E, Mb⁆ ⊔ Subgroup.zpowers b := by
    refine le_antisymm ?_ (sup_le hNleE (Subgroup.zpowers_le.mpr (hBle i₀ hbB)))
    calc E = ⨆ i, B i := hEeq
      _ ≤ ⁅E, Mb⁆ ⊔ Subgroup.zpowers b := iSup_le hgen
  have hN_le : Nat.card E ≤ Nat.card ↥⁅E, Mb⁆ * 3 := by
    haveI : IsMulCommutative ↥E := hE_ab
    have hzle : Subgroup.zpowers b ≤ E := Subgroup.zpowers_le.mpr (hBle i₀ hbB)
    have hcard_sup := card_sup_mul_card_inf ((⁅E, Mb⁆).subgroupOf E)
      ((Subgroup.zpowers b).subgroupOf E)
    have hsupE : (⁅E, Mb⁆).subgroupOf E ⊔ (Subgroup.zpowers b).subgroupOf E = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNleE hzle, hE_eq_sup.symm, Subgroup.subgroupOf_self]
    rw [hsupE, Subgroup.card_top, s15_Thirteen_card_subgroupOf_of_le hNleE,
      s15_Thirteen_card_subgroupOf_of_le hzle, Nat.card_zpowers] at hcard_sup
    have hb3 : orderOf b = 3 := by
      have hdvd : orderOf b ∣ 3 := by
        rw [← hcard i₀]
        exact Subgroup.orderOf_dvd_natCard (B i₀) hbB
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h (orderOf_eq_one_iff.not.mpr (fun hb => hb1 (Subtype.ext hb)))
      · exact h
    rw [hb3] at hcard_sup
    calc Nat.card E = Nat.card E * 1 := (mul_one _).symm
      _ ≤ Nat.card E * Nat.card ↥((⁅E, Mb⁆).subgroupOf E ⊓
            (Subgroup.zpowers b).subgroupOf E) := Nat.mul_le_mul_left _ Nat.card_pos
      _ = Nat.card ↥⁅E, Mb⁆ * 3 := hcard_sup
  have hn_bound : Fintype.card ι - 1 ≤ n := by
    have h1 : 3 ^ Fintype.card ι ≤ 3 ^ (n + 1) := by
      calc 3 ^ Fintype.card ι = Nat.card E := hEcard.symm
        _ ≤ Nat.card ↥⁅E, Mb⁆ * 3 := hN_le
        _ = 3 ^ n * 3 := by rw [hn]
        _ = 3 ^ (n + 1) := by rw [pow_succ]
    have h2 : Fintype.card ι ≤ n + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    omega
  exact ⟨⁅E, Mb⁆, hNleE.trans hEle, hNnormal, hN_el, ⟨n, hn_bound, hn⟩, hNleMbMb⟩

private noncomputable def psiBarK (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) : ↥D.M →* ↥(Mbar D.M V₀ V hV) :=
  ((actTil V₀ V hV).comp (Subgroup.inclusion hMs)).codRestrict _
    (fun m => by
      change actTil V₀ V hV ⟨(m : G), hMs m.2⟩ ∈ Mbar D.M V₀ V hV
      exact actTil_mem_barSub V₀ V hV m.2 (hMs m.2))

private theorem psiBarK_surjective (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) : Function.Surjective (psiBarK D hV hMs) := by
  intro y
  obtain ⟨g, hgM, hgy⟩ := (mem_barSub V₀ V hV D.M y).1 y.2
  refine ⟨⟨(g : G), hgM⟩, Subtype.ext ?_⟩
  show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = (y : MulAut (Vtil V₀ V hV))
  rw [show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = actTil V₀ V hV g from
    congrArg (actTil V₀ V hV) (Subtype.ext rfl)]
  exact hgy

private theorem psiBarK_ker (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) :
    (psiBarK D hV hMs).ker = (F11.CTilde D.M V₀ V).subgroupOf D.M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    mem_cTilde_iff hV (hMs.trans (stabTil_le_normalizer V₀ V))]
  constructor
  · intro hm
    refine ⟨m.2, hMs m.2, ?_⟩
    have h2 := congrArg Subtype.val hm
    change actTil V₀ V hV (Subgroup.inclusion hMs m) = 1 at h2
    rwa [show Subgroup.inclusion hMs m = (⟨(m : G), hMs m.2⟩ : stabTil V₀ V) from
      Subtype.ext rfl] at h2
  · rintro ⟨-, hst, hact⟩
    apply Subtype.ext
    show actTil V₀ V hV ⟨(m : G), hMs m.2⟩ = 1
    rw [show (⟨(m : G), hMs m.2⟩ : stabTil V₀ V) = ⟨(m : G), hst⟩ from Subtype.ext rfl]
    exact hact

private noncomputable def phiK (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    F11.MBar11 D.M V₀ V ≃* ↥(Mbar D.M V₀ V hV) :=
  QuotientGroup.liftEquiv ((F11.CTilde D.M V₀ V).subgroupOf D.M)
    (psiBarK_surjective D hV hMs) (psiBarK_ker D hV hMs).symm

private theorem s15_Thirteen_isElemAbelian_map {A B : Type*} [Group A] [Group B]
    {N : Subgroup A} (hN : IsElemAbelian 3 N) (e : A ≃* B) :
    IsElemAbelian 3 (N.map e.toMonoidHom) := by
  constructor
  · refine IsMulCommutative.of_comm fun x y => ?_
    obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    apply Subtype.ext
    show (x : B) * y = y * x
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hN.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · rintro x ⟨a, ha, hax⟩
    rw [← hax, ← map_pow, hN.2 a ha, map_one]

private theorem s15_Thirteen_isElemAbelian_comap {A B : Type*} [Group A] [Group B]
    {K : Subgroup B} (hK : IsElemAbelian 3 K) (f : A →* B) (hf : Function.Injective f) :
    IsElemAbelian 3 (K.comap f) := by
  constructor
  · refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
    apply hf
    show f ((x : A) * (y : A)) = f ((y : A) * (x : A))
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hK.1.is_comm.comm ⟨f x, x.2⟩ ⟨f y, y.2⟩)
  · intro x hx
    apply hf
    show f ((x : A) ^ 3) = f 1
    rw [map_pow, map_one]
    exact hK.2 (f x) hx

private theorem s15_Thirteen_k_eq_one_of_three_mem' (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h3 : 3 ∈ D.sig) : D.k = 1 := by
  have hsp := hSg.sig1_sp 3 (h1219 ▸ h3)
  unfold Data.k RankThreeUC.kParam
  rw [if_pos hsp]

theorem s15_Thirteen_exists_xbar (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hγ : gamma15 D.M V₀ V hV L = 2) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    ∃ n : ℕ, s15 D.M V₀ V hV L - 1 ≤ n ∧ ∃ Xbar : Subgroup (F11.MBar11 D.M V₀ V),
      Xbar.Normal ∧ IsElemAbelian 3 Xbar ∧ Nat.card Xbar = 3 ^ n ∧
      Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
  classical
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hcardL : Nat.card ↥(barSub V₀ V hV L) = 3 :=
    s15_TwoD_card_eq_three D h1217 h hV hL hγ
  let B : D.M → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun m => barSub V₀ V hV (conjSubgroup L (m : G))
  let Wtil : D.M → Subgroup (Vtil V₀ V hV) :=
    fun m => wTil V₀ V hV (conjSubgroup L (m : G))
  have hBcard : ∀ m : D.M, Nat.card (B m) = 3 := by
    intro m
    rw [show B m = barSub V₀ V hV (conjSubgroup L (m : G)) from rfl,
      s15_Infra_barSub_conjSubgroup V₀ V hV (hMs m.2) L,
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact hcardL
  have hBcomm : ∀ m m' : D.M, B m ≠ B m' → ∀ x y, x ∈ B m → y ∈ B m' → Commute x y := by
    intro m m' hne x y hx hy
    have hne' : (m' : G) * (m : G)⁻¹ ∉ nBar D.M V₀ V hV L := fun hmem =>
      hne ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV m.2 m'.2).1 hmem).symm
    have hc := (s15_Kbar_commute_conj h m.2 m'.2 hne').1
    have hmem : ⁅x, y⁆ ∈ ⁅B m, B m'⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hc, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  have hWtil_eq : ∀ {m m' : D.M}, B m = B m' → Wtil m = Wtil m' := by
    intro m m' h
    change commSub ⊤ (B m) = commSub ⊤ (B m')
    rw [h]
  have hWtil_triv : ∀ m m' : D.M, B m ≠ B m' → B m' ≤ centSub (Wtil m) := by
    intro m m' hne
    have hne' : (m' : G) * (m : G)⁻¹ ∉ nBar D.M V₀ V hV L := fun hmem =>
      hne ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV m.2 m'.2).1 hmem).symm
    have hc := (s15_Kbar_commute_conj h m.2 m'.2 hne').2
    rw [commSub_eq_bot_iff] at hc
    intro g hg w hw
    exact mem_fixV.mp (hc hw) g hg
  have hsSupIndep : sSupIndep (Set.range B) := by
    intro U hU
    rw [disjoint_iff]
    obtain ⟨m₀, rfl⟩ := hU
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxY : x ∈ sSup (Set.range B \ {B m₀}) := (Subgroup.mem_inf.mp hx).2
    have hxU : x ∈ B m₀ := (Subgroup.mem_inf.mp hx).1
    have hfix₀ : Wtil m₀ ≤ fixV (Subgroup.zpowers x) := by
      have hYle : sSup (Set.range B \ {B m₀}) ≤ centSub (Wtil m₀) := by
        apply sSup_le
        rintro V ⟨⟨m, rfl⟩, hVne⟩
        exact hWtil_triv m₀ m (fun h => hVne h.symm)
      have hxcent : x ∈ centSub (Wtil m₀) := hYle hxY
      intro w hw
      rw [mem_fixV_zpowers]
      exact (mem_centSub.mp hxcent) w hw
    have hfix : ∀ m : D.M, Wtil m ≤ fixV (Subgroup.zpowers x) := by
      intro m
      by_cases hm : B m = B m₀
      · rw [hWtil_eq hm]; exact hfix₀
      · have hle : B m₀ ≤ centSub (Wtil m) := hWtil_triv m m₀ hm
        have hxcent : x ∈ centSub (Wtil m) := hle hxU
        intro w hw
        rw [mem_fixV_zpowers]
        exact (mem_centSub.mp hxcent) w hw
    have htop : (⊤ : Subgroup (Vtil V₀ V hV)) ≤ fixV (Subgroup.zpowers x) := by
      rw [← s15_Two_iSup_commSub_eq_top D h1217 h hL]
      exact iSup_le hfix
    apply MulEquiv.ext
    intro v
    have hv : v ∈ fixV (Subgroup.zpowers x) := htop (Subgroup.mem_top v)
    rwa [mem_fixV_zpowers] at hv
  let B' : ↥(Set.range B) → Subgroup (MulAut (Vtil V₀ V hV)) := fun i => (i : Subgroup _)
  have hEsSup : (⨆ m : D.M, B m) = sSup (Set.range B) := (sSup_range (f := B)).symm
  have hBle' : ∀ i : ↥(Set.range B), B' i ≤ (⨆ m : D.M, B m) := by
    intro i
    rw [hEsSup]
    exact le_sSup i.2
  have hEeq' : (⨆ m : D.M, B m) = ⨆ i : ↥(Set.range B), B' i := by
    rw [hEsSup, sSup_eq_iSup']
  have hcard' : ∀ i : ↥(Set.range B), Nat.card (B' i) = 3 := by
    intro i
    obtain ⟨m, hm⟩ := i.2
    rw [show B' i = B m from hm.symm]
    exact hBcard m
  have hcomm' : Pairwise fun i j : ↥(Set.range B) =>
      ∀ x y, x ∈ B' i → y ∈ B' j → Commute x y := by
    intro i j hij x y hx hy
    obtain ⟨m, hm⟩ := i.2
    obtain ⟨m', hm'⟩ := j.2
    refine hBcomm m m' ?_ x y ?_ ?_
    · intro h
      exact hij (Subtype.ext (by rw [← hm, ← hm', h]))
    · change x ∈ (i : Subgroup _) at hx
      rwa [← hm] at hx
    · change y ∈ (j : Subgroup _) at hy
      rwa [← hm'] at hy
  have hind' : iSupIndep B' := (sSupIndep_iff (Set.range B)).1 hsSupIndep
  have htrans' : ∀ i j : ↥(Set.range B), ∃ q ∈ Mbar D.M V₀ V hV,
      B' j = (B' i).map (MulAut.conj q).toMonoidHom := by
    intro i j
    obtain ⟨m, hm⟩ := i.2
    obtain ⟨m', hm'⟩ := j.2
    refine ⟨(actTil V₀ V hV ⟨(m' : G), hMs m'.2⟩)⁻¹ *
      actTil V₀ V hV ⟨(m : G), hMs m.2⟩, ?_, ?_⟩
    · exact (Mbar D.M V₀ V hV).mul_mem ((Mbar D.M V₀ V hV).inv_mem
        (actTil_mem_barSub V₀ V hV m'.2 (hMs m'.2)))
        (actTil_mem_barSub V₀ V hV m.2 (hMs m.2))
    · have hj : B' j = B m' := hm'.symm
      have hi : B' i = B m := hm.symm
      rw [hj, hi]
      change barSub V₀ V hV (conjSubgroup L (m' : G)) =
        (barSub V₀ V hV (conjSubgroup L (m : G))).map
          (MulAut.conj ((actTil V₀ V hV ⟨(m' : G), hMs m'.2⟩)⁻¹ *
            actTil V₀ V hV ⟨(m : G), hMs m.2⟩)).toMonoidHom
      rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs m'.2) L,
        s15_Infra_barSub_conjSubgroup V₀ V hV (hMs m.2) L, Subgroup.map_map]
      congr 1
      ext φ
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  haveI : Fintype ↥(Set.range B) := (Set.finite_range B).fintype
  haveI : Nonempty ↥(Set.range B) := ⟨⟨B 1, Set.mem_range.mpr ⟨1, rfl⟩⟩⟩
  obtain ⟨N, hNle, hNnormal, hN_el, ⟨n, hn_bound, hNcard⟩, hNc⟩ :=
    s15_Thirteen_xbar_abstract (A := MulAut (Vtil V₀ V hV))
      (Mb := Mbar D.M V₀ V hV) (E := ⨆ m : D.M, B m) (B := B')
      (s15_Infra_iSup_barSub_le h) hBle' hEeq' hcard' hcomm' hind'
      (s15_Infra_iSup_barSub_normal h) htrans'
  have hιcard : Fintype.card (↥(Set.range B)) = s15 D.M V₀ V hV L := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, s15_Core_s15_eq_ncard_range h]
  have hsn : s15 D.M V₀ V hV L - 1 ≤ n := by
    rw [← hιcard]; exact hn_bound
  let Φ := phiK D hV hMs
  let Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    (N.subgroupOf (Mbar D.M V₀ V hV)).map Φ.symm.toMonoidHom
  have hNsub : (N.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    refine ⟨fun x hx q => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      hNnormal (q : MulAut (Vtil V₀ V hV)) q.2 (x : MulAut (Vtil V₀ V hV)) hx
  have hXnorm : Xbar.Normal := hNsub.map Φ.symm.toMonoidHom Φ.symm.surjective
  have hXcard : Nat.card Xbar = 3 ^ n := by
    rw [show Xbar = _ from rfl, Subgroup.card_map_of_injective Φ.symm.injective,
      s15_Thirteen_card_subgroupOf_of_le hNle, hNcard]
  have hN_el' : IsElemAbelian 3 (N.subgroupOf (Mbar D.M V₀ V hV)) :=
    s15_Thirteen_isElemAbelian_comap hN_el (Mbar D.M V₀ V hV).subtype
      (Subgroup.subtype_injective _)
  have hXel : IsElemAbelian 3 Xbar := by
    rw [show Xbar = _ from rfl]
    exact s15_Thirteen_isElemAbelian_map hN_el' Φ.symm
  have hmapc : (⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)),
      (⊤ : Subgroup (F11.MBar11 D.M V₀ V))⁆).map Φ.toMonoidHom =
      ⁅(⊤ : Subgroup ↥(Mbar D.M V₀ V hV)), (⊤ : Subgroup ↥(Mbar D.M V₀ V hV))⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top]
    have hrange : Φ.toMonoidHom.range = (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) :=
      MonoidHom.range_eq_top.mpr Φ.surjective
    rw [hrange]
  have hXc : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)),
      (⊤ : Subgroup (F11.MBar11 D.M V₀ V))⁆ := by
    have h1 : Xbar.map Φ.toMonoidHom ≤
        ⁅(⊤ : Subgroup ↥(Mbar D.M V₀ V hV)), (⊤ : Subgroup ↥(Mbar D.M V₀ V hV))⁆ := by
      rw [show Xbar = _ from rfl, Subgroup.map_map]
      have hcomp : Φ.toMonoidHom.comp Φ.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
      rw [hcomp, Subgroup.map_id, ← s15_Thirteen_subgroupOf_commutator_self (Mbar D.M V₀ V hV)]
      exact fun z hz => hNc (Subgroup.mem_subgroupOf.mp hz)
    intro x hx
    have hxmap : Φ x ∈ Xbar.map Φ.toMonoidHom := ⟨x, hx, rfl⟩
    have hxcomm : Φ x ∈ ⁅(⊤ : Subgroup ↥(Mbar D.M V₀ V hV)),
        (⊤ : Subgroup ↥(Mbar D.M V₀ V hV))⁆ := h1 hxmap
    rw [← hmapc] at hxcomm
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxcomm
    rwa [Φ.injective hyx] at hy
  exact ⟨n, hsn, Xbar, hXnorm, hXel, hXcard, hXc⟩

theorem s15_Thirteen_k_of_large_s (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h1217 : R1217 D) (h1110 : R1110G D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hγ : gamma15 D.M V₀ V hV L = 2)
    (hs : 7 ≤ s15 D.M V₀ V hV L) : D.k = 1 := by
  classical
  have hpf := h.hyp151.hyp125.pairFacts
  haveI hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    WeakClosure81.cTilde_subgroupOf_normal hV hpf.le_normalizer hpf.le_normalizer₀
  obtain ⟨n, hsn, Xbar, hXnorm, hXel, hXcard, hXc⟩ :=
    s15_Thirteen_exists_xbar D h1217 h.hyp151 hV hL hγ
  have hn6 : 6 ≤ n := by omega
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp151.hyp125
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (F11.O2p 3 D.M)
  have hO2p_le : F11.O2p 3 D.M ≤ D.M := by
    rw [F11.O2p]
    exact Subgroup.map_subtype_le _
  have hPle : P ≤ D.M := by
    obtain ⟨Q, hQ⟩ := hP
    rw [← hQ]
    exact (Subgroup.map_subtype_le (Q : Subgroup ↥(F11.O2p 3 D.M))).trans hO2p_le
  have hBple : F11.barPreimage11 D.M V₀ V Xbar ≤ D.M := by
    rw [F11.barPreimage11]
    exact Subgroup.map_subtype_le _
  have hRle : P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar ≤ D.M :=
    (inf_le_left.trans inf_le_left).trans hPle
  have hOmega : F11.Omega1p 3 (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ≤
      D.M := by
    rw [F11.Omega1p]
    exact (Subgroup.closure_le D.M).mpr fun x hx => hRle hx.1
  have hkey := ((h1110 V₀ V hH11 3 Nat.prime_three (by norm_num) P hP).2.2 n
    (by omega) Xbar hXnorm hXel hXcard hXc).1.2.2.2
  have hle : CFSG.Open.pRank 3 (F11.Omega1p 3 (P ⊓ ⁅D.M, D.M⁆ ⊓
      F11.barPreimage11 D.M V₀ V Xbar)) ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.SectionRank.pRank_mono (by norm_num) hOmega
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := by
    have h3 : 3 ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by omega)
    exact le_trans (by omega : 4 ≤ n / 2 + 1) (le_trans hkey hle)
  exact s15_Thirteen_k_eq_one_of_three_mem' D hSg h1219
    (hSg.four_mem 3 Nat.prime_three (by norm_num) h4)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
