module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154R1110Sec
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycResChi_not_quasisimple_of_card_dvd_prime {X : Type*} [Group X]
    {p : ℕ} (hp : p.Prime) (h : Nat.card X ∣ p) : ¬ CFSG.Open.IsQuasisimple X := by
  intro hq
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic X := isCyclic_of_card_dvd_prime h
  have hsub : Subsingleton (X ⧸ Subgroup.center X) :=
    QuotientGroup.subsingleton_iff.mpr Subgroup.center_eq_top
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  exact not_nontrivial_iff_subsingleton.mpr hsub inferInstance

private theorem s16h_e3_CycResChi_prime_card_not_quasisimple {X : Type*} [Group X] {p : ℕ}
    (hp : p.Prime) (h : Nat.card X = p) : ¬ CFSG.Open.IsQuasisimple X :=
  s16h_e3_CycResChi_not_quasisimple_of_card_dvd_prime hp (by rw [h])

private theorem s16h_e3_CycResChi_conc4_133_of_prime_card {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ} (hp : p.Prime)
    (hL : Nat.card ↥L = p) (h : Conc4_136W A t L) : Conc4_133 A t L := by
  obtain ⟨-, -, hcases⟩ := h
  rcases hcases with h133 | ⟨K, hK, g, -, -, hKL, -⟩ | ⟨hcomp, -⟩ | ⟨-, -, hcomp, -⟩
  · exact h133
  · have hKle : K ≤ L := by rw [hKL]; exact le_sup_left
    have hdK : Nat.card ↥K ∣ p := by
      rw [← hL]
      exact Subgroup.card_dvd_of_le hKle
    exact absurd hK.2.2 (s16h_e3_CycResChi_not_quasisimple_of_card_dvd_prime hp hdK)
  · exact absurd hcomp.2.2 (s16h_e3_CycResChi_prime_card_not_quasisimple hp hL)
  · exact absurd hcomp.2.2 (s16h_e3_CycResChi_prime_card_not_quasisimple hp hL)

private theorem s16h_e3_CycResChi_card_of_elemAbelianRank {X : Type*} [Group X] {p n : ℕ}
    (h : CFSG.Quasithin.IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  calc Nat.card X = Nat.card (Multiplicative (Fin n → ZMod p)) := Nat.card_congr e.toEquiv
    _ = Nat.card (Fin n → ZMod p) := Nat.card_congr Multiplicative.toAdd
    _ = ∏ _i : Fin n, Nat.card (ZMod p) := Nat.card_pi
    _ = p ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Nat.card_zmod, Fintype.card_fin]

private theorem s16h_e3_CycResChi_prime_of_conc4_133 {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ} (hp : p.Prime)
    (hL : Nat.card ↥L = p) (h : Conc4_133 A t L) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  obtain ⟨q, -, -, -, -, hrows⟩ := h
  rcases hrows with ⟨hcyc, -⟩ | ⟨hcyc, -⟩ | ⟨hP, -⟩ | ⟨hE, -⟩ | ⟨hcyc, -⟩ |
    ⟨r, m, -, hr2, hE, -, -⟩ | ⟨hE, -⟩
  · exact Or.inl (hL.symm.trans hcyc.2)
  · exact Or.inr (Or.inl (hL.symm.trans hcyc.2))
  · exfalso
    have h27 : p = 27 := hL.symm.trans hP.2.1
    rw [h27] at hp
    norm_num at hp
  · exfalso
    have h9 : p = 9 := hL.symm.trans (s16h_e3_CycResChi_card_of_elemAbelianRank hE)
    rw [h9] at hp
    norm_num at hp
  · exact Or.inr (Or.inr (hL.symm.trans hcyc.2))
  · exfalso
    have hqp : q ^ r = p := (s16h_e3_CycResChi_card_of_elemAbelianRank hE).symm.trans hL
    have hr1 : r = 1 := (hp.pow_eq_iff.mp hqp).2
    omega
  · exfalso
    have h9 : p = 9 := hL.symm.trans (s16h_e3_CycResChi_card_of_elemAbelianRank hE)
    rw [h9] at hp
    norm_num at hp

private theorem s16h_e3_CycResChi_subgroupOf_commutator_self {X : Type*} [Group X]
    (H : Subgroup X) : (⁅H, H⁆).subgroupOf H = ⁅(⊤ : Subgroup ↥H), ⊤⁆ := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← Subgroup.map_subtype_commutator H, ← _root_.commutator_def,
    Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private lemma s16h_e3_CycResChi_card_subgroupOf_of_le {A : Type*} [Group A] {E U : Subgroup A}
    (hU : U ≤ E) : Nat.card ↥(U.subgroupOf E) = Nat.card U := by
  rw [← Subgroup.card_subtype E (U.subgroupOf E), Subgroup.map_subgroupOf_eq_of_le hU]

private theorem s16h_e3_CycResChi_xbar_abstract {A : Type*} [Group A] [Finite A]
    {Mb E : Subgroup A} {ι : Type*} [Fintype ι] [Nonempty ι] {p : ℕ} (hp : p.Prime)
    (B : ι → Subgroup A)
    (hEle : E ≤ Mb) (hBle : ∀ i, B i ≤ E) (hEeq : E = ⨆ i, B i)
    (hcard : ∀ i, Nat.card (B i) = p)
    (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ B i → y ∈ B j → Commute x y)
    (hind : iSupIndep B)
    (hEn : (E.subgroupOf Mb).Normal)
    (htrans : ∀ i j, ∃ q ∈ Mb, B j = (B i).map (MulAut.conj q).toMonoidHom) :
    ∃ N : Subgroup A, N ≤ Mb ∧ (∀ q ∈ Mb, ∀ x ∈ N, q * x * q⁻¹ ∈ N) ∧ IsElemAbelian p N ∧
      (∃ n, Fintype.card ι - 1 ≤ n ∧ Nat.card N = p ^ n) ∧ N ≤ ⁅Mb, Mb⁆ := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
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
  have hE_exp : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    have hx' : x ∈ φ.range := by rw [hφrange]; exact hx
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hx'
    have hup : u ^ p = 1 := by
      funext i
      have h := pow_card_eq_one' (x := u i)
      rwa [hcard i] at h
    rw [← hu, ← map_pow, hup, map_one]
  have hE_el : IsElemAbelian p E := ⟨hE_ab, hE_exp⟩
  have hEcard : Nat.card E = p ^ Fintype.card ι := by
    have h1 : Nat.card (∀ i, B i) = Nat.card E := by
      rw [← hφrange]
      exact Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    calc Nat.card E = Nat.card (∀ i, B i) := h1.symm
      _ = ∏ i, Nat.card (B i) := Nat.card_pi
      _ = ∏ _i : ι, p := Finset.prod_congr rfl (fun i _ => hcard i)
      _ = p ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
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
  have hN_el : IsElemAbelian p ⁅E, Mb⁆ := by
    refine ⟨?_, fun x hx => hE_exp x (hNleE hx)⟩
    refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
    change (x : A) * (y : A) = (y : A) * (x : A)
    exact congrArg Subtype.val
      (hE_ab.is_comm.comm ⟨x, hNleE x.2⟩ ⟨y, hNleE y.2⟩)
  have hN_isPGroup : IsPGroup p ↥⁅E, Mb⁆ := fun x =>
    ⟨1, by simpa using Subtype.ext (hN_el.2 x.1 x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN_isPGroup
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hp2 : 2 ≤ p := hp.two_le
  have hBne : B i₀ ≠ ⊥ := by
    intro hbot
    have h := hcard i₀
    rw [hbot, Subgroup.card_bot] at h
    omega
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hbgen : Subgroup.zpowers b = B i₀ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB) ?_
    rw [Nat.card_zpowers, hcard i₀]
    have hdvd : orderOf b ∣ p := by
      rw [← hcard i₀]
      exact Subgroup.orderOf_dvd_natCard (B i₀) hbB
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
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
  have hN_le : Nat.card E ≤ Nat.card ↥⁅E, Mb⁆ * p := by
    haveI : IsMulCommutative ↥E := hE_ab
    have hzle : Subgroup.zpowers b ≤ E := Subgroup.zpowers_le.mpr (hBle i₀ hbB)
    have hcard_sup := card_sup_mul_card_inf ((⁅E, Mb⁆).subgroupOf E)
      ((Subgroup.zpowers b).subgroupOf E)
    have hsupE : (⁅E, Mb⁆).subgroupOf E ⊔ (Subgroup.zpowers b).subgroupOf E = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNleE hzle, hE_eq_sup.symm, Subgroup.subgroupOf_self]
    rw [hsupE, Subgroup.card_top,
      s16h_e3_CycResChi_card_subgroupOf_of_le hNleE,
      s16h_e3_CycResChi_card_subgroupOf_of_le hzle, Nat.card_zpowers] at hcard_sup
    have hbp : orderOf b = p := by
      have hdvd : orderOf b ∣ p := by
        rw [← hcard i₀]
        exact Subgroup.orderOf_dvd_natCard (B i₀) hbB
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd h (orderOf_eq_one_iff.not.mpr (fun hb => hb1 (Subtype.ext hb)))
      · exact h
    rw [hbp] at hcard_sup
    calc Nat.card E = Nat.card E * 1 := (mul_one _).symm
      _ ≤ Nat.card E * Nat.card ↥((⁅E, Mb⁆).subgroupOf E ⊓
            (Subgroup.zpowers b).subgroupOf E) := Nat.mul_le_mul_left _ Nat.card_pos
      _ = Nat.card ↥⁅E, Mb⁆ * p := hcard_sup
  have hn_bound : Fintype.card ι - 1 ≤ n := by
    have h1 : p ^ Fintype.card ι ≤ p ^ (n + 1) := by
      calc p ^ Fintype.card ι = Nat.card E := hEcard.symm
        _ ≤ Nat.card ↥⁅E, Mb⁆ * p := hN_le
        _ = p ^ n * p := by rw [hn]
        _ = p ^ (n + 1) := by rw [pow_succ]
    have h2 : Fintype.card ι ≤ n + 1 :=
      (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega
  exact ⟨⁅E, Mb⁆, hNleE.trans hEle, hNnormal, hN_el, ⟨n, hn_bound, hn⟩, hNleMbMb⟩

private noncomputable def s16h_e3_CycResChi_psiBarK (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V) :
    ↥D.M →* ↥(Mbar D.M V₀ V hV) :=
  ((actTil V₀ V hV).comp (Subgroup.inclusion hMs)).codRestrict _
    (fun m => by
      change actTil V₀ V hV ⟨(m : G), hMs m.2⟩ ∈ Mbar D.M V₀ V hV
      exact actTil_mem_barSub V₀ V hV m.2 (hMs m.2))

private theorem s16h_e3_CycResChi_psiBarK_surjective (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V) :
    Function.Surjective (s16h_e3_CycResChi_psiBarK D hV hMs) := by
  intro y
  obtain ⟨g, hgM, hgy⟩ := (mem_barSub V₀ V hV D.M y).1 y.2
  refine ⟨⟨(g : G), hgM⟩, Subtype.ext ?_⟩
  show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = (y : MulAut (Vtil V₀ V hV))
  rw [show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = actTil V₀ V hV g from
    congrArg (actTil V₀ V hV) (Subtype.ext rfl)]
  exact hgy

private theorem s16h_e3_CycResChi_psiBarK_ker (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V) :
    (s16h_e3_CycResChi_psiBarK D hV hMs).ker =
      (F11.CTilde D.M V₀ V).subgroupOf D.M := by
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

private noncomputable def s16h_e3_CycResChi_phiK (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    F11.MBar11 D.M V₀ V ≃* ↥(Mbar D.M V₀ V hV) :=
  QuotientGroup.liftEquiv ((F11.CTilde D.M V₀ V).subgroupOf D.M)
    (s16h_e3_CycResChi_psiBarK_surjective D hV hMs)
    (s16h_e3_CycResChi_psiBarK_ker D hV hMs).symm

private theorem s16h_e3_CycResChi_isElemAbelian_map {A B : Type*} [Group A] [Group B]
    {p : ℕ} {N : Subgroup A} (hN : IsElemAbelian p N) (e : A ≃* B) :
    IsElemAbelian p (N.map e.toMonoidHom) := by
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

private theorem s16h_e3_CycResChi_isElemAbelian_comap {A B : Type*} [Group A] [Group B]
    {p : ℕ} {K : Subgroup B} (hK : IsElemAbelian p K) (f : A →* B) (hf : Function.Injective f) :
    IsElemAbelian p (K.comap f) := by
  constructor
  · refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
    apply hf
    show f ((x : A) * (y : A)) = f ((y : A) * (x : A))
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hK.1.is_comm.comm ⟨f x, x.2⟩ ⟨f y, y.2⟩)
  · intro x hx
    apply hf
    show f ((x : A) ^ p) = f 1
    rw [map_pow, map_one]
    exact hK.2 (f x) hx

private theorem s16h_e3_CycResChi_iSup_wTil_eq_top {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) {t : MulAut (Vtil V₀ V h.isElemAbelian)}
    (hconc : Conc4_136W (Mbar D.M V₀ V h.isElemAbelian) t
      (barSub V₀ V h.isElemAbelian L)) :
    ⨆ m : D.M, commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
      (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) = ⊤ := by
  classical
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hW : ∀ m : D.M, commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
      (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) =
      (commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
        (barSub V₀ V h.isElemAbelian L)).map
        ((actTil V₀ V h.isElemAbelian ⟨m, hMs m.2⟩)⁻¹).toMonoidHom := by
    intro m
    have hα := s15_Kbar_commSub_map_conj (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
      (barSub V₀ V h.isElemAbelian L) (actTil V₀ V h.isElemAbelian ⟨m, hMs m.2⟩)⁻¹
    have htop : (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian)).map
        ((actTil V₀ V h.isElemAbelian ⟨m, hMs m.2⟩)⁻¹).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (by
        intro x
        exact ⟨(actTil V₀ V h.isElemAbelian ⟨m, hMs m.2⟩) x, by simp⟩)
    rw [htop] at hα
    rw [← hα, s15_Infra_barSub_conjSubgroup V₀ V h.isElemAbelian (hMs m.2) L]
  have hle : (⨆ X ∈ conjSubs (Mbar D.M V₀ V h.isElemAbelian)
      (commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
        (barSub V₀ V h.isElemAbelian L)), X) ≤
      ⨆ m : D.M, commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
        (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) := by
    refine iSup₂_le fun X hX => ?_
    obtain ⟨g, hgA, rfl⟩ := hX
    obtain ⟨m, hmM, hmg⟩ := (mem_barSub V₀ V h.isElemAbelian D.M g).1 hgA
    let m' : D.M := ⟨(m : G), hmM⟩
    have h2 : ((actTil V₀ V h.isElemAbelian
        ⟨(((m'⁻¹ : D.M) : G)), hMs (D.M.inv_mem m'.2)⟩)⁻¹).toMonoidHom = g.toMonoidHom := by
      apply congrArg MulEquiv.toMonoidHom
      have helem : (⟨((m'⁻¹ : D.M) : G), hMs (D.M.inv_mem m'.2)⟩ : stabTil V₀ V) =
          (⟨(m' : G), hMs m'.2⟩ : stabTil V₀ V)⁻¹ := Subtype.ext rfl
      rw [helem, map_inv, inv_inv]
      simpa [m'] using hmg
    calc (commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
          (barSub V₀ V h.isElemAbelian L)).map g.toMonoidHom
        = (commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
            (barSub V₀ V h.isElemAbelian L)).map
            ((actTil V₀ V h.isElemAbelian
              ⟨(((m'⁻¹ : D.M) : G)), hMs (D.M.inv_mem m'.2)⟩)⁻¹).toMonoidHom := by
          rw [h2]
      _ = commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
            (barSub V₀ V h.isElemAbelian (conjSubgroup L (((m'⁻¹ : D.M) : G)))) := by
          rw [hW (m'⁻¹)]
      _ ≤ ⨆ m : D.M, commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
            (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) :=
          le_iSup (fun m : D.M => commSub (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian))
            (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G)))) (m'⁻¹)
  exact le_antisymm le_top (hconc.1.symm.trans_le hle)

private theorem s16h_e3_CycResChi_exists_xbar (D : Data G) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    ∃ n : ℕ, s15 D.M V₀ V h.hyp151.isElemAbelian L - 1 ≤ n ∧
      ∃ Xbar : Subgroup (F11.MBar11 D.M V₀ V),
        Xbar.Normal ∧ IsElemAbelian p Xbar ∧ Nat.card Xbar = p ^ n ∧
        Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
  classical
  have hV := h.hyp151.isElemAbelian
  have hpf := h.hyp151.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  obtain ⟨t, -, -, -, -, hWconc⟩ := hc
  have hspan := s16h_e3_CycResChi_iSup_wTil_eq_top h.hyp151 hWconc
  let B : D.M → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun m => barSub V₀ V hV (conjSubgroup L (m : G))
  let Wtil : D.M → Subgroup (Vtil V₀ V hV) :=
    fun m => commSub ⊤ (B m)
  have hcardL : Nat.card ↥(barSub V₀ V hV L) = p := hLp.2
  have hBcard : ∀ m : D.M, Nat.card (B m) = p := by
    intro m
    rw [show B m = barSub V₀ V hV (conjSubgroup L (m : G)) from rfl,
      s15_Infra_barSub_conjSubgroup V₀ V hV (hMs m.2) L,
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact hcardL
  have hBcomm : ∀ m m' : D.M, B m ≠ B m' → ∀ x y, x ∈ B m → y ∈ B m' → Commute x y := by
    intro m m' hne x y hx hy
    have hne' : (m' : G) * (m : G)⁻¹ ∉ nBar D.M V₀ V hV L := fun hmem =>
      hne ((s15_Infra_mul_inv_mem_nBar_iff h.hyp151.hyp125 hV m.2 m'.2).1 hmem).symm
    have hc := (s15_Kbar_commute_conj h.hyp151 m.2 m'.2 hne').1
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
      hne ((s15_Infra_mul_inv_mem_nBar_iff h.hyp151.hyp125 hV m.2 m'.2).1 hmem).symm
    have hc := (s15_Kbar_commute_conj h.hyp151 m.2 m'.2 hne').2
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
    have hYle : sSup (Set.range B \ {B m₀}) ≤ centSub (Wtil m₀) := by
      apply sSup_le
      rintro X ⟨⟨m, rfl⟩, hXne⟩
      exact hWtil_triv m₀ m (fun hh => hXne hh.symm)
    have hcent₀ : x ∈ centSub (Wtil m₀) := hYle hxY
    have hfix : ∀ m : D.M, Wtil m ≤ fixV (Subgroup.zpowers x) := by
      intro m
      by_cases hm : B m = B m₀
      · rw [hWtil_eq hm]
        intro w hw
        rw [mem_fixV_zpowers]
        exact (mem_centSub.mp hcent₀) w hw
      · have hle : B m₀ ≤ centSub (Wtil m) := hWtil_triv m m₀ hm
        have hxcent : x ∈ centSub (Wtil m) := hle hxU
        intro w hw
        rw [mem_fixV_zpowers]
        exact (mem_centSub.mp hxcent) w hw
    have htop : (⊤ : Subgroup (Vtil V₀ V hV)) ≤ fixV (Subgroup.zpowers x) := by
      rw [← hspan]
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
  have hcard' : ∀ i : ↥(Set.range B), Nat.card (B' i) = p := by
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
    s16h_e3_CycResChi_xbar_abstract (A := MulAut (Vtil V₀ V hV))
      (Mb := Mbar D.M V₀ V hV) (E := ⨆ m : D.M, B m) (B := B') hp
      (s15_Infra_iSup_barSub_le h.hyp151) hBle' hEeq' hcard' hcomm' hind'
      (s15_Infra_iSup_barSub_normal h.hyp151) htrans'
  have hιcard : Fintype.card (↥(Set.range B)) = s15 D.M V₀ V hV L := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, s15_Core_s15_eq_ncard_range h.hyp151]
  have hsn : s15 D.M V₀ V hV L - 1 ≤ n := by
    rw [← hιcard]; exact hn_bound
  let Φ := s16h_e3_CycResChi_phiK D hV hMs
  let Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    (N.subgroupOf (Mbar D.M V₀ V hV)).map Φ.symm.toMonoidHom
  have hNsub : (N.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    refine ⟨fun x hx q => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      hNnormal (q : MulAut (Vtil V₀ V hV)) q.2 (x : MulAut (Vtil V₀ V hV)) hx
  have hXnorm : Xbar.Normal := hNsub.map Φ.symm.toMonoidHom Φ.symm.surjective
  have hXcard : Nat.card Xbar = p ^ n := by
    rw [show Xbar = _ from rfl, Subgroup.card_map_of_injective Φ.symm.injective,
      s16h_e3_CycResChi_card_subgroupOf_of_le hNle, hNcard]
  have hN_el' : IsElemAbelian p (N.subgroupOf (Mbar D.M V₀ V hV)) :=
    s16h_e3_CycResChi_isElemAbelian_comap hN_el (Mbar D.M V₀ V hV).subtype
      (Subgroup.subtype_injective _)
  have hXel : IsElemAbelian p Xbar := by
    rw [show Xbar = _ from rfl]
    exact s16h_e3_CycResChi_isElemAbelian_map hN_el' Φ.symm
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
      rw [hcomp, Subgroup.map_id,
        ← s16h_e3_CycResChi_subgroupOf_commutator_self (Mbar D.M V₀ V hV)]
      exact fun z hz => hNc (Subgroup.mem_subgroupOf.mp hz)
    intro x hx
    have hxmap : Φ x ∈ Xbar.map Φ.toMonoidHom := ⟨x, hx, rfl⟩
    have hxcomm : Φ x ∈ ⁅(⊤ : Subgroup ↥(Mbar D.M V₀ V hV)),
        (⊤ : Subgroup ↥(Mbar D.M V₀ V hV))⁆ := h1 hxmap
    rw [← hmapc] at hxcomm
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxcomm
    rwa [Φ.injective hyx] at hy
  exact ⟨n, hsn, Xbar, hXnorm, hXel, hXcard, hXc⟩

theorem s16h_e3_cyclic_chi_resid
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    (hσG : SigmaThree D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L <
        gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hχ : ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n)
    (hpσ : p ∉ D.sig) (h3 : D.sig = {3})
    (hs6 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 6) :
    Hyp154 D V₀ V L ∨ Concl164 D V₀ V h.hyp151.isElemAbelian L := by
  have hV := h.hyp151.isElemAbelian
  have hc0 := hc
  obtain ⟨t, -, -, -, -, hWconc⟩ := hc
  have h133 : Conc4_133 (Mbar D.M V₀ V hV) t (barSub V₀ V hV L) :=
    s16h_e3_CycResChi_conc4_133_of_prime_card hp hLp.2 hWconc
  have hp3 : p ≠ 3 := fun e => hpσ (e ▸ (h3 ▸ Set.mem_singleton 3))
  have hp5 : 5 ≤ p := by
    rcases s16h_e3_CycResChi_prime_of_conc4_133 hp hLp.2 h133 with h | h | h <;> omega
  have hp2 : p ≠ 2 := by omega
  have hp3lt : 3 < p := by omega
  haveI hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    CFSG.LocalAnalysis.WeakClosure81.cTilde_subgroupOf_normal hV
      h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨n, hn, Xbar, hXn, hXe, hXcard, hXc⟩ :=
    s16h_e3_CycResChi_exists_xbar D h hc0 hp hLp
  have hn5 : 5 ≤ n := by omega
  have hCore : R1110Core D :=
    r1110Core_holds D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111 S.h112 S.hThin S.hCyc
  have h1110 : R1110G D :=
    r1110G_of_core_second D hCore
      (r1110Second_holds D S.hx S.hSig S.h61 S.h63 S.h77 hCore)
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 S.h127 h.hyp151.hyp125
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (F11.O2p p D.M)
  have hO2p_le : F11.O2p p D.M ≤ D.M := by
    rw [F11.O2p]
    exact Subgroup.map_subtype_le _
  have hPle : P ≤ D.M := by
    obtain ⟨Q, hQ⟩ := hP
    rw [← hQ]
    exact (Subgroup.map_subtype_le (Q : Subgroup ↥(F11.O2p p D.M))).trans hO2p_le
  have hkey := ((h1110 V₀ V hH11 p hp hp2 P hP).2.2 n (by omega) Xbar hXn hXe hXcard hXc).1.2.2.2
  have hOle : F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ≤ D.M := by
    rw [F11.Omega1p]
    refine (Subgroup.closure_le D.M).mpr ?_
    rintro x ⟨hx, -⟩
    exact (inf_le_left.trans inf_le_left).trans hPle hx
  have hle : CFSG.Open.pRank p (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓
      F11.barPreimage11 D.M V₀ V Xbar)) ≤ CFSG.Open.pRank p D.M :=
    CFSG.SectionRank.pRank_mono (by omega : 1 < p) hOle
  have hm3 : CFSG.Open.pRank 3 D.M = 3 :=
    s16h_pRank_eq_three D S hr3 (h3 ▸ Set.mem_singleton 3)
  have h2 : CFSG.Open.pRank p D.M ≤ 2 :=
    pRank_le_two_of_twoLocal D S.hx hσG h3 hm3 hp hp3lt D.maxLocal.1
  have h3le : 3 ≤ CFSG.Open.pRank p D.M := by
    have h3n : 3 ≤ n / 2 + 1 := by
      have : 2 ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by omega)
      omega
    exact h3n.trans (hkey.trans hle)
  exact absurd h2 (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
