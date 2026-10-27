module

public import CFSG.LocalAnalysis.StandardType.FS81.RowSplit
public import CFSG.LocalAnalysis.StandardType.FS81.CapE7
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthModels
import CFSG.LocalAnalysis.StandardType.FS81.SplitEAux
import CFSG.LocalAnalysis.StandardType.FS81.TwD7CentGen
import CFSG.LocalAnalysis.StandardType.FS81.TwD7CentDecomp
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelAut
import CFSG.LocalAnalysis.StandardType.FS81.S7Fusion
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem le_centralizer_of_normal_of_isSimple {G : Type} [Group G] [Finite G] {b₀ : G}
    {K R : Subgroup G} (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKs : IsSimpleGroup ↥K) (hK3 : 3 ∣ Nat.card K)
    (hRC : R ≤ Subgroup.centralizer ({b₀} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal) (hR3 : ¬ 3 ∣ Nat.card R) :
    R ≤ Subgroup.centralizer (K : Set G) := by
  have hRKn : ((R ⊓ K).subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxR, hxK⟩ := hx
    refine ⟨?_, K.mul_mem (K.mul_mem g.2 hxK) (K.inv_mem g.2)⟩
    have h := hRn.conj_mem ⟨x, hRC hxR⟩ (by rwa [Subgroup.mem_subgroupOf])
      ⟨(g : G), hKC g.2⟩
    rwa [Subgroup.mem_subgroupOf] at h
  have hbot : R ⊓ K = ⊥ := by
    have := hKs
    have := hRKn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ K).subgroupOf K) with h | h
    · have h' := Subgroup.subgroupOf_eq_bot.mp h
      rwa [disjoint_iff, inf_assoc, inf_idem] at h'
    · exfalso
      have hKR : K ≤ R := fun x hx => (Subgroup.subgroupOf_eq_top.mp h hx).1
      exact hR3 (hK3.trans (Subgroup.card_dvd_of_le hKR))
  rw [Subgroup.le_centralizer_iff]
  intro k hk r hr
  have hcomm : r * k * r⁻¹ * k⁻¹ ∈ R ⊓ K := by
    refine ⟨?_, ?_⟩
    · have h := hRn.conj_mem ⟨r⁻¹, hRC (R.inv_mem hr)⟩
        (by rw [Subgroup.mem_subgroupOf]; exact R.inv_mem hr) ⟨k, hKC hk⟩
      rw [Subgroup.mem_subgroupOf] at h
      have h' : r * (k * r⁻¹ * k⁻¹) ∈ R := R.mul_mem hr h
      simpa [mul_assoc] using h'
    · have h := hKn.conj_mem ⟨k, hKC hk⟩ (by rw [Subgroup.mem_subgroupOf]; exact hk)
        ⟨r, hRC hr⟩
      rw [Subgroup.mem_subgroupOf] at h
      exact K.mul_mem h (K.inv_mem hk)
  rw [hbot, Subgroup.mem_bot] at hcomm
  have h2 := congrArg (· * (k * r)) hcomm
  simpa [mul_assoc] using h2

theorem le_centralizer_of_isSimpleGroup_of_le_normalizer {G : Type} [Group G] {X R : Subgroup G}
    (hX : IsSimpleGroup ↥X) (hXN : X ≤ Subgroup.normalizer (R : Set G)) {x : G} (hxX : x ∈ X)
    (hxR : x ∈ Subgroup.centralizer (R : Set G)) (hx1 : x ≠ 1) :
    X ≤ Subgroup.centralizer (R : Set G) := by
  have hNn : ((Subgroup.centralizer (R : Set G)).subgroupOf X).Normal := by
    refine ⟨fun a ha y => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at ha ⊢
    intro r hr
    have hr' : (y : G)⁻¹ * r * (y : G)⁻¹⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXN y.2)) r).mp hr
    rw [inv_inv] at hr'
    have hc := ha _ hr'
    show r * ((y : G) * a * (y : G)⁻¹) = ((y : G) * a * (y : G)⁻¹) * r
    calc r * ((y : G) * a * (y : G)⁻¹)
        = (y : G) * (((y : G)⁻¹ * r * y) * a) * (y : G)⁻¹ := by group
      _ = (y : G) * (a * ((y : G)⁻¹ * r * y)) * (y : G)⁻¹ := by rw [hc]
      _ = ((y : G) * a * (y : G)⁻¹) * r := by group
  have := hX
  have := hNn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((Subgroup.centralizer (R : Set G)).subgroupOf X) with h | h
  · exfalso
    have hmem : (⟨x, hxX⟩ : ↥X) ∈ (Subgroup.centralizer (R : Set G)).subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      exact hxR
    rw [h, Subgroup.mem_bot] at hmem
    exact hx1 (congrArg Subtype.val hmem)
  · exact Subgroup.subgroupOf_eq_top.mp h

theorem exists_centralizer_eq_of_recOutTwD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) ∧
      (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R ∧
      Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K) := by
  classical
  obtain ⟨-, hHyp, hCanon⟩ := id hstd
  obtain ⟨hA, hEmax, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, hKn, hKz, -, hcyc, -, -⟩ := hA
  obtain ⟨hRow, -, hsup, hmax, hE1card, hself⟩ := hCanon
  obtain ⟨hKs, -⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hRow hKz
  have hdisj : Disjoint (Subgroup.zpowers b₀) K := disjoint_zpowers_of_center hKC hKz
  have hout := centralizer_eq_sup_of_recOutTwD7 hstd hB hrec
  have hKN : Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    have hA3 : IsPGroup 3 ↥(E ⊓ K) :=
      CFSG.StandardType.TableB.isPGroup_of_isElemAbelian hmax.2.1
    have hAnc : ¬ IsCyclic ↥(E ⊓ K) := by
      refine CFSG.StandardType.TableB.not_isCyclic_of_card (p := 3) (by norm_num) hmax.2.1.2 ?_
      rw [hE1card]
      show 9 ≤ 3 ^ 7
      norm_num
    exact normalizer_zpowers_le_normalizer hKs hKC hKn hcyc (A := E ⊓ K) inf_le_right hA3 hAnc
  have hN : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    intro hle
    set e : Coords (Row.twD7.n + 1) := Pi.single 1 1 + Pi.single 2 1 with he
    have he0 : e ≠ 0 := fun h0 => by
      have := congrFun h0 1
      simp [he] at this
    have hwt : wt e = 2 := by rw [he]; decide
    obtain ⟨g, hgN, hg⟩ := ((hrec.2.2 e he0).mpr (Or.inl hwt))
    have hgE : g ∈ Subgroup.normalizer (E : Set G) := by
      rw [← hB.1]
      exact hgN
    have hgb : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := hle hgE
    have h1 : g * b₀ * g⁻¹ ∈ Subgroup.zpowers b₀ :=
      (Subgroup.mem_normalizer_iff.mp hgb b₀).mp (Subgroup.mem_zpowers b₀)
    have h2 : g * B.b 1 * g⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hKN hgb) (B.b 1)).mp (hB.2.2 1 (by decide))
    have hvec : B.vec e ∈ K := by
      rw [he, B.vec_add, B.vec_single, B.vec_single]
      exact K.mul_mem (hB.2.2 1 (by decide)) (hB.2.2 2 (by decide))
    have h3 : g * (b₀ * B.b 1) * g⁻¹ ∈ K := by
      have hmem : g * (b₀ * B.b 1) * g⁻¹ ∈ Subgroup.zpowers (B.vec e) :=
        (SetLike.ext_iff.mp hg _).mp (Subgroup.mem_zpowers _)
      exact (Subgroup.zpowers_le.mpr hvec) hmem
    have h4 : g * b₀ * g⁻¹ ∈ K := by
      have : g * b₀ * g⁻¹ = (g * (b₀ * B.b 1) * g⁻¹) * (g * B.b 1 * g⁻¹)⁻¹ := by group
      rw [this]
      exact K.mul_mem h3 (K.inv_mem h2)
    have h5 : g * b₀ * g⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj h1 h4
    have h6 : b₀ = 1 := by
      have : b₀ = g⁻¹ * (g * b₀ * g⁻¹) * g := by group
      rw [this, h5]
      group
    rw [h6, orderOf_one] at hb₀
    exact absurd hb₀ (by decide)
  exact exists_centralizer_eq_sup_of_eq_sup_centralizer hb₀ hKC hKn hcyc hEmax.2.1 hsup hself hN
    hout

theorem exists_threePrime_core_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) :
    ∃ R₀ : Subgroup G, R₀ ≤ Subgroup.centralizer ({b₀} : Set G) ∧
      (R₀.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R₀ ∧
      Subgroup.centralizer ({b₀} : Set G) = R₀ ⊔ (Subgroup.zpowers b₀ ⊔ K) ∧
      R₀ ≤ Subgroup.centralizer (E : Set G) ∧
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (R₀ : Set G) ∧
      (∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
        (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
        R ≤ R₀) ∧
      ∀ X : Subgroup G, IsSimpleGroup ↥X →
        X ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G) →
        (∃ x ∈ X, x ∈ E ∧ x ≠ 1) → R₀ ≤ Subgroup.centralizer (X : Set G) := by
  classical
  obtain ⟨-, hHyp, hCanon⟩ := id hstd
  obtain ⟨hA, hEmax, hb₀E, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, hKn, hKz, -, -, -, -⟩ := hA
  obtain ⟨hRow, -, hsup, -, hE1card, hself⟩ := hCanon
  obtain ⟨hKs, -⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hRow hKz
  have hE : IsElemAbelian 3 E := hEmax.2.1
  have hK3 : 3 ∣ Nat.card K := by
    have h : 3 ∣ Nat.card ↥(E ⊓ K) := by rw [hE1card]; exact dvd_pow_self 3 (by decide)
    exact h.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hcentE : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ({b₀} : Set G) →
      S ≤ Subgroup.centralizer (K : Set G) → S ≤ Subgroup.centralizer (E : Set G) := by
    intro S hSC hSK
    rw [Subgroup.le_centralizer_iff, ← hsup]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro r hr
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hSC hr))
    · exact inf_le_right.trans ((Subgroup.le_centralizer_iff).mp hSK)
  obtain ⟨R₀, hR₀C, hR₀n, hR₀3, hCeq⟩ := exists_centralizer_eq_of_recOutTwD7 hstd hB hrec
  have hR₀K : R₀ ≤ Subgroup.centralizer (K : Set G) :=
    le_centralizer_of_normal_of_isSimple hKC hKn hKs hK3 hR₀C hR₀n hR₀3
  have hR₀E : R₀ ≤ Subgroup.centralizer (E : Set G) := hcentE R₀ hR₀C hR₀K
  have hcop₀ : Nat.Coprime 3 (Nat.card R₀) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR₀3
  have hTR : Subgroup.zpowers b₀ ⊔ K ≤ Subgroup.centralizer (R₀ : Set G) := by
    refine sup_le ?_ ((Subgroup.le_centralizer_iff).mp hR₀K)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hR₀C hr))
  have hcommR : ∀ a ∈ R₀, ∀ b ∈ Subgroup.zpowers b₀ ⊔ K, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hTR hb) a ha
  have hzK : Subgroup.zpowers b₀ ≤ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk))
  have hcommK : ∀ a ∈ Subgroup.zpowers b₀, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hzK ha) b hb).symm
  have h3' : ∀ x ∈ Subgroup.centralizer (E : Set G), Nat.Coprime 3 (orderOf x) → x ∈ R₀ := by
    intro x hxE hx3
    have hxC : x ∈ Subgroup.centralizer ({b₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hxE b₀ hb₀E).symm
    obtain ⟨r, hr, s, hs, rfl⟩ := fs81Sp_mem_sup_of_commute hcommR (hCeq ▸ hxC)
    have hsE : s ∈ Subgroup.centralizer (E : Set G) := by
      have : s = r⁻¹ * (r * s) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hR₀E hr)) hxE
    obtain ⟨z, hz, k, hk, rfl⟩ := fs81Sp_mem_sup_of_commute hcommK hs
    have hzE : z ∈ E := (Subgroup.zpowers_le.mpr hb₀E) hz
    have hzC : z ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨z, hzE⟩)
    have hkE : k ∈ E := by
      have hkA : k ∈ E ⊓ K := by
        rw [← hself]
        refine ⟨?_, hk⟩
        have hkC : k ∈ Subgroup.centralizer (E : Set G) := by
          have : k = z⁻¹ * (z * k) := by group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzC) hsE
        exact Subgroup.centralizer_le inf_le_left hkC
      exact hkA.1
    have hsE' : z * k ∈ E := E.mul_mem hzE hkE
    have hrs : Commute r (z * k) := (Subgroup.mem_centralizer_iff.mp (hR₀E hr) _ hsE').symm
    set m := orderOf (r * (z * k))
    have hpow : r ^ m * (z * k) ^ m = 1 := by
      rw [← hrs.mul_pow]
      exact pow_orderOf_eq_one _
    have hsm : (z * k) ^ m ∈ R₀ := by
      rw [eq_inv_of_mul_eq_one_right hpow]
      exact R₀.inv_mem (R₀.pow_mem hr m)
    have hsm1 : (z * k) ^ m = 1 := by
      have h1 : orderOf ((z * k) ^ m) ∣ 3 := orderOf_dvd_of_pow_eq_one (hE.2 _ (E.pow_mem hsE' m))
      have h2 : orderOf ((z * k) ^ m) ∣ Nat.card R₀ := Subgroup.orderOf_dvd_natCard R₀ hsm
      have h3 := Nat.dvd_gcd h1 h2
      rw [hcop₀, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    have hs1 : z * k = 1 := by
      have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hE.2 _ hsE'))
        (orderOf_dvd_of_pow_eq_one hsm1)
      rw [hx3, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    rw [hs1, mul_one]
    exact hr
  have hconj : ∀ n ∈ Subgroup.normalizer (E : Set G), ∀ r ∈ R₀, n * r * n⁻¹ ∈ R₀ := by
    intro n hn r hr
    refine h3' _ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : n⁻¹ * e * n⁻¹⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) e).mp he
      rw [inv_inv] at he'
      have hc : (n⁻¹ * e * n) * r = r * (n⁻¹ * e * n) :=
        Subgroup.mem_centralizer_iff.mp (hR₀E hr) _ he'
      calc e * (n * r * n⁻¹) = n * ((n⁻¹ * e * n) * r) * n⁻¹ := by group
        _ = n * (r * (n⁻¹ * e * n)) * n⁻¹ := by rw [hc]
        _ = n * r * n⁻¹ * e := by group
    · have hord : orderOf (n * r * n⁻¹) = orderOf r := by
        simpa using orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective r
      rw [hord]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard R₀ hr) hcop₀
  have hNR : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (R₀ : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj n hn h, fun hh => ?_⟩
    have := hconj n⁻¹ (Subgroup.inv_mem _ hn) _ hh
    rwa [inv_inv, show n⁻¹ * (n * h * n⁻¹) * n = h by group] at this
  have hCR : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (R₀ : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hR₀C]
    exact hR₀n
  refine ⟨R₀, hR₀C, hR₀n, hR₀3, hCeq, hR₀E, hNR, fun R hRC hRn hR3 => ?_,
    fun X hX hXle ⟨x, hxX, hxE, hx1⟩ => ?_⟩
  ·
    have hRK : R ≤ Subgroup.centralizer (K : Set G) :=
      le_centralizer_of_normal_of_isSimple hKC hKn hKs hK3 hRC hRn hR3
    have hRE : R ≤ Subgroup.centralizer (E : Set G) := hcentE R hRC hRK
    have hcop : Nat.Coprime 3 (Nat.card R) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR3
    intro r hr
    exact h3' r (hRE hr)
      (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard R hr) hcop)
  ·
    rw [Subgroup.le_centralizer_iff]
    exact le_centralizer_of_isSimpleGroup_of_le_normalizer hX (hXle.trans (sup_le hCR hNR)) hxX
      ((Subgroup.le_centralizer_iff.mp hR₀E) hxE) hx1

theorem exists_threePrime_core_beta_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀)
    {J : Subgroup G} (hJs : IsSimpleGroup ↥J)
    (hJC : J ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G))
    (hJgen : J ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hβ₁J : b₀⁻¹ * B.b 1 ∈ J)
    (hMJ : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J)
    (hinv : ∃ t ∈ J, t * (b₀⁻¹ * B.b 1) * t⁻¹ = (b₀⁻¹ * B.b 1)⁻¹) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G) ∧ ¬ 3 ∣ Nat.card R ∧
      R ≤ Subgroup.centralizer (J : Set G) ∧
      (∀ σ ∈ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G),
        R ≤ Subgroup.centralizer (J.map (MulAut.conj σ).toMonoidHom : Set G)) ∧
      ∀ x ∈ Subgroup.centralizer ({b₀ * B.b 1} : Set G),
        x * (b₀⁻¹ * B.b 1) * x⁻¹ ∈ Subgroup.zpowers (b₀⁻¹ * B.b 1) →
          x ∈ R ⊔ (Subgroup.zpowers (b₀ * B.b 1) ⊔ J) := by
  obtain ⟨R₀, hR₀C, hR₀n, hR₀3, hCeq, hR₀E, hNR, -, hker⟩ :=
    exists_threePrime_core_twD7 hstd hB hrec
  obtain ⟨-, hHyp, hCanon⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, -, hKz, -, -, -, -⟩ := hA
  obtain ⟨hRow, -⟩ := hCanon
  obtain ⟨hKs, -⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hRow hKz
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have hbE : ∀ i, B.b i ∈ E := fun i => hB.1 ▸ B.b_mem_span i
  have hb₀E : b₀ ∈ E := hB.2.1 ▸ hbE 0
  have hb₁1 : B.b 1 ≠ 1 := by
    intro h
    have h3 := B.ord 1
    rw [h, orderOf_one] at h3
    exact absurd h3 (by decide)
  have hRK : R₀ ≤ Subgroup.centralizer (K : Set G) :=
    hker K hKs (hKC.trans le_sup_left) ⟨B.b 1, hb₁K, hbE 1, hb₁1⟩
  have hβ₁1 : b₀⁻¹ * B.b 1 ≠ 1 := by
    intro h
    have h' : b₀ = B.b 1 := inv_mul_eq_one.mp h
    have h1 : b₀ = 1 := Subgroup.disjoint_def.mp (disjoint_zpowers_of_center hKC hKz)
      (Subgroup.mem_zpowers b₀) (by rw [h']; exact hb₁K)
    rw [h1, orderOf_one] at hb₀
    exact absurd hb₀ (by decide)
  have hRJ : R₀ ≤ Subgroup.centralizer (J : Set G) :=
    hker J hJs hJgen ⟨_, hβ₁J, E.mul_mem (E.inv_mem hb₀E) (hbE 1), hβ₁1⟩
  have hσN : Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (R₀ : Set G) :=
    sup_le ((Subgroup.normal_subgroupOf_iff_le_normalizer hR₀C).mp hR₀n) hNR
  refine ⟨R₀, fun r hr => ?_, hR₀3, hRJ, fun σ hσ r hr => ?_, fun x hx hxβ₁ =>
    mem_sup_of_conj_mem_zpowers_twD7 hstd hB hrec hRK hCeq hJC hβ₁J hMJ hinv hx hxβ₁⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hR₀E hr) _ (E.mul_mem hb₀E (hbE 1))).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
    have hr' : σ⁻¹ * r * σ⁻¹⁻¹ ∈ R₀ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hσN hσ)) r).mp hr
    rw [inv_inv] at hr'
    have h := Subgroup.mem_centralizer_iff.mp (hRJ hr') j hj
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc σ * j * σ⁻¹ * r = σ * (j * (σ⁻¹ * r * σ)) * σ⁻¹ := by group
      _ = σ * ((σ⁻¹ * r * σ) * j) * σ⁻¹ := by rw [h]
      _ = r * (σ * j * σ⁻¹) := by group

section Cap

open scoped Pointwise

theorem centralizer_inf_eq_of_mul_mem {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E Y : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀)
    (hY : IsEm 8 Y) (hEY : E ≤ Y)
    (hCH : ∀ x ∈ Subgroup.centralizer ({B.b 1} : Set G) ⊓ K, ∃ d ∈
      Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G), x * d ∈ Y)
    (hRY : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
      (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
      R ≤ Subgroup.centralizer (Y : Set G)) :
    Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K := by
  classical
  obtain ⟨-, hHyp, hCanon⟩ := id hstd
  obtain ⟨hA, hEmax, hb₀E, hEcard, -, -⟩ := hHyp
  obtain ⟨-, hKC, -, hKz, -, -, -, -⟩ := hA
  obtain ⟨hRow, -, -, -, -, hself⟩ := hCanon
  obtain ⟨hKs, -⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hRow hKz
  have hY8 : IsEm 8 Y := hY
  have hb₀Y : b₀ ∈ Y := hEY hb₀E
  have hout := centralizer_eq_sup_of_recOutTwD7 hstd hB hrec
  have hdec : ∀ c ∈ Subgroup.centralizer ({b₀} : Set G), ∃ k ∈ K, ∃ d ∈
      Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G), c = k * d :=
    fun c hc => fs81Sp_mem_sup_of_commute (A := K)
      (B := Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))
      (fun a ha b hb => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 a ha)
      (hout ▸ hc)
  have hpart : ∀ k ∈ K, ∀ d ∈ Subgroup.centralizer (K : Set G),
      (∀ a ∈ E ⊓ K, a * (k * d) = (k * d) * a) → k ∈ E ⊓ K := by
    intro k hk d hd hkd
    rw [← hself]
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, hk⟩
    have h2 : a * d = d * a := Subgroup.mem_centralizer_iff.mp hd a ha.2
    calc a * k = a * (k * d) * d⁻¹ := by group
      _ = k * d * a * d⁻¹ := by rw [hkd a ha]
      _ = k * (d * a) * d⁻¹ := by group
      _ = k * (a * d) * d⁻¹ := by rw [h2]
      _ = k * a := by group
  let H : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∃ d ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer (K : Set G), k * d ∈ Y}
      mul_mem' := by
        rintro a b ⟨ha, d, hd, hadY⟩ ⟨hb, d', hd', hbdY⟩
        refine ⟨K.mul_mem ha hb, d * d', Subgroup.mul_mem _ hd hd', ?_⟩
        have hdb : b * d = d * b := Subgroup.mem_centralizer_iff.mp hd.2 b hb
        have : a * b * (d * d') = (a * d) * (b * d') := by
          calc a * b * (d * d') = a * (b * d) * d' := by group
            _ = a * (d * b) * d' := by rw [hdb]
            _ = (a * d) * (b * d') := by group
        rw [this]
        exact Y.mul_mem hadY hbdY
      one_mem' := ⟨K.one_mem, 1, Subgroup.one_mem _, by rw [mul_one]; exact Y.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, d, hd, hadY⟩
        refine ⟨K.inv_mem ha, d⁻¹, Subgroup.inv_mem _ hd, ?_⟩
        have hda : a * d = d * a := Subgroup.mem_centralizer_iff.mp hd.2 a ha
        have : a⁻¹ * d⁻¹ = (a * d)⁻¹ := by rw [hda, mul_inv_rev]
        rw [this]
        exact Y.inv_mem hadY }
  have hmemH : ∀ k, k ∈ H ↔ k ∈ K ∧ ∃ d ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G), k * d ∈ Y := fun _ => Iff.rfl
  have hAH : E ⊓ K ≤ H := fun a ha =>
    (hmemH a).mpr ⟨ha.2, 1, Subgroup.one_mem _, by rw [mul_one]; exact hEY ha.1⟩
  have hCH' : Subgroup.centralizer ({B.b 1} : Set G) ⊓ K ≤ H := fun x hx =>
    (hmemH x).mpr ⟨(Subgroup.mem_inf.mp hx).2, hCH x hx⟩
  obtain ⟨t, htK, htN, hgen⟩ := exists_mem_le_of_centralizer_le_twD7 hstd hB hrec
  have hAut : Nat.card (ggAutomizer ⊤ E) = 696729600 := by
    rw [← hB.1]
    exact hrec.1
  obtain ⟨ι, hι, hιY⟩ := exists_injective_hom_range_eq_of_isEm_eight hY8
  have hge := le_natCard_ggAutomizer_range_of_card_E8 natCard_galoisField_two_one ι hι
    (hιY.symm ▸ hEY) hEmax.2.1 hEcard.ge
  rw [hιY] at hge
  have hAutY : Nat.card (ggAutomizer Y E) = Nat.card (ggAutomizer ⊤ E) :=
    le_antisymm (Subgroup.card_le_of_le (ggAutomizer_mono E le_top)) (by rw [hAut]; exact hge)
  obtain ⟨y, hyY, -, c, hcE, htyc⟩ := exists_mul_of_card_ggAutomizer_eq hAutY htN
  have htH : t ∈ H := by
    have hcC : c ∈ Subgroup.centralizer ({b₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hcE b₀ hb₀E).symm
    obtain ⟨k, hk, d, hd, hkd⟩ := hdec _ hcC
    have hkA : k ∈ E ⊓ K := hpart k hk d hd.2 fun a ha => by
      rw [← hkd]
      exact Subgroup.mem_centralizer_iff.mp hcE a ha.1
    have hdk : d * k = k * d := (Subgroup.mem_centralizer_iff.mp hd.2 k hk).symm
    have htk : t * k⁻¹ ∈ H := by
      refine (hmemH _).mpr ⟨K.mul_mem htK (K.inv_mem hk), d⁻¹, Subgroup.inv_mem _ hd, ?_⟩
      have : t * k⁻¹ * d⁻¹ = y := by
        have h1 : t = y * (k * d) := by rw [← hkd, htyc]
        calc t * k⁻¹ * d⁻¹ = y * (k * d) * k⁻¹ * d⁻¹ := by rw [← h1]
          _ = y * (d * k) * k⁻¹ * d⁻¹ := by rw [hdk]
          _ = y := by group
      rw [this]
      exact hyY
    have := H.mul_mem htk (hAH hkA)
    rwa [inv_mul_cancel_right] at this
  have hKH : K ≤ H := hgen H hCH' htH
  have hKY : K ≤ Y := by
    have hnorm : ((K ⊓ Y).subgroupOf K).Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      obtain ⟨-, d, hd, hgdY⟩ := (hmemH _).mp (hKH g.2)
      show (g : G) * a * (g : G)⁻¹ ∈ K ⊓ Y
      refine ⟨K.mul_mem (K.mul_mem g.2 ha.1) (K.inv_mem g.2), ?_⟩
      have hda : (a : G) * d = d * a := Subgroup.mem_centralizer_iff.mp hd.2 a ha.1
      have : (g : G) * a * (g : G)⁻¹ = ((g : G) * d) * a * ((g : G) * d)⁻¹ := by
        calc (g : G) * a * (g : G)⁻¹ = (g : G) * (a * d) * d⁻¹ * (g : G)⁻¹ := by group
          _ = (g : G) * (d * a) * d⁻¹ * (g : G)⁻¹ := by rw [hda]
          _ = ((g : G) * d) * a * ((g : G) * d)⁻¹ := by group
      rw [this]
      exact Y.mul_mem (Y.mul_mem hgdY ha.2) (Y.inv_mem hgdY)
    have := hKs
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ Y).subgroupOf K) with h | h
    · exfalso
      have hb1K : B.b 1 ∈ K := hB.2.2 1 (by decide)
      have hb1E : B.b 1 ∈ E := hB.1 ▸ B.b_mem_span 1
      have hmem : (⟨B.b 1, hb1K⟩ : ↥K) ∈ (K ⊓ Y).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr ⟨hb1K, hEY hb1E⟩
      rw [h, Subgroup.mem_bot] at hmem
      have h1 : B.b 1 = 1 := congrArg Subtype.val hmem
      have hord := B.ord 1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by decide)
    · intro k hk
      exact (Subgroup.subgroupOf_eq_top.mp h hk).2
  obtain ⟨R, hRC, hRn, hR3, hCeq⟩ := exists_centralizer_eq_of_recOutTwD7 hstd hB hrec
  have hRY : R ≤ Subgroup.centralizer (Y : Set G) := hRY R hRC hRn hR3
  have hZ := centralizer_inf_eq_bot_of_isEm_eight hY8
  have hTY : Subgroup.zpowers b₀ ⊔ K ≤ Y := sup_le (Subgroup.zpowers_le.mpr hb₀Y) hKY
  have hRT : R ≤ Subgroup.normalizer ((Subgroup.zpowers b₀ ⊔ K : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro r hr t ht
    have hrt : t * r = r * t := Subgroup.mem_centralizer_iff.mp (hRY hr) t (hTY ht)
    rw [← hrt]
    simpa using ht
  have hcoe : (↑(R ⊔ (Subgroup.zpowers b₀ ⊔ K)) : Set G) =
      (R : Set G) * ((Subgroup.zpowers b₀ ⊔ K : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right R _ hRT
  apply le_antisymm
  · rintro c ⟨hcC, hcY⟩
    have hcT : c ∈ R ⊔ (Subgroup.zpowers b₀ ⊔ K) := by
      rw [← hCeq]
      exact hcC
    have hcRT : c ∈ (R : Set G) * ((Subgroup.zpowers b₀ ⊔ K : Subgroup G) : Set G) := by
      rw [← hcoe]
      exact hcT
    obtain ⟨r, hr, s, hs, rfl⟩ := hcRT
    have hrY : r ∈ Y := by
      have : r = r * s * s⁻¹ := by group
      rw [this]
      exact Y.mul_mem hcY (Y.inv_mem (hTY hs))
    have hr1 : r ∈ Subgroup.centralizer (Y : Set G) ⊓ Y := ⟨hRY hr, hrY⟩
    rw [hZ, Subgroup.mem_bot] at hr1
    show r * s ∈ _
    rw [hr1, one_mul]
    exact hs
  · refine le_inf (sup_le ?_ hKC) hTY
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem le_centralizer_of_le_sup_normalizer {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E Y : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀)
    (hY : IsEm 8 Y) (hEY : E ≤ Y)
    (hYgen : Y ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    {R : Subgroup G} (hRC : R ≤ Subgroup.centralizer ({b₀} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hR3 : ¬ 3 ∣ Nat.card R) : R ≤ Subgroup.centralizer (Y : Set G) := by
  classical
  obtain ⟨-, hHyp, -⟩ := id hstd
  obtain ⟨hA, -, hb₀E, -, -, -⟩ := hHyp
  obtain ⟨hb₀, -, -, -, -, -, -, -⟩ := hA
  obtain ⟨R₀, -, -, -, -, -, -, hRR₀, hXR₀⟩ := exists_threePrime_core_twD7 hstd hB hrec
  have hZ := centralizer_inf_eq_bot_of_isEm_eight hY
  have hYs : IsSimpleGroup ↥Y := by
    obtain ⟨⟨t, r, n⟩, ⟨-, -, hn⟩, hlab⟩ := exists_glaLabel hY
    dsimp only at hn
    subst hn
    have hK' : CFSG.LocalAnalysis.GLTheoremA.Rk2IsLabel ↥Y (⟨t, r, 1⟩ : GLALabel) := hlab
    obtain ⟨hQ, -, -⟩ := CFSG.LocalAnalysis.GLTheoremA.quasisimple_markedModel_of_isLabel hK'
    have hZ' : Subgroup.center ↥Y = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hzG : (z : G) ∈ Subgroup.centralizer (Y : Set G) ⊓ Y :=
        ⟨Subgroup.mem_centralizer_iff.2 fun y hy => by
          have := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
          exact congrArg Subtype.val this, z.2⟩
      rw [hZ] at hzG
      exact Subtype.ext (Subgroup.mem_bot.1 hzG)
    have := hQ.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hZ').trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hb₀1 : b₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hb₀
    exact absurd hb₀ (by decide)
  exact (hRR₀ R hRC hRn hR3).trans (hXR₀ Y hYs hYgen ⟨b₀, hEY hb₀E, hb₀E, hb₀1⟩)

theorem centralizer_inf_eq_and_le_centralizer_of_le_sup_normalizer {G : Type} [Group G]
    [Finite G] {b₀ : G} {K E Y : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀)
    (hY : IsEm 8 Y) (hEY : E ≤ Y) (hCKY : Subgroup.centralizer ({B.b 1} : Set G) ⊓ K ≤ Y)
    (hYgen : Y ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G)) :
    Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K ∧
      ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
        (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
        R ≤ Subgroup.centralizer (Y : Set G) := by
  have hRY : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
      (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
      R ≤ Subgroup.centralizer (Y : Set G) := fun _ hRC hRn hR3 =>
    le_centralizer_of_le_sup_normalizer hstd hB hrec hY hEY hYgen hRC hRn hR3
  refine ⟨centralizer_inf_eq_of_mul_mem hstd hB hrec hY hEY
    (fun x hx => ⟨1, Subgroup.one_mem _, ?_⟩) hRY, hRY⟩
  rw [mul_one]
  exact hCKY hx

end Cap

end CFSG.StandardType.FrameRoute.FS81
