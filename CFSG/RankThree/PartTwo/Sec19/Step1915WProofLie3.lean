module

public import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie9Gen
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.CentralCover.FourGroupWitness
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

@[expose] def KS1917Lie3Sylow : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → p ^ e % 9 ≠ 1 → p ^ e % 9 ≠ 8 →
    ∀ S : Sylow 3 X, Nat.card (S : Subgroup X) = 9 ∧ ∀ s ∈ (S : Subgroup X), s ^ 3 = 1

@[expose] def KS1917Lie3Fusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → p ^ e % 9 ≠ 1 → p ^ e % 9 ≠ 8 →
    ∀ S : Sylow 3 X, ∀ x ∈ (S : Subgroup X), x ≠ 1 →
      ∃ g ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), g * x * g⁻¹ ∉ Subgroup.zpowers x

@[expose] def KS1917Lie3AutCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → p ^ e % 9 ≠ 1 → p ^ e % 9 ≠ 8 →
    ∀ (S : Sylow 3 X) (α : MulAut X), (∃ k : ℕ, α ^ 3 ^ k = 1) →
      (∀ s ∈ (S : Subgroup X), α s = s) → ∃ s ∈ (S : Subgroup X), α = MulAut.conj s

namespace Step1915WProof

section Nine

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_comm_of_mem_normalizer {p : ℕ} [Fact p.Prime] {R : Subgroup G} {s : G}
    (hs : ∃ k : ℕ, s ^ p ^ k = 1) (hsR : s ∈ Subgroup.normalizer (R : Set G))
    (hpR : p ∣ Nat.card R) : ∃ r ∈ R, r ≠ 1 ∧ s * r = r * s := by
  set H := Subgroup.zpowers s with hH
  have hHN : H ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hsR
  have hH3 : IsPGroup p H := by
    obtain ⟨k, hk⟩ := hs
    rintro ⟨_, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (s ^ n) ^ p ^ k = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hk,
      _root_.one_zpow]
  let _ : MulAction H R :=
    MulAction.compHom R (R.normalizerMonoidHom.comp (Subgroup.inclusion hHN))
  have hfix1 : (1 : R) ∈ MulAction.fixedPoints H R := fun h => by
    change (R.normalizerMonoidHom (Subgroup.inclusion hHN h)) 1 = 1
    exact map_one _
  obtain ⟨r, hr, hr1⟩ :=
    hH3.exists_fixed_point_of_prime_dvd_card_of_fixed_point R hpR hfix1
  refine ⟨r, r.2, fun h => hr1 (Subtype.ext h.symm), ?_⟩
  have h := hr ⟨s, Subgroup.mem_zpowers s⟩
  change (R.normalizerMonoidHom (Subgroup.inclusion hHN ⟨s, Subgroup.mem_zpowers s⟩)) r = r at h
  have h' := congrArg Subtype.val h
  rw [Sec4.normalizerMonoidHom_apply_coe] at h'
  change s * (r : G) * s⁻¹ = r at h'
  calc s * (r : G) = s * r * s⁻¹ * s := by group
    _ = r * s := by rw [h']

omit [Finite G] in
theorem inv_mem_normalizer' {D : Subgroup G} {s : G} (hs : s ∈ Subgroup.normalizer (D : Set G)) :
    s⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
  Subgroup.inv_mem _ hs

theorem card_inf_centralizer_eq_three {D : Subgroup G} (hD9 : Nat.card D = 9) {s : G}
    (hs : ∃ k : ℕ, s ^ 3 ^ k = 1) (hsD : s ∈ Subgroup.normalizer (D : Set G))
    (hnc : ∃ d ∈ D, s * d ≠ d * s) :
    Nat.card (D ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := D ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hdvd : Nat.card C ∣ 9 := hD9 ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨r, hrD, hr1, hrs⟩ := exists_ne_one_comm_of_mem_normalizer hs hsD (by rw [hD9]; norm_num)
  have hrC : r ∈ C := ⟨hrD, Subgroup.mem_centralizer_singleton_iff.mpr hrs.symm⟩
  have h1 : Nat.card C ≠ 1 := by
    intro h
    have : r = 1 := by
      have := (Subgroup.card_eq_one.mp h)
      rw [this] at hrC
      exact (Subgroup.mem_bot).mp hrC
    exact hr1 this
  have h9 : Nat.card C ≠ 9 := by
    intro h
    have hCD : C = D := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hD9])
    obtain ⟨d, hd, hds⟩ := hnc
    have hdC : d ∈ C := hCD ▸ hd
    exact hds (Subgroup.mem_centralizer_singleton_iff.mp hdC.2).symm
  have : Nat.card C ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h9d : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [h9d] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

@[expose] def commHom (D : Subgroup G) (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (s : G)
    (hsD : s ∈ Subgroup.normalizer (D : Set G)) : D →* D where
  toFun y := ⟨s * y * s⁻¹ * (y : G)⁻¹, D.mul_mem ((Subgroup.mem_normalizer_iff.mp hsD y).mp y.2)
    (D.inv_mem y.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have ha : s * (a : G) * s⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hsD a).mp a.2
    have hb : s * (b : G) * s⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hsD b).mp b.2
    have h1 := hD _ (D.inv_mem a.2) _ (D.mul_mem hb (D.inv_mem b.2))
    calc s * (a * b : G) * s⁻¹ * (a * b : G)⁻¹ =
        (s * a * s⁻¹) * ((s * b * s⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (s * a * s⁻¹) * ((a : G)⁻¹ * (s * b * s⁻¹ * (b : G)⁻¹)) := by rw [h1]
      _ = s * a * s⁻¹ * (a : G)⁻¹ * (s * b * s⁻¹ * (b : G)⁻¹) := by group

theorem commutator_mem_inf_centralizer {D : Subgroup G} (hD9 : Nat.card D = 9)
    (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {s : G} (hs : ∃ k : ℕ, s ^ 3 ^ k = 1)
    (hsD : s ∈ Subgroup.normalizer (D : Set G)) (hnc : ∃ d ∈ D, s * d ≠ d * s) {y : G}
    (hy : y ∈ D) : s * y * s⁻¹ * y⁻¹ ∈ D ⊓ Subgroup.centralizer ({s} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := D ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hC3 := card_inf_centralizer_eq_three hD9 hs hsD hnc
  set f := commHom D hD s hsD with hf
  have hker : Nat.card f.ker = 3 := by
    rw [← hC3]
    have : f.ker = C.subgroupOf D := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h' := congrArg Subtype.val h
        change s * (x : G) * s⁻¹ * (x : G)⁻¹ = 1 at h'
        refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        symm
        calc s * (x : G) = s * x * s⁻¹ * (x : G)⁻¹ * x * s := by group
          _ = x * s := by rw [h']; group
      · intro h
        apply Subtype.ext
        change s * (x : G) * s⁻¹ * (x : G)⁻¹ = 1
        rw [← Subgroup.mem_centralizer_singleton_iff.mp h.2]
        group
    rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hrange : Nat.card f.range = 3 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hker, hD9] at h
    omega
  set R := f.range.map D.subtype with hR
  have hRcard : Nat.card R = 3 := by
    rw [hR, Subgroup.card_map_of_injective D.subtype_injective, hrange]
  have hmemR : ∀ x : G, x ∈ R ↔ ∃ w ∈ D, x = s * w * s⁻¹ * w⁻¹ := by
    intro x
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨f ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
  have hsR : s ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemR, hmemR]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨s * w * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsD w).mp hw, by group⟩
    · rintro ⟨w, hw, hx⟩
      refine ⟨s⁻¹ * w * s, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (inv_mem_normalizer' hsD) w).mp hw
        rwa [inv_inv] at this
      · have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
        rw [this, hx]
        group
  obtain ⟨r, hrR, hr1, hrs⟩ := exists_ne_one_comm_of_mem_normalizer hs hsR (by rw [hRcard])
  have hrD : r ∈ D := by
    obtain ⟨w, hw, rfl⟩ := (hmemR r).mp hrR
    exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp hsD w).mp hw) (D.inv_mem hw)
  have hRC : R ≤ C := by
    have hle : R ⊓ C ≤ R := inf_le_left
    have hrRC : r ∈ R ⊓ C := ⟨hrR, hrD, Subgroup.mem_centralizer_singleton_iff.mpr hrs.symm⟩
    have hcard : Nat.card R ≤ Nat.card (R ⊓ C : Subgroup G) := by
      have hdvd : Nat.card (R ⊓ C : Subgroup G) ∣ 3 := hRcard ▸ Subgroup.card_dvd_of_le hle
      have h1 : Nat.card (R ⊓ C : Subgroup G) ≠ 1 := by
        intro h
        rw [Subgroup.card_eq_one.mp h] at hrRC
        exact hr1 ((Subgroup.mem_bot).mp hrRC)
      have : Nat.card (R ⊓ C : Subgroup G) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd h h1
        · exact h
      rw [this, hRcard]
    have := Subgroup.eq_of_le_of_card_ge hle hcard
    rw [← this]
    exact inf_le_right
  exact hRC ((hmemR _).mpr ⟨y, hy, rfl⟩)

end Nine

theorem conj_mem_upperCentralSeries_two_of_eq {G : Type} [Group G] {P : Subgroup G} {x : G}
    (hx : x ∈ P) (h2 : (⟨x, hx⟩ : P) ∈ Subgroup.upperCentralSeries P 2)
    (hZ : (⟨x, hx⟩ : P) ∉ Subgroup.center P) (k : G) {y : G} (hy : y = k * x * k⁻¹) :
    ∃ hky : y ∈ P.map (MulAut.conj k).toMonoidHom,
      (⟨y, hky⟩ : P.map (MulAut.conj k).toMonoidHom) ∈
          Subgroup.upperCentralSeries (P.map (MulAut.conj k).toMonoidHom) 2 ∧
        (⟨y, hky⟩ : P.map (MulAut.conj k).toMonoidHom) ∉
          Subgroup.center (P.map (MulAut.conj k).toMonoidHom) := by
  subst hy
  exact conj_mem_upperCentralSeries_two hx h2 hZ k

open Step1917Steps in
theorem step1917Z2KLie3_of (hSyl : KS1917Lie3Sylow) (hFus : KS1917Lie3Fusion)
    (hAut : KS1917Lie3AutCent) : Step1917Z2KLie3 := by
  intro G _ _ L Q T z p e _ he hiso h91 h98 hLp hQ3 hQN hQnab hrank hTY hQT hzL hzT hz1 hzc
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : L →* L ⧸ CFSG.pCore 2 L := QuotientGroup.mk' (CFSG.pCore 2 L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := Group.IsPerfect.ofSurjective (f := π) hπs
  obtain ⟨hXs, -⟩ := Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso
  have hZX : Subgroup.center (L ⧸ CFSG.pCore 2 L) = ⊥ :=
    Step1914TriProof.center_eq_bot_of_isSimpleGroup_of_isPerfect
  have hYN : Q ⊔ L ≤ Subgroup.normalizer (L : Set G) := sup_le hQN Subgroup.le_normalizer
  have hTL : IsSylowOf 3 (T ⊓ L) L := hTY.inf_of_le_normalizer le_sup_right hYN
  set D := T ⊓ L with hD
  have hD3 : IsPGroup 3 D := hTL.isPGroup
  have hT3 : IsPGroup 3 T := hTY.isPGroup
  set D' : Subgroup L := D.subgroupOf L with hD'
  have hD'3 : IsPGroup 3 D' := hD3.comap_subtype
  have hinj : Set.InjOn π (D' : Set L) :=
    Sec12.injOn_mk_of_coprime _ (Step1919EndProof.not_three_dvd_card_pCore L) hD'3
  set Dbar : Subgroup (L ⧸ CFSG.pCore 2 L) := D'.map π with hDbar
  have hcardD' : Nat.card D' = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcardDbar : Nat.card Dbar = Nat.card D :=
    (Step198DProof.card_map_of_injOn π hinj).trans hcardD'
  have hfact : (Nat.card (L ⧸ CFSG.pCore 2 L)).factorization 3 = (Nat.card L).factorization 3 := by
    have hc := (CFSG.pCore 2 L).card_eq_card_quotient_mul_card_subgroup
    have h0 : Nat.card (L ⧸ CFSG.pCore 2 L) ≠ 0 := Nat.card_pos.ne'
    have h1 : Nat.card (CFSG.pCore 2 L) ≠ 0 := Nat.card_pos.ne'
    rw [hc, Nat.factorization_mul h0 h1, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (Step1919EndProof.not_three_dvd_card_pCore L),
      add_zero]
  have hcardS : Nat.card Dbar = 3 ^ (Nat.card (L ⧸ CFSG.pCore 2 L)).factorization 3 := by
    rw [hcardDbar, hTL.card_eq, hfact]
  set S : Sylow 3 (L ⧸ CFSG.pCore 2 L) := Sylow.ofCard Dbar hcardS with hSdef
  have hSD : (S : Subgroup (L ⧸ CFSG.pCore 2 L)) = Dbar := rfl
  obtain ⟨hS9, hS3⟩ := hSyl _ p e he hiso h91 h98 S
  rw [hSD] at hS9 hS3
  have hD9 : Nat.card D = 9 := hcardDbar ▸ hS9
  have hπmem : ∀ d (hd : d ∈ D), π ⟨d, hd.2⟩ ∈ Dbar := fun d hd =>
    ⟨⟨d, hd.2⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  have hDexp : ∀ d ∈ D, d ^ 3 = 1 := by
    intro d hd
    have h1 : π (⟨d, hd.2⟩ ^ 3) = π 1 := by rw [map_pow, hS3 _ (hπmem d hd), map_one]
    have h2 := hinj (D'.pow_mem (Subgroup.mem_subgroupOf.mpr hd) 3) D'.one_mem h1
    simpa using congrArg Subtype.val h2
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := D)
      (by rw [hD9]; norm_num)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hTND : ∀ t ∈ T, t ∈ Subgroup.normalizer (D : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hYN (hTY.le ht)⟩
  have hTpow : ∀ t ∈ T, ∃ k : ℕ, t ^ 3 ^ k = 1 := fun t ht => by
    obtain ⟨k, hk⟩ := hT3 ⟨t, ht⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hzD : z ∈ D := ⟨hzT, hzL⟩
  have hz3 : z ^ 3 = 1 := hDexp z hzD
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hπ1 : ∀ d (hd : d ∈ D), π ⟨d, hd.2⟩ = 1 → d = 1 := by
    intro d hd h
    have := hinj (Subgroup.mem_subgroupOf.mpr hd) D'.one_mem (h.trans (map_one π).symm)
    exact congrArg Subtype.val this
  have hαL : ∀ l : L, Step199Proof.pCoreAct L ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
      MulAut.conj (π l) := by
    intro l
    ext q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Step199Proof.pCoreAct_mk ⟨(l : G), Subgroup.le_normalizer l.2⟩ k (l * k * l⁻¹)
      (by simp), MulAut.conj_apply]
    rfl
  by_cases hcase : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t
  ·
    exfalso
    set C : Subgroup G := T ⊓ (Step199Proof.pCoreAct L).ker.map
      (Subgroup.normalizer (L : Set G)).subtype with hCdef
    have hdec : ∀ t ∈ T, ∃ d ∈ D, d⁻¹ * t ∈ C := by
      intro t ht
      have htN : t ∈ Subgroup.normalizer (L : Set G) := hYN (hTY.le ht)
      set α := Step199Proof.pCoreAct L ⟨t, htN⟩ with hα
      have hα3 : ∃ k : ℕ, α ^ 3 ^ k = 1 := by
        obtain ⟨k, hk⟩ := hTpow t ht
        refine ⟨k, ?_⟩
        rw [hα, ← map_pow]
        convert map_one (Step199Proof.pCoreAct L)
        exact Subtype.ext (by simpa using hk)
      have hfix : ∀ x ∈ (S : Subgroup (L ⧸ CFSG.pCore 2 L)), α x = x := by
        rintro _ ⟨d', hd', rfl⟩
        have hd'D : (d' : G) ∈ D := Subgroup.mem_subgroupOf.mp hd'
        rw [hα]
        change Step199Proof.pCoreAct L ⟨t, htN⟩ (d' : L ⧸ CFSG.pCore 2 L) = d'
        rw [Step199Proof.pCoreAct_mk ⟨t, htN⟩ d' d' (by
          change (d' : G) = t * d' * t⁻¹
          rw [hcase t ht _ hd'D, mul_inv_cancel_right])]
      obtain ⟨x, hxS, hαx⟩ := hAut _ p e he hiso h91 h98 S α hα3 hfix
      obtain ⟨d', hd', rfl⟩ := hxS
      have hd'D : (d' : G) ∈ D := Subgroup.mem_subgroupOf.mp hd'
      refine ⟨d', hd'D, hTY.le.trans le_rfl |> fun _ => T.mul_mem (T.inv_mem hd'D.1) ht, ?_⟩
      have hdN : (d' : G)⁻¹ * t ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer d'.2)) htN
      refine ⟨⟨(d' : G)⁻¹ * t, hdN⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      have e : (⟨(d' : G)⁻¹ * t, hdN⟩ : Subgroup.normalizer (L : Set G)) =
          (⟨(d' : G), Subgroup.le_normalizer d'.2⟩ : Subgroup.normalizer (L : Set G))⁻¹ *
            ⟨t, htN⟩ := rfl
      rw [e, map_mul, map_inv, hαL, ← hα, hαx, inv_mul_cancel]
    have hCD : ∀ x ∈ C, x ∈ D → x = 1 := by
      rintro x ⟨-, ⟨y, hy, rfl⟩⟩ hxD
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy
      have hyL : (y : G) ∈ L := hxD.2
      have e : y = ⟨((⟨(y : G), hyL⟩ : L) : G), Subgroup.le_normalizer hyL⟩ := rfl
      rw [e, hαL] at hy
      have hc : π ⟨y, hyL⟩ ∈ Subgroup.center (L ⧸ CFSG.pCore 2 L) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (L ⧸ CFSG.pCore 2 L) => φ g) hy
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * π ⟨y, hyL⟩ = π ⟨y, hyL⟩ * g * (π ⟨y, hyL⟩)⁻¹ * π ⟨y, hyL⟩ := by rw [this]
          _ = π ⟨y, hyL⟩ * g := by group
      rw [hZX, Subgroup.mem_bot] at hc
      exact hπ1 _ hxD hc
    have hC3 : IsPGroup 3 C := hT3.to_le inf_le_left
    have hCcyc : IsCyclic C := by
      by_contra hnc
      have : Fact (IsPGroup 3 C) := ⟨hC3⟩
      obtain ⟨B, -, hB9, hBel⟩ := CFSG.lemma_4_5_a (R := C) (p := 3) (by norm_num) hnc
      set B' : Subgroup G := B.map C.subtype with hB'
      have hB'C : B' ≤ C := Subgroup.map_subtype_le _
      have hB'9 : Nat.card B' = 9 := by
        rw [hB', Subgroup.card_map_of_injective C.subtype_injective, hB9]
        norm_num
      have hB'exp : ∀ b ∈ B', b ^ 3 = 1 := by
        rintro _ ⟨b, hb, rfl⟩
        have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := B) b hb
        simpa using congrArg Subtype.val this
      have hB'comm : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        have := hBel.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
        exact congrArg (fun w : B => ((w : C) : G)) this
      have hcommDB : ∀ (m : D) (n : B'), Commute (D.subtype m) (B'.subtype n) := by
        intro m n
        exact (hcase n (hB'C n.2).1 m m.2).symm
      set f : D × B' →* G := MonoidHom.noncommCoprod D.subtype B'.subtype hcommDB with hf
      have hfinj : Function.Injective f := by
        rw [injective_iff_map_eq_one]
        rintro ⟨m, n⟩ h
        change (m : G) * n = 1 at h
        have hn : (n : G) = (m : G)⁻¹ := eq_inv_of_mul_eq_one_right h
        have hnD : (n : G) ∈ D := hn ▸ D.inv_mem m.2
        have hn1 : (n : G) = 1 := hCD _ (hB'C n.2) hnD
        have hm1 : (m : G) = 1 := by
          rw [hn1, mul_one] at h
          exact h
        exact Prod.ext (Subtype.ext hm1) (Subtype.ext hn1)
      have h4 : 4 ≤ CFSG.Open.pRank 3 (Q ⊔ L) := by
        refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) ?_ ?_ ?_ f hfinj ?_
        · rintro ⟨a, b⟩ ⟨a', b'⟩
          exact Prod.ext (Subtype.ext (hDcomm _ a.2 _ a'.2)) (Subtype.ext (hB'comm _ b.2 _ b'.2))
        · rintro ⟨a, b⟩
          exact Prod.ext (Subtype.ext (by simpa using hDexp _ a.2))
            (Subtype.ext (by simpa using hB'exp _ b.2))
        · rw [Nat.card_prod, hD9, hB'9]
          norm_num
        · rintro _ ⟨⟨a, b⟩, rfl⟩
          exact Subgroup.mul_mem _ (le_sup_right (a := Q) a.2.2)
            (hTY.le (hB'C b.2).1)
      omega
    have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
      intro a ha b hb
      have := (IsCyclic.isMulCommutative (α := C)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    obtain ⟨a, haQ, b, hbQ, hab⟩ := hQnab
    apply hab
    obtain ⟨da, hda, hca⟩ := hdec a (hQT haQ)
    obtain ⟨db, hdb, hcb⟩ := hdec b (hQT hbQ)
    have ea : a = da * (da⁻¹ * a) := by group
    have eb : b = db * (db⁻¹ * b) := by group
    set ca := da⁻¹ * a
    set cb := db⁻¹ * b
    have h1 : ca * db = db * ca := hcase ca hca.1 db hdb
    have h2 : cb * da = da * cb := hcase cb hcb.1 da hda
    rw [ea, eb]
    calc da * ca * (db * cb) = da * (ca * db) * cb := by group
      _ = da * (db * ca) * cb := by rw [h1]
      _ = (da * db) * (ca * cb) := by group
      _ = (db * da) * (cb * ca) := by rw [hDcomm _ hda _ hdb, hCcomm _ hca _ hcb]
      _ = db * (da * cb) * ca := by group
      _ = db * (cb * da) * ca := by rw [h2]
      _ = db * cb * (da * ca) := by group
  ·
    push Not at hcase
    obtain ⟨s, hsT, d₀, hd₀, hsd⟩ := hcase
    have hzpow : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
    have hCs : ∀ s' ∈ T, (∃ d ∈ D, s' * d ≠ d * s') →
        D ⊓ Subgroup.centralizer ({s'} : Set G) = Subgroup.zpowers z := by
      intro s' hs' hnc
      have h3 := card_inf_centralizer_eq_three hD9 (hTpow s' hs') (hTND s' hs') hnc
      refine (Subgroup.eq_of_le_of_card_ge ?_ (by rw [h3, hzpow])).symm
      exact Subgroup.zpowers_le.mpr ⟨hzD, Subgroup.mem_centralizer_singleton_iff.mpr
        (hzc s' hs').symm⟩
    have hcomm' : ∀ s' ∈ T, ∀ y ∈ D, s' * y * s'⁻¹ * y⁻¹ ∈ Subgroup.zpowers z := by
      intro s' hs' y hy
      by_cases hnc : ∃ d ∈ D, s' * d ≠ d * s'
      · rw [← hCs s' hs' hnc]
        exact commutator_mem_inf_centralizer hD9 hDcomm (hTpow s' hs') (hTND s' hs') hnc hy
      · push Not at hnc
        rw [hnc y hy, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
    have hzT' : ∀ w ∈ Subgroup.zpowers z, ∀ t ∈ T, t * w = w * t := by
      rintro _ ⟨k, rfl⟩ t ht
      exact (Commute.zpow_right (hzc t ht) k).eq
    set x := π ⟨z, hzL⟩ with hx
    have hxS : x ∈ (S : Subgroup (L ⧸ CFSG.pCore 2 L)) := hπmem z hzD
    have hx1 : x ≠ 1 := fun h => hz1 (hπ1 z hzD h)
    obtain ⟨gb, hgN, hgx⟩ := hFus _ p e he hiso h91 h98 S x hxS hx1
    obtain ⟨g, rfl⟩ := hπs gb
    set O := CFSG.Open.pCoreOf 2 L with hO
    have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    have hDO : D ≤ Subgroup.normalizer (O : Set G) :=
      inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    have hOD : O ⊓ D = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨hwO, hwD⟩
      obtain ⟨j, hj⟩ := hO2 ⟨w, hwO⟩
      exact (Subgroup.mem_bot).mpr (eq_one_of_pow_two_pow_of_pow_three_pow (j := j) (k := 1)
        (by simpa using congrArg Subtype.val hj) (by rw [pow_one]; exact hDexp w hwD))
    set B := O ⊔ D with hB
    have hBcard : Nat.card B = Nat.card O * 9 := by
      rw [hB, CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hDO hOD, hD9]
    have hBfact : (Nat.card B).factorization 3 = 2 := by
      obtain ⟨a, ha⟩ := hO2.exists_card_eq
      rw [hBcard, ha, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by
          intro h3
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
            (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
          omega), zero_add, show (9 : ℕ) = 3 ^ 2 by norm_num,
        Nat.Prime.factorization_pow Nat.prime_three]
      simp
    have hDB : IsSylowOf 3 D B := CFSG.ABGLocalTools.isSylowOf_of_card le_sup_right (by
      rw [hD9, hBfact]; norm_num)
    have hBL : B ≤ L := sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 L) inf_le_right
    have hπB : ∀ b (hb : b ∈ B), π ⟨b, hBL hb⟩ ∈ Dbar := by
      intro b hb
      rw [← SetLike.mem_coe, hB, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDO] at hb
      obtain ⟨o, ho, d, hd, rfl⟩ := hb
      have hoL : o ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L ho
      have e : (⟨o * d, hBL (Subgroup.mul_mem_sup ho hd)⟩ : L) = ⟨o, hoL⟩ * ⟨d, hd.2⟩ := rfl
      have ho1 : π ⟨o, hoL⟩ = 1 := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          Step1911EndProof.mem_pCore_iff]
        exact ho
      rw [e, map_mul, ho1, one_mul]
      exact hπmem d hd
    have hgDB : IsSylowOf 3 (D.map (MulAut.conj (g : G)).toMonoidHom) B := by
      refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ (by
        rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective, hD9, hBfact]
        norm_num)
      rintro _ ⟨d, hd, rfl⟩
      change (g : G) * d * (g : G)⁻¹ ∈ B
      have hgdL : (g : G) * d * (g : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem g.2 hd.2) (L.inv_mem g.2)
      have h1 : π ⟨(g : G) * d * (g : G)⁻¹, hgdL⟩ ∈ Dbar := by
        have e : (⟨(g : G) * d * (g : G)⁻¹, hgdL⟩ : L) = g * ⟨d, hd.2⟩ * g⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hgN _).mp (hπmem d hd)
      obtain ⟨d₁, hd₁, hd₁e⟩ := h1
      have hd₁D : (d₁ : G) ∈ D := Subgroup.mem_subgroupOf.mp hd₁
      have hm : (d₁ : G)⁻¹ * ((g : G) * d * (g : G)⁻¹) ∈ O := by
        have := QuotientGroup.eq.mp hd₁e
        rw [Step1911EndProof.mem_pCore_iff] at this
        simpa using this
      have : (g : G) * d * (g : G)⁻¹ = (d₁ : G) * ((d₁ : G)⁻¹ * ((g : G) * d * (g : G)⁻¹)) := by
        group
      rw [this, hB, sup_comm]
      exact Subgroup.mul_mem_sup hd₁D hm
    obtain ⟨b, hbB, hbD⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hDB hgDB
    set n : G := b⁻¹ * (g : G) with hn
    have hnL : n ∈ L := L.mul_mem (L.inv_mem (hBL hbB)) g.2
    have hnD : ∀ d ∈ D, n * d * n⁻¹ ∈ D := by
      intro d hd
      have h1 : (g : G) * d * (g : G)⁻¹ ∈ D.map (MulAut.conj b).toMonoidHom := by
        rw [← hbD]
        exact ⟨d, hd, rfl⟩
      obtain ⟨d₂, hd₂, hd₂e⟩ := h1
      change b * d₂ * b⁻¹ = (g : G) * d * (g : G)⁻¹ at hd₂e
      have : n * d * n⁻¹ = d₂ := by
        rw [hn]
        calc b⁻¹ * (g : G) * d * (b⁻¹ * (g : G))⁻¹ = b⁻¹ * ((g : G) * d * (g : G)⁻¹) * b := by
              group
          _ = d₂ := by rw [← hd₂e]; group
      rw [this]
      exact hd₂
    set z' := n * z * n⁻¹ with hz'
    have hz'D : z' ∈ D := hnD z hzD
    have hz'z : z' ∉ Subgroup.zpowers z := by
      intro hmem
      apply hgx
      have hz'L : z' ∈ L := hz'D.2
      have e1 : (⟨z', hz'L⟩ : L) = ⟨b, hBL hbB⟩⁻¹ * (g * ⟨z, hzL⟩ * g⁻¹) * ⟨b, hBL hbB⟩ := by
        apply Subtype.ext
        simp only [hz', hn, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hb' := hπB b hbB
      have hgz : π (g * ⟨z, hzL⟩ * g⁻¹) ∈ Dbar := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hxS
      have hDbc : ∀ u ∈ Dbar, ∀ v ∈ Dbar, u * v = v * u := by
        intro u hu v hv
        have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := Dbar)
          (by rw [hS9]; norm_num)).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
        exact congrArg Subtype.val this
      have h2 : π ⟨z', hz'L⟩ = π g * x * (π g)⁻¹ := by
        rw [e1, map_mul, map_mul, map_inv, hDbc _ (Subgroup.inv_mem _ hb') _ hgz,
          inv_mul_cancel_right, map_mul, map_mul, map_inv]
      rw [← h2]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have e2 : (⟨z', hz'L⟩ : L) = (⟨z, hzL⟩ : L) ^ k := Subtype.ext (by simp [← hk])
      rw [e2, map_zpow]
    have hz'T : z' ∈ T := hz'D.1
    have hz'2 : (⟨z', hz'T⟩ : T) ∈ Subgroup.upperCentralSeries T 2 := by
      rw [mem_upperCentralSeries_two_iff_of_mem]
      intro q hq r hr
      have h1 := hcomm' q hq z' hz'D
      have e : z' * q * z'⁻¹ * q⁻¹ = (q * z' * q⁻¹ * z'⁻¹)⁻¹ := by group
      rw [e]
      exact hzT' _ (Subgroup.inv_mem _ h1) r hr
    have hz'Z : (⟨z', hz'T⟩ : T) ∉ Subgroup.center T := by
      intro h
      apply hz'z
      rw [← hCs s hsT ⟨d₀, hd₀, hsd⟩]
      refine ⟨hz'D, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact ((mem_center_iff_of_mem hz'T).mp h s hsT).symm
    obtain ⟨hzP, h2, hZ⟩ := conj_mem_upperCentralSeries_two_of_eq hz'T hz'2 hz'Z n⁻¹
      (y := z) (by rw [hz']; group)
    refine ⟨T.map (MulAut.conj n⁻¹).toMonoidHom, ?_, hT3.map _, hzP, h2, hZ⟩
    rintro _ ⟨t, ht, rfl⟩
    have hn' : n⁻¹ ∈ Q ⊔ L := le_sup_right (a := Q) (L.inv_mem hnL)
    exact (Q ⊔ L).mul_mem ((Q ⊔ L).mul_mem hn' (hTY.le ht)) ((Q ⊔ L).inv_mem hn')

end Step1915WProof

end CFSG.RankThree.PartTwo.Sec19
