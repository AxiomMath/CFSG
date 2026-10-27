module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End2Proof2126
public import CFSG.RankThree.PartTwo.Sec21.Item2119End4ProofGL2
import CFSG.RankThree.PartTwo.Sec21.Item2119EndProof2124
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof2120
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

@[expose] def Item2126P : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        ∀ n p : ℕ, Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) → p.Prime → 3 < p →
          p ∣ 2 ^ n - 1 →
          ∃ P W₀ : Subgroup G, IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
            W₀ ≤ Subgroup.normalizer (A : Set G) ∧ W₀ ≤ Subgroup.normalizer (P : Set G) ∧
            W₀ ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (A : Set G) ∧
            trivOnQuot A (Subgroup.zpowers d) ≤ starOf A W₀

namespace Item2119End4Proof

variable {G : Type} [Group G]

theorem conj_inv_of_trivOnQuot {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {d t w : G} (hdA : d ∈ A) (htN : t ∈ Subgroup.normalizer (A : Set G))
    (ht : ∀ x ∈ A, x⁻¹ * (t * x * t⁻¹) ∈ Subgroup.zpowers d) (htd : t * d * t⁻¹ = d⁻¹)
    (hw : ∀ x ∈ A, x⁻¹ * (w * x * w⁻¹) ∈ Subgroup.zpowers d) (hwd : w * d * w⁻¹ = d) :
    ∀ x ∈ A, (t * w * t⁻¹ * w) * x * (t * w * t⁻¹ * w)⁻¹ = x := by
  have hdA' : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have htδ : ∀ δ ∈ Subgroup.zpowers d, t * δ * t⁻¹ = δ⁻¹ := by
    intro δ hδ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, htd, inv_zpow]
  have ht'δ : ∀ δ ∈ Subgroup.zpowers d, t⁻¹ * δ * t = δ⁻¹ := by
    intro δ hδ
    have h1 := htδ δ⁻¹ (Subgroup.inv_mem _ hδ)
    rw [inv_inv] at h1
    calc t⁻¹ * δ * t = t⁻¹ * (t * δ⁻¹ * t⁻¹) * t := by rw [h1]
      _ = δ⁻¹ := by group
  have hwδ : ∀ δ ∈ Subgroup.zpowers d, w * δ * w⁻¹ = δ := by
    intro δ hδ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hwd]
  intro x hx
  set δ₁ := x⁻¹ * (w * x * w⁻¹) with hδ₁
  have hδ₁d : δ₁ ∈ Subgroup.zpowers d := hw x hx
  have hwx : w * x * w⁻¹ = x * δ₁ := by rw [hδ₁]; group
  have hx' : t⁻¹ * x * t ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) x).mp hx
    simpa using this
  set ε := x⁻¹ * (t⁻¹ * x * t) with hε
  have hεd : ε ∈ Subgroup.zpowers d := by
    have h1 := ht (t⁻¹ * x * t) hx'
    have h2 : (t⁻¹ * x * t)⁻¹ * (t * (t⁻¹ * x * t) * t⁻¹) = ε⁻¹ := by
      rw [hε]
      group
    rw [h2] at h1
    simpa using Subgroup.inv_mem _ h1
  have htx : t⁻¹ * x * t = x * ε := by rw [hε]; group
  have htx' : t * x * t⁻¹ = x * ε := by
    have h1 : x = t * (x * ε) * t⁻¹ := by rw [← htx]; group
    have h2 : t * (x * ε) * t⁻¹ = (t * x * t⁻¹) * (t * ε * t⁻¹) := by group
    rw [h2, htδ ε hεd] at h1
    calc t * x * t⁻¹ = (t * x * t⁻¹) * ε⁻¹ * ε := by group
      _ = x * ε := by rw [← h1]
  have hεA : ε ∈ A := hdA' hεd
  have hδ₁A : δ₁ ∈ A := hdA' hδ₁d
  calc (t * w * t⁻¹ * w) * x * (t * w * t⁻¹ * w)⁻¹
      = t * (w * (t⁻¹ * (w * x * w⁻¹) * t) * w⁻¹) * t⁻¹ := by group
    _ = t * (w * ((t⁻¹ * x * t) * (t⁻¹ * δ₁ * t)) * w⁻¹) * t⁻¹ := by rw [hwx]; group
    _ = t * (w * (x * ε * δ₁⁻¹) * w⁻¹) * t⁻¹ := by rw [htx, ht'δ δ₁ hδ₁d]
    _ = t * ((w * x * w⁻¹) * (w * ε * w⁻¹) * (w * δ₁⁻¹ * w⁻¹)) * t⁻¹ := by group
    _ = t * (x * δ₁ * ε * δ₁⁻¹) * t⁻¹ := by
        rw [hwx, hwδ ε hεd, hwδ δ₁⁻¹ (Subgroup.inv_mem _ hδ₁d)]
    _ = t * (x * ε) * t⁻¹ := by
        rw [show x * δ₁ * ε * δ₁⁻¹ = x * (δ₁ * ε) * δ₁⁻¹ by group, hcomm δ₁ hδ₁A ε hεA]
        group
    _ = (t * x * t⁻¹) * (t * ε * t⁻¹) := by group
    _ = x := by rw [htx', htδ ε hεd]; group

theorem comm_of_trivOnQuot {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {d w w' : G} (hdA : d ∈ A)
    (hw : ∀ x ∈ A, x⁻¹ * (w * x * w⁻¹) ∈ Subgroup.zpowers d) (hwd : w * d * w⁻¹ = d)
    (hw' : ∀ x ∈ A, x⁻¹ * (w' * x * w'⁻¹) ∈ Subgroup.zpowers d) (hw'd : w' * d * w'⁻¹ = d) :
    ∀ x ∈ A, (w * w') * x * (w * w')⁻¹ = (w' * w) * x * (w' * w)⁻¹ := by
  have hdA' : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have hfix : ∀ v : G, v * d * v⁻¹ = d → ∀ δ ∈ Subgroup.zpowers d, v * δ * v⁻¹ = δ := by
    intro v hv δ hδ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hv]
  intro x hx
  set δ := x⁻¹ * (w * x * w⁻¹) with hδ
  set δ' := x⁻¹ * (w' * x * w'⁻¹) with hδ'
  have hwx : w * x * w⁻¹ = x * δ := by rw [hδ]; group
  have hw'x : w' * x * w'⁻¹ = x * δ' := by rw [hδ']; group
  have hδA : δ ∈ A := hdA' (hw x hx)
  have hδ'A : δ' ∈ A := hdA' (hw' x hx)
  calc (w * w') * x * (w * w')⁻¹ = w * (w' * x * w'⁻¹) * w⁻¹ := by group
    _ = (w * x * w⁻¹) * (w * δ' * w⁻¹) := by rw [hw'x]; group
    _ = x * δ * δ' := by rw [hwx, hfix w hwd δ' (hw' x hx)]
    _ = x * δ' * δ := by rw [mul_assoc, hcomm δ hδA δ' hδ'A, ← mul_assoc]
    _ = (w' * x * w'⁻¹) * (w' * δ * w'⁻¹) := by rw [hw'x, hfix w' hw'd δ (hw x hx)]
    _ = (w' * w) * x * (w' * w)⁻¹ := by
        rw [show (w' * w) * x * (w' * w)⁻¹ = w' * (w * x * w⁻¹) * w'⁻¹ by group, hwx]
        group

end Item2119End4Proof

open Item2119End4Proof Item2119EndProof

theorem item2126Torus_of
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hP : Item2126P) : Item2126Torus := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf n p hLn hp hp3 hpd
  obtain ⟨P, W₀, hPe, hP2, hWA, hWP, hWC, hT⟩ := hP G A E U c L d U₀ a X hE h23 h24 Lf hLf n p hLn
    hp hp3 hpd
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨eXL⟩, hdX, hdTX, -⟩ := h23
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨m, -, -, ⟨eL⟩⟩ := hcfg.lthree
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hE.mem_U₀.1
      mem_pair := hE.mem_pair }
  obtain ⟨hn', he', hC', h27', hS3'⟩ :=
    Item21LateProof.case7_of_lBar_L3 h211 h2116 hpair' (eXL.trans eL)
  have hcfgX : Config2119 G A E U₀ a X :=
    ⟨hpair', ⟨m, hn', he', ⟨eXL.trans eL⟩⟩, hC', h27', hS3'⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs'.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, hw3, hwd₀, hwA, hwmove⟩,
    t, ⟨htL, htN⟩, htd₀⟩ := Item21Late2Proof.frame_of h45 h66 hcfg
  obtain ⟨-, d', -, -, -, hTU', -, -, -, ⟨w', ⟨hw'X, hw'N⟩, hw'3, hw'd', hw'A, hw'move⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfgX
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU d hE.mem_d hd1 hE.type_d)
  have hZ' : Subgroup.zpowers d' = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU' d ⟨hdA, hdX⟩ hd1 hdTX)
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  have hw'd : w' * d * w'⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hw'd' (by rw [hZ']; exact Subgroup.mem_zpowers d)
  rw [hZ₀] at hwA
  rw [hZ'] at hw'A
  have htd : t * d * t⁻¹ = d⁻¹ := by
    have hdd₀ : d ∈ Subgroup.zpowers d₀ := by rw [hZ₀]; exact Subgroup.mem_zpowers d
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdd₀
    rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, htd₀, inv_zpow]
  have hwc : w * c * w⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL), mul_inv_cancel_right]
  have hw'a : w' * a * w'⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hw'X), mul_inv_cancel_right]
  have htT : A.normalizerMonoidHom ⟨t, htN⟩ ∈ trivOnQuot A (Subgroup.zpowers d) := by
    rw [← h24]
    exact Subgroup.mem_sup_right ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.mpr htL, rfl⟩
  have ht : ∀ x ∈ A, x⁻¹ * (t * x * t⁻¹) ∈ Subgroup.zpowers d := by
    intro x hx
    exact htT ⟨x, hx⟩
  have hv := conj_inv_of_trivOnQuot hcomm hdA htN ht htd hwA hwd
  have hv' := conj_inv_of_trivOnQuot hcomm hdA htN ht htd hw'A hw'd
  have hww' := comm_of_trivOnQuot hcomm hdA hwA hwd hw'A hw'd
  set φ := A.normalizerMonoidHom with hφ
  set τ := φ ⟨t, htN⟩ with hτ
  set ω := φ ⟨w, hwN⟩ with hω
  set ω' := φ ⟨w', hw'N⟩ with hω'
  have hφext : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (A : Set G)),
      (∀ x ∈ A, g * x * g⁻¹ = x) → φ ⟨g, hg⟩ = 1 := by
    intro g hg h
    ext x
    exact h x x.2
  have hvN : t * w * t⁻¹ * w ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hwN) (Subgroup.inv_mem _ htN))
      hwN
  have hv'N : t * w' * t⁻¹ * w' ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hw'N)
      (Subgroup.inv_mem _ htN)) hw'N
  have hτω : τ * ω * τ⁻¹ * ω = 1 := by
    have h1 := hφext _ hvN hv
    have e : (⟨t * w * t⁻¹ * w, hvN⟩ : ↥(Subgroup.normalizer (A : Set G))) =
        ⟨t, htN⟩ * ⟨w, hwN⟩ * ⟨t, htN⟩⁻¹ * ⟨w, hwN⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv] at h1
    exact h1
  have hτω' : τ * ω' * τ⁻¹ * ω' = 1 := by
    have h1 := hφext _ hv'N hv'
    have e : (⟨t * w' * t⁻¹ * w', hv'N⟩ : ↥(Subgroup.normalizer (A : Set G))) =
        ⟨t, htN⟩ * ⟨w', hw'N⟩ * ⟨t, htN⟩⁻¹ * ⟨w', hw'N⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv] at h1
    exact h1
  have hωω' : ω * ω' = ω' * ω := by
    have hN1 : w * w' ∈ Subgroup.normalizer (A : Set G) := Subgroup.mul_mem _ hwN hw'N
    have hN2 : w' * w ∈ Subgroup.normalizer (A : Set G) := Subgroup.mul_mem _ hw'N hwN
    have h1 : φ ⟨w * w', hN1⟩ = φ ⟨w' * w, hN2⟩ := by
      ext x
      exact hww' x x.2
    have e1 : (⟨w * w', hN1⟩ : ↥(Subgroup.normalizer (A : Set G))) = ⟨w, hwN⟩ * ⟨w', hw'N⟩ :=
      rfl
    have e2 : (⟨w' * w, hN2⟩ : ↥(Subgroup.normalizer (A : Set G))) = ⟨w', hw'N⟩ * ⟨w, hwN⟩ :=
      rfl
    rw [e1, e2, map_mul, map_mul] at h1
    exact h1
  have hω3 : ω ^ 3 = 1 := by
    have e : (⟨w, hwN⟩ : ↥(Subgroup.normalizer (A : Set G))) ^ 3 = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow]
      exact hw3
    rw [hω, ← map_pow, e, map_one]
  have hω'3 : ω' ^ 3 = 1 := by
    have e : (⟨w', hw'N⟩ : ↥(Subgroup.normalizer (A : Set G))) ^ 3 = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow]
      exact hw'3
    rw [hω', ← map_pow, e, map_one]
  have hcommω : ⁅τ, ω⁆ = ω := by
    rw [commutatorElement_def]
    calc τ * ω * τ⁻¹ * ω⁻¹ = (τ * ω * τ⁻¹ * ω) * (ω⁻¹ * ω⁻¹) := by group
      _ = ω := by
        rw [hτω, one_mul]
        calc ω⁻¹ * ω⁻¹ = ω⁻¹ * ω⁻¹ * ω ^ 3 := by rw [hω3, mul_one]
          _ = ω := by group
  have hcommω' : ⁅τ, ω'⁆ = ω' := by
    rw [commutatorElement_def]
    calc τ * ω' * τ⁻¹ * ω'⁻¹ = (τ * ω' * τ⁻¹ * ω') * (ω'⁻¹ * ω'⁻¹) := by group
      _ = ω' := by
        rw [hτω', one_mul]
        calc ω'⁻¹ * ω'⁻¹ = ω'⁻¹ * ω'⁻¹ * ω' ^ 3 := by rw [hω'3, mul_one]
          _ = ω' := by group
  have hτW : τ ∈ starOf A W₀ := hT htT
  have hωW : ω ∈ starOf A W₀ := by
    apply hT
    rw [← h24]
    exact Subgroup.mem_sup_right ⟨⟨w, hwN⟩, Subgroup.mem_subgroupOf.mpr hwL, rfl⟩
  have hω'W : ω' ∈ starOf A W₀ := by
    apply hT
    rw [← h24]
    exact Subgroup.mem_sup_left ⟨⟨w', hw'N⟩, Subgroup.mem_subgroupOf.mpr hw'X, rfl⟩
  have hωC : ω ∈ ⁅starOf A W₀, starOf A W₀⁆ := by
    rw [← hcommω]
    exact Subgroup.commutator_mem_commutator hτW hωW
  have hω'C : ω' ∈ ⁅starOf A W₀, starOf A W₀⁆ := by
    rw [← hcommω']
    exact Subgroup.commutator_mem_commutator hτW hω'W
  set T := Subgroup.zpowers ω ⊔ Subgroup.zpowers ω' with hTdef
  have hTle : T ≤ ⁅starOf A W₀, starOf A W₀⁆ :=
    sup_le (Subgroup.zpowers_le.mpr hωC) (Subgroup.zpowers_le.mpr hω'C)
  have hexp : ∀ g ∈ T, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨i, -, j, -, rfl⟩ :=
      Item21Late2Proof.exists_pow_mul_pow_of_mem_sup hωω' hω3 hω'3 hg
    rw [(Commute.pow_pow (show Commute ω ω' from hωω') i j).mul_pow, ← pow_mul, ← pow_mul,
      mul_comm i, mul_comm j, pow_mul, pow_mul, hω3, hω'3, one_pow, one_pow, one_mul]
  have hT3 : IsPGroup 3 T := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  have hB9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA c hcA) hd3 (h3 c hcA) hd1
    (fun h => hcL ((Subgroup.zpowers_le.mpr hE.mem_d.2) h))
  have haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact not_mem_sup_of_config2119End hE
  have hω1 : ω ≠ 1 := by
    intro h
    obtain ⟨y, hyA, hy⟩ := hwmove
    apply hy
    have := congrArg (fun σ : MulAut A => ((σ ⟨y, hyA⟩ : A) : G)) h
    exact this
  have hω'ω : ω' ∉ Subgroup.zpowers ω := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hc' : w' * c * w'⁻¹ = c := by
      have h1 := congrArg (fun σ : MulAut A => ((σ ⟨c, hcA⟩ : A) : G)) hk
      have h2 : ((ω ^ k) ⟨c, hcA⟩ : A) = ⟨c, hcA⟩ := by
        have hωc : ω ⟨c, hcA⟩ = ⟨c, hcA⟩ := Subtype.ext hwc
        have key : ∀ j : ℤ, (ω ^ j) ⟨c, hcA⟩ = ⟨c, hcA⟩ := by
          intro j
          induction j using Int.induction_on with
          | zero => rfl
          | succ j ih =>
            rw [zpow_add_one, MulAut.mul_apply, hωc, ih]
          | pred j ih =>
            rw [zpow_sub_one, MulAut.mul_apply]
            have hinv : ω⁻¹ ⟨c, hcA⟩ = ⟨c, hcA⟩ := by
              conv_lhs => rw [← hωc]
              exact MulAut.inv_apply_self _ _ _
            rw [hinv, ih]
        exact key k
      rw [h2] at h1
      exact h1.symm
    obtain ⟨y, hyA, hy⟩ := hw'move
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hw'a hw'd hc' y hyA)
  have hT9 : Nat.card T = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers hωω' hω3 hω'3 hω1 hω'ω
  have hTc := isCyclic_of_le_commutator_starOf hp3 hPe hP2 hWA hWP hWC T hT3 hTle
  obtain ⟨g, hg⟩ := hTc.exists_generator
  have hord : orderOf g = 9 := by
    rw [← hT9]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hexp g g.2)
  have := orderOf_dvd_of_pow_eq_one hg3
  rw [hord] at this
  norm_num at this

end CFSG.RankThree.PartTwo.Sec21
