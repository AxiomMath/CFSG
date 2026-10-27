module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Unique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yh
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.Quasithin.MS93.S59Set

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Q : Type} [Group Q] [Finite Q]

open scoped commutatorElement

private theorem normalizer_le_normalizer_oUpperTwo' {X : Subgroup Q} :
    Subgroup.normalizer (X : Set Q) ≤ Subgroup.normalizer (S17.oUpperTwo X : Set Q) := by
  intro g hg
  have hmap : (S17.oUpperTwo X).map (MulAut.conj g).toMonoidHom ≤ S17.oUpperTwo X := by
    rw [S17.oUpperTwo_eq_closure, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hxX, hxodd⟩, rfl⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxX, by
      change Odd (orderOf ((MulAut.conj g) x))
      rw [MulEquiv.orderOf_eq]
      exact hxodd⟩
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hmap ?_)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem pCoreOf_eq_inf {P X : Subgroup Q} (hXP : X ≤ P)
    (hX : P ≤ Subgroup.normalizer (X : Set Q)) :
    CFSG.Open.pCoreOf 2 X = X ⊓ CFSG.Open.pCoreOf 2 P := by
  refine le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X) ?_) ?_
  · refine CFSG.LieType.BorelTits.le_pCoreOf 2 ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXP)
      ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXP)]
    exact hX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  · have hN : X ⊓ CFSG.Open.pCoreOf 2 P ≤ CFSG.Open.pCoreOf 2 P := inf_le_right
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).to_le hN)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    refine Subgroup.le_normalizer_inf ?_ ?_
    · exact Subgroup.le_normalizer
    · exact hXP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)

private theorem pCoreOf_eq_of_isLeviFamily {P : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    (hL : IsLeviFamily P d L) (i : Fin d) :
    CFSG.Open.pCoreOf 2 (L i) = CFSG.Open.pCoreOf 2 P := by
  have hPN : P ≤ Subgroup.normalizer (L i : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hL.le i)).mp (hL.normal i)
  rw [pCoreOf_eq_inf (hL.le i) hPN, inf_eq_right.mpr (hL.pCoreOf_le i)]

private theorem subsingleton_of_isPGroup_two_of_commutator_eq_top {H : Type} [Group H] [Finite H]
    (hp : IsPGroup 2 H) (hperf : commutator H = ⊤) : Subsingleton H := by
  by_contra h
  have : Nontrivial H := not_subsingleton_iff_nontrivial.mp h
  have : Group.IsNilpotent H := hp.isNilpotent
  have : Group.IsSolvable H := IsNilpotent.to_isSolvable
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial H
  rw [hperf] at hlt
  exact lt_irrefl _ hlt

private theorem bar2_equiv_bar2_sup_pCoreOf {P X : Subgroup Q} (hXP : X ≤ P)
    (hX : P ≤ Subgroup.normalizer (X : Set Q)) :
    Nonempty (Bar2 (X ⊔ CFSG.Open.pCoreOf 2 P) ≃* Bar2 X) := by
  let O : Subgroup Q := CFSG.Open.pCoreOf 2 P
  let N : Subgroup Q := X ⊔ O
  have hOP : O ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hXO : X ≤ Subgroup.normalizer (O : Set Q) :=
    hXP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hXN : X ≤ N := le_sup_left
  have hON : O ≤ N := le_sup_right
  have hNP : N ≤ P := sup_le hXP hOP
  have hPN : P ≤ Subgroup.normalizer (N : Set Q) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX hp)),
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P) hp))]
  have hNnorm : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  have hcoreN : CFSG.Open.pCoreOf 2 N = O := by
    rw [pCoreOf_eq_inf hNP hPN, inf_eq_right.mpr hON]
  have hcoreX : CFSG.Open.pCoreOf 2 X = X ⊓ O := pCoreOf_eq_inf hXP hX
  have hcoreN_sub : CFSG.pCore 2 ↥N = O.subgroupOf N := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 N, hcoreN]
  have hcoreX_sub : CFSG.pCore 2 ↥X = O.subgroupOf X := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 X, hcoreX, Subgroup.inf_subgroupOf_left]
  let qX : ↥X →* Bar2 N :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥N)).comp (Subgroup.inclusion hXN)
  have hker : qX.ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker,
      show qX x = (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) ⟨x, hXN x.2⟩ from rfl,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcoreN_sub, Subgroup.mem_subgroupOf,
      hcoreX_sub, Subgroup.mem_subgroupOf]
  have hsurj : Function.Surjective qX := by
    intro y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N) y
    have hn : (n : Q) ∈ (↑N : Set Q) := n.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X O hXO] at hn
    obtain ⟨x, hxX, o, hO, hxo⟩ := hn
    refine ⟨⟨x, hxX⟩, ?_⟩
    have hxn : (⟨x, hXN hxX⟩ : ↥N)⁻¹ * n = ⟨o, hON hO⟩ := by
      ext
      change x⁻¹ * (n : Q) = o
      rw [← hxo]
      group
    have ho : (⟨o, hON hO⟩ : ↥N) ∈ CFSG.pCore 2 ↥N := by
      rw [hcoreN_sub, Subgroup.mem_subgroupOf]
      exact hO
    rw [show qX ⟨x, hxX⟩ = (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) ⟨x, hXN hxX⟩ from rfl,
      QuotientGroup.mk'_eq_mk']
    exact ⟨⟨o, hON hO⟩, ho, by rw [← hxn]; group⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective qX hsurj)).symm⟩

private theorem not_isMulCommutative_of_isL2 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsL2 X n) (hn : 3 ≤ n) : ¬ IsMulCommutative X := by
  intro hcomm
  have : IsMulCommutative X := hcomm
  have hsimple : IsSimpleGroup X := S19.isSimpleGroup_of_isL2_or_isSz (Or.inl h)
  have hprime : (Nat.card X).Prime := (Group.is_simple_iff_prime_card (α := X)).1 hsimple
  obtain ⟨hEv, -⟩ := P22fin.isL2Ev_of_isL2 h
  have h6 : 6 < Nat.card X := P22y.six_lt_card_of_isL2Ev hEv (by omega)
  have heven : Even (Nat.card X) := S19.even_card_of_isL2_or_isSz (Or.inl h)
  have h2 : Nat.card X = 2 :=
    (Nat.Prime.dvd_iff_eq hprime (by norm_num : (2 : ℕ) ≠ 1)).1 heven.two_dvd
  omega

private theorem eq_pCoreOf_or_eq_of_normal_of_isSimple {P N X : Subgroup Q}
    (hNP : N ≤ P) (hNnorm : (N.subgroupOf P).Normal)
    (hON : CFSG.Open.pCoreOf 2 P ≤ N) (hsimple : IsSimpleGroup (Bar2 N))
    (hXN : X ≤ N) (hXnorm : (X.subgroupOf N).Normal)
    (hOX : CFSG.Open.pCoreOf 2 P ≤ X) :
    X = CFSG.Open.pCoreOf 2 P ∨ X = N := by
  have hPN : P ≤ Subgroup.normalizer (N : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hNnorm
  have hcoreN : CFSG.Open.pCoreOf 2 N = CFSG.Open.pCoreOf 2 P := by
    rw [pCoreOf_eq_inf hNP hPN, inf_eq_right.mpr hON]
  have hcoreN_sub : CFSG.pCore 2 ↥N = (CFSG.Open.pCoreOf 2 P).subgroupOf N := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 N, hcoreN]
  let q : ↥N →* Bar2 N := QuotientGroup.mk' (CFSG.pCore 2 ↥N)
  have hnormal : ((X.subgroupOf N).map q).Normal :=
    hXnorm.map q (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X.subgroupOf N).map q) with hbot | htop
  · left
    have hX'sub : X.subgroupOf N ≤ CFSG.pCore 2 ↥N := by
      intro x hx
      have hmem : q x ∈ (X.subgroupOf N).map q := Subgroup.mem_map_of_mem q hx
      rw [hbot, Subgroup.mem_bot] at hmem
      have hxk : x ∈ q.ker := MonoidHom.mem_ker.mpr hmem
      have hqker : q.ker = CFSG.pCore 2 ↥N := QuotientGroup.ker_mk' _
      rwa [hqker] at hxk
    have hXle : X ≤ CFSG.Open.pCoreOf 2 P := by
      intro x hx
      have hx' : (⟨x, hXN hx⟩ : ↥N) ∈ CFSG.pCore 2 ↥N :=
        hX'sub (Subgroup.mem_subgroupOf.mpr hx)
      rw [hcoreN_sub, Subgroup.mem_subgroupOf] at hx'
      exact hx'
    exact le_antisymm hXle hOX
  · right
    have hX'top : X.subgroupOf N = ⊤ := by
      have h1 : Subgroup.comap q ((X.subgroupOf N).map q) = (X.subgroupOf N) ⊔ q.ker :=
        Subgroup.comap_map_eq q _
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', hcoreN_sub] at h1
      have hker_le : (CFSG.Open.pCoreOf 2 P).subgroupOf N ≤ X.subgroupOf N :=
        Subgroup.subgroupOf_mono N hOX
      rw [h1]
      exact (sup_eq_left.mpr hker_le).symm
    exact le_antisymm hXN (Subgroup.subgroupOf_eq_top.mp hX'top)


omit [Finite Q] in
private theorem commutator_sup_pCoreOf_eq_of_isQuasisimple {X : Subgroup Q}
    (hq : CFSG.Open.IsQuasisimple (Bar2 X)) :
    ⁅X, X⁆ ⊔ CFSG.Open.pCoreOf 2 X = X := by
  let N : Subgroup Q := CFSG.Open.pCoreOf 2 X
  have hNle : N ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hker : CFSG.pCore 2 ↥X = N.subgroupOf X := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 X]
  let q : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hmapq : Subgroup.map q (commutator ↥X) = commutator (Bar2 X) := by
    change Subgroup.map q ⁅(⊤ : Subgroup ↥X), ⊤⁆ = ⁅(⊤ : Subgroup (Bar2 X)), ⊤⁆
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  rw [hq.1] at hmapq
  have hle : commutator ↥X ≤ (⁅X, X⁆).subgroupOf X := by
    rw [← Subgroup.map_subtype_commutator X]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem X.subtype hx)
  have htop : Subgroup.map q ((⁅X, X⁆).subgroupOf X) = ⊤ := by
    rw [eq_top_iff, ← hmapq]
    exact Subgroup.map_mono hle
  have h1 : Subgroup.comap q (Subgroup.map q ((⁅X, X⁆).subgroupOf X)) =
      (⁅X, X⁆).subgroupOf X ⊔ q.ker := Subgroup.comap_map_eq q _
  rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', hker] at h1
  have hsup : (⁅X, X⁆ ⊔ N).subgroupOf X = ⊤ := by
    rw [Subgroup.subgroupOf_sup (Subgroup.commutator_le_self X) hNle, h1]
  exact le_antisymm (sup_le (Subgroup.commutator_le_self X) hNle)
    (Subgroup.subgroupOf_eq_top.mp hsup)


private theorem isPGroup_quotient_oUpperTwo (X N : Subgroup Q)
    [hN : (N.subgroupOf X).Normal] (hJN : S17.oUpperTwo X ≤ N) :
    IsPGroup 2 (↥X ⧸ N.subgroupOf X) := by
  rw [IsPGroup.iff_orderOf]
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf X) y
  obtain ⟨a, m, hm, hx⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hodd : Odd (orderOf (x ^ 2 ^ a)) := by
    rw [orderOf_pow_of_dvd (by positivity) (hx ▸ dvd_mul_right _ _), hx,
      Nat.mul_div_cancel_left m (by positivity)]
    exact hm
  have hoddQ : Odd (orderOf ((x : Q) ^ 2 ^ a)) := by
    rw [← Subgroup.coe_pow, Subgroup.orderOf_coe]
    exact hodd
  have hmem : x ^ 2 ^ a ∈ N.subgroupOf X := by
    rw [Subgroup.mem_subgroupOf]
    refine hJN ?_
    rw [S17.oUpperTwo_eq_closure]
    exact Subgroup.subset_closure ⟨by rw [Subgroup.coe_pow]; exact X.pow_mem x.2 _, hoddQ⟩
  have hpow : (QuotientGroup.mk' (N.subgroupOf X) x) ^ 2 ^ a = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  have hdvd : orderOf (QuotientGroup.mk' (N.subgroupOf X) x) ∣ 2 ^ a :=
    orderOf_dvd_iff_pow_eq_one.mpr hpow
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, hk⟩


private theorem oUpperTwo_sup_pCoreOf_eq_of_isQuasisimple {X : Subgroup Q}
    (hq : CFSG.Open.IsQuasisimple (Bar2 X)) :
    S17.oUpperTwo X ⊔ CFSG.Open.pCoreOf 2 X = X := by
  let N : Subgroup Q := CFSG.Open.pCoreOf 2 X
  let J : Subgroup Q := S17.oUpperTwo X
  have hJle : J ≤ X := S17.oUpperTwo_le X
  have hNle : N ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hMle : J ⊔ N ≤ X := sup_le hJle hNle
  have hXJ : X ≤ Subgroup.normalizer (J : Set Q) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oUpperTwo' (X := X))
  have hXN : X ≤ Subgroup.normalizer (N : Set Q) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hMnorm : ((J ⊔ N).subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMle]
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXJ hx)),
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXN hx))]
  let : ((J ⊔ N).subgroupOf X).Normal := hMnorm
  have hpgroup : IsPGroup 2 (↥X ⧸ (J ⊔ N).subgroupOf X) :=
    isPGroup_quotient_oUpperTwo X (J ⊔ N) le_sup_left
  have hcore : CFSG.pCore 2 ↥X = N.subgroupOf X := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 X]
  have hker_le : CFSG.pCore 2 ↥X ≤ (J ⊔ N).subgroupOf X := by
    rw [hcore]
    exact Subgroup.subgroupOf_mono X le_sup_right
  let q : ↥X →* (↥X ⧸ (J ⊔ N).subgroupOf X) :=
    QuotientGroup.mk' ((J ⊔ N).subgroupOf X)
  have hker_le' : CFSG.pCore 2 ↥X ≤ q.ker := by simpa [q] using hker_le
  let f : Bar2 X →* (↥X ⧸ (J ⊔ N).subgroupOf X) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥X) q hker_le'
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective _ q (QuotientGroup.mk'_surjective _) hker_le'
  have hperf : commutator (↥X ⧸ (J ⊔ N).subgroupOf X) = ⊤ := by
    have hmap := Subgroup.map_commutator (H₁ := (⊤ : Subgroup (Bar2 X))) (H₂ := ⊤) f
    rw [Subgroup.map_top_of_surjective f hf] at hmap
    rw [show ⁅(⊤ : Subgroup (Bar2 X)), ⊤⁆ = commutator (Bar2 X) from rfl,
      hq.1, Subgroup.map_top_of_surjective f hf] at hmap
    exact hmap.symm
  have : Subsingleton (↥X ⧸ (J ⊔ N).subgroupOf X) :=
    subsingleton_of_isPGroup_two_of_commutator_eq_top hpgroup hperf
  have htop : (J ⊔ N).subgroupOf X = ⊤ := QuotientGroup.subsingleton_iff.mp inferInstance
  exact le_antisymm hMle (Subgroup.subgroupOf_eq_top.mp htop)


omit [Finite Q] in
private theorem isPGroup_quotient_commutator {X O : Subgroup Q}
    [(⁅X, X⁆.subgroupOf X).Normal] (hsup : ⁅X, X⁆ ⊔ (X ⊓ O) = X)
    (hO : IsPGroup 2 ↥O) :
    IsPGroup 2 (↥X ⧸ (⁅X, X⁆).subgroupOf X) := by
  have hCle : ⁅X, X⁆ ≤ X := Subgroup.commutator_le_self X
  have hNle : X ⊓ O ≤ X := inf_le_left
  have hN2 : IsPGroup 2 ↥(X ⊓ O) := hO.to_le inf_le_right
  have hCnorm : X ≤ Subgroup.normalizer ((⁅X, X⁆ : Subgroup Q) : Set Q) :=
    Subgroup.normalizer_commutator_ge_left X X
  let q : ↥X →* (↥X ⧸ (⁅X, X⁆).subgroupOf X) :=
    QuotientGroup.mk' ((⁅X, X⁆).subgroupOf X)
  let φ : ↥(X ⊓ O) →* (↥X ⧸ (⁅X, X⁆).subgroupOf X) :=
    q.comp (Subgroup.inclusion hNle)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((⁅X, X⁆).subgroupOf X) y
    have hx : (x : Q) ∈ (↑(⁅X, X⁆ ⊔ (X ⊓ O)) : Set Q) := by
      rw [hsup]
      exact x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (⁅X, X⁆) (X ⊓ O)
      (hNle.trans hCnorm)] at hx
    obtain ⟨c, hc, n, hn, hcn⟩ := hx
    refine ⟨⟨n, hn⟩, ?_⟩
    have hxe : (x : ↥X) = ⟨c, hCle hc⟩ * ⟨n, hNle hn⟩ := by
      ext
      exact hcn.symm
    have hcq : q ⟨c, hCle hc⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    change q ⟨n, hNle hn⟩ = q x
    rw [hxe, map_mul, hcq, one_mul]
  exact IsPGroup.of_surjective hN2 φ hφ

private theorem subsingleton_quotient_commutator_of_odd_generated {X Y : Subgroup Q}
    [(⁅X, X⁆.subgroupOf X).Normal] (hgen : X = S17.oUpperTwo Y)
    (hp : IsPGroup 2 (↥X ⧸ (⁅X, X⁆).subgroupOf X)) :
    Subsingleton (↥X ⧸ (⁅X, X⁆).subgroupOf X) := by
  let q : ↥X →* (↥X ⧸ (⁅X, X⁆).subgroupOf X) :=
    QuotientGroup.mk' ((⁅X, X⁆).subgroupOf X)
  have hgenX : X = S17.oUpperTwo X := by
    refine le_antisymm ?_ (S17.oUpperTwo_le X)
    calc X = S17.oUpperTwo Y := hgen
      _ ≤ S17.oUpperTwo X := by
        rw [S17.oUpperTwo_eq_closure, S17.oUpperTwo_eq_closure]
        refine Subgroup.closure_mono ?_
        rintro y ⟨hyY, hyodd⟩
        exact ⟨hgen.symm ▸ Subgroup.subset_closure ⟨hyY, hyodd⟩, hyodd⟩
  have hSimg : {y : Q | y ∈ X ∧ Odd (orderOf y)} =
      X.subtype '' {x : ↥X | Odd (orderOf x)} := by
    ext y; constructor
    · rintro ⟨hyX, hyodd⟩
      exact ⟨⟨y, hyX⟩, by simpa using hyodd, rfl⟩
    · rintro ⟨x, hxodd, rfl⟩
      exact ⟨x.2, by simpa using hxodd⟩
  have htop : (⊤ : Subgroup ↥X) = Subgroup.closure {x : ↥X | Odd (orderOf x)} := by
    apply Subgroup.map_injective (Subgroup.subtype_injective X)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, MonoidHom.map_closure, ← hSimg]
    rw [← S17.oUpperTwo_eq_closure]
    exact hgenX
  have hQtop : (⊤ : Subgroup (↥X ⧸ (⁅X, X⁆).subgroupOf X)) =
      Subgroup.closure (q '' {x : ↥X | Odd (orderOf x)}) := by
    rw [← Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _), htop,
      MonoidHom.map_closure]
  have htriv : q '' {x : ↥X | Odd (orderOf x)} = {1} := by
    ext y; constructor
    · rintro ⟨x, hxodd, rfl⟩
      have hodd : Odd (orderOf (q x)) := hxodd.of_dvd_nat (orderOf_map_dvd q x)
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hp (q x)
      have hone : orderOf (q x) = 1 := by
        rcases k with _ | k
        · simpa using hk
        · obtain ⟨m, hm⟩ := hodd
          have h2 : 2 ∣ orderOf (q x) := by
            rw [hk]
            exact dvd_pow_self 2 (Nat.succ_ne_zero k)
          obtain ⟨t, ht⟩ := h2
          omega
      rwa [orderOf_eq_one_iff] at hone
    · rintro rfl
      exact ⟨1, by simp [orderOf_one], map_one q⟩
  have htopbot : (⊤ : Subgroup (↥X ⧸ (⁅X, X⁆).subgroupOf X)) = ⊥ := by
    rw [hQtop, htriv]
    exact Subgroup.closure_eq_bot_iff.mpr (by intro y hy; simpa using hy)
  refine ⟨fun a b => ?_⟩
  have ha : a = 1 := by
    have : a ∈ (⊥ : Subgroup (↥X ⧸ (⁅X, X⁆).subgroupOf X)) := htopbot ▸ Subgroup.mem_top a
    simpa using this
  have hb : b = 1 := by
    have : b ∈ (⊥ : Subgroup (↥X ⧸ (⁅X, X⁆).subgroupOf X)) := htopbot ▸ Subgroup.mem_top b
    simpa using this
  rw [ha, hb]


private theorem commutator_eq_self_of_odd_generated {X O Y : Subgroup Q}
    (hgen : X = S17.oUpperTwo Y)
    (hsup : ⁅X, X⁆ ⊔ (X ⊓ O) = X) (hO : IsPGroup 2 ↥O) :
    ⁅X, X⁆ = X := by
  have hCle : ⁅X, X⁆ ≤ X := Subgroup.commutator_le_self X
  have hCnorm : X ≤ Subgroup.normalizer ((⁅X, X⁆ : Subgroup Q) : Set Q) :=
    Subgroup.normalizer_commutator_ge_left X X
  have hCsub : ((⁅X, X⁆).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCle).mpr hCnorm
  let : ((⁅X, X⁆).subgroupOf X).Normal := hCsub
  have hp : IsPGroup 2 (↥X ⧸ (⁅X, X⁆).subgroupOf X) :=
    isPGroup_quotient_commutator hsup hO
  have : Subsingleton (↥X ⧸ (⁅X, X⁆).subgroupOf X) :=
    subsingleton_quotient_commutator_of_odd_generated hgen hp
  have htop : (⁅X, X⁆).subgroupOf X = ⊤ := QuotientGroup.subsingleton_iff.mp inferInstance
  exact le_antisymm hCle (Subgroup.subgroupOf_eq_top.mp htop)



private theorem exists_normal_sup_of_isL2 {M Dsub : Subgroup Q} {d d' : ℕ}
    {L : Fin d → Subgroup Q} {K J : Fin d' → Subgroup Q}
    (hL : IsLeviFamily (Dsub ⊓ M) d L) (hKJ : S19.IsDynkinFamilyIn M Dsub d' K J)
    (i : Fin d') (n : ℕ) (hJ : IsL2 (Bar2 (J i)) n) :
    ∃ N : Subgroup Q, CFSG.Open.pCoreOf 2 (Dsub ⊓ M) ≤ N ∧ N ≤ Dsub ⊓ M ∧
      (N.subgroupOf (Dsub ⊓ M)).Normal ∧ IsL2 (Bar2 N) n ∧ N ≤ ⨆ l, L l := by
  set P : Subgroup Q := Dsub ⊓ M with hPdef
  set O : Subgroup Q := CFSG.Open.pCoreOf 2 P with hOdef
  unfold S19.IsDynkinFamilyIn at hKJ
  dsimp only at hKJ
  rw [← hPdef, ← hOdef] at hKJ
  obtain ⟨hKbasic, hKcomm, hKiSup, hKind, hJeq⟩ := hKJ
  obtain ⟨hOK, hKP, hKnorm, hKeq, hJnotO⟩ := hKbasic i
  have hPK : P ≤ Subgroup.normalizer (K i : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mp hKnorm
  have hJi_norm : P ≤ Subgroup.normalizer (J i : Set Q) := by
    rw [hJeq i]
    exact hPK.trans (normalizer_le_normalizer_oUpperTwo' (X := K i))
  have hJi_le_P : J i ≤ P := by
    rw [hJeq i]
    exact (S17.oUpperTwo_le (K i)).trans hKP
  let N : Subgroup Q := J i ⊔ O
  have hOP : O ≤ P := by rw [hOdef]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hON : O ≤ N := le_sup_right
  have hNP : N ≤ P := sup_le hJi_le_P hOP
  have hPN : P ≤ Subgroup.normalizer (N : Set Q) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hJi_norm hp)),
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P) hp))]
  have hNnorm : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  have hL2N : IsL2 (Bar2 N) n := by
    obtain ⟨e⟩ := bar2_equiv_bar2_sup_pCoreOf (P := P) (X := J i) hJi_le_P hJi_norm
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hJ
  have hN_le_sup : N ≤ ⨆ l, L l := by
    rw [hL.iSup_eq]
    refine sup_le ?_ le_sup_right
    calc J i = S17.oUpperTwo (K i) := hJeq i
      _ ≤ K i := S17.oUpperTwo_le (K i)
      _ ≤ ⨆ k, K k := le_iSup K i
      _ = Opp 2 P ⊔ O := hKiSup
  exact ⟨N, hON, hNP, hNnorm, hL2N, hN_le_sup⟩

private theorem not_commutator_le_of_isL2 {P O N : Subgroup Q} {n : ℕ}
    (hO : O = CFSG.Open.pCoreOf 2 P) (hNP : N ≤ P) (hNnorm : (N.subgroupOf P).Normal)
    (hON : O ≤ N) (hL2 : IsL2 (Bar2 N) n) (hn : 3 ≤ n) : ¬ ⁅N, N⁆ ≤ O := by
  have hON' : CFSG.Open.pCoreOf 2 P ≤ N := hO ▸ hON
  have hPN : P ≤ Subgroup.normalizer (N : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hNnorm
  have hcoreN : CFSG.Open.pCoreOf 2 N = O := by
    rw [pCoreOf_eq_inf hNP hPN, inf_eq_right.mpr (hO ▸ hON), hO]
  have hcoreN_sub : CFSG.pCore 2 ↥N = O.subgroupOf N := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 N, hcoreN]
  have hcommN : ¬ IsMulCommutative (Bar2 N) := not_isMulCommutative_of_isL2 hL2 hn
  intro hle
  apply hcommN
  refine isMulCommutative_iff.mpr fun a b => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N) b
  have hmem : ⁅x, y⁆ ∈ CFSG.pCore 2 ↥N := by
    rw [hcoreN_sub, Subgroup.mem_subgroupOf]
    change ⁅(x : Q), (y : Q)⁆ ∈ O
    exact hle (Subgroup.commutator_mem_commutator x.2 y.2)
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) ⁅x, y⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

omit [Finite Q] in
private theorem exists_not_le_commutator_of_isSimple {P O N : Subgroup Q} {d : ℕ}
    {L : Fin d → Subgroup Q} (hL : IsLeviFamily P d L) (hO : O = CFSG.Open.pCoreOf 2 P)
    (hNsup : N ≤ ⨆ l, L l) (hnot : ¬ ⁅N, N⁆ ≤ O) :
    ∃ l, ¬ ⁅N, L l⁆ ≤ O := by
  by_contra h
  push Not at h
  have h1 : ⁅⨆ l, L l, N⁆ ≤ O :=
    CFSG.Quasithin.MS93.S59.commutator_iSup_le
      (K := L) (A := N) (N := O)
      (fun l => (hL.le l).trans
        (hO.symm ▸ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)))
      (fun l => by rw [Subgroup.commutator_comm]; exact h l)
  exact hnot (Subgroup.commutator_mono hNsup le_rfl |>.trans h1)

private theorem le_of_not_commutator_le {P O N X : Subgroup Q}
    (hO : O = CFSG.Open.pCoreOf 2 P) (hNP : N ≤ P) (hNnorm : (N.subgroupOf P).Normal)
    (hON : O ≤ N) (hsimple : IsSimpleGroup (Bar2 N))
    (hXP : X ≤ P) (hXnorm : (X.subgroupOf P).Normal) (hOX : O ≤ X)
    (hne : ¬ ⁅N, X⁆ ≤ O) : N ≤ X := by
  have hPN : P ≤ Subgroup.normalizer (N : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hNnorm
  have hNX : X ≤ Subgroup.normalizer (N : Set Q) := hXP.trans hPN
  have hXN : P ≤ Subgroup.normalizer (X : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXP).mp hXnorm
  have hMleN : ⁅N, X⁆ ⊔ O ≤ N := by
    refine sup_le ?_ hON
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hNX
  have hMleX : ⁅N, X⁆ ⊔ O ≤ X := by
    refine sup_le ?_ hOX
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp (hNP.trans hXN)
  have hMnorm : P ≤ Subgroup.normalizer ((⁅N, X⁆ ⊔ O : Subgroup Q) : Set Q) := by
    intro p hp
    rw [hO, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, Subgroup.map_commutator,
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPN hp)),
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXN hp)),
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P) hp))]
  have hMnormN : ((⁅N, X⁆ ⊔ O).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleN).mpr (hNP.trans hMnorm)
  have hMeq : ⁅N, X⁆ ⊔ O = CFSG.Open.pCoreOf 2 P ∨ ⁅N, X⁆ ⊔ O = N :=
    eq_pCoreOf_or_eq_of_normal_of_isSimple hNP hNnorm (hO ▸ hON) hsimple hMleN hMnormN
      (hO ▸ le_sup_right)
  have hMne : ⁅N, X⁆ ⊔ O ≠ CFSG.Open.pCoreOf 2 P := by
    intro hEq
    apply hne
    have h : ⁅N, X⁆ ≤ ⁅N, X⁆ ⊔ O := le_sup_left
    rw [hEq] at h
    exact hO.symm ▸ h
  rw [← hMeq.resolve_left hMne]
  exact hMleX

namespace IsLeviFamily

variable {M Dsub : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}

private theorem dynkin_member_perfect {P : Subgroup Q} {d d' : ℕ}
    {L : Fin d → Subgroup Q} {K J : Fin d' → Subgroup Q} {σ : Fin d' ≃ Fin d}
    (hL : IsLeviFamily P d L) (hq : ∀ i, CFSG.Open.IsQuasisimple (Bar2 (L i)))
    (hσ : ∀ k, K k = L (σ k)) (hJeq : ∀ k, J k = S17.oUpperTwo (K k)) (k : Fin d') :
    ⁅J k, J k⁆ = J k ∧ CFSG.Open.IsQuasisimple (Bar2 (J k)) ∧ K k = J k ⊔ pCoreOf 2 P := by
  let O : Subgroup Q := CFSG.Open.pCoreOf 2 P
  have hKk : K k = L (σ k) := hσ k
  have hJk : J k = S17.oUpperTwo (L (σ k)) := by
    rw [hJeq k, hKk]
  have hLk_perf : S17.oUpperTwo (L (σ k)) ⊔ O = L (σ k) := by
    have h := oUpperTwo_sup_pCoreOf_eq_of_isQuasisimple (hq (σ k))
    rwa [pCoreOf_eq_of_isLeviFamily hL (σ k)] at h
  have hKk_sup : K k = J k ⊔ O := by
    calc K k = L (σ k) := hKk
      _ = S17.oUpperTwo (L (σ k)) ⊔ O := hLk_perf.symm
      _ = J k ⊔ O := by rw [hJk]
  have hJr : J k ⊔ O = L (σ k) := by rw [← hKk_sup, hKk]
  have hJk_le_P : J k ≤ P := by
    rw [hJk]
    exact (S17.oUpperTwo_le (L (σ k))).trans (hL.le (σ k))
  have hJk_norm : P ≤ Subgroup.normalizer (J k : Set Q) := by
    rw [hJk]
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer (hL.le (σ k))).mp
      (hL.normal (σ k))).trans (normalizer_le_normalizer_oUpperTwo' (X := L (σ k)))
  have hqJ : CFSG.Open.IsQuasisimple (Bar2 (J k)) := by
    obtain ⟨e⟩ := bar2_equiv_bar2_sup_pCoreOf (P := P) (X := J k) hJk_le_P hJk_norm
    have hq' : CFSG.Open.IsQuasisimple (Bar2 (J k ⊔ O)) := by
      rw [hJr]
      exact hq (σ k)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq'
  refine ⟨?_, hqJ, hKk_sup⟩
  have hsupJ : ⁅J k, J k⁆ ⊔ (J k ⊓ O) = J k := by
    have h := commutator_sup_pCoreOf_eq_of_isQuasisimple hqJ
    rwa [pCoreOf_eq_inf hJk_le_P hJk_norm] at h
  have hO2 : IsPGroup 2 ↥O := by
    rw [show O = CFSG.Open.pCoreOf 2 P from rfl]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  exact commutator_eq_self_of_odd_generated hJk hsupJ hO2

private theorem exists_equiv_and_perfect {M Dsub : Subgroup Q} {d d' : ℕ}
    {L : Fin d → Subgroup Q} {K J : Fin d' → Subgroup Q}
    (hL : IsLeviFamily (Dsub ⊓ M) d L) (hq : ∀ i, CFSG.Open.IsQuasisimple (Bar2 (L i)))
    (hd2 : d ≤ 2) (hKJ : S19.IsDynkinFamilyIn M Dsub d' K J) :
    ∃ (σ : Fin d' ≃ Fin d), (∀ k, K k = L (σ k)) ∧ d' ≤ 2 ∧
      (∀ k, ⁅J k, J k⁆ = J k ∧ CFSG.Open.IsQuasisimple (Bar2 (J k)) ∧
        K k = J k ⊔ pCoreOf 2 (Dsub ⊓ M)) := by
  set P : Subgroup Q := Dsub ⊓ M with hPdef
  set O : Subgroup Q := CFSG.Open.pCoreOf 2 P with hOdef
  have hKJ' : S19.IsDynkinFamilyIn M Dsub d' K J := hKJ
  unfold S19.IsDynkinFamilyIn at hKJ
  dsimp only at hKJ
  rw [← hPdef, ← hOdef] at hKJ
  obtain ⟨hKbasic, hKcomm, hKiSup, hKind, hJeq⟩ := hKJ
  have hperf : ∀ l, ⁅L l, L l⁆ ⊔ O = L l := by
    intro l
    have h := commutator_sup_pCoreOf_eq_of_isQuasisimple (hq l)
    rwa [show CFSG.Open.pCoreOf 2 (L l) = O from by
      simpa [hOdef] using pCoreOf_eq_of_isLeviFamily hL l] at h
  obtain ⟨σ, hσ⟩ := IsLeviFamily.exists_equiv_of_isDynkinFamilyIn hL hperf hKJ'
  have hd'2 : d' ≤ 2 := by
    have hcard := Fintype.card_congr σ
    have h1 : Fintype.card (Fin d') = d' := Fintype.card_fin d'
    have h2 : Fintype.card (Fin d) = d := Fintype.card_fin d
    rw [h1, h2] at hcard
    exact hcard.trans_le hd2
  refine ⟨σ, hσ, hd'2, fun k => dynkin_member_perfect hL hq hσ hJeq k⟩

private theorem mem_normalizer_of_odd {M Dsub : Subgroup Q} {d d' : ℕ}
    {L : Fin d → Subgroup Q} {K : Fin d' → Subgroup Q} {σ : Fin d' ≃ Fin d}
    (hL : IsLeviFamily (Dsub ⊓ M) d L)
    (hperf : ∀ l, ⁅L l, L l⁆ ⊔ pCoreOf 2 (Dsub ⊓ M) = L l)
    (hσ : ∀ k, K k = L (σ k)) (hd2 : d ≤ 2) (g : Q)
    (hg : g ∈ Subgroup.normalizer ((Dsub ⊓ M : Subgroup Q) : Set Q)) (hodd : Odd (orderOf g)) :
    ∀ k, g ∈ Subgroup.normalizer ((K k : Subgroup Q) : Set Q) := by
  set P : Subgroup Q := Dsub ⊓ M with hPdef
  set O : Subgroup Q := CFSG.Open.pCoreOf 2 P with hOdef
  intro k
  let c : Q →* Q := (MulAut.conj g).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj g).injective
  have hPmap : P.map c = P := by
    simpa [c] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)
  have hLmap : IsLeviFamily P d (fun l => (L l).map c) := by
    have h := IsLeviFamily.map (φ := c) hc (P := P) (L := L) hL
    simpa [hPmap] using h
  obtain ⟨τ, hτ⟩ := IsLeviFamily.exists_equiv_of_isDynkinFamilyIn hL hperf
    (isDynkinFamilyIn_of_isLeviFamily hLmap)
  have hinj : Function.Injective L := hL.injective hperf
  have hpow : ∀ j (l : Fin d),
      (L l).map (MulAut.conj (g ^ j)).toMonoidHom = L ((τ ^ j) l) := by
    intro j
    induction j with
    | zero =>
        intro l
        rw [pow_zero, map_one]
        exact Subgroup.map_id (L l)
    | succ j ih =>
        intro l
        rw [pow_succ', map_mul]
        have hmul : ((MulAut.conj g) * (MulAut.conj (g ^ j))).toMonoidHom =
            (MulAut.conj g).toMonoidHom.comp (MulAut.conj (g ^ j)).toMonoidHom := rfl
        rw [hmul, ← Subgroup.map_map, ih l, hτ ((τ ^ j) l)]
        congr 1
        rw [pow_succ']
        rfl
  have hτm : τ ^ orderOf g = 1 := by
    ext l
    have h2 : (L l).map (MulAut.conj (g ^ orderOf g)).toMonoidHom = L l := by
      rw [pow_orderOf_eq_one, map_one]
      exact Subgroup.map_id (L l)
    have h3 : L ((τ ^ orderOf g) l) = L l := by
      rw [← hpow (orderOf g) l, h2]
    exact congrArg Fin.val (hinj h3)
  have hτ2 : τ ^ 2 = 1 := by
    interval_cases d
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
    · rcases TauCeti.perm_fin_two_eq_one_or_swap τ with h | h
      · rw [h]; simp
      · rw [h]; exact Equiv.swap_mul_self 0 1
  have hτ1 : τ = 1 := (pow_eq_one_iff_of_coprime hodd.coprime_two_right).mp ⟨hτm, hτ2⟩
  have hLfix : ∀ l, (L l).map c = L l := by
    intro l
    simpa [hτ1] using hτ l
  rw [hσ k]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [c] using hLfix (σ k))

theorem false_of_isL2 (hL : IsLeviFamily (Dsub ⊓ M) d L)
    (hno : ∀ i (N : Subgroup Q) (n : ℕ), pCoreOf 2 (Dsub ⊓ M) ≤ N → N ≤ L i →
      (N.subgroupOf (L i)).Normal → 3 ≤ n → ¬ IsL2 (Bar2 N) n)
    {d' : ℕ} {K J : Fin d' → Subgroup Q} (hKJ : S19.IsDynkinFamilyIn M Dsub d' K J)
    (i : Fin d') (n : ℕ) (hn : 3 ≤ n) (hJ : IsL2 (Bar2 (J i)) n) : False := by
  set P : Subgroup Q := Dsub ⊓ M with hPdef
  set O : Subgroup Q := CFSG.Open.pCoreOf 2 P with hOdef
  obtain ⟨N, hON, hNP, hNnorm, hL2N, hNsup⟩ := exists_normal_sup_of_isL2 hL hKJ i n hJ
  have hPN : P ≤ Subgroup.normalizer (N : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hNnorm
  have hsimpleN : IsSimpleGroup (Bar2 N) := S19.isSimpleGroup_of_isL2_or_isSz (Or.inl hL2N)
  have hnot : ¬ ⁅N, N⁆ ≤ O := not_commutator_le_of_isL2 hOdef hNP hNnorm hON hL2N hn
  obtain ⟨l, hl⟩ := exists_not_le_commutator_of_isSimple hL hOdef hNsup hnot
  have hNX : N ≤ L l :=
    le_of_not_commutator_le hOdef hNP hNnorm hON hsimpleN (hL.le l) (hL.normal l)
      (hL.pCoreOf_le l) hl
  exact hno l N n hON hNX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr ((hL.le l).trans hPN)) hn hL2N

theorem nineteen_twentyOne (hL : IsLeviFamily (Dsub ⊓ M) d L)
    (halt : LeviAlt (Dsub ⊓ M) d L) {d' : ℕ} {K J : Fin d' → Subgroup Q}
    (hKJ : S19.IsDynkinFamilyIn M Dsub d' K J) (i : Fin d') (n : ℕ) (hn : 3 ≤ n)
    (hJ : IsL2 (Bar2 (J i)) n) :
    d' ≤ 2 ∧
      (∀ k, ⁅J k, J k⁆ = J k ∧ CFSG.Open.IsQuasisimple (Bar2 (J k)) ∧
        K k = J k ⊔ pCoreOf 2 (Dsub ⊓ M)) ∧
      (∀ g ∈ normalizer ((Dsub ⊓ M : Subgroup Q) : Set Q), Odd (orderOf g) →
        ∀ k, g ∈ normalizer ((K k : Subgroup Q) : Set Q)) := by
  rcases halt with ⟨hd2, hq⟩ | hno
  · have hperf : ∀ l, ⁅L l, L l⁆ ⊔ CFSG.Open.pCoreOf 2 (Dsub ⊓ M) = L l := by
      intro l
      have h := commutator_sup_pCoreOf_eq_of_isQuasisimple (X := L l) (hq l)
      rwa [pCoreOf_eq_of_isLeviFamily hL l] at h
    obtain ⟨σ, hσ, hd'2, hmem⟩ := exists_equiv_and_perfect hL hq hd2 hKJ
    refine ⟨hd'2, hmem, ?_⟩
    intro g hg hgodd k
    exact mem_normalizer_of_odd (M := M) (Dsub := Dsub) (L := L) (K := K)
      (σ := σ) hL hperf hσ hd2 g hg hgodd k
  · exact (false_of_isL2 hL hno hKJ i n hn hJ).elim

end IsLeviFamily

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
