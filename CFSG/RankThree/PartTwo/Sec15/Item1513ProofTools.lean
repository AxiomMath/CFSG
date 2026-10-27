module

public import CFSG.RankThree.PartTwo.Sec15.Item1511Proof
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.K74Plane
import CFSG.RankThree.PartTwo.Sec13.Item13GL

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1513

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_autIn_inf_dvd [Finite G] (A L : Subgroup G) :
    Nat.card (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) ∣
      Nat.card (Sec4.autIn L A) := by
  set K := L ⊓ Subgroup.normalizer (A : Set G) with hKdef
  have hKA : K ≤ Subgroup.normalizer (A : Set G) := inf_le_right
  have hKB : K ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hk.2, Subgroup.le_normalizer hk.1⟩
  set φ₁ : ↥K →* MulAut ↥A := A.normalizerMonoidHom.comp (Subgroup.inclusion hKA) with hφ₁
  set φ₂ : ↥K →* MulAut ↥(A ⊓ L) :=
    (A ⊓ L).normalizerMonoidHom.comp (Subgroup.inclusion hKB) with hφ₂
  have h1 : φ₁.range = Sec4.autIn L A := by
    ext σ
    rw [Sec4.mem_autIn_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, hKA k.2, k.2.1, rfl⟩
    · rintro ⟨g, hN, hL, rfl⟩
      exact ⟨⟨g, hL, hN⟩, rfl⟩
  have h2 : φ₂.range = Sec4.autIn K (A ⊓ L) := by
    ext σ
    rw [Sec4.mem_autIn_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, hKB k.2, k.2, rfl⟩
    · rintro ⟨g, hN, hK', rfl⟩
      exact ⟨⟨g, hK'⟩, rfl⟩
  have hker : φ₁.ker ≤ φ₂.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have h := congrArg (fun σ : MulAut ↥A => ((σ ⟨(x : G), x.2.1⟩ : ↥A) : G)) hk
    exact h
  rw [← h1, ← h2, ← Subgroup.index_ker, ← Subgroup.index_ker]
  exact Subgroup.index_dvd_of_le hker

theorem isElemAbelian_inf {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) :
    CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
  ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hD.isElemAbelian.2 x hx.1⟩

theorem false_of_isIrreducibleOn_of_card {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    (hcard : Nat.card (Sec4.autIn L A) = 3 ∨ Nat.card (Sec4.autIn L A) = 6) : False := by
  have h4 := KFacts.four_dvd_card_of_isIrreducibleOn (isElemAbelian_inf hD) h9 hirr
  have hdvd := (h4.trans (card_autIn_inf_dvd A L))
  rcases hcard with h | h <;> rw [h] at hdvd <;> norm_num at hdvd


theorem cases_of_irreducible (h131 : Item131) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L))) :
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      (IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) := by
  have hD := h.toSec13Data
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, -, hprod, htyp⟩ |
      ⟨-, -, -, ⟨e3⟩⟩ | ⟨-, -, ⟨e3⟩, -⟩ | ⟨hcL, -⟩
  · refine ⟨hprod, ?_⟩
    rcases htyp with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · refine (false_of_isIrreducibleOn_of_card hD h9 hirr (Or.inr ?_)).elim
    rw [Nat.card_congr e3.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  · refine (false_of_isIrreducibleOn_of_card hD h9 hirr (Or.inl ?_)).elim
    rw [Nat.card_congr e3.toEquiv, Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)),
      Nat.card_zmod]
  · exact (h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA hcL).elim

theorem false_of_mem_normalizer_Y {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h1511 : Item1511Star A (lB A) c L) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hmeet : MeetsY4 A (lB A) L Y) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwY : w ∈ Subgroup.normalizer (Y : Set G))
    (hw3 : w ^ 3 = 1) (hwC : w ∉ Subgroup.centralizer (A : Set G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  set K := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
    Subgroup.normalizer (Y : Set G) with hK
  set Q₀ := Subgroup.zpowers w ⊔ A with hQ₀
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hD.A_le_normalizer_zpowers
  have hQK : Q₀ ≤ K := sup_le (Subgroup.zpowers_le.mpr ⟨hWH hwA, hwY⟩) (le_inf hAH hAY)
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mpr hwA
  have hcard := Sec6.card_sup_mul_card_inf hwN
  have hw3' : Nat.card (Subgroup.zpowers w) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hw3
  have hQdvd : Nat.card Q₀ ∣ 3 ^ 4 := by
    have h1 : Nat.card Q₀ ∣ Nat.card (Subgroup.zpowers w) * Nat.card A :=
      hcard ▸ Dvd.intro _ rfl
    rw [hD.card_eq] at h1
    exact h1.trans (by
      rw [show (3 : ℕ) ^ 4 = 3 * 27 by norm_num]
      exact Nat.mul_dvd_mul_right hw3' 27)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hQdvd
  have hQ3 : IsPGroup 3 Q₀ := IsPGroup.of_card hk
  obtain ⟨P', hP'⟩ := (hQ3.comap_subtype (K := K)).exists_le_sylow
  set P := (P' : Subgroup ↥K).map K.subtype with hPdef
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P K := ⟨P', rfl⟩
  have hQP : Q₀ ≤ P := fun y hy => ⟨⟨y, hQK hy⟩, hP' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hAP : A ≤ P := le_sup_right.trans hQP
  have hwP : w ∈ P := hQP (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
  obtain ⟨-, -, -, -, hΩP⟩ := h1511 p e he hL3 Y hY hmeet P hAP hPsyl
  have hwA' : w ∈ A := by
    rw [hΩP]
    exact Subgroup.subset_closure ⟨hwP, hw3⟩
  exact hwC (Subgroup.mem_centralizer_iff.mpr fun x hx => hD.commute hx hwA')

omit [Finite G]
  in
theorem mem_normalizer_sup {A S : Subgroup G} {x : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxS : x ∈ Subgroup.normalizer (S : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) := by
  have h : (A ⊔ S).map (MulAut.conj x).toMonoidHom = A ⊔ S := by
    rw [Subgroup.map_sup, map_conj_eq_self hxA, map_conj_eq_self hxS]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem exists_S0 {A : Subgroup G} (h153 : Item153Main A (lB A))
    (hnorm : Claim153Normal A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    ∃ S₀ ∈ scriptQPiStar A (lB A) ⊤ (piOf 2),
      Subgroup.normalizer ((A ⊔ S₀ : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Y : Set G) := by
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hbot : (⊥ : Subgroup G) ∈
      scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2))) hbot
  obtain ⟨hM, hS2, -⟩ := h153 Y hY
  obtain ⟨hSG, hSN⟩ := hS2 S hS
  have hNM : Subgroup.normalizer (X : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [hM]
    rfl
  exact ⟨S, hSG, hSN.trans (hnorm Y hY _ hNM)⟩

omit [Finite G]
  in
theorem normalizer_le_normalizer_centralizer (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  intro w hw
  have h : (Subgroup.centralizer (A : Set G)).map (MulAut.conj w).toMonoidHom =
      Subgroup.centralizer (A : Set G) := by
    rw [map_conj_centralizer, map_conj_eq_self hw]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

omit [Finite G]
  in
theorem normalizer_le_normalizer_xA (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (xA A : Set G) :=
  (normalizer_le_normalizer_centralizer A).trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)

omit [Finite G]
  in
theorem xA_le_centralizer (A : Subgroup G) : xA A ≤ Subgroup.centralizer (A : Set G) :=
  pPrimeCoreOf_le 3 _

theorem normalizer_le_sup_of_transOn {A : Subgroup G}
    (htr : TransOn A (lB A) (xA A) ⊤) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) :
    Subgroup.normalizer (A : Set G) ≤
      xA A ⊔ (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G)) := by
  intro g hg
  have hSg : S.map (MulAut.conj g).toMonoidHom ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := by
    have h1 := Sec17.HeadProof.map_conj_mem_scriptQPiStar hg hS
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  obtain ⟨x, hx, hxS⟩ := htr S hS _ hSg
  have hxA : x ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer _ (xA_le_centralizer A hx.1)
  have hn : x⁻¹ * g ∈ Subgroup.normalizer (S : Set G) := by
    have h : S.map (MulAut.conj (x⁻¹ * g)).toMonoidHom = S := by
      rw [← Late.map_conj_map_conj, hxS, Late.map_conj_map_conj, inv_mul_cancel,
        Late.map_conj_one]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  have hgx : g = x * (x⁻¹ * g) := by group
  rw [hgx]
  exact Subgroup.mul_mem_sup hx.1 (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hxA) hg, hn⟩)

theorem exists_mem_of_le_sup {A S : Subgroup G}
    (hfr : Subgroup.normalizer (A : Set G) ≤
      xA A ⊔ (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G)))
    {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hw3 : w ^ 3 = 1)
    (hwC : w ∉ Subgroup.centralizer (A : Set G)) :
    ∃ w' ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G),
      w' ^ 3 = 1 ∧ w' ∉ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := xA A with hXdef
  set N := Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) with hNdef
  have hXW : X ≤ Subgroup.normalizer (A : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (xA_le_centralizer A hx)
  have hWX : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    normalizer_le_normalizer_xA A
  have hX3 : Nat.Coprime 3 (Nat.card X) := coprime_card_pPrimeCoreOf 3 _
  have hw1 : w ≠ 1 := fun h1 => hwC (h1 ▸ Subgroup.one_mem _)
  have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  set U := X ⊔ Subgroup.zpowers w with hUdef
  set M := U ⊓ N with hMdef
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr (hWX hwA)
  have hUmul := Subgroup.coe_mul_of_right_le_normalizer_left X (Subgroup.zpowers w) hwN
  have hMX : M ≤ Subgroup.normalizer (X : Set G) := fun m hm => hWX hm.2.1
  have hU : U = M ⊔ X := by
    refine le_antisymm (fun g hg => ?_) (sup_le inf_le_left le_sup_left)
    have hgW : g ∈ Subgroup.normalizer (A : Set G) := (sup_le hXW (Subgroup.zpowers_le.mpr hwA)) hg
    have hg' := hfr hgW
    have hNX : N ≤ Subgroup.normalizer (X : Set G) := fun n hn => hWX hn.1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X N hNX] at hg'
    obtain ⟨x, hx, n, hn, rfl⟩ := hg'
    have hnU : n ∈ U := by
      have : n = x⁻¹ * (x * n) := by group
      rw [this]
      exact U.mul_mem (U.inv_mem (Subgroup.mem_sup_left hx)) hg
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx)
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hnU, hn⟩))
  have hUc : Nat.card U = 3 * Nat.card X := by
    have h1 := Sec6.card_sup_mul_card_inf hwN
    have hdisj : Subgroup.zpowers w ⊓ X = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hy3 : orderOf y ∣ 3 := hwo ▸ orderOf_dvd_of_mem_zpowers hy.1
      have hyX : orderOf y ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hy.2
      have h1y : orderOf y = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hy3 hX3) hyX
      exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1y)
    rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hwo, sup_comm] at h1
    exact h1
  have h3M : 3 ∣ Nat.card M := by
    have h2 := Sec6.card_sup_mul_card_inf hMX
    rw [← hU, hUc] at h2
    have hXpos : 0 < Nat.card X := Nat.card_pos
    have h4 : Nat.card X * (3 * Nat.card (M ⊓ X : Subgroup G)) = Nat.card X * Nat.card M := by
      linarith [h2]
    exact ⟨_, (Nat.eq_of_mul_eq_mul_left hXpos h4).symm⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3M
  refine ⟨(y : G), y.2.2, ?_, fun hyC => ?_⟩
  · rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
  · have hyo : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy]
    have hyU : (y : G) ∈ ((X ⊔ Subgroup.zpowers w : Subgroup G) : Set G) := y.2.1
    rw [hUmul] at hyU
    obtain ⟨x, hx, z, hz, hxz₀⟩ := hyU
    have hxz : x * z = (y : G) := hxz₀
    have hzC : z ∈ Subgroup.centralizer (A : Set G) := by
      have : z = x⁻¹ * (y : G) := by rw [← hxz]; group
      rw [this]
      exact mul_mem (inv_mem (xA_le_centralizer A hx)) hyC
    rcases eq_of_mem_zpowers_of_pow_three hw3 hz with rfl | rfl | rfl
    ·
      rw [mul_one] at hxz
      have h3X : 3 ∣ Nat.card X := hyo ▸ hxz ▸ Subgroup.orderOf_dvd_natCard X hx
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hX3 h3X
    · exact hwC hzC
    · apply hwC
      have : w = (w ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hw3, one_mul, pow_one]
      rw [this]
      exact pow_mem hzC 2

end CFSG.RankThree.PartTwo.Sec15.Proof1513
