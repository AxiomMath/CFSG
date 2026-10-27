module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1SigComm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Ten
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase153

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise IsMulCommutative

section Delta

variable {W : Type} [CommGroup W]

private theorem s16e_core_comm_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

theorem s16e_core_deltaSym [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W} {p r : ℕ}
    (hp : p = 3 ∨ p = 7) (hr : 3 ≤ r) (hE : IsElemAbelianOfRank p r ↥L)
    (hWL : commSub ⊤ L = ⊤) (hW : Conc4_136W A t L) :
    ⁅L, Subgroup.zpowers t⁆ ≠ ⊥ ∧ ∃ m : ℕ, DeltaSym A t (⊤ : Subgroup W) r m := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hcomm := s16e_core_comm_of_elem hE
  have hcard : Nat.card ↥L = p ^ r := A38.card_eq_of_isElemAbelianOfRank hpp hE
  have hp3 : 3 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have h27 : 27 ≤ p ^ r :=
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
      _ ≤ p ^ r := Nat.pow_le_pow_right (by omega) hr
  obtain ⟨-, -, h⟩ := hW
  rcases h with h133 | ⟨K, hK, g, hg, hKne, hLK, htens⟩ | ⟨hcomp, -, -⟩ | ⟨-, -, hcomp, -⟩
  · obtain ⟨p', hp'p, -, hLt, -, halt⟩ := h133
    rcases halt with ⟨hcyc, h | h | h⟩ | ⟨hcyc, h⟩ | ⟨h1p2, h⟩ | ⟨hEA, h8, -⟩ |
      ⟨hcyc, h | h⟩ | ⟨r', m', hpm, hr2, hEAr, hrk', hDelta⟩ | ⟨hEA, h6, hinv⟩
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · exact (r1613g_not_isPOnePlusTwo_of_comm hcomm h1p2).elim
    · exfalso
      have hc9 : Nat.card ↥L = 9 := by
        have h9' := A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 3) hEA
        simpa using h9'
      omega
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · have hp'pr : p'.Prime := hp'p
      have hcard' : Nat.card ↥L = p' ^ r' := A38.card_eq_of_isElemAbelianOfRank hp'pr hEAr
      have hpow : p ^ r = p' ^ r' := hcard.symm.trans hcard'
      obtain ⟨r₁, rfl⟩ : ∃ r₁, r = r₁ + 1 := ⟨r - 1, by omega⟩
      obtain ⟨r₂, rfl⟩ : ∃ r₂, r' = r₂ + 1 := ⟨r' - 1, by omega⟩
      obtain ⟨hpp', hrr'⟩ := Nat.Prime.pow_inj hpp hp'pr hpow
      subst hpp'
      have hrr : r₁ = r₂ := hrr'
      subst hrr
      rw [hWL] at hDelta
      exact ⟨hLt, m', hDelta⟩
    · exfalso
      have hc9 : Nat.card ↥L = 9 := by
        have h9' := A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 3) hEA
        simpa using h9'
      omega
  · exfalso
    have hKL : K ≤ L := hLK ▸ le_sup_left
    exact r1613g_not_isQuasisimple_of_comm
      (fun a b => Subtype.ext (by
        have h := congrArg (fun x : ↥L => (x : MulAut W))
          (hcomm ⟨a.1, hKL a.2⟩ ⟨b.1, hKL b.2⟩)
        exact h)) hK.2.2
  · exact (r1613g_not_isQuasisimple_of_comm hcomm hcomp.2.2).elim
  · exact (r1613g_not_isQuasisimple_of_comm hcomm hcomp.2.2).elim

end Delta

private theorem s16e_core_isElemAbelian {X : Type*} [Group X] {p n : ℕ} {E : Subgroup X}
    (hE : IsElemAbelianOfRank p n ↥E) : IsElemAbelian p E := by
  obtain ⟨e⟩ := hE
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun a ha => ?_⟩
  · have h1 : e a * e b = e b * e a := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact e.injective h1
  · have h1 : e (⟨a, ha⟩ ^ p) = 1 := by
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      simp
    have h2 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val h2

private theorem s16e_core_isElemAbelian_map {A B : Type*} [Group A] [Group B] {p : ℕ}
    {N : Subgroup A} (hN : IsElemAbelian p N) (e : A ≃* B) :
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

private theorem s16e_core_isElemAbelian_comap {A B : Type*} [Group A] [Group B] {p : ℕ}
    {K : Subgroup B} (hK : IsElemAbelian p K) (f : A →* B) (hf : Function.Injective f) :
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

private theorem s16e_core_card_subgroupOf_of_le {A : Type*} [Group A] {E U : Subgroup A}
    (hU : U ≤ E) : Nat.card ↥(U.subgroupOf E) = Nat.card U := by
  rw [← Subgroup.card_subtype E (U.subgroupOf E), Subgroup.map_subgroupOf_eq_of_le hU]

private theorem s16e_core_subgroupOf_commutator_self {X : Type*} [Group X] (H : Subgroup X) :
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

private theorem s16e_core_normal_subgroupOf {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} (h : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) :
    (L.subgroupOf A).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg := h g g.2
  have hmem : (MulAut.conj (g : MulAut W)).toMonoidHom (n : MulAut W) ∈
      L.map (MulAut.conj (g : MulAut W)).toMonoidHom := Subgroup.mem_map_of_mem _ hn
  rw [hg] at hmem
  simpa [MulAut.conj_apply] using hmem

variable {G : Type} [Group G] [Finite G]

theorem s16e_mem_sig_of_elem_core (D : Data G) (hSg : UC6S846.SigmaStd D) (h127 : R127 D)
    (h1110 : R1110Core D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 6 ≤ r)
    (hE : IsElemAbelianOfRank p r ↥(lBar V₀ V hV L)) : p ∈ D.sig := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hconc hs
  obtain ⟨t, htA, ht2, ht1, htrk, hW⟩ := id hconc
  obtain ⟨hLt, m, hD⟩ := s16e_core_deltaSym hp (by omega) hE hwT hW
  have hLA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hset.hyp151.le
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = lBar V₀ V hV L :=
    fun g hg => lBar_conj_eq_of_s15_eq_one hs hg
  have hLcomm : lBar V₀ V hV L ≤ ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆ :=
    s16e_comm_le_commutator hpp (by omega) hLA hLn hE hLt hD
  have hpf := hset.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal hV hMs
  obtain ⟨Φ, -⟩ := s15_Three_barImage_equiv hV hMs
  let Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).map Φ.symm.toMonoidHom
  have hNsub : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    s16e_core_normal_subgroupOf hLn
  have hXnorm : Xbar.Normal := hNsub.map Φ.symm.toMonoidHom Φ.symm.surjective
  have hXcard : Nat.card Xbar = p ^ r := by
    rw [show Xbar = _ from rfl, Subgroup.card_map_of_injective Φ.symm.injective,
      s16e_core_card_subgroupOf_of_le hLA, A38.card_eq_of_isElemAbelianOfRank hpp hE]
  have hel : IsElemAbelian p (lBar V₀ V hV L) := s16e_core_isElemAbelian hE
  have hel' : IsElemAbelian p ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) :=
    s16e_core_isElemAbelian_comap hel (Mbar D.M V₀ V hV).subtype (Subgroup.subtype_injective _)
  have hXel : IsElemAbelian p Xbar := by
    rw [show Xbar = _ from rfl]
    exact s16e_core_isElemAbelian_map hel' Φ.symm
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
      rw [hcomp, Subgroup.map_id, ← s16e_core_subgroupOf_commutator_self (Mbar D.M V₀ V hV)]
      exact fun z hz => hLcomm (Subgroup.mem_subgroupOf.mp hz)
    intro x hx
    have hxmap : Φ x ∈ Xbar.map Φ.toMonoidHom := ⟨x, hx, rfl⟩
    have hxcomm : Φ x ∈ ⁅(⊤ : Subgroup ↥(Mbar D.M V₀ V hV)),
        (⊤ : Subgroup ↥(Mbar D.M V₀ V hV))⁆ := h1 hxmap
    rw [← hmapc] at hxcomm
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxcomm
    rwa [Φ.injective hyx] at hy
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 hset.hyp16.hyp125
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (F11.O2p p D.M)
  have hO2p_le : F11.O2p p D.M ≤ D.M := by
    rw [F11.O2p]
    exact Subgroup.map_subtype_le _
  have hPle : P ≤ D.M := by
    obtain ⟨Q, hQ⟩ := hP
    rw [← hQ]
    exact (Subgroup.map_subtype_le (Q : Subgroup ↥(F11.O2p p D.M))).trans hO2p_le
  have hBple : F11.barPreimage11 D.M V₀ V Xbar ≤ D.M := by
    rw [F11.barPreimage11]
    exact Subgroup.map_subtype_le _
  have hRle : P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar ≤ D.M :=
    (inf_le_left.trans inf_le_left).trans hPle
  have hOmega : F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ≤ D.M := by
    rw [F11.Omega1p]
    exact (Subgroup.closure_le D.M).mpr fun x hx => hRle hx.1
  have hkey := ((h1110 V₀ V hH11 p hpp hp2 P hP).2.2 r (by omega) Xbar hXnorm hXel hXcard
    hXc).2.2.2
  have hle : CFSG.Open.pRank p (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓
      F11.barPreimage11 D.M V₀ V Xbar)) ≤ CFSG.Open.pRank p D.M :=
    CFSG.SectionRank.pRank_mono hpp.one_lt hOmega
  have h4 : 4 ≤ CFSG.Open.pRank p D.M :=
    le_trans (by omega : 4 ≤ r / 2 + 1) (le_trans hkey hle)
  exact hSg.four_mem p hpp hp2 h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
