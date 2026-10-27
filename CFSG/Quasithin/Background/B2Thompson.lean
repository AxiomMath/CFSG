module

public import CFSG.Quasithin.Background.AutOnIndex
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

private theorem omegaOneOf_mono {X Y : Subgroup G} (h : X ≤ Y) : omegaOneOf X ≤ omegaOneOf Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

private theorem isElemAbelian_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

private theorem isElemAbelian_of_forall {E : Subgroup G}
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a ^ 2 = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, h2⟩

private theorem isElemAbelian_mono {E F : Subgroup G} (hFE : F ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

private theorem isElemAbelian_bot : IsElemAbelian 2 (⊥ : Subgroup G) :=
  isElemAbelian_of_forall
    (fun a ha b hb => by rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb])
    fun a ha => by rw [Subgroup.mem_bot.mp ha]; exact one_pow 2

private theorem comm_of_mem_closure {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {x y : G}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S) : x * y = y * x := by
  have h1 : ∀ z ∈ Subgroup.closure S, ∀ b ∈ S, z * b = b * z := by
    intro z hz b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {b} := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hS a ha h hb).symm
    exact ((Subgroup.mem_centralizer_iff.mp (hle hz)) b rfl).symm
  have hle : Subgroup.closure S ≤ Subgroup.centralizer {y} := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact h1 h hy a ha
  exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) y rfl).symm

private theorem pow_two_eq_one_of_mem_closure {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (h2 : ∀ a ∈ S, a ^ 2 = 1) {x : G} (hx : x ∈ Subgroup.closure S) : x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (comm_of_mem_closure hS hx hy) 2, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

private theorem isElemAbelian_closure {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (h2 : ∀ a ∈ S, a ^ 2 = 1) : IsElemAbelian 2 (Subgroup.closure S) :=
  isElemAbelian_of_forall (fun _ hx _ hy => comm_of_mem_closure hS hx hy)
    fun _ hx => pow_two_eq_one_of_mem_closure hS h2 hx

private theorem isElemAbelian_sup {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

private theorem isElemAbelian_zpowers {x : G} (hx : x ^ 2 = 1) :
    IsElemAbelian 2 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

section FiniteSection

variable [Finite G]

private theorem exists_card_eq_two_pow {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    ∃ k : ℕ, Nat.card E = 2 ^ k := by
  have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  exact IsPGroup.iff_card.mp hp

private theorem pRank_set_bddAbove (H : Subgroup G) :
    BddAbove {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨E, _, _, hk⟩
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ = Nat.card E := hk.symm
    _ ≤ Nat.card G := E.card_le_card_group

private theorem card_le_two_pow_pRank {E H : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 ^ pRank 2 H := by
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow hE
  have : k ≤ pRank 2 H := le_csSup (pRank_set_bddAbove H) ⟨E, hEH, hE, hk⟩
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) this

private theorem exists_card_eq_two_pow_pRank (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ pRank 2 H :=
  CFSG.SectionRank.exists_pRank one_lt_two H

private theorem pRank_mono {R S : Subgroup G} (h : R ≤ S) : pRank 2 R ≤ pRank 2 S :=
  CFSG.SectionRank.pRank_mono one_lt_two h

@[expose] def IsElemAbelianCorank (H : Subgroup G) (i : ℕ) (A : Subgroup G) : Prop :=
  A ≤ H ∧ IsElemAbelian 2 A ∧ Nat.card A * 2 ^ i = 2 ^ pRank 2 H

@[expose] def thompsonJi (H : Subgroup G) (i : ℕ) : Subgroup G :=
  ⨆ (A : Subgroup G) (_ : IsElemAbelianCorank H i A), A

theorem isMaxElemAbelian_iff_corank_zero {H A : Subgroup G} :
    IsMaxElemAbelian H A ↔ IsElemAbelianCorank H 0 A := by
  constructor
  · rintro ⟨hAH, hA, hmax⟩
    refine ⟨hAH, hA, ?_⟩
    obtain ⟨E, hEH, hE, hEc⟩ := exists_card_eq_two_pow_pRank H
    have h1 : Nat.card E ≤ Nat.card A := hmax E hEH hE
    have h2 : Nat.card A ≤ 2 ^ pRank 2 H := card_le_two_pow_pRank hAH hA
    rw [pow_zero, mul_one]
    omega
  · rintro ⟨hAH, hA, hc⟩
    refine ⟨hAH, hA, fun B hBH hB => ?_⟩
    rw [pow_zero, mul_one] at hc
    rw [hc]
    exact card_le_two_pow_pRank hBH hB

theorem exists_isMaxElemAbelian (H : Subgroup G) : ∃ A, IsMaxElemAbelian H A := by
  obtain ⟨E, hEH, hE, hEc⟩ := exists_card_eq_two_pow_pRank H
  exact ⟨E, isMaxElemAbelian_iff_corank_zero.mpr ⟨hEH, hE, by rw [hEc, pow_zero, mul_one]⟩⟩

private theorem exists_isElemAbelianCorank (S : Subgroup G) {i : ℕ} (hi : i ≤ pRank 2 S) :
    ∃ A, IsElemAbelianCorank S i A := by
  obtain ⟨E, hES, hE, hEc⟩ := exists_card_eq_two_pow_pRank S
  obtain ⟨K, hKc, -, hKE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := pRank 2 S - i) (H := ⊥) (L := E)
    (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hEc]; exact pow_dvd_pow 2 (Nat.sub_le _ _)) bot_le
  refine ⟨K, hKE.trans hES, isElemAbelian_mono hKE hE, ?_⟩
  rw [hKc, ← pow_add, Nat.sub_add_cancel hi]

private theorem le_thompsonJi {S A : Subgroup G} {i : ℕ} (hA : IsElemAbelianCorank S i A) :
    A ≤ thompsonJi S i :=
  le_iSup₂_of_le A hA le_rfl

private theorem thompsonJi_le (S : Subgroup G) (i : ℕ) : thompsonJi S i ≤ S :=
  iSup_le fun _ => iSup_le fun hA => hA.1

omit [Finite G] in
private theorem le_thompsonJ {S A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ thompsonJ S :=
  le_iSup₂_of_le A hA le_rfl

omit [Finite G] in
private theorem thompsonJ_le (S : Subgroup G) : thompsonJ S ≤ S :=
  iSup_le fun _ => iSup_le fun hA => hA.1

theorem thompsonJ_eq_thompsonJi_zero (S : Subgroup G) : thompsonJ S = thompsonJi S 0 :=
  le_antisymm
    (iSup_le fun _ => iSup_le fun hA =>
      le_thompsonJi (isMaxElemAbelian_iff_corank_zero.mp hA))
    (iSup_le fun _ => iSup_le fun hA =>
      le_thompsonJ (isMaxElemAbelian_iff_corank_zero.mpr hA))

private theorem IsElemAbelianCorank.exists_rank {H A : Subgroup G} {i : ℕ}
    (hA : IsElemAbelianCorank H i A) : ∃ a : ℕ, Nat.card A = 2 ^ a ∧ a + i = pRank 2 H := by
  obtain ⟨a, ha⟩ := exists_card_eq_two_pow hA.2.1
  refine ⟨a, ha, ?_⟩
  have h := hA.2.2
  rw [ha, ← pow_add] at h
  exact Nat.pow_right_injective le_rfl h

theorem thompsonJi_mono {S : Subgroup G} {i j : ℕ} (hij : i ≤ j) (hj : j < pRank 2 S) :
    thompsonJi S i ≤ thompsonJi S j := by
  refine iSup_le fun A => iSup_le fun hA => ?_
  obtain ⟨a, ha, ham⟩ := hA.exists_rank
  intro x hx
  have hx2 : x ^ 2 = 1 := hA.2.1.2 x hx
  have hcard : Nat.card (Subgroup.zpowers x) ∣ 2 ^ (pRank 2 S - j) := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one hx2).trans
      (dvd_pow_self 2 (by omega))
  obtain ⟨K, hKc, hxK, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hcard
    (by rw [ha]; exact pow_dvd_pow 2 (by omega)) (Subgroup.zpowers_le.mpr hx)
  have hK : IsElemAbelianCorank S j K := by
    refine ⟨hKA.trans hA.1, isElemAbelian_mono hKA hA.2.1, ?_⟩
    rw [hKc, ← pow_add, Nat.sub_add_cancel hj.le]
  exact le_thompsonJi hK (hxK (Subgroup.mem_zpowers x))

private theorem mem_thompsonJi_of_centralizes {S : Subgroup G} {i : ℕ} (hi : i < pRank 2 S)
    {x : G} (hxS : x ∈ S) (hx2 : x ^ 2 = 1)
    (hxC : x ∈ Subgroup.centralizer (thompsonJi S i : Set G)) : x ∈ thompsonJi S i := by
  obtain ⟨A, hA⟩ := exists_isElemAbelianCorank S hi.le
  have hAJ : A ≤ thompsonJi S i := le_thompsonJi hA
  have hBe : IsElemAbelian 2 (A ⊔ Subgroup.zpowers x) := by
    refine isElemAbelian_sup hA.2.1 (isElemAbelian_zpowers hx2) fun a ha b hb => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hax : Commute a x := Subgroup.mem_centralizer_iff.mp hxC a (hAJ ha)
    exact (hax.zpow_right n).eq
  have hBS : A ⊔ Subgroup.zpowers x ≤ S := sup_le hA.1 (Subgroup.zpowers_le.mpr hxS)
  obtain ⟨a, ha, ham⟩ := hA.exists_rank
  obtain ⟨b, hb⟩ := exists_card_eq_two_pow hBe
  have hab : a ≤ b := by
    have := Subgroup.card_le_of_le (le_sup_left : A ≤ A ⊔ Subgroup.zpowers x)
    rw [ha, hb] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hbm : b ≤ pRank 2 S := by
    have := card_le_two_pow_pRank hBS hBe
    rw [hb] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hBk : IsElemAbelianCorank S (pRank 2 S - b) (A ⊔ Subgroup.zpowers x) :=
    ⟨hBS, hBe, by rw [hb, ← pow_add, Nat.add_sub_cancel' hbm]⟩
  have hki : pRank 2 S - b ≤ i := by omega
  exact thompsonJi_mono hki hi (le_thompsonJi hBk
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))

theorem omegaOneCenterOf_thompsonJi_le {S : Subgroup G} {i j : ℕ} (hij : i ≤ j)
    (hj : j < pRank 2 S) :
    omegaOneCenterOf (thompsonJi S j) ≤
        omegaOneOf (S ⊓ Subgroup.centralizer (thompsonJi S i : Set G)) ∧
      omegaOneOf (S ⊓ Subgroup.centralizer (thompsonJi S i : Set G)) =
        omegaOneCenterOf (thompsonJi S i) := by
  have h1 := thompsonJi_mono hij hj
  have hi : i < pRank 2 S := lt_of_le_of_lt hij hj
  refine ⟨omegaOneOf_mono ?_, le_antisymm ?_ (omegaOneOf_mono ?_)⟩
  · intro x hx
    exact ⟨thompsonJi_le S j hx.1, Subgroup.centralizer_le h1 hx.2⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨⟨hxS, hxC⟩, hx2⟩
    exact Subgroup.subset_closure
      ⟨⟨mem_thompsonJi_of_centralizes hi hxS hx2 hxC, hxC⟩, hx2⟩
  · intro x hx
    exact ⟨thompsonJi_le S i hx.1, hx.2⟩

private theorem pRank_eq_of_thompsonJ_le {S R : Subgroup G} (hJ : thompsonJ S ≤ R) (hRS : R ≤ S) :
    pRank 2 R = pRank 2 S := by
  refine le_antisymm (pRank_mono hRS) ?_
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian S
  have hc := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
  rw [pow_zero, mul_one] at hc
  have := card_le_two_pow_pRank ((le_thompsonJ hA).trans hJ) hA.2.1
  rw [hc] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

private theorem thompsonJi_eq_aux {S R : Subgroup G} {i : ℕ} (hJ : thompsonJ S ≤ R)
    (hRS : R ≤ S) (hi : thompsonJi S i ≤ R) : thompsonJi S i = thompsonJi R i := by
  have hr := pRank_eq_of_thompsonJ_le hJ hRS
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hA => ?_
    exact le_thompsonJi ⟨(le_thompsonJi hA).trans hi, hA.2.1, by rw [hr]; exact hA.2.2⟩
  · refine iSup_le fun A => iSup_le fun hA => ?_
    exact le_thompsonJi ⟨hA.1.trans hRS, hA.2.1, by rw [← hr]; exact hA.2.2⟩

theorem thompsonJi_eq_of_le {S R : Subgroup G} {i : ℕ} (hi : i < pRank 2 S)
    (hJi : thompsonJi S i ≤ R) (hRS : R ≤ S) : thompsonJi S i = thompsonJi R i := by
  have hJ : thompsonJ S ≤ R := by
    rw [thompsonJ_eq_thompsonJi_zero]
    exact (thompsonJi_mono (Nat.zero_le i) hi).trans hJi
  exact thompsonJi_eq_aux hJ hRS hJi

omit [Finite G] in
private theorem omegaOneOf_le (X : Subgroup G) : omegaOneOf X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

omit [Finite G] in
private theorem thompsonJ_le_baum (S : Subgroup G) : thompsonJ S ≤ baum S := by
  refine le_inf (thompsonJ_le S) ?_
  rw [Subgroup.le_centralizer_iff]
  intro x hx
  exact (omegaOneOf_le (centerOf (thompsonJ S)) hx).2

theorem baum_eq_of_le {S R : Subgroup G} (hb : baum S ≤ R) (hRS : R ≤ S) :
    baum S = baum R := by
  have hJ : thompsonJ S ≤ R := (thompsonJ_le_baum S).trans hb
  have hJeq : thompsonJ S = thompsonJ R := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_aux hJ hRS (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJ)
  have hS : baum S = S ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJ R) : Set G) := by
    rw [← hJeq]
    rfl
  rw [hS] at hb ⊢
  exact le_antisymm (le_inf hb inf_le_right) (inf_le_inf_right _ hRS)

theorem eq_omegaOneOf_centralizer {S A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    A = omegaOneOf (S ⊓ Subgroup.centralizer (A : Set G)) := by
  apply le_antisymm
  · intro x hx
    refine Subgroup.subset_closure
      ⟨⟨hA.1 hx, Subgroup.mem_centralizer_iff.mpr fun a ha => isElemAbelian_comm hA.2.1 ha hx⟩,
        hA.2.1.2 x hx⟩
  · refine (Subgroup.closure_le A).mpr ?_
    rintro y ⟨⟨hyS, hyC⟩, hy2⟩
    have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
      intro a ha b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hay : Commute a y := Subgroup.mem_centralizer_iff.mp hyC a ha
      exact (hay.zpow_right n).eq
    have hBe := isElemAbelian_sup hA.2.1 (isElemAbelian_zpowers hy2) hcomm
    have hBS : A ⊔ Subgroup.zpowers y ≤ S := sup_le hA.1 (Subgroup.zpowers_le.mpr hyS)
    have hAB : A = A ⊔ Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hBS hBe)
    have hyB : y ∈ A ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    rwa [← hAB] at hyB

theorem omegaOne_centralizer_thompsonJ (S : Subgroup G) :
    omegaOneOf (S ⊓ Subgroup.centralizer (thompsonJ S : Set G)) =
        omegaOneCenterOf (thompsonJ S) ∧
      omegaOneCenterOf (thompsonJ S) = ⨅ (A : Subgroup G) (_ : IsMaxElemAbelian S A), A := by
  have h1 : omegaOneOf (S ⊓ Subgroup.centralizer (thompsonJ S : Set G)) ≤
      ⨅ (A : Subgroup G) (_ : IsMaxElemAbelian S A), A := by
    refine le_iInf₂ fun A hA => ?_
    calc omegaOneOf (S ⊓ Subgroup.centralizer (thompsonJ S : Set G))
        ≤ omegaOneOf (S ⊓ Subgroup.centralizer (A : Set G)) :=
          omegaOneOf_mono (inf_le_inf_left S (Subgroup.centralizer_le (le_thompsonJ hA)))
      _ = A := (eq_omegaOneOf_centralizer hA).symm
  have h2 : (⨅ (A : Subgroup G) (_ : IsMaxElemAbelian S A), A) ≤
      omegaOneCenterOf (thompsonJ S) := by
    intro x hx
    simp only [Subgroup.mem_iInf] at hx
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
    have hx0 := hx A₀ hA₀
    have hxC : x ∈ Subgroup.centralizer (thompsonJ S : Set G) := by
      have hle : thompsonJ S ≤ Subgroup.centralizer {x} := by
        refine iSup_le fun A => iSup_le fun hA => ?_
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact isElemAbelian_comm hA.2.1 (hx A hA) ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hle hy) x rfl).symm
    exact Subgroup.subset_closure ⟨⟨le_thompsonJ hA₀ hx0, hxC⟩, hA₀.2.1.2 x hx0⟩
  have h3 : omegaOneCenterOf (thompsonJ S) ≤
      omegaOneOf (S ⊓ Subgroup.centralizer (thompsonJ S : Set G)) :=
    omegaOneOf_mono fun x hx => ⟨thompsonJ_le S hx.1, hx.2⟩
  exact ⟨le_antisymm (h1.trans h2) h3, le_antisymm (h3.trans h1) h2⟩

theorem baum_eq_baum_centralizer {S U : Subgroup G} (hU : IsElemAbelian 2 U) (hUS : U ≤ S)
    (hJ : thompsonJ S ≤ S ⊓ Subgroup.centralizer (U : Set G)) :
    baum S = baum (S ⊓ Subgroup.centralizer (U : Set G)) := by
  have hE : U ≤ omegaOneCenterOf (thompsonJ S) := by
    rw [← (omegaOne_centralizer_thompsonJ S).1]
    intro u hu
    refine Subgroup.subset_closure ⟨⟨hUS hu, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩,
      hU.2 u hu⟩
    exact ((Subgroup.mem_centralizer_iff.mp (hJ hj).2 u hu)).symm
  have hb : baum S ≤ S ⊓ Subgroup.centralizer (U : Set G) :=
    inf_le_inf_left S (Subgroup.centralizer_le hE)
  exact baum_eq_of_le hb inf_le_left

omit [Finite G] in
private theorem relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

omit [Finite G] in
private theorem card_sup_mul_card_inf {V A : Subgroup G} (hV : IsElemAbelian 2 V) :
    Nat.card ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V : Subgroup G) *
        Nat.card (V ⊓ A : Subgroup G) =
      Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
  set C := A ⊓ Subgroup.centralizer (V : Set G) with hC
  have hCN : C ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have h1 := relIndex_sup_eq_of_le_normalizer hCN
  have h2 := Subgroup.relIndex_mul_card V (C ⊔ V)
  have h3 := Subgroup.relIndex_mul_card V C
  have h4 : V ⊓ (C ⊔ V) = V := inf_of_le_left le_sup_right
  have h5 : V ⊓ C = V ⊓ A := by
    apply le_antisymm
    · exact inf_le_inf_left V inf_le_left
    · rintro x ⟨hxV, hxA⟩
      exact ⟨hxV, hxA,
        Subgroup.mem_centralizer_iff.mpr fun v hv => isElemAbelian_comm hV hv hxV⟩
  rw [h4, h1] at h2
  rw [h5] at h3
  rw [← h2, ← h3]
  ring

private theorem card_inf_le_card_inf_centralizer {V A : Subgroup G} (hA : IsElemAbelian 2 A) :
    Nat.card (V ⊓ A : Subgroup G) ≤ Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
  Subgroup.card_le_of_le
    (inf_le_inf_left V fun _ hx =>
      Subgroup.mem_centralizer_iff.mpr fun _ ha => isElemAbelian_comm hA ha hx)

omit [Finite G] in
private theorem isElemAbelian_sup_centralizer {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) :=
  isElemAbelian_sup (isElemAbelian_mono inf_le_left hA) hV
    fun _ hc v hv => (Subgroup.mem_centralizer_iff.mp hc.2 v hv).symm

private theorem B24_aux {V S A : Subgroup G} {j : ℕ} (hV : IsElemAbelian 2 V) (hVS : V ≤ S)
    (hA : IsElemAbelianCorank S j A) :
    Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
        Nat.card ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V : Subgroup G) *
          Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ∧
      Nat.card ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V : Subgroup G) ≤
        Nat.card A * 2 ^ j ∧
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
          Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) = Nat.card A := by
  have hBe := isElemAbelian_sup_centralizer hV hA.2.1
  have hBS : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ S :=
    sup_le (inf_le_left.trans hA.1) hVS
  refine ⟨?_, ?_, ?_⟩
  · calc Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G)
        = Nat.card ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V : Subgroup G) *
            Nat.card (V ⊓ A : Subgroup G) := (card_sup_mul_card_inf hV).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (card_inf_le_card_inf_centralizer hA.2.1)
  · rw [hA.2.2]
    exact card_le_two_pow_pRank hBS hBe
  · have := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set G)) A
    rwa [inf_of_le_left inf_le_left] at this

theorem card_le_relIndex_mul_card_mul_two_pow {V S A : Subgroup G} {j : ℕ}
    (hV : IsElemAbelian 2 V) (hVS : V ≤ S) (hA : IsElemAbelianCorank S j A) :
    Nat.card V ≤ (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) * 2 ^ j := by
  obtain ⟨h1, h2, h3⟩ := B24_aux hV hVS hA
  have hpos : 0 < Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G)
      ≤ _ := h1
    _ ≤ (Nat.card A * 2 ^ j) *
        Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
      Nat.mul_le_mul_right _ h2
    _ = _ := by rw [← h3]; ring

theorem card_le_relIndex_mul_card {V S A : Subgroup G} (hV : IsElemAbelian 2 V) (hVS : V ≤ S)
    (hA : IsMaxElemAbelian S A) :
    Nat.card V ≤ (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  simpa using card_le_relIndex_mul_card_mul_two_pow hV hVS
    (isMaxElemAbelian_iff_corank_zero.mp hA)

theorem isMaxElemAbelian_sup_of_eq {V S A : Subgroup G} {j : ℕ} (hV : IsElemAbelian 2 V)
    (hVS : V ≤ S) (hA : IsElemAbelianCorank S j A)
    (heq : Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) * 2 ^ j) :
    IsMaxElemAbelian S ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
  obtain ⟨h1, h2, h3⟩ := B24_aux hV hVS hA
  have hBe := isElemAbelian_sup_centralizer hV hA.2.1
  have hBS : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ S :=
    sup_le (inf_le_left.trans hA.1) hVS
  have hD : 0 < Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  have hrhs : Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) =
      (Nat.card A * 2 ^ j) *
        Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
    rw [heq, ← h3]; ring
  have hB : Nat.card ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V : Subgroup G) =
      Nat.card A * 2 ^ j := by
    refine Nat.eq_of_mul_eq_mul_right hD (le_antisymm ?_ (hrhs ▸ h1))
    exact Nat.mul_le_mul_right _ h2
  exact isMaxElemAbelian_iff_corank_zero.mpr
    ⟨hBS, hBe, by rw [pow_zero, mul_one, hB, hA.2.2]⟩

theorem B24_three {V S A : Subgroup G} (hV : IsElemAbelian 2 V) (hVS : V ≤ S)
    (hA : IsMaxElemAbelian S A)
    (heq : Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) :
    IsMaxElemAbelian S ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ∧
      pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) = pRank 2 S ∧
      (∀ A' : Subgroup G, IsMaxElemAbelian (S ⊓ Subgroup.centralizer (V : Set G)) A' →
        IsMaxElemAbelian S A') ∧
      V ≤ omegaOneCenterOf (thompsonJ (S ⊓ Subgroup.centralizer (V : Set G))) ∧
      omegaOneCenterOf (thompsonJ S) ≤
        omegaOneCenterOf (thompsonJ (S ⊓ Subgroup.centralizer (V : Set G))) := by
  have hA0 : IsElemAbelianCorank S 0 A := isMaxElemAbelian_iff_corank_zero.mp hA
  have hB := isMaxElemAbelian_sup_of_eq hV hVS hA0 (by rw [pow_zero, mul_one]; exact heq)
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => isElemAbelian_comm hV hv hx
  have hBle : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ S ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (sup_le (inf_le_left.trans hA.1) hVS) (sup_le inf_le_right hVC)
  have hpr : pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) = pRank 2 S := by
    refine le_antisymm (pRank_mono inf_le_left) ?_
    have hc := (isMaxElemAbelian_iff_corank_zero.mp hB).2.2
    rw [pow_zero, mul_one] at hc
    have := card_le_two_pow_pRank hBle hB.2.1
    rw [hc] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hsub : ∀ A' : Subgroup G, IsMaxElemAbelian (S ⊓ Subgroup.centralizer (V : Set G)) A' →
      IsMaxElemAbelian S A' := by
    intro A' hA'
    have hc := (isMaxElemAbelian_iff_corank_zero.mp hA').2.2
    rw [hpr] at hc
    exact isMaxElemAbelian_iff_corank_zero.mpr ⟨hA'.1.trans inf_le_left, hA'.2.1, hc⟩
  refine ⟨hB, hpr, hsub, ?_, ?_⟩
  · rw [(omegaOne_centralizer_thompsonJ _).2]
    refine le_iInf₂ fun A' hA' => ?_
    refine le_trans ?_ (eq_omegaOneOf_centralizer hA').ge
    intro v hv
    exact Subgroup.subset_closure
      ⟨⟨Subgroup.mem_inf.mpr ⟨hVS hv, hVC hv⟩,
        Subgroup.mem_centralizer_iff.mpr fun a ha =>
          (Subgroup.mem_centralizer_iff.mp (hA'.1 ha).2 v hv).symm⟩, hV.2 v hv⟩
  · rw [(omegaOne_centralizer_thompsonJ S).2, (omegaOne_centralizer_thompsonJ _).2]
    exact le_iInf₂ fun A' hA' => iInf₂_le A' (hsub A' hA')

end FiniteSection

@[expose, instance_reducible] def commGroupOfElemAbelian {V : Subgroup G}
    (hV : IsElemAbelian 2 V) : CommGroup V :=
  { (inferInstance : Group V) with
    mul_comm := fun a b => Subtype.ext (by
      have := hV.1
      exact setLike_mul_comm a.2 b.2) }

private theorem conjAct_apply_coe (V : Subgroup G) (g : Subgroup.normalizer (V : Set G))
    (v : V) : ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

private noncomputable def conjHom (V A : Subgroup G) (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    A →* MulAut V :=
  (conjAct V).comp (Subgroup.inclusion hA)

private theorem conjHom_apply_coe {V A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (a : A) (v : V) : ((conjHom V A hA a v : V) : G) = a * v * (a : G)⁻¹ :=
  conjAct_apply_coe V (Subgroup.inclusion hA a) v

private theorem range_conjHom (V A : Subgroup G) (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    (conjHom V A hA).range = autOn A V := by
  unfold conjHom autOn
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

private theorem ker_conjHom (V A : Subgroup G) (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    (conjHom V A hA).ker = (A ⊓ Subgroup.centralizer (V : Set G)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨a.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) h
    simp only [conjHom_apply_coe, MulAut.one_apply] at this
    have h2 : (a : G) * v * (a : G)⁻¹ = v := this
    calc v * (a : G) = (a * v * (a : G)⁻¹) * a := by rw [h2]
      _ = a * v := by group
  · rintro ⟨-, hc⟩
    ext v
    rw [conjHom_apply_coe, MulAut.one_apply]
    have h := Subgroup.mem_centralizer_iff.mp hc v v.2
    show (a : G) * v * (a : G)⁻¹ = v
    rw [← h, mul_inv_cancel_right]

theorem card_autOn_eq_relIndex {A V : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (autOn A V) = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A :=
  CFSG.Quasithin.AutOn.card_autOn_eq_relIndex hA

private theorem fixV_autOn {A V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    @fixV V (commGroupOfElemAbelian hV) (autOn A V) =
      (Subgroup.centralizer (A : Set G)).subgroupOf V := by
  ext v
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h (conjHom V A hA ⟨a, ha⟩) (by rw [← range_conjHom V A hA]; exact ⟨_, rfl⟩)
    have h3 : (a : G) * v * (a : G)⁻¹ = v := by
      have := conjHom_apply_coe hA ⟨a, ha⟩ v
      rw [← this]
      exact congrArg (fun x : V => (x : G)) h1
    calc (a : G) * v = ((a : G) * v * (a : G)⁻¹) * a := by group
      _ = v * a := by rw [h3]
  · intro h x hx
    rw [← range_conjHom V A hA] at hx
    obtain ⟨a, rfl⟩ := hx
    apply Subtype.ext
    rw [conjHom_apply_coe]
    have := h a a.2
    rw [this, mul_inv_cancel_right]

theorem card_fixV_autOn_eq {A V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (@fixV V (commGroupOfElemAbelian hV) (autOn A V)) =
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  rw [fixV_autOn hV hA, ← Subgroup.inf_subgroupOf_right (Subgroup.centralizer (A : Set G)) V,
    inf_comm]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem isElemAbelian2_autOn {A V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : IsElemAbelian 2 A) (hAn : A ≤ Subgroup.normalizer (V : Set G)) :
    @IsElemAbelian2 V (commGroupOfElemAbelian hV) (autOn A V) := by
  have key : ∀ x ∈ autOn A V, ∃ a : A, conjHom V A hAn a = x := by
    intro x hx
    rw [← range_conjHom V A hAn] at hx
    exact hx
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨a, rfl⟩ := key x hx
    obtain ⟨b, rfl⟩ := key y hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := hA.1
    exact setLike_mul_comm a.2 b.2
  · obtain ⟨a, rfl⟩ := key x hx
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (hA.2 a a.2)
    rw [this, map_one]

theorem autOn_ne_bot_of_not_le_centralizer {A V : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (h : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    autOn A V ≠ ⊥ := by
  intro hbot
  apply h
  intro a ha
  have hmem : conjHom V A hA ⟨a, ha⟩ ∈ autOn A V := by
    rw [← range_conjHom V A hA]
    exact ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  have h2 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) hmem
  simp only [conjHom_apply_coe, MulAut.one_apply] at h2
  have h3 : (a : G) * v * (a : G)⁻¹ = v := h2
  calc v * a = ((a : G) * v * (a : G)⁻¹) * a := by rw [h3]
    _ = a * v := by group

theorem autOn_le_autOn {A H : Subgroup G} (V : Subgroup G) (h : A ≤ H) :
    autOn A V ≤ autOn H V :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

section FiniteBridge

variable [Finite G]

theorem isFFModule_autOn {H V S A : Subgroup G} (hV : IsElemAbelian 2 V) (hVS : V ≤ S)
    (hVH : H ≤ Subgroup.normalizer (V : Set G)) (hAH : A ≤ H) (hA : IsMaxElemAbelian S A)
    (hA1 : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    @IsFFModule V (commGroupOfElemAbelian hV) (autOn H V) := by
  have hAn : A ≤ Subgroup.normalizer (V : Set G) := hAH.trans hVH
  refine ⟨autOn A V, autOn_le_autOn V hAH, autOn_ne_bot_of_not_le_centralizer hAn hA1,
    isElemAbelian2_autOn hV hA.2.1 hAn, ?_⟩
  exact (card_le_relIndex_mul_card hV hVS hA).trans
    (le_of_eq (congrArg₂ (· * ·) (card_autOn_eq_relIndex hAn) (card_fixV_autOn_eq hV hAn)).symm)

end FiniteBridge


end CFSG.Quasithin
