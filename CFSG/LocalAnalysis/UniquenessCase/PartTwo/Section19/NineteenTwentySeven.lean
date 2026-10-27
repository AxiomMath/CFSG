module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.GroupTheory.PRankCommutingPerfect
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22za
public import CFSG.CGT.PushingUpLit.CGT6.Emb5CompBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Helpers
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Arith
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem two_dvd_card_of_isComponent_subgroupOf {H K : Subgroup G} (hKH : K ≤ H)
    (hK : CFSG.IsComponent (K.subgroupOf H)) : 2 ∣ Nat.card K := by
  have h := CFSG.CGT.PushingUpLit.CGT6.even_card_of_isComponent hK
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at h
  exact even_iff_two_dvd.mp h

private theorem exists_odd_prime_dvd_of_isComponent {H K : Subgroup G} (hKH : K ≤ H)
    (hK : CFSG.IsComponent (K.subgroupOf H)) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card K := by
  have hq : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH) hK.1
  haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  haveI : Group.IsPerfect ↥K := hq.1
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card K) with ⟨k, hk⟩ | hodd
  · exfalso
    haveI : IsPGroup 2 ↥K := IsPGroup.iff_card.mpr ⟨k, hk⟩
    haveI : Group.IsNilpotent ↥K := (show IsPGroup 2 ↥K from ‹_›).isNilpotent
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  · obtain ⟨q, hqprime, hqdvd, hqodd⟩ := hodd
    refine ⟨q, hqprime, ?_, hqdvd⟩
    intro hq2
    rw [hq2] at hqodd
    exact absurd hqodd (by decide)

theorem nineteen_twentyseven (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h) :
    R19_27At D V₀ V p L A t B r A₀ H h := by
  classical
  intro K hKH hKcomp
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_isZModSq h.ctx22.ctx.hAcard
  have hAH : A ≤ H := h.hH ▸ le_centralizer_of_isMulCommutative_of_le hAcomm h.ctx22.hA₀
  by_contra hnot
  rw [SetLike.le_def] at hnot
  push Not at hnot
  obtain ⟨a, haA, haN⟩ := hnot
  let f : ℕ → Subgroup G := fun i => K.map (MulAut.conj (a ^ i)).toMonoidHom
  have hf0 : f 0 = K := by
    change K.map (MulAut.conj (a ^ 0)).toMonoidHom = K
    rw [pow_zero, map_one]
    exact CFSG.QuasithinUnique.B113Lie.map_one_aut K
  have hf_add : ∀ i j : ℕ, f (i + j) =
      (f i).map (MulAut.conj (a ^ j)).toMonoidHom := by
    intro i j
    change K.map (MulAut.conj (a ^ (i + j))).toMonoidHom =
      (K.map (MulAut.conj (a ^ i)).toMonoidHom).map (MulAut.conj (a ^ j)).toMonoidHom
    rw [show a ^ (i + j) = a ^ j * a ^ i by rw [add_comm, pow_add], map_mul,
      Subgroup.map_map]
    rfl
  have hleH : ∀ i : ℕ, f i ≤ H := by
    intro i
    have hai : a ^ i ∈ H := H.pow_mem (hAH haA) i
    have hmap : H.map (MulAut.conj (a ^ i)).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hai)
    calc f i = K.map (MulAut.conj (a ^ i)).toMonoidHom := rfl
      _ ≤ H.map (MulAut.conj (a ^ i)).toMonoidHom := Subgroup.map_mono hKH
      _ = H := hmap
  have hcomp : ∀ i : ℕ, CFSG.IsComponent ((f i).subgroupOf H) := by
    intro i
    have hai : a ^ i ∈ H := H.pow_mem (hAH haA) i
    let φ : ↥H ≃* ↥H := MulAut.conj ⟨a ^ i, hai⟩
    have hbase : CFSG.IsComponent ((K.subgroupOf H).map φ.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv φ hKcomp
    have heq : (K.subgroupOf H).map φ.toMonoidHom = (f i).subgroupOf H := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, f]
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨(y : G), hy, ?_⟩
        have hvy := congrArg Subtype.val hxy
        simpa only [φ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hvy
      · rintro ⟨y, hy, hxy⟩
        refine ⟨⟨y, hKH hy⟩, hy, ?_⟩
        apply Subtype.ext
        simpa only [φ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hxy
    rwa [heq] at hbase
  have hf_perfect : ∀ i : ℕ, ⁅f i, f i⁆ = f i := by
    intro i
    have hqi : CFSG.IsQuasisimple ↥(f i) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (hleH i)) (hcomp i).1
    exact Subgroup.isPerfect_iff.mp hqi.1
  have hf_card : ∀ i : ℕ, Nat.card (f i) = Nat.card K := by
    intro i
    exact Subgroup.card_map_of_injective (MulAut.conj (a ^ i)).injective
  obtain ⟨q, hq, hq2, hqdvd⟩ := exists_odd_prime_dvd_of_isComponent hKH hKcomp
  haveI : Fact q.Prime := ⟨hq⟩
  have hqcard : ∀ i : ℕ, q ∣ Nat.card (f i) := by
    intro i
    rw [hf_card i]
    exact hqdvd
  have h2dvd : 2 ∣ Nat.card K := two_dvd_card_of_isComponent_subgroupOf hKH hKcomp
  obtain ⟨zK, hzK⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2dvd
  let z : G := (zK : G)
  have hzK_mem : z ∈ K := zK.2
  have hz2 : orderOf z = 2 := by
    rw [show orderOf z = orderOf zK from Subgroup.orderOf_coe zK, hzK]
  have hper : f (orderOf a) = K := by
    change K.map (MulAut.conj (a ^ orderOf a)).toMonoidHom = K
    rw [pow_orderOf_eq_one, map_one]
    exact CFSG.QuasithinUnique.B113Lie.map_one_aut K
  have hex : ∃ k : ℕ, 0 < k ∧ f k = K := ⟨orderOf a, orderOf_pos a, hper⟩
  let d := Nat.find hex
  have hd_pos : 0 < d := (Nat.find_spec hex).1
  have hd_eq : f d = K := (Nat.find_spec hex).2
  have hd_min : ∀ k : ℕ, 0 < k → f k = K → d ≤ k :=
    fun k hk hk' => Nat.find_min' hex ⟨hk, hk'⟩
  have hd_ne_one : d ≠ 1 := by
    intro hd1
    apply haN
    have h1 : K.map (MulAut.conj a).toMonoidHom = K := by
      have hd1' := hd_eq
      rw [hd1] at hd1'
      simpa [f] using hd1'
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have hd_dvd : d ∣ orderOf a := by
    have hm : orderOf a = (orderOf a / d) * d + orderOf a % d := by
      rw [mul_comm]
      exact (Nat.div_add_mod (orderOf a) d).symm
    have hf_mul : ∀ k : ℕ, f (k * d) = K := by
      intro k
      induction k with
      | zero => simpa using hf0
      | succ k ih =>
        have heq : (k + 1) * d = k * d + d := by ring
        rw [heq, hf_add, ih]
        exact hd_eq
    have hmain : f ((orderOf a / d) * d + orderOf a % d) = K := hm ▸ hper
    rw [hf_add, hf_mul] at hmain
    by_cases hmod : orderOf a % d = 0
    · exact Nat.dvd_of_mod_eq_zero hmod
    · exfalso
      have hr : 0 < orderOf a % d := Nat.pos_of_ne_zero hmod
      have hlt : orderOf a % d < d := Nat.mod_lt _ hd_pos
      have hmin := hd_min _ hr (by simpa [f] using hmain)
      omega
  have hdvdA : orderOf a ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A haA
  have hcardA : Nat.card A = (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) :=
    card_eq_of_isZModSq h.ctx22.ctx.hAcard
  have hdvd_sq : d ∣ (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) := by
    rw [← hcardA]
    exact hd_dvd.trans hdvdA
  have hn0 : S17.nOf L ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := h26
    omega
  have hodd_sub : Odd (2 ^ S17.nOf L - 1) := by
    have hpow : Even (2 ^ S17.nOf L) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      refine ⟨2 ^ k, ?_⟩
      rw [hk, pow_succ]
      ring
    exact Nat.Even.sub_odd (Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))) hpow odd_one
  have hd_ge : 7 ≤ d := by
    by_contra hlt
    have hdle : d ≤ 6 := by omega
    have hdodd : Odd d := Odd.of_dvd_nat (hodd_sub.mul hodd_sub) hdvd_sq
    obtain ⟨k, hk⟩ := hdodd
    have hcases : d = 1 ∨ d = 3 ∨ d = 5 := by omega
    rcases hcases with h1 | h3 | h5
    · exact hd_ne_one h1
    · rw [h3] at hdvd_sq
      have h3dvd : 3 ∣ (2 ^ S17.nOf L - 1) ^ 2 := by
        rw [pow_two]
        exact hdvd_sq
      exact CFSG.GH74.Uniqueness.Hering.three_not_dvd_two_pow_sub_one h26
        (Nat.Prime.dvd_of_dvd_pow (p := 3) (n := 2) (by norm_num) h3dvd)
    · rw [h5] at hdvd_sq
      have h5dvd : 5 ∣ (2 ^ S17.nOf L - 1) ^ 2 := by
        rw [pow_two]
        exact hdvd_sq
      obtain ⟨m, hm⟩ := h26
      rw [hm] at h5dvd
      exact CFSG.SignalizerFunctorTheorem.McBride.SzModel.not_five_dvd_two_pow_sub_one m
        (Nat.Prime.dvd_of_dvd_pow (p := 5) (n := 2) (by norm_num) h5dvd)
  have hf_ne : ∀ i j : ℕ, i < j → j ≤ 6 → f i ≠ f j := by
    intro i j hij hj6 heq
    have hsub : j - i + i = j := Nat.sub_add_cancel (le_of_lt hij)
    have hstep : f j = (f (j - i)).map (MulAut.conj (a ^ i)).toMonoidHom := by
      rw [← hf_add (j - i) i, hsub]
    have hfi : f i = (f 0).map (MulAut.conj (a ^ i)).toMonoidHom := by
      rw [← hf_add 0 i, zero_add]
    have hmaps : (f 0).map (MulAut.conj (a ^ i)).toMonoidHom =
        (f (j - i)).map (MulAut.conj (a ^ i)).toMonoidHom := by
      rw [← hfi, heq, hstep]
    have hcancel : f 0 = f (j - i) :=
      Subgroup.map_injective (f := (MulAut.conj (a ^ i)).toMonoidHom)
        (MulAut.conj (a ^ i)).injective hmaps
    have hK : f (j - i) = K := by rw [← hcancel, hf0]
    have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
    have hle := hd_min _ hpos hK
    omega
  have hf_comm : ∀ i j : ℕ, i ≠ j → i ≤ 6 → j ≤ 6 → ⁅f i, f j⁆ = ⊥ := by
    intro i j hij hi6 hj6
    have hne : (f i).subgroupOf H ≠ (f j).subgroupOf H := by
      intro heq
      have hfi : f i = f j := by
        have hcongr := congrArg (Subgroup.map H.subtype) heq
        rwa [Subgroup.map_subgroupOf_eq_of_le (hleH i),
          Subgroup.map_subgroupOf_eq_of_le (hleH j)] at hcongr
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact hf_ne i j hlt hj6 hfi
      · exact hf_ne j i hgt hi6 hfi.symm
    rcases CFSG.LocalCores.distinct_components_commute (hcomp i) (hcomp j) with heq | hbot
    · exact absurd heq hne
    · have hcongr := congrArg (Subgroup.map H.subtype) hbot
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hleH i),
        Subgroup.map_subgroupOf_eq_of_le (hleH j), Subgroup.map_bot] at hcongr
  let P : ℕ → Subgroup G := fun j => ⨆ i ∈ Finset.range j, f (i + 1)
  have hP_leC : ∀ j : ℕ, j ≤ 6 → P j ≤ Subgroup.centralizer ({z} : Set G) := by
    intro j hj
    refine iSup₂_le fun i hi => ?_
    have hij : i < j := Finset.mem_range.mp hi
    have hc : f 0 ≤ Subgroup.centralizer ((f (i + 1) : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hf_comm 0 (i + 1) (by omega) (by omega) (by omega))
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hc (by rw [hf0]; exact hzK_mem)) y hy)
  have hrank : ∀ j : ℕ, j ≤ 6 → j ≤ CFSG.Open.pRank q (P j) := by
    intro j hj6
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have ih' : j ≤ CFSG.Open.pRank q (P j) := ih (by omega)
      have hle : P j ≤ P (j + 1) := by
        refine iSup₂_le fun i hi => ?_
        exact le_iSup₂_of_le i (Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega))
          le_rfl
      have hle2 : f (j + 1) ≤ P (j + 1) :=
        le_iSup₂_of_le j (Finset.mem_range.mpr (by omega)) le_rfl
      have hcomm : ⁅P j, f (j + 1)⁆ ≤ CFSG.Open.pCoreOf 2 (P (j + 1)) := by
        have hbot : ⁅P j, f (j + 1)⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          refine iSup₂_le fun i hi => ?_
          have hij : i < j := Finset.mem_range.mp hi
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (hf_comm (i + 1) (j + 1) (by omega) (by omega) (by omega))
        rw [hbot]
        exact bot_le
      have hstep := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf
        (q := q) (M := P (j + 1)) (L := P j) (X := f (j + 1)) hq2 hle hle2 hcomm
        (hf_perfect (j + 1)) (hqcard (j + 1))
      omega
  have h6 : 6 ≤ CFSG.Open.pRank q (Subgroup.centralizer ({z} : Set G)) :=
    (hrank 6 le_rfl).trans (CFSG.SectionRank.pRank_mono hq.one_lt (hP_leC 6 le_rfl))
  have hloc := uc22p22za_pRank_le_evenRank (p := q) hq hq2
    (CFSG.QuasithinUnique.Lin2.isTwoLocal_centralizer_of_sq_eq_one (z := z)
      (by rw [← hz2]; exact pow_orderOf_eq_one z) (by
        intro hz1
        rw [hz1, orderOf_one] at hz2
        omega))
  have he : evenRank G = 3 := evenRank_eq_three_of_ctx h.ctx22.ctx
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
