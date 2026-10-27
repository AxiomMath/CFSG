module

public import CFSG.Quasithin.MS93.SkItems
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Quasisimple

variable {Q : Type*} [Group Q]

theorem le_center_of_isQuasisimple (hQ : CFSG.IsQuasisimple Q) {K : Subgroup Q} [hK : K.Normal]
    (hne : K ≠ ⊤) : K ≤ Subgroup.center Q := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have hmap : (K.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hK.map _ (QuotientGroup.mk'_surjective _)
  rcases hmap.eq_bot_or_eq_top with h | h
  · intro x hx
    have hx' := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center Q)) hx
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  · exfalso
    apply hne
    have hdecomp : ∀ x : Q, ∃ z ∈ Subgroup.center Q,
        (QuotientGroup.mk x : Q ⧸ K) = QuotientGroup.mk z := by
      intro x
      have hx : QuotientGroup.mk' (Subgroup.center Q) x ∈
          K.map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := hx
      refine ⟨k⁻¹ * x, ?_, ?_⟩
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
        exact hkx
      · rw [QuotientGroup.eq]
        have := hK.conj_mem k⁻¹ (inv_mem hk) x⁻¹
        rwa [inv_inv, mul_assoc] at this
    have hcomm : commutator Q ≤ K := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [← QuotientGroup.eq_one_iff]
      obtain ⟨z, hz, hxz⟩ := hdecomp x
      obtain ⟨z', -, hyz⟩ := hdecomp y
      have hc : ⁅z, z'⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz z').symm
      have hmk : (QuotientGroup.mk ⁅x, y⁆ : Q ⧸ K) =
          ⁅(QuotientGroup.mk x : Q ⧸ K), QuotientGroup.mk y⁆ :=
        map_commutatorElement (QuotientGroup.mk' K) x y
      have hmk' : (QuotientGroup.mk ⁅z, z'⁆ : Q ⧸ K) =
          ⁅(QuotientGroup.mk z : Q ⧸ K), QuotientGroup.mk z'⁆ :=
        map_commutatorElement (QuotientGroup.mk' K) z z'
      rw [hmk, hxz, hyz, ← hmk', hc, QuotientGroup.mk_one]
    rw [hperf.commutator_eq_top] at hcomm
    exact top_le_iff.1 hcomm

end Quasisimple

section NaturalModules

variable {G : Type} [Group G]

theorem eq_one_of_isSumOfNaturalModulesVia {A V Z : Subgroup G} {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    {α : ↥A →* ↥Γ} (hnat : IsSumOfNaturalModulesVia A V Z α false 1) {a : ↥A}
    (ha : ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ = v) : α a = 1 := by
  obtain ⟨-, -, β, hβ, -, hβeq⟩ := hnat
  have key : ∀ x : ι → F,
      ((α a : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x = x := by
    intro x
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd (fun _ => x))
    have h := hβeq a u u (ha u u.2).symm 0
    rw [hu] at h
    simpa [moduleAct] using h.symm
  have hmat : ((α a : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) = 1 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
  apply Subtype.ext
  apply Units.ext
  simpa using hmat

end NaturalModules

section TwoCore

variable {G : Type} [Group G]

theorem map_pCore_le_pCoreOf {L M : Subgroup G} (hLM : L ≤ M)
    (hN : M ≤ Subgroup.normalizer (L : Set G)) :
    (CFSG.pCore 2 ↥L).map L.subtype ≤ pCoreOf 2 M := by
  set P := (CFSG.pCore 2 ↥L).map L.subtype with hP
  have hPM : P ≤ M := (Subgroup.map_subtype_le _).trans hLM
  have hPp : IsPGroup 2 P := CFSG.pCore_isPGroup.map L.subtype
  have key : ∀ m ∈ M, ∀ x ∈ P, m * x * m⁻¹ ∈ P := by
    intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmL : ∀ z : ↥L, m * (z : G) * m⁻¹ ∈ L := fun z =>
      (Subgroup.mem_normalizer_iff.1 (hN hm) z).1 z.2
    have hmL' : ∀ z : ↥L, m⁻¹ * (z : G) * m⁻¹⁻¹ ∈ L := fun z =>
      (Subgroup.mem_normalizer_iff.1 (hN (inv_mem hm)) z).1 z.2
    let σ : ↥L ≃* ↥L :=
      { toFun := fun z => ⟨m * z * m⁻¹, hmL z⟩
        invFun := fun z => ⟨m⁻¹ * z * m⁻¹⁻¹, hmL' z⟩
        left_inv := fun z => Subtype.ext (by simp [mul_assoc])
        right_inv := fun z => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun z w => Subtype.ext (by simp [mul_assoc]) }
    have hσ := CFSG.pCore_map_iso 2 σ
    have hmem : σ y ∈ CFSG.pCore 2 ↥L := by
      rw [← hσ]
      exact ⟨y, hy, rfl⟩
    exact ⟨σ y, hmem, rfl⟩
  have hnorm : M ≤ Subgroup.normalizer (P : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key m hm x, fun hx => ?_⟩
    have := key m⁻¹ (inv_mem hm) _ hx
    simpa [mul_assoc] using this
  have hle := CFSG.LieType.BorelTits.le_pCore 2
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hPM).2 hnorm)
    (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm)
  rw [pCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hPM]
  exact Subgroup.map_mono hle

theorem commute_of_mem_pCore {L M : Subgroup G} (hLM : L ≤ M)
    (hN : M ≤ Subgroup.normalizer (L : Set G)) {y : ↥L} (hy : y ∈ CFSG.pCore 2 ↥L) {u : G}
    (hu : u ∈ Xq M) : (y : G) * u * (y : G)⁻¹ = u := by
  have hyQ : (y : G) ∈ pCoreOf 2 M := map_pCore_le_pCoreOf hLM hN ⟨y, hy, rfl⟩
  have huZ := PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) hu
  have hc := Subgroup.mem_centralizer_iff.1 huZ.2 _ hyQ
  rw [hc, mul_inv_cancel_right]

end TwoCore

section CenterSL3

variable {F : Type} [Field F]

theorem pow_three_eq_one_of_mem_center_statedSL {g : ↥(StatedSL 3 F)}
    (hg : g ∈ Subgroup.center ↥(StatedSL 3 F)) : g ^ 3 = 1 := by
  set e := specialLinearGroupEquivStatedSL 3 F
  obtain ⟨A, rfl⟩ := e.surjective g
  have hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hg (e B)
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr3 : r ^ 3 = 1 := by simpa using hr
  have hA3 : A ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, ← map_pow, hr3, map_one]
    rfl
  rw [← map_pow, hA3, map_one]

theorem card_center_statedSL_three_le : Nat.card ↥(Subgroup.center ↥(StatedSL 3 F)) ≤ 3 := by
  set e := specialLinearGroupEquivStatedSL 3 F
  have h1 : Nat.card ↥(Subgroup.center ↥(StatedSL 3 F)) =
      Nat.card ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.card_map_of_injective e.injective
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := F) 0
  rw [h1, Nat.card_congr e.toEquiv, Fintype.card_fin]
  exact card_rootsOfUnity (R := F) (k := 3)

theorem pCore_le_ker_of_surjective_statedSL {L : Type*} [Group L] [Finite F]
    {α : L →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) : CFSG.pCore 2 L ≤ α.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.IsQuasisimple ↥(StatedSL 3 F) :=
    CFSG.Quasithin.EmptyFaithfulMultiple.FFL.isQuasisimple_statedSL (m := 2) le_rfl F
  have hNn : ((CFSG.pCore 2 L).map α).Normal := (CFSG.pCore_normal (p := 2) (G := L)).map α hα
  have hNp : IsPGroup 2 ↥((CFSG.pCore 2 L).map α) := (CFSG.pCore_isPGroup (p := 2) (G := L)).map α
  have hne : (CFSG.pCore 2 L).map α ≠ ⊤ := by
    intro htop
    rw [htop] at hNp
    have h2 : IsPGroup 2 ↥(StatedSL 3 F) := hNp.of_equiv Subgroup.topEquiv
    have : Group.IsPerfect ↥(StatedSL 3 F) := hq.1
    have : Nontrivial ↥(StatedSL 3 F) := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      obtain ⟨-, -, a, b, hab⟩ := hq
      exact hab (Subsingleton.elim _ _)
    exact Group.IsPerfect.not_isNilpotent _ h2.isNilpotent
  have hc := le_center_of_isQuasisimple hq hne
  rw [← Subgroup.map_eq_bot_iff, eq_bot_iff]
  intro g hg
  obtain ⟨k, hk⟩ := hNp ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 := pow_three_eq_one_of_mem_center_statedSL (hc hg)
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hd : orderOf g ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  rw [Subgroup.mem_bot]
  exact hd

end CenterSL3

private theorem ker_ne_top_of_surjective {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Surjective f) (hB : 1 < Nat.card B) : f.ker ≠ ⊤ := by
  intro htop
  have h1 : ∀ x : B, x = 1 := fun x => by
    obtain ⟨y, rfl⟩ := hf x
    exact (MonoidHom.mem_ker).1 (htop ▸ Subgroup.mem_top y)
  have : Nat.card B = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h1 a).trans (h1 b).symm⟩, ⟨1⟩⟩
  omega

theorem card_statedSL_three_eq_mul {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    {F : Type} [Field F] [Finite F] {α : Q →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) :
    ∃ c : ℕ, (c = 1 ∨ c = 3) ∧
      Nat.card ↥(StatedSL 3 F) = c * Nat.card (Q ⧸ Subgroup.center Q) := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hcardSL := CFSG.SectionRank.OddCover.card_statedSL_three (K := F)
  have hne : α.ker ≠ ⊤ := by
    refine ker_ne_top_of_surjective hα ?_
    rw [hcardSL]
    have e2 : 4 ≤ Nat.card F ^ 2 := by nlinarith
    have e3 : 8 ≤ Nat.card F ^ 3 := by nlinarith
    calc 1 < 8 * 3 * 7 := by norm_num
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul e3 (by omega)) (by omega)
  have hK : α.ker ≤ Subgroup.center Q := le_center_of_isQuasisimple hQ hne
  set Z := Subgroup.center Q with hZdef
  set c := Nat.card ↥(Z.map α) with hcdef
  refine ⟨c, ?_, ?_⟩
  · have hle : Z.map α ≤ Subgroup.center ↥(StatedSL 3 F) := Subgroup.map_center_le_center hα
    have hc3 : c ≤ 3 := (Subgroup.card_le_of_le hle).trans card_center_statedSL_three_le
    have hc0 : 0 < c := Nat.card_pos
    have hodd : ¬ 2 ∣ c := by
      intro h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Z.map α)) 2 h2
      have h3 : (g : ↥(StatedSL 3 F)) ^ 3 = 1 := pow_three_eq_one_of_mem_center_statedSL (hle g.2)
      have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using h3)
      have := orderOf_dvd_of_pow_eq_one hg3
      rw [hg] at this
      norm_num at this
    omega
  · have hQK : Nat.card Q = Nat.card ↥(StatedSL 3 F) * Nat.card α.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv]
    have hQZ : Nat.card Q = Nat.card (Q ⧸ Z) * Nat.card Z :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hZ : Nat.card Z = c * Nat.card α.ker := by
      set f := α.comp Z.subtype with hf
      have hker : f.ker = α.ker.subgroupOf Z := by
        ext x
        simp [f, Subgroup.mem_subgroupOf]
      have hrange : f.range = Z.map α := by
        rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv]
    have hpos : 0 < Nat.card α.ker := Nat.card_pos
    have key : Nat.card ↥(StatedSL 3 F) * Nat.card α.ker =
        (c * Nat.card (Q ⧸ Z)) * Nat.card α.ker := by
      rw [← hQK, hQZ, hZ]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos key

private theorem two_pow_mul_odd_eq {x y u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ x * u = 2 ^ y * v) : x = y ∧ u = v := by
  have key : ∀ {x y u v : ℕ}, Odd u → Odd v → 2 ^ x * u = 2 ^ y * v → x ≤ y → x = y ∧ u = v := by
    intro x y u v hu _ h hxy
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    rw [pow_add, mul_assoc] at h
    have h' : u = 2 ^ d * v := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa using h'
    · exfalso
      rw [h'] at hu
      have : Even (2 ^ d * v) := (Nat.even_pow.2 ⟨even_two, hd.ne'⟩).mul_right v
      exact (Nat.not_even_iff_odd.2 hu) this
  rcases le_total x y with hxy | hyx
  · exact key hu hv h hxy
  · obtain ⟨h1, h2⟩ := key hv hu h.symm hyx
    exact ⟨h1.symm, h2.symm⟩

private theorem odd_two_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have he : Even (2 ^ m) := Nat.even_pow.2 ⟨even_two, by omega⟩
  obtain ⟨r, hr⟩ := he
  exact ⟨r - 1, by omega⟩

theorem card_sl3_ne_card_sp4 {n k c : ℕ} (hk : 2 ≤ k) (hc : c = 1 ∨ c = 3) :
    (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) ≠
      c * ((2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1))) := by
  intro h
  have hc1 : 1 ≤ c := by omega
  have hcodd : Odd c := by rcases hc with rfl | rfl <;> decide
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h4 : 1 ≤ (2 ^ k) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    have hb2 : 1 ≤ (2 ^ k) ^ 2 - 1 := by
      have : 4 ≤ (2 ^ k) ^ 2 := by
        rw [← pow_mul]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hb4 : 1 ≤ (2 ^ k) ^ 4 - 1 := by
      have : 16 ≤ (2 ^ k) ^ 4 := by
        rw [← pow_mul]
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (k * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    simp at h
    have : 0 < c * ((2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1))) := by positivity
    omega
  · simp only [← pow_mul] at h
    have hu : Odd ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) :=
      (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
    have hv : Odd (c * ((2 ^ (k * 2) - 1) * (2 ^ (k * 4) - 1))) :=
      hcodd.mul ((odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega)))
    have h' : 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) =
        2 ^ (k * 4) * (c * ((2 ^ (k * 2) - 1) * (2 ^ (k * 4) - 1))) :=
      calc _ = 2 ^ (n * 3) * (2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1) := by ring
        _ = _ := h
        _ = _ := by ring
    obtain ⟨hnk, huv⟩ := two_pow_mul_odd_eq hu hv h'
    obtain ⟨m, rfl, rfl⟩ : ∃ m, n = 4 * m ∧ k = 3 * m := ⟨n / 4, by omega, by omega⟩
    have hm : 1 ≤ m := by omega
    have e12 : 4 * m * 3 = 3 * m * 4 := by ring
    rw [e12] at huv
    have hW : 0 < 2 ^ (3 * m * 4) - 1 := by
      have : 2 ≤ 2 ^ (3 * m * 4) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (3 * m * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have huv' : 2 ^ (4 * m * 2) - 1 = c * (2 ^ (3 * m * 2) - 1) := by
      apply Nat.eq_of_mul_eq_mul_right hW
      rw [huv]
      ring
    have hX : 4 ∣ 2 ^ (3 * m * 2) := by
      rw [show 3 * m * 2 = 2 + (6 * m - 2) by omega, pow_add]
      exact Dvd.intro _ rfl
    have hY : 4 ∣ 2 ^ (4 * m * 2) := by
      rw [show 4 * m * 2 = 2 + (8 * m - 2) by omega, pow_add]
      exact Dvd.intro _ rfl
    have hXY : 2 ^ (3 * m * 2) < 2 ^ (4 * m * 2) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hX1 : 1 ≤ 2 ^ (3 * m * 2) := Nat.one_le_two_pow
    rcases hc with rfl | rfl <;> omega

private theorem one_lt_card_sp4 {k : ℕ} (hk : 1 ≤ k) :
    1 < (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
  have hq : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : 4 ≤ (2 ^ k) ^ 2 := by nlinarith
  have h4 : 16 ≤ (2 ^ k) ^ 4 := by nlinarith
  calc 1 < 16 * (3 * 15) := by norm_num
    _ ≤ _ := Nat.mul_le_mul h4 (Nat.mul_le_mul (by omega) (by omega))

private theorem card_statedSp_two {F : Type} [Field F] [Finite F] {k : ℕ}
    (hF : Nat.card F = 2 ^ k) :
    Nat.card ↥(StatedSp 2 F) = (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by decide)]
  norm_num

section TypeExcl

variable {G : Type} [Group G] [Finite G]

theorem sl3_sp4U_false {M T L : Subgroup G} (h : PUHyp M T L) {n : ℕ} {F : Type} [Field F]
    [Fintype F] (hcardF : Fintype.card F = 2 ^ n) {α : ↥L →* ↥(StatedSL 3 F)}
    (hαs : Function.Surjective α) (hP₀α : CFSG.pCore 2 ↥L ≤ α.ker) (h4 : IsSp4U M T L) :
    False := by
  have hQ := h.quasisimple
  set αbar : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(StatedSL 3 F) := QuotientGroup.lift _ α hP₀α
  have hαbar : Function.Surjective αbar := by
    intro x
    obtain ⟨y, rfl⟩ := hαs x
    exact ⟨QuotientGroup.mk y, rfl⟩
  obtain ⟨c, hc, hSL⟩ := card_statedSL_three_eq_mul hQ hαbar
  have hcardF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcardF]
  rw [CFSG.SectionRank.OddCover.card_statedSL_three, hcardF'] at hSL
  rcases h4 with ⟨k, F', hF', hFt', β, hk2, hcardK, hβs, hβnat⟩ | ⟨β, hβs, hβnat⟩
  ·
    have hP₀β : CFSG.pCore 2 ↥L ≤ β.ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      exact eq_one_of_isSumOfNaturalModulesVia hβnat
        (fun v hv => commute_of_mem_pCore h.L_le h.le_normalizer hy (h.Uq_le_Xq hv))
    set βbar : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(StatedSp 2 F') := QuotientGroup.lift _ β hP₀β
    have hβbar : Function.Surjective βbar := by
      intro x
      obtain ⟨y, rfl⟩ := hβs x
      exact ⟨QuotientGroup.mk y, rfl⟩
    have hcardK' : Nat.card F' = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcardK]
    have hchar : CharP F' 2 := by
      obtain ⟨p, hp, m, hpp, hpm⟩ := FiniteField.card' F'
      rw [hcardK] at hpm
      have h2p : p ∣ 2 ^ k := hpm ▸ dvd_pow_self p (PNat.ne_zero m)
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
        (hpp.dvd_of_dvd_pow h2p)
      exact hp2 ▸ hp
    have hcen : Subgroup.center ↥(StatedSp 2 F') = ⊥ := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq,
        CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot]
    have hcardSp := card_statedSp_two hcardK'
    have hkerZ : βbar.ker = Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      apply le_antisymm
      · refine le_center_of_isQuasisimple hQ (ker_ne_top_of_surjective hβbar ?_)
        rw [hcardSp]
        exact one_lt_card_sp4 (by omega)
      · intro z hz
        rw [MonoidHom.mem_ker]
        have hmem := Subgroup.map_center_le_center hβbar ⟨z, hz, rfl⟩
        rwa [hcen, Subgroup.mem_bot] at hmem
    have hSp : Nat.card ↥(StatedSp 2 F') =
        Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective βbar hβbar).toEquiv]
      exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hkerZ).toEquiv
    rw [← hSp, hcardSp] at hSL
    exact card_sl3_ne_card_sp4 hk2 hc hSL
  ·
    set βL : ↥L →* ↥(StatedSp 2 (ZMod 2)) := β.comp (Subgroup.inclusion h.L_le)
    have hP₀β : CFSG.pCore 2 ↥L ≤ βL.ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      exact eq_one_of_isSumOfNaturalModulesVia hβnat (a := Subgroup.inclusion h.L_le y)
        (fun v hv => commute_of_mem_pCore h.L_le h.le_normalizer hy (h.Uq_le_Xq hv))
    set βbar : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(StatedSp 2 (ZMod 2)) := QuotientGroup.lift _ βL hP₀β
    have hcardSp2 : Nat.card ↥(StatedSp 2 (ZMod 2)) = 720 := by
      rw [card_statedSp_two (k := 1) (by rw [Nat.card_zmod]; rfl)]
      norm_num
    by_cases hker : βbar.ker = ⊤
    ·
      have hL1 : (L.subgroupOf M).map β = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        rw [Subgroup.mem_bot]
        have hmem : (QuotientGroup.mk ⟨x, hx⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ βbar.ker :=
          hker ▸ Subgroup.mem_top _
        exact (MonoidHom.mem_ker).1 hmem
      have htop : (T.subgroupOf M).map β = ⊤ := by
        have hsup : (⊤ : Subgroup ↥M) = L.subgroupOf M ⊔ T.subgroupOf M := by
          rw [← Subgroup.subgroupOf_sup h.L_le h.le, ← h.eq_sup, Subgroup.subgroupOf_self]
        rw [← Subgroup.map_top_of_surjective β hβs, hsup, Subgroup.map_sup, hL1, bot_sup_eq]
      have hTp : IsPGroup 2 ↥(T.subgroupOf M) :=
        h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm
      have hp : IsPGroup 2 ↥((T.subgroupOf M).map β) := hTp.map β
      rw [htop] at hp
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨m, hm⟩ := (hp.of_equiv Subgroup.topEquiv).exists_card_eq
      rw [hcardSp2] at hm
      have h3 : 3 ∣ 2 ^ m := hm ▸ (by norm_num : 3 ∣ 720)
      have := Nat.prime_three.dvd_of_dvd_pow h3
      norm_num at this
    · have hKZ := le_center_of_isQuasisimple hQ hker
      have hdvd1 : (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).index ∣ βbar.ker.index :=
        Subgroup.index_dvd_of_le hKZ
      have hdvd2 : βbar.ker.index ∣ 720 := by
        rw [← hcardSp2, Subgroup.index,
          Nat.card_congr (QuotientGroup.quotientKerEquivRange βbar).toEquiv]
        exact Subgroup.card_subgroup_dvd_card _
      have h7SL : 7 ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
        have : 7 ∣ (2 ^ n) ^ 3 - 1 := by
          have e : (2 ^ n) ^ 3 = 8 ^ n := by
            rw [← pow_mul, mul_comm, pow_mul]
            norm_num
          rw [e]
          simpa using Nat.sub_dvd_pow_sub_pow 8 1 n
        exact Dvd.dvd.mul_left this _
      rw [hSL] at h7SL
      have h7 : 7 ∣ (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).index := by
        rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h7SL with h7c | h7Z
        · rcases hc with rfl | rfl <;> norm_num at h7c
        · exact h7Z
      have := h7.trans (hdvd1.trans hdvd2)
      norm_num at this

theorem sl3U_sp4U_false {M T L M₁ T₁ : Subgroup G} (h : PUHyp M T L) (h₁ : PUHyp M₁ T₁ L)
    (h3 : IsSL3U M₁ T₁ L) (h4 : IsSp4U M T L) : False := by
  obtain ⟨hX₁, -, n, F, hF, hFt, α, hcardF, hαs, hαnat⟩ := h3
  refine sl3_sp4U_false h hcardF hαs (fun y hy => ?_) h4
  rw [MonoidHom.mem_ker]
  refine eq_one_of_isSumOfNaturalModulesVia hαnat (fun v hv => ?_)
  refine commute_of_mem_pCore h₁.L_le h₁.le_normalizer hy ?_
  rw [hX₁]
  exact le_sup_right (a := Zq M₁ L) hv

theorem case5_sp4U_false {M T L : Subgroup G} (h : PUHyp M T L) (h5 : MS93Case5 (Vq M L) L)
    (h4 : IsSp4U M T L) : False := by
  obtain ⟨n, F, hF, hFt, α, hcardF, hαs, -⟩ := h5
  exact sl3_sp4U_false h hcardF hαs (pCore_le_ker_of_surjective_statedSL hαs) h4

end TypeExcl

end CFSG.Quasithin.MS93
