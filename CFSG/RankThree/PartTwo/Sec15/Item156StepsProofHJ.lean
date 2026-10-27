module

import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item152GenProofX
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof156

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof152Gen
open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.CoprimeFixedPoint

variable {G : Type} [Group G] [Finite G]

theorem not_le_thetaQuotCentralizer_of_mem_partTwoF {A X : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hXp : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (h3 : 3 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    ¬ A ≤ Sec4.thetaQuotCentralizer X := by
  intro hAle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ē, hē3, hēZ⟩ := Sec6.exists_pow_three_eq_one_not_mem_center hXp h3
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) ē
  have hθ := solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAF.1.2 a a.2)⟩
  let α : ↥A →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hAX)
  have hα : ∀ (a : ↥A) (x : ↥X), ((α a x : ↥X) : G) = (a : G) * x * (a : G)⁻¹ :=
    fun a x => Sec4.normalizerMonoidHom_apply_coe _ x
  have hNα : ∀ a : ↥A, ∀ n ∈ aschbacherSolvableCore 3 ↥X,
      α a n ∈ aschbacherSolvableCore 3 ↥X := by
    intro a n hn
    rw [← Sec4.map_aschbacherSolvableCore (α a)]
    exact Subgroup.mem_map_of_mem _ hn
  have hlift := coprime_fixed_point_lifting 3 hA3 α _ hNα hθ.2.2.1
  have hfix : ((x₀ : ↥X) : ↥X ⧸ aschbacherSolvableCore 3 ↥X) ∈
      {q | ∀ a : ↥A, quotientAction α (aschbacherSolvableCore 3 ↥X) hNα a q = q} := by
    intro a
    rw [quotientAction_mk, QuotientGroup.eq]
    obtain ⟨-, hal⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hAle a.2)
    have h1 := inv_mem (hal (x₀ : G) x₀.2)
    have he : (((α a x₀)⁻¹ * x₀ : ↥X) : G) = ((x₀ : G)⁻¹ * ((a : G) * x₀ * (a : G)⁻¹))⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hα]
      group
    refine (Subgroup.mem_map_iff_mem X.subtype_injective).mp ?_
    rw [Subgroup.coe_subtype, he]
    exact h1
  rw [hlift] at hfix
  obtain ⟨x, hxfix, hxx₀⟩ := hfix
  have hxA : ∀ a ∈ A, a * (x : G) = (x : G) * a := by
    intro a ha
    have h := congrArg Subtype.val (hxfix ⟨a, ha⟩)
    rw [hα] at h
    calc a * (x : G) = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h]
  obtain ⟨e, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  have hyimg : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (x ^ r) =
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x₀) ^ r := by
    rw [map_pow, hxx₀]
    rfl
  have hēr : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x₀) ^ r ∉
      Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    intro hc
    apply hēZ
    rcases (show r % 3 = 1 ∨ r % 3 = 2 by omega) with h1 | h2
    · rwa [pow_eq_pow_mod r hē3, h1, pow_one] at hc
    · rw [pow_eq_pow_mod r hē3, h2] at hc
      have h4 := pow_mem hc 2
      rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hē3, one_mul] at h4
  have hy3 : ((x ^ r : ↥X) : G) ^ 3 = 1 := by
    have h : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ((x ^ r) ^ 3) = 1 := by
      rw [map_pow, hyimg, ← pow_mul, mul_comm, pow_mul, hē3, one_pow]
    have hmem : (x ^ r) ^ 3 ∈ aschbacherSolvableCore 3 ↥X := (QuotientGroup.eq_one_iff _).mp h
    have hk : ((x ^ r) ^ 3) ^ 3 ^ e = 1 := by
      rw [← pow_mul, ← pow_mul, show r * (3 * 3 ^ e) = 3 ^ e * r * 3 by ring, pow_mul, ← hor,
        pow_orderOf_eq_one, one_pow]
    have h1 := Sec13.eq_one_of_pow_three_pow_of_not_dvd hθ.2.2.1 hmem hk
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hyA : ((x ^ r : ↥X) : G) ∈ A := by
    refine mem_of_mem_partTwoF hAF hy3 (fun a ha => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_pow]
    exact ((Commute.pow_left (hxA a ha).symm r).eq).symm
  apply hēr
  rw [← hyimg, Subgroup.mem_center_iff]
  intro q
  obtain ⟨q', rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) q
  obtain ⟨-, hyl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hAle hyA)
  have h1 := hyl (q' : G) q'.2
  have h2 := (Subgroup.mem_normalizer_iff.mp
    (Sec6.le_normalizer_theta X (inv_mem (x ^ r).2)) _).mp h1
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  refine (Subgroup.mem_map_iff_mem X.subtype_injective).mp ?_
  rw [Subgroup.coe_subtype]
  have he : (((q' * x ^ r)⁻¹ * (x ^ r * q') : ↥X) : G) =
      ((x ^ r : ↥X) : G)⁻¹ * ((q' : G)⁻¹ * (((x ^ r : ↥X) : G) * q' * ((x ^ r : ↥X) : G)⁻¹)) *
        ((x ^ r : ↥X) : G)⁻¹⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
    group
  rw [he]
  exact h2

theorem card_mulAut_of_mulEquiv_five {Q : Type*} [Group Q] (e : Q ≃* alternatingGroup (Fin 5)) :
    Nat.card (MulAut Q) = 120 := by
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    ← Nat.card_congr CyclicAlternatingFive.autEquiv.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

theorem exists_ne_one_mem_thetaQuotCentralizer_of_five {B X : Subgroup G}
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hB9 : Nat.card B = 9)
    (e : ↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* alternatingGroup (Fin 5)) :
    ∃ b ∈ B, b ≠ 1 ∧ b ∈ Sec4.thetaQuotCentralizer X := by
  let f : ↥B →* MulAut (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    (Sec4.thetaQuotMulAut ↥X).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hBX))
  have hrange : Nat.card f.range ∣ 120 :=
    card_mulAut_of_mulEquiv_five e ▸ Subgroup.card_subgroup_dvd_card _
  have hk := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hB9] at hk
  by_contra hcon
  push Not at hcon
  have hker : Nat.card f.ker = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    by_contra hb1
    exact hcon b b.2 (fun h => hb1 (Subtype.ext h))
      ⟨Subgroup.inclusion hBX b, MonoidHom.mem_ker.mpr hb, rfl⟩
  rw [hker, one_mul] at hk
  rw [hk] at hrange
  norm_num at hrange

theorem mem_center_of_five_dvd_card_centralizer
    {Γ : Type} [Group Γ] [Finite Γ] (hΓ : Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2))
    (P : Sylow 3 Γ) {B : Subgroup Γ} (hBP : B ≤ P) (hB9 : Nat.card B = 9) {b : Γ} (hbB : b ∈ B)
    (h5 : 5 ∣ Nat.card (Subgroup.centralizer ({b} : Set Γ))) :
    b ∈ (P : Subgroup Γ) ⊓ Subgroup.centralizer ((P : Subgroup Γ) : Set Γ) := by
  by_contra hbZ
  obtain ⟨-, -, -, h4, -⟩ := Sec4.Sporadic.rank3II_4_15 Γ hΓ P _ rfl _ rfl
  obtain ⟨-, ⟨eN⟩, -⟩ := h4 B ⟨hBP, hB9⟩ b hbB hbZ
  have hN72 : Nat.card (Subgroup.normalizer (Subgroup.zpowers b : Set Γ)) = 72 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin,
      KFacts.KS14.card_alternatingGroup_four]
    rfl
  have hCN : Subgroup.centralizer ({b} : Set Γ) ≤
      Subgroup.normalizer (Subgroup.zpowers b : Set Γ) := by
    rw [← KFacts.KS14.centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  have hdvd := Subgroup.card_dvd_of_le hCN
  rw [hN72] at hdvd
  have := h5.trans hdvd
  norm_num at this

theorem false_of_isMulCommutative_card_twentySeven
    {L E : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hEL : E ≤ L) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE27 : Nat.card E = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set E' := E.subgroupOf L with hE'
  have hE'27 : Nat.card E' = 27 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE27]
  have hdisj : Disjoint E' π.ker := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hE'27, hπ, QuotientGroup.ker_mk', show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ.2.2.1)
  have hinj : Function.Injective (π.comp E'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (x : ↥L) ∈ E' ⊓ π.ker := ⟨x.2, hx⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  set Ē := E'.map π with hĒ
  have hĒ27 : Nat.card Ē = 27 := by
    have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
    rw [hĒ, ← h, hE'27]
  have hĒ3 : IsPGroup 3 Ē := IsPGroup.of_card (n := 3) (by rw [hĒ27]; norm_num)
  obtain ⟨P, hĒP⟩ := hĒ3.exists_le_sylow
  obtain ⟨⟨hH, -⟩, -⟩ := Sec4.Sporadic.rank3II_4_15 _ hJ P _ rfl _ rfl
  have hP27 : Nat.card (P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = 27 := hH.2.1
  have hĒeq : Ē = P := Subgroup.eq_of_le_of_card_ge hĒP (by rw [hP27, hĒ27])
  have hPc : Subgroup.center (P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨p, hp⟩ -
    rw [Subgroup.mem_center_iff]
    rintro ⟨q, hq⟩
    rw [← hĒeq] at hp hq
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc _ (Subgroup.mem_subgroupOf.mp hy) _ (Subgroup.mem_subgroupOf.mp hx))
  have h3 := hH.1.2.2.2
  rw [hPc, Subgroup.card_top, hP27] at h3
  norm_num at h3

theorem apply_eq_of_pow_three_eq_one {Q : Type*} [Group Q] [Finite Q]
    (hZ : Nat.card (Subgroup.center Q) = 3) {σ : MulAut Q} (hσ : σ ^ 3 = 1) {z : Q}
    (hz : z ∈ Subgroup.center Q) : σ z = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hz3 : z ^ 3 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center Q) hz
    rw [hZ] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hzc : Subgroup.zpowers z = Subgroup.center Q := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
    rw [hZ, Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
  have hσz : σ z ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := σ.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz h]
  have hmem : σ z ∈ Subgroup.zpowers z := hzc ▸ hσz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : σ z = z ^ (k % 3) := by
    rw [← hk]
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [zpow_add, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hz3, one_zpow,
      one_mul]
  have hσpow : ∀ n : ℕ, (σ ^ n) z = z ^ ((k % 3) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, hk', map_zpow, ih, ← zpow_mul, ← pow_succ]
  have h3 := hσpow 3
  rw [hσ, MulAut.one_apply] at h3
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
  · exfalso
    rw [h] at h3
    norm_num at h3
    exact hz1 h3
  · rw [hk', h, zpow_one]
  · exfalso
    rw [h] at h3
    have h8 : z ^ ((2 : ℤ) ^ 3) = z ^ (2 : ℤ) := by
      rw [show (2 : ℤ) ^ 3 = 2 + 3 * 2 by norm_num, zpow_add, zpow_mul,
        show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hz3, one_zpow, mul_one]
    rw [h8] at h3
    apply hz1
    have h5 : z ^ (2 : ℤ) = z * z := by rw [zpow_two]
    rw [h5] at h3
    have h6 : z * z = z * 1 := by rw [mul_one]; exact h3.symm
    exact mul_left_cancel h6

theorem mem_thetaQuotCentralizer_of_mk_mem_center {X : Subgroup G} {w : G} (hwX : w ∈ X)
    (hc : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨w, hwX⟩ ∈
      Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    w ∈ Sec4.thetaQuotCentralizer X := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.le_normalizer hwX, fun l hl => ?_⟩
  have h := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨l, hl⟩)
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at h
  have h2 : (((⟨l, hl⟩ * ⟨w, hwX⟩ : ↥X)⁻¹ * (⟨w, hwX⟩ * ⟨l, hl⟩) : ↥X) : G) ∈
      inSubgroup (aschbacherSolvableCore 3) X := ⟨_, h, rfl⟩
  have h3 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta X hwX) _).mp h2
  have he : l⁻¹ * (w * l * w⁻¹) =
      w * (((⟨l, hl⟩ * ⟨w, hwX⟩ : ↥X)⁻¹ * (⟨w, hwX⟩ * ⟨l, hl⟩) : ↥X) : G) * w⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [he]
  exact h3

theorem exists_ne_one_mem_thetaQuotCentralizer_of_six
    {A L X : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (h6 : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)))
    (hcov : X ≤ (X ⊓ L) ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    ∃ b ∈ A ⊓ L, b ≠ 1 ∧ b ∈ Sec4.thetaQuotCentralizer X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, h9, -⟩ := j2_point_facts hD hJ
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  set B := A ⊓ L with hB
  have hθ := solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  obtain ⟨wb, hwb⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) 3 (by rw [h6.1])
  have hwb3 : orderOf (wb : ↥X ⧸ aschbacherSolvableCore 3 ↥X) = 3 := by
    rw [Subgroup.orderOf_coe, hwb]
  have hwb3' : (wb : ↥X ⧸ aschbacherSolvableCore 3 ↥X) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (wb : ↥X ⧸ aschbacherSolvableCore 3 ↥X)
    rwa [hwb3] at h
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hAX
  have hBXL : B ≤ Subgroup.normalizer ((X ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hBX (inf_le_left.trans hD.le_normalizer)
  have hfixw : ∀ b (hb : b ∈ B),
      Sec4.thetaQuotMulAut ↥X (X.normalizerMonoidHom ⟨b, hBX hb⟩)
        (wb : ↥X ⧸ aschbacherSolvableCore 3 ↥X) = wb := by
    intro b hb
    refine apply_eq_of_pow_three_eq_one h6.1 ?_ wb.2
    have h1 : (⟨b, hBX hb⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hA.1.2 b hb.1)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hW := map_subgroupOf_eq_top_of_le_sup inf_le_left hcov
  obtain ⟨m, hm, hmw⟩ : (wb : ↥X ⧸ aschbacherSolvableCore 3 ↥X) ∈
      ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
    hW ▸ Subgroup.mem_top _
  have hmR : (m : G) ∈ X ⊓ L := Subgroup.mem_subgroupOf.mp hm
  set R := X ⊓ L with hR
  set K : Subgroup ↥R := (inSubgroup (aschbacherSolvableCore 3) X).subgroupOf R with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk r => ?_⟩
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta X r.2.1) _).mp hk
  have hB3 : IsPGroup 3 B := fun b => ⟨1, Subtype.ext (by simpa using hA.1.2 b b.2.1)⟩
  let α : ↥B →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hBXL)
  have hα : ∀ (b : ↥B) (x : ↥R), ((α b x : ↥R) : G) = (b : G) * x * (b : G)⁻¹ :=
    fun b x => Sec4.normalizerMonoidHom_apply_coe _ x
  have hKα : ∀ b : ↥B, ∀ k ∈ K, α b k ∈ K := by
    intro b k hk
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    rw [hα]
    exact (Subgroup.mem_normalizer_iff.mp
      ((hBX.trans (Sec6.normalizer_le_normalizer_theta X)) b.2) _).mp hk
  have hKcop : ¬ 3 ∣ Nat.card K := by
    intro h3
    apply hθ.2.2.1
    have h1 : Nat.card K ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) X) := by
      have h0 : Nat.card K =
          Nat.card (inSubgroup (aschbacherSolvableCore 3) X ⊓ R : Subgroup G) := by
        rw [hK, ← Subgroup.inf_subgroupOf_right]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : inSubgroup (aschbacherSolvableCore 3) X ⊓ R ≤ R)).toEquiv
      rw [h0]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (inSubgroup (aschbacherSolvableCore 3) X) =
        Nat.card (aschbacherSolvableCore 3 ↥X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    rw [h2] at h1
    exact h3.trans h1
  have hlift := coprime_fixed_point_lifting 3 hB3 α K hKα hKcop
  have hfix : ((⟨m, hmR⟩ : ↥R) : ↥R ⧸ K) ∈
      {q | ∀ b : ↥B, quotientAction α K hKα b q = q} := by
    intro b
    rw [quotientAction_mk, QuotientGroup.eq, hK, Subgroup.mem_subgroupOf]
    have h1 := hfixw b b.2
    rw [← hmw] at h1
    have h2 : (((X.normalizerMonoidHom ⟨b, hBX b.2⟩ m)⁻¹ * m : ↥X) : G) ∈
        inSubgroup (aschbacherSolvableCore 3) X :=
      ⟨_, QuotientGroup.eq.mp h1, rfl⟩
    have he : (((α b ⟨m, hmR⟩)⁻¹ * ⟨m, hmR⟩ : ↥R) : G) =
        (((X.normalizerMonoidHom ⟨b, hBX b.2⟩ m)⁻¹ * m : ↥X) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hα, Subgroup.coe_mul, Subgroup.coe_inv,
        Sec4.normalizerMonoidHom_apply_coe]
    rw [he]
    exact h2
  rw [hlift] at hfix
  obtain ⟨c', hc'fix, hc'm⟩ := hfix
  have hc'B : ∀ b ∈ B, b * (c' : G) = (c' : G) * b := by
    intro b hb
    have h := congrArg Subtype.val (hc'fix ⟨b, hb⟩)
    rw [hα] at h
    calc b * (c' : G) = b * c' * b⁻¹ * b := by group
      _ = c' * b := by rw [h]
  have hc'K : (c' : ↥R)⁻¹ * ⟨m, hmR⟩ ∈ K := QuotientGroup.eq.mp hc'm
  obtain ⟨e, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c').ne' 3 (by norm_num)
  set w : G := ((c' ^ r : ↥R) : G) with hw
  have hwX : w ∈ X := (c' ^ r).2.1
  have hwL : w ∈ L := (c' ^ r).2.2
  have hc'X : (c' : G) ∈ X := c'.2.1
  have hc'img : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨c', hc'X⟩ = wb := by
    rw [← hmw, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [hK, Subgroup.mem_subgroupOf] at hc'K
    obtain ⟨t, ht, hte⟩ := hc'K
    have he : (⟨c', hc'X⟩ : ↥X)⁻¹ * m = t := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [Subgroup.coe_subtype] at hte
      rw [hte]
      rfl
    rw [he]
    exact ht
  have hwimg : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨w, hwX⟩ =
      (wb : ↥X ⧸ aschbacherSolvableCore 3 ↥X) ^ r := by
    rw [← hc'img, ← map_pow]
    congr 1
  have hwc : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨w, hwX⟩ ∈
      Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rw [hwimg]
    exact pow_mem wb.2 r
  have hw1' : (wb : ↥X ⧸ aschbacherSolvableCore 3 ↥X) ^ r ≠ 1 := by
    intro h
    have h3 := orderOf_dvd_of_pow_eq_one h
    rw [hwb3] at h3
    exact hr3 h3
  have hw1 : w ≠ 1 := by
    intro h
    apply hw1'
    rw [← hwimg]
    have : (⟨w, hwX⟩ : ↥X) = 1 := Subtype.ext h
    rw [this, map_one]
  have hw3 : w ^ 3 = 1 := by
    have h : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ((⟨w, hwX⟩ : ↥X) ^ 3) = 1 := by
      rw [map_pow, hwimg, ← pow_mul, mul_comm, pow_mul, hwb3', one_pow]
    have hmem : (⟨w, hwX⟩ : ↥X) ^ 3 ∈ aschbacherSolvableCore 3 ↥X :=
      (QuotientGroup.eq_one_iff _).mp h
    have hk : ((⟨w, hwX⟩ : ↥X) ^ 3) ^ 3 ^ e = 1 := by
      have h0 : ((c' ^ r) ^ 3) ^ 3 ^ e = 1 := by
        rw [← pow_mul, ← pow_mul, show r * (3 * 3 ^ e) = 3 ^ e * r * 3 by ring, pow_mul, ← hor,
          pow_orderOf_eq_one, one_pow]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one]
      show (w ^ 3) ^ 3 ^ e = 1
      rw [hw, ← Subgroup.coe_pow, ← Subgroup.coe_pow, h0, Subgroup.coe_one]
    have h1 := Sec13.eq_one_of_pow_three_pow_of_not_dvd hθ.2.2.1 hmem hk
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hwB' : ∀ b ∈ B, b * w = w * b := by
    intro b hb
    rw [hw, Subgroup.coe_pow]
    exact (Commute.pow_right (hc'B b hb) r).eq
  by_cases hwB : w ∈ B
  · exact ⟨w, hwB, hw1, mem_thetaQuotCentralizer_of_mk_mem_center hwX hwc⟩
  · exfalso
    have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
      ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hA.1.2 x hx.1⟩
    have hE := isElemAbelian_sup_zpowers hBe hw3 hwB'
    have hcomm : ∀ x ∈ B, ∀ y ∈ Subgroup.zpowers w, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (hwB' x hx) k).eq
    obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    have hinf : B ⊓ Subgroup.zpowers w = ⊥ := by
      have hw3' : Nat.card (Subgroup.zpowers w) = 3 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
      have hdvd : Nat.card (B ⊓ Subgroup.zpowers w : Subgroup G) ∣ 3 :=
        hw3' ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact Subgroup.eq_bot_of_card_eq _ h
      · exfalso
        apply hwB
        have heq : B ⊓ Subgroup.zpowers w = Subgroup.zpowers w :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hw3'])
        have hmem : w ∈ B ⊓ Subgroup.zpowers w := heq.symm ▸ Subgroup.mem_zpowers w
        exact hmem.1
    have hE27 : Nat.card (B ⊔ Subgroup.zpowers w : Subgroup G) = 27 := by
      rw [hinf, Subgroup.card_bot, mul_one, h9, Nat.card_zpowers, orderOf_eq_prime hw3 hw1] at h1
      exact h1
    exact false_of_isMulCommutative_card_twentySeven hJ
      (sup_le inf_le_right (Subgroup.zpowers_le.mpr hwL))
      (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE27

end CFSG.RankThree.PartTwo.Sec15.Proof156
