module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL264Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofKit
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltCtx
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearCover
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinearTwo
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores CFSG.GorensteinWalter CFSG.Open
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedScalars StatedSL)
open BenderSuzuki.MatrixGroups

@[expose] def IsLie42GenericL2 (X : Type) [Group X] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ Nonempty (X ≃* projSL 2 (GaloisField p e))) ∨
    (∃ n : ℕ, 4 ≤ n ∧ n ≠ 6 ∧ Nonempty (X ≃* projSL 2 (GaloisField 2 n)))

namespace Item434RowsProof.SeitzL2

theorem card_psl2_mul_gcd (F : Type) [Field F] [Finite F] :
    Nat.card (PSL2 F) * Nat.gcd 2 (Nat.card F - 1) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have h1 := (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin 2) F)).card_eq_card_quotient_mul_card_subgroup
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear F 2 (by norm_num),
    CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2 (by norm_num)] at h1
  change Nat.card (Matrix.SpecialLinearGroup (Fin 2) F ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) * _ = _
  rw [← h1]
  simp

theorem gcd_two_pow_sub_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Nat.gcd 2 (p ^ k - 1) = if p = 2 then 1 else 2 := by
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  split_ifs with h2
  · subst h2
    have hev : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    have hodd : ¬ 2 ∣ 2 ^ k - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  · have hodd : Odd (p ^ k) := (hp.odd_of_ne_two h2).pow
    have hev : 2 ∣ p ^ k - 1 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    exact Nat.gcd_eq_left hev

theorem three_dvd_of_not_dvd {s : ℕ} (hs : ¬ 3 ∣ s) : 3 ∣ s ^ 4 + s ^ 2 + 1 := by
  have h : s % 3 = 1 ∨ s % 3 = 2 := by omega
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.add_mod (s ^ 4), Nat.pow_mod, Nat.pow_mod s 2]
  rcases h with h | h <;> rw [h]

theorem cube_identity {s : ℕ} (hs : 1 ≤ s) :
    s ^ 3 * ((s ^ 3) ^ 2 - 1) = s * (s ^ 2 - 1) * (s ^ 2 * (s ^ 4 + s ^ 2 + 1)) := by
  have h2 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
  have h6 : 1 ≤ (s ^ 3) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hs)
  zify [h2, h6]
  ring

variable {K : Type} [Field K] [Finite K]

theorem card_le_three_of_pow_three {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) {P : Subgroup (PSL2 K)} (hP : ∀ x ∈ P, x ^ 3 = 1) :
    Nat.card P ≤ 3 := by
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hexp : Monoid.exponent P ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hP x x.2)
  have hPp : IsPGroup 3 P := IsPGroup.of_exponent_dvd_pow (n := 1) (by rwa [pow_one])
  have hcop : Nat.Coprime 3 (Nat.card K) := by
    rw [hK]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  by_cases h7 : 7 ≤ Nat.card K
  · obtain ⟨R, hR⟩ := hPp.exists_le_sylow
    have : IsCyclic (R : Subgroup (PSL2 K)) :=
      psl2_sylow_isCyclic_of_coprime_field_card K hK h7 3 (by norm_num) hcop R
    have : IsCyclic P := Subgroup.isCyclic_of_le hR
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd (by norm_num) hexp
  ·
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hdvd := Subgroup.card_subgroup_dvd_card P
    have hmul := card_psl2_mul_gcd K
    have hq : Nat.card K = 2 ∨ Nat.card K = 4 ∨ Nat.card K = 5 := by
      have hK3 : ¬ 3 ∣ Nat.card K := fun h =>
        absurd (Nat.Coprime.eq_one_of_dvd hcop h) (by norm_num)
      have hK1 : 2 ≤ Nat.card K := by
        rw [hK]
        exact hp.two_le.trans (Nat.le_self_pow (by omega) p)
      have hK6 : Nat.card K ≠ 6 := by
        intro h6
        have h2 : 2 ∣ p ^ f := by rw [← hK, h6]; norm_num
        have h3 : 3 ∣ p ^ f := by rw [← hK, h6]; norm_num
        have hp2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
          (Nat.prime_two.dvd_of_dvd_pow h2)
        have hp3' := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
          (Nat.prime_three.dvd_of_dvd_pow h3)
        omega
      omega
    have h60 : Nat.card (PSL2 K) ∣ 60 := by
      rcases hq with h | h | h
      · rw [h] at hmul
        have hc : Nat.card (PSL2 K) = 6 := by norm_num at hmul; omega
        rw [hc]
        norm_num
      · rw [h] at hmul
        have hc : Nat.card (PSL2 K) = 60 := by norm_num at hmul; omega
        rw [hc]
      · rw [h] at hmul
        have hc : Nat.card (PSL2 K) = 60 := by norm_num at hmul; omega
        rw [hc]
    have h3k : 3 ^ k ∣ 60 := by rw [← hk]; exact hdvd.trans h60
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      have := this.trans h3k
      norm_num at this
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num

theorem card_le_three_of_le_range_pglAction {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) {E : Subgroup (MulAut (PSL2 K))}
    (hE : ∀ α ∈ E, α ^ 3 = 1) (hle : E ≤ (pglAction K).range) : Nat.card E ≤ 3 := by
  have hinj := Item434SmallTwoOther.L264.conj_injective_psl2 K
  have hinn : E ≤ (MulAut.conj : PSL2 K →* _).range := fun α hα =>
    CFSG.RankThree.PartTwo.KFacts.isInnerAut_of_mem_inndiag_of_pow_three (hle hα) (hE α hα)
  have hPmap : (E.comap (MulAut.conj : PSL2 K →* _)).map MulAut.conj = E :=
    Subgroup.map_comap_eq_self hinn
  have hP3 : ∀ x ∈ E.comap (MulAut.conj : PSL2 K →* _), x ^ 3 = 1 :=
    fun x hx => hinj (by rw [map_pow, map_one]; exact hE _ hx)
  rw [← hPmap, Subgroup.card_map_of_injective hinj]
  exact card_le_three_of_pow_three hp3 hK hf hP3

theorem isCoatom_and_card_fixed {p f : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) (h8 : p = 2 → f ≠ 3)
    {φ : MulAut (PSL2 K)} (hφ3 : φ ^ 3 = 1) (hφ : φ ∉ (pglAction K).range) :
    IsCoatom (signalizerFixedSubgroup φ) ∧ 3 ∣ f ∧
      Nat.card (PSL2 K) = Nat.card (signalizerFixedSubgroup φ) *
        ((p ^ (f / 3)) ^ 2 * ((p ^ (f / 3)) ^ 4 + (p ^ (f / 3)) ^ 2 + 1)) := by
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hφ1 : φ ≠ 1 := fun h => hφ (h ▸ Subgroup.one_mem _)
  have hord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨σ, hσ, g, hg⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent Nat.prime_three φ hord hφ
  set π := pglAction K g
  have hfix : signalizerFixedSubgroup φ =
      (signalizerFixedSubgroup (psl2FieldAut K σ)).map π.toMonoidHom := by
    ext x
    constructor
    · intro hx
      have hx' : φ x = x := hx
      rw [hg, MulAut.mul_apply, MulAut.mul_apply] at hx'
      refine ⟨π⁻¹ x, ?_, ?_⟩
      · change psl2FieldAut K σ (π⁻¹ x) = π⁻¹ x
        have h := congrArg (fun y => π⁻¹ y) hx'
        simpa only [MulAut.inv_apply_self] using h
      · change π (π⁻¹ x) = x
        exact MulAut.apply_inv_self _ π x
    · rintro ⟨y, hy, rfl⟩
      have hy' : psl2FieldAut K σ y = y := hy
      change φ (π y) = π y
      rw [hg, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy']
  obtain ⟨e1⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixed_psl2FieldAut
    (by decide : Odd 3) hσ
  obtain ⟨hdvd, hcardσ⟩ := CFSG.RankThree.LinearTwo.card_fixedSubfield hp hf hK σ
  rw [hσ] at hdvd hcardσ
  set m := f / 3 with hm
  have hfm : f = m * 3 := by rw [hm]; exact (Nat.div_mul_cancel hdvd).symm
  have hm1 : 0 < m := by omega
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedSubfield K σ) p m hm1 hcardσ
  let e3 : signalizerFixedSubgroup φ ≃* PSL2MatrixGroup (GaloisField p m) :=
    (MulEquiv.subgroupCongr hfix).trans
      ((Subgroup.equivMapOfInjective _ π.toMonoidHom π.injective).symm.trans
        (e1.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2))))
  refine ⟨?_, hdvd, ?_⟩
  · by_cases hp2 : p = 2
    · subst hp2
      have hm2 : 2 ≤ m := by
        have := h8 rfl
        omega
      exact Item434SmallTwoOther.L264.isCoatom_of_mulEquiv_psl2_subfield hK Nat.prime_three
        (by norm_num) hfm hm2 e3
    · exact CFSG.Glauberman.Dickson.MaxUp.isCoatom_of_mulEquiv_psl2 hK hp2 Nat.prime_three
        (by norm_num) hfm e3
  ·
    set s := p ^ m with hs
    have hs1 : 1 ≤ s := Nat.one_le_pow _ _ hp.pos
    have hGF : Nat.card (GaloisField p m) = s := GaloisField.card p m (by omega)
    have hC := card_psl2_mul_gcd (GaloisField p m)
    have hS := card_psl2_mul_gcd K
    rw [← Nat.card_congr e3.toEquiv, hGF] at hC
    have hqs : Nat.card K = s ^ 3 := by rw [hK, hfm, hs, pow_mul]
    rw [hqs, cube_identity hs1] at hS
    have hg : Nat.gcd 2 (s ^ 3 - 1) = Nat.gcd 2 (s - 1) := by
      rw [hs, ← pow_mul, gcd_two_pow_sub_one hp (by omega), gcd_two_pow_sub_one hp hm1]
    rw [hg, ← hC] at hS
    have hgpos : 0 < Nat.gcd 2 (s - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    apply Nat.eq_of_mul_eq_mul_right hgpos
    rw [hS]
    ring

theorem card_eq_nine_and_closure_fixed_eq_top {p f : ℕ}
    [Fact p.Prime] (hp3 : p ≠ 3) (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) (h8 : p = 2 → f ≠ 3)
    {E : Subgroup (MulAut (PSL2 K))} (hE : ∀ α ∈ E, α ^ 3 = 1) (h9 : 9 ≤ Nat.card E) :
    Nat.card E = 9 ∧ Subgroup.closure {x : PSL2 K | ∃ ψ ∈ E, ψ ≠ 1 ∧ ψ x = x} = ⊤ := by
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ : MulAut (PSL2 K) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom
  have hker : Nat.card (E ⊓ ψ.ker : Subgroup _) ≤ 3 :=
    card_le_three_of_le_range_pglAction hp3 hK hf (fun α hα => hE α hα.1) fun α hα =>
      CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hα.2
  have himg : Nat.card (E.map ψ) ≤ 3 := Item434SmallTwoOther.L264.card_map_rightHom_le_three hE
  have hcard := Item434Alt.card_eq_card_inf_ker_mul_card_map ψ E
  have hE9 : Nat.card E = 9 := by
    have : Nat.card E ≤ 3 * 3 := by rw [hcard]; exact Nat.mul_le_mul hker himg
    omega
  have hker3 : 3 ≤ Nat.card (E ⊓ ψ.ker : Subgroup _) := by
    by_contra hlt
    have : Nat.card E ≤ 2 * 3 := by rw [hcard]; exact Nat.mul_le_mul (by omega) himg
    omega
  refine ⟨hE9, ?_⟩
  obtain ⟨c, hcE, hc1⟩ : ∃ c ∈ E ⊓ ψ.ker, c ≠ 1 := by
    rcases (E ⊓ ψ.ker).bot_or_exists_ne_one with hbot | h
    · rw [hbot, Subgroup.card_bot] at hker3
      omega
    · exact h
  obtain ⟨t, rfl⟩ : c ∈ (MulAut.conj : PSL2 K →* _).range :=
    CFSG.RankThree.PartTwo.KFacts.isInnerAut_of_mem_inndiag_of_pow_three
      (CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hcE.2) (hE _ hcE.1)
  have ht3 : t ^ 3 = 1 := Item434SmallTwoOther.L264.conj_injective_psl2 K
    (by rw [map_pow, map_one]; exact hE _ hcE.1)
  obtain ⟨φ, hφE, hφ⟩ : ∃ φ ∈ E, φ ∉ (pglAction K).range := by
    by_contra hcon
    push Not at hcon
    have := card_le_three_of_le_range_pglAction hp3 hK hf hE fun α hα => hcon α hα
    omega
  have hφ1 : φ ≠ 1 := fun h => hφ (h ▸ Subgroup.one_mem _)
  obtain ⟨hcoat, h3f, hcardS⟩ := isCoatom_and_card_fixed hp3 hK hf h8 (hE φ hφE) hφ
  set H := Subgroup.closure {x : PSL2 K | ∃ ψ ∈ E, ψ ≠ 1 ∧ ψ x = x} with hH
  have hfixH : signalizerFixedSubgroup φ ≤ H := fun x hx =>
    Subgroup.subset_closure ⟨φ, hφE, hφ1, hx⟩
  have hpt : IsPGroup 3 (Subgroup.zpowers t) := IsPGroup.of_exponent_dvd_pow (n := 1) (by
    rw [IsCyclic.exponent_eq_card, Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ht3)
  obtain ⟨R, hR⟩ := hpt.exists_le_sylow
  have h7 : 7 ≤ Nat.card K := by
    rw [hK]
    have hf3 : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    calc 7 ≤ 2 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf3
  have hcop : Nat.Coprime 3 (Nat.card K) := by
    rw [hK]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  have : IsCyclic (R : Subgroup (PSL2 K)) :=
    psl2_sylow_isCyclic_of_coprime_field_card K hK h7 3 (by norm_num) hcop R
  have htR : t ∈ (R : Subgroup (PSL2 K)) := hR (Subgroup.mem_zpowers t)
  have hRH : (R : Subgroup (PSL2 K)) ≤ H := fun r hr => Subgroup.subset_closure
    ⟨MulAut.conj t, hcE.1, hc1, by
      have hrt : r * t = t * r := congrArg Subtype.val
        ((IsCyclic.isMulCommutative (α := (R : Subgroup (PSL2 K)))).is_comm.comm
          ⟨r, hr⟩ ⟨t, htR⟩)
      rw [MulAut.conj_apply, ← hrt, mul_inv_cancel_right]⟩
  have hne : signalizerFixedSubgroup φ ≠ H := by
    intro heq
    have hRC : (R : Subgroup (PSL2 K)) ≤ signalizerFixedSubgroup φ := hRH.trans heq.symm.le
    obtain ⟨c', hc'⟩ := Subgroup.card_dvd_of_le hRC
    have hidx := (R : Subgroup (PSL2 K)).card_mul_index
    have hpm : ¬ 3 ∣ p ^ (f / 3) := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    obtain ⟨u, hu⟩ := three_dvd_of_not_dvd hpm
    have hRpos : 0 < Nat.card (R : Subgroup (PSL2 K)) := Nat.card_pos
    have h3 : 3 ∣ (R : Subgroup (PSL2 K)).index := by
      refine ⟨c' * (p ^ (f / 3)) ^ 2 * u, Nat.eq_of_mul_eq_mul_left hRpos ?_⟩
      rw [hidx, hcardS, hc', hu]
      ring
    exact R.not_dvd_index h3
  exact hcoat.lt_iff.mp (lt_of_le_of_ne hfixH hne)

omit [Finite K] in
theorem statedScalars_subgroupOf_eq_bot [CharP K 2] :
    (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot

theorem center_eq_bot_of_L2
    {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hK : Nat.card K = p ^ f) (θ : X ⧸ Subgroup.center X ≃* PSL2 K) :
    Subgroup.center X = ⊥ := by
  have hp : p.Prime := Fact.out
  have : Group.IsPerfect X := hq.1
  have hodd : Odd (Nat.card (Subgroup.center X)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    exact Odd.pow (by decide)
  by_cases hp2 : p = 2
  · subst hp2
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    obtain ⟨φ, -, -, hD⟩ := CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map
      (K := K) (n := 2) le_rfl hodd (θ.trans (CFSG.SectionRank.OddCover.pslEquiv K))
    rw [← hD, statedScalars_subgroupOf_eq_bot, Subgroup.map_bot]
  · set π : X →* PSL2 K := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hπ
    have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center X := by
      ext x
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h9 : p ^ f ≠ 9 := by
      intro h9
      have hdvd : p ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
        exact dvd_pow_self p (by rintro rfl; norm_num at h9)
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow hdvd))
    have h := (CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel hp2 hK π hπs
      (by rw [hker]) (by rw [hker]; exact hodd)).1 h9
    rwa [hker] at h

end Item434RowsProof.SeitzL2

open Item434RowsProof Item434RowsProof.SeitzL2

theorem seitzHyperGamma_eq_top_of_L2
    (X : Type) [Group X] [Finite X]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (hL : IsLie42GenericL2 (X ⧸ Subgroup.center X)) (E : Subgroup (MulAut X))
    (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hc : Nat.card E = 9 ∨ (Nat.card E = 27 ∧ Subgroup.center X = ⊥)) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  obtain ⟨p, e, hpF, hp3, he, hpe8, ⟨θ₀⟩⟩ : ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ e ∧
      (p = 2 → e ≠ 3) ∧ Nonempty (X ⧸ Subgroup.center X ≃* projSL 2 (GaloisField p e)) := by
    rcases hL with ⟨p, e, hp, hp3, he, h⟩ | ⟨n, hn4, hn6, h⟩
    · exact ⟨p, e, hp, by omega, he, fun h2 => by omega, h⟩
    · exact ⟨2, n, ⟨Nat.prime_two⟩, by norm_num, by omega, fun _ => by omega, h⟩
  set K := GaloisField p e with hKdef
  have hK : Nat.card K = p ^ e := GaloisField.card p e (by omega)
  set θ : X ⧸ Subgroup.center X ≃* PSL2 K := θ₀.trans (projSLEquivPSL K) with hθ
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_L2 hq hZ3 hp3 hK θ
  set ι : X ≃* PSL2 K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ
    with hι
  set E' : Subgroup (MulAut (PSL2 K)) := E.map (MulAut.congr ι).toMonoidHom with hE'
  have hE'3 : ∀ α ∈ E', α ^ 3 = 1 := by
    rintro _ ⟨α, hα, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 α hα, map_one]
  have hcard' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.congr ι).injective
  have h9 : 9 ≤ Nat.card E' := by
    rw [hcard']
    rcases hc with h | ⟨h, -⟩ <;> omega
  obtain ⟨hE9, hgen⟩ := card_eq_nine_and_closure_fixed_eq_top hp3 hK he hpe8 hE'3 h9
  have hEc : Nat.card E = 9 := by rw [← hcard', hE9]
  refine seitzHyperGamma_eq_top_of_closure hE.2 hEc ?_
  have hsub : {y : PSL2 K | ∃ ψ ∈ E', ψ ≠ 1 ∧ ψ y = y} ⊆
      ι.toMonoidHom '' {x : X | ∃ φ ∈ E, φ ≠ 1 ∧ φ x = x} := by
    rintro y ⟨_, ⟨φ, hφ, rfl⟩, hψ1, hψy⟩
    refine ⟨ι.symm y, ⟨φ, hφ, fun h1 => hψ1 ?_, ?_⟩, ι.apply_symm_apply y⟩
    · rw [h1, map_one]
    · have h1 : ι (φ (ι.symm y)) = y := by
        have h0 := hψy
        rw [MulEquiv.coe_toMonoidHom, MulAut.congr_apply] at h0
        exact h0
      have h2 := congrArg ι.symm h1
      rwa [MulEquiv.symm_apply_apply] at h2
  have htop : (⊤ : Subgroup (PSL2 K)) ≤ (Subgroup.closure
      {x : X | ∃ φ ∈ E, φ ≠ 1 ∧ φ x = x}).map ι.toMonoidHom := by
    rw [← hgen, MonoidHom.map_closure]
    exact Subgroup.closure_mono hsub
  rw [eq_top_iff]
  intro x _
  obtain ⟨z, hz, hzx⟩ := htop (Subgroup.mem_top (ι x))
  rwa [ι.injective hzx] at hz

end CFSG.RankThree.PartTwo.Sec4
