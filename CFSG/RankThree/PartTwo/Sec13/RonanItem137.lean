module

public import CFSG.RankThree.PartTwo.Sec13.RonanItem137PGL
public import CFSG.RankThree.PartTwo.Sec13.Item137ProofInvert
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Transport
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanItem137

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open scoped commutatorElement

section Lift

variable {Γ : Type*} [Group Γ] [Finite Γ]

private theorem mem_normalizer_of_map_le' {X : Subgroup Γ} {g : Γ}
    (h : X.map (MulAut.conj g).toMonoidHom ≤ X) : g ∈ Subgroup.normalizer (X : Set Γ) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge h ?_)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_mem_inf_normalizer_inverting {N : Subgroup Γ} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {K₀ E₀ P₀ : Subgroup Γ} (hEK : E₀ ≤ Subgroup.normalizer (K₀ : Set Γ)) (hEP : E₀ ≤ P₀)
    (hPW : P₀ ≤ K₀ ⊔ E₀) (hP3 : IsPGroup 3 P₀)
    (hcent : ∀ z ∈ ⁅P₀, P₀⁆, ∀ x ∈ P₀, x * z = z * x)
    {k₀ : Γ} (hk₀ : k₀ ∈ K₀)
    (hnorm : ∀ x ∈ P₀, QuotientGroup.mk' N (k₀ * x * k₀⁻¹) ∈ P₀.map (QuotientGroup.mk' N))
    (hinv : ∀ z ∈ ⁅P₀, P₀⁆,
      QuotientGroup.mk' N (k₀ * z * k₀⁻¹) = (QuotientGroup.mk' N z)⁻¹) :
    ∃ k ∈ K₀, k ∈ Subgroup.normalizer (P₀ : Set Γ) ∧ ∀ z ∈ ⁅P₀, P₀⁆, k * z * k⁻¹ = z⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' N with hπ
  have hdisj : P₀ ⊓ N = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP3
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  have hinj : ∀ x ∈ P₀, ∀ y ∈ P₀, π x = π y → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
    have h2 : x⁻¹ * y ∈ P₀ ⊓ N := ⟨P₀.mul_mem (P₀.inv_mem hx) hy, h1⟩
    rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact h2
  set X : Subgroup Γ := (P₀ ⊔ N) ⊓ (K₀ ⊔ E₀) with hX
  have hP₀X : P₀ ≤ X := le_inf le_sup_left hPW
  have hXle : X ≤ P₀ ⊔ N := inf_le_left
  have hmem_sup : ∀ y : Γ, π y ∈ P₀.map π → y ∈ P₀ ⊔ N := by
    rintro y ⟨p, hp, hpy⟩
    have h1 : p⁻¹ * y ∈ N := QuotientGroup.eq.mp hpy
    have : y = p * (p⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hp h1
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 P₀ X := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hP₀X, hP3, ?_⟩
    intro h3
    have h1 := Subgroup.relIndex_mul_relIndex P₀ X (P₀ ⊔ N) hP₀X hXle
    have h2 : P₀.relIndex (P₀ ⊔ N) = P₀.relIndex N := by
      rw [sup_comm]
      exact CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal N P₀
    have h3' : P₀.relIndex N ∣ Nat.card N := Subgroup.index_dvd_card _
    apply hN
    refine dvd_trans h3 (dvd_trans (Dvd.intro _ h1) ?_)
    rw [h2]
    exact h3'
  have hk₀X : k₀ ∈ Subgroup.normalizer (X : Set Γ) := by
    apply mem_normalizer_of_map_le'
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxPN, hxW⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · obtain ⟨p, hp, ν, hν, hpν⟩ := Subgroup.mem_sup_of_normal_right.mp hxPN
      have e : (MulAut.conj k₀).toMonoidHom x = (k₀ * p * k₀⁻¹) * (k₀ * ν * k₀⁻¹) := by
        rw [← hpν]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      refine mul_mem (hmem_sup _ (hnorm p hp)) (Subgroup.mem_sup_right ?_)
      exact (inferInstance : N.Normal).conj_mem ν hν k₀
    · have : (MulAut.conj k₀).toMonoidHom x = k₀ * x * k₀⁻¹ := rfl
      rw [this]
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hk₀) hxW) (inv_mem (Subgroup.mem_sup_left hk₀))
  obtain ⟨n, hnX, m, hmN, hk₀nm⟩ := Sec18.exists_mul_of_isSylowOf hsyl
    (K := Subgroup.zpowers k₀) (Subgroup.zpowers_le.mpr hk₀X) (Subgroup.mem_zpowers k₀)
  obtain ⟨p, hp, ν, hν, hpν⟩ := Subgroup.mem_sup_of_normal_right.mp (hXle hnX)
  have hπν : π ν = 1 := (QuotientGroup.eq_one_iff ν).mpr hν
  have hπn : π n = π p := by
    rw [← hpν, map_mul, hπν, mul_one]
  have hmW : m ∈ K₀ ⊔ E₀ := by
    have : m = n⁻¹ * k₀ := by rw [hk₀nm]; group
    rw [this]
    exact mul_mem (inv_mem (Subgroup.mem_inf.mp hnX).2) (Subgroup.mem_sup_left hk₀)
  have hmm : m ∈ ((E₀ ⊔ K₀ : Subgroup Γ) : Set Γ) := by
    rw [sup_comm]
    exact hmW
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E₀ K₀ hEK] at hmm
  obtain ⟨x, hx, k, hk, hxk⟩ := hmm
  have hkm : k = x⁻¹ * m := by rw [← hxk]; group
  have hxN : x ∈ Subgroup.normalizer (P₀ : Set Γ) := Subgroup.le_normalizer (hEP hx)
  refine ⟨k, hk, ?_, ?_⟩
  · rw [hkm]
    exact mul_mem (inv_mem hxN) hmN
  · intro z hz
    have hzP : z ∈ P₀ := by
      refine (Subgroup.commutator_le.mpr ?_ : ⁅P₀, P₀⁆ ≤ P₀) hz
      intro a ha b hb
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hmconj : P₀.map (MulAut.conj m).toMonoidHom = P₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hmN
    have hmz : m * z * m⁻¹ ∈ ⁅P₀, P₀⁆ := by
      have : (MulAut.conj m).toMonoidHom z ∈ ⁅P₀, P₀⁆.map (MulAut.conj m).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hz
      rw [Subgroup.map_commutator, hmconj] at this
      exact this
    have hmzP : m * z * m⁻¹ ∈ P₀ := by
      refine (Subgroup.commutator_le.mpr ?_ : ⁅P₀, P₀⁆ ≤ P₀) hmz
      intro a ha b hb
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hπm : π (m * z * m⁻¹) = π z⁻¹ := by
      have e : m * z * m⁻¹ = n⁻¹ * (k₀ * z * k₀⁻¹) * n := by
        rw [show m = n⁻¹ * k₀ by rw [hk₀nm]; group]
        group
      rw [e, map_mul, map_mul, map_inv, hπn, hinv z hz, ← map_inv, ← map_inv, ← map_mul,
        ← map_mul]
      congr 1
      have h1 := hcent z⁻¹ (inv_mem hz) p hp
      rw [mul_assoc, ← h1]
      group
    have hmz' : m * z * m⁻¹ = z⁻¹ := hinj _ hmzP _ (inv_mem hzP) hπm
    have hxz : x⁻¹ * z⁻¹ * x = z⁻¹ := by
      have h1 := hcent z⁻¹ (inv_mem hz) x⁻¹ (inv_mem (hEP hx))
      rw [h1]
      group
    rw [hkm]
    calc x⁻¹ * m * z * (x⁻¹ * m)⁻¹ = x⁻¹ * (m * z * m⁻¹) * x := by group
      _ = z⁻¹ := by rw [hmz', hxz]

end Lift

section Prod

theorem prod_conj_one_left {A B : Type*} [Group A] [Group B] (a : A) (s σ : B) :
    ((1 : A), σ) * (a, s) * ((1 : A), σ)⁻¹ = (a, σ * s * σ⁻¹) := by
  ext <;> simp

variable {Y₁ : Type*} [Group Y₁] [Finite Y₁] {Y₀ : Type*} [Group Y₀] [Finite Y₀]

theorem card_top_prod (S : Subgroup Y₀) :
    Nat.card ((⊤ : Subgroup (Multiplicative (ZMod 3))).prod S : Subgroup _) = 3 * Nat.card S := by
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top,
    Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)), Nat.card_zmod]

theorem exists_eq_top_prod {Q : Subgroup (Multiplicative (ZMod 3) × Y₀)}
    (hY₀ : (Nat.card Y₀).factorization 3 = 3) (hQ : Nat.card Q = 81) :
    ∃ S : Subgroup Y₀, Nat.card S = 27 ∧
      Q = (⊤ : Subgroup (Multiplicative (ZMod 3))).prod S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := Q.map (MonoidHom.snd (Multiplicative (ZMod 3)) Y₀) with hS
  have hQle : Q ≤ (⊤ : Subgroup (Multiplicative (ZMod 3))).prod S := by
    intro x hx
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_map_of_mem _ hx⟩
  have hge : 27 ≤ Nat.card S := by
    have h1 := Subgroup.card_le_of_le hQle
    rw [card_top_prod, hQ] at h1
    omega
  have hdvd81 : Nat.card S ∣ 81 := by
    have := Subgroup.card_map_dvd (H := Q) (MonoidHom.snd (Multiplicative (ZMod 3)) Y₀)
    rwa [hQ] at this
  have hdvdY : Nat.card S ∣ Nat.card Y₀ := Subgroup.card_subgroup_dvd_card S
  have hle : Nat.card S ≤ 27 := by
    have hpos : 0 < Nat.card S := Nat.card_pos
    obtain ⟨a, ha, hSa⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card S ∣ 3 ^ 4 by
      simpa using hdvd81)
    have h3 : 3 ^ a ∣ Nat.card Y₀ := hSa ▸ hdvdY
    have hY0 : Nat.card Y₀ ≠ 0 := Nat.card_pos.ne'
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hY0).mp h3
    rw [hY₀] at this
    rw [hSa]
    calc 3 ^ a ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
      _ = 27 := by norm_num
  have hS27 : Nat.card S = 27 := le_antisymm hle hge
  refine ⟨S, hS27, ?_⟩
  exact Subgroup.eq_of_le_of_card_ge hQle (by rw [card_top_prod, hQ, hS27])

theorem commutator_top_prod (S : Subgroup Y₀) :
    ⁅(⊤ : Subgroup (Multiplicative (ZMod 3))).prod S, (⊤ : Subgroup (Multiplicative (ZMod 3))).prod S⁆ =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod ⁅S, S⁆ := by
  rw [Subgroup.commutator_prod_prod]
  congr 1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x _
  rw [Subgroup.mem_centralizer_iff]
  intro y _
  exact mul_comm y x

theorem exists_inverting_of_prod (φ : Y₁ ≃* Multiplicative (ZMod 3) × Y₀)
    (hY₀ : (Nat.card Y₀).factorization 3 = 3) {Pb : Subgroup Y₁} (hPb : Nat.card Pb = 81)
    (hT3 : ∀ S : Subgroup Y₀, Nat.card S = 27 → ∃ σ ∈ commutator Y₀,
      σ ∈ Subgroup.normalizer (S : Set Y₀) ∧ (∀ z ∈ ⁅S, S⁆, σ * z * σ⁻¹ = z⁻¹) ∧
        (∀ z ∈ ⁅S, S⁆, ∀ x ∈ S, x * z = z * x)) :
    ∃ b : Y₁, φ b ∈ (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator Y₀) ∧
      b ∈ Subgroup.normalizer (Pb : Set Y₁) ∧ (∀ z ∈ ⁅Pb, Pb⁆, b * z * b⁻¹ = z⁻¹) ∧
      (∀ z ∈ ⁅Pb, Pb⁆, ∀ x ∈ Pb, x * z = z * x) := by
  set Q := Pb.map φ.toMonoidHom with hQdef
  have hQ : Nat.card Q = 81 := by
    rw [hQdef, Subgroup.card_map_of_injective φ.injective, hPb]
  obtain ⟨S, hS27, hQS⟩ := exists_eq_top_prod hY₀ hQ
  obtain ⟨σ, hσc, hσN, hσinv, hσcent⟩ := hT3 S hS27
  have hPbmem : ∀ x : Y₁, x ∈ Pb ↔ (φ x).2 ∈ S := by
    intro x
    constructor
    · intro hx
      have : φ x ∈ Q := Subgroup.mem_map_of_mem _ hx
      rw [hQS] at this
      exact (Subgroup.mem_prod.mp this).2
    · intro hx
      have : φ x ∈ Q := by
        rw [hQS]
        exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, hx⟩
      obtain ⟨y, hy, hyx⟩ := this
      have : y = x := φ.injective hyx
      rwa [this] at hy
  have hcomm : ∀ z ∈ ⁅Pb, Pb⁆, (φ z).1 = 1 ∧ (φ z).2 ∈ ⁅S, S⁆ := by
    intro z hz
    have h1 : φ z ∈ ⁅Q, Q⁆ := by
      have : φ.toMonoidHom z ∈ ⁅Pb, Pb⁆.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hz
      rwa [Subgroup.map_commutator] at this
    rw [hQS, commutator_top_prod] at h1
    obtain ⟨h1a, h1b⟩ := Subgroup.mem_prod.mp h1
    exact ⟨Subgroup.mem_bot.mp h1a, h1b⟩
  refine ⟨φ.symm (1, σ), ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hσc⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have e : φ (φ.symm (1, σ) * x * (φ.symm (1, σ))⁻¹) = ((φ x).1, σ * (φ x).2 * σ⁻¹) := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact prod_conj_one_left _ _ _
    rw [hPbmem, hPbmem, e]
    exact Subgroup.mem_normalizer_iff.mp hσN _
  · intro z hz
    obtain ⟨hz1, hz2⟩ := hcomm z hz
    apply φ.injective
    have hφz : φ z = (1, (φ z).2) := Prod.ext hz1 rfl
    have h3 := hσinv _ hz2
    calc φ (φ.symm (1, σ) * z * (φ.symm (1, σ))⁻¹)
        = (1, σ) * φ z * (1, σ)⁻¹ := by
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      _ = (1, σ) * (1, (φ z).2) * (1, σ)⁻¹ := by rw [← hφz]
      _ = (1, σ * (φ z).2 * σ⁻¹) := prod_conj_one_left _ _ _
      _ = (1, ((φ z).2)⁻¹) := by rw [h3]
      _ = (φ z)⁻¹ := Prod.ext (by rw [Prod.fst_inv, hz1]; exact inv_one.symm) rfl
      _ = φ z⁻¹ := (map_inv _ _).symm
  · intro z hz x hx
    obtain ⟨hz1, hz2⟩ := hcomm z hz
    have hxS := (hPbmem x).mp hx
    apply φ.injective
    rw [map_mul, map_mul]
    refine Prod.ext ?_ ?_
    · show (φ x).1 * (φ z).1 = (φ z).1 * (φ x).1
      exact mul_comm _ _
    · exact hσcent _ hz2 _ hxS

end Prod

section Glue

noncomputable def mapEquivOfInjOn {Γ M : Type*} [Group Γ] [Group M] (f : Γ →* M)
    {X : Subgroup Γ} (h : ∀ x ∈ X, ∀ y ∈ X, f x = f y → x = y) : X ≃* X.map f :=
  (MonoidHom.ofInjective (f := f.comp X.subtype)
    (fun a b hab => Subtype.ext (h a a.2 b b.2 hab))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem card_map_eq_of_injOn' {Γ M : Type*} [Group Γ] [Group M] (f : Γ →* M)
    {X : Subgroup Γ} (h : ∀ x ∈ X, ∀ y ∈ X, f x = f y → x = y) :
    Nat.card (X.map f) = Nat.card X :=
  (Nat.card_congr (mapEquivOfInjOn f h).toEquiv).symm

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem factorization_card_map_mk {N : Subgroup Γ} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    (W : Subgroup Γ) :
    (Nat.card (W.map (QuotientGroup.mk' N))).factorization 3 = (Nat.card W).factorization 3 := by
  set ψ := (QuotientGroup.mk' N).comp W.subtype with hψ
  have hrange : ψ.range = W.map (QuotientGroup.mk' N) := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 : Nat.card W = Nat.card (W ⧸ ψ.ker) * Nat.card ψ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (W ⧸ ψ.ker) = Nat.card (W.map (QuotientGroup.mk' N)) := by
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have h3 : Nat.card ψ.ker ∣ Nat.card N := by
    let g : ψ.ker →* N :=
      ((W.subtype.comp ψ.ker.subtype).codRestrict N (fun w => by
        have := w.2
        rw [MonoidHom.mem_ker] at this
        exact (QuotientGroup.eq_one_iff _).mp this))
    refine Subgroup.card_dvd_of_injective g (fun a b hab => ?_)
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have h4 : ¬ 3 ∣ Nat.card ψ.ker := fun h => hN (h.trans h3)
  have hpos1 : Nat.card ψ.ker ≠ 0 := Nat.card_pos.ne'
  have hpos2 : Nat.card (W ⧸ ψ.ker) ≠ 0 := Nat.card_pos.ne'
  rw [h1, Nat.factorization_mul hpos2 hpos1, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h4, add_zero, h2]

theorem exists_mem_inf_normalizer_inverting_of_prod {N : Subgroup Γ} [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {K₀ E₀ P₀ : Subgroup Γ}
    (hEK : E₀ ≤ Subgroup.normalizer (K₀ : Set Γ)) (hEP : E₀ ≤ P₀) (hPW : P₀ ≤ K₀ ⊔ E₀)
    (hP3 : IsPGroup 3 P₀) (hP81 : Nat.card P₀ = 81)
    (hW81 : (Nat.card ↥(K₀ ⊔ E₀)).factorization 3 = 4)
    {Y₀ : Type*} [Group Y₀] [Finite Y₀] {Y : Subgroup (Γ ⧸ N)}
    (hY : Y = (K₀ ⊔ E₀).map (QuotientGroup.mk' N)) :
    ∀ (φ : ↥Y ≃* Multiplicative (ZMod 3) × Y₀)
    (hKφ : (((K₀.map (QuotientGroup.mk' N)).subgroupOf Y).map φ.toMonoidHom) =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator Y₀))
    (hT3 : (Nat.card Y₀).factorization 3 = 3 → ∀ S : Subgroup Y₀, Nat.card S = 27 →
      ∃ σ ∈ commutator Y₀,
      σ ∈ Subgroup.normalizer (S : Set Y₀) ∧ (∀ z ∈ ⁅S, S⁆, σ * z * σ⁻¹ = z⁻¹) ∧
        (∀ z ∈ ⁅S, S⁆, ∀ x ∈ S, x * z = z * x)),
    ∃ k ∈ K₀, k ∈ Subgroup.normalizer (P₀ : Set Γ) ∧ ∀ z ∈ ⁅P₀, P₀⁆, k * z * k⁻¹ = z⁻¹ := by
  classical
  subst hY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' N with hπ
  set W₀ := K₀ ⊔ E₀ with hW₀
  set Y₁ := W₀.map π with hY₁
  intro φ hKφ hT3
  have hdisj : P₀ ⊓ N = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP3
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  have hinj : ∀ x ∈ P₀, ∀ y ∈ P₀, π x = π y → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
    have h2 : x⁻¹ * y ∈ P₀ ⊓ N := ⟨P₀.mul_mem (P₀.inv_mem hx) hy, h1⟩
    rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact h2
  have hY₁3 : (Nat.card Y₁).factorization 3 = 4 := by
    rw [hY₁, factorization_card_map_mk hN W₀, hW81]
  have hY₀ : (Nat.card Y₀).factorization 3 = 3 := by
    have hc : Nat.card Y₁ = 3 * Nat.card Y₀ := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_prod,
        Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)), Nat.card_zmod]
    have h0 : Nat.card Y₀ ≠ 0 := Nat.card_pos.ne'
    rw [hc, Nat.factorization_mul (by norm_num) h0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three] at hY₁3
    omega
  have hPY : P₀.map π ≤ Y₁ := Subgroup.map_mono hPW
  set Pb : Subgroup Y₁ := (P₀.map π).subgroupOf Y₁ with hPb
  have hPb81 : Nat.card Pb = 81 := by
    rw [hPb, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv,
      card_map_eq_of_injOn' π hinj, hP81]
  obtain ⟨b, hbK, hbN, hbinv, hbcent⟩ := exists_inverting_of_prod φ hY₀ hPb81 (hT3 hY₀)
  have hbmem : b ∈ (K₀.map π).subgroupOf Y₁ := by
    have : φ b ∈ ((K₀.map π).subgroupOf Y₁).map φ.toMonoidHom := by rw [hKφ]; exact hbK
    obtain ⟨b', hb', hbb'⟩ := this
    have : b' = b := φ.injective hbb'
    rwa [this] at hb'
  obtain ⟨k₀, hk₀, hk₀b⟩ := Subgroup.mem_subgroupOf.mp hbmem
  have hmemPb : ∀ y : Y₁, y ∈ Pb ↔ (y : Γ ⧸ N) ∈ P₀.map π := fun y => Iff.rfl
  have hbPb : ∀ x ∈ P₀, ∀ (hx : π x ∈ Y₁), (⟨π x, hx⟩ : Y₁) ∈ Pb := fun x hx hx' =>
    (hmemPb _).mpr (Subgroup.mem_map_of_mem _ hx)
  have hnorm : ∀ x ∈ P₀, π (k₀ * x * k₀⁻¹) ∈ P₀.map π := by
    intro x hx
    have hxY : π x ∈ Y₁ := hPY (Subgroup.mem_map_of_mem _ hx)
    have h1 := (Subgroup.mem_normalizer_iff.mp hbN) ⟨π x, hxY⟩
    have h2 := h1.mp (hbPb x hx hxY)
    have e : ((b * ⟨π x, hxY⟩ * b⁻¹ : Y₁) : Γ ⧸ N) = π (k₀ * x * k₀⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hk₀b, map_mul, map_inv]
    rw [← e]
    exact h2
  have hcommP : ∀ z ∈ ⁅P₀, P₀⁆, ∃ w : Y₁, w ∈ ⁅Pb, Pb⁆ ∧ (w : Γ ⧸ N) = π z := by
    intro z hz
    have hz' : π z ∈ ⁅P₀.map π, P₀.map π⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem _ hz
    have hmapPb : Pb.map Y₁.subtype = P₀.map π := by
      rw [hPb, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPY]
    rw [← hmapPb, ← Subgroup.map_commutator] at hz'
    obtain ⟨w, hw, hwz⟩ := hz'
    exact ⟨w, hw, hwz⟩
  have hinv : ∀ z ∈ ⁅P₀, P₀⁆, π (k₀ * z * k₀⁻¹) = (π z)⁻¹ := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hcommP z hz
    have h1 := hbinv w hw
    have e : ((b * w * b⁻¹ : Y₁) : Γ ⧸ N) = π (k₀ * z * k₀⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hk₀b, hwz, map_mul, map_inv]
    rw [← e, h1]
    simp only [Subgroup.coe_inv, hwz]
  have hcent : ∀ z ∈ ⁅P₀, P₀⁆, ∀ x ∈ P₀, x * z = z * x := by
    intro z hz x hx
    obtain ⟨w, hw, hwz⟩ := hcommP z hz
    have hxY : π x ∈ Y₁ := hPY (Subgroup.mem_map_of_mem _ hx)
    have h1 := hbcent w hw ⟨π x, hxY⟩ (hbPb x hx hxY)
    have h2 : π x * π z = π z * π x := by
      have := congrArg Subtype.val h1
      simpa only [Subgroup.coe_mul, hwz] using this
    have hzP : z ∈ P₀ := by
      refine (Subgroup.commutator_le.mpr ?_ : ⁅P₀, P₀⁆ ≤ P₀) hz
      intro a ha b hb
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact hinj _ (P₀.mul_mem hx hzP) _ (P₀.mul_mem hzP hx) (by rw [map_mul, map_mul, h2])
  exact exists_mem_inf_normalizer_inverting hN hEK hEP hPW hP3 hcent hk₀ hnorm hinv

end Glue

section Transfer

variable {G : Type} [Group G]

theorem coe_mem_normalizer_of_subgroupOf {H P : Subgroup G} (hPH : P ≤ H) {k : H}
    (hk : k ∈ Subgroup.normalizer ((P.subgroupOf H : Subgroup H) : Set H)) :
    (k : G) ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h1 := (Subgroup.mem_normalizer_iff.mp hk ⟨g, hPH hg⟩).mp hg
    exact h1
  · intro hg
    have hgH : g ∈ H := by
      have : g = (k : G)⁻¹ * ((k : G) * g * (k : G)⁻¹) * (k : G) := by group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem k.2) (hPH hg)) k.2
    exact (Subgroup.mem_normalizer_iff.mp hk ⟨g, hgH⟩).mpr hg

theorem mem_commutator_image {H P : Subgroup G} (hPH : P ≤ H) {z : G} (hz : z ∈ ⁅P, P⁆) :
    ∃ w : H, w ∈ ⁅P.subgroupOf H, P.subgroupOf H⁆ ∧ (w : G) = z := by
  have hmap : (P.subgroupOf H).map H.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH]
  rw [← hmap, ← Subgroup.map_commutator] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  exact ⟨w, hw, hwz⟩

end Transfer

section T3Subtype

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

local notation "Y₀" => projImage (glPi π 3 (p ^ f) K)

theorem exists_inverting_subtype (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f)
    (hY : (Nat.card ↥(projImage (glPi π 3 (p ^ f) K))).factorization 3 = 3)
    (S : Subgroup ↥(projImage (glPi π 3 (p ^ f) K))) (hS : Nat.card S = 27) :
    ∃ σ ∈ commutator ↥(projImage (glPi π 3 (p ^ f) K)),
      σ ∈ Subgroup.normalizer (S : Set ↥(projImage (glPi π 3 (p ^ f) K))) ∧
      (∀ z ∈ ⁅S, S⁆, σ * z * σ⁻¹ = z⁻¹) ∧ (∀ z ∈ ⁅S, S⁆, ∀ x ∈ S, x * z = z * x) := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  set S' : Subgroup (RonanItem137PGL.PGL3 K) := S.map (Y₀ : Subgroup _).subtype with hS'
  have hS'Y : S' ≤ Y₀ := Subgroup.map_subtype_le S
  have hS'card : Nat.card S' = 27 := by
    rw [hS', Subgroup.card_map_of_injective (Y₀ : Subgroup _).subtype_injective, hS]
  obtain ⟨σ', hσ'sl, hσ'N, hσ'inv, hσ'cent⟩ :=
    RonanItem137PGL.exists_inverting_of_card_twentySeven hK hq hY hS'Y hS'card
  have hσ'Y : σ' ∈ Y₀ := Subgroup.map_mono (Sec4.slPi_le_glPi hπ) hσ'sl
  have hmem : ∀ x : ↥Y₀, x ∈ S ↔ (x : RonanItem137PGL.PGL3 K) ∈ S' := fun x =>
    (Subgroup.mem_map_iff_mem (Y₀ : Subgroup _).subtype_injective).symm
  have hcomm : ∀ z ∈ ⁅S, S⁆, (z : RonanItem137PGL.PGL3 K) ∈ ⁅S', S'⁆ := by
    intro z hz
    have : (Y₀ : Subgroup _).subtype z ∈ ⁅S, S⁆.map (Y₀ : Subgroup _).subtype :=
      Subgroup.mem_map_of_mem _ hz
    rwa [Subgroup.map_commutator] at this
  refine ⟨⟨σ', hσ'Y⟩, ?_, ?_, ?_, ?_⟩
  · rw [CFSG.RankThree.PartTwo.Sec13.commutator_projImage_glPi hK hq2]
    exact Subgroup.mem_subgroupOf.mpr hσ'sl
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem, hmem]
    exact Subgroup.mem_normalizer_iff.mp hσ'N _
  · intro z hz
    apply Subtype.ext
    exact hσ'inv _ (hcomm z hz)
  · intro z hz x hx
    apply Subtype.ext
    exact hσ'cent _ (hcomm z hz) _ ((hmem x).mp hx)

end T3Subtype

section Main

variable {G : Type} [Group G] [Finite G]

theorem two_lt_of_equiv {A L : Subgroup G} {c : G} (h : Sec13Data G A c L) {K : Type} [Field K]
    {p f : ℕ} {π : Bool} (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × ↥(projImage (glPi π 3 (p ^ f) K))) :
    2 < p ^ f := by
  by_contra hle
  have h2 : p ^ f = 2 := by
    have hf : f ≠ 0 := by have := hK.one_le; omega
    have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
    omega
  cases π
  · exact false_of_isSolvable h (isSolvable_projImage_glPi_two hK h2) φ
  · change p ^ f % 3 = 1 at hq
    omega

theorem main_aux {E K P : Subgroup G} {e : G} (hD : Sec13Data G E e K)
    (hPH : P ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G)) (hEP : E ≤ P)
    (hPW : P ≤ K ⊔ E) (hP3 : IsPGroup 3 P) (hP81 : Nat.card P = 81)
    (hW : (Nat.card ↥(K ⊔ E)).factorization 3 = 4) {Kf : Type} [Field Kf] {p f : ℕ} {π : Bool}
    (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f))
    (φ : lBarA e K E ≃* Multiplicative (ZMod 3) × ↥(projImage (glPi π 3 (p ^ f) Kf))) :
    ∃ s ∈ K ⊓ Subgroup.normalizer (P : Set G), ∀ z ∈ ⁅P, P⁆, s * z * s⁻¹ = z⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : K ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) :=
    le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) :=
    hD.A_le_normalizer_zpowers
  haveI : Finite Kf := hKf.finite
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) Kf) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) Kf →* _)
      (QuotientGroup.mk'_surjective _)
  have hq2 : 2 < p ^ f := two_lt_of_equiv hD hKf hq φ
  have hN : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers e : Set G))) :=
    (solvable_prime_complement_core_characterization
      (H := Subgroup.normalizer (Subgroup.zpowers e : Set G)) Nat.prime_three).2.2.1
  have hEK : E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)) ≤
      Subgroup.normalizer ((K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)) :
        Subgroup _) : Set _) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.mp (hD.le_normalizer (Subgroup.mem_subgroupOf.mp hx))
      (y : G)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  have hEP' : E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)) ≤
      P.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)) := Subgroup.comap_mono hEP
  have hPW' : P.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)) ≤
      K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)) ⊔
        E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)) := by
    rw [← Subgroup.subgroupOf_sup hKH hEH]
    exact Subgroup.comap_mono hPW
  have hP3' : IsPGroup 3 (P.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G))) :=
    hP3.comap_subtype
  have hP81' : Nat.card (P.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G))) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv]
    exact hP81
  have hW81' : (Nat.card ↥(K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)) ⊔
      E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)))).factorization 3 = 4 := by
    rw [← Subgroup.subgroupOf_sup hKH hEH,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hKH hEH)).toEquiv]
    exact hW
  have hY : lBarA e K E = (K.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G)) ⊔
      E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers e : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers e : Set G)))) := by
    unfold lBarA
    rw [Subgroup.subgroupOf_sup hKH hEH]
  obtain ⟨k, hk, hkN, hkinv⟩ := exists_mem_inf_normalizer_inverting_of_prod hN hEK hEP' hPW'
    hP3' hP81' hW81' hY φ (map_lBar_eq_commutator hD φ)
    (fun hY₀ S hS => exists_inverting_subtype hKf hq hq2 hY₀ S hS)
  refine ⟨(k : G), ⟨Subgroup.mem_subgroupOf.mp hk, coe_mem_normalizer_of_subgroupOf hPH hkN⟩, ?_⟩
  intro z hz
  obtain ⟨w, hw, hwz⟩ := mem_commutator_image hPH hz
  have := congrArg Subtype.val (hkinv w hw)
  subst hwz
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

theorem exists_mem_inf_normalizer_inverting_of_sylow {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec13Data G A c L) {P E F : Subgroup G} {t : G} (hcfg : Config137 A c L P E F t)
    (hST : HypS E ∨ HypT E) {e : G} {K : Subgroup G}
    (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e)
    (heZ : e ∈ Subgroup.centralizer (P : Set G)) (hPGL : Sec8.IsZ3PGLThreePi (lBarA e K E))
    (hPW : P ≤ K ⊔ E) (hW : (Nat.card ↥(K ⊔ E)).factorization 3 = 4) :
    ∃ s ∈ K ⊓ Subgroup.normalizer (P : Set G), ∀ z ∈ ⁅P, P⁆, s * z * s⁻¹ = z⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXE : E ∈ partTwoE G ∧ E ∉ partTwoT G := by
    rcases hST with hS | hT
    · exact ⟨hS.1, hS.2.1⟩
    · exact ⟨hT.1, hT.2.1⟩
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hXF : E ∈ partTwoF G := hFE ▸ hXE.1
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF
      not_mem_partTwoT := hXE.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  obtain ⟨hPsyl, hAP, -, -, hΔ, -, -, hEA, -, -, -, -, -, -, -, -, -⟩ := hcfg
  have hP3 : IsPGroup 3 P := hPsyl.isPGroup
  have hEΔ : E ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 27} := by
    rw [hΔ]
    exact Or.inr (Or.inr (Or.inl rfl))
  have hAΔ : A ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 27} := by
    rw [hΔ]
    exact Or.inl rfl
  have hEP : E ≤ P := hEΔ.1
  have hE27 : Nat.card E = 27 := hEΔ.2.2
  have hA27 : Nat.card A = 27 := hAΔ.2.2
  have hP81 : Nat.card P = 81 := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP3
    have h1 : 3 ^ 3 ∣ 3 ^ a := by
      rw [← ha, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
      exact Subgroup.card_dvd_of_le hEP
    have h2 : 3 ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
    have h3 : a ≠ 3 := by
      intro ha3
      apply hEA
      have hPE : P = E := by
        refine (Subgroup.eq_of_le_of_card_ge hEP ?_).symm
        rw [ha, ha3, hE27]
        norm_num
      have hAE : A ≤ E := hPE ▸ hAP
      exact (Subgroup.eq_of_le_of_card_ge hAE (by rw [hA27, hE27])).symm
    have h4 : a ≤ 4 := by
      have hdvd : 3 ^ a ∣ Nat.card ↥(K ⊔ E) := ha ▸ Subgroup.card_dvd_of_le hPW
      have hpos : Nat.card ↥(K ⊔ E) ≠ 0 := Nat.card_pos.ne'
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).mp hdvd
      omega
    have : a = 4 := by omega
    rw [ha, this]
    norm_num
  have hPH : P ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    intro x hx
    apply centralizer_le_normalizer_zpowers e
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp heZ x hx
  obtain ⟨π', p, f, Kf, _, hKf, hq, ⟨φ⟩⟩ := hPGL
  exact main_aux hD hPH hEP hPW hP3 hP81 hW hKf hq φ

end Main

@[expose] def Item137PGLSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
        ∀ (P E F : Subgroup G) (t : G), Config137 A c L P E F t → HypS E ∨ HypT E →
          Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
            ∀ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E → K ∈ lA E e →
              e ∈ Subgroup.centralizer (P : Set G) → e ∉ Subgroup.zpowers c →
              Sec8.IsZ3PGLThreePi (lBarA e K E) →
                P ≤ K ⊔ E ∧ (Nat.card ↥(K ⊔ E)).factorization 3 = 4

theorem item137InvertPGL_of_sylow (hS : Item137PGLSylow) : Item137InvertPGL := by
  intro G _ _ A c L h hM P E F t hcfg hST hU e K heΩ hK heZ hec hPGL
  obtain ⟨hPW, hW⟩ := hS G A c L h hM P E F t hcfg hST hU e K heΩ hK heZ hec hPGL
  exact exists_mem_inf_normalizer_inverting_of_sylow h hcfg hST heΩ hK heZ hPGL hPW hW

end CFSG.RankThree.PartTwo.Sec13.RonanItem137
