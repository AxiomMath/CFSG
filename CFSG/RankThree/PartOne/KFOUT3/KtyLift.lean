module

public import CFSG.RankThree.PartOne.KF.CentralQuot
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne.KFU
open scoped commutatorElement

section Commutator

variable {Λ : Type*} [Group Λ]

theorem conj_mem_commutator {H : Subgroup Λ} {y : Λ} (hy : ∀ b ∈ H, y * b * y⁻¹ ∈ H) {x : Λ}
    (hx : x ∈ ⁅H, H⁆) : y * x * y⁻¹ ∈ ⁅H, H⁆ := by
  have h : ⁅H, H⁆ ≤ (⁅H, H⁆).comap (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (by simpa [MulAut.conj_apply] using hy a ha)
      (by simpa [MulAut.conj_apply] using hy b hb)
  simpa [MulAut.conj_apply] using h hx

theorem commutator_self_le (H : Subgroup Λ) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

end Commutator

section Lift

variable {Λ Q : Type*} [Group Λ] [Group Q] {p : ℕ} {ε : Λ →* Q}

theorem exists_pow_lift (hε : IsCentralPQuot p ε) {P : Subgroup Λ} {σ : Q} (hσ : σ ∈ P.map ε)
    (hσp : σ ^ p = 1) : ∃ z ∈ P, ε z = σ ∧ z ^ p = 1 := by
  obtain ⟨x, hxP, rfl⟩ := hσ
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hε.coprime 1 0
  refine ⟨x ^ c, P.pow_mem hxP c, ?_, ?_⟩
  · rw [map_pow, pow_eq_pow_mod c hσp, hc1]
    exact (pow_eq_pow_mod 1 hσp).symm.trans (pow_one _)
  · have hmem : x ^ p ∈ ε.ker := by
      rw [MonoidHom.mem_ker, map_pow, hσp]
    have hk : (x ^ p) ^ Nat.card ε.ker = 1 := by
      have := pow_card_eq_one' (G := ε.ker) (x := ⟨x ^ p, hmem⟩)
      simpa using congrArg Subtype.val this
    have hkc : Nat.card ε.ker ∣ c := (Nat.modEq_zero_iff_dvd).mp hc2
    obtain ⟨t, ht⟩ := hkc
    calc (x ^ c) ^ p = (x ^ p) ^ c := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((x ^ p) ^ Nat.card ε.ker) ^ t := by rw [ht, pow_mul]
      _ = 1 := by rw [hk, one_pow]

theorem commutator_mul_central {a b z w : Λ} (hz : z ∈ Subgroup.center Λ)
    (hw : w ∈ Subgroup.center Λ) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' : ∀ x, z * x = x * z := fun x => (Subgroup.mem_center_iff.mp hz x).symm
  have hw' : ∀ x, w * x = x * w := fun x => (Subgroup.mem_center_iff.mp hw x).symm
  have e1 : z * (b * w) * z⁻¹ = b * w := by rw [hz' (b * w), mul_assoc, mul_inv_cancel, mul_one]
  have e2 : w * a⁻¹ * w⁻¹ = a⁻¹ := by rw [hw' a⁻¹, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]
        group
    _ = a * (b * w) * a⁻¹ * (b * w)⁻¹ := by rw [e1]
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = ⁅a, b⁆ := by rw [e2, commutatorElement_def]

theorem center_eq_bot_of_simple_perfect {S : Subgroup Q} (hSperf : Group.IsPerfect S)
    (hSsimple : IsSimpleGroup S) : ∀ z ∈ Subgroup.center ↥S, z = 1 := by
  have : Nontrivial S := hSsimple.toNontrivial
  have hSncomm : ¬ IsMulCommutative S := by
    have := hSperf
    exact Group.IsPerfect.not_isMulCommutative S
  intro z hz
  rcases (Subgroup.center ↥S).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · rw [h] at hz
    exact Subgroup.mem_bot.mp hz
  · exact absurd (Subgroup.center_eq_top_iff.mp h) hSncomm

theorem exists_perfect_lift_core (hε : IsCentralPQuot p ε) {Y : Subgroup Λ} {S : Subgroup Q}
    (hSY : ∀ σ ∈ S, ∃ y ∈ Y, ε y = σ) (hSperf : Group.IsPerfect S) :
    ∃ P : Subgroup Λ, P ≤ Y ∧ P.map ε = S ∧ ⁅P, P⁆ = P ∧
      ∀ y ∈ Y, (∀ σ ∈ S, ε y * σ * (ε y)⁻¹ ∈ S) → ∀ b ∈ P, y * b * y⁻¹ ∈ P := by
  classical
  let P₀ : Subgroup Λ := Y ⊓ S.comap ε
  have hP₀S : P₀.map ε = S := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_inf.mp hx).2
    · intro σ hσ
      obtain ⟨y, hy, rfl⟩ := hSY σ hσ
      exact ⟨y, Subgroup.mem_inf.mpr ⟨hy, hσ⟩, rfl⟩
  have hP₀norm : ∀ y ∈ Y, (∀ σ ∈ S, ε y * σ * (ε y)⁻¹ ∈ S) → ∀ b ∈ P₀, y * b * y⁻¹ ∈ P₀ := by
    intro y hy hyS b hb
    obtain ⟨hbY, hbS⟩ := Subgroup.mem_inf.mp hb
    refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem hy hbY) (Y.inv_mem hy), ?_⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hyS _ hbS
  let P₁ : Subgroup Λ := ⁅P₀, P₀⁆
  let P : Subgroup Λ := ⁅P₁, P₁⁆
  have hSS : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp hSperf
  have hP₁S : P₁.map ε = S := by
    show (⁅P₀, P₀⁆).map ε = S
    rw [Subgroup.map_commutator, hP₀S, hSS]
  have hPS : P.map ε = S := by
    show (⁅P₁, P₁⁆).map ε = S
    rw [Subgroup.map_commutator, hP₁S, hSS]
  have hP₁le : P₁ ≤ P₀ := commutator_self_le P₀
  have hPle : P ≤ P₁ := commutator_self_le P₁
  have hPY : P ≤ Y := fun x hx => (Subgroup.mem_inf.mp (hP₁le (hPle hx))).1
  have hPperf : ⁅P, P⁆ = P := by
    refine le_antisymm (commutator_self_le P) ?_
    show ⁅P₁, P₁⁆ ≤ ⁅P, P⁆
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haS : ε a ∈ P.map ε := by rw [hPS, ← hP₁S]; exact Subgroup.mem_map_of_mem ε ha
    have hbS : ε b ∈ P.map ε := by rw [hPS, ← hP₁S]; exact Subgroup.mem_map_of_mem ε hb
    obtain ⟨a', ha'P, ha'⟩ := haS
    obtain ⟨b', hb'P, hb'⟩ := hbS
    have hza : a'⁻¹ * a ∈ ε.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ha', inv_mul_cancel]
    have hzb : b'⁻¹ * b ∈ ε.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hb', inv_mul_cancel]
    have hcomm : ⁅a, b⁆ = ⁅a', b'⁆ := by
      have hA : a = a' * (a'⁻¹ * a) := by group
      have hB : b = b' * (b'⁻¹ * b) := by group
      calc ⁅a, b⁆ = ⁅a' * (a'⁻¹ * a), b' * (b'⁻¹ * b)⁆ := by rw [← hA, ← hB]
        _ = ⁅a', b'⁆ := commutator_mul_central (hε.central hza) (hε.central hzb)
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator ha'P hb'P
  refine ⟨P, hPY, hPS, hPperf, fun y hy hyS b hb => ?_⟩
  exact conj_mem_commutator (fun b' hb' => conj_mem_commutator
    (fun b'' hb'' => hP₀norm y hy hyS b'' hb'') hb') hb

theorem exists_perfect_lift (hε : IsCentralPQuot p ε) {Y : Subgroup Λ} {S : Subgroup Q}
    (hSY : ∀ σ ∈ S, ∃ y ∈ Y, ε y = σ) (hSnorm : ∀ y ∈ Y, ∀ σ ∈ S, ε y * σ * (ε y)⁻¹ ∈ S)
    (hSperf : Group.IsPerfect S) (hSsimple : IsSimpleGroup S) :
    ∃ P : Subgroup Λ, P ≤ Y ∧ (∀ y ∈ Y, ∀ b ∈ P, y * b * y⁻¹ ∈ P) ∧ P.map ε = S ∧
      IsQuasisimple P := by
  classical
  obtain ⟨P, hPY, hPS, hPperf, hPnorm'⟩ := exists_perfect_lift_core hε hSY hSperf
  have hPnorm : ∀ y ∈ Y, ∀ b ∈ P, y * b * y⁻¹ ∈ P := fun y hy b hb =>
    hPnorm' y hy (hSnorm y hy) b hb
  have : Nontrivial S := hSsimple.toNontrivial
  have hSncomm : ¬ IsMulCommutative S := by
    have := hSperf
    exact Group.IsPerfect.not_isMulCommutative S
  have hSZ : ∀ z ∈ Subgroup.center ↥S, z = 1 := center_eq_bot_of_simple_perfect hSperf hSsimple
  have hPmem : ∀ x : P, ε (x : Λ) ∈ S := fun x => by
    rw [← hPS]
    exact Subgroup.mem_map_of_mem ε x.2
  let εP : ↥P →* ↥S := (ε.comp P.subtype).codRestrict S hPmem
  have hεP_surj : Function.Surjective εP := by
    intro σ
    have : (σ : Q) ∈ P.map ε := by
      rw [hPS]
      exact σ.2
    obtain ⟨x, hx, hxσ⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxσ⟩
  have hkerc : εP.ker = Subgroup.center ↥P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx g
      have hx1 : (x : Λ) ∈ ε.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hx
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hε.central hx1) g)
    · intro hx
      apply hSZ
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := hεP_surj w
      rw [← map_mul, ← map_mul, hx y]
  let e : ↥P ⧸ Subgroup.center ↥P ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective εP hεP_surj)
  refine ⟨P, hPY, hPnorm, hPS, Subgroup.isPerfect_iff.mpr hPperf, e.isSimpleGroup, ?_⟩
  by_contra hcon
  apply hSncomm
  refine ⟨⟨fun a b => ?_⟩⟩
  by_contra hne
  apply hcon
  refine ⟨e.symm a, e.symm b, fun h2 => hne ?_⟩
  have h3 := congrArg e h2
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3

theorem card_dvd_of_equiv [Finite Λ] (hε : IsCentralPQuot p ε) {N N' : Subgroup Λ} (e : N ≃* N')
    (hN : ∀ z ∈ Subgroup.center ↥(N.map ε), z = 1) :
    Nat.card (N.map ε) ∣ Nat.card (N'.map ε) := by
  have hrange : ∀ M : Subgroup Λ, (ε.comp M.subtype).range = M.map ε := by
    intro M
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_map]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, m.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have h1 := Subgroup.card_ker_mul_card_range (ε.comp N.subtype)
  have h2 := Subgroup.card_ker_mul_card_range (ε.comp N'.subtype)
  rw [hrange] at h1 h2
  have hZ : Subgroup.center ↥N ≤ (ε.comp N.subtype).ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : (⟨ε (z : Λ), Subgroup.mem_map_of_mem ε z.2⟩ : ↥(N.map ε)) ∈
        Subgroup.center ↥(N.map ε) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨m, hm, hmw⟩ := w.2
      apply Subtype.ext
      show (w : Q) * ε (z : Λ) = ε (z : Λ) * (w : Q)
      rw [← hmw, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨m, hm⟩)
    exact congrArg Subtype.val (hN _ hzc)
  have hK : (ε.comp N.subtype).ker ≤ Subgroup.center ↥N := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hx1 : (x : Λ) ∈ ε.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hε.central hx1) g)
  have hK' : (ε.comp N'.subtype).ker ≤ Subgroup.center ↥N' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hx1 : (x : Λ) ∈ ε.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hε.central hx1) g)
  have hker : Nat.card (ε.comp N.subtype).ker = Nat.card ↥(Subgroup.center ↥N) :=
    le_antisymm (Subgroup.card_le_of_le hK) (Subgroup.card_le_of_le hZ)
  have hNN : Nat.card N = Nat.card N' := Nat.card_congr e.toEquiv
  have hZZ : Nat.card ↥(Subgroup.center ↥N') = Nat.card ↥(Subgroup.center ↥N) := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.card_map_of_injective e.injective
  have hdvd : Nat.card (ε.comp N'.subtype).ker ∣ Nat.card ↥(Subgroup.center ↥N) := by
    rw [← hZZ]
    exact Subgroup.card_dvd_of_le hK'
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card (ε.comp N'.subtype).ker := Nat.card_pos
  have key : Nat.card (ε.comp N'.subtype).ker * (m * Nat.card (N.map ε)) =
      Nat.card (ε.comp N'.subtype).ker * Nat.card (N'.map ε) := by
    calc Nat.card (ε.comp N'.subtype).ker * (m * Nat.card (N.map ε))
        = (Nat.card (ε.comp N'.subtype).ker * m) * Nat.card (N.map ε) := by ring
      _ = Nat.card ↥(Subgroup.center ↥N) * Nat.card (N.map ε) := by rw [← hm]
      _ = Nat.card (ε.comp N.subtype).ker * Nat.card (N.map ε) := by rw [hker]
      _ = Nat.card N := h1
      _ = Nat.card N' := hNN
      _ = Nat.card (ε.comp N'.subtype).ker * Nat.card (N'.map ε) := h2.symm
  have := Nat.eq_of_mul_eq_mul_left hpos key
  exact ⟨m, by rw [← this]; ring⟩

end Lift

end CFSG.RankThree.PartOne.KFOUT3
