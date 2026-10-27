module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofWE
import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec14.Item1417

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

namespace Proof152ResW

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem conj_eq_of_mem_normalizer {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    (h3 : A.normalizerMonoidHom ⟨w, hw⟩ ^ 3 = 1) {g : G} (hgA : g ∈ A) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) (hwg : w ∈ Subgroup.normalizer (Subgroup.zpowers g : Set G)) :
    w * g * w⁻¹ = g := by
  have hmem : w * g * w⁻¹ ∈ Subgroup.zpowers g :=
    (Subgroup.mem_normalizer_iff.mp hwg g).mp (Subgroup.mem_zpowers g)
  have hw3 : w ^ 3 * g * (w ^ 3)⁻¹ = g := by
    have h := congrArg (fun σ : MulAut ↥A => ((σ ⟨g, hgA⟩ : ↥A) : G)) h3
    simp only [MulAut.one_apply] at h
    rw [← map_pow] at h
    have he : (⟨w, hw⟩ : ↥(Subgroup.normalizer (A : Set G))) ^ 3 = ⟨w ^ 3, pow_mem hw 3⟩ :=
      Subtype.ext (by simp)
    rw [he] at h
    exact h
  rcases eq_of_mem_zpowers_of_pow_three hg3 hmem with h1 | h1 | h1
  · exfalso
    apply hg1
    have e : g = w⁻¹ * (w * g * w⁻¹) * w := by group
    rw [e, h1]
    group
  · exact h1
  · exfalso
    have hg4 : g ^ 2 * g ^ 2 = g := by
      rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hg3, one_mul]
    have e2 : w * (w * g * w⁻¹) * w⁻¹ = g := by
      rw [h1, ← conj_pow, h1, sq (g ^ 2), hg4]
    have e3 : w ^ 3 * g * (w ^ 3)⁻¹ = g ^ 2 := by
      calc w ^ 3 * g * (w ^ 3)⁻¹ = w * (w * (w * g * w⁻¹) * w⁻¹) * w⁻¹ := by
            rw [pow_three]; group
        _ = g ^ 2 := by rw [e2, h1]
    rw [hw3] at e3
    apply hg1
    have : g * g = g * 1 := by rw [mul_one, ← sq, ← e3]
    exact mul_left_cancel this

omit [Finite G] in
theorem mem_centralizer_of_fix {w a c d : G} (ha : w * a * w⁻¹ = a) (hc : w * c * w⁻¹ = c)
    (hd : w * d * w⁻¹ = d) :
    Subgroup.zpowers a ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers d) ≤
      Subgroup.centralizer ({w} : Set G) := by
  have key : ∀ y : G, w * y * w⁻¹ = y → Subgroup.zpowers y ≤ Subgroup.centralizer ({w} : Set G) :=
    fun y hy => Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (by
      have : w * y = y * w := by
        calc w * y = w * y * w⁻¹ * w := by group
          _ = y * w := by rw [hy]
      exact this.symm))
  exact sup_le (key a ha) (sup_le (key c hc) (key d hd))

omit [Finite G] in
theorem oThreeWStar_le_wStar : oThreeWStar A ≤ wStar A :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem map_conj_inv_mul_eq {F : Subgroup G} {w₁ w₂ : G}
    (h : F.map (MulAut.conj w₂).toMonoidHom = F.map (MulAut.conj w₁).toMonoidHom) :
    F.map (MulAut.conj (w₁⁻¹ * w₂)).toMonoidHom = F := by
  have h' := congrArg (Subgroup.map (MulAut.conj w₁⁻¹).toMonoidHom) h
  rw [Subgroup.map_map, Subgroup.map_map] at h'
  have e1 : (MulAut.conj w₁⁻¹).toMonoidHom.comp (MulAut.conj w₂).toMonoidHom =
      (MulAut.conj (w₁⁻¹ * w₂)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have e2 : (MulAut.conj w₁⁻¹).toMonoidHom.comp (MulAut.conj w₁).toMonoidHom =
      MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [e1, e2, Subgroup.map_id] at h'
  exact h'

theorem card_le_ncard_orbitIn {F : Subgroup G}
    (hfree : ∀ w ∈ oThreeWPre A, F.map (MulAut.conj w).toMonoidHom = F →
      ∀ y ∈ A, w * y * w⁻¹ = y) :
    Nat.card (oThreeWStar A) ≤ (orbitIn (oThreeWPre A) F).ncard := by
  classical
  have hpre : ∀ σ : ↥(oThreeWStar A), ∃ w : G, ∃ hw : w ∈ Subgroup.normalizer (A : Set G),
      A.normalizerMonoidHom ⟨w, hw⟩ = σ := fun σ => by
    obtain ⟨w, hw, -, hσ⟩ := Sec4.mem_autIn_iff.mp (oThreeWStar_le_wStar σ.2)
    exact ⟨w, hw, hσ⟩
  choose pre hpreN hpreσ using hpre
  have hpreP : ∀ σ, pre σ ∈ oThreeWPre A := fun σ =>
    Holds134.mem_oThreeWPre_iff.mpr ⟨hpreN σ, by rw [hpreσ σ]; exact σ.2⟩
  let f : ↥(oThreeWStar A) → ↥(orbitIn (oThreeWPre A) F) := fun σ =>
    ⟨F.map (MulAut.conj (pre σ)).toMonoidHom, pre σ, hpreP σ, rfl⟩
  have hf : Function.Injective f := by
    intro σ τ hστ
    have h1 : F.map (MulAut.conj (pre σ)).toMonoidHom = F.map (MulAut.conj (pre τ)).toMonoidHom :=
      congrArg Subtype.val hστ
    have h2 := map_conj_inv_mul_eq h1
    have hmem : (pre τ)⁻¹ * pre σ ∈ oThreeWPre A := mul_mem (inv_mem (hpreP τ)) (hpreP σ)
    have hcent := hfree _ hmem h2
    have hN : (pre τ)⁻¹ * pre σ ∈ Subgroup.normalizer (A : Set G) :=
      mul_mem (inv_mem (hpreN τ)) (hpreN σ)
    have h3 : A.normalizerMonoidHom ⟨(pre τ)⁻¹ * pre σ, hN⟩ = 1 := by
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [MulAut.one_apply, Sec4.normalizerMonoidHom_apply_coe]
      exact hcent y y.2
    have h4 : (⟨(pre τ)⁻¹ * pre σ, hN⟩ : ↥(Subgroup.normalizer (A : Set G))) =
        (⟨pre τ, hpreN τ⟩)⁻¹ * ⟨pre σ, hpreN σ⟩ := rfl
    rw [h4, map_mul, map_inv, hpreσ, hpreσ, inv_mul_eq_one] at h3
    exact Subtype.ext h3.symm
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_coe_set_eq] at h

omit [Finite G] in
theorem not_mem_orbitIn {X F D : Subgroup G} (hXD : X ≤ Subgroup.normalizer (D : Set G))
    (hFD : F ≠ D) : D ∉ orbitIn X F := by
  rintro ⟨x, hx, hxD⟩
  apply hFD
  have h := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hxD
  have e : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hD : D.map (MulAut.conj x⁻¹).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXD (inv_mem hx))
  rw [Subgroup.map_map, e, Subgroup.map_id] at h
  rw [← h]
  exact hD

omit [Finite G] in
theorem isElemAbelian_sup (hA : Late.IsE27 A) {c' d : G} (hc'A : c' ∈ A) (hdA : d ∈ A) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c' ⊔ Subgroup.zpowers d) := by
  have hBA : Subgroup.zpowers c' ⊔ Subgroup.zpowers d ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hc'A) (Subgroup.zpowers_le.mpr hdA)
  exact ⟨⟨⟨fun u v => Subtype.ext (show (u : G) * v = v * u from congrArg Subtype.val
    (hA.1.1.is_comm.comm ⟨u, hBA u.2⟩ ⟨v, hBA v.2⟩))⟩⟩, fun u hu => hA.1.2 u (hBA hu)⟩

theorem exists_eq_zpowers_mul (hA : Late.IsE27 A) {c' d : G} (hc'A : c' ∈ A) (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hc'd : c' ∉ Subgroup.zpowers d) {F : Subgroup G}
    (hFE : F ≤ Subgroup.zpowers c' ⊔ Subgroup.zpowers d) (hF3 : Nat.card F = 3)
    (hFd : F ≠ Subgroup.zpowers d) : ∃ b ∈ Subgroup.zpowers d, F = Subgroup.zpowers (c' * b) := by
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 :=
    Sec13.card_zpowers_of_pow_three (hA.1.2 d hdA) hd1
  have hFd' : ¬ F ≤ Subgroup.zpowers d := fun h =>
    hFd (Subgroup.eq_of_le_of_card_ge h (by rw [hd3, hF3]))
  exact (Sec13.mem_pointsOff_iff (isElemAbelian_sup hA hc'A hdA)
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers c')) rfl hc'd).mp ⟨hFE, hF3, hFd'⟩

omit [Finite G] in
theorem not_mem_zpowers_symm (hA : Late.IsE27 A) {c' d : G} (hc'1 : c' ≠ 1)
    (hdA : d ∈ A) (hdc : d ∉ Subgroup.zpowers c') : c' ∉ Subgroup.zpowers d := by
  intro h
  apply hdc
  rcases eq_of_mem_zpowers_of_pow_three (hA.1.2 d hdA) h with h1 | h1 | h1
  · exact absurd h1 hc'1
  · rw [h1]
    exact Subgroup.mem_zpowers d
  · have : d = c' ^ 2 := by
      rw [h1, ← pow_mul]
      have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
      calc d = d ^ 3 * d := by rw [hd3, one_mul]
        _ = d ^ (2 * 2) := by rw [← pow_succ]
    rw [this]
    exact pow_mem (Subgroup.mem_zpowers c') 2

theorem card_sup_eq_nine (hA : Late.IsE27 A) {c' d : G} (hc'A : c' ∈ A) (hc'1 : c' ≠ 1)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : d ∉ Subgroup.zpowers c') :
    Nat.card (Subgroup.zpowers c' ⊔ Subgroup.zpowers d : Subgroup G) = 9 := by
  have h1 := Proof152WE.card_closure_pair hA hc'A hdA
  rw [Proof152WE.zpowers_inf_eq_bot (Proof152WE.card_zpowers_eq_three hA hdA hd1) hdc,
    Subgroup.card_bot, mul_one, Proof152WE.card_zpowers_eq_three hA hc'A hc'1,
    Proof152WE.card_zpowers_eq_three hA hdA hd1, Set.insert_eq, Subgroup.closure_union,
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure] at h1
  exact h1

theorem eq_sup_of_not_mem (hA : Late.IsE27 A) {c' d a : G} (hc'A : c' ∈ A) (hc'1 : c' ≠ 1)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : d ∉ Subgroup.zpowers c') (haA : a ∈ A)
    (haE : a ∉ Subgroup.zpowers c' ⊔ Subgroup.zpowers d) :
    A = Subgroup.zpowers a ⊔ (Subgroup.zpowers c' ⊔ Subgroup.zpowers d) := by
  set E := Subgroup.zpowers c' ⊔ Subgroup.zpowers d with hE
  set B := Subgroup.zpowers a ⊔ E with hB
  have hE9 : Nat.card E = 9 := card_sup_eq_nine hA hc'A hc'1 hdA hd1 hdc
  have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr hc'A) (Subgroup.zpowers_le.mpr hdA)
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr haA) hEA
  have hEB : E ≤ B := le_sup_right
  have hdvd1 : 9 ∣ Nat.card B := hE9 ▸ Subgroup.card_dvd_of_le hEB
  have hdvd2 : Nat.card B ∣ 27 := hA.2 ▸ Subgroup.card_dvd_of_le hBA
  have hne : Nat.card B ≠ 9 := by
    intro h9
    have hEeq : E = B := Subgroup.eq_of_le_of_card_ge hEB (by rw [hE9, h9])
    exact haE (hEeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have h27 : Nat.card B = 27 := by
    obtain ⟨i, hi, hBi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card B ∣ 3 ^ 3 by simpa using hdvd2)
    rw [hBi] at hdvd1 hne ⊢
    interval_cases i <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hBA (by rw [hA.2, h27])).symm

theorem omegaA_facts_of_case2 (hA : Late.IsE27 A) {c' d : G} (hc'A : c' ∈ A) (hc'1 : c' ≠ 1)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : d ∉ Subgroup.zpowers c')
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hab : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A)) (h9 : Nat.card (oThreeWStar A) = 9)
    (hΩ : (omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c') ∧ (omegaA A).ncard = 3) ∨
      ∃ a ∈ A, a ∉ Subgroup.zpowers d ∧
        omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers c') ∪
          orbitIn (oThreeWPre A) (Subgroup.zpowers a) ∧ (omegaA A).ncard = 6) :
    Subgroup.zpowers d ∉ omegaA A ∧
      ∀ b ∈ Subgroup.zpowers d, Subgroup.zpowers (c' * b) ∈ omegaA A := by
  classical
  set P := oThreeWPre A with hP
  set F := Subgroup.zpowers c' with hF
  set D := Subgroup.zpowers d with hD
  set E := F ⊔ D with hE
  have hc'3 : c' ^ 3 = 1 := hA.1.2 c' hc'A
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hcd : c' ∉ D := not_mem_zpowers_symm hA hc'1 hdA hdc
  have hFD : F ≠ D := fun h => hdc (h ▸ Subgroup.mem_zpowers d)
  have hPN : P ≤ Subgroup.normalizer (A : Set G) := fun w hw =>
    (Holds134.mem_oThreeWPre_iff.mp hw).1
  have hPD : P ≤ Subgroup.normalizer (D : Set G) := hPN.trans hWd
  have hρ : ∀ w (hw : w ∈ P), A.normalizerMonoidHom ⟨w, hPN hw⟩ ∈ oThreeWStar A := fun w hw =>
    (Holds134.mem_oThreeWPre_iff.mp hw).2
  have hfix : ∀ w ∈ P, ∀ g ∈ A, g ^ 3 = 1 → g ≠ 1 →
      w ∈ Subgroup.normalizer (Subgroup.zpowers g : Set G) → w * g * w⁻¹ = g :=
    fun w hw g hgA hg3 hg1 hwg =>
      conj_eq_of_mem_normalizer (hPN hw) (hab.2 _ (hρ w hw)) hgA hg3 hg1 hwg
  have hfixd : ∀ w ∈ P, w * d * w⁻¹ = d := fun w hw => hfix w hw d hdA hd3 hd1 (hPD hw)
  have hcomm : ∀ w₁ ∈ P, ∀ w₂ ∈ P, ∀ y ∈ A,
      w₁ * (w₂ * y * w₂⁻¹) * w₁⁻¹ = w₂ * (w₁ * y * w₁⁻¹) * w₂⁻¹ := by
    intro w₁ h₁ w₂ h₂ y hy
    have hc := congrArg Subtype.val (hab.1.is_comm.comm ⟨_, hρ w₁ h₁⟩ ⟨_, hρ w₂ h₂⟩)
    have hcy := congrArg (fun σ : MulAut ↥A => ((σ ⟨y, hy⟩ : ↥A) : G)) hc
    simpa [Sec4.normalizerMonoidHom_apply_coe] using hcy
  have hfin : (omegaA A).Finite := Set.toFinite _
  have hOF : orbitIn P F ⊆ omegaA A := by
    rcases hΩ with ⟨h, -⟩ | ⟨a, -, -, h, -⟩
    · rw [h]
    · rw [h]
      exact Set.subset_union_left
  have hle6 : (omegaA A).ncard ≤ 6 := by
    rcases hΩ with ⟨-, h⟩ | ⟨a, -, -, -, h⟩ <;> omega
  have hmapF : ∀ w, F.map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (w * c' * w⁻¹) :=
    fun w => by rw [hF, MonoidHom.map_zpowers]; rfl
  have hcardF : ∀ w, Nat.card (F.map (MulAut.conj w).toMonoidHom) = 3 := fun w => by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective, hF]
    exact Sec13.card_zpowers_of_pow_three hc'3 hc'1
  have hnorm : ∀ w : G, F.map (MulAut.conj w).toMonoidHom = F →
      w ∈ Subgroup.normalizer (F : Set G) := fun w h =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  obtain ⟨h, hhP, hhF, hhA⟩ : ∃ h ∈ P, F.map (MulAut.conj h).toMonoidHom = F ∧
      ¬ ∀ y ∈ A, h * y * h⁻¹ = y := by
    by_contra hno
    push Not at hno
    have h1 : Nat.card (oThreeWStar A) ≤ (orbitIn P F).ncard :=
      card_le_ncard_orbitIn (A := A) (F := F) fun w hw hwF => hno w hw hwF
    have h2 := Set.ncard_le_ncard hOF hfin
    rw [h9] at h1
    omega
  have hhc : h * c' * h⁻¹ = c' := hfix h hhP c' hc'A hc'3 hc'1 (hnorm h hhF)
  have hhd : h * d * h⁻¹ = d := hfixd h hhP
  have hmemE : ∀ w ∈ P, w * c' * w⁻¹ ∈ E := by
    intro w hw
    by_contra hnot
    apply hhA
    have hwc : w * c' * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hPN hw) c').mp hc'A
    have hAeq := eq_sup_of_not_mem hA hc'A hc'1 hdA hd1 hdc hwc hnot
    have hhw : h * (w * c' * w⁻¹) * h⁻¹ = w * c' * w⁻¹ := by
      rw [hcomm h hhP w hw c' hc'A, hhc]
    intro y hy
    rw [hAeq] at hy
    have hyc := mem_centralizer_of_fix hhw hhc hhd hy
    have : h * y = y * h := (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
    rw [this, mul_inv_cancel_right]
  have hpt : ∀ w ∈ P, ∃ b ∈ D, F.map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (c' * b) := by
    intro w hw
    refine exists_eq_zpowers_mul hA hc'A hdA hd1 hcd ?_ (hcardF w) ?_
    · rw [hmapF]
      exact Subgroup.zpowers_le.mpr (hmemE w hw)
    · intro h'
      exact not_mem_orbitIn hPD hFD ⟨w, hw, h'.symm⟩
  obtain ⟨x, hxP, hxF⟩ : ∃ x ∈ P, F.map (MulAut.conj x).toMonoidHom ≠ F := by
    by_contra hno
    push Not at hno
    have horb : orbitIn P F = {F} := by
      ext F'
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hno w hw
      · intro hF'
        rw [Set.mem_singleton_iff] at hF'
        refine ⟨1, one_mem _, ?_⟩
        rw [hF']
        have e : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
          ext y
          simp
        rw [e, Subgroup.map_id]
    rcases hΩ with ⟨hΩe, h3⟩ | ⟨a, haA, had, hΩe, h6⟩
    · rw [hΩe, horb, Set.ncard_singleton] at h3
      omega
    · have hfixc : ∀ w ∈ P, w * c' * w⁻¹ = c' := fun w hw =>
        hfix w hw c' hc'A hc'3 hc'1 (hnorm w (hno w hw))
      have ha1 : a ≠ 1 := fun h1 => had (h1 ▸ one_mem _)
      have ha3 : a ^ 3 = 1 := hA.1.2 a haA
      by_cases haE : a ∈ E
      ·
        have hEc : ∀ w ∈ P, E ≤ Subgroup.centralizer ({w} : Set G) := fun w hw =>
          le_sup_right.trans (mem_centralizer_of_fix (a := 1) (by group) (hfixc w hw)
            (hfixd w hw))
        have horba : orbitIn P (Subgroup.zpowers a) ⊆ {Subgroup.zpowers a} := by
          rintro _ ⟨w, hw, rfl⟩
          rw [Set.mem_singleton_iff, MonoidHom.map_zpowers]
          congr 1
          have : w * a = a * w := (Subgroup.mem_centralizer_singleton_iff.mp
            (hEc w hw haE)).symm
          change w * a * w⁻¹ = a
          rw [this, mul_inv_cancel_right]
        have hsub : omegaA A ⊆ {F, Subgroup.zpowers a} := by
          rw [hΩe, horb]
          exact Set.union_subset (fun _ h => Or.inl h) (horba.trans fun _ h => Or.inr h)
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        have h2 := Set.ncard_insert_le F {Subgroup.zpowers a}
        rw [Set.ncard_singleton] at h2
        omega
      ·
        have hAeq := eq_sup_of_not_mem hA hc'A hc'1 hdA hd1 hdc haA haE
        have h1 : Nat.card (oThreeWStar A) ≤ (orbitIn P (Subgroup.zpowers a)).ncard :=
          card_le_ncard_orbitIn (A := A) (F := Subgroup.zpowers a) fun w hw hwa y hy => by
            have hwa' : w * a * w⁻¹ = a := hfix w hw a haA ha3 ha1
              (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hwa)
            rw [hAeq] at hy
            have hyc := mem_centralizer_of_fix hwa' (hfixc w hw) (hfixd w hw) hy
            have : w * y = y * w := (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
            rw [this, mul_inv_cancel_right]
        have h2 : orbitIn P (Subgroup.zpowers a) ⊆ omegaA A := by
          rw [hΩe]
          exact Set.subset_union_right
        have h3 := Set.ncard_le_ncard h2 hfin
        rw [h9] at h1
        omega
  have hx3 : x ^ 3 ∈ Subgroup.normalizer (F : Set G) := by
    have hcent : x ^ 3 * c' * (x ^ 3)⁻¹ = c' := by
      have h' := congrArg (fun σ : MulAut ↥A => ((σ ⟨c', hc'A⟩ : ↥A) : G))
        (hab.2 _ (hρ x hxP))
      simp only [MulAut.one_apply] at h'
      rw [← map_pow, show (⟨x, hPN hxP⟩ : ↥(Subgroup.normalizer (A : Set G))) ^ 3 =
        ⟨x ^ 3, pow_mem (hPN hxP) 3⟩ from Subtype.ext (by simp)] at h'
      exact h'
    refine centralizer_singleton_le_normalizer_zpowers c' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x ^ 3 * c' = x ^ 3 * c' * (x ^ 3)⁻¹ * x ^ 3 := by group
      _ = c' * x ^ 3 := by rw [hcent]
  have hx2F : F.map (MulAut.conj (x * x)).toMonoidHom ≠ F := by
    intro h'
    apply hxF
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    have h2 := mul_mem (inv_mem (hnorm _ h')) hx3
    have e : (x * x)⁻¹ * x ^ 3 = x := by group
    rwa [e] at h2
  have hx12 : F.map (MulAut.conj (x * x)).toMonoidHom ≠ F.map (MulAut.conj x).toMonoidHom := by
    intro h'
    apply hxF
    have h'' := map_conj_inv_mul_eq h'
    have e : x⁻¹ * (x * x) = x := by group
    rwa [e] at h''
  obtain ⟨b₁, hb₁D, hb₁⟩ := hpt x hxP
  obtain ⟨b₂, hb₂D, hb₂⟩ := hpt (x * x) (mul_mem hxP hxP)
  have hFΩ : ∀ w ∈ P, F.map (MulAut.conj w).toMonoidHom ∈ omegaA A := fun w hw =>
    hOF ⟨w, hw, rfl⟩
  refine ⟨?_, fun b hb => ?_⟩
  · rcases hΩ with ⟨hΩe, -⟩ | ⟨a, -, had, hΩe, -⟩
    · rw [hΩe]
      exact not_mem_orbitIn hPD hFD
    · rw [hΩe]
      rintro (h' | h')
      · exact not_mem_orbitIn hPD hFD h'
      · exact not_mem_orbitIn hPD (fun h'' => had (h'' ▸ Subgroup.mem_zpowers a)) h'
  · have hb₁1 : b₁ ≠ 1 := by
      rintro rfl
      apply hxF
      rw [hb₁, mul_one]
    have hb₂1 : b₂ ≠ 1 := by
      rintro rfl
      apply hx2F
      rw [hb₂, mul_one]
    have hb₁₂ : b₁ ≠ b₂ := by
      rintro rfl
      apply hx12
      rw [hb₁, hb₂]
    have hF1 : F ∈ omegaA A := by
      have h' := hFΩ 1 (one_mem _)
      have e : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext y
        simp
      rwa [e, Subgroup.map_id] at h'
    have hΩ1 : Subgroup.zpowers (c' * b₁) ∈ omegaA A := hb₁ ▸ hFΩ x hxP
    have hΩ2 : Subgroup.zpowers (c' * b₂) ∈ omegaA A := hb₂ ▸ hFΩ _ (mul_mem hxP hxP)
    rcases eq_of_mem_zpowers_of_pow_three hd3 hb with rfl | rfl | rfl
    · rw [mul_one]
      exact hF1
    · rcases eq_of_mem_zpowers_of_pow_three hd3 hb₁D with h1 | h1 | h1
      · exact absurd h1 hb₁1
      · rwa [← h1]
      · rcases eq_of_mem_zpowers_of_pow_three hd3 hb₂D with h2 | h2 | h2
        · exact absurd h2 hb₂1
        · rwa [← h2]
        · exact absurd (h1.trans h2.symm) hb₁₂
    · rcases eq_of_mem_zpowers_of_pow_three hd3 hb₁D with h1 | h1 | h1
      · exact absurd h1 hb₁1
      · rcases eq_of_mem_zpowers_of_pow_three hd3 hb₂D with h2 | h2 | h2
        · exact absurd h2 hb₂1
        · exact absurd (h1.trans h2.symm) hb₁₂
        · rwa [← h2]
      · rwa [← h1]

theorem omegaA_facts_of_case3 (hA : Late.IsE27 A) {c' d : G} (hc'A : c' ∈ A) (hc'1 : c' ≠ 1)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : d ∉ Subgroup.zpowers c')
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hΩ : omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c'))
    (h12 : (omegaA A).ncard = 12) :
    Subgroup.zpowers d ∉ omegaA A ∧
      ∀ b ∈ Subgroup.zpowers d, Subgroup.zpowers (c' * b) ∈ omegaA A := by
  classical
  set F := Subgroup.zpowers c' with hF
  set D := Subgroup.zpowers d with hD
  set E := F ⊔ D with hE
  have hcd : c' ∉ D := not_mem_zpowers_symm hA hc'1 hdA hdc
  have hFD : F ≠ D := fun h => hdc (h ▸ Subgroup.mem_zpowers d)
  have hDΩ : D ∉ omegaA A := by
    rw [hΩ]
    exact not_mem_orbitIn hWd hFD
  refine ⟨hDΩ, fun b₀ hb₀ => ?_⟩
  by_contra hno
  have hE9 : Nat.card E = 9 := card_sup_eq_nine hA hc'A hc'1 hdA hd1 hdc
  have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr hc'A) (Subgroup.zpowers_le.mpr hdA)
  obtain ⟨a, haA, haE⟩ : ∃ a ∈ A, a ∉ E := by
    by_contra h'
    push Not at h'
    have h1 := Subgroup.card_le_of_le (show A ≤ E from h')
    rw [hA.2, hE9] at h1
    omega
  have hAa := eq_sup_of_not_mem hA hc'A hc'1 hdA hd1 hdc haA haE
  have hpA : (Sec13.pointsOff A E).ncard = 9 := Sec13.ncard_pointsOff hA.1 haA hAa haE hE9
  have hpE : (Sec13.pointsOff E D).ncard = 3 :=
    Holds134.ncard_pointsOff_zpowers hA.1 hdA hd1 hc'A hcd
  have hmemE : Subgroup.zpowers (c' * b₀) ∈ Sec13.pointsOff E D :=
    (Sec13.mem_pointsOff_iff (isElemAbelian_sup hA hc'A hdA)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c')) rfl hcd).mpr ⟨b₀, hb₀, rfl⟩
  have hd3 : Nat.card D = 3 := Sec13.card_zpowers_of_pow_three (hA.1.2 d hdA) hd1
  have hsub : omegaA A ⊆
      Sec13.pointsOff A E ∪ (Sec13.pointsOff E D \ {Subgroup.zpowers (c' * b₀)}) := by
    intro F' hF'
    obtain ⟨hF'A, hF'3, -⟩ := mem_omegaA_iff.mp hF'
    by_cases hF'E : F' ≤ E
    · right
      refine ⟨⟨hF'E, hF'3, fun hle => ?_⟩, fun h' => hno (h' ▸ hF')⟩
      have hF'D : F' = D := Subgroup.eq_of_le_of_card_ge hle (by rw [hF'3, hd3])
      exact hDΩ (hF'D ▸ hF')
    · left
      exact ⟨hF'A, hF'3, hF'E⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (Sec13.pointsOff A E)
    (Sec13.pointsOff E D \ {Subgroup.zpowers (c' * b₀)})
  have h3 := Set.ncard_sdiff_singleton_of_mem hmemE
  rw [hpE] at h3
  omega

theorem not_mem_zpowers_of_dData (h415 : Sec4.Item4_15) {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Y M X : Subgroup G} {c' : G} {L' : Subgroup G} {d : G}
    (hpt : Pt152 A (lB A) Y M X c' L') (hd : DData152 A X c' L' d) :
    d ∉ Subgroup.zpowers c' := by
  have hA := h.isE27
  obtain ⟨-, hc3, -⟩ := zpowers_mem_omegaA_iff.mp hpt.omega
  have h' : Sec14Std G A c' L' :=
    { h with zpowers_mem_omegaA := hpt.omega, mem_lA := hpt.mem_lA }
  have hcL : c' ∉ L' :=
    not_mem_of_center_eq_bot h'.toSec13Data (KFacts.KS14.center_eq_bot_of_j2 h415 hpt.hj)
  intro hdc
  have hzeq : Subgroup.zpowers d = Subgroup.zpowers c' :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc)
      (by rw [hc3, Proof152WE.card_zpowers_eq_three hA hd.mem_d hd.ne_d])
  have hcd : c' ∈ Subgroup.zpowers d := hzeq ▸ Subgroup.mem_zpowers c'
  exact hcL (Subgroup.zpowers_le.mpr hd.central_d.1 hcd)

theorem omegaA_eq_or_facts (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    {c : G} {L : Subgroup G} (h : Sec14Std G A c L) {Y M X : Subgroup G} {c' : G}
    {L' : Subgroup G} {d : G} (hpt : Pt152 A (lB A) Y M X c' L') (hd : DData152 A X c' L' d) :
    omegaA A = {Subgroup.zpowers c'} ∨
      (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
        Subgroup.zpowers d ∉ omegaA A ∧
        ∀ b ∈ Subgroup.zpowers d, Subgroup.zpowers (c' * b) ∈ omegaA A) := by
  have hA := h.isE27
  obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp hpt.omega
  have hc1 : c' ≠ 1 := by
    intro hc1
    rw [hc1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  have h' : Sec14Std G A c' L' :=
    { h with zpowers_mem_omegaA := hpt.omega, mem_lA := hpt.mem_lA }
  have hdc := not_mem_zpowers_of_dData h415 h hpt hd
  obtain ⟨hdL, S3, hdS, hSd⟩ := hd.central_d
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥L')
      Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hpt.hj hdL hd.ne_d S3 hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd.ne_d)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hpt.hj hdL hd.ne_d
    ⟨S3, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA hd.mem_d hc1 hpt.mem_lA.1 hJq
  rcases h134 G A c' L' h'.toSec13Data hpt.hj d hd.mem_d hd.ne_d ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, hWd, hab, h9, -, hΩ⟩ | ⟨-, hWd, hΩ, h12⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hWd, omegaA_facts_of_case2 hA hcA hc1 hd.mem_d hd.ne_d hdc hWd hab h9 ?_⟩
    rcases hΩ with h3 | ⟨I, -, -, -, a, haAK, had, hΩe, h6, -⟩
    · exact Or.inl h3
    · exact Or.inr ⟨a, haAK.1, had, hΩe, h6⟩
  · exact Or.inr ⟨hWd, omegaA_facts_of_case3 hA hcA hc1 hd.mem_d hd.ne_d hdc hWd hΩ h12⟩

end Proof152ResW

open Proof152ResW

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152ConfWd (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (d : G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → DData152 A X c' L' d → PData152 A X p P →
    TData152 A LB X P T → KData152 A LB P T K S →
    P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
    ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal →
    ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G) →
    generalizedFitting ↥(P ⊔ S) = CFSG.pCore 2 ↥(P ⊔ S) →
    P ⊓ Subgroup.centralizer ({c'} : Set G) ≤ (frattini ↥P).map P.subtype →
    omegaA A ≠ {Subgroup.zpowers c'} →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
    Subgroup.zpowers d ∉ omegaA A →
    (∀ b ∈ Subgroup.zpowers d, Subgroup.zpowers (c' * b) ∈ omegaA A) →
    P ≤ Subgroup.centralizer ({d} : Set G) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c' : Set G)

@[expose] noncomputable def Step152ConfWdR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfWd A (lB A)

theorem step152ConfW_of_Wd
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h142 : Item142AllS14)
    (h135 : Item135) (hmult : KFacts.KS18Mult) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (hWd : Step152ConfWd A (lB A)) : Step152ConfW A (lB A) := by
  intro Y M X c' L' d p P T K S hpt hd hP hT hK hθ hn hps hfs hfr
  by_cases hΩ : omegaA A = {Subgroup.zpowers c'}
  · exact normalizer_le_of_omegaA_eq hΩ
  obtain ⟨hWdd, hDΩ, hpts⟩ := (omegaA_eq_or_facts h134 h48 h415 h hpt hd).resolve_left hΩ
  have hA := h.isE27
  have hp3 := ne_three_of_le_theta hP hθ
  obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp hpt.omega
  have hc1 : c' ≠ 1 := by
    intro hc1
    rw [hc1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  have hdc := not_mem_zpowers_of_dData h415 h hpt hd
  have hcd := not_mem_zpowers_symm hA hc1 hd.mem_d hdc
  obtain ⟨e, he, hec, hPe⟩ := exists_le_centralizer h415 h hpt hd hP hp3 hfr
  have heΩ : Subgroup.zpowers e ∉ omegaA A := fun heΩ =>
    not_le_centralizer_of_mem_omegaA h134 h48 h415 h142 h135 hmult h hpt hd hP hp3 hfr he heΩ hPe
  have hcl : Subgroup.closure ({c', d} : Set G) = Subgroup.zpowers c' ⊔ Subgroup.zpowers d := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hEA : Subgroup.closure ({c', d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hcA
    · exact hd.mem_d
  have he1 : e ≠ 1 := fun h1 => hec (h1 ▸ one_mem _)
  have hed : Subgroup.zpowers e = Subgroup.zpowers d := by
    by_contra hne
    obtain ⟨b, hb, hbe⟩ := exists_eq_zpowers_mul hA hcA hd.mem_d hd.ne_d hcd
      (F := Subgroup.zpowers e) (hcl ▸ Subgroup.zpowers_le.mpr he)
      (Proof152WE.card_zpowers_eq_three hA (hEA he) he1) hne
    exact heΩ (hbe ▸ hpts b hb)
  have hPd : P ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [← centralizer_singleton_eq_of_zpowers_eq hed]
    exact hPe
  exact hWd Y M X c' L' d p P T K S hpt hd hP hT hK hθ hn hps hfs hfr hΩ hWdd hDΩ hpts hPd

theorem step152ConfWR_of_Wd
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h142 : Item142AllS14)
    (h135 : Item135) (hmult : KFacts.KS18Mult) (hWd : Step152ConfWdR) : Step152ConfWR :=
  fun G _ _ A c L hR => step152ConfW_of_Wd h134 h48 h415 h142 h135 hmult hR.toSec14Std
    (hWd G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
