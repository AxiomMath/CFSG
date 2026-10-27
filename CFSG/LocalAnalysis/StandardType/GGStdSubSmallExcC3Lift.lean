module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthDefs
public import CFSG.Quasithin.Vol2.Ch11L2Q5cMult

public section

namespace CFSG.StandardType.SmallExc

open scoped MatrixGroups commutatorElement
open CFSG.Assembly

section Lift

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R} {F : Type} [Field F] [Finite F]
  [CharP F 2] {n : ℕ} {ρ : SL(2, F) →* R}

theorem commutator_range_slTwo (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ⁅ρ.range, ρ.range⁆ = ρ.range := by
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hP := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    hP.commutator_eq_top]

variable [Finite L']

theorem exists_two_pow_eq_one_of_slTwo (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hρ : Function.Injective ρ) {z : L'} (hz : z ∈ ⁅ρ.range.comap ψ, ρ.range.comap ψ⁆)
    (hz1 : ψ z = 1) : ∃ k : ℕ, z ^ 2 ^ k = 1 := by
  set Q := ⁅ρ.range.comap ψ, ρ.range.comap ψ⁆ with hQ
  have hYp := commutator_range_slTwo (ρ := ρ) hn hF
  have hQp : ⁅Q, Q⁆ = Q := CFSG.RankThree.PartOne.S15K.commutator_comap_perfect hψ hker hYp
  have hQmap : Q.map ψ = ρ.range := CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hYp
  let e : SL(2, F) ≃* ρ.range := MonoidHom.ofInjective hρ
  let f : Q →* ρ.range := (ψ.comp Q.subtype).codRestrict ρ.range fun q => by
    rw [← hQmap]
    exact Subgroup.mem_map_of_mem ψ q.2
  let π : Q →* SL(2, F) := e.symm.toMonoidHom.comp f
  have hπ : π.ker ≤ Subgroup.center Q := by
    intro q hq
    have h1 : f q = 1 := e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.mp hq)
    have h2 : ψ q = 1 := congrArg Subtype.val h1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker h2) g)
  have hX : commutator Q = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hQp)
  have hzk : (⟨z, hz⟩ : Q) ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    show e.symm (f ⟨z, hz⟩) = 1
    rw [show f ⟨z, hz⟩ = 1 from Subtype.ext hz1, map_one]
  obtain ⟨k, hk⟩ := CFSG.Quasithin.Vol2.Ch11.SecH.isPGroup_two_ker hX hn hF π hπ ⟨_, hzk⟩
  exact ⟨k, congrArg Subtype.val (congrArg Subtype.val hk)⟩

theorem exists_lift_of_slTwo (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {tb : R} (htb : tb ∈ ρ.range) (htbp : tb ^ p = 1) :
    ∃ t ∈ ⁅ρ.range.comap ψ, ρ.range.comap ψ⁆, t ^ p = 1 ∧ ψ t = tb := by
  set Q := ⁅ρ.range.comap ψ, ρ.range.comap ψ⁆ with hQ
  have hQmap : Q.map ψ = ρ.range :=
    CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ (commutator_range_slTwo hn hF)
  rw [← hQmap] at htb
  obtain ⟨q, hq, rfl⟩ := htb
  obtain ⟨k, hk⟩ := exists_two_pow_eq_one_of_slTwo hψ hker hn hF hρ (Q.pow_mem hq p)
    (by rw [map_pow, htbp])
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨q ^ (2 ^ k * u), Q.pow_mem hq _, ?_, ?_⟩
  · rw [← pow_mul, show 2 ^ k * u * p = p * 2 ^ k * u by ring, pow_mul, pow_mul, hk, one_pow]
  · rw [map_pow, pow_eq_pow_mod _ htbp, hu, pow_one]

theorem eq_of_slTwo (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {t₁ t₂ : L'} (h₁ : t₁ ∈ ⁅ρ.range.comap ψ, ρ.range.comap ψ⁆)
    (h₂ : t₂ ∈ ⁅ρ.range.comap ψ, ρ.range.comap ψ⁆) (hp₁ : t₁ ^ p = 1) (hp₂ : t₂ ^ p = 1)
    (h : ψ t₁ = ψ t₂) : t₁ = t₂ := by
  have hz1 : ψ (t₂⁻¹ * t₁) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨k, hk⟩ := exists_two_pow_eq_one_of_slTwo hψ hker hn hF hρ
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ h₂) h₁) hz1
  have hcomm : Commute t₂ (t₂⁻¹ * t₁) := Subgroup.mem_center_iff.mp (hker hz1) t₂
  have h3 := hcomm.mul_pow p
  rw [mul_inv_cancel_left, hp₁, hp₂, one_mul] at h3
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have ho : orderOf (t₂⁻¹ * t₁) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3.symm)
      (orderOf_dvd_of_pow_eq_one hk)
  exact (inv_mul_eq_one.mp (orderOf_eq_one_iff.mp ho)).symm

end Lift

@[expose] def GGStdSubTwoTorusSLTwoAut (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) :
    Prop :=
  ∀ Ab : Subgroup (MulAut R), IsElemAbelian p Ab → (∀ φ ∈ Ab, φ ∈ I) → p ^ r ≤ Nat.card Ab →
    ∀ ab ∈ Ab, ab ≠ 1 → ∀ D : Subgroup R, D ≤ ggFix ab →
      (∀ c ∈ ggFix ab, ∀ d ∈ D, c * d * c⁻¹ ∈ D) → CFSG.IsQuasisimple D →
      (∀ φ ∈ Ab, (∀ d ∈ D, φ d = d) → φ ∈ Subgroup.zpowers ab) →
      ∃ t : R, t ^ p = 1 ∧ (∀ φ ∈ Ab, φ t = t) ∧ MulAut.conj t ∈ Ab ∧
        (∃ j ∈ D, t * j ≠ j * t) ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ), 2 ≤ n ∧
          Nat.card F = 2 ^ n ∧ ∃ ρ : SL(2, F) →* R, Function.Injective ρ ∧ t ∈ ρ.range ∧
            ρ.range ≤ D ∧ ∀ φ ∈ Ab, ∀ y ∈ ρ.range, φ y ∈ ρ.range

theorem ggStdSubTwoTorusInnerSmall_of_slTwoAut {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] {I : Set (MulAut R)} (h : GGStdSubTwoTorusSLTwoAut p r R I) :
    GGStdSubTwoTorusInnerSmall p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ a haA ha1 hEcomp hcentA _
  have hind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hAbI : ∀ φ ∈ Ab, φ ∈ I := by
    rintro φ ⟨a', ha', hφ⟩
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a' ha'
    rwa [TypeA.induced_unique ψ hψ hφ hφ']
  obtain ⟨ab, hab⟩ := hind a haA
  have hab1 : ab ≠ 1 := by
    rintro rfl
    exact ha1 (TypeA.mulAut_eq_of_forall ψ hker hperf fun l => (hab l).symm)
  set E := LargeEvenLayer (ggFix a) with hE
  have hEq : CFSG.IsQuasisimple E := (TableBSymp.isQuasisimple_iff _).mp hEcomp.2.2
  have hEperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 hEq.1
  set D := E.map ψ with hD
  have hDq : CFSG.IsQuasisimple D :=
    (TableBSymp.isQuasisimple_iff _).mp (SURepair.isQuasisimple_map_of_isQuasisimple hker hEq)
  have hDfix : D ≤ ggFix ab := by
    rintro _ ⟨e, he, rfl⟩
    rw [mem_ggFix, hab, mem_ggFix.mp (hEcomp.1 he)]
  have hnorm : ∀ g : L', ab (ψ g) = ψ g → ∀ y ∈ ggFix a, g * y * g⁻¹ ∈ ggFix a := by
    intro g hg y hy
    have hz := TableBUD.mul_inv_mem_center_of_fix hker hab hg
    have hag : a g = (a g * g⁻¹) * g := by group
    rw [mem_ggFix] at hy ⊢
    rw [map_mul, map_mul, map_inv, hy, hag]
    have e := Subgroup.mem_center_iff.mp hz (g * y * g⁻¹)
    calc a g * g⁻¹ * g * y * (a g * g⁻¹ * g)⁻¹
        = (a g * g⁻¹) * (g * y * g⁻¹) * (a g * g⁻¹)⁻¹ := by group
      _ = (g * y * g⁻¹) * (a g * g⁻¹) * (a g * g⁻¹)⁻¹ := by rw [e]
      _ = g * y * g⁻¹ := by group
  have hDn : ∀ c ∈ ggFix ab, ∀ d ∈ D, c * d * c⁻¹ ∈ D := by
    intro c hc d hd
    obtain ⟨g, rfl⟩ := hψ c
    obtain ⟨e, he, rfl⟩ := hd
    have hg : ab (ψ g) = ψ g := mem_ggFix.mp hc
    have hg' : ab (ψ g⁻¹) = ψ g⁻¹ := by rw [map_inv, map_inv, hg]
    refine ⟨g * e * g⁻¹, StdSubRestThree.conj_mem_largeEvenLayer (hnorm g hg)
      (fun y hy => ?_) he, by rw [map_mul, map_mul, map_inv]⟩
    have h1 := hnorm g⁻¹ hg' y hy
    rwa [inv_inv] at h1
  have hcentD : ∀ φ ∈ Ab, (∀ d ∈ D, φ d = d) → φ ∈ Subgroup.zpowers ab := by
    rintro φ ⟨a', ha', hφ⟩ hfix
    have h1 : ⁅E, E⁆ ≤ ggFix a' := TableBUD.commutator_le_ggFix a' fun y hy =>
      TableBUD.mul_inv_mem_center_of_fix hker hφ (hfix _ ⟨y, hy, rfl⟩)
    have hfixE : ∀ j ∈ E, a' j = j := fun j hj => mem_ggFix.mp (h1 (by rw [hEperf]; exact hj))
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ((hcentA a' ha').mp hfixE)
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, TypeA.induced_unique ψ hψ (a := a') ?_ hφ⟩
    intro l
    rw [TableBUD.induced_zpow hab m l, hm]
  have hcard : Nat.card Ab = Nat.card A := TypeA.card_inducedSub hψ hker hperf hind
  obtain ⟨tb, htbp, htbfix, ⟨a'', ha'', h''⟩, ⟨jb, hjbD, hjb⟩, F, _, _, _, n, hn, hF, ρ, hρ, htbY,
    hYD, hYinv⟩ := h Ab (TypeA.isElemAbelian_inducedSub hψ hA) hAbI (hcard ▸ hr) ab
      ⟨a, haA, hab⟩ hab1 D hDfix hDn hDq hcentD
  set Q := ⁅ρ.range.comap ψ, ρ.range.comap ψ⁆ with hQ
  obtain ⟨t, htQ, htp, hψt⟩ := exists_lift_of_slTwo hψ hker hn hF hρ hp hp2 htbY htbp
  have hQE : Q ≤ E := by
    rw [hQ, Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨e₁, he₁, h₁⟩ := hYD hy₁
    obtain ⟨e₂, he₂, h₂⟩ := hYD hy₂
    have hz₁ : e₁⁻¹ * y₁ ∈ Subgroup.center L' :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h₁, inv_mul_cancel])
    have hz₂ : e₂⁻¹ * y₂ ∈ Subgroup.center L' :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h₂, inv_mul_cancel])
    have hc : ⁅y₁, y₂⁆ = ⁅e₁, e₂⁆ := by
      rw [show y₁ = e₁ * (e₁⁻¹ * y₁) by group, show y₂ = e₂ * (e₂⁻¹ * y₂) by group,
        CFSG.RankThree.PartOne.S15K.commutator_mul_central_left hz₁,
        CFSG.RankThree.PartOne.S15K.commutator_mul_central_right hz₂]
    rw [hc, ← hEperf]
    exact Subgroup.commutator_mem_commutator he₁ he₂
  have hfixA : ∀ a' ∈ A, a' t = t := by
    intro a' ha'
    obtain ⟨φ, hφ⟩ := hind a' ha'
    have hφA : φ ∈ Ab := ⟨a', ha', hφ⟩
    have hYc : (ρ.range.comap ψ).map (a' : MulAut L').toMonoidHom ≤ ρ.range.comap ψ := by
      rintro _ ⟨y, hy, rfl⟩
      show ψ (a' y) ∈ ρ.range
      rw [← hφ]
      exact hYinv φ hφA _ hy
    have hQc : Q.map (a' : MulAut L').toMonoidHom ≤ Q := by
      rw [hQ, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hYc hYc
    have hat : a' t ∈ Q := hQc ⟨t, htQ, rfl⟩
    refine eq_of_slTwo hψ hker hn hF hρ hp hp2 hat htQ (by rw [← map_pow, htp, map_one]) htp ?_
    rw [← hφ, hψt, htbfix φ hφA]
  have hconj : MulAut.conj t = a'' := TypeA.mulAut_eq_of_forall ψ hker hperf fun l => by
    rw [← h'' l, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hψt]
  obtain ⟨j, hjE, rfl⟩ := hjbD
  refine ⟨t, hQE htQ, htp, hfixA, hconj ▸ ha'', j, hjE, fun hc => hjb ?_⟩
  rw [← hψt, ← map_mul, ← map_mul, hc]

end CFSG.StandardType.SmallExc

end
