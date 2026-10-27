module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HDefs
public import CFSG.RankThree.PartTwo.Sec12.Hering129KM3
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open Hering129KM2
open scoped Matrix
open CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof (qOne tOne SL23)

section Realize

variable {G : Type} [Group G] {x₁ x₂ n₁ t : G}

theorem theta_mem_autIn (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9)
    (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁)
    (ht1 : t * x₁ * t⁻¹ = x₁) (ht2 : t * x₂ * t⁻¹ = x₂ * x₁) (γ : SL23) :
    theta h12 h1 h2 hcard γ ∈ Sec4.autIn ⊤ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) := by
  have hfin : Finite (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hx₁E : x₁ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx₂E : x₂ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  have hN₁ := mem_normalizer_of_conj h12 (m := n₁) (by rw [hF1]; exact inv_mem hx₂E)
    (by rw [hF2]; exact hx₁E)
  have hNt := mem_normalizer_of_conj h12 (m := t) (by rw [ht1]; exact hx₁E)
    (by rw [ht2]; exact mul_mem hx₂E hx₁E)
  have hS : theta h12 h1 h2 hcard qOne ∈
      Sec4.autIn ⊤ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :=
    Sec4.mem_autIn_iff.mpr ⟨n₁, hN₁, trivial, normalizerMonoidHom_eq_theta h12 h1 h2 hcard hN₁
      (a := 0) (b := 1) (c := -1) (d := 0) (by rw [hF1]; simp) (by rw [hF2]; simp) qOne
      (by decide +kernel)⟩
  have hT : theta h12 h1 h2 hcard tOne ∈
      Sec4.autIn ⊤ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :=
    Sec4.mem_autIn_iff.mpr ⟨t, hNt, trivial, normalizerMonoidHom_eq_theta h12 h1 h2 hcard hNt
      (a := 1) (b := 1) (c := 0) (d := 1) (by rw [ht1]; simp)
      (by rw [ht2, zpow_one, zpow_one, h12]) tOne (by decide +kernel)⟩
  have hrange : (theta h12 h1 h2 hcard).range ≤
      Sec4.autIn ⊤ (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) := by
    rw [MonoidHom.range_eq_map, ← closure_qOne_tOne, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨γ, hγ, rfl⟩
    rcases hγ with rfl | rfl
    · exact hS
    · exact hT
  exact hrange ⟨γ, rfl⟩

theorem exists_conj_of_sl (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9)
    (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁)
    (ht1 : t * x₁ * t⁻¹ = x₁) (ht2 : t * x₂ * t⁻¹ = x₂ * x₁) (γ : SL23) :
    ∃ n ∈ Subgroup.normalizer
        ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G),
      ∀ v : Fin 2 → ZMod 3, n * pt x₁ x₂ v * n⁻¹ =
        pt x₁ x₂ ((γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v) := by
  obtain ⟨n, hnN, -, hn⟩ := Sec4.mem_autIn_iff.mp
    (theta_mem_autIn h12 h1 h2 hcard hF1 hF2 ht1 ht2 γ)
  refine ⟨n, hnN, fun v => ?_⟩
  have h := DFunLike.congr_fun hn (coordEquiv h12 h1 h2 hcard (Multiplicative.ofAdd v))
  have h' := congrArg Subtype.val h
  rw [Sec4.normalizerMonoidHom_apply_coe hnN, theta_apply_coord, coordEquiv_apply_coe,
    toAdd_ofAdd] at h'
  exact h'

end Realize

theorem mem_normalizer_of_forall_mem' {G : Type*} [Group G] (S : Subgroup G) [Finite S] {c : G}
    (h : ∀ s ∈ S, c * s * c⁻¹ ∈ S) : c ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  let φ : S → S := fun s => ⟨c * s * c⁻¹, h s s.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : c * (a : G) * c⁻¹ = c * (b : G) * c⁻¹ := congrArg (fun t : S => (t : G)) hab
    exact Subtype.ext (by simpa using h1)
  obtain ⟨s, hs⟩ := Finite.surjective_of_injective hinj ⟨c * n * c⁻¹, hn⟩
  have h2 : c * (s : G) * c⁻¹ = c * n * c⁻¹ := congrArg (fun t : S => (t : G)) hs
  have h3 : (s : G) = n := by simpa using h2
  rw [← h3]
  exact s.2

theorem pt_e1 {G : Type} [Group G] {x₁ x₂ : G} (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) :
    pt x₁ x₂ ![1, 0] = x₁ := by
  rw [pt_eq h1 h2 (i := 1) (j := 0) (by simp) (by simp)]
  simp

theorem pt_e2 {G : Type} [Group G] {x₁ x₂ : G} (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) :
    pt x₁ x₂ ![0, 1] = x₂ := by
  rw [pt_eq h1 h2 (i := 0) (j := 1) (by simp) (by simp)]
  simp

theorem pt_e3 {G : Type} [Group G] {x₁ x₂ : G} (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) :
    pt x₁ x₂ ![0, 2] = x₂⁻¹ := by
  rw [pt_eq h1 h2 (i := 0) (j := 2) (by simp) (by simp)]
  have h3 : x₂ ^ (3 : ℤ) = 1 := by exact_mod_cast h2
  calc x₁ ^ (0 : ℤ) * x₂ ^ (2 : ℤ) = x₂ ^ (3 : ℤ) * x₂⁻¹ := by
        rw [zpow_zero, one_mul, ← zpow_neg_one, ← zpow_add]; norm_num
    _ = x₂⁻¹ := by rw [h3, one_mul]

theorem exists_sl_mulVec_e1 (v : Fin 2 → ZMod 3) (hv : v ≠ 0) :
    ∃ γ : SL23, (γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ ![1, 0] = v := by
  have key : ∀ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) → a * a - (-(b * (1 - a * a))) * b = 1 := by
    decide +kernel
  have ha : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  refine ⟨⟨!![v 0, -(v 1 * (1 - v 0 * v 0)); v 1, v 0], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    exact key _ _ ha
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

section Det

variable {G : Type} [Group G] {x₁ x₂ n₁ t : G}

theorem sl_complement (a b c d : ZMod 3) (h : a * d - b * c = 2) :
    (2 * d) * a - (2 * b) * c = 1 ∧
      !![a, b; c, d] * !![2 * d, 2 * b; c, a] = !![1, 0; 0, 2] := by
  revert a b c d
  decide +kernel

theorem det_one_of_noRefl (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9)
    (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁)
    (ht1 : t * x₁ * t⁻¹ = x₁) (ht2 : t * x₂ * t⁻¹ = x₂ * x₁)
    (hNR : ∀ m ∈ Subgroup.normalizer
        ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G),
      m * x₁ * m⁻¹ = x₁ → m * x₂ * m⁻¹ = x₂⁻¹ → False)
    {m : G} (hmN : m ∈ Subgroup.normalizer
        ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G)) :
    ∃ a b c d : ℤ, (a * d - b * c) % 3 = 1 ∧ m * x₁ * m⁻¹ = x₁ ^ a * x₂ ^ c ∧
      m * x₂ * m⁻¹ = x₁ ^ b * x₂ ^ d := by
  have hx₁E : x₁ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx₂E : x₂ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  obtain ⟨a, c, hm1⟩ := Sec4.exists_zpow_mul_of_mem_sup h12
    ((Subgroup.mem_normalizer_iff.mp hmN x₁).mp hx₁E)
  obtain ⟨b, d, hm2⟩ := Sec4.exists_zpow_mul_of_mem_sup h12
    ((Subgroup.mem_normalizer_iff.mp hmN x₂).mp hx₂E)
  refine ⟨a, b, c, d, ?_, hm1, hm2⟩
  set A : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![(a : ZMod 3), b; c, d] with hA
  have hconj := conj_pt h12 h1 h2 hm1 hm2
  have hdet0 : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h3 : m * pt x₁ x₂ v * m⁻¹ = 1 := by
      rw [hconj v, ← hA, hAv]
      simp [pt]
    have h4 : pt x₁ x₂ v = 1 := by
      have : pt x₁ x₂ v = m⁻¹ * (m * pt x₁ x₂ v * m⁻¹) * m := by group
      rw [this, h3]
      group
    apply hv
    have h5 : coordEquiv h12 h1 h2 hcard (Multiplicative.ofAdd v) = 1 :=
      Subtype.ext (by simpa [coordEquiv_apply_coe] using h4)
    have h6 : Multiplicative.ofAdd v = 1 := (coordEquiv h12 h1 h2 hcard).injective
      (by rw [h5, map_one])
    simpa using h6
  have hdetA : A.det = a * d - b * c := by
    rw [hA, Matrix.det_fin_two_of]
  by_contra hne
  have hdet2 : A.det = 2 := by
    have hz : ((a * d - b * c : ℤ) : ZMod 3) = A.det := by
      rw [hdetA]; push_cast; rfl
    have hmod : ((a * d - b * c) % 3 : ℤ) = 0 ∨ ((a * d - b * c) % 3 : ℤ) = 1 ∨
        ((a * d - b * c) % 3 : ℤ) = 2 := by omega
    have hz' : ((((a * d - b * c) % 3 : ℤ)) : ZMod 3) = A.det := by
      rw [← hz]
      have := ZMod.intCast_mod (a * d - b * c) 3
      simpa using this
    rcases hmod with h | h | h
    · exfalso
      apply hdet0
      rw [← hz', h]
      simp
    · exact absurd h hne
    · rw [← hz', h]
      rfl
  obtain ⟨hγdet, hAγ⟩ := sl_complement (a : ZMod 3) b c d (by rw [← hdetA]; exact hdet2)
  let γ : SL23 := ⟨!![2 * (d : ZMod 3), 2 * (b : ZMod 3); (c : ZMod 3), (a : ZMod 3)], by
    rw [Matrix.det_fin_two_of]; exact hγdet⟩
  obtain ⟨n, hnN, hn⟩ := exists_conj_of_sl h12 h1 h2 hcard hF1 hF2 ht1 ht2 γ
  refine hNR (m * n) (Subgroup.mul_mem _ hmN hnN) ?_ ?_
  · have e1 : pt x₁ x₂ ![1, 0] = x₁ := pt_e1 h1 h2
    calc m * n * x₁ * (m * n)⁻¹ = m * (n * pt x₁ x₂ ![1, 0] * n⁻¹) * m⁻¹ := by
          rw [e1]; group
      _ = x₁ := by
          rw [hn, hconj]
          have : A *ᵥ ((γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ ![1, 0]) = ![1, 0] := by
            rw [Matrix.mulVec_mulVec]
            have hAγ' : A * (γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![1, 0; 0, 2] := hAγ
            rw [hAγ']
            ext i
            fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          rw [this, e1]
  · have e2 : pt x₁ x₂ ![0, 1] = x₂ := pt_e2 h1 h2
    have e3 : pt x₁ x₂ ![0, 2] = x₂⁻¹ := pt_e3 h1 h2
    calc m * n * x₂ * (m * n)⁻¹ = m * (n * pt x₁ x₂ ![0, 1] * n⁻¹) * m⁻¹ := by
          rw [e2]; group
      _ = x₂⁻¹ := by
          rw [hn, hconj]
          have : A *ᵥ ((γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ ![0, 1]) = ![0, 2] := by
            rw [Matrix.mulVec_mulVec]
            have hAγ' : A * (γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![1, 0; 0, 2] := hAγ
            rw [hAγ']
            ext i
            fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          rw [this, e3]

end Det

section Assemble

variable {G : Type} [Group G] {x₁ x₂ n₁ t : G}

theorem hessF_of_noRefl (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9)
    (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁)
    (ht1 : t * x₁ * t⁻¹ = x₁) (ht2 : t * x₂ * t⁻¹ = x₂ * x₁)
    (hNR : ∀ m ∈ Subgroup.normalizer
        ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G),
      m * x₁ * m⁻¹ = x₁ → m * x₂ * m⁻¹ = x₂⁻¹ → False) :
    HessF x₁ t (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) := by
  have hdet : ∀ m ∈ ((⊤ : Subgroup G) ⊔ Subgroup.zpowers t) ⊓ Subgroup.normalizer
      ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G),
      ∃ a b c d : ℤ, (a * d - b * c) % 3 = 1 ∧ m * x₁ * m⁻¹ = x₁ ^ a * x₂ ^ c ∧
        m * x₂ * m⁻¹ = x₁ ^ b * x₂ ^ d := fun m hm =>
    det_one_of_noRefl h12 h1 h2 hcard hF1 hF2 ht1 ht2 hNR (Subgroup.mem_inf.mp hm).2
  obtain ⟨-, hab, hcard9, hx₁F, hwF, -, hcomm, hnt, hAut⟩ := hess_abstract (Lh := ⊤)
    (F := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) (w := t) rfl trivial trivial h12 h1 h2 hcard
    trivial hF1 hF2 ht1 (Or.inl ht2) hdet
  haveI : Finite (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨hab, hcard9, hx₁F, mem_normalizer_of_forall_mem' _ hwF, hcomm, hnt, ?_,
    ?_⟩
  ·
    intro f hf hf1
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 hf
    set v : Fin 2 → ZMod 3 := ![(i : ZMod 3), (j : ZMod 3)] with hv
    have hv0 : v ≠ 0 := by
      intro h0
      apply hf1
      have e : pt x₁ x₂ v = x₁ ^ i * x₂ ^ j := pt_eq h1 h2 rfl rfl
      rw [← e, h0]
      simp [pt]
    obtain ⟨γ, hγ⟩ := exists_sl_mulVec_e1 v hv0
    obtain ⟨n, hnN, hn⟩ := exists_conj_of_sl h12 h1 h2 hcard hF1 hF2 ht1 ht2 γ
    refine ⟨n, hnN, ?_⟩
    have e1 : pt x₁ x₂ ![1, 0] = x₁ := pt_e1 h1 h2
    have := hn ![1, 0]
    rw [e1, hγ] at this
    rw [this]
    exact pt_eq h1 h2 rfl rfl
  · rw [top_sup_eq] at hAut
    exact hAut

end Assemble

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
