module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem b15_S4C_mem_normalizer_centralizer {V : Subgroup G} {x : G}
    (hx : x ∈ normalizer (V : Set G)) : x ∈ normalizer (centralizer (V : Set G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer] at hx ⊢
  rw [E3.conjSubgroup_centralizer, hx]

private theorem b15_S4C_commutator_mul_left {z x y : G} (hzx : z * x = x * z)
    (hzy : z * y = y * z) : ⁅z * x, y⁆ = ⁅x, y⁆ := by
  have h1 : Commute z (x * y * x⁻¹) :=
    ((show Commute z x from hzx).mul_right (show Commute z y from hzy)).mul_right
      (show Commute z x from hzx).inv_right
  have h2 : z * (x * y * x⁻¹) * z⁻¹ = x * y * x⁻¹ := by
    rw [h1.eq]; group
  rw [commutatorElement_def, commutatorElement_def]
  calc z * x * y * (z * x)⁻¹ * y⁻¹ = (z * (x * y * x⁻¹) * z⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h2]

private theorem b15_S4C_commutator_mul_right {z x y : G} (hzx : z * x = x * z)
    (hzy : z * y = y * z) : ⁅x, z * y⁆ = ⁅x, y⁆ := by
  have h1 : Commute z (x * y * x⁻¹ * y⁻¹) :=
    ((((show Commute z x from hzx).mul_right (show Commute z y from hzy)).mul_right
      (show Commute z x from hzx).inv_right).mul_right (show Commute z y from hzy).inv_right)
  have h2 : z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    rw [h1.eq]; group
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (z * y) * x⁻¹ * (z * y)⁻¹ = z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ := by
        have hxz : x * z = z * x := hzx.symm
        calc x * (z * y) * x⁻¹ * (z * y)⁻¹ = (x * z) * y * x⁻¹ * y⁻¹ * z⁻¹ := by group
          _ = (z * x) * y * x⁻¹ * y⁻¹ * z⁻¹ := by rw [hxz]
          _ = z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := h2

private theorem b15_S4C_conj_mem {D : Subgroup G} {n : G} (hn : n ∈ normalizer (D : Set G))
    {x : G} (hx : x ∈ Subgroup.closure
      ({y | ∃ a ∈ D, y = a * a} ∪ {y | ∃ a ∈ D, ∃ b ∈ D, y = ⁅a, b⁆})) :
    n * x * n⁻¹ ∈ Subgroup.closure
      ({y | ∃ a ∈ D, y = a * a} ∪ {y | ∃ a ∈ D, ∃ b ∈ D, y = ⁅a, b⁆}) := by
  have hconj : ∀ a ∈ D, n * a * n⁻¹ ∈ D := fun a ha =>
    (Subgroup.mem_normalizer_iff.1 hn a).1 ha
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
    · refine Subgroup.subset_closure (Or.inl ⟨n * a * n⁻¹, hconj a ha, ?_⟩)
      group
    · refine Subgroup.subset_closure
        (Or.inr ⟨n * a * n⁻¹, hconj a ha, n * b * n⁻¹, hconj b hb, ?_⟩)
      rw [commutatorElement_def, commutatorElement_def]
      group
  | one =>
    have h1 : n * 1 * n⁻¹ = 1 := by group
    rw [h1]
    exact Subgroup.one_mem _
  | mul y z _ _ hy hz =>
    have h1 : n * (y * z) * n⁻¹ = (n * y * n⁻¹) * (n * z * n⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have h1 : n * y⁻¹ * n⁻¹ = (n * y * n⁻¹)⁻¹ := by group
    rw [h1]
    exact Subgroup.inv_mem _ hy

private theorem b15_S4C_mem_normalizer_closure {D : Subgroup G} {n : G}
    (hn : n ∈ normalizer (D : Set G)) :
    n ∈ normalizer (Subgroup.closure
      ({y | ∃ a ∈ D, y = a * a} ∪ {y | ∃ a ∈ D, ∃ b ∈ D, y = ⁅a, b⁆}) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => b15_S4C_conj_mem hn hx, fun hx => ?_⟩
  have h1 := b15_S4C_conj_mem ((normalizer (D : Set G)).inv_mem hn) hx
  have h2 : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
  rwa [h2] at h1

namespace Cfg1511

variable {M V₀ V U S H Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem isElemAbelian_tSub15_inf_centralizer
    (c : Cfg1511 M V₀ V U S H S Q₀ p) (hX : XData15 V₀ U H Q₀ p X v)
    (hTKC : tSub15 M V₀ V U S ≤ kHull15 V₀ H ⊔ cSub15 M V₀ V U H S)
    (hEV : tSub15 M V₀ V U S ⊓ kHull15 V₀ H ⊓ centralizer (V₀ : Set G) ≤ V₀) :
    IsElemAbelian 2 (tSub15 M V₀ V U S ⊓ centralizer (V : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := tSub15 M V₀ V U S with hTdef
  set C := cSub15 M V₀ V U H S with hCdef
  set K := kHull15 V₀ H with hKdef
  set D := T ⊓ centralizer (V : Set G) with hDdef
  have hNH : M ⊓ centralizer (V : Set G) ≤ M ⊓ centralizer (U : Set G) :=
    inf_le_inf_left M (Subgroup.centralizer_le c.cex.le)
  have hnormal : ((M ⊓ centralizer (V : Set G)).subgroupOf
      (M ⊓ centralizer (U : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNH]
    intro x hx
    have hxV : x ∈ normalizer (V : Set G) := by rw [c.cex.hyp.h6.normalizer_eq]; exact hx.1
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx.1, b15_S4C_mem_normalizer_centralizer hxV⟩
  have hSyl : IsSylowIn 2 (S ⊓ (M ⊓ centralizer (V : Set G))) (M ⊓ centralizer (V : Set G)) :=
    c.cex.sylow.inf_normal hNH hnormal
  have hV₁V : v1Sub15 V₀ U ≤ V := (v1Sub15_le_left V₀ U).trans c.cex.hyp.h6.le
  have hDQ : D = S ⊓ (M ⊓ centralizer (V : Set G)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxT, hxV⟩ := hx
      exact ⟨tSub15_le_P M V₀ V U S hxT,
        cTilde_le_M M V₀ V (tSub15_le_cTilde M V₀ V U S hxT), hxV⟩
    · intro x hx
      obtain ⟨hxS, hxM, hxV⟩ := hx
      refine ⟨mem_tSub15_iff.2 ⟨hxS, ?_, Subgroup.centralizer_le hV₁V hxV⟩, hxV⟩
      refine FourteenTwo.mem_cTilde_iff_comm.2
        ⟨hxM, c.cex.hyp.h6.le_normalizer₀ hxM, fun w hw => ?_⟩
      have hcomm : x * w = w * x := (Subgroup.mem_centralizer_iff.1 hxV w hw).symm
      rw [hcomm]
      simp
  rw [← hDQ] at hSyl
  have hU : InCalU M (M ⊓ normalizer (D : Set G)) := c.cex.hyp.qclause D hSyl
  have hCK : C ≤ centralizer (K : Set G) := cSub15_le_centralizer M V₀ V U H S
  have hKn : K ≤ normalizer (C : Set G) :=
    (Subgroup.le_centralizer_iff.1 hCK).trans (Subgroup.centralizer_le_normalizer _)
  have hCT : C ≤ T := cSub15_le_tSub15 M V₀ V U H S
  have hCV : C ≤ centralizer (V : Set G) := c.cSub15_le_centralizer_V hX
  have hV₀K : V₀ ≤ K := Hyp1510.V₀_le_kHull15 V₀ H
  have hDT : D ≤ T := inf_le_left
  have hdecomp : ∀ d ∈ D, ∃ k ∈ V₀, ∃ c' ∈ C, d = k * c' := by
    intro d hd
    have hdKC : d ∈ ((K ⊔ C : Subgroup G) : Set G) := hTKC hd.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K C hKn] at hdKC
    obtain ⟨k, hk, c', hc', rfl⟩ := hdKC
    refine ⟨k, ?_, c', hc', rfl⟩
    have hk' : k = (k * c') * c'⁻¹ := by group
    have hkT : k ∈ T := by
      rw [hk']
      exact T.mul_mem hd.1 (T.inv_mem (hCT hc'))
    have hkV : k ∈ centralizer (V : Set G) := by
      rw [hk']
      exact (centralizer (V : Set G)).mul_mem hd.2
        ((centralizer (V : Set G)).inv_mem (hCV hc'))
    exact hEV ⟨⟨hkT, hk⟩, Subgroup.centralizer_le c.cex.hyp.h6.le hkV⟩
  set R : Subgroup G := Subgroup.closure
    ({y | ∃ a ∈ D, y = a * a} ∪ {y | ∃ a ∈ D, ∃ b ∈ D, y = ⁅a, b⁆}) with hRdef
  have hRD : R ≤ D := by
    rw [hRdef, Subgroup.closure_le]
    rintro y (⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact D.mul_mem ha ha
    · rw [commutatorElement_def]
      exact D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb)
  have hCk : ∀ {k c' : G}, k ∈ V₀ → c' ∈ C → k * c' = c' * k := fun {k c'} hk hc' =>
    Subgroup.mem_centralizer_iff.1 (hCK hc') k (hV₀K hk)
  have hV₀c : ∀ {k k' : G}, k ∈ V₀ → k' ∈ V₀ → k * k' = k' * k := fun {k k'} hk hk' => by
    have := c.cex.hyp.elemAbelian₀.1
    exact congrArg Subtype.val (mul_comm' (⟨k, hk⟩ : V₀) ⟨k', hk'⟩)
  have hV₀sq : ∀ {k : G}, k ∈ V₀ → k * k = 1 := fun {k} hk => by
    simpa [pow_two] using c.cex.hyp.elemAbelian₀.2 k hk
  have hRC : R ≤ C := by
    rw [hRdef, Subgroup.closure_le]
    rintro y (⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · obtain ⟨k, hk, c', hc', rfl⟩ := hdecomp a ha
      have h1 : k * c' * (k * c') = c' * c' := by
        calc k * c' * (k * c') = k * (c' * k) * c' := by group
          _ = k * (k * c') * c' := by rw [hCk hk hc']
          _ = (k * k) * c' * c' := by group
          _ = c' * c' := by rw [hV₀sq hk]; group
      rw [h1]
      exact C.mul_mem hc' hc'
    · obtain ⟨k, hk, c', hc', rfl⟩ := hdecomp a ha
      obtain ⟨k₁, hk₁, c₁, hc₁, rfl⟩ := hdecomp b hb
      have hkk₁c₁ : k * (k₁ * c₁) = (k₁ * c₁) * k := by
        calc k * (k₁ * c₁) = (k * k₁) * c₁ := by group
          _ = (k₁ * k) * c₁ := by rw [hV₀c hk hk₁]
          _ = k₁ * (k * c₁) := by group
          _ = k₁ * (c₁ * k) := by rw [hCk hk hc₁]
          _ = (k₁ * c₁) * k := by group
      rw [b15_S4C_commutator_mul_left (hCk hk hc') hkk₁c₁,
        b15_S4C_commutator_mul_right (hCk hk₁ hc') (hCk hk₁ hc₁), commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hc' hc₁) (C.inv_mem hc')) (C.inv_mem hc₁)
  have hNR : M ⊓ normalizer (D : Set G) ≤ normalizer (R : Set G) := fun n hn =>
    b15_S4C_mem_normalizer_closure hn.2
  have hR2 : IsPGroup 2 R :=
    c.hyp.sylow.isPGroup.to_le (hRD.trans (hDT.trans (tSub15_le_P M V₀ V U S)))
  have hRbot : R = ⊥ := by
    by_contra hRne
    have hRn : normalizer (R : Set G) ≤ M := normalizer_le_of_inCalU hU hNR hRne hR2
    have hKR : K ≤ normalizer (R : Set G) :=
      (Subgroup.le_centralizer_iff.1 (hRC.trans hCK)).trans
        (Subgroup.centralizer_le_normalizer _)
    exact XData15.not_le_M c hX (hX.le_kHull15.trans (hKR.trans hRn))
  have hsq : ∀ a ∈ D, a * a = 1 := fun a ha => by
    have h1 : a * a ∈ R := Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩)
    rw [hRbot] at h1
    exact Subgroup.mem_bot.1 h1
  have hcm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => by
    have h1 : ⁅a, b⁆ ∈ R := Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, rfl⟩)
    rw [hRbot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 h1)
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact hcm x.1 x.2 y.1 y.2
  · rw [pow_two]
    exact hsq x hx

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
