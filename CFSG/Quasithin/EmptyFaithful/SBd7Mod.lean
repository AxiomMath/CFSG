module

public import CFSG.Quasithin.EmptyFaithful.SBd5Perf
public import CFSG.Quasithin.EmptyFaithful.SBd5UL
public import CFSG.Quasithin.EmptyFaithful.SBd6Tw

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace SBd7

section Duality

theorem exists_fixed_of_ne_top {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (M : Set (Matrix (Fin 3) (Fin 3) F)) (B : AddSubgroup (Fin 3 → F))
    (hB : ∀ A ∈ M, ∀ v : Fin 3 → F, A.transpose.mulVec v - v ∈ B) (hBtop : B ≠ ⊤) :
    ∃ x : Fin 3 → F, x ≠ 0 ∧ ∀ A ∈ M, A.mulVec x = x := by
  classical
  let W : Submodule F (Fin 3 → F) :=
    { carrier := B
      add_mem' := fun {a b} ha hb => B.add_mem ha hb
      zero_mem' := B.zero_mem
      smul_mem' := fun c x hx => by
        rcases SBd5.eq_zero_or_one_of_card_two hF c with rfl | rfl
        · simp
        · simpa using hx }
  have hlt : W < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hBtop
    rw [eq_top_iff]
    intro x _
    have : x ∈ W := by rw [h]; trivial
    exact this
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_le_ker_of_lt_top W hlt
  set x : Fin 3 → F := fun i => f (fun j => if i = j then 1 else 0) with hx
  have hfv : ∀ v, f v = v ⬝ᵥ x := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    simp [dotProduct, hx]
  refine ⟨x, ?_, fun A hA => ?_⟩
  · intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    rw [hfv, h0]
    simp
  · funext i
    have h1 := hfW (show A.transpose.mulVec (fun j => if i = j then 1 else 0) -
        (fun j => if i = j then (1 : F) else 0) ∈ W from hB A hA _)
    rw [LinearMap.mem_ker, hfv, sub_dotProduct, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec, sub_eq_zero] at h1
    simpa [dotProduct] using h1

end Duality

section Case3

variable {G : Type} [Group G]

theorem le_commutator_of_case3 {L Q : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hα : IsModO2Surj L α)
    (hZ1 : IsSumOfNaturalModulesVia L (centerOf Q) ⊥ α false 1)
    (hZ2 : IsSumOfNaturalModulesVia L Q (centerOf Q) α true 2) :
    centerOf Q ≤ ⁅Q, Q⁆ := by
  classical
  obtain ⟨hLZ, -, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := hZ1
  obtain ⟨hLQ, hZQ, β₂, hβ₂s, hβ₂k, hβ₂e⟩ := hZ2
  have hβ₁i : Function.Injective β₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₁k, Subgroup.bot_subgroupOf]
  have hD : ∀ q ∈ ⁅Q, Q⁆, q ∈ centerOf Q := by
    intro q hq
    refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_) hq
    have hc : ⁅a, b⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
    have h1 : β₂ (⟨⁅a, b⁆, hc⟩ : ↥Q) = 1 := by
      have : (⟨⁅a, b⁆, hc⟩ : ↥Q) = ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, mul_inv_cancel]
    have h2 : (⟨⁅a, b⁆, hc⟩ : ↥Q) ∈ β₂.ker := h1
    rw [hβ₂k, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hLD : L ≤ Subgroup.normalizer ((⁅Q, Q⁆ : Subgroup G) : Set G) := fun l hl =>
    SBd5.mem_normalizer_commutator_of (hLQ hl) (hLQ hl)
  let X : AddSubgroup (Fin 3 → F) :=
    { carrier := {x | ∃ d : ↥(centerOf Q), (d : G) ∈ ⁅Q, Q⁆ ∧ Multiplicative.toAdd (β₁ d) 0 = x}
      zero_mem' := ⟨1, ⁅Q, Q⁆.one_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, rfl⟩
        refine ⟨u₁ * u₂, ⁅Q, Q⁆.mul_mem hu₁ hu₂, ?_⟩
        simp
      neg_mem' := by
        rintro _ ⟨u₁, hu₁, rfl⟩
        refine ⟨u₁⁻¹, ⁅Q, Q⁆.inv_mem hu₁, ?_⟩
        show Multiplicative.toAdd (β₁ u₁⁻¹) 0 = -(Multiplicative.toAdd (β₁ u₁) 0)
        rw [map_inv, toAdd_inv]
        rfl }
  have hXinv : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∀ x ∈ X,
      (g : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ X := by
    intro g x hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨l, hl⟩ := SBd5.act_surj hα.1 g
    have hlu : (l : G) * (u : G) * (l : G)⁻¹ ∈ centerOf Q :=
      (Subgroup.mem_normalizer_iff.mp (hLZ l.2) _).mp u.2
    have hluD : (l : G) * (u : G) * (l : G)⁻¹ ∈ ⁅Q, Q⁆ :=
      (Subgroup.mem_normalizer_iff.mp (hLD l.2) _).mp hu
    refine ⟨⟨_, hlu⟩, hluD, ?_⟩
    have := hβ₁e l u ⟨_, hlu⟩ rfl 0
    rw [this]
    have h' : moduleAct false (α l : Matrix.GeneralLinearGroup (Fin 3) F) =
        ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      simp [moduleAct]
    rw [h', ← hl]
  rcases SBd6.irreducible_vec hF X hXinv with h | h
  ·
    exfalso
    have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
      intro a ha b hb
      have hc : ⁅a, b⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator ha hb
      have hcZ : (⟨⁅a, b⁆, hD _ hc⟩ : ↥(centerOf Q)) = 1 := by
        apply hβ₁i
        apply Multiplicative.toAdd.injective
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        have hmem : Multiplicative.toAdd (β₁ ⟨⁅a, b⁆, hD _ hc⟩) 0 ∈ X := ⟨_, hc, rfl⟩
        rw [h] at hmem
        have h0 : Multiplicative.toAdd (β₁ ⟨⁅a, b⁆, hD _ hc⟩) 0 = 0 := by simpa using hmem
        rw [h0]
        simp
      have : ⁅a, b⁆ = 1 := congrArg Subtype.val hcZ
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    obtain ⟨q, hq⟩ := hβ₂s (Multiplicative.ofAdd (fun _ _ => (1 : F)))
    have hqk : q ∈ β₂.ker := by
      rw [hβ₂k, Subgroup.mem_subgroupOf]
      exact ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm _ q.2 b hb).symm⟩
    have h1 : β₂ q = 1 := hqk
    rw [hq] at h1
    have h2 := congrArg (fun w : Multiplicative (Fin 2 → Fin 3 → F) =>
      Multiplicative.toAdd w (0 : Fin 2) (0 : Fin 3)) h1
    simp at h2
  · intro z hz
    have hmem : Multiplicative.toAdd (β₁ ⟨z, hz⟩) 0 ∈ X := by rw [h]; trivial
    obtain ⟨d, hdD, hd⟩ := hmem
    have hdz : d = ⟨z, hz⟩ := by
      apply hβ₁i
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact hd
    have : (d : G) = z := congrArg Subtype.val hdz
    rw [← this]
    exact hdD

theorem exists_mul_of_dual {L Q H Y : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hZ2 : IsSumOfNaturalModulesVia L Q (centerOf Q) α true 2)
    (hYL : Y ≤ L) (hYQ : Y ≤ Subgroup.normalizer (Q : Set G)) (hH : ⁅Q, Y⁆ ≤ H)
    (hfix : ∀ x : Fin 3 → F, (∀ (y : G) (hy : y ∈ Y),
      ((α ⟨y, hYL hy⟩ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x) →
        x = 0) :
    ∀ q ∈ Q, ∃ h ∈ H, ∃ z ∈ centerOf Q, q = h * z := by
  classical
  obtain ⟨hLQ, hZQ, β, hβs, hβk, hβe⟩ := hZ2
  have hcoord : ∀ j : Fin 2, ∀ a : Fin 3 → F, ∃ h : ↥Q, (h : G) ∈ H ∧
      Multiplicative.toAdd (β h) = Pi.single j a := by
    intro j
    let B : AddSubgroup (Fin 3 → F) :=
      { carrier := {a | ∃ h : ↥Q, (h : G) ∈ H ∧ Multiplicative.toAdd (β h) = Pi.single j a}
        zero_mem' := ⟨1, H.one_mem, by simp⟩
        add_mem' := by
          rintro _ _ ⟨h₁, hh₁, e₁⟩ ⟨h₂, hh₂, e₂⟩
          refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
          rw [map_mul, toAdd_mul, e₁, e₂, ← Pi.single_add]
        neg_mem' := by
          rintro _ ⟨h₁, hh₁, e₁⟩
          refine ⟨h₁⁻¹, H.inv_mem hh₁, ?_⟩
          rw [map_inv, toAdd_inv, e₁, ← Pi.single_neg] }
    have hB : B = ⊤ := by
      by_contra hne
      have hBM : ∀ A ∈ {A : Matrix (Fin 3) (Fin 3) F | ∃ (y : G) (hy : y ∈ Y),
          A = ((α ⟨y, hYL hy⟩ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)},
          ∀ v : Fin 3 → F, A.transpose.mulVec v - v ∈ B := by
        rintro A ⟨y, hy, rfl⟩ v
        obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd (Pi.single j v))
        have hy' : y⁻¹ ∈ Y := Y.inv_mem hy
        have hyq : y⁻¹ * (q : G) * (y⁻¹)⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hYQ hy') _).mp q.2
        have hact := hβe ⟨y⁻¹, hYL hy'⟩ q ⟨_, hyq⟩ rfl
        have hmod : moduleAct true (α ⟨y⁻¹, hYL hy'⟩ : Matrix.GeneralLinearGroup (Fin 3) F) =
            ((α ⟨y, hYL hy⟩ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose := by
          have : (⟨y⁻¹, hYL hy'⟩ : ↥L) = (⟨y, hYL hy⟩ : ↥L)⁻¹ := rfl
          rw [this, map_inv]
          simp [moduleAct]
        have hqe : Multiplicative.toAdd (β q) = Pi.single j v := by
          rw [hq]; rfl
        refine ⟨⟨_, hyq⟩ * q⁻¹, ?_, ?_⟩
        · have hmem : ((⟨_, hyq⟩ * q⁻¹ : ↥Q) : G) ∈ ⁅Q, Y⁆ := by
            rw [Subgroup.commutator_comm]
            have : ((⟨_, hyq⟩ * q⁻¹ : ↥Q) : G) = ⁅y⁻¹, (q : G)⁆ := by
              simp [commutatorElement_def]
            rw [this]
            exact Subgroup.commutator_mem_commutator hy' q.2
          exact hH hmem
        · rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hqe]
          funext i
          have hi := hact i
          rw [hmod, hqe] at hi
          by_cases hij : i = j
          · subst hij
            simp only [Pi.add_apply, Pi.neg_apply, Pi.single_eq_same] at hi ⊢
            rw [hi]
            simp [sub_eq_add_neg]
          · simp only [Pi.add_apply, Pi.neg_apply, Pi.single_eq_of_ne hij, Matrix.mulVec_zero] at hi ⊢
            rw [hi]
            simp
      obtain ⟨x, hx0, hxfix⟩ := exists_fixed_of_ne_top hF _ B hBM hne
      exact hx0 (hfix x fun y hy => hxfix _ ⟨y, hy, rfl⟩)
    intro a
    have : a ∈ B := by rw [hB]; trivial
    exact this
  intro q hq
  obtain ⟨h₀, hh₀, e₀⟩ := hcoord 0 (Multiplicative.toAdd (β ⟨q, hq⟩) 0)
  obtain ⟨h₁, hh₁, e₁⟩ := hcoord 1 (Multiplicative.toAdd (β ⟨q, hq⟩) 1)
  have hsum : β (h₀ * h₁) = β ⟨q, hq⟩ := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, e₀, e₁]
    funext i
    fin_cases i <;> simp
  have hmem : (h₀ * h₁)⁻¹ * (⟨q, hq⟩ : ↥Q) ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsum, inv_mul_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at hmem
  refine ⟨((h₀ * h₁ : ↥Q) : G), H.mul_mem hh₀ hh₁, _, hmem, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

end Case3

end SBd7

end CFSG.Quasithin
