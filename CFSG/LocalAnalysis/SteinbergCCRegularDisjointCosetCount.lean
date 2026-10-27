module

public import CFSG.LocalAnalysis.SteinbergCCRegularComplementCovariance
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis

theorem binary_regular_disjoint_subspace_coset_count {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (U R : Submodule (ZMod 2) V)
    (hUR : IsCompl U R) (hn : 3 ≤ Module.finrank (ZMod 2) U)
    (hm : 1 ≤ Module.finrank (ZMod 2) R) (Δ : Set (Submodule (ZMod 2) V)) (hRΔ : R ∈ Δ)
    (hdimΔ : ∀ Q ∈ Δ, Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) R)
    (hdisj : ∀ Q ∈ Δ, ∀ Z ∈ Δ, Q ≠ Z → Q ⊓ Z = ⊥) (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hHΔ : ∀ h ∈ H, ∀ Q ∈ Δ, Q.map (h : V →ₗ[ZMod 2] V) ∈ Δ)
    (hHU : ∀ h ∈ H, U.map (h : V →ₗ[ZMod 2] V) = U) (hHR : ∀ h ∈ H, ∀ r ∈ R, h r = r)
    (hreg : ∀ u ∈ U, ∀ v ∈ U, u ≠ 0 → v ≠ 0 → ∃! h, h ∈ H ∧ h u = v) :
    let A := {Q ∈ Δ | Q ⊓ U = ⊥}
    let B := {Q ∈ Δ | Q ≤ U}
    (∀ Q ∈ Δ, Q ≤ U ∨ IsCompl Q U) ∧
      (Δ = A ∪ B ∧ Disjoint A B) ∧
      (∀ Q ∈ Δ, Q ≠ R → ¬ Q ≤ U → ∀ h ∈ H, Q.map (h : V →ₗ[ZMod 2] V) = Q → h = 1) ∧
      (A = {R} ∨
        (A.ncard = 2 ^ Module.finrank (ZMod 2) U ∧
          (∀ h ∈ H, ∀ Q ∈ A \ {R}, Q.map (h : V →ₗ[ZMod 2] V) ∈ A \ {R}) ∧
          (∀ Q ∈ A \ {R}, ∀ Z ∈ A \ {R}, ∃! h, h ∈ H ∧ Q.map (h : V →ₗ[ZMod 2] V) = Z) ∧
          (∀ Q ∈ A, (∃ v ∈ Q, v ≠ 0) ∧ ∀ v ∈ Q, v ≠ 0 → v ∉ U) ∧
          (∀ v : V, v ∉ U → ∃! Q, Q ∈ A ∧ v ∈ Q))) ∧
      (B.Nonempty →
        (∀ h ∈ H, ∀ Q ∈ B, Q.map (h : V →ₗ[ZMod 2] V) ∈ B) ∧
        (∀ Q ∈ B, ∀ Z ∈ B, ∃ h ∈ H, Q.map (h : V →ₗ[ZMod 2] V) = Z) ∧
        (∀ Q ∈ B, (∃ v ∈ Q, v ≠ 0) ∧ ∀ v ∈ Q, v ≠ 0 → v ∈ U) ∧
        (∀ v ∈ U, v ≠ 0 → ∃! Q, Q ∈ B ∧ v ∈ Q) ∧
        B.ncard * (2 ^ Module.finrank (ZMod 2) R - 1) = 2 ^ Module.finrank (ZMod 2) U - 1 ∧
        B.ncard = (2 ^ Module.finrank (ZMod 2) U - 1) / (2 ^ Module.finrank (ZMod 2) R - 1) ∧
        Odd B.ncard ∧ 0 < B.ncard) := by
  intro A B
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun Q : Submodule (ZMod 2) V => (Q : Set V)) SetLike.coe_injective
  obtain ⟨hcard, hkr⟩ := regular_complement_card_ker_range U R hUR (by omega) H hHU hHR hreg
  have hmem_map : ∀ (h : V ≃ₗ[ZMod 2] V) (Q : Submodule (ZMod 2) V) (x : V), x ∈ Q →
      h x ∈ Q.map (h : V →ₗ[ZMod 2] V) := fun h Q x hx => Submodule.mem_map_of_mem hx
  have hHUmem : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U := by
    intro h hh u hu
    rw [← hHU h hh]
    exact hmem_map h U u hu
  have hHUnot : ∀ h ∈ H, ∀ v : V, v ∉ U → h v ∉ U := by
    intro h hh v hv hhv
    apply hv
    have := hHUmem h⁻¹ (H.inv_mem hh) (h v) hhv
    rwa [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at this
  have hmapR : ∀ h ∈ H, R.map (h : V →ₗ[ZMod 2] V) = R := by
    intro h hh
    ext v
    simp only [Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hHR h hh w hw]
      exact hw
    · intro hv
      exact ⟨v, hv, hHR h hh v hv⟩
  have hdiffU : ∀ h ∈ H, ∀ x : V, h x - x ∈ U := by
    intro h hh x
    by_cases hne : h = 1
    · rw [hne, LinearEquiv.coe_one, id, sub_self]
      exact U.zero_mem
    · rw [← (hkr h hh hne).2]
      exact ⟨x, rfl⟩
  have hQcard : ∀ Q : Submodule (ZMod 2) V, Nat.card Q = 2 ^ Module.finrank (ZMod 2) Q := by
    intro Q
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Q)
    rwa [Nat.card_zmod] at h
  have hne_bot : ∀ Q ∈ Δ, Q ≠ ⊥ := by
    intro Q hQ hQb
    have := hdimΔ Q hQ
    rw [hQb, finrank_bot] at this
    omega
  have hdisj' : ∀ Q ∈ Δ, ∀ Z ∈ Δ, ∀ x : V, x ∈ Q → x ∈ Z → x ≠ 0 → Q = Z := by
    intro Q hQ Z hZ x hxQ hxZ hx0
    by_contra hne
    have hx : x ∈ Q ⊓ Z := ⟨hxQ, hxZ⟩
    rw [hdisj Q hQ Z hZ hne] at hx
    exact hx0 ((Submodule.mem_bot _).mp hx)
  have hexists_ne : ∀ Q ∈ Δ, ∃ v ∈ Q, v ≠ (0 : V) := fun Q hQ =>
    Submodule.exists_mem_ne_zero_of_ne_bot (hne_bot Q hQ)
  have h8 : 8 ≤ 2 ^ Module.finrank (ZMod 2) U :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hn
  have hmul_stab : ∀ Q : Submodule (ZMod 2) V, ∀ h h' : V ≃ₗ[ZMod 2] V,
      Q.map (h : V →ₗ[ZMod 2] V) = Q.map (h' : V →ₗ[ZMod 2] V) →
      Q.map ((h'⁻¹ * h : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = Q := by
    intro Q h h' hQ
    rw [submodule_map_linearEquiv_mul, hQ, ← submodule_map_linearEquiv_mul, inv_mul_cancel,
      submodule_map_linearEquiv_one]
  have hstab : ∀ Q ∈ Δ, Q ≠ R → ¬ Q ≤ U → ∀ h ∈ H,
      Q.map (h : V →ₗ[ZMod 2] V) = Q → h = 1 := by
    intro Q hQ hQR hQU h hh hhQ
    by_contra hne
    apply hQU
    have hhQmem : ∀ x ∈ Q, h x ∈ Q := fun x hx => hhQ ▸ hmem_map h Q x hx
    set φ : V →ₗ[ZMod 2] V := (h : V →ₗ[ZMod 2] V) - LinearMap.id with hφ
    have hφx : ∀ x : V, φ x = h x - x := fun x => by
      rw [hφ, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
    have hinj : Function.Injective (φ.domRestrict Q) := by
      refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
      have hxker : (x : V) ∈ LinearMap.ker φ := hx
      rw [(hkr h hh hne).1] at hxker
      have hxQR : (x : V) ∈ Q ⊓ R := ⟨x.2, hxker⟩
      rw [hdisj Q hQ R hRΔ hQR] at hxQR
      exact Subtype.ext ((Submodule.mem_bot _).mp hxQR)
    have hrange_le : LinearMap.range (φ.domRestrict Q) ≤ Q := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.domRestrict_apply, hφx]
      exact Q.sub_mem (hhQmem x x.2) x.2
    have hrange_eq : LinearMap.range (φ.domRestrict Q) = Q :=
      Submodule.eq_of_le_of_finrank_eq hrange_le (LinearMap.finrank_range_of_inj hinj)
    rw [← hrange_eq]
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.domRestrict_apply, hφx]
    exact hdiffU h hh x
  have hinf : ∀ Q ∈ Δ, Q ≠ R → ¬ Q ≤ U → Q ⊓ U = ⊥ := by
    intro Q hQ hQR hQU
    obtain ⟨y, hyQ, hyU⟩ := Set.not_subset.mp hQU
    let F : H × (Q ⊓ U : Submodule (ZMod 2) V) → U := fun p =>
      ⟨(p.1 : V ≃ₗ[ZMod 2] V) (y + p.2) - y, by
        have hsplit : (p.1 : V ≃ₗ[ZMod 2] V) (y + p.2) - y =
            ((p.1 : V ≃ₗ[ZMod 2] V) (y + p.2) - (y + p.2)) + p.2 := by abel
        rw [hsplit]
        exact U.add_mem (hdiffU p.1 p.1.2 _) p.2.2.2⟩
    have hFinj : Function.Injective F := by
      rintro ⟨h, w⟩ ⟨h', w'⟩ hF
      have hF' : (h : V ≃ₗ[ZMod 2] V) (y + w) = (h' : V ≃ₗ[ZMod 2] V) (y + w') :=
        sub_left_injective (congrArg Subtype.val hF)
      by_cases hhh : h = h'
      · subst hhh
        have hww : (w : V) = w' := add_left_cancel ((h : V ≃ₗ[ZMod 2] V).injective hF')
        rw [Subtype.ext hww]
      · exfalso
        have hyw : y + (w : V) ∉ U := fun hmem => hyU (by
          have hsub := U.sub_mem hmem w.2.2
          rwa [add_sub_cancel_right] at hsub)
        have hz0 : (h : V ≃ₗ[ZMod 2] V) (y + w) ≠ 0 := fun h0 =>
          hHUnot h h.2 _ hyw (h0 ▸ U.zero_mem)
        have hQQ : Q.map ((h : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) =
            Q.map ((h' : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) := by
          refine hdisj' _ (hHΔ h h.2 Q hQ) _ (hHΔ h' h'.2 Q hQ) _
            (hmem_map _ Q _ (Q.add_mem hyQ w.2.1)) ?_ hz0
          rw [hF']
          exact hmem_map _ Q _ (Q.add_mem hyQ w'.2.1)
        have h1 := hstab Q hQ hQR hQU _ (H.mul_mem (H.inv_mem h'.2) h.2) (hmul_stab Q _ _ hQQ)
        exact hhh (Subtype.ext (inv_mul_eq_one.mp h1).symm)
    have hle := Nat.card_le_card_of_injective F hFinj
    rw [Nat.card_prod, hcard, hQcard (Q ⊓ U), hQcard U] at hle
    have hd : Module.finrank (ZMod 2) (Q ⊓ U : Submodule (ZMod 2) V) = 0 := by
      by_contra hd0
      have h2 : 2 ≤ 2 ^ Module.finrank (ZMod 2) (Q ⊓ U : Submodule (ZMod 2) V) :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hd0)
      have h3 := Nat.mul_le_mul_left (2 ^ Module.finrank (ZMod 2) U - 1) h2
      omega
    exact Submodule.finrank_eq_zero.mp hd
  have hsum_dim := Submodule.finrank_add_eq_of_isCompl hUR
  have hcompl : ∀ Q ∈ Δ, Q ⊓ U = ⊥ → IsCompl Q U := by
    intro Q hQ hQU
    refine ⟨disjoint_iff.mpr hQU, codisjoint_iff.mpr (Submodule.eq_top_of_finrank_eq ?_)⟩
    have h := Submodule.finrank_sup_add_finrank_inf_eq Q U
    rw [hQU, finrank_bot, add_zero, hdimΔ Q hQ] at h
    omega
  have ha : ∀ Q ∈ Δ, Q ≤ U ∨ IsCompl Q U := by
    intro Q hQ
    by_cases hQU : Q ≤ U
    · exact Or.inl hQU
    · right
      by_cases hQR : Q = R
      · rw [hQR]
        exact hUR.symm
      · exact hcompl Q hQ (hinf Q hQ hQR hQU)
  have hA_notU : ∀ Q ∈ A, ¬ Q ≤ U := fun Q hQ hle =>
    hne_bot Q hQ.1 (by rw [← inf_eq_left.mpr hle]; exact hQ.2)
  have hRA : R ∈ A := ⟨hRΔ, hUR.symm.inf_eq_bot⟩
  have hAB : Δ = A ∪ B ∧ Disjoint A B := by
    refine ⟨?_, Set.disjoint_left.mpr fun Q hQA hQB => hA_notU Q hQA hQB.2⟩
    ext Q
    constructor
    · intro hQ
      rcases ha Q hQ with h | h
      · exact Or.inr ⟨hQ, h⟩
      · exact Or.inl ⟨hQ, h.inf_eq_bot⟩
    · rintro (⟨hQ, -⟩ | ⟨hQ, -⟩) <;> exact hQ
  have hAcount : ∀ v : V, v ∉ U →
      A.ncard ≤ 2 ^ Module.finrank (ZMod 2) U ∧
        (A.ncard = 2 ^ Module.finrank (ZMod 2) U → ∃ Q ∈ A, v ∈ Q) := by
    intro v hv
    have hex : ∀ Q ∈ A, ∃ w ∈ Q, v - w ∈ U := by
      intro Q hQ
      have hvQU : v ∈ Q ⊔ U := by
        rw [(hcompl Q hQ.1 hQ.2).sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hvQU
      exact ⟨w, hw, by rwa [add_sub_cancel_left]⟩
    let f : Submodule (ZMod 2) V → V := fun Q =>
      if h : ∃ w ∈ Q, v - w ∈ U then h.choose else 0
    have hf : ∀ Q ∈ A, f Q ∈ Q ∧ v - f Q ∈ U := by
      intro Q hQ
      have h := hex Q hQ
      simp only [f, h, ↓reduceDIte]
      exact h.choose_spec
    let S : Set V := {w | v - w ∈ U}
    have hmaps : Set.MapsTo f A S := fun Q hQ => (hf Q hQ).2
    have hinjA : Set.InjOn f A := by
      intro Q hQ Z hZ hQZ
      refine hdisj' Q hQ.1 Z hZ.1 (f Q) (hf Q hQ).1 (hQZ ▸ (hf Z hZ).1) fun h0 => hv ?_
      have h1 := (hf Q hQ).2
      rwa [h0, sub_zero] at h1
    have hScard : S.ncard = 2 ^ Module.finrank (ZMod 2) U := by
      have hSimg : S = (fun u => v - u) '' (U : Set V) := by
        ext w
        constructor
        · intro hw
          exact ⟨v - w, hw, sub_sub_cancel v w⟩
        · rintro ⟨u, hu, rfl⟩
          show v - (v - u) ∈ U
          rw [sub_sub_cancel]
          exact hu
      rw [hSimg, Set.ncard_image_of_injective _ sub_right_injective, ← Nat.card_coe_set_eq]
      exact hQcard U
    refine ⟨hScard ▸ Set.ncard_le_ncard_of_injOn f hmaps hinjA, fun hAq => ?_⟩
    have himg : f '' A = S := Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.mpr hmaps)
      (by rw [hinjA.ncard_image, hAq, hScard])
    have hvS : v ∈ f '' A := by
      rw [himg]
      show v - v ∈ U
      rw [sub_self]
      exact U.zero_mem
    obtain ⟨Q, hQ, hQv⟩ := hvS
    exact ⟨Q, hQ, hQv ▸ (hf Q hQ).1⟩
  have hdA : A = {R} ∨
      (A.ncard = 2 ^ Module.finrank (ZMod 2) U ∧
        (∀ h ∈ H, ∀ Q ∈ A \ {R}, Q.map (h : V →ₗ[ZMod 2] V) ∈ A \ {R}) ∧
        (∀ Q ∈ A \ {R}, ∀ Z ∈ A \ {R}, ∃! h, h ∈ H ∧ Q.map (h : V →ₗ[ZMod 2] V) = Z) ∧
        (∀ Q ∈ A, (∃ v ∈ Q, v ≠ 0) ∧ ∀ v ∈ Q, v ≠ 0 → v ∉ U) ∧
        (∀ v : V, v ∉ U → ∃! Q, Q ∈ A ∧ v ∈ Q)) := by
    by_cases hAR : A = {R}
    · exact Or.inl hAR
    right
    obtain ⟨Q₁, hQ₁A, hQ₁R⟩ : ∃ Q ∈ A, Q ≠ R := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      exact hAR (Set.eq_singleton_iff_unique_mem.mpr ⟨hRA, hcon⟩)
    have hmapA : ∀ h ∈ H, ∀ Q ∈ A, Q ≠ R → Q.map (h : V →ₗ[ZMod 2] V) ∈ A \ {R} := by
      intro h hh Q hQ hQR
      refine ⟨⟨hHΔ h hh Q hQ.1, ?_⟩, fun hQhR => hQR ?_⟩
      · rw [eq_bot_iff]
        rintro _ ⟨⟨x, hx, rfl⟩, hxU⟩
        have hxU' : x ∈ U := by
          by_contra hxU''
          exact hHUnot h hh x hxU'' hxU
        have hx0 : x ∈ Q ⊓ U := ⟨hx, hxU'⟩
        rw [hQ.2] at hx0
        rw [(Submodule.mem_bot _).mp hx0, map_zero]
        exact Submodule.zero_mem _
      · have h1 := congrArg (Submodule.map ((h⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)) hQhR
        rw [← submodule_map_linearEquiv_mul, inv_mul_cancel, submodule_map_linearEquiv_one,
          hmapR _ (H.inv_mem hh)] at h1
        exact h1
    set O : Set (Submodule (ZMod 2) V) :=
      (fun h : V ≃ₗ[ZMod 2] V => Q₁.map (h : V →ₗ[ZMod 2] V)) '' (H : Set (V ≃ₗ[ZMod 2] V))
      with hO
    have hOsub : O ⊆ A \ {R} := by
      rintro _ ⟨h, hh, rfl⟩
      exact hmapA h hh Q₁ hQ₁A hQ₁R
    have hOinj : Set.InjOn (fun h : V ≃ₗ[ZMod 2] V => Q₁.map (h : V →ₗ[ZMod 2] V))
        (H : Set (V ≃ₗ[ZMod 2] V)) := by
      intro h hh h' hh' hQ
      have h1 := hstab Q₁ hQ₁A.1 hQ₁R (hA_notU Q₁ hQ₁A) _ (H.mul_mem (H.inv_mem hh') hh)
        (hmul_stab Q₁ h h' hQ)
      exact (inv_mul_eq_one.mp h1).symm
    have hOcard : O.ncard = 2 ^ Module.finrank (ZMod 2) U - 1 := by
      rw [hO, hOinj.ncard_image, ← Nat.card_coe_set_eq]
      exact hcard
    have hRO : R ∉ O := fun hRO => (hOsub hRO).2 rfl
    have hinsert_sub : insert R O ⊆ A := Set.insert_subset hRA fun Q hQ => (hOsub hQ).1
    have hinsert_card : (insert R O).ncard = 2 ^ Module.finrank (ZMod 2) U := by
      rw [Set.ncard_insert_of_notMem hRO, hOcard]
      omega
    obtain ⟨r, hrR, hr0⟩ := hexists_ne R hRΔ
    have hrU : r ∉ U := fun hrU => hr0 (by
      have hrUR : r ∈ U ⊓ R := ⟨hrU, hrR⟩
      rw [hUR.inf_eq_bot] at hrUR
      exact (Submodule.mem_bot _).mp hrUR)
    have hAeq : insert R O = A :=
      Set.eq_of_subset_of_ncard_le hinsert_sub (by rw [hinsert_card]; exact (hAcount r hrU).1)
    have hAcard : A.ncard = 2 ^ Module.finrank (ZMod 2) U := by rw [← hAeq, hinsert_card]
    have hAO : A \ {R} = O := by
      rw [← hAeq, Set.insert_sdiff_of_mem _ (Set.mem_singleton R),
        Set.sdiff_singleton_eq_self hRO]
    refine ⟨hAcard, fun h hh Q hQ => hmapA h hh Q hQ.1 hQ.2, ?_, ?_, ?_⟩
    ·
      intro Q hQ Z hZ
      rw [hAO] at hQ hZ
      obtain ⟨h₁, hh₁, rfl⟩ := hQ
      obtain ⟨h₂, hh₂, rfl⟩ := hZ
      refine ⟨h₂ * h₁⁻¹, ⟨H.mul_mem hh₂ (H.inv_mem hh₁), ?_⟩, ?_⟩
      · rw [← submodule_map_linearEquiv_mul, mul_assoc, inv_mul_cancel, mul_one]
      · rintro h ⟨hh, hhQ⟩
        have hQ₁ : Q₁.map ((h * h₁ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) =
            Q₁.map (h₂ : V →ₗ[ZMod 2] V) := by
          rw [submodule_map_linearEquiv_mul]
          exact hhQ
        have h1 := hOinj (H.mul_mem hh hh₁) hh₂ hQ₁
        rw [← h1, mul_inv_cancel_right]
    · intro Q hQ
      refine ⟨hexists_ne Q hQ.1, fun v hvQ hv0 hvU => hv0 ?_⟩
      have hv : v ∈ Q ⊓ U := ⟨hvQ, hvU⟩
      rw [hQ.2] at hv
      exact (Submodule.mem_bot _).mp hv
    · intro v hv
      obtain ⟨Q, hQ, hvQ⟩ := (hAcount v hv).2 hAcard
      refine ⟨Q, ⟨hQ, hvQ⟩, fun Z ⟨hZ, hvZ⟩ => ?_⟩
      exact hdisj' Z hZ.1 Q hQ.1 v hvZ hvQ (fun h0 => hv (h0 ▸ U.zero_mem))
  have heB : B.Nonempty →
      (∀ h ∈ H, ∀ Q ∈ B, Q.map (h : V →ₗ[ZMod 2] V) ∈ B) ∧
      (∀ Q ∈ B, ∀ Z ∈ B, ∃ h ∈ H, Q.map (h : V →ₗ[ZMod 2] V) = Z) ∧
      (∀ Q ∈ B, (∃ v ∈ Q, v ≠ 0) ∧ ∀ v ∈ Q, v ≠ 0 → v ∈ U) ∧
      (∀ v ∈ U, v ≠ 0 → ∃! Q, Q ∈ B ∧ v ∈ Q) ∧
      B.ncard * (2 ^ Module.finrank (ZMod 2) R - 1) = 2 ^ Module.finrank (ZMod 2) U - 1 ∧
      B.ncard = (2 ^ Module.finrank (ZMod 2) U - 1) / (2 ^ Module.finrank (ZMod 2) R - 1) ∧
      Odd B.ncard ∧ 0 < B.ncard := by
    rintro ⟨Q₀, hQ₀⟩
    obtain ⟨u, huQ₀, hu0⟩ := hexists_ne Q₀ hQ₀.1
    have huU : u ∈ U := hQ₀.2 huQ₀
    have hmapB : ∀ h ∈ H, ∀ Q ∈ B, Q.map (h : V →ₗ[ZMod 2] V) ∈ B := by
      intro h hh Q hQ
      refine ⟨hHΔ h hh Q hQ.1, ?_⟩
      rw [← hHU h hh]
      exact Submodule.map_mono hQ.2
    have hcover : ∀ v ∈ U, v ≠ 0 → ∃ h ∈ H, v ∈ Q₀.map (h : V →ₗ[ZMod 2] V) := by
      intro v hvU hv0
      obtain ⟨h, ⟨hh, hhu⟩, -⟩ := hreg u huU v hvU hu0 hv0
      exact ⟨h, hh, hhu ▸ hmem_map h Q₀ u huQ₀⟩
    have horbit : ∀ Q ∈ B, ∃ h ∈ H, Q₀.map (h : V →ₗ[ZMod 2] V) = Q := by
      intro Q hQ
      obtain ⟨v, hvQ, hv0⟩ := hexists_ne Q hQ.1
      obtain ⟨h, hh, hvh⟩ := hcover v (hQ.2 hvQ) hv0
      exact ⟨h, hh, hdisj' _ (hHΔ h hh Q₀ hQ₀.1) Q hQ.1 v hvh hvQ hv0⟩
    have htransB : ∀ Q ∈ B, ∀ Z ∈ B, ∃ h ∈ H, Q.map (h : V →ₗ[ZMod 2] V) = Z := by
      intro Q hQ Z hZ
      obtain ⟨h₁, hh₁, rfl⟩ := horbit Q hQ
      obtain ⟨h₂, hh₂, rfl⟩ := horbit Z hZ
      refine ⟨h₂ * h₁⁻¹, H.mul_mem hh₂ (H.inv_mem hh₁), ?_⟩
      rw [← submodule_map_linearEquiv_mul, mul_assoc, inv_mul_cancel, mul_one]
    have hpartB : ∀ v ∈ U, v ≠ 0 → ∃! Q, Q ∈ B ∧ v ∈ Q := by
      intro v hvU hv0
      obtain ⟨h, hh, hvh⟩ := hcover v hvU hv0
      refine ⟨_, ⟨hmapB h hh Q₀ hQ₀, hvh⟩, fun Z ⟨hZ, hvZ⟩ => ?_⟩
      exact hdisj' Z hZ.1 _ (hHΔ h hh Q₀ hQ₀.1) v hvZ hvh hv0
    have : Fintype V := Fintype.ofFinite V
    have hBfin : B.Finite := Set.toFinite B
    have hcount : B.ncard * (2 ^ Module.finrank (ZMod 2) R - 1) =
        2 ^ Module.finrank (ZMod 2) U - 1 := by
      let t : Submodule (ZMod 2) V → Finset V := fun Q =>
        Finset.univ.filter fun v => v ∈ Q ∧ v ≠ 0
      have htcard : ∀ Q : Submodule (ZMod 2) V,
          (t Q).card = 2 ^ Module.finrank (ZMod 2) Q - 1 := by
        intro Q
        have hteq : t Q = (Finset.univ.filter fun v => v ∈ Q).erase 0 := by
          ext v
          simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          exact and_comm
        rw [hteq, Finset.card_erase_of_mem (by simp), ← Fintype.card_subtype,
          ← Nat.card_eq_fintype_card, hQcard Q]
      have hunion : hBfin.toFinset.biUnion t = t U := by
        ext v
        simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, t, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨Q, hQ, hvQ, hv0⟩
          exact ⟨hQ.2 hvQ, hv0⟩
        · rintro ⟨hvU, hv0⟩
          obtain ⟨Q, ⟨hQ, hvQ⟩, -⟩ := hpartB v hvU hv0
          exact ⟨Q, hQ, hvQ, hv0⟩
      have hpair : (hBfin.toFinset : Set (Submodule (ZMod 2) V)).PairwiseDisjoint t := by
        intro Q hQ Z hZ hQZ
        rw [Function.onFun, Finset.disjoint_left]
        intro v hvQ hvZ
        simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hvQ hvZ
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hQ hZ
        exact hQZ (hdisj' Q hQ.1 Z hZ.1 v hvQ.1 hvZ.1 hvQ.2)
      have h1 := Finset.card_biUnion hpair
      rw [hunion, htcard U, Finset.sum_congr rfl fun Q hQ => by
        rw [htcard Q, hdimΔ Q (hBfin.mem_toFinset.mp hQ).1], Finset.sum_const, smul_eq_mul,
        ← Set.ncard_eq_toFinset_card B hBfin] at h1
      exact h1.symm
    have hBpos : 0 < B.ncard := (Set.ncard_pos hBfin).mpr ⟨Q₀, hQ₀⟩
    have hpos : 0 < 2 ^ Module.finrank (ZMod 2) R - 1 := by
      have : 2 ≤ 2 ^ Module.finrank (ZMod 2) R :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hm
      omega
    have hodd : Odd (2 ^ Module.finrank (ZMod 2) U - 1) := by
      have heven : Even (2 ^ Module.finrank (ZMod 2) U) :=
        (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      obtain ⟨k, hk⟩ := heven
      exact ⟨k - 1, by omega⟩
    refine ⟨hmapB, htransB, fun Q hQ => ⟨hexists_ne Q hQ.1, fun v hvQ _ => hQ.2 hvQ⟩, hpartB,
      hcount, (Nat.div_eq_of_eq_mul_left hpos hcount.symm).symm, ?_, hBpos⟩
    rw [← hcount] at hodd
    exact (Nat.odd_mul.mp hodd).1
  exact ⟨ha, hAB, hstab, hdA, heB⟩

end CFSG.LocalAnalysis
