module

public import CFSG.Quasithin.Background.G10Clifford

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace G11

theorem exists_eq_span_singleton_of_finrank_le_one {S : Submodule (ZMod 2) V}
    (h : Module.finrank (ZMod 2) ↥S ≤ 1) : ∃ c : V, S = Submodule.span (ZMod 2) {c} := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h
  refine ⟨(v : V), le_antisymm (fun w hw => ?_) (Submodule.span_le.2 (by simp))⟩
  obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
  exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩

namespace G108Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem g10_14 (h12 : G1012Concl Γ v₁ W X L) : G1014Concl B Γ v₁ W X L := by
  intro I hI hv x hxN hx1 hnot
  obtain ⟨h, hh, hnot⟩ := hnot
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hxX : x ∈ X := hxN.1
  have hxI : conjSub x I = I := hxN.2
  have hxmem : ∀ u ∈ I, x u ∈ I := fun u hu => by
    rw [← hxI]
    exact apply_mem_conjSub hu
  have hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have h2v : ∀ w : V, w + w = 0 := fun w => by
    rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hnontriv : ∃ u ∈ I, x u ≠ u := by
    by_contra hcon
    have hcon' : ∀ u ∈ I, x u = u := by
      intro u hu
      by_contra hne
      exact hcon ⟨u, hu, hne⟩
    apply hnot
    have hmemH : x * h * x⁻¹ * h⁻¹ ∈ normalClosure Γ L :=
      (normalClosure Γ L).mul_mem
        (normalClosure_normal Γ L x (hyp.X_le hxX) h hh) ((normalClosure Γ L).inv_mem hh)
    refine ⟨hmemH, fun u hu => ?_⟩
    have h1 : h⁻¹ u ∈ I := hirr.1 h⁻¹ ((normalClosure Γ L).inv_mem hh) u hu
    have h2 : x⁻¹ (h⁻¹ u) = h⁻¹ u := by
      show x.symm (h⁻¹ u) = h⁻¹ u
      rw [LinearEquiv.symm_apply_eq]
      exact (hcon' _ h1).symm
    have e : (x * h * x⁻¹ * h⁻¹ : GLV V) u = x (h (x⁻¹ (h⁻¹ u))) := rfl
    rw [e, h2]
    have : h (h⁻¹ u) = u := by simp
    rw [this]
    exact hcon' u hu
  obtain ⟨c, hc⟩ := exists_eq_span_singleton_of_finrank_le_one (h12 I hI hv).1
  have hcomm : ∀ i ∈ I, i ∈ perp B v₁ → x i - i ∈ I ⊓ W := by
    intro i hi hperp
    exact ⟨I.sub_mem (hxmem i hi) hi, hyp.commutator_le x hxX i hperp⟩
  by_cases hI1 : I ≤ perp B v₁
  ·
    left
    refine ⟨hI1, c, hc, fun u hu => ?_, hnontriv⟩
    have := hcomm u hu (hI1 hu)
    rwa [hc] at this
  · right
    have hI1' : ∃ i₀ ∈ I, i₀ ∉ perp B v₁ := by
      by_contra hcon
      apply hI1
      intro u hu
      by_contra hu'
      exact hcon ⟨u, hu, hu'⟩
    obtain ⟨i₀, hi₀, hi₀p⟩ := hI1'
    have hBi₀ : B v₁ i₀ = 1 := by
      have : B v₁ i₀ ≠ 0 := fun h0 => hi₀p (LinearMap.mem_ker.2 h0)
      rcases hc2 (B v₁ i₀) with h0 | h1
      · exact absurd h0 this
      · exact h1
    have hsplit : ∀ u ∈ I, ∃ p ∈ I ⊓ perp B v₁, ∃ c₀ : ZMod 2, u = p + c₀ • i₀ := by
      intro u hu
      refine ⟨u - (B v₁ u) • i₀, ⟨I.sub_mem hu (I.smul_mem _ hi₀), ?_⟩, B v₁ u, by abel⟩
      rw [SetLike.mem_coe, perp, LinearMap.mem_ker]
      rw [map_sub, map_smul, hBi₀, smul_eq_mul, mul_one, sub_self]
    by_cases h2a : ∀ i ∈ I ⊓ perp B v₁, x i = i
    ·
      left
      refine ⟨hI1, ⟨x i₀ - i₀, ?_, hnontriv⟩, ?_⟩
      · intro u hu
        obtain ⟨p, hp, c₀, rfl⟩ := hsplit u hu
        have hxp := h2a p hp
        have : x (p + c₀ • i₀) - (p + c₀ • i₀) = c₀ • (x i₀ - i₀) := by
          rw [map_add, map_smul, hxp, smul_sub]
          abel
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · intro i hi
        constructor
        · intro hxi
          by_contra hip
          have hBi : B v₁ i = 1 := by
            have : B v₁ i ≠ 0 := fun h0 => hip (LinearMap.mem_ker.2 h0)
            rcases hc2 (B v₁ i) with h0 | h1
            · exact absurd h0 this
            · exact h1
          apply absurd hnontriv
          push Not
          intro u hu
          have hsplit' : ∃ p ∈ I ⊓ perp B v₁, ∃ c₀ : ZMod 2, u = p + c₀ • i := by
            refine ⟨u - (B v₁ u) • i, ⟨I.sub_mem hu (I.smul_mem _ hi), ?_⟩, B v₁ u, by abel⟩
            rw [SetLike.mem_coe, perp, LinearMap.mem_ker]
            rw [map_sub, map_smul, hBi, smul_eq_mul, mul_one, sub_self]
          obtain ⟨p, hp, c₀, rfl⟩ := hsplit'
          rw [map_add, map_smul, h2a p hp, hxi]
        · intro hip
          exact h2a i ⟨hi, hip⟩
    ·
      right
      push Not at h2a
      obtain ⟨i₁, hi₁, hxi₁⟩ := h2a
      have hc₁mem : x i₁ - i₁ ∈ I ⊓ W := hcomm i₁ hi₁.1 hi₁.2
      have hc₁ne : x i₁ - i₁ ≠ 0 := fun h0 => hxi₁ (sub_eq_zero.1 h0)
      have hIW : I ⊓ W = Submodule.span (ZMod 2) {x i₁ - i₁} := by
        refine le_antisymm (fun w hw => ?_) (Submodule.span_le.2 (by simpa using hc₁mem))
        rw [hc] at hw hc₁mem
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hw
        obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hc₁mem
        rcases hc2 a with rfl | rfl
        · rw [zero_smul] at ha
          rw [← ha]
          exact Submodule.zero_mem _
        · rcases hc2 b with rfl | rfl
          · rw [zero_smul] at hb
            exact absurd hb.symm hc₁ne
          · rw [one_smul] at ha hb
            rw [← ha, hb]
            exact Submodule.mem_span_singleton_self _
      refine ⟨hI1, ?_, x i₁ - i₁, hIW, fun u hu => ?_, ⟨i₁, hi₁, hxi₁⟩⟩
      ·
        have hle : commSpace (Subgroup.zpowers x) I ≤
            Submodule.span (ZMod 2) ({x i₁ - i₁, x i₀ - i₀} : Set V) := by
          refine commSpace_le_iff.2 fun k hk u hu => ?_
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
          have hxx : x ^ n = 1 ∨ x ^ n = x := by
            have hsq : x * x = 1 := hyp.X_sq x hxX
            have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hsq
            rcases Int.emod_two_eq_zero_or_one n with h0 | h1
            · left
              have : n = 2 * (n / 2) := by omega
              rw [this, zpow_mul]
              simp [hx2]
            · right
              have : n = 2 * (n / 2) + 1 := by omega
              rw [this, zpow_add, zpow_mul]
              simp [hx2]
          rcases hxx with h1 | h1
          · rw [h1]
            simp
          · rw [h1]
            obtain ⟨p, hp, c₀, rfl⟩ := hsplit u hu
            have hpW := hcomm p hp.1 hp.2
            have : x (p + c₀ • i₀) - (p + c₀ • i₀) = (x p - p) + c₀ • (x i₀ - i₀) := by
              rw [map_add, map_smul, smul_sub]
              abel
            rw [this]
            refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
            · have hpW' : x p - p ∈ Submodule.span (ZMod 2) {x i₁ - i₁} := hIW ▸ hpW
              exact Submodule.span_mono (by simp) hpW'
            · exact Submodule.subset_span (by simp)
        calc Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers x) I)
            ≤ Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) ({x i₁ - i₁, x i₀ - i₀} : Set V)) :=
              Submodule.finrank_mono hle
          _ ≤ 2 := by
              classical
              have := finrank_span_finset_le_card (R := ZMod 2)
                ({x i₁ - i₁, x i₀ - i₀} : Finset V)
              simp only [Finset.coe_insert, Finset.coe_singleton] at this
              exact this.trans (Finset.card_le_two)
      · have := hcomm u hu.1 hu.2
        rw [hIW] at this
        exact this

end G108Hyp

theorem g10_14 (h12 : G1012Stmt) : G1014Stmt :=
  fun V _ _ _ B Γ v₁ W X X₀ L hyp => hyp.g10_14 (h12 V B Γ v₁ W X X₀ L hyp)

end G11

end CFSG.Quasithin
