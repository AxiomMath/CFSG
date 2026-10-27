module

public import CFSG.Quasithin.Background.G10SixteenB
public import CFSG.Quasithin.Background.G10FifteenIso
public import CFSG.Quasithin.Background.G10FifteenNondegD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem A5_two_ne : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → σ ≠ 1 →
    ∃ x₁ x₂ : Fin 5 → ZMod 2, (∑ i, x₁ i = 0) ∧ (∑ i, x₂ i = 0) ∧
      permAct σ x₁ + x₁ ≠ 0 ∧ permAct σ x₂ + x₂ ≠ 0 ∧ permAct σ x₁ + x₁ ≠ permAct σ x₂ + x₂ := by
  decide +kernel

theorem card_permCore_five : Nat.card ↥(permCore 5) = 16 := by
  have e : ↥(permCore 5) ≃ {x : Fin 5 → ZMod 2 // ∑ i, x i = 0} :=
    Equiv.subtypeEquivRight fun x => Iff.rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

theorem finrank_eq_four_of_equiv_permCore [Finite V] (I : Submodule (ZMod 2) V)
    (e : ↥I ≃ₗ[ZMod 2] ↥(permCore 5)) : Module.finrank (ZMod 2) ↥I = 4 := by
  have h1 : Nat.card ↥I = 16 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_permCore_five
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥I), Nat.card_zmod] at h1
  have h2 : (2 : ℕ) ^ Module.finrank (ZMod 2) ↥I = 2 ^ 4 := by rw [h1]; norm_num
  exact Nat.pow_right_injective (le_refl 2) h2

theorem two_le_finrank_of_two_ne [Finite V] (S : Submodule (ZMod 2) V) {w₁ w₂ : V} (h₁ : w₁ ∈ S)
    (h₂ : w₂ ∈ S) (h₁0 : w₁ ≠ 0) (h₂0 : w₂ ≠ 0) (h12 : w₁ ≠ w₂) :
    2 ≤ Module.finrank (ZMod 2) ↥S := by
  by_contra hlt
  have hle : Module.finrank (ZMod 2) ↥S ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hle
  obtain ⟨c₁, hc₁⟩ := hv ⟨w₁, h₁⟩
  obtain ⟨c₂, hc₂⟩ := hv ⟨w₂, h₂⟩
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have e1 : c₁ • (v : V) = w₁ := congrArg Subtype.val hc₁
  have e2 : c₂ • (v : V) = w₂ := congrArg Subtype.val hc₂
  rcases hc c₁ with rfl | rfl
  · exact h₁0 (by rw [← e1, zero_smul])
  · rcases hc c₂ with rfl | rfl
    · exact h₂0 (by rw [← e2, zero_smul])
    · exact h12 (by rw [← e1, ← e2])

theorem mem_or_mul_mem_of_mem_sup_zpowers {G : Type*} [Group G] {A : Subgroup G} {x : G}
    (hx2 : x * x = 1) (hcomm : ∀ a ∈ A, a * x = x * a) {g : G}
    (hg : g ∈ A ⊔ Subgroup.zpowers x) : g ∈ A ∨ g * x ∈ A := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, g = a ∨ g = a * x}
      mul_mem' := by
        rintro g g' ⟨a, ha, hg⟩ ⟨a', ha', hg'⟩
        rcases hg with hg | hg <;> rcases hg' with hg' | hg'
        · exact ⟨a * a', A.mul_mem ha ha', Or.inl (by rw [hg, hg'])⟩
        · exact ⟨a * a', A.mul_mem ha ha', Or.inr (by rw [hg, hg']; group)⟩
        · refine ⟨a * a', A.mul_mem ha ha', Or.inr ?_⟩
          rw [hg, hg']
          calc a * x * a' = a * (x * a') := by group
            _ = a * (a' * x) := by rw [hcomm a' ha']
            _ = a * a' * x := by group
        · refine ⟨a * a', A.mul_mem ha ha', Or.inl ?_⟩
          rw [hg, hg']
          calc a * x * (a' * x) = a * (x * a') * x := by group
            _ = a * (a' * x) * x := by rw [hcomm a' ha']
            _ = a * a' * (x * x) := by group
            _ = a * a' := by rw [hx2, mul_one]
      one_mem' := ⟨1, A.one_mem, Or.inl rfl⟩
      inv_mem' := by
        rintro g ⟨a, ha, hg⟩
        rcases hg with hg | hg
        · exact ⟨a⁻¹, A.inv_mem ha, Or.inl (by rw [hg])⟩
        · refine ⟨a⁻¹, A.inv_mem ha, Or.inr ?_⟩
          rw [hg]
          calc (a * x)⁻¹ = x⁻¹ * a⁻¹ := by group
            _ = x * a⁻¹ := by rw [hxinv]
            _ = a⁻¹ * x := by
              have := hcomm a⁻¹ (A.inv_mem ha)
              exact this.symm }
  have hle : A ⊔ Subgroup.zpowers x ≤ S :=
    sup_le (fun a ha => ⟨a, ha, Or.inl rfl⟩)
      ((Subgroup.zpowers_le).2 ⟨1, A.one_mem, Or.inr (by group)⟩)
  obtain ⟨a, ha, h | h⟩ := hle hg
  · exact Or.inl (h ▸ ha)
  · right
    rw [h, mul_assoc, hx2, mul_one]
    exact ha


theorem two_le_finrank_raU_of_A5 [Finite V] {a l : GLV V} {I : Submodule (ZMod 2) V}
    (hIl : ∀ u ∈ I, l u ∈ I) (hal : ∀ u ∈ I, a u = l u) (σ : ↥(alternatingGroup (Fin 5)))
    (ψ : ↥I ≃ₗ[ZMod 2] ↥(permCore 5))
    (hψ : ∀ u w : ↥I, (w : V) = l (u : V) →
      (ψ w : Fin 5 → ZMod 2) = permAct (σ : Equiv.Perm (Fin 5)) (ψ u))
    (hσ : (σ : Equiv.Perm (Fin 5)) ≠ 1) : 2 ≤ Module.finrank (ZMod 2) ↥(raU a I) := by
  obtain ⟨x₁, x₂, hx₁, hx₂, hne₁, hne₂, hne₁₂⟩ := A5_two_ne _ (MonoidHom.mem_ker.1 σ.2) hσ
  obtain ⟨u₁, hu₁⟩ := ψ.surjective (⟨x₁, hx₁⟩ : ↥(permCore 5))
  obtain ⟨u₂, hu₂⟩ := ψ.surjective (⟨x₂, hx₂⟩ : ↥(permCore 5))
  have hu₁' : (ψ u₁ : Fin 5 → ZMod 2) = x₁ := congrArg Subtype.val hu₁
  have hu₂' : (ψ u₂ : Fin 5 → ZMod 2) = x₂ := congrArg Subtype.val hu₂
  let w₁ : ↥I := ⟨l (u₁ : V), hIl _ u₁.2⟩
  let w₂ : ↥I := ⟨l (u₂ : V), hIl _ u₂.2⟩
  have hw₁ : (ψ w₁ : Fin 5 → ZMod 2) = permAct (σ : Equiv.Perm (Fin 5)) x₁ := by
    rw [hψ u₁ w₁ rfl, hu₁']
  have hw₂ : (ψ w₂ : Fin 5 → ZMod 2) = permAct (σ : Equiv.Perm (Fin 5)) x₂ := by
    rw [hψ u₂ w₂ rfl, hu₂']
  have hv : ∀ u : ↥I, a (u : V) - (u : V) ∈ raU a I := fun u => ⟨(u : V), u.2, rfl⟩
  have hvw : ∀ (u w : ↥I), (w : V) = l (u : V) → a (u : V) - (u : V) = ((w + u : ↥I) : V) := by
    intro u w hw
    have hneg : -(u : V) = (u : V) := neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 _)
    rw [hal _ u.2, sub_eq_add_neg, hneg]
    show l (u : V) + (u : V) = (w : V) + (u : V)
    rw [hw]
  have hψadd : ∀ u w : ↥I, (ψ (w + u) : Fin 5 → ZMod 2) =
      (ψ w : Fin 5 → ZMod 2) + (ψ u : Fin 5 → ZMod 2) := fun u w => by
    rw [map_add]
    rfl
  refine two_le_finrank_of_two_ne (raU a I) (hv u₁) (hv u₂) ?_ ?_ ?_
  · intro h0
    rw [hvw u₁ w₁ rfl] at h0
    have h1 : w₁ + u₁ = 0 := Subtype.ext h0
    have h2 := congrArg (fun w : ↥I => (ψ w : Fin 5 → ZMod 2)) h1
    simp only [hψadd, hw₁, hu₁', map_zero] at h2
    exact hne₁ h2
  · intro h0
    rw [hvw u₂ w₂ rfl] at h0
    have h1 : w₂ + u₂ = 0 := Subtype.ext h0
    have h2 := congrArg (fun w : ↥I => (ψ w : Fin 5 → ZMod 2)) h1
    simp only [hψadd, hw₂, hu₂', map_zero] at h2
    exact hne₂ h2
  · intro h0
    rw [hvw u₁ w₁ rfl, hvw u₂ w₂ rfl] at h0
    have h1 : w₁ + u₁ = w₂ + u₂ := Subtype.ext h0
    have h2 : (ψ (w₁ + u₁) : Fin 5 → ZMod 2) = (ψ (w₂ + u₂) : Fin 5 → ZMod 2) :=
      congrArg (fun w : ↥I => (ψ w : Fin 5 → ZMod 2)) h1
    rw [hψadd, hψadd, hw₁, hw₂, hu₁', hu₂'] at h2
    exact hne₁₂ h2

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem not_III {a : GLV V} (ha : a ∈ X) (ha1 : a ≠ 1)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2)
    {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hIII : ¬ Homogeneous (normalClosure Γ L) ∧ SelfDual (normalClosure Γ L) I ∧ NondegOn B I ∧
      ¬ FaithfulOn (normalClosure Γ L) I ∧ Module.finrank (ZMod 2) V = 8 ∧
      ∃ x ∈ X, conjSub x I ≠ I ∧
        normalClosure Γ L = L ⊔ L.map (MulAut.conj x).toMonoidHom ∧
        Nat.card X = 8 ∧ X = (X ⊓ normalClosure Γ L) ⊔ Subgroup.zpowers x ∧
        I = commSpace L ⊤ ∧ IsA5Module L I ∧ conjSub x I = fixedSpace L) : False := by
  obtain ⟨-, -, -, -, hV8, x, hx, hne, hH, -, hXdec, -, hA5, hIfix⟩ := hIII
  have hx2 : x * x = 1 := hyp.X_sq x hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxH : ∀ h ∈ normalClosure Γ L, x * h * x⁻¹ ∈ normalClosure Γ L :=
    normalClosure_normal Γ L x (hyp.X_le hx)
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hI' : IrrPlus (normalClosure Γ L) (conjSub x I) := hyp.irrPlus_conj hI hx
  have hinvI' : Invariant (normalClosure Γ L) (conjSub x I) :=
    hirr.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx) |>.1
  have haI : conjSub a I = I := hyp.conj_eq_of_finrank_le ha hrank hI
  have haI' : conjSub a (conjSub x I) = conjSub x I := hyp.conj_eq_of_finrank_le ha hrank hI'
  have hax : a * x = x * a := hyp.X_comm a ha x hx
  have haH : a ∈ normalClosure Γ L := by
    have h1 : a ∈ (X ⊓ normalClosure Γ L) ⊔ Subgroup.zpowers x := hXdec ▸ ha
    have hc : ∀ b ∈ X ⊓ normalClosure Γ L, b * x = x * b := fun b hb => hyp.X_comm b hb.1 x hx
    rcases mem_or_mul_mem_of_mem_sup_zpowers hx2 hc h1 with h | h
    · exact h.2
    · exfalso
      have h2 : conjSub a I = conjSub (a * x) (conjSub x I) := by
        rw [← conjSub_mul]
        congr 1
        calc a = a * (x * x) := by rw [hx2, mul_one]
          _ = a * x * x := by group
      rw [hinvI'.conjSub_eq h.2, haI] at h2
      exact hne h2.symm
  have hIL : ∀ l ∈ L, ∀ u ∈ I, l u ∈ I := fun l hl u hu =>
    hI.1 l (le_normalClosure Γ L hl) u hu
  have hstep2 : ∀ h ∈ normalClosure Γ L, ∃ l ∈ L, ∀ u ∈ I, h u = l u := by
    let S' : Subgroup (GLV V) :=
      { carrier := {h | h ∈ normalClosure Γ L ∧ ∃ l ∈ L, ∀ u ∈ I, h u = l u}
        mul_mem' := by
          rintro h₁ h₂ ⟨hh₁, l₁, hl₁, e₁⟩ ⟨hh₂, l₂, hl₂, e₂⟩
          refine ⟨(normalClosure Γ L).mul_mem hh₁ hh₂, l₁ * l₂, L.mul_mem hl₁ hl₂, fun u hu => ?_⟩
          show h₁ (h₂ u) = l₁ (l₂ u)
          rw [e₂ u hu, e₁ _ (hIL l₂ hl₂ u hu)]
        one_mem' := ⟨(normalClosure Γ L).one_mem, 1, L.one_mem, fun u _ => rfl⟩
        inv_mem' := by
          rintro h ⟨hh, l, hl, e⟩
          refine ⟨(normalClosure Γ L).inv_mem hh, l⁻¹, L.inv_mem hl, fun u hu => ?_⟩
          have hv : l⁻¹ u ∈ I := hIL l⁻¹ (L.inv_mem hl) u hu
          have h1 : h (l⁻¹ u) = u := by
            rw [e _ hv]
            exact LinearEquiv.apply_symm_apply l u
          show h⁻¹ u = l⁻¹ u
          calc h⁻¹ u = h⁻¹ (h (l⁻¹ u)) := by rw [h1]
            _ = l⁻¹ u := LinearEquiv.symm_apply_apply h _ }
    have hL' : L ≤ S' := fun l hl => ⟨le_normalClosure Γ L hl, l, hl, fun u _ => rfl⟩
    have hLx : L.map (MulAut.conj x).toMonoidHom ≤ S' := by
      rintro _ ⟨l, hl, rfl⟩
      refine ⟨hxH l (le_normalClosure Γ L hl), 1, L.one_mem, fun u hu => ?_⟩
      have hxu : x⁻¹ u ∈ fixedSpace L := by
        rw [← hIfix, hxinv]
        exact apply_mem_conjSub hu
      have h1 : l (x⁻¹ u) = x⁻¹ u := hxu l hl
      show x (l (x⁻¹ u)) = u
      rw [h1, hxinv]
      have := congrArg (fun e : GLV V => e u) hx2
      exact this
    intro h hh
    exact (hH.le.trans (sup_le hL' hLx) hh).2
  obtain ⟨l, hlL, hal⟩ := hstep2 a haH
  obtain ⟨φ, ψ, hφψ⟩ := hA5
  have hfrI : Module.finrank (ZMod 2) ↥I = 4 := finrank_eq_four_of_equiv_permCore I ψ
  have hinf : I ⊓ conjSub x I = ⊥ := by
    have hinvinf : Invariant (normalClosure Γ L) (I ⊓ conjSub x I) := hirr.1.inf hinvI'
    rcases hirr.eq_bot_or_eq hinvinf (inf_le_left : I ⊓ conjSub x I ≤ I) with h0 | h1
    · exact h0
    · exfalso
      have hle : I ≤ conjSub x I := by
        intro u hu
        have hmem : u ∈ I ⊓ conjSub x I := by rw [h1]; exact hu
        exact hmem.2
      have heq : I = conjSub x I := by
        refine Submodule.eq_of_le_of_finrank_eq hle ?_
        rw [finrank_conjSub]
      exact hne heq.symm
  have hc : IsCompl I (conjSub x I) := by
    refine ⟨disjoint_iff.2 hinf, ?_⟩
    rw [codisjoint_iff]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq I (conjSub x I)
    rw [hinf, finrank_bot, finrank_conjSub, hfrI] at h1
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hnt : ∃ u ∈ I, a u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply ha1
    refine eq_one_of_centralizes_compl hc hcon ?_
    intro u hu
    obtain ⟨w, hw, rfl⟩ := hu
    show a (x w) = x w
    have : a (x w) = x (a w) := by
      have := congrArg (fun e : GLV V => e w) hax
      exact this
    rw [this, hcon w hw]
  obtain ⟨u₀, hu₀, hau₀⟩ := hnt
  have hσ : (φ ⟨l, hlL⟩ : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h1
    apply hau₀
    have hw : (⟨l u₀, hIL l hlL u₀ hu₀⟩ : ↥I) = ⟨u₀, hu₀⟩ := by
      apply ψ.injective
      apply Subtype.ext
      have := hφψ ⟨l, hlL⟩ ⟨u₀, hu₀⟩ ⟨l u₀, hIL l hlL u₀ hu₀⟩ rfl
      rw [this, h1]
      rfl
    rw [hal u₀ hu₀]
    exact congrArg Subtype.val hw
  have hf2 : 2 ≤ Module.finrank (ZMod 2) ↥(raU a I) :=
    two_le_finrank_raU_of_A5 (hIL l hlL) hal (φ ⟨l, hlL⟩) ψ
      (fun u w hw => hφψ ⟨l, hlL⟩ u w hw) hσ
  have hnt' : raU a (conjSub x I) ≠ ⊥ := by
    rw [Ne, raU_eq_bot_iff]
    intro hall
    apply hau₀
    have h1 := hall (x u₀) (apply_mem_conjSub hu₀)
    have h2 : a (x u₀) = x (a u₀) := by
      have := congrArg (fun e : GLV V => e u₀) hax
      exact this
    rw [h2] at h1
    exact x.injective h1
  have hf1 : 1 ≤ Module.finrank (ZMod 2) ↥(raU a (conjSub x I)) :=
    Submodule.one_le_finrank_iff.2 hnt'
  have hsum := finrank_raU_sup haI haI' hinf
  have hle : raU a (I ⊔ conjSub x I) ≤ LinearMap.range (a.toLinearMap - LinearMap.id) := by
    rw [← raU_top]
    exact raU_mono a le_top
  have := Submodule.finrank_mono hle
  omega

end G108Hyp

end G11

end CFSG.Quasithin
