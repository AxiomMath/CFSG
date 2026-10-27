module

public import CFSG.Quasithin.Vol2.Ch11SecU1Main
public import CFSG.Quasithin.EmptyFaithful.E22PTypeII
public import CFSG.Quasithin.Vol2.Ch11SecU1Aux

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b

variable {G : Type} [Group G] [Finite G]

theorem exists_member (hTor : TorusMember) (hComp : ComponentMember) {L : Subgroup G}
    (h : Setting L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hA4 : 4 ≤ Nat.card A) :
    ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ K : Subgroup G, IsE 1 ⊤ T (A1b.conjSub g A) K ∧
      ¬ K ≤ Subgroup.centralizer {z} := by
  have hLn := h.almostSimple.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hA.2 x hx
  have hord : ∀ x ∈ A, x ≠ 1 → orderOf x = 2 := fun x hx hx1 => orderOf_eq_prime (hA.2 x hx) hx1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isElemAbelian hA hy hx))
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz2
  have hmem : ∀ (B : Subgroup G) (g x : G), x ∈ B → g * x * g⁻¹ ∈ A1b.conjSub g B :=
    fun _ _ x hx => ⟨x, hx, rfl⟩
  have hmemc : ∀ (g x : G), x ∈ A → g * x * g⁻¹ ∈ A1b.conjSub g A := hmem A
  by_cases hI : ∃ x ∈ A, x ∈ L ∧ x ≠ 1 ∧ ∃ y ∈ A, y ∈ L ∧ y ≠ 1 ∧ x ≠ y
  ·
    obtain ⟨x, hxA, hxL, hx1, y, hyA, hyL, hy1, hxy⟩ := hI
    obtain ⟨l, -, hl⟩ := h.inner_conj x hxL z hzL (hord x hxA hx1) hz2
    obtain ⟨g, hgT, hgx⟩ := exists_conj_le_eq hT hzT hA hxA hl
    have hzA : z ∈ A1b.conjSub g A := hgx ▸ hmemc g x hxA
    have hy2 : orderOf (g * y * g⁻¹) = 2 := by rw [orderOf_conj']; exact hord y hyA hy1
    have hzy : z ≠ g * y * g⁻¹ := fun he => hxy (by
      rw [← hgx] at he
      simpa using he)
    exact ⟨g, hgT, member_of_oddTorus hTor hO2 hT hgT (isElemAbelian_conjSub hA g) hzA hzL hz2
      (hmemc g y hyA) hzy (h.inner_torus _ (hLn.conj_mem y hyL g) hy2)⟩
  push Not at hI
  obtain ⟨x₁, hx₁A, hx₁1, -⟩ := exists_mem_ne_ne (by omega : 3 ≤ Nat.card A) 1 1
  obtain ⟨x₂, hx₂A, hx₂1, hx₂x₁⟩ := exists_mem_ne_ne (by omega : 3 ≤ Nat.card A) 1 x₁
  have hne1 : ∀ x ∈ A, x ∉ L → x ≠ 1 := fun x _ hxL hx => hxL (hx ▸ L.one_mem)
  have hpair : ∀ t₁ ∈ A, ∀ t₂ ∈ A, t₁ ∉ L → t₂ ∉ L → t₁ * t₂ ∈ L :=
    fun t₁ h₁ t₂ h₂ h₁L h₂L => h.outer_pair t₁ t₂ h₁L h₂L (hord t₁ h₁ (hne1 t₁ h₁ h₁L))
      (hord t₂ h₂ (hne1 t₂ h₂ h₂L)) (hcomm t₁ h₁ t₂ h₂)
  have hinv : ∀ x ∈ A, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_left (hsq x hx)
  obtain ⟨v, hvA, hvL, hv1⟩ : ∃ v ∈ A, v ∈ L ∧ v ≠ 1 := by
    by_cases h₁ : x₁ ∈ L
    · exact ⟨x₁, hx₁A, h₁, hx₁1⟩
    by_cases h₂ : x₂ ∈ L
    · exact ⟨x₂, hx₂A, h₂, hx₂1⟩
    refine ⟨x₁ * x₂, A.mul_mem hx₁A hx₂A, hpair x₁ hx₁A x₂ hx₂A h₁ h₂, fun e => hx₂x₁ ?_⟩
    calc x₂ = x₁⁻¹ * (x₁ * x₂) := by group
      _ = x₁ := by rw [e, mul_one, hinv x₁ hx₁A]
  obtain ⟨b, hbA, hbL⟩ : ∃ b ∈ A, b ∉ L := by
    by_contra hcon
    push Not at hcon
    exact hx₂x₁ (hI x₂ hx₂A (hcon x₂ hx₂A) hx₂1 x₁ hx₁A (hcon x₁ hx₁A) hx₁1)
  have hA4' : ∀ x ∈ A, x = 1 ∨ x = v ∨ x = b ∨ x = v * b := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    by_cases hxL : x ∈ L
    · exact Or.inr (Or.inl (hI x hx hxL hx1 v hvA hvL hv1))
    have hxb : x * b ∈ L := hpair x hx b hbA hxL hbL
    have hxe : x = x * b * b := by rw [mul_assoc, hsq b hbA, mul_one]
    by_cases hxb1 : x * b = 1
    · exact Or.inr (Or.inr (Or.inl (by rw [hxe, hxb1, one_mul])))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [hxe, hI (x * b) (A.mul_mem hx hbA) hxb hxb1 v hvA hvL hv1])))
  obtain ⟨l, -, hl⟩ := h.inner_conj v hvL z hzL (hord v hvA hv1) hz2
  obtain ⟨g, hgT, hgv⟩ := exists_conj_le_eq hT hzT hA hvA hl
  have hzA : z ∈ A1b.conjSub g A := hgv ▸ hmemc g v hvA
  have hb₃L : g * b * g⁻¹ ∉ L := fun hm => hbL (by
    have := hLn.conj_mem _ hm g⁻¹
    simpa [mul_assoc] using this)
  have hb₃2 : orderOf (g * b * g⁻¹) = 2 := by rw [orderOf_conj']; exact hord b hbA (hne1 b hbA hbL)
  have hA' := isElemAbelian_conjSub hA g
  rcases h.outer _ hb₃L hb₃2 with hδ | hσ
  · exact ⟨g, hgT, member_of_oddTorus hTor hO2 hT hgT hA' hzA hzL hz2 (hmemc g b hbA)
      (fun e => hb₃L (e ▸ hzL)) hδ⟩
  obtain ⟨k, hkT, hkSyl⟩ := exists_conj_le_sylow hT hA' (hmemc g b hbA)
  refine ⟨k * g, by rw [A1b.conjSub_mul]; exact hkT, ?_⟩
  rw [A1b.conjSub_mul]
  refine member_of_sigma hComp h hO2 hT hkT (isElemAbelian_conjSub hA' k) (hmem _ k z hzA)
    (hLn.conj_mem z hzL k) (fun e => hz1 ?_) (hmem _ k _ (hmemc g b hbA)) ?_ hkSyl
    (hσ.conj hLn k) hzL hz2
  · calc z = k⁻¹ * (k * z * k⁻¹) * k := by group
      _ = 1 := by rw [e]; group
  · intro x hx
    rw [A1b.mem_conjSub_iff, A1b.mem_conjSub_iff] at hx
    have hxe : x = k * g * (g⁻¹ * (k⁻¹ * x * k) * g) * (k * g)⁻¹ := by group
    rcases hA4' _ hx with h1 | h1 | h1 | h1 <;> rw [h1] at hxe
    · exact Or.inl (by rw [hxe]; group)
    · refine Or.inr (Or.inl ?_)
      rw [hxe, ← hgv]
      group
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [hxe]
      group
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [hxe, ← hgv]
      group

theorem inEFor_one_of_setting (hTor : TorusMember) (hComp : ComponentMember) {L : Subgroup G}
    (h : Setting L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) : InEFor 1 ⊤ T := by
  have := h.almostSimple.normal
  have := h.almostSimple.simple
  have hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥ :=
    pCoreOf_top_eq_bot_of_normal_simple L h.almostSimple.nonabelian h.almostSimple.centralizer_eq
  obtain ⟨z, hzL, hz2, -, hzc⟩ := h.exists_central_involution hT
  refine inEFor_top_of_coatom_conj hT
    (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hzc t ht))
    (h.isSolvable_centralizer hzL hz2) (h.isCoatom_centralizer hzL hz2) (fun A hAT hA2 => ?_)
    (fun A _ hA hA4 => exists_member hTor hComp h hT hO2 hzL hz2 hzc hA hA4)
  exact isE_one_top_of_almostSimple L T A h.almostSimple.nonabelian
    h.almostSimple.centralizer_eq hT (h.sup_eq_top hT) hAT hA2

theorem nParam_le_one_of_setting (hTor : TorusMember) (hComp : ComponentMember)
    {L : Subgroup G} (h : Setting L) : E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have h1 := (nParam_le_iff (H := (⊤ : Subgroup G)) (n := 1) one_pos).mpr
    (fun T hT => inEFor_one_of_setting hTor hComp h hT)
  simpa using h1

end CFSG.Quasithin.Vol2.Ch11.SecU1
