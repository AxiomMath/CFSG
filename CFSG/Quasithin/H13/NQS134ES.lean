module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.H13.NQS13410S

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def l3E23 : L3.Γ := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

@[expose] def InEll (p : L3.Vec) : Prop := L3.act l3E23 p = p

instance : DecidablePred InEll := fun p => by unfold InEll; infer_instance

@[expose] def FixEll (σ : L3.Γ) : Prop := ∀ p : L3.Vec, InEll p → L3.act σ p = p

instance : DecidablePred FixEll := fun σ => by unfold FixEll; infer_instance

theorem l3E23_mem : l3E23 ∈ l3Blist := by decide

theorem vec_add_self : ∀ a : L3.Vec, a + a = 0 := by decide

theorem l3_span_of_fix : ∀ a b d : L3.Vec,
    (∀ γ : L3.Γ, L3.act γ a = a → L3.act γ b = b → L3.act γ d = d) →
      d = 0 ∨ d = a ∨ d = b ∨ d = a + b := by
  decide +kernel

theorem l3e1_ne_zero : l3e1 ≠ 0 := by decide

theorem ell_P2 : ∀ σ : L3.Γ, InL3P2 σ → ∀ p : L3.Vec, InEll p → InEll (L3.act σ p) := by
  decide +kernel

theorem ell_comm : ∀ σ ∈ l3Blist, ∀ p : L3.Vec, InEll p →
    p + L3.act σ p = 0 ∨ p + L3.act σ p = l3e1 := by
  decide +kernel

theorem ell_index : ∀ σ ∈ l3Blist, ∀ σ' ∈ l3Blist, ¬ FixEll σ → ¬ FixEll σ' →
    FixEll (σ * σ') := by
  decide +kernel

theorem ell_key : ∀ σ ∈ l3Blist, σ * σ = 1 →
    4 ≤ (Finset.univ.filter fun p : L3.Vec => L3.act σ p = p ∧
      L3.act (l3E23 * σ * l3E23⁻¹) p = p).card → FixEll σ := by
  decide +kernel

theorem l3B_not_elem : ∃ b ∈ l3Blist, b * b ≠ 1 := by decide

theorem inEll_e1 : InEll l3e1 := by decide

variable {G : Type} [Group G]

namespace L3Coords

variable {K X : Subgroup G} (C : L3Coords K X)

theorem conj' (g : ↥(normalizer (X : Set G))) (x : ↥X) :
    C.c ⟨(g : G) * x * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 x).mp x.2⟩ =
      L3.act (C.ρ g) (C.c x) := by
  have h1 := C.equiv g x
  have e : conjAct X g x = ⟨(g : G) * x * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 x).mp x.2⟩ :=
    Subtype.ext (A5.conjAct_val X g x)
  rwa [e] at h1

theorem c_mul (hX2 : ∀ x ∈ X, x * x = 1) {a b : G} (ha : a ∈ X) (hb : b ∈ X) :
    C.c ⟨a * b, mul_mem ha hb⟩ = C.c ⟨a, ha⟩ + C.c ⟨b, hb⟩ := by
  have hfix : ∀ γ : L3.Γ, L3.act γ (C.c ⟨a, ha⟩) = C.c ⟨a, ha⟩ →
      L3.act γ (C.c ⟨b, hb⟩) = C.c ⟨b, hb⟩ →
        L3.act γ (C.c ⟨a * b, mul_mem ha hb⟩) = C.c ⟨a * b, mul_mem ha hb⟩ := by
    intro γ h1 h2
    obtain ⟨g, -, rfl⟩ := C.image_K γ
    have e1 := (C.fix_iff g ⟨a, ha⟩).2 h1
    have e2 := (C.fix_iff g ⟨b, hb⟩).2 h2
    refine (C.fix_iff g ⟨a * b, mul_mem ha hb⟩).1 ?_
    show (g : G) * (a * b) * (g : G)⁻¹ = a * b
    calc (g : G) * (a * b) * (g : G)⁻¹ = ((g : G) * a * (g : G)⁻¹) * ((g : G) * b * (g : G)⁻¹) :=
          by group
      _ = a * b := by rw [show (g : G) * a * (g : G)⁻¹ = a from e1,
          show (g : G) * b * (g : G)⁻¹ = b from e2]
  have hinj : ∀ {x y : G} (hx : x ∈ X) (hy : y ∈ X), C.c ⟨x, hx⟩ = C.c ⟨y, hy⟩ → x = y :=
    fun hx hy h => congrArg Subtype.val (C.c_inj h)
  have hone : C.c ⟨1, one_mem X⟩ = 0 := C.c_one
  rcases l3_span_of_fix _ _ _ hfix with h | h | h | h
  ·
    have hab : a * b = 1 := hinj _ (one_mem X) (h.trans hone.symm)
    have hb' : b = a := by
      have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
      rw [h1, inv_eq_of_mul_eq_one_right (hX2 a ha)]
    subst hb'
    rw [h, vec_add_self]
  ·
    have hab : a * b = a := hinj _ ha h
    have hb1 : b = 1 := by
      have := congrArg (a⁻¹ * ·) hab
      simpa using this
    subst hb1
    rw [h, show C.c ⟨1, hb⟩ = 0 from hone, add_zero]
  ·
    have hab : a * b = b := hinj _ hb h
    have ha1 : a = 1 := by
      have := congrArg (· * b⁻¹) hab
      simpa using this
    subst ha1
    rw [h, show C.c ⟨1, ha⟩ = 0 from hone, zero_add]
  · exact h

theorem card_le_four [Finite G] {Y : Subgroup G} (hYN : Y ≤ normalizer (X : Set G))
    (hY2 : ∀ y ∈ Y, y * y = 1) (hYB : ∀ (y : G) (hy : y ∈ Y), C.ρ ⟨y, hYN hy⟩ ∈ l3Blist) :
    Nat.card Y ≤ 4 * Nat.card ↥(Y ⊓ centralizer (X : Set G)) := by
  classical
  let f : ↥Y →* L3.Γ := C.ρ.comp (Subgroup.inclusion hYN)
  have hker : f.ker = (Y ⊓ centralizer (X : Set G)).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    simp only [f, MonoidHom.comp_apply]
    exact ⟨fun h => ⟨y.2, (C.ker _).1 h⟩, fun h => (C.ker (Subgroup.inclusion hYN y)).2 h.2⟩
  have hcardker : Nat.card f.ker = Nat.card ↥(Y ⊓ centralizer (X : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : Y ⊓ centralizer (X : Set G) ≤ Y)).toEquiv
  have hmul : Nat.card ↥(Y ⊓ centralizer (X : Set G)) * Nat.card f.range = Nat.card Y := by
    rw [← hcardker, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hRB : f.range ≤ l3B := by
    rintro _ ⟨y, rfl⟩
    exact hYB y y.2
  have hR4 : Nat.card f.range ≤ 4 := by
    have hdvd : Nat.card f.range ∣ 8 := card_l3B ▸ Subgroup.card_dvd_of_le hRB
    have hne : f.range ≠ l3B := by
      intro h
      obtain ⟨b, hb, hb2⟩ := l3B_not_elem
      have hbR : b ∈ f.range := h ▸ (show b ∈ l3B from hb)
      obtain ⟨y, rfl⟩ := hbR
      apply hb2
      rw [← map_mul]
      have : y * y = 1 := Subtype.ext (hY2 y y.2)
      rw [this, map_one]
    have hlt : Nat.card f.range < 8 := by
      have hle := Subgroup.card_le_of_le hRB
      rw [card_l3B] at hle
      rcases hle.lt_or_eq with h | h
      · exact h
      · exact absurd (Subgroup.eq_of_le_of_card_ge hRB (by rw [h, card_l3B])) hne
    have : Nat.card f.range ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have h8 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [h8] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  rw [← hmul, mul_comm]
  exact Nat.mul_le_mul_right _ hR4

end L3Coords

end CFSG.Quasithin.H13.NQS134
