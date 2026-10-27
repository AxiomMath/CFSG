module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

namespace CommProd

variable {X : Type*} [Group X] {N₁ N₂ : Subgroup X}

@[expose] def mulHom (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) : ↥N₁ × ↥N₂ →* X where
  toFun p := (p.1 : X) * p.2
  map_one' := by simp
  map_mul' p q := by
    have h := hcomm q.1 q.1.2 p.2 p.2.2
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    calc (p.1 * q.1 : X) * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by simp only [mul_assoc]
      _ = p.1 * (p.2 * q.1) * q.2 := by rw [h]
      _ = _ := by simp only [mul_assoc]

theorem mulHom_apply (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (a : N₁) (b : N₂) :
    mulHom hcomm (a, b) = (a : X) * b := rfl

theorem mulHom_injective (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : N₁ ⊓ N₂ = ⊥) :
    Function.Injective (mulHom hcomm) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨a, b⟩ h
  have h1 : (a : X) * b = 1 := h
  have h2 : (a : X) ∈ N₂ := by
    have : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact N₂.inv_mem b.2
  have h3 : (a : X) ∈ N₁ ⊓ N₂ := ⟨a.2, h2⟩
  rw [hdisj, Subgroup.mem_bot] at h3
  have h4 : (b : X) = 1 := by
    rw [h3, one_mul] at h1
    exact h1
  have ha1 : a = 1 := Subtype.ext h3
  have hb1 : b = 1 := Subtype.ext h4
  rw [Subgroup.mem_bot]
  exact Prod.ext ha1 hb1

theorem range_mulHom (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) :
    (mulHom hcomm).range = N₁ ⊔ N₂ := by
  apply le_antisymm
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact Subgroup.mul_mem_sup a.2 b.2
  · refine sup_le ?_ ?_
    · intro a ha
      exact ⟨(⟨a, ha⟩, 1), by simp [mulHom_apply]⟩
    · intro b hb
      exact ⟨(1, ⟨b, hb⟩), by simp [mulHom_apply]⟩

theorem exists_mul_eq (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) {x : X} (hx : x ∈ N₁ ⊔ N₂) :
    ∃ a ∈ N₁, ∃ b ∈ N₂, a * b = x := by
  rw [← range_mulHom hcomm] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem mem_normalizer_of_comm {a : X} (ha : a ∈ N₁) {U : Subgroup X} (hU : U ≤ N₂)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) : a ∈ Subgroup.normalizer (U : Set X) := by
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (hcomm a ha h (hU hh)).symm

theorem mem_normalizer_left {U₁ U₂ : Subgroup X}
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : N₁ ⊓ N₂ = ⊥) (hU₁ : U₁ ≤ N₁)
    (hU₂ : U₂ ≤ N₂) {a b : X} (ha : a ∈ N₁) (hb : b ∈ N₂)
    (hd : a * b ∈ Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup X) : Set X)) :
    a ∈ Subgroup.normalizer (U₁ : Set X) := by
  have hinter : ∀ x, x ∈ U₁ ⊔ U₂ → x ∈ N₁ → x ∈ U₁ := by
    intro x hx hxN
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      exists_mul_eq (fun a ha b hb => hcomm a (hU₁ ha) b (hU₂ hb)) hx
    have hvN : v ∈ N₁ := by
      have := N₁.mul_mem (N₁.inv_mem (hU₁ hu)) hxN
      simpa using this
    have hv1 : v = 1 := by
      have : v ∈ N₁ ⊓ N₂ := ⟨hvN, hU₂ hv⟩
      rwa [hdisj, Subgroup.mem_bot] at this
    simpa [hv1] using hu
  have hconj : ∀ h ∈ N₁, a * b * h * (a * b)⁻¹ = a * h * a⁻¹ := by
    intro h hh
    have hbh : b * h = h * b := (hcomm h hh b hb).symm
    calc a * b * h * (a * b)⁻¹ = a * (b * h) * b⁻¹ * a⁻¹ := by group
      _ = a * (h * b) * b⁻¹ * a⁻¹ := by rw [hbh]
      _ = a * h * a⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 : a * b * h * (a * b)⁻¹ ∈ U₁ ⊔ U₂ :=
      (Subgroup.mem_normalizer_iff.1 hd h).1 (Subgroup.mem_sup_left hh)
    rw [hconj h (hU₁ hh)] at h1
    exact hinter _ h1 (N₁.mul_mem (N₁.mul_mem ha (hU₁ hh)) (N₁.inv_mem ha))
  · intro hh
    have hhN : h ∈ N₁ := by
      have := N₁.mul_mem (N₁.mul_mem (N₁.inv_mem ha) (hU₁ hh)) ha
      simpa [mul_assoc] using this
    have h1 : h ∈ U₁ ⊔ U₂ := by
      rw [Subgroup.mem_normalizer_iff.1 hd h, hconj h hhN]
      exact Subgroup.mem_sup_left hh
    exact hinter _ h1 hhN

theorem isSolvable_sup {A B : Subgroup X} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : Group.IsSolvable ↥A) (hB : Group.IsSolvable ↥B) : Group.IsSolvable ↥(A ⊔ B) := by
  have hs : Group.IsSolvable ↥(mulHom hcomm).range :=
    Group.isSolvable_of_surjective (f := (mulHom hcomm).rangeRestrict)
      (mulHom hcomm).rangeRestrict_surjective
  rwa [range_mulHom hcomm] at hs

theorem card_sup {A B : Subgroup X} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 : Nat.card (↥A × ↥B) = Nat.card ↥(mulHom hcomm).range :=
    Nat.card_congr (MonoidHom.ofInjective (mulHom_injective hcomm hdisj)).toEquiv
  rw [range_mulHom hcomm, Nat.card_prod] at h1
  exact h1.symm

theorem normalizer_sup_inf_sup {U₁ U₂ : Subgroup X}
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : N₁ ⊓ N₂ = ⊥) (hU₁ : U₁ ≤ N₁)
    (hU₂ : U₂ ≤ N₂) :
    Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup X) : Set X) ⊓ (N₁ ⊔ N₂) =
      (Subgroup.normalizer (U₁ : Set X) ⊓ N₁) ⊔ (Subgroup.normalizer (U₂ : Set X) ⊓ N₂) := by
  have hcomm' : ∀ a ∈ N₂, ∀ b ∈ N₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  apply le_antisymm
  · rintro d ⟨hdn, hdN⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq hcomm hdN
    have ha' : a ∈ Subgroup.normalizer (U₁ : Set X) :=
      mem_normalizer_left hcomm hdisj hU₁ hU₂ ha hb hdn
    have hb' : b ∈ Subgroup.normalizer (U₂ : Set X) := by
      refine mem_normalizer_left hcomm' (by rwa [inf_comm]) hU₂ hU₁ hb ha ?_
      rw [← hcomm a ha b hb, sup_comm]
      exact hdn
    exact Subgroup.mul_mem_sup ⟨ha', ha⟩ ⟨hb', hb⟩
  · refine sup_le ?_ ?_
    · rintro a ⟨ha₁, ha⟩
      exact ⟨Subgroup.inf_normalizer_le_normalizer_sup U₁ U₂
        ⟨ha₁, mem_normalizer_of_comm ha hU₂ hcomm⟩, Subgroup.mem_sup_left ha⟩
    · rintro b ⟨hb₂, hb⟩
      exact ⟨Subgroup.inf_normalizer_le_normalizer_sup U₁ U₂
        ⟨mem_normalizer_of_comm hb hU₁ hcomm', hb₂⟩, Subgroup.mem_sup_right hb⟩

end CommProd

theorem q_two_closed_prod {X : Type*} [Group X] (N₁ N₂ : Subgroup X)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : N₁ ⊓ N₂ = ⊥)
    (U₁ U₂ : Subgroup X) (hU₁ : U₁ ≤ N₁) (hU₂ : U₂ ≤ N₂)
    (P₁ : ∀ A : Subgroup X, A ≤ N₁ → U₁ ≤ A → Group.IsSolvable ↥A →
      A ≤ Subgroup.normalizer (U₁ : Set X))
    (P₂ : ∀ A : Subgroup X, A ≤ N₂ → U₂ ≤ A → Group.IsSolvable ↥A →
      A ≤ Subgroup.normalizer (U₂ : Set X))
    (D : Subgroup X) (hD : D ≤ N₁ ⊔ N₂) (hDs : Group.IsSolvable ↥D) (hU : U₁ ⊔ U₂ ≤ D) :
    D ≤ Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup X) : Set X) := by
  let ψ := CommProd.mulHom hcomm
  let E : Subgroup (↥N₁ × ↥N₂) := D.comap ψ
  have hE : Group.IsSolvable ↥E := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := (ψ.comp E.subtype).codRestrict D (fun e => e.2)) ?_
    intro x y h
    exact Subtype.ext (CommProd.mulHom_injective hcomm hdisj (congrArg Subtype.val h))
  let φ₁ : ↥N₁ × ↥N₂ →* X := N₁.subtype.comp (MonoidHom.fst _ _)
  let φ₂ : ↥N₁ × ↥N₂ →* X := N₂.subtype.comp (MonoidHom.snd _ _)
  have h₁ : E.map φ₁ ≤ Subgroup.normalizer (U₁ : Set X) := by
    refine P₁ _ ?_ ?_ ?_
    · rintro _ ⟨e, -, rfl⟩
      exact e.1.2
    · intro u hu
      refine ⟨(⟨u, hU₁ hu⟩, 1), ?_, rfl⟩
      change (u : X) * 1 ∈ D
      rw [mul_one]
      exact hU (Subgroup.mem_sup_left hu)
    · exact Group.isSolvable_of_surjective (f := φ₁.subgroupMap E) (φ₁.subgroupMap_surjective E)
  have h₂ : E.map φ₂ ≤ Subgroup.normalizer (U₂ : Set X) := by
    refine P₂ _ ?_ ?_ ?_
    · rintro _ ⟨e, -, rfl⟩
      exact e.2.2
    · intro u hu
      refine ⟨(1, ⟨u, hU₂ hu⟩), ?_, rfl⟩
      change (1 : X) * u ∈ D
      rw [one_mul]
      exact hU (Subgroup.mem_sup_right hu)
    · exact Group.isSolvable_of_surjective (f := φ₂.subgroupMap E) (φ₂.subgroupMap_surjective E)
  intro d hd
  have hd' : d ∈ ψ.range := by
    rw [CommProd.range_mulHom hcomm]
    exact hD hd
  obtain ⟨⟨a, b⟩, hab⟩ := hd'
  have hmem : (a, b) ∈ E := by
    change ψ (a, b) ∈ D
    rw [hab]
    exact hd
  have ha₁ : (a : X) ∈ Subgroup.normalizer (U₁ : Set X) := h₁ ⟨(a, b), hmem, rfl⟩
  have hb₂ : (b : X) ∈ Subgroup.normalizer (U₂ : Set X) := h₂ ⟨(a, b), hmem, rfl⟩
  have ha₂ : (a : X) ∈ Subgroup.normalizer (U₂ : Set X) :=
    CommProd.mem_normalizer_of_comm a.2 hU₂ hcomm
  have hb₁ : (b : X) ∈ Subgroup.normalizer (U₁ : Set X) := by
    refine CommProd.mem_normalizer_of_comm (N₁ := N₂) (N₂ := N₁) b.2 hU₁ ?_
    intro x hx y hy
    exact (hcomm y hy x hx).symm
  have hdeq : d = (a : X) * b := hab.symm
  rw [hdeq]
  exact Subgroup.mul_mem _ (Subgroup.inf_normalizer_le_normalizer_sup U₁ U₂ ⟨ha₁, ha₂⟩)
    (Subgroup.inf_normalizer_le_normalizer_sup U₁ U₂ ⟨hb₁, hb₂⟩)

theorem q_two_closed_prod_normalizer_solvable {X : Type*} [Group X] (N₁ N₂ : Subgroup X)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : N₁ ⊓ N₂ = ⊥)
    (U₁ U₂ : Subgroup X) (hU₁ : U₁ ≤ N₁) (hU₂ : U₂ ≤ N₂)
    (h₁ : Group.IsSolvable ↥(Subgroup.normalizer (U₁ : Set X) ⊓ N₁))
    (h₂ : Group.IsSolvable ↥(Subgroup.normalizer (U₂ : Set X) ⊓ N₂)) :
    Group.IsSolvable ↥(Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup X) : Set X) ⊓ (N₁ ⊔ N₂)) := by
  rw [CommProd.normalizer_sup_inf_sup hcomm hdisj hU₁ hU₂]
  exact CommProd.isSolvable_sup (fun a ha b hb => hcomm a ha.2 b hb.2) h₁ h₂

theorem q_two_closed_prod_normalizer_card {X : Type*} [Group X] (N₁ N₂ : Subgroup X)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hdisj : N₁ ⊓ N₂ = ⊥)
    (U₁ U₂ : Subgroup X) (hU₁ : U₁ ≤ N₁) (hU₂ : U₂ ≤ N₂) :
    Nat.card ↥(Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup X) : Set X) ⊓ (N₁ ⊔ N₂)) =
      Nat.card ↥(Subgroup.normalizer (U₁ : Set X) ⊓ N₁) *
        Nat.card ↥(Subgroup.normalizer (U₂ : Set X) ⊓ N₂) := by
  rw [CommProd.normalizer_sup_inf_sup hcomm hdisj hU₁ hU₂]
  refine CommProd.card_sup (fun a ha b hb => hcomm a ha.2 b hb.2) ?_
  rw [eq_bot_iff, ← hdisj]
  exact inf_le_inf inf_le_right inf_le_right

end CFSG.Quasithin
