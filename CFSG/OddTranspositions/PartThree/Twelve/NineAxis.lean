module

public import CFSG.OddTranspositions.PartThree.Twelve.Nine
import CFSG.OddTranspositions.PartThree.Twelve.Seven
import CFSG.GF2Type.Smith1979.W4AsSurvNine
import Mathlib.Algebra.Order.Group.Action.End

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Fischer

variable {G : Type} [Group G] {D : Set G}

theorem twelveNine [Finite G] (hS : Asc72.Setup G D) (hL : IsHypLineSpace D)
    (htwin : ∀ a ∈ D, ∀ b ∈ D, commSet D a = commSet D b → a = b) {u w₁ w₂ : G} (hu : u ∈ D)
    (hw₁ : w₁ ∈ D) (hw₂ : w₂ ∈ D) (hw₁u : ¬ Commute w₁ u) (hw₂u : ¬ Commute w₂ u)
    (hgcd : Nat.gcd ((lineMem D u w₁).ncard - 1) ((lineMem D u w₂).ncard - 1) ∣ 2)
    (σ : commGraph D ≃g commGraph D) (hσ : ∀ v : D, Commute (v : G) u → σ v = v) :
    (∀ v : D, σ v = v) ∨ ∀ v : D, (σ v : G) = u * v * u := by
  classical
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hS.oddT.1 u hu] at h
    simpa [pow_two] using h
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  let A := commGraph D ≃g commGraph D
  let E : Subgroup A :=
    { carrier := {τ | ∀ v : D, Commute (v : G) u → τ v = v}
      mul_mem' := fun {a b} ha hb => fun v hv => by
        rw [RelIso.mul_apply, hb v hv, ha v hv]
      one_mem' := fun v _ => rfl
      inv_mem' := fun {a} ha => fun v hv => by
        apply a.injective
        rw [RelIso.apply_inv_self, ha v hv] }
  have hEmem : ∀ τ : A, τ ∈ E ↔ ∀ v : D, Commute (v : G) u → τ v = v := fun _ => Iff.rfl
  haveI : Finite A :=
    Finite.of_injective (fun f : A => f.toEquiv) RelIso.toEquiv_injective
  haveI : Finite E :=
    Finite.of_injective (fun g : E => (↑g : A)) Subtype.coe_injective
  let φ : D → D := fun v => ⟨u * (v : G) * u, by simpa [hu_inv] using hS.conj_mem u v.2⟩
  have hφφ : ∀ v : D, φ (φ v) = v := by
    intro v
    apply Subtype.ext
    show u * (u * (v : G) * u) * u = (v : G)
    calc u * (u * (v : G) * u) * u = (u * u) * (v : G) * (u * u) := by group
      _ = (v : G) := by rw [hu2, one_mul, mul_one]
  let e : D ≃ D :=
    { toFun := φ, invFun := φ, left_inv := hφφ, right_inv := hφφ }
  have hconj : ∀ x y : G, Commute (u * x * u) (u * y * u) ↔ Commute x y := by
    intro x y
    simpa [hu_inv] using (Commute.conj_iff u (a := x) (b := y))
  let cu : A :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        rw [commGraph_adj_iff, commGraph_adj_iff]
        have hne : (e a : G) ≠ (e b : G) ↔ (a : G) ≠ (b : G) := by
          constructor
          · intro h h'
            exact h (by rw [Subtype.ext h'])
          · intro h h'
            exact h (congrArg Subtype.val (e.injective (Subtype.ext h')))
        rw [hne]
        exact and_congr Iff.rfl (hconj (a : G) (b : G)) }
  have hcu_apply : ∀ v : D, (cu v : G) = u * (v : G) * u := fun v => rfl
  have hcu_mem : cu ∈ E := (hEmem cu).mpr (fun v hv => by
    apply Subtype.ext
    rw [hcu_apply v, hv.symm.eq, mul_assoc, hu2, mul_one])
  have hcu_ne : cu ≠ 1 := by
    intro h
    have h1 : u * w₁ * u = w₁ := by
      have h2 : (cu ⟨w₁, hw₁⟩ : D) = (⟨w₁, hw₁⟩ : D) := by
        have hh := congrArg (fun f : A => (f : D → D)) h
        rw [show ((1 : A) : D → D) = id from rfl] at hh
        exact congrFun hh ⟨w₁, hw₁⟩
      have h3 : (cu ⟨w₁, hw₁⟩ : G) = w₁ := congrArg Subtype.val h2
      simpa [hcu_apply] using h3
    have huw : u * w₁ = w₁ * u := by
      have h4 : (u * w₁ * u) * u = w₁ * u := by rw [h1]
      simpa [mul_assoc, hu2] using h4
    exact hw₁u huw.symm
  let X : G → Set D := fun w => {x : D | (x : G) ∈ lineMem D u w ∧ (x : G) ≠ u}
  have hcardX : ∀ w ∈ D, (X w).ncard = (lineMem D u w).ncard - 1 := by
    intro w _
    have hline_u : u ∈ lineMem D u w := by
      rw [mem_lineMem]
      exact ⟨hu, fun x hx => hx.1⟩
    have himg : (Subtype.val '' X w) = lineMem D u w \ {u} := by
      ext g
      constructor
      · rintro ⟨x, ⟨hxline, hxne⟩, rfl⟩
        exact ⟨hxline, hxne⟩
      · rintro ⟨hgl, hgne⟩
        exact ⟨⟨g, hgl.1⟩, ⟨hgl, hgne⟩, rfl⟩
    rw [← Set.ncard_image_of_injective (X w) Subtype.coe_injective, himg,
      Set.ncard_sdiff_singleton_of_mem hline_u]
  have hE_dvd : ∀ w ∈ D, ¬ Commute w u → Nat.card E ∣ (X w).ncard := by
    intro w hw hwu
    letI : MulAction E D := MulAction.compHom D (Subgroup.subtype E)
    refine CFSG.GF2Type.Smith1979.W4As.Surv.card_dvd_ncard_of_free (G := E) (S := X w)
      (Set.toFinite (X w)) ?_ ?_
    · intro g a ha
      have hgE : ∀ v : D, Commute (v : G) u → (↑g : A) v = v :=
        (hEmem (↑g)).mp g.2
      have hline : ((↑g : A) a : G) ∈ lineMem D u w :=
        mem_lineMem_of_forall_apply_eq (↑g) (a := u) (b := w)
          (fun v hv => hgE v hv.1.2) ha.1
      have hne : ((↑g : A) a : G) ≠ u := by
        intro hEq
        have hgu : (↑g : A) ⟨u, hu⟩ = ⟨u, hu⟩ := hgE ⟨u, hu⟩ (Commute.refl u)
        have h1 : (↑g : A) a = (↑g : A) ⟨u, hu⟩ := by
          rw [hgu]
          exact Subtype.ext hEq
        have h2 : a = ⟨u, hu⟩ := (g : A).injective h1
        exact ha.2 (congrArg Subtype.val h2)
      change ((↑g : A) a : G) ∈ lineMem D u w ∧ ((↑g : A) a : G) ≠ u
      exact ⟨hline, hne⟩
    · intro g a ha hfix
      have hgE : ∀ v : D, Commute (v : G) u → (↑g : A) v = v :=
        (hEmem (↑g)).mp g.2
      have ha_u : ¬ Commute (a : G) u := (hL u hu w hw hwu a ha.1 ha.2).1
      have hfix' : (↑g : A) a = a := hfix
      have hgid : ∀ v : D, (↑g : A) v = v := fun v =>
        apply_eq_of_apply_eq (w := a) hS hL htwin hu hgE ha_u hfix' v
      have hcone : (↑g : A) = 1 := RelIso.ext hgid
      exact Subtype.ext hcone
  have hgcd2 : Nat.card E ∣ 2 := by
    have h1 := hE_dvd w₁ hw₁ hw₁u
    have h2 := hE_dvd w₂ hw₂ hw₂u
    rw [hcardX w₁ hw₁] at h1
    rw [hcardX w₂ hw₂] at h2
    exact dvd_trans (Nat.dvd_gcd h1 h2) hgcd
  have hcardE : Nat.card E = 2 := by
    have hge : 2 ≤ Nat.card E := by
      have hpair : ({1, cu} : Set A).ncard = 2 := Set.ncard_pair (Ne.symm hcu_ne)
      have hsub : ({1, cu} : Set A) ⊆ (E : Set A) := by
        intro x hx
        rcases hx with rfl | rfl
        · exact E.one_mem
        · exact hcu_mem
      have hle : ({1, cu} : Set A).ncard ≤ (E : Set A).ncard := Set.ncard_le_ncard hsub
      rw [hpair, ← Nat.card_coe_set_eq] at hle
      exact hle
    have hle : Nat.card E ≤ 2 := Nat.le_of_dvd (by norm_num) hgcd2
    omega
  have hEeq : (E : Set A) = {1, cu} := by
    have hsub : ({1, cu} : Set A) ⊆ (E : Set A) := by
      intro x hx
      rcases hx with rfl | rfl
      · exact E.one_mem
      · exact hcu_mem
    have hle : (E : Set A).ncard ≤ ({1, cu} : Set A).ncard := by
      rw [show (E : Set A).ncard = 2 from hcardE, Set.ncard_pair (Ne.symm hcu_ne)]
    exact (Set.eq_of_subset_of_ncard_le hsub hle).symm
  have hσE : σ ∈ (E : Set A) := (hEmem σ).mpr hσ
  rw [hEeq] at hσE
  rcases hσE with h | h
  · left
    intro v
    rw [h]
    exact congrFun (show ((1 : A) : D → D) = id from rfl) v
  · right
    intro v
    rw [h]
    exact hcu_apply v

theorem twelveNine_forall [Finite G] (hS : Asc72.Setup G D) (hL : IsHypLineSpace D)
    (htwin : ∀ a ∈ D, ∀ b ∈ D, commSet D a = commSet D b → a = b) {d w₁ w₂ : G} (hd : d ∈ D)
    (hw₁ : w₁ ∈ D) (hw₂ : w₂ ∈ D) (hw₁d : ¬ Commute w₁ d) (hw₂d : ¬ Commute w₂ d)
    (hgcd : Nat.gcd ((lineMem D d w₁).ncard - 1) ((lineMem D d w₂).ncard - 1) ∣ 2) (u : D)
    (σ : commGraph D ≃g commGraph D) (hσ : ∀ v : D, Commute (v : G) u → σ v = v) :
    (∀ v : D, σ v = v) ∨ ∀ v : D, (σ v : G) = (u : G) * v * u := by
  classical
  obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj hd u.2)
  let w₁' : G := g * w₁ * g⁻¹
  let w₂' : G := g * w₂ * g⁻¹
  have hw₁'D : w₁' ∈ D := hS.conj_mem g hw₁
  have hw₂'D : w₂' ∈ D := hS.conj_mem g hw₂
  have hw₁'u : ¬ Commute w₁' u := by
    intro h
    apply hw₁d
    rw [← hg] at h
    exact (Commute.conj_iff g).mp h
  have hw₂'u : ¬ Commute w₂' u := by
    intro h
    apply hw₂d
    rw [← hg] at h
    exact (Commute.conj_iff g).mp h
  have hnc₁ : (lineMem D u w₁').ncard = (lineMem D d w₁).ncard := by
    have h1 : lineMem D u w₁' = (MulAut.conj g) '' lineMem D d w₁ := by
      have hw : w₁' = g * w₁ * g⁻¹ := rfl
      rw [← hg, hw]
      exact lineMem_conj (fun g' x hx => hS.conj_mem g' hx) g d w₁
    rw [h1, Set.ncard_image_of_injective _ (MulAut.conj g).injective]
  have hnc₂ : (lineMem D u w₂').ncard = (lineMem D d w₂).ncard := by
    have h1 : lineMem D u w₂' = (MulAut.conj g) '' lineMem D d w₂ := by
      have hw : w₂' = g * w₂ * g⁻¹ := rfl
      rw [← hg, hw]
      exact lineMem_conj (fun g' x hx => hS.conj_mem g' hx) g d w₂
    rw [h1, Set.ncard_image_of_injective _ (MulAut.conj g).injective]
  have hgcd' : Nat.gcd ((lineMem D u w₁').ncard - 1) ((lineMem D u w₂').ncard - 1) ∣ 2 := by
    rw [hnc₁, hnc₂]
    exact hgcd
  exact twelveNine hS hL htwin u.2 hw₁'D hw₂'D hw₁'u hw₂'u hgcd' σ hσ

end CFSG.OddTranspositions.PartThree
