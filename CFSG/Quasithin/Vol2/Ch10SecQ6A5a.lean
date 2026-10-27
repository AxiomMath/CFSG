module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrCl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

set_option maxRecDepth 10000 in
theorem eq_one_of_fix_O : ∀ σ : Perm (Fin 5), (∀ u : Fin 5 → ZMod 2, IsO u → pv σ u = u) →
    σ = 1 := by
  decide +kernel

@[expose] def va : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def vb : Perm (Fin 5) := swap 0 2 * swap 1 3

theorem va_mem : va ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem vb_mem : vb ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide

set_option maxRecDepth 10000 in
theorem fixO_V4 : ∀ u : Fin 5 → ZMod 2, IsO u → pv va u = u → pv vb u = u → u = 0 ∨ u = wv 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem exists_sign_apply : ∀ k : Fin 5, ∃ γ : Perm (Fin 5), Perm.sign γ = 1 ∧ γ 4 = k := by
  decide +kernel

theorem exists_alt_apply (k : Fin 5) : ∃ γ ∈ alternatingGroup (Fin 5), γ 4 = k := by
  obtain ⟨γ, hγ, hk⟩ := exists_sign_apply k
  exact ⟨γ, Perm.mem_alternatingGroup.mpr hγ, hk⟩

theorem card_O : Nat.card {u : Fin 5 → ZMod 2 // IsO u} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

variable {W : Type*} [CommGroup W]

@[expose] def IsA5Coord (Λ : Subgroup (MulAut W)) (π : alternatingGroup (Fin 5) →* Λ)
    (Ψ : W → Fin 5 → ZMod 2) : Prop :=
  Function.Surjective π ∧ (∀ w w', Ψ (w * w') = Ψ w + Ψ w') ∧ Function.Injective Ψ ∧
    (∀ w, IsO (Ψ w)) ∧ (∀ u, IsO u → ∃ w, Ψ w = u) ∧
    ∀ (γ : alternatingGroup (Fin 5)) (w : W), Ψ ((π γ : MulAut W) w) = pv γ (Ψ w)

theorem allOnes_not_mem : G6.allOnes 5 ∉ G6.coreMod 5 := by
  change ¬ (∑ i, Multiplicative.toAdd (G6.allOnes 5) i = 0)
  decide

theorem altDn5_ker {m : G6.PermMod 5} (hm : m ∈ (FFModel.altDn 5).ker) : m = 1 := by
  obtain ⟨hz, hc⟩ := hm
  have h2 : G6.allOnes 5 * G6.allOnes 5 = 1 := by decide
  have hle : Subgroup.zpowers (G6.allOnes 5) ≤ pairSub (G6.allOnes 5) h2 :=
    (Subgroup.zpowers_le).mpr (Or.inr rfl)
  rcases hle hz with h | h
  · exact h
  · exact absurd (h ▸ hc) allOnes_not_mem

theorem exists_isA5Coord {Λ : Subgroup (MulAut W)} (h : AlternatingNatural Λ ⊤ ⊥ 5) :
    ∃ π Ψ, IsA5Coord Λ π Ψ := by
  obtain ⟨π, hsurj, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  let κ : (↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) →*
      ↥(FFModel.altDn 5).sec :=
    QuotientGroup.lift ((FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) (MonoidHom.id _)
      (fun x hx => Subtype.ext (altDn5_ker (Subgroup.mem_subgroupOf.mp hx)))
  have hκ : ∀ m : ↥(FFModel.altDn 5).sec, κ (QuotientGroup.mk m) = m := fun m =>
    QuotientGroup.lift_mk _ _ _
  have hmk : ∀ q, (QuotientGroup.mk (κ q) :
      ↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) = q := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hκ]
  let Ψ : W → Fin 5 → ZMod 2 := fun w =>
    Multiplicative.toAdd (show G6.PermMod 5 from
      ((κ (β ⟨w, Subgroup.mem_top w⟩) : ↥(FFModel.altDn 5).sec) : (FFModel.altDn 5).Amb))
  refine ⟨π, Ψ, hsurj, fun w w' => ?_, fun w w' hww => ?_, fun w => (κ (β _)).2,
    fun u hu => ?_, fun γ w => ?_⟩
  · change Multiplicative.toAdd (show G6.PermMod 5 from
      ((κ (β (⟨w, Subgroup.mem_top w⟩ * ⟨w', Subgroup.mem_top w'⟩)) :
        ↥(FFModel.altDn 5).sec) : (FFModel.altDn 5).Amb)) = _
    rw [map_mul, map_mul]
    rfl
  · have h1 : κ (β ⟨w, Subgroup.mem_top w⟩) = κ (β ⟨w', Subgroup.mem_top w'⟩) :=
      Subtype.ext (Multiplicative.toAdd.injective hww)
    have h2 : β ⟨w, Subgroup.mem_top w⟩ = β ⟨w', Subgroup.mem_top w'⟩ := by
      rw [← hmk (β _), h1, hmk]
    have h3 : β (⟨w, Subgroup.mem_top w⟩ * (⟨w', Subgroup.mem_top w'⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h4 := (hβk _).mp h3
    rw [Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.mp h4
  · obtain ⟨⟨w, hw0⟩, hw⟩ := hβs (QuotientGroup.mk ⟨Multiplicative.ofAdd u, hu⟩)
    refine ⟨w, ?_⟩
    change Multiplicative.toAdd (show G6.PermMod 5 from
      ((κ (β ⟨w, Subgroup.mem_top w⟩) : ↥(FFModel.altDn 5).sec) : (FFModel.altDn 5).Amb)) = u
    rw [hw, hκ]
    rfl
  · have he := hβe γ ⟨w, Subgroup.mem_top w⟩ (κ (β ⟨w, Subgroup.mem_top w⟩))
      (Subgroup.mem_top _) (hsec γ _ (κ (β ⟨w, Subgroup.mem_top w⟩)).2)
      (hmk (β ⟨w, Subgroup.mem_top w⟩)).symm
    change Multiplicative.toAdd (show G6.PermMod 5 from
      ((κ (β ⟨(π γ : MulAut W) w, Subgroup.mem_top _⟩) : ↥(FFModel.altDn 5).sec) :
        (FFModel.altDn 5).Amb)) = _
    rw [he, hκ]
    rfl

theorem card_eq_of_isA5Coord [Finite W] {Λ : Subgroup (MulAut W)}
    {π : alternatingGroup (Fin 5) →* Λ} {Ψ : W → Fin 5 → ZMod 2} (h : IsA5Coord Λ π Ψ) :
    Nat.card W = 2 ^ 4 := by
  obtain ⟨-, -, hinj, hO, honto, -⟩ := h
  have hb : Function.Bijective (fun w => (⟨Ψ w, hO w⟩ : {u : Fin 5 → ZMod 2 // IsO u})) :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun ⟨u, hu⟩ => by
      obtain ⟨w, hw⟩ := honto u hu
      exact ⟨w, Subtype.ext hw⟩⟩
  rw [Nat.card_eq_of_bijective _ hb, card_O]
  norm_num

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
