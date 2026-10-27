module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10B
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.E10

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem secIdx_le_two_of_le {x : G} {Z N K : Subgroup G}
    (hNZ : N ≤ Subgroup.normalizer (Z : Set G)) (hxZ : x ∈ Subgroup.normalizer (Z : Set G))
    (hKN : K ≤ N) (hK2 : K.relIndex N ≤ 2) (hK : ∀ e ∈ K, x * e * x⁻¹ * e⁻¹ ∈ Z) :
    secIdx (Subgroup.zpowers x) Z N ≤ 2 := by
  have hle : K ≤ fixSecIn (Subgroup.zpowers x) Z N := fun e he =>
    (mem_fixSecIn_zpowers_iff hNZ hxZ).mpr ⟨hKN he, hK e he⟩
  have h0 : K.relIndex N ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact (Subgroup.relIndex_le_of_le_left hle h0).trans hK2

omit [Finite G] in
theorem sup_decomp {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    ∀ t ∈ A ⊔ B, ∃ u ∈ B, ∃ v : A, t = u * v := by
  intro t ht
  rw [sup_comm] at ht
  obtain ⟨u, hu, v, hv, h⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hAB).mp ht
  exact ⟨u, hu, ⟨v, hv⟩, h⟩

omit [Finite G] in
theorem sup_coset {A B : Subgroup G} (hA : Nat.card A = 2)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    ∀ t₁ ∈ A ⊔ B, t₁ ∉ B → ∀ t₂ ∈ A ⊔ B, t₂ ∉ B → t₁⁻¹ * t₂ ∈ B := by
  intro t₁ h₁ n₁ t₂ h₂ n₂
  obtain ⟨u₁, hu₁, v₁, e₁⟩ := sup_decomp hAB t₁ h₁
  obtain ⟨u₂, hu₂, v₂, e₂⟩ := sup_decomp hAB t₂ h₂
  have hv1 : (v₁ : G) ≠ 1 := by
    intro h
    rw [h, mul_one] at e₁
    exact n₁ (e₁ ▸ hu₁)
  have hv : (v₂ : G) = v₁ := by
    rcases card_two_cases hA v₁.2 hv1 v₂ v₂.2 with h | h
    · rw [h, mul_one] at e₂
      exact absurd (e₂ ▸ hu₂) n₂
    · exact h
  have hn : ((v₁ : G))⁻¹ ∈ Subgroup.normalizer (B : Set G) := hAB (A.inv_mem v₁.2)
  have key : ((v₁ : G))⁻¹ * (u₁⁻¹ * u₂) * ((v₁ : G))⁻¹⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (B.mul_mem (B.inv_mem hu₁) hu₂)
  have e : t₁⁻¹ * t₂ = ((v₁ : G))⁻¹ * (u₁⁻¹ * u₂) * ((v₁ : G))⁻¹⁻¹ := by
    rw [e₁, e₂, hv]
    group
  rw [e]
  exact key

omit [Finite G] in
theorem sup_inter_le {A B W : Subgroup G} (hA : Nat.card A = 2)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hBW : B ≤ W) (hAW : ¬ A ≤ W) :
    ∀ t ∈ A ⊔ B, t ∈ W → t ∈ B := by
  intro t ht htW
  obtain ⟨u, hu, v, e⟩ := sup_decomp hAB t ht
  by_cases hv : (v : G) = 1
  · rw [hv, mul_one] at e
    exact e ▸ hu
  · exfalso
    have hvW : (v : G) ∈ W := by
      have : (v : G) = u⁻¹ * t := by rw [e]; group
      rw [this]
      exact W.mul_mem (W.inv_mem (hBW hu)) htW
    refine hAW fun y hy => ?_
    rcases card_two_cases hA v.2 hv y hy with h | h
    · rw [h]; exact W.one_mem
    · rw [h]; exact hvW

omit [Finite G] in
theorem comm_inv_mul {x : G} {W : Subgroup G} (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) {a b : G} (ha : a ∈ W) (hb : b ∈ W) :
    x * (a⁻¹ * b) * x⁻¹ * (a⁻¹ * b)⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ * (x * b * x⁻¹ * b⁻¹) := by
  have ha₁ : x * a * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxW a).mp ha
  have hb₁ : x * b * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxW b).mp hb
  have hc : a * ((x * a * x⁻¹)⁻¹ * (x * b * x⁻¹) * b⁻¹) =
      ((x * a * x⁻¹)⁻¹ * (x * b * x⁻¹) * b⁻¹) * a :=
    hWc a ha _ (W.mul_mem (W.mul_mem (W.inv_mem ha₁) hb₁) (W.inv_mem hb))
  have e1 : x * (a⁻¹ * b) * x⁻¹ * (a⁻¹ * b)⁻¹ =
      ((x * a * x⁻¹)⁻¹ * (x * b * x⁻¹) * b⁻¹) * a := by group
  have e2 : (x * a * x⁻¹ * a⁻¹)⁻¹ * (x * b * x⁻¹ * b⁻¹) =
      a * ((x * a * x⁻¹)⁻¹ * (x * b * x⁻¹) * b⁻¹) := by group
  rw [e1, e2, hc]

theorem final_contra (hS : Sit H M S) (hT : ClaimT H M)
    {β α' m γ' α : Geo H M} (hp : S34.PD β α') (hb : Back H M β α' m γ') (hα : α ∈ nbrs β)
    (hWQ : Wl α ≤ Qv γ') {x : G} (hx : x ∈ stab α) (hxQ : x ∉ Qv α)
    (hcomm : ∀ e ∈ Wl α ⊓ stab α', x * e * x⁻¹ * e⁻¹ ∈ Zv α' ⊔ Zv β) : False := by
  obtain ⟨hvm, hvγ, hd3, hd2, hne, hdγα⟩ := back_facts hS hp hb
  have hvα : vtype α = true := vtype_nbr_S5 hp.vδ hα
  have hαβ : β ∈ nbrs α := mem_nbrs_symm.mp hα
  have hZβα : Zv β ≤ Zv α := Zv_le_Zv_of_nbr hS hp.vδ hα
  have hZW : Zv α ≤ Wl α := (Zv_le_Vn hα).trans (Vn_le_Wl hαβ)
  have hWc := Wl_comm hS α
  have hconj : ∀ w ∈ Wl α, ∀ z ∈ Wl α, w * z * w⁻¹ = z := fun w hw z hz => by
    rw [hWc w hw z hz]; group
  have hNZ : Wl α ≤ Subgroup.normalizer (Zv α : Set G) := fun w hw => by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [hconj w hw z (hZW hz)]
      exact hz
    · intro hz
      have h1 := hconj w⁻¹ ((Wl α).inv_mem hw) (w * z * w⁻¹) (hZW hz)
      have : z = w * z * w⁻¹ := by
        calc z = w⁻¹ * (w * z * w⁻¹) * w⁻¹⁻¹ := by group
          _ = w * z * w⁻¹ := h1
      rw [this]
      exact hz
  have hxZ : x ∈ Subgroup.normalizer (Zv α : Set G) :=
    stab_le_normalizer_Zv hS.glob.amalg α hx
  have hxW : x ∈ Subgroup.normalizer (Wl α : Set G) := Wl_normal α hx
  have hcard : Nat.card (Zv α') = 2 := hS.cardZ5 α' hp.vδ'
  have hZ'β : Zv α' ≤ Subgroup.normalizer (Zv β : Set G) := fun z hz =>
    stab_le_normalizer_Zv hS.glob.amalg β
      ((PD_Vn_le_stab hS hp).2 (Zv_le_Vn_S5 hS hp.vδ' hz))
  have hWm : Wl α ≤ stab m := fun w hw => Qv_le_stab hS (mem_nbrs_symm.mp hb.2.1) (hWQ hw)
  have h2 : secIdx (Subgroup.zpowers x) (Zv α) (Wl α) ≤ 2 := by
    by_cases hZ' : Zv α' ≤ Wl α
    · have hWst : Wl α ≤ stab α' := fun w hw =>
        mem_stab_of_centralizes hS hvm (mem_nbrs_symm.mp hb.1) (hWm hw) fun z hz =>
          hconj w hw z (hZ' hz)
      have hKW : fixSecIn (Subgroup.zpowers x) (Zv α) (Wl α) ≤ Wl α :=
        (Subgroup.closure_le _).mpr fun _ h => h.1
      show (fixSecIn (Subgroup.zpowers x) (Zv α) (Wl α)).relIndex (Wl α) ≤ 2
      refine relIndex_le_two_of hKW ?_
      intro a ha haK c hc hcK
      have hca : x * a * x⁻¹ * a⁻¹ ∉ Zv α := fun h =>
        haK ((mem_fixSecIn_zpowers_iff hNZ hxZ).mpr ⟨ha, h⟩)
      have hcc : x * c * x⁻¹ * c⁻¹ ∉ Zv α := fun h =>
        hcK ((mem_fixSecIn_zpowers_iff hNZ hxZ).mpr ⟨hc, h⟩)
      have hTa := hcomm a ⟨ha, hWst ha⟩
      have hTc := hcomm c ⟨hc, hWst hc⟩
      have key := sup_coset hcard hZ'β _ hTa (fun h => hca (hZβα h)) _ hTc
        (fun h => hcc (hZβα h))
      refine (mem_fixSecIn_zpowers_iff hNZ hxZ).mpr ⟨(Wl α).mul_mem ((Wl α).inv_mem ha) hc, ?_⟩
      rw [comm_inv_mul hWc hxW ha hc]
      exact hZβα key
    · refine secIdx_le_two_of_le hNZ hxZ (K := Wl α ⊓ stab α') inf_le_left ?_ ?_
      · exact relIndex_le_two_of_le_Qv hS hvm (mem_nbrs_symm.mp hb.1) hb.2.1 hne hWQ
      · intro e he
        have ht := hcomm e he
        have hxe : x * e * x⁻¹ * e⁻¹ ∈ Wl α :=
          (Wl α).mul_mem ((Subgroup.mem_normalizer_iff.mp hxW e).mp he.1) ((Wl α).inv_mem he.1)
        exact hZβα (sup_inter_le hcard hZ'β (hZβα.trans hZW) hZ' _ ht hxe)
  have := hT α hvα x hx hxQ
  omega

end S35.E10

end F53.Stellmacher

end CFSG.Quasithin
