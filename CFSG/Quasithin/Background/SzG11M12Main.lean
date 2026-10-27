module

public import CFSG.Quasithin.Background.SzG11SConf
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.Quasithin.Background.SzG11M12Out

public section

namespace CFSG.Quasithin.G11.SzG11S

namespace M12Vec

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

variable [Finite V]

theorem rank_ge_three
    (c : PCore H) (Γ X : Subgroup (GLV V)) (hHΓ : H ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hC : ∀ x ∈ Γ, (∀ h ∈ H, x * h = h * x) → x = 1)
    (hV : Module.finrank (ZMod 2) V = 10) (hXΓ : X ≤ Γ) (hsq : ∀ x ∈ X, x * x = 1)
    (a : GLV V) (ha : a ∈ X) (h1 : a ≠ 1) :
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) := by
  have haΓ : a ∈ Γ := hXΓ ha
  have hx : ∀ h ∈ H, a * h * a⁻¹ ∈ H := hN a haΓ
  have hx' : ∀ h ∈ H, a⁻¹ * h * a ∈ H := fun h hh => by
    simpa using hN a⁻¹ (Γ.inv_mem haΓ) h hh
  rcases classify c a hx hx' with hin | hout
  · have haH : a ∈ H := mem_of_inner c Γ hHΓ hC a haΓ hx hin
    exact inner_rank c ⟨a, haH⟩ (fun h => h1 (congrArg Subtype.val h))
      (Subtype.ext (hsq a ha))
  · have hrn := LinearMap.finrank_range_add_finrank_ker (a.toLinearMap - LinearMap.id)
    have hker : Module.finrank (ZMod 2) (LinearMap.ker (a.toLinearMap - LinearMap.id)) ≤ 6 := by
      apply finrank_le_six c hV
      intro i j hij hmem
      have h2 : a (c.pr i j) = c.pr i j := by
        have : (a.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) (c.pr i j) = 0 := hmem
        simpa [sub_eq_zero] using this
      exact outer_pr_ne c a hx hout hij hij h2
    omega

theorem finite_glv : Finite (GLV V) :=
  Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

omit [Finite V] in
theorem sub_sub_self_aux (v u : V) : v - u - (u - v) = 0 := by
  rw [sub_eq_add_neg (v - u) (u - v), neg_sub]
  exact ZModModule.add_self _

theorem fixed_ge_two
    (c : PCore H) (Γ X : Subgroup (GLV V)) (hHΓ : H ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hC : ∀ x ∈ Γ, (∀ h ∈ H, x * h = h * x) → x = 1)
    (hXΓ : X ≤ Γ) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hsq : ∀ x ∈ X, x * x = 1)
    (hX : Nat.card X = 16) : 2 ≤ Module.finrank (ZMod 2) (fixedSpace X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (GLV V) := finite_glv
  have hcl : ∀ x ∈ X, x ∈ H ∨ OuterAct c x := by
    intro x hx
    have hxΓ : x ∈ Γ := hXΓ hx
    have hx1 : ∀ h ∈ H, x * h * x⁻¹ ∈ H := hN x hxΓ
    have hx2 : ∀ h ∈ H, x⁻¹ * h * x ∈ H := fun h hh => by
      simpa using hN x⁻¹ (Γ.inv_mem hxΓ) h hh
    rcases classify c x hx1 hx2 with hin | hout
    · exact Or.inl (mem_of_inner c Γ hHΓ hC x hxΓ hx1 hin)
    · exact Or.inr hout
  have hprod : ∀ x ∈ X, ∀ y ∈ X, x ∉ H → y ∉ H → x * y ∈ H := by
    intro x hx y hy hxH hyH
    have hox := (hcl x hx).resolve_left hxH
    have hoy := (hcl y hy).resolve_left hyH
    have hxy : x * y ∈ Γ := Γ.mul_mem (hXΓ hx) (hXΓ hy)
    have hy1 : ∀ h ∈ H, y * h * y⁻¹ ∈ H := hN y (hXΓ hy)
    refine mem_of_inner c Γ hHΓ hC (x * y) hxy ?_ (inner_of_outer_mul c x y hy1 hox hoy)
    intro h hh
    have h1 := hN x (hXΓ hx) _ (hy1 h hh)
    have e : x * y * h * (x * y)⁻¹ = x * (y * h * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact h1
  let K : Subgroup ↥X := H.subgroupOf X
  have hK8 : 8 ≤ Nat.card K := by
    have hcm := K.card_mul_index
    rw [hX] at hcm
    have hidx : K.index ≤ 2 := by
      by_cases hall : ∀ b : ↥X, b ∈ K
      · have : K = ⊤ := eq_top_iff.2 fun b _ => hall b
        rw [this, Subgroup.index_top]
        norm_num
      · push Not at hall
        obtain ⟨a, haK⟩ := hall
        have h2 : K.index = 2 := by
          rw [Subgroup.index_eq_two_iff]
          refine ⟨a, fun b => ?_⟩
          by_cases hb : b ∈ K
          · refine Or.inr ⟨hb, fun hba => haK ?_⟩
            have := K.mul_mem (K.inv_mem hb) hba
            simpa using this
          · refine Or.inl ⟨?_, hb⟩
            have hbH : (b : GLV V) ∉ H := fun h => hb (Subgroup.mem_subgroupOf.2 h)
            have haH : (a : GLV V) ∉ H := fun h => haK (Subgroup.mem_subgroupOf.2 h)
            exact Subgroup.mem_subgroupOf.2 (hprod b b.2 a a.2 hbH haH)
        rw [h2]
    have hi : K.index = 0 ∨ K.index = 1 ∨ K.index = 2 := by omega
    rcases hi with h | h | h <;> rw [h] at hcm <;> omega
  have hK16 : Nat.card K ∣ 2 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card K
    rw [hX] at this
    exact this
  have h8 : 2 ^ 3 ∣ Nat.card K := by
    obtain ⟨m, hm, hmK⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hK16
    have h3m : 3 ≤ m := by
      by_contra hlt
      have h2m : m ≤ 2 := by omega
      have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2m
      omega
    rw [hmK]
    exact pow_dvd_pow 2 h3m
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) 2 h8
  let E : Subgroup (GLV V) := (E₀.map K.subtype).map X.subtype
  have hEcard : Nat.card E = 8 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective K.subtype_injective, hE₀]
    norm_num
  have hEX : E ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hEH : E ≤ H := by
    rintro _ ⟨y, ⟨z, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.1 z.2
  have h3 := fixed_E8 c E hEH hEcard (fun x hx y hy => hcomm x (hEX hx) y (hEX hy))
    (fun x hx => hsq x (hEX hx))
  have hEi : (E.subgroupOf X).index = 2 := by
    have hcm := (E.subgroupOf X).card_mul_index
    rw [hX] at hcm
    have h8' : Nat.card (E.subgroupOf X) = 8 := by
      rw [← hEcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
    rw [h8'] at hcm
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hEi
  have hya : ∀ y ∈ X, y ∈ E ∨ y * (a : GLV V) ∈ E := by
    intro y hy
    rcases ha ⟨y, hy⟩ with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inr (Subgroup.mem_subgroupOf.1 h1)
    · exact Or.inl (Subgroup.mem_subgroupOf.1 h1)
  have haa : ∀ v : V, (a : GLV V) ((a : GLV V) v) = v := fun v => by
    have := congrArg (fun g : GLV V => g v) (hsq a a.2)
    simpa using this
  have haF : ∀ v ∈ fixedSpace E, (a : GLV V) v ∈ fixedSpace E := by
    intro v hv e he
    have hc' : e * (a : GLV V) = (a : GLV V) * e := hcomm e (hEX he) a a.2
    have h1 : e ((a : GLV V) v) = (a : GLV V) (e v) := by
      have := congrArg (fun g : GLV V => g v) hc'
      simpa using this
    rw [h1, hv e he]
  have hgF : ∀ v ∈ fixedSpace E,
      (((a : GLV V).toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) v) ∈ fixedSpace E :=
    fun v hv => (fixedSpace E).sub_mem (haF v hv) hv
  let g : ↥(fixedSpace E) →ₗ[ZMod 2] ↥(fixedSpace E) :=
    ((a : GLV V).toLinearMap - LinearMap.id).restrict hgF
  have hgv : ∀ w : ↥(fixedSpace E), ((g w : ↥(fixedSpace E)) : V) = (a : GLV V) (w : V) - w :=
    fun w => rfl
  have hg2 : g ∘ₗ g = 0 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    show ((g (g w) : ↥(fixedSpace E)) : V) = 0
    rw [hgv, hgv, map_sub, haa]
    exact sub_sub_self_aux _ _
  have hrk : LinearMap.range g ≤ LinearMap.ker g := LinearMap.range_le_ker_iff.2 hg2
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hle := Submodule.finrank_mono hrk
  have hker2 : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker g) := by omega
  have hmap : (LinearMap.ker g).map (fixedSpace E).subtype ≤ fixedSpace X := by
    rintro _ ⟨w, hw, rfl⟩ y hy
    have hwa : (a : GLV V) (w : V) = (w : V) := by
      have h1 := congrArg Subtype.val (LinearMap.mem_ker.1 hw)
      rw [hgv] at h1
      exact sub_eq_zero.1 h1
    rcases hya y hy with hyE | hyaE
    · exact w.2 y hyE
    · have h1 := w.2 _ hyaE
      calc y ((fixedSpace E).subtype w) = y ((a : GLV V) (w : V)) := by
            rw [hwa]; rfl
        _ = (y * (a : GLV V)) (w : V) := rfl
        _ = (w : V) := h1
  calc 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker g) := hker2
    _ = Module.finrank (ZMod 2) ((LinearMap.ker g).map (fixedSpace E).subtype) :=
        (Submodule.finrank_map_subtype_eq _ _).symm
    _ ≤ _ := Submodule.finrank_mono hmap

end M12Vec

theorem noConfigM12 :
    NoConfigM12 := by
  intro V _ _ _ B Γ v₁ W X X₀ L hS _ hM hX hd hC
  obtain ⟨c⟩ := M12Vec.PCore.exists hM
  have hyp := hS.hyp
  have hLΓ : L ≤ Γ := hS.h108.component.1
  have hHΓ := normalClosure_le hLΓ
  have hN := normalClosure_normal Γ L
  rcases hyp.three with h3 | ⟨a, ha, hr, hv⟩
  · have h2 := M12Vec.fixed_ge_two c Γ X hHΓ hN hC hyp.X_le hyp.X_comm hyp.X_sq hX
    have hcard : Nat.card (fixedSpace X) = 2 ^ Module.finrank (ZMod 2) (fixedSpace X) :=
      (FiniteField.pow_finrank_eq_natCard 2 (fixedSpace X)).symm
    have h4 : 2 ^ 2 ≤ 2 ^ Module.finrank (ZMod 2) (fixedSpace X) :=
      Nat.pow_le_pow_right (by norm_num) h2
    have hsub : ((fixedSpace X : Submodule (ZMod 2) V) : Set V) ⊆ {0, v₁} := fun v hv => by
      rcases h3 v hv with h | h <;> simp [h]
    have hle : Nat.card (fixedSpace X) ≤ 2 := by
      have e1 : Nat.card (fixedSpace X) = Set.ncard (fixedSpace X : Set V) :=
        Nat.card_coe_set_eq _
      have e2 : Set.ncard (fixedSpace X : Set V) ≤ Set.ncard ({0, v₁} : Set V) :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      have e3 : Set.ncard ({0, v₁} : Set V) ≤ 2 := by
        calc Set.ncard ({0, v₁} : Set V) ≤ Set.ncard ({v₁} : Set V) + 1 :=
              Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      omega
    omega
  · by_cases h1 : a = 1
    · apply hyp.point
      rw [h1] at hv
      obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hv
      rw [← hw]
      simp
    · have := M12Vec.rank_ge_three c Γ X hHΓ hN hC hd hyp.X_le hyp.X_sq a ha h1
      omega

end CFSG.Quasithin.G11.SzG11S
