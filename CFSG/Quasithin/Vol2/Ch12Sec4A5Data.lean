module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Vol2.Ch12Sec4A5Model
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.H13.A5Mod

open Equiv

variable {G : Type} [Group G]

theorem conjAct_apply_coe (W : Subgroup G) (g : Subgroup.normalizer (W : Set G)) (w : ↥W) :
    ((conjAct W g w : ↥W) : G) = (g : G) * w * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion le_rfl g) w

structure Data (K W : Subgroup G) : Type where
  normalizes : K ≤ Subgroup.normalizer (W : Set G)
  q : ↥K →* ↥(alternatingGroup (Fin 5))
  q_surj : Function.Surjective q
  q_eq_one : ∀ k : ↥K, q k = 1 ↔ (k : G) ∈ Subgroup.centralizer (W : Set G)
  β : G → Fin 5 → ZMod 2
  β_mem : ∀ w ∈ W, β w ∈ ev5
  β_inj : ∀ w₁ ∈ W, ∀ w₂ ∈ W, β w₁ = β w₂ → w₁ = w₂
  β_surj : ∀ x ∈ ev5, ∃ w ∈ W, β w = x
  β_mul : ∀ w₁ ∈ W, ∀ w₂ ∈ W, β (w₁ * w₂) = β w₁ + β w₂
  β_conj : ∀ k : ↥K, ∀ w ∈ W,
    β ((k : G) * w * (k : G)⁻¹) = act5 (q k : Perm (Fin 5)) (β w)

theorem altDn_five_ker_eq_bot :
    ((Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5).subgroupOf (G6.coreMod 5)) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_subgroupOf] at hm
  obtain ⟨hz, hc⟩ := hm
  have hz' : (m : G6.PermMod 5) ∈ Subgroup.zpowers (G6.allOnes 5) := hz
  have hc' : (m : G6.PermMod 5) ∈ G6.coreMod 5 := hc
  have h5 : ∑ i : Fin 5, Multiplicative.toAdd (G6.allOnes 5) i = 1 := by
    simp only [G6.allOnes, toAdd_ofAdd]
    decide
  have h2 : G6.allOnes 5 ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [G6.allOnes]
    decide
  have hne : G6.allOnes 5 ≠ 1 := by
    intro h
    have := congrFun (congrArg Multiplicative.toAdd h) 0
    revert this
    simp [G6.allOnes]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (G6.allOnes 5) = 2 := orderOf_eq_prime h2 hne
  have hj' : (m : G6.PermMod 5) = 1 ∨ (m : G6.PermMod 5) = G6.allOnes 5 := by
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hord] at hz'
    simp only [Finset.mem_image, Finset.mem_range] at hz'
    obtain ⟨i, hi, he⟩ := hz'
    interval_cases i
    · left
      rw [← he, pow_zero]
    · right
      rw [← he, pow_one]
  rcases hj' with h1 | h1
  · exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  · exfalso
    rw [h1] at hc'
    have h0 : ∑ i : Fin 5, Multiplicative.toAdd (G6.allOnes 5) i = 0 := hc'
    rw [h5] at h0
    exact one_ne_zero h0

theorem toAdd_mem_ev5 {x : G6.PermMod 5} (hx : x ∈ G6.coreMod 5) :
    Multiplicative.toAdd x ∈ ev5 := by
  rw [mem_ev5]
  exact G6.mem_coreMod.1 hx

theorem ofAdd_mem_coreMod {x : Fin 5 → ZMod 2} (hx : x ∈ ev5) :
    Multiplicative.ofAdd x ∈ G6.coreMod 5 := by
  rw [G6.mem_coreMod]
  exact mem_ev5.1 hx

theorem conjAct_eq_one_iff (W : Subgroup G) (g : Subgroup.normalizer (W : Set G)) :
    conjAct W g = 1 ↔ (g : G) ∈ Subgroup.centralizer (W : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

@[expose] def coord (y : ↥(FFModel.altDn 5).sec) : Fin 5 → ZMod 2 :=
  Multiplicative.toAdd (show G6.PermMod 5 from y.1)

theorem coord_mem (y : ↥(FFModel.altDn 5).sec) : coord y ∈ ev5 :=
  toAdd_mem_ev5 y.2

theorem coord_injective : Function.Injective coord := fun _ _ h =>
  Subtype.ext (Multiplicative.toAdd.injective h)

theorem coord_mul (y z : ↥(FFModel.altDn 5).sec) : coord (y * z) = coord y + coord z := rfl

theorem coord_act (γ : ↥(alternatingGroup (Fin 5))) (y : ↥(FFModel.altDn 5).sec)
    (hy : (FFModel.altDn 5).act γ (y : (FFModel.altDn 5).Amb) ∈ (FFModel.altDn 5).sec) :
    coord ⟨(FFModel.altDn 5).act γ (y : (FFModel.altDn 5).Amb), hy⟩ =
      act5 (γ : Perm (Fin 5)) (coord y) := by
  funext i
  rfl

theorem exists_coord {x : Fin 5 → ZMod 2} (hx : x ∈ ev5) :
    ∃ y : ↥(FFModel.altDn 5).sec, coord y = x :=
  ⟨⟨Multiplicative.ofAdd x, ofAdd_mem_coreMod hx⟩, rfl⟩

theorem exists_data {K W : Subgroup G} (h : IsA5ModuleUnder K W) : Nonempty (Data K W) := by
  classical
  obtain ⟨hKW, hc, π, hπs, -, -, -, -, hsec, -, β₀, hβ₀s, hβ₀k, hβ₀i⟩ := h
  have hker : (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = ⊥ :=
    altDn_five_ker_eq_bot
  let e₀ : ↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec ≃*
      ↥(FFModel.altDn 5).sec :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans QuotientGroup.quotientBot
  have he₀ : ∀ m, e₀ (QuotientGroup.mk m) = m := fun m => rfl
  have hmk : ∀ u m, e₀ (β₀ u) = m → β₀ u = QuotientGroup.mk m := fun u m h' =>
    e₀.injective (h'.trans (he₀ m).symm)
  have hπi : Function.Injective π := by
    have : IsSimpleGroup (FFModel.altDn 5).Gam := alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h' | h'
    · exact (MonoidHom.ker_eq_bot_iff π).1 h'
    · exfalso
      obtain ⟨g, hg, x, hx, hgx⟩ := nontrivial
      let γ : (FFModel.altDn 5).Gam :=
        ⟨g, Equiv.Perm.mem_alternatingGroup.2 (mem_alt5.1 hg)⟩
      have hπγ : π γ = 1 := (MonoidHom.mem_ker).1 (h' ▸ Subgroup.mem_top γ)
      obtain ⟨m, hm⟩ := exists_coord hx
      obtain ⟨u, hu⟩ := hβ₀s (QuotientGroup.mk m)
      have h1 := hβ₀i γ u m (Subgroup.mem_top _) (hsec γ m m.2) hu
      have h2 : (⟨((π γ : ↥(autOn K W)) : MulAut ↥W) (u : ↥W), Subgroup.mem_top _⟩ :
          ↥(⊤ : Subgroup ↥W)) = u := by
        apply Subtype.ext
        rw [hπγ]
        rfl
      rw [h2, hu] at h1
      have h3 := congrArg e₀ h1
      rw [he₀, he₀] at h3
      apply hgx
      have h4 := congrArg coord h3
      rw [coord_act, hm] at h4
      exact h4.symm
  let π' := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  have hmemA : ∀ k : ↥K, conjAct W ⟨k, hKW k.2⟩ ∈ autOn K W := fun k =>
    ⟨⟨k, hKW k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
  let fW : ↥K →* ↥(autOn K W) :=
    ((conjAct W).comp (Subgroup.inclusion hKW)).codRestrict (autOn K W) hmemA
  have hfW : ∀ k : ↥K, ((fW k : ↥(autOn K W)) : MulAut ↥W) = conjAct W ⟨k, hKW k.2⟩ :=
    fun k => rfl
  let q : ↥K →* ↥(alternatingGroup (Fin 5)) := π'.symm.toMonoidHom.comp fW
  have hπq : ∀ k : ↥K, π (q k) = fW k := fun k => π'.apply_symm_apply (fW k)
  let βW : ↥W → Fin 5 → ZMod 2 := fun w => coord (e₀ (β₀ ⟨w, Subgroup.mem_top w⟩))
  let β : G → Fin 5 → ZMod 2 := fun g => if hg : g ∈ W then βW ⟨g, hg⟩ else 0
  have hβ : ∀ (w : G) (hw : w ∈ W), β w = βW ⟨w, hw⟩ := fun w hw => dite_eq_left hw
  refine ⟨⟨hKW, q, ?_, ?_, β, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro γ
    obtain ⟨⟨k, hkN⟩, hkK, he⟩ := Subgroup.mem_map.1 (π γ).2
    refine ⟨⟨k, Subgroup.mem_subgroupOf.1 hkK⟩, ?_⟩
    apply hπi
    rw [hπq]
    exact Subtype.ext he
  · intro k
    constructor
    · intro h1
      have h2 : fW k = 1 := by
        rw [← hπq, h1]
        exact π.map_one
      have h3 := congrArg Subtype.val h2
      rw [hfW] at h3
      exact (conjAct_eq_one_iff W ⟨k, hKW k.2⟩).1 h3
    · intro h1
      have h2 : fW k = 1 :=
        Subtype.ext (by rw [hfW]; exact (conjAct_eq_one_iff W ⟨k, hKW k.2⟩).2 h1)
      apply hπi
      rw [hπq, h2]
      exact π.map_one.symm
  · intro w hw
    rw [hβ w hw]
    exact coord_mem _
  · intro w₁ hw₁ w₂ hw₂ h12
    rw [hβ w₁ hw₁, hβ w₂ hw₂] at h12
    have h2 := e₀.injective (coord_injective h12)
    have h3 : β₀ (⟨⟨w₁, hw₁⟩, Subgroup.mem_top _⟩ * (⟨⟨w₂, hw₂⟩, Subgroup.mem_top _⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h4 := (hβ₀k _).1 h3
    rw [Subgroup.mem_bot] at h4
    have h5 := congrArg (fun x : ↥W => (x : G)) h4
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h5
    rw [mul_inv_eq_one] at h5
    exact h5
  · intro x hx
    obtain ⟨m, hm⟩ := exists_coord hx
    obtain ⟨u, hu⟩ := hβ₀s (e₀.symm m)
    refine ⟨((u : ↥W) : G), (u : ↥W).2, ?_⟩
    rw [hβ _ (u : ↥W).2]
    have hu' : (⟨⟨((u : ↥W) : G), (u : ↥W).2⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥W)) = u :=
      rfl
    show coord (e₀ (β₀ ⟨⟨((u : ↥W) : G), (u : ↥W).2⟩, Subgroup.mem_top _⟩)) = x
    rw [hu', hu, MulEquiv.apply_symm_apply, hm]
  · intro w₁ hw₁ w₂ hw₂
    rw [hβ w₁ hw₁, hβ w₂ hw₂, hβ _ (W.mul_mem hw₁ hw₂)]
    have h1 : (⟨⟨w₁ * w₂, W.mul_mem hw₁ hw₂⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥W)) =
        ⟨⟨w₁, hw₁⟩, Subgroup.mem_top _⟩ * ⟨⟨w₂, hw₂⟩, Subgroup.mem_top _⟩ := rfl
    show coord (e₀ (β₀ ⟨⟨w₁ * w₂, W.mul_mem hw₁ hw₂⟩, Subgroup.mem_top _⟩)) =
      coord (e₀ (β₀ ⟨⟨w₁, hw₁⟩, Subgroup.mem_top _⟩)) +
        coord (e₀ (β₀ ⟨⟨w₂, hw₂⟩, Subgroup.mem_top _⟩))
    rw [h1, map_mul, map_mul, coord_mul]
  · intro k w hw
    have hkw : (k : G) * w * (k : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (hKW k.2) w).1 hw
    rw [hβ _ hkw, hβ w hw]
    set u : ↥(⊤ : Subgroup ↥W) := ⟨⟨w, hw⟩, Subgroup.mem_top _⟩ with hudef
    set m := e₀ (β₀ u) with hmdef
    have hu := hmk u m hmdef.symm
    have h1 := hβ₀i (q k) u m (Subgroup.mem_top _) (hsec (q k) m m.2) hu
    have h2 : (⟨((π (q k) : ↥(autOn K W)) : MulAut ↥W) (u : ↥W), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup ↥W)) = ⟨⟨(k : G) * w * (k : G)⁻¹, hkw⟩, Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hπq, hfW]
      exact conjAct_apply_coe W ⟨k, hKW k.2⟩ ⟨w, hw⟩
    rw [h2] at h1
    have h3 := congrArg e₀ h1
    rw [he₀] at h3
    show coord (e₀ (β₀ ⟨⟨(k : G) * w * (k : G)⁻¹, hkw⟩, Subgroup.mem_top _⟩)) =
      act5 _ (coord m)
    rw [h3]
    exact coord_act (q k) m _

end CFSG.Quasithin.H13.A5Mod
