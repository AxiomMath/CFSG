module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

theorem card_coreMod_three : Nat.card (G6.coreMod 3) = 4 := by
  show Nat.card {x : G6.PermMod 3 // ∑ i, Multiplicative.toAdd x i = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem natKer_three : G6.natKer 3 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hsq : G6.allOnes 3 ^ 2 = 1 := by decide +kernel
  have hne : G6.allOnes 3 ≠ 1 := by decide +kernel
  have hnot : G6.allOnes 3 ∉ G6.coreMod 3 := by
    intro h
    have h' : ∑ i : Fin 3, Multiplicative.toAdd (G6.allOnes 3) i = 0 := h
    revert h'; decide +kernel
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (G6.allOnes 3) = 2 := orderOf_eq_prime hsq hne
  have hk2 : G6.allOnes 3 ^ k = G6.allOnes 3 ^ (k % 2) := by
    have := zpow_mod_orderOf (G6.allOnes 3) k
    rw [hord] at this
    exact_mod_cast this.symm
  have hm : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hm with hm | hm
  · rw [hm] at hk2; simp at hk2
    exact Subtype.ext (hk.symm.trans hk2)
  · rw [hm] at hk2; simp at hk2
    exfalso
    have hu' : (u : G6.PermMod 3) = G6.allOnes 3 := by rw [← hk2]; exact hk.symm
    have := u.2
    rw [hu'] at this
    exact hnot this

theorem coreMod_three_orbit : ∀ u : G6.PermMod 3, ∑ i, Multiplicative.toAdd u i = 0 → u ≠ 1 →
    ∀ v : G6.PermMod 3, ∑ i, Multiplicative.toAdd v i = 0 →
      v = 1 ∨ ∃ σ : Equiv.Perm (Fin 3), G6.permAct 3 σ u = v := by
  decide +kernel

theorem mem_cSecIn {F L X : Subgroup G} (hFL : F ≤ Subgroup.normalizer (L : Set G)) {f : G}
    (hf : f ∈ cSecIn F L X) : f ∈ F ∧ ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ L := by
  induction hf using Subgroup.closure_induction with
  | mem f hf => exact hf
  | one => exact ⟨F.one_mem, fun x _ => by simp⟩
  | mul f g _ _ hf hg =>
    refine ⟨F.mul_mem hf.1 hg.1, fun x hx => ?_⟩
    have e : f * g * x * (f * g)⁻¹ * x⁻¹ =
        (f * (g * x * g⁻¹ * x⁻¹) * f⁻¹) * (f * x * f⁻¹ * x⁻¹) := by group
    rw [e]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hFL hf.1) _).mp (hg.2 x hx)) (hf.2 x hx)
  | inv f _ hf =>
    refine ⟨F.inv_mem hf.1, fun x hx => ?_⟩
    have e : f⁻¹ * x * f⁻¹⁻¹ * x⁻¹ = f⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * f⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hFL (F.inv_mem hf.1)) _).mp (L.inv_mem (hf.2 x hx))

namespace NatSn

variable {F L X : Subgroup G} [(L.subgroupOf X).Normal]

theorem normalizes (h : NaturalSn 3 F L X) : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ ∈ X := by
  obtain ⟨θ, β, -, -, hβs, -, hequiv⟩ := h
  intro f hf x hx
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
  obtain ⟨hfx, -⟩ := hequiv ⟨f, hf⟩ u ⟨x, hx⟩ hu
  exact hfx

theorem relIndex_eq_four (h : NaturalSn 3 F L X) : L.relIndex X = 4 := by
  obtain ⟨θ, β, -, -, hβs, hβk, -⟩ := h
  have hker : β.ker = ⊥ := by rw [hβk, natKer_three]
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hker
  let e : ↥(G6.coreMod 3) ≃* (↥X ⧸ L.subgroupOf X) := MulEquiv.ofBijective β ⟨hinj, hβs⟩
  show Nat.card (↥X ⧸ L.subgroupOf X) = 4
  rw [← Nat.card_congr e.toEquiv, card_coreMod_three]

theorem relIndex_cSecIn (h : NaturalSn 3 F L X) : (cSecIn F L X).relIndex F = 6 := by
  obtain ⟨θ, -, hθs, hθk, -⟩ := h
  have h1 := Subgroup.index_ker θ
  rw [hθk, θ.range_eq_top_of_surjective hθs, Subgroup.card_top] at h1
  unfold Subgroup.relIndex
  rw [h1, Nat.card_perm]
  simp [Nat.factorial]

theorem irreducible (h : NaturalSn 3 F L X) {Y : Subgroup G} (hLY : L ≤ Y) (hYX : Y ≤ X)
    (hinv : ∀ f ∈ F, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) : Y = L ∨ Y = X := by
  obtain ⟨θ, β, hθs, -, hβs, -, hequiv⟩ := h
  let π : ↥X →* ↥X ⧸ L.subgroupOf X := QuotientGroup.mk' (L.subgroupOf X)
  let Yb : Subgroup (↥X ⧸ L.subgroupOf X) := (Y.subgroupOf X).map π
  let Yh : Subgroup ↥(G6.coreMod 3) := Yb.comap β
  have hmem : ∀ x : ↥X, π x ∈ Yb ↔ (x : G) ∈ Y := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have h1 : y⁻¹ * x ∈ L.subgroupOf X := QuotientGroup.eq.mp hyx
      have h2 : (y : G)⁻¹ * (x : G) ∈ L := h1
      have h3 : (y : G) ∈ Y := hy
      have : (x : G) = (y : G) * ((y : G)⁻¹ * (x : G)) := by group
      rw [this]
      exact Y.mul_mem h3 (hLY h2)
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hact : ∀ u ∈ Yh, ∀ σ : Equiv.Perm (Fin 3), G6.coreAct 3 σ u ∈ Yh := by
    intro u hu σ
    obtain ⟨f, rfl⟩ := hθs σ
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β u)
    have hxY : (x : G) ∈ Y := (hmem x).mp (by
      show π x ∈ Yb
      have : π x = β u := hx
      rw [this]; exact hu)
    obtain ⟨hfx, hres⟩ := hequiv f u x hx.symm
    show β (G6.coreAct 3 (θ f) u) ∈ Yb
    rw [hres]
    exact (hmem ⟨(f : G) * (x : G) * (f : G)⁻¹, hfx⟩).mpr (hinv f f.2 x hxY)
  by_cases hY1 : ∀ u ∈ Yh, u = 1
  · left
    refine le_antisymm (fun y hy => ?_) hLY
    have hyX : y ∈ X := hYX hy
    obtain ⟨u, hu⟩ := hβs (π ⟨y, hyX⟩)
    have huY : u ∈ Yh := by
      show β u ∈ Yb
      rw [hu]; exact (hmem ⟨y, hyX⟩).mpr hy
    have h1 : u = 1 := hY1 u huY
    rw [h1, map_one] at hu
    have : (⟨y, hyX⟩ : ↥X) ∈ L.subgroupOf X := (QuotientGroup.eq_one_iff _).mp hu.symm
    exact this
  · right
    push Not at hY1
    obtain ⟨u₀, hu₀, hu₀1⟩ := hY1
    have hall : ∀ v : ↥(G6.coreMod 3), v ∈ Yh := by
      intro v
      have := coreMod_three_orbit u₀.1 u₀.2 (fun h => hu₀1 (Subtype.ext h)) v.1 v.2
      rcases this with h1 | ⟨σ, hσ⟩
      · have : v = 1 := Subtype.ext h1
        rw [this]; exact Yh.one_mem
      · have : G6.coreAct 3 σ u₀ = v := Subtype.ext hσ
        rw [← this]; exact hact u₀ hu₀ σ
    refine le_antisymm hYX (fun x hx => ?_)
    obtain ⟨u, hu⟩ := hβs (π ⟨x, hx⟩)
    have : π ⟨x, hx⟩ ∈ Yb := by rw [← hu]; exact hall u
    exact (hmem ⟨x, hx⟩).mp this

end NatSn

end S152Fin

end CFSG.Quasithin
