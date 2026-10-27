module

public import CFSG.Quasithin.Background.FLc2MLCore
public import CFSG.Quasithin.Background.FLcP0Ker
public import CFSG.Quasithin.Background.FLcNat
public import CFSG.Quasithin.Background.FLcGrp

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G]

theorem ml_abstract [Finite G] {V : Type} [CommGroup V] (ι : V →* G) (hι : Function.Injective ι)
    {L SL Ml : Subgroup G} {n c : ℕ} (hn3 : 3 ≤ n) (hc : IsNode n c) (hSylL : IsSylowTwoOf SL L)
    (θ : ↥L →* MulAut V) (hθ : ∀ (l : ↥L) (v : V), ι (θ l v) = (l : G) * ι v * (l : G)⁻¹)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (ρ : SLt n →* MulAut V) (hρinj : Function.Injective ρ)
    (hρθ : ∀ l : ↥L, ∃ g, ρ g = θ l) (hθρ : ∀ g, ∃ l : ↥L, θ l = ρ g) (Zu' : Subgroup V)
    (hfixV : ∀ g : SLt n, ∀ v ∈ Zu', (∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) v = v) →
      ∀ i, ∀ hi : IsNode n i, i ≠ c →
        (ρ (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹)) v = v)
    (hZuS : ∀ s : ↥L, (s : G) ∈ SL → ∀ v ∈ Zu', θ s v = v)
    (hMlL : Ml ≤ L) (hMl : L ⊓ Subgroup.centralizer ((Zu'.map ι : Subgroup G) : Set G) ≤ Ml)
    (hMlne : Ml ≠ L)
    (hnc : ¬ L ≤ Subgroup.centralizer ((Zu'.map ι : Subgroup G) : Set G)) :
    Ml = L ⊓ Subgroup.centralizer ((Zu'.map ι : Subgroup G) : Set G) := by
  set Zu : Subgroup G := Zu'.map ι with hZu
  have hSLL : SL ≤ L := hSylL.1
  have hcent : ∀ (W : Subgroup V) (x : ↥L),
      (x : G) ∈ Subgroup.centralizer ((W.map ι : Subgroup G) : Set G) ↔ ∀ v ∈ W, θ x v = v := by
    intro W x
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h v hv
      have h1 : ι v * (x : G) = (x : G) * ι v := h (ι v) ⟨v, hv, rfl⟩
      apply hι
      rw [hθ]
      calc (x : G) * ι v * (x : G)⁻¹ = (ι v * (x : G)) * (x : G)⁻¹ := by rw [h1]
        _ = ι v := by group
    · rintro h _ ⟨v, hv, rfl⟩
      have h1 := hθ x v
      rw [h v hv] at h1
      calc ι v * (x : G) = ((x : G) * ι v * (x : G)⁻¹) * (x : G) := by rw [← h1]
        _ = (x : G) * ι v := by group
  have hθr : ∀ l : ↥L, θ l ∈ ρ.range := fun l => by
    obtain ⟨g, hg⟩ := hρθ l
    exact ⟨g, hg⟩
  let e : SLt n ≃* ↥ρ.range := MonoidHom.ofInjective hρinj
  let α₀ : ↥L →* SLt n := e.symm.toMonoidHom.comp (θ.codRestrict ρ.range hθr)
  have hα₀ : ∀ l : ↥L, ρ (α₀ l) = θ l := fun l => by
    have h1 : e (α₀ l) = θ.codRestrict ρ.range hθr l := e.apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    exact h2
  have hα₀s : Function.Surjective α₀ := fun g => by
    obtain ⟨l, hl⟩ := hθρ g
    exact ⟨l, hρinj (by rw [hα₀, hl])⟩
  have hα₀k : ∀ l : ↥L, α₀ l = 1 ↔ (l : G) ∈ Subgroup.centralizer ((⊤ : Subgroup V).map ι : Set G) := by
    intro l
    rw [hcent ⊤ l]
    constructor
    · intro h v _
      have : ρ (α₀ l) = 1 := by rw [h, map_one]
      rw [hα₀] at this
      rw [this]
      rfl
    · intro h
      apply hρinj
      rw [hα₀, map_one]
      refine MulEquiv.ext fun v => ?_
      exact h v trivial
  have hK2 := kernel_isPGroup (by omega : 2 ≤ n) α₀ hα₀s hα₀k hsimple
  have hKSL : ∀ l : ↥L, α₀ l = 1 → (l : G) ∈ SL := by
    intro l hl
    have hnorm : ((L ⊓ Subgroup.centralizer (((⊤ : Subgroup V).map ι : Subgroup G) : Set G)).subgroupOf L).Normal := by
      have : α₀.ker = (L ⊓ Subgroup.centralizer (((⊤ : Subgroup V).map ι : Subgroup G) : Set G)).subgroupOf L := by
        ext a
        rw [MonoidHom.mem_ker, hα₀k, Subgroup.mem_subgroupOf]
        exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
      rw [← this]
      exact α₀.normal_ker
    have hle := A4.le_of_normal_of_isSylowTwoOf hSylL inf_le_left hnorm hK2
    exact hle ⟨l.2, (hα₀k l).1 hl⟩
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hSylL
  let Q : Sylow 2 (SLt n) := Sylow.mapSurjective (f := α₀) hα₀s P
  have hQ : (Q : Subgroup (SLt n)) = (P : Subgroup ↥L).map α₀ := Sylow.coe_mapSurjective hα₀s P
  obtain ⟨g, hg⟩ := exists_conj_eq_unitriangular (by omega : 1 ≤ n) Q
  let α : ↥L →* SLt n := (MulAut.conj g⁻¹).toMonoidHom.comp α₀
  have hαs : Function.Surjective α := (MulAut.conj g⁻¹).surjective.comp hα₀s
  have hαk : ∀ x : ↥L, α x = 1 → (x : G) ∈ SL := by
    intro x hx
    apply hKSL
    have : g⁻¹ * α₀ x * g⁻¹⁻¹ = 1 := hx
    have h2 : α₀ x = 1 := by
      have h3 : g * (g⁻¹ * α₀ x * g⁻¹⁻¹) * g⁻¹ = α₀ x := by group
      rw [this] at h3
      simpa using h3.symm
    exact h2
  have hαB : (SL.subgroupOf L).map α = Ut n := by
    have h1 : (SL.subgroupOf L).map α₀ = conjSub g (Ut n) := by
      rw [← hP, ← hQ, hg]
      rfl
    have h2 : (SL.subgroupOf L).map α = conjSub g⁻¹ ((SL.subgroupOf L).map α₀) := by
      rw [conjSub, Subgroup.map_map]
    rw [h2, h1, conjSub_inv_conjSub]
  have hρα : ∀ x : ↥L, ρ (g * α x * g⁻¹) = θ x := by
    intro x
    have : g * α x * g⁻¹ = α₀ x := by
      show g * (g⁻¹ * α₀ x * g⁻¹⁻¹) * g⁻¹ = α₀ x
      group
    rw [this, hα₀]
  have hR : ∀ i, ∀ hi : IsNode n i, i ≠ c →
      ∃ x : ↥L, α x = reflection n (ZMod 2) i hi.1 hi.2 ∧
        (x : G) ∈ L ⊓ Subgroup.centralizer (Zu : Set G) := by
    intro i hi hic
    obtain ⟨x, hx⟩ := hαs (reflection n (ZMod 2) i hi.1 hi.2)
    refine ⟨x, hx, x.2, (hcent Zu' x).2 fun v hv => ?_⟩
    have hs : ∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) v = v := by
      intro s hs
      rw [← hαB] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      rw [hρα]
      exact hZuS t (Subgroup.mem_subgroupOf.1 ht) v hv
    have := hfixV g v hv hs i hi hic
    rw [← hx, hρα] at this
    exact this
  have hSLP : SL ≤ L ⊓ Subgroup.centralizer (Zu : Set G) := fun s hs =>
    ⟨hSLL hs, (hcent Zu' ⟨s, hSLL hs⟩).2 fun v hv => hZuS ⟨s, hSLL hs⟩ hs v hv⟩
  have hPne : L ⊓ Subgroup.centralizer (Zu : Set G) ≠ L := fun h => hnc (by
    intro x hx
    have : x ∈ L ⊓ Subgroup.centralizer (Zu : Set G) := by rw [h]; exact hx
    exact this.2)
  exact eq_of_reflections hc hSLP inf_le_left hMl hMlL α hαk hαB hPne hMlne hR

end CFSG.Quasithin.FLc
