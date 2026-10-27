module

public import CFSG.Quasithin.Background.FLcFlagU
public import CFSG.Quasithin.Background.FLcNat
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.Background.FLcGrp

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G]

theorem exists_normalized [Finite G] {L B UL : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hB : IsSylowTwoOf B L) (α : ↥L →* SLt n) (β : ↥UL ≃* Multiplicative (Vt n))
    (hαs : Function.Surjective α)
    (hrel : ∀ (a : ↥L) (u v : ↥UL), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = mat (α a) *ᵥ Multiplicative.toAdd (β u)) :
    ∃ (α' : ↥L →* SLt n) (β' : ↥UL ≃* Multiplicative (Vt n)),
      Function.Surjective α' ∧ (∀ a, α' a = 1 ↔ α a = 1) ∧
      (B.subgroupOf L).map α' = Ut n ∧
      ∀ (a : ↥L) (u v : ↥UL), (v : G) = a * u * a⁻¹ →
        Multiplicative.toAdd (β' v) = mat (α' a) *ᵥ Multiplicative.toAdd (β' u) := by
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hB
  let Q : Sylow 2 (SLt n) := Sylow.mapSurjective (f := α) hαs P
  have hQ : (Q : Subgroup (SLt n)) = (P : Subgroup ↥L).map α := Sylow.coe_mapSurjective hαs P
  obtain ⟨g, hg⟩ := exists_conj_eq_unitriangular hn Q
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp α, β.trans (actM g⁻¹), ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj g⁻¹).surjective.comp hαs
  · intro a
    constructor
    · intro h
      have h1 : g⁻¹ * α a * g⁻¹⁻¹ = 1 := h
      have h2 : α a = 1 := by
        have h3 : g * (g⁻¹ * α a * g⁻¹⁻¹) * g⁻¹ = α a := by group
        rw [h1] at h3
        simpa using h3.symm
      exact h2
    · intro h
      show g⁻¹ * α a * g⁻¹⁻¹ = 1
      rw [h]
      group
  · have h1 : (B.subgroupOf L).map α = conjSub g (Ut n) := by
      rw [← hP, ← hQ, hg]
      rfl
    have h2 : (B.subgroupOf L).map ((MulAut.conj g⁻¹).toMonoidHom.comp α) =
        conjSub g⁻¹ ((B.subgroupOf L).map α) := by
      rw [conjSub, Subgroup.map_map]
    rw [h2, h1, conjSub_inv_conjSub]
  · intro a u v huv
    have h1 := hrel a u v huv
    show Multiplicative.toAdd (actM g⁻¹ (β v)) =
      mat (g⁻¹ * α a * g⁻¹⁻¹) *ᵥ Multiplicative.toAdd (actM g⁻¹ (β u))
    rw [toAdd_actM, toAdd_actM, h1, mulVec_mulVec, mulVec_mulVec]
    congr 1
    have e : mat g⁻¹⁻¹ * mat g⁻¹ = 1 := by
      rw [inv_inv, mat_mul_inv]
    rw [mat_mul, mat_mul, mul_assoc (mat g⁻¹ * mat (α a)), e, mul_one]

theorem exists_inner_of_normalizes {L UL : Subgroup G} {n : ℕ} (α : ↥L →* SLt n)
    (β : ↥UL ≃* Multiplicative (Vt n)) (hαs : Function.Surjective α)
    (hLU : L ≤ Subgroup.normalizer (UL : Set G))
    (hrel : ∀ (a : ↥L) (u v : ↥UL), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = mat (α a) *ᵥ Multiplicative.toAdd (β u))
    {x : G} (hx : x ∈ Subgroup.normalizer (UL : Set G)) :
    ∃ l : ↥L, ∀ u : ↥UL, x * (u : G) * x⁻¹ = (l : G) * (u : G) * (l : G)⁻¹ := by
  let φ : Multiplicative (Vt n) ≃* Multiplicative (Vt n) :=
    β.symm.trans ((UL.normalizerMonoidHom ⟨x, hx⟩).trans β)
  obtain ⟨g, hg⟩ := exists_mat_of_mulEquiv φ
  obtain ⟨l, hl⟩ := hαs g
  refine ⟨l, fun u => ?_⟩
  have hlu : (l : G) * (u : G) * (l : G)⁻¹ ∈ UL :=
    (Subgroup.mem_normalizer_iff.1 (hLU l.2) (u : G)).1 u.2
  have h1 := hg (Multiplicative.toAdd (β u))
  rw [ofAdd_toAdd] at h1
  have h2 : φ (β u) = β ⟨x * (u : G) * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx (u : G)).1 u.2⟩ := by
    show β ((UL.normalizerMonoidHom ⟨x, hx⟩) (β.symm (β u))) = _
    rw [MulEquiv.symm_apply_apply]
    congr 1
  have h3 := hrel l u ⟨(l : G) * (u : G) * (l : G)⁻¹, hlu⟩ rfl
  rw [h2, ← hl] at h1
  have h4 : β ⟨x * (u : G) * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx (u : G)).1 u.2⟩ =
      β ⟨(l : G) * (u : G) * (l : G)⁻¹, hlu⟩ := by
    apply Multiplicative.toAdd.injective
    rw [h1, h3]
  have := congrArg Subtype.val (β.injective h4)
  exact this

theorem flag_eq {L S UL : Subgroup G} {n : ℕ} (α : ↥L →* SLt n) (β : ↥UL ≃* Multiplicative (Vt n))
    (hαB : ((S ⊓ L).subgroupOf L).map α = Ut n)
    (hLU : L ≤ Subgroup.normalizer (UL : Set G))
    (hrel : ∀ (a : ↥L) (u v : ↥UL), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = mat (α a) *ᵥ Multiplicative.toAdd (β u))
    {X : Subgroup G} {k : ℕ} (hXU : X ≤ UL) (hXc : Nat.card X = 2 ^ k)
    (hXN : S ≤ Subgroup.normalizer (X : Set G)) :
    ∀ x : G, x ∈ X ↔ ∃ hx : x ∈ UL, Multiplicative.toAdd (β ⟨x, hx⟩) ∈
      flagSpace n (ZMod 2) k := by
  let Z : Subgroup (Multiplicative (Vt n)) := (X.subgroupOf UL).map β.toMonoidHom
  have hZinv : SInvG (Ut n) Z := by
    intro q hq z hz
    rw [← hαB] at hq
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨y, hyX, rfl⟩ := hz
    have hbS : (b : G) ∈ S := (Subgroup.mem_subgroupOf.1 hb).1
    have hyX' : (y : G) ∈ X := hyX
    have hxX : (b : G) * y * (b : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hXN hbS) _).1 hyX'
    have hxU : (b : G) * y * (b : G)⁻¹ ∈ UL := (Subgroup.mem_normalizer_iff.1 (hLU b.2) _).1 y.2
    have h1 := hrel b y ⟨(b : G) * y * (b : G)⁻¹, hxU⟩ rfl
    refine ⟨⟨(b : G) * y * (b : G)⁻¹, hxU⟩, hxX, ?_⟩
    show β ⟨(b : G) * y * (b : G)⁻¹, hxU⟩ = Multiplicative.ofAdd (mat (α b) *ᵥ Multiplicative.toAdd (β y))
    rw [← h1]
    rfl
  have hZc : Nat.card Z = 2 ^ k := by
    rw [Subgroup.card_map_of_injective β.injective, ← hXc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXU).toEquiv
  have hZY : Z = Yk n k := eq_Yk_of_Ut_invariant hZinv hZc
  intro x
  constructor
  · intro hx
    refine ⟨hXU hx, ?_⟩
    have : β ⟨x, hXU hx⟩ ∈ Z := ⟨⟨x, hXU hx⟩, hx, rfl⟩
    rw [hZY, Yk, mem_subgroupOfSpace] at this
    exact this
  · rintro ⟨hxU, hxF⟩
    have h1 : β ⟨x, hxU⟩ ∈ Z := by
      rw [hZY, Yk, mem_subgroupOfSpace]
      exact hxF
    obtain ⟨y, hyX, hy⟩ := h1
    have : y = ⟨x, hxU⟩ := β.injective hy
    rw [this] at hyX
    exact hyX

theorem mem_normalizer_iff_stab {L UL : Subgroup G} {n : ℕ} (α : ↥L →* SLt n)
    (β : ↥UL ≃* Multiplicative (Vt n)) (hLU : L ≤ Subgroup.normalizer (UL : Set G))
    (hrel : ∀ (a : ↥L) (u v : ↥UL), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = mat (α a) *ᵥ Multiplicative.toAdd (β u))
    {X : Subgroup G} {k : ℕ}
    (hX : ∀ x : G, x ∈ X ↔ ∃ hx : x ∈ UL, Multiplicative.toAdd (β ⟨x, hx⟩) ∈
      flagSpace n (ZMod 2) k) (a : ↥L) :
    (a : G) ∈ Subgroup.normalizer (X : Set G) ↔ α a ∈ stabilizer (flagSpace n (ZMod 2) k) := by
  rw [mem_stabilizer_iff]
  have hmem : ∀ u : ↥UL, (a : G) * (u : G) * (a : G)⁻¹ ∈ UL := fun u =>
    (Subgroup.mem_normalizer_iff.1 (hLU a.2) (u : G)).1 u.2
  have hact : ∀ u : ↥UL, Multiplicative.toAdd (β ⟨(a : G) * (u : G) * (a : G)⁻¹, hmem u⟩) =
      mat (α a) *ᵥ Multiplicative.toAdd (β u) := fun u => hrel a u _ rfl
  have hXu : ∀ u : ↥UL, (u : G) ∈ X ↔ Multiplicative.toAdd (β u) ∈ flagSpace n (ZMod 2) k := by
    intro u
    rw [hX]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨u.2, h⟩⟩
  constructor
  · intro hN v
    set u : ↥UL := β.symm (Multiplicative.ofAdd v) with hu
    have hβu : Multiplicative.toAdd (β u) = v := by
      rw [hu, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rw [← hβu, ← hact u, ← hXu u, ← hXu ⟨_, hmem u⟩]
    exact Subgroup.mem_normalizer_iff.1 hN (u : G)
  · intro hv
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hhU, hhF⟩ := (hX h).1 hh
      have h1 := (hv _).1 hhF
      rw [← hact ⟨h, hhU⟩] at h1
      exact (hX _).2 ⟨hmem ⟨h, hhU⟩, h1⟩
    · intro hh
      obtain ⟨hhU, hhF⟩ := (hX _).1 hh
      have hhU' : h ∈ UL := by
        have := (Subgroup.mem_normalizer_iff.1 (hLU (L.inv_mem a.2)) _).1 hhU
        simpa [mul_assoc] using this
      have hact' := hact ⟨h, hhU'⟩
      have h1 : Multiplicative.toAdd (β ⟨h, hhU'⟩) ∈ flagSpace n (ZMod 2) k := by
        rw [hv]
        rw [← hact']
        exact hhF
      exact (hX h).2 ⟨hhU', h1⟩

end CFSG.Quasithin.FLc
