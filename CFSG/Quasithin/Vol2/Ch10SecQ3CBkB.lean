module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkA
public import CFSG.Quasithin.Vol2.Ch10SecKIK4e
public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure NatData (X V : Subgroup G) (n : ℕ) : Prop where
  le : V ≤ blockQ X
  comm : V ≤ Subgroup.centralizer (blockQ X : Set G)
  exp : ∀ v ∈ V, v ^ 2 = 1
  norm : X ≤ Subgroup.normalizer (V : Set G)
  nat : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥X ∧
    ∃ β : ↥V →* Multiplicative (Fin 2 → F), Function.Bijective β ∧
      ∀ (ℓ : ↥X) (u v : ↥V), (v : G) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (β v) =
          (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

namespace NatData

variable {X V : Subgroup G} {n : ℕ}

theorem irred (h : NatData X V n) {W : Subgroup G} (hWV : W ≤ V)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  obtain ⟨F, _, _, -, α, hαs, -, β, hβ, hβe⟩ := h.nat
  set W' : AddSubgroup (Fin 2 → F) :=
    { carrier := {w | ∃ u : ↥V, (u : G) ∈ W ∧ Multiplicative.toAdd (β u) = w}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', W.mul_mem hu hu', by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, W.one_mem, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, W.inv_mem hu, by rw [map_inv, toAdd_inv]⟩ }
  have hinv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, ∀ w ∈ W',
      (g : Matrix (Fin 2) (Fin 2) F).mulVec w ∈ W' := by
    rintro g _ ⟨u, hu, rfl⟩
    obtain ⟨ℓ, rfl⟩ := hαs g
    have hv : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (h.norm ℓ.2) u).mp u.2
    refine ⟨⟨_, hv⟩, (Subgroup.mem_normalizer_iff.mp (hXW ℓ.2) u).mp hu, ?_⟩
    exact hβe ℓ u ⟨_, hv⟩ rfl
  rcases eq_bot_or_eq_top_of_invariant W' hinv with h' | h'
  · left
    rw [eq_bot_iff]
    intro x hx
    have hxW' : Multiplicative.toAdd (β ⟨x, hWV hx⟩) ∈ W' := ⟨⟨x, hWV hx⟩, hx, rfl⟩
    rw [h', AddSubgroup.mem_bot] at hxW'
    have h1 : β ⟨x, hWV hx⟩ = β 1 := by rw [map_one]; exact hxW'
    have h2 := congrArg Subtype.val (hβ.1 h1)
    simpa using h2
  · right
    refine le_antisymm hWV fun v hv => ?_
    have hvW' : Multiplicative.toAdd (β ⟨v, hv⟩) ∈ W' := h' ▸ AddSubgroup.mem_top _
    obtain ⟨u, hu, hue⟩ := hvW'
    have : u = ⟨v, hv⟩ := hβ.1 (by simpa using hue)
    have hv' : v = (u : G) := by rw [this]
    rw [hv']
    exact hu

theorem ne_bot (h : NatData X V n) : V ≠ ⊥ := by
  obtain ⟨F, _, _, -, α, -, -, β, hβ, -⟩ := h.nat
  intro hV
  obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd (Pi.single 0 1))
  have hu1 : u = 1 := Subtype.ext (by
    have h0 : (u : G) ∈ (⊥ : Subgroup G) := hV ▸ u.2
    exact (Subgroup.mem_bot).mp h0)
  rw [hu1, map_one] at hu
  have := congrArg (fun y : Multiplicative (Fin 2 → F) => (Multiplicative.toAdd y) 0) hu
  simp at this

theorem not_central (h : NatData X V n) : ¬ X ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨F, _, _, -, α, hαs, -, β, hβ, hβe⟩ := h.nat
  intro hXC
  obtain ⟨ℓ, hℓ⟩ := hαs ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd (Pi.single 1 1))
  have hc : (u : G) = ℓ * u * (ℓ : G)⁻¹ := by
    rw [(Subgroup.mem_centralizer_iff.mp (hXC ℓ.2) u u.2).symm, mul_inv_cancel_right]
  have h1 := hβe ℓ u u hc
  rw [hℓ, hu] at h1
  have := congrFun h1 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this

theorem commutator_eq (h : NatData X V n) : ⁅V, X⁆ = V := by
  have hle : ⁅V, X⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def]
    have h1 : x * v⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (h.norm hx) _).mp (V.inv_mem hv)
    have e : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
    rw [e]
    exact V.mul_mem hv h1
  have hN : X ≤ Subgroup.normalizer ((⁅V, X⁆ : Subgroup G) : Set G) :=
    SecA.le_normalizer_commutator h.norm Subgroup.le_normalizer
  rcases h.irred hle hN with h' | h'
  · exfalso
    apply h.not_central
    have := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h'
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (this hv) x hx).symm
  · exact h'

theorem eq_one_of_fix (h : NatData X V n) {b : G} (hb : b ∈ X)
    (hbo : orderOf b ≠ 1) (hbodd : Odd (orderOf b)) {v : G} (hv : v ∈ V)
    (hfix : b * v * b⁻¹ = v) : v = 1 := by
  obtain ⟨F, _, _, hF, α, -, hαk, β, hβ, hβe⟩ := h.nat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hk : IsPGroup 2 α.ker := by
    rw [hαk]
    exact CFSG.pCore_isPGroup
  have hord : orderOf (α ⟨b, hb⟩) = orderOf b := by
    rw [orderOf_map_eq_of_odd α hk (by rwa [Subgroup.orderOf_mk])]
    rw [Subgroup.orderOf_mk]
  have hsq : α ⟨b, hb⟩ ^ 2 ≠ 1 := by
    intro h2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1
    · exact hbo h1
    · rw [h1] at hbodd
      exact absurd hbodd (by decide)
  have h1 := hβe ⟨b, hb⟩ ⟨v, hv⟩ ⟨v, hv⟩ hfix.symm
  have h2 := eq_zero_of_fix _ hsq h1.symm
  have h3 : β ⟨v, hv⟩ = β 1 := by
    rw [map_one]
    exact h2
  exact congrArg Subtype.val (hβ.1 h3)

end NatData

theorem block_of_natData [Finite G] {X V : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hperf : ⁅X, X⁆ = X)
    (hchar : CharTwo X) (h : NatData X V n) (hU : blockU X ≤ V) :
    IsShort2 X ∧ IsLin2Type X n ∧ blockZ X = ⊥ ∧ blockU X = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUV : blockU X = V := le_antisymm hU (by
    calc V = ⁅V, X⁆ := h.commutator_eq.symm
      _ ≤ ⁅blockQ X, X⁆ := Subgroup.commutator_mono h.le le_rfl)
  have hZ : blockZ X = ⊥ := by
    rcases h.irred (W := blockZ X) (hUV ▸ SecC.C10KH.blockZ_le X)
        (SecC.C10KH.le_normalizer_blockZ X) with h' | h'
    · exact h'
    · exfalso
      apply h.not_central
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvZ : v ∈ blockZ X := h' ▸ hv
      exact (Subgroup.mem_centralizer_iff.mp hvZ.2 x hx).symm
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβ, hβe⟩ := h.nat
  refine ⟨⟨?_, hchar, ⟨fun u hu => ⟨hU hu |> h.le, hU hu |> h.comm⟩,
      fun u hu => h.exp u (hU hu)⟩, ?_, ?_⟩, ?_, hZ, hUV⟩
  ·
    intro N _ hN2
    by_contra hNt
    have : Nontrivial (↥X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNt
    have : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hperf
    exact Group.IsPerfect.not_isNilpotent (↥X ⧸ N) hN2.isNilpotent
  ·
    left
    have e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hαs)
    exact Ch11.SecA.isQuasisimple_of_mulEquiv_SL2 hn (by rw [Nat.card_eq_fintype_card, hF]) e
  ·
    refine ⟨?_, fun W hZW hWU hXW => ?_⟩
    · rw [hZ, hUV, bot_lt_iff_ne_bot]
      exact h.ne_bot
    · rw [hUV] at hWU ⊢
      rw [hZ]
      exact h.irred hWU hXW
  ·
    refine ⟨F, inferInstance, inferInstance, hF, α, hαs, hαk,
      β.comp (MulEquiv.subgroupCongr hUV).toMonoidHom, ?_, ?_, ?_⟩
    · exact hβ.2.comp (MulEquiv.subgroupCongr hUV).surjective
    · ext u
      rw [MonoidHom.mem_ker, hZ, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
      constructor
      · intro hu
        have := hβ.1 (hu.trans (map_one β).symm)
        exact congrArg Subtype.val this
      · intro hu
        have : (MulEquiv.subgroupCongr hUV) u = 1 := Subtype.ext hu
        simp [this]
    · intro ℓ u v huv
      exact hβe ℓ _ _ huv

namespace NatData

variable {X V : Subgroup G} {n : ℕ}

theorem map_equiv (h : NatData X V n) (f : G ≃* G) :
    NatData (X.map f.toMonoidHom) (V.map f.toMonoidHom) n := by
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβ, hβe⟩ := h.nat
  let φ : X ≃* (X.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective X f.toMonoidHom f.injective
  let ψ : V ≃* (V.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective V f.toMonoidHom f.injective
  have hφs : ∀ y : (X.map f.toMonoidHom : Subgroup G), ((φ.symm y : X) : G) = f.symm y := by
    intro y
    apply f.injective
    rw [MulEquiv.apply_symm_apply]
    exact (congrArg Subtype.val (φ.apply_symm_apply y))
  have hψs : ∀ y : (V.map f.toMonoidHom : Subgroup G), ((ψ.symm y : V) : G) = f.symm y := by
    intro y
    apply f.injective
    rw [MulEquiv.apply_symm_apply]
    exact (congrArg Subtype.val (ψ.apply_symm_apply y))
  refine ⟨?_, ?_, ?_, ?_, F, inferInstance, inferInstance, hF, α.comp φ.symm.toMonoidHom,
    hαs.comp φ.symm.surjective, ?_, β.comp ψ.symm.toMonoidHom,
    hβ.comp ψ.symm.bijective, ?_⟩
  · rw [Lin2.blockQ_map_equiv]
    exact Subgroup.map_mono h.le
  · rw [Lin2.blockQ_map_equiv, centralizer_map_equiv]
    exact Subgroup.map_mono h.comm
  · rintro _ ⟨v, hv, rfl⟩
    have := congrArg f (h.exp v hv)
    simpa using this
  · rw [normalizer_map_equiv]
    exact Subgroup.map_mono h.norm
  · ext ℓ'
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαk,
      ← CFSG.pCore_map_iso 2 φ, Subgroup.mem_map_equiv]
    rfl
  · intro ℓ' u' v' huv
    have h' : ((ψ.symm v' : V) : G) = ((φ.symm ℓ' : X) : G) * ((ψ.symm u' : V) : G) *
        ((φ.symm ℓ' : X) : G)⁻¹ := by
      rw [hψs, hψs, hφs, huv, map_mul, map_mul, InvMemClass.coe_inv, map_inv]
    exact hβe (φ.symm ℓ') (ψ.symm u') (ψ.symm v') h'

theorem card (h : NatData X V n) : Nat.card V = 4 ^ n := by
  obtain ⟨F, _, _, hF, -, -, -, β, hβ, -⟩ := h.nat
  rw [Nat.card_eq_of_bijective β hβ]
  change Nat.card (Fin 2 → F) = 4 ^ n
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF, Nat.card_fin, ← pow_mul, mul_comm n 2,
    pow_mul]
  norm_num

end NatData

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
