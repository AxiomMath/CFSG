module

public import CFSG.Quasithin.Background.Harris.G2.U33Setup
public import CFSG.Quasithin.Background.Harris.G2.Transport
public import CFSG.Quasithin.Background.SmithB45U33Mid
public import CFSG.Quasithin.Background.SmithB42U33SixProof
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.H13
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]


theorem finrank_eq_six_of_u33 [Finite V] {L : Subgroup (GLV V)} (hs : IsSimpleGroup ↥L)
    (hm : StatedClassicalModel ↥L .PSU 3 3 1) (hirr : IsIrr L ⊤)
    (hd : Module.finrank (ZMod 2) V ≤ 8) : Module.finrank (ZMod 2) V = 6 := by
  classical
  have hP : B42TypeU33 ↥L := b42TypeU33_of_simple hs hm
  obtain ⟨θ⟩ := B42U33.nonempty_equiv_g2Derived hP
  let σ : ↥(g2Derived (ZMod 2)) →* (V →ₗ[ZMod 2] V) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)).comp
      (L.subtype.comp θ.symm.toMonoidHom)
  have hσ : ∀ h u, σ h u = ((θ.symm h : ↥L) : GLV V) u := fun _ _ => rfl
  have hnt : ∃ h, σ h ≠ 1 := by
    have : Nontrivial ↥L := hs.toNontrivial
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥L)
    refine ⟨θ x, fun h => hx1 ?_⟩
    have h3 : ((x : ↥L) : GLV V) = 1 := by
      apply LinearEquiv.toLinearMap_injective
      have := h
      change (((θ.symm (θ x) : ↥L) : GLV V) : V →ₗ[ZMod 2] V) = 1 at this
      rwa [MulEquiv.symm_apply_apply] at this
    exact Subtype.ext h3
  have hirrM : ∀ U : Submodule (ZMod 2) V, (∀ h, ∀ u ∈ U, σ h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    obtain ⟨-, -, hI⟩ := hirr
    refine hI U (fun l hl u hu => ?_) bot_le le_top
    have := hU (θ ⟨l, hl⟩) u hu
    rwa [hσ, MulEquiv.symm_apply_apply] at this
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at this
  have hle : Nat.card V ≤ 2 ^ 12 := by
    rw [hcardV]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h6 := B45U33.card_le_of_g2Derived σ hnt hirrM hle
  have hup : Module.finrank (ZMod 2) V ≤ 6 := by
    rw [hcardV] at h6
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h6
  have hW : ∀ w : Multiplicative V, w ^ 2 = 1 := fun w => by
    rw [pow_two]; exact mul_self_eq_one_multiplicative w
  have hlow := B42U33.six_le_of_card_dvd hW (natCard_multiplicative (V := V)) (toMulSub L)
    ((natCard_toMulSub L).trans (B42U33.card_of_b42TypeU33 hP))
  omega

theorem u33_natural_coords [Finite V] {L : Subgroup (GLV V)} (hs : IsSimpleGroup ↥L)
    (hm : StatedClassicalModel ↥L .PSU 3 3 1) (hdim : Module.finrank (ZMod 2) V = 6) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ∧
      ∃ (φ : V ≃+ (Ix3 → K)) (e : ↥L ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆),
        ∀ (h : ↥L) (v : V), φ ((h : GLV V) v) =
          g2Act ⟨(e h : quasithinZorn K ≃ₗ[K] quasithinZorn K), derived_le_cayley K (e h).2⟩
            (φ v) := by
  classical
  have hW : ∀ w : Multiplicative V, w ^ 2 = 1 := fun w => by
    rw [pow_two]; exact mul_self_eq_one_multiplicative w
  have hcard : Nat.card (Multiplicative V) = 2 ^ 6 := by
    rw [natCard_multiplicative, hdim]
  obtain ⟨K, instK, instF, hK, π, hRV⟩ :=
    B42U33.u33SixNatural (Multiplicative V) hW hcard (toMulSub L) (b42TypeU33_toMulSub hs hm)
  have hK2 : Nat.card K = 2 := by rwa [pow_one] at hK
  have hchar : CharP K 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hK
  refine ⟨K, instK, instF, hchar, hK2, ?_⟩
  let Γ₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K) := ⁅quasithinG2 K, quasithinG2 K⁆
  have hΓ₀ : Γ₀ ≤ cayleyGroup K := derived_le_cayley K
  obtain ⟨f, hfadd, hfker, hfonto, hfact⟩ :=
    CFSG.Quasithin.Vol2.KGNat.exists_coord (CFSG.Quasithin.Vol2.KGNat.linModelZorn Γ₀ hΓ₀) hRV
  let φAdd : V →+ (Ix3 → K) :=
    AddMonoidHom.mk' (fun v => f (Multiplicative.ofAdd v)) fun a b => by
      have := hfadd (Multiplicative.ofAdd a) (Subgroup.mem_top _) (Multiplicative.ofAdd b)
        (Subgroup.mem_top _)
      exact this
  have hφinj : Function.Injective φAdd := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have := (hfker (Multiplicative.ofAdd v) (Subgroup.mem_top _)).1 hv
    simpa using this
  have hφsurj : Function.Surjective φAdd := fun w => by
    obtain ⟨u, -, hu⟩ := hfonto w
    exact ⟨Multiplicative.toAdd u, hu⟩
  let φ : V ≃+ (Ix3 → K) := AddEquiv.ofBijective φAdd ⟨hφinj, hφsurj⟩
  have hφ : ∀ v, φ v = f (Multiplicative.ofAdd v) := fun v => rfl
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    let γ0 : ↥Γ₀ := γ
    have hγ1 : (⟨(γ0 : quasithinZorn K ≃ₗ[K] quasithinZorn K), hΓ₀ γ0.2⟩ :
        ↥(cayleyGroup K)) = 1 := by
      apply CFSG.Quasithin.Vol2.Ch11.G2Q8.cayley_eq_one
      intro w
      obtain ⟨u, -, hu⟩ := hfonto w
      have h1 := hfact γ u (Subgroup.mem_top _)
      rw [hγ] at h1
      simp only [Subgroup.coe_one, MulAut.one_apply, hu] at h1
      exact h1.symm
    have h3 : (γ0 : quasithinZorn K ≃ₗ[K] quasithinZorn K) = 1 :=
      congrArg (fun x : ↥(cayleyGroup K) => (x : quasithinZorn K ≃ₗ[K] quasithinZorn K)) hγ1
    have hγ0 : γ0 = 1 := Subtype.ext h3
    exact hγ0
  let e : ↥L ≃* ↥Γ₀ :=
    (toMulSubEquiv L).trans (MulEquiv.ofBijective π ⟨hπinj, hRV.1⟩).symm
  refine ⟨φ, e, fun h v => ?_⟩
  have hπe : π (e h) = toMulSubEquiv L h := by
    change (MulEquiv.ofBijective π ⟨hπinj, hRV.1⟩) ((MulEquiv.ofBijective π ⟨hπinj, hRV.1⟩).symm
      (toMulSubEquiv L h)) = _
    rw [MulEquiv.apply_symm_apply]
  have h1 := hfact (e h) (Multiplicative.ofAdd v) (Subgroup.mem_top _)
  rw [hπe] at h1
  rw [hφ, hφ]
  exact h1

end CFSG.Quasithin.G11.Harris.G2
