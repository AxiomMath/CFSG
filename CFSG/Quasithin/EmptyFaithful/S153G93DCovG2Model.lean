module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCovG2Two
public import CFSG.Quasithin.Background.JonesParshallG2Field
public import CFSG.Quasithin.EmptyFaithful.S153EB6C

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace CovG2

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open

section Field

variable {K : Type} [Field K] [Finite K]

theorem charP_two_of_card_two (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])

theorem exists_order_three_fix_field
    [CharP K 2] (hK : Nat.card K = 2) (w : Ix3 → K) :
    ∃ x : ↥(cayleyGroup K),
      (x : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ ⁅cayleyGroup K, cayleyGroup K⁆ ∧
      x ^ 3 = 1 ∧ g2Act x w = w ∧ ∃ w', g2Act x w' ≠ w' := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  have key : ∀ (g : ↥(cayleyGroup K)) (v : Ix3 → K),
      (RingEquiv.piCongrRight fun _ : Ix3 => ε) (g2Act g v) =
        g2Act ⟨zornConj ε g, zornConj_mem ε g.2⟩ ((RingEquiv.piCongrRight fun _ : Ix3 => ε) v) :=
    fun g v => g2Act_zornConj ε g v
  obtain ⟨x₂, hx₂d, hx₂3, hx₂w, w₂, hw₂⟩ :=
    exists_order_three_fix_two ((RingEquiv.piCongrRight fun _ : Ix3 => ε) w)
  rw [← map_cayley_commutator ε] at hx₂d
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx₂d
  have hyC : y ∈ cayleyGroup K := Subgroup.commutator_le_self _ hy
  have hxy : (⟨zornConj ε y, zornConj_mem ε hyC⟩ : ↥(cayleyGroup (ZMod 2))) = x₂ :=
    Subtype.ext hyx
  have key' : ∀ v : Ix3 → K, (RingEquiv.piCongrRight fun _ : Ix3 => ε) (g2Act ⟨y, hyC⟩ v) =
      g2Act x₂ ((RingEquiv.piCongrRight fun _ : Ix3 => ε) v) := by
    intro v
    rw [key ⟨y, hyC⟩ v, hxy]
  refine ⟨⟨y, hyC⟩, hy, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change y ^ 3 = 1
    apply (zornConj ε).injective
    rw [map_pow, map_one]
    have h1 : (zornConj ε y : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) = ↑x₂ :=
      hyx
    rw [h1, ← Subgroup.coe_pow, hx₂3]
    rfl
  · apply (RingEquiv.piCongrRight fun _ : Ix3 => ε).injective
    rw [key']
    exact hx₂w
  · refine ⟨(RingEquiv.piCongrRight fun _ : Ix3 => ε).symm w₂, fun h => hw₂ ?_⟩
    have h1 := congrArg (RingEquiv.piCongrRight fun _ : Ix3 => ε) h
    rw [key', RingEquiv.apply_symm_apply] at h1
    exact h1

end Field

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem act_mul_inv_mem_zornR_iff (x : ↥(cayleyGroup K)) {m : Multiplicative (quasithinZorn K)}
    (hm : m ∈ zornO0 K) :
    Multiplicative.ofAdd ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd m)) *
        m⁻¹ ∈ zornR K ↔
      g2Act x (zP (Multiplicative.toAdd m)) = zP (Multiplicative.toAdd m) := by
  have htr : cayleyTr (Multiplicative.toAdd m) = 0 := hm
  have hu : Multiplicative.ofAdd
      ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd m)) ∈ zornO0 K := by
    show cayleyTr ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd m)) = 0
    rw [cg_tr x, htr]
  have hmem : Multiplicative.ofAdd
      ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd m)) * m⁻¹ ∈ zornO0 K :=
    (zornO0 K).mul_mem hu ((zornO0 K).inv_mem hm)
  have hz : zP ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd m)) =
      g2Act x (zP (Multiplicative.toAdd m)) :=
    (g2_zP_apply x _ htr).trans (g2Act_apply x _).symm
  have hP : zornPHom (⟨Multiplicative.ofAdd ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (Multiplicative.toAdd m)) * m⁻¹, hmem⟩ : ↥(zornO0 K)) =
      Multiplicative.ofAdd (g2Act x (zP (Multiplicative.toAdd m))) *
        (Multiplicative.ofAdd (zP (Multiplicative.toAdd m)))⁻¹ := by
    have e : (⟨Multiplicative.ofAdd ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (Multiplicative.toAdd m)) * m⁻¹, hmem⟩ : ↥(zornO0 K)) =
        (⟨_, hu⟩ : ↥(zornO0 K)) * (⟨m, hm⟩ : ↥(zornO0 K))⁻¹ := rfl
    rw [e, map_mul, map_inv]
    change Multiplicative.ofAdd (zP ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (Multiplicative.toAdd m))) * (Multiplicative.ofAdd (zP (Multiplicative.toAdd m)))⁻¹ = _
    rw [hz]
  constructor
  · intro h
    have h1 := zornPHom_of_mem (x := ⟨_, hmem⟩) h
    rw [hP, mul_inv_eq_one] at h1
    exact Multiplicative.ofAdd.injective h1
  · intro h
    apply zornPHom_eq_one (x := ⟨_, hmem⟩)
    rw [hP, h, mul_inv_cancel]

end Model

section Cover

variable {K : Type} [Field K] [Finite K]

theorem model_order_three
    (hK : Nat.card K = 2)
    {Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)}
    (hΓ : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ Γ) :
    ∀ m ∈ zornO0 K, ∃ γ : ↥Γ, γ ^ 3 = 1 ∧ zornAct Γ γ m * m⁻¹ ∈ zornR K ∧
      ∃ m' ∈ zornO0 K, zornAct Γ γ m' * m'⁻¹ ∉ zornR K := by
  have hchar : CharP K 2 := charP_two_of_card_two hK
  have hG : quasithinG2 K = cayleyGroup K :=
    CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup
  intro m hm
  obtain ⟨x, hxd, hx3, hxw, w', hxne⟩ :=
    exists_order_three_fix_field hK (zP (Multiplicative.toAdd m))
  have hxΓ : (x : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ Γ := by
    apply hΓ
    rw [hG]
    exact hxd
  refine ⟨⟨x, hxΓ⟩, ?_, ?_, Multiplicative.ofAdd (zI w'), cayleyTr_zI w', ?_⟩
  · apply Subtype.ext
    have h3 := congrArg Subtype.val hx3
    simpa using h3
  · show Multiplicative.ofAdd ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (Multiplicative.toAdd m)) * m⁻¹ ∈ zornR K
    rw [act_mul_inv_mem_zornR_iff x hm]
    exact hxw
  · show Multiplicative.ofAdd ((x : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (Multiplicative.toAdd (Multiplicative.ofAdd (zI w')))) *
        (Multiplicative.ofAdd (zI w'))⁻¹ ∉ zornR K
    rw [act_mul_inv_mem_zornR_iff x (m := Multiplicative.ofAdd (zI w')) (cayleyTr_zI w'),
      toAdd_ofAdd, zP_zI]
    exact hxne

end Cover

end CovG2

end S153G93D

end CFSG.Quasithin
