module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828E34Good
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNSz
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Blueprint CFSG.ShultStronglyClosedTI.SuzukiModel CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms

theorem normalizer_suzukiU_e34 {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.normalizer ((suzukiU a K : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)) =
      suzukiB a K :=
  ((suzukiPointAction_suzukiGroup hK).normalizer_eq_stabilizer
    (Nat.one_lt_two_pow (by omega))).trans (suzuki_ovoid_stabilizer hK).2

theorem suzukiU_ti_e34 {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : suzukiGroup a K)
    (hg : g ∉ suzukiB a K) :
    suzukiU a K ⊓ (suzukiU a K).map (MulAut.conj g).toMonoidHom = ⊥ := by
  have hP := suzukiPointAction_suzukiGroup hK
  have hstab := (suzuki_ovoid_stabilizer hK).2
  have hgα : g • (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) ≠
      (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) := by
    intro h
    exact hg (by rw [← hstab]; exact MulAction.mem_stabilizer_iff.2 h)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨u, hu, hxu⟩ := Subgroup.mem_map.1 hxc
  have huα : u • (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) =
      (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) :=
    MulAction.mem_stabilizer_iff.1 (hP.le_stabilizer_left hu)
  have hfix : x • (g • (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK)) =
      g • (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) := by
    rw [← hxu]
    change (g * u * g⁻¹) • (g • (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ :
      suzukiOmegaSub hK)) = g • (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ :
      suzukiOmegaSub hK)
    rw [← mul_smul, show g * u * g⁻¹ * g = g * u by group, mul_smul, huα]
  obtain ⟨w0, -, huniq⟩ := hP.regular _ _ hgα hgα
  have h1 := huniq ⟨x, hxU⟩ hfix
  have h2 := huniq 1 (by simp)
  have hx1 : x = 1 := congrArg Subtype.val (h1.trans h2.symm)
  rw [Subgroup.mem_bot]
  exact hx1

theorem suzukiU_involution_e34 {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : suzukiGroup a K)
    (hs : s ∈ suzukiU a K) (hs2 : s ^ 2 = 1) : s ∈ suzukiZ0 a K := by
  by_cases h1 : s = 1
  · rw [h1]
    exact Subgroup.one_mem _
  · have hord : orderOf s = 2 := orderOf_eq_prime hs2 h1
    obtain ⟨v, -, hsv⟩ :=
      (mem_suzukiB_and_orderOf_eq_two_iff hK).1 ⟨suzukiU_le_suzukiB a K hs, hord⟩
    exact (mem_suzukiZ0_iff hK).2 ⟨v, hsv⟩

theorem suzukiZ0_trans_e34 {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (z z' : suzukiGroup a K)
    (hz : z ∈ suzukiZ0 a K) (hz' : z' ∈ suzukiZ0 a K) (hz1 : z ≠ 1) (hz1' : z' ≠ 1) :
    ∃ g ∈ Subgroup.normalizer ((suzukiU a K : Subgroup (suzukiGroup a K)) :
      Set (suzukiGroup a K)), g * z * g⁻¹ = z' := by
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
  obtain ⟨w, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz'
  have hv : v ≠ 0 := fun h => hz1 (by rw [h, suzukiSElt_zero_zero hK])
  have hw : w ≠ 0 := fun h => hz1' (by rw [h, suzukiSElt_zero_zero hK])
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -, -⟩ := suzuki_frobenius_exponents a K hK
  obtain ⟨m, hm⟩ := hbij.2 (Units.mk0 (w * v⁻¹) (mul_ne_zero hw (inv_ne_zero hv)))
  have hm' : m ^ (2 ^ (a + 1) + 1) = Units.mk0 (w * v⁻¹) (mul_ne_zero hw (inv_ne_zero hv)) := by
    rw [← zpow_natCast]
    push_cast
    exact hm
  have hval : (m : K) ^ (2 ^ (a + 1) + 1) * v = w := by
    have h1 := congrArg (fun x : Kˣ => (x : K)) hm'
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at h1
    rw [h1, mul_assoc, inv_mul_cancel₀ hv, mul_one]
  refine ⟨suzukiDElt a K m⁻¹, suzukiT_le_normalizer hK (suzukiDElt_mem_suzukiT a K m⁻¹), ?_⟩
  rw [suzukiDElt_conj' hK, inv_inv, mul_zero, hval]

theorem good_suzukiU_e34 {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    E3Good_e34 (suzukiGroup a K) (2 ^ (2 * a + 1)) (suzukiU a K) := by
  have hN := normalizer_suzukiU_e34 hK
  refine ⟨⟨suzukiZ0 a K, suzukiZ0_le_suzukiU, card_suzukiZ0 hK,
    fun z hz => (isElemAbelian_suzukiZ0 hK).2 z hz,
    fun s hs hs2 => suzukiU_involution_e34 hK s hs hs2, ?_⟩, ?_, ?_⟩
  · intro z hz z' hz' hz1 hz1'
    exact suzukiZ0_trans_e34 hK z z' hz hz' hz1 hz1'
  · intro g hg
    rw [hN] at hg
    exact suzukiU_ti_e34 hK g hg
  · refine ⟨suzukiT a K, suzukiT_le_normalizer hK, isCyclic_suzukiT, ?_⟩
    intro n hn
    rw [hN] at hn
    have hn' : n ∈ (suzukiB a K : Set (suzukiGroup a K)) := hn
    rw [(suzuki_borel_structure hK).2.2.2.2.2.1] at hn'
    obtain ⟨u, hu, t, ht, rfl⟩ := Set.mem_mul.1 hn'
    exact ⟨u, hu, t, ht, rfl⟩

theorem sylow_map_conj_e34 {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {X : Type} [Group X]
    [Finite X] (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) :
    ∃ g : suzukiGroup a K, (S : Subgroup X).map e.toMonoidHom =
      (suzukiU a K).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_eq_suzukiU hK
  let S0 : Sylow 2 (suzukiGroup a K) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P S0
  refine ⟨g, ?_⟩
  have h1 : (S0 : Subgroup (suzukiGroup a K)) = (S : Subgroup X).map e.toMonoidHom := rfl
  rw [← h1, ← hg, Sylow.coe_subgroup_smul, ← hP]
  rfl

theorem good_sylow_e34 {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {X : Type} [Group X] [Finite X]
    (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) : E3Good_e34 X (2 ^ (2 * a + 1)) (S : Subgroup X) := by
  obtain ⟨g, hg⟩ := sylow_map_conj_e34 hK e S
  have h1 : E3Good_e34 (suzukiGroup a K) (2 ^ (2 * a + 1)) ((S : Subgroup X).map e.toMonoidHom) := by
    rw [hg]
    exact good_map_e34 (MulAut.conj g) _ _ (good_suzukiU_e34 hK)
  have h2 := good_map_e34 e.symm _ _ h1
  have hid : ((S : Subgroup X).map e.toMonoidHom).map e.symm.toMonoidHom = (S : Subgroup X) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  rw [hid] at h2
  exact h2

theorem outer_odd_e34 {X : Type} [Group X] {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) (A : Type) [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    (eN : ↥N ≃* X) (hC : ∀ x : A, (∀ m ∈ N, x * m = m * x) → x = 1) :
    Odd (Nat.card (A ⧸ N)) := by
  have hM : CFSG.Blueprint.SuzukiModel ↥N 2 (2 * a + 1) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨eN.trans e⟩⟩
  have hodd : Odd (Nat.card (Outer ↥N)) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} ↥N 2 (2 * a + 1) hM).1.2.2
  let conjN : A → (↥N ≃* ↥N) := fun x =>
    { toFun := fun m => ⟨x * m * x⁻¹, Subgroup.Normal.conj_mem inferInstance (m : A) m.2 x⟩
      invFun := fun m => ⟨x⁻¹ * m * x, by
        simpa using Subgroup.Normal.conj_mem inferInstance (m : A) m.2 x⁻¹⟩
      left_inv := fun m => Subtype.ext (by simp [mul_assoc])
      right_inv := fun m => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun m m' => Subtype.ext (by simp [mul_assoc]) }
  let ψ : A →* MulAut ↥N :=
    { toFun := conjN
      map_one' := MulEquiv.ext fun m => Subtype.ext (by simp [conjN])
      map_mul' := fun x y => MulEquiv.ext fun m => Subtype.ext (by simp [conjN, mul_assoc]) }
  let φ : A →* Outer ↥N := (QuotientGroup.mk' (inner ↥N)).comp ψ
  have hker : ∀ x : A, φ x = 1 ↔ x ∈ N := by
    intro x
    change (QuotientGroup.mk (ψ x) : Outer ↥N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 h
      have hcomm : ∀ n ∈ N, ((m : A)⁻¹ * x) * n = n * ((m : A)⁻¹ * x) := by
        intro n hn
        have h1 : (m : A) * n * (m : A)⁻¹ = x * n * x⁻¹ := by
          have := congrArg (fun f : MulAut ↥N => ((f ⟨n, hn⟩ : ↥N) : A)) hm
          simpa [ψ, conjN, MulAut.conj_apply] using this
        calc ((m : A)⁻¹ * x) * n = (m : A)⁻¹ * (x * n * x⁻¹) * x := by group
          _ = (m : A)⁻¹ * ((m : A) * n * (m : A)⁻¹) * x := by rw [h1]
          _ = n * ((m : A)⁻¹ * x) := by group
      have hx := hC ((m : A)⁻¹ * x) hcomm
      have hxm : x = m := by
        rw [inv_mul_eq_one] at hx
        exact hx.symm
      rw [hxm]
      exact m.2
    · intro hx
      refine MonoidHom.mem_range.2 ⟨⟨x, hx⟩, MulEquiv.ext fun n => Subtype.ext ?_⟩
      simp [ψ, conjN, MulAut.conj_apply]
  have hkerN : φ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hker x]
  have e1 : A ⧸ N ≃* A ⧸ φ.ker := QuotientGroup.quotientMulEquivOfEq hkerN.symm
  have e2 : A ⧸ φ.ker ≃* φ.range := QuotientGroup.quotientKerEquivRange φ
  have hcard : Nat.card (A ⧸ N) = Nat.card φ.range := Nat.card_congr (e1.trans e2).toEquiv
  have hdvd : Nat.card φ.range ∣ Nat.card (Outer ↥N) := Subgroup.card_subgroup_dvd_card _
  rw [hcard]
  exact hodd.of_dvd_nat hdvd

theorem e3_828_holds :
    CFSG.Quasithin.H13.L828N.E3_828 := by
  intro n X _ _ hX
  obtain ⟨hp, a, ha, K, hF, hFin, hf, hK, ⟨e⟩⟩ := hX
  subst hf
  refine ⟨fun A _ _ N _ ⟨eN⟩ hC => outer_odd_e34 ha hK e A N eN hC, fun S => ?_⟩
  obtain ⟨⟨Z, hZS, hZc, hZsq, hZinv, hZtr⟩, hTI, C, hCN, hCc, hCdec⟩ :=
    good_sylow_e34 hK e S
  exact ⟨⟨Z, hZS, hZc, hZsq, hZinv, hZtr⟩, hTI, isCyclic_quot_e34 _ _ C hCN hCdec⟩

end CFSG.Quasithin.H13
