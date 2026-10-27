module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupSemilinear

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism

section Scalar

variable {k Q : Type*} [Field k] [Group Q] (e : Multiplicative k ≃* Q)

theorem exists_scalar_hom : ∃ sc : kˣ →* MulAut Q, Function.Injective sc ∧
    ∀ (c : kˣ) (b : k), sc c (e (.ofAdd b)) = e (.ofAdd (c * b)) := by
  have happ : ∀ (c : kˣ) (b : k), coordSemilinearAut e c (RingEquiv.refl k) (e (.ofAdd b)) =
      e (.ofAdd (c * b)) := fun c b => by
    rw [coordSemilinearAut_apply, RingEquiv.refl_apply]
  let sc : kˣ →* MulAut Q :=
    { toFun := fun c => coordSemilinearAut e c (RingEquiv.refl k)
      map_one' := MulEquiv.ext fun x => by
        obtain ⟨b, rfl⟩ := e.surjective x
        rw [show b = .ofAdd b.toAdd from rfl, happ, Units.val_one, one_mul, MulAut.one_apply]
      map_mul' := fun c d => MulEquiv.ext fun x => by
        obtain ⟨b, rfl⟩ := e.surjective x
        rw [show b = .ofAdd b.toAdd from rfl, happ, MulAut.mul_apply, happ, happ, Units.val_mul,
          mul_assoc] }
  refine ⟨sc, fun c d hcd => ?_, happ⟩
  have h := coordSemilinearAut_injective e (a₁ := (c, RingEquiv.refl k))
    (a₂ := (d, RingEquiv.refl k)) hcd
  exact congrArg Prod.fst h

end Scalar

variable {G : Type} [Group G] [Finite G]

theorem torus_inf_centralizer_eq_bot
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ⊓
      Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, hXreg, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, hQ4, hzQ⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hz1 : z ≠ 1 := fun h1 => by
    have := h.local_datum.distinguished_order
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨⟨y, hy⟩, -, huniq⟩ := hXreg z ⟨hzQ, hz1⟩ z ⟨hzQ, hz1⟩
  have hxz : x⁻¹ * z * x = z := by
    rw [mul_assoc, Subgroup.mem_centralizer_iff.mp hx.2 z hzQ, inv_mul_cancel_left]
  have h1 := huniq ⟨x, hx.1⟩ hxz
  have h2 := huniq 1 (by simp)
  have := congrArg Subtype.val (h1.trans h2.symm)
  exact Subgroup.mem_bot.mpr this

variable {m : ℕ} {k : Type} [Field k] [Finite k]

omit [Finite G] in
theorem exists_scalar_of_mem_torus
    (hk : Nat.card k = 2 ^ (2 * m + 1)) {K B X Q : Subgroup G}
    (ψ : K ≃* suzukiGroup m k) (hψB : (B.subgroupOf K).map ψ.toMonoidHom = suzukiT m k)
    (hKB : K ⊓ B = X) (e : Multiplicative k ≃* Q)
    (he : ∀ b : k, ((e (.ofAdd b) : Q) : G) = (ψ.symm (suzukiSElt m k 0 b) : G))
    {x : G} (hx : x ∈ X) :
    ∃ μ : kˣ, ∀ b : k, x * (e (.ofAdd b) : G) * x⁻¹ = e (.ofAdd (μ * b)) := by
  rw [← hKB] at hx
  have hxT : ψ ⟨x, hx.1⟩ ∈ suzukiT m k := by
    rw [← hψB, mem_map_subgroupOf_iff]
    exact hx.2
  obtain ⟨l, hl⟩ := mem_suzukiT_iff.1 hxT
  refine ⟨l⁻¹ ^ (2 ^ (m + 1) + 1), fun b => ?_⟩
  have h1 : ψ.symm (suzukiDElt m k l * suzukiSElt m k 0 b * (suzukiDElt m k l)⁻¹) =
      ⟨x, hx.1⟩ * ψ.symm (suzukiSElt m k 0 b) * (⟨x, hx.1⟩ : K)⁻¹ := by
    rw [hl, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [suzukiDElt_conj' hk, mul_zero] at h1
  rw [he, he, Units.val_pow_eq_pow_val, h1]
  rfl

theorem map_conj_torus_eq_range
    (hk : Nat.card k = 2 ^ (2 * m + 1)) {K B X Q L : Subgroup G}
    (ψ : K ≃* suzukiGroup m k) (hψB : (B.subgroupOf K).map ψ.toMonoidHom = suzukiT m k)
    (hKB : K ⊓ B = X) (e : Multiplicative k ≃* Q)
    (he : ∀ b : k, ((e (.ofAdd b) : Q) : G) = (ψ.symm (suzukiSElt m k 0 b) : G))
    (hXL : X ≤ L) (hL : L ≤ Subgroup.normalizer (Q : Set G))
    (hXC : X ⊓ Subgroup.centralizer (Q : Set G) = ⊥) (hXcard : Nat.card X = Nat.card k - 1)
    (sc : kˣ →* MulAut Q) (hsci : Function.Injective sc)
    (hsc : ∀ (c : kˣ) (b : k), sc c (e (.ofAdd b)) = e (.ofAdd (c * b))) :
    (X.subgroupOf L).map (conjToAut Q L hL) = sc.range := by
  have hle : (X.subgroupOf L).map (conjToAut Q L hL) ≤ sc.range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨μ, hμ⟩ := exists_scalar_of_mem_torus hk ψ hψB hKB e he hx
    refine ⟨μ, MulEquiv.ext fun y => ?_⟩
    obtain ⟨b, rfl⟩ := e.surjective y
    refine Subtype.ext ?_
    rw [show b = .ofAdd b.toAdd from rfl, hsc, conjToAut_apply_coe]
    exact (hμ b.toAdd).symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective hsci).toEquiv, Nat.card_units, ← hXcard]
  refine Nat.card_le_card_of_injective (fun x => ⟨conjToAut Q L hL ⟨x, hXL x.2⟩,
    Subgroup.mem_map_of_mem _ (show (⟨x, hXL x.2⟩ : L) ∈ X.subgroupOf L from x.2)⟩) ?_
  intro x x' hxx'
  have h1 : conjToAut Q L hL ⟨x, hXL x.2⟩ = conjToAut Q L hL ⟨x', hXL x'.2⟩ :=
    congrArg Subtype.val hxx'
  have h2 : (x : G) * (x' : G)⁻¹ ∈ X ⊓ Subgroup.centralizer (Q : Set G) := by
    refine ⟨X.mul_mem x.2 (X.inv_mem x'.2), Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy₁ : (x' : G)⁻¹ * y * x' ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hL (hXL x'.2)) ((x' : G)⁻¹ * y * x')).mpr (by
        rwa [show (x' : G) * ((x' : G)⁻¹ * y * x') * (x' : G)⁻¹ = y by group])
    have h3 := congrArg (fun α : MulAut Q => ((α ⟨_, hy₁⟩ : Q) : G)) h1
    simp only [conjToAut_apply_coe] at h3
    rw [show (x' : G) * ((x' : G)⁻¹ * y * x') * (x' : G)⁻¹ = y by group] at h3
    calc y * ((x : G) * (x' : G)⁻¹)
        = (x : G) * ((x' : G)⁻¹ * y * x') * (x : G)⁻¹ * ((x : G) * (x' : G)⁻¹) := by rw [h3]
      _ = (x : G) * (x' : G)⁻¹ * y := by group
  rw [hXC, Subgroup.mem_bot, mul_inv_eq_one] at h2
  exact Subtype.ext h2

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
