module

public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Vol2.Ch11G2Q8OffQr

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open scoped IsMulCommutative

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem ringEquiv_ext_of_gen [Finite K] {θ : Kˣ} (hθ : ∀ u : Kˣ, ∃ k : ℤ, θ ^ k = u)
    {σ σ' : K ≃+* K} (h : σ (θ : K) = σ' (θ : K)) : σ = σ' := by
  ext x
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · obtain ⟨k, hk⟩ := hθ (Units.mk0 x hx)
    have hx' : x = (θ : K) ^ k := by
      rw [← Units.val_zpow_eq_zpow_val, hk, Units.val_mk0]
    rw [hx', map_zpow₀, map_zpow₀, h]

section FlagReal

variable {G : Type} [Group G] [Finite G] {L V X : Subgroup G} [IsMulCommutative ↥V]
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)} {f : ↥V → (Ix3 → K)}

omit [Finite G] in
theorem exists_frob_of_mem [Finite K]
    (hf : IsCoord (lmG K) (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    {φ : MulAut ↥V} (hφ : φ ∈ autOn X V) :
    ∃ (c : K) (γ : ↥(cayleyGroup K)) (σ : K ≃+* K), c ≠ 0 ∧
      ∀ w, f (φ w) = c • g2Act γ (frobQ σ (f w)) := by
  obtain ⟨x, hxX, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hφ
  exact exists_smul_frob_conjV hf hc0 hc1 hK hn hXN ⟨hxX, hxV⟩

theorem exists_g2Hom_of_fixStable [Finite K]
    (hf : IsCoord (lmG K) (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hfinj : Function.Injective f) (hsq : ∀ v : ↥V, v ^ 2 = 1) {c₀ : K} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    {Ā : Subgroup (MulAut ↥V)} (hĀX : Ā ≤ autOn X V) (hĀ1 : ∀ φ ∈ Ā, φ * φ = 1) {k : ℕ}
    (hk : Nat.card K < k) (hP : ∀ B ≤ Ā, Nat.card ↥Ā < k * Nat.card ↥B →
      ∀ v : ↥V, (∀ b ∈ B, b v = v) → ∀ φ ∈ Ā, φ v = v) :
    ∃ Φ : ↥Ā →* ↥(cayleyGroup K), Function.Injective Φ ∧
      ∀ (φ : ↥Ā) (w : ↥V), f ((φ : MulAut ↥V) w) = g2Act (Φ φ) (f w) := by
  classical
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsurj : Function.Surjective f := hf.surj
  have : Finite (MulAut ↥V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  let B : Subgroup (MulAut ↥V) :=
    { carrier := {φ | φ ∈ Ā ∧ ∃ (c : K) (γ : ↥(cayleyGroup K)), c ≠ 0 ∧
        ∀ w, f (φ w) = c • g2Act γ (f w)}
      one_mem' := ⟨Ā.one_mem, 1, 1, one_ne_zero, fun w => by
        rw [MulAut.one_apply, one_smul, map_one]
        rfl⟩
      mul_mem' := by
        rintro φ ψ ⟨hφ, c, γ, hc, hcγ⟩ ⟨hψ, d, δ, hd, hdδ⟩
        refine ⟨Ā.mul_mem hφ hψ, c * d, γ * δ, mul_ne_zero hc hd, fun w => ?_⟩
        rw [MulAut.mul_apply, hcγ, hdδ, g2Act_smul, smul_smul, g2Act_mul_apply]
      inv_mem' := by
        rintro φ ⟨hφ, c, γ, hc, hcγ⟩
        refine ⟨Ā.inv_mem hφ, c⁻¹, γ⁻¹, inv_ne_zero hc, fun w => ?_⟩
        have h1 := hcγ (φ⁻¹ w)
        rw [MulAut.apply_inv_self] at h1
        rw [h1, g2Act_smul, g2Act_inv_apply, smul_smul, inv_mul_cancel₀ hc, one_smul] }
  have hBĀ : B ≤ Ā := fun φ hφ => hφ.1
  choose c γ σ hc hrep using fun φ : ↥Ā => exists_frob_of_mem hf hc0 hc1 hK hn hXN (hĀX φ.2)
  obtain ⟨θ, hθ⟩ := IsCyclic.exists_zpow_surjective (G := Kˣ)
  have hfib : ∀ φ ψ : ↥Ā, σ φ (θ : K) = σ ψ (θ : K) → (φ : MulAut ↥V)⁻¹ * ψ ∈ B := by
    intro φ ψ h
    have hσ := ringEquiv_ext_of_gen hθ h
    refine ⟨Ā.mul_mem (Ā.inv_mem φ.2) ψ.2, (σ φ).symm (c ψ / c φ),
      frobConj (σ φ).symm ((γ φ)⁻¹ * γ ψ), ?_, fun w => ?_⟩
    · rw [ne_eq, map_eq_zero_iff _ (σ φ).symm.injective]
      exact div_ne_zero (hc ψ) (hc φ)
    · obtain ⟨u, hu⟩ : ∃ u, u = ((φ : MulAut ↥V)⁻¹ * ψ) w := ⟨_, rfl⟩
      have h1 : f ((φ : MulAut ↥V) u) = f ((ψ : MulAut ↥V) w) := by
        rw [hu, MulAut.mul_apply, MulAut.apply_inv_self]
      rw [hrep, hrep, hσ] at h1
      have h3 : frobQ (σ ψ) (f u) = (c ψ / c φ) • g2Act ((γ φ)⁻¹ * γ ψ) (frobQ (σ ψ) (f w)) := by
        calc frobQ (σ ψ) (f u)
            = (c φ)⁻¹ • g2Act (γ φ)⁻¹ (c φ • g2Act (γ φ) (frobQ (σ ψ) (f u))) := by
              rw [g2Act_smul, g2Act_inv_apply, smul_smul, inv_mul_cancel₀ (hc φ), one_smul]
          _ = (c φ)⁻¹ • g2Act (γ φ)⁻¹ (c ψ • g2Act (γ ψ) (frobQ (σ ψ) (f w))) := by rw [h1]
          _ = _ := by rw [g2Act_smul, smul_smul, g2Act_mul_apply, div_eq_inv_mul]
      rw [← hu]
      have h5 := congrArg (frobQ ((σ φ).symm : K →+* K)) h3
      rw [hσ, frobQ_symm', frobQ_smul, ← hσ, ← g2Act_frobConj (σ φ).symm, frobQ_symm'] at h5
      · exact h5
  have hcard : Nat.card ↥Ā ≤ Nat.card K * Nat.card ↥B := by
    have := Fintype.ofFinite ↥Ā
    have := Fintype.ofFinite K
    have := Fintype.ofFinite (MulAut ↥V)
    have h1 := Finset.card_le_mul_card_image (Finset.univ : Finset ↥Ā)
      (f := fun φ => σ φ (θ : K)) (Nat.card ↥B) (fun k _ => by
        obtain ⟨φ₀, -, hφ₀⟩ := Finset.mem_image.mp ‹k ∈ _›
        have hinj : Set.InjOn (fun ψ : ↥Ā => ((φ₀ : MulAut ↥V)⁻¹ * ψ))
            (Finset.univ.filter fun ψ => σ ψ (θ : K) = k : Finset ↥Ā) := by
          intro ψ _ ψ' _ h
          exact Subtype.ext (mul_left_cancel h)
        have h3 := Finset.card_le_card_of_injOn
          (t := Finset.univ.filter fun x : MulAut ↥V => x ∈ B)
          (fun ψ : ↥Ā => ((φ₀ : MulAut ↥V)⁻¹ * ψ)) (fun ψ hψ => by
            rw [Finset.mem_coe, Finset.mem_filter] at hψ
            rw [Finset.mem_coe, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hfib φ₀ ψ (by rw [hφ₀, hψ.2])⟩) hinj
        have hBc : (Finset.univ.filter fun x : MulAut ↥V => x ∈ B).card = Nat.card ↥B := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact h3.trans hBc.le)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
    refine h1.trans ?_
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ ((Finset.card_le_univ _).trans
      (Nat.card_eq_fintype_card (α := K)).ge)
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hfixB : ∀ v : ↥V, (∀ b ∈ B, b v = v) → ∀ φ ∈ Ā, φ v = v :=
    hP B hBĀ (hcard.trans_lt (Nat.mul_lt_mul_of_pos_right hk hBpos))
  have hĀ2 : IsPGroup 2 ↥Ā := fun φ =>
    ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, pow_one, sq, Subgroup.coe_one]; exact hĀ1 φ φ.2)⟩
  have hf1 : f 1 = 0 := hf.map_one
  obtain ⟨v₁, hv₁⟩ := hsurj (eu 0 1)
  have hV1 : (⊤ : Subgroup ↥V) ≠ ⊥ := by
    intro h
    have hv : v₁ ∈ (⊥ : Subgroup ↥V) := h ▸ Subgroup.mem_top v₁
    rw [Subgroup.mem_bot] at hv
    rw [hv, hf1] at hv₁
    exact one_ne_zero (congrFun hv₁ (.inl 0)).symm
  obtain ⟨v₀, -, hv₀1, hv₀⟩ := B1.exists_fixed_ne_one hsq hĀ2 (M := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _) hV1
  have hfv₀ : f v₀ ≠ 0 := fun h => hv₀1 (hfinj (by rw [h, hf1]))
  have hσ : ∀ φ : ↥Ā, ∀ t : K, σ φ t = t := by
    intro φ t
    by_contra ht
    obtain ⟨v', hv'⟩ := hsurj (t • f v₀)
    have hv'B : ∀ b ∈ B, b v' = v' := by
      intro b hbB
      have hbĀ := hBĀ hbB
      obtain ⟨-, cb, γb, -, hb⟩ := hbB
      apply hfinj
      rw [hb, hv', g2Act_smul, smul_comm, ← hb, hv₀ b hbĀ]
    have h1 := hfixB v' hv'B φ φ.2
    have h3 := congrArg f h1
    rw [hrep, hv', frobQ_smul, g2Act_smul, smul_comm, ← hrep, hv₀ _ φ.2] at h3
    have h4 : (σ φ t - t) • f v₀ = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact h3
    exact hfv₀ ((smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr ht))
  have hlin : ∀ (φ : ↥Ā) w, f ((φ : MulAut ↥V) w) = c φ • g2Act (γ φ) (f w) := fun φ w => by
    rw [hrep]
    congr 2
    funext j
    exact hσ φ _
  have hc1' : ∀ φ : ↥Ā, c φ = 1 := by
    intro φ
    have hsq' : ∀ x, g2Act (γ φ * γ φ) x = (c φ * c φ)⁻¹ • x := by
      intro x
      obtain ⟨w, rfl⟩ := hsurj x
      have h1 := congrArg f (show (φ : MulAut ↥V) ((φ : MulAut ↥V) w) = w by
        rw [← MulAut.mul_apply, hĀ1 φ φ.2, MulAut.one_apply])
      rw [hlin, hlin, g2Act_smul, smul_smul] at h1
      rw [g2Act_mul_apply]
      conv_rhs => rw [← h1]
      rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero (hc φ) (hc φ)), one_smul]
    have hcc : (c φ * c φ)⁻¹ = 1 := scalar_eq_one hsq'
    have h3 : c φ * c φ = 1 := by rw [← inv_inv (c φ * c φ), hcc, inv_one]
    exact eq_of_mul_self_eq_charTwo (by rw [h3, one_mul])
  have hact : ∀ (φ : ↥Ā) w, f ((φ : MulAut ↥V) w) = g2Act (γ φ) (f w) := fun φ w => by
    rw [hlin, hc1', one_smul]
  have hγeq : ∀ φ ψ : ↥Ā, (∀ x, g2Act (γ φ) x = g2Act (γ ψ) x) → γ φ = γ ψ := fun φ ψ h =>
    cayley_ext h
  refine ⟨{ toFun := γ
            map_one' := cayley_eq_one fun x => by
              obtain ⟨w, rfl⟩ := hsurj x
              rw [← hact]
              rfl
            map_mul' := fun φ ψ => cayley_ext fun x => by
              obtain ⟨w, rfl⟩ := hsurj x
              rw [← hact, g2Act_mul_apply, ← hact, ← hact]
              rfl }, fun φ ψ h => ?_, hact⟩
  apply Subtype.ext
  refine MulEquiv.ext fun w => hfinj ?_
  rw [hact, hact]
  exact congrArg (fun g => g2Act g (f w)) h

end FlagReal

end CFSG.Quasithin.Vol2.Ch11.G2Q8
