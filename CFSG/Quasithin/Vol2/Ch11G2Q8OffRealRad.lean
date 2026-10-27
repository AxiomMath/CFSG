module

public import CFSG.Quasithin.Vol2.Ch11G2Q8OffReal
public import CFSG.Quasithin.Vol2.Ch11G2Q8RadLift
public import CFSG.Quasithin.Vol2.Ch11G2Q8Weyl
public import CFSG.Quasithin.Background.G64Linear

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open scoped IsMulCommutative

variable {K : Type} [Field K] [CharP K 2]

section Fix

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem exists_fixMod_ne_zero [Finite K] (hf : IsCoord (lmG K) H Z π f)
    (hW : ∀ w : W, w ^ 2 = 1) {Ā : Subgroup (MulAut W)} (hĀ2 : IsPGroup 2 ↥Ā)
    (hĀZ : ∀ φ ∈ Ā, ∀ z ∈ Z, φ z ∈ Z) :
    ∃ x : Ix3 → K, x ≠ 0 ∧ ∀ φ ∈ Ā, ∀ w, f w = x → f (φ w) = x := by
  obtain ⟨σ, hσ⟩ := hf.exists_section hW
  have hwd : ∀ φ ∈ Ā, ∀ a b : W, f a = f b → f (φ a) = f (φ b) := fun φ hφ a b h =>
    hf.map_eq_of_eq (φ := (φ : MulAut W).toMonoidHom) (hĀZ φ hφ) h
  let _ : MulAction ↥Ā (Multiplicative (Ix3 → K)) :=
    { smul := fun φ x => Multiplicative.ofAdd (f ((φ : MulAut W) (σ x)))
      one_smul := fun x => by
        change Multiplicative.ofAdd (f (σ x)) = x
        rw [hσ]
        rfl
      mul_smul := fun φ ψ x => by
        change Multiplicative.ofAdd (f ((φ : MulAut W) ((ψ : MulAut W) (σ x)))) =
          Multiplicative.ofAdd (f ((φ : MulAut W)
            (σ (Multiplicative.ofAdd (f ((ψ : MulAut W) (σ x)))))))
        rw [hwd _ φ.2 _ (σ (Multiplicative.ofAdd (f ((ψ : MulAut W) (σ x))))) (by
          rw [hσ, toAdd_ofAdd])] }
  have hne : (Multiplicative.ofAdd (q6 (1 : K) 0 0 0 0 0)) ≠ 1 := by
    intro h
    have h1 := congrFun (congrArg Multiplicative.toAdd h) (.inl 0)
    simp [q6] at h1
  obtain ⟨a, ha1, ha⟩ := G64.exists_fixed_ne_one (Q := ↥Ā) hĀ2
    (fun a => by
      rw [sq]
      change Multiplicative.ofAdd (Multiplicative.toAdd a + Multiplicative.toAdd a) = 1
      rw [show Multiplicative.toAdd a + Multiplicative.toAdd a = 0 from
        funext fun i => CharTwo.add_self_eq_zero _]
      rfl)
    (fun φ => by
      change Multiplicative.ofAdd (f ((φ : MulAut W) (σ 1))) = 1
      rw [map_one, map_one, hf.map_one]
      rfl)
    ⟨_, hne⟩
  refine ⟨Multiplicative.toAdd a, ha1, fun φ hφ w hw => ?_⟩
  have h1 : Multiplicative.ofAdd (f (φ (σ a))) = a := ha ⟨φ, hφ⟩
  rw [hwd φ hφ w (σ a) (by rw [hw, hσ])]
  exact congrArg Multiplicative.toAdd h1

end Fix

section FlagReal

variable {G : Type} [Group G] [Finite G] {L V X : Subgroup G} [IsMulCommutative ↥V]
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)} {f : ↥V → (Ix3 → K)}

omit [Finite G] [IsMulCommutative ↥V] in
theorem autOn_apply_of_mem_centralizer {h : MulAut ↥V} (hh : h ∈ autOn L V) {z : ↥V}
    (hz : z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V) : h z = z := by
  obtain ⟨y, hyL, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hh
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hz
  apply Subtype.ext
  rw [SecA.conjV_apply_coe, hz y hyL, mul_inv_cancel_right]

omit [Finite G] in
theorem eq_rhoG_of_autOn
    (hf : IsCoord (lmG K) (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (hcomm : commV (autOn L V) = ⊤)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    {φ : MulAut ↥V} (hφ : φ ∈ autOn X V) {γ : ↥(cayleyGroup K)}
    (hγ : ∀ w, f (φ w) = g2Act γ (f w)) :
    φ = ((rhoG hc0 hc1 π γ : ↥(autOn L V)) : MulAut ↥V) := by
  obtain ⟨x, hxX, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hφ
  exact eq_rhoG_of_modZ hf hc0 hc1 hcomm
    (fun z hz h hh => autOn_apply_of_mem_centralizer hh hz)
    (fun h hh => conjV_mul_conjV_inv_mem (hXN ⟨hxX, hxV⟩) hxV hh) hγ

omit [Finite G] in
theorem eq_rhoG_of_smul
    (hf : IsCoord (lmG K) (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (hcomm : commV (autOn L V) = ⊤)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    {φ : MulAut ↥V} (hφ : φ ∈ autOn X V) (hφ1 : φ * φ = 1) {c : K} (hc : c ≠ 0)
    {γ : ↥(cayleyGroup K)} (hγ : ∀ w, f (φ w) = c • g2Act γ (f w)) :
    φ = ((rhoG hc0 hc1 π γ : ↥(autOn L V)) : MulAut ↥V) := by
  have hsq' : ∀ x, g2Act (γ * γ) x = (c * c)⁻¹ • x := by
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    have h1 := congrArg f (show φ (φ w) = w by
      rw [← MulAut.mul_apply, hφ1, MulAut.one_apply])
    rw [hγ, hγ, g2Act_smul, smul_smul] at h1
    rw [g2Act_mul_apply]
    conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul]
  have hcc : (c * c)⁻¹ = 1 := scalar_eq_one hsq'
  have h3 : c * c = 1 := by rw [← inv_inv (c * c), hcc, inv_one]
  have hc1' : c = 1 := eq_of_mul_self_eq_charTwo (by rw [h3, one_mul])
  exact eq_rhoG_of_autOn hf hc0 hc1 hcomm hXN hφ fun w => by rw [hγ, hc1', one_smul]

theorem exists_g2Hom_rad [Finite K]
    (hf : IsCoord (lmG K) (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hsq : ∀ v : ↥V, v ^ 2 = 1) (hcomm : commV (autOn L V) = ⊤) {c₀ : K} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    {Ā : Subgroup (MulAut ↥V)} (hĀX : Ā ≤ autOn X V) (hĀ1 : ∀ φ ∈ Ā, φ * φ = 1) {k : ℕ}
    (hk : Nat.card K < k) (hP : ∀ B ≤ Ā, Nat.card ↥Ā < k * Nat.card ↥B →
      ∀ v : ↥V, (∀ b ∈ B, b v = v) → ∀ φ ∈ Ā, φ v = v) :
    ∃ Φ : ↥Ā →* ↥(cayleyGroup K), Function.Injective Φ ∧
      (∀ (φ : ↥Ā) (w : ↥V), f ((φ : MulAut ↥V) w) = g2Act (Φ φ) (f w)) ∧
      ∀ φ : ↥Ā, (φ : MulAut ↥V) = ((rhoG hc0 hc1 π (Φ φ) : ↥(autOn L V)) : MulAut ↥V) := by
  classical
  have hsurj : Function.Surjective f := hf.surj
  have : Finite (MulAut ↥V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hZfix : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V,
      h z = z := fun h hh z hz => autOn_apply_of_mem_centralizer hh hz
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
  obtain ⟨x₀, hx₀, hx₀fix⟩ := exists_fixMod_ne_zero hf hsq hĀ2 fun φ hφ z hz => by
    obtain ⟨y, hyX, hyV, rfl⟩ := SecA.mem_autOn_iff.mp (hĀX hφ)
    exact conjV_mem_centralizer (hXN ⟨hyX, hyV⟩) hyV hz
  obtain ⟨v₀, hv₀⟩ := hsurj x₀
  have hσ : ∀ φ : ↥Ā, ∀ t : K, σ φ t = t := by
    intro φ t
    by_contra ht
    obtain ⟨v', hv'⟩ := hsurj (t • x₀)
    have hv'B : ∀ b ∈ B, b v' = v' := by
      intro b hbB
      have hbĀ := hBĀ hbB
      obtain ⟨-, cb, γb, hcb, hb⟩ := hbB
      have hbρ := eq_rhoG_of_smul hf hc0 hc1 hcomm hXN (hĀX hbĀ) (hĀ1 b hbĀ) hcb hb
      have hbact : ∀ w, f (b w) = g2Act γb (f w) := fun w => by
        rw [hbρ, IsCoord.actG hf hc0 hc1]
      have h1 : g2Act γb x₀ = x₀ := by rw [← hv₀, ← hbact, hx₀fix b hbĀ v₀ hv₀, hv₀]
      rw [hbρ]
      exact rhoG_fix hK hn hf hc0 hc1 hsq hZfix (by rw [hv', g2Act_smul, h1])
    have h1 := hfixB v' hv'B φ φ.2
    have h3 := congrArg f h1
    have h4 : c φ • g2Act (γ φ) (frobQ (σ φ) x₀) = x₀ := by
      rw [← hv₀, ← hrep, hx₀fix φ φ.2 v₀ hv₀, hv₀]
    rw [hrep, hv', frobQ_smul, g2Act_smul, smul_comm, h4] at h3
    have h5 : (σ φ t - t) • x₀ = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact h3
    exact hx₀ ((smul_eq_zero.mp h5).resolve_left (sub_ne_zero.mpr ht))
  have hlin : ∀ (φ : ↥Ā) w, f ((φ : MulAut ↥V) w) = c φ • g2Act (γ φ) (f w) := fun φ w => by
    rw [hrep]
    congr 2
    funext j
    exact hσ φ _
  have hρ : ∀ φ : ↥Ā, (φ : MulAut ↥V) = ((rhoG hc0 hc1 π (γ φ) : ↥(autOn L V)) : MulAut ↥V) :=
    fun φ => eq_rhoG_of_smul hf hc0 hc1 hcomm hXN (hĀX φ.2) (hĀ1 φ φ.2) (hc φ) (hlin φ)
  have hact : ∀ (φ : ↥Ā) w, f ((φ : MulAut ↥V) w) = g2Act (γ φ) (f w) := fun φ w => by
    rw [hρ φ, IsCoord.actG hf hc0 hc1]
  refine ⟨{ toFun := γ
            map_one' := cayley_eq_one fun x => by
              obtain ⟨w, rfl⟩ := hsurj x
              rw [← hact]
              rfl
            map_mul' := fun φ ψ => cayley_ext fun x => by
              obtain ⟨w, rfl⟩ := hsurj x
              rw [← hact, g2Act_mul_apply, ← hact, ← hact]
              rfl }, fun φ ψ h => ?_, hact, hρ⟩
  apply Subtype.ext
  rw [hρ φ, hρ ψ]
  exact congrArg (fun g => ((rhoG hc0 hc1 π g : ↥(autOn L V)) : MulAut ↥V)) h

end FlagReal

end CFSG.Quasithin.Vol2.Ch11.G2Q8
