module

public import CFSG.Quasithin.EmptyFaithful.S153E58O
public import CFSG.Quasithin.EmptyFaithful.S153E61AA
public import CFSG.Quasithin.EmptyFaithful.S153E58M

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement
open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E61A

section Abstract

variable {W : Type} [CommGroup W] [Finite W] {H K : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}
  {bil : W → W → ZMod 2}

theorem z2_eq_of_add_eq_zero : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide

theorem bil_zero_W₂ (hS : S153E58.Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) :
    ∀ a ∈ W₂, ∀ b ∈ W₂, bil a b = 0 := by
  obtain ⟨e, hT, -⟩ := S153E58.exists_coords_of_realizes hπ
  obtain ⟨h₀, hh₀, hns⟩ := hS.exists_swap
  have hh₀K : h₀ ∉ K := fun hK => hns (fun w hw => hS.inv₁ h₀ hK w hw)
  have hinvK : h₀⁻¹ ∉ K := fun hK => hh₀K (by simpa using K.inv_mem hK)
  have hsw := hS.swap_of_not_mem_K hπ (H.inv_mem hh₀) hinvK
  intro a ha b hb
  have h1 := hS.bil_inv h₀ hh₀ (h₀⁻¹ a) (h₀⁻¹ b)
  rw [MulAut.apply_inv_self, MulAut.apply_inv_self] at h1
  rw [h1]
  exact hS.bil_zero_W₁ hT _ (hsw.2 a ha) _ (hsw.2 b hb)

theorem eq_one_of_triv₂ (hS : S153E58.Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) {c : MulAut W} (hc : c ∈ K)
    (h2 : ∀ w ∈ W₂, c w = w) : c = 1 := by
  obtain ⟨e, hT, -⟩ := S153E58.exists_coords_of_realizes hπ
  obtain ⟨h₀, hh₀, hns⟩ := hS.exists_swap
  have hh₀K : h₀ ∉ K := fun hK => hns (fun w hw => hS.inv₁ h₀ hK w hw)
  have hsw := hS.swap_of_not_mem_K hπ hh₀ hh₀K
  have hc' : h₀⁻¹ * c * h₀ ∈ H := by
    have := hS.Kn h₀⁻¹ (H.inv_mem hh₀) c hc
    simpa [mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem hh₀) (hS.KH hc)) hh₀
  have h1 : ∀ w ∈ W₁, (h₀⁻¹ * c * h₀) w = w := by
    intro w hw
    have hw' : h₀ w ∈ W₂ := hsw.1 w hw
    rw [MulAut.mul_apply, MulAut.mul_apply, h2 _ hw']
    exact MulAut.inv_apply_self _ _ _
  have := hS.eq_one_of_triv₁ hT hc' h1
  have h3 : c = 1 := by
    have h4 : c = h₀ * (h₀⁻¹ * c * h₀) * h₀⁻¹ := by group
    rw [h4, this]
    group
  exact h3

omit [Finite W] in
theorem q_zero_of_irr (hS : S153E58.Setup58 H K W₁ W₂ bil) (q : W → ZMod 2)
    (hq : ∀ a b, q (a * b) = q a + q b + bil a b) (hqK : ∀ k ∈ K, ∀ a, q (k a) = q a)
    {W₀ : Subgroup W} (hirr : IsIrrOn153 K W₀) (hiso : ∀ a ∈ W₀, ∀ b ∈ W₀, bil a b = 0)
    (hcard : 2 < Nat.card ↥W₀) : ∀ a ∈ W₀, q a = 0 := by
  have hq1 : q 1 = 0 := by
    have h := hq 1 1
    rw [mul_one, hS.bil_one_right] at h
    have key : ∀ x : ZMod 2, x = x + x + 0 → x = 0 := by decide
    exact key _ h
  have hqinv : ∀ b ∈ W₀, q b⁻¹ = q b := by
    intro b hb
    have h := hq b b⁻¹
    rw [mul_inv_cancel, hq1, hiso b hb b⁻¹ (W₀.inv_mem hb), add_zero] at h
    exact z2_eq_of_add_eq_zero _ _ h.symm
  let R : Subgroup W :=
    { carrier := {a | a ∈ W₀ ∧ q a = 0}
      one_mem' := ⟨W₀.one_mem, hq1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha0⟩ ⟨hb, hb0⟩
        refine ⟨W₀.mul_mem ha hb, ?_⟩
        rw [hq, ha0, hb0, hiso a ha b hb]
        rfl
      inv_mem' := by
        rintro a ⟨ha, ha0⟩
        exact ⟨W₀.inv_mem ha, by rw [hqinv a ha, ha0]⟩ }
  have hRle : R ≤ W₀ := fun a ha => ha.1
  have hRinv : ∀ k ∈ K, ∀ b ∈ R, k b ∈ R := by
    rintro k hk b ⟨hb, hb0⟩
    exact ⟨hirr.2.1 k hk b hb, by rw [hqK k hk, hb0]⟩
  rcases hirr.2.2 R hRle hRinv with hR | hR
  · exfalso
    have hinj : Function.Injective (fun a : ↥W₀ => q (a : W)) := by
      intro a b hab
      have h1 : (a : W) * (b : W)⁻¹ ∈ R := by
        refine ⟨W₀.mul_mem a.2 (W₀.inv_mem b.2), ?_⟩
        rw [hq, hqinv _ b.2, hiso _ a.2 _ (W₀.inv_mem b.2)]
        have hab' : q (a : W) = q (b : W) := hab
        rw [hab']
        generalize q (b : W) = z
        revert z
        decide
      rw [hR, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact Subtype.ext h1
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_zmod] at this
    omega
  · intro a ha
    have : a ∈ R := hR ▸ ha
    exact this.2

omit [Finite W] in
theorem exists_act (hS : S153E58.Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    {e : ↥W₁ ≃* S153E58.V3} (hT : S153E58.TransvIn K W₁ e)
    (he : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥W₁) (hu : (π γ : MulAut W) (u : W) ∈ W₁),
      e ⟨(π γ : MulAut W) (u : W), hu⟩ = natAct (StatedSL 3 (ZMod 2)) γ (e u))
    (γ δ : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h1 : γ * δ = 1) (h2 : δ * γ = 1) :
    ∃ k ∈ K, (∀ (a : W) (ha : a ∈ W₁) (b : W) (hb : b ∈ W₁),
        γ *ᵥ Multiplicative.toAdd (e ⟨a, ha⟩) = Multiplicative.toAdd (e ⟨b, hb⟩) → k a = b) ∧
      (∀ u ∈ W₂, ∀ v ∈ W₂, δᵀ *ᵥ Multiplicative.toAdd (S153E58.dualCoord bil e u) =
        Multiplicative.toAdd (S153E58.dualCoord bil e v) → k u = v) := by
  let gl : GL (Fin 3) (ZMod 2) := ⟨γ, δ, h1, h2⟩
  let g : ↥(StatedSL 3 (ZMod 2)) := ⟨gl, S153E58.mem_statedSL_three_two gl⟩
  refine ⟨(π g : MulAut W), (π g).2, ?_, ?_⟩
  · intro a ha b hb hab
    have hmem : (π g : MulAut W) a ∈ W₁ := hS.inv₁ _ (π g).2 a ha
    have h3 := he g ⟨a, ha⟩ hmem
    have h4 : e ⟨(π g : MulAut W) a, hmem⟩ = e ⟨b, hb⟩ := by
      rw [h3]
      show Multiplicative.ofAdd (γ *ᵥ Multiplicative.toAdd (e ⟨a, ha⟩)) = _
      rw [hab]
      rfl
    exact congrArg Subtype.val (e.injective h4)
  · intro u hu v hv huv
    have hmem : (π g : MulAut W) u ∈ W₂ := hS.inv₂ _ (π g).2 u hu
    have h3 := hS.dualCoord_equivariant he g u
    have h4 : S153E58.dualCoord bil e ((π g : MulAut W) u) = S153E58.dualCoord bil e v := by
      rw [h3]
      show Multiplicative.ofAdd (δᵀ *ᵥ Multiplicative.toAdd (S153E58.dualCoord bil e u)) = _
      rw [huv]
      rfl
    have h4' : hS.dualEquiv hT ⟨(π g : MulAut W) u, hmem⟩ = hS.dualEquiv hT ⟨v, hv⟩ := by
      rw [hS.dualEquiv_apply hT, hS.dualEquiv_apply hT]
      exact h4
    exact congrArg Subtype.val ((hS.dualEquiv hT).injective h4')

theorem exists_conj_mem_of_singular (hS : S153E58.Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) (q : W → ZMod 2)
    (hq : ∀ a b, q (a * b) = q a + q b + bil a b) (hqK : ∀ k ∈ K, ∀ a, q (k a) = q a)
    {Pt : Subgroup W} (hPt : ∀ x ∈ Pt, q x = 0)
    {ℓ₁ ℓ₂ : W} (h₁ : ℓ₁ ∈ W₁) (h₁' : ℓ₁ ≠ 1) (h₁P : ℓ₁ ∈ Pt)
    (h₂ : ℓ₂ ∈ W₂) (h₂' : ℓ₂ ≠ 1) (h₂P : ℓ₂ ∈ Pt) :
    ∀ w, q w = 0 → ∃ k ∈ K, k w ∈ Pt := by
  obtain ⟨e, hT, he⟩ := S153E58.exists_coords_of_realizes hπ
  have hqW₁ : ∀ a ∈ W₁, q a = 0 :=
    q_zero_of_irr hS q hq hqK hS.irr₁ (hS.bil_zero_W₁ hT) (by rw [hS.card₁]; norm_num)
  have hqW₂ : ∀ a ∈ W₂, q a = 0 :=
    q_zero_of_irr hS q hq hqK hS.irr₂ (bil_zero_W₂ hS hπ) (by rw [hS.card₂]; norm_num)
  have hℓ : bil ℓ₁ ℓ₂ = 0 := by
    have h := hq ℓ₁ ℓ₂
    rw [hPt _ (Pt.mul_mem h₁P h₂P), hPt _ h₁P, hPt _ h₂P] at h
    simpa using h.symm
  have hX : ∀ a (ha : a ∈ W₁), a ≠ 1 → Multiplicative.toAdd (e ⟨a, ha⟩) ≠ 0 := by
    intro a ha ha1 h0
    apply ha1
    have : e ⟨a, ha⟩ = 1 := by
      have := congrArg Multiplicative.ofAdd h0
      simpa using this
    have h3 : (⟨a, ha⟩ : ↥W₁) = 1 := e.injective (this.trans (map_one e).symm)
    exact congrArg Subtype.val h3
  have hF : ∀ u ∈ W₂, u ≠ 1 → Multiplicative.toAdd (S153E58.dualCoord bil e u) ≠ 0 := by
    intro u hu hu1 h0
    apply hu1
    apply hS.dualCoord_eq_one hT hu
    have := congrArg Multiplicative.ofAdd h0
    simpa using this
  intro w hw
  obtain ⟨x, hx, u, hu, rfl⟩ := Subgroup.mem_sup.1 (hS.dir.1 ▸ Subgroup.mem_top w : w ∈ W₁ ⊔ W₂)
  by_cases hu1 : u = 1
  · by_cases hx1 : x = 1
    · refine ⟨1, K.one_mem, ?_⟩
      rw [hu1, hx1]
      simp
    · obtain ⟨γ, δ, h1, h2, h3⟩ := nat_trans (hX x hx hx1) (hX ℓ₁ h₁ h₁')
      obtain ⟨k, hk, hk₁, -⟩ := exists_act hS hT he γ δ h1 h2
      refine ⟨k, hk, ?_⟩
      rw [hu1, mul_one, hk₁ x hx ℓ₁ h₁ h3]
      exact h₁P
  · by_cases hx1 : x = 1
    · obtain ⟨γ, δ, h1, h2, h3⟩ := dual_trans (hF u hu hu1) (hF ℓ₂ h₂ h₂')
      obtain ⟨k, hk, -, hk₂⟩ := exists_act hS hT he γ δ h1 h2
      refine ⟨k, hk, ?_⟩
      rw [hx1, one_mul, hk₂ u hu ℓ₂ h₂ h3]
      exact h₂P
    · have hbil : bil x u = 0 := by
        have h := hq x u
        rw [hw, hqW₁ x hx, hqW₂ u hu] at h
        simpa using h.symm
      have hflag : Multiplicative.toAdd (S153E58.dualCoord bil e u) ⬝ᵥ
          Multiplicative.toAdd (e ⟨x, hx⟩) = 0 := by
        rw [dotProduct_comm, ← hS.bil_eq_dot e ⟨x, hx⟩ u]
        exact hbil
      have hflag' : Multiplicative.toAdd (S153E58.dualCoord bil e ℓ₂) ⬝ᵥ
          Multiplicative.toAdd (e ⟨ℓ₁, h₁⟩) = 0 := by
        rw [dotProduct_comm, ← hS.bil_eq_dot e ⟨ℓ₁, h₁⟩ ℓ₂]
        exact hℓ
      obtain ⟨γ, δ, h1, h2, h3, h4⟩ := flag_trans (hX x hx hx1) (hF u hu hu1) hflag (hX ℓ₁ h₁ h₁')
        (hF ℓ₂ h₂ h₂') hflag'
      obtain ⟨k, hk, hk₁, hk₂⟩ := exists_act hS hT he γ δ h1 h2
      refine ⟨k, hk, ?_⟩
      rw [map_mul, hk₁ x hx ℓ₁ h₁ h3, hk₂ u hu ℓ₂ h₂ h4]
      exact Pt.mul_mem h₁P h₂P

end Abstract

end S153E61A

end CFSG.Quasithin
