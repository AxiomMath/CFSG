module

public import CFSG.Quasithin.Background.G10Basic
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.G10Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem le_of_normal_of_pow_mem_normalCore_of_odd_index {G : Type*} [Group G] [Finite G]
    (S N : Subgroup G) [hN : N.Normal] (hS : ¬ 2 ∣ S.index)
    (hpow : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k ∈ S.normalCore) : N ≤ S := by
  let ρ : G →* Equiv.Perm (G ⧸ S) := MulAction.toPermHom G (G ⧸ S)
  let P : Subgroup (Equiv.Perm (G ⧸ S)) := N.map ρ
  have hP : IsPGroup 2 P := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨k, hk⟩ := hpow n hn
    refine ⟨k, Subtype.ext ?_⟩
    show (ρ n) ^ 2 ^ k = 1
    rw [← map_pow]
    ext ω
    induction ω using QuotientGroup.induction_on with
    | H g =>
      show (n ^ 2 ^ k) • (g : G ⧸ S) = g
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
      have h1 : g⁻¹ * n ^ 2 ^ k * g⁻¹⁻¹ ∈ S := hk g⁻¹
      have h2 : (n ^ 2 ^ k * g)⁻¹ * g = (g⁻¹ * n ^ 2 ^ k * g⁻¹⁻¹)⁻¹ := by group
      rw [h2]
      exact S.inv_mem h1
  have hcard : ¬ 2 ∣ Nat.card (G ⧸ S) := by
    rwa [← Subgroup.index]
  obtain ⟨ω, hω⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ S) hcard
  induction ω using QuotientGroup.induction_on with
  | H g₀ =>
    intro n hn
    have hfix : ∀ m ∈ N, (m * g₀)⁻¹ * g₀ ∈ S := by
      intro m hm
      have := (MulAction.mem_fixedPoints.1 hω) ⟨ρ m, Subgroup.mem_map_of_mem ρ hm⟩
      have h3 : ((m * g₀ : G) : G ⧸ S) = (g₀ : G ⧸ S) := this
      exact QuotientGroup.eq.1 h3
    have hconj : g₀ * n⁻¹ * g₀⁻¹ ∈ N := hN.conj_mem n⁻¹ (N.inv_mem hn) g₀
    have h5 := hfix _ hconj
    have h4 : ((g₀ * n⁻¹ * g₀⁻¹) * g₀)⁻¹ * g₀ = n := by group
    rwa [h4] at h5

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace G101Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)}

private theorem apply_inv_left (h : G101Hyp B Γ v₁ W X X₀) {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ)
    (u w : V) : B u (γ w) = B (γ⁻¹ u) w := by
  have h1 := h.isometry γ hγ (γ⁻¹ u) w
  have h2 : γ (γ⁻¹ u) = u := γ.apply_symm_apply u
  rwa [h2] at h1

private def stabPerp (h : G101Hyp B Γ v₁ W X X₀) (U : Submodule (ZMod 2) V)
    (hU : Invariant Γ U) : Subgroup ↥Γ where
  carrier := {γ | ∀ u ∈ U, B u ((γ : V ≃ₗ[ZMod 2] V) v₁) = B u v₁}
  mul_mem' := by
    intro a b ha hb u hu
    show B u ((a : V ≃ₗ[ZMod 2] V) ((b : V ≃ₗ[ZMod 2] V) v₁)) = B u v₁
    calc B u ((a : V ≃ₗ[ZMod 2] V) ((b : V ≃ₗ[ZMod 2] V) v₁))
        = B ((a : V ≃ₗ[ZMod 2] V)⁻¹ u) ((b : V ≃ₗ[ZMod 2] V) v₁) := h.apply_inv_left a.2 u _
      _ = B ((a : V ≃ₗ[ZMod 2] V)⁻¹ u) v₁ := hb _ (hU _ (Γ.inv_mem a.2) u hu)
      _ = B u ((a : V ≃ₗ[ZMod 2] V) v₁) := (h.apply_inv_left a.2 u v₁).symm
      _ = B u v₁ := ha u hu
  one_mem' := fun u _ => rfl
  inv_mem' := by
    intro a ha u hu
    show B u ((a : V ≃ₗ[ZMod 2] V)⁻¹ v₁) = B u v₁
    calc B u ((a : V ≃ₗ[ZMod 2] V)⁻¹ v₁)
        = B ((a : V ≃ₗ[ZMod 2] V)⁻¹⁻¹ u) v₁ := h.apply_inv_left (Γ.inv_mem a.2) u v₁
      _ = B ((a : V ≃ₗ[ZMod 2] V) u) v₁ := by rw [inv_inv]
      _ = B ((a : V ≃ₗ[ZMod 2] V) u) ((a : V ≃ₗ[ZMod 2] V) v₁) :=
          (ha _ (hU _ a.2 u hu)).symm
      _ = B u v₁ := h.isometry _ a.2 u v₁

theorem g10_3_twoReducedOn (h : G101Hyp B Γ v₁ W X X₀) (U : Submodule (ZMod 2) V)
    (hU : Invariant Γ U) : TwoReducedOn Γ U := by
  intro N hNΓ hNnorm hN2 n hn u hu
  have hN' : (N.subgroupOf Γ).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hNnorm g g.2 x hx⟩
  have hS : ¬ 2 ∣ (stabPerp h U hU).index := by
    have hle : MulAction.stabilizer ↥Γ v₁ ≤ stabPerp h U hU := by
      intro γ hγ u' _
      have : (γ : V ≃ₗ[ZMod 2] V) v₁ = v₁ := hγ
      rw [this]
    have hodd : Odd (stabPerp h U hU).index :=
      Odd.of_dvd_nat h.odd_index (Subgroup.index_dvd_of_le hle)
    rintro ⟨c, hc⟩
    obtain ⟨m, hm⟩ := hodd
    omega
  have hpow : ∀ x ∈ N.subgroupOf Γ, ∃ k : ℕ, x ^ 2 ^ k ∈ (stabPerp h U hU).normalCore := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨k, hk⟩ := hN2 x hx
    refine ⟨k, fun b u' hu' => ?_⟩
    have hmΓ : (x : V ≃ₗ[ZMod 2] V) ^ 2 ^ k ∈ Γ := Γ.pow_mem x.2 _
    have hb : (b : V ≃ₗ[ZMod 2] V)⁻¹ ∈ Γ := Γ.inv_mem b.2
    have hbu : (b : V ≃ₗ[ZMod 2] V)⁻¹ u' ∈ U := hU _ hb u' hu'
    have hmb : ((x : V ≃ₗ[ZMod 2] V) ^ 2 ^ k) ((b : V ≃ₗ[ZMod 2] V)⁻¹ u') =
        (b : V ≃ₗ[ZMod 2] V)⁻¹ u' := hk _ hbu
    have hmb' : ((x : V ≃ₗ[ZMod 2] V) ^ 2 ^ k)⁻¹ ((b : V ≃ₗ[ZMod 2] V)⁻¹ u') =
        (b : V ≃ₗ[ZMod 2] V)⁻¹ u' := (LinearEquiv.symm_apply_eq _).2 hmb.symm
    show B u' ((b : V ≃ₗ[ZMod 2] V) (((x : V ≃ₗ[ZMod 2] V) ^ 2 ^ k)
      ((b : V ≃ₗ[ZMod 2] V)⁻¹ v₁))) = B u' v₁
    calc B u' ((b : V ≃ₗ[ZMod 2] V) (((x : V ≃ₗ[ZMod 2] V) ^ 2 ^ k)
          ((b : V ≃ₗ[ZMod 2] V)⁻¹ v₁)))
        = B ((b : V ≃ₗ[ZMod 2] V)⁻¹ u') (((x : V ≃ₗ[ZMod 2] V) ^ 2 ^ k)
          ((b : V ≃ₗ[ZMod 2] V)⁻¹ v₁)) := h.apply_inv_left b.2 _ _
      _ = B (((x : V ≃ₗ[ZMod 2] V) ^ 2 ^ k)⁻¹ ((b : V ≃ₗ[ZMod 2] V)⁻¹ u'))
          ((b : V ≃ₗ[ZMod 2] V)⁻¹ v₁) := h.apply_inv_left hmΓ _ _
      _ = B ((b : V ≃ₗ[ZMod 2] V)⁻¹ u') ((b : V ≃ₗ[ZMod 2] V)⁻¹ v₁) := by rw [hmb']
      _ = B u' v₁ := h.isometry _ hb u' v₁
  have hNS := le_of_normal_of_pow_mem_normalCore_of_odd_index (stabPerp h U hU)
    (N.subgroupOf Γ) hS hpow
  have hF4 : ∀ y ∈ N, ∀ u' ∈ U, B u' (y v₁) = B u' v₁ := fun y hy u' hu' =>
    hNS (show (⟨y, hNΓ hy⟩ : ↥Γ) ∈ N.subgroupOf Γ from hy) u' hu'
  have hF5 : ∀ y ∈ N, ∀ w : V, ∀ u' ∈ U, B u' (y w) = B u' w := by
    intro y hy
    let Fx : Submodule (ZMod 2) V :=
      { carrier := {w | ∀ u' ∈ U, B u' (y w) = B u' w}
        add_mem' := fun {a b} ha hb u' hu' => by
          simp only [map_add]
          rw [ha u' hu', hb u' hu']
        zero_mem' := fun u' _ => by simp
        smul_mem' := fun c a ha u' hu' => by
          simp only [map_smul]
          rw [ha u' hu'] }
    have horb : ∀ γ : ↥Γ, (γ : V ≃ₗ[ZMod 2] V) v₁ ∈ Fx := by
      intro γ u' hu'
      have hγ : (γ : V ≃ₗ[ZMod 2] V)⁻¹ ∈ Γ := Γ.inv_mem γ.2
      have hconj : (γ : V ≃ₗ[ZMod 2] V)⁻¹ * y * (γ : V ≃ₗ[ZMod 2] V) ∈ N := by
        simpa using hNnorm _ hγ y hy
      calc B u' (y ((γ : V ≃ₗ[ZMod 2] V) v₁))
          = B ((γ : V ≃ₗ[ZMod 2] V)⁻¹ u') ((γ : V ≃ₗ[ZMod 2] V)⁻¹
            (y ((γ : V ≃ₗ[ZMod 2] V) v₁))) := (h.isometry _ hγ u' _).symm
        _ = B ((γ : V ≃ₗ[ZMod 2] V)⁻¹ u') v₁ := hF4 _ hconj _ (hU _ hγ u' hu')
        _ = B u' ((γ : V ≃ₗ[ZMod 2] V) v₁) := (h.apply_inv_left γ.2 u' v₁).symm
    have htop : (⊤ : Submodule (ZMod 2) V) ≤ Fx := by
      rw [← h.span_orbit, Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      exact horb γ
    exact fun w => htop (Submodule.mem_top : w ∈ (⊤ : Submodule (ZMod 2) V))
  have hnΓ : n ∈ Γ := hNΓ hn
  have h0 : n u - u = 0 := by
    apply h.nondegenerate
    intro w
    rw [map_sub, LinearMap.sub_apply]
    have h1 : B (n u) w = B u w := by
      have e : n (n⁻¹ w) = w := n.apply_symm_apply w
      calc B (n u) w = B (n u) (n (n⁻¹ w)) := by rw [e]
        _ = B u (n⁻¹ w) := h.isometry n hnΓ u _
        _ = B u w := hF5 n⁻¹ (N.inv_mem hn) w u hu
    rw [h1, sub_self]
  exact sub_eq_zero.1 h0

theorem g10_3_pCoreOf_eq_bot (h : G101Hyp B Γ v₁ W X X₀) : pCoreOf 2 Γ = ⊥ := by
  have hU : Invariant Γ (⊤ : Submodule (ZMod 2) V) := fun _ _ _ _ => Submodule.mem_top
  refine eq_bot_iff.2 fun n hn => ?_
  rw [Subgroup.mem_bot]
  refine LinearEquiv.ext fun u => ?_
  have hnorm : ∀ γ ∈ Γ, ∀ x ∈ pCoreOf 2 Γ, γ * x * γ⁻¹ ∈ pCoreOf 2 Γ := fun γ hγ x hx =>
    (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Γ hγ) x).1 hx
  have hpow : ∀ x ∈ pCoreOf 2 Γ, ∃ k : ℕ, ∀ u ∈ (⊤ : Submodule (ZMod 2) V), (x ^ 2 ^ k) u = u := by
    intro x hx
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Γ) ⟨x, hx⟩
    refine ⟨k, fun u _ => ?_⟩
    have : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [this]
    rfl
  exact h.g10_3_twoReducedOn ⊤ hU (pCoreOf 2 Γ) (CFSG.LieType.BorelTits.pCoreOf_le 2 Γ) hnorm
    hpow n hn u Submodule.mem_top

end G101Hyp

namespace G11

theorem g10_3 : G1003Stmt := by
  intro V _ _ _ B Γ v₁ W X X₀ h
  exact And.intro (fun U _ hU => h.g10_3_twoReducedOn U hU) h.g10_3_pCoreOf_eq_bot

end G11

end CFSG.Quasithin
