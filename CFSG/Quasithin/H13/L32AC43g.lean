module

public import CFSG.Quasithin.H13.L32AC43f
public import CFSG.Quasithin.Background.G64RealizeSec

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H.SU3
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H
open scoped Pointwise

theorem exists_scalar_normalizer {X : Type} [CommGroup X] [Finite X]
    {L : Subgroup (MulAut X)} (hnat : BinaryNaturalSU3 L ⊤ ⊥ 3) {P : Subgroup (MulAut X)}
    (hP : IsSylowTwoOf P L) :
    ∃ ν ∈ L, ν ∈ Subgroup.normalizer (P : Set (MulAut X)) ∧
      ∀ Y : Subgroup X, Y ≤ fixV P → Y ≠ ⊥ → (∀ y ∈ Y, ν y ∈ Y) → 64 ≤ Nat.card Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, π, hπ⟩ := hnat
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two
    (by omega : 1 ≤ 2 * 3) (CFSG.Quasithin.H.SU3.card_eq_two_pow hF)
  obtain ⟨f, -, hfk, hfe⟩ := G64.RealizesVia.exists_secMap rfl hπ
  let θ : X → (Fin 3 → F) := fun x => @Multiplicative.toAdd (Fin 3 → F)
    (((f ⟨x, Subgroup.mem_top x⟩ : ↥(FFModel.nat (StatedSU 3 (2 ^ 3) F)).sec) :
      (FFModel.nat (StatedSU 3 (2 ^ 3) F)).Amb))
  have hθ1 : θ 1 = 0 := by
    show @Multiplicative.toAdd (Fin 3 → F) (((f 1 : ↥(FFModel.nat (StatedSU 3 (2 ^ 3) F)).sec) :
      (FFModel.nat (StatedSU 3 (2 ^ 3) F)).Amb)) = 0
    rw [map_one]
    rfl
  have hθinj : ∀ a b : X, θ a = θ b → a = b := by
    intro a b hab
    have h1 : f ⟨a, Subgroup.mem_top a⟩ = f ⟨b, Subgroup.mem_top b⟩ :=
      Subtype.ext (Multiplicative.toAdd.injective hab)
    have h2 : f (⟨a, Subgroup.mem_top a⟩ * ⟨b, Subgroup.mem_top b⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hfk _).mp h2
    rw [Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.mp h3
  obtain ⟨π', hinj, hsurj, hθeq⟩ : ∃ π' : ↥(StatedSU 3 (2 ^ 3) F) →* ↥L,
      Function.Injective π' ∧ Function.Surjective π' ∧ ∀ (γ : ↥(StatedSU 3 (2 ^ 3) F)) (x : X),
        θ (((π' γ : ↥L) : MulAut X) x) =
          ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ θ x :=
    ⟨π, G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ, hπ.1, fun γ x =>
      congrArg Multiplicative.toAdd (hfe γ ⟨x, Subgroup.mem_top x⟩ (Subgroup.mem_top _))⟩
  clear hfe hfk hπ
  set P' : Subgroup ↥(StatedSU 3 (2 ^ 3) F) := (P.subgroupOf L).comap π' with hP'
  have hP'2 : IsPGroup 2 ↥P' := by
    have h1 : IsPGroup 2 ↥(P.subgroupOf L) :=
      hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
    exact h1.comap_of_injective π' hinj
  have hP'i : ¬ 2 ∣ P'.index := by
    rw [hP', Subgroup.index_comap_of_surjective _ hsurj]
    exact hP.2.2
  have hUs := isSylowIn_uiSub (n := 3) (K := F) (by norm_num) hF
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(StatedSU 3 (2 ^ 3) F) hUs.toSylow
    (hP'2.toSylow hP'i)
  have hgP : ∀ γ : ↥(StatedSU 3 (2 ^ 3) F), γ ∈ P' ↔ g⁻¹ * γ * g ∈ (uiSub 3 F).subgroupOf _ := by
    intro γ
    have h1 : P' = MulAut.conj g • (uiSub 3 F).subgroupOf (StatedSU 3 (2 ^ 3) F) := by
      have := congrArg (fun S : Sylow 2 ↥(StatedSU 3 (2 ^ 3) F) =>
        (S : Subgroup ↥(StatedSU 3 (2 ^ 3) F))) hg
      simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, IsSylowIn.coe_toSylow] at this
      exact this.symm
    rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
      MulAut.conj_apply, inv_inv]
  obtain ⟨α, hα⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hnP : ∀ γ ∈ P',
      g * torI (n := 3) hF α * g⁻¹ * γ * (g * torI (n := 3) hF α * g⁻¹)⁻¹ ∈ P' := by
    intro γ hγ
    rw [hgP] at hγ ⊢
    have e : g⁻¹ * (g * torI (n := 3) hF α * g⁻¹ * γ * (g * torI (n := 3) hF α * g⁻¹)⁻¹) * g =
        torI (n := 3) hF α * (g⁻¹ * γ * g) * (torI (n := 3) hF α)⁻¹ := by group
    rw [e]
    exact SU3.torI_conj_mem_uiSub (n := 3) hF α hγ
  have hscal : ∀ v : Fin 3 → F,
      (∀ γ ∈ P', ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) →
      (((g * torI (n := 3) hF α * g⁻¹ : ↥(StatedSU 3 (2 ^ 3) F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ v = (α : F) • v := by
    intro v hv
    set A : GL (Fin 3) F := (g : GL (Fin 3) F) with hA
    set w := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v with hw
    have hvw : v = (A : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
      rw [hw, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hfw : ∀ u ∈ uiSub 3 F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
      intro u hu
      have huS : u ∈ StatedSU 3 (2 ^ 3) F := uiSub_le hu
      have hmem : g * ⟨u, huS⟩ * g⁻¹ ∈ P' := by
        rw [hgP]
        have e : g⁻¹ * (g * ⟨u, huS⟩ * g⁻¹) * g = ⟨u, huS⟩ := by group
        rw [e]
        exact hu
      have h1 := hv _ hmem
      have e2 : (((g * ⟨u, huS⟩ * g⁻¹ : ↥(StatedSU 3 (2 ^ 3) F)) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) = ((A * u * A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
        rfl
      rw [e2] at h1
      have key : (u : Matrix (Fin 3) (Fin 3) F) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            ((A * u * A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        rw [← Units.val_mul, ← Units.val_mul]
        congr 1
        group
      calc (u : Matrix (Fin 3) (Fin 3) F) *ᵥ w
          = ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
              (((A * u * A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
            rw [hw, mulVec_mulVec, mulVec_mulVec, key]
        _ = w := by rw [h1]
    obtain ⟨c, hc⟩ := SU3.fix_uiSub (n := 3) (by norm_num) hF hfw
    have e3 : (((g * torI (n := 3) hF α * g⁻¹ : ↥(StatedSU 3 (2 ^ 3) F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) *
          (((torI (n := 3) hF α : ↥(StatedSU 3 (2 ^ 3) F)) : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl
    rw [e3, ← mulVec_mulVec, ← mulVec_mulVec, ← hw, hc, SU3.torI_mulVec_e, mulVec_smul, hvw, hc,
      mulVec_smul, smul_smul]
  have : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) fun a b h => MulEquiv.ext (congrFun h)
  obtain ⟨ν, hν⟩ : ∃ ν : MulAut X,
      ν = ((π' (g * torI (n := 3) hF α * g⁻¹) : ↥L) : MulAut X) := ⟨_, rfl⟩
  refine ⟨ν, by rw [hν]; exact (π' _).2, Subgroup.mem_normalizer_fintype fun y hy => ?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := hsurj ⟨y, hP.1 hy⟩
    have hγP : γ ∈ P' := by
      show π' γ ∈ P.subgroupOf L
      rw [hγ]
      exact hy
    have h1 := hnP γ hγP
    have h2 : ((π' (g * torI (n := 3) hF α * g⁻¹ * γ * (g * torI (n := 3) hF α * g⁻¹)⁻¹) : ↥L) :
        MulAut X) = ν * y * ν⁻¹ := by
      rw [map_mul, map_mul, map_inv, hγ, hν]
      rfl
    rw [← h2]
    exact h1
  · intro Y hYP hY1 hYν
    have hfixY : ∀ y ∈ Y, ∀ γ ∈ P',
        ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ θ y = θ y := by
      intro y hy γ hγ
      rw [← hθeq, mem_fixV.mp (hYP hy) _ (show ((π' γ : ↥L) : MulAut X) ∈ P from hγ)]
    have hνθ : ∀ y ∈ Y, θ (ν y) = (α : F) • θ y := by
      intro y hy
      rw [hν, hθeq, hscal _ (hfixY y hy)]
    have hpow : ∀ k : ℕ, ∀ y ∈ Y, (ν ^ k) y ∈ Y ∧ θ ((ν ^ k) y) = (α : F) ^ k • θ y := by
      intro k
      induction k with
      | zero => intro y hy; simp [hy]
      | succ k ih =>
        intro y hy
        obtain ⟨h1, h2⟩ := ih _ (hYν y hy)
        refine ⟨?_, ?_⟩
        · rw [pow_succ ν, MulAut.mul_apply]
          exact h1
        · rw [pow_succ ν, MulAut.mul_apply, h2, hνθ y hy, smul_smul, pow_succ]
    obtain ⟨⟨y₀, hy₀⟩, hy₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hY1
    have hv₀ : θ y₀ ≠ 0 := by
      intro h
      apply hy₀1
      exact Subtype.ext (hθinj _ _ (h.trans hθ1.symm))
    have hall : ∀ c : F, ∃ y ∈ Y, θ y = c • θ y₀ := by
      intro c
      by_cases hc : c = 0
      · exact ⟨1, Y.one_mem, by rw [hθ1, hc, zero_smul]⟩
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, α ^ k = Units.mk0 c hc := by
          have h1 : Units.mk0 c hc ∈ Subgroup.zpowers α := hα _
          rw [← (isOfFinOrder_of_finite α).mem_powers_iff_mem_zpowers] at h1
          exact Submonoid.mem_powers_iff _ _ |>.mp h1
        refine ⟨_, (hpow k y₀ hy₀).1, ?_⟩
        rw [(hpow k y₀ hy₀).2]
        congr 1
        rw [← Units.val_pow_eq_pow_val, hk, Units.val_mk0]
    choose φ hφY hφ using hall
    have hφinj : Function.Injective fun c : F => (⟨φ c, hφY c⟩ : ↥Y) := by
      intro c c' h
      have h1 : c • θ y₀ = c' • θ y₀ := by
        rw [← hφ, ← hφ]
        exact congrArg (fun z : ↥Y => θ z) h
      have h2 : (c - c') • θ y₀ = 0 := by rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 hv₀
    have h1 := Nat.card_le_card_of_injective _ hφinj
    rw [hF] at h1
    norm_num at h1
    exact h1

end CFSG.Quasithin.H13.L32A.C
