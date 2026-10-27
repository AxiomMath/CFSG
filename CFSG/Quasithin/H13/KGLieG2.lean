module

public import CFSG.Quasithin.H13.KGLieNat
public import CFSG.Quasithin.H13.KGLieSec

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup

@[expose] noncomputable def zscal {F : Type} [Field F] (c : Fˣ) :
    Multiplicative (quasithinZorn F) ≃* Multiplicative (quasithinZorn F) :=
  (DistribMulAction.toAddEquiv (quasithinZorn F) c).toMultiplicative

theorem toAdd_zscal {F : Type} [Field F] (c : Fˣ) (x : Multiplicative (quasithinZorn F)) :
    Multiplicative.toAdd (zscal c x) = (c : F) • Multiplicative.toAdd x := rfl

section Zorn

variable {F : Type} [Field F]

theorem zscal_mem_zornO0_iff (c : Fˣ) (x : Multiplicative (quasithinZorn F)) :
    x ∈ zornO0 F ↔ zscal c x ∈ zornO0 F := by
  rw [G64.mem_zornO0, G64.mem_zornO0, toAdd_zscal]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← mul_add]
  constructor
  · intro h0
    rw [h0, mul_zero]
  · intro h0
    exact (mul_eq_zero.1 h0).resolve_left c.ne_zero

theorem zscal_mem_zornR_iff (c : Fˣ) (x : Multiplicative (quasithinZorn F)) :
    x ∈ zornR F ↔ zscal c x ∈ zornR F := by
  rw [G64.mem_zornR, G64.mem_zornR, toAdd_zscal]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨(c : F) * d, ?_⟩
    rw [hd]
    ext <;> simp
  · rintro ⟨d, hd⟩
    refine ⟨(c : F)⁻¹ * d, ?_⟩
    have : Multiplicative.toAdd x = (c : F)⁻¹ • ((c : F) • Multiplicative.toAdd x) := by
      rw [smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]
    rw [this, hd]
    ext <;> simp

theorem zscal_zornAct (Γ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)) (c : Fˣ) (γ : ↥Γ)
    (x : Multiplicative (quasithinZorn F)) :
    zscal c (zornAct Γ γ x) = zornAct Γ γ (zscal c x) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_zscal]
  show (c : F) • (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) (Multiplicative.toAdd x) =
    (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) ((c : F) • Multiplicative.toAdd x)
  rw [LinearEquiv.map_smul]

theorem eq_of_zscal_mem_zornR {x : Multiplicative (quasithinZorn F)} (hxk : x ∉ zornR F)
    {c c' : Fˣ} (h : zscal c x * (zscal c' x)⁻¹ ∈ zornR F) : c = c' := by
  by_contra hne
  apply hxk
  obtain ⟨d, hd⟩ := (G64.mem_zornR).1 h
  have hd' : ((c : F) - c') • Multiplicative.toAdd x = (d, 0, 0, d) := by
    rw [← hd, toAdd_mul, toAdd_inv, toAdd_zscal, toAdd_zscal, sub_smul, sub_eq_add_neg]
  have hsub : (c : F) - c' ≠ 0 := sub_ne_zero.2 (fun h => hne (Units.ext h))
  refine (G64.mem_zornR).2 ⟨((c : F) - c')⁻¹ * d, ?_⟩
  have : Multiplicative.toAdd x =
      ((c : F) - c')⁻¹ • (((c : F) - c') • Multiplicative.toAdd x) := by
    rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
  rw [this, hd']
  ext <;> simp

@[expose] def zornU : ↥(zornO0 F) →* Multiplicative (Fin 3 → F) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd (x : Multiplicative (quasithinZorn F))).2.1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem card_zornQ_ge [Finite F] :
    Nat.card F ^ 3 ≤ Nat.card (↥(zornO0 F) ⧸ (zornR F).subgroupOf (zornO0 F)) := by
  have hN : (zornR F).subgroupOf (zornO0 F) ≤ (zornU (F := F)).ker := by
    intro x hx
    obtain ⟨d, hd⟩ := (G64.mem_zornR).1 (Subgroup.mem_subgroupOf.1 hx)
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (Multiplicative.toAdd (x : Multiplicative (quasithinZorn F))).2.1 = 1
    rw [hd]
    rfl
  set φ := QuotientGroup.lift _ (zornU (F := F)) hN with hφ
  set f : (Fin 3 → F) → ↥(zornO0 F) ⧸ (zornR F).subgroupOf (zornO0 F) :=
    fun u => QuotientGroup.mk ⟨Multiplicative.ofAdd ((0, u, 0, 0) : quasithinZorn F),
      (G64.mem_zornO0).2 (by simp)⟩ with hf
  have hfi : Function.Injective f := by
    intro u u' huu
    have h1 := congrArg φ huu
    rw [hf] at h1
    simp only [hφ, QuotientGroup.lift_mk] at h1
    exact Multiplicative.ofAdd.injective h1
  have hle := Nat.card_le_card_of_injective f hfi
  rwa [Nat.card_fun, Nat.card_fin] at hle

end Zorn

theorem factLieG2Row1321_holds : A5.FactLieG2Row1321 := by
  intro V _ _ hV2 G L v hB4 hc n hn h
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hF8 : 8 ≤ Nat.card F := hF ▸ eight_le_two_pow hn
  obtain ⟨m, hmL, hinj, hcard⟩ := scalars_of_realizes hπ (fun c : Fˣ => zscal c)
    (fun c x => zscal_mem_zornO0_iff c x) (fun c x => zscal_mem_zornR_iff c x)
    (fun c γ x => zscal_zornAct _ c γ x)
    (fun x _ hxk c c' hcc => eq_of_zscal_mem_zornR hxk hcc)
  refine false_of_cond_scalars hV2 hB4 hc (ι := Fˣ) ?_ m hmL hinj ?_
  · rw [Nat.card_units]
    omega
  · rw [hcard]
    calc 16 < 8 ^ 3 := by norm_num
      _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hF8 3
      _ ≤ _ := card_zornQ_ge

end CFSG.Quasithin.H13.KGLie
