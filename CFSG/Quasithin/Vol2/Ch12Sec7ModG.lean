module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModD
public import CFSG.Quasithin.Vol2.Ch12Sec7ModF
public import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6Six

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Fischer

theorem encV_add (x y : Fin 3 → F4) : encV (x + y) = encV x ^^^ encV y := by
  have h := decV_xor (encV_lt x) (encV_lt y)
  rw [decV_encV, decV_encV] at h
  rw [← h, encV_decV (xor_lt_64 _ (encV_lt x) _ (encV_lt y))]

namespace Coding

variable {V : Type} [CommGroup V] (C : Coding V)

theorem cB_eq_of (a : MulAut V) (B : B6) (h : ∀ v, C.cd (a v) = B.app (C.cd v)) : C.cB a = B := by
  apply B6.ext_app
  intro c hc
  have e := h (C.dc c)
  rw [C.cd_dc c hc, C.cd_apply, C.cd_dc c hc] at e
  exact e

@[expose] def recode (b : MulAut V) : Coding V where
  cd v := C.cd (b v)
  dc c := b⁻¹ (C.dc c)
  cd_lt v := C.cd_lt _
  dc_cd v := by simp [C.dc_cd]
  cd_dc c hc := by simp [C.cd_dc c hc]
  cd_mul u v := by simp [map_mul, C.cd_mul]

theorem recode_cd (b : MulAut V) (v : V) : (C.recode b).cd v = C.cd (b v) := rfl

theorem recode_cB (b a : MulAut V) : (C.recode b).cB a = C.cB (b * a * b⁻¹) := by
  apply cB_eq_of
  intro v
  rw [recode_cd, recode_cd, ← C.cd_apply]
  simp

end Coding

@[expose] def IdentL {V : Type} [CommGroup V] (C : Coding V) (H : Subgroup (MulAut V)) : Prop :=
  (∀ a : MulAut V, a ∈ H ↔ C.cB a ∈ gm6) ∧ ∀ B ∈ gm6, ∃ a : MulAut V, C.cB a = B

theorem IdentL.recode {V : Type} [CommGroup V] {C : Coding V} {H : Subgroup (MulAut V)}
    (hC : IdentL C H) {b : MulAut V} (hb : b ∈ H) : IdentL (C.recode b) H := by
  refine ⟨fun a => ?_, fun B hB => ?_⟩
  · rw [C.recode_cB, ← hC.1]
    constructor
    · intro ha
      exact H.mul_mem (H.mul_mem hb ha) (H.inv_mem hb)
    · intro ha
      have := H.mul_mem (H.mul_mem (H.inv_mem hb) ha) hb
      simpa [mul_assoc] using this
  · obtain ⟨a, ha⟩ := hC.2 B hB
    refine ⟨b⁻¹ * a * b, ?_⟩
    rw [C.recode_cB]
    simpa [mul_assoc] using ha

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_identL (hV2 : ∀ v : V, v ^ 2 = 1)
    (hV : Nat.card V = 2 ^ 6) (H : Subgroup (MulAut V)) (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (he : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {t : V} (ht : Nat.card (Orbit.orbitIn H t) = 18) : ∃ C : Coding V, IdentL C H := by
  classical
  let _ : Module (ZMod 2) (Additive V) := zmod2ModuleOfExp hV2
  have : Finite (Additive V) := Finite.of_equiv V Additive.ofMul
  have hW : Nat.card (Additive V) = 2 ^ 6 := by
    rw [← hV]
    exact Nat.card_congr Additive.toMul
  let ρ : ↥H →* (Additive V →ₗ[ZMod 2] Additive V) := linAutHom.comp H.subtype
  have hρ : Function.Injective ρ := fun a b h => Subtype.ext (linAutHom_injective h)
  obtain ⟨Φ, μ, hμ, -, hequiv, hcent⟩ := exists_f4_model hW hperf ρ hρ hZ
  have hact : ∀ (h : ↥H) (v : V), Φ (Additive.ofMul ((h : MulAut V) v)) =
      ((μ h : GL3) : Matrix (Fin 3) (Fin 3) F4).mulVec (Φ (Additive.ofMul v)) :=
    fun h v => hequiv h (Additive.ofMul v)
  set Γ : Subgroup GL3 := μ.range with hΓ
  have hcardH : Nat.card H = 1080 := by
    obtain ⟨e⟩ := he
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H),
      Nat.card_congr e.toEquiv, hZ, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcard : Nat.card Γ = 1080 := by
    rw [← hcardH]
    exact (Nat.card_congr (MonoidHom.ofInjective hμ).toEquiv).symm
  have hZmap : (Subgroup.center H).map μ = scalars := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc⟩ := hcent g hg
      exact ⟨c, hc⟩
    · rw [card_scalars, Subgroup.card_map_of_injective hμ, hZ]
  have hsc : scalars ≤ Γ := by
    rw [← hZmap]
    exact Subgroup.map_le_range μ _
  have hsimple : SimpleMod Γ := by
    intro N hNΓ hnorm hscN
    obtain ⟨e⟩ := he
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    have hs : IsSimpleGroup (H ⧸ Subgroup.center H) := e.isSimpleGroup
    let N' : Subgroup H := N.comap μ
    have hN'n : N'.Normal := ⟨fun n hn g => by
      show μ (g * n * g⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hnorm _ ⟨g, rfl⟩ _ hn⟩
    have hZN' : Subgroup.center H ≤ N' := fun z hz => hscN (hZmap ▸ ⟨z, hz, rfl⟩)
    have hmapN : (N'.map (QuotientGroup.mk' (Subgroup.center H))).Normal :=
      Subgroup.Normal.map hN'n _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (N'.map (QuotientGroup.mk' (Subgroup.center H))) with h | h
    · left
      have hle : N' ≤ Subgroup.center H := by
        intro n hn
        have hmem : QuotientGroup.mk' (Subgroup.center H) n ∈
            N'.map (QuotientGroup.mk' (Subgroup.center H)) := ⟨n, hn, rfl⟩
        rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
        exact hmem
      apply le_antisymm _ hscN
      intro x hx
      obtain ⟨g, rfl⟩ := hNΓ hx
      rw [← hZmap]
      exact ⟨g, hle hx, rfl⟩
    · right
      apply le_antisymm hNΓ
      rintro _ ⟨g, rfl⟩
      have hmem : QuotientGroup.mk' (Subgroup.center H) g ∈
          N'.map (QuotientGroup.mk' (Subgroup.center H)) := by
        rw [h]
        trivial
      obtain ⟨n, hn, hng⟩ := hmem
      have hz : n⁻¹ * g ∈ Subgroup.center H := QuotientGroup.eq.mp hng
      have e2 : g = n * (n⁻¹ * g) := by group
      rw [e2, map_mul]
      exact N.mul_mem hn (hZN' hz)
  have h18 : Nat.card (orb Γ (Φ (Additive.ofMul t))) = 18 := by
    have himg : orb Γ (Φ (Additive.ofMul t)) =
        (fun v : V => Φ (Additive.ofMul v)) '' Orbit.orbitIn H t := by
      ext y
      constructor
      · rintro ⟨γ, ⟨h, rfl⟩, rfl⟩
        exact ⟨(h : MulAut V) t, ⟨h, h.2, rfl⟩, hact h t⟩
      · rintro ⟨w, ⟨h, hh, rfl⟩, rfl⟩
        exact ⟨μ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, (hact ⟨h, hh⟩ t).symm⟩
    rw [himg, Nat.card_image_of_injective (fun u v huv =>
      Additive.ofMul.injective (Φ.injective huv)) _, ht]
  obtain ⟨g, hg⟩ := exists_conj_gm hcard hsc hsimple h18
  let C : Coding V :=
    { cd := fun v => encV ((g : Matrix (Fin 3) (Fin 3) F4).mulVec (Φ (Additive.ofMul v)))
      dc := fun c => Additive.toMul (Φ.symm (((g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) F4).mulVec
        (decV c)))
      cd_lt := fun v => encV_lt _
      dc_cd := fun v => by
        simp only [decV_encV, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec,
          AddEquiv.symm_apply_apply, toMul_ofMul]
      cd_dc := fun c hc => by
        simp only [ofMul_toMul, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec,
          ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
        exact encV_decV hc
      cd_mul := fun u v => by
        simp only [ofMul_mul, map_add, Matrix.mulVec_add, encV_add] }
  have key : ∀ h : ↥H, C.cB h =
      (Mc.ofMat (((g * μ h * g⁻¹ : GL3)) : Matrix (Fin 3) (Fin 3) F4)).toB6 := by
    intro h
    apply C.cB_eq_of
    intro v
    rw [toB6_app _ (C.cd_lt v)]
    show encV ((g : Matrix (Fin 3) (Fin 3) F4).mulVec (Φ (Additive.ofMul ((h : MulAut V) v)))) =
      _
    rw [hact h v]
    have e3 : (C.cd v) = encV ((g : Matrix (Fin 3) (Fin 3) F4).mulVec (Φ (Additive.ofMul v))) :=
      rfl
    rw [e3, ← encV_decV (Mc.app_lt _ (Mc.ofMat_valid _)
      (v := encV ((g : Matrix (Fin 3) (Fin 3) F4).mulVec (Φ (Additive.ofMul v))))), ← app_ofMat,
      decV_encV]
    have hM : ((g * μ h * g⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) F4) *
        (g : Matrix (Fin 3) (Fin 3) F4) =
        (g : Matrix (Fin 3) (Fin 3) F4) * ((μ h : GL3) : Matrix (Fin 3) (Fin 3) F4) := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul]
      congr 1
      group
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  refine ⟨C, fun a => ⟨fun ha => ?_, fun h => ?_⟩, fun B hB => ?_⟩
  · have hmem : g * μ ⟨a, ha⟩ * g⁻¹ ∈ gm := (hg _).1 ⟨⟨a, ha⟩, rfl⟩
    rw [show a = ((⟨a, ha⟩ : ↥H) : MulAut V) from rfl, key]
    exact List.mem_map.2 ⟨_, (mem_gm_iff _).1 hmem, rfl⟩
  · obtain ⟨A, hA, hAa⟩ := List.mem_map.1 h
    have hγ : g⁻¹ * glOf A hA * g ∈ Γ := by
      rw [hg]
      simpa [mul_assoc] using glOf_mem A hA
    obtain ⟨h', hh'⟩ := hγ
    have e4 : C.cB h' = C.cB a := by
      rw [key, hh', ← hAa]
      congr 1
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
      exact ofMat_glOf A hA
    rw [← C.cB_injective e4]
    exact h'.2
  · obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
    have hγ : g⁻¹ * glOf A hA * g ∈ Γ := by
      rw [hg]
      simpa [mul_assoc] using glOf_mem A hA
    obtain ⟨h', hh'⟩ := hγ
    refine ⟨h', ?_⟩
    rw [key, hh']
    congr 1
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
    exact ofMat_glOf A hA

end CFSG.Quasithin.H13.S127.Mod

end
