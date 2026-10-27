module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoNorm
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoEngine
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoKData11
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoKData10
public import CFSG.Quasithin.AppendixH.Common.OctadFlag
public import CFSG.Quasithin.AppendixH.H14.MathieuModuleCoordinates
public import CFSG.Quasithin.Background.HMathieuFacts24Base

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu

open CFSG.Quasithin.H.Mathieu.H16Pf

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

private theorem rho11_eq_rhoM24 (hΓ : Γ ≤ AutPerm) (k : ↥Γ) :
    rho11 Γ hΓ k = rhoM24 ⟨(k : S24), hΓ k.2⟩ := rfl

private theorem hasArr_koPerm_priv (t : Fin 16) : HasArr (koPerm t) (koArr t) :=
  hasArr_permOfArr (koArr_ok t).1

private theorem koPerm_mem_AutPerm_priv (t : Fin 16) : koPerm t ∈ AutPerm :=
  mem_AutPerm_of_arr (koArr_ok t).1 (koArr_ok t).2.1

private theorem koPerm_mem_mog22plus_priv (t : Fin 16) : koPerm t ∈ mog22plus :=
  mog22_le_mog22plus (koPerm_mem_mog22 t)

private theorem rhoM24_koPerm_toW (t : Fin 16) (m : ℕ) :
    rhoM24 ⟨koPerm t, koPerm_mem_AutPerm_priv t⟩ (toW 11 m) = toW 11 (act11 (koArr t) m) :=
  rho11_toW AutPerm le_rfl ⟨koPerm t, _⟩ (hasArr_koPerm_priv t) m

private theorem rho10_koPerm_toW (t : Fin 16) (m : ℕ) :
    rho10 mog22plus le_rfl ⟨koPerm t, koPerm_mem_mog22plus_priv t⟩ (toW 10 m) =
      toW 10 (act10 (koArr t) m) :=
  rho10_toW mog22plus le_rfl ⟨koPerm t, _⟩ (hasArr_koPerm_priv t) m

private theorem koMats11_length : koMats11.length = 16 := rfl

private theorem koMats10_length : koMats10.length = 16 := rfl

private theorem koMats11_getD {t : ℕ} (ht : t < 16) :
    koMats11.getD t [] = matOf 11 (act11 (koArr t)) := by
  rw [koMats11_spec]
  rw [List.getD_eq_getElem
    (l := (List.range 16).map fun t => matOf 11 (act11 (koArr t))) (d := []) (n := t)
    (by simpa using ht)]
  simp

private theorem koMats10_getD {t : ℕ} (ht : t < 16) :
    koMats10.getD t [] = matOf 10 (act10 (koArr t)) := by
  rw [koMats10_spec]
  rw [List.getD_eq_getElem
    (l := (List.range 16).map fun t => matOf 10 (act10 (koArr t))) (d := []) (n := t)
    (by simpa using ht)]
  simp

private theorem act11_mod (aa : Array ℕ) (m : ℕ) : act11 aa (m % 2 ^ 11) = act11 aa m := by
  have hlen : liftECols.length = 11 := rfl
  change actM ccECols (permM aa (actM liftECols (m % 2 ^ 11))) =
    actM ccECols (permM aa (actM liftECols m))
  rw [show actM liftECols (m % 2 ^ 11) = actM liftECols m by
    simpa only [hlen] using actM_mod liftECols m]

private theorem act10_mod (aa : Array ℕ) (m : ℕ) : act10 aa (m % 2 ^ 10) = act10 aa m := by
  have hlen : lift10Cols.length = 10 := rfl
  change actM cc10Cols (permM aa (actM lift10Cols (m % 2 ^ 10))) =
    actM cc10Cols (permM aa (actM lift10Cols m))
  rw [show actM lift10Cols (m % 2 ^ 10) = actM lift10Cols m by
    simpa only [hlen] using actM_mod lift10Cols m]

private theorem actM_koMats11 (t m : ℕ) (ht : t < 16) :
    actM (koMats11.getD t []) m = act11 (koArr t) m := by
  rw [koMats11_getD ht]
  have hlen : (matOf 11 (act11 (koArr t))).length = 11 := length_matOf 11 _
  rw [← actM_mod (matOf 11 (act11 (koArr t))) m, hlen,
    actM_matOf (xorLin_act11 (koArr t)) 11 (m % 2 ^ 11) (Nat.mod_lt _ (Nat.two_pow_pos 11))]
  exact act11_mod (koArr t) m

private theorem actM_koMats10 (t m : ℕ) (ht : t < 16) :
    actM (koMats10.getD t []) m = act10 (koArr t) m := by
  rw [koMats10_getD ht]
  have hlen : (matOf 10 (act10 (koArr t))).length = 10 := length_matOf 10 _
  rw [← actM_mod (matOf 10 (act10 (koArr t))) m, hlen,
    actM_matOf (xorLin_act10 (koArr t)) 10 (m % 2 ^ 10) (Nat.mod_lt _ (Nat.two_pow_pos 10))]
  exact act10_mod (koArr t) m

private theorem conj_mem_mog22plus {a b : Fin 24} (hab : a ≠ b) {τ : S24}
    (hτ : τ ∈ M24g) (h0 : τ 0 = a) (h1 : τ 1 = b) {Γ : Subgroup S24}
    (hΓ : Γ ≤ M2ab a b) (x : ↥Γ) : τ⁻¹ * (x : S24) * τ ∈ mog22plus := by
  obtain ⟨hxM, hxcase⟩ := (mem_M2ab_iff a b hab (x : S24)).1 (hΓ x.2)
  refine ⟨?_, ?_⟩
  · exact AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hxM) hτ
  · have hτa : τ⁻¹ a = 0 := by rw [← h0]; simp
    have hτb : τ⁻¹ b = 1 := by rw [← h1]; simp
    rcases hxcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left
      exact ⟨by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0, ha, hτa],
             by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hb, hτb]⟩
    · right
      exact ⟨by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0, ha, hτb],
             by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hb, hτa]⟩

private theorem twistEquiv_rho {Γ : Subgroup S24} (hΓ : Γ ≤ AutPerm) {V : Type*} [CommGroup V]
    {ρ : ↥Γ →* MulAut V} (e : V ≃* W11)
    (he : ∀ (γ : ↥Γ) (v : V), e (ρ γ v) = rho11 Γ hΓ γ (e v))
    (g₀ : ↥AutPerm) (k : ↥Γ) (v : V) :
    twistEquiv e rhoM24 g₀ (ρ k v) =
      rhoM24 (g₀ * ⟨(k : S24), hΓ k.2⟩ * g₀⁻¹) (twistEquiv e rhoM24 g₀ v) := by
  simp only [twistEquiv, MulEquiv.trans_apply]
  rw [he k v, rho11_eq_rhoM24 hΓ k]
  have hcomp : rhoM24 (g₀ * ⟨(k : S24), hΓ k.2⟩ * g₀⁻¹) =
      rhoM24 g₀ * rhoM24 ⟨(k : S24), hΓ k.2⟩ * (rhoM24 g₀)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hcomp, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]

private theorem actsByMats_ne22 (τ : S24) (hτ : τ ∈ M24g) (hτO : τ • octad0 = O)
    (hΓ : Γ ≤ AutPerm) (hfix : octFix O ≤ Γ)
    (e : V ≃* W11) (he : ∀ (γ : ↥Γ) (v : V), e (ρ γ v) = rho11 Γ hΓ γ (e v)) :
    ActsByMats (MaskCoords.ofEquiv (twistEquiv e rhoM24 ⟨τ⁻¹, M24g.inv_mem hτ⟩))
      (rImg ρ (octFix O)) koMats11 := by
  set g₀ : ↥AutPerm := ⟨τ⁻¹, M24g.inv_mem hτ⟩ with hg₀
  set e' : V ≃* W11 := twistEquiv e rhoM24 g₀ with he'
  set c : MaskCoords V 11 := MaskCoords.ofEquiv e' with hc
  have hvme : ∀ m, e' (c.vm m) = toW 11 m := fun m => by
    rw [hc, MaskCoords.ofEquiv_vm, MulEquiv.apply_symm_apply]
  have hmap : octFix O = (octFix octad0).map (MulAut.conj τ).toMonoidHom := by
    rw [← hτO, octFix_smul hτ]
  have hconj : ∀ (k : ↥Γ) (v : V),
      e' (ρ k v) = rhoM24 (g₀ * ⟨(k : S24), hΓ k.2⟩ * g₀⁻¹) (e' v) := by
    intro k v
    rw [he']
    exact twistEquiv_rho hΓ e he g₀ k v
  have hstep : ∀ (k : ↥Γ) (m : ℕ),
      e' (ρ k (c.vm m)) = rhoM24 (g₀ * ⟨(k : S24), hΓ k.2⟩ * g₀⁻¹) (toW 11 m) :=
    fun k m => by rw [hconj k (c.vm m), hvme m]
  have hg₀val : (g₀ : S24) = τ⁻¹ := congrArg Subtype.val hg₀
  refine ⟨?_, ?_⟩
  · rintro g hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
    have hkO : (k : S24) ∈ octFix O := Subgroup.mem_subgroupOf.1 hk
    have hconjfix : τ⁻¹ * (k : S24) * τ ∈ octFix octad0 := by
      rw [hmap] at hkO
      obtain ⟨h, hh, hhh⟩ := Subgroup.mem_map.1 hkO
      have hh' : h = τ⁻¹ * (k : S24) * τ := by
        rw [← hhh]
        change h = τ⁻¹ * ((MulAut.conj τ) h) * τ
        rw [MulAut.conj_apply]
        group
      rwa [hh'] at hh
    rw [octFix_octad0] at hconjfix
    obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 hconjfix
    refine ⟨t, t.2, fun m => ?_⟩
    have hgk : g₀ * ⟨(k : S24), hΓ k.2⟩ * g₀⁻¹ =
        ⟨koPerm t, koPerm_mem_AutPerm_priv t⟩ := by
      apply Subtype.ext
      change (g₀ : S24) * (k : S24) * (g₀ : S24)⁻¹ = koPerm t
      rw [hg₀val, inv_inv]
      exact ht
    apply e'.injective
    rw [hstep k m, hgk, rhoM24_koPerm_toW t m,
      hvme (actM (koMats11.getD t []) m), actM_koMats11 t m t.2]
  · intro t ht
    have ht16 : t < 16 := by rwa [koMats11_length] at ht
    set m0 : S24 := τ * koPerm ⟨t, ht16⟩ * τ⁻¹ with hm0
    have hm0O : m0 ∈ octFix O := by
      rw [hmap]
      refine Subgroup.mem_map.2 ⟨koPerm ⟨t, ht16⟩, ?_, ?_⟩
      · rw [octFix_octad0]
        exact (mem_fixO_iff _).2 ⟨⟨t, ht16⟩, rfl⟩
      · change (MulAut.conj τ) (koPerm ⟨t, ht16⟩) = m0
        simp [MulAut.conj_apply, hm0]
    have hk0 : τ⁻¹ * m0 * τ = koPerm ⟨t, ht16⟩ := by
      rw [hm0]
      group
    have hgk : g₀ * ⟨m0, hΓ (hfix hm0O)⟩ * g₀⁻¹ =
        ⟨koPerm ⟨t, ht16⟩, koPerm_mem_AutPerm_priv ⟨t, ht16⟩⟩ := by
      apply Subtype.ext
      change (g₀ : S24) * m0 * (g₀ : S24)⁻¹ = koPerm ⟨t, ht16⟩
      rw [hg₀val, inv_inv]
      exact hk0
    refine ⟨ρ ⟨m0, hfix hm0O⟩, Subgroup.mem_map.2
      ⟨⟨m0, hfix hm0O⟩, Subgroup.mem_subgroupOf.2 hm0O, rfl⟩, fun m => ?_⟩
    apply e'.injective
    rw [hstep ⟨m0, hfix hm0O⟩ m, hgk, rhoM24_koPerm_toW ⟨t, ht16⟩ m,
      hvme (actM (koMats11.getD t []) m), actM_koMats11 t m ht16]

private theorem actsByMats_eq22 (τ : S24) (hτ : τ ∈ M24g) (hτO : τ • octad0 = O)
    (hΓ : Γ ≤ M2ab a b) (hfix : octFix O ≤ Γ)
    (hmem : ∀ γ : ↥Γ, τ⁻¹ * (γ : S24) * τ ∈ mog22plus)
    (e : V ≃* W10)
    (he : ∀ (γ : ↥Γ) (v : V),
      e (ρ γ v) = rho10 mog22plus le_rfl ⟨τ⁻¹ * (γ : S24) * τ, hmem γ⟩ (e v)) :
    ActsByMats (MaskCoords.ofEquiv e) (rImg ρ (octFix O)) koMats10 := by
  set c : MaskCoords V 10 := MaskCoords.ofEquiv e with hc
  have hvme : ∀ m, e (c.vm m) = toW 10 m := fun m => by
    rw [hc, MaskCoords.ofEquiv_vm, MulEquiv.apply_symm_apply]
  have hmap : octFix O = (octFix octad0).map (MulAut.conj τ).toMonoidHom := by
    rw [← hτO, octFix_smul hτ]
  have hconjfix : ∀ k : ↥Γ, (k : S24) ∈ octFix O → τ⁻¹ * (k : S24) * τ ∈ octFix octad0 := by
    intro k hkO
    rw [hmap] at hkO
    obtain ⟨h, hh, hhh⟩ := Subgroup.mem_map.1 hkO
    have hh' : h = τ⁻¹ * (k : S24) * τ := by
      rw [← hhh]
      change h = τ⁻¹ * ((MulAut.conj τ) h) * τ
      rw [MulAut.conj_apply]
      group
    rwa [hh'] at hh
  refine ⟨?_, ?_⟩
  · rintro g hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
    have hkO : (k : S24) ∈ octFix O := Subgroup.mem_subgroupOf.1 hk
    rw [octFix_octad0] at hconjfix
    obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (hconjfix k hkO)
    refine ⟨t, t.2, fun m => ?_⟩
    have hsub : (⟨τ⁻¹ * (k : S24) * τ, hmem k⟩ : ↥mog22plus) =
        ⟨koPerm t, koPerm_mem_mog22plus_priv t⟩ := Subtype.ext ht
    apply e.injective
    rw [he k (c.vm m), hvme m, hsub, rho10_koPerm_toW t m,
      hvme (actM (koMats10.getD t []) m), actM_koMats10 t m t.2]
  · intro t ht
    have ht16 : t < 16 := by rwa [koMats10_length] at ht
    set m0 : S24 := τ * koPerm ⟨t, ht16⟩ * τ⁻¹ with hm0
    have hm0O : m0 ∈ octFix O := by
      rw [hmap]
      refine Subgroup.mem_map.2 ⟨koPerm ⟨t, ht16⟩, ?_, ?_⟩
      · rw [octFix_octad0]
        exact (mem_fixO_iff _).2 ⟨⟨t, ht16⟩, rfl⟩
      · change (MulAut.conj τ) (koPerm ⟨t, ht16⟩) = m0
        simp [MulAut.conj_apply, hm0]
    have hk0 : τ⁻¹ * m0 * τ = koPerm ⟨t, ht16⟩ := by
      rw [hm0]
      group
    have hsub : (⟨τ⁻¹ * m0 * τ, hmem ⟨m0, hfix hm0O⟩⟩ : ↥mog22plus) =
        ⟨koPerm ⟨t, ht16⟩, koPerm_mem_mog22plus_priv ⟨t, ht16⟩⟩ :=
      Subtype.ext hk0
    refine ⟨ρ ⟨m0, hfix hm0O⟩, Subgroup.mem_map.2
      ⟨⟨m0, hfix hm0O⟩, Subgroup.mem_subgroupOf.2 hm0O, rfl⟩, fun m => ?_⟩
    apply e.injective
    rw [he ⟨m0, hfix hm0O⟩ (c.vm m), hvme m, hsub, rho10_koPerm_toW ⟨t, ht16⟩ m,
      hvme (actM (koMats10.getD t []) m), actM_koMats10 t m ht16]

theorem mctx_rho_injective (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  by_cases hd : d = 22
  · rcases mctx_cases hM with ⟨h24, _⟩ | ⟨h23, _⟩ | ⟨_, _, h2⟩
    · exact absurd (h24.symm.trans hd) (by norm_num)
    · exact absurd (h23.symm.trans hd) (by norm_num)
    · obtain ⟨τ, hτ, hτO, h0, h1⟩ :=
        exists_flag_pair hM.cfg.octad hM.cfg.a_O hM.cfg.b_O hM.cfg.ne
      have hmem := conj_mem_mog22plus hM.cfg.ne hτ h0 h1 h2
      have hreal : IsMathModule false 22 a b Γ ρ := by rw [← hd]; exact ⟨β, hM.real⟩
      obtain ⟨e, he0⟩ := CFSG.Quasithin.AppendixH.H14.exists_equiv_cocode22 hM.cfg.ne hτ h0 h1 h2 hreal
      have he : ∀ (x : ↥Γ) (v : V), e (ρ x v) = rho10 mog22plus le_rfl
          ⟨τ⁻¹ * (x : S24) * τ, hmem x⟩ (e v) := fun x v => he0 x v (hmem x)
      have hrho : rho10 mog22plus le_rfl ⟨τ⁻¹ * (γ : S24) * τ, hmem γ⟩ = 1 := by
        ext v
        obtain ⟨u, rfl⟩ := e.surjective v
        rw [MulAut.one_apply, ← he γ u, hγ, MulAut.one_apply]
      have hx1 : (⟨τ⁻¹ * (γ : S24) * τ, hmem γ⟩ : ↥mog22plus) = 1 :=
        rho10_mog22plus_injective
          (hrho.trans (map_one (rho10 mog22plus le_rfl)).symm)
      have hconj : τ⁻¹ * (γ : S24) * τ = 1 := congrArg Subtype.val hx1
      apply Subtype.ext
      calc (γ : S24) = τ * (τ⁻¹ * (γ : S24) * τ) * τ⁻¹ := by group
        _ = 1 := by rw [hconj]; simp
  · have hΓ : Γ ≤ AutPerm := mctx_le_M24 hM
    obtain ⟨e, he⟩ := CFSG.Quasithin.AppendixH.H14.exists_equiv_cocode hd hΓ ⟨β, hM.real⟩
    have hrho : rho11 Γ hΓ γ = 1 := by
      ext v
      obtain ⟨u, rfl⟩ := e.surjective v
      rw [MulAut.one_apply, ← he γ u, hγ, MulAut.one_apply]
    exact rho11_injective Γ hΓ (hrho.trans (map_one (rho11 Γ hΓ)).symm)

theorem exists_kFrame (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    ∃ (D : KData) (c : MaskCoords V D.n), D.good = true ∧ D.n = (if d = 22 then 10 else 11) ∧
      D.dU = (if d = 22 then 5 else 6) ∧ ActsByMats c (rImg ρ (octFix O)) D.cols := by
  by_cases hd : d = 22
  · rcases mctx_cases hM with ⟨h24, _⟩ | ⟨h23, _⟩ | ⟨_, _, h2⟩
    · exact absurd (h24.symm.trans hd) (by norm_num)
    · exact absurd (h23.symm.trans hd) (by norm_num)
    · obtain ⟨τ, hτ, hτO, h0, h1⟩ :=
        exists_flag_pair hM.cfg.octad hM.cfg.a_O hM.cfg.b_O hM.cfg.ne
      have hmem := conj_mem_mog22plus hM.cfg.ne hτ h0 h1 h2
      have hreal : IsMathModule false 22 a b Γ ρ := by rw [← hd]; exact ⟨β, hM.real⟩
      obtain ⟨e, he0⟩ := CFSG.Quasithin.AppendixH.H14.exists_equiv_cocode22 hM.cfg.ne hτ h0 h1 h2 hreal
      exact ⟨D10, MaskCoords.ofEquiv e, D10_good, by rw [if_pos hd]; rfl, by rw [if_pos hd]; rfl,
        actsByMats_eq22 τ hτ hτO h2 (mctx_octFix_le hM) hmem e
          (fun x v => he0 x v (hmem x))⟩
  · have hΓ : Γ ≤ AutPerm := mctx_le_M24 hM
    obtain ⟨e, he⟩ := CFSG.Quasithin.AppendixH.H14.exists_equiv_cocode hd hΓ ⟨β, hM.real⟩
    obtain ⟨τ, hτ, hτO⟩ := exists_smul_octad_eq isOctad_octad0 hM.cfg.octad
    exact ⟨D11, _, D11_good, by rw [if_neg hd]; rfl, by rw [if_neg hd]; rfl,
      actsByMats_ne22 τ hτ hτO hΓ (mctx_octFix_le hM) e he⟩

end CFSG.ASVolI.AppH
