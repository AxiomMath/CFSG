module

public import CFSG.Quasithin.Background.B1MoreTwelveB
public import CFSG.Quasithin.Background.B19Basic

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple

namespace B1Red

variable {W : Type*} [CommGroup W]

@[expose] def blockOf (J F : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  Subgroup.closure {t | t ∈ transvectionsIn J ∧ ∃ f ∈ F, t * f ≠ f * t}

theorem blockOf_map_conj {J F : Subgroup (MulAut W)} {x : MulAut W}
    (hx : ∀ j ∈ J, x * j * x⁻¹ ∈ J) (hx' : ∀ j ∈ J, x⁻¹ * j * x ∈ J) :
    blockOf J (F.map (MulAut.conj x).toMonoidHom) =
      (blockOf J F).map (MulAut.conj x).toMonoidHom := by
  unfold blockOf
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨⟨hyJ, hyt⟩, _, ⟨f, hfF, rfl⟩, hnc⟩
    refine ⟨x⁻¹ * y * x, ⟨⟨hx' y hyJ, ?_⟩, f, hfF, ?_⟩, by group⟩
    · simpa using B1.isTransvection_conj hyt x⁻¹
    · intro h
      apply hnc
      calc y * (x * f * x⁻¹) = x * ((x⁻¹ * y * x) * f) * x⁻¹ := by group
        _ = x * (f * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
        _ = (x * f * x⁻¹) * y := by group
  · rintro ⟨t, ⟨⟨htJ, htt⟩, f, hfF, hnc⟩, rfl⟩
    refine ⟨⟨hx t htJ, B1.isTransvection_conj htt x⟩, x * f * x⁻¹, ⟨f, hfF, rfl⟩, ?_⟩
    intro h
    apply hnc
    have h' : x * (t * f) * x⁻¹ = x * (f * t) * x⁻¹ := by
      calc x * (t * f) * x⁻¹ = (x * t * x⁻¹) * (x * f * x⁻¹) := by group
        _ = (x * f * x⁻¹) * (x * t * x⁻¹) := h
        _ = x * (f * t) * x⁻¹ := by group
    have := mul_left_cancel (mul_right_cancel h')
    exact this

end B1Red

namespace IsTransvectionBlocks

open CFSG.Quasithin.B1Red

section Blocks

variable {W : Type*} [CommGroup W] {J : Subgroup (MulAut W)}
  {𝓗 : Finset (Subgroup (MulAut W))}

theorem not_oddCoreOfSub_le_biSup (hb : IsTransvectionBlocks J 𝓗) {G : Subgroup (MulAut W)}
    (hG : G ∈ 𝓗) : ¬ oddCoreOfSub G ≤ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ G), H' := by
  intro hle
  have hbot : oddCoreOfSub G ≤ ⊥ := by
    rw [← hb.inf_biSup_ne_eq_bot hG]
    exact le_inf (oddCoreOfSub_le G) hle
  have := hb.card_oddCoreOfSub_of_mem hG
  rw [le_bot_iff.1 hbot, Subgroup.card_bot] at this
  omega

theorem oddCoreOfSub_injOn (hb : IsTransvectionBlocks J 𝓗) {G G' : Subgroup (MulAut W)}
    (hG : G ∈ 𝓗) (hG' : G' ∈ 𝓗) (h : oddCoreOfSub G = oddCoreOfSub G') : G = G' := by
  by_contra hne
  apply hb.not_oddCoreOfSub_le_biSup hG
  rw [h]
  refine (oddCoreOfSub_le G').trans ?_
  exact le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut W)) (_ : H' ∈ 𝓗) =>
    ⨆ (_ : H' ≠ G), H') G' hG' (le_iSup (fun _ : G' ≠ G => G') (Ne.symm hne))

theorem exists_eq_of_oddCoreOfSub_le_iSup (hb : IsTransvectionBlocks J 𝓗)
    {G : Subgroup (MulAut W)} (hG : G ∈ 𝓗) {ι : Type*} (Gi : ι → Subgroup (MulAut W))
    (hGi : ∀ i, Gi i ∈ 𝓗) (hle : oddCoreOfSub G ≤ ⨆ i, oddCoreOfSub (Gi i)) :
    ∃ i, Gi i = G := by
  by_contra hcon
  push Not at hcon
  apply hb.not_oddCoreOfSub_le_biSup hG
  refine hle.trans (iSup_le fun i => (oddCoreOfSub_le _).trans ?_)
  exact le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut W)) (_ : H' ∈ 𝓗) =>
    ⨆ (_ : H' ≠ G), H') (Gi i) (hGi i) (le_iSup (fun _ : Gi i ≠ G => Gi i) (hcon i))

variable [Finite W]

theorem blockOf_oddCoreOfSub (hV : ∀ v : W, v ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    {G : Subgroup (MulAut W)} (hG : G ∈ 𝓗) : blockOf J (oddCoreOfSub G) = G := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro t ⟨htJ, f, hf, hnc⟩
    obtain ⟨G', hG', htG'⟩ := hb.cover t htJ
    by_cases hGG : G' = G
    · exact hGG ▸ htG'
    · exact absurd (hb.comm G' hG' G hG hGG t htG' f (oddCoreOfSub_le G hf)) hnc
  · refine le_trans (le_of_eq (hb.closure_eq G hG).symm) (Subgroup.closure_mono fun t htG => ?_)
    refine ⟨⟨hb.le_J hG htG.1, htG.2⟩, ?_⟩
    have hne : oddCoreOfSub G ≠ ⊥ := by
      intro h
      have := hb.card_oddCoreOfSub_of_mem hG
      rw [h, Subgroup.card_bot] at this
      omega
    obtain ⟨f, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    exact ⟨f, f.2, hb.not_commute_of_mem_oddCoreOfSub hV hG htG f.2
      (fun h => hf1 (Subtype.ext h))⟩

theorem eq_oddCoreOfSub_of_inverted (hb : IsTransvectionBlocks J 𝓗)
    {G₀ : Subgroup (MulAut W)} (hG₀ : G₀ ∈ 𝓗) {Kp : Subgroup (MulAut W)}
    (hKp3 : Nat.card ↥Kp = 3) (hKpJ : Kp ≤ J) {s : MulAut W} (hsG : s ∈ G₀)
    (hnorm : ∀ k ∈ Kp, s * k * s⁻¹ ∈ Kp) (hnc : ∃ k ∈ Kp, s * k ≠ k * s) :
    Kp = oddCoreOfSub G₀ := by
  classical
  have : Finite ↥Kp := Nat.finite_of_card_ne_zero (by rw [hKp3]; norm_num)
  obtain ⟨k, hkK, hsk⟩ := hnc
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hsk (by simp)
  have hk3 : k ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥Kp) (x := ⟨k, hkK⟩)
    rw [hKp3] at h
    exact congrArg Subtype.val h
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  have hKpz : Subgroup.zpowers k = Kp :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hkK) (by rw [Nat.card_zpowers, hord, hKp3])
  set R : Subgroup (MulAut W) := ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ G₀), H' with hRdef
  have hJeq : J = G₀ ⊔ R := by
    rw [← hb.iSup_eq]
    apply le_antisymm
    · refine iSup₂_le fun H hH => ?_
      by_cases hHG : H = G₀
      · rw [hHG]
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut W))
          (_ : H' ∈ 𝓗) => ⨆ (_ : H' ≠ G₀), H') H hH (le_iSup (fun _ : H ≠ G₀ => H) hHG))
    · exact sup_le (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut W)) (_ : K ∈ 𝓗) => K) G₀ hG₀
          le_rfl)
        (iSup₂_le fun H hH => iSup_le fun _ => le_iSup₂_of_le
          (f := fun (K : Subgroup (MulAut W)) (_ : K ∈ 𝓗) => K) H hH le_rfl)
  have hRcent : ∀ r ∈ R, ∀ g ∈ G₀, g * r = r * g := by
    have hle : R ≤ Subgroup.centralizer (G₀ : Set (MulAut W)) := by
      refine iSup₂_le fun H hH => iSup_le fun hne => fun b hb' => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hb.comm G₀ hG₀ H hH (Ne.symm hne) g hg b hb'
    intro r hr g hg
    exact Subgroup.mem_centralizer_iff.1 (hle hr) g hg
  have hGR : G₀ ⊓ R = ⊥ := hb.inf_biSup_ne_eq_bot hG₀
  have hRn : R ≤ Subgroup.normalizer (G₀ : Set (MulAut W)) :=
    le_normalizer_of_conj fun r hr g hg => by
      rw [(hRcent r hr g hg).symm]
      simpa using hg
  have hkJ : k ∈ G₀ ⊔ R := by
    rw [← hJeq]
    exact hKpJ hkK
  obtain ⟨g, hg, r, hr, hkgr⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hRn).1 hkJ
  have hgr : g * r = r * g := hRcent r hr g hg
  have hcube : g ^ 3 * r ^ 3 = 1 := by
    have : (g * r) ^ 3 = g ^ 3 * r ^ 3 := Commute.mul_pow (show Commute g r from hgr) 3
    rw [← this, ← hkgr, hk3]
  have hr3 : r ^ 3 = 1 := by
    have h1 : r ^ 3 = (g ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hcube
    have h2 : r ^ 3 ∈ G₀ ⊓ R := ⟨h1 ▸ G₀.inv_mem (G₀.pow_mem hg 3), R.pow_mem hr 3⟩
    rwa [hGR, Subgroup.mem_bot] at h2
  have hsr : s * r = r * s := hRcent r hr s hsG
  have hrs' : r * s⁻¹ = s⁻¹ * r := by
    calc r * s⁻¹ = s⁻¹ * (s * r) * s⁻¹ := by group
      _ = s⁻¹ * (r * s) * s⁻¹ := by rw [hsr]
      _ = s⁻¹ * r := by group
  have hnk : s * k * s⁻¹ ∈ Subgroup.zpowers k := by
    rw [hKpz]
    exact hnorm k hkK
  have hsk' : s * k * s⁻¹ = k⁻¹ := by
    rcases B19.eq_of_mem_zpowers_three hk3 hnk with h1 | h2 | h3
    · exfalso
      apply hk1
      have : k = s⁻¹ * (s * k * s⁻¹) * s := by group
      rw [this, h1]
      group
    · exfalso
      apply hsk
      have : s * k = (s * k * s⁻¹) * s := by group
      rw [this, h2]
    · exact h3
  have hkdecomp : s * k * s⁻¹ = (s * g * s⁻¹) * r := by
    rw [hkgr]
    calc s * (g * r) * s⁻¹ = (s * g) * (r * s⁻¹) := by group
      _ = (s * g) * (s⁻¹ * r) := by rw [hrs']
      _ = (s * g * s⁻¹) * r := by group
  have hrinv : r⁻¹ * g⁻¹ = g⁻¹ * r⁻¹ := by
    calc r⁻¹ * g⁻¹ = (g * r)⁻¹ := by group
      _ = (r * g)⁻¹ := by rw [hgr]
      _ = g⁻¹ * r⁻¹ := by group
  have hsgs : s * g * s⁻¹ = g⁻¹ * (r⁻¹ * r⁻¹) := by
    have h1 : s * g * s⁻¹ * r = (g * r)⁻¹ := by
      rw [← hkdecomp, ← hkgr]
      exact hsk'
    calc s * g * s⁻¹ = (s * g * s⁻¹ * r) * r⁻¹ := by group
      _ = (g * r)⁻¹ * r⁻¹ := by rw [h1]
      _ = r⁻¹ * g⁻¹ * r⁻¹ := by group
      _ = g⁻¹ * r⁻¹ * r⁻¹ := by rw [hrinv]
      _ = g⁻¹ * (r⁻¹ * r⁻¹) := by group
  have hr2 : r⁻¹ * r⁻¹ ∈ G₀ ⊓ R := by
    refine ⟨?_, R.mul_mem (R.inv_mem hr) (R.inv_mem hr)⟩
    have : r⁻¹ * r⁻¹ = g * (s * g * s⁻¹) := by rw [hsgs]; group
    rw [this]
    exact G₀.mul_mem hg (G₀.mul_mem (G₀.mul_mem hsG hg) (G₀.inv_mem hsG))
  rw [hGR, Subgroup.mem_bot] at hr2
  have hr1 : r = 1 := by
    have hr22 : r ^ 2 = 1 := by
      calc r ^ 2 = (r⁻¹ * r⁻¹)⁻¹ := by group
        _ = 1 := by rw [hr2, inv_one]
    calc r = r ^ 3 * (r ^ 2)⁻¹ := by group
      _ = 1 := by rw [hr3, hr22]; group
  have hkg : k = g := by rw [hkgr, hr1, mul_one]
  have hkO : k ∈ oddCoreOfSub G₀ :=
    (hb.mem_oddCoreOfSub_iff_of_mem hG₀).2 ⟨hkg ▸ hg, hk3⟩
  have hle : Kp ≤ oddCoreOfSub G₀ := by
    rw [← hKpz]
    exact Subgroup.zpowers_le.2 hkO
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hb.card_oddCoreOfSub_of_mem hG₀, hKp3])

end Blocks

end IsTransvectionBlocks

end CFSG.Quasithin
