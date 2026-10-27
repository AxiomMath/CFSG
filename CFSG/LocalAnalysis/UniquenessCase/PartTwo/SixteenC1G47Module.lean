module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Split

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private lemma s16c1_G47_mul_u_eq {Hs : Type*} [Group Hs] {u : Hs} (hu2 : u * u = 1) (s : Hs) :
    s * u = u * (u * s * u⁻¹ * s) * s⁻¹ := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  calc s * u = s * u⁻¹ := by rw [hu]
    _ = (u * u) * (s * u⁻¹) := by rw [hu2, one_mul]
    _ = u * (u * s * u⁻¹ * s) * s⁻¹ := by group

private lemma s16c1_G47_conj_mul_mul {Hs : Type*} [Group Hs] {u : Hs} (hu2 : u * u = 1)
    (s : Hs) : (s * u * s⁻¹) * u * (u * s * u⁻¹ * s) = s * s := by
  calc (s * u * s⁻¹) * u * (u * s * u⁻¹ * s)
      = s * u * s⁻¹ * (u * u) * s * u⁻¹ * s := by group
    _ = s * u * s⁻¹ * 1 * s * u⁻¹ * s := by rw [hu2]
    _ = s * s := by group

private lemma s16c1_G47_mem_of_sq_mem {Hs : Type*} [Group Hs] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {S : Subgroup Hs} (hS : IsPGroup q S) {T : Subgroup Hs} {s : Hs} (hs : s ∈ S)
    (hsq : s * s ∈ T) : s ∈ T := by
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hk' : s ^ (q ^ k) = 1 := by
    have h := congrArg (fun x : S => (x : Hs)) hk
    simpa using h
  have hoddq : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  obtain ⟨m, hm⟩ := Odd.pow (n := k) hoddq
  have hpow : (s * s) ^ m * s = 1 := by
    have h2 : s ^ (q ^ k) = s ^ (2 * m + 1) := by rw [hm]
    rw [h2, pow_add, pow_mul, pow_one] at hk'
    simpa [pow_two] using hk'
  have hs_eq : s = ((s * s) ^ m)⁻¹ := (inv_eq_of_mul_eq_one_right hpow).symm
  rw [hs_eq]
  exact T.inv_mem (T.pow_mem hsq m)

private lemma s16c1_G47_mem_Z_of_conj_eq {Hs : Type*} [Group Hs] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {S Z : Subgroup Hs} (hS : IsPGroup q S) {u s : Hs} (hs : s ∈ S)
    (hSZ : u * s * u⁻¹ * s ∈ Z) (hconj : s * u * s⁻¹ = u) : s ∈ Z := by
  have hsu : s * u = u * s := by
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [hconj]
  have hc : u * s * u⁻¹ * s = s * s := by
    rw [← hsu]
    group
  exact s16c1_G47_mem_of_sq_mem hq hq2 hS hs (by rw [← hc]; exact hSZ)

theorem s16c1_G47_module {Hs F : Type} [Group Hs] [Finite Hs] [Group F] [Finite F] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {S Z : Subgroup Hs} (hS : IsPGroup q S) (hZS : Z ≤ S) {u : Hs}
    (hu2 : u * u = 1) (hSu : ∀ s ∈ S, u * s * u⁻¹ ∈ S)
    (hSZ : ∀ s ∈ S, u * s * u⁻¹ * s ∈ Z) (hZc : ∀ c ∈ Z, ∀ s ∈ S, c * s = s * c)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Z)
    (hnc : ¬ ∃ s ∈ S, S ≤ Z ⊔ Subgroup.zpowers s) (hF : ∀ e : F, e * e = 1)
    (ρ : Hs →* MulAut F) (hD : ∃ e : F, ρ u e * e ≠ 1)
    (hTI : ∀ r : Hs, r * u * r⁻¹ ≠ u → ∀ e e' : F, ρ r (ρ u e * e) = ρ u e' * e' →
      ρ u e * e = 1)
    (hZD : ∀ c ∈ Z, ∀ e : F, ρ c (ρ u e * e) = ρ u e * e) : False := by
  obtain ⟨e₀, he₀⟩ := hD
  set F₁ : Subgroup F :=
    Subgroup.closure {f : F | ∃ y ∈ S, ∃ e : F, f = ρ y (ρ u e * e)} with hF₁def
  have hstable : ∀ s ∈ S, ∀ f ∈ F₁, ρ s f ∈ F₁ := by
    intro s hs f hf
    have hgen : {f : F | ∃ y ∈ S, ∃ e : F, f = ρ y (ρ u e * e)} ⊆
        F₁.comap (ρ s).toMonoidHom := by
      rintro f ⟨y, hy, e, rfl⟩
      exact Subgroup.mem_comap.mpr (by
        show ρ s (ρ y (ρ u e * e)) ∈ F₁
        have h1 : ρ s (ρ y (ρ u e * e)) = ρ (s * y) (ρ u e * e) :=
          (congrArg (fun g : MulAut F => g (ρ u e * e)) (map_mul ρ s y)).symm
        rw [h1]
        exact Subgroup.subset_closure ⟨s * y, S.mul_mem hs hy, e, rfl⟩)
    have hle : F₁ ≤ F₁.comap (ρ s).toMonoidHom := by
      rw [hF₁def]
      exact (Subgroup.closure_le (F₁.comap (ρ s).toMonoidHom)).mpr hgen
    exact Subgroup.mem_comap.mp (hle hf)
  have hZtriv : ∀ c ∈ Z, ∀ f ∈ F₁, ρ c f = f := by
    intro c hc f hf
    have hgen : {f : F | ∃ y ∈ S, ∃ e : F, f = ρ y (ρ u e * e)} ⊆
        (MonoidHom.eqLocus (ρ c).toMonoidHom (MonoidHom.id F) : Subgroup F) := by
      rintro f ⟨y, hy, e, rfl⟩
      change ρ c (ρ y (ρ u e * e)) = ρ y (ρ u e * e)
      calc ρ c (ρ y (ρ u e * e)) = (ρ c * ρ y) (ρ u e * e) := rfl
        _ = ρ (c * y) (ρ u e * e) := by rw [map_mul ρ c y]
        _ = ρ (y * c) (ρ u e * e) := by rw [hZc c hc y hy]
        _ = (ρ y * ρ c) (ρ u e * e) := by rw [map_mul ρ y c]
        _ = ρ y (ρ c (ρ u e * e)) := rfl
        _ = ρ y (ρ u e * e) := by rw [hZD c hc e]
    have hle : F₁ ≤ (MonoidHom.eqLocus (ρ c).toMonoidHom (MonoidHom.id F) : Subgroup F) := by
      rw [hF₁def]
      exact (Subgroup.closure_le
        (MonoidHom.eqLocus (ρ c).toMonoidHom (MonoidHom.id F) : Subgroup F)).mpr hgen
    have hcf : f ∈ (MonoidHom.eqLocus (ρ c).toMonoidHom (MonoidHom.id F) : Subgroup F) := hle hf
    change ρ c f = f at hcf
    exact hcf
  have hmem_gen : ∀ e : F, ρ u e * e ∈ F₁ := by
    intro e
    rw [hF₁def]
    exact Subgroup.subset_closure ⟨1, S.one_mem, e, by rw [map_one, MulAut.one_apply]⟩
  have hker : ∀ s ∈ S, (∀ f ∈ F₁, ρ s f = f) → s ∈ Z := by
    intro s hs hfix
    by_contra hsZ
    have hne : s * u * s⁻¹ ≠ u := fun hconj =>
      hsZ (s16c1_G47_mem_Z_of_conj_eq hq hq2 hS hs (hSZ s hs) hconj)
    exact he₀ (hTI s hne e₀ e₀ (hfix (ρ u e₀ * e₀) (hmem_gen e₀)))
  have hu_triv : ∀ f ∈ F₁, ρ u f = f := by
    have hsplit := s16c1_G47_split hq hq2 hS hZS hcomm hnc hF ρ F₁ hstable hZtriv hker
    have hGle : Subgroup.closure {f : F | f ∈ F₁ ∧ ∃ s ∈ S, s ∉ Z ∧ ρ s f = f} ≤
        (MonoidHom.eqLocus (ρ u).toMonoidHom (MonoidHom.id F) : Subgroup F) := by
      rw [Subgroup.closure_le]
      rintro f ⟨hfF₁, s, hs, hsZ, hfixs⟩
      change ρ u f = f
      set c : Hs := u * s * u⁻¹ * s with hc_def
      have hcZ : c ∈ Z := by rw [hc_def]; exact hSZ s hs
      have hmul : s * u = u * c * s⁻¹ := by rw [hc_def]; exact s16c1_G47_mul_u_eq hu2 s
      have hne : s * u * s⁻¹ ≠ u := fun hconj =>
        hsZ (s16c1_G47_mem_Z_of_conj_eq hq hq2 hS hs (by rw [← hc_def]; exact hcZ) hconj)
      have hsinv : ρ s⁻¹ f = f := by
        have h2 : ρ s⁻¹ (ρ s f) = ρ s⁻¹ f := by rw [hfixs]
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h2
        exact h2.symm
      have hcf : ρ c (ρ s⁻¹ f) = ρ s⁻¹ f :=
        hZtriv c hcZ (ρ s⁻¹ f) (hstable s⁻¹ (S.inv_mem hs) f hfF₁)
      have hsu_fix : ρ s (ρ u f) = ρ u f := by
        calc ρ s (ρ u f) = ρ (s * u) f := by rw [← MulAut.mul_apply, ← map_mul]
          _ = ρ (u * c * s⁻¹) f := by rw [hmul]
          _ = ρ u (ρ c (ρ s⁻¹ f)) := by
                rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
          _ = ρ u (ρ s⁻¹ f) := by rw [hcf]
          _ = ρ u f := by rw [hsinv]
      have hfixδ : ρ s (ρ u f * f) = ρ u f * f := by rw [map_mul, hsu_fix, hfixs]
      have hδ : ρ u f * f = 1 := hTI s hne f f hfixδ
      have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hF f)
      calc ρ u f = f⁻¹ := mul_eq_one_iff_eq_inv.mp hδ
        _ = f := hfinv
    have hle : F₁ ≤ (MonoidHom.eqLocus (ρ u).toMonoidHom (MonoidHom.id F) : Subgroup F) := by
      rw [← hsplit]
      exact hGle
    intro f hf
    have hmem : f ∈ (MonoidHom.eqLocus (ρ u).toMonoidHom (MonoidHom.id F) : Subgroup F) := hle hf
    change ρ u f = f at hmem
    exact hmem
  let K : Subgroup Hs :=
    { carrier := {t : Hs | ∀ f ∈ F₁, ρ t f = f}
      one_mem' := by intro f _; rw [map_one, MulAut.one_apply]
      mul_mem' := by
        intro a b ha hb f hf
        rw [map_mul, MulAut.mul_apply, hb f hf, ha f hf]
      inv_mem' := by
        intro a ha f hf
        have h2 : ρ a⁻¹ (ρ a f) = f := by
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
        rw [ha f hf] at h2
        exact h2 }
  have hS_triv : ∀ s ∈ S, s ∈ K := by
    intro s hs
    set c : Hs := u * s * u⁻¹ * s with hc_def
    have hcZ : c ∈ Z := by rw [hc_def]; exact hSZ s hs
    have htK : s * u * s⁻¹ ∈ K := by
      intro f hf
      have hsf : ρ s⁻¹ f ∈ F₁ := hstable s⁻¹ (S.inv_mem hs) f hf
      have huf : ρ u (ρ s⁻¹ f) = ρ s⁻¹ f := hu_triv (ρ s⁻¹ f) hsf
      calc ρ (s * u * s⁻¹) f = ρ s (ρ u (ρ s⁻¹ f)) := by
              rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
        _ = ρ s (ρ s⁻¹ f) := by rw [huf]
        _ = f := by
              rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have huK : u ∈ K := hu_triv
    have hcK : c ∈ K := hZtriv c hcZ
    have hsqK : s * s ∈ K := by
      have hprod : (s * u * s⁻¹) * u * c = s * s := by
        rw [hc_def]
        exact s16c1_G47_conj_mul_mul hu2 s
      rw [← hprod]
      exact K.mul_mem (K.mul_mem htK huK) hcK
    exact s16c1_G47_mem_of_sq_mem hq hq2 hS hs hsqK
  have hSZ_le : S ≤ Z := fun s hs => hker s hs (hS_triv s hs)
  exact hnc ⟨1, S.one_mem, by rw [Subgroup.zpowers_one_eq_bot, sup_bot_eq]; exact hSZ_le⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
