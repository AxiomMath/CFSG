module

public import CFSG.Quasithin.EmptyFaithful.S1421QA13aCount
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.QA13a

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four CFSG.PSL3Four.Native

theorem two_pow_le_eight {k c : ℕ} (hdvd : 2 ^ k ∣ c) (hc : c = 168 ∨ c = 60 ∨ c = 72) :
    2 ^ k ≤ 8 := by
  by_contra hlt
  have hk : 4 ≤ k := by
    by_contra hk
    have : k ≤ 3 := by omega
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h16 : 16 ∣ c := (pow_dvd_pow 2 hk).trans hdvd
  omega

theorem card_le_eight {Γ : Type*} [Group Γ] [Finite Γ] {C F : Subgroup Γ} {c : ℕ}
    (hC : Nat.card C = c)
    (hc : c = 168 ∨ c = 60 ∨ c = 72) (hF : F ≤ C) (h2 : IsPGroup 2 F) : Nat.card F ≤ 8 := by
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hdvd : Nat.card F ∣ c := hC ▸ Subgroup.card_dvd_of_le hF
  rw [hk] at hdvd ⊢
  exact two_pow_le_eight hdvd hc

theorem two_pow_le_four {k : ℕ} (hdvd : 2 ^ k ∣ 60) : 2 ^ k ≤ 4 := by
  by_contra hlt
  have hk : 3 ≤ k := by
    by_contra hk
    have : k ≤ 2 := by omega
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h8 : 8 ∣ 60 := (pow_dvd_pow 2 hk).trans hdvd
  omega

theorem card_eq_eight {Γ : Type*} [Group Γ] [Finite Γ] {F : Subgroup Γ} (h2 : IsPGroup 2 F)
    (h8 : Nat.card F ≤ 8) (h4 : ¬ Nat.card F ≤ 4) : Nat.card F = 8 := by
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  rw [hk] at h8 h4 ⊢
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp_all

theorem index_centralizer_C₂ (x : ↥C₂) :
    (Subgroup.centralizer ({x} : Set ↥C₂)).index = 1 ∨
      (Subgroup.centralizer ({x} : Set ↥C₂)).index = 21 ∨
      (Subgroup.centralizer ({x} : Set ↥C₂)).index = 42 ∨
      (Subgroup.centralizer ({x} : Set ↥C₂)).index = 56 ∨
      (Subgroup.centralizer ({x} : Set ↥C₂)).index = 24 := by
  obtain ⟨e, he, -⟩ := classes_C₂
  obtain ⟨i, hi⟩ := e.surjective (ConjClasses.mk x)
  have hset : (ConjClasses.mk x).carrier = conjugatesOf x := rfl
  have hidx : (Subgroup.centralizer ({x} : Set ↥C₂)).index = Nat.card (e i).carrier := by
    rw [Subgroup.index_centralizer_eq_ncard, ← hset, ← hi, ← Nat.card_coe_set_eq]
  rw [hidx, he i]
  fin_cases i <;> simp

theorem bound_C₂ {F : Subgroup (Equiv.Perm (Fin 42))} (hF : F ≤ C₂)
    (h2 : IsPGroup 2 F) :
    Nat.card F ≤ 8 ∧ ((∀ a ∈ F, ∀ b ∈ F, a * b = b * a) → Nat.card F ≤ 4) := by
  have h8 : Nat.card F ≤ 8 := card_le_eight card_C₂ (Or.inl rfl) hF h2
  refine ⟨h8, fun hab => ?_⟩
  by_contra hgt
  have hF8 : Nat.card F = 8 := card_eq_eight h2 h8 hgt
  have hE : Nat.card (F.subgroupOf C₂) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv]
    exact hF8
  have : IsSimpleGroup ↥C₂ := isSimpleGroup_C₂
  refine no_abelian_eight_simple168 (D := ↥C₂) card_C₂ index_centralizer_C₂ (F.subgroupOf C₂) hE ?_
  intro a ha b hb
  exact Subtype.ext (hab a ha b hb)

theorem bound_C₃ {F : Subgroup (Equiv.Perm (Fin 42))} (hF : F ≤ C₃)
    (h2 : IsPGroup 2 F) : Nat.card F ≤ 4 := by
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hdvd : Nat.card F ∣ 60 := card_C₃ ▸ Subgroup.card_dvd_of_le hF
  rw [hk] at hdvd ⊢
  exact two_pow_le_four hdvd

theorem bound_C₄ {F : Subgroup (Equiv.Perm (Fin 42))} (hF : F ≤ C₄)
    (h2 : IsPGroup 2 F) :
    Nat.card F ≤ 8 ∧ ((∀ a ∈ F, ∀ b ∈ F, a * b = b * a) → Nat.card F ≤ 4) := by
  have h8 : Nat.card F ≤ 8 := card_le_eight card_C₄ (Or.inr (Or.inr rfl)) hF h2
  refine ⟨h8, fun hab => ?_⟩
  by_contra hgt
  have hF8 : Nat.card F = 8 := card_eq_eight h2 h8 hgt
  have hE : Nat.card (F.subgroupOf C₄) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv]
    exact hF8
  obtain ⟨-, h1, h2', -⟩ := card_derivedSeries_C₄
  refine no_abelian_eight_of_derived (D := ↥C₄) card_C₄ h1 h2' (F.subgroupOf C₄) hE ?_
  intro a ha b hb
  exact Subtype.ext (hab a ha b hb)

theorem conj_transport {n r c : Equiv.Perm (Fin 42)} (hc : c ∈ R)
    (hn : n = c * r * c⁻¹) {F : Subgroup (Equiv.Perm (Fin 42))}
    (hF : F ≤ S ⊓ Subgroup.centralizer ({n} : Set (Equiv.Perm (Fin 42)))) :
    ∃ F' : Subgroup (Equiv.Perm (Fin 42)),
      F' ≤ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S ∧
        Nat.card F' = Nat.card F ∧ (IsPGroup 2 F → IsPGroup 2 F') ∧
        ((∀ a ∈ F, ∀ b ∈ F, a * b = b * a) → ∀ a ∈ F', ∀ b ∈ F', a * b = b * a) := by
  refine ⟨F.map (MulAut.conj c⁻¹).toMonoidHom, ?_, ?_, fun h2 => h2.map _, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    have hfS : f ∈ S := (hF hf).1
    have hfn : f * n = n * f := Subgroup.mem_centralizer_singleton_iff.mp (hF hf).2
    refine ⟨?_, ?_⟩
    · show (MulAut.conj c⁻¹) f ∈ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42)))
      rw [Subgroup.mem_centralizer_singleton_iff]
      show c⁻¹ * f * c⁻¹⁻¹ * r = r * (c⁻¹ * f * c⁻¹⁻¹)
      have e1 : c⁻¹ * f * c⁻¹⁻¹ * r = c⁻¹ * (f * n) * c := by
        rw [hn]; group
      have e2 : r * (c⁻¹ * f * c⁻¹⁻¹) = c⁻¹ * (n * f) * c := by
        rw [hn]; group
      rw [e1, e2, hfn]
    · exact conj_mem_S (R.inv_mem hc) hfS
  · exact Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  · intro hab a ha b hb
    obtain ⟨f, hf, rfl⟩ := ha
    obtain ⟨g, hg, rfl⟩ := hb
    show (MulAut.conj c⁻¹) f * (MulAut.conj c⁻¹) g = (MulAut.conj c⁻¹) g * (MulAut.conj c⁻¹) f
    rw [← map_mul, ← map_mul, hab f hf g hg]

theorem outer_involution_bound {n : Equiv.Perm (Fin 42)}
    (hnR : n ∈ R) (hnS : n ∉ S) (hn2 : n * n = 1) {F : Subgroup (Equiv.Perm (Fin 42))}
    (hF : F ≤ S ⊓ Subgroup.centralizer ({n} : Set (Equiv.Perm (Fin 42)))) (h2 : IsPGroup 2 F) :
    Nat.card F ≤ 8 ∧ ((∀ a ∈ F, ∀ b ∈ F, a * b = b * a) → Nat.card F ≤ 4) := by
  have hn1 : n ≠ 1 := fun h => hnS (h ▸ S.one_mem)
  let x : ↥R := ⟨n, hnR⟩
  have hx : orderOf x = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      simpa [pow_two] using hn2
    · intro h
      exact hn1 (congrArg Subtype.val h)
  rcases (orderOf_eq_two_iff x).mp hx with h | h | h | h
  · exact absurd (mem_S_of_isConj₁ h) hnS
  · obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
    obtain ⟨F', hF', hcard, h2', hab'⟩ := conj_transport hcR hc hF
    have hb := bound_C₂ (by simpa [C₂, r₂R] using hF') (h2' h2)
    refine ⟨hcard ▸ hb.1, fun hab => hcard ▸ hb.2 (hab' hab)⟩
  · obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
    obtain ⟨F', hF', hcard, h2', hab'⟩ := conj_transport hcR hc hF
    have hb := bound_C₃ (by simpa [C₃, r₃R] using hF') (h2' h2)
    exact ⟨hcard ▸ hb.trans (by norm_num), fun _ => hcard ▸ hb⟩
  · obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
    obtain ⟨F', hF', hcard, h2', hab'⟩ := conj_transport hcR hc hF
    have hb := bound_C₄ (by simpa [C₄, r₄R] using hF') (h2' h2)
    refine ⟨hcard ▸ hb.1, fun hab => hcard ▸ hb.2 (hab' hab)⟩

theorem core_perm {T' N' : Subgroup (Equiv.Perm (Fin 42))}
    (hTR : T' ≤ R) (hT2 : IsPGroup 2 T') (hP : 64 ≤ Nat.card ↥(T' ⊓ S)) (hNT : N' ≤ T')
    (hNn : ∀ t ∈ T', ∀ a ∈ N', t * a * t⁻¹ ∈ N')
    (hcomm : ∀ a ∈ N', ∀ b ∈ N', a * b = b * a) (hsq : ∀ a ∈ N', a * a = 1) : N' ≤ S := by
  intro n hn
  by_contra hnS
  have hnR : n ∈ R := hTR (hNT hn)
  have hcount := count_lemma (S' := S) (T' := T') (N' := N')
    (fun t ht => R_le_normalizer (hTR ht)) hNT hNn hn
  set C := T' ⊓ S ⊓ Subgroup.centralizer ({n} : Set (Equiv.Perm (Fin 42))) with hC
  set E := N' ⊓ S with hE
  have hC2 : IsPGroup 2 C := hT2.to_le (inf_le_left.trans inf_le_left)
  have hCle : C ≤ S ⊓ Subgroup.centralizer ({n} : Set (Equiv.Perm (Fin 42))) :=
    fun a ha => ⟨ha.1.2, ha.2⟩
  have hE2 : IsPGroup 2 E := hT2.to_le (inf_le_left.trans hNT)
  have hEle : E ≤ S ⊓ Subgroup.centralizer ({n} : Set (Equiv.Perm (Fin 42))) := fun a ha =>
    ⟨ha.2, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha.1 n hn)⟩
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => hcomm a ha.1 b hb.1
  have hb1 := (outer_involution_bound hnR hnS (hsq n hn) hCle hC2).1
  have hb2 := (outer_involution_bound hnR hnS (hsq n hn) hEle hE2).2 hEab
  have hmul := Nat.mul_le_mul hb1 hb2
  omega

section Transport

variable {K : Type} [Group K]

theorem exists_autIso (hK : IsPSL 3 2 2 K) :
    ∃ (ψ : K ≃* ↥S) (Θ : MulAut K ≃* ↥R),
      (∀ (σ : MulAut K) (k : K),
        ((ψ (σ k) : ↥S) : Equiv.Perm (Fin 42)) =
          (Θ σ : Equiv.Perm (Fin 42)) * (ψ k : Equiv.Perm (Fin 42)) * (Θ σ : Equiv.Perm (Fin 42))⁻¹)
      ∧ ∀ k : K, (Θ (MulAut.conj k) : Equiv.Perm (Fin 42)) = (ψ k : Equiv.Perm (Fin 42)) := by
  obtain ⟨ψ⟩ := exact_model.2.2.2.1 K hK
  obtain ⟨e, he1, -⟩ := full_automorphism_action
  refine ⟨ψ, (MulAut.congr ψ).trans e.symm, fun σ k => ?_, fun k => ?_⟩
  · have h1 := he1 (e.symm (MulAut.congr ψ σ)) (ψ k)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : (MulAut.congr ψ σ) (ψ k) = ψ (σ k) := by
      simp [MulAut.congr_apply]
    rw [h2] at h1
    exact h1
  · have h1 : e ⟨(ψ k : Equiv.Perm (Fin 42)), S_le_R (ψ k).2⟩ = MulAut.congr ψ (MulAut.conj k) := by
      apply MulEquiv.ext
      intro s
      apply Subtype.ext
      rw [he1]
      simp [MulAut.congr_apply, MulAut.conj_apply]
    show ((e.symm (MulAut.congr ψ (MulAut.conj k)) : ↥R) : Equiv.Perm (Fin 42)) = _
    rw [← h1, MulEquiv.symm_apply_apply]

theorem eq_one_of_central_psl34 (hK : IsPSL 3 2 2 K) {z : K}
    (hz : ∀ x : K, x * z = z * x) : z = 1 := by
  obtain ⟨ψ⟩ := exact_model.2.2.2.1 K hK
  have hc : ((ψ z : ↥S) : Equiv.Perm (Fin 42)) ∈
      Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine ⟨?_, S_le_R (ψ z).2⟩
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => by
      have := congrArg (fun y : K => ((ψ y : ↥S) : Equiv.Perm (Fin 42))) (hz (ψ.symm ⟨g, hg⟩))
      simpa using this
  rw [centralizer_S_inf_R, Subgroup.mem_bot] at hc
  exact ψ.injective (Subtype.ext (by simpa using hc))

theorem card_psl34 (hK : IsPSL 3 2 2 K) : Nat.card K = 20160 := by
  obtain ⟨ψ⟩ := exact_model.2.2.2.1 K hK
  rw [Nat.card_congr ψ.toEquiv]
  exact card_S

theorem core_psl34 (hK : IsPSL 3 2 2 K)
    {T' N' : Subgroup (MulAut K)} (hT2 : IsPGroup 2 T') (hNT : N' ≤ T')
    (hNn : ∀ t ∈ T', ∀ a ∈ N', t * a * t⁻¹ ∈ N')
    (hcomm : ∀ a ∈ N', ∀ b ∈ N', a * b = b * a) (hsq : ∀ a ∈ N', a * a = 1)
    {P : Subgroup K} (hP : 64 ≤ Nat.card P) (hPT : ∀ p ∈ P, MulAut.conj p ∈ T') :
    ∀ a ∈ N', ∃ k : K, a = MulAut.conj k := by
  obtain ⟨ψ, Θ, hΘ, hΘc⟩ := exists_autIso hK
  let θ : MulAut K →* Equiv.Perm (Fin 42) := R.subtype.comp Θ.toMonoidHom
  have hθ : ∀ a, θ a = ((Θ a : ↥R) : Equiv.Perm (Fin 42)) := fun a => rfl
  have hPle : P.map (S.subtype.comp ψ.toMonoidHom) ≤ T'.map θ ⊓ S := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨⟨MulAut.conj p, hPT p hp, ?_⟩, (ψ p).2⟩
    rw [hθ, hΘc]
    rfl
  have hP' : 64 ≤ Nat.card ↥(T'.map θ ⊓ S) := by
    have h1 : Nat.card ↥(P.map (S.subtype.comp ψ.toMonoidHom)) = Nat.card P :=
      Subgroup.card_map_of_injective (fun a b h => ψ.injective (Subtype.ext h))
    have h2 := Subgroup.card_le_of_le hPle
    omega
  have hmain := core_perm (T' := T'.map θ) (N' := N'.map θ)
    (by rintro _ ⟨t, -, rfl⟩; exact (Θ t).2) (hT2.map θ) hP' (Subgroup.map_mono hNT)
    (by
      rintro _ ⟨t, ht, rfl⟩ _ ⟨a, ha, rfl⟩
      exact ⟨t * a * t⁻¹, hNn t ht a ha, by rw [map_mul, map_mul, map_inv]⟩)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha b hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hsq a ha, map_one])
  intro a ha
  have haS : θ a ∈ S := hmain ⟨a, ha, rfl⟩
  refine ⟨ψ.symm ⟨θ a, haS⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply ψ.injective
  apply Subtype.ext
  rw [hΘ a x]
  simp [MulAut.conj_apply, hθ]

end Transport

end CFSG.Quasithin.QA13a
