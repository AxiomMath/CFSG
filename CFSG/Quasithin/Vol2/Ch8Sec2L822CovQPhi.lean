module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovG
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1c

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

theorem cov_Q_phi_theta_exists {G : Type} [Group G] {H K : Subgroup G} (hKH : K ≤ H)
    (θ : ↥H →* Equiv.Perm (Fin 5)) (hθK : (K.subgroupOf H).map θ = alternatingGroup (Fin 5)) :
    ∃ θK : ↥K →* ↥(alternatingGroup (Fin 5)), Function.Surjective θK ∧
      ∀ x : ↥K, ((θK x : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = θ ⟨(x : G), hKH x.2⟩ := by
  have hrange : ∀ x : ↥K, θ (Subgroup.inclusion hKH x) ∈ alternatingGroup (Fin 5) := by
    intro x
    rw [← hθK]
    exact Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.2 x.2)
  refine ⟨(θ.comp (Subgroup.inclusion hKH)).codRestrict (alternatingGroup (Fin 5)) hrange, ?_, ?_⟩
  · intro a
    have ha : (a : Equiv.Perm (Fin 5)) ∈ (K.subgroupOf H).map θ := by
      rw [hθK]
      exact a.2
    obtain ⟨h, hh, hθh⟩ := Subgroup.mem_map.1 ha
    exact ⟨⟨(h : G), Subgroup.mem_subgroupOf.1 hh⟩, Subtype.ext hθh⟩
  · intro x
    rfl

theorem cov_Q_phi_quot_exists {G : Type} [Group G] {K Kz : Subgroup G} (hKKz : K ≤ Kz) :
    ∃ f : ↥K →* ↥(CFSG.Quasithin.modO2Image Kz K), Function.Surjective f ∧
      ∀ x : ↥K, ((f x : ↥(CFSG.Quasithin.modO2Image Kz K)) : ↥Kz ⧸ CFSG.pCore 2 ↥Kz) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) (Subgroup.inclusion hKKz x) := by
  refine ⟨((QuotientGroup.mk' (CFSG.pCore 2 ↥Kz)).comp (Subgroup.inclusion hKKz)).codRestrict
    (CFSG.Quasithin.modO2Image Kz K) (fun x => kzMemModO2Image_kz3.mpr ⟨(x : G), x.2, hKKz x.2, rfl⟩), ?_, ?_⟩
  · intro a
    obtain ⟨y, hyK, hyKz, hay⟩ := kzMemModO2Image_kz3.mp a.2
    exact ⟨⟨y, hyK⟩, Subtype.ext hay⟩
  · intro x
    rfl

theorem cov_Q_phi_ker_pow {G : Type} [Group G] {K Kz : Subgroup G} (hKKz : K ≤ Kz)
    (f : ↥K →* ↥(CFSG.Quasithin.modO2Image Kz K))
    (hf : ∀ x : ↥K, ((f x : ↥(CFSG.Quasithin.modO2Image Kz K)) : ↥Kz ⧸ CFSG.pCore 2 ↥Kz) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) (Subgroup.inclusion hKKz x)) :
    ∀ x ∈ f.ker, ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
  intro x hx
  have h1 : f x = 1 := MonoidHom.mem_ker.1 hx
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) (Subgroup.inclusion hKKz x) = 1 := by
    rw [← hf x]
    exact congrArg Subtype.val h1
  rw [QuotientGroup.mk'_apply] at h2
  have hmem : Subgroup.inclusion hKKz x ∈ CFSG.pCore 2 ↥Kz := (QuotientGroup.eq_one_iff _).mp h2
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Kz)) ⟨Subgroup.inclusion hKKz x, hmem⟩
  refine ⟨n, ?_⟩
  apply Subgroup.inclusion_injective hKKz
  rw [map_pow, map_one]
  have h3 := congrArg Subtype.val hn
  simpa using h3

theorem cov_Q_phi {G : Type} [Group G] [Finite G] {H K Kz : Subgroup G}
    (hKH : K ≤ H) (hKKz : K ≤ Kz) (θ : ↥H →* Equiv.Perm (Fin 5))
    (hθK : (K.subgroupOf H).map θ = alternatingGroup (Fin 5))
    {y : G} (hyK : y ∈ K) (hθy : θ ⟨y, hKH hyK⟩ ≠ 1) :
    ∃ (hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) ⟨y, hKKz hyK⟩ :
          ↥Kz ⧸ CFSG.pCore 2 ↥Kz) ∈ CFSG.Quasithin.modO2Image Kz K)
      (φ : ↥(CFSG.Quasithin.modO2Image Kz K) →* ↥(alternatingGroup (Fin 5))),
      Function.Surjective φ ∧
        φ ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) ⟨y, hKKz hyK⟩, hmem⟩ ≠ 1 := by
  obtain ⟨θK, hθKsurj, hθKval⟩ := cov_Q_phi_theta_exists hKH θ hθK
  obtain ⟨f, hfsurj, hfval⟩ := cov_Q_phi_quot_exists hKKz
  obtain ⟨ψ, hψsurj, hψf⟩ :=
    exists_lift_a5_cv f hfsurj (cov_Q_phi_ker_pow hKKz f hfval) θK hθKsurj
  have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) ⟨y, hKKz hyK⟩ :
      ↥Kz ⧸ CFSG.pCore 2 ↥Kz) ∈ CFSG.Quasithin.modO2Image Kz K :=
    kzMemModO2Image_kz3.mpr ⟨y, hyK, hKKz hyK, rfl⟩
  refine ⟨hmem, ψ, hψsurj, ?_⟩
  have hfy : f ⟨y, hyK⟩ = ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) ⟨y, hKKz hyK⟩, hmem⟩ :=
    Subtype.ext (hfval ⟨y, hyK⟩)
  intro h
  apply hθy
  have h1 : θK ⟨y, hyK⟩ = 1 := by
    rw [← hfy, hψf] at h
    exact h
  have h2 := congrArg Subtype.val h1
  rw [hθKval] at h2
  exact h2

end CFSG.Quasithin.H13
