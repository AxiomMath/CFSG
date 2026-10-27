module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221A8Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221PiK

public section

namespace CFSG.Quasithin.S15221

open Equiv Equiv.Perm CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin
  CFSG.QuasithinUnique.Vol2Native.L239.L42Insp

variable {G : Type*} [Group G]

section Main

variable [Finite G]

theorem card_twoPart_A8 : (20160 : ℕ).factorization 2 = 6 := by
  have h6 : 6 ≤ (20160 : ℕ).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mp (by norm_num)
  have h7 : ¬ 7 ≤ (20160 : ℕ).factorization 2 := fun h =>
    absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mpr h)
      (by norm_num)
  omega

theorem card_image_sylow {K D : Subgroup G} (hDK : D ≤ K) (hD2 : IsPGroup 2 D)
    (hDi : ¬ 2 ∣ (D.subgroupOf K).index) (e : OTwoQuot K ≃* alternatingGroup (Fin 8)) :
    Nat.card (((D.subgroupOf K).map (e.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)))).map
        (alternatingGroup (Fin 8)).subtype) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : Function.Surjective (e.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hDk2 : IsPGroup 2 (D.subgroupOf K) := hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDK).symm
  let SD : Sylow 2 ↥K := hDk2.toSylow hDi
  have h1 := Sylow.card_eq_multiplicity (SD.mapSurjective hπ)
  rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective]
  have h2 : Nat.card ((D.subgroupOf K).map (e.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)))) = 64 := by
    have h3 : Nat.card ↥(SD.mapSurjective hπ).toSubgroup =
        Nat.card ((D.subgroupOf K).map (e.toMonoidHom.comp
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)))) := rfl
    rw [← h3, h1, card_A8, card_twoPart_A8]
    norm_num
  exact h2

theorem P0_le_cent8 {p : Perm (Fin 8)} (hp : p ∈ P0) : p ∈ cent8 :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr (tau0_comm_P0 p hp), P0_le_A8 hp⟩

theorem exists_Ctilde {K D : Subgroup G} (hDK : D ≤ K) (hD2 : IsPGroup 2 D)
    (hDi : ¬ 2 ∣ (D.subgroupOf K).index) (e : OTwoQuot K ≃* alternatingGroup (Fin 8)) :
    ∃ C : Subgroup G, D ≤ C ∧ C ≤ K ∧
      (∀ g : G, g ∈ Subgroup.normalizer (K : Set G) → g ∈ Subgroup.normalizer (D : Set G) →
        g ∈ Subgroup.normalizer (C : Set G)) ∧
      ∃ σ : ↥C →* Perm (Fin 4), Function.Surjective σ ∧ IsPGroup 2 σ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP64 := card_image_sylow hDK hD2 hDi e
  set P : Subgroup (Perm (Fin 8)) := ((D.subgroupOf K).map (e.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)))).map (alternatingGroup (Fin 8)).subtype with hP
  have hPA : P ≤ alternatingGroup (Fin 8) := Subgroup.map_subtype_le _
  obtain ⟨g0, hg0A, hg0⟩ := sylow_conj hPA hP64
  set π₁ := piK K e g0 with hπ₁
  have hmemP : ∀ y : Perm (Fin 8), y ∈ P ↔ ∃ k : ↥K, (k : G) ∈ D ∧
      ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) = y := by
    intro y
    constructor
    · rintro ⟨a, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, Subgroup.mem_subgroupOf.mp hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩
  have hDP0 : ∀ (x : G) (hx : x ∈ D), π₁ ⟨x, hDK hx⟩ ∈ P0 := by
    intro x hx
    rw [piK_apply]
    exact (hg0 _).mp ((hmemP _).mpr ⟨⟨x, hDK hx⟩, hx, rfl⟩)
  have hP0D : ∀ p ∈ P0, ∃ (x : G) (hx : x ∈ D), π₁ ⟨x, hDK hx⟩ = p := by
    intro p hp
    have h1 : g0⁻¹ * p * g0 ∈ P := by
      rw [hg0]
      simpa [mul_assoc] using hp
    obtain ⟨k, hk, hkp⟩ := (hmemP _).mp h1
    refine ⟨k, hk, ?_⟩
    rw [piK_apply, hkp]
    group
  set C : Subgroup G := (cent8.comap π₁).map K.subtype with hC
  have hmemC : ∀ x : G, x ∈ C ↔ ∃ hx : x ∈ K, π₁ ⟨x, hx⟩ ∈ cent8 := by
    intro x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hCK : C ≤ K := Subgroup.map_subtype_le _
  have hDC : D ≤ C := fun x hx => (hmemC x).mpr ⟨hDK hx, P0_le_cent8 (hDP0 x hx)⟩
  have hcentC : ∀ c : ↥C, (π₁.comp (Subgroup.inclusion hCK)) c ∈ cent8 := fun c =>
    ((hmemC c.1).mp c.2).2
  let ρ : ↥C →* ↥cent8 := MonoidHom.codRestrict (π₁.comp (Subgroup.inclusion hCK)) cent8 hcentC
  have hρ : ∀ c : ↥C, ((ρ c : ↥cent8) : Perm (Fin 8)) = π₁ ⟨c.1, hCK c.2⟩ := fun c => rfl
  have hρsurj : Function.Surjective ρ := by
    intro c'
    obtain ⟨x, hx⟩ := exists_piK_eq K e g0 hg0A c'.2.2
    have hxC : (x : G) ∈ C := (hmemC x.1).mpr ⟨x.2, by
      rw [show (⟨x.1, x.2⟩ : ↥K) = x from rfl, hx]
      exact c'.2⟩
    exact ⟨⟨x.1, hxC⟩, Subtype.ext (by rw [hρ]; exact hx)⟩
  have hρ2 : IsPGroup 2 ρ.ker := by
    intro c
    have hk : π₁ ⟨c.1.1, hCK c.1.2⟩ = 1 := by
      have := congrArg (fun z : ↥cent8 => (z : Perm (Fin 8))) (MonoidHom.mem_ker.mp c.2)
      simpa [hρ] using this
    have hmem : (⟨c.1.1, hCK c.1.2⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := (piK_eq_one_iff K e g0).mp hk
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥K) ⟨_, hmem⟩
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(CFSG.Open.pCore 2 ↥K) => ((z : ↥K) : G)) hj
    simpa using this
  have hconj : ∀ g : G, g ∈ Subgroup.normalizer (K : Set G) →
      g ∈ Subgroup.normalizer (D : Set G) → ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro g hgK hgD x hx
    obtain ⟨hxK, hxc⟩ := (hmemC x).mp hx
    have hx' : g * x * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgK x).mp hxK
    obtain ⟨z, hzD, hz⟩ := hP0D tau0 tau0_mem_P0
    have hzK : z ∈ K := hDK hzD
    have hz' : g * z * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hgD z).mp hzD
    have hz'K : g * z * g⁻¹ ∈ K := hDK hz'
    have hker : ∀ (w : G) (hw : w ∈ K) (hw' : g * w * g⁻¹ ∈ K), π₁ ⟨w, hw⟩ = 1 →
        π₁ ⟨g * w * g⁻¹, hw'⟩ = 1 := fun w hw hw' h => piK_conj_eq_one K e g0 hgK hw hw' h
    have hz'tau : π₁ ⟨g * z * g⁻¹, hz'K⟩ = tau0 := by
      have hsign : sign (π₁ ⟨g * z * g⁻¹, hz'K⟩) = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp (piK_mem_alternating K e g0 hg0A _)
      have hcentral : ∀ p ∈ P0, p * π₁ ⟨g * z * g⁻¹, hz'K⟩ = π₁ ⟨g * z * g⁻¹, hz'K⟩ * p := by
        intro p hp
        obtain ⟨d, hdD, hdp⟩ := hP0D p hp
        have hdK : d ∈ K := hDK hdD
        have hgDi : g⁻¹ ∈ Subgroup.normalizer (D : Set G) := inv_mem hgD
        have hd₁D : g⁻¹ * d * g⁻¹⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hgDi d).mp hdD
        have hd₁K : g⁻¹ * d * g⁻¹⁻¹ ∈ K := hDK hd₁D
        have hc1 : π₁ ⟨z, hzK⟩ * π₁ ⟨g⁻¹ * d * g⁻¹⁻¹, hd₁K⟩ =
            π₁ ⟨g⁻¹ * d * g⁻¹⁻¹, hd₁K⟩ * π₁ ⟨z, hzK⟩ := by
          rw [show π₁ ⟨z, hzK⟩ = tau0 from hz]
          exact (tau0_comm_P0 _ (hDP0 _ hd₁D)).symm
        have hd₂ : g * (g⁻¹ * d * g⁻¹⁻¹) * g⁻¹ ∈ K := by
          have e1 : g * (g⁻¹ * d * g⁻¹⁻¹) * g⁻¹ = d := by group
          rw [e1]
          exact hdK
        have h1 := comm_conj_aux K π₁ hker hzK hd₁K hz'K hd₂ hc1
        have h2 : π₁ ⟨g * (g⁻¹ * d * g⁻¹⁻¹) * g⁻¹, hd₂⟩ = p := by
          rw [← hdp]
          exact piK_congr K e g0 hd₂ hdK (by group)
        rw [h2] at h1
        exact h1.symm
      rcases cent_P0 hsign hcentral with h1 | h1
      · exfalso
        have hgi : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hgK
        have hzz : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ ∈ K := by
          have e1 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
          rw [e1]
          exact hzK
        have h3 := piK_conj_eq_one K e g0 hgi hz'K hzz h1
        have h4 : π₁ ⟨z, hzK⟩ = 1 := by
          rw [← h3]
          exact piK_congr K e g0 hzK hzz (by group)
        rw [show π₁ ⟨z, hzK⟩ = tau0 from hz] at h4
        exact tau0_ne_one h4
      · exact h1
    have hxz : π₁ ⟨x, hxK⟩ * π₁ ⟨z, hzK⟩ = π₁ ⟨z, hzK⟩ * π₁ ⟨x, hxK⟩ := by
      rw [show π₁ ⟨z, hzK⟩ = tau0 from hz]
      exact Subgroup.mem_centralizer_singleton_iff.mp hxc.1
    have h5 := comm_conj_aux K π₁ hker hxK hzK hx' hz'K hxz
    rw [hz'tau] at h5
    exact (hmemC _).mpr ⟨hx', Subgroup.mem_centralizer_singleton_iff.mpr h5,
      piK_mem_alternating K e g0 hg0A _⟩
  refine ⟨C, hDC, hCK, fun g hgK hgD => ?_, sigma8.comp ρ, sigma8_surjective.comp hρsurj, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj g hgK hgD h
    · intro hh
      have h6 := hconj g⁻¹ (inv_mem hgK) (inv_mem hgD) _ hh
      have e1 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rwa [e1] at h6
  · rw [← MonoidHom.comap_ker]
    exact isPGroup_ker_sigma8.comap_of_ker_isPGroup ρ hρ2

end Main

end CFSG.Quasithin.S15221
