module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch11SecU1Out3
public import CFSG.Quasithin.Vol2.Ch11SecU1Sig1
public import CFSG.Quasithin.Vol2.Ch11SecU1Sig2

public section

namespace CFSG.Quasithin.RonanE114.L2

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Quasithin.Vol2.Ch11.SecU1 CFSG.Quasithin.Vol2.Ch11.SecU1.Sig
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F]

theorem sigmaFacts_inr_gen {q₀ : ℕ} (hq₀ : IsOddPrimePower q₀)
    (hq5 : 5 ≤ q₀) (hF : Nat.card F = q₀ ^ 2) {σ : F ≃+* F} (hσ : orderOf σ = 2) :
    SigmaFacts (pGammaL2PSLRange F) (SemidirectProduct.inr σ) := by
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
    simpa using congrArg (fun τ : F ≃+* F => τ z) h1
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    norm_num at hσ
  have hK₀p : Nat.card K₀ = q₀ := Nat.pow_left_injective two_ne_zero (by
    show Nat.card K₀ ^ 2 = q₀ ^ 2
    rw [← hcard, hF])
  obtain ⟨p, a, hp, hpodd, ha, hq₀p⟩ := hq₀
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 2 * a, hp, hpodd, by omega, by rw [hF, hq₀p]; ring⟩
  have hK₀odd : IsOddPrimePower (Nat.card K₀) := ⟨p, a, hp, hpodd, ha, by rw [hK₀p, hq₀p]⟩
  have hperf : Group.IsPerfect (PSL2 K₀) := psl2_isPerfect_of_card_gt_three K₀ (by omega)
  have : IsSimpleGroup (PSL2 K₀) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  set v : PGammaL2 F := SemidirectProduct.inr σ with hv
  set ι : PSL2 K₀ →* PGammaL2 F := (incl F).comp (psl2Sub K₀) with hιdef
  have hι : Function.Injective ι := (incl_injective F).comp (psl2Sub_injective K₀)
  set L := pGammaL2PSLRange F with hLdef
  have hLn : L.Normal := pGammaL2PSLRange_normal F hodd (by rw [hF]; nlinarith)
  let e : PSL2 K₀ ≃* ↥ι.range := MonoidHom.ofInjective hι
  have hL₀C : ι.range ≤ Subgroup.centralizer {v} := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((commute_inr_iff σ _).mpr (psl2Sub_mem_fieldCent hK₀ x)).symm
  have hL₀L : ι.range ≤ L := by
    rintro _ ⟨x, rfl⟩
    exact ⟨psl2Sub K₀ x, rfl⟩
  set C₀ := L ⊓ Subgroup.centralizer {v} with hC₀def
  have hC₀ : C₀ = (fieldCent σ).map (incl F) := by
    ext z
    constructor
    · rintro ⟨⟨y, rfl⟩, hz⟩
      exact ⟨y, (commute_inr_iff σ y).mp (Subgroup.mem_centralizer_singleton_iff.mp hz).symm, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        ((commute_inr_iff σ y).mpr hy).symm⟩
  have hC₀card : Nat.card C₀ = 2 * Nat.card ι.range := by
    rw [hC₀, Subgroup.card_map_of_injective (incl_injective F),
      card_fieldCent_eq hK₀ h90 hσσ hcard hodd, pgl2_card_eq_two_mul hK₀odd,
      ← Nat.card_congr e.toEquiv]
  have hL₀C₀ : ι.range ≤ C₀ := le_inf hL₀L hL₀C
  have hperfL₀ : ⁅ι.range, ι.range⁆ = ι.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      hperf.commutator_eq_top]
  have hidx : (ι.range.subgroupOf C₀).index = 2 := by
    have h := (ι.range.subgroupOf C₀).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₀C₀).toEquiv, hC₀card] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h.trans (mul_comm _ _))
  have hcomm : ⁅C₀, C₀⁆ ≤ ι.range := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h : ⁅(⟨a, ha⟩ : ↥C₀), ⟨b, hb⟩⁆ ∈ ι.range.subgroupOf C₀ := by
      rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
        Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
        inv_mem_iff, inv_mem_iff]
      tauto
    rw [Subgroup.mem_subgroupOf] at h
    simpa [commutatorElement_def] using h
  have hL₀eq : ι.range = ⁅C₀, C₀⁆ := by
    refine le_antisymm ?_ hcomm
    calc ι.range = ⁅ι.range, ι.range⁆ := hperfL₀.symm
      _ ≤ ⁅C₀, C₀⁆ := Subgroup.commutator_mono hL₀C₀ hL₀C₀
  have hmap : ∀ y ∈ Subgroup.centralizer {v}, C₀.map (MulAut.conj y).toMonoidHom ≤ C₀ := by
    rintro y hy _ ⟨z, hz, rfl⟩
    obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
    exact ⟨hLn.conj_mem z hzL y, Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hzC) (inv_mem hy)⟩
  have key : ∀ y ∈ Subgroup.centralizer {v}, ∀ x ∈ ι.range, y * x * y⁻¹ ∈ ι.range := by
    intro y hy x hx
    rw [hL₀eq] at hx ⊢
    have h : (⁅C₀, C₀⁆ : Subgroup (PGammaL2 F)).map (MulAut.conj y).toMonoidHom ≤ ⁅C₀, C₀⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (hmap y hy) (hmap y hy)
    exact h ⟨x, hx, rfl⟩
  have hN : Subgroup.centralizer {v} ≤ Subgroup.normalizer (ι.range : Set (PGammaL2 F)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key g hg x, fun h => ?_⟩
    simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ h
  have hCL : L ⊓ Subgroup.centralizer (ι.range : Set (PGammaL2 F)) = ⊥ := by
    refine le_bot_iff.mp fun z hz => ?_
    obtain ⟨⟨y, rfl⟩, hzC⟩ := Subgroup.mem_inf.mp hz
    have hfix : ∀ g : PSL2 K₀,
        semilinearAction F (incl F y) (psl2Sub K₀ g) = psl2Sub K₀ g := fun g => by
      rw [← commute_incl_iff]
      exact (Subgroup.mem_centralizer_iff.mp hzC (ι g) ⟨g, rfl⟩).symm
    rcases eq_of_fixes_psl2Sub hσ1 hK₀ hcard _ hfix with h | h
    · exact Subgroup.mem_bot.mpr h
    · exfalso
      have h1 := congrArg SemidirectProduct.right h
      rw [incl_apply, SemidirectProduct.right_inl, SemidirectProduct.right_inr] at h1
      exact hσ1 h1.symm
  refine ⟨ι.range, le_inf hL₀L hL₀C, e.symm.isSimpleGroup, ?_, hN, hCL⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_perfect (X := PSL2 K₀)
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩

theorem sigmaPGammaL2_gen {K : Type} [Field K] [Finite K] {q₀ : ℕ}
    (hq₀ : IsOddPrimePower q₀) (hq5 : 5 ≤ q₀) (hK : Nat.card K = q₀ ^ 2)
    (v : PGammaL2 K) (hv : orderOf v = 2) (hvr : v.right ≠ 1) :
    SigmaFacts (pGammaL2PSLRange K) v := by
  have hodd : IsOddPrimePower (Nat.card K) := by
    obtain ⟨p, a, hp, hpodd, ha, hq₀p⟩ := hq₀
    exact ⟨p, 2 * a, hp, hpodd, by omega, by rw [hK, hq₀p]; ring⟩
  have : (pGammaL2PSLRange K).Normal := pGammaL2PSLRange_normal K hodd (by rw [hK]; nlinarith)
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd v hv hvr
  have hσ : orderOf v.right = 2 := by
    have h2 : v ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hv])
    have h3 : v.right ^ 2 = 1 := by
      have h := map_pow (SemidirectProduct.rightHom (φ := pgl2FieldAut K)) v 2
      rw [h2, map_one, SemidirectProduct.rightHom_eq_right] at h
      exact h.symm
    exact orderOf_eq_prime h3 hvr
  have h := sigmaFacts_conj (sigmaFacts_inr_gen hq₀ hq5 hK hσ) (SemidirectProduct.inl C)
  rwa [← hC, show SemidirectProduct.inl C * ((SemidirectProduct.inl C)⁻¹ * v *
      SemidirectProduct.inl C) * (SemidirectProduct.inl C)⁻¹ = v by group] at h

end CFSG.Quasithin.RonanE114.L2

namespace CFSG.Quasithin.RonanE114.L2

open CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
  CFSG.Quasithin.Vol2.Ch11.SecU1

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

theorem outer_pair_gen {e : L ≃* PSL2 K} {ι : G →* PGammaL2 K} (h : Adapted e ι)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKc : Nat.card K = p ^ f) {t₁ t₂ : G}
    (h₁ : t₁ ∉ L) (h₂ : t₂ ∉ L) (o₁ : orderOf t₁ = 2) (o₂ : orderOf t₂ = 2)
    (hc : t₁ * t₂ = t₂ * t₁) : t₁ * t₂ ∈ L := by
  have hsq : ∀ t : G, orderOf t = 2 → ι t * ι t = 1 := fun t ht => by
    have h1 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht] at this
    rw [← map_mul, ← sq, h1, map_one]
  have hJ : ∀ t : G, t ∉ L → ι t ∉ pGammaL2PSLRange K := fun t ht hJ =>
    ht ((mem_iff_of_adapted h).mpr hJ)
  have hinl : ∀ v : PGammaL2 K, v.right = 1 → v = SemidirectProduct.inl v.left := fun v hv => by
    rw [← SemidirectProduct.inl_left_mul_inr_right v, hv, map_one, mul_one,
      SemidirectProduct.left_inl]
  have hcI : ι t₁ * ι t₂ = ι t₂ * ι t₁ := by rw [← map_mul, ← map_mul, hc]
  rw [mem_iff_of_adapted h, map_mul]
  by_cases r₁ : (ι t₁).right = 1 <;> by_cases r₂ : (ι t₂).right = 1
  · have hs : ∀ t : G, t ∉ L → (ι t).right = 1 → ¬ SqLeft (ι t) := fun t ht hr hs =>
      hJ t ht ((mem_pslRange_iff _).mpr ⟨hr, hs⟩)
    exact mul_mem_pslRange_of_not r₁ r₂ (hs t₁ h₁ r₁) (hs t₂ h₂ r₂)
  · exfalso
    apply hJ t₁ h₁
    obtain ⟨g, hg⟩ : ∃ g, ι t₁ = SemidirectProduct.inl g := ⟨_, hinl _ r₁⟩
    rw [hg] at hcI ⊢
    exact mem_pslRange_of_commute_fieldInv hp hp2 hKc (ι t₂) (hsq t₂ o₂) r₂ g hcI.symm
  · exfalso
    apply hJ t₂ h₂
    obtain ⟨g, hg⟩ : ∃ g, ι t₂ = SemidirectProduct.inl g := ⟨_, hinl _ r₂⟩
    rw [hg] at hcI ⊢
    exact mem_pslRange_of_commute_fieldInv hp hp2 hKc (ι t₁) (hsq t₁ o₁) r₁ g hcI
  · have hrr : ∀ t : G, orderOf t = 2 → (ι t).right * (ι t).right = 1 := fun t ht => by
      have := congrArg SemidirectProduct.right (hsq t ht)
      simpa using this
    have heq := ringAut_eq_of_sq' (hrr t₁ o₁) (hrr t₂ o₂) r₁ r₂
    have hr : (ι t₁ * ι t₂).right = 1 := by
      rw [SemidirectProduct.mul_right, heq, hrr t₂ o₂]
    obtain ⟨g, hg⟩ : ∃ g, ι t₁ * ι t₂ = SemidirectProduct.inl g := ⟨_, hinl _ hr⟩
    rw [hg]
    refine mem_pslRange_of_commute_fieldInv hp hp2 hKc (ι t₁) (hsq t₁ o₁) r₁ g ?_
    rw [← hg]
    calc ι t₁ * (ι t₁ * ι t₂) = ι t₁ * (ι t₂ * ι t₁) := by rw [hcI]
      _ = ι t₁ * ι t₂ * ι t₁ := by rw [mul_assoc]

end CFSG.Quasithin.RonanE114.L2
