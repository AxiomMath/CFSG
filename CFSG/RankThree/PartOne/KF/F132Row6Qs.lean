module

public import CFSG.RankThree.PartOne.KF.F132Row6Types

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Row6Qs

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

omit [Finite G] in
theorem isQuasisimple_conjBy_of {K0 : Subgroup G} (hq : IsQuasisimple ↥K0) (w : G) :
    IsQuasisimple ↥(conjBy w K0) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K0.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective) hq

omit [Finite G] in
theorem not_dvd_card_center_conjBy_of {K0 : Subgroup G} (w : G)
    (h : ¬ p ∣ Nat.card (Subgroup.center ↥K0)) :
    ¬ p ∣ Nat.card (Subgroup.center ↥(conjBy w K0)) := by
  let e : K0 ≃* conjBy w K0 :=
    K0.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
  have hc : (Subgroup.center K0).map (e : K0 →* conjBy w K0) = Subgroup.center (conjBy w K0) :=
    Subgroup.map_center_eq e
  rw [← hc, Subgroup.card_map_of_injective e.injective]
  exact h

theorem row6_exc_isQuasisimple (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (hG : Sec12TwoGeneric p c L E) (hf3 : 3 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → unitaryInvolution K 2 f (u : K) = u)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (ε : ↥L →* StatedProj (StatedSU 5 (2 ^ f) K)) (hε : IsCentralPQuot p ε)
    (hq : IsCentralPQuot p (suQ 5 hK))
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus6 (unitaryInvolution K 2 f) p).map (suQ 5 hK))
    (S : D8Ctx p K L (E ⊓ L))
    (hS : ∀ (d : D8Mod p K) (m : ↥(SU (unitaryInvolution K 2 f) 5)),
      (m : GL (Fin 5) K) = diagU (d8Vec 5 d) →
        ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d)) = suQ 5 hK m) :
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → kExceptional p (kZero p E s) f →
      IsQuasisimple ↥(kZero p E s) ∧ ¬ p ∣ Nat.card (Subgroup.center ↥(kZero p E s)) := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : 1 ≤ f := by omega
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R : Sec12Three.Restr c L E (E ⊓ L) := h.restr_of_generic hG
  let σ : K ≃+* K := unitaryInvolution K 2 f
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hσζ : σ (ζ : K) = ζ := hfix ζ hζp
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  set z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζp⟩ with hz
  set d₀ : D8Mod p K := ((1 : rootsOfUnity p K), z) with hd₀
  set x₀ : G := ((S.tor d₀ : ↥(E ⊓ L)) : G) with hx₀
  have hx₀E : x₀ ∈ E := (S.tor d₀).2.1
  have hx₀L : x₀ ∈ L := (S.tor d₀).2.2
  have hm₀ : ((bA6 σ ζ hσζ : ↥(SU σ 5)) : GL (Fin 5) K) = diagU (d8Vec 5 d₀) := by
    rw [d8Vec_five]
    rfl
  have hb₀ : suQ 5 hK (bA6 σ ζ hσζ) = ε ⟨x₀, hx₀L⟩ := (hS d₀ _ hm₀).symm
  obtain ⟨hx₀1, hqs, hz', hAK, hmodA, himgA⟩ := row6_layerA h hf3 hK hfix hζ ε (suQ 5 hK) hε hq hAT
    (hEA ▸ hx₀E) hx₀L hb₀
  obtain ⟨t₀, ht₀L, hr₀, hw₀⟩ := exists_weylE_reflection S R hp hp2 hζex 0
  have hrs₀ : t₀ ∈ reflectionSet p E := ⟨hr₀, L, hF13.inZeroStar, ht₀L⟩
  have hfix₀ := fix_of_weylE_fix S R hp hp2 hζex ⟨t₀, ht₀L⟩ d₀
    (by rw [hw₀, d8Act_sr_zero, inv_one])
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hAK' : Nat.card ↥(E ⊓ kLayer L x₀) = p := by rw [hEA]; exact hAK
  have hK1 := kZero_eq_of_layer_qs h hE3 h.L_le_centralizer hcL hr₀ ht₀L (hF13.reflection t₀ hrs₀)
    hx₀E hx₀L hx₀1 hfix₀ hAK' hqs hz'
  have hK0 : kZero p E t₀ = kLayer L x₀ := hK1.1
  have hex₀ : kExceptional p (kZero p E t₀) f := ⟨hf1, hpq, by rw [hK0]; exact hmodA⟩
  have hq₀ : IsQuasisimple ↥(kZero p E t₀) ∧ ¬ p ∣ Nat.card (Subgroup.center ↥(kZero p E t₀)) := by
    rw [hK0]
    exact ⟨hqs, hz'⟩
  obtain ⟨-, r₀, r₁, -, -, -, -, -, -, -, -, -, -, hexcconj, -⟩ :=
    row6_main_ext hGA h hF13 hEA hG hf3 hpq hK hfix hζ ε hε hq hAT S hS
  obtain ⟨x, hxL, hxE, hx⟩ := hexcconj t₀ hrs₀ ht₀L hex₀
  have hKt : kZero p E t₀ = conjBy x (kZero p E r₀) := by
    rw [hx]
    exact kZero_conj p r₀ hxE
  have hKr : kZero p E r₀ = conjBy x⁻¹ (kZero p E t₀) := by
    rw [hKt, Equivariance.conjBy_inv_conjBy]
  have hq₁ : IsQuasisimple ↥(kZero p E r₀) ∧ ¬ p ∣ Nat.card (Subgroup.center ↥(kZero p E r₀)) := by
    rw [hKr]
    exact ⟨isQuasisimple_conjBy_of hq₀.1 x⁻¹, not_dvd_card_center_conjBy_of x⁻¹ hq₀.2⟩
  intro s hs hsL hexc
  obtain ⟨y, hyL, hyE, hy⟩ := hexcconj s hs hsL hexc
  rw [hy, kZero_conj p r₀ hyE]
  exact ⟨isQuasisimple_conjBy_of hq₁.1 y, not_dvd_card_center_conjBy_of y hq₁.2⟩

theorem kf132Row6_exc_quasisimple_and_center
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f) :
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → kExceptional p (kZero p E s) f →
      IsQuasisimple ↥(kZero p E s) ∧ ¬ p ∣ Nat.card (Subgroup.center ↥(kZero p E s)) := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_row6 hGA hF hpq hmod
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, hchar, hK, ⟨ζ₀, hζ₀⟩, ε, hε, hFT₁, hFT₂⟩ :=
    exists_runitary_frame_of (n := 5) (Or.inr rfl) d8Comb_five hcore hf1 hpq hmod
  have hq : IsCentralPQuot p (suQ 5 hK) := isCentralPQuot_suQ hp hp2 (by norm_num) hpq hf1 hK
  have hfix : ∀ u : Kˣ, u ^ p = 1 → unitaryInvolution K 2 f (u : K) = u := by
    intro u hu
    have h2 : u ^ (2 ^ f - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, hu, one_pow]
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val]
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : u ^ 2 ^ f = u := by
      calc u ^ 2 ^ f = u ^ (2 ^ f - 1) * u := by rw [← pow_succ, Nat.sub_add_cancel hq1]
        _ = u := by rw [h2, one_mul]
    rw [this]
  have hAT : ((A ⊓ L).subgroupOf L).map ε =
      (torus6 (unitaryInvolution K 2 f) p).map (suQ 5 hK) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  obtain ⟨S, hS⟩ := rowSU_S (n := 5) (Or.inr rfl) d8Comb_five d8Comb2_five hp hp2 hK hf1 hpq
    ⟨ζ₀, hζ₀⟩ ε hε hcore.F_le hcore.F_exp hFT₁ hFT₂
  exact row6_exc_isQuasisimple hGA h hF13 hEA hG hf3 hpq hK hfix hζ₀ ε hε hq hAT S hS

theorem kf132Row6_exc_quasisimple
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f) :
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → kExceptional p (kZero p E s) f →
      IsQuasisimple ↥(kZero p E s) :=
  fun s hs hsL hexc =>
    (kf132Row6_exc_quasisimple_and_center hGA h hF hF13 hEA hf1 hpq hmod s hs hsL hexc).1

end Row6Qs

end CFSG.RankThree.PartOne.KF132
