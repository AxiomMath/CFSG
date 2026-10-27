module

public import CFSG.Quasithin.Background.FFC4Five
public import CFSG.Quasithin.Vol2.Ch10SecAShape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits Equiv Equiv.Perm

section Perm5

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2000

private theorem lred2_perm5_pow_eight : ∀ g : Perm (Fin 5), g ^ 8 = 1 → g ^ 4 = 1 := by
  decide +kernel

private theorem lred2_perm5_odd_two (σ p : Perm (Fin 5)) (hσ1 : σ ≠ 1) (hσ3 : σ ^ 3 = 1)
    (hp4 : p ^ 4 = 1) (hps : sign p = -1) (hpp : (p * (σ * p * σ⁻¹)) ^ 4 = 1) :
    p ^ 2 = 1 ∧ p * σ = σ * p := by
  have key : ∀ σ p : Perm (Fin 5), σ ≠ 1 → σ ^ 3 = 1 → p ^ 4 = 1 → sign p = -1 →
      (p * (σ * p * σ⁻¹)) ^ 4 = 1 → p ^ 2 = 1 ∧ p * σ = σ * p := by
    decide +kernel
  exact key σ p hσ1 hσ3 hp4 hps hpp

private theorem lred2_perm5_card_odd_comm : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 3 = 1 →
    (Finset.univ.filter
      (fun t : Perm (Fin 5) => sign t = -1 ∧ t ^ 2 = 1 ∧ t * σ = σ * t)).card ≤ 1 := by
  decide +kernel

private theorem lred2_perm5_card_comm : ∀ p : Perm (Fin 5), sign p = -1 → p ^ 2 = 1 →
    (Finset.univ.filter (fun g : Perm (Fin 5) => g * p = p * g)).card = 12 := by
  decide +kernel

private theorem lred2_pow_eight {P : Subgroup (Perm (Fin 5))} (hP : IsPGroup 2 ↥P) {p : Perm (Fin 5)}
    (hp : p ∈ P) : p ^ 8 = 1 := by
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hdvd : 2 ^ m ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card P
    rw [hm, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    simpa [Nat.factorial] using this
  have hm3 : m ≤ 3 := by
    by_contra h
    have h4 : 2 ^ 4 ∣ 120 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h4
  have h8 : 2 ^ m ∣ 8 := by
    have : 2 ^ m ∣ 2 ^ 3 := pow_dvd_pow 2 hm3
    simpa using this
  have h1 : (⟨p, hp⟩ : ↥P) ^ (2 ^ m) = 1 := by
    rw [← hm]
    exact pow_card_eq_one'
  obtain ⟨k, hk⟩ := h8
  have h2 : (⟨p, hp⟩ : ↥P) ^ 8 = 1 := by rw [hk, pow_mul, h1, one_pow]
  simpa using congrArg Subtype.val h2

theorem lred2_perm5_even_of_normalized {P S₀ : Subgroup (Perm (Fin 5))} {σ : Perm (Fin 5)}
    (hP : IsPGroup 2 ↥P) (hσ1 : σ ≠ 1) (hσ3 : σ ^ 3 = 1) (hσP : ∀ p ∈ P, σ * p * σ⁻¹ ∈ P)
    (hS₀ : ∀ s ∈ S₀, ∀ p ∈ P, s * p * s⁻¹ ∈ P) (h8 : Nat.card ↥S₀ = 8) :
    P ≤ alternatingGroup (Fin 5) := by
  intro p hp
  by_contra hne
  have hps : sign p = -1 := by
    rcases Int.units_eq_one_or (sign p) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hne
    · exact h
  have key : ∀ q ∈ P, sign q = -1 → q ^ 2 = 1 ∧ q * σ = σ * q := by
    intro q hq hqs
    have hq4 : q ^ 4 = 1 := lred2_perm5_pow_eight _ (lred2_pow_eight hP hq)
    have hqq : (q * (σ * q * σ⁻¹)) ^ 4 = 1 :=
      lred2_perm5_pow_eight _ (lred2_pow_eight hP (P.mul_mem hq (hσP q hq)))
    exact lred2_perm5_odd_two σ q hσ1 hσ3 hq4 hqs hqq
  obtain ⟨hp2, hpσ⟩ := key p hp hps
  have hcard := lred2_perm5_card_odd_comm σ hσ1 hσ3
  have hpmem : p ∈ Finset.univ.filter
      (fun t : Perm (Fin 5) => sign t = -1 ∧ t ^ 2 = 1 ∧ t * σ = σ * t) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hps, hp2, hpσ⟩
  have hcent : S₀ ≤ Subgroup.centralizer ({p} : Set (Perm (Fin 5))) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hq : s * p * s⁻¹ ∈ P := hS₀ s hs p hp
    have hqs : sign (s * p * s⁻¹) = -1 := by
      rw [map_mul, map_mul, map_inv, mul_comm (sign s), mul_assoc, mul_inv_cancel, mul_one, hps]
    obtain ⟨hq2, hqσ⟩ := key _ hq hqs
    have hqmem : s * p * s⁻¹ ∈ Finset.univ.filter
        (fun t : Perm (Fin 5) => sign t = -1 ∧ t ^ 2 = 1 ∧ t * σ = σ * t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqs, hq2, hqσ⟩
    have heq : s * p * s⁻¹ = p := Finset.card_le_one.mp hcard _ hqmem _ hpmem
    have h' : s * p = p * s := by
      calc s * p = (s * p * s⁻¹) * s := by group
        _ = p * s := by rw [heq]
    exact h'
  have hC : Nat.card ↥(Subgroup.centralizer ({p} : Set (Perm (Fin 5)))) = 12 := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have := lred2_perm5_card_comm p hps hp2
    convert this using 2
    ext g
    simp [Subgroup.mem_centralizer_singleton_iff, eq_comm]
  have := Subgroup.card_dvd_of_le hcent
  rw [h8, hC] at this
  omega

end Perm5

section Offender

variable {W : Type} [CommGroup W] [Finite W]

theorem lred2_false_of_sym5_offender {X H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hα : U ⊔ fixV H = ⊤) (hUZ : U ⊓ fixV H = Z) {π : Perm (Fin 5) →* ↥H}
    (hπ : (FFModel.symDn 5).RealizesVia H U Z π) {A : Subgroup (MulAut W)}
    (hA : IsFFStarOffender X A)
    (hlift : ∀ a ∈ A, ∃ σ : Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧
      ((π σ : ↥H) : MulAut W) = a) : False := by
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.symDn_faithful (by norm_num)) hπ
  obtain ⟨q, hqs, hqr, hqk, hqe⟩ := FFC.exists_modelHom FFC.symDn_ker_five hπ hα hUZ
  have hker : q.ker = fixV H := by
    ext w
    exact hqk w
  have hrange : q.range = G6.coreMod 5 := by
    ext m
    constructor
    · rintro ⟨w, rfl⟩
      exact hqs w
    · intro hm
      obtain ⟨w, hw⟩ := hqr m hm
      exact ⟨w, hw⟩
  have hc : 0 < Nat.card ↥(fixV H) := Nat.card_pos
  have hW : Nat.card W = 16 * Nat.card ↥(fixV H) := by
    have h1 := Subgroup.card_ker_mul_card_range q
    have h2 : Nat.card q.range = 16 :=
      (congrArg (fun S : Subgroup (G6.PermMod 5) => Nat.card S) hrange).trans FFC.card_coreMod_five
    rw [hker, h2] at h1
    rw [← h1]
    ring
  obtain ⟨-, hA1, ⟨hcomm, hsq⟩, hoff⟩ := hA
  let π₀ : ↥(alternatingGroup (Fin 5)) →* ↥H := π.comp (alternatingGroup (Fin 5)).subtype
  have hinj₀ : Function.Injective π₀ := hinj.comp (alternatingGroup (Fin 5)).subtype_injective
  have hlift₀ : ∀ a ∈ A, ∃ σ : ↥(alternatingGroup (Fin 5)), ((π₀ σ : ↥H) : MulAut W) = a := by
    intro a ha
    obtain ⟨σ, hσ, hσa⟩ := hlift a ha
    exact ⟨⟨σ, hσ⟩, hσa⟩
  have hbot := hoff ⊥ bot_le
  rw [B1.fixV_bot, Subgroup.card_bot, Subgroup.card_top, one_mul] at hbot
  have hA4 : Nat.card A ≤ 4 := by
    have hpg : IsPGroup 2 ↥A := fun g => ⟨1, Subtype.ext (by simpa using hsq g g.2)⟩
    obtain ⟨m, hm⟩ := hpg.exists_card_eq
    set ρ : Perm (Fin 5) →* MulAut W := H.subtype.comp π with hρ
    have hρinj : Function.Injective ρ := H.subtype_injective.comp hinj
    have hAle : A ≤ (alternatingGroup (Fin 5)).map ρ := by
      intro a ha
      obtain ⟨σ, hσ, hσa⟩ := hlift a ha
      exact ⟨σ, hσ, hσa⟩
    have hH60 : Nat.card ↥((alternatingGroup (Fin 5)).map ρ) = 60 := by
      rw [Subgroup.card_map_of_injective hρinj]
      exact FFC.card_alt_five
    have hdvd : 2 ^ m ∣ 60 := by
      rw [← hm, ← hH60]
      exact Subgroup.card_dvd_of_le hAle
    have hm2 : m ≤ 2 := by
      by_contra hm3
      have : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 4 := by norm_num
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  have hx1' : (x : MulAut W) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨σ, hσ⟩ := hlift₀ (x : MulAut W) x.2
  obtain ⟨hσ1, hσ2, hσs⟩ := FFC.lift_props hinj₀ σ hσ hx1' (hsq x x.2)
  have hS1 : ∀ k ∈ fixV A, q k ∈ FFC.fixS (σ : Perm (Fin 5)) := by
    intro k hk
    have hxk : ((π (σ : Perm (Fin 5)) : ↥H) : MulAut W) k = k := by
      have : ((π₀ σ : ↥H) : MulAut W) k = k := by
        rw [hσ]
        exact hk _ x.2
      exact this
    refine FFC.mem_fixS (hqs k) ?_
    have h2 : q (((π (σ : Perm (Fin 5)) : ↥H) : MulAut W) k) =
        G6.permAct 5 (σ : Perm (Fin 5)) (q k) := hqe (σ : Perm (Fin 5)) k
    rw [hxk] at h2
    exact h2.symm
  have hfix1 : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV H) * 4 := by
    have h1 := FFC.card_le_of_maps_into q (fixV A) (FFC.fixS (σ : Perm (Fin 5))) hS1
    rw [hker] at h1
    exact h1.trans (Nat.mul_le_mul_left _ (FFC.card_fixS_le hσ1 hσ2 hσs))
  have hA4' : 4 ≤ Nat.card A := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card A * Nat.card ↥(fixV A) ≤ 3 * (Nat.card ↥(fixV H) * 4) :=
      Nat.mul_le_mul (by omega) hfix1
    omega
  have hnle : ¬ A ≤ Subgroup.zpowers (x : MulAut W) := by
    intro hle
    have h1 : Nat.card A ≤ Nat.card (Subgroup.zpowers (x : MulAut W)) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf (x : MulAut W) ≤ 2 :=
      Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (hsq x x.2))
    omega
  obtain ⟨y, hyA, hy⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
  have hyx : (x : MulAut W) ≠ y := fun h => hy (h ▸ Subgroup.mem_zpowers _)
  obtain ⟨τ, hτ⟩ := hlift₀ y hyA
  obtain ⟨hτ1, hτ2, hτs⟩ := FFC.lift_props hinj₀ τ hτ hy1 (hsq y hyA)
  obtain ⟨hστ, hcommτ⟩ := FFC.lift_pair hinj₀ σ τ hσ hτ hyx (hcomm x x.2 y hyA)
  have hS2 : ∀ k ∈ fixV A, q k ∈ FFC.fixS₂ (σ : Perm (Fin 5)) (τ : Perm (Fin 5)) := by
    intro k hk
    have hxk : ((π (σ : Perm (Fin 5)) : ↥H) : MulAut W) k = k := by
      have : ((π₀ σ : ↥H) : MulAut W) k = k := by
        rw [hσ]
        exact hk _ x.2
      exact this
    have hyk : ((π (τ : Perm (Fin 5)) : ↥H) : MulAut W) k = k := by
      have : ((π₀ τ : ↥H) : MulAut W) k = k := by
        rw [hτ]
        exact hk _ hyA
      exact this
    refine FFC.mem_fixS₂ (hqs k) ?_ ?_
    · have h2 : q (((π (σ : Perm (Fin 5)) : ↥H) : MulAut W) k) =
          G6.permAct 5 (σ : Perm (Fin 5)) (q k) := hqe (σ : Perm (Fin 5)) k
      rw [hxk] at h2
      exact h2.symm
    · have h2 : q (((π (τ : Perm (Fin 5)) : ↥H) : MulAut W) k) =
          G6.permAct 5 (τ : Perm (Fin 5)) (q k) := hqe (τ : Perm (Fin 5)) k
      rw [hyk] at h2
      exact h2.symm
  have hfix2 : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV H) * 2 := by
    have h1 := FFC.card_le_of_maps_into q (fixV A)
      (FFC.fixS₂ (σ : Perm (Fin 5)) (τ : Perm (Fin 5))) hS2
    rw [hker] at h1
    exact h1.trans (Nat.mul_le_mul_left _
      (FFC.card_fixS₂_le hσ1 hτ1 hστ hσ2 hτ2 hcommτ hσs hτs))
  have h1 : Nat.card A * Nat.card ↥(fixV A) ≤ 4 * (Nat.card ↥(fixV H) * 2) :=
    Nat.mul_le_mul hA4 hfix2
  omega

end Offender

section Assembly

variable {V : Type} [CommGroup V] [Finite V]

private theorem lred2_card_sylow {G : Type} [Group G] [Finite G] {T H : Subgroup G}
    (hT : IsSylowTwoOf T H) (hH : Nat.card ↥H = 120) : Nat.card ↥T = 8 := by
  obtain ⟨hTH, hpg, hodd⟩ := hT
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  have h1 := Subgroup.card_mul_index (T.subgroupOf H)
  have h2 : Nat.card ↥(T.subgroupOf H) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  rw [h2, hm, hH] at h1
  have hi : Odd (T.subgroupOf H).index := Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]; exact hodd)
  obtain ⟨h3, -⟩ := CFSG.Quasithin.Vol2.Ch10.SecA.two_pow_mul_odd_inj hi (by decide : Odd 15)
    (h1.trans (by norm_num : (120 : ℕ) = 2 ^ 3 * 15))
  rw [hm, h3]
  norm_num

theorem lred2_false_of_sym5 {X J S Q B : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hJX : J ≤ X) (hJn : X ≤ Subgroup.normalizer (J : Set (MulAut V)))
    (hS : IsSylowTwoOf S X) (hSQ : S ≤ Q) (hB : IsFFStarOffender X B) (hBJ : B ≤ J)
    (hBQ : B ≤ pCoreOf 2 Q) {y : MulAut V} (hyQ : y ∈ Q) (hyJ : y ∈ J) (hy3 : orderOf y = 3)
    (hα : U ⊔ fixV J = ⊤) (hUZ : U ⊓ fixV J = Z) {π : Perm (Fin 5) →* ↥J}
    (hπ : (FFModel.symDn 5).RealizesVia J U Z π) : False := by
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.symDn_faithful (by norm_num)) hπ
  have hsurj : Function.Surjective π := hπ.1
  set ρ : Perm (Fin 5) →* MulAut V := J.subtype.comp π with hρ
  have hρinj : Function.Injective ρ := J.subtype_injective.comp hinj
  have hρJ : ∀ γ, ρ γ ∈ J := fun γ => (π γ).2
  have hρlift : ∀ g ∈ J, ∃ γ, ρ γ = g := by
    intro g hg
    obtain ⟨γ, hγ⟩ := hsurj ⟨g, hg⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩
  have hρrange : ρ.range = J := by
    ext g
    constructor
    · rintro ⟨γ, rfl⟩
      exact hρJ γ
    · intro hg
      exact hρlift g hg
  have hJcard : Nat.card ↥J = 120 := by
    rw [← Nat.card_congr (Equiv.ofBijective π ⟨hinj, hsurj⟩), Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hSyl : IsSylowTwoOf (S ⊓ J) J :=
    A4.isSylowTwoOf_inf_normal hS hJX hJn
  have hS8 : Nat.card ↥(S ⊓ J) = 8 := lred2_card_sylow hSyl hJcard
  set P' : Subgroup (MulAut V) := J ⊓ pCoreOf 2 Q with hP'
  set Pt : Subgroup (Perm (Fin 5)) := P'.comap ρ with hPt
  set St : Subgroup (Perm (Fin 5)) := (S ⊓ J).comap ρ with hSt
  have hPtpg : IsPGroup 2 ↥Pt := by
    refine IsPGroup.of_injective (pCoreOf_isPGroup 2 Q)
      ((ρ.comp Pt.subtype).codRestrict (pCoreOf 2 Q) (fun x => x.2.2)) ?_
    intro a b hab
    have h1 : ρ (a : Perm (Fin 5)) = ρ (b : Perm (Fin 5)) :=
      congrArg (fun z : ↥(pCoreOf 2 Q) => (z : MulAut V)) hab
    exact Subtype.ext (hρinj h1)
  have hSt8 : Nat.card ↥St = 8 := by
    have h1 : St.map ρ = S ⊓ J := by
      rw [hSt, Subgroup.map_comap_eq, hρrange]
      exact inf_eq_right.mpr inf_le_right
    rw [← Subgroup.card_map_of_injective hρinj, h1]
    exact hS8
  have hnormQ : ∀ g ∈ Q, ∀ n, n ∈ pCoreOf 2 Q → g * n * g⁻¹ ∈ pCoreOf 2 Q := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 Q (Subgroup.le_normalizer hg)) n).mp hn
  have hconjP : ∀ g ∈ Q, g ∈ J → ∀ p ∈ Pt, ∀ r : Perm (Fin 5), ρ r = g → r * p * r⁻¹ ∈ Pt := by
    intro g hgQ hgJ p hp r hr
    have h1 : ρ (r * p * r⁻¹) = g * ρ p * g⁻¹ := by rw [map_mul, map_mul, map_inv, hr]
    show ρ (r * p * r⁻¹) ∈ P'
    rw [h1]
    exact ⟨J.mul_mem (J.mul_mem hgJ (hρJ p)) (J.inv_mem hgJ), hnormQ g hgQ _ hp.2⟩
  obtain ⟨σ, hσ⟩ := hρlift y hyJ
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, map_one] at hσ
    rw [← hσ, orderOf_one] at hy3
    omega
  have hσ3 : σ ^ 3 = 1 := by
    apply hρinj
    rw [map_pow, hσ, map_one, ← hy3]
    exact pow_orderOf_eq_one y
  have hPalt : Pt ≤ alternatingGroup (Fin 5) :=
    lred2_perm5_even_of_normalized hPtpg hσ1 hσ3
      (fun p hp => hconjP y hyQ hyJ p hp σ hσ)
      (fun s hs p hp => hconjP (ρ s) (hSQ (show ρ s ∈ S ⊓ J from hs).1) (hρJ s) p hp s rfl) hSt8
  refine lred2_false_of_sym5_offender hα hUZ hπ hB fun b hb => ?_
  obtain ⟨γ, hγ⟩ := hρlift b (hBJ hb)
  have hγP : γ ∈ Pt := by
    show ρ γ ∈ P'
    rw [hγ]
    exact ⟨hBJ hb, hBQ hb⟩
  exact ⟨γ, hPalt hγP, hγ⟩

end Assembly

end CFSG.Quasithin
