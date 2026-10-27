module

public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.D14Chief
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.D15Proof

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isNormalIn_bot (H U : Subgroup G) : IsNormalIn H U ⊥ :=
  ⟨bot_le, fun g _ x hx => by
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, mul_one, mul_inv_cancel]⟩

variable [Finite G]

theorem relIndex_ne_zero (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem exists_isChiefSeriesFrom {H U : Subgroup G} :
    ∀ N : Subgroup G, IsNormalIn H U N → ∃ n, IsChiefSeriesFrom H U N n := by
  intro N
  induction N using WellFoundedLT.induction with
  | _ N ih =>
    intro hN
    by_cases hbot : N = ⊥
    · subst hbot
      exact ⟨0, IsChiefSeriesFrom.bot⟩
    obtain ⟨L, hL⟩ := (Set.toFinite {K : Subgroup G | IsNormalIn H U K ∧ K < N}).exists_maximal
      ⟨⊥, isNormalIn_bot H U, bot_lt_iff_ne_bot.mpr hbot⟩
    have hLs : IsNormalIn H U L ∧ L < N := hL.1
    have hstep : IsChiefStep H U L N := by
      refine ⟨hN, hLs.1, hLs.2, fun K hK hLK hKN => ?_⟩
      by_cases hKN' : K = N
      · exact Or.inr hKN'
      · exact Or.inl (le_antisymm (hL.2 ⟨hK, lt_of_le_of_ne hKN hKN'⟩ hLK) hLK)
    obtain ⟨n, hn⟩ := ih L hLs.2 hLs.1
    by_cases hc : IsCentralStep H L N
    · exact ⟨n, IsChiefSeriesFrom.central hstep hc hn⟩
    · exact ⟨n + 1, IsChiefSeriesFrom.noncentral hstep hc hn⟩

theorem isCentralStep_of_commutator_le {H T U L N : Subgroup G} (hT : IsSylowTwoOf T H)
    (hUH : U ≤ H) (hNT : N ≤ T) (hstep : IsChiefStep H U L N)
    (hP : ⁅N, oTwoUpper H⁆ ≤ L) : IsCentralStep H L N := by
  have hTH : T ≤ H := hT.1
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNH : N ≤ H := hstep.1.1.trans hUH
  have hLN : L ≤ N := hstep.2.2.1.le
  set P := oTwoUpper H with hPdef
  have hPH : P ≤ H := oTwoUpper_le H
  have hTP : T ⊔ P = H := by
    rw [hPdef, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hT
  have hPN : ∀ p ∈ P, ∀ x ∈ N, p * x * p⁻¹ * x⁻¹ ∈ L := by
    intro p hp x hx
    have h1 : ⁅x, p⁆ ∈ L := hP (Subgroup.commutator_mem_commutator hx hp)
    have h2 := L.inv_mem h1
    rwa [commutatorElement_inv, commutatorElement_def] at h2
  set K := centralizerMod L N T with hKdef
  have hKN : K ≤ N := centralizerMod_le_left L N T
  have hLK : L ≤ K := by
    intro l hl
    refine ⟨hLN hl, Subgroup.le_normalizer hl, fun t ht => ?_⟩
    have h1 : t * l⁻¹ * t⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hHL (hTH ht)) _).mp (L.inv_mem hl)
    have e : l * t * l⁻¹ * t⁻¹ = l * (t * l⁻¹ * t⁻¹) := by group
    rw [e]
    exact L.mul_mem hl h1
  have hTK : ∀ t ∈ T, ∀ y ∈ K, t * y * t⁻¹ ∈ K := by
    intro t ht y hy
    have htH := hTH ht
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hHN htH) y).mp hy.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hHL htH) hy.2.1) (Subgroup.inv_mem _ (hHL htH)),
      fun t' ht' => ?_⟩
    have h1 : y * (t⁻¹ * t' * t) * y⁻¹ * (t⁻¹ * t' * t)⁻¹ ∈ L :=
      hy.2.2 _ (T.mul_mem (T.mul_mem (T.inv_mem ht) ht') ht)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hHL htH) _).mp h1
    have e : t * y * t⁻¹ * t' * (t * y * t⁻¹)⁻¹ * t'⁻¹ =
        t * (y * (t⁻¹ * t' * t) * y⁻¹ * (t⁻¹ * t' * t)⁻¹) * t⁻¹ := by group
    rw [e]
    exact h2
  have hPK : ∀ p ∈ P, ∀ y ∈ K, p * y * p⁻¹ ∈ K := by
    intro p hp y hy
    have e : p * y * p⁻¹ = (p * y * p⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact K.mul_mem (hLK (hPN p hp y (hKN hy))) hy
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [← hTP]
    refine sup_le (fun t ht => B6.mem_normalizer_of_forall_mem (hTK t ht) fun y hy => ?_)
      (fun p hp => B6.mem_normalizer_of_forall_mem (hPK p hp) fun y hy => ?_)
    · simpa using hTK t⁻¹ (T.inv_mem ht) y hy
    · simpa using hPK p⁻¹ (P.inv_mem hp) y hy
  have hKnorm : IsNormalIn H U K :=
    ⟨hKN.trans hstep.1.1, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHK hg) x).mp hx⟩
  obtain ⟨x, hxN, hxL, hxT⟩ :=
    D14.exists_fixed_of_lt hT.2.1 hNT hstep.2.2.1 (hTH.trans hHN) (hTH.trans hHL)
  have hxK : x ∈ K := by
    refine ⟨hxN, hHL (hNH hxN), fun t ht => ?_⟩
    have h1 := L.inv_mem (hxT t ht)
    have e : (t * x * t⁻¹ * x⁻¹)⁻¹ = x * t * x⁻¹ * t⁻¹ := by group
    rwa [e] at h1
  have hKeq : K = N :=
    (hstep.2.2.2 K hKnorm hLK hKN).resolve_left fun h => hxL (h ▸ hxK)
  have hle : H ≤ centralizerMod L H N := by
    refine hTP.symm.le.trans (sup_le (fun t ht => ⟨hTH ht, hHL (hTH ht), fun u hu => ?_⟩)
      (fun p hp => ⟨hPH hp, hHL (hPH hp), fun u hu => hPN p hp u hu⟩))
    have hu : u ∈ K := hKeq ▸ hu
    have h1 := L.inv_mem (hu.2.2 t ht)
    have e : (u * t * u⁻¹ * t⁻¹)⁻¹ = t * u * t⁻¹ * u⁻¹ := by group
    rwa [e] at h1
  intro g hg x hx
  exact (hle hg).2.2 x hx

theorem pow_le_relIndex {H U A : Subgroup G} (hUH : U ≤ H) (hAH : A ≤ H) {k : ℕ}
    (hk : ∀ L' N' : Subgroup G, IsChiefStep H U L' N' → ¬ IsCentralStep H L' N' →
      k ≤ (centralizerMod L' N' A).relIndex N')
    {N : Subgroup G} {n : ℕ} (h : IsChiefSeriesFrom H U N n) :
    k ^ n ≤ (Subgroup.centralizer (A : Set G)).relIndex N := by
  induction h with
  | bot => simp
  | @central N L n hstep _ _ ih =>
    exact ih.trans (Subgroup.relIndex_le_of_le_right hstep.2.2.1.le (relIndex_ne_zero _ _))
  | @noncentral N L n hstep hnc _ ih =>
    set C := Subgroup.centralizer (A : Set G) with hCdef
    set D := centralizerMod L N A with hDdef
    have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
    have hLN : L ≤ N := hstep.2.2.1.le
    have hNH : N ≤ H := hstep.1.1.trans hUH
    have hDN : D ≤ N := centralizerMod_le_left L N A
    have hLD : L ≤ D := by
      intro l hl
      refine ⟨hLN hl, Subgroup.le_normalizer hl, fun a ha => ?_⟩
      have h1 : a * l⁻¹ * a⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hHL (hAH ha)) _).mp (L.inv_mem hl)
      have e : l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) := by group
      rw [e]
      exact L.mul_mem hl h1
    have hCD : C ⊓ N ≤ D := by
      rintro x ⟨hxC, hxN⟩
      refine ⟨hxN, hHL (hNH hxN), fun a ha => ?_⟩
      have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxC a ha
      have e : x * a * x⁻¹ * a⁻¹ = 1 := by
        rw [← hxa]
        group
      rw [e]
      exact L.one_mem
    have e2 : (C ⊓ D) ⊓ N = C ⊓ N :=
      le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf (le_inf inf_le_left hCD) inf_le_right)
    have e3 : (C ⊓ D).relIndex N = C.relIndex N := by
      rw [← Subgroup.inf_relIndex_right (C ⊓ D) N, e2, Subgroup.inf_relIndex_right]
    have e1 : C.relIndex N = C.relIndex D * D.relIndex N := by
      have := Subgroup.relIndex_inf_mul_relIndex C D N
      rw [inf_eq_left.mpr hDN, e3] at this
      exact this.symm
    have h1 : C.relIndex L ≤ C.relIndex D :=
      Subgroup.relIndex_le_of_le_right hLD (relIndex_ne_zero _ _)
    calc k ^ (n + 1) = k ^ n * k := pow_succ k n
      _ ≤ C.relIndex L * D.relIndex N := Nat.mul_le_mul ih (hk L N hstep hnc)
      _ ≤ C.relIndex D * D.relIndex N := Nat.mul_le_mul_right _ h1
      _ = C.relIndex N := e1.symm

end CFSG.Quasithin.D15Proof
