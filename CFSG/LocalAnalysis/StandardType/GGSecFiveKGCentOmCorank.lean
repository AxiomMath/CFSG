module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmFrame

import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin

@[expose] def kgcTorusSet {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {G : Type*} [Group G]
    (ψ : spinGroup (quadPlus n K) →* G) (D : Subgroup G) (p : ℕ) : Set (spinGroup (quadPlus n K)) :=
  {h | h ∈ ggTorus (plusDatum n K hn) ∧ h ^ p = 1 ∧
    ∀ β ∈ {β | β ∈ (plusDatum n K hn).roots ∧
      (plusDatum n K hn).rootGroup β ≤ (Subgroup.centralizer (D : Set G)).comap ψ},
      ∀ z ∈ (plusDatum n K hn).rootGroup β, Commute h z}

theorem kgcDiag_one {n : ℕ} {K : Type} [Field K] (m : Fin n ⊕ Fin n) : kgcDiag
    (1 : spinGroup (quadPlus n K)) m = 1 := by
  rw [kgcDiag, map_one, LinearEquiv.coe_one, id_eq, Pi.single_eq_same]

theorem kgcDiag_mul {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {x : spinGroup (quadPlus n K)}
    (hx : x ∈ ggTorus (plusDatum n K hn)) (y : spinGroup (quadPlus n K)) (m : Fin n ⊕ Fin n) :
    kgcDiag (x * y) m = kgcDiag x m * kgcDiag y m := by
  rw [kgcDiag, map_mul, LinearEquiv.mul_apply, spinAction_apply_eq_kgcDiag_mul hn hx]
  rfl

theorem kgcDiag_pow {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {z : spinGroup (quadPlus n K)}
    (hz : z ∈ ggTorus (plusDatum n K hn)) (a : ℕ) (m : Fin n ⊕ Fin n) :
    kgcDiag (z ^ a) m = kgcDiag z m ^ a := by
  induction a with
  | zero => rw [pow_zero, pow_zero, kgcDiag_one]
  | succ a ih => rw [pow_succ' z, kgcDiag_mul hn hz, ih, pow_succ']

theorem commute_of_mem_ggTorus_plus {n : ℕ} {K : Type} [Field K] [CharP K 2] (hn : 3 ≤ n)
    {x y : spinGroup (quadPlus n K)} (hx : x ∈ ggTorus (plusDatum n K hn))
    (hy : y ∈ ggTorus (plusDatum n K hn)) : Commute x y := by
  show x * y = y * x
  refine RootCentOmega.spinAction_quadPlus_injective
    (LinearEquiv.ext fun v => funext fun m => ?_)
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    spinAction_apply_eq_kgcDiag_mul hn hx, spinAction_apply_eq_kgcDiag_mul hn hy,
    spinAction_apply_eq_kgcDiag_mul hn hy, spinAction_apply_eq_kgcDiag_mul hn hx]
  ring

private theorem kgcDiag_mul_eq_one_of_conj_longRoot {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {σ : spinGroup (quadPlus n K)}
    (hσ : σ ∈ ggTorus (plusDatum n K hn)) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (h : σ * (plusFrame n K hn).longRoot hij s t (.ofAdd 1) * σ⁻¹ =
      (plusFrame n K hn).longRoot hij s t (.ofAdd 1)) :
    kgcDiag σ (kgcIdx i s) * kgcDiag σ (kgcIdx j t) = 1 := by
  rw [StdPosD.conj_longRoot_of_smul (plusFrame n K hn) hij s t
    (spinAction_vec_eq_kgcDiag_smul hn hσ i s) (spinAction_vec_eq_kgcDiag_smul hn hσ j t),
    mul_one] at h
  exact Multiplicative.ofAdd.injective ((plusFrame n K hn).longRoot_injective hij s t h)

theorem kgcDiag_eq_of_smul {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {h : spinGroup (quadPlus n K)}
    {k : Fin n} {r : Bool} {c : K} (hc : spinAction (quadPlus n K) h ((plusFrame n K hn).vec k r) =
      c • (plusFrame n K hn).vec k r) : kgcDiag h (kgcIdx k r) = c := by
  rw [kgcDiag, ← plusFrame_vec_eq_single_kgcIdx hn, hc, Pi.smul_apply,
    plusFrame_vec_eq_single_kgcIdx hn, Pi.single_eq_same, smul_eq_mul, mul_one]

theorem kgcFixedIdx_iff {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {S : Set (spinGroup (quadPlus n K))}
    (hS : S ⊆ ggTorus (plusDatum n K hn)) (k : Fin n) (r : Bool) :
    KGCFixedIdx hn S k ↔ ∀ σ ∈ S, kgcDiag σ (kgcIdx k r) = 1 := by
  have key : ∀ σ ∈ S, ∀ r : Bool, kgcDiag σ (kgcIdx k r) = 1 → kgcDiag σ (kgcIdx k (!r)) = 1 :=
    fun σ hσ r h => by
      have h2 := kgcDiag_mul_kgcDiag_not hn (hS hσ) k r
      rwa [h, one_mul] at h2
  refine ⟨fun h σ hσ => ?_, fun h σ hσ => ?_⟩
  · have h1 := kgcDiag_eq_one_of_fix hn (hS hσ) (h σ hσ)
    cases r
    · exact key σ hσ true h1
    · exact h1
  · have h1 : kgcDiag σ (kgcIdx k true) = 1 := by
      cases r
      · exact key σ hσ false (h σ hσ)
      · exact h σ hσ
    rw [spinAction_vec_eq_kgcDiag_smul hn (hS hσ), h1, one_smul]

private theorem conj_eq_of_mem_kgcLiftSet {n : ℕ} {K : Type} [Field K] {G : Type*} [Group G]
    {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G} (hψ : Function.Injective ψ)
    {σ u : spinGroup (quadPlus n K)} (hσ : σ ∈ kgcLiftSet ψ D)
    (hu : ψ u ∈ Subgroup.centralizer (D : Set G)) : σ * u * σ⁻¹ = u := by
  obtain ⟨d, hd, hσd⟩ := hσ
  exact hψ ((hσd u).symm.trans
    (mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hu d hd)))

theorem kgcLiftSet_subset_kgcTorusSet {n : ℕ} {K : Type} [Field K] [CharP K 2] (hn : 3 ≤ n)
    {G : Type*} [Group G]
    {p : ℕ} {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G} (hψ : Function.Injective ψ)
    (hDp : ∀ d ∈ D, d ^ p = 1)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum n K hn), ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹)) :
    kgcLiftSet ψ D ⊆ kgcTorusSet hn ψ D p := by
  have hcen : ∀ τ : spinGroup (quadPlus n K), (∀ u, τ * u * τ⁻¹ = u) → τ = 1 := fun τ hτ => by
    have h : τ ∈ Subgroup.center (spinGroup (quadPlus n K)) :=
      Subgroup.mem_center_iff.mpr fun u => (mul_inv_eq_iff_eq_mul.mp (hτ u)).symm
    rwa [RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := K) hn,
      Subgroup.mem_bot] at h
  intro σ hσL
  obtain ⟨d, hd, hσ⟩ := id hσL
  obtain ⟨s, hs, hsd⟩ := hlift d hd
  have hσs : s⁻¹ * σ = 1 := hcen _ fun u => by
    have e := hψ ((hσ u).symm.trans (hsd u))
    calc s⁻¹ * σ * u * (s⁻¹ * σ)⁻¹ = s⁻¹ * (σ * u * σ⁻¹) * s := by group
      _ = u := by rw [e]; group
  have hpow : ∀ k : ℕ, ∀ u, d ^ k * ψ u * (d ^ k)⁻¹ = ψ (σ ^ k * u * (σ ^ k)⁻¹) := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      calc d ^ (k + 1) * ψ u * (d ^ (k + 1))⁻¹ = d * (d ^ k * ψ u * (d ^ k)⁻¹) * d⁻¹ := by group
        _ = ψ (σ ^ (k + 1) * u * (σ ^ (k + 1))⁻¹) := by rw [ih, hσ]; congr 1; group
  refine ⟨inv_mul_eq_one.mp hσs ▸ hs, hcen _ fun u => hψ ?_, fun β hβ z hz =>
    mul_inv_eq_iff_eq_mul.mp (conj_eq_of_mem_kgcLiftSet hψ hσL (Subgroup.mem_comap.mp (hβ.2 hz)))⟩
  rw [← hpow p u, hDp d hd, one_mul, inv_one, mul_one]

theorem pow_eq_one_of_kgcDiag {n : ℕ} {K : Type} [Field K] [CharP K 2] (hn : 3 ≤ n) {p : ℕ}
    {x : spinGroup (quadPlus n K)}
    (hx : x ∈ ggTorus (plusDatum n K hn)) (h : ∀ k : Fin n, kgcDiag x (.inl k) ^ p = 1) :
    x ^ p = 1 := by
  refine RootCentOmega.spinAction_quadPlus_injective
    (LinearEquiv.ext fun v => funext fun m => ?_)
  rw [spinAction_apply_eq_kgcDiag_mul hn (pow_mem hx p), kgcDiag_pow hn hx, map_one,
    LinearEquiv.coe_one, id_eq]
  suffices kgcDiag x m ^ p = 1 by rw [this, one_mul]
  rcases m with k | k
  · exact h k
  · rw [eq_inv_of_mul_eq_one_right (kgcDiag_inl_mul_inr hn hx k), inv_pow, h k, inv_one]

theorem mem_kgcTorusSet_of_kgcDiag {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {G : Type*} [Group G]
    {p : ℕ} {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G} (hψ : Function.Injective ψ)
    (hLT : kgcLiftSet ψ D ⊆ ggTorus (plusDatum n K hn)) {x : spinGroup (quadPlus n K)}
    (hx : x ∈ ggTorus (plusDatum n K hn)) (hxp : x ^ p = 1)
    (hroot : ∀ {i j : Fin n}, i ≠ j → ∀ s t : Bool,
      (∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx i s) * kgcDiag σ (kgcIdx j t) = 1) →
        kgcDiag x (kgcIdx i s) * kgcDiag x (kgcIdx j t) = 1) :
    x ∈ kgcTorusSet hn ψ D p := by
  refine ⟨hx, hxp, fun β hβ z hz => ?_⟩
  obtain ⟨i, j, hij, s, t, -, hR⟩ := exists_plusRootGroup_eq (K := K) hn hβ.1
  have hR' : (plusDatum n K hn).rootGroup β = ((plusFrame n K hn).longRoot hij s t).range := hR
  rw [hR'] at hz
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hz
  have hmem : (plusFrame n K hn).longRoot hij s t (.ofAdd 1) ∈ (plusDatum n K hn).rootGroup β := by
    rw [hR']
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have h1 : ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx i s) * kgcDiag σ (kgcIdx j t) = 1 :=
    fun σ hσ => kgcDiag_mul_eq_one_of_conj_longRoot hn (hLT hσ) hij s t
      (conj_eq_of_mem_kgcLiftSet hψ hσ (Subgroup.mem_comap.mp (hβ.2 hmem)))
  exact mul_inv_eq_iff_eq_mul.mp
    (conj_longRoot_eq_of_kgcDiag_mul hn hx hij s t (hroot hij s t h1) (Multiplicative.toAdd y))

theorem mem_centralizer_longRoot_of_kgcDiag {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {G : Type*}
    [Group G] {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G}
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum n K hn), ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹))
    {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (h : ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx i s) * kgcDiag σ (kgcIdx j t) = 1) (b : K) :
    ψ ((plusFrame n K hn).longRoot hij s t (.ofAdd b)) ∈ Subgroup.centralizer (D : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
  obtain ⟨σ, hσT, hσ⟩ := hlift d hd
  rw [← mul_inv_eq_iff_eq_mul, hσ, conj_longRoot_eq_of_kgcDiag_mul hn hσT hij s t
    (h σ ⟨d, hd, hσ⟩) b]

theorem sq_le_ncard_kgcTorusSet {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 3 ≤ n)
    {G : Type*} [Group G]
    {p : ℕ} (hp : p.Prime) {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G}
    {x y : spinGroup (quadPlus n K)} (hx : x ∈ kgcTorusSet hn ψ D p)
    (hy : y ∈ kgcTorusSet hn ψ D p) {m₁ m₂ : Fin n ⊕ Fin n} (hx₁ : kgcDiag x m₁ ≠ 1)
    (hx₂ : kgcDiag x m₂ = 1) (hy₁ : kgcDiag y m₁ = 1) (hy₂ : kgcDiag y m₂ ≠ 1) :
    p ^ 2 ≤ Set.ncard (kgcTorusSet hn ψ D p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : (kgcTorusSet hn ψ D p).Finite := by
    have : Finite (spinGroup (quadPlus n K)) :=
      Finite.of_injective (fun σ => ⇑(spinAction (quadPlus n K) σ))
        fun a b h => RootCentOmega.spinAction_quadPlus_injective (DFunLike.coe_injective h)
    exact Set.toFinite _
  have hprim : ∀ {z : spinGroup (quadPlus n K)} {m : Fin n ⊕ Fin n},
      z ∈ kgcTorusSet hn ψ D p → kgcDiag z m ≠ 1 → IsPrimitiveRoot (kgcDiag z m) p := by
    intro z m hz h1
    have hp1 : kgcDiag z m ^ p = 1 := by rw [← kgcDiag_pow hn hz.1, hz.2.1, kgcDiag_one]
    rw [← orderOf_eq_prime hp1 h1]
    exact IsPrimitiveRoot.orderOf _
  have hv : ∀ (a b : ℕ) m, kgcDiag (x ^ a * y ^ b) m = kgcDiag x m ^ a * kgcDiag y m ^ b :=
    fun a b m => by rw [kgcDiag_mul hn (pow_mem hx.1 a), kgcDiag_pow hn hx.1, kgcDiag_pow hn hy.1]
  have hf : Function.Injective fun ab : Fin p × Fin p => x ^ (ab.1 : ℕ) * y ^ (ab.2 : ℕ) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 := congrArg (kgcDiag · m₁) h
    have h2 := congrArg (kgcDiag · m₂) h
    simp only [hv, hx₂, hy₁, one_pow, mul_one, one_mul] at h1 h2
    exact Prod.ext (Fin.ext ((hprim hx hx₁).pow_inj a.2 a'.2 h1))
      (Fin.ext ((hprim hy hy₂).pow_inj b.2 b'.2 h2))
  have hrange : Set.range (fun ab : Fin p × Fin p => x ^ (ab.1 : ℕ) * y ^ (ab.2 : ℕ)) ⊆
      kgcTorusSet hn ψ D p := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show x ^ (a : ℕ) * y ^ (b : ℕ) ∈ kgcTorusSet hn ψ D p
    refine ⟨mul_mem (pow_mem hx.1 _) (pow_mem hy.1 _), ?_, fun β hβ z hz =>
      ((hx.2.2 β hβ z hz).pow_left _).mul_left ((hy.2.2 β hβ z hz).pow_left _)⟩
    rw [((commute_of_mem_ggTorus_plus hn hx.1 hy.1).pow_pow _ _).mul_pow, pow_right_comm x,
      hx.2.1, one_pow, pow_right_comm y, hy.2.1, one_pow, one_mul]
  calc p ^ 2 = Set.ncard (Set.range fun ab : Fin p × Fin p => x ^ (ab.1 : ℕ) * y ^ (ab.2 : ℕ)) := by
        rw [Set.ncard_range_of_injective hf, Nat.card_prod, Nat.card_fin, sq]
    _ ≤ _ := Set.ncard_le_ncard hrange hfin

end CFSG.StandardType.KGCentOm

end
