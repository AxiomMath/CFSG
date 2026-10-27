module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutKExt
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Ctr

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.F431.F45
  CFSG.QuasithinUnique CFSG.GH74.GLS.Stage4.Hex

section Generic

variable {D H : Type*} [Group D] [Group H]

theorem perfectCore_map_inj (Φ : D →* H) (hΦ : Function.Injective Φ) (X : Subgroup D) :
    perfectCore (X.map Φ) = (perfectCore X).map Φ := by
  unfold perfectCore
  rw [Subgroup.map_iInf Φ hΦ]
  congr 1
  funext n
  exact (map_derivedSeriesOf Φ X n).symm

theorem centerOf_map_inj (Φ : D →* H) (hΦ : Function.Injective Φ) (X : Subgroup D) :
    centerOf (X.map Φ) = (centerOf X).map Φ := by
  ext g
  constructor
  · rintro ⟨hgX, hgc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hgX
    refine Subgroup.mem_map.mpr ⟨x, ⟨hx, ?_⟩, rfl⟩
    show x ∈ Subgroup.centralizer (X : Set D)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp hgc (Φ y) (Subgroup.mem_map_of_mem Φ hy)
    exact hΦ (by simpa [map_mul] using this)
  · rintro hg
    obtain ⟨x, ⟨hx, hxc⟩, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨Subgroup.mem_map_of_mem Φ hx, ?_⟩
    show Φ x ∈ Subgroup.centralizer ((X.map Φ : Subgroup H) : Set H)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hxc y hy
    simp only [← map_mul]
    exact congrArg Φ this

end Generic

section Centers


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sq_eq_one_of_mem_center_Pr {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {y : C K}
    (hy : y ∈ centerOf (perfectCore (Pmin K ⟨1, by decide⟩))) : y ^ 2 = 1 := by
  have hPC : parabolicSubgroup Tag.G2 K {⟨1, by decide⟩} ≤ adjointGroup Tag.G2 K :=
    parabolicSubgroup_le_adjointGroup _ _ _
  obtain ⟨hx, hxc⟩ := (mem_centerOf_perfectCore_subgroupOf hPC y).mp hy
  obtain ⟨t, ht⟩ := center_one hK hn hx hxc
  have : y = xe rC t := Subtype.ext ht
  rw [this, pow_two, xe_mul_self]

omit [Finite K] [CharP K 2] in
theorem delta_apply {n a : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (ha : 1 ≤ a)
    {σ₀ : K ≃+* K} (ho : orderOf σ₀ = 2 ^ a) :
    Even n ∧ ∀ c, (σ₀ ^ 2 ^ (a - 1)) c = c ^ 2 ^ (n / 2) := by
  have hδ : (σ₀ ^ 2 ^ (a - 1)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel ha, ← ho, pow_orderOf_eq_one]
  have h1 : σ₀ ^ 2 ^ (a - 1) ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [ho] at this
    have h2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 this
    omega
  exact involution_apply hn hK hδ h1

end Centers

section Perfect


variable {K : Type} [Field K] [Finite K] [CharP K 2] {A : LieAmalgamExt (C K)}

omit [CharP K 2] in
theorem inf_range_eq_map {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) {P : Subgroup (C K)}
    {N : Subgroup ↥A.K} (hN : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ P, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ) :
    N ⊓ (iK A hgen).range = P.map (iK A hgen) := by
  have hinj : Function.Injective (MulAut.conj : C K →* MulAut (C K)) :=
    conj_injective_of_center center_C_eq_bot'
  ext x
  constructor
  · rintro ⟨hxN, y, rfl⟩
    obtain ⟨g, hg, σ, hσ, hx⟩ := (hN _).1 hxN
    rw [iK_coe] at hx
    have h1 : fieldAut K σ = MulAut.conj (g⁻¹ * y) := by
      rw [map_mul, map_inv, hx]
      group
    have hσ1 : σ = 1 := fieldAut_eq_one_of_eq_conj hn hK h1
    rw [hσ1, map_one, mul_one] at hx
    have hyg : y = g := hinj hx
    exact ⟨g, hg, by rw [← hyg]⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(hN _).2 ⟨y, hy, 1, Subgroup.one_mem _, by simp [iK_coe]⟩, y, rfl⟩

omit [CharP K 2] in
theorem centerOf_perfectCore_eq {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) {ψ : ↥A.K} {α : MulAut (C K)}
    (P : OutProps (iK A hgen) ψ α) {Pc : Subgroup (C K)} {N : Subgroup ↥A.K}
    (hN : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ Pc, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ) :
    centerOf (perfectCore N) = (centerOf (perfectCore Pc)).map (iK A hgen) := by
  have hinj : Function.Injective (iK A hgen) := iK_injective A hgen center_C_eq_bot'
  rw [P.perfectCore_eq_inf_range N, inf_range_eq_map hn hK hgen hN, perfectCore_map_inj _ hinj,
    centerOf_map_inj _ hinj]

end Perfect

section Objects

variable {K : Type} [Field K]
  {A : LieAmalgamExt (C K)}

abbrev outS (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) : Subgroup ↥A.K :=
  (U K).map (iK A hgen)

open scoped Classical in
noncomputable abbrev outI (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) :
    Finset ↥A.K :=
  {iK A hgen (xa (1 : K)), iK A hgen (xu 1), iK A hgen (xv 1), iK A hgen (xb 1),
    iK A hgen (xc 1)}

theorem mem_outS_iff (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) (x : ↥A.K) :
    x ∈ outS hgen ↔ ∃ u ∈ U K, (x : MulAut (C K)) = MulAut.conj u := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, Subtype.ext hx.symm⟩

theorem mem_outI_iff (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) (i : ↥A.K) :
    i ∈ outI hgen ↔ ∃ u ∈ ({xa (1 : K), xu 1, xv 1, xb 1, xc 1} : Set (C K)),
      (i : MulAut (C K)) = MulAut.conj u := by
  constructor
  · intro hi
    simp only [outI, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact ⟨xa 1, by simp, rfl⟩
    · exact ⟨xu 1, by simp, rfl⟩
    · exact ⟨xv 1, by simp, rfl⟩
    · exact ⟨xb 1, by simp, rfl⟩
    · exact ⟨xc 1, by simp, rfl⟩
  · rintro ⟨u, hu, hi⟩
    have : i = iK A hgen u := Subtype.ext hi
    subst this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    simp only [outI, Finset.mem_insert, Finset.mem_singleton]
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp

end Objects

section Roots

variable {K : Type} [Field K]
  [CharP K 2]

theorem orderOf_xe_one (γ : Fin Tag.G2.rank → ℤ) : orderOf (xe γ (1 : K)) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact xe_mul_self γ 1)
    (fun h => one_ne_zero ((xe_eq_one_iff γ).1 h))

theorem mem_roots {u : C K} (hu : u ∈ ({xa (1 : K), xu 1, xv 1, xb 1, xc 1} : Set (C K))) :
    u ∈ U K ∧ orderOf u = 2 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl
  · exact ⟨xa_mem_U 1, orderOf_xe_one rA⟩
  · exact ⟨xu_mem_U 1, orderOf_xe_one rU⟩
  · exact ⟨xv_mem_U 1, orderOf_xe_one rV⟩
  · exact ⟨xb_mem_U 1, orderOf_xe_one rB⟩
  · exact ⟨xc_mem_U 1, orderOf_xe_one rC⟩

end Roots

end CFSG.Quasithin.H13.F431.G2.OutK
