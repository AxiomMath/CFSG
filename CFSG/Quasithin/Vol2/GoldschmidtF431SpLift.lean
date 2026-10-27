module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

section Transport

variable {D H : Type*} [Group D] [Group H] (Φ : D →* H)

theorem pCoreOf_map_of_injective (hΦ : Function.Injective Φ) (X : Subgroup D) :
    pCoreOf 2 (X.map Φ) = (pCoreOf 2 X).map Φ := by
  let e : ↥X ≃* ↥(X.map Φ) := Subgroup.equivMapOfInjective X Φ hΦ
  have h1 := map_pCore_mulEquiv 2 e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem perfectCore_map_of_injective (hΦ : Function.Injective Φ) (X : Subgroup D) :
    perfectCore (X.map Φ) = (perfectCore X).map Φ := by
  unfold perfectCore
  rw [Subgroup.map_iInf Φ hΦ]
  congr 1
  funext n
  exact (map_derivedSeriesOf Φ X n).symm

theorem centerOf_map_of_injective (hΦ : Function.Injective Φ) (X : Subgroup D) :
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

theorem isSylowTwoOf_map_of_odd (hΦ : Function.Injective Φ) (hodd : Odd Φ.range.index)
    {U : Subgroup D} (hU : IsSylowTwoOf U ⊤) : IsSylowTwoOf (U.map Φ) ⊤ := by
  obtain ⟨-, hp, hidx⟩ := hU
  refine ⟨le_top, hp.map Φ, ?_⟩
  have e : ∀ V : Subgroup D, (V.subgroupOf ⊤).index = V.index := fun V =>
    Subgroup.relIndex_top_right V
  have e' : ∀ V : Subgroup H, (V.subgroupOf ⊤).index = V.index := fun V =>
    Subgroup.relIndex_top_right V
  rw [e] at hidx
  rw [e', Subgroup.index_map_of_injective U hΦ]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
  · exact hidx h
  · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

end Transport

section OddIndex

variable {H : Type*} [Group H] [Finite H] {Inn : Subgroup H} [Inn.Normal]

omit [Finite H] in
theorem mem_of_pow_two_pow_eq_one (hodd : Odd Inn.index) {x : H} {k : ℕ} (hx : x ^ (2 ^ k) = 1) :
    x ∈ Inn := by
  have h1 : orderOf (QuotientGroup.mk x : H ⧸ Inn) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hx]
    rfl
  have h2 : orderOf (QuotientGroup.mk x : H ⧸ Inn) ∣ Inn.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) Inn.index :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 : orderOf (QuotientGroup.mk x : H ⧸ Inn) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

theorem pCoreOf_le_of_odd (N : Subgroup H) (hodd : Odd Inn.index) : pCoreOf 2 N ≤ Inn := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hp := pCoreOf_isPGroup 2 N
  obtain ⟨k, hk⟩ := hp ⟨x, hx⟩
  exact mem_of_pow_two_pow_eq_one hodd (k := k) (congrArg Subtype.val hk)

omit [Finite H] in
theorem le_normalizer_inf_normal (N : Subgroup H) :
    N ≤ Subgroup.normalizer ((N ⊓ Inn : Subgroup H) : Set H) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxN, hxI⟩
    exact ⟨N.mul_mem (N.mul_mem hn hxN) (N.inv_mem hn),
      Subgroup.Normal.conj_mem inferInstance x hxI n⟩
  · rintro ⟨hxN, hxI⟩
    refine ⟨?_, ?_⟩
    · have := N.mul_mem (N.mul_mem (N.inv_mem hn) hxN) hn
      simpa [mul_assoc] using this
    · have := Subgroup.Normal.conj_mem inferInstance _ hxI n⁻¹
      simpa [mul_assoc] using this

theorem pCoreOf_eq_inf_of_odd (N : Subgroup H) (hodd : Odd Inn.index) :
    pCoreOf 2 N = pCoreOf 2 (N ⊓ Inn) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine le_pCoreOf 2 (le_inf (pCoreOf_le 2 N) (pCoreOf_le_of_odd N hodd)) ?_
      (pCoreOf_isPGroup 2 N)
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (inf_le_left.trans (le_normalizer_pCoreOf 2 N))
  · refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans inf_le_left)
      ((le_normalizer_inf_normal (Inn := Inn) N).trans
        (normalizer_le_normalizer_pCoreOf 2 (N ⊓ Inn))) ?_
    exact pCoreOf_isPGroup 2 (N ⊓ Inn)

theorem perfectCore_eq_inf_of_odd (N : Subgroup H) (hodd : Odd Inn.index) :
    perfectCore N = perfectCore (N ⊓ Inn) := by
  apply le_antisymm
  · have hq : Odd (Nat.card (↥N ⧸ Inn.subgroupOf N)) := by
      rw [← Subgroup.index_eq_card]
      exact Odd.of_dvd_nat hodd (Subgroup.relIndex_dvd_index_of_normal Inn N)
    have : Finite (↥N ⧸ Inn.subgroupOf N) := inferInstance
    obtain ⟨ℓ, hℓ⟩ := (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hq).solvable
    have hle : derivedSeriesOf N ℓ ≤ N ⊓ Inn := by
      have h1 : (derivedSeries ↥N ℓ).map (QuotientGroup.mk' (Inn.subgroupOf N)) = ⊥ := by
        rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective _), hℓ]
      have h2 : derivedSeries ↥N ℓ ≤ Inn.subgroupOf N := by
        intro x hx
        have : QuotientGroup.mk' (Inn.subgroupOf N) x = 1 := by
          have := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Inn.subgroupOf N)) hx
          rwa [h1, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff x).mp this
      rw [derivedSeriesOf_eq_map_derivedSeries]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.2, Subgroup.mem_subgroupOf.mp (h2 hx)⟩
    have key : ∀ m, derivedSeriesOf N (ℓ + m) ≤ derivedSeriesOf (N ⊓ Inn) m := by
      intro m
      induction m with
      | zero => exact hle
      | succ m ih =>
        rw [← add_assoc, derivedSeriesOf_succ, derivedSeriesOf_succ]
        exact Subgroup.commutator_mono ih ih
    exact le_iInf fun m => (perfectCore_le_derivedSeriesOf N (ℓ + m)).trans (key m)
  · exact perfectCore_mono inf_le_left

theorem conj_mem_centerOf_perfectCore {G : Type*} [Group G] {M : Subgroup G} {n z : G}
    (hn : n ∈ M) (hz : z ∈ centerOf (perfectCore M)) :
    n * z * n⁻¹ ∈ centerOf (perfectCore M) := by
  obtain ⟨hzP, hzc⟩ := hz
  have hnorm := perfectCore_normal M
  have hP : ∀ {m : G}, m ∈ M → ∀ {w : G}, w ∈ perfectCore M → m * w * m⁻¹ ∈ perfectCore M := by
    intro m hm w hw
    have := hnorm.conj_mem ⟨w, perfectCore_le M hw⟩ (Subgroup.mem_subgroupOf.mpr hw) ⟨m, hm⟩
    simpa using Subgroup.mem_subgroupOf.mp this
  refine ⟨hP hn hzP, ?_⟩
  show n * z * n⁻¹ ∈ Subgroup.centralizer ((perfectCore M : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 : n⁻¹ * w * n⁻¹⁻¹ ∈ perfectCore M := hP (M.inv_mem hn) hw
  have h2 := Subgroup.mem_centralizer_iff.mp hzc _ h1
  calc w * (n * z * n⁻¹) = n * ((n⁻¹ * w * n) * z) * n⁻¹ := by group
    _ = n * (z * (n⁻¹ * w * n)) * n⁻¹ := by
      rw [show n⁻¹ * w * n = n⁻¹ * w * n⁻¹⁻¹ by group, h2]
    _ = n * z * n⁻¹ * w := by group

end OddIndex

end CFSG.Quasithin.H13.F431
