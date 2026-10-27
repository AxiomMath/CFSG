module

public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.EmptyFaithful.S146Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

variable {T M : Subgroup G}

theorem Setting146.isSQTKTC_of_pCoreOf_ne_bot (S : Setting146 G T M) {I : Subgroup G}
    (hI : pCoreOf 2 I ≠ ⊥) : IsSQTKTC I :=
  ⟨kGroup_of_pCoreOf_ne_bot S.hyp1281.qtke S.hyp1281.simple S.hyp1281.nonabelian hI,
    stronglyQuasithin_of_pCoreOf_ne_bot S.hyp1281.qtke hI⟩

theorem Setting146.obs_a (S : Setting146 G T M) {H : Subgroup G} {u : G} (hu : IsInvU T M H u)
    (hidx : (tU T u).relIndex (tZero T u) = 2)
    (hN0 : Subgroup.normalizer (tZero T u : Set G) = T)
    (hNu : Subgroup.normalizer (tU T u : Set G) = tZero T u) {I : Subgroup G}
    (hI : IsIStar T M u I) {X : Subgroup G} (hXS : X ≤ T ⊓ I) (hX1 : X ≠ ⊥)
    (hXI : I ≤ Subgroup.normalizer (X : Set G)) :
    IsIStar T M u (Subgroup.normalizer (X : Set G)) ∧
      T ⊓ Subgroup.normalizer (X : Set G) = T ⊓ I ∧
      IsSylowTwoOf (T ⊓ I) (Subgroup.normalizer (X : Set G)) := by
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hXO : X ≤ pCoreOf 2 (Subgroup.normalizer (X : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (hT2.to_le (hXS.trans inf_le_left))
  have hO : pCoreOf 2 (Subgroup.normalizer (X : Set G)) ≠ ⊥ := fun h =>
    hX1 (le_bot_iff.mp (hXO.trans h.le))
  obtain ⟨hJ, hTJ⟩ := hI.of_le hXI hO
  refine ⟨hJ, hTJ, ?_⟩
  have := (isIStar_sylow_cases S hu hidx hN0 hNu hJ).1
  rwa [hTJ] at this

theorem Setting146.mcOf_eq_centralizer (S : Setting146 G T M) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    mcOf T = Subgroup.centralizer ({z} : Set G) := by
  ext x
  constructor
  · intro hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Subgroup.mem_centralizer_iff.mp hx z hz
  · intro hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    by_cases hy1 : y = 1
    · simp [hy1]
    · have hyz : y = z := S.Z_eq_of_iff hy hz ⟨fun h => absurd h hy1, fun h => absurd h hz1⟩
      subst hyz
      exact Subgroup.mem_centralizer_iff.mp hx y rfl

theorem exists_sq_mem_normalizer_of_lt {A S₀ : Subgroup G} (hS : IsPGroup 2 S₀) (hA : A < S₀) :
    ∃ r ∈ S₀, r ∉ A ∧ r ∈ Subgroup.normalizer (A : Set G) ∧ r ^ 2 ∈ A := by
  classical
  obtain ⟨x, hxS, hxA, hxN⟩ := exists_mem_normalizer_of_lt_isPGroup hS hA
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨x, hxS⟩
  have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_coe (⟨x, hxS⟩ : S₀)).trans hk
  have hex : ∃ j, x ^ (2 ^ j) ∈ A := ⟨k, by rw [← hk', pow_orderOf_eq_one]; exact A.one_mem⟩
  have hspec := Nat.find_spec hex
  have hmin := fun m => Nat.find_min hex (m := m)
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hspec
    exact hxA hspec
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hnot : x ^ (2 ^ j) ∉ A := hmin j (by omega)
  refine ⟨x ^ (2 ^ j), S₀.pow_mem hxS _, hnot, Subgroup.pow_mem _ hxN _, ?_⟩
  have : (x ^ (2 ^ j)) ^ 2 = x ^ (2 ^ Nat.find hex) := by
    rw [hj, ← pow_mul, pow_succ]
  rw [this]
  exact hspec

theorem pCoreOf_le_of_eq_pCoreOf_normalizer {H R : Subgroup G} (hRH : R ≤ H)
    (hR : R = pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G))) : pCoreOf 2 H ≤ R := by
  set Q := pCoreOf 2 H with hQ
  have hR2 : IsPGroup 2 R := by rw [hR]; exact pCoreOf_isPGroup 2 _
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 H
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := hRH.trans (le_normalizer_pCoreOf 2 H)
  have hP2 : IsPGroup 2 (R ⊔ Q : Subgroup G) := hR2.to_sup_of_normal_right' hQ2 hRQ
  have hQN : Q ⊓ Subgroup.normalizer (R : Set G) ≤ R := by
    have hle : Q ⊓ Subgroup.normalizer (R : Set G) ≤
        pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) := by
      refine le_pCoreOf_of_le_normalizer 2
        (le_inf (inf_le_left.trans (pCoreOf_le 2 H)) inf_le_right) ?_ (hQ2.to_le inf_le_left)
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pCoreOf 2 H hg.1, Subgroup.le_normalizer hg.2⟩
    rw [← hR] at hle
    exact hle
  by_contra hQR
  have hlt : R < R ⊔ Q := lt_of_le_of_ne le_sup_left fun h => hQR (sup_eq_left.mp h.symm)
  obtain ⟨x, hxP, hxR, hxN⟩ := exists_mem_normalizer_of_lt_isPGroup hP2 hlt
  have hx' : x ∈ ((R ⊔ Q : Subgroup G) : Set G) := hxP
  rw [Subgroup.coe_mul_of_left_le_normalizer_right R Q hRQ] at hx'
  obtain ⟨r, hr, q, hq, rfl⟩ := hx'
  have hqN : q ∈ Subgroup.normalizer (R : Set G) := by
    have h1 : r⁻¹ ∈ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer (R.inv_mem hr)
    have := Subgroup.mul_mem _ h1 hxN
    simpa using this
  exact hxR (R.mul_mem hr (hQN ⟨hq, hqN⟩))


end CFSG.Quasithin
