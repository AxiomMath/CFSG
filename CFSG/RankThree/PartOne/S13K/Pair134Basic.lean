module

public import CFSG.RankThree.PartOne.S11d.Common
public import CFSG.RankThree.PartOne.Assembly

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne

theorem derivedSeries_eq_top_of_isPerfect {K : Type*} [Group K] (hK : Group.IsPerfect K) (n : ℕ) :
    derivedSeries K n = ⊤ := by
  induction n with
  | zero => exact derivedSeries_zero K
  | succ n ih =>
    rw [derivedSeries_succ, ih]
    exact hK.commutator_eq_top

theorem le_of_perfect_of_centralizes {H : Type*} [Group H] {K P N : Subgroup H}
    (hK : Group.IsPerfect ↥K) (hN : N.Normal) (hNs : Group.IsSolvable ↥N) (hKP : K ≤ P ⊔ N)
    (hc : K ≤ Subgroup.centralizer (N : Set H)) : K ≤ P := by
  classical
  have hcomm : ∀ (k : ↥K) (n : ↥N), Commute (K.subtype k) (N.subtype n) := fun k n =>
    ((Subgroup.mem_centralizer_iff.mp (hc k.2) n n.2)).symm
  let φ : ↥K × ↥N →* H := MonoidHom.noncommCoprod K.subtype N.subtype hcomm
  have hφ : ∀ k : ↥K, ∀ n : ↥N, φ (k, n) = (k : H) * n := fun k n => rfl
  let S : Subgroup (↥K × ↥N) := P.comap φ
  let π : ↥S →* ↥K := (MonoidHom.fst ↥K ↥N).comp S.subtype
  let ρ : ↥S →* ↥N := (MonoidHom.snd ↥K ↥N).comp S.subtype
  have hπ : Function.Surjective π := by
    intro k
    obtain ⟨y, hy, n, hn, hyn⟩ := Subgroup.mem_sup_of_normal_right.mp (hKP k.2)
    refine ⟨⟨(k, ⟨n⁻¹, N.inv_mem hn⟩), ?_⟩, rfl⟩
    show φ (k, ⟨n⁻¹, N.inv_mem hn⟩) ∈ P
    rw [hφ]
    have : (k : H) * n⁻¹ = y := by rw [← hyn]; group
    simp only [this]
    exact hy
  obtain ⟨m, hm⟩ := hNs.solvable
  have h1 : (derivedSeries ↥S m).map ρ ≤ ⊥ := by
    refine (map_derivedSeries_le_derivedSeries ρ m).trans (le_of_eq hm)
  have h2 : (derivedSeries ↥S m).map π = ⊤ := by
    rw [map_derivedSeries_eq hπ, derivedSeries_eq_top_of_isPerfect hK]
  intro k hk
  have hk' : (⟨k, hk⟩ : ↥K) ∈ (derivedSeries ↥S m).map π := by
    rw [h2]
    exact Subgroup.mem_top _
  obtain ⟨s, hs, hsk⟩ := Subgroup.mem_map.mp hk'
  have hs1 : ρ s = 1 := by
    have := h1 (Subgroup.mem_map_of_mem ρ hs)
    simpa using this
  have hs2 : (s : ↥K × ↥N) = (⟨k, hk⟩, 1) := by
    refine Prod.ext ?_ ?_
    · exact hsk
    · exact hs1
  have hsS : (s : ↥K × ↥N) ∈ S := s.2
  rw [hs2] at hsS
  have : φ (⟨k, hk⟩, 1) ∈ P := hsS
  rw [hφ] at this
  simpa using this

theorem le_of_sectionTenRel {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {K I J : Subgroup G} (hK : Group.IsPerfect ↥K) (hKI : K ≤ I)
    (hKθ : K ≤ Subgroup.centralizer (inSubgroup (aschbacherSolvableCore p) I : Set G))
    (hIJ : sectionTenRel p I J) : K ≤ J := by
  classical
  set N := inSubgroup (aschbacherSolvableCore p) I with hN
  obtain ⟨hNI, hNn⟩ := theta_le_and_normal p I
  obtain ⟨hNs, -⟩ := theta_solvable_and_not_dvd hp I
  have hsup : (I ⊓ J ⊔ N).subgroupOf I = (I ⊓ J).subgroupOf I ⊔ N.subgroupOf I :=
    Subgroup.subgroupOf_sup inf_le_left hNI
  have hIJ' : I = I ⊓ J ⊔ N := hIJ
  rw [← hIJ', Subgroup.subgroupOf_self] at hsup
  have hKperf : Group.IsPerfect ↥(K.subgroupOf I) := by
    have := hK
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKI).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hNsolv : Group.IsSolvable ↥(N.subgroupOf I) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNI).toMonoidHom)
      (MulEquiv.injective _)
  have hc : K.subgroupOf I ≤ Subgroup.centralizer (N.subgroupOf I : Set ↥I) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hKθ (Subgroup.mem_subgroupOf.mp hx)) y
      (Subgroup.mem_subgroupOf.mp hy)
  have hmain := le_of_perfect_of_centralizes hKperf hNn hNsolv
    (le_of_eq_of_le rfl (hsup ▸ le_top)) hc
  intro k hk
  have := hmain (Subgroup.mem_subgroupOf.mpr hk : (⟨k, hKI hk⟩ : ↥I) ∈ K.subgroupOf I)
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2

theorem centralizes_of_mem_theta_of_mem_normalizer {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {E : Subgroup G} (hE : IsElementaryAbelian p E) {e : G} (heE : e ∈ E) {y : G}
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hyθ : y ∈ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G))) :
    ∀ a ∈ E, y * a * y⁻¹ = a := by
  intro a ha
  set C := Subgroup.centralizer ({e} : Set G) with hC
  set θ := inSubgroup (aschbacherSolvableCore p) C with hθ
  obtain ⟨hθC, hθn⟩ := theta_le_and_normal p C
  obtain ⟨-, hθp⟩ := theta_solvable_and_not_dvd hp C
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hE.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨e, heE⟩))
  have hyC : y ∈ C := hθC hyθ
  have h1 : a * y⁻¹ * a⁻¹ ∈ θ := by
    have := hθn.conj_mem ⟨y⁻¹, C.inv_mem hyC⟩ (Subgroup.mem_subgroupOf.mpr (θ.inv_mem hyθ))
      ⟨a, haC⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hz : y * a * y⁻¹ * a⁻¹ ∈ θ := by
    have := θ.mul_mem hyθ h1
    simpa [mul_assoc] using this
  have hzE : y * a * y⁻¹ * a⁻¹ ∈ E := by
    have h2 : y * a * y⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hyN a).mp ha
    exact E.mul_mem h2 (E.inv_mem ha)
  have hzp : (y * a * y⁻¹ * a⁻¹) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ hzE
  have hord : orderOf (y * a * y⁻¹ * a⁻¹) = 1 := by
    have hdvdp : orderOf (y * a * y⁻¹ * a⁻¹) ∣ p := orderOf_dvd_of_pow_eq_one hzp
    rcases (Nat.dvd_prime hp).mp hdvdp with h | h
    · exact h
    · exfalso
      apply hθp
      have : orderOf (⟨y * a * y⁻¹ * a⁻¹, hz⟩ : ↥θ) ∣ Nat.card ↥θ := orderOf_dvd_natCard _
      rw [← Subgroup.orderOf_coe] at this
      simp only [h] at this
      exact this
  have hz1 : y * a * y⁻¹ * a⁻¹ = 1 := orderOf_eq_one_iff.mp hord
  exact mul_inv_eq_one.mp hz1

theorem commute_of_distinct_components {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElementaryAbelian p E) {e : G} (heE : e ∈ E) {I₁ I₂ : Subgroup G}
    (h1 : I₁ ∈ thetaComponentsAt p e) (h2 : I₂ ∈ thetaComponentsAt p e) (hne : I₁ ≠ I₂)
    {k₁ k₂ : G} (hk₁ : k₁ ∈ I₁) (hk₂ : k₂ ∈ I₂) (hn₁ : k₁ ∈ Subgroup.normalizer (E : Set G))
    (hn₂ : k₂ ∈ Subgroup.normalizer (E : Set G)) :
    E.normalizerMonoidHom ⟨k₁, hn₁⟩ * E.normalizerMonoidHom ⟨k₂, hn₂⟩ =
      E.normalizerMonoidHom ⟨k₂, hn₂⟩ * E.normalizerMonoidHom ⟨k₁, hn₁⟩ := by
  have hcomm := S11d.commutator_mem_theta_of_ne hp h1 h2 hne k₁ hk₁ k₂ hk₂
  have hzN : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)
  have hzc := centralizes_of_mem_theta_of_mem_normalizer hp hE heE hzN hcomm
  have hone : E.normalizerMonoidHom ⟨k₁ * k₂ * k₁⁻¹ * k₂⁻¹, hzN⟩ = 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    exact hzc a a.2
  have hprod : E.normalizerMonoidHom ⟨k₁ * k₂ * k₁⁻¹ * k₂⁻¹, hzN⟩ =
      E.normalizerMonoidHom ⟨k₁, hn₁⟩ * E.normalizerMonoidHom ⟨k₂, hn₂⟩ *
        (E.normalizerMonoidHom ⟨k₁, hn₁⟩)⁻¹ * (E.normalizerMonoidHom ⟨k₂, hn₂⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [hprod] at hone
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hone)

end CFSG.RankThree.PartOne.S13K
