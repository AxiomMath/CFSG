module

public import CFSG.RankThree.PartOne.S11c.Sec66TDefs
public import CFSG.RankThree.CentralCover.SteinbergBNLinearSplitPrime
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)

namespace OddRank

theorem isElementaryAbelian_of_isElemAbelian {Y : Type*} [Group Y] {p : ℕ} {V : Subgroup Y}
    (h : CFSG.Assembly.IsElemAbelian p V) : CFSG.IsElementaryAbelian p V :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h

theorem not_localRankLeTwo_of_involution {T : Type} [Group T] [Finite T] {p r : ℕ} (hp : p.Prime)
    (hr : 3 ≤ r) {u : T} (hu : orderOf u = 2) {V : Subgroup T}
    (hVu : V ≤ Subgroup.centralizer ({u} : Set T)) (hV : CFSG.IsElementaryAbelian p V)
    (hVcard : Nat.card V = p ^ r) : ¬ LocalRankLeTwo p T := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro hrank
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := V) p (n := 3)
    (by rw [hVcard]; exact pow_dvd_pow p hr)
  set R : Subgroup T := K.map V.subtype with hR
  have hRcard : Nat.card R = p ^ 3 := by
    rw [hR, Subgroup.card_map_of_injective V.subtype_injective, hK]
  have hRV : R ≤ V := Subgroup.map_subtype_le K
  have hRab : CFSG.IsElementaryAbelian p R := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      have h1 := hV.is_comm.comm (⟨(a : T), hRV a.2⟩ : V) ⟨(b : T), hRV b.2⟩
      exact congrArg (fun x : V => (x : T)) h1
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
      apply Subtype.ext
      have h1 : (⟨(x : T), hRV x.2⟩ : V) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p V)
          ⟨(x : T), hRV x.2⟩
      simpa using congrArg (fun y : V => (y : T)) h1
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    omega
  have hU2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  refine hrank R hRab hRcard (Subgroup.zpowers u) ?_ hU2 ?_
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · intro x hx
    have hxC := hVu (hRV hx)
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure] at hxC
    exact Subgroup.centralizer_le_normalizer _ hxC

theorem not_localRankLeTwo_psl_odd {T : Type} [Group T] [Finite T] {p n ℓ f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hℓ2 : ℓ ≠ 2) (hmod : StatedClassicalModel T .PSL n ℓ f)
    (hpn : p ∣ n) (hpq : p ∣ ℓ ^ f - 1) : ¬ LocalRankLeTwo p T := by
  classical
  obtain ⟨⟨hℓ, hf, hn2, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hn5 : 5 ≤ n := by
    have h1 : p ≤ n := Nat.le_of_dvd (by omega) hpn
    have h5 : 5 ≤ p := by
      by_contra h
      have h4 : p = 4 := by omega
      subst h4
      norm_num at hp
    omega
  have := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hchar : CharP k ℓ := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hk])
  have hpk : p ∣ Fintype.card k - 1 := by rwa [← Nat.card_eq_fintype_card, hk]
  let ψ : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let φ : (⊤ : Subgroup T) →* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    ψ.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom
  have hφs : Function.Surjective φ := ψ.surjective.comp Subgroup.topEquiv.surjective
  have hker : φ.ker ≤ Subgroup.center (⊤ : Subgroup T) := by
    intro x hx
    have hx' : φ x = 1 := hx
    have : x = 1 := (ψ.injective.comp Subgroup.topEquiv.injective) (by
      simpa [φ] using hx')
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨u, -, hu, V, hV, hVab, hVcard, -⟩ :=
    CFSG.RankThree.CentralCover.linear_split_prime_central_cover_two_local_rank (⊤ : Subgroup T)
      hℓ hp hp3 hpk (by omega) φ hφs hker
  have hr : (if ℓ = 2 then n - 2 - (if p ∣ n then 1 else 0) else
      n - 1 - (if p ∣ n then 1 else 0)) = n - 2 := by
    simp only [hpn, hℓ2, ↓reduceIte]
    omega
  rw [hr] at hVcard
  exact not_localRankLeTwo_of_involution hp (by omega) hu (le_inf_iff.mp hV).2
    (isElementaryAbelian_of_isElemAbelian hVab) hVcard

theorem not_localRankLeTwo_psu_odd {T : Type} [Group T] [Finite T] {p n ℓ f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hℓ2 : ℓ ≠ 2) (hmod : StatedClassicalModel T .PSU n ℓ f)
    (hpn : p ∣ n) (hpq : p ∣ ℓ ^ f + 1) : ¬ LocalRankLeTwo p T := by
  classical
  obtain ⟨⟨hℓ, hf, hn3, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hn5 : 5 ≤ n := by
    have h1 : p ≤ n := Nat.le_of_dvd (by omega) hpn
    have h5 : 5 ≤ p := by
      by_contra h
      have h4 : p = 4 := by omega
      subst h4
      norm_num at hp
    omega
  have hU : UnitaryFieldData ℓ f k := ⟨hℓ, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  let ψ : T ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  let φ : (⊤ : Subgroup T) →* unitaryPSU hU n := ψ.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom
  have hφs : Function.Surjective φ := ψ.surjective.comp Subgroup.topEquiv.surjective
  have hker : φ.ker ≤ Subgroup.center (⊤ : Subgroup T) := by
    intro x hx
    have hx' : φ x = 1 := hx
    have : x = 1 := (ψ.injective.comp Subgroup.topEquiv.injective) (by
      simpa [φ] using hx')
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨u, -, hu, V, hV, hVab, hVcard⟩ :=
    CFSG.RankThree.Classical2.unitary_split_prime_central_cover_two_local_rank (⊤ : Subgroup T)
      hU hp hp3 hpq (by omega) φ hφs hker
  have hr : (if ℓ = 2 then n - 2 - (if p ∣ n then 1 else 0) else
      n - 1 - (if p ∣ n then 1 else 0)) = n - 2 := by
    simp only [hpn, hℓ2, ↓reduceIte]
    omega
  have hVcard' : Nat.card V = p ^ (n - 2) := by rw [← hr]; exact hVcard
  exact not_localRankLeTwo_of_involution hp (by omega) hu (le_inf_iff.mp hV).2
    (isElementaryAbelian_of_isElemAbelian hVab) hVcard'

end OddRank

end CFSG.RankThree.PartOne
