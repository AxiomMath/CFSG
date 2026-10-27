module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rg
public import CFSG.Foundations.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22p22r_isSylowOf_map_top {p : ℕ} [Fact p.Prime] {A B : Type} [Group A] [Finite A] [Group B]
    {f : A →* B} (hf : Function.Surjective f) {T : Subgroup A}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T ⊤) : CFSG.ABGLocalTools.IsSylowOf p (T.map f) ⊤ := by
  haveI : Finite B := Finite.of_surjective f hf
  obtain ⟨-, hpg, hndvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hT
  rw [Subgroup.relIndex_top_right] at hndvd
  let S : Sylow p A := hpg.toSylow hndvd
  have hS : (S : Subgroup A) = T := rfl
  have hSm : ((S.mapSurjective hf : Sylow p B) : Subgroup B) = T.map f := by
    rw [Sylow.coe_mapSurjective, hS]
  refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_top, hpg.map f, ?_⟩
  rw [Subgroup.relIndex_top_right, ← hSm]
  exact (S.mapSurjective hf).not_dvd_index

theorem uc22p22r_normalizes {Hg : Type} [Group Hg] [Finite Hg] {q : ℕ} (hq : q.Prime) {x : Hg}
    (hx : orderOf x = q) {T M K : Subgroup Hg} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTM : T ≤ M)
    (hxM : x ∈ M) (hR : CFSG.solvableRadical Hg ≤ M) (hU : ∀ h : Hg, h⁻¹ * x * h ∈ M → h ∈ M)
    (hKp : Group.IsPerfect K) (hKs : K.IsSubnormal) {N : Subgroup ↥K} [hNn : N.Normal]
    (hNR : ∀ n ∈ N, (n : Hg) ∈ CFSG.solvableRadical Hg) (hNq : CFSG.Open.IsQuasisimple (↥K ⧸ N))
    (hKM : ¬ K ≤ M) : x ∈ normalizer (K : Set Hg) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set R := CFSG.solvableRadical Hg with hRdef
  haveI hRn : R.Normal := CFSG.SignalizerFunctorTheorem.Nonsolvable.instNormalSolvableRadical
  haveI hRs : Group.IsSolvable ↥R :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  set π : Hg →* Hg ⧸ R := QuotientGroup.mk' R with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hker : π.ker = R := QuotientGroup.ker_mk' R
  have h0 : ∀ Y : Subgroup Hg, x ∈ Y → Y ≤ M → ∀ n ∈ normalizer (Y : Set Hg), n ∈ M := by
    intro Y hxY hYM n hn
    apply hU
    apply hYM
    have hn' : n⁻¹ ∈ normalizer (Y : Set Hg) := Subgroup.inv_mem _ hn
    have h1 := (Subgroup.mem_normalizer_iff.1 hn' x).1 hxY
    simpa using h1
  have hlift : ∀ h : Hg, π h ∈ centralizer ({π x} : Set (Hg ⧸ R)) → h ∈ M := by
    intro h hh
    set Y : Subgroup Hg := (Subgroup.zpowers (π x)).comap π with hY
    have hxY : x ∈ Y := Subgroup.mem_zpowers _
    have hYM : Y ≤ M := by
      intro y hy
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hyR : (x ^ i)⁻¹ * y ∈ R := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hi, inv_mul_cancel]
      have hy' : y = x ^ i * ((x ^ i)⁻¹ * y) := by group
      rw [hy']
      exact M.mul_mem (M.zpow_mem hxM i) (hR hyR)
    have hhN : h ∈ normalizer (Y : Set Hg) := by
      apply Subgroup.mem_normalizer_fintype
      intro n hn
      have hn' : π n ∈ Subgroup.zpowers (π x) := hn
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hn'
      have hcomm : π h * π n = π n * π h := by
        rw [← hi]
        exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 hh) i).eq
      show π (h * n * h⁻¹) ∈ Subgroup.zpowers (π x)
      rw [map_mul, map_mul, map_inv, hcomm, mul_inv_cancel_right]
      exact hn'
    exact h0 Y hxY hYM h hhN
  have hπx : orderOf (π x) = q := by
    have hdvd : orderOf (π x) ∣ q := by
      rw [← hx]
      exact orderOf_map_dvd π x
    rcases (Nat.dvd_prime hq).1 hdvd with h1 | h1
    · exfalso
      have h2 : π x = 1 := orderOf_eq_one_iff.1 h1
      have hxR : x ∈ R := by
        rw [← hker]
        exact h2
      apply hKM
      intro k _
      apply hU k
      have h3 := hRn.conj_mem x hxR k⁻¹
      simpa using hR h3
    · exact h1
  set κ : Subgroup (Hg ⧸ R) := K.map π with hκdef
  have hκc : IsComponentOf κ ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact CFSG.Open.IsSubnormal.of_mathlib (hKs.map hπsurj)
    · let φ : ↥K ⧸ N →* Hg ⧸ R := QuotientGroup.lift N (π.comp K.subtype) (fun n hn => by
        show π (n : Hg) = 1
        rw [← MonoidHom.mem_ker, hker]
        exact hNR n hn)
      have hrange : φ.range = κ := by
        ext y
        constructor
        · rintro ⟨z, rfl⟩
          obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
          exact ⟨k, k.2, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨QuotientGroup.mk ⟨k, hk⟩, rfl⟩
      have hkerφ : φ.ker ≠ ⊤ := by
        intro htop
        apply hKM
        intro k hk
        have h1 : φ (QuotientGroup.mk ⟨k, hk⟩) = 1 := by
          rw [← MonoidHom.mem_ker, htop]
          exact Subgroup.mem_top _
        have h2 : π k = 1 := h1
        have h3 : k ∈ R := by
          rw [← hker]
          exact h2
        exact hR h3
      have hq' := CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hNq φ hkerφ
      rw [hrange] at hq'
      exact hq'
  have hκM : ¬ κ ≤ M.map π := by
    intro h
    apply hKM
    intro k hk
    obtain ⟨m, hm, hmk⟩ := h ⟨k, hk, rfl⟩
    have hmR : m⁻¹ * k ∈ R := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hmk, inv_mul_cancel]
    have hk' : k = m * (m⁻¹ * k) := by group
    rw [hk']
    exact M.mul_mem hm (hR hmR)
  have hFO := uc22p22r_free_orbit hq (π x) hπx (T := T.map π) (M := M.map π)
    (uc22p22r_isSylowOf_map_top hπsurj hT) (Subgroup.map_mono hTM) ⟨x, hxM, rfl⟩
    (fun y hy => by
      obtain ⟨h, rfl⟩ := hπsurj y
      exact ⟨h, hlift h hy, rfl⟩) hκc hκM
  have hcomap : κ.comap π = K ⊔ R := by
    rw [hκdef, Subgroup.comap_map_eq, hker]
  have hxKR : x ∈ normalizer ((K ⊔ R : Subgroup Hg) : Set Hg) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    have hn' : π n ∈ κ := by
      have : n ∈ κ.comap π := by
        rw [hcomap]
        exact hn
      exact this
    have h1 : π x * π n * (π x)⁻¹ ∈ κ := (Subgroup.mem_normalizer_iff.1 hFO _).1 hn'
    have h2 : x * n * x⁻¹ ∈ κ.comap π := by
      show π (x * n * x⁻¹) ∈ κ
      rw [map_mul, map_mul, map_inv]
      exact h1
    rw [hcomap] at h2
    exact h2
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_sup_le_normalizer hKp hKs hRn hRs hxKR

end CFSG.LocalAnalysis.UniquenessCase.UC22
