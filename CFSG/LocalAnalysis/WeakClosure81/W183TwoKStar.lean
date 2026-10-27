module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoPerf
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoOdd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrbit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem w183b5_center_eq_bot {G : Type*} [Group G] {L : Subgroup G} {S : Type} [Group S]
    (e : ↥L ≃* S) (hZ : Subgroup.center S = ⊥) : Subgroup.center ↥L = ⊥ := by
  haveI : Subsingleton (Subgroup.center S) := by rw [hZ]; infer_instance
  haveI : Subsingleton (Subgroup.center ↥L) := (Subgroup.centerCongr e).toEquiv.subsingleton
  exact Subgroup.eq_bot_of_subsingleton (Subgroup.center ↥L)

private theorem w183b5_isQuasisimple_of_simple (S : Type*) [Group S] [IsSimpleGroup S]
    (hSnc : ∃ u v : S, u * v ≠ v * u) : CFSG.Open.IsQuasisimple S := by
  letI : Group.IsPerfect S :=
    ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top S hSnc⟩
  exact CFSG.ComponentClassification.Quasisimple.simple_of_perfect S

theorem kk_eq_bot_of_simple_subnormal {Y : Type} [Group Y] [Finite Y] {Kk P Λ : Subgroup Y}
    (hKn : Kk.Normal) (hPn : P.Normal) (hKP : Kk ≤ P)
    (hKc : Kk ≤ Subgroup.centralizer (P : Set Y))
    (hle : ∀ N : Subgroup Y, N.Normal → ¬ N ≤ Kk → P ≤ N) (hΛP : Λ ≤ P)
    (hΛs : Λ.IsSubnormal) (hΛk : Λ ⊓ Kk = ⊥) {S : Type} [Group S] [IsSimpleGroup S]
    (hSnc : ∃ u v : S, u * v ≠ v * u) (e : ↥Λ ≃* S) : Kk = ⊥ := by
  classical
  letI : Fintype Y := Fintype.ofFinite Y
  let A : Y → Subgroup Y := fun y => Λ.map (MulAut.conj y).toMonoidHom
  have hΛnle : ¬ Λ ≤ Kk := by
    intro hleKk
    have hbot : Λ = ⊥ := by rw [← inf_eq_left.mpr hleKk, hΛk]
    haveI : Nontrivial ↥Λ := e.toEquiv.nontrivial
    have hsub : Subsingleton ↥Λ := by rw [hbot]; infer_instance
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial ↥Λ).exists_pair_ne
    exact hab (Subsingleton.elim a b)
  have hNCnle : ¬ Subgroup.normalClosure (Λ : Set Y) ≤ Kk :=
    fun h => hΛnle ((Subgroup.le_normalClosure (H := Λ)).trans h)
  have hPleNC : P ≤ Subgroup.normalClosure (Λ : Set Y) := hle _ inferInstance hNCnle
  have hNCleP : Subgroup.normalClosure (Λ : Set Y) ≤ P := by
    haveI : P.Normal := hPn
    exact Subgroup.normalClosure_le_normal (fun x hx => hΛP hx)
  have hPeqNC : P = Subgroup.normalClosure (Λ : Set Y) := le_antisymm hPleNC hNCleP
  have hA_iso : ∀ y : Y, ↥(A y) ≃* S := fun y =>
    (Subgroup.equivMapOfInjective Λ ((MulAut.conj y).toMonoidHom)
      (MulAut.conj y).injective).symm.trans e
  have hAcomp : ∀ y : Y, CFSG.Open.IsComponentOf (A y) ⊤ := by
    intro y
    refine ⟨le_top, ?_, ?_⟩
    · exact CFSG.Open.IsSubnormal.top_iff.mpr
        (Subgroup.IsSubnormal.map (MulAut.conj y).surjective hΛs)
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv (hA_iso y)
        (w183b5_isQuasisimple_of_simple S hSnc)
  have hAleP : ∀ y : Y, A y ≤ P := by
    intro y x hx
    have hx' : x ∈ Λ.map (MulAut.conj y).toMonoidHom := hx
    rw [Subgroup.mem_map] at hx'
    obtain ⟨a, ha, rfl⟩ := hx'
    change y * a * y⁻¹ ∈ P
    exact hPn.conj_mem a (hΛP ha) y
  have hP_eq_iSup : P = ⨆ y, A y := by
    apply le_antisymm
    · rw [hPeqNC]
      change Subgroup.closure (Group.conjugatesOfSet (Λ : Set Y)) ≤ ⨆ y, A y
      rw [Subgroup.closure_le]
      rintro x hx
      rw [Group.mem_conjugatesOfSet_iff] at hx
      obtain ⟨a, ha, hconj⟩ := hx
      rw [isConj_iff] at hconj
      obtain ⟨c, rfl⟩ := hconj
      exact Subgroup.mem_iSup_of_mem c (by
        rw [Subgroup.mem_map]
        exact ⟨a, ha, rfl⟩)
    · exact iSup_le hAleP
  let F : Finset (Subgroup Y) := Finset.univ.image A
  have hFmem : ∀ L ∈ F, ∃ y : Y, A y = L := by
    intro L hL
    change L ∈ Finset.univ.image A at hL
    rw [Finset.mem_image] at hL
    simpa using hL
  have hF_eq_iSup : (⨆ L ∈ F, L) = ⨆ y, A y := by
    change (⨆ L ∈ Finset.univ.image A, L) = ⨆ y, A y
    rw [Finset.iSup_finset_image]
    simp
  have hZ : ∀ L ∈ F, Subgroup.center ↥L = ⊥ := by
    intro L hL
    obtain ⟨y, rfl⟩ := hFmem L hL
    exact w183b5_center_eq_bot (hA_iso y)
      (CFSG.ComponentClassification.Helpers.center_eq_bot S hSnc)
  have hcomm : ∀ L ∈ F, ∀ M ∈ F, L ≠ M → ⁅L, M⁆ = ⊥ := by
    intro L hL M hM hne
    obtain ⟨c, rfl⟩ := hFmem L hL
    obtain ⟨d, rfl⟩ := hFmem M hM
    exact CFSG.ComponentClassification.LocalComponents.commute_of_ne (A c) (A d)
      (hAcomp c) (hAcomp d) hne
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  have hkP : k ∈ P := hKP hk
  have hk_iSup : k ∈ ⨆ L ∈ F, L := by
    rw [hF_eq_iSup, ← hP_eq_iSup]
    exact hkP
  have hk_cent : ∀ y ∈ ⨆ L ∈ F, L, k * y = y * k := by
    intro y hy
    have hyP : y ∈ P := by rw [hF_eq_iSup, ← hP_eq_iSup] at hy; exact hy
    exact (Subgroup.mem_centralizer_iff.mp (hKc hk) y hyP).symm
  exact CFSG.ComponentClassification.GSThmB.eq_one_of_mem_iSup_of_commute F hZ hcomm hk_iSup
    hk_cent

theorem kk_eq_bot_of_component (hM : OddMultiplier186Triv) {Y : Type} [Group Y] [Finite Y]
    {Kk P Lc : Subgroup Y} (hKn : Kk.Normal) (hPn : P.Normal) (hKP : Kk ≤ P)
    (hKc : Kk ≤ Subgroup.centralizer (P : Set Y)) (hodd : Odd (Nat.card ↥Kk))
    (h2q : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ P)
    (hle : ∀ N : Subgroup Y, N.Normal → ¬ N ≤ Kk → P ≤ N) (hLsub : Lc.IsSubnormal) {S : Type}
    [Group S] [IsSimpleGroup S] (hSnc : ∃ u v : S, u * v ≠ v * u) (hS : Shape186OddTriv S)
    (φ : ↥Lc →* S) (hφs : Function.Surjective φ) (hφk : ∀ k : ↥Lc, φ k = 1 ↔ (k : Y) ∈ Kk) :
    Kk = ⊥ := by
  obtain ⟨Λ, hΛs, hΛL, hΛk, ⟨e⟩⟩ := exists_simple_subnormal_of_section hM hKP hKc hodd
    (le_of_simple_section hKP hPn h2q hSnc φ hφs hφk) hLsub hSnc hS φ hφs hφk
  exact kk_eq_bot_of_simple_subnormal hKn hPn hKP hKc hle
    (hΛL.trans (le_of_simple_section hKP hPn h2q hSnc φ hφs hφk)) hΛs hΛk hSnc e

end CFSG.LocalAnalysis.WeakClosure81

end
