module

public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.Classical2 CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

section Helpers

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem dicksonHom_eq_one_of_mem_orthDerived (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ orthDerived Q) :
    dicksonHom Q hQ ⟨g, orthDerived_le_orthogonalGroup hg⟩ = 1 := by
  have hle : orthDerived Q ≤
      (dicksonHom Q hQ).ker.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    refine ⟨⁅(⟨a, ha⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.mp (hle hg)
  have : g' = ⟨g, orthDerived_le_orthogonalGroup hg⟩ := Subtype.ext hgg'
  rw [← this]
  exact hg'

end Helpers

section Binary

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.commute_fixed_of_mem_orthDerived (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) (hQ : Q.polarBilin.Nondegenerate) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (hdim : finrank K (fixedSpace x) = 2)
    {m w₀ : V ≃ₗ[K] V} (hm : m ∈ isometryCentralizer Q x) (hmΩ : m ∈ orthDerived Q)
    (hw : w₀ ∈ supportedBlock Q x (X - 1)) (hwp : w₀ ^ p = 1) : m * w₀ = w₀ * m := by
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hwM : w₀ ∈ isometryCentralizer Q x := supportedBlock_le_isometryCentralizer _ hw
  have h1 : dicksonCentralizer Q x hQ ⟨m, hm⟩ = 1 :=
    dicksonHom_eq_one_of_mem_orthDerived hQ hmΩ
  have h2 := DFunLike.congr_fun (hx.dicksonCentralizer_eq_dicksonFixed hp2 hQ hRep) ⟨m, hm⟩
  rw [h1] at h2
  have hδm : dicksonHom (Q.comp (fixedSpace x).subtype) hQW
      ⟨isometryRestrictFixed Q x ⟨m, hm⟩, isometryRestrictFixed_mem_orthogonalGroup _⟩ = 1 :=
    h2.symm
  have hδw : dicksonHom (Q.comp (fixedSpace x).subtype) hQW
      ⟨isometryRestrictFixed Q x ⟨w₀, hwM⟩, isometryRestrictFixed_mem_orthogonalGroup _⟩ = 1 := by
    refine dicksonHom_eq_one_of_pow_eq_one hQW hp2 ?_
    refine Subtype.ext ?_
    show (isometryRestrictFixed Q x ⟨w₀, hwM⟩) ^ p = 1
    rw [← map_pow]
    have : (⟨w₀, hwM⟩ : ↥(isometryCentralizer Q x)) ^ p = 1 := Subtype.ext hwp
    rw [this, map_one]
  have hcomm := commute_of_dicksonHom_eq_one hQW hdim
    (isometryRestrictFixed_mem_orthogonalGroup ⟨m, hm⟩)
    (isometryRestrictFixed_mem_orthogonalGroup ⟨w₀, hwM⟩) hδm hδw
  have hmc : m ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hm).2
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
  have hmr : m r ∈ othersSpace x.toLinearMap (X - 1) := mem_othersSpace_of_apply hmc hr
  have hw1 := (mem_supportedBlock.mp hw).2 r hr
  have hw2 := (mem_supportedBlock.mp hw).2 _ hmr
  have hcu := congrArg (fun φ : fixedSpace x ≃ₗ[K] fixedSpace x => (φ ⟨u, hu⟩ : V)) hcomm
  show m (w₀ (u + r)) = w₀ (m (u + r))
  simp only [map_add, hw1, hw2]
  exact congrArg (· + m r) hcu

end Binary

section PCore

theorem mem_pCoreOf_of_central {G : Type*} [Group G] {p : ℕ} {N : Subgroup G} {w : G}
    (hwN : w ∈ N) (hc : ∀ n ∈ N, w * n = n * w) (hw : w ^ p = 1) :
    w ∈ CFSG.Assembly.pCoreOf p N := by
  refine Subgroup.mem_map.mpr ⟨⟨w, hwN⟩, ?_, rfl⟩
  let P : Subgroup ↥N := Subgroup.zpowers ⟨w, hwN⟩
  have hcomm : ∀ (n : ↥N) (k : ℤ), (⟨w, hwN⟩ : ↥N) ^ k * n = n * (⟨w, hwN⟩ : ↥N) ^ k := by
    intro n k
    have h1 : Commute (⟨w, hwN⟩ : ↥N) n := Subtype.ext (hc n n.2)
    exact (h1.zpow_left k).eq
  have hPn : P.Normal := by
    refine ⟨fun t ht g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [← hcomm g k, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hPp : IsPGroup p P := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine Subtype.ext ?_
    show (g : ↥N) ^ p ^ 1 = 1
    rw [pow_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : (⟨w, hwN⟩ : ↥N) ^ p = 1 := Subtype.ext hw
    rw [this, one_zpow]
  rw [CFSG.pCore_eq_iSup]
  exact Subgroup.mem_iSup_of_mem P (Subgroup.mem_iSup_of_mem hPn
    (Subgroup.mem_iSup_of_mem hPp (Subgroup.mem_zpowers _)))

end PCore

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

theorem orthogonal_high_Witt_or_binary_fixed_space_local_core_centralization
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (a : ProjOrthDerived Q) (haA : a ∈ A) (ha1 : a ≠ 1)
    (x : orthDerived Q) (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a)
    (hxp : orderOf x = p)
    (hW : finrank K (fixedSpace (x : V ≃ₗ[K] V)) ≤ 2 ∨
      ∃ U : Submodule K V, U ≤ fixedSpace (x : V ≃ₗ[K] V) ∧ finrank K U = 3 ∧
        ∀ u ∈ U, Q u = 0) :
    ((∃ U : Submodule K V, U ≤ fixedSpace (x : V ≃ₗ[K] V) ∧ finrank K U = 3 ∧
        ∀ u ∈ U, Q u = 0) →
      IsComponent (((fixedComponentImage Q (x : V ≃ₗ[K] V)).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))))) ∧
    (finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 2 →
      ∀ w₀ : orthDerived Q, w₀ ^ p = 1 →
        (w₀ : V ≃ₗ[K] V) ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1) →
        (∀ n ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
          (QuotientGroup.mk w₀ : ProjOrthDerived Q) * n = n * QuotientGroup.mk w₀) ∧
        (QuotientGroup.mk w₀ : ProjOrthDerived Q) ∈
          Assembly.pCoreOf p (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) ∧
    ((∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) →
      (∀ y ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), orderOf y = p →
        ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
            (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
          s * MulAut.conj y = MulAut.conj y * s) ∧
      ∀ g ∈ A, ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
        s * MulAut.conj g = MulAut.conj g * s) := by
  classical
  have _hA2 := hAcard
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have ha : orderOf a = p := orderOf_eq_prime (hA.2 a haA) ha1
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨⟨Rep, hRep⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl B hB a ha x hxa hxp
  obtain ⟨hNeq, -, -, -, -, -, -, hfac⟩ := hmain Rep hRep
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_center_eq_bot hcenterT
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))
    with hN
  have hNeq' : N = centralizerImage Q xe := hNeq
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  have hwpow : ∀ w₀ : orthDerived Q, w₀ ^ p = 1 → (w₀ : V ≃ₗ[K] V) ^ p = 1 := fun w₀ hw₀ => by
    have := congrArg Subtype.val hw₀
    simpa using this
  have hwN : ∀ w₀ : orthDerived Q, (w₀ : V ≃ₗ[K] V) ∈ supportedBlock Q xe (X - 1) →
      ρ w₀ ∈ N := fun w₀ hw₀B => by
    rw [hNeq']
    exact Subgroup.mem_map.mpr ⟨w₀, Subgroup.mem_subgroupOf.mpr
      (supportedBlock_le_isometryCentralizer _ hw₀B), rfl⟩
  have hhigh : (∃ U : Submodule K V, U ≤ fixedSpace xe ∧ finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) →
      (∃ U' : Submodule K (fixedSpace xe), finrank K U' = 3 ∧
        ∀ u ∈ U', (Q.comp (fixedSpace xe).subtype) u = 0) := by
    rintro ⟨U, hUW, hU3, hUQ⟩
    refine ⟨U.comap (fixedSpace xe).subtype, ?_, fun u hu => hUQ _ hu⟩
    rw [← hU3]
    exact (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq
  have hJN : fixedComponentImage Q xe ≤ N := by
    rw [hNeq']
    exact fixedComponentImage_le_centralizerImage
  have hJnorm : ((fixedComponentImage Q xe).subgroupOf N).Normal := by
    rw [hNeq']
    exact hx.normal_fixedComponentImage
  have hbin : finrank K (fixedSpace xe) = 2 → ∀ w₀ : orthDerived Q, w₀ ^ p = 1 →
      (w₀ : V ≃ₗ[K] V) ∈ supportedBlock Q xe (X - 1) →
      ∀ n ∈ N, ρ w₀ * n = n * ρ w₀ := by
    intro hdim w₀ hw₀p hw₀B n hn
    rw [hNeq'] at hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    have := hx.commute_fixed_of_mem_orthDerived hp2 hQ hRep hdim
      (Subgroup.mem_subgroupOf.mp hm) m.2 hw₀B (hwpow w₀ hw₀p)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext this.symm
  refine ⟨?_, ?_, ?_⟩
  · intro hHW
    exact isComponent_conj_subgroupOf hB a hinj hJN hJnorm
      (hx.isQuasisimple_fixedComponentImage (hhigh hHW))
  · intro hdim w₀ hw₀p hw₀B
    refine ⟨hbin hdim w₀ hw₀p hw₀B, ?_⟩
    refine mem_pCoreOf_of_central (hwN w₀ hw₀B) (hbin hdim w₀ hw₀p hw₀B) ?_
    show ρ w₀ ^ p = 1
    rw [← map_pow, hw₀p, map_one]
  · intro hpm
    have hy : ∀ y ∈ N, orderOf y = p → ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
        s * MulAut.conj y = MulAut.conj y * s := by
      intro y hy hyp s hs
      obtain ⟨z, k, w, hyzkw, -, -, -, hzN, hzc, hzp, hkD, hkp, ⟨w₀, hw₀ρ, hw₀p, hw₀B, -, -⟩,
        hS⟩ := hfac hpm y hy hyp
      have hsw : s * MulAut.conj w = MulAut.conj w * s := by
        rw [← hw₀ρ]
        rcases hW with hle | hHW
        · by_cases h1 : finrank K (fixedSpace xe) ≤ 1
          ·
            have hQW := hx.polarBilin_fixed_nondegenerate
            have hw₀M : (w₀ : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe :=
              supportedBlock_le_isometryCentralizer _ hw₀B
            have hone := eq_one_of_finrank_le_one hQW h1
              (g := ⟨restrictFixed Q xe ⟨w₀, hw₀B⟩, restrictFixed_mem_orthogonalGroup _⟩) hp2
              (Subtype.ext (by
                show (restrictFixed Q xe ⟨w₀, hw₀B⟩) ^ p = 1
                rw [← map_pow]
                have : (⟨(w₀ : V ≃ₗ[K] V), hw₀B⟩ : ↥(supportedBlock Q xe (X - 1))) ^ p = 1 :=
                  Subtype.ext (hwpow w₀ hw₀p)
                rw [this, map_one]))
            have h2 : (⟨(w₀ : V ≃ₗ[K] V), hw₀B⟩ : ↥(supportedBlock Q xe (X - 1))) = 1 :=
              restrictFixed_injective hx (by rw [map_one]; exact hone)
            have h2' : (w₀ : V ≃ₗ[K] V) = 1 :=
              congrArg (fun y : ↥(supportedBlock Q xe (X - 1)) => (y : V ≃ₗ[K] V)) h2
            have h3 : w₀ = 1 := Subtype.ext h2'
            rw [h3, QuotientGroup.mk_one, map_one, one_mul, mul_one]
          · have hdim : finrank K (fixedSpace xe) = 2 := by omega
            exact commute_core_conj_of_central hp hB a hinj (hwN w₀ hw₀B)
              (hbin hdim w₀ hw₀p hw₀B) (by rw [← map_pow, hw₀p, map_one]) s hs
        · have hT' := hhigh hHW
          have hw₀F : (w₀ : V ≃ₗ[K] V) ∈ supportedFixedDerived Q xe :=
            hx.mem_supportedFixedDerived_of_odd_pow hT' hw₀B hp2 (hwpow w₀ hw₀p)
          have h0 := commutator_core_map_conj_eq_bot hp hB a hinj hJN hJnorm
            (hx.isQuasisimple_fixedComponentImage hT')
          rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
          have hwJ : ρ w₀ ∈ fixedComponentImage Q xe :=
            Subgroup.mem_map.mpr ⟨w₀, Subgroup.mem_subgroupOf.mpr hw₀F, rfl⟩
          exact Subgroup.mem_centralizer_iff.mp (h0 (Subgroup.mem_map_of_mem _ hwJ)) s hs
      obtain ⟨hsz, hsk⟩ := hS s hs
      rw [hyzkw, map_mul, map_mul]
      calc s * (MulAut.conj z * MulAut.conj k * MulAut.conj w)
          = (s * MulAut.conj z) * MulAut.conj k * MulAut.conj w := by simp only [mul_assoc]
        _ = MulAut.conj z * (s * MulAut.conj k) * MulAut.conj w := by
          rw [hsz]; simp only [mul_assoc]
        _ = MulAut.conj z * (MulAut.conj k * s) * MulAut.conj w := by rw [hsk]
        _ = MulAut.conj z * MulAut.conj k * (s * MulAut.conj w) := by simp only [mul_assoc]
        _ = MulAut.conj z * MulAut.conj k * (MulAut.conj w * s) := by rw [hsw]
        _ = MulAut.conj z * MulAut.conj k * MulAut.conj w * s := by simp only [mul_assoc]
    refine ⟨hy, fun g hg s hs => ?_⟩
    by_cases hg1 : g = 1
    · rw [hg1, map_one, mul_one, one_mul]
    · have hgN : g ∈ N := by
        have := hA.1
        rw [hN, Subgroup.mem_centralizer_singleton_iff]
        have := mul_comm' (⟨g, hg⟩ : ↥A) ⟨a, haA⟩
        exact congrArg Subtype.val this
      exact hy g hgN (orderOf_eq_prime (hA.2 g hg) hg1) s hs

end CFSG.RankThree.PartOne
