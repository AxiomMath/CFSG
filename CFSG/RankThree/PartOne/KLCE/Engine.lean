module

public import CFSG.RankThree.PartOne.KLCE.Descent
public import CFSG.RankThree.PartOne.KLCE.EngineGroup
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.RankThree.PartOne.S11d.Facts5

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE


section Torus

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]

theorem exists_odd_pow_eq_one_of_mem_torusGroup [CharP L 2] [Algebra.IsAlgebraic K L]
    {h : ModGL τ L} (hh : h ∈ torusGroup τ L) : ∃ m : ℕ, Odd m ∧ h ^ m = 1 := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hodd : ∀ i, Odd (orderOf (a i)) := fun i =>
    odd_orderOf_of_charTwo (a i) (isOfFinOrder_of_isAlgebraic (K := K) (a i))
  refine ⟨∏ i, orderOf (a i), ?_, ?_⟩
  · exact Finset.prod_induction _ Odd (fun x y hx hy => hx.mul hy) odd_one
      (fun i _ => hodd i)
  · have h1 : a ^ (∏ i, orderOf (a i)) = 1 := by
      funext i
      rw [Pi.pow_apply, Pi.one_apply]
      exact orderOf_dvd_iff_pow_eq_one.1 (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    have h2 := (rootDiagUnitHom τ L).map_pow a (∏ i, orderOf (a i))
    rw [h1, map_one] at h2
    exact h2.symm

theorem exists_mul_of_mem_torus_sup_rootSpan {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L S) :
    ∃ t ∈ torusGroup τ L, ∃ q ∈ rootSpan τ L S, y = t * q := by
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L) (rootSpan τ L S)
    (KE.torusGroup_le_normalizer_rootSpan hS)
  have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L S : Subgroup (ModGL τ L)) :
    Set (ModGL τ L)) := hy
  rw [e] at hy'
  obtain ⟨t, ht, q, hq, rfl⟩ := hy'
  exact ⟨t, ht, q, hq, rfl⟩

end Torus

section Structure

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]

@[expose] def layerComp (g₀ : ModGL τ L) (c : adjointGroup τ K) {ι' : Type}
    (P : ι' → Subgroup (ModGL τ L)) (i : ι') : Subgroup (adjointGroup τ K) :=
  (P i).comap (psiTilde τ K L g₀ c)

theorem layerData_structure_odd [CharP L 2] [Algebra.IsAlgebraic K L] {p : ℕ} (hp : p.Prime)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (N g₀ : ModGL τ L) (hg₀C : g₀ ∈ adjointGroup τ L)
    (hg₀ : Units.map (entrywiseHom Fr) g₀ = g₀ * N)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Units.map (entrywiseHom Fr) x = x) → ⁅P, P⁆ = P → P ≤ (adjEmb τ K L).range)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf N (Units.map (entrywiseHom Fr)) →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    {ι' : Type} (P : ι' → Subgroup (ModGL τ L)) (hfam : IsSigmaFamily N Fr S P)
    (hjoin : ∀ y ∈ rootSpan τ L S ⊓ twistedFixedPoints N (Units.map (entrywiseHom Fr)),
      ∃ m : ℕ, Odd m ∧ y ^ m ∈ ⨆ i, P i)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ P i, ∀ v ∈ P j, u * v = v * u)
    {x : adjointGroup τ K} (hx : orderOf x = p) (c : adjointGroup τ K)
    (hc : c * x * c⁻¹ ∈ subtorusImage (adjEmb τ K L) g₀
      (subtorusSigma N (Units.map (entrywiseHom Fr)) S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ →
      rootCharKernel a ⊆ S) :
    (∀ i, P i ≤ (psiTilde τ K L g₀ c).range) ∧
      (∀ i, CFSG.RankThree.PartOne.IsComponentOf (Subgroup.centralizer ({x} : Set _))
        (layerComp g₀ c P i)) ∧
      Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K)) ⊓
        Subgroup.centralizer ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)) :
          Set (adjointGroup τ K))) ∧
      ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)).subgroupOf
        (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))).Normal ∧
      Odd ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)).subgroupOf
        (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))).index := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have hψtinj : Function.Injective (psiTilde τ K L g₀ c) := psiTilde_injective g₀ c
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  obtain ⟨ψ, -, hψ, hψHQ, hψR, -, hPψ, -⟩ := sigma_embedding_data_of_stab (adjEmb τ K L)
    adjEmb_injective (fun y => adjEmb_mem y) (Units.map (entrywiseHom Fr))
    (adjEmb_frobenius Fr hFr) N g₀ hg₀C hg₀ hperf hp hstab hS hSn P hPfin hPq hPQ hPR hPadj
    hPnorm hPcent hx c hc hkerZ
  have hψt_eq : ∀ y : Subgroup.centralizer ({x} : Set (adjointGroup τ K)),
      psiTilde τ K L g₀ c y = ψ y := fun y => by rw [hψ y, psiTilde_apply]
  have hψt_mem : ∀ y ∈ Subgroup.centralizer ({x} : Set (adjointGroup τ K)),
      psiTilde τ K L g₀ c y ∈ torusGroup τ L ⊔ rootSpan τ L S ∧
      N * Units.map (entrywiseHom Fr) (psiTilde τ K L g₀ c y) * N⁻¹ =
        psiTilde τ K L g₀ c y := fun y hy => by
    have h := hψt_eq ⟨y, hy⟩
    exact ⟨h ▸ hψHQ ⟨y, hy⟩, h ▸ hψR ⟨y, hy⟩⟩
  have hPrange : ∀ i, P i ≤ (psiTilde τ K L g₀ c).range := fun i u hu => by
    obtain ⟨y, hy⟩ := hPψ i hu
    exact ⟨y, (hψt_eq y).trans hy⟩
  have hmap : ∀ i, (layerComp g₀ c P i).map (psiTilde τ K L g₀ c) = P i := fun i => by
    unfold layerComp
    rw [Subgroup.map_comap_eq, inf_eq_right.2 (hPrange i)]
  have hz : psiTilde τ K L g₀ c x ∈ subtorusSigma N (Units.map (entrywiseHom Fr)) S := by
    rw [psiTilde_apply]
    exact (mem_subtorusImage_iff (adjEmb τ K L) g₀ _ (c * x * c⁻¹)).1 hc
  have hQX : ∀ i, layerComp g₀ c P i ≤ Subgroup.centralizer ({x} : Set (adjointGroup τ K)) :=
    fun i y hy => by
    have h1 : psiTilde τ K L g₀ c y ∈ P i := hy
    have h2 := Subgroup.mem_centralizer_iff.1 hz.2 _ (hPQ i h1)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    apply hψtinj
    rw [map_mul, map_mul]
    exact h2
  have hJQ : (⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)) =
      (⨆ i, P i).comap (psiTilde τ K L g₀ c) := by
    have h1 : (⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)).map
        (psiTilde τ K L g₀ c) = ⨆ i, P i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hmap
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective hψtinj _).symm
  have hmemJQ : ∀ y, y ∈ (⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)) ↔
      psiTilde τ K L g₀ c y ∈ ⨆ i, P i := fun y => by
    rw [hJQ]
    rfl
  have hnormP : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S,
      y ∈ twistedFixedPoints N (Units.map (entrywiseHom Fr)) →
      ∀ v ∈ ⨆ i, P i, y * v * y⁻¹ ∈ ⨆ i, P i := by
    intro y hy hyR v hv
    have hle : (⨆ i, P i) ≤ (⨆ i, P i).comap (MulAut.conj y).toMonoidHom :=
      iSup_le fun i u hu => by
        change y * u * y⁻¹ ∈ ⨆ i, P i
        exact le_iSup P i (hPnorm i y hy hyR u hu)
    exact hle hv
  have hnormal : ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)).subgroupOf
      (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hmemJQ] at hn ⊢
    have hg := hψt_mem (g : adjointGroup τ K) g.2
    have h := hnormP _ hg.1 hg.2 _ hn
    change psiTilde τ K L g₀ c ((g : adjointGroup τ K) * (n : adjointGroup τ K) *
      (g : adjointGroup τ K)⁻¹) ∈ _
    rw [map_mul, map_mul, map_inv]
    exact h
  have hodd : Odd ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)).subgroupOf
      (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))).index := by
    have : Finite ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K))) := inferInstance
    refine odd_index_of_sq_mem _ (fun g hg => ?_)
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    have hg2 : psiTilde τ K L g₀ c ((g : adjointGroup τ K) ^ 2) ∈ ⨆ i, P i :=
      (hmemJQ _).1 (by simpa using hg)
    rw [map_pow] at hg2
    obtain ⟨hHQ, hR⟩ := hψt_mem (g : adjointGroup τ K) g.2
    obtain ⟨t, ht, q, hq, hu⟩ := exists_mul_of_mem_torus_sup_rootSpan hS hHQ
    have hq2 : (psiTilde τ K L g₀ c (g : adjointGroup τ K)) ^ 2 ∈ rootSpan τ L S :=
      (iSup_le hPQ : (⨆ i, P i) ≤ rootSpan τ L S) hg2
    rw [hu, pow_two] at hq2
    have h1 : t * q * t ∈ rootSpan τ L S := by
      have := mul_mem hq2 (inv_mem hq)
      simpa [mul_assoc] using this
    have hnorm : t ∈ Subgroup.normalizer (rootSpan τ L S : Set (ModGL τ L)) :=
      KE.torusGroup_le_normalizer_rootSpan hS ht
    have h2 : t * q * t⁻¹ ∈ rootSpan τ L S := (Subgroup.mem_normalizer_iff.1 hnorm q).1 hq
    have ht2 : t ^ 2 ∈ rootSpan τ L S := by
      have : t ^ 2 = (t * q * t⁻¹)⁻¹ * (t * q * t) := by rw [pow_two]; group
      rw [this]
      exact mul_mem (inv_mem h2) h1
    obtain ⟨m, hm, htm⟩ := exists_odd_pow_eq_one_of_mem_torusGroup (K := K) ht
    obtain ⟨k, hk⟩ := hm
    have e1 : t ^ (2 * k + 1) = 1 := by rw [← hk]; exact htm
    have htQ : t ∈ rootSpan τ L S := by
      have : t = (t ^ 2) ^ (k + 1) := by
        calc t = t ^ (2 * k + 1) * t := by rw [e1, one_mul]
          _ = t ^ (2 * k + 1 + 1) := (pow_succ _ _).symm
          _ = (t ^ 2) ^ (k + 1) := by rw [← pow_mul]; ring_nf
      rw [this]
      exact pow_mem ht2 _
    have huQ : psiTilde τ K L g₀ c (g : adjointGroup τ K) ∈ rootSpan τ L S := by
      rw [hu]
      exact mul_mem htQ hq
    obtain ⟨mm, ⟨kk, hkk⟩, hym⟩ := hjoin _ ⟨huQ, hR⟩
    have hym' : (psiTilde τ K L g₀ c (g : adjointGroup τ K)) ^ (2 * kk + 1) ∈ ⨆ i, P i := by
      rw [← hkk]
      exact hym
    have hyeq : psiTilde τ K L g₀ c (g : adjointGroup τ K) =
        (psiTilde τ K L g₀ c (g : adjointGroup τ K)) ^ (2 * kk + 1) *
          (((psiTilde τ K L g₀ c (g : adjointGroup τ K)) ^ 2) ^ kk)⁻¹ := by
      rw [pow_succ, ← pow_mul]
      group
    refine (hmemJQ _).2 ?_
    rw [hyeq]
    exact mul_mem hym' (inv_mem (pow_mem hg2 kk))
  have hequiv : ∀ i, ↥(layerComp g₀ c P i) ≃* ↥(P i) := fun i =>
    (Subgroup.equivMapOfInjective _ (psiTilde τ K L g₀ c) hψtinj).trans
      (MulEquiv.subgroupCongr (hmap i))
  have hquasi : ∀ i, CFSG.IsQuasisimple ↥(layerComp g₀ c P i) := fun i =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (hequiv i).symm (hPq i)
  have hcommQ : ∀ i j, i ≠ j → ∀ y ∈ layerComp g₀ c P i, ∀ y' ∈ layerComp g₀ c P j,
      y * y' = y' * y := fun i j hij y hy y' hy' => by
    apply hψtinj
    rw [map_mul, map_mul]
    exact hcomm i j hij _ hy _ hy'
  have hJle : ∀ i, (⨆ j, layerComp g₀ c P j : Subgroup (adjointGroup τ K)) ≤
      Subgroup.normalizer ((layerComp g₀ c P i : Subgroup (adjointGroup τ K)) :
        Set (adjointGroup τ K)) := fun i => by
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · subst hij
      exact Subgroup.le_normalizer
    · intro y hy
      refine Subgroup.mem_normalizer_iff.2 fun u => ?_
      have hconj : ∀ u ∈ layerComp g₀ c P i, y * u * y⁻¹ = u := fun u hu => by
        rw [← hcommQ i j (Ne.symm hij) u hu y hy]
        group
      constructor
      · intro hu
        rw [hconj u hu]
        exact hu
      · intro hu
        have e := hconj _ hu
        have e2 : y * u * y⁻¹ = u := by
          have := congrArg (fun z => y⁻¹ * z * y) e
          simpa [mul_assoc] using this
        rw [e2] at hu
        exact hu
  have hsub : ∀ i, ((layerComp g₀ c P i).subgroupOf
      (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))).IsSubnormal := fun i => by
    refine Subgroup.IsSubnormal.step _
      ((⨆ j, layerComp g₀ c P j : Subgroup (adjointGroup τ K)).subgroupOf
        (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))) ?_ hnormal.isSubnormal ?_
    · intro a ha
      exact Subgroup.mem_subgroupOf.2 (le_iSup (layerComp g₀ c P) i (Subgroup.mem_subgroupOf.1 ha))
    · refine ⟨fun b hb a => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hb ⊢
      have ha : (a : Subgroup.centralizer ({x} : Set (adjointGroup τ K))) ∈ _ := a.2
      rw [Subgroup.mem_subgroupOf] at ha
      have h := (Subgroup.mem_normalizer_iff.1 (hJle i ha) _).1 hb
      simpa using h
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K)) ⊓
      Subgroup.centralizer ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)) :
        Set (adjointGroup τ K))) := by
    have hmemT : ∀ y ∈ Subgroup.centralizer ({x} : Set (adjointGroup τ K)) ⊓
        Subgroup.centralizer ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)) :
          Set (adjointGroup τ K)), psiTilde τ K L g₀ c y ∈ torusGroup τ L := by
      intro y hy
      obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨hHQ, hR⟩ := hψt_mem y hyX
      have := hPcent _ hHQ hR (fun i u hu => by
        obtain ⟨w, hw⟩ := hPrange i hu
        have hwQ : w ∈ layerComp g₀ c P i := by
          show psiTilde τ K L g₀ c w ∈ P i
          rw [hw]
          exact hu
        have hwJ : w ∈ (⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)) :=
          le_iSup (layerComp g₀ c P) i hwQ
        have h := Subgroup.mem_centralizer_iff.1 hyC w hwJ
        have h2 : psiTilde τ K L g₀ c (w * y) = psiTilde τ K L g₀ c (y * w) := by rw [h]
        rw [map_mul, map_mul, hw] at h2
        exact h2.symm)
      exact (mem_twistedTorusOf.1 (subtorusSigma_le_twistedTorusOf _ _ _ this)).1
    refine Group.isSolvable_of_comm (fun a b => ?_)
    apply Subtype.ext
    apply hψtinj
    have ha := hmemT a a.2
    have hb := hmemT b b.2
    change psiTilde τ K L g₀ c ((a : adjointGroup τ K) * b) =
      psiTilde τ K L g₀ c ((b : adjointGroup τ K) * a)
    rw [map_mul, map_mul]
    exact KE.torusGroup_comm ha hb
  exact ⟨hPrange, fun i => ⟨hQX i, hquasi i, hsub i⟩, hsolv, hnormal, hodd⟩


theorem layerData_structure [CharP L 2] [Algebra.IsAlgebraic K L] {p : ℕ} (hp : p.Prime)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (N g₀ : ModGL τ L) (hg₀C : g₀ ∈ adjointGroup τ L)
    (hg₀ : Units.map (entrywiseHom Fr) g₀ = g₀ * N)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Units.map (entrywiseHom Fr) x = x) → ⁅P, P⁆ = P → P ≤ (adjEmb τ K L).range)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf N (Units.map (entrywiseHom Fr)) →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    {ι' : Type} (P : ι' → Subgroup (ModGL τ L)) (hfam : IsSigmaFamily N Fr S P)
    (hjoin : rootSpan τ L S ⊓ twistedFixedPoints N (Units.map (entrywiseHom Fr)) ≤ ⨆ i, P i)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ P i, ∀ v ∈ P j, u * v = v * u)
    {x : adjointGroup τ K} (hx : orderOf x = p) (c : adjointGroup τ K)
    (hc : c * x * c⁻¹ ∈ subtorusImage (adjEmb τ K L) g₀
      (subtorusSigma N (Units.map (entrywiseHom Fr)) S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ →
      rootCharKernel a ⊆ S) :
    (∀ i, P i ≤ (psiTilde τ K L g₀ c).range) ∧
      (∀ i, CFSG.RankThree.PartOne.IsComponentOf (Subgroup.centralizer ({x} : Set _))
        (layerComp g₀ c P i)) ∧
      Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K)) ⊓
        Subgroup.centralizer ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)) :
          Set (adjointGroup τ K))) ∧
      ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)).subgroupOf
        (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))).Normal ∧
      Odd ((⨆ i, layerComp g₀ c P i : Subgroup (adjointGroup τ K)).subgroupOf
        (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))).index :=
  layerData_structure_odd hp Fr hFr N g₀ hg₀C hg₀ hperf hstab hS hSn P hfam
    (fun y hy => ⟨1, odd_one, by simpa using hjoin hy⟩) hcomm hx c hc hkerZ

end Structure

end CFSG.RankThree.PartOne.KLCE
