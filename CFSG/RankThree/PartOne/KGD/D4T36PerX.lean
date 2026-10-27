module

public import CFSG.RankThree.PartOne.KGD.D4T36Family
public import CFSG.RankThree.PartOne.KGD.D4QPerX

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold
open scoped Matrix MatrixGroups Pointwise

section PerX

theorem d4T36_perx {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ]
    [IsAlgClosed L] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (σ : K ≃+* K) [Algebra K L]
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (w : WeylGroup TwistTag.D4.tag) (hnw : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = w)
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    {g0 : ModGL TwistTag.D4.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range)
    (hcomm : (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L ℓ f).comp (algebraMap K L))
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx : orderOf x = p)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * g0)
    (hh : rootDiagUnit TwistTag.D4.tag b ∈
      twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    (∀ V : Subgroup (Subgroup.centralizer
        ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
      V.Normal → Group.IsSolvable V → ∀ v ∈ V,
        d4QPsi (triEmb K σ L) g0 c x v ∈
          twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) ∧
        ∃ a : Fin TwistTag.D4.tag.rank → Lˣ,
          d4QPsi (triEmb K σ L) g0 c x v = rootDiagUnit TwistTag.D4.tag a ∧
            ∀ α ∈ rootCharKernel b, rootChar a α = 1) ∧
    ((rootCharKernel b).Nonempty →
      ∃ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P ∧ CFSG.IsQuasisimple P ∧
        P ≤ rootSpan TwistTag.D4.tag L (rootCharKernel b) ∧
        P ≤ (d4QPsi (triEmb K σ L) g0 c x).range ∧
        ∀ r : ℕ, r.Prime → r ∣ ℓ ^ f + 1 → ∃ y ∈ P, orderOf y = r) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hq2' : ε = 1 ∨ 2 < ℓ ^ f := by
    rcases hε with rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr ?_
      by_contra hlt
      have h2 : ℓ ^ f = 2 := by omega
      rw [h2] at hpd
      have h3 : (p : ℤ) ∣ 3 := by simpa using hpd
      have := Int.le_of_dvd (by norm_num) h3
      omega
  have hordW := not_dvd_card_weylGroup_D4 hp hp3
  have hιC := triEmb_mem_adjointGroup (K := K) (σ := σ) (L := L)
  have hιΦ := triEmb_fixed (K := K) (σ := σ) (L := L) Fr hcomm
  have hT := twistedTorus_D4_eq_map_of_weylImage Fr hn w hnw (d4T36M ε) hw
  have hperf' : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P →
      P ≤ adjointGroup TwistTag.D4.tag L → (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) →
        ⁅P, P⁆ = P → P ≤ (triEmb K σ L).range := fun P _ hPC hPF _ => hperf P hPC hPF
  have hordb : orderOf (rootDiagUnit TwistTag.D4.tag b) = p := by
    rw [hb]
    have e1 : orderOf (g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * g0) =
        orderOf (triEmb K σ L (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (triEmb K σ L (c * x * c⁻¹))
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (triEmb K σ L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective _ triEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      rw [show ((MulAut.conj c).toMonoidHom x) = c * x * c⁻¹ from rfl] at this
      exact this
    rw [e1, e2, e3, hx]
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hordb
  have hbfix : b ∈ fixedCharTuples (d4T36M ε) Fr := by
    have hh' := hh
    rw [hT] at hh'
    obtain ⟨b', hb', hbb'⟩ := Subgroup.mem_map.1 hh'
    have : b' = b := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) hbb'
    exact this ▸ hb'
  have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [d4Q_rootChar_neg, hα.2, inv_one]⟩
  have conj1 : ∀ (S : Set (Fin TwistTag.D4.tag.rank → ℤ)), rootCharKernel b = S →
      (∀ α ∈ S, IsRoot TwistTag.D4.tag α) → ∀ z : ModGL TwistTag.D4.tag L,
      z ∈ subtorusSigma n (twistHom TwistTag.D4 L Fr) S →
      z ∈ twistedTorusOf n (twistHom TwistTag.D4 L Fr) ∧
        ∃ a : Fin TwistTag.D4.tag.rank → Lˣ, z = rootDiagUnit TwistTag.D4.tag a ∧
          ∀ α ∈ rootCharKernel b, rootChar a α = 1 := by
    intro S hSeq hS z hz
    obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨hzH, -⟩ := mem_twistedTorusOf.1 hzT
    obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hzH
    refine ⟨hzT, a', ha', fun α hα => ?_⟩
    rw [hSeq] at hα
    exact (rootDiagUnit_mem_centralizer_rootSpan_iff a' hS).1 (ha' ▸ hzC) α hα
  have core : ∀ (S : Set (Fin TwistTag.D4.tag.rank → ℤ)), rootCharKernel b = S →
      (∀ α ∈ S, IsRoot TwistTag.D4.tag α) → (∀ α ∈ S, -α ∈ S) →
      ∀ {ι' : Type} (P : ι' → Subgroup (ModGL TwistTag.D4.tag L)), (∀ i, Finite (P i)) →
        (∀ i, CFSG.IsQuasisimple (P i)) → (∀ i, P i ≤ rootSpan TwistTag.D4.tag L S) →
        (∀ i, P i ≤ twistedFixedPoints n (twistHom TwistTag.D4 L Fr)) →
        (∀ i, P i ≤ adjointGroup TwistTag.D4.tag L) →
        (∀ i, ∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S,
          y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) →
            ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) →
        (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S,
          y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) →
          (∀ i, ∀ u ∈ P i, y * u = u * y) →
            y ∈ subtorusSigma n (twistHom TwistTag.D4 L Fr) S) →
        ∃ ψ : Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →*
            ModGL TwistTag.D4.tag L,
          Function.Injective ψ ∧
          (∀ y, ψ y = g0⁻¹ * triEmb K σ L
            (c * (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * c⁻¹) * g0) ∧
          (∀ i, P i ≤ ψ.range) ∧
          ∀ V : Subgroup (Subgroup.centralizer
              ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
            V.Normal → Group.IsSolvable V → ∀ v ∈ V,
              ψ v ∈ subtorusSigma n (twistHom TwistTag.D4 L Fr) S := by
    intro S hSeq hS hSn ι' P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    have hsub : ∀ α ∈ S, rootChar b α = 1 := fun α hα => by
      rw [← hSeq] at hα
      exact hα.2
    have hcb : rootDiagUnit TwistTag.D4.tag b ∈
        subtorusSigma n (twistHom TwistTag.D4 L Fr) S :=
      Subgroup.mem_inf.2 ⟨hh, (rootDiagUnit_mem_centralizer_rootSpan_iff b hS).2 hsub⟩
    have hcS : c * x * c⁻¹ ∈ subtorusImage (triEmb K σ L) g0
        (subtorusSigma n (twistHom TwistTag.D4 L Fr) S) :=
      (mem_subtorusImage_iff (triEmb K σ L) g0 _ (c * x * c⁻¹)).2 (by rw [← hb]; exact hcb)
    have hkerZ : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ,
        rootDiagUnit TwistTag.D4.tag a = g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * g0 →
          rootCharKernel a ⊆ S := fun a ha => by
      have hab : a = b := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) (ha.trans hb.symm)
      rw [hab]
      exact hSeq.subset
    obtain ⟨ψ, hψinj, hψ, -, -, -, hPψ, hψV⟩ := sigma_embedding_data (triEmb K σ L)
      triEmb_injective hιC (twistHom TwistTag.D4 L Fr) hιΦ n g0 hg0C hg0 hperf' hp hordW hS hSn P
      hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ
    exact ⟨ψ, hψinj, hψ, hPψ, hψV⟩
  have hdψ : ∀ (ψ : Subgroup.centralizer
        ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →* ModGL TwistTag.D4.tag L),
      (∀ y, ψ y = g0⁻¹ * triEmb K σ L
        (c * (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * c⁻¹) * g0) →
      d4QPsi (triEmb K σ L) g0 c x = ψ := fun ψ hψ =>
    MonoidHom.ext fun y => (d4QPsi_apply (triEmb K σ L) g0 c x y).trans (hψ y).symm
  rcases d4T36_rootCharKernel_cases hε hbfix hb1 with hempty | ⟨i, hi⟩
  ·
    have hspan : rootSpan TwistTag.D4.tag L (∅ : Set (Fin TwistTag.D4.tag.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    obtain ⟨ψ, -, hψ, -, hψV⟩ := core ∅ hempty (by simp) (by simp) (ι' := Empty)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
      (by
        intro y hy hyR _
        rw [hspan, sup_bot_eq] at hy
        refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
        rw [hspan, Subgroup.mem_centralizer_iff]
        intro g hg
        have : g = 1 := hg
        rw [this, one_mul, mul_one])
    refine ⟨fun V hVn hVs v hv => ?_, fun hne => ?_⟩
    · rw [hdψ ψ hψ]
      exact conj1 ∅ hempty (by simp) _ (hψV V hVn hVs v hv)
    · exfalso
      rw [hempty] at hne
      exact Set.not_nonempty_empty hne
  ·
    have hSeq : rootCharKernel b = d4Sigma i := hi
    obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent, hPr⟩ := d4T36_family hf hk hε hq2' Fr
      hFr n hn (fun x => by rw [hnw]; exact hw x) i
    obtain ⟨ψ, -, hψ, hPψ, hψV⟩ := core (d4Sigma i) hSeq (fun α hα => isRoot_of_mem_d4Sigma hα)
      (fun α hα => by
        rw [← hSeq] at hα ⊢
        exact hrootneg α hα)
      (ι' := Unit) (fun _ => P) (fun _ => hPfin) (fun _ => hPq) (fun _ => hPQ) (fun _ => hPR)
      (fun _ => hPadj) (fun _ y hy hyR u hu => hPnorm y hy hyR u hu)
      (fun y hy hyR hcomm => hPcent y hy hyR (fun u hu => hcomm () u hu))
    refine ⟨fun V hVn hVs v hv => ?_, fun _ => ⟨P, hPfin, hPq, ?_, ?_, hPr⟩⟩
    · rw [hdψ ψ hψ]
      exact conj1 (d4Sigma i) hSeq (fun α hα => isRoot_of_mem_d4Sigma hα) _
        (hψV V hVn hVs v hv)
    · rw [hSeq]
      exact hPQ
    · rw [hdψ ψ hψ]
      exact hPψ ()

end PerX

end CFSG.RankThree.PartOne.KGD
