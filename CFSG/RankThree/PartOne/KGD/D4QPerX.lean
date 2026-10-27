module

public import CFSG.RankThree.PartOne.KGD.D4QA3
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.KGD.D4QFrame

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley.TrialityFold
open scoped Matrix MatrixGroups Pointwise

section Centralizer

variable {L : Type} [Field L]

theorem rootDiagUnit_mem_centralizer_rootSpan_iff (a : Fin TwistTag.D4.tag.rank → Lˣ)
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α) :
    rootDiagUnit TwistTag.D4.tag a ∈
        Subgroup.centralizer ((rootSpan TwistTag.D4.tag L S : Subgroup _) : Set _) ↔
      ∀ α ∈ S, rootChar a α = 1 := by
  constructor
  · intro h α hα
    have hmem := Subgroup.mem_centralizer_iff.1 h _ (pinnedX_mem_rootSpan hα (1 : L))
    have hconj := rootDiagUnit_conj_pinnedX a (hS α hα) (1 : L)
    have hX : rootDiagUnit TwistTag.D4.tag a * pinnedX TwistTag.D4.tag L α 1 *
        (rootDiagUnit TwistTag.D4.tag a)⁻¹ = pinnedX TwistTag.D4.tag L α 1 := by
      rw [← hmem]
      group
    have h3 : pinnedX TwistTag.D4.tag L α (((rootChar a α : Lˣ) : L) * 1) =
        pinnedX TwistTag.D4.tag L α 1 := hconj.symm.trans hX
    have h4 := pinnedX_injective (τ := TwistTag.D4.tag) (R := L) α h3
    exact Units.ext (by simpa using h4)
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle : rootSpan TwistTag.D4.tag L S ≤ Subgroup.centralizer
        ({rootDiagUnit TwistTag.D4.tag a} : Set (ModGL TwistTag.D4.tag L)) := by
      refine iSup₂_le fun α hα => ?_
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hconj := rootDiagUnit_conj_pinnedX a (hS α hα) c
      rw [h α hα, Units.val_one, one_mul] at hconj
      rw [mul_inv_eq_iff_eq_mul] at hconj
      exact hconj.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

end Centralizer

section Psi

variable {L : Type} [Field L]

@[expose] def d4QPsi {C : Type} [Group C] (ι : C →* ModGL TwistTag.D4.tag L)
    (g0 : ModGL TwistTag.D4.tag L) (c x : C) :
    Subgroup.centralizer ({x} : Set C) →* ModGL TwistTag.D4.tag L :=
  ((MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp (MulAut.conj c).toMonoidHom)).comp
    (Subgroup.centralizer ({x} : Set C)).subtype

theorem d4QPsi_apply {C : Type} [Group C] (ι : C →* ModGL TwistTag.D4.tag L)
    (g0 : ModGL TwistTag.D4.tag L) (c x : C) (y : Subgroup.centralizer ({x} : Set C)) :
    d4QPsi ι g0 c x y = g0⁻¹ * ι (c * (y : C) * c⁻¹) * g0 := by
  simp [d4QPsi, MulAut.conj_apply]

theorem d4QPsi_injective {C : Type} [Group C] {ι : C →* ModGL TwistTag.D4.tag L}
    (hι : Function.Injective ι) (g0 : ModGL TwistTag.D4.tag L) (c x : C) :
    Function.Injective (d4QPsi ι g0 c x) := by
  intro a b hab
  rw [d4QPsi_apply, d4QPsi_apply] at hab
  have h1 := mul_right_cancel (mul_left_cancel hab)
  have h2 := hι h1
  have h3 : (a : C) = b := by
    have := congrArg (fun z => c⁻¹ * z * c) h2
    simpa [mul_assoc] using this
  exact Subtype.ext h3

theorem d4QPsi_mul {C : Type} [Group C] (ι : C →* ModGL TwistTag.D4.tag L)
    (g0 m : ModGL TwistTag.D4.tag L) (c x : C) (y : Subgroup.centralizer ({x} : Set C)) :
    d4QPsi ι (g0 * m) c x y = m⁻¹ * d4QPsi ι g0 c x y * m := by
  rw [d4QPsi_apply, d4QPsi_apply]
  group

end Psi

section Std

variable {L : Type} [Field L]

theorem d4Q_nw_facts (Fr : L →+* L) {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∈ monomialSubgroup TwistTag.D4.tag L ∧
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∈ adjointGroup TwistTag.D4.tag L ∧
      twistHom TwistTag.D4 L Fr (canonicalRep (coxeterSystem TwistTag.D4.tag) L w) =
        canonicalRep (coxeterSystem TwistTag.D4.tag) L w := by
  obtain ⟨hmono, hΓ⟩ := Subgroup.mem_inf.1 (canonicalRep_mem_graphFixedMonomial TwistTag.D4 L Fr hw)
  obtain ⟨hadj, hfix⟩ := (mem_twistedFixedGroup_iff_twistHom _ _ _).1 hΓ
  exact ⟨hmono, hadj, hfix⟩

theorem d4Q_conj_monomial {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x = -x) (Fr : L →+* L)
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4) :
    ∃ hn'' : (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ * n *
        canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∈ monomialSubgroup TwistTag.D4.tag L,
      ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
        weylQuotientHom TwistTag.D4.tag L ⟨_, hn''⟩ • x = -x := by
  obtain ⟨hnwM, -, -⟩ := d4Q_nw_facts Fr hw
  have hn'' : (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ * n *
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem (mul_mem (inv_mem hnwM) hn) hnwM
  refine ⟨hn'', fun x => ?_⟩
  have hcan : weylQuotientHom TwistTag.D4.tag L
      ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) L w, hnwM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have e : (⟨_, hn''⟩ : monomialSubgroup TwistTag.D4.tag L) =
      (⟨canonicalRep (coxeterSystem TwistTag.D4.tag) L w, hnwM⟩ : monomialSubgroup _ _)⁻¹ *
        ⟨n, hn⟩ * ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) L w, hnwM⟩ := rfl
  rw [e, map_mul, map_mul, map_inv, hcan, mul_smul, mul_smul, hnW, smul_neg, inv_smul_smul]

theorem d4Q_perx_std [IsAlgClosed L] {C : Type} [Group C]
    (ι : C →* ModGL TwistTag.D4.tag L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup TwistTag.D4.tag L) (Fr : L →+* L)
    (hιΦ : ∀ y, twistHom TwistTag.D4 L Fr (ι y) = ι y)
    {n g0 : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x = -x)
    (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L Fr g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P → P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    {p : ℕ} (hp : p.Prime) (hordW : ¬ p ∣ Nat.card (WeylGroup TwistTag.D4.tag))
    {x : C} (hx : orderOf x = p) (c : C) {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * ι (c * x * c⁻¹) * g0)
    (hh : rootDiagUnit TwistTag.D4.tag b ∈ twistedTorusOf n (twistHom TwistTag.D4 L Fr))
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    {S₀ : Set (Fin TwistTag.D4.tag.rank → ℤ)} (hS₀ : ∀ α ∈ S₀, IsRoot TwistTag.D4.tag α)
    (hS₀n : ∀ α ∈ S₀, -α ∈ S₀)
    (hsurv : ∀ α, α ∈ rootCharKernel b ↔ ∃ β ∈ S₀, α = w • β)
    (hfam : ∀ (n'' : ModGL TwistTag.D4.tag L) (hn'' : n'' ∈ monomialSubgroup TwistTag.D4.tag L),
      (∀ x : Fin TwistTag.D4.tag.rank → ℤ,
        weylQuotientHom TwistTag.D4.tag L ⟨n'', hn''⟩ • x = -x) →
      ∃ (ι' : Type) (P : ι' → Subgroup (ModGL TwistTag.D4.tag L)),
        (∀ i, Finite (P i)) ∧ (∀ i, CFSG.IsQuasisimple (P i)) ∧
        (∀ i, P i ≤ rootSpan TwistTag.D4.tag L S₀) ∧
        (∀ i, P i ≤ twistedFixedPoints n'' (twistHom TwistTag.D4 L Fr)) ∧
        (∀ i, P i ≤ adjointGroup TwistTag.D4.tag L) ∧
        (∀ i, ∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S₀,
          y ∈ twistedFixedPoints n'' (twistHom TwistTag.D4 L Fr) → ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) ∧
        (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S₀,
          y ∈ twistedFixedPoints n'' (twistHom TwistTag.D4 L Fr) →
          (∀ i, ∀ u ∈ P i, y * u = u * y) →
            y ∈ subtorusSigma n'' (twistHom TwistTag.D4 L Fr) S₀)) :
    ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal → Group.IsSolvable V →
      ∀ v ∈ V, d4QPsi ι g0 c x v ∈ twistedTorusOf n (twistHom TwistTag.D4 L Fr) ∧
        ∃ a : Fin TwistTag.D4.tag.rank → Lˣ, d4QPsi ι g0 c x v = rootDiagUnit TwistTag.D4.tag a ∧
          ∀ α ∈ rootCharKernel b, rootChar a α = 1 := by
  classical
  set F := twistHom TwistTag.D4 L Fr with hF
  obtain ⟨hnwM, hnwA, hnwF⟩ := d4Q_nw_facts Fr hw
  obtain ⟨hn'', hn''W⟩ := d4Q_conj_monomial hn hnW Fr hw
  have hnwconj := canonicalRep_conj_rootDiagUnit (K := L) (τ := TwistTag.D4.tag) w
  generalize hnwdef : canonicalRep (coxeterSystem TwistTag.D4.tag) L w = nw at hnwM hnwA hnwF hn'' hn''W hnwconj
  set n'' := nw⁻¹ * n * nw with hn''def
  set g0' := g0 * nw with hg0'def
  have hg0'C : g0' ∈ adjointGroup TwistTag.D4.tag L := mul_mem hg0C hnwA
  have hg0' : F g0' = g0' * n'' := by
    rw [hg0'def, map_mul, hg0, hnwF, hn''def]
    group
  set b' : Fin TwistTag.D4.tag.rank → Lˣ := weylTuple w⁻¹ b with hb'def
  have hb'conj : nw⁻¹ * rootDiagUnit TwistTag.D4.tag b * nw = rootDiagUnit TwistTag.D4.tag b' := by
    have h1 : nw * rootDiagUnit TwistTag.D4.tag b' * nw⁻¹ = rootDiagUnit TwistTag.D4.tag b := by
      rw [hnwconj, hb'def, weylTuple_weylTuple, mul_inv_cancel, weylTuple_one]
    rw [← h1]
    group
  have hchar : ∀ β, rootChar b' β = rootChar b (w • β) := fun β => by
    rw [hb'def, rootChar_weylTuple, inv_inv]
  have hψ' : ∀ y : Subgroup.centralizer ({x} : Set C), d4QPsi ι g0' c x y =
      nw⁻¹ * d4QPsi ι g0 c x y * nw := fun y => d4QPsi_mul ι g0 nw c x y
  have hcb' : rootDiagUnit TwistTag.D4.tag b' ∈ subtorusSigma n'' F S₀ := by
    refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup b', ?_⟩, ?_⟩
    · have hfix := (mem_twistedTorusOf.1 hh).2
      rw [← hb'conj, map_mul, map_mul, map_inv, hnwF]
      calc n'' * (nw⁻¹ * F (rootDiagUnit TwistTag.D4.tag b) * nw) * n''⁻¹
          = nw⁻¹ * (n * F (rootDiagUnit TwistTag.D4.tag b) * n⁻¹) * nw := by
            simp only [hn''def]
            group
        _ = nw⁻¹ * rootDiagUnit TwistTag.D4.tag b * nw := by rw [hfix]
    · refine (rootDiagUnit_mem_centralizer_rootSpan_iff b' hS₀).2 fun β hβ => ?_
      rw [hchar]
      exact ((hsurv _).2 ⟨β, hβ, rfl⟩).2
  have hconjd : g0'⁻¹ * ι (c * x * c⁻¹) * g0' = rootDiagUnit TwistTag.D4.tag b' := by
    rw [← hb'conj, hb, hg0'def]
    group
  obtain ⟨ι', P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam n'' hn'' hn''W
  obtain ⟨ψ', hψ'inj, hψ'f, -, -, -, -, hψ'V⟩ := sigma_embedding_data ι hι hιC F hιΦ n'' g0' hg0'C
    hg0' (fun P' hf hPC hPF hPP => hperf P' hf hPC hPF hPP) hp hordW hS₀ hS₀n
    P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c
    ((mem_subtorusImage_iff ι g0' _ (c * x * c⁻¹)).2 (by rw [hconjd]; exact hcb'))
    (by
      intro a ha α hα
      have hab : a = b' := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
        (ha.trans hconjd)
      subst hab
      obtain ⟨hαr, hα1⟩ := hα
      have hwα : w • α ∈ rootCharKernel b :=
        ⟨IsRoot.smul hαr w, by rw [← hchar]; exact hα1⟩
      obtain ⟨β, hβ, hβα⟩ := (hsurv _).1 hwα
      have : α = β := smul_left_cancel w hβα
      exact this ▸ hβ)
  intro V hVn hVs v hv
  have hψ'v : ψ' v ∈ subtorusSigma n'' F S₀ := hψ'V V hVn hVs v hv
  have hψeq : d4QPsi ι g0 c x v = nw * ψ' v * nw⁻¹ := by
    have h1 : ψ' v = nw⁻¹ * d4QPsi ι g0 c x v * nw := by
      rw [hψ'f v, ← hψ' v, d4QPsi_apply]
    rw [h1]
    group
  obtain ⟨hψ'T, hψ'C⟩ := Subgroup.mem_inf.1 hψ'v
  obtain ⟨hψ'H, hψ'fix⟩ := mem_twistedTorusOf.1 hψ'T
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hψ'H
  have hcent : ∀ β ∈ S₀, rootChar a' β = 1 :=
    (rootDiagUnit_mem_centralizer_rootSpan_iff a' hS₀).1 (ha' ▸ hψ'C)
  have hψval : d4QPsi ι g0 c x v = rootDiagUnit TwistTag.D4.tag (weylTuple w a') := by
    rw [hψeq, ha', ← hnwconj]
  refine ⟨?_, weylTuple w a', hψval, fun α hα => ?_⟩
  · refine mem_twistedTorusOf.2 ⟨by rw [hψval]; exact rootDiagUnit_mem_torusGroup _, ?_⟩
    rw [hψeq, map_mul, map_mul, map_inv, hnwF]
    calc n * (nw * F (ψ' v) * nw⁻¹) * n⁻¹
        = nw * (n'' * F (ψ' v) * n''⁻¹) * nw⁻¹ := by
          simp only [hn''def]
          group
      _ = nw * ψ' v * nw⁻¹ := by rw [hψ'fix]
  · obtain ⟨β, hβ, rfl⟩ := (hsurv α).1 hα
    rw [rootChar_weylTuple, inv_smul_smul]
    exact hcent β hβ

theorem d4Q_orbit_zero :
    TwistTag.D4.orbit ⟨0, by decide⟩ = {i0, i1, i3} := rfl

theorem d4Q_orbit_one : TwistTag.D4.orbit ⟨1, by decide⟩ = {i2} := rfl

theorem d4Q_S₀_zero (β : Fin TwistTag.D4.tag.rank → ℤ) :
    ((∃ i ∈ ({i0, i1, i3} : Finset (Fin TwistTag.D4.tag.rank)),
        (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = β) ∨
      (∃ i ∈ ({i0, i1, i3} : Finset (Fin TwistTag.D4.tag.rank)),
        (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = -β)) ↔
      β ∈ threeRootSet d4Qr₁ d4Qr₂ d4Qr₃ := by
  simp only [threeRootSet, d4Qr₁, d4Qr₂, d4Qr₃, Set.mem_insert_iff, Set.mem_singleton_iff,
    Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
  simp only [neg_neg, @eq_comm _ (Pi.single i0 1), @eq_comm _ (Pi.single i1 1),
    @eq_comm _ (Pi.single i3 1), neg_eq_iff_eq_neg]
  tauto

theorem d4Q_S₀_one (β : Fin TwistTag.D4.tag.rank → ℤ) :
    ((∃ i ∈ ({i2} : Finset (Fin TwistTag.D4.tag.rank)),
        (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = β) ∨
      (∃ i ∈ ({i2} : Finset (Fin TwistTag.D4.tag.rank)),
        (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = -β)) ↔
      β ∈ ({Pi.single i2 1, -Pi.single i2 1} : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  simp only [Finset.mem_singleton, exists_eq_left, Set.mem_insert_iff, Set.mem_singleton_iff,
    @eq_comm _ (Pi.single i2 1), neg_eq_iff_eq_neg]

end Std

section PerX

variable {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ] [IsAlgClosed L]

theorem d4Q_perx (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    [Algebra K L] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1)
    {g0 : ModGL TwistTag.D4.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * trialityOpposition L)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range)
    (hcomm : (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L ℓ f).comp (algebraMap K L))
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx : orderOf x = p)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * g0)
    (hh : rootDiagUnit TwistTag.D4.tag b ∈
      twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
      V.Normal → Group.IsSolvable V → ∀ v ∈ V,
        d4QPsi (triEmb K σ L) g0 c x v ∈
          twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) ∧
        ∃ a : Fin TwistTag.D4.tag.rank → Lˣ,
          d4QPsi (triEmb K σ L) g0 c x v = rootDiagUnit TwistTag.D4.tag a ∧
            ∀ α ∈ rootCharKernel b, rootChar a α = 1 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hpq' : p ∣ ℓ ^ f + 1 := by exact_mod_cast hpq
  have hqge : 4 ≤ ℓ ^ f := by
    have hle : p ≤ ℓ ^ f + 1 := Nat.le_of_dvd (by positivity) hpq'
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  set z := trialityOpposition L with hzdef
  have hzM : z ∈ monomialSubgroup TwistTag.D4.tag L := trialityOpposition_mem_monomialSubgroup
  have hzW : ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
      weylQuotientHom TwistTag.D4.tag L ⟨z, hzM⟩ • v = -v :=
    weylQuotientHom_trialityOpposition_smul
  have hordW := not_dvd_card_weylGroup_D4 hp hp3
  have hιC := triEmb_mem_adjointGroup (K := K) (σ := σ) (L := L)
  have hιΦ := triEmb_fixed (K := K) (σ := σ) (L := L) Fr hcomm
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
  have hbap := CFSG.RankThree.Chevalley.pow_eq_one_of_orderOf_rootDiagUnit hordb
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hordb
  have hbfix : b ∈ fixedCharTuples d4QM Fr := by
    have hh' := hh
    rw [hFrdef, d4Q_twistedTorus] at hh'
    obtain ⟨b', hb', hbb'⟩ := hh'
    have : b' = b := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) hbb'
    exact this ▸ hb'
  obtain ⟨hb1', hb3'⟩ := d4Q_eq_of_pow_eq_one hFr hpq' hbfix hbap
  have hAB : ¬ (b i0 = 1 ∧ b i2 = 1) := by
    rintro ⟨h0, h2⟩
    apply hb1
    funext j
    rcases fin_cases j with rfl | rfl | rfl | rfl
    · exact h0
    · rw [hb1', h0]; rfl
    · exact h2
    · rw [hb3', h0]; rfl
  have hperf' : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P →
      P ≤ adjointGroup TwistTag.D4.tag L → (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) →
        ⁅P, P⁆ = P → P ≤ (triEmb K σ L).range := fun P _ hPC hPF _ => hperf P hPC hPF
  have hstd := fun {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
      {S₀ : Set (Fin TwistTag.D4.tag.rank → ℤ)} (hS₀ : ∀ α ∈ S₀, IsRoot TwistTag.D4.tag α)
      (hS₀n : ∀ α ∈ S₀, -α ∈ S₀)
      (hsurv : ∀ α, α ∈ rootCharKernel b ↔ ∃ β ∈ S₀, α = w • β)
      (hfam : ∀ (n'' : ModGL TwistTag.D4.tag L) (hn'' : n'' ∈ monomialSubgroup TwistTag.D4.tag L),
        (∀ x : Fin TwistTag.D4.tag.rank → ℤ,
          weylQuotientHom TwistTag.D4.tag L ⟨n'', hn''⟩ • x = -x) →
        ∃ (ι' : Type) (P : ι' → Subgroup (ModGL TwistTag.D4.tag L)),
          (∀ i, Finite (P i)) ∧ (∀ i, CFSG.IsQuasisimple (P i)) ∧
          (∀ i, P i ≤ rootSpan TwistTag.D4.tag L S₀) ∧
          (∀ i, P i ≤ twistedFixedPoints n'' (twistHom TwistTag.D4 L Fr)) ∧
          (∀ i, P i ≤ adjointGroup TwistTag.D4.tag L) ∧
          (∀ i, ∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S₀,
            y ∈ twistedFixedPoints n'' (twistHom TwistTag.D4 L Fr) →
              ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) ∧
          (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S₀,
            y ∈ twistedFixedPoints n'' (twistHom TwistTag.D4 L Fr) →
            (∀ i, ∀ u ∈ P i, y * u = u * y) →
              y ∈ subtorusSigma n'' (twistHom TwistTag.D4 L Fr) S₀)) =>
    d4Q_perx_std (triEmb K σ L) triEmb_injective hιC Fr hιΦ hzM hzW hg0C hg0 hperf' hp hordW hx c
      hb hh hw hS₀ hS₀n hsurv hfam
  rcases rootCharKernel_cases (a := b) (A := b i0) (B := b i2) rfl hb1' rfl hb3' hp hp3
    (hbap i0) (hbap i2) hAB with hempty | ⟨α, hαr, -, hker⟩
  ·
    refine hstd (one_mem _) (S₀ := ∅) (by simp) (by simp) (fun α => ?_) (fun n'' hn'' hn''W => ?_)
    · rw [hempty]
      simp
    · refine ⟨Empty, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
        fun e => e.elim, fun e => e.elim, fun e => e.elim, ?_⟩
      intro y hy hyR _
      have hspan : rootSpan TwistTag.D4.tag L (∅ : Set (Fin TwistTag.D4.tag.rank → ℤ)) = ⊥ := by
        simp [rootSpan]
      rw [hspan, sup_bot_eq] at hy
      refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
      rw [hspan, Subgroup.mem_centralizer_iff]
      intro g hg
      have : g = 1 := hg
      rw [this, one_mul, mul_one]
  · obtain ⟨w, hw, a₀, hdiag, -, -⟩ := (diagram_root_orbit_reduction TwistTag.D4).1 α hαr
    have hsurv_gen : ∀ S₀ : Set (Fin TwistTag.D4.tag.rank → ℤ),
        (∀ β, β ∈ S₀ ↔ ((∃ i ∈ TwistTag.D4.orbit a₀,
            (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = β) ∨
          (∃ i ∈ TwistTag.D4.orbit a₀,
            (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = -β))) →
        ∀ α', α' ∈ rootCharKernel b ↔ ∃ β ∈ S₀, α' = w • β := by
      intro S₀ hS₀ α'
      rw [hker, hdiag]
      simp only [Set.mem_union, Set.mem_neg, Finset.mem_coe, Finset.mem_image]
      constructor
      · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, h⟩)
        · exact ⟨_, (hS₀ _).2 (Or.inl ⟨i, hi, rfl⟩), rfl⟩
        · refine ⟨-Pi.single i 1, (hS₀ _).2 (Or.inr ⟨i, hi, by rw [neg_neg]⟩), ?_⟩
          rw [smul_neg, h, neg_neg]
      · rintro ⟨β, hβ, rfl⟩
        rcases (hS₀ β).1 hβ with ⟨i, hi, rfl⟩ | ⟨i, hi, h⟩
        · exact Or.inl ⟨i, hi, rfl⟩
        · right
          refine ⟨i, hi, ?_⟩
          rw [h, smul_neg]
    rcases (show a₀ = ⟨0, by decide⟩ ∨ a₀ = ⟨1, by decide⟩ by fin_cases a₀ <;> simp) with rfl | rfl
    ·
      refine hstd hw (S₀ := threeRootSet d4Qr₁ d4Qr₂ d4Qr₃) ?_ ?_
        (hsurv_gen _ fun β => by rw [d4Q_orbit_zero]; exact (d4Q_S₀_zero β).symm)
        (fun n'' hn'' hn''W => ?_)
      · intro β hβ
        rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl
        exacts [(d4Q_isRoot).1, IsRoot.neg (d4Q_isRoot).1, (d4Q_isRoot).2.1,
          IsRoot.neg (d4Q_isRoot).2.1, (d4Q_isRoot).2.2, IsRoot.neg (d4Q_isRoot).2.2]
      · intro β hβ
        rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · rw [neg_neg]
          exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rw [neg_neg]
          exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        · rw [neg_neg]
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := d4Q_a3_family hf hqge hn'' hn''W
        exact ⟨Unit, fun _ => P, fun _ => hPfin, fun _ => hPq, fun _ => hPQ, fun _ => hPR,
          fun _ => hPadj, fun _ y hy hyR u hu => hPnorm y hy hyR u hu,
          fun y hy hyR hcomm => hPcent y hy hyR (fun u hu => hcomm () u hu)⟩
    ·
      have hθ : IsRoot TwistTag.D4.tag (Pi.single i2 1 : Fin TwistTag.D4.tag.rank → ℤ) :=
        isRoot_single _ _
      have hρθ : permLattice TwistTag.D4.perm (Pi.single i2 1 : Fin TwistTag.D4.tag.rank → ℤ) =
          Pi.single i2 1 := by
        rw [permLattice_single, perm_i2]
      refine hstd hw (S₀ := {Pi.single i2 1, -Pi.single i2 1}) ?_ ?_
        (hsurv_gen _ fun β => by rw [d4Q_orbit_one]; exact (d4Q_S₀_one β).symm)
        (fun n'' hn'' hn''W => ?_)
      · intro β hβ
        rcases hβ with rfl | hβ
        · exact hθ
        · rw [Set.mem_singleton_iff] at hβ
          rw [hβ]
          exact IsRoot.neg hθ
      · intro β hβ
        rcases hβ with rfl | hβ
        · exact Or.inr rfl
        · rw [Set.mem_singleton_iff] at hβ
          rw [hβ, neg_neg]
          exact Or.inl rfl
      · obtain ⟨S, hSfin, hSq, hSz, hS1⟩ := d4Q_a1_data hf hqge hn'' hn''W hθ hρθ
        obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ :=
          a1_sigma_family n'' (twistHom TwistTag.D4 L Fr) hθ S hS1 hSq hSz
        exact ⟨Unit, fun _ => P, fun _ => hPfin, fun _ => hPq, fun _ => hPQ, fun _ => hPR,
          fun _ => hPadj, fun _ y hy hyR u hu => hPnorm y hy hyR u hu,
          fun y hy hyR hcomm => hPcent y hy hyR (fun u hu => hcomm () u hu)⟩

end PerX

end CFSG.RankThree.PartOne.KGD
