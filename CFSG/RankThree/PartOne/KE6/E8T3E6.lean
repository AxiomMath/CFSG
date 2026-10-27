module

public import CFSG.RankThree.PartOne.KE.SigmaTransport
public import CFSG.RankThree.PartOne.KE.E8A2NativeModuleCertificate1952Inputs

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

@[expose] def e6Nodes (τ : Tag) : Set (Fin τ.rank) := {i | i.val ≤ 5}

@[expose] def E6Layer (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∀ α ∈ parabolicRoots τ (e6Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α ∈ parabolicRoots τ (e6Nodes τ)) →
      (∀ α ∈ parabolicRoots τ (e6Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • weylQuotientHom τ L ⟨n, hn⟩ • α +
          ε • (weylQuotientHom τ L ⟨n, hn⟩ • α) + α = 0) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (parabolicRoots τ (e6Nodes τ)),
        (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (rootSpan τ L (parabolicRoots τ (e6Nodes τ)) : Set (ModGL τ L))) ∧
      ∀ (m : Fin τ.rank), m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L] [IsAlgClosure k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P

variable {L : Type} [Field L]

theorem e8_e6_family (hE6 : E6Layer Tag.E8) [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.E8)
    (n : ModGL Tag.E8 L) (hn : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hmaps : ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v) • α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8))
    (hrel : ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v) • (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v) • α +
        ε • ((v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v) • α) + α = 0) :
    ∃ P : Unit → Subgroup (ModGL Tag.E8 L),
      IsSigmaFamily n (iterateFrobenius L ℓ f)
        ((fun γ => v • γ) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8)) P ∧
      P () = rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      ∃ h₀ : ModGL Tag.E8 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E8 L (e8Index 3)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P () := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L v
  have hVadj : V ∈ adjointGroup Tag.E8 L := canonicalRep_mem_adjointGroup _ L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  set n' : ModGL Tag.E8 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVm) hn) hVm
  have hn'adj : n' ∈ adjointGroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVadj) hnC) hVadj
  have hπV : weylQuotientHom Tag.E8 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E8 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E8 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hn⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  set P' : Subgroup (ModGL Tag.E8 L) :=
    rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) ⊓ twistedFixedPoints n' Φ
    with hP'
  obtain ⟨hfin, hq, hcent, hsl⟩ := hE6 L ℓ f hf ε hε n' hn'm hn'adj
    (by rw [hπn']; exact hmaps) (by rw [hπn']; exact hrel) P' rfl
  have hroots : ∀ r ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8), IsRoot Tag.E8 r := fun r hr => hr.1
  have hHN : torusGroup Tag.E8 L ≤ Subgroup.normalizer
      (rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) : Set (ModGL Tag.E8 L)) :=
    CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hroots
  have hfam : IsSigmaFamily n' Fr (parabolicRoots Tag.E8 (e6Nodes Tag.E8))
      (fun _ : Unit => P') := by
    refine ⟨fun _ => hfin, fun _ => hq, fun _ => inf_le_left, fun _ => inf_le_right,
      fun _ => inf_le_left.trans (rootSpan_le_adjointGroup L _), fun _ y hy hyR u hu => ?_,
      fun y hy hyR hcomm => ?_⟩
    · have hyN : y ∈ Subgroup.normalizer
          (rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) : Set (ModGL Tag.E8 L)) :=
        (sup_le hHN Subgroup.le_normalizer) hy
      have hyR' : y ∈ twistedFixedPoints n' Φ := hyR
      have hu2 : u ∈ twistedFixedPoints n' Φ := hu.2
      have hR : y * u * y⁻¹ ∈ twistedFixedPoints n' Φ :=
        mul_mem (mul_mem hyR' hu2) (inv_mem hyR')
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hyN u).1 hu.1, hR⟩
    · obtain ⟨hyH, hyC⟩ := hcent y hy (fun u hu => hcomm () u hu)
      exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hyC⟩
  have htr := isSigmaFamily_transport Fr hFrbij v n hroots hfam
  set c₀ : ModGL Tag.E8 L →* ModGL Tag.E8 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  refine ⟨fun _ => P'.map c₀, htr, ?_, ?_⟩
  · have hQ : (rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8))).map c₀ =
        rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8)) :=
      map_conj_rootSpan v hroots
    have hR : (twistedFixedPoints n' Φ).map c₀ = twistedFixedPoints n Φ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hcapp]
        exact (mem_twistedFixedPoints_conj hΦV).1 hx
      · intro hy
        refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
        · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
          rw [e]
          exact hy
        · rw [hcapp]
          group
    show P'.map c₀ = _
    rw [hP', Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]
  · obtain ⟨h₀, hh₀⟩ := hsl (e8Index 3) rfl k hk
    refine ⟨V * h₀, fun Y => ?_⟩
    refine ⟨h₀ * simpleRootSL2 Tag.E8 L (e8Index 3)
      (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹, hh₀ Y, ?_⟩
    rw [hcapp]
    group

end CFSG.RankThree.PartOne.KE6
