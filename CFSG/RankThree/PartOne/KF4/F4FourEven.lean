module

public import CFSG.RankThree.PartOne.KF4.F4FourData
public import CFSG.RankThree.PartOne.KF4.B2Even
public import CFSG.RankThree.PartOne.KF4.EvenCore

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec weylMatrix_apply weylMatrix_injective)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise commutatorElement


theorem commutator_mul_mul_of_commute {G : Type*} [Group G] {z₁ z₂ q₁ q₂ : G}
    (h12 : Commute z₁ q₂) (h21 : Commute z₂ q₁) (hzz : Commute z₁ z₂)
    (h11 : Commute z₁ q₁) (h22 : Commute z₂ q₂) : ⁅z₁ * q₁, z₂ * q₂⁆ = ⁅q₁, q₂⁆ := by
  have e1 : z₁ * q₁ * (z₂ * q₂) = (z₁ * z₂) * (q₁ * q₂) := h21.symm.mul_mul_mul_comm z₁ q₂
  have e2 : z₂ * q₂ * (z₁ * q₁) = (z₁ * z₂) * (q₂ * q₁) := by
    rw [h12.symm.mul_mul_mul_comm z₂ q₁, hzz.eq.symm]
  have hA : Commute (z₁ * z₂) q₁ := h11.mul_left h21
  have hB : Commute (z₁ * z₂) q₂ := h12.mul_left h22
  have hc : Commute (z₁ * z₂) (q₁ * q₂ * (q₂ * q₁)⁻¹) :=
    (hA.mul_right hB).mul_right (hB.mul_right hA).inv_right
  calc ⁅z₁ * q₁, z₂ * q₂⁆ = (z₁ * q₁ * (z₂ * q₂)) * (z₂ * q₂ * (z₁ * q₁))⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = (z₁ * z₂) * (q₁ * q₂ * (q₂ * q₁)⁻¹) * (z₁ * z₂)⁻¹ := by
        rw [e1, e2]
        group
    _ = q₁ * q₂ * (q₂ * q₁)⁻¹ := by
        rw [hc.eq]
        group
    _ = ⁅q₁, q₂⁆ := by
        rw [commutatorElement_def]
        group

theorem inf_centralizer_derived_eq_center_map {C : Type*} [Group C] {D : Subgroup C}
    (h : ∀ d : D, (∀ a ∈ (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ : Subgroup D), d * a = a * d) →
      d ∈ Subgroup.center D) :
    D ⊓ Subgroup.centralizer ((⁅D, D⁆ : Subgroup C) : Set C) =
      (Subgroup.center D).map D.subtype := by
  have hmap : (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ : Subgroup D).map D.subtype = ⁅D, D⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  ext y
  constructor
  · intro hy
    obtain ⟨hyD, hyc⟩ := Subgroup.mem_inf.1 hy
    refine ⟨⟨y, hyD⟩, h ⟨y, hyD⟩ fun a ha => ?_, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hyc (a : C) (by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ ha)
    exact Subtype.ext h1.symm
  · rintro ⟨d, hd, rfl⟩
    refine Subgroup.mem_inf.2 ⟨d.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    rw [← hmap] at ha
    obtain ⟨a', -, rfl⟩ := ha
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hd a')

theorem f4_four_perx_even (K : Type) [Field K] [Finite K] {f : ℕ} [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = (weylMatrix f4W4) *ᵥ u)
    (g0 : ModGL .F4 L) (hg0C : g0 ∈ adjointGroup .F4 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L 2 f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .F4 L), Finite P → P ≤ adjointGroup .F4 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L 2 f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .F4 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L 2 f))) =
      (fixedCharTuples (weylMatrix f4W4) (iterateFrobenius L 2 f)).map (rootDiagUnitHom .F4 L))
    {x : adjointGroup .F4 K} (hx : orderOf x = p) (c : adjointGroup .F4 K)
    (hh : g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) →* ModGL .F4 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .F4 K L (c * (y : adjointGroup .F4 K) * c⁻¹) * g0) ∧
      (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) ∧
      (∀ b : Fin Tag.F4.rank → Lˣ,
        rootDiagUnit .F4 b = g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 →
        (rootCharKernel b).Nonempty →
        ∃ Pt : Subgroup (ModGL .F4 L), CFSG.IsQuasisimple Pt ∧ ⁅ψ.range, ψ.range⁆ = Pt ∧
          ∃ i : Fin Tag.F4.rank,
            ((i = f4Index 0 ∨ i = f4Index 1) ∨ (i = f4Index 2 ∨ i = f4Index 3)) ∧
            ∃ h₀ : ModGL .F4 L, h₀ ∈ adjointGroup .F4 L ∧
              (∀ Y : SL2 K, h₀ * simpleRootSL2 .F4 L i
                (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ ψ.range) ∧
              Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
                  Subgroup.centralizer ((⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
                    Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ :
                      Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) =
                (Subgroup.center (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))).map
                  (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))).subtype) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  set Φ : ModGL .F4 L →* ModGL .F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hordW : ¬ p ∣ Nat.card (WeylGroup .F4) := not_dvd_card_weylGroup_F4 hp hp3
  have hinj0 : Function.Injective (rootDiagUnitHom .F4 L) := rootDiagUnit_injective
  set ι : adjointGroup .F4 K →* ModGL .F4 L := adjEmb .F4 K L with hιdef
  set h : ModGL .F4 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit .F4 b = h := hbh
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbp : orderOf (rootDiagUnit .F4 b) = p := by rw [hbh']; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit .F4 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  have core : ∀ (S : Set (Fin Tag.F4.rank → ℤ)), rootCharKernel b = S →
      (∀ α ∈ S, IsRoot .F4 α) → (∀ α ∈ S, -α ∈ S) →
      ∀ {ι' : Type} (P : ι' → Subgroup (ModGL .F4 L)), (∀ i, Finite (P i)) →
        (∀ i, CFSG.IsQuasisimple (P i)) → (∀ i, P i ≤ rootSpan .F4 L S) →
        (∀ i, P i ≤ twistedFixedPoints n Φ) → (∀ i, P i ≤ adjointGroup .F4 L) →
        (∀ i, ∀ y ∈ torusGroup .F4 L ⊔ rootSpan .F4 L S, y ∈ twistedFixedPoints n Φ →
          ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) →
        (∀ y ∈ torusGroup .F4 L ⊔ rootSpan .F4 L S, y ∈ twistedFixedPoints n Φ →
          (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S) →
        ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) →* ModGL .F4 L,
          Function.Injective ψ ∧ (∀ y, ψ y = g0⁻¹ * ι (c * (y : adjointGroup .F4 K) * c⁻¹) * g0) ∧
          (∀ y, ψ y ∈ torusGroup .F4 L ⊔ rootSpan .F4 L S) ∧
          (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup .F4 L) ∧
          (∀ i, P i ≤ ψ.range) ∧
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
            Group.IsSolvable V → ∀ v ∈ V, ψ v ∈ subtorusSigma n Φ S := by
    intro S hSeq hS hSn ι' P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    have hsub : S ⊆ rootCharKernel b := fun α hα => by rw [hSeq]; exact hα
    have hle := rootSpan_le_centralizer (K := L) b hsub
    have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S) := by
      rw [mem_subtorusImage_iff]
      refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      rw [hbh'] at h1
      exact h1
    have hkerZ : ∀ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit .F4 a = h → rootCharKernel a ⊆ S :=
      fun a ha => by rw [hker a ha, hSeq]
    exact sigma_embedding_data ι adjEmb_injective adjEmb_mem Φ (adjEmb_frobenius Fr hFr) n g0
      hg0C hg0 hperf hp hordW hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ
  have hkd := f4Four_kernel_of_fixed Fr hFr hp hp3 hb hap hb1
  have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  rcases hkd with hA | ⟨v, hSeq, hrot⟩
  ·
    have hspan : rootSpan .F4 L (rootCharKernel b) = ⊥ := by
      rw [hA]
      simp [rootSpan]
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, -, hψV⟩ := core (rootCharKernel b) rfl
      (fun α hα => hα.1) hrootneg (ι' := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun y hy hyR _ => by
        rw [hspan, sup_bot_eq] at hy
        refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [hspan] at hg
        have : g = 1 := hg
        rw [this, one_mul, mul_one])
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v hv => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v hv), fun b' hb' hne => ?_⟩
    exfalso
    rw [hker b' hb', hA] at hne
    exact Set.not_nonempty_empty hne
  ·
    have hSeq' : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support := by
      rw [hSeq]
      exact Set.ext fun r => ⟨fun ⟨r₀, hr₀, h⟩ => ⟨r₀, hr₀, h.symm⟩,
        fun ⟨r₀, hr₀, h⟩ => ⟨r₀, hr₀, h.symm⟩⟩
    have hw0 : weylQuotientHom .F4 L ⟨n, hnm⟩ = f4W4 := by
      apply weylMatrix_injective
      ext i j
      rw [weylMatrix_apply, hnW (Pi.single j 1), Matrix.mulVec_single_one]
      rfl
    have hmaps : MapsRootLines n f4W4 := hw0 ▸ mapsRootLines_weylQuotientHom (⟨n, hnm⟩ :
      monomialSubgroup .F4 L)
    have hkc : Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
      rcases Nat.eq_or_lt_of_le hf with h1 | h1
      · left
        rw [hK, ← h1]
        norm_num
      · right
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h1
    obtain ⟨hfam, hdec, h₀, hh₀C, hh₀⟩ :=
      f4B2_family_even (k := K) hFr hkc n hnm f4W4 hmaps v hrot
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := core _ hSeq' (isRoot_sigmaSetB2 v)
      (neg_mem_sigmaSetB2 v) _ hPfin hPq hPQ hPR hPadj hPnorm hPcent
    set Sv : Set (Fin Tag.F4.rank → ℤ) := (fun γ => v • γ) '' parabolicRoots Tag.F4 f4B2Support
      with hSv
    set P₀ : Subgroup (ModGL .F4 L) := rootSpan .F4 L Sv ⊓ twistedFixedPoints n Φ with hP₀def
    have hsub : Sv ⊆ rootCharKernel b := fun α hα => by rw [hSeq']; exact hα
    have hlecent := rootSpan_le_centralizer (K := L) b hsub
    have hP₀ψ : ∀ z ∈ P₀, ∃ y : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
        ψ y = z := by
      intro z hz
      obtain ⟨hzQ, hzfix⟩ := Subgroup.mem_inf.1 hz
      have hzadj : z ∈ adjointGroup .F4 L := rootSpan_le_adjointGroup L _ hzQ
      have hgz : g0 * z * g0⁻¹ ∈ adjointGroup .F4 L :=
        mul_mem (mul_mem hg0C hzadj) (inv_mem hg0C)
      have hgzfix : Units.map (entrywiseHom Fr) (g0 * z * g0⁻¹) = g0 * z * g0⁻¹ := by
        have hz' : n * Φ z * n⁻¹ = z := mem_twistedFixedPoints.1 hzfix
        have h1 : Φ (g0 * z * g0⁻¹) = Φ g0 * Φ z * (Φ g0)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        calc Φ (g0 * z * g0⁻¹) = Φ g0 * Φ z * (Φ g0)⁻¹ := h1
          _ = (g0 * n) * Φ z * (g0 * n)⁻¹ := by rw [hg0]
          _ = g0 * (n * Φ z * n⁻¹) * g0⁻¹ := by group
          _ = g0 * z * g0⁻¹ := by rw [hz']
      obtain ⟨yK, hyK, hyKeq⟩ := mem_map_adjointGroup_F4_of_frobenius_fixed Fr hFr hgz hgzfix
      set y₀ : adjointGroup .F4 K := ⟨yK, hyK⟩ with hy₀
      have hι : ι y₀ = g0 * z * g0⁻¹ := hyKeq
      have hzcomm : z * rootDiagUnit .F4 b = rootDiagUnit .F4 b * z :=
        Subgroup.mem_centralizer_singleton_iff.1 (hlecent hzQ)
      have hX : ι (c * x * c⁻¹) = g0 * rootDiagUnit .F4 b * g0⁻¹ := by
        rw [hbh', hhdef]
        group
      have hcomm0 : ι y₀ * ι (c * x * c⁻¹) = ι (c * x * c⁻¹) * ι y₀ := by
        rw [hι, hX]
        calc g0 * z * g0⁻¹ * (g0 * rootDiagUnit .F4 b * g0⁻¹)
            = g0 * (z * rootDiagUnit .F4 b) * g0⁻¹ := by group
          _ = g0 * (rootDiagUnit .F4 b * z) * g0⁻¹ := by rw [hzcomm]
          _ = g0 * rootDiagUnit .F4 b * g0⁻¹ * (g0 * z * g0⁻¹) := by group
      have hmem : c⁻¹ * y₀ * c ∈ Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply adjEmb_injective (τ := .F4) (K := K) (L := L)
        change ι _ = ι _
        have hcx : ι (c * x * c⁻¹) = ι c * ι x * (ι c)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        rw [hcx] at hcomm0
        simp only [map_mul, map_inv]
        calc (ι c)⁻¹ * ι y₀ * ι c * ι x
            = (ι c)⁻¹ * (ι y₀ * (ι c * ι x * (ι c)⁻¹)) * ι c := by group
          _ = (ι c)⁻¹ * ((ι c * ι x * (ι c)⁻¹) * ι y₀) * ι c := by rw [hcomm0]
          _ = ι x * ((ι c)⁻¹ * ι y₀ * ι c) := by group
      refine ⟨⟨c⁻¹ * y₀ * c, hmem⟩, ?_⟩
      rw [hψ]
      have e : c * (c⁻¹ * y₀ * c) * c⁻¹ = y₀ := by group
      change g0⁻¹ * ι (c * (c⁻¹ * y₀ * c) * c⁻¹) * g0 = z
      rw [e, hι]
      group
    have hcomm_eq : ⁅ψ.range, ψ.range⁆ = ⁅P₀, P₀⁆ := by
      refine le_antisymm (Subgroup.commutator_le.2 ?_) (Subgroup.commutator_mono ?_ ?_)
      · rintro _ ⟨y₁, rfl⟩ _ ⟨y₂, rfl⟩
        obtain ⟨z₁, hz₁, hz₁fix, q₁, hq₁, hy₁⟩ :=
          hdec (ψ y₁) (hψHQ y₁) (mem_twistedFixedPoints.2 (hψR y₁))
        obtain ⟨z₂, hz₂, hz₂fix, q₂, hq₂, hy₂⟩ :=
          hdec (ψ y₂) (hψHQ y₂) (mem_twistedFixedPoints.2 (hψR y₂))
        have hc1 := fun q (hq : q ∈ P₀) => Subgroup.mem_centralizer_iff.1
          (Subgroup.mem_inf.1 hz₁).2 q (Subgroup.mem_inf.1 hq).1
        have hc2 := fun q (hq : q ∈ P₀) => Subgroup.mem_centralizer_iff.1
          (Subgroup.mem_inf.1 hz₂).2 q (Subgroup.mem_inf.1 hq).1
        have hzz : z₁ * z₂ = z₂ * z₁ := by
          obtain ⟨b₁, hb₁⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hz₁).1
          rw [hb₁]
          exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ (Subgroup.mem_inf.1 hz₂).1
        rw [hy₁, hy₂, commutator_mul_mul_of_commute (hc1 q₂ hq₂).symm (hc2 q₁ hq₁).symm hzz
          (hc1 q₁ hq₁).symm (hc2 q₂ hq₂).symm]
        exact Subgroup.commutator_mem_commutator hq₁ hq₂
      · intro z hz
        obtain ⟨y, hy⟩ := hP₀ψ z hz
        exact ⟨y, hy⟩
      · intro z hz
        obtain ⟨y, hy⟩ := hP₀ψ z hz
        exact ⟨y, hy⟩
    have hZ' : ∀ d : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
        (∀ a ∈ (⁅(⊤ : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))),
          (⊤ : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))))⁆ :
            Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))), d * a = a * d) →
          d ∈ Subgroup.center (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))) := by
      intro d hd
      have hψd : ψ d ∈ subtorusSigma n Φ Sv := by
        refine hPcent (ψ d) (hψHQ d) (mem_twistedFixedPoints.2 (hψR d)) ?_
        intro i u hu
        rw [← hcomm_eq] at hu
        have hu' : u ∈ (⁅(⊤ : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))),
            (⊤ : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))))⁆ :
              Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))).map ψ := by
          rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map]
          exact hu
        obtain ⟨a, ha, rfl⟩ := hu'
        rw [← map_mul, ← map_mul, hd a ha]
      rw [Subgroup.mem_center_iff]
      intro e
      have hdT : ψ d ∈ torusGroup .F4 L :=
        (mem_twistedTorusOf.1 (Subgroup.mem_inf.1 hψd).1).1
      have hdc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hψd).2
      obtain ⟨z, hz, hzfix, q, hq, hqe⟩ :=
        hdec (ψ e) (hψHQ e) (mem_twistedFixedPoints.2 (hψR e))
      have hzd : ψ d * z = z * ψ d := by
        obtain ⟨b₁, hb₁⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdT
        rw [hb₁]
        exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ (Subgroup.mem_inf.1 hz).1
      have hqd : q * ψ d = ψ d * q := hdc q (Subgroup.mem_inf.1 hq).1
      apply hψinj
      rw [map_mul, map_mul, hqe]
      calc z * q * ψ d = z * (q * ψ d) := by group
        _ = z * (ψ d * q) := by rw [hqd]
        _ = (z * ψ d) * q := by group
        _ = (ψ d * z) * q := by rw [hzd]
        _ = ψ d * (z * q) := by group
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v' hv' => subtorusSigma_le_twistedTorusOf _ _ _
      (hψV V hVn hVs v' hv'), fun b' _ _ => ⟨⁅P₀, P₀⁆, hPq (), hcomm_eq, f4Index 1,
        Or.inl (Or.inr rfl), h₀, hh₀C, fun Y => ?_, ?_⟩⟩
    · obtain ⟨y, hy⟩ := hP₀ψ _ (hh₀ Y)
      exact ⟨y, hy⟩
    · exact inf_centralizer_derived_eq_center_map hZ'


theorem odd_sq_add_one_of_two_pow {f : ℕ} (hf : 1 ≤ f) : Odd ((2 ^ f) ^ 2 + 1) := by
  have h : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have h2 : Even ((2 ^ f) ^ 2) := Nat.even_pow.2 ⟨h, by norm_num⟩
  exact h2.add_one

section Main


theorem f4_four_main_even (K : Type) [Field K] [Finite K] {f : ℕ} [CharP K 2] (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = (weylMatrix f4W4) *ᵥ u) :
    (∀ x : adjointGroup .F4 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V)) ∧
    (∀ B : Subgroup (MulAut (adjointGroup .F4 K)),
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .F4 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
        ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (adjointGroup .F4 K))))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := f4_four_frame K hf hK hp hp3 hΦ L n hnm hnW
  have hqodd : Odd ((Nat.card K) ^ 2 + 1) := by
    rw [hK]
    exact odd_sq_add_one_of_two_pow hf
  have hsolv : ∀ x : adjointGroup .F4 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V) := by
    intro x hx V hVn hVs
    have hpg : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨c, hc⟩ := hconj _ hpg
    have hh := hc x (Subgroup.mem_zpowers x)
    obtain ⟨ψ, hψinj, -, hψV, -⟩ := f4_four_perx_even K hK hf hp hp3 L n hnm hnW g0 hg0C hg0 hperf
      hT hx c hh
    by_contra hnodd
    have h2 : 2 ∣ Nat.card V := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hv2 : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))) = 2 := by
      rw [orderOf_injective ψ hψinj, Subgroup.orderOf_coe, hv]
    have hmem := hψV V hVn hVs v v.2
    rw [hT] at hmem
    obtain ⟨b', hb', hb'v⟩ := hmem
    have hdvd : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))) ∣
        (Nat.card K) ^ 2 + 1 := by
      rw [← hb'v]
      exact (orderOf_map_dvd (rootDiagUnitHom .F4 L) b').trans
        (f4Four_orderOf_dvd (iterateFrobenius L 2 f) (q := Nat.card K) (fun c => by
          rw [hK]
          exact iterateFrobenius_def 2 f c) hb')
    rw [hv2] at hdvd
    exact (Nat.not_even_iff_odd.2 hqodd) (even_iff_two_dvd.2 hdvd)
  refine ⟨hsolv, ?_⟩
  intro B hB A hAB hA hcard hAin
  have hC : Subgroup.center (adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup .F4 K) :=
    A.comap (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    have h1 : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) (q ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ hq
    exact hIntinj (h1.trans (map_one _).symm)
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  obtain ⟨x, hxA, hx1, b, hb, hne⟩ := f4_four_exists_nonregular K hp L n g0 A₀ hA₀card hA₀exp c hc
    (f4Index 1)
  have hxp : orderOf x = p := orderOf_eq_prime (hA₀exp x hxA) hx1
  have hxA' : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) x ∈ A := by
    rw [← hA₀map]
    exact ⟨x, hxA, rfl⟩
  obtain ⟨ψ, hψinj, hψ, -, hψK⟩ := f4_four_perx_even K hK hf hp hp3 L n hnm hnW g0 hg0C hg0 hperf
    hT hxp c (hc x hxA)
  obtain ⟨Pt, hPq, hcomm, i, hi, h₀, hh₀C, hψr, hZ⟩ := hψK b hb hne
  refine ⟨MulAut.conj x, hxA', fun h1 => hx1 (hIntinj (by rw [h1, map_one])), ?_⟩
  exact f4_even_core_odd_of_embedding K hf hK L hp hB c g0 hg0C ψ hψinj hψ hPq hcomm i h₀ hh₀C
    (Or.inr ⟨hψr, hZ⟩) (hsolv x hxp)

end Main

section Final


theorem planeLocalCoreOdd_F4_four_even (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 4).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup .F4 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hK
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hout := F4_outer_commutator_odd K
  have hcore := localCoreTrivialOn_noninner_F4 K hp hp3
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by simpa [exhaustionPhi] using hpf
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + 1) p).2 hpq
    simpa using this
  have hcm := canonicalRep_mem_monomialSubgroup L f4W4
  have hπ : weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W4, hcm⟩ = f4W4 :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep f4W4)
  have hnW : ∀ u, weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W4, hcm⟩ • u =
      (weylMatrix f4W4) *ᵥ u := fun u => by
    rw [hπ, weylMatrix_mulVec]
  have h := f4_four_main_even K hf hK hp hp3 hΦ L _ hcm hnW
  exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore h.2

theorem oddEndpoint_F4_evenPhi4 :
    OddEndpoint .F4 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 4 ℓ f := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨rfl, hc2⟩ := hc
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (planeLocalCoreOdd_F4_four_even K hf hK hp hp3 (by simpa [cycloVal, hK] using hc2))).1

end Final

end CFSG.RankThree.PartOne.KF4
