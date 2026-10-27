module

public import CFSG.RankThree.PartOne.KE.E7FourFrame
public import CFSG.RankThree.PartOne.KE.E7FourS0
public import CFSG.RankThree.PartOne.KE.E7D4A1Family
public import CFSG.RankThree.PartOne.KE.E7ThreeA1Family
public import CFSG.RankThree.PartOne.KE.SigmaEmbedCore

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

@[expose] def e7F4S0Set : Set (Fin Tag.E7.rank → ℤ) :=
  {α | ∃ l ∈ e7F4S0, α = toVec Tag.E7.rank l}

@[expose] def e7D4Set (c : D4A1Cert) : Set (Fin Tag.E7.rank → ℤ) :=
  (fun γ => (coxeterSystem Tag.E7).wordProd c.w • γ) ''
    parabolicRoots Tag.E7 (d4Nodes Tag.E7)

@[expose] def E7StabHyp {L : Type} [Field L] (n : ModGL .E7 L) (Fr : L →+* L) (p : ℕ) : Prop :=
  ∀ a : Fin Tag.E7.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
    rootDiagUnit .E7 a ∈ twistedTorusOf n (Units.map (entrywiseHom Fr)) →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup .E7))

section Prelim

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L ℓ]

omit [Finite K] in
theorem e7_perx_prelim (F : E7FourFrame K L ℓ f p) (hp : p.Prime)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ b : Fin Tag.E7.rank → Lˣ, b ∈ fixedCharTuples e7F4W (iterateFrobenius L ℓ f) ∧
      (∀ i, b i ^ p = 1) ∧ b ≠ 1 ∧
      rootDiagUnit .E7 b = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∧
      ∀ a, rootDiagUnit .E7 a = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 → a = b := by
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  set h : ModGL .E7 L := F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 with hhdef
  have hh' := hh
  rw [F.hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit .E7 b = h := hbh
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (adjEmb .E7 K L (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj F.g0⁻¹).toMonoidHom (MulAut.conj F.g0⁻¹).injective
        (adjEmb .E7 K L (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (adjEmb .E7 K L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective (adjEmb .E7 K L) adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbp : orderOf (rootDiagUnit .E7 b) = p := by rw [hbh']; exact hordh
  exact ⟨b, hb, pow_eq_one_of_orderOf_rootDiagUnit hbp, ne_one_of_orderOf_rootDiagUnit hp hbp,
    hbh', fun a ha => hinj0 (ha.trans hbh'.symm)⟩

end Prelim

section Core

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]

omit [Finite K] in
theorem e7_perx_hc_hkerZ (Fr : L →+* L) (g0 : ModGL .E7 L) {x c : adjointGroup .E7 K}
    {n : ModGL .E7 L} {b : Fin Tag.E7.rank → Lˣ}
    (hbh : rootDiagUnit .E7 b = g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * g0)
    (hh : g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom Fr)))
    {S : Set (Fin Tag.E7.rank → ℤ)} (hSeq : rootCharKernel b = S) :
    c * x * c⁻¹ ∈ subtorusImage (adjEmb .E7 K L) g0
        (subtorusSigma n (Units.map (entrywiseHom Fr)) S) ∧
      ∀ a : Fin Tag.E7.rank → Lˣ,
        rootDiagUnit .E7 a = g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * g0 → rootCharKernel a ⊆ S := by
  have hsub : S ⊆ rootCharKernel b := fun α hα => by rw [hSeq]; exact hα
  have hle := rootSpan_le_centralizer (K := L) b hsub
  refine ⟨?_, fun a ha => ?_⟩
  · rw [mem_subtorusImage_iff]
    refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    rw [hbh] at h1
    exact h1
  · have : a = b := rootDiagUnit_injective (ha.trans hbh.symm)
    rw [this, hSeq]

theorem e7_perx_core_of_stab (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (n g0 : ModGL .E7 L) (hg0C : g0 ∈ adjointGroup .E7 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E7 L), Finite P → P ≤ adjointGroup .E7 L →
      (∀ x ∈ P, Units.map (entrywiseHom Fr) x = x) → ⁅P, P⁆ = P → P ≤ (adjEmb .E7 K L).range)
    {p : ℕ} (hp : p.Prime) (hstab : E7StabHyp n Fr p)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    {b : Fin Tag.E7.rank → Lˣ}
    (hbh : rootDiagUnit .E7 b = g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * g0)
    (hh : g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom Fr)))
    {S : Set (Fin Tag.E7.rank → ℤ)} (hSeq : rootCharKernel b = S)
    (hS : ∀ α ∈ S, IsRoot .E7 α) (hSn : ∀ α ∈ S, -α ∈ S)
    {ι' : Type} {P : ι' → Subgroup (ModGL .E7 L)} (hPfin : ∀ i, Finite (P i))
    (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan .E7 L S)
    (hPR : ∀ i, P i ≤ twistedFixedPoints n (Units.map (entrywiseHom Fr)))
    (hPadj : ∀ i, P i ≤ adjointGroup .E7 L)
    (hPnorm : ∀ i, ∀ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L S,
      y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) → ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L S) ∧
      (∀ y, n * Units.map (entrywiseHom Fr) (ψ y) * n⁻¹ = ψ y) ∧
      (∀ y, ψ y ∈ adjointGroup .E7 L) ∧ (∀ i, P i ≤ ψ.range) ∧
      ∀ i, ∀ d : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)), ∀ u ∈ P i,
        ψ d * u * (ψ d)⁻¹ ∈ P i := by
  obtain ⟨hcS, hkerZ⟩ := e7_perx_hc_hkerZ Fr g0 hbh hh hSeq
  exact sigma_embedding_core_of_stab (adjEmb .E7 K L) adjEmb_injective adjEmb_mem
    (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFr) n g0 hg0C hg0 hperf hp
    (fun a hap ha1 haT => hstab a hap ha1 haT) hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hx c hcS
    hkerZ

end Core

section Special

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem e7_four_perx_special (hD4 : D4TranspositionLayer Tag.E7) (F : E7FourFrame K L ℓ f p)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E7.rank → Lˣ}
    (hbh : rootDiagUnit .E7 b = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0)
    (cert : D4A1Cert) (hcert : cert ∈ e7F4Certs)
    (hker : rootCharKernel b = e7F4S0Set ∪ classSetL7 e7F4Rows cert.cls) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0) ∧
      (∀ y, ψ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b)) ∧
      (∀ y, F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * F.n⁻¹ = ψ y) ∧
      (∀ y, ψ y ∈ adjointGroup .E7 L) ∧
      ∃ PD : Subgroup (ModGL .E7 L), PD ≤ ψ.range ∧ Finite PD ∧ CFSG.IsQuasisimple PD ∧
        (∀ d : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)), ∀ u ∈ PD,
          ψ d * u * (ψ d)⁻¹ ∈ PD) ∧
        (∀ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b),
          (∀ u ∈ PD, y * u = u * y) →
            y ∈ Subgroup.centralizer (rootSpan .E7 L (e7D4Set cert) : Set (ModGL .E7 L))) ∧
        (∀ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b),
          (∀ u ∈ PD, y * u = u * y) →
            ∃ h ∈ torusGroup .E7 L,
              h ∈ Subgroup.centralizer (rootSpan .E7 L (e7D4Set cert) : Set (ModGL .E7 L)) ∧
              ∃ z ∈ rootSpan .E7 L {toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r},
                y = h * z) ∧
        ({toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} ⊆ e7F4S0Set) ∧
        ∀ m : Fin Tag.E7.rank, m.val = 3 → ∃ h₀ : ModGL .E7 L, ∀ Y : SL(2, K),
          h₀ * simpleRootSL2 .E7 L m (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
            h₀⁻¹ ∈ PD := by
  classical
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hgood := e7F4_certs_good cert hcert
  obtain ⟨hr, hrS, hSigma, horth, hfix, u, hu, hcertw⟩ := D4A1Cert.sound hgood
  obtain ⟨-, -, -, -, -, -, -, hab, ha, hbl, -⟩ := hgood
  have hnC : F.n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' F.hnm
  have hnr : weylQuotientHom .E7 L ⟨F.n, F.hnm⟩ • toVec Tag.E7.rank cert.r =
      toVec Tag.E7.rank cert.r := by
    rw [F.hnW]
    exact hfix
  obtain ⟨PD, hPD, hfac, hsl⟩ := e7_d4_swap_factor hD4 hf hK
    ((coxeterSystem Tag.E7).wordProd cert.w) F.n F.hnm hnC cert.a cert.b hab
    (by rcases ha with h | h | h <;> simp [h]) (by rcases hbl with h | h | h <;> simp [h])
    (by rw [F.hnW]; exact ⟨u, hu, hcertw⟩)
  have hkerS : rootCharKernel b = e7D4Set cert ∪ {toVec Tag.E7.rank cert.r,
      -toVec Tag.E7.rank cert.r} := hker.trans hSigma
  have hroots : ∀ α ∈ e7D4Set cert, IsRoot Tag.E7 α := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul hα.1 _
  have hrootsA : ∀ α ∈ ({toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} :
      Set (Fin Tag.E7.rank → ℤ)), IsRoot Tag.E7 α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hr, IsRoot.neg hr]
  have horth' : ∀ α ∈ e7D4Set cert, ∀ β ∈ ({toVec Tag.E7.rank cert.r,
      -toVec Tag.E7.rank cert.r} : Set (Fin Tag.E7.rank → ℤ)),
        α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
    intro α hα β hβ
    rcases hβ with rfl | rfl
    · exact horth α hα
    · rw [Matrix.mulVec_neg, dotProduct_neg, horth α hα, neg_zero]
  have hS : ∀ α ∈ rootCharKernel b, IsRoot Tag.E7 α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hHN := torus_sup_union_le_normalizers (L := L) hτ hroots hrootsA horth'
  have hPQ : PD ≤ rootSpan .E7 L (rootCharKernel b) := by
    rw [hkerS, rootSpan_union_eq]
    exact (hfac.le_root ()).trans le_sup_left
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψnorm⟩ := e7_perx_core_of_stab Fr hFr F.n F.g0
    F.hg0C F.hg0 F.hperf hp hstab hx c hbh hh rfl hS hSn (P := fun _ : Unit => PD)
    (fun _ => hfac.finite ()) (fun _ => hfac.quasi ()) (fun _ => hPQ) (fun _ => hfac.le_fix ())
    (fun _ => hfac.le_adj ()) (fun _ y hy hyR u hu => by
      rw [hkerS] at hy
      exact hfac.norm () y (hHN hy).1 hyR u hu)
  refine ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, PD, hPψ (), hfac.finite (), hfac.quasi (),
    hψnorm (), ?_, ?_, ?_, hsl⟩
  · intro y hy hc
    rw [hkerS] at hy
    exact (ThetaFree.one_sided hτ hroots hrootsA horth' hfac.thetaFree hfac.le_root hy
      fun i u hu => hc u hu).2
  · intro y hy hc
    rw [hkerS] at hy
    exact (ThetaFree.one_sided hτ hroots hrootsA horth' hfac.thetaFree hfac.le_root hy
      fun i u hu => hc u hu).1
  · intro α hα
    rcases hα with rfl | rfl
    · exact hrS
    · exact e7F4_S0_neg _ hrS

omit [Finite K] [IsAlgClosure K L] [CharP L ℓ] [Fact ℓ.Prime] in
theorem commute_of_mem_torus_sup_rootSpan {S : Set (Fin Tag.E7.rank → ℤ)} {t y : ModGL .E7 L}
    (ht : t ∈ torusGroup .E7 L)
    (htC : t ∈ Subgroup.centralizer (rootSpan .E7 L S : Set (ModGL .E7 L)))
    (hy : y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L S) : y * t = t * y := by
  have hle : torusGroup .E7 L ⊔ rootSpan .E7 L S ≤ Subgroup.centralizer ({t} : Set (ModGL .E7 L)) := by
    refine sup_le (fun h hh => ?_) (fun g hg => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ hh
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (Subgroup.mem_centralizer_iff.1 htC g hg).symm
  exact (Subgroup.mem_centralizer_iff.1 (hle hy) t rfl).symm

theorem e7_four_perx_central (hD4 : D4TranspositionLayer Tag.E7) (F : E7FourFrame K L ℓ f p)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E7.rank → Lˣ}
    (hbh : rootDiagUnit .E7 b = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0)
    (hkind : rootCharKernel b = e7F4S0Set ∨ ∃ cert ∈ e7F4Certs,
      rootCharKernel b = e7F4S0Set ∪ classSetL7 e7F4Rows cert.cls) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0) ∧
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V, ∀ t ∈ torusGroup .E7 L,
          t ∈ Subgroup.centralizer (rootSpan .E7 L e7F4S0Set : Set (ModGL .E7 L)) →
            ψ v * t = t * ψ v := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  rcases hkind with hker | ⟨cert, hcert, hker⟩
  · have hS : ∀ α ∈ e7F4S0Set, IsRoot Tag.E7 α := fun α hα => by
      rw [← hker] at hα
      exact hα.1
    have hSn : ∀ α ∈ e7F4S0Set, -α ∈ e7F4S0Set := e7F4_S0_neg
    obtain ⟨ψ, hψinj, hψ, hψHQ, -⟩ := e7_perx_core_of_stab Fr hFr F.n F.g0 F.hg0C F.hg0 F.hperf
      hp hstab hx c hbh hh hker hS hSn (P := fun e : Empty => (e.elim : Subgroup (ModGL .E7 L)))
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
    refine ⟨ψ, hψinj, hψ, fun V _ _ v _ t ht htC => ?_⟩
    exact commute_of_mem_torus_sup_rootSpan ht htC (hψHQ v)
  · obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, PD, hPψ, hPfin, hPq, hPnorm, hcent, hone, hsub, hsl⟩ :=
      e7_four_perx_special hD4 F hf hK hp hstab hx c hh hbh cert hcert hker
    refine ⟨ψ, hψinj, hψ, fun V hVn hVs v hv t ht htC => ?_⟩
    have hcomm := commutes_of_quasisimple_embedding ψ hψinj PD hPψ hPq hPnorm V v hv
    obtain ⟨h, hH, -, z, hz, hyz⟩ := hone (ψ v) (hψHQ v) hcomm
    have hzS : z ∈ rootSpan .E7 L e7F4S0Set := rootSpan_mono hsub hz
    have hzt : z * t = t * z := Subgroup.mem_centralizer_iff.1 htC z hzS
    obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    have hht : h * rootDiagUnit .E7 b₁ = rootDiagUnit .E7 b₁ * h :=
      (rootDiagUnit_mul_comm_of_mem_torusGroup b₁ hH).symm
    rw [hyz]
    calc h * z * rootDiagUnit .E7 b₁ = h * (z * rootDiagUnit .E7 b₁) := by group
      _ = h * (rootDiagUnit .E7 b₁ * z) := by rw [hzt]
      _ = (h * rootDiagUnit .E7 b₁) * z := by group
      _ = (rootDiagUnit .E7 b₁ * h) * z := by rw [hht]
      _ = rootDiagUnit .E7 b₁ * (h * z) := by group

theorem e7_four_perx_sigma (hD4 : D4TranspositionLayer Tag.E7) (F : E7FourFrame K L ℓ f p)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hq4 : 4 ≤ Nat.card K)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E7.rank → Lˣ}
    (hbh : rootDiagUnit .E7 b = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0)
    (hkind : rootCharKernel b = e7F4S0Set ∨ ∃ cert ∈ e7F4Certs,
      rootCharKernel b = e7F4S0Set ∪ classSetL7 e7F4Rows cert.cls) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0) ∧
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ subtorusSigma F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
            (rootCharKernel b) := by
  classical
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hnC : F.n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' F.hnm
  have hS : ∀ α ∈ rootCharKernel b, IsRoot Tag.E7 α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  obtain ⟨hcS, hkerZ⟩ := e7_perx_hc_hkerZ Fr F.g0 hbh hh (S := rootCharKernel b) rfl
  have hfinal : ∀ {ι' : Type} (P : ι' → Subgroup (ModGL .E7 L)),
      IsSigmaFamily F.n Fr (rootCharKernel b) P →
        ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L,
          Function.Injective ψ ∧
          (∀ y, ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0) ∧
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))), V.Normal →
            Group.IsSolvable V → ∀ v ∈ V,
              ψ v ∈ subtorusSigma F.n (Units.map (entrywiseHom Fr)) (rootCharKernel b) := by
    intro ι' P hfam
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
    obtain ⟨ψ, hψinj, hψ, -, -, -, -, hψV⟩ := sigma_embedding_data_of_stab (adjEmb .E7 K L)
      adjEmb_injective adjEmb_mem (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFr) F.n
      F.g0 F.hg0C F.hg0 F.hperf hp (fun a hap ha1 haT => hstab a hap ha1 haT) hS hSn P hPfin hPq
      hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ
    exact ⟨ψ, hψinj, hψ, hψV⟩
  rcases hkind with hker | ⟨cert, hcert, hker⟩
  ·
    obtain ⟨hα, hβ, hγ⟩ := e7F4_S0_isRoot
    obtain ⟨hwα, hwβ, hwγ⟩ := e7F4_S0_fixed
    obtain ⟨o12, o13, o23⟩ := e7F4_S0_orth
    have hnv : ∀ u : Fin Tag.E7.rank → ℤ, weylQuotientHom .E7 L ⟨F.n, F.hnm⟩ • u =
        e7F4W *ᵥ u := fun u => by
      rw [F.hnW]
      exact e7F4_weylImage u
    obtain ⟨P, hfam⟩ := e7_three_a1_sigma_family (k := K) hK hq4 F.n F.hnm hα hβ hγ
      (by rw [hnv]; exact hwα) (by rw [hnv]; exact hwβ) (by rw [hnv]; exact hwγ) o12 o13 o23
    have hSeq : rootCharKernel b = ({e7F4α, -e7F4α} ∪ {e7F4β, -e7F4β} ∪ {e7F4γ, -e7F4γ} :
        Set (Fin Tag.E7.rank → ℤ)) := hker.trans e7F4_S0_eq
    exact hfinal P (by rw [hSeq]; exact hfam)
  · have hgood := e7F4_certs_good cert hcert
    obtain ⟨hr, hrS, hSigma, horth, hfix, u, hu, hcertw⟩ := D4A1Cert.sound hgood
    obtain ⟨-, -, -, -, -, -, -, hab, ha, hbl, -⟩ := hgood
    have hnr : weylQuotientHom .E7 L ⟨F.n, F.hnm⟩ • toVec Tag.E7.rank cert.r =
        toVec Tag.E7.rank cert.r := by
      rw [F.hnW]
      exact hfix
    obtain ⟨P, hfam, -, -⟩ := e7_d4a1_sigma_family hD4 hf (k := K) hK hq4
      ((coxeterSystem Tag.E7).wordProd cert.w) F.n F.hnm hnC cert.a cert.b hab
      (by rcases ha with h | h | h <;> simp [h]) (by rcases hbl with h | h | h <;> simp [h])
      (by rw [F.hnW]; exact ⟨u, hu, hcertw⟩) hr hnr horth
    have hkerS : rootCharKernel b = e7D4Set cert ∪ {toVec Tag.E7.rank cert.r,
        -toVec Tag.E7.rank cert.r} := hker.trans hSigma
    exact hfinal P (by rw [hkerS]; exact hfam)

end Special

end CFSG.RankThree.PartOne.KE
