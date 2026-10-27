module

public import CFSG.RankThree.PartOne.KE.E7ThreeFrame
public import CFSG.RankThree.PartOne.KE.E7FourPerX
public import CFSG.RankThree.PartOne.KE.E7ThreeLattice
public import CFSG.RankThree.PartOne.KE.E7ThreeLayers

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

section Prelim

variable {K : Type} [Field K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L ℓ] {ε : ℤ}

theorem e7_three_prelim (F : E7ThreeFrame K L ℓ f p ε) (hp : p.Prime)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ b : Fin Tag.E7.rank → Lˣ, b ∈ fixedCharTuples (ε • e7T3W) (iterateFrobenius L ℓ f) ∧
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

section Arith

theorem e7T3_q_gt_two {p q : ℕ} (hp3 : 3 < p) {ε : ℤ} (hε : ε = -1) (hq : 2 ≤ q)
    (hpq : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) : ε = -1 → 2 < q := by
  intro _
  by_contra hle
  have hq2 : q = 2 := by omega
  subst hq2
  subst hε
  have h3 : (p : ℤ) ∣ 3 := by simpa using hpq
  have := Int.le_of_dvd (by norm_num) h3
  omega

end Arith

section Core

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}

theorem e7_three_perx (hLay : E7ThreeLayers) (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E7.rank → Lˣ} (hb : b ∈ fixedCharTuples (ε • e7T3W) (iterateFrobenius L ℓ f))
    (hap : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1)
    (hbh : rootDiagUnit .E7 b = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0) :
    ∃ (ι' : Type) (P : ι' → Subgroup (ModGL .E7 L))
      (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L),
      IsSigmaFamily F.n (iterateFrobenius L ℓ f) (rootCharKernel b) P ∧
      Function.Injective ψ ∧
      (∀ y, ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0) ∧
      (∀ y, ψ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b)) ∧
      (∀ y, F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * F.n⁻¹ = ψ y) ∧
      (∀ y, ψ y ∈ adjointGroup .E7 L) ∧ (∀ i, P i ≤ ψ.range) ∧
      (∀ i, ∀ d : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)), ∀ u ∈ P i,
        ψ d * u * (ψ d)⁻¹ ∈ P i) ∧
      (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ subtorusSigma F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
            (rootCharKernel b)) ∧
      ((Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1 : Fin Tag.E7.rank → ℤ) ∈ rootCharKernel b →
        ∃ (i₀ : ι') (m : Fin Tag.E7.rank) (h₀ : ModGL .E7 L), ∀ Y : SL(2, K),
          h₀ * simpleRootSL2 .E7 L m (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈
            P i₀) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + (ε : ZMod p) * (Nat.card K : ℕ) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) p).2
      hpf
    simpa using this
  have hq2 : ε = -1 → 2 < ℓ ^ f := by
    intro hε1
    have hKq : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [← hK]
    exact e7T3_q_gt_two hp3 hε1 hKq hpf hε1
  have hnC : F.n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' F.hnm
  have hS : ∀ α ∈ rootCharKernel b, IsRoot Tag.E7 α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  obtain ⟨hcS, hkerZ⟩ := e7_perx_hc_hkerZ (K := K) Fr F.g0 hbh hh (S := rootCharKernel b) rfl
  have hlayer : E7Layer F.n Fr (rootCharKernel b) K := by
    rcases e7T3_kernel_structure Fr hFr hp hp3 hε hΦ hb hap hb1 with h | ⟨cert, hcert, h, hgood⟩
    · rw [h]
      exact e7Layer_empty F.n Fr K
    · rw [h]
      exact hLay L ℓ f hf K hK ε hε hq2 F.n F.hnm hnC F.hnW cert hcert hgood
  obtain ⟨ι', P, hfam, hdesc⟩ := hlayer
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := sigma_embedding_data_of_stab
    (adjEmb .E7 K L) adjEmb_injective adjEmb_mem (Units.map (entrywiseHom Fr))
    (adjEmb_frobenius Fr hFr) F.n F.g0 F.hg0C F.hg0 F.hperf hp
    (fun a hap ha1 haT => hstab a hap ha1 haT) hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c
    hcS hkerZ
  exact ⟨ι', P, ψ, ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩, hψinj, hψ, hψHQ, hψR, hψadj,
    hPψ, fun i d u hu => hPnorm i (ψ d) (hψHQ d) (hψR d) u hu, hψV, hdesc⟩

end Core

end CFSG.RankThree.PartOne.KE
