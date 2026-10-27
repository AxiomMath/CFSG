module

public import CFSG.RankThree.PartOne.KEXC.KeyBalanced
public import CFSG.RankThree.PartOne.KEXC.TorusConj
public import CFSG.RankThree.PartOne.KLR.StarRad
public import CFSG.RankThree.PartOne.KLR.FrobTrick

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLR
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem mem_normalizer_map {G H : Type*} [Group G] [Group H] (f : G →* H) {S : Subgroup G}
    {x : G} (hx : x ∈ Subgroup.normalizer (S : Set G)) :
    f x ∈ Subgroup.normalizer ((S.map f : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx s).1 hs, by simp [map_mul, map_inv]⟩
  · rintro ⟨s', hs', hh⟩
    refine ⟨x⁻¹ * s' * x, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * s' * x)).2 (by simpa [mul_assoc] using hs')
    · rw [map_mul, map_mul, map_inv, hh]
      group

section Torus

variable {L : Type} [Field L]

theorem rootDiagUnit_pow_eq {τ : Tag} (b : Fin τ.rank → Lˣ) (n : ℕ) :
    rootDiagUnit τ b ^ n = rootDiagUnit τ (b ^ n) :=
  (map_pow (rootDiagUnitHom τ L) b n).symm

theorem pow_eq_one_of_rootDiagUnit_pow_eq_one {p : ℕ} {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (h : rootDiagUnit ReeTag.F4.tag b ^ p = 1) : ∀ i, b i ^ p = 1 := by
  have h1 : rootDiagUnit ReeTag.F4.tag (b ^ p) = 1 := by
    rw [← rootDiagUnit_pow_eq]
    exact h
  have h2 : b ^ p = 1 := rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
  exact fun i => congrFun h2 i

variable [CharP L 2] [IsAlgClosed L]

theorem involution_mem_rootSpan {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hbp : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1)
    {y : ModGL ReeTag.F4.tag L} (hy : y ∈ adjointGroup ReeTag.F4.tag L)
    (hcomm : y * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * y)
    (hy2 : y * y = 1) : y ∈ rootSpan ReeTag.F4.tag L (rootCharKernel b) := by
  have hordW : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) := not_dvd_card_weylGroup_F4 hp hp3
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨(isRoot_neg_iff).2 hα.1, by rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2]; simp⟩
  have hHQ := mem_torus_mul_rootSpan_of_commute hp hordW hbp hb1 hS hSn (fun _ h => h) hy hcomm
  have : ExpChar L 2 := ExpChar.prime Nat.prime_two
  have : PerfectRing L 2 := PerfectField.toPerfectRing 2
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃+* L, ∀ c, σ c = c ^ 2 :=
    ⟨frobeniusEquiv L 2, fun c => by simp [frobeniusEquiv_apply, frobenius_def]⟩
  exact mem_rootSpan_of_mul_self_eq_one σ hσ hS hHQ hy2

end Torus

section Balanced

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] [IsAlgClosed L] (D : ReeFrameData K L a)

theorem exists_root_trivial_on (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K - 1) {E R₀ : Subgroup (ModGL ReeTag.F4.tag L)}
    (hEN : E ≤ Subgroup.normalizer (R₀ : Set (ModGL ReeTag.F4.tag L)))
    (hR0 : R₀ ≠ ⊥) (hR2 : IsPGroup 2 R₀)
    (hEtw : E ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))
    (hEp : ∀ x ∈ E, x ^ p = 1)
    {b₀ : Fin ReeTag.F4.tag.rank → Lˣ} (hb₀E : rootDiagUnit ReeTag.F4.tag b₀ ∈ E)
    (hb₀1 : b₀ ≠ 1)
    (hR₀S : R₀ ≤ rootSpan ReeTag.F4.tag L (rootCharKernel b₀) ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    ∃ α, α ∈ rootCharKernel b₀ ∧ ∀ b : Fin ReeTag.F4.tag.rank → Lˣ,
      rootDiagUnit ReeTag.F4.tag b ∈ E → rootChar b α = 1 := by
  classical
  have hbp : ∀ b : Fin ReeTag.F4.tag.rank → Lˣ, rootDiagUnit ReeTag.F4.tag b ∈ E →
      ∀ i, b i ^ p = 1 := fun b hb =>
    pow_eq_one_of_rootDiagUnit_pow_eq_one (hEp _ hb)
  have hp2 : p ≠ 2 := by omega
  have hb₀tw := hEtw hb₀E
  have hw := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff D.isFrob w b₀).1 hb₀tw
  obtain ⟨u, J, hJ, hΦ⟩ := exists_balanced_conj (a := a) hp hp3 (hbp b₀ hb₀E) hb₀1 hw
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  set ū := canonicalRep (coxeterSystem ReeTag.F4.tag) L u with hū
  have hS : ∀ α ∈ rootCharKernel b₀, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hst : ∀ β, IsRoot ReeTag.F4.tag β →
      (w • ReeTag.F4.dualRoot β ∈ rootCharKernel b₀ ↔ β ∈ rootCharKernel b₀) := fun β hβ =>
    mem_kernel_iff_smul_dualRoot hp hp2 (hbp b₀ hb₀E) hw hβ
  have hFN : Fext D.F ū =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm u) :=
    D.isFrob.fext_canonicalRep u
  have hNad : ū ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L u
  have hnad : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  have hn'ad : ū * n * (Fext D.F ū)⁻¹ ∈ adjointGroup ReeTag.F4.tag L :=
    mul_mem (mul_mem hNad hnad) (inv_mem (Fext_mem D.F hNad))
  have hperm : PermAct (ū * n * (Fext D.F ū)⁻¹) (u * w * (ReeTag.F4.weylPerm u)⁻¹) := by
    rw [hFN]
    exact ((permAct_canonicalRep u).mul (permAct_canonicalRep w)).mul
      (permAct_canonicalRep (ReeTag.F4.weylPerm u)).inv
  have hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)),
      (u * w * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈
        parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) :=
    fun γ hγ => smul_dualRoot_mem_parabolic hS w u hst hΦ hγ
  have hmap := map_conj_rootSpan_inf_twistedFixed (F := D.F) u hS n
  rw [hΦ] at hmap
  set R : Subgroup (ModGL ReeTag.F4.tag L) := R₀.map (MulAut.conj ū).toMonoidHom with hR
  have hRP : R ≤ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (J : Set (Fin ReeTag.F4.tag.rank))) ⊓ twistedFixed D.F (ū * n * (Fext D.F ū)⁻¹) := by
    rw [← hmap]
    exact Subgroup.map_mono hR₀S
  have hR0' : R ≠ ⊥ := fun h =>
    hR0 ((Subgroup.map_eq_bot_iff_of_injective R₀ (MulAut.conj ū).injective).1 h)
  have hR2' : IsPGroup 2 R := hR2.map _
  obtain ⟨α₀, hα₀⟩ : (rootCharKernel b₀).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hR0
    rw [eq_bot_iff]
    intro x hx
    have h1 := (hR₀S hx).1
    have h2 : rootSpan ReeTag.F4.tag L (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    rw [hne, h2] at h1
    exact h1
  refine ⟨α₀, hα₀, fun b hb => ?_⟩
  have hbp' := hbp b hb
  obtain ⟨b', hb'conj, hb'char⟩ := exists_rootDiagUnit_conj (L := L) (τ := ReeTag.F4.tag) u b
  have hb'p : ∀ k, b' k ^ p = 1 := by
    intro k
    have h1 : b' k = rootChar b' (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
      (CTTorus.rootChar_single b' k).symm
    have h2 : rootChar b' (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        rootChar b (u⁻¹ • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) := by
      conv_lhs => rw [← smul_inv_smul u (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)]
      exact hb'char _
    rw [h1, h2]
    exact CTTorus.rootChar_pow_eq_one hbp' _
  have hbtw := hEtw hb
  have hb'fix : rootDiagUnit ReeTag.F4.tag b' ∈ twistedFixed D.F (ū * n * (Fext D.F ū)⁻¹) := by
    rw [hb'conj]
    exact (conj_mem_twistedFixed_iff hNad hbtw.1).2 hbtw
  have hb'N : rootDiagUnit ReeTag.F4.tag b' ∈
      Subgroup.normalizer (R : Set (ModGL ReeTag.F4.tag L)) := by
    rw [hb'conj]
    exact mem_normalizer_map (MulAut.conj ū).toMonoidHom (hEN hb)
  have hk := key_balanced D ha hK hn'ad hperm hJ hstab hp hp2 hpq hR0' hR2' hRP hb'p hb'fix hb'N
  have hα₀J : u • α₀ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) := by
    rw [← hΦ]
    exact ⟨α₀, hα₀, rfl⟩
  have h3 := rootChar_eq_one_of_support hk hα₀J
  rw [hb'char] at h3
  exact h3

end Balanced

end CFSG.RankThree.PartOne.KEXC
