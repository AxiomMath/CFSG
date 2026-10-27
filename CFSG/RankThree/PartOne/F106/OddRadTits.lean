module

public import CFSG.RankThree.PartOne.F106.OddRadGen
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.RankThree.PartOne.TCX.Ree.A1Layer
public import CFSG.RankThree.PartOne.TCX.Ree.B2Layer
public import CFSG.RankThree.PartOne.TCX.Plane
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.CharacterTheory.Burnside
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.RankThree.PartOne.F106.OddRadTools
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.KLR.SectorTori
public import CFSG.RankThree.PartOne.KLR.StarRad
public import CFSG.RankThree.PartOne.TCF.Pow2
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.TCX
  CFSG.RankThree.PartOne.TCX.Ree CFSG.RankThree.PartOne.TCF
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.LieType.Ree.ReeTag (reeFixedEquivReeGamma)

open scoped Pointwise commutatorElement

set_option linter.unusedSectionVars false

theorem isSolvable_of_card_eq_pow_mul_pow {G : Type*} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rwa [← Nat.card_eq_fintype_card])

section Layer

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] [IsAlgClosed L] (D : ReeFrameData K L a)

theorem solvable_parabolic_fixed_zero (ha0 : a = 0) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} (hn' : n' ∈ adjointGroup ReeTag.F4.tag L)
    {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    {J : Finset (Fin ReeTag.F4.tag.rank)} (hJ : BalancedSupport J)
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)),
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
        (J : Set (Fin ReeTag.F4.tag.rank))) :
    Group.IsSolvable ↥(rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (J : Set (Fin ReeTag.F4.tag.rank))) ⊓ twistedFixed D.F n') := by
  classical
  subst ha0
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hSL2 : Group.IsSolvable (SL2 K) := by
    refine isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 1) (b := 1)
      Nat.prime_two Nat.prime_three (by norm_num) ?_
    rw [CFSG.RankThree.PartOne.TCX.card_SL2', hK2]
    norm_num
  have hSz : Group.IsSolvable ↥(suzukiGroup 0 K) := by
    refine isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 5) (a := 2) (b := 1)
      Nat.prime_two Nat.prime_five (by norm_num) ?_
    rw [CFSG.LieType.Ree.suzuki_order hK]
    norm_num
  rcases hJ with rfl | h02 | h03 | h13 | h12
  · rw [rootSpan_parabolicRoots_empty, bot_inf_eq]
    infer_instance
  · have hJ : J = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h02 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    obtain ⟨⟨e⟩, -⟩ := a1_level D a1Pair_zero_two hK hn' hperm hstab
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · have hJ : J = ({⟨0, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h03 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    obtain ⟨⟨e⟩, -⟩ := a1_level D a1Pair_zero_three hK hn' hperm hstab
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · have hJ : J = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h13 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    obtain ⟨⟨e⟩, -⟩ := a1_level D a1Pair_one_three hK hn' hperm hstab
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · have hJs : (J : Set (Fin ReeTag.F4.tag.rank)) = f4B2Support := by
      ext k
      constructor
      · intro hk
        have hk' := (h12 k).1 hk
        refine (mem_f4B2Support k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      · intro hk
        have hk' := (mem_f4B2Support k).1 hk
        refine (h12 k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (congrArg Fin.val h)
        · exact Or.inr (congrArg Fin.val h)
    rw [hJs] at hstab ⊢
    obtain ⟨⟨e⟩, -⟩ := b2_level D hK hperm hstab
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem starSolvable_zero (ha0 : a = 0) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p)
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    Group.IsSolvable ↥(rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) := by
  have hbp := pow_eq_one_of_orderOf_rootDiagUnit hord
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hord
  have hw := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff D.isFrob w b).1 hb
  obtain ⟨u, J, hJ, hΦ⟩ := exists_balanced_conj (a := a) hp hp3 hbp hb1 hw
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hst : ∀ β, IsRoot ReeTag.F4.tag β →
      (w • ReeTag.F4.dualRoot β ∈ rootCharKernel b ↔ β ∈ rootCharKernel b) := fun β hβ =>
    mem_kernel_iff_smul_dualRoot hp (by omega) hbp hw hβ
  have hFN : Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm u) :=
    D.isFrob.fext_canonicalRep u
  have hNad : canonicalRep (coxeterSystem ReeTag.F4.tag) L u ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L u
  have hnad : canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L w
  have hn'ad : canonicalRep (coxeterSystem ReeTag.F4.tag) L u *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      (Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹ ∈
      adjointGroup ReeTag.F4.tag L :=
    mul_mem (mul_mem hNad hnad) (inv_mem (Fext_mem D.F hNad))
  have hperm : PermAct (canonicalRep (coxeterSystem ReeTag.F4.tag) L u *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      (Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹)
      (u * w * (ReeTag.F4.weylPerm u)⁻¹) := by
    rw [hFN]
    exact ((permAct_canonicalRep u).mul (permAct_canonicalRep w)).mul
      (permAct_canonicalRep (ReeTag.F4.weylPerm u)).inv
  have key := solvable_parabolic_fixed_zero D ha0 hK hn'ad hperm hJ
    (fun γ hγ => smul_dualRoot_mem_parabolic hS w u hst hΦ hγ)
  have hmap := map_conj_rootSpan_inf_twistedFixed (F := D.F) u hS
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
  rw [hΦ] at hmap
  have hsolv : Group.IsSolvable ↥((rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)).map
      (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).toMonoidHom) := by
    rw [hmap]
    exact key
  let e := Subgroup.equivMapOfInjective (rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).injective
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end Layer

section Main

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

theorem solvable_centralizer_of_frame {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hconj : ∀ x : ReeTag.F4.reeGamma K a, orderOf x = p →
      ∃ c : ReeTag.F4.reeGamma K a,
        g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ ∈ torusGroup ReeTag.F4.tag L)
    (hrad : ∀ b : Fin ReeTag.F4.tag.rank → Lˣ,
      orderOf (rootDiagUnit ReeTag.F4.tag b) = p →
      rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D.F n →
      Group.IsSolvable ↥(rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D.F n))
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨c, hcH⟩ := hconj x hx
  let ψ : ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag L :=
    ((MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a)).comp (MulAut.conj c).toMonoidHom
  have hψ : ∀ d, ψ d = g₀⁻¹ * thetaGamma L a (c * d * c⁻¹) * g₀ := fun d => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro d₁ d₂ h
    rw [hψ, hψ] at h
    have h1 := mul_left_cancel (mul_right_cancel h)
    have h2 := mul_left_cancel (mul_right_cancel (thetaGamma_injective L h1))
    exact h2
  have hψmem : ∀ d, ψ d ∈ adjointGroup ReeTag.F4.tag L := fun d => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg₀) (thetaGamma_mem_adjointGroup L _)) hg₀
  have hψtw : ∀ d, ψ d ∈ twistedFixed D.F n := fun d => by
    rw [hψ]
    exact conj_mem_twistedFixed D.F hg₀ hFg₀ (thetaGamma_mem_adjointGroup L _) (D.fext_theta _)
  have hy : ψ x = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ := hψ x
  have hyH : ψ x ∈ torusGroup ReeTag.F4.tag L := by rw [hy]; exact hcH
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
  have hordy : orderOf (rootDiagUnit ReeTag.F4.tag b) = p := by
    rw [← hb, orderOf_injective ψ hψinj x]
    exact hx
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hordy
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hordy
  have hordW : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) := not_dvd_card_weylGroup_F4 hp hp3
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨(isRoot_neg_iff).2 hα.1, by rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2]; simp⟩
  have hcommh : ∀ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * ψ d := by
    intro d hd
    rw [← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.1 hd
  have hHQ : ∀ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d ∈ (torusGroup ReeTag.F4.tag L : Set (ModGL ReeTag.F4.tag L)) *
        (rootSpan ReeTag.F4.tag L (rootCharKernel b) : Set (ModGL ReeTag.F4.tag L)) :=
    fun d hd => mem_torus_mul_rootSpan_of_commute hp hordW hap ha1 hS hSn (fun _ h => h)
      (hψmem d) (hcommh d hd)
  set P : Subgroup (ModGL ReeTag.F4.tag L) :=
    rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D.F n with hP
  have hPs : Group.IsSolvable ↥P := hrad b hordy (by rw [← hb]; exact hψtw x)
  set C : Subgroup (ReeTag.F4.reeGamma K a) :=
    Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) with hC
  have hcomm : ∀ d₁ ∈ C, ∀ d₂ ∈ C, ψ ⁅d₁, d₂⁆ ∈ P := by
    intro d₁ hd₁ d₂ hd₂
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hT : ψ d₁ * ψ d₂ * (ψ d₁)⁻¹ * (ψ d₂)⁻¹ ∈ twistedFixed D.F n :=
      (twistedFixed D.F n).mul_mem ((twistedFixed D.F n).mul_mem
        ((twistedFixed D.F n).mul_mem (hψtw d₁) (hψtw d₂))
        ((twistedFixed D.F n).inv_mem (hψtw d₁))) ((twistedFixed D.F n).inv_mem (hψtw d₂))
    exact ⟨commutator_mem_rootSpan hS (hHQ d₁ hd₁) (hHQ d₂ hd₂), hT⟩
  let ψC : ↥C →* ModGL ReeTag.F4.tag L := ψ.comp C.subtype
  have hψC : Function.Injective ψC := hψinj.comp Subtype.val_injective
  have hcle : commutator ↥C ≤ P.comap ψC := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    exact hcomm (g₁ : _) g₁.2 (g₂ : _) g₂.2
  let φ : ↥(commutator ↥C) →* ↥P :=
    ((ψC.comp (commutator ↥C).subtype)).codRestrict P fun g => hcle g.2
  have hφ : Function.Injective φ := fun g₁ g₂ h =>
    Subtype.ext (hψC (congrArg Subtype.val h))
  have hcs : Group.IsSolvable ↥(commutator ↥C) := Group.isSolvable_of_isSolvable_injective hφ
  refine Group.isSolvable_of_ker_le_range (commutator ↥C).subtype
    (Abelianization.of : ↥C →* Abelianization ↥C) ?_
  rw [Abelianization.ker_of, Subgroup.range_subtype]

end Main

section Zero

theorem solvable_centralizer_ree_zero {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2) (x : ReeTag.F4.reeGamma K 0)
    (hx : orderOf x = 5) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 0))) := by
  classical
  have hK1 : Nat.card K = 2 ^ (2 * 0 + 1) := by rw [hK]; norm_num
  have hp : (5 : ℕ).Prime := by norm_num
  have hp3 : 3 < 5 := by norm_num
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK1
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h5 : 5 ∣ (2 ^ (2 * 0 + 1)) ^ 2 + 1 := by norm_num
  rcases dvd_phi4_cases (a := 0) hp hp3 h5 with ⟨hpp, -⟩ | ⟨hpm, -⟩
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4p D.isFrob
    obtain ⟨g₀, hg₀, hFg₀, hconj⟩ := sector_hconj D _ E hEH hEF _ hE hp
      (pow_factorization_card_reeGamma_dvd_phi4p hK1 hp hp3 hpp)
    exact solvable_centralizer_of_frame D hg₀ hFg₀ hp hp3 hconj
      (fun b hordb hbT => starSolvable_zero D rfl hK1 _ hp hp3 hordb hbT) x hx
  · exfalso
    norm_num at hpm

end Zero

section Tits

open CFSG.Sporadic.Schreier.Tits


theorem oddRadConcl_titsD (β : MulAut ↥titsD) (hβ : orderOf β = 5) : OddRadConcl ↥titsD β := by
  classical
  obtain ⟨hp2, -⟩ := AT_Tits_derived_group_Schreier
  have hβinn : β ∈ inner ↥titsD := by
    let q : Outer ↥titsD := (QuotientGroup.mk β : Outer ↥titsD)
    obtain ⟨k, hk⟩ := hp2 q
    have h5 : q ^ 5 = 1 := by
      have : β ^ 5 = 1 := by
        have := pow_orderOf_eq_one β
        rwa [hβ] at this
      show (QuotientGroup.mk β : Outer ↥titsD) ^ 5 = 1
      rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
    have hd5 : orderOf q ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have hd2 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h1 : orderOf q = 1 := by
      rcases (Nat.dvd_prime Nat.prime_five).1 hd5 with h | h
      · exact h
      · exfalso
        rw [h] at hd2
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd2
        omega
    rw [orderOf_eq_one_iff] at h1
    exact (QuotientGroup.eq_one_iff β).1 h1
  obtain ⟨t, rfl⟩ := hβinn
  have htord : orderOf t = 5 := by
    rw [← orderOf_conj_eq titsD_center t]
    exact hβ
  let ιf : ↥titsD →* ↥(ReeTag.F4.reeGamma (ZMod 2) 0) :=
    (((reeFixedEquivReeGamma (ZMod 2) 0).toMonoidHom.comp
      (commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0)).subtype).comp titsDerivedIso.symm.toMonoidHom)
  have hι : Function.Injective ιf := by
    intro u v h
    have h1 : ((titsDerivedIso.symm u : ↥(commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0))) :
        ↥(reeFixed ReeTag.F4 (ZMod 2) 0)) =
        ((titsDerivedIso.symm v : ↥(commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0))) :
          ↥(reeFixed ReeTag.F4 (ZMod 2) 0)) :=
      (reeFixedEquivReeGamma (ZMod 2) 0).injective h
    exact titsDerivedIso.symm.injective (Subtype.ext h1)
  have hιt : orderOf (ιf t) = 5 := by rw [orderOf_injective ιf hι t, htord]
  have hsolv : Group.IsSolvable
      ↥(Subgroup.centralizer ({ιf t} : Set ↥(ReeTag.F4.reeGamma (ZMod 2) 0))) :=
    solvable_centralizer_ree_zero (Nat.card_zmod 2) (ιf t) hιt
  have hY : Group.IsSolvable ↥(ιf.range ⊓ Subgroup.centralizer ({ιf t} : Set _)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective _)
  have h1 := card_radical_residual_of_embedding ιf hι t
  unfold OddRadConcl
  rw [eqLocus_conj_eq_centralizer t, h1, radical_perfectResidual_eq_bot_of_isSolvable hY]
  simp

theorem oddRadAt_smallModel_tits : OddRadAt (SmallModel .Tits) := by
  intro T _ _ _ hS β hβ
  obtain ⟨n, f, hadm, hM, -⟩ := hS
  obtain ⟨-, hRT⟩ := CFSG.RankThree.PartOne.Sec66T.lieModel_Tits_iff.mp hM
  obtain ⟨E⟩ := titsModelEquiv T 2 f hRT
  exact oddRadConcl_of_mulEquiv E (fun β' hβ' => oddRadConcl_titsD β' hβ') β hβ

end Tits

end CFSG.RankThree.PartOne.F106
