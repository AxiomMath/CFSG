module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality

private theorem ggLieAut_exists_entry_ne_zero {τ : Tag} {L : Type} [Field L]
    {f : Module.End L (RootModule τ L)} (hf : f ≠ 0) :
    ∃ (a b : Label τ), f (Finsupp.single b 1) a ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  refine Finsupp.basisSingleOne.ext fun i => ?_
  simp only [Finsupp.coe_basisSingleOne, LinearMap.zero_apply]
  exact Finsupp.ext fun a => by rw [h a i, Finsupp.zero_apply]

theorem rootSubgroup_injective_of_isRoot
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (h : rootSubgroup τ L γ = rootSubgroup τ L δ) : γ = δ := by
  set g : ModGL τ L := pinnedX τ L γ 1 with hgdef
  have hg1 : g ≠ 1 := by
    rw [hgdef]
    intro h1
    have h10 : (1 : L) = 0 := pinnedX_injective τ L γ (by rw [h1, pinnedX_zero])
    exact one_ne_zero h10
  have hgUγ : g ∈ rootSubgroup τ L γ := by
    rw [hgdef]; exact mem_rootSubgroup.2 ⟨1, rfl⟩
  have hgUδ : g ∈ rootSubgroup τ L δ := by rw [← h]; exact hgUγ
  have hgadj : g ∈ adjointGroup τ L := rootSubgroup_le_adjointGroup γ hgUγ
  let gA : adjointGroup τ L := ⟨g, hgadj⟩
  have hne : ((g : Module.End L (RootModule τ L)) - 1) ≠ 0 := by
    intro h0
    exact hg1 (Units.ext (sub_eq_zero.1 h0))
  obtain ⟨a, b, hab⟩ := ggLieAut_exists_entry_ne_zero hne
  have hmat : ((gA : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b 1) a -
      (Finsupp.single b 1 : RootModule τ L) a ≠ 0 := by
    have : (gA : ModGL τ L) = g := rfl
    rw [this]
    simpa using hab
  have hshiftγ : ∃ k : ℕ, 1 ≤ k ∧ labelWt τ a = labelWt τ b + k • γ := by
    refine (rootOperatorFamily τ).rootSubgroup_weight_shift ⟨γ, hγ⟩ gA ?_ a b hmat
    have : gA ∈ (rootSubgroup τ L γ).subgroupOf (adjointGroup τ L) := hgUγ
    rwa [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq L ⟨γ, hγ⟩] at this
  have hshiftδ : ∃ k : ℕ, 1 ≤ k ∧ labelWt τ a = labelWt τ b + k • δ := by
    refine (rootOperatorFamily τ).rootSubgroup_weight_shift ⟨δ, hδ⟩ gA ?_ a b hmat
    have : gA ∈ (rootSubgroup τ L δ).subgroupOf (adjointGroup τ L) := hgUδ
    rwa [(rootOperatorFamily τ).subgroupOf_rootSubgroup_eq L ⟨δ, hδ⟩] at this
  obtain ⟨k, hk1, hk⟩ := hshiftγ
  obtain ⟨k', hk'1, hk'⟩ := hshiftδ
  have hkk : k • γ = k' • δ := add_left_cancel (hk.symm.trans hk')
  obtain ⟨j, f, hf⟩ := hγ.exists_addMonoidHom_eq_single
  obtain ⟨l, f', hf'⟩ := hδ.exists_addMonoidHom_eq_single
  have hA : (k : ℤ) = (k' : ℤ) * (f δ) j := by
    have h1 : f (k • γ) = f (k' • δ) := congrArg f hkk
    rw [map_nsmul, map_nsmul, hf] at h1
    have h2 := congrFun h1 j
    simpa using h2
  have hB : (k' : ℤ) = (k : ℤ) * (f' γ) l := by
    have h1 : f' (k' • δ) = f' (k • γ) := congrArg f' hkk.symm
    rw [map_nsmul, map_nsmul, hf'] at h1
    have h2 := congrFun h1 l
    simpa using h2
  have hkpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk1
  have hk'pos : (0 : ℤ) < (k' : ℤ) := by exact_mod_cast hk'1
  have hApos : 0 < (f δ) j := by
    by_contra hle
    push Not at hle
    nlinarith [hA, hkpos, hk'pos]
  have hunit : (f δ) j * (f' γ) l = 1 := by
    have h1 : (k : ℤ) = (k : ℤ) * ((f' γ) l * (f δ) j) := by
      calc (k : ℤ) = (k' : ℤ) * (f δ) j := hA
        _ = ((k : ℤ) * (f' γ) l) * (f δ) j := by rw [hB]
        _ = (k : ℤ) * ((f' γ) l * (f δ) j) := by ring
    have h2 : (k : ℤ) * ((f' γ) l * (f δ) j) - (k : ℤ) = 0 := by linarith
    have h3 : (k : ℤ) * ((f' γ) l * (f δ) j - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (ne_of_gt hkpos)
    · rw [mul_comm]; exact sub_eq_zero.1 h4
  have hA1 : (f δ) j = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h | h
    · exact h
    · exfalso; nlinarith [h, hApos]
  have hkk' : k = k' := by
    have : (k : ℤ) = (k' : ℤ) := by rw [hA, hA1, mul_one]
    exact_mod_cast this
  subst hkk'
  exact nsmul_right_injective (M := Fin τ.rank → ℤ) (n := k) (by omega) hkk

theorem torusGroup_exists_pow_eq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {h : ModGL τ L} (hh : h ∈ torusGroup τ L)
    {n : ℕ} (hn : 0 < n) : ∃ k ∈ torusGroup τ L, k ^ n = h := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hroot : ∀ i : Fin τ.rank, ∃ b : Lˣ, b ^ n = a i := by
    intro i
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (a i : L) hn
    have hy0 : y ≠ 0 := by
      rintro rfl
      have h0 : (a i : L) = 0 := by rw [← hy, zero_pow hn.ne']
      exact (a i).ne_zero h0
    exact ⟨Units.mk0 y hy0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hy)⟩
  choose b hb using hroot
  refine ⟨rootDiagUnit τ b, rootDiagUnit_mem_torusGroup b, ?_⟩
  rw [rootDiagUnit_pow]
  congr 1
  funext i
  exact hb i

private theorem ggLieAut_mul_canonicalRep_pow_card_mem_torusGroup
    {τ : Tag} {L : Type} [Field L] (m : ModGL τ L) (w : WeylGroup τ)
    (hm : m ∈ torusGroup τ L) :
    (m * canonicalRep (coxeterSystem τ) L w) ^ Nat.card (WeylGroup τ) ∈ torusGroup τ L := by
  have key : ∀ j : ℕ, ∃ h ∈ torusGroup τ L,
      (m * canonicalRep (coxeterSystem τ) L w) ^ j =
        h * canonicalRep (coxeterSystem τ) L (w ^ j) := by
    intro j
    induction j with
    | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, canonicalRep_one, mul_one]⟩
    | succ j ih =>
      obtain ⟨h, hh, hh'⟩ := ih
      obtain ⟨k, hk, hk'⟩ := canonicalRep_mul_mem (R := L) (w ^ j) w
      have hconj : canonicalRep (coxeterSystem τ) L (w ^ j) * m *
          (canonicalRep (coxeterSystem τ) L (w ^ j))⁻¹ ∈ torusGroup τ L :=
        (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) (w ^ j)) m).1 hm
      refine ⟨h * (canonicalRep (coxeterSystem τ) L (w ^ j) * m *
          (canonicalRep (coxeterSystem τ) L (w ^ j))⁻¹) * k, mul_mem (mul_mem hh hconj) hk, ?_⟩
      rw [pow_succ, hh', pow_succ]
      rw [show h * (canonicalRep (coxeterSystem τ) L (w ^ j) * m *
            (canonicalRep (coxeterSystem τ) L (w ^ j))⁻¹) * k *
            canonicalRep (coxeterSystem τ) L (w ^ j * w) =
          h * (canonicalRep (coxeterSystem τ) L (w ^ j) * m *
            (canonicalRep (coxeterSystem τ) L (w ^ j))⁻¹) *
            (k * canonicalRep (coxeterSystem τ) L (w ^ j * w)) from by group]
      rw [← hk']
      group
  obtain ⟨h, hh, hpow⟩ := key (Nat.card (WeylGroup τ))
  rw [hpow]
  have hwN : w ^ Nat.card (WeylGroup τ) = 1 := by
    haveI : Fintype (WeylGroup τ) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  rw [hwN, canonicalRep_one, mul_one]
  exact hh

private theorem ggLieAut_normalizer_le_torus_normalizer
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (D : LangDatum τ L) (A : Subgroup (ModGL τ L)) (hA : A ≤ D.torus)
    (hroot : rootsTrivialOn A = ∅) :
    Subgroup.normalizer (A : Set (ModGL τ L)) ⊓ D.model ≤
      Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
  have hA_torus : A ≤ torusGroup τ L := hA.trans (by
    intro x hx; exact hx.1)
  let sec : A → Fin τ.rank → Lˣ := fun x =>
    Classical.choose (exists_rootDiagUnit_eq_of_mem_torusGroup (hA_torus x.2))
  have hsec : ∀ x : A, rootDiagUnit τ (sec x) = (x : ModGL τ L) := fun x =>
    (Classical.choose_spec (exists_rootDiagUnit_eq_of_mem_torusGroup (hA_torus x.2))).symm
  have hkernel : familyKernel sec = ∅ := by
    ext γ
    constructor
    · intro hγ
      obtain ⟨hγroot, hγfix⟩ := hγ
      have : γ ∈ rootsTrivialOn A := by
        refine ⟨hγroot, ?_⟩
        intro a ha
        let x : A := ⟨rootDiagUnit τ a, ha⟩
        have hxa : sec x = a := rootDiagUnit_injective (by rw [hsec x])
        rw [← hxa]
        exact hγfix x
      rw [hroot] at this
      exact this
    · intro hγ
      exact absurd hγ (by simp)
  have hgroup : familyGroup (K := L) sec = torusGroup τ L := by
    rw [familyGroup, hkernel]
    simp [rootSpan]
  have hstep : ∀ g ∈ Subgroup.normalizer (A : Set (ModGL τ L)) ⊓ adjointGroup τ L,
      ∀ h ∈ torusGroup τ L, g * h * g⁻¹ ∈ torusGroup τ L := by
    intro g hg h hh
    obtain ⟨hgA, hgG⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, hkpow⟩ := torusGroup_exists_pow_eq hh (Nat.card_pos (α := WeylGroup τ))
    have hgk : g * k * g⁻¹ ∈ familyCentralizer τ L sec := by
      rw [mem_familyCentralizer]
      refine ⟨?_, fun x => ?_⟩
      · exact mul_mem (mul_mem hgG (torusGroup_le_adjointGroup' hk)) (inv_mem hgG)
      · have hdA : rootDiagUnit τ (sec x) ∈ A := by rw [hsec x]; exact x.2
        have heA : g⁻¹ * rootDiagUnit τ (sec x) * g ∈ A :=
          (Subgroup.mem_normalizer_iff.1 (inv_mem hgA) (rootDiagUnit τ (sec x))).1 hdA
        have hconj : (g⁻¹ * rootDiagUnit τ (sec x) * g) * k *
            (g⁻¹ * rootDiagUnit τ (sec x) * g)⁻¹ = k := by
          let e : A := ⟨g⁻¹ * rootDiagUnit τ (sec x) * g, heA⟩
          have := conj_rootDiagUnit_of_mem_torusGroup (sec e) hk
          rwa [hsec e] at this
        calc rootDiagUnit τ (sec x) * (g * k * g⁻¹) * (rootDiagUnit τ (sec x))⁻¹
            = g * ((g⁻¹ * rootDiagUnit τ (sec x) * g) * k *
                (g⁻¹ * rootDiagUnit τ (sec x) * g)⁻¹) * g⁻¹ := by group
          _ = g * k * g⁻¹ := by rw [hconj]
    obtain ⟨w, -, m, hm, hmw⟩ := familyCentralizer_le_mul τ L sec hgk
    have hmH : m ∈ torusGroup τ L := by rw [← hgroup]; exact hm
    have heq : g * h * g⁻¹ = (m * canonicalRep (coxeterSystem τ) L w) ^
        Nat.card (WeylGroup τ) := by
      rw [← hkpow, (conj_pow).symm, hmw]
    rw [heq]
    exact ggLieAut_mul_canonicalRep_pow_card_mem_torusGroup m w hmH
  intro n hn
  obtain ⟨hnA, hnM⟩ := Subgroup.mem_inf.1 hn
  have hnG : n ∈ adjointGroup τ L := (D.mem_model.1 hnM).1
  refine Subgroup.mem_normalizer_iff.2 fun h =>
    ⟨hstep n (Subgroup.mem_inf.2 ⟨hnA, hnG⟩) h, fun hh => ?_⟩
  have hmem : n⁻¹ ∈ Subgroup.normalizer (A : Set (ModGL τ L)) ⊓ adjointGroup τ L :=
    Subgroup.mem_inf.2 ⟨inv_mem hnA, inv_mem hnG⟩
  have := hstep n⁻¹ hmem (n * h * n⁻¹) hh
  have heq : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h := by group
  rwa [heq] at this

private theorem ggLieAut_exists_pow_ne_one {L : Type} [Field L] [IsAlgClosed L]
    {n : ℕ} (hn : 0 < n) : ∃ s : Lˣ, s ^ n ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hy1 : ∀ y : Lˣ, y = 1 := by
    intro y
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (y : L) hn
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hs
      exact (Units.ne_zero y) hs.symm
    have h1 : (Units.mk0 s hs0) ^ n = 1 := h _
    have hval : s ^ n = (1 : L) := by
      have := congrArg Units.val h1
      simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] using this
    exact Units.ext (by rw [← hs]; exact hval)
  have hfin : Finite L := Finite.of_injective
    (fun x : L => if x = 0 then (true : Bool) else false) (by
      intro x y hxy
      dsimp only at hxy
      by_cases hx : x = 0
      · rw [if_pos hx] at hxy
        have hy : y = 0 := by
          by_contra hy
          rw [if_neg hy] at hxy
          exact Bool.noConfusion hxy
        rw [hx, hy]
      · rw [if_neg hx] at hxy
        have hy : y ≠ 0 := by
          intro hy
          rw [if_pos hy] at hxy
          exact Bool.noConfusion hxy
        have hx1 : x = 1 := congrArg Units.val (hy1 (Units.mk0 x hx))
        have hy1' : y = 1 := congrArg Units.val (hy1 (Units.mk0 y hy))
        rw [hx1, hy1'])
  exact (not_finite_iff_infinite.2 (inferInstance : Infinite L)) hfin

private theorem ggLieAut_exists_zpow_ne_one {L : Type} [Field L] [IsAlgClosed L]
    {m : ℤ} (hm : m ≠ 0) : ∃ s : Lˣ, s ^ m ≠ 1 := by
  have hmabs : 0 < m.natAbs := Int.natAbs_pos.2 hm
  obtain ⟨t, ht⟩ := ggLieAut_exists_pow_ne_one (L := L) hmabs
  rcases lt_trichotomy m 0 with hlt | heq | hgt
  · refine ⟨t, ?_⟩
    have hmn : m = -(m.natAbs : ℤ) := by
      have h1 : (m.natAbs : ℤ) = -m := by
        rw [← Int.natAbs_neg m]
        exact Int.natAbs_of_nonneg (le_of_lt (neg_pos.2 hlt))
      omega
    rw [hmn, zpow_neg, zpow_natCast]
    exact fun h => ht (inv_eq_one.1 h)
  · exact absurd heq hm
  · refine ⟨t, ?_⟩
    have hmn : m = (m.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hgt)).symm
    rw [hmn, zpow_natCast]
    exact ht

private theorem ggLieAut_centralizer_torus_eq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] :
    adjointGroup τ L ⊓ Subgroup.centralizer (torusGroup τ L : Set (ModGL τ L)) ≤
      torusGroup τ L := by
  intro z hz
  obtain ⟨hzG, hzC⟩ := Subgroup.mem_inf.1 hz
  have hkernel : familyKernel (fun x : Fin τ.rank → Lˣ => x) = ∅ := by
    ext γ
    constructor
    · rintro ⟨hγroot, hγfix⟩
      obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 0 := by
        by_contra h
        push Not at h
        exact hγroot.ne_zero (funext h)
      obtain ⟨s, hs⟩ := ggLieAut_exists_zpow_ne_one (L := L) hi
      exact hs (by
        have := hγfix (Pi.mulSingle i s)
        rwa [CFSG.RankThree.Chevalley.rootChar_mulSingle_eq_zpow] at this)
    · intro h; exact absurd h (by simp)
  have hgroup : familyGroup (K := L) (fun x : Fin τ.rank → Lˣ => x) = torusGroup τ L := by
    rw [familyGroup, hkernel]
    simp [rootSpan]
  have hzF : z ∈ familyCentralizer τ L (fun x : Fin τ.rank → Lˣ => x) := by
    rw [mem_familyCentralizer]
    refine ⟨hzG, fun x => ?_⟩
    have hx := Subgroup.mem_centralizer_iff.1 hzC (rootDiagUnit τ x)
      (rootDiagUnit_mem_torusGroup x)
    rw [show rootDiagUnit τ x * z * (rootDiagUnit τ x)⁻¹ = z from by
      rw [hx, mul_assoc, mul_inv_cancel, mul_one]]
  obtain ⟨w, hw, m, hm, hzm⟩ := familyCentralizer_le_mul τ L (fun x : Fin τ.rank → Lˣ => x) hzF
  have hw1 : w = 1 := by
    refine ext_single fun i => ?_
    set e : Fin τ.rank → ℤ := Pi.single i 1 with he
    by_contra hne
    have hne' : w • e ≠ e := by simpa using hne
    have hu : w • e - e ≠ 0 := sub_ne_zero.2 hne'
    obtain ⟨j, hj⟩ : ∃ j, (w • e - e) j ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    obtain ⟨s, hs⟩ := ggLieAut_exists_zpow_ne_one (L := L) hj
    have hfix := hw (Pi.mulSingle j s) e
    have h1 : rootChar (Pi.mulSingle j s) (w • e - e) = 1 := by
      rw [rootChar_sub, hfix, mul_inv_cancel]
    rw [CFSG.RankThree.Chevalley.rootChar_mulSingle_eq_zpow] at h1
    exact hs h1
  rw [hzm, hw1, canonicalRep_one, mul_one]
  rw [hgroup] at hm
  exact hm

private theorem ggLieAut_normalizer_factor
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {n : ModGL τ L}
    (hn : n ∈ adjointGroup τ L ⊓
      Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L))) :
    ∃ (u : WeylGroup τ) (t : ModGL τ L), t ∈ torusGroup τ L ∧
      n = canonicalRep (coxeterSystem τ) L u * t := by
  obtain ⟨hnG, hnN⟩ := Subgroup.mem_inf.1 hn
  have hcomm := (triangular_borel_structure.{0, 0} τ L).1
  have hCV : adjointGroup τ L ⊓ Subgroup.centralizer (torusGroup τ L : Set (ModGL τ L)) =
      torusGroup τ L :=
    le_antisymm ggLieAut_centralizer_torus_eq
      (le_inf torusGroup_le_adjointGroup' fun h hh =>
        Subgroup.mem_centralizer_iff.2 fun x hx => hcomm _ hx _ hh)
  obtain ⟨h, hh, u, hnu⟩ :=
    CFSG.RankThree.Chevalley.exists_eq_mul_canonicalRep_of_mem_normalizer
      (V := torusGroup τ L) (fun x hx => hx) hCV (Subgroup.mem_inf.2 ⟨hnG, hnN⟩)
  refine ⟨u, (canonicalRep (coxeterSystem τ) L u)⁻¹ * h * canonicalRep (coxeterSystem τ) L u,
    (Subgroup.mem_normalizer_iff.1 (inv_mem (canonicalRep_mem_normalizer (R := L) u)) h).1 hh, ?_⟩
  rw [hnu]
  group

private theorem ggLieAut_rho_add
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : FrobRootMap D ρ) (γ δ : Fin τ.rank → ℤ) : ρ (γ + δ) = ρ γ + ρ δ := by
  by_contra hne
  have hz : ρ (γ + δ) - ρ γ - ρ δ ≠ 0 := sub_ne_zero.2 (by
    intro h
    exact hne (by rw [sub_eq_iff_eq_add.1 h, add_comm]))
  have hzero : CFSG.LieType.Steinberg.Adjoint.iform (ρ (γ + δ) - ρ γ - ρ δ)
      (ρ (γ + δ) - ρ γ - ρ δ) = 0 := by
    simp only [CFSG.LieType.Steinberg.Adjoint.iform_sub_left,
      CFSG.LieType.Steinberg.Adjoint.iform_sub_right,
      CFSG.LieType.Steinberg.Adjoint.iform_add_left,
      CFSG.LieType.Steinberg.Adjoint.iform_add_right, hρ.iform_eq]
    rw [CFSG.LieType.Steinberg.Adjoint.iform_comm δ γ]
    ring
  have hpos := CFSG.LieType.Steinberg.Adjoint.iform_self_pos (x := ρ (γ + δ) - ρ γ - ρ δ) hz
  rw [hzero] at hpos
  exact absurd hpos (lt_irrefl 0)

private theorem ggLieAut_root_compat

    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    {n : ModGL τ L} (hnM : n ∈ D.model) (u : WeylGroup τ) {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (hn : n = canonicalRep (coxeterSystem τ) L u * t) :
    ∀ γ, u • ρ γ = ρ (u • γ) := by
  have hstepn : D.step n = n := by
    have := (D.mem_model.1 hnM).2
    simpa [CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.step, MulAut.conj_apply] using this
  have hU : ∀ i, (rootSubgroup τ L (Pi.single i 1)).map (MulAut.conj n).toMonoidHom =
      rootSubgroup τ L (u • Pi.single i 1) := by
    intro i
    rw [hn, map_conj_mul,
      CFSG.RankThree.Chevalley.map_conj_rootSubgroup_of_mem_torusGroup ht (isRoot_single τ i)]
    exact (canonical_weyl_root_transport τ L).2.1 u (Pi.single i 1) (isRoot_single τ i)
  have h2 : ∀ i, (rootSubgroup τ L (u • Pi.single i 1)).map D.step =
      rootSubgroup τ L (u • ρ (Pi.single i 1)) := by
    intro i
    rw [← hU i, Subgroup.map_map]
    have hcomp : D.step.comp (MulAut.conj n).toMonoidHom =
        (MulAut.conj n).toMonoidHom.comp D.step := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, hstepn]
    rw [hcomp, ← Subgroup.map_map]
    rw [hρ.map_rootSubgroup (Pi.single i 1) (isRoot_single τ i)]
    rw [hn, map_conj_mul,
      CFSG.RankThree.Chevalley.map_conj_rootSubgroup_of_mem_torusGroup ht
        ((hρ.isRoot_iff (Pi.single i 1)).2 (isRoot_single τ i))]
    exact (canonical_weyl_root_transport τ L).2.1 u (ρ (Pi.single i 1))
      ((hρ.isRoot_iff (Pi.single i 1)).2 (isRoot_single τ i))
  have hsimple : ∀ i, u • ρ (Pi.single i 1) = ρ (u • Pi.single i 1) := by
    intro i
    have h1 : (rootSubgroup τ L (u • Pi.single i 1)).map D.step =
        rootSubgroup τ L (ρ (u • Pi.single i 1)) :=
      hρ.map_rootSubgroup _ (IsRoot.smul (isRoot_single τ i) u)
    have heq : rootSubgroup τ L (ρ (u • Pi.single i 1)) =
        rootSubgroup τ L (u • ρ (Pi.single i 1)) := by rw [← h1, h2 i]
    exact (rootSubgroup_injective_of_isRoot
      ((hρ.isRoot_iff (u • Pi.single i 1)).2 (IsRoot.smul (isRoot_single τ i) u))
      (IsRoot.smul ((hρ.isRoot_iff (Pi.single i 1)).2 (isRoot_single τ i)) u) heq).symm
  have hρ_zero : ρ 0 = 0 := by
    have h : ρ 0 = ρ 0 + ρ 0 := by
      have := ggLieAut_rho_add D ρ hρ 0 0
      rwa [add_zero] at this
    have h2' : ρ 0 + ρ 0 = ρ 0 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2'
  have hbasis : ∀ γ : Fin τ.rank → ℤ,
      γ = ∑ i, γ i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    intro γ
    ext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [Pi.smul_apply, Pi.single_apply, hi]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h_ext : ∀ (f g : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)),
      (∀ i, f (Pi.single i 1) = g (Pi.single i 1)) → f = g := by
    intro f g h
    refine AddMonoidHom.ext fun γ => ?_
    rw [hbasis γ]
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, map_zsmul, h i]
  let f₁ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    { toFun := fun γ => ρ (u • γ)
      map_zero' := by simp [hρ_zero]
      map_add' := fun a b => by
        show ρ (u • (a + b)) = ρ (u • a) + ρ (u • b)
        rw [smul_add]
        exact ggLieAut_rho_add D ρ hρ (u • a) (u • b) }
  let f₂ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    { toFun := fun γ => u • ρ γ
      map_zero' := by simp [hρ_zero]
      map_add' := fun a b => by
        show u • ρ (a + b) = u • ρ a + u • ρ b
        rw [ggLieAut_rho_add D ρ hρ a b, smul_add] }
  have hf : f₁ = f₂ := h_ext f₁ f₂ fun i => (hsimple i).symm
  intro γ
  exact (DFunLike.congr_fun hf γ).symm

private theorem ggLieAut_step_mem_normalizer

    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (hq : ∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) :
    ∀ g ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)),
      D.step g ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
  obtain ⟨f, hf1, hfq⟩ := hq
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFr' : Fr = iterateFrobenius L 2 f := by
    ext c; rw [hFr c, hfq, iterateFrobenius_def]
  have hPmem : P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · exact Subgroup.one_mem _
    · cases ht
      exact diagramMap_mem_normalizer (k := L) t
  have hQmem : D.n * P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
    apply mul_mem
    · obtain ⟨u, hu⟩ := D.n_weyl
      rw [hu]
      exact canonicalRep_mem_normalizer (τ := τ) (R := L) u
    · exact hPmem
  have hstep : D.step = frobTwistGL τ L 2 f (D.n * P) := by
    ext g
    rw [frobTwistGL_apply]
    rw [show D.step g = D.n * D.Φ g * D.n⁻¹ from by
      simp [CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.step, MulAut.conj_apply]]
    rw [hΦ g, hFr']
    group
  have hH : (torusGroup τ L).map D.step = torusGroup τ L := by
    rw [hstep]
    exact map_frobTwistGL_torusGroup (p := 2) (e := f) hQmem
  intro g hg
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · rw [← hH] at hh
    obtain ⟨h', hh', rfl⟩ := hh
    rw [← hH]
    exact ⟨g * h' * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg h').1 hh',
      by simp only [map_mul, map_inv]⟩
  · obtain ⟨z, hz, hz'⟩ : ∃ z ∈ torusGroup τ L,
        D.step z = D.step g * h * (D.step g)⁻¹ := by
      rw [← hH] at hh
      exact Subgroup.mem_map.1 hh
    rw [← hH]
    refine ⟨g⁻¹ * z * g, (Subgroup.mem_normalizer_iff.1 (inv_mem hg) z).1 hz, ?_⟩
    simp only [map_mul, map_inv, hz']
    group

private theorem ggLieAut_step_mem_adjointGroup


    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (D : LangDatum τ L) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    {g : ModGL τ L} (hg : g ∈ adjointGroup τ L) : D.step g ∈ adjointGroup τ L := by
  have hmap : (rootSpan τ L {α | IsRoot τ α}).map D.step ≤ rootSpan τ L {α | IsRoot τ α} := by
    refine Subgroup.map_le_iff_le_comap.2 ?_
    refine iSup₂_le fun γ hγ => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    have h1 : D.step x ∈ (rootSubgroup τ L γ).map D.step := ⟨x, hx, rfl⟩
    rw [hρ.map_rootSubgroup γ hγ] at h1
    exact Subgroup.mem_iSup_of_mem (ρ γ)
      (Subgroup.mem_iSup_of_mem ((hρ.isRoot_iff γ).2 hγ) h1)
  rw [adjointGroup_eq_rootSpan]
  exact hmap ⟨g, by rwa [adjointGroup_eq_rootSpan] at hg, rfl⟩

private theorem ggLieAut_step_mem_inf

    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (hq : ∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) :
    ∀ g ∈ adjointGroup τ L ⊓ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)),
      D.step g ∈ adjointGroup τ L ⊓ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
  intro g hg
  obtain ⟨hgG, hgN⟩ := Subgroup.mem_inf.1 hg
  exact Subgroup.mem_inf.2
    ⟨ggLieAut_step_mem_adjointGroup D ρ hρ hgG, ggLieAut_step_mem_normalizer D hq g hgN⟩

private theorem ggLieAut_sigma_canonicalRep
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (hq : ∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) (u : WeylGroup τ)
    (hu : ∀ γ, u • ρ γ = ρ (u • γ)) :
    ∃ s ∈ torusGroup τ L, D.step (canonicalRep (coxeterSystem τ) L u) =
      canonicalRep (coxeterSystem τ) L u * s := by
  set nu := canonicalRep (coxeterSystem τ) L u with hnu
  have hmem : D.step nu ∈ adjointGroup τ L ⊓
      Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    ggLieAut_step_mem_inf D ρ hρ hq nu (Subgroup.mem_inf.2
      ⟨canonicalRep_mem_adjointGroup (coxeterSystem τ) L u,
        canonicalRep_mem_normalizer (R := L) u⟩)
  obtain ⟨u', s, hs, hsig⟩ := ggLieAut_normalizer_factor hmem
  have hroot : ∀ γ, IsRoot τ γ → u' • (ρ γ) = u • (ρ γ) := by
    intro γ hγ
    have hγ' : IsRoot τ (ρ γ) := (hρ.isRoot_iff γ).2 hγ
    have hA : (rootSubgroup τ L (ρ γ)).map (MulAut.conj (D.step nu)).toMonoidHom =
        rootSubgroup τ L (u' • ρ γ) := by
      rw [hsig, map_conj_mul,
        CFSG.RankThree.Chevalley.map_conj_rootSubgroup_of_mem_torusGroup hs hγ']
      exact (canonical_weyl_root_transport τ L).2.1 u' (ρ γ) hγ'
    have hB : (rootSubgroup τ L (ρ γ)).map (MulAut.conj (D.step nu)).toMonoidHom =
        rootSubgroup τ L (u • ρ γ) := by
      rw [← hρ.map_rootSubgroup γ hγ, Subgroup.map_map]
      have hcomp : (MulAut.conj (D.step nu)).toMonoidHom.comp D.step =
          D.step.comp (MulAut.conj nu).toMonoidHom := by
        refine MonoidHom.ext fun x => ?_
        change D.step nu * D.step x * (D.step nu)⁻¹ = D.step (nu * x * nu⁻¹)
        rw [map_mul, map_mul, map_inv]
      rw [hcomp, ← Subgroup.map_map, hnu, (canonical_weyl_root_transport τ L).2.1 u γ hγ,
        hρ.map_rootSubgroup (u • γ) (IsRoot.smul hγ u), hu γ]
    have heq : rootSubgroup τ L (u' • ρ γ) = rootSubgroup τ L (u • ρ γ) := by rw [← hA, hB]
    exact rootSubgroup_injective_of_isRoot (IsRoot.smul hγ' u') (IsRoot.smul hγ' u) heq
  have hu' : u' = u := by
    refine ext_single fun i => ?_
    have hγ : IsRoot τ (ρ.symm (Pi.single i 1)) := by
      refine (hρ.isRoot_iff (ρ.symm (Pi.single i 1))).1 ?_
      rw [Equiv.apply_symm_apply]
      exact isRoot_single τ i
    have h := hroot (ρ.symm (Pi.single i 1)) hγ
    rwa [Equiv.apply_symm_apply] at h
  rw [hu'] at hsig
  exact ⟨s, hs, hsig⟩

private theorem ggLieAut_lang_torus
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (hq : ∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) :
    ∀ c ∈ torusGroup τ L, ∃ ζ ∈ torusGroup τ L, ζ⁻¹ * D.step ζ = c := by
  obtain ⟨f, hf1, hfq⟩ := hq
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFr' : Fr = iterateFrobenius L 2 f := by
    ext c; rw [hFr c, hfq, iterateFrobenius_def]
  have hPmem : P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · exact Subgroup.one_mem _
    · cases ht
      exact diagramMap_mem_normalizer (k := L) t
  have hQmem : D.n * P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
    apply mul_mem
    · obtain ⟨u, hu⟩ := D.n_weyl
      rw [hu]; exact canonicalRep_mem_normalizer (τ := τ) (R := L) u
    · exact hPmem
  have hstep : D.step = frobTwistGL τ L 2 f (D.n * P) := by
    ext g
    rw [frobTwistGL_apply]
    rw [show D.step g = D.n * D.Φ g * D.n⁻¹ from by
      simp [CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.step, MulAut.conj_apply]]
    rw [hΦ g, hFr']
    group
  have hstepH : ∀ g ∈ torusGroup τ L, D.step g ∈ torusGroup τ L := by
    intro g hg
    rw [hstep]
    have := (map_frobTwistGL_torusGroup (p := 2) (e := f) hQmem).le
    exact this ⟨g, hg, rfl⟩
  have hkernel : familyKernel (fun x : Fin τ.rank → Lˣ => x) = ∅ := by
    ext γ
    constructor
    · rintro ⟨hγroot, hγfix⟩
      obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 0 := by
        by_contra h
        push Not at h
        exact hγroot.ne_zero (funext h)
      obtain ⟨s, hs⟩ := ggLieAut_exists_zpow_ne_one (L := L) hi
      exact hs (by
        have := hγfix (Pi.mulSingle i s)
        rwa [CFSG.RankThree.Chevalley.rootChar_mulSingle_eq_zpow] at this)
    · intro h; exact absurd h (by simp)
  have hgroup : familyGroup (K := L) (fun x : Fin τ.rank → Lˣ => x) = torusGroup τ L := by
    rw [familyGroup, hkernel]
    simp [rootSpan]
  have hZ : familyGroup (K := L) (fun x : Fin τ.rank → Lˣ => x) ⊓
      Subgroup.centralizer (torusGroup τ L : Set (ModGL τ L)) = torusGroup τ L := by
    rw [hgroup]
    refine le_antisymm inf_le_left ?_
    refine le_inf le_rfl fun h hh => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    exact (triangular_borel_structure.{0, 0} τ L).1 x hx h hh
  have hclosed : closedIdentityComponent (familyGroup (K := L)
      (fun x : Fin τ.rank → Lˣ => x) ⊓
      Subgroup.centralizer (torusGroup τ L : Set (ModGL τ L))) = torusGroup τ L := by
    rw [hZ, ← hgroup]
    exact closedIdentityComponent_familyGroup (fun x : Fin τ.rank → Lˣ => x)
  have hS : ∀ g ∈ familyGroup (K := L) (fun x : Fin τ.rank → Lˣ => x) ⊓
      Subgroup.centralizer (torusGroup τ L : Set (ModGL τ L)),
      frobTwistGL τ L 2 f (D.n * P) g ∈
        familyGroup (K := L) (fun x : Fin τ.rank → Lˣ => x) ⊓
          Subgroup.centralizer (torusGroup τ L : Set (ModGL τ L)) := by
    intro g hg
    obtain ⟨hgH, -⟩ := Subgroup.mem_inf.1 hg
    rw [hgroup] at hgH
    have hsg : D.step g ∈ torusGroup τ L := hstepH g hgH
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    · rw [hgroup]; rw [← hstep]; exact hstepH g hgH
    · rw [← hstep]
      exact (triangular_borel_structure.{0, 0} τ L).1 x hx (D.step g) hsg
  intro c hc
  have h := exists_inv_mul_frobTwistGL_familyGroup_inf_centralizer (p := 2)
    (fun x : Fin τ.rank → Lˣ => x) (torusGroup τ L : Set (ModGL τ L)) hf1 (D.n * P) hS
  rw [hclosed] at h
  obtain ⟨ζ, hζ, hζ'⟩ := h c hc
  rw [← hstep] at hζ'
  exact ⟨ζ, hζ, hζ'⟩

theorem ggLieAutomizer_holds
    :
    ∀ (τ : Tag), IsExcTag τ → ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
      (ρ : Equiv.Perm (Fin τ.rank → ℤ)), FrobRootMap D ρ → Finite D.model →
      (∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ A : Subgroup (ModGL τ L), A ≤ D.torus → (∀ x ∈ A, x ^ p = 1) →
        rootsTrivialOn A = ∅ →
        (Subgroup.normalizer (A : Set (ModGL τ L)) ⊓ D.model ≤
          Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L))) ∧
        (∀ n ∈ Subgroup.normalizer (A : Set (ModGL τ L)) ⊓ D.model,
          ∃ (u : WeylGroup τ) (t : ModGL τ L), t ∈ torusGroup τ L ∧
            n = canonicalRep (coxeterSystem τ) L u * t ∧ ∀ γ, u • ρ γ = ρ (u • γ)) ∧
        (∀ u : WeylGroup τ, (∀ γ, u • ρ γ = ρ (u • γ)) →
          (A.map (MulAut.conj (canonicalRep (coxeterSystem τ) L u)).toMonoidHom = A) →
          ∃ n ∈ Subgroup.normalizer (A : Set (ModGL τ L)) ⊓ D.model, ∃ t ∈ torusGroup τ L,
            n = canonicalRep (coxeterSystem τ) L u * t) := by
  intro τ hτ L _ _ _ D ρ hρ hfin hq p hp hp2 A hA hAexp hroot
  refine ⟨ggLieAut_normalizer_le_torus_normalizer D A hA hroot, ?_, ?_⟩
  · intro n hn
    obtain ⟨hnA, hnM⟩ := Subgroup.mem_inf.1 hn
    have hnN : n ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
      ggLieAut_normalizer_le_torus_normalizer D A hA hroot hn
    obtain ⟨u, t, ht, hnt⟩ := ggLieAut_normalizer_factor
      (Subgroup.mem_inf.2 ⟨(D.mem_model.1 hnM).1, hnN⟩)
    exact ⟨u, t, ht, hnt, ggLieAut_root_compat D ρ hρ hnM u ht hnt⟩
  ·
    intro u hu hA_map
    obtain ⟨s, hs, hsig⟩ := ggLieAut_sigma_canonicalRep D ρ hρ hq u hu
    obtain ⟨ζ, hζ, hζ'⟩ := ggLieAut_lang_torus D hq s hs
    have hA_torus : A ≤ torusGroup τ L := hA.trans (fun x hx => hx.1)
    have hcomm := (triangular_borel_structure.{0, 0} τ L).1
    have hfix : ∀ a ∈ A, MulAut.conj ζ⁻¹ a = a := by
      intro a ha
      have haT : a ∈ torusGroup τ L := hA_torus ha
      have hcomm' : a * ζ = ζ * a := hcomm a haT ζ hζ
      rw [MulAut.conj_apply, inv_inv, mul_assoc, hcomm', ← mul_assoc, inv_mul_cancel, one_mul]
    have hζA : A.map (MulAut.conj ζ⁻¹).toMonoidHom = A := by
      apply le_antisymm
      · rintro _ ⟨a, ha, rfl⟩
        change MulAut.conj ζ⁻¹ a ∈ A
        rw [hfix a ha]
        exact ha
      · intro a ha
        exact ⟨a, ha, by simpa only [MulEquiv.coe_toMonoidHom] using hfix a ha⟩
    have hζ'' : D.step ζ = ζ * s := by
      rw [← hζ']
      group
    have hstep_eq : ∀ y, D.n * D.Φ y * D.n⁻¹ = D.step y := by
      intro y
      simp [CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.step, MulAut.conj_apply]
    refine ⟨canonicalRep (coxeterSystem τ) L u * ζ⁻¹, ?_, ζ⁻¹, inv_mem hζ, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    ·
      rw [Subgroup.mem_normalizer_iff_conj_image_eq]
      have hmap : A.map
          (MulAut.conj (canonicalRep (coxeterSystem τ) L u * ζ⁻¹)).toMonoidHom = A := by
        rw [map_conj_mul, hζA, hA_map]
      have h := congrArg SetLike.coe hmap
      rwa [Subgroup.coe_map] at h
    ·
      rw [D.mem_model]
      refine ⟨?_, ?_⟩
      · exact mul_mem (canonicalRep_mem_adjointGroup (coxeterSystem τ) L u)
          (torusGroup_le_adjointGroup' (inv_mem hζ))
      · rw [hstep_eq, map_mul, hsig, map_inv, hζ'']
        group

end CFSG.StandardType.LieCore
