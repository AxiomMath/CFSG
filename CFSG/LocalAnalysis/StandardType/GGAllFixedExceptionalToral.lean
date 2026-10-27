module

public import CFSG.LocalAnalysis.StandardType.GGFamCentralizerSolvable
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvLangSetup
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralInd
public import CFSG.RankThree.PartOne.KE6.EqpA24
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8b
public import CFSG.RankThree.PartTwo.KFacts.AutPSUDet

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.StandardType.ExcFramesHalf
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.AlgebraicGroups
open scoped commutatorElement

section Certificates


theorem inndiag_full_toral_centralizer_solvable
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hpqK : p ∣ Nat.card K ^ 2 - 1)
    (A : Subgroup (ModGL τ K))
    (hAp : ∀ x ∈ A, x ^ p = 1)
    (hT : IsToralSubgroup τ (AlgebraicClosure K)
      (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))))
    (hNPC : CFSG.HasNormalPComplement p
      ↥(_root_.commutator ↥(adjointGroup τ K ⊓
        Subgroup.centralizer (A : Set (ModGL τ K))))) :
    Group.IsSolvable ↥(adjointGroup τ K ⊓
      Subgroup.centralizer (A : Set (ModGL τ K))) := by
  classical
  let L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hncard⟩ := FiniteField.card K 2
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hncard
  let φ := baseChangeGL (τ := τ) (algebraMap K L)
  let Fr : L →+* L := iterateFrobenius L 2 n
  let F := entrywiseFrobGL τ L 2 n
  have hFr : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    rw [hK]
    exact iterateFrobenius_def _ _ _
  have hFix : ∀ y : ModGL τ K, F (φ y) = φ y := by
    intro y
    have hcomp : Fr.comp (algebraMap K L) = algebraMap K L := by
      refine RingHom.ext fun c => ?_
      change Fr (algebraMap K L c) = algebraMap K L c
      rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
    change entrywiseFrobGL τ L 2 n (baseChangeGL (algebraMap K L) y) =
      baseChangeGL (algebraMap K L) y
    rw [entrywiseFrobGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, hcomp]
  obtain ⟨g, hgG, hg⟩ := hT
  have hTor : ∀ x : A, g⁻¹ * φ x * g ∈ torusGroup τ L := fun x =>
    hg _ (Subgroup.mem_map_of_mem _ x.2)
  choose afam hafam using fun x : A =>
    exists_rootDiagUnit_eq_of_mem_torusGroup (hTor x)
  have hexp : ∀ (x : A) i, afam x i ^ p = 1 := by
    intro x i
    have hpow : (g⁻¹ * φ x * g) ^ p = g⁻¹ * (φ x) ^ p * g := by
      have h := conj_pow (a := g⁻¹) (b := φ x) (i := p)
      simpa only [inv_inv] using h
    have h1 : rootDiagUnit τ (afam x ^ p) = rootDiagUnit τ 1 := by
      rw [← rootDiagUnit_pow, ← hafam x, rootDiagUnit_one, hpow,
        ← map_pow, hAp x x.2, map_one]
      group
    exact congrFun (rootDiagUnit_injective h1) i
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  have hcop : Nat.Coprime p (2 ^ (n : ℕ)) := by
    apply (Nat.Prime.coprime_iff_not_dvd hp).2
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow hd))
  have hnF : ∀ x : A, (g⁻¹ * F g) * F (rootDiagUnit τ (afam x)) *
      (g⁻¹ * F g)⁻¹ = rootDiagUnit τ (afam x) := by
    intro x
    rw [← hafam x, map_mul, map_mul, map_inv, hFix]
    group
  obtain ⟨w, z, hz, hlang⟩ := exists_lang_datum_of_plane 2 n hn hcop afam hexp hgG hnF
  have hzC := familyGroup_le_familyCentralizer (K := L) afam hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  let g0 := g * z
  have hg0C : g0 ∈ adjointGroup τ L := mul_mem hgG hzG
  have hg0F : F g0 = g0 * canonicalRep (coxeterSystem τ) L w :=
    inv_mul_eq_iff_eq_mul.1 hlang
  have hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) L w := hg0F
  obtain ⟨S, -, ι, hSD, -, -, hιinj, hΓ, hιform, -⟩ :=
    exists_langSetup_conj_of_prime_bound hτ K
      (p := 5) Nat.prime_five (by decide) (Or.inl le_rfl)
      hFr hg0C hg0 1 (by simp) (by simp [LangDatum.ofFrobenius, LangDatum.torus])
  let f : ModGL τ K →* ModGL τ L := (MulAut.conj g0⁻¹).toMonoidHom.comp φ
  have hf : Function.Injective f :=
    (MulAut.conj g0⁻¹).injective.comp (baseChangeGL_injective (algebraMap K L))
  have hfam : ∀ x : A, f x = rootDiagUnit τ (afam x) := by
    intro x
    have hzd : z⁻¹ * rootDiagUnit τ (afam x) * z = rootDiagUnit τ (afam x) := by
      have h := hzcomm x
      rw [mul_inv_eq_iff_eq_mul] at h
      calc z⁻¹ * rootDiagUnit τ (afam x) * z =
          z⁻¹ * (rootDiagUnit τ (afam x) * z) := by group
        _ = z⁻¹ * (z * rootDiagUnit τ (afam x)) := by rw [h]
        _ = rootDiagUnit τ (afam x) := by group
    change (g * z)⁻¹ * φ x * (g * z) = rootDiagUnit τ (afam x)
    calc (g * z)⁻¹ * φ x * (g * z) = z⁻¹ * (g⁻¹ * φ x * g) * z := by group
      _ = rootDiagUnit τ (afam x) := by rw [hafam x, hzd]
  have hTfam : ∀ x, rootDiagUnit τ (afam x) ∈ S.D.torus := by
    intro x
    rw [hSD]
    change rootDiagUnit τ (afam x) ∈
      twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr))
    apply mem_twistedTorusOf.2
    refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    change canonicalRep (coxeterSystem τ) L w * F (rootDiagUnit τ (afam x)) *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootDiagUnit τ (afam x)
    rw [← hfam x]
    change canonicalRep (coxeterSystem τ) L w * F (g0⁻¹ * φ x * g0) *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ = g0⁻¹ * φ x * g0
    rw [map_mul, map_mul, map_inv, hFix, hg0F]
    group
  have hGT : (adjointGroup τ K).map f = S.Γ := by
    have hcomp : f.comp (adjointGroup τ K).subtype = ι := by
      apply MonoidHom.ext
      intro y
      exact (hιform y).symm
    calc
      (adjointGroup τ K).map f = (f.comp (adjointGroup τ K).subtype).range := by
        exact ((MonoidHom.range_comp f (adjointGroup τ K).subtype).trans
          (congrArg (Subgroup.map f) (Subgroup.range_subtype _))).symm
      _ = S.Γ := by rw [hcomp, hΓ]
  let C := adjointGroup τ K ⊓ Subgroup.centralizer (A : Set (ModGL τ K))
  let H := S.Γ ⊓ Subgroup.centralizer (Set.range fun x : A => rootDiagUnit τ (afam x))
  have hCH : C.map f = H := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hGT ▸ Subgroup.mem_map_of_mem f hc.1, ?_⟩
      change f c ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      change rootDiagUnit τ (afam x) * f c = f c * rootDiagUnit τ (afam x)
      rw [← hfam x, ← map_mul, ← map_mul]
      exact congrArg f (Subgroup.mem_centralizer_iff.1 hc.2 x x.2)
    · intro hy
      obtain ⟨c, hc, rfl⟩ := hGT.symm ▸ hy.1
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      change c ∈ Subgroup.centralizer (A : Set (ModGL τ K))
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      apply hf
      rw [map_mul, map_mul]
      have h := Subgroup.mem_centralizer_iff.1 hy.2 _ ⟨⟨x, hx⟩, rfl⟩
      simpa only [← hfam] using h
  let e : ↥C ≃* ↥H := (C.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hCH)
  have hNPC_H : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥H) :=
    CFSG.hasNormalPComplement_of_equiv p e.commutatorCongr hNPC
  let eD : ↥(_root_.commutator ↥H) ≃* ↥⁅H, H⁆ :=
    ((_root_.commutator ↥H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator H))
  have hNPC_amb : CFSG.HasNormalPComplement p ↥⁅H, H⁆ :=
    CFSG.hasNormalPComplement_of_equiv p eD hNPC_H
  have hpqS : p ∣ S.D.q ^ 2 - 1 := by
    rw [hSD]
    exact hpqK
  have hsolv : Group.IsSolvable ↥H :=
    TableCRes.isSolvable_familyToral (τ := τ) (L := L) (p₀ := 5) (p := p) S
      hτ hp hpodd afam hTfam hexp hpqS hNPC_amb
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem adjoint_full_toral_centralizer_solvable
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hpqK : p ∣ Nat.card K ^ 2 - 1)
    (A : Subgroup (adjointGroup τ K))
    (hAp : ∀ x ∈ A, x ^ p = 1)
    (hT : IsToralSubgroup τ (AlgebraicClosure K)
      (A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup τ K).subtype)))
    (hNPC : CFSG.HasNormalPComplement p
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup τ K))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup τ K))) := by
  classical
  let L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fintype K := Fintype.ofFinite K
  have : Finite (adjointGroup τ K) := by
    have : Finite (ModGL τ K) := finite_modGL
    exact Subtype.finite
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  have htorA : ∃ g ∈ adjointGroup τ L, ∀ x ∈ A,
      g⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g ∈
        torusGroup τ L := by
    obtain ⟨g, hgG, hg⟩ := hT
    exact ⟨g, hgG, fun x hx => hg _ (Subgroup.mem_map_of_mem _ hx)⟩
  obtain ⟨g, hg, hgA⟩ := htorA
  obtain ⟨D⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8bAux.langPlaneData_of_toral
      hp (by
        intro hd
        have : Fintype K := Fintype.ofFinite K
        obtain ⟨f, -, hf⟩ := FiniteField.card K 2
        rw [Nat.card_eq_fintype_card, hf] at hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow hd))) hAp hg hgA
  obtain ⟨S, -, ι, hSD, -, -, hιinj, hΓ, hιform, -⟩ :=
    CFSG.StandardType.exists_langSetup_conj_of_prime_bound hτ K
      (p := 5) Nat.prime_five (by decide) (Or.inl le_rfl)
      D.hFr D.hg0C D.hg0 1 (by simp) (by simp [LangDatum.ofFrobenius, LangDatum.torus])
  have hmemT : ∀ x : A,
      ι (D.c * (x : adjointGroup τ K) * D.c⁻¹) ∈ S.D.torus := by
    intro x
    have hxT := D.hc x x.2
    obtain ⟨t, ht, hconj⟩ := hxT
    have hEq : D.g0⁻¹ * baseChangeGL (algebraMap K L)
        ((D.c * (x : adjointGroup τ K) * D.c⁻¹ : adjointGroup τ K) :
          ModGL τ K) * D.g0 = t := by
      rw [← hconj]
      change D.g0⁻¹ * (D.g0 * t * D.g0⁻¹) * D.g0 = t
      group
    have hιeq : ι (D.c * (x : adjointGroup τ K) * D.c⁻¹) =
        D.g0⁻¹ * baseChangeGL (algebraMap K L)
          ((D.c * (x : adjointGroup τ K) * D.c⁻¹ : adjointGroup τ K) :
            ModGL τ K) * D.g0 := hιform _
    rw [hιeq, hEq, hSD]
    simpa [LangDatum.ofFrobenius, LangDatum.torus] using ht
  have hex : ∀ x : A, ∃ a : Fin τ.rank → Lˣ,
      rootDiagUnit τ a = ι (D.c * (x : adjointGroup τ K) * D.c⁻¹) := by
    intro x
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
      (mem_twistedTorusOf.1 (by
        have h := hmemT x
        simpa [hSD, LangDatum.ofFrobenius, LangDatum.torus] using h)).1
    exact ⟨a, by simpa only [map_mul, map_inv] using ha.symm⟩
  choose afam' hafam' using hex
  have hTfam : ∀ x, rootDiagUnit τ (afam' x) ∈ S.D.torus := by
    intro x
    rw [hafam' x]
    exact hmemT x
  have hap' : ∀ x j, afam' x j ^ p = 1 := by
    intro x j
    have hx5 : (D.c * (x : adjointGroup τ K) * D.c⁻¹) ^ p = 1 := by
      calc (D.c * (x : adjointGroup τ K) * D.c⁻¹) ^ p
          = D.c * (x : adjointGroup τ K) ^ p * D.c⁻¹ := by rw [conj_pow]
        _ = D.c * 1 * D.c⁻¹ := by rw [hAp x x.2]
        _ = 1 := by group
    have hroot5 : rootDiagUnit τ (afam' x) ^ p = 1 := by
      rw [hafam' x, ← map_pow, hx5, map_one]
    have htuple : (afam' x) ^ p = 1 := by
      apply rootDiagUnit_injective
      rw [← rootDiagUnit_pow, rootDiagUnit_one]
      exact hroot5
    exact congrFun htuple j
  let H : Subgroup (ModGL τ L) :=
    S.Γ ⊓ Subgroup.centralizer (Set.range fun x : A => rootDiagUnit τ (afam' x))
  let C : Subgroup (adjointGroup τ K) :=
    Subgroup.centralizer (A : Set (adjointGroup τ K))
  let φ : ↥C →* ↥H :=
  { toFun := fun y =>
      ⟨ι (D.c * y.1 * D.c⁻¹), by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [← hΓ]
          exact ⟨_, rfl⟩
        · rw [Subgroup.mem_centralizer_iff]
          rintro _ ⟨x, rfl⟩
          change rootDiagUnit τ (afam' x) * ι (D.c * y.1 * D.c⁻¹) =
            ι (D.c * y.1 * D.c⁻¹) * rootDiagUnit τ (afam' x)
          rw [hafam' x]
          have hy : Commute y.1 x :=
            ((Subgroup.mem_centralizer_iff.1 y.2) x x.2).symm
          have hconj : Commute (D.c * y.1 * D.c⁻¹) (D.c * x * D.c⁻¹) := by
            simpa [mul_assoc] using hy.conj D.c
          exact (hconj.map ι).symm⟩
    map_one' := by ext; simp
    map_mul' := by intro y z; ext; simp [mul_assoc] }
  have hφinj : Function.Injective φ := by
    intro y z h
    apply Subtype.ext
    have h' : ι (D.c * y.1 * D.c⁻¹) = ι (D.c * z.1 * D.c⁻¹) :=
      congrArg Subtype.val h
    have h'' := hιinj h'
    have := congrArg (fun w : adjointGroup τ K => D.c⁻¹ * w * D.c) h''
    simpa [mul_assoc] using this
  have hφsurj : Function.Surjective φ := by
    intro h
    have hhΓ : (h.1 : ModGL τ L) ∈ ι.range := by
      have := h.2.1
      rwa [← hΓ] at this
    obtain ⟨z, hz⟩ := hhΓ
    let y : adjointGroup τ K := D.c⁻¹ * z * D.c
    have hyC : y ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hcent0 : rootDiagUnit τ (afam' ⟨x, hx⟩) * h.1 =
          h.1 * rootDiagUnit τ (afam' ⟨x, hx⟩) :=
        Subgroup.mem_centralizer_iff.1 h.2.2 _ ⟨⟨x, hx⟩, rfl⟩
      have hcent : Commute h.1 (rootDiagUnit τ (afam' ⟨x, hx⟩)) := hcent0.symm
      rw [← hz, hafam' ⟨x, hx⟩] at hcent
      have hzcomm : Commute z (D.c * x * D.c⁻¹) := by
        apply hιinj
        simpa [map_mul] using hcent.eq
      have hycomm : Commute y x := by
        have := hzcomm.conj D.c⁻¹
        simpa [y, mul_assoc] using this
      exact hycomm.symm
    refine ⟨⟨y, hyC⟩, ?_⟩
    refine Subtype.ext ?_
    have hyz : D.c * y * D.c⁻¹ = z := by dsimp [y]; group
    change ι (D.c * y * D.c⁻¹) = h.1
    rw [hyz]
    exact hz
  let e : ↥C ≃* ↥H := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hmap : (_root_.commutator ↥C).map e.toMonoidHom = _root_.commutator ↥H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective,
      ← _root_.commutator_def]
  let eD : ↥(_root_.commutator ↥C) ≃* ↥(_root_.commutator ↥H) :=
    ((_root_.commutator ↥C).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hNPC_H : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥H) :=
    CFSG.hasNormalPComplement_of_equiv p eD hNPC
  let eAmb : ↥(_root_.commutator ↥H) ≃* ↥⁅H, H⁆ :=
    ((_root_.commutator ↥H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator H))
  have hNPC_H_amb : CFSG.HasNormalPComplement p ↥⁅H, H⁆ :=
    CFSG.hasNormalPComplement_of_equiv p eAmb hNPC_H
  have hpq : p ∣ S.D.q ^ 2 - 1 := by
    rw [hSD]
    change p ∣ Nat.card K ^ 2 - 1
    exact hpqK
  have hsolvH : Group.IsSolvable ↥H :=
    TableCRes.isSolvable_familyToral (τ := τ) (L := L) (p₀ := 5) (p := p) S
      hτ hp hpodd
      (ι := A) afam' hTfam hap' hpq (by simpa [H] using hNPC_H_amb)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective


theorem adjoint_full_centralizer_solvable_of_nonTorsion
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp3 : p ≠ 3) (hp5 : τ = .E8 → p ≠ 5)
    (hpqK : p ∣ Nat.card K ^ 2 - 1)
    (A : Subgroup (adjointGroup τ K)) (hA : IsElemAbelian p A)
    (hNPC : CFSG.HasNormalPComplement p
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup τ K))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup τ K))) := by
  classical
  let L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup τ K) := by
    have : Finite (ModGL τ K) := finite_modGL
    exact Subtype.finite
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  let f : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype
  have hf : Function.Injective f :=
    (baseChangeGL_injective (algebraMap K L)).comp (Subgroup.subtype_injective _)
  let A' := A.map f
  have : Finite ↥A' := Finite.of_equiv A (A.equivMapOfInjective f hf).toEquiv
  have hA' : A' ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K L) x.2
  have hT : IsToralSubgroup τ L A' :=
    LieCore.isToralSubgroup_of_nonTorsion hp hp2 (fun _ => hp3) hp5 hp2.symm
      (CFSG.RankThree.PartOne.KE6.eqp_halg K L) hA' (by infer_instance) (hA.map f)
  exact adjoint_full_toral_centralizer_solvable hτ hp hpodd hpqK A hA.2 hT hNPC


end Certificates

end CFSG.StandardType
