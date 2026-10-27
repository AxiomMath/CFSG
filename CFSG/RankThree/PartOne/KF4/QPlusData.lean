module

public import CFSG.RankThree.PartOne.KF4.QPlusFrame
public import CFSG.RankThree.PartOne.KF4.QPlusCore
public import CFSG.RankThree.PartOne.KE.PlaneOdd
public import CFSG.RankThree.PartOne.KE.NativeCyclicF4
public import CFSG.RankThree.PartOne.KF4.QPlusPerX

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.LocalRank
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise


section Standardize

variable (K : Type) [Field K] [Finite K] {f : ℕ} {p : ℕ}
  (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

theorem qp_entrywise_canonicalRep (f : ℕ) (u : WeylGroup Tag.F4) :
    Units.map (entrywiseHom (iterateFrobenius L 2 f)) (canonicalRep (coxeterSystem Tag.F4) L u) =
      canonicalRep (coxeterSystem Tag.F4) L u := by
  rw [units_map_entrywiseHom_eq_baseChangeGL_self, CFSG.LieType.Chevalley.baseChangeGL_canonicalRep]

theorem qp_standardize (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (g0 : ModGL Tag.F4 L) (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L 2 f)) g0 = g0 * qpRep L)
    {x : adjointGroup Tag.F4 K} (hx : orderOf x = p) (c : adjointGroup Tag.F4 K)
    (b : Fin Tag.F4.rank → Lˣ)
    (hb : rootDiagUnit Tag.F4 b = g0⁻¹ * adjEmb Tag.F4 K L (c * x * c⁻¹) * g0)
    (hbT : b ∈ fixedCharTuples (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ)
      (iterateFrobenius L 2 f)) :
    ∃ (c' : adjointGroup Tag.F4 K) (b' : Fin Tag.F4.rank → Lˣ) (u : WeylGroup Tag.F4)
      (J : Finset (Fin Tag.F4.rank)), J ≠ Finset.univ ∧
      g0⁻¹ * adjEmb Tag.F4 K L (c' * x * c'⁻¹) * g0 ∈
        twistedTorusOf (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))) ∧
      rootDiagUnit Tag.F4 b' = g0⁻¹ * adjEmb Tag.F4 K L (c' * x * c'⁻¹) * g0 ∧
      rootCharKernel b' = parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank)) ∧
      rootCharKernel b' = (fun α => u • α) '' rootCharKernel b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  set Φ : ModGL Tag.F4 L →* ModGL Tag.F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def 2 f c
  set ι : adjointGroup Tag.F4 K →* ModGL Tag.F4 L := adjEmb Tag.F4 K L with hιdef
  set h : ModGL Tag.F4 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
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
  have hbp : orderOf (rootDiagUnit Tag.F4 b) = p := by rw [hb]; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  obtain ⟨z, hz0, -, hzk⟩ := exists_eigencolumn_of_mem_fixedCharTuples
    (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) Fr hFr hp hbT hap hb1
  obtain ⟨u, J₀, hu, hJ₀⟩ := exists_smul_rootKernel_eq_parabolicRoots
    (not_dvd_card_weylGroup_F4 hp hp3) z
  have hJne : J₀ ≠ Set.univ := hJ₀ hz0
  have hker : rootCharKernel b = rootKernel z := by rw [hzk]; rfl
  set nu : ModGL Tag.F4 L := canonicalRep (coxeterSystem Tag.F4) L u with hnu
  have hnuC : nu ∈ adjointGroup Tag.F4 L := canonicalRep_mem_adjointGroup _ L u
  have hyC : g0 * nu * g0⁻¹ ∈ adjointGroup Tag.F4 L :=
    mul_mem (mul_mem hg0C hnuC) (inv_mem hg0C)
  have hyF : Φ (g0 * nu * g0⁻¹) = g0 * nu * g0⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg0, qp_entrywise_canonicalRep L f u]
    have := qpRep_conj_canonicalRep (M := L) u
    calc g0 * qpRep L * nu * (g0 * qpRep L)⁻¹ = g0 * (qpRep L * nu * (qpRep L)⁻¹) * g0⁻¹ := by
          group
      _ = g0 * nu * g0⁻¹ := by rw [this]
  have hmem := F4_frobenius_fixed_eq_map (k := K) Fr hFr
  have hy : g0 * nu * g0⁻¹ ∈ (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K L)) := by
    rw [← hmem]
    exact Subgroup.mem_inf.2 ⟨hyC, hyF⟩
  obtain ⟨cu', hcu', hcu⟩ := hy
  set cu : adjointGroup Tag.F4 K := ⟨cu', hcu'⟩ with hcudef
  have hcuι : ι cu = g0 * nu * g0⁻¹ := hcu
  have hJJ : ((J₀.toFinite.toFinset : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank)) = J₀ :=
    J₀.toFinite.coe_toFinset
  have eq1 : g0⁻¹ * ι ((cu * c) * x * (cu * c)⁻¹) * g0 = nu * h * nu⁻¹ := by
    have e : (cu * c) * x * (cu * c)⁻¹ = cu * (c * x * c⁻¹) * cu⁻¹ := by group
    rw [e, map_mul, map_mul, map_inv, hcuι, hhdef]
    group
  have eq2 : nu * h * nu⁻¹ = rootDiagUnit Tag.F4 (weylTuple u b) := by
    rw [← hb]
    exact canonicalRep_conj_rootDiagUnit u b
  have hfixgen : ∀ y : adjointGroup Tag.F4 K,
      qpRep L * Φ (g0⁻¹ * ι y * g0) * (qpRep L)⁻¹ = g0⁻¹ * ι y * g0 := fun y => by
    rw [map_mul, map_mul, map_inv, hg0, hιdef, adjEmb_frobenius Fr hFr y]
    group
  have hkerEq : rootCharKernel (weylTuple u b) = (fun α => u • α) '' rootCharKernel b := by
    ext α
    constructor
    · rintro ⟨hα, hχ⟩
      refine ⟨u⁻¹ • α, ⟨IsRoot.smul hα u⁻¹, ?_⟩, smul_inv_smul u α⟩
      rw [← rootChar_weylTuple]
      exact hχ
    · rintro ⟨β, ⟨hβ, hχ⟩, rfl⟩
      refine ⟨IsRoot.smul hβ u, ?_⟩
      rw [rootChar_weylTuple, inv_smul_smul]
      exact hχ
  refine ⟨cu * c, weylTuple u b, u, J₀.toFinite.toFinset, ?_, ?_, ?_, ?_, hkerEq⟩
  · intro hJ
    apply hJne
    rw [← hJJ, hJ, Finset.coe_univ]
  · rw [eq1, eq2]
    exact mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup _, by
      rw [← eq2, ← eq1]
      exact hfixgen _⟩
  · rw [eq1, eq2]
  · rw [hJJ, hkerEq, hker, hu]

end Standardize

theorem qp_exists_ne_one_ker {A : Type*} [Group A] [Finite A] {L : Type*} [Field L]
    {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ 2) (χ : A →* Lˣ) (hχ : ∀ a, χ a ^ p = 1) :
    ∃ a : A, a ≠ 1 ∧ χ a = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective χ := (injective_iff_map_eq_one χ).2 fun a ha => by
    by_contra hne
    exact hcon a hne ha
  have hle : Nat.card A ≤ Nat.card (rootsOfUnity p L) :=
    Nat.card_le_card_of_injective (fun a => (⟨χ a, (mem_rootsOfUnity p (χ a)).2 (hχ a)⟩ :
      rootsOfUnity p L)) fun a b hab => hinj (congrArg Subtype.val hab)
  have h2 := card_rootsOfUnity L p
  have hp2 := hp.two_le
  rw [hA] at hle
  nlinarith

section Main

variable (K : Type) [Field K] [Finite K] [CharP K 2] {f : ℕ} {p : ℕ}
  (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

include L in
theorem f4_qplus_main (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) + 1 = 0) :
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
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hdvd : p ∣ Nat.card K + 1 := by
    refine (ZMod.natCast_eq_zero_iff (Nat.card K + 1) p).1 ?_
    push_cast
    exact hΦ
  have hq4 : 4 ≤ 2 ^ f := by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  set Φ : ModGL .F4 L →* ModGL .F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hinj0 : Function.Injective (rootDiagUnitHom .F4 L) := rootDiagUnit_injective
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := f4_qplus_frame K hf hK hp hp3 hΦ L
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def 2 f c
  have hodd : Odd (Nat.card K + 1) := by
    rw [hK]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have htor : ∀ (x : adjointGroup .F4 K) (c : adjointGroup .F4 K),
      g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf (qpRep L) Φ →
      ∃ b : Fin Tag.F4.rank → Lˣ,
        b ∈ fixedCharTuples (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) Fr ∧
          rootDiagUnit .F4 b = g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 := fun x c hh => by
    rw [hT] at hh
    obtain ⟨b, hb, hbh⟩ := hh
    exact ⟨b, hb, hbh⟩
  have hsolv : ∀ x : adjointGroup .F4 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V) := by
    intro x hx V hVn hVs
    have hpg : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨c, hc⟩ := hconj _ hpg
    have hh := hc x (Subgroup.mem_zpowers x)
    obtain ⟨b, hbT, hb⟩ := htor x c hh
    obtain ⟨c', b', u, J, hJu, hh', hb', hJ, -⟩ := qp_standardize K L hK hp hp3 g0 hg0C hg0 hx c b
      hb hbT
    obtain ⟨ψ, hψinj, -, hψV, -⟩ := f4_qplus_perx K L hf hK hq4 hp hp3 g0 hg0C hg0 hperf hx c'
      hh' hJu b' hb' hJ
    by_contra hnodd
    have h2 : 2 ∣ Nat.card V := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hv2 : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))) = 2 := by
      rw [orderOf_injective ψ hψinj, Subgroup.orderOf_coe, hv]
    have hmem := hψV V hVn hVs v v.2
    rw [hT] at hmem
    obtain ⟨b'', hb'', hb''v⟩ := hmem
    have hdvd2 : orderOf (ψ (v : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)))) ∣
        Nat.card K + 1 := by
      rw [← hb''v]
      refine orderOf_dvd_of_pow_eq_one ?_
      have hpow : rootDiagUnit .F4 b'' ^ (Nat.card K + 1) =
          rootDiagUnit .F4 (b'' ^ (Nat.card K + 1)) :=
        ((rootDiagUnitHom .F4 L).map_pow b'' (Nat.card K + 1)).symm
      have hb''pow : b'' ^ (Nat.card K + 1) = 1 := funext fun i => by
        rw [Pi.pow_apply, Pi.one_apply]
        exact (qp_mem_fixedCharTuples_iff hFr b'').1 hb'' i
      show rootDiagUnit .F4 b'' ^ (Nat.card K + 1) = 1
      rw [hpow, hb''pow, rootDiagUnit_one]
    rw [hv2] at hdvd2
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd2)
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
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  let φ : A₀ →* ModGL .F4 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .F4 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * adjEmb .F4 K L (c * (q : adjointGroup .F4 K) * c⁻¹) * g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf (qpRep L) Φ := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.F4.rank → Lˣ, φ q = rootDiagUnit .F4 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  set α₀ : Fin Tag.F4.rank → ℤ := Pi.single (f4Index 0) 1 with hα₀def
  have hα₀ : IsRoot .F4 α₀ := IsRoot.basis (f4Index 0)
  let χ : A₀ →* Lˣ :=
    { toFun := fun q => rootChar (β q) α₀
      map_one' := by rw [hβone]; exact CTTorus.rootChar_one α₀
      map_mul' := fun q q' => by rw [hβmul, CTTorus.rootChar_mul] }
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hχp : ∀ q : A₀, χ q ^ p = 1 := fun q => by
    rw [← map_pow]
    have h1 : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K))
        ((q : adjointGroup .F4 K) ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    have h2 : (q : adjointGroup .F4 K) ^ p = 1 := hIntinj (h1.trans (map_one _).symm)
    have h3 : q ^ p = 1 := Subtype.ext h2
    rw [h3, map_one]
  obtain ⟨q, hq1, hqχ⟩ := qp_exists_ne_one_ker hp hA₀card χ hχp
  set x : adjointGroup .F4 K := (q : adjointGroup .F4 K) with hxdef
  have hx1 : x ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hxp : x ^ p = 1 := by
    have h1 : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) (x ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ q.2
    exact hIntinj (h1.trans (map_one _).symm)
  have hx : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxA : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) x ∈ A := q.2
  have hh : g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf (qpRep L) Φ := by
    rw [← hφ q]
    exact hφT q
  have hb : rootDiagUnit .F4 (β q) = g0⁻¹ * adjEmb .F4 K L (c * x * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  have hβT : β q ∈ fixedCharTuples (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) Fr := by
    have hmem : rootDiagUnit .F4 (β q) ∈ twistedTorusOf (qpRep L) Φ := by rw [hb]; exact hh
    rw [hT] at hmem
    obtain ⟨b₁, hb₁, hb₁q⟩ := hmem
    have : b₁ = β q := hinj0 hb₁q
    rw [← this]
    exact hb₁
  obtain ⟨c', b', u, J, hJu, hh', hb', hJ, hkerEq⟩ := qp_standardize K L hK hp hp3 g0 hg0C hg0
    hx c (β q) hb hβT
  have hne : (rootCharKernel (β q)).Nonempty := ⟨α₀, hα₀, hqχ⟩
  have hJne : J.Nonempty := by
    by_contra hJe
    have hJe' : J = ∅ := Finset.not_nonempty_iff_eq_empty.1 hJe
    have hempty : rootCharKernel b' = ∅ := by
      rw [hJ, hJe']
      ext α
      simp only [Finset.coe_empty, Set.mem_empty_iff_false, iff_false]
      intro hα
      exact IsRoot.ne_zero hα.1 (funext fun i => hα.2 i (Set.notMem_empty i))
    rw [hkerEq] at hempty
    exact (hne.image _).ne_empty hempty
  obtain ⟨ψ, hψinj, hψ, -, hPt⟩ := f4_qplus_perx K L hf hK hq4 hp hp3 g0 hg0C hg0 hperf hx c' hh'
    hJu b' hb' hJ
  obtain ⟨Pt, hcomm, hPtL, i, h₀, hh₀C, hroot⟩ := hPt hJne
  refine ⟨MulAut.conj x, hxA, fun h1 => hx1 (hIntinj (by rw [h1, map_one])), ?_⟩
  exact f4_even_core_odd_of_embedding_layer K hf hK L hp hB c' g0 hg0C ψ hψinj hψ hPtL hcomm i h₀
    hh₀C hroot (hsolv x hx)

end Main

section Final


theorem planeLocalCoreOdd_F4_qplus (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 2).eval (Nat.card K : ℤ)) :
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
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
  have hΦ : ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) + 1) p).2 hpq
    simpa using this
  have h := f4_qplus_main K L hf hK hp hp3 hΦ
  exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot h.1 hout hcore h.2

theorem oddEndpoint_F4_evenQPlus :
    OddEndpoint .F4 fun p ℓ f => ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 2 ℓ f := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨rfl, hc2⟩ := hc
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e
    (planeLocalCoreOdd_F4_qplus K hf hK hp hp3 (by simpa [cycloVal, hK] using hc2))).1

end Final

end CFSG.RankThree.PartOne.KF4
