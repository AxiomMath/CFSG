module

public import CFSG.RankThree.PartOne.KE.A1TwE6Ten
public import CFSG.RankThree.PartOne.KLCE.TwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6FiveAd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitComponentEmbed
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A1Fixed
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E6TwFourKernel
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KLCE.E8Seven
public import CFSG.RankThree.PartOne.KLCE.EngineG

public noncomputable section

namespace CFSG.StandardType

open Matrix CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.RankThree.Classical (conjSL)
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)
open CFSG.RankThree.PartOne.KE
open CFSG.StandardType.E6Nonsplit
open scoped Matrix Polynomial MatrixGroups

namespace TwE6Nonsplit

theorem a1_twisted_structure
    {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 < p) (hordW : ¬ p ∣ Nat.card (WeylGroup TwistTag.E6.tag))
    (n : ModGL TwistTag.E6.tag L) (hnC : n ∈ adjointGroup TwistTag.E6.tag L)
    {θ : Fin TwistTag.E6.tag.rank → ℤ} (hθ : IsRoot TwistTag.E6.tag θ)
    (hZcyc : IsCyclic (subtorusA1 n (twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)) θ))
    {N : ℕ} (hN : N ≠ 0)
    (hZcard : Nat.card (subtorusA1 n (twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)) θ) = N)
    (hord : p ^ ((ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1)).factorization p =
      p ^ N.factorization p)
    (hkerZ : ∀ a : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag a ∈
        subtorusA1 n (twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)) θ →
      orderOf (rootDiagUnit TwistTag.E6.tag a) = p → rootCharKernel a ⊆ {θ, -θ}) :
    ∀ (S : Subgroup (SL2 L)) [Finite S],
      (∀ B : SL2 L, n * twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)
          (rootSL2 TwistTag.E6.tag L θ B) * n⁻¹ = rootSL2 TwistTag.E6.tag L θ B ↔ B ∈ S) →
      Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
        Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range →
      ∀ x : twistedE6RootGroup K σ, orderOf x = p →
        (CFSG.IsQuasisimple S →
          ∃ (ψ : ↥(Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))) →*
              ModGL TwistTag.E6.tag L)
            (P Z : Subgroup (ModGL TwistTag.E6.tag L)),
            Function.Injective ψ ∧ Nonempty (↥S ≃* ↥P) ∧ P ≤ ψ.range ∧
            (∀ d : ↥(Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), ∀ u ∈ P,
              ψ d * u * (ψ d)⁻¹ ∈ P) ∧
            (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) ∧
            (∀ d : ↥(Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))),
              (∀ u ∈ P, ψ d * u = u * ψ d) → ψ d ∈ Z)) ∧
        (Group.IsSolvable S →
          Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)))) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted_gen K (ℓ := ℓ) (f := f) hf L n hnC
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, hRcard, hpp⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  set R := twistedFixedGroup TwistTag.E6 L Fr with hR
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R).Normal := by
    have e : C'.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hyΓ : ∀ y : twistedE6RootGroup K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    fun y => graphFixedRootGroup_le _ _ _ y.2
  have hιC : ∀ y, ι y ∈ adjointGroup TwistTag.E6.tag L := fun y =>
    baseChangeGL_mem_adjointGroup _ ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hyΓ y)).1
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by
      change algebraMap K L (σ c) = Fr (algebraMap K L c)
      rw [hσ, hFr, map_pow]
  have hιΦ : ∀ y, twistHom TwistTag.E6 L Fr (ι y) = ι y := fun y => by
    change twistHom TwistTag.E6 L Fr (baseChangeGL (algebraMap K L) (y : ModGL _ K)) =
      baseChangeGL (algebraMap K L) (y : ModGL _ K)
    rw [twistHom_baseChangeGL (algebraMap K L) hcomm,
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hyΓ y)).2]
  have hrat3 : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ι.range.relIndex X ∣ 3 ^ k ∧
        (∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X →
          IsPGroup p' P → P ≤ ι.range) ∧
        ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X → ⁅P, P⁆ = P → P ≤ ι.range := by
    intro X _ hXC hXF
    have hXR : X ≤ R := fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    rw [hrange]
    refine ⟨relIndex_dvd_of_le_of_index_dvd hXR (hk ▸ dvd_rfl), fun p' hp' hp'3 P hPX hP => ?_,
      fun P hPX hPP => ?_⟩
    · have : Finite P :=
        Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
      exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp' Nat.prime_three (by omega) hk hP
    · have hPR : P ≤ R := hPX.trans hXR
      calc P = ⁅P, P⁆ := hPP.symm
        _ ≤ ⁅R, R⁆ := Subgroup.commutator_mono hPR hPR
        _ = C' := hder
  have hrat2 : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ι.range.relIndex X ∣ 3 ^ k ∧
        ∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X →
          IsPGroup p' P → P ≤ ι.range := fun X _ hXC hXF => by
    have h := hrat3 X hXC hXF
    exact ⟨h.1, h.2.1⟩
  have hordC : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ N.factorization p := by
    have h1 := hpp p hp (by omega)
    have h2 : Nat.card C' = Nat.card (twistedE6RootGroup K σ) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [h2, hRcard] at h1
    rw [h1]
    exact hord
  have hZle : subtorusA1 n (twistHom TwistTag.E6 L Fr) θ ≤
      twistedTorusOf n (twistHom TwistTag.E6 L Fr) := subtorusA1_le_twistedTorusOf _ _ _
  obtain ⟨-, -, -, -, -, hconj⟩ := sylow_conjugacy_of_subtorus (3 ^ k) ι hι
    (twistHom TwistTag.E6 L Fr) n g0 hg0C hg0 hp (by omega) hN hrat2 _ hZle hZcyc hZcard hordC
  exact a1_centralizer_structure ι hι hιC (twistHom TwistTag.E6 L Fr) hιΦ n g0 hg0C hg0
    (fun P hP hPC hPF hPp => (hrat3 P hPC hPF).2.2 P le_rfl hPp) hp hordW hθ (hZ := hZcyc) hconj
    hkerZ

theorem twE6_ten_structure
    {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 10).eval ((ℓ ^ f : ℕ) : ℤ)) :
    ∀ x : twistedE6RootGroup K σ, orderOf x = p →
      ∀ X : Subgroup (twistedE6RootGroup K σ),
        IsComponentOf X (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))) →
          4 ≤ ℓ ^ f ∧ Nonempty (SL(2, GaloisField ℓ f) ≃* ↥X) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hℓq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
  have hpf' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 4 - ((ℓ ^ f : ℕ) : ℤ) ^ 3 +
      ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord10, hΦ5⟩ := CTE6.twE6Ten_data hp hp5 hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup TwistTag.E6.tag) :=
    not_dvd_card_weylGroup_E (τ := .E6) hp hp7 (Or.inl rfl)
  obtain ⟨-, -, -, -, hrange, hPfix, ⟨hn, hπ, hv1, hv2⟩, htw, -⟩ :=
    E6_highest_root_graph_fixed_and_signed_order_five_descent L
  set n : ModGL TwistTag.E6.tag L := e6HRn L with hndef
  have hnC : n ∈ adjointGroup TwistTag.E6.tag L := monomialSubgroup_le_adjointGroup' hn
  set v := weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ with hvdef
  have hv : ∀ x : Fin TwistTag.E6.tag.rank → ℤ,
      v • x = (((-1 : ℤ)) • e6O5W) *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [hv1 x, smul_neg, e6HRw_smul, neg_one_smul, Matrix.neg_mulVec]
    rfl
  have hθroot : IsRoot TwistTag.E6.tag e6O5Theta :=
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.1
  have hθ : e6HighestRoot = e6O5Theta := rfl
  have hT := twistedTorus_E6_eq_map_of_weylImage Fr hn v rfl ((-1 : ℤ) • e6O5W) hv
  have hZeq := subtorusA1_eq_map_fixedBlockTuples hT hθroot
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.E6.tag L) := rootDiagUnit_injective
  set D := CFSG.RankThree.PartOne.KLCE.twE6SignedBlock (-1) (Or.inr rfl) with hD
  have hq5 : (1 : ℤ) < ((ℓ ^ f : ℕ) : ℤ) ^ 5 := by
    have : (2 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast hq2
    calc (1 : ℤ) < 2 := by norm_num
      _ ≤ 2 ^ 5 := by norm_num
      _ ≤ ((ℓ ^ f : ℕ) : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) this 5
  have hne : D.P.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    rw [hD]
    change (Polynomial.X ^ 5 - Polynomial.C (-1) : ℤ[X]).eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    omega
  obtain ⟨hcycB, hcardB⟩ := D.isCyclic_and_card Fr hFr hℓ hℓq hne
  have hZcyc : IsCyclic (subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom TwistTag.E6.tag L) hinj0).isCyclic.1
      hcycB
  have hZcard : Nat.card (subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta) =
      (ℓ ^ f) ^ 5 + 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0]
    refine hcardB.trans ?_
    rw [hD]
    change ((Polynomial.X ^ 5 - Polynomial.C (-1) : ℤ[X]).eval ((ℓ ^ f : ℕ) : ℤ)).natAbs = _
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have e : ((ℓ ^ f : ℕ) : ℤ) ^ 5 - -1 = (((ℓ ^ f) ^ 5 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [e, Int.natAbs_natCast]
  have hN : (ℓ ^ f) ^ 5 + 1 ≠ 0 := by omega
  have hord := CTTw.ordProj_twisted_ten hp hq2 hpq hord10
  have hz' : ∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
      (((-1 : ℤ) • e6O5W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z =
        ((ℓ ^ f : ℕ) : ZMod p) • z →
        {α | IsRoot Tag.E6 α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} := fun z hz0 hzM =>
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.2.2.2.2.2 p hp hp5
      (-((ℓ ^ f : ℕ) : ZMod p)) hΦ5 z hz0 (transpose_eigen_neg e6O5W _ z hzM)
  have hz : ∀ z : Fin TwistTag.E6.tag.rank → ZMod p, z ≠ 0 →
      (((-1 : ℤ) • e6O5W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z =
        ((ℓ ^ f : ℕ) : ZMod p) • z →
        {α | IsRoot TwistTag.E6.tag α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} :=
    fun z hz0 hzM => hz' z hz0 hzM
  have hkerZ : ∀ b : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag b ∈ subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta →
      orderOf (rootDiagUnit TwistTag.E6.tag b) = p →
      rootCharKernel b ⊆ {e6O5Theta, -e6O5Theta} := by
    intro b hb hbp
    rw [hZeq] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have : b' = b := hinj0 hbb'
    subst this
    exact (A1BlockData.rootCharKernel_eq Fr hFr hp hz hb'.1
      (CFSG.RankThree.PartOne.KE.pow_eq_one_of_orderOf_rootDiagUnit hbp)
      (CFSG.RankThree.PartOne.KE.ne_one_of_orderOf_rootDiagUnit hp hbp)).le
  have hρmem : ∀ B : SL2 L, rootSL2 TwistTag.E6.tag L e6HighestRoot B ∈
      rootSubgroup TwistTag.E6.tag L e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag L (-e6HighestRoot) := fun B => by
    rw [← hrange]
    exact ⟨B, rfl⟩
  have hΦ : ∀ B : SL2 L, twistHom TwistTag.E6 L Fr (rootSL2 TwistTag.E6.tag L e6HighestRoot B) =
      rootSL2 TwistTag.E6.tag L e6HighestRoot (SpecialLinearGroup.map Fr B) := fun B => by
    rw [twistHom_apply, entrywise_rootSL2_of_field Fr e6HighestRoot B]
    exact hPfix _ (hρmem _)
  have hnQ : ∀ B : SL2 L, n * rootSL2 TwistTag.E6.tag L e6HighestRoot B * n⁻¹ =
      rootSL2 TwistTag.E6.tag L e6HighestRoot (WSL * B * WSL⁻¹) := fun B => by
    have h := htw (RingEquiv.refl L) B
    have hP := hPfix _ (hρmem B)
    have hmapid : SpecialLinearGroup.map (RingEquiv.refl L).toRingHom B = B := by
      ext i j
      simp [SpecialLinearGroup.map_apply_coe]
    have e : Units.map (entrywiseHom (RingEquiv.refl L).toRingHom)
        (rootSL2 TwistTag.E6.tag L e6HighestRoot B) = rootSL2 TwistTag.E6.tag L e6HighestRoot B :=
      Units.ext (entrywise_id _)
    rw [e6HRTwist, e, hmapid] at h
    calc n * rootSL2 TwistTag.E6.tag L e6HighestRoot B * n⁻¹
        = n * (diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
          (diagramMap TwistTag.E6 L)⁻¹) * n⁻¹ := by rw [hP]
      _ = n * diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
          (diagramMap TwistTag.E6 L)⁻¹ * n⁻¹ := by group
      _ = rootSL2 TwistTag.E6.tag L e6HighestRoot (WSL * B * WSL⁻¹) := h
  have : NeZero f := ⟨by omega⟩
  letI : Algebra (ZMod ℓ) L := ZMod.algebra L ℓ
  let k := GaloisField ℓ f
  letI : Algebra k L := (IsAlgClosed.lift : k →ₐ[ZMod ℓ] L).toRingHom.toAlgebra
  have hkcard : Nat.card k = ℓ ^ f := GaloisField.card ℓ f (by omega)
  have hFrk : ∀ c, Fr c = c ^ Nat.card k := fun c => by rw [hkcard]; exact hFr c
  obtain ⟨P, hP⟩ := exists_WSL_twist (K := k) (L := L) Fr hFrk
  have hX : ∀ B : SL2 L, n * twistHom TwistTag.E6 L Fr (rootSL2 TwistTag.E6.tag L e6HighestRoot B) *
      n⁻¹ = rootSL2 TwistTag.E6.tag L e6HighestRoot
        (conjSL (P * GeneralLinearGroup.map Fr P⁻¹) (SpecialLinearGroup.map Fr B)) := fun B => by
    rw [hΦ B, hnQ, hP, conjSL_toGL]
  set S : Subgroup (SL2 L) :=
    (SpecialLinearGroup.map (algebraMap k L)).range.map (conjSL P) with hSdef
  have hS1 : ∀ B : SL2 L, n * twistHom TwistTag.E6 L Fr
      (rootSL2 TwistTag.E6.tag L e6HighestRoot B) * n⁻¹ =
        rootSL2 TwistTag.E6.tag L e6HighestRoot B ↔ B ∈ S :=
    fun B => a1_hS1_of_action Fr hFrk P hX B
  have hS3 : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range :=
    sl2_conj_range_centralizer (K := k) P
  obtain ⟨e0⟩ := E6Nonsplit.nonempty_mulEquiv_sl2_conj_range (K := k) (L := L) P
  haveI : Finite ↥S := Finite.of_equiv _ e0.toEquiv
  have hStr := a1_twisted_structure (ℓ := ℓ) hf K hK σ hσ L hp hp7 hordW n hnC hθroot hZcyc hN
    hZcard hord hkerZ S hS1 hS3
  intro x hx X hXcomp
  by_cases hK4 : 4 ≤ ℓ ^ f
  · have hk4 : 4 ≤ Nat.card k := by rwa [hkcard]
    obtain ⟨-, hSqs⟩ := sl2_conj_range_quasisimple (L := L) hk4 P
    obtain ⟨ψ, P', Z, hψ, ⟨hPe⟩, hP'ψ, hnorm, hZ, hcent⟩ := (hStr x hx).1 hSqs
    obtain ⟨e1⟩ := ExcNonsplit.nonempty_mulEquiv_of_isComponentOf_centralizer ψ hψ hPe hSqs hP'ψ
      hnorm hZ hcent hXcomp
    exact ⟨hK4, ⟨e0.trans e1⟩⟩
  · exfalso
    have hklt : Nat.card k < 4 := by rw [hkcard]; omega
    haveI hsolSL : Group.IsSolvable SL(2, k) := isSolvable_SL_two_of_card_lt_four hklt
    haveI : Group.IsSolvable ↥S :=
      Group.isSolvable_of_isSolvable_injective (f := e0.symm.toMonoidHom) e0.symm.injective
    haveI := (hStr x hx).2 inferInstance
    exact ExcNonsplit.not_isComponentOf_of_isSolvable hXcomp

end TwE6Nonsplit

end CFSG.StandardType
