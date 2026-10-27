module

public import CFSG.RankThree.PartOne.KE.E6TwFourFamily
public import CFSG.RankThree.PartOne.KE.E6TwFourArith
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.RankThree.PartOne.KE.CommutatorFactor
public import CFSG.RankThree.PartOne.KE.E6TwFourKernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix e6Index e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)
open scoped Matrix MatrixGroups

section Emb

@[expose] def twE6Emb (K : Type) [Field K] (σ : K ≃+* K) (L : Type) [Field L] [Algebra K L] :
    twistedE6RootGroup K σ →* ModGL Tag.E6 L :=
  (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype

variable {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]

theorem twE6Emb_apply (y : twistedE6RootGroup K σ) :
    twE6Emb K σ L y = baseChangeGL (algebraMap K L) (y : ModGL TwistTag.E6.tag K) :=
  rfl

theorem twE6Emb_injective : Function.Injective (twE6Emb K σ L) :=
  (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)

theorem twE6Emb_mem (y : twistedE6RootGroup K σ) :
    twE6Emb K σ L y ∈ adjointGroup Tag.E6 L :=
  baseChangeGL_mem_adjointGroup _
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (graphFixedRootGroup_le _ _ _ y.2)).1

theorem twE6Emb_fixed (Fr : L →+* L) (hcomm : (algebraMap K L).comp σ.toRingHom =
      Fr.comp (algebraMap K L)) (y : twistedE6RootGroup K σ) :
    twistE6 Fr (twE6Emb K σ L y) = twE6Emb K σ L y := by
  change twistHom TwistTag.E6 L Fr (baseChangeGL (algebraMap K L) (y : ModGL TwistTag.E6.tag K)) =
    baseChangeGL (algebraMap K L) (y : ModGL TwistTag.E6.tag K)
  rw [twistHom_baseChangeGL (algebraMap K L) hcomm,
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (graphFixedRootGroup_le _ _ _ y.2)).2]

end Emb

section Rational

theorem e6_tw_rational {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    ∃ kk : ℕ,
      (∀ (X : Subgroup (ModGL Tag.E6 L)) [Finite X], X ≤ adjointGroup Tag.E6 L →
        (∀ x ∈ X, twistE6 Fr x = x) →
        (twE6Emb K σ L).range.relIndex X ∣ 3 ^ kk ∧
          (∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL Tag.E6 L), P ≤ X →
            IsPGroup p' P → P ≤ (twE6Emb K σ L).range) ∧
          ∀ P : Subgroup (ModGL Tag.E6 L), P ≤ X → ⁅P, P⁆ = P → P ≤ (twE6Emb K σ L).range) ∧
      ∀ p : ℕ, p.Prime → 3 < p →
        p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
          p ^ ((ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
            ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1)).factorization p := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨-, -, hder, ⟨kk, hk⟩, -, hRcard, hpp⟩ :=
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
  have hrange : (twE6Emb K σ L).range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have key : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      C'.relIndex X ∣ 3 ^ kk ∧
        (∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X →
          IsPGroup p' P → P ≤ C') ∧
        ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X → ⁅P, P⁆ = P → P ≤ C' := by
    intro X _ hXC hXF
    have hXR : X ≤ R := fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    refine ⟨relIndex_dvd_of_le_of_index_dvd hXR (hk ▸ dvd_rfl), fun p' hp' hp'3 P hPX hP => ?_,
      fun P hPX hPP => ?_⟩
    · have : Finite P :=
        Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
      exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp' Nat.prime_three (by omega) hk hP
    · have hPR : P ≤ R := hPX.trans hXR
      calc P = ⁅P, P⁆ := hPP.symm
        _ ≤ ⁅R, R⁆ := Subgroup.commutator_mono hPR hPR
        _ = C' := hder
  refine ⟨kk, fun X hX hXC hXF => ?_, fun p hp hp3 => ?_⟩
  · rw [hrange]
    exact @key X hX hXC hXF
  · have h1 := hpp p hp hp3
    have h2 : Nat.card C' = Nat.card (twistedE6RootGroup K σ) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [h2, hRcard] at h1
    exact h1

end Rational

section Frame

theorem card_fixSubfield_twisted {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (fixSubfield σ) = ℓ ^ f := by
  have hK2 : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK2
  have hσfr : σ = fr ^ f := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr f c]
  have hσo : orderOf σ = 2 := by
    rw [hσfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 2 rfl), hord,
      Nat.mul_div_cancel _ (by omega)]
  obtain ⟨-, hσcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ
    (by omega : 1 ≤ 2 * f) hK2 σ
  rw [hσo, Nat.mul_div_cancel_left _ (by norm_num)] at hσcard
  exact hσcard

theorem e6_tw_four_frame {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x) :
    ∃ g0 : ModGL Tag.E6 L, g0 ∈ adjointGroup Tag.E6 L ∧
      twistE6 (iterateFrobenius L ℓ f) g0 = g0 * n ∧
      (∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
        (∀ x ∈ P, twistE6 (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
          P ≤ (twE6Emb K σ L).range) ∧
      twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) =
        (fixedCharTuples (e6SM (-1)) (iterateFrobenius L ℓ f)).map
          (rootDiagUnitHom Tag.E6 L) ∧
      ∀ Q : Subgroup (twistedE6RootGroup K σ), IsPGroup p Q →
        ∃ c : twistedE6RootGroup K σ, ∀ q ∈ Q, g0⁻¹ * twE6Emb K σ L (c * q * c⁻¹) * g0 ∈
          twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hℓq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
  have hnC : n ∈ adjointGroup Tag.E6 L := monomialSubgroup_le_adjointGroup' hnm
  obtain ⟨g0, hg0C, hg0'⟩ : ∃ g0 : ModGL Tag.E6 L, g0 ∈ adjointGroup Tag.E6 L ∧
      twistE6 Fr g0 = g0 * n := lang_conjugator_twisted_gen K (ℓ := ℓ) (f := f) hf L n hnC
  have hT : twistedTorusOf n (twistE6 Fr) =
      (fixedCharTuples (e6SM (-1)) Fr).map (rootDiagUnitHom Tag.E6 L) :=
    twistedTorus_E6_eq_map_of_weylImage Fr hnm _ rfl (e6SM (-1)) hnW
  obtain ⟨kk, hrat, hordC⟩ := e6_tw_rational hℓ hf K hK σ hσ L Fr hFr
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E6 L) := rootDiagUnit_injective
  set G3 := fixedBlockTuples (e6SM (-1)) Fr
    (e6SCols 3 (-1) '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) with hG3
  set G0 := fixedBlockTuples (e6SM (-1)) Fr
    (e6SCols 0 (-1) '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) with hG0
  set N : ℕ := ((((ℓ ^ f : ℕ) : ℤ) ^ 3 - (-1 : ℤ) * ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ((ℓ ^ f : ℕ) : ℤ) -
    (-1 : ℤ)).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL Tag.E6 L) := (G3 ⊔ G0).map (rootDiagUnitHom Tag.E6 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n (twistE6 Fr) := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e6S_card_sup (-1) (Or.inr rfl) Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := pow_ne_zero 2 (e6S_card_ne_zero (Or.inr rfl) hq2)
  have hord : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ N.factorization p := by
    rw [hordC p hp hp3]
    exact e6TwFour_ordProj hp hp3 hq2 hpq
  obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen (3 ^ kk) (twE6Emb K σ L)
    twE6Emb_injective (twistE6 Fr) n g0 hg0C hg0' hp hp3 hN
    (fun X hX hXC hXF => ⟨(@hrat X hX hXC hXF).1, (@hrat X hX hXC hXF).2.1⟩) Z0 hZ0le hZ0card
    hord
  refine ⟨g0, hg0C, hg0', fun P hPfin hPC hPF hPP => (@hrat P hPfin hPC hPF).2.2 P le_rfl hPP,
    hT, fun Q hQ => ?_⟩
  obtain ⟨c, hc⟩ := hconj Q hQ
  exact ⟨c, fun q hq => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc q hq))⟩

end Frame

section PerX

theorem e6_tw_four_perx {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((ℓ ^ f : ℕ) : ZMod p) = 4) (hΦ : ((ℓ ^ f : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x)
    (g0 : ModGL Tag.E6 L) (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    (hT : twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) =
      (fixedCharTuples (e6SM (-1)) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom Tag.E6 L))
    {x : twistedE6RootGroup K σ} (hx : orderOf x = p) (c : twistedE6RootGroup K σ)
    (hh : g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) →* ModGL Tag.E6 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * twE6Emb K σ L (c * (y : twistedE6RootGroup K σ) * c⁻¹) * g0) ∧
      ∀ b : Fin Tag.E6.rank → Lˣ,
        rootDiagUnit Tag.E6 b = g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0 →
        (∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
          Group.IsSolvable V → ∀ v ∈ V,
            ψ v ∈ subtorusSigma n (twistE6 (iterateFrobenius L ℓ f)) (rootCharKernel b)) ∧
        ((rootCharKernel b).Nonempty →
          ∃ Pt : Subgroup (ModGL Tag.E6 L), CFSG.IsQuasisimple Pt ∧ ⁅ψ.range, ψ.range⁆ = Pt ∧
            (∃ h₀ : ModGL Tag.E6 L, ∀ Y : SL(2, fixSubfield σ),
              h₀ * simpleRootSL2 Tag.E6 L (e6Index 0)
                (Matrix.SpecialLinearGroup.map ((algebraMap K L).comp (fixSubfield σ).subtype)
                  Y) * h₀⁻¹ ∈ Pt) ∧
            ∃ v : WeylGroup Tag.E6, rootCharKernel b = sigmaSetE6A3 v ∧
              ∃ H : SL(4, L), ∀ Y : SL(4, fixSubfield σ),
                rhoSigmaE6A3 L v (H * Matrix.SpecialLinearGroup.map
                  ((algebraMap K L).comp (fixSubfield σ).subtype) Y * H⁻¹) ∈ Pt) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL Tag.E6 L →* ModGL Tag.E6 L := twistE6 Fr with hΦdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by
      change algebraMap K L (σ c) = Fr (algebraMap K L c)
      rw [hσ, hFr, map_pow]
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E6 L) := rootDiagUnit_injective
  set ι : twistedE6RootGroup K σ →* ModGL Tag.E6 L := twE6Emb K σ L with hιdef
  set h : ModGL Tag.E6 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit Tag.E6 b = h := hbh
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι twE6Emb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbp : orderOf (rootDiagUnit Tag.E6 b) = p := by rw [hbh']; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  have hstab : ∀ a : Fin Tag.E6.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit Tag.E6 a ∈ twistedTorusOf n Φ → rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup Tag.E6)) := by
    intro a hap' ha1 haT
    rw [hT] at haT
    obtain ⟨a', ha', haa⟩ := haT
    have : a' = a := hinj0 haa
    subst this
    exact e6TwFour_stab_of_fixed Fr hFr hp hp3 hord hΦ ha' hap' ha1
  have core : ∀ (S : Set (Fin Tag.E6.rank → ℤ)), rootCharKernel b = S →
      (∀ α ∈ S, IsRoot Tag.E6 α) → (∀ α ∈ S, -α ∈ S) →
      ∀ {ι' : Type} (P : ι' → Subgroup (ModGL Tag.E6 L)), (∀ i, Finite (P i)) →
        (∀ i, CFSG.IsQuasisimple (P i)) → (∀ i, P i ≤ rootSpan Tag.E6 L S) →
        (∀ i, P i ≤ twistedFixedPoints n Φ) → (∀ i, P i ≤ adjointGroup Tag.E6 L) →
        (∀ i, ∀ y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L S, y ∈ twistedFixedPoints n Φ →
          ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) →
        (∀ y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L S, y ∈ twistedFixedPoints n Φ →
          (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S) →
        ∃ ψ : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) →* ModGL Tag.E6 L,
          Function.Injective ψ ∧
          (∀ y, ψ y = g0⁻¹ * ι (c * (y : twistedE6RootGroup K σ) * c⁻¹) * g0) ∧
          (∀ y, ψ y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L S) ∧
          (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup Tag.E6 L) ∧
          (∀ i, P i ≤ ψ.range) ∧
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))),
            V.Normal → Group.IsSolvable V → ∀ v ∈ V, ψ v ∈ subtorusSigma n Φ S := by
    intro S hSeq hS hSn ι' P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    have hsub : S ⊆ rootCharKernel b := fun α hα => by rw [hSeq]; exact hα
    have hle := rootSpan_le_centralizer (K := L) b hsub
    have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S) := by
      rw [mem_subtorusImage_iff]
      refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      rw [hbh'] at h1
      exact h1
    have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a = h → rootCharKernel a ⊆ S :=
      fun a ha => by rw [hker a ha, hSeq]
    exact sigma_embedding_data_of_stab ι twE6Emb_injective twE6Emb_mem Φ
      (twE6Emb_fixed Fr hcomm) n g0 hg0C hg0 hperf hp hstab hS hSn P hPfin hPq hPQ hPR hPadj
      hPnorm hPcent hx c hcS hkerZ
  have hkd := e6TwFour_kernel_of_fixed Fr hFr hp hp3 hΦ hb hap hb1
  have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  rcases hkd with hA | ⟨v, hSeq, hunit⟩
  ·
    have hspan : rootSpan Tag.E6 L (rootCharKernel b) = ⊥ := by
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
    refine ⟨ψ, hψinj, hψ, fun b' hb' => ⟨fun V hVn hVs v hv => ?_, fun hne => ?_⟩⟩
    · rw [hker b' hb']
      exact hψV V hVn hVs v hv
    · exfalso
      rw [hker b' hb', hA] at hne
      exact Set.not_nonempty_empty hne
  ·
    have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
    have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
    have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
    have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ hσ
    obtain ⟨P, hP, hP1, ⟨h₀, hh₀⟩, ⟨H, hH⟩⟩ :=
      e6_tw_four_family hℓ hf (k := fixSubfield σ) hkc Fr hFr n hnm hnW v hunit
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hP
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := core (sigmaSetE6A3 v) hSeq
      (sigmaSetE6A3_isRoot v) (sigmaSetE6A3_neg v) P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    refine ⟨ψ, hψinj, hψ, fun b' hb' => ⟨fun V hVn hVs v' hv' => ?_, fun _ => ?_⟩⟩
    · rw [hker b' hb', hSeq]
      exact hψV V hVn hVs v' hv'
    · refine ⟨P (), hPq (), ?_, ⟨h₀, hh₀⟩, v, by rw [hker b' hb', hSeq], H, hH⟩
      refine commutator_range_eq_of_family ψ (H := torusGroup Tag.E6 L)
        (Q := rootSpan Tag.E6 L (sigmaSetE6A3 v)) (R := twistedFixedPoints n Φ) ?_ ?_ hψHQ
        (fun y => mem_twistedFixedPoints.2 (hψR y)) hP1 (hPψ ()) ?_
      · exact torusGroup_le_normalizer_rootSpan (sigmaSetE6A3_isRoot v)
      · intro a ha a' ha'
        obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
        exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ ha'
      · exact Subgroup.isPerfect_iff.1 (hPq ()).1

end PerX

section Solvable

theorem e6_tw_four_abelian_two_torsion {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {V : Type*} [Group V] (ψ : V →* ModGL Tag.E6 L)
    (hψ : Function.Injective ψ)
    (hV : ∀ v : V, ψ v ∈ (fixedCharTuples (e6SM (-1)) Fr).map (rootDiagUnitHom Tag.E6 L)) :
    (∀ v w : V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  choose a ha hav using fun v : V => hV v
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E6 L) := rootDiagUnit_injective
  have hmul : ∀ v w : V, a (v * w) = a v * a w := fun v w => by
    apply hinj0
    rw [hav, map_mul, map_mul, hav, hav]
  refine ⟨fun v w => ?_, ?_⟩
  · apply hψ
    rw [map_mul, map_mul, ← hav v, ← hav w, ← map_mul, ← map_mul, mul_comm]
  · set Γ : Subgroup (Fin Tag.E6.rank → Lˣ) :=
      (fixedCharTuples (e6SM (-1)) Fr) ⊓ ψ.range.comap (rootDiagUnitHom Tag.E6 L) with hΓ
    have hΓle : Γ ≤ fixedCharTuples (e6SM (-1)) Fr := inf_le_left
    let φ : {v : V // v ^ 2 = 1} → {g : Γ // g ^ 2 = 1} := fun v =>
      ⟨⟨a v.1, Subgroup.mem_inf.2 ⟨ha v.1, ⟨v.1, (hav v.1).symm⟩⟩⟩, by
        apply Subtype.ext
        apply hinj0
        change rootDiagUnitHom Tag.E6 L (a v.1 ^ 2) = rootDiagUnitHom Tag.E6 L 1
        rw [map_pow, hav, ← map_pow, v.2, map_one, map_one]⟩
    have hφ : Function.Injective φ := fun v w h => by
      apply Subtype.ext
      apply hψ
      rw [← hav v.1, ← hav w.1]
      have := congrArg (fun g : {g : Γ // g ^ 2 = 1} => ((g.1 : Γ) : Fin Tag.E6.rank → Lˣ)) h
      simp only [φ] at this
      rw [this]
    obtain ⟨hfin, hcard⟩ := e6S_card_two_torsion_le_four Fr hFr (Or.inr rfl) hΓle
    exact (Nat.card_le_card_of_injective φ hφ).trans hcard

theorem e6_tw_four_solvable {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x) :
    ∀ x : twistedE6RootGroup K σ, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
        Group.IsSolvable V →
        (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_tw_four_frame K hf hK σ hσ hp hp3 hpq L n hnm hnW
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  intro x hx V hVn hVs
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ψ, hψinj, -, hψ⟩ := e6_tw_four_perx K hf hK σ hσ hp hp3 hordq hΦ L n hnm hnW g0 hg0C
    hg0 hperf hT hx c hh
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hh).1
  obtain ⟨hψV, -⟩ := hψ b hb.symm
  have hVT : ∀ v : V, ψ (v : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))) ∈
      (fixedCharTuples (e6SM (-1)) (iterateFrobenius L ℓ f)).map
        (rootDiagUnitHom Tag.E6 L) := fun v => by
    rw [← hT]
    exact subtorusSigma_le_twistedTorusOf _ _ _ (hψV V hVn hVs v v.2)
  obtain ⟨hab, h2⟩ := e6_tw_four_abelian_two_torsion (iterateFrobenius L ℓ f) hFr
    (ψ.comp V.subtype) (hψinj.comp V.subtype_injective) hVT
  refine ⟨fun v hv w hw => ?_, h2⟩
  have := hab ⟨v, hv⟩ ⟨w, hw⟩
  exact congrArg Subtype.val this

end Solvable

end CFSG.RankThree.PartOne.KE
