module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9End2
public import CFSG.RankThree.PartTwo.Sec17.Item174Layer

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def conjAutX (X : Subgroup G) : ↥(Subgroup.normalizer (X : Set G)) →* MulAut ↥X where
  toFun g :=
    { toFun := fun x => ⟨(g : G) * x * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩
      invFun := fun x => ⟨(g : G)⁻¹ * x * (g : G), by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem g.2) x).mp x.2
        simpa using this⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
  map_mul' g h := MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc])

theorem coe_conjAutX (X : Subgroup G) (g : ↥(Subgroup.normalizer (X : Set G))) (x : ↥X) :
    ((conjAutX X g x : ↥X) : G) = (g : G) * x * (g : G)⁻¹ :=
  rfl

theorem mem_pPrimeCore_iff (X : Subgroup G) (x : ↥X) :
    x ∈ pPrimeCore 3 ↥X ↔ (x : G) ∈ pPrimeCoreOf 3 X :=
  (Subgroup.mem_map_iff_mem X.subtype_injective).symm

theorem map_conjAutX_pPrimeCore (X : Subgroup G) (g : ↥(Subgroup.normalizer (X : Set G))) :
    (pPrimeCore 3 ↥X).map (conjAutX X g : ↥X →* ↥X) = pPrimeCore 3 ↥X := by
  have hgK : (g : G) ∈ Subgroup.normalizer (pPrimeCoreOf 3 X : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 X g.2
  ext y
  change y ∈ (pPrimeCore 3 ↥X).map (conjAutX X g).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv, mem_pPrimeCore_iff, mem_pPrimeCore_iff]
  have e : (g : G) * (((conjAutX X g).symm y : ↥X) : G) * (g : G)⁻¹ = y := by
    rw [← coe_conjAutX, MulEquiv.apply_symm_apply]
  rw [Subgroup.mem_normalizer_iff.mp hgK, e]

@[expose] noncomputable def conjAutQ (X : Subgroup G) [(pPrimeCore 3 ↥X).Normal] :
    ↥(Subgroup.normalizer (X : Set G)) →* MulAut (↥X ⧸ pPrimeCore 3 ↥X) where
  toFun g := QuotientGroup.congr _ _ (conjAutX X g) (map_conjAutX_pPrimeCore X g)
  map_one' := MulEquiv.ext fun q => QuotientGroup.induction_on q fun x => by
    rw [QuotientGroup.congr_mk, map_one]
    rfl
  map_mul' g h := MulEquiv.ext fun q => QuotientGroup.induction_on q fun x => by
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
      map_mul, MulAut.mul_apply]

theorem conjAutQ_mk (X : Subgroup G) [(pPrimeCore 3 ↥X).Normal]
    (g : ↥(Subgroup.normalizer (X : Set G))) (x : ↥X) :
    conjAutQ X g (x : ↥X ⧸ pPrimeCore 3 ↥X) = ((conjAutX X g x : ↥X) : ↥X ⧸ pPrimeCore 3 ↥X) :=
  QuotientGroup.congr_mk _ _ _ (map_conjAutX_pPrimeCore X g) x

@[expose] def KFactL3Aut : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (n : ℕ), Odd n →
    Nonempty (H ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 n)) →
    ∀ σ : MulAut H, (∃ k : ℕ, σ ^ (2 ^ k) = 1) → ∀ t : H, orderOf t = 3 → σ t = t →
      ∀ D : Subgroup H, D ≠ ⊥ → IsPGroup 2 D → (∀ d ∈ D, σ d ∈ D) →
        (∀ u : H, u * t = t * u → ∀ d ∈ D, u * d * u⁻¹ ∈ D) → σ = 1

@[expose] def KFact26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → omegaA A = {Subgroup.zpowers c} → ¬ IsL3TwoPow L →
    ¬ ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c) →
    haveI : (pPrimeCore 3 ↥(normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
      c)).Normal := pPrimeCore_normal
    ∃ n : ℕ, Odd n ∧
      Nonempty (↥(normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c) ⧸
        pPrimeCore 3 ↥(normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c) ≃*
          CFSG.PGLModel.projSL 3 (GaloisField 2 n))

@[expose] def KFact26At (A : Subgroup G) (c : G) (L Y₀ : Subgroup G) : Prop :=
  omegaA A = {Subgroup.zpowers c} → ¬ IsL3TwoPow L →
    ¬ ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c) →
    haveI : (pPrimeCore 3 ↥(normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
      c)).Normal := pPrimeCore_normal
    ∃ n : ℕ, Odd n ∧
      Nonempty (↥(normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c) ⧸
        pPrimeCore 3 ↥(normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c) ≃*
          CFSG.PGLModel.projSL 3 (GaloisField 2 n))

theorem kfact39At_of {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (h26 : KFact26At A c L Y₀) (hL3 : KFactL3Aut) : KFact39At A c L Y₀ := by
  intro hΩ hL hW γ hγA hk x hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E : Subgroup G := A ⊓ L with hEdef
  set X := normalClosureIn (Subgroup.centralizer (E : Set G)) c with hXdef
  set K := pPrimeCoreOf 3 X with hKdef
  set W := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)) with hWdef
  obtain ⟨n, hn, ⟨e⟩⟩ := h26 hΩ hL hW
  haveI : (pPrimeCore 3 ↥X).Normal := pPrimeCore_normal
  set K' := pPrimeCore 3 ↥X with hK'def
  have hcA : c ∈ A := h.mem_A
  have hM : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    h.normalizer_le.trans (normalizer_le_normalizer_w Y₀)
  have hCAW : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.centralizer_le_normalizer (A : Set G)).trans hM
  have hcCE : c ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he => h.commute he.1 hcA
  have hWC : W ≤ Subgroup.centralizer (E : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (Subgroup.centralizer_le (inf_le_right.trans h.le_y0))
  have hcX : c ∈ X := by
    rw [hXdef, normalClosureIn]
    exact Subgroup.subset_closure ⟨1, one_mem _, by simp⟩
  have hKX : K ≤ X := pPrimeCoreOf_le 3 X
  have hXK : X ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hγX : γ ∈ Subgroup.normalizer (X : Set G) :=
    le_normalizer_normalClosureIn _ c (Subgroup.centralizer_le inf_le_left hγA)
  set σ := conjAutQ X ⟨γ, hγX⟩ with hσdef
  have hσk : σ ^ (2 ^ (Classical.choose hk)) = 1 := by
    rw [hσdef, ← map_pow]
    have : (⟨γ, hγX⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ (2 ^ (Classical.choose hk)) = 1 :=
      Subtype.ext (by simpa using Classical.choose_spec hk)
    rw [this, map_one]
  have hc3 : orderOf c = 3 := by
    have hmem : Subgroup.zpowers c ∈ omegaA A := hΩ ▸ Set.mem_singleton _
    rw [← Nat.card_zpowers]
    exact (mem_omegaA_iff.mp hmem).2.1
  set t : ↥X ⧸ K' := ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ K') with htdef
  have ht3 : orderOf t = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [htdef, ← QuotientGroup.mk_pow]
      have : (⟨c, hcX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simp [← hc3, pow_orderOf_eq_one])
      rw [this, QuotientGroup.mk_one]
    · intro h1
      have hcK : (⟨c, hcX⟩ : ↥X) ∈ K' := (QuotientGroup.eq_one_iff _).mp h1
      rw [mem_pPrimeCore_iff] at hcK
      have hdvd : 3 ∣ Nat.card K := hc3 ▸ Subgroup.orderOf_dvd_natCard K hcK
      have := Nat.Coprime.eq_one_of_dvd (coprime_card_pPrimeCoreOf 3 X) hdvd
      norm_num at this
  have hσt : σ t = t := by
    rw [htdef, hσdef, conjAutQ_mk]
    congr 1
    refine Subtype.ext ?_
    rw [coe_conjAutX]
    have hγc : c * γ = γ * c := Subgroup.mem_centralizer_iff.mp hγA c hcA
    change γ * c * γ⁻¹ = c
    rw [← hγc, mul_inv_cancel_right]
  set D : Subgroup (↥X ⧸ K') := ((W ⊓ X).subgroupOf X).map (QuotientGroup.mk' K') with hDdef
  have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hD2 : IsPGroup 2 D := ((hW2.to_le inf_le_left).comap_subtype).map _
  have hcW : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans (Subgroup.le_normalizer.trans hM)
  have hcWX : ⁅Subgroup.zpowers c, W⁆ ≤ W ⊓ X := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp hcW) ?_
    rw [Subgroup.commutator_le]
    intro g hg w hw
    have hgX : g ∈ X := (Subgroup.zpowers_le.mpr hcX) hg
    have hwX : w * g⁻¹ * w⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_normalClosureIn _ c (hWC hw)) _).mp
        (inv_mem hgX)
    rw [commutatorElement_def]
    have := mul_mem hgX hwX
    rwa [show g * (w * g⁻¹ * w⁻¹) = g * w * g⁻¹ * w⁻¹ by group] at this
  have hD1 : D ≠ ⊥ := by
    intro hD
    apply hW
    rw [Subgroup.commutator_comm]
    intro y hy
    have hy' := hcWX hy
    have hmem : ((⟨y, hy'.2⟩ : ↥X) : ↥X ⧸ K') ∈ D :=
      ⟨⟨y, hy'.2⟩, Subgroup.mem_subgroupOf.mpr hy', rfl⟩
    rw [hD, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_pPrimeCore_iff] at hmem
    exact hmem
  have hnorm : ∀ z : ↥X, (z : G) ∈ Subgroup.normalizer (W : Set G) → ∀ d ∈ D,
      (z : ↥X ⧸ K') * d * (z : ↥X ⧸ K')⁻¹ ∈ D := by
    rintro z hzW _ ⟨w, hw, rfl⟩
    have hw' := Subgroup.mem_subgroupOf.mp hw
    refine ⟨z * w * z⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, (z * w * z⁻¹).2⟩, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hzW _).mp hw'.1
  have hσD : ∀ d ∈ D, σ d ∈ D := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' := Subgroup.mem_subgroupOf.mp hw
    rw [QuotientGroup.mk'_apply, hσdef, conjAutQ_mk]
    refine ⟨conjAutX X ⟨γ, hγX⟩ w, Subgroup.mem_subgroupOf.mpr ⟨?_, (conjAutX X _ w).2⟩, rfl⟩
    rw [coe_conjAutX]
    exact (Subgroup.mem_normalizer_iff.mp (hCAW hγA) _).mp hw'.1
  have hTD : ∀ u : ↥X ⧸ K', u * t = t * u → ∀ d ∈ D, u * d * u⁻¹ ∈ D := by
    intro u hu
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
    have hyc : (y : G) * c * (y : G)⁻¹ * c⁻¹ ∈ K := by
      have h1 : ((y * ⟨c, hcX⟩ * y⁻¹ * (⟨c, hcX⟩ : ↥X)⁻¹ : ↥X) : ↥X ⧸ K') = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv, ← htdef, hu]
        group
      have h2 := (mem_pPrimeCore_iff X _).mp ((QuotientGroup.eq_one_iff _).mp h1)
      simpa using h2
    obtain ⟨o, ho, z, hzX, hzc, hoz⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.gen49e_mem_mul_centralizer Nat.prime_three hKX hXK
        (coprime_card_pPrimeCoreOf 3 X) hcX y.2 hc3 hyc
    have hyz : ((y : ↥X) : ↥X ⧸ K') = ((⟨z, hzX⟩ : ↥X) : ↥X ⧸ K') := by
      rw [QuotientGroup.eq]
      refine (mem_pPrimeCore_iff X _).mpr ?_
      have hmem : z⁻¹ * o⁻¹ * z⁻¹⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hXK (inv_mem hzX)) _).mp (inv_mem ho)
      have : (((y : ↥X)⁻¹ * ⟨z, hzX⟩ : ↥X) : G) = z⁻¹ * o⁻¹ * z⁻¹⁻¹ := by
        change (y : G)⁻¹ * z = _
        rw [← hoz]
        group
      rw [this]
      exact hmem
    rw [hyz]
    have hzC : z ∈ Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ((Commute.zpow_right (show Commute z c from hzc) m).eq).symm
    exact hnorm ⟨z, hzX⟩ (normalizer_le_normalizer_w Y₀
      (h.normalizer_c_le (Subgroup.centralizer_le_normalizer _ hzC)))
  have hσ1 : σ = 1 :=
    hL3 (↥X ⧸ K') n hn ⟨e⟩ σ ⟨_, hσk⟩ t ht3 hσt D hD1 hD2 hσD hTD
  have hfix := congrArg (fun f : MulAut (↥X ⧸ K') => f ((⟨x, hx⟩ : ↥X) : ↥X ⧸ K')) hσ1
  simp only [MulAut.one_apply] at hfix
  rw [hσdef, conjAutQ_mk, QuotientGroup.eq_iff_div_mem, mem_pPrimeCore_iff] at hfix
  simpa [div_eq_mul_inv, coe_conjAutX] using hfix

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
