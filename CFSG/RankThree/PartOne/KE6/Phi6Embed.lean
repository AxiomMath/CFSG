module

public import CFSG.RankThree.PartOne.KE6.Phi6Solvable
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff twistedTorusOf
  twistedFixedPoints mem_twistedFixedPoints subtorusSigma subtorusSigma_le_twistedTorusOf)
open scoped Matrix Pointwise commutatorElement

theorem isQuasisimple_perfectResidual {C Γ : Type*} [Group C] [Group Γ] (D : Subgroup C)
    (ψ : D →* Γ) (hψ : Function.Injective ψ) (P : Subgroup Γ) (hPq : CFSG.IsQuasisimple P)
    (hmap : (CFSG.perfectResidual D).map ψ = P) :
    CFSG.IsQuasisimple ↥((CFSG.perfectResidual D).map D.subtype) := by
  let e₁ : ↥((CFSG.perfectResidual D).map D.subtype) ≃* ↥(CFSG.perfectResidual D) :=
    (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).symm
  let e₂ : ↥(CFSG.perfectResidual D) ≃* ↥P :=
    (Subgroup.equivMapOfInjective _ ψ hψ).trans (MulEquiv.subgroupCongr hmap)
  exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv (e₁.trans e₂).symm hPq

theorem phi6_embedding_A2A2 (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * phi6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E6 K L).range)
    {x : adjointGroup Tag.E6 K} (hxp : orderOf x = p)
    (hh : g0⁻¹ * adjEmb Tag.E6 K L x * g0 ∈
      twistedTorus (phi6N L) (iterateFrobenius L ℓ f))
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L x * g0) =
        parabolicRoots Tag.E6 supportA2A2) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K)) →* ModGL Tag.E6 L,
      Function.Injective ψ ∧
      (∀ d, ψ d = g0⁻¹ * adjEmb Tag.E6 K L (d : adjointGroup Tag.E6 K) * g0) ∧
      (∀ d, ψ d ∈ torusGroup Tag.E6 L ⊔
        rootSpan Tag.E6 L (torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L x * g0))) ∧
      (∀ d, phi6N L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ d) *
        (phi6N L)⁻¹ = ψ d) ∧
      phi6P L (iterateFrobenius L ℓ f) (torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L x * g0)) ≤
        ψ.range ∧
      CFSG.IsQuasisimple ↥(phi6P L (iterateFrobenius L ℓ f)
        (torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L x * g0))) ∧
      (torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel (g0⁻¹ *
          adjEmb Tag.E6 K L x * g0))) ⊓
        Subgroup.centralizer (↑(phi6P L (iterateFrobenius L ℓ f) (torusRootKernel (g0⁻¹ *
          adjEmb Tag.E6 K L x * g0))) : Set (ModGL Tag.E6 L)) ≤ torusGroup Tag.E6 L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr c
  have hℓ : ℓ.Prime := Fact.out
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpq
    exact hpq
  have hp7 : 7 ≤ p := (e6Six_data hp hp3 hpq').2.2.2.2.1
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E6) := by
    have : Fintype (WeylGroup Tag.E6) := Fintype.ofFinite _
    rw [(CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2]
    intro hd
    have h51840 : p ∣ 2 ^ 7 * 3 ^ 4 * 5 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).1 h51840 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  set ι : adjointGroup Tag.E6 K →* ModGL Tag.E6 L := adjEmb Tag.E6 K L with hιdef
  set h : ModGL Tag.E6 L := g0⁻¹ * ι x * g0 with hhdef
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hh).1
  have hb' : rootDiagUnit Tag.E6 b = g0⁻¹ * ι x * g0 := hb.symm
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι x) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective (ι x)
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    rw [e1, orderOf_injective ι adjEmb_injective x, hxp]
  have hNorm : torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel h) ≤
      Subgroup.normalizer (rootSpan Tag.E6 L (torusRootKernel h) : Set (ModGL Tag.E6 L)) :=
    torusGroup_sup_rootSpan_le_normalizer fun α hα => hα.1
  have hrootneg : ∀ α ∈ torusRootKernel h, -α ∈ torusRootKernel h := fun α hα => by
    rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
    exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  obtain ⟨hfin, hqs, -, -, -, hC6, hcentQ⟩ := phi6_A2A2_case (K := K) hℓ hf hK hFr hp hp3 hpq'
    hh hordh hA2A2
  have hcS : 1 * x * 1⁻¹ ∈ subtorusImage ι g0
      (subtorusSigma (phi6N L) (Units.map (entrywiseHom Fr)) (torusRootKernel h)) := by
    rw [mem_subtorusImage_iff]
    refine Subgroup.mem_inf.2 ⟨by simpa using hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hle := rootSpan_le_centralizer (K := L) b (S := torusRootKernel h) (by
      rw [← torusRootKernel_rootDiagUnit, hb])
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    rw [hb'] at h1
    simpa using h1
  have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a =
      g0⁻¹ * ι (1 * x * 1⁻¹) * g0 → rootCharKernel a ⊆ torusRootKernel h := fun a ha => by
    have : a = b := rootDiagUnit_injective (ha.trans (by simpa using hb'.symm))
    rw [this, ← torusRootKernel_rootDiagUnit, hb]
  obtain ⟨ψ, hψinj, hψdef, hψHQ, hψfix, hψadj, hPψ, -⟩ := sigma_embedding_data ι adjEmb_injective
    adjEmb_mem (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFrK) (phi6N L) g0 hg0C hg0
    hperf hp hordW (S := torusRootKernel h) (fun α hα => hα.1) hrootneg
    (fun _ : Unit => phi6P L Fr (torusRootKernel h)) (fun _ => hfin) (fun _ => hqs)
    (fun _ => (phi6P_le _).trans inf_le_left) (fun _ => (phi6P_le _).trans inf_le_right)
    (fun _ => (phi6P_le _).trans (inf_le_left.trans (rootSpan_le_adjointGroup L _)))
    (fun _ y hy hyR u hu => phi6P_conj_mem (hNorm hy) hyR hu)
    (fun y hy hyR hc => by
      have hyH : y ∈ torusGroup Tag.E6 L := hC6 ⟨hy, Subgroup.mem_centralizer_iff.2 fun u hu =>
        (hc () u hu).symm⟩
      have hcent := hcentQ y hyH (fun u hu => hc () u hu)
      exact Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hyH, mem_twistedFixedPoints.1 hyR⟩,
        Subgroup.mem_centralizer_iff.2 fun g hg => (hcent g hg).symm⟩)
    hxp 1 hcS hkerZ
  refine ⟨ψ, hψinj, fun d => by simpa using hψdef d, hψHQ, hψfix, hPψ (), hqs, hC6⟩

end CFSG.RankThree.PartOne.KE6
