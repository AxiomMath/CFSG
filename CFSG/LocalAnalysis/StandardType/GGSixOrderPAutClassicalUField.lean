module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalUInner
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraph
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff gramSU unitarySU_eq_gramSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace OrdPFieldSU

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

noncomputable abbrev projP (h : UnitaryFieldData 2 f F) (hn : 1 ≤ n) :
    ↥(unitarySU 2 f F n) →* primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  (InndiagSU.projEquiv h hn).toMonoidHom.comp (InndiagSU.projU f n F)

omit [Finite F] [CharP F 2] in
theorem projP_apply (h : UnitaryFieldData 2 f F) (hn : 1 ≤ n) (x : ↥(unitarySU 2 f F n))
    (hx : (x : GL (Fin n) F) ∈ gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    projP h hn x = ((⟨x, hx⟩ : gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
      primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
  rfl

omit [Finite F] [CharP F 2] in
theorem projP_surjective (h : UnitaryFieldData 2 f F) (hn : 1 ≤ n) :
    Function.Surjective (projP h hn) :=
  (InndiagSU.projEquiv h hn).surjective.comp InndiagSU.projU_surjective

omit [Finite F] [CharP F 2] in
theorem projP_eq_one_iff (h : UnitaryFieldData 2 f F) (hn : 1 ≤ n) (x : ↥(unitarySU 2 f F n)) :
    projP h hn x = 1 ↔ ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c = x := by
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  change (QuotientGroup.mk (s := (LargeEvenScalars (Fin n) F).subgroupOf
    (LargeEvenSUGroup (Fin n) F (2 ^ f))) (x : ↥(LargeEvenSUGroup (Fin n) F (2 ^ f)))) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

omit [Finite F] [CharP F 2] in
theorem mem_gramSU_one (h : UnitaryFieldData 2 f F) (x : ↥(unitarySU 2 f F n)) :
    (x : GL (Fin n) F) ∈ gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  InndiagSU.largeEvenSUGroup_eq_gramSU (d := n) h ▸ x.2

section Split

variable (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem exists_conj_mem_centralizer_split {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hf : 1 ≤ f) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Unitary.rootDatum hF n) .PSU n f ψ)
    (hpq : p ∣ 2 ^ f + 1) (hpn : ¬ p ∣ n) {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G))
    (hyp : y ^ p = 1) (hyI : ¬ GGPsiInnerDiag (Unitary.rootDatum hF n) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hrk : 2 ≤ n / 2 := hrank
  have hn : 4 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hcop : Nat.Coprime p (Nat.gcd n (2 ^ f + 1)) :=
    (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun hd => hpn (hd.trans (Nat.gcd_dvd_left _ _))
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set φ := SURep.ggFrameU hF ψ P₀ hP₀ with hφ
  have hrφ : φ.range = G₀ := (SURep.range_ggFrameU hF ψ P₀ hP₀).trans hrange
  have hker₁ : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f F n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hC₁ : Subgroup.centralizer (φ.range : Set G) = ⊥ := by
    rw [hrφ]
    exact hS.centralizer_eq_bot
  set π := projP h hn1 with hπdef
  have hk : π.ker = φ.ker := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπdef, projP_eq_one_iff]
    constructor
    · rintro ⟨c, hc⟩
      have hz : φ z ∈ Subgroup.centralizer (φ.range : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨u, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← hc, TypeA.PGLTor.scalar_mul_comm]
      rw [hC₁, Subgroup.mem_bot] at hz
      exact hz
    · intro hz
      obtain ⟨e, he⟩ := SURep.ggFrameKer_of_ker_le_center hF hn3 hnq hker₁ z hz
      have he0 : e ≠ 0 := by
        rintro rfl
        have h1 := (z : GL (Fin n) F).det_ne_zero
        rw [he, map_zero, det_zero] at h1
        exact h1 rfl
      refine ⟨Units.mk0 e he0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, he, Units.val_mk0]
  set Θ := AutSt.modelEquiv φ π (projP_surjective h hn1) hk with hΘdef
  have hΘ : ∀ x, ((Θ (π x) : φ.range) : G) = φ x :=
    AutSt.modelEquiv_apply φ π (projP_surjective h hn1) hk
  have hyM' : y ∈ Subgroup.normalizer (φ.range : Set G) := by
    rw [hrφ]
    exact hyM
  set a : MulAut φ.range := φ.range.normalizerMonoidHom ⟨y⁻¹, inv_mem hyM'⟩ with hadef
  have ha : ∀ x : φ.range, ((a x : φ.range) : G) = y⁻¹ * x * y :=
    OrdPGraph.normalizerMonoidHom_inv_apply hyM'
  have hap : a ^ p = 1 := by
    rw [hadef, ← map_pow]
    have e : (⟨y⁻¹, inv_mem hyM'⟩ : Subgroup.normalizer (φ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, hyp, inv_one]; rfl)
    rw [e, map_one]
  set β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    MulAut.congr Θ.symm a with hβdef
  have hβ : ∀ x, Θ (β x) = a (Θ x) := fun x => by
    rw [hβdef, MulAut.congr_apply]
    simp
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← map_pow, hap, map_one]
  have hrel : ∀ x x' : ↥(unitarySU 2 f F n), β (π x) = π x' → y⁻¹ * φ x * y = φ x' := by
    intro x x' hxx'
    have e := congrArg (fun z => ((Θ z : φ.range) : G)) hxx'
    simp only [hβ, ha, hΘ] at e
    exact e
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  obtain ⟨⟨A, θ⟩, hAθ⟩ := primeFormPsi_surjective h hC1 hn3 hq β
  rw [primeFormPsi_apply] at hAθ
  have hθ1 : θ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hAθ
    apply hyI
    have hpair : (y⁻¹, (A : GL (Fin n) F)) ∈ SUTorus.suPairs φ := by
      refine ⟨SUTorus.mem_normalizer_of_mem_primeFormUnitary h A.2, fun u v hv => ?_⟩
      rw [inv_inv]
      refine hrel u v ?_
      rw [← hAθ, hπdef, projP_apply h hn1 u (mem_gramSU_one h u), primeFormConjHom_mk,
        projP_apply h hn1 v (mem_gramSU_one h v)]
      congr 1
      apply Subtype.ext
      exact hv.symm
    obtain ⟨s, hs, -⟩ := OrdPInnerSU.exists_eq_of_mem_suPairs h hn hker₁ hC₁ hcop A.2 hpair hyp
    refine ⟨y⁻¹, ψ.range.inv_mem ⟨_, hs⟩, fun γ _ => ⟨1, one_mem _, fun z _ => ?_⟩⟩
    simp
  obtain ⟨hθo, H, hH⟩ := RecipeFieldSpU.primeForm_conj_of_pow_eq_one h hn3 hq hpp hp2 A θ hθ1
    (by rw [hAθ]; exact hβp)
  have hθp : θ ^ p = 1 := hθo ▸ pow_orderOf_eq_one θ
  have hβH : β = primeFormConjHom h _ H * primeFormFieldHom h hC1 θ *
      (primeFormConjHom h _ H)⁻¹ := by
    rw [← hAθ]
    exact hH
  obtain ⟨P, hP⟩ := OrdPInnerSU.exists_bstar_frame hF hf hS hpq hpn hP₀
  obtain ⟨τ, hHτ⟩ := OrdPInnerSU.exists_mul_diagHom_mem h hn1 H.2
  obtain ⟨H', hH'⟩ : ∃ H' : ↥(unitarySU 2 f F n), (H' : GL (Fin n) F) = H * diagHom n τ :=
    ⟨⟨_, hHτ⟩, rfl⟩
  refine ⟨φ (H' * P⁻¹), Subgroup.le_normalizer (hrφ ▸ ⟨_, rfl⟩), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨x, hxb, hxp, σ, hσ⟩ := hP b hb
  rw [← hφ] at hxb
  obtain ⟨D, hD⟩ : ∃ D : ↥(unitarySU 2 f F n), D = P⁻¹ * x * P := ⟨_, rfl⟩
  rw [← hD] at hσ
  have hσp : σ ^ p = 1 := by
    apply diagHom_injective n
    rw [map_pow, ← hσ, map_one, ← Subgroup.coe_pow, hD]
    have e : (P⁻¹ * x * P) ^ p = 1 := by
      rw [show P⁻¹ * x * P = MulAut.conj P⁻¹ x by simp, ← map_pow, hxp, map_one]
    rw [e]
    rfl
  have hθσ : ∀ i, θ ((σ i : Fˣ) : F) = σ i := fun i =>
    OrdPRest.ringAut_fix_of_pow_eq_one hpp hθp (by
      rw [← Units.val_pow_eq_pow_val, ← Pi.pow_apply, hσp, Pi.one_apply, Units.val_one])
  have hfD : primeFormFieldHom h hC1 θ (π D) = π D := by
    rw [hπdef, projP_apply h hn1 D (mem_gramSU_one h D)]
    change primeFormFieldAut h hC1 θ _ = _
    rw [primeFormFieldAut_mk]
    congr 1
    apply Subtype.ext
    change glAut θ (D : GL (Fin n) F) = D
    rw [hσ]
    apply Units.ext
    rw [coe_glAut, coe_diagHom, Matrix.diagonal_map (map_zero θ)]
    congr 1
    funext i
    exact hθσ i
  have hcD : primeFormConjHom h _ H (π D) = π (H' * D * H'⁻¹) := by
    rw [hπdef, projP_apply h hn1 D (mem_gramSU_one h D), primeFormConjHom_mk,
      projP_apply h hn1 (H' * D * H'⁻¹) (mem_gramSU_one h _)]
    congr 1
    apply Subtype.ext
    change (H : GL (Fin n) F) * D * (H : GL (Fin n) F)⁻¹ = H' * D * (H' : GL (Fin n) F)⁻¹
    rw [hH', hσ]
    calc (H : GL (Fin n) F) * diagHom n σ * (H : GL (Fin n) F)⁻¹ =
        (H : GL (Fin n) F) * (diagHom n τ * diagHom n σ * (diagHom n τ)⁻¹) *
          (H : GL (Fin n) F)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul, mul_comm τ σ, mul_inv_cancel_right]
      _ = (H : GL (Fin n) F) * diagHom n τ * diagHom n σ * ((H : GL (Fin n) F) * diagHom n τ)⁻¹ :=
          by group
  have hfix : β (π (H' * D * H'⁻¹)) = π (H' * D * H'⁻¹) := by
    have hinv : ∀ z, (primeFormConjHom h _ H)⁻¹ (primeFormConjHom h _ H z) = z := fun z => by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [← hcD, hβH, MulAut.mul_apply, MulAut.mul_apply, hinv, hfD]
  have hcomm : y * φ (H' * D * H'⁻¹) = φ (H' * D * H'⁻¹) * y := by
    calc y * φ (H' * D * H'⁻¹) = y * (y⁻¹ * φ (H' * D * H'⁻¹) * y) := by rw [hrel _ _ hfix]
      _ = φ (H' * D * H'⁻¹) * y := by group
  have hbm : b = (φ (H' * P⁻¹))⁻¹ * φ (H' * D * H'⁻¹) * φ (H' * P⁻¹) := by
    rw [← hxb, ← map_inv, ← map_mul, ← map_mul, hD]
    congr 1
    group
  rw [hbm]
  calc (φ (H' * P⁻¹))⁻¹ * φ (H' * D * H'⁻¹) * φ (H' * P⁻¹) *
        ((φ (H' * P⁻¹))⁻¹ * y * φ (H' * P⁻¹)) =
      (φ (H' * P⁻¹))⁻¹ * (φ (H' * D * H'⁻¹) * y) * φ (H' * P⁻¹) := by group
    _ = (φ (H' * P⁻¹))⁻¹ * (y * φ (H' * D * H'⁻¹)) * φ (H' * P⁻¹) := by rw [hcomm]
    _ = (φ (H' * P⁻¹))⁻¹ * y * φ (H' * P⁻¹) *
        ((φ (H' * P⁻¹))⁻¹ * φ (H' * D * H'⁻¹) * φ (H' * P⁻¹)) := by group

end Split

end OrdPFieldSU

section Family

theorem ggOrdPFieldConj_PSU_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSU n f).D .PSU n f ψ → p ∣ 2 ^ f + 1 → ¬ p ∣ n →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      ¬ GGPsiInnerDiag (ggU .PSU n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS hpq hpn y hyM hyo hyI
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  exact OrdPFieldSU.exists_conj_mem_centralizer_split
    (F := GaloisField 2 (2 * (f + 1))) (card_galoisField_two_mul 2 (f + 1) (by omega)) (by omega)
    hS hpq hpn hyM hyp hyI

@[expose] def GGOrdPFieldConjPSURest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .PSU n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSU n f).D .PSU n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → (¬ p ∣ 2 ^ f + 1 ∨ p ∣ n) →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiDiagField (ggU .PSU n f).D ψ y →
      ¬ GGPsiInnerDiag (ggU .PSU n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPFieldConjAt_PSU_of_rest (h : GGOrdPFieldConjPSURest) : GGOrdPFieldConjAt .PSU := by
  intro G _ _ p Bs G₀ n f ψ hS h24 y hyM hyo hDF hyI
  by_cases hc : p ∣ 2 ^ f + 1 ∧ ¬ p ∣ n
  · exact ggOrdPFieldConj_PSU_split G p Bs G₀ n f ψ hS hc.1 hc.2 y hyM hyo hyI
  · refine h G p Bs G₀ n f ψ hS h24 ?_ y hyM hyo hDF hyI
    by_cases hpq : p ∣ 2 ^ f + 1
    · exact Or.inr (not_not.mp fun hn => hc ⟨hpq, hn⟩)
    · exact Or.inl hpq

end Family

end CFSG.StandardType
