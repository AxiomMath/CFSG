module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockAbs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

@[expose] def GGKGIsReflAt (p : ℕ) {R : Type} [Group R] (E : Subgroup R) (w : R) : Prop :=
  w ∈ Subgroup.normalizer (E : Set R) ∧ (∀ e ∈ E, w * (w * e * w⁻¹) * w⁻¹ = e) ∧
    Nat.card {e : E // w * (e : R) * w⁻¹ = e} * p = Nat.card E

@[expose] def GGKGRootDatumAt (p : ℕ) {R : Type} [Group R] (E : Subgroup R) : Prop :=
  ∀ w₀ : R, GGKGIsReflAt p E w₀ →
    ∃ w : R, (∀ e ∈ E, w * e * w⁻¹ = w₀ * e * w₀⁻¹) ∧ ∃ J : Subgroup R, w ∈ J ∧
      IsComponentOf J
        (Subgroup.centralizer ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)) ∧
      p ∣ Nat.card J ∧
      ∀ a ∈ E, w * a = a * w → J ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set R))

@[expose] def GGKGRootDatum (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E → p ^ r ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → GGKGRootDatumAt p E

private theorem ggKGTr_lift_conj_mul_inv {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (Λ : R →* MulAut L') {n : L'} {w : R} (hΛn : Λ (ψ n) = MulAut.conj n) (hw : ψ n = w)
    (e : R) : Λ (w * e * w⁻¹) = MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ := by
  have h : Λ w = MulAut.conj n := by rw [← hw, hΛn]
  rw [← h, ← map_mul, ← map_inv, ← map_mul]

private theorem ggKGTr_lift_conj_inv_mul {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (Λ : R →* MulAut L') {n : L'} {w : R} (hΛn : Λ (ψ n) = MulAut.conj n) (hw : ψ n = w)
    (e : R) : Λ (w⁻¹ * e * w) = (MulAut.conj n)⁻¹ * Λ e * MulAut.conj n := by
  have h : Λ w = MulAut.conj n := by rw [← hw, hΛn]
  rw [← h, ← map_inv, ← map_mul, ← map_mul]

private theorem ggKGTr_commutator_mul_central_left {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (t s : G) : ⁅t * z, s⁆ = ⁅t, s⁆ := by
  have hz1 : ∀ x : G, z * x = x * z := fun x => (Subgroup.mem_center_iff.mp hz x).symm
  simp only [commutatorElement_def]
  rw [mul_inv_rev]
  calc t * z * s * (z⁻¹ * t⁻¹) * s⁻¹
      = t * (z * s) * (z⁻¹ * t⁻¹) * s⁻¹ := by group
    _ = t * (s * z) * (z⁻¹ * t⁻¹) * s⁻¹ := by rw [hz1 s]
    _ = t * s * t⁻¹ * s⁻¹ := by group

private theorem ggKGTr_commutator_mul_central_right {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (t s : G) : ⁅t, s * z⁆ = ⁅t, s⁆ := by
  have hz1 : ∀ x : G, z * x = x * z := fun x => (Subgroup.mem_center_iff.mp hz x).symm
  simp only [commutatorElement_def]
  rw [mul_inv_rev]
  calc t * (s * z) * t⁻¹ * (z⁻¹ * s⁻¹)
      = t * s * z * t⁻¹ * z⁻¹ * s⁻¹ := by group
    _ = t * s * (z * t⁻¹) * z⁻¹ * s⁻¹ := by group
    _ = t * s * (t⁻¹ * z) * z⁻¹ * s⁻¹ := by rw [hz1 (t⁻¹)]
    _ = t * s * t⁻¹ * s⁻¹ := by group

private theorem ggKGTr_perfect_le_layer {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {C : Subgroup R} {Q : Subgroup L'} (hQ : ⁅Q, Q⁆ = Q)
    (hle : Q.map ψ ≤ LargeEvenLayer C) : Q ≤ LargeEvenLayer (C.comap ψ) := by
  have hmap : LargeEvenLayer C ≤ (LargeEvenLayer (C.comap ψ)).map ψ := by
    refine sSup_le fun K hK => ?_
    have hY : (C.comap ψ).map ψ ≤ C := by
      rw [Subgroup.map_comap_eq_self_of_surjective hψ]
    have hn : (((C.comap ψ).map ψ).subgroupOf C).Normal := by
      rw [Subgroup.map_comap_eq_self_of_surjective hψ, Subgroup.subgroupOf_self]
      infer_instance
    have hc : ⁅C, C⁆ ≤ (C.comap ψ).map ψ := by
      rw [Subgroup.map_comap_eq_self_of_surjective hψ]
      simpa only [sup_idem] using Subgroup.commutator_le_sup C C
    obtain ⟨K', hK', hK'map⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.T123CB.exists_component_lift_of_commutator_le ψ
        (fun g hg => hker hg) hY hn hc (CFSG.Assembly.isComponentOf_iff_open.mp hK)
    rw [← hK'map]
    exact Subgroup.map_mono (le_sSup (CFSG.Assembly.isComponentOf_iff_open.mpr hK'))
  have hQT : Q ≤ LargeEvenLayer (C.comap ψ) ⊔ ψ.ker := by
    rw [← Subgroup.comap_map_eq]
    exact Subgroup.map_le_iff_le_comap.mp (hle.trans hmap)
  have hcomm_le : ⁅LargeEvenLayer (C.comap ψ) ⊔ ψ.ker,
      LargeEvenLayer (C.comap ψ) ⊔ ψ.ker⁆ ≤ LargeEvenLayer (C.comap ψ) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨t, ht, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨t', ht', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have h1 : ⁅t * z, t' * z'⁆ = ⁅t, t' * z'⁆ :=
      ggKGTr_commutator_mul_central_left (hker hz) t (t' * z')
    have h2 : ⁅t, t' * z'⁆ = ⁅t, t'⁆ :=
      ggKGTr_commutator_mul_central_right (hker hz') t t'
    rw [h1, h2]
    simpa only [sup_idem] using
      Subgroup.commutator_le_sup (LargeEvenLayer (C.comap ψ)) (LargeEvenLayer (C.comap ψ))
        (Subgroup.commutator_mem_commutator ht ht')
  calc Q = ⁅Q, Q⁆ := hQ.symm
    _ ≤ ⁅LargeEvenLayer (C.comap ψ) ⊔ ψ.ker,
          LargeEvenLayer (C.comap ψ) ⊔ ψ.ker⁆ := Subgroup.commutator_mono hQT hQT
    _ ≤ LargeEvenLayer (C.comap ψ) := hcomm_le

theorem ggTorusRootSL2_of_rootDatum {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (h : GGKGRootDatum p r R) :
    GGTorusRootSL2 p r R I := by
  classical
  intro L' _ _ ψ A hTB φ hφauto hφrefl
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := hTB
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ' ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ', ih]
    have hφp : φ' ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ' hφ'I hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ' l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦmem : ∀ e : E, Λ (e : R) ∈ A := fun e => Subgroup.mem_comap.mp (hE ▸ e.2)
  let Φfun : E → A := fun e => (⟨Λ (e : R), hΦmem e⟩ : A)
  have hΦfun_val : ∀ e : E, (Φfun e : MulAut L') = Λ (e : R) := fun e => rfl
  have hΦbij : Function.Bijective Φfun := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective Φfun hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn n, hn] at h1
    exact h1
  have h3' : p ^ 3 ≤ Nat.card E := hcardE ▸ h3
  have hr' : p ^ r ≤ Nat.card E := hcardE ▸ hr
  have hFix : ∀ e ∈ E, ggFix (Λ e) = (Subgroup.centralizer ({e} : Set R)).comap ψ := by
    intro e he
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      have h2 : e * ψ x * e⁻¹ = ψ x := by
        have h1 : Λ e x = x := mem_ggFix.mp hx
        rw [← hΛmap, h1]
      have h3 : e * ψ x = ψ x * e := by
        calc e * ψ x = (e * ψ x * e⁻¹) * e := by group
          _ = ψ x * e := by rw [h2]
      exact h3.symm
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hx
      obtain ⟨xe, hxe, hxep⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (hEab.2 e he)
      have hcx : x * xe = xe * x :=
        commute_of_lift_pow_eq_one hp hker hcpL (by rw [hxe]; exact hx) hxep
      rw [mem_ggFix, hΛeq hxe, MulAut.conj_apply]
      calc xe * x * xe⁻¹ = (x * xe) * xe⁻¹ := by rw [hcx]
        _ = x := by group
  obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hφauto
  have hvφ : φ = ggConjAut A hcN := MulEquiv.ext fun b => Subtype.ext (hvc b)
  set w₀ : R := ψ n with hw₀
  have hΛw0 : Λ w₀ = MulAut.conj n := by rw [hw₀, hΛn n]
  have hconj : ∀ e : R, Λ (w₀ * e * w₀⁻¹) = MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ :=
    fun e => ggKGTr_lift_conj_mul_inv Λ (hΛn n) hw₀.symm e
  have hnorm : w₀ ∈ Subgroup.normalizer (E : Set R) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      have h2 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hcN (Λ e)).mp (show Λ e ∈ A from he)
      rwa [← hconj e] at h2
    · intro he
      have h2 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ ∈ A := by
        rw [← hconj e]
        exact he
      exact (Subgroup.mem_normalizer_iff.mp hcN (Λ e)).mpr h2
  have hinv : ∀ e ∈ E, w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹ = e := by
    intro e he
    refine hΛinj ?_
    have hconj2 : ggConjAut A hcN ^ 2 = 1 := by rw [← hvφ, hφrefl.1]
    have hpow : (MulAut.conj n) ^ 2 * Λ e * ((MulAut.conj n) ^ 2)⁻¹ = Λ e := by
      have h1 : (((ggConjAut A hcN ^ 2) ⟨Λ e, show Λ e ∈ A from he⟩ : ↥A) : MulAut L') = Λ e := by
        rw [hconj2]
        rfl
      rwa [ggConjAut_pow_apply A hcN 2 ⟨Λ e, show Λ e ∈ A from he⟩] at h1
    calc Λ (w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹)
        = MulAut.conj n * (MulAut.conj n * Λ e * (MulAut.conj n)⁻¹) *
            (MulAut.conj n)⁻¹ := by
          rw [map_mul, map_mul, hconj e, map_inv, hΛw0]
      _ = (MulAut.conj n) ^ 2 * Λ e * ((MulAut.conj n) ^ 2)⁻¹ := by
          rw [pow_two]
          group
      _ = Λ e := hpow
  have hfixcard : Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} * p = Nat.card E := by
    rw [show Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} =
        Nat.card {b : A // φ b = b} from
      Nat.card_congr (Equiv.subtypeEquiv
        (Equiv.ofBijective Φfun hΦbij) (fun e => ?_))]
    · rw [hφrefl.2, hcardE]
    · constructor
      · intro he
        apply Subtype.ext
        rw [Equiv.coe_ofBijective, hvc, hΦfun_val e, ← hconj (e : R), he]
      · intro hb
        have h1 : MulAut.conj n * Λ (e : R) * (MulAut.conj n)⁻¹ = Λ (e : R) := by
          have h2 := congrArg (fun b : ↥A => ((b : ↥A) : MulAut L')) hb
          rw [Equiv.coe_ofBijective] at h2
          rw [hvc, hΦfun_val e] at h2
          exact h2
        rw [← hconj (e : R)] at h1
        exact hΛinj h1
  have hrefl : GGKGIsReflAt p E w₀ := ⟨hnorm, hinv, hfixcard⟩
  obtain ⟨w, hw, J, hwJ, hJcomp, hpJ, hlayer⟩ := h E hEab h3' hr' hscE w₀ hrefl
  set F : Subgroup R := E ⊓ Subgroup.centralizer ({w} : Set R) with hF
  set C : Subgroup R := Subgroup.centralizer (F : Set R) with hC
  have hJcompC : IsComponentOf J C := by
    simpa only [hC, hF] using hJcomp
  have hYmap : (C.comap ψ).map ψ = C := Subgroup.map_comap_eq_self_of_surjective hψ C
  have hn : (((C.comap ψ).map ψ).subgroupOf C).Normal := by
    rw [hYmap, Subgroup.subgroupOf_self]
    infer_instance
  have hc : ⁅C, C⁆ ≤ (C.comap ψ).map ψ := by
    rw [hYmap]
    simpa only [sup_idem] using Subgroup.commutator_le_sup C C
  obtain ⟨Q', hQ'comp_open, hQ'map⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T123CB.exists_component_lift_of_commutator_le ψ
      (fun g hg => hker hg) (le_of_eq hYmap) hn hc (CFSG.Assembly.isComponentOf_iff_open.mp hJcompC)
  have hQ'comp : IsComponentOf Q' (C.comap ψ) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hQ'comp_open
  have hpQ' : p ∣ Nat.card Q' := by
    have hdvd : Nat.card J ∣ Nat.card Q' := by
      rw [← hQ'map]
      exact Subgroup.card_map_dvd Q' ψ
    exact hpJ.trans hdvd
  obtain ⟨n', hn'Q', hn'⟩ : ∃ n' ∈ Q', ψ n' = w := by
    have hwQ' : w ∈ Q'.map ψ := by rw [hQ'map]; exact hwJ
    exact Subgroup.mem_map.mp hwQ'
  have hΛw : Λ w = MulAut.conj n' := by rw [← hn', hΛn n']
  have hHypCent : ggHypCent A n' = C.comap ψ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro f hf
      obtain ⟨hfE, hfw⟩ := Subgroup.mem_inf.mp hf
      have hfw' : w * f = f * w := (Subgroup.mem_centralizer_singleton_iff.mp hfw).symm
      have hcommconj : MulAut.conj n' * Λ f = Λ f * MulAut.conj n' := by
        refine mul_inv_eq_iff_eq_mul.mp ?_
        rw [← ggKGTr_lift_conj_mul_inv Λ (hΛn n') hn' f,
          show w * f * w⁻¹ = f by rw [hfw']; group]
      have hxfix : x ∈ ggFix (Λ f) :=
        Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx (Λ f))
          ⟨show Λ f ∈ A from hfE, hcommconj⟩
      have h1 : f * ψ x * f⁻¹ = ψ x := by
        have h1' : Λ f x = x := mem_ggFix.mp hxfix
        rw [← hΛmap, h1']
      have h2 : f * ψ x = ψ x * f := by
        calc f * ψ x = (f * ψ x * f⁻¹) * f := by group
          _ = ψ x * f := by rw [h1]
      exact h2
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hx
      rw [ggHypCent]
      refine Subgroup.mem_iInf.mpr fun a => Subgroup.mem_iInf.mpr fun ha => ?_
      obtain ⟨e, rfl⟩ := hAΛ a ha.1
      have heE : e ∈ E := show Λ e ∈ A from ha.1
      have hwe : w * e = e * w := by
        have h1 : (MulAut.conj n' * Λ e) * (MulAut.conj n')⁻¹ = Λ e :=
          mul_inv_eq_iff_eq_mul.mpr ha.2
        rw [← ggKGTr_lift_conj_mul_inv Λ (hΛn n') hn' e] at h1
        exact mul_inv_eq_iff_eq_mul.mp (hΛinj h1)
      have heF : e ∈ F := ⟨heE, Subgroup.mem_centralizer_singleton_iff.mpr hwe.symm⟩
      rw [mem_ggFix]
      obtain ⟨xe, hxe, hxep⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (hEab.2 e heE)
      have hcx : x * xe = xe * x :=
        commute_of_lift_pow_eq_one hp hker hcpL (by rw [hxe]; exact (hx e heF).symm) hxep
      rw [hΛeq hxe, MulAut.conj_apply]
      calc xe * x * xe⁻¹ = (x * xe) * xe⁻¹ := by rw [hcx]
        _ = x := by group
  have hψwu : ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
    intro e he
    rw [hw e he]
    exact (Subgroup.mem_normalizer_iff.mp hnorm e).mp he
  have hWeyl : GGTorusWeylElt p A n' := by
    intro a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (hEab.2 e heE)
    have hΛxe : Λ e = MulAut.conj x := hΛeq hx
    set u : L' := n' * x * n'⁻¹ with hu
    have hψu : ψ u = w * e * w⁻¹ := by rw [hu, map_mul, map_mul, map_inv, hn', hx]
    have hup : u ^ p = 1 := by rw [hu, conj_pow, hxp, mul_one, mul_inv_cancel]
    have hxu : x * u = u * x := by
      have hcommψ : ψ x * ψ u = ψ u * ψ x := by
        rw [hx, hψu]
        exact TableB.IsElemAbelian.comm hEab heE (hψwu e heE)
      exact commute_of_lift_pow_eq_one hp hker hcpL hcommψ hup
    have hux : n' * (Λ e n')⁻¹ = u * x⁻¹ := by
      rw [hΛxe, MulAut.conj_apply, hu]
      group
    have huxp : (u * x⁻¹) ^ p = 1 := by
      have hc : Commute u x := hxu.symm
      rw [(hc.inv_right).mul_pow, hup, inv_pow, hxp, inv_one, mul_one]
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [hux, huxp]
    · obtain ⟨e', rfl⟩ := hAΛ a' ha'
      have he'E : e' ∈ E := ha'
      obtain ⟨x', hx', hx'p⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (hEab.2 e' he'E)
      have hΛx' : Λ e' = MulAut.conj x' := hΛeq hx'
      have hψux : ψ (u * x⁻¹) ∈ E := by
        rw [map_mul, map_inv, hψu, hx]
        exact E.mul_mem (hψwu e heE) (E.inv_mem heE)
      have hcommψ : ψ x' * ψ (u * x⁻¹) = ψ (u * x⁻¹) * ψ x' := by
        rw [hx']
        exact TableB.IsElemAbelian.comm hEab he'E hψux
      have hcx' : x' * (u * x⁻¹) = (u * x⁻¹) * x' :=
        commute_of_lift_pow_eq_one hp hker hcpL hcommψ huxp
      rw [hux, hΛx', MulAut.conj_apply]
      calc x' * (u * x⁻¹) * x'⁻¹ = ((u * x⁻¹) * x') * x'⁻¹ := by rw [hcx']
        _ = u * x⁻¹ := by group
  have hwE : w ∈ Subgroup.normalizer (E : Set R) := by
    haveI : Finite R := Finite.of_surjective ψ hψ
    have hle : E.map (MulAut.conj w).toMonoidHom ≤ E := by
      rw [Subgroup.map_le_iff_le_comap]
      intro e he
      change w * e * w⁻¹ ∈ E
      exact hψwu e he
    have hcard : Nat.card (E.map (MulAut.conj w).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj w).injective
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hle hcard.ge)
  have hn'N : MulAut.conj n' ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    refine mem_normalizer_of_forall_conj_mem fun b hb => ?_
    obtain ⟨e, rfl⟩ := hAΛ b hb
    have hwinv : w⁻¹ ∈ Subgroup.normalizer (E : Set R) := Subgroup.inv_mem _ hwE
    have hwe : w⁻¹ * e * w ∈ E := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp hwinv e).mp (show e ∈ E from hb)
    rw [← ggKGTr_lift_conj_inv_mul Λ (hΛn n') hn' e]
    exact Subgroup.mem_comap.mp (show w⁻¹ * e * w ∈ A.comap Λ from hwe)
  have hconjAut : ggConjAut A hn'N = φ := by
    rw [show φ = ggConjAut A hcN from hvφ]
    refine MulEquiv.ext fun b => Subtype.ext ?_
    obtain ⟨e, he⟩ := hAΛ (b : MulAut L') b.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ b.2
    rw [ggConjAut_apply, ggConjAut_apply, ← he,
      ← ggKGTr_lift_conj_mul_inv Λ (hΛn n') hn' e, hw e heE, hconj e]
  have hLayer : ∀ (a : MulAut L') (ha : a ∈ A), φ ⟨a, ha⟩ = ⟨a, ha⟩ →
      n' ∈ LargeEvenLayer (ggFix a) := by
    intro a ha hfix
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    have h1 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ = Λ e := by
      have h2 := congrArg (fun b : ↥A => ((b : ↥A) : MulAut L')) hfix
      simpa only [hvc] using h2
    have hw0e : w₀ * e * w₀⁻¹ = e := by
      apply hΛinj
      rw [hconj e]
      exact h1
    have hwe : w * e = e * w := by
      have h2 : w * e * w⁻¹ = e := by rw [hw e heE, hw0e]
      exact mul_inv_eq_iff_eq_mul.mp h2
    have hQperf : ⁅Q', Q'⁆ = Q' :=
      CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hQ'comp.2.2.1
    have hQmap : Q'.map ψ ≤ LargeEvenLayer (Subgroup.centralizer ({e} : Set R)) := by
      rw [hQ'map]
      exact hlayer e heE hwe
    have hQle : Q' ≤ LargeEvenLayer ((Subgroup.centralizer ({e} : Set R)).comap ψ) :=
      ggKGTr_perfect_le_layer hψ hker hQperf hQmap
    rw [← hFix e heE] at hQle
    exact hQle hn'Q'
  exact ⟨n', hn'N, Q', hWeyl, hconjAut, hn'Q', by rw [hHypCent]; exact hQ'comp, hpQ', hLayer⟩

end CFSG.StandardType

end
