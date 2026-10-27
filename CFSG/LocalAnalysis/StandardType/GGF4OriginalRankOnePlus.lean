module

public import CFSG.LocalAnalysis.StandardType.GGF4OriginalRankOne
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusRankOne
public import CFSG.LocalAnalysis.StandardType.GGSignedTorusInnerAction
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly Multiplicative Module
open CFSG.RankThree.Classical2 (orthDerived)

namespace OmPlusFrame

theorem exists_b3_torus_automizer {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank F V = 8) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (E : Subgroup ↥(orthDerived Q)) (hE : IsElemAbelian p E)
    (hcard : p ^ 3 ≤ Nat.card E)
    (hsc : ∀ z : ↥(orthDerived Q), (∀ a ∈ E, z * a = a * z) → z ^ p = 1 → z ∈ E) :
    ∃ τ : (Fin 3 → Multiplicative (ZMod p)) →* ↥(orthDerived Q),
      Function.Injective τ ∧ τ.range = E ∧
      (∀ g : ↥(orthDerived Q), (∀ a ∈ E, g * a * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p),
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      ∃ e : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer (⊤ : Subgroup ↥(orthDerived Q)) E),
        ∀ i, GGIsReflection p (e ((CoxeterMatrix.B 3).simple i) : MulAut ↥E) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite F
  have hcardE : Nat.card E = p ^ 3 := le_antisymm
    (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.card_le_pow_pred_of_isElemAbelian_orthDerived
      hQ (n := 4) (by omega) hminus (by norm_num) (by decide) hp hp2 hpq E hE) hcard
  let A : Subgroup (V ≃ₗ[F] V) := E.map (orthDerived Q).subtype
  have hAO : A ≤ orthDerived Q := Subgroup.map_subtype_le E
  have hApow : ∀ a ∈ A, a ^ p = 1 := by
    rintro a ⟨z, hz, rfl⟩
    exact congrArg Subtype.val (hE.2 z hz)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro a ⟨z, hz, rfl⟩ b ⟨z', hz', rfl⟩
    exact congrArg Subtype.val (CFSG.Open.IsElemAbelian.comm hE hz hz')
  have hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A := by
    intro g hg hgp hgc
    let z : ↥(orthDerived Q) := ⟨g, hg⟩
    have hz : z ∈ E := hsc z
      (fun a ha => Subtype.ext (hgc a ⟨a, ha, rfl⟩)) (Subtype.ext hgp)
    exact ⟨z, hz, rfl⟩
  have hcardA : Nat.card A = p ^ 3 := by
    change Nat.card (E.map (orthDerived Q).subtype) = p ^ 3
    rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective, hcardE]
  have hne : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr h
    rw [hbot, Subgroup.card_bot] at hcardA
    have := Nat.one_lt_pow (by decide : 3 ≠ 0) hp.one_lt
    omega
  have hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ v ∈ T, Q v = 0 :=
    OrthRestOdd.exists_totallySingular_three Q hQ (by omega)
  obtain ⟨r, τ, _, _, _, _, hτinj, hτrange, hperm, _, hnorm, hchar⟩ :=
    OrthTorus.exists_torus_frame_full hp2 (Or.inr hpq) hQ hT hAO hApow hAcomm hmax hne
  have hr : r = 3 := by
    have hτcard : Nat.card A = p ^ r := by
      rw [← hτrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hτinj,
        Subgroup.card_top, Nat.card_fun, Nat.card_fin]
      change Nat.card (ZMod p) ^ r = p ^ r
      rw [Nat.card_zmod]
    exact Nat.pow_right_injective hp.two_le (hτcard.symm.trans hcardA)
  subst r
  have hsgn : ∀ i : Fin 3, ∃ w ∈ orthDerived Q,
      ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f) := by
    rcases hchar with ⟨-, hdim'⟩ | ⟨-, -, hs⟩
    · omega
    · exact hs
  have hτO : ∀ f, τ f ∈ orthDerived Q := fun f => hAO (hτrange ▸ ⟨f, rfl⟩)
  let τΩ : (Fin 3 → Multiplicative (ZMod p)) →* ↥(orthDerived Q) :=
    τ.codRestrict (orthDerived Q) hτO
  have hτΩinj : Function.Injective τΩ := fun f f' h => hτinj (congrArg Subtype.val h)
  have hτΩrange : τΩ.range = E := by
    ext z
    constructor
    · rintro ⟨f, rfl⟩
      have hf : τ f ∈ A := hτrange ▸ ⟨f, rfl⟩
      obtain ⟨z, hz, hzτ⟩ := hf
      have hz' : z = τΩ f := Subtype.ext hzτ
      exact hz' ▸ hz
    · intro hz
      have hzA : (z : V ≃ₗ[F] V) ∈ τ.range := hτrange.symm ▸ ⟨z, hz, rfl⟩
      obtain ⟨f, hf⟩ := hzA
      exact ⟨f, Subtype.ext hf⟩
  have hnormΩ : ∀ g : ↥(orthDerived Q), (∀ a ∈ E, g * a * g⁻¹ ∈ E) →
      ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * τΩ f * g⁻¹ = τΩ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
    intro g hg
    obtain ⟨π, ε, hε, hact⟩ := hnorm g (by
      rintro a ⟨z, hz, rfl⟩
      exact ⟨g * z * g⁻¹, hg z hz, rfl⟩)
    exact ⟨π, ε, hε, fun f f' h i => hact f f' (congrArg Subtype.val h) i⟩
  refine ⟨τΩ, hτΩinj, hτΩrange, hnormΩ, ?_⟩
  exact exists_coxeterB_three_automizer_of_torus hp hp2 E τΩ hτΩinj hτΩrange
    (fun i => by
      obtain ⟨w, hw, hact⟩ := hsgn i
      exact ⟨⟨w, hw⟩, fun f => Subtype.ext (hact f)⟩)
    (fun σ => by
      obtain ⟨w, hw, hact⟩ := hperm σ
      exact ⟨⟨w, hw⟩, fun f => Subtype.ext (hact f)⟩) hnormΩ

end OmPlusFrame

section Original

theorem ggF4Plus_original_b3_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hmark : GGCentralImage .POmegaMinus 4 f L) :
    ∃ ε : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, GGIsReflection p (ε ((CoxeterMatrix.B 3).simple i) : MulAut ↥Bs) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hBs, -, -, -⟩ := hc.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ 1 :=
      (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hpq
    omega
  obtain ⟨ψ, hker, hrange, ℓ, hℓ, -, hpow, hrank⟩ :=
    F4KGPosition.exists_spinMinus_lifts_of_f4_member ggInnerDiagMpInput_holds hcfg
      (Or.inl rfl) hmark
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 f :=
    ⟨Nat.prime_two, by omega, by change 4 ≤ 4; exact le_rfl⟩
  have hrk : 2 ≤ (ggU .POmegaMinus 4 f).D.rank :=
    two_le_lieUniversal_rank .POmegaMinus 4 2 f Nat.prime_two hadm (by decide)
  have hBL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    (ggF4QGeFour_localMap_of_mp ggInnerDiagMpInput_holds hcfg (Or.inl rfl)
      ψ hadm hrk hker hrange).1
  let Q := CFSG.LieType.Universal.Spin.quadMinus 4 (GaloisField 2 f)
    (CFSG.LieType.Universal.minusCoeffs 2 f).1 (CFSG.LieType.Universal.minusCoeffs 2 f).2
  let ψn : ↥(spinGroup Q) →* G := ψ
  let ℓn : ↥Bs →* ↥(spinGroup Q) := ℓ
  have hirr := CFSG.LieType.Universal.minusCoeffs_irr 2 f
  have hZS : Subgroup.center ↥(spinGroup Q) = ⊥ :=
    CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
      (F := GaloisField 2 f) (by decide : 4 ≤ 4) hirr
  have hψn : Function.Injective ψn := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZS.le
  let ι := CFSG.LieType.Universal.Spin.spinEquivCommutatorQuadMinus (n := 4) le_rfl hirr
    (CharTwo.two_eq_zero (R := GaloisField 2 f))
  let ψΩ : ↥(orthDerived Q) →* G := ψn.comp ι.symm.toMonoidHom
  let ℓΩ : ↥Bs →* ↥(orthDerived Q) := ι.toMonoidHom.comp ℓn
  have hψΩ : Function.Injective ψΩ := hψn.comp ι.symm.injective
  have hrangeΩ : ψΩ.range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.symm.surjective,
      ← MonoidHom.range_eq_map]
    exact hrange
  have hcompatΩ : ∀ (b : ↥Bs) (z : ↥(orthDerived Q)),
      (b : G)⁻¹ * ψΩ z * (b : G) = ψΩ (ℓΩ b * z * (ℓΩ b)⁻¹) := by
    intro b z
    have h1 : ι.symm (ℓΩ b * z * (ℓΩ b)⁻¹) = ℓn b * ι.symm z * (ℓn b)⁻¹ := by
      simp only [ℓΩ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
        MulEquiv.symm_apply_apply]
    change (b : G)⁻¹ * ψn (ι.symm z) * b = ψn (ι.symm (ℓΩ b * z * (ℓΩ b)⁻¹))
    rw [h1]
    exact hℓ b (ι.symm z)
  have hZΩ : Subgroup.center ↥(orthDerived Q) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : ι.symm z ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply ι.injective
      rw [map_mul, map_mul, ι.apply_symm_apply]
      exact hz (ι g)
    rw [hZS, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← ι.apply_symm_apply z, hz', map_one]
  have hpowΩ : ∀ b : ↥Bs, ℓΩ b ^ p = 1 := by
    intro b
    have hpow' : ℓn b ^ p = 1 := hpow b
    change (ι (ℓn b)) ^ p = 1
    rw [← map_pow, hpow', map_one]
  have hEcomm : ∀ a ∈ ℓΩ.range, ∀ b ∈ ℓΩ.range, a * b = b * a := by
    rintro a ⟨u, rfl⟩ b ⟨v, rfl⟩
    rw [← map_mul, ← map_mul, hBs.1.is_comm.comm u v]
  have hE : IsElemAbelian p ℓΩ.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hEcomm a a.2 b b.2)⟩⟩, ?_⟩
    rintro a ⟨b, rfl⟩
    exact hpowΩ b
  have hrankΩ : p ^ 3 ≤ Nat.card ℓΩ.range := by
    have hR : ℓΩ.range = ℓn.range.map ι.toMonoidHom := MonoidHom.range_comp _ _
    rw [hR, Subgroup.card_map_of_injective ι.injective]
    exact hrank
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.RankThree.PartOne.S15K.polar_nondegenerate_quadMinus hirr
  have hdim : finrank (GaloisField 2 f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
    CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by omega) hirr
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpqF : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hF]; exact hpq
  have hsc : ∀ z : ↥(orthDerived Q), (∀ a ∈ ℓΩ.range, z * a = a * z) →
      z ^ p = 1 → z ∈ ℓΩ.range := fun z hz hzp =>
    mem_range_inner_lift_of_pow_eq_one_of_commute hc.2.1.2.2.2 ψΩ hψΩ hZΩ ℓΩ hcompatΩ hzp hz
  obtain ⟨-, -, -, -, ε, hε⟩ :=
    OmPlusFrame.exists_b3_torus_automizer hQ hdim hminus hp hp2 hpqF ℓΩ.range hE hrankΩ hsc
  exact exists_coxeterB_three_automizer_of_inner_lift hp hp2 hBs hc.2.1.2.2.2 hBL
    ψΩ hψΩ hrangeΩ hZΩ ℓΩ hcompatΩ ε hε

theorem ggF4OriginalRankOneFamily_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGCentralImage .POmegaMinus 4 f L) :
    GGOriginalRankOneFamily p L (L ⊔ K) Bs (ggCoxRefl CoxeterMatrix.F₄ e) := by
  have hc : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hBs, hx, -, -⟩ := hc.tableB_facts
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ 1 :=
      (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hpq
    omega
  obtain ⟨ε, hε⟩ := ggF4Plus_original_b3_of_cfg hcfg hf hpq hmark
  have hBL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    hc.bstar_le_normalizer (ggLNoncyclicInput_holds G p B x L hc.1)
  have hL : CFSG.Assembly.IsSubnormal L (Subgroup.centralizer ({x} : Set G)) :=
    hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1
  have hAH : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  exact ggOriginalRankOneFamily_of_b3 hp hp2 hBs hcfg.1.2.2.2.1 hx hL hBL le_sup_left
    hAH hpres le_sup_left ε hε (Equiv.refl _) (fun _ _ => rfl)
    (fun r hrL hr => (ggOppPlus_rankOne_of_cfg hcfg hf hpq hmark hrL hr).1)

end Original

end CFSG.StandardType

end
