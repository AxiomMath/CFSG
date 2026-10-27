module

public import CFSG.Quasithin.Background.C35InspD4A
public import CFSG.Quasithin.Background.C35InspBase
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4Perf
public import CFSG.Quasithin.H13.NQCatD4Irred
public import CFSG.Quasithin.Background.SmithB42D4Main
public import CFSG.LieType.Chevalley.GraphFixedBorelOvergroups
public import CFSG.LieType.Chevalley.GraphFixedParabolicCells
public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer
public import CFSG.LieType.Chevalley.GraphFixedRootBruhat
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListTits
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsCycle
public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Walter.Cited.PSL2Small

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique Matrix CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

section D4

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

include hσ3 in
theorem fivesix_inj
    {e f e' f' : ↥(trialityFixedField K τ₀)}
    (h : ox₅ σ e * ox₆ σ f = ox₅ σ e' * ox₆ σ f') : e = e' ∧ f = f' := by
  have h1 : ox₅ σ (e + e') * ox₆ σ (f + f') = 1 := by
    rw [ox₅_add σ hσ3, ox₆_add σ hσ3]
    have e1 : ox₅ σ e * ox₅ σ e' * (ox₆ σ f * ox₆ σ f') =
        (ox₅ σ e * ox₆ σ f) * (ox₅ σ e' * ox₆ σ f') := by
      rw [show ox₅ σ e * ox₅ σ e' * (ox₆ σ f * ox₆ σ f') =
        ox₅ σ e * (ox₅ σ e' * ox₆ σ f) * ox₆ σ f' by group, (comm56 σ hσ3 e' f).eq]
      group
    have hsq5 : ox₅ σ e' * ox₅ σ e' = 1 := by
      rw [← ox₅_add σ hσ3, CharTwo.add_self_eq_zero, ox₅_zero σ hσ3]
    have hsq6 : ox₆ σ f' * ox₆ σ f' = 1 := by
      rw [← ox₆_add σ hσ3, CharTwo.add_self_eq_zero, ox₆_zero σ hσ3]
    rw [e1, h, show ox₅ σ e' * ox₆ σ f' * (ox₅ σ e' * ox₆ σ f') =
      ox₅ σ e' * (ox₆ σ f' * ox₅ σ e') * ox₆ σ f' by group, ← (comm56 σ hσ3 e' f').eq,
      show ox₅ σ e' * (ox₅ σ e' * ox₆ σ f') * ox₆ σ f' =
        (ox₅ σ e' * ox₅ σ e') * (ox₆ σ f' * ox₆ σ f') by group, hsq5, hsq6, one_mul]
  obtain ⟨he, hf⟩ := five_six_eq_one σ hσ3 h1
  exact ⟨(add_eq_zero_iff_eq_neg.mp he).trans (CharTwo.neg_eq _),
    (add_eq_zero_iff_eq_neg.mp hf).trans (CharTwo.neg_eq _)⟩

@[expose] noncomputable def coord56
    (z : GL) : Fin 2 → ↥(orbitField TwistTag.D4 K τ₀ fa1) :=
  open Classical in
  if h : ∃ w : Fin 2 → ↥(orbitField TwistTag.D4 K τ₀ fa1),
      z = ox₅ σ (toK σ (w 1)) * ox₆ σ (toK σ (w 0)) then h.choose else 0

include hσ3 in
theorem coord56_eq
    (w : Fin 2 → ↥(orbitField TwistTag.D4 K τ₀ fa1)) :
    coord56 σ (ox₅ σ (toK σ (w 1)) * ox₆ σ (toK σ (w 0))) = w := by
  have h : ∃ w' : Fin 2 → ↥(orbitField TwistTag.D4 K τ₀ fa1),
      ox₅ σ (toK σ (w 1)) * ox₆ σ (toK σ (w 0)) = ox₅ σ (toK σ (w' 1)) * ox₆ σ (toK σ (w' 0)) :=
    ⟨w, rfl⟩
  rw [coord56, dite_eq_left h]
  obtain ⟨h1, h0⟩ := fivesix_inj σ hσ3 h.choose_spec
  ext i
  fin_cases i
  · exact (congrArg Subtype.val h0).symm
  · exact (congrArg Subtype.val h1).symm

end D4

theorem d4_holds_base :
    ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Base K Y M₀ V →
      ∀ f : ℕ, 1 ≤ f → Is3D4 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V := by
  intro A _ _ K Y M₀ V hD f hf1 hX
  classical
  have hX' := hX
  obtain ⟨-, F, _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have : CharP F 2 := CFSG.Quasithin.B42D4.charP_two_of_card hf1 hcard
  have hσ3 : σ.toRingHom ^ 3 = 1 := CFSG.Quasithin.B42D4.sigma_cube hcard σ hσ
  have hkcard : Nat.card ↥(trialityFixedField F σ.toRingHom) = 2 ^ f :=
    CFSG.Quasithin.B42D4.card_fixedField hf1 hcard σ hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 3
  set C := graphFixedRootGroup TwistTag.D4 F σ.toRingHom with hCdef
  let φ : ↥K →* ↥C := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφker : φ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    exact ⟨k, hx⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 F 2 σ w₀ hw₀).1
  have hU₀ : IsSylowTwoOf ((graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf C) ⊤ :=
    hPU ▸ isSylowTwoOf_top_of_sylow PU
  obtain ⟨g, hNY, hne, hns⟩ := hD.exists_conj_normalizer φ hφker.le hφs hU₀
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hθ
  have hθker : θ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hφker]
  set θ' : ↥K →* ModGL TwistTag.D4.tag F := C.subtype.comp θ with hθ'
  have hθ'ker : θ'.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hθ', MonoidHom.comp_apply, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one, ← MonoidHom.mem_ker, hθker]
  have hYK : Y ≤ K := hD.parabolic.1
  have hM₀K : M₀ ≤ K := hD.eq_perfectCore ▸ (perfectCore_le Y).trans hYK
  have hZY : centerOf K ≤ Y := hD.center_le.trans (Subgroup.map_subtype_le _)
  have hmapY : img θ' Y = (img θ Y).map C.subtype := by
    rw [img, img, Subgroup.map_map]
  obtain ⟨-, -, -, -, -, -, hBN, -⟩ := fixed_Borel_self_normalizers TwistTag.D4 F σ w₀ hw₀
  have hBC : graphFixedRootBorel TwistTag.D4 F σ.toRingHom ≤ C := hBN ▸ inf_le_left
  have hB : graphFixedRootBorel TwistTag.D4 F σ.toRingHom ≤ img θ' Y := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer
        (graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom : Set (ModGL TwistTag.D4.tag F)) := by
      rw [← hBN] at hb
      exact hb.2
    have hbN' : (⟨b, hBC hb⟩ : ↥C) ∈ Subgroup.normalizer
        (((graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom).subgroupOf C : Subgroup ↥C) :
          Set ↥C) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 hbN u).trans Iff.rfl
    rw [hmapY]
    exact ⟨⟨b, hBC hb⟩, hNY hbN', rfl⟩
  have hYC : img θ' Y ≤ C := by
    rw [hmapY]
    exact Subgroup.map_subtype_le _
  have hcl := fixed_Borel_overgroup_classification TwistTag.D4 F σ
  obtain ⟨-, -, hmemP, -, hP0, hPuniv⟩ := fixed_standard_parabolic_cells TwistTag.D4 F σ
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = fa0 ∨ a = fa1 := by decide
  have hYa : ∃ a : Fin TwistTag.D4.foldedTag.rank,
      img θ' Y = graphFixedParabolic TwistTag.D4 F σ.toRingHom {a} := by
    have hJ := (hcl _ hB hYC).1
    set J := {a | canonicalRep (coxeterSystem TwistTag.D4.tag) F (TwistTag.D4.orbitReflection a) ∈
      img θ' Y} with hJdef
    by_cases h0 : fa0 ∈ J <;> by_cases h1 : fa1 ∈ J
    · exfalso
      apply hne
      have hJu : J = Set.univ := by
        ext a
        simp only [Set.mem_univ, iff_true]
        rcases hcases a with rfl | rfl
        · exact h0
        · exact h1
      rw [hJu, hPuniv] at hJ
      rw [eq_top_iff]
      intro x _
      have hx : (x : ModGL TwistTag.D4.tag F) ∈ img θ' Y := by rw [hJ]; exact x.2
      rw [hmapY] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [← Subtype.ext hyx]
      exact hy
    · refine ⟨fa0, ?_⟩
      rw [hJ]
      congr 1
      ext a
      rcases hcases a with rfl | rfl
      · simpa using h0
      · simp only [Set.mem_singleton_iff]
        exact ⟨fun h => absurd h h1, fun h => absurd h (by decide)⟩
    · refine ⟨fa1, ?_⟩
      rw [hJ]
      congr 1
      ext a
      rcases hcases a with rfl | rfl
      · simp only [Set.mem_singleton_iff]
        exact ⟨fun h => absurd h h0, fun h => absurd h (by decide)⟩
      · simpa using h1
    · exfalso
      apply hns
      have hJe : J = ∅ := by
        ext a
        simp only [Set.mem_empty_iff_false, iff_false]
        rcases hcases a with rfl | rfl
        · exact h0
        · exact h1
      rw [hJe, hP0] at hJ
      have hsolv : Group.IsSolvable ↥(img θ' Y) := by
        rw [hJ]
        exact isSolvable_graphFixedRootBorel (t := TwistTag.D4) (K := F) (σ := σ.toRingHom)
          σ.surjective
      rw [hmapY] at hsolv
      exact Group.isSolvable_of_isSolvable_injective
        (f := ((img θ Y).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom)
        ((img θ Y).equivMapOfInjective C.subtype C.subtype_injective).injective
  obtain ⟨a, ha⟩ := hYa
  have hMa : img θ' M₀ = perfectCore (graphFixedParabolic TwistTag.D4 F σ.toRingHom {a}) := by
    rw [hD.eq_perfectCore, img_perfectCore θ' hYK, ha]
  have hne' : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      ({a} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ := fun a => by
    rcases hcases a with rfl | rfl
    · exact singleton_ne_univ_fa0
    · exact singleton_ne_univ_fa1
  obtain ⟨hQP, hPN, hQ2, -⟩ := library_facts σ a (hne' a)
  have hVK : V ≤ K := hD.V_le.trans hM₀K
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hD.V_elem.2 x x.2)⟩
  have hOQ : pCoreOf 2 (perfectCore (graphFixedParabolic TwistTag.D4 F σ.toRingHom {a})) ≤
      graphFixedParabolicRadical TwistTag.D4 F σ.toRingHom {a} := by
    have hF : Vol2Native.L239.Lie.ParabolicFacts (graphFixedParabolic TwistTag.D4 F σ.toRingHom {a})
        (graphFixedParabolicRadical TwistTag.D4 F σ.toRingHom {a}) := by
      rcases hcases a with rfl | rfl
      · exact parabolicFacts_a0 σ hσ3 hK4
      · exact parabolicFacts_a1 σ hσ3
    by_cases h0 : pCoreOf 2 (perfectCore (graphFixedParabolic TwistTag.D4 F σ.toRingHom {a})) = ⊥
    · rw [h0]
      exact bot_le
    · exact (H13.NQCat.D4Irred.pCoreOf_eq_of_parabolicFacts hF h0).le
  have hVQ : ∀ v (hv : v ∈ V), θ' ⟨v, hVK hv⟩ ∈
      graphFixedParabolicRadical TwistTag.D4 F σ.toRingHom {a} := by
    intro v hv
    have h := img_le_pCoreOf θ' hD.V_le (le_normalizer_of_comm hD.V_comm) hV2 hVK
      ⟨⟨v, hVK hv⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
    rw [hMa] at h
    exact hOQ h
  have hVC : ∀ v (hv : v ∈ V), θ' ⟨v, hVK hv⟩ ∈ Subgroup.centralizer
      (graphFixedParabolicRadical TwistTag.D4 F σ.toRingHom {a} :
        Set (ModGL TwistTag.D4.tag F)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rcases hcases a with rfl | rfl
    · have hQM : Q0 σ ≤ img θ' M₀ := by
        rw [hMa]
        exact CFSG.Quasithin.H13.Sec53F.TriD4.Q0_le_perfectCore σ hσ3 hK4
      have hQn : img θ' M₀ ≤ Subgroup.normalizer (Q0 σ : Set (ModGL TwistTag.D4.tag F)) := by
        rw [hMa]
        exact (perfectCore_le (P0 σ)).trans hPN
      exact hD.comm_of_pCore θ' hθ'ker.le hQM hQn hQ2 hv (hVK hv) hq
    · by_cases hf1 : f = 1
      · have hU := isPGroup_posUnipotent σ hσ3
        have hE : Nat.card ↥(orbitField TwistTag.D4 F σ.toRingHom fa1) = 2 ^ f := by
          rw [orbitField_fa1_eq σ]
          exact hkcard
        have h0 := perfectCore_bot_of_card_two σ fa1 hU (by rw [hE, hf1]; norm_num)
        have hv1 : θ' ⟨v, hVK hv⟩ = 1 := by
          have hmem : θ' ⟨v, hVK hv⟩ ∈ img θ' M₀ :=
            ⟨⟨v, hVK hv⟩, Subgroup.mem_subgroupOf.2 (hD.V_le hv), rfl⟩
          rw [hMa, h0, Subgroup.mem_bot] at hmem
          exact hmem
        rw [hv1]
        exact (mul_one q).trans (one_mul q).symm
      · have hf2 : 2 ≤ f := by omega
        have hk4 : 4 ≤ Nat.card ↥(trialityFixedField F σ.toRingHom) := by
          rw [hkcard]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        have hQM : Q1 σ ≤ img θ' M₀ := by
          rw [hMa]
          exact CFSG.Quasithin.H13.Sec53F.TriD4.Q1_le_perfectCore σ hσ3 hk4
        have hQn : img θ' M₀ ≤ Subgroup.normalizer (Q1 σ : Set (ModGL TwistTag.D4.tag F)) := by
          rw [hMa]
          exact (perfectCore_le (P1 σ)).trans hPN
        exact hD.comm_of_pCore θ' hθ'ker.le hQM hQn hQ2 hv (hVK hv) hq
  have hVZ' : ¬ V ≤ centerOf K := by
    intro h
    apply hD.V_ne
    rw [← hD.V_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact Subgroup.mem_centralizer_iff.1 (h hv).2 m (hM₀K hm)
  rcases hcases a with rfl | rfl
  ·
    exfalso
    apply hVZ'
    rw [← hD.V_comm, Subgroup.commutator_le]
    intro v hv m hm
    have hmP : θ' ⟨m, hM₀K hm⟩ ∈ perfectCore (P0 σ) := by
      rw [← hMa]
      exact ⟨⟨m, hM₀K hm⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.1
      (H13.NQCat.D4Irred.perfectCore_le_centralizer σ hσ3 hmP) _ ⟨hVQ v hv, hVC v hv⟩
    have h1 : ⁅(⟨v, hVK hv⟩ : ↥K), ⟨m, hM₀K hm⟩⁆ ∈ θ'.ker := by
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        hc]
      group
    rw [hθ'ker] at h1
    exact mem_centerOf_iff.2 h1
  ·
    have hE : Nat.card ↥(orbitField TwistTag.D4 F σ.toRingHom fa1) = 2 ^ f := by
      rw [orbitField_fa1_eq σ]
      exact hkcard
    have hU := isPGroup_posUnipotent σ hσ3
    by_cases hf2 : f = 1
    ·
      exfalso
      subst hf2
      have h0 := perfectCore_bot_of_card_two σ fa1 hU (by rw [hE]; rfl)
      apply hD.ne_bot
      rw [eq_bot_iff]
      intro m hm
      have hm1 : θ' ⟨m, hM₀K hm⟩ = 1 := by
        have : θ' ⟨m, hM₀K hm⟩ ∈ img θ' M₀ := ⟨⟨m, hM₀K hm⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
        rw [hMa, h0, Subgroup.mem_bot] at this
        exact this
      have hmZ : m ∈ centerOf K := by
        have : (⟨m, hM₀K hm⟩ : ↥K) ∈ θ'.ker := hm1
        rw [hθ'ker] at this
        exact mem_centerOf_iff.2 this
      have hM₀Z : M₀ ≤ centerOf K := fun x hx => by
        have : θ' ⟨x, hM₀K hx⟩ = 1 := by
          have h' : θ' ⟨x, hM₀K hx⟩ ∈ img θ' M₀ := ⟨⟨x, hM₀K hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
          rw [hMa, h0, Subgroup.mem_bot] at h'
          exact h'
        have h'' : (⟨x, hM₀K hx⟩ : ↥K) ∈ θ'.ker := this
        rw [hθ'ker] at h''
        exact mem_centerOf_iff.2 h''
      have hperf : ⁅M₀, M₀⁆ = M₀ := hD.eq_perfectCore ▸ perfectCore_perfect Y
      have hab : ⁅M₀, M₀⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_iff.1 (hM₀Z hx).2 y (hM₀K hy)
      rw [← hperf, hab] at hm
      exact hm
    have hf2' : 2 ≤ f := by omega
    have hE4' : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 F σ.toRingHom fa1) := by
      rw [hE]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2'
    have hE4 : ∃ s : Finset ↥(orbitField TwistTag.D4 F σ.toRingHom fa1), s.card = 4 :=
      exists_finset_card_four hE4'
    have : CharP ↥(orbitField TwistTag.D4 F σ.toRingHom fa1) 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hf1 hE
    have := sl2_isSimple hE4
    obtain ⟨R, hRu, hRW, hRinj, lam, hlams, hlamdec⟩ := levi_proj_d4 σ fa1 hU hE4
    have hVa : graphFixedSimpleComplement TwistTag.D4 F σ.toRingHom fa1 = Q1 σ :=
      (radical_eq_simpleComplement σ.toRingHom fa1 supp_fa1).symm
    let eL : ↥R.range ≃* SL2 ↥(orbitField TwistTag.D4 F σ.toRingHom fa1) :=
      (MonoidHom.ofInjective hRinj).symm
    have heL : ∀ l : ↥R.range, R (eL l) = (l : ModGL TwistTag.D4.tag F) := fun l =>
      congrArg Subtype.val ((MonoidHom.ofInjective hRinj).apply_symm_apply l)
    have hinj : Set.InjOn (MonoidHom.id (ModGL TwistTag.D4.tag F))
        (perfectCore (P1 σ) : Set (ModGL TwistTag.D4.tag F)) := fun _ _ _ _ h => h
    have hMN : img θ' M₀ = (perfectCore (P1 σ)).map (MonoidHom.id (ModGL TwistTag.D4.tag F)) := by
      rw [Subgroup.map_id]
      exact hMa
    set ν := liftHom hM₀K θ' (MonoidHom.id (ModGL TwistTag.D4.tag F)) (perfectCore (P1 σ)) hinj
      hMN with hν
    have hνs := liftHom_surjective hM₀K θ' (MonoidHom.id (ModGL TwistTag.D4.tag F))
      (perfectCore (P1 σ)) hinj hMN
    have hνspec : ∀ x : ↥M₀, ((ν x : ↥(perfectCore (P1 σ))) : ModGL TwistTag.D4.tag F) =
        θ' ⟨x, hM₀K x.2⟩ := fun x =>
      liftHom_spec hM₀K θ' (MonoidHom.id (ModGL TwistTag.D4.tag F)) (perfectCore (P1 σ)) hinj
        hMN x
    have hν1 : ∀ x : ↥M₀, ν x = 1 ↔ (x : A) ∈ centerOf K := by
      intro x
      rw [hν, liftHom_eq_one_iff, ← MonoidHom.mem_ker, hθ'ker]
      exact mem_centerOf_iff.symm
    let α : ↥M₀ →* SL2 ↥(orbitField TwistTag.D4 F σ.toRingHom fa1) :=
      eL.toMonoidHom.comp (lam.comp ν)
    have hαs : Function.Surjective α := eL.surjective.comp (hlams.comp hνs)
    have hαρ : ∀ x : ↥M₀, R (α x) = ((lam (ν x) : ↥R.range) : ModGL TwistTag.D4.tag F) :=
      fun x => heL _
    have hαker : IsPGroup 2 α.ker := by
      rintro ⟨x, hx⟩
      have h1 : lam (ν x) = 1 := (MulEquiv.map_eq_one_iff eL).mp hx
      have hq := hlamdec (ν x)
      rw [h1, OneMemClass.coe_one, inv_one, one_mul, hVa] at hq
      obtain ⟨k, hk⟩ := hQ2 ⟨_, hq⟩
      have hk2 : ((ν x : ↥(perfectCore (P1 σ))) : ModGL TwistTag.D4.tag F) ^ 2 ^ k = 1 :=
        (SubgroupClass.coe_pow _ _).symm.trans (congrArg Subtype.val hk)
      have hk' : ν (x ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact Subtype.ext ((SubgroupClass.coe_pow _ _).trans hk2)
      have hxZ : (⟨((x ^ 2 ^ k : ↥M₀) : A), hM₀K (x ^ 2 ^ k).2⟩ : ↥K) ∈ Subgroup.center ↥K :=
        mem_centerOf_iff.1 ((hν1 _).1 hk')
      obtain ⟨l, hl⟩ := isPGroup_center hD.center ⟨_, hxZ⟩
      refine ⟨k + l, Subtype.ext (Subtype.ext ?_)⟩
      have hl' := congrArg (fun z : ↥(Subgroup.center ↥K) => ((z : ↥K) : A)) hl
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hl'
      show (x : A) ^ 2 ^ (k + l) = 1
      rw [pow_add, pow_mul]
      exact hl'
    have hO : CFSG.pCore 2 ↥M₀ = α.ker := pCore_two_eq_ker (sl2_nonabelian hE4) α hαs hαker
    let c : ↥V → (Fin 2 → ↥(orbitField TwistTag.D4 F σ.toRingHom fa1)) := fun v =>
      coord56 σ (θ' ⟨v, hVK v.2⟩)
    have hcoord : ∀ v : ↥V, θ' ⟨v, hVK v.2⟩ = ox₅ σ (toK σ (c v 1)) * ox₆ σ (toK σ (c v 0)) := by
      intro v
      obtain ⟨e', f', hef⟩ := centerQ1_d4 σ hσ3 (hVQ v v.2) (hVC v v.2)
      have hmem : ∀ x : ↥(trialityFixedField F σ.toRingHom),
          (x : F) ∈ orbitField TwistTag.D4 F σ.toRingHom fa1 := fun x => by
        rw [orbitField_fa1_eq σ]
        exact x.2
      have h : θ' ⟨v, hVK v.2⟩ = ox₅ σ (toK σ ((![⟨f', hmem f'⟩, ⟨e', hmem e'⟩] :
          Fin 2 → ↥(orbitField TwistTag.D4 F σ.toRingHom fa1)) 1)) *
          ox₆ σ (toK σ ((![⟨f', hmem f'⟩, ⟨e', hmem e'⟩] :
            Fin 2 → ↥(orbitField TwistTag.D4 F σ.toRingHom fa1)) 0)) := by
        rw [hef]
        rfl
      show θ' ⟨v, hVK v.2⟩ = ox₅ σ (toK σ (coord56 σ (θ' ⟨v, hVK v.2⟩) 1)) *
        ox₆ σ (toK σ (coord56 σ (θ' ⟨v, hVK v.2⟩) 0))
      rw [h, coord56_eq σ hσ3]
    have hone : (1 : ModGL TwistTag.D4.tag F) =
        ox₅ σ (toK σ ((0 : Fin 2 → ↥(orbitField TwistTag.D4 F σ.toRingHom fa1)) 1)) *
          ox₆ σ (toK σ ((0 : Fin 2 → ↥(orbitField TwistTag.D4 F σ.toRingHom fa1)) 0)) := by
      have h0 : toK σ (0 : ↥(orbitField TwistTag.D4 F σ.toRingHom fa1)) = 0 := rfl
      rw [Pi.zero_apply, Pi.zero_apply, h0, ox₅_zero σ hσ3, ox₆_zero σ hσ3, one_mul]
    have htoK_add : ∀ x y : ↥(orbitField TwistTag.D4 F σ.toRingHom fa1),
        toK σ (x + y) = toK σ x + toK σ y := fun _ _ => rfl
    have hcmul : ∀ u v : ↥V, c (u * v) = c u + c v := by
      intro u v
      have h1 : θ' ⟨((u * v : ↥V) : A), hVK (u * v).2⟩ =
          ox₅ σ (toK σ ((c u + c v) 1)) * ox₆ σ (toK σ ((c u + c v) 0)) := by
        rw [show (⟨((u * v : ↥V) : A), hVK (u * v).2⟩ : ↥K) = ⟨u, hVK u.2⟩ * ⟨v, hVK v.2⟩ from rfl,
          map_mul, hcoord u, hcoord v, Pi.add_apply, Pi.add_apply, htoK_add, htoK_add,
          ox₅_add σ hσ3, ox₆_add σ hσ3,
          show ox₅ σ (toK σ (c u 1)) * ox₆ σ (toK σ (c u 0)) *
              (ox₅ σ (toK σ (c v 1)) * ox₆ σ (toK σ (c v 0))) =
            ox₅ σ (toK σ (c u 1)) * (ox₆ σ (toK σ (c u 0)) * ox₅ σ (toK σ (c v 1))) *
              ox₆ σ (toK σ (c v 0)) by group,
          ← (comm56 σ hσ3 (toK σ (c v 1)) (toK σ (c u 0))).eq]
        group
      show coord56 σ _ = _
      rw [h1, coord56_eq σ hσ3]
    let β : ↥V →* Multiplicative (Fin 2 → ↥(orbitField TwistTag.D4 F σ.toRingHom fa1)) :=
      { toFun := fun v => Multiplicative.ofAdd (c v)
        map_one' := by
          show Multiplicative.ofAdd (coord56 σ (θ' 1)) = 1
          rw [map_one, hone, coord56_eq σ hσ3]
          rfl
        map_mul' := fun u v => by
          show Multiplicative.ofAdd (c (u * v)) =
            Multiplicative.ofAdd (c u) * Multiplicative.ofAdd (c v)
          rw [hcmul]
          rfl }
    have hMV := le_normalizer_of_comm hD.V_comm
    have hVZ : ¬ V ≤ V ⊓ centerOf K := fun h => hVZ' fun v hv => (h hv).2
    have hβker : β.ker = (V ⊓ centerOf K).subgroupOf V := by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show Multiplicative.ofAdd (c v) = 1 ↔ _
      constructor
      · intro h0
        have hc0 : c v = 0 := h0
        have h1 : (⟨v, hVK v.2⟩ : ↥K) ∈ θ'.ker := by
          rw [MonoidHom.mem_ker, hcoord v, hc0, ← hone]
        rw [hθ'ker] at h1
        exact ⟨v.2, mem_centerOf_iff.2 h1⟩
      · rintro ⟨-, hvZ⟩
        have h1 : θ' ⟨v, hVK v.2⟩ = 1 := by
          rw [← MonoidHom.mem_ker, hθ'ker]
          exact mem_centerOf_iff.1 hvZ
        show Multiplicative.ofAdd (coord56 σ (θ' ⟨v, hVK v.2⟩)) = 1
        rw [h1, hone, coord56_eq σ hσ3]
        rfl
    have hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
        Multiplicative.toAdd (β v) =
          ((α a : SL2 ↥(orbitField TwistTag.D4 F σ.toRingHom fa1)) :
            Matrix (Fin 2) (Fin 2) ↥(orbitField TwistTag.D4 F σ.toRingHom fa1)) *ᵥ
            Multiplicative.toAdd (β u) := by
      intro a u v huv
      show c v = _ *ᵥ c u
      have hv : θ' ⟨v, hVK v.2⟩ =
          θ' ⟨a, hM₀K a.2⟩ * θ' ⟨u, hVK u.2⟩ * (θ' ⟨a, hM₀K a.2⟩)⁻¹ := by
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
        exact Subtype.ext huv
      set q : ModGL TwistTag.D4.tag F := ((lam (ν a) : ↥R.range) : ModGL TwistTag.D4.tag F)⁻¹ *
        ((ν a : ↥(perfectCore (P1 σ))) : ModGL TwistTag.D4.tag F) with hqdef
      have hq : q ∈ Q1 σ := by
        have := hlamdec (ν a)
        rw [hVa] at this
        exact this
      have hqc := Subgroup.mem_centralizer_iff.1 (hVC u u.2) _ hq
      have ha' : θ' ⟨a, hM₀K a.2⟩ = R (α a) * q := by
        rw [hqdef, hαρ, ← hνspec]
        group
      have hv' : θ' ⟨v, hVK v.2⟩ = R (α a) * θ' ⟨u, hVK u.2⟩ * (R (α a))⁻¹ := by
        rw [hv, ha']
        calc R (α a) * q * θ' ⟨u, hVK u.2⟩ * (R (α a) * q)⁻¹ =
              R (α a) * (q * θ' ⟨u, hVK u.2⟩) * q⁻¹ * (R (α a))⁻¹ := by group
          _ = _ := by
            rw [hqc]
            group
      rw [hcoord u, d4_action σ hσ3 R hRu hRW (α a) (c u)] at hv'
      show coord56 σ (θ' ⟨v, hVK v.2⟩) = _
      rw [hv', coord56_eq σ hσ3]
    have hnat := isNaturalSection_of_equiv hMV hVZ α hαs hO.symm β hβker hequiv
    have hco : IsCoatom (img θ Y) := by
      refine ⟨hne, fun M' hM' => ?_⟩
      have hM'B : img θ' Y ≤ M'.map C.subtype := by
        rw [hmapY]
        exact Subgroup.map_mono hM'.le
      have hM'C : M'.map C.subtype ≤ C := Subgroup.map_subtype_le _
      have hJ := (hcl _ (hB.trans hM'B) hM'C).1
      set J' := {b | canonicalRep (coxeterSystem TwistTag.D4.tag) F
        (TwistTag.D4.orbitReflection b) ∈ M'.map C.subtype} with hJ'
      have h1 : fa1 ∈ J' := by
        show canonicalRep _ _ _ ∈ M'.map C.subtype
        apply hM'B
        rw [ha]
        exact (hmemP {fa1} fa1).2 rfl
      by_cases h0 : fa0 ∈ J'
      · have hJu : J' = Set.univ := by
          ext b
          simp only [Set.mem_univ, iff_true]
          rcases hcases b with rfl | rfl
          · exact h0
          · exact h1
        rw [hJu, hPuniv] at hJ
        rw [eq_top_iff]
        intro x _
        have hx : (x : ModGL TwistTag.D4.tag F) ∈ M'.map C.subtype := by
          rw [hJ]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        rw [← Subtype.ext hyx]
        exact hy
      · exfalso
        have hJ1 : J' = {fa1} := by
          ext b
          simp only [Set.mem_singleton_iff]
          rcases hcases b with rfl | rfl
          · exact ⟨fun h => absurd h h0, fun h => absurd h (by decide)⟩
          · exact ⟨fun _ => rfl, fun _ => h1⟩
        rw [hJ1, ← ha, hmapY] at hJ
        exact hM'.ne (Subgroup.map_injective C.subtype_injective hJ).symm
    exact ⟨f, Or.inr (Or.inr (Or.inr (Or.inl hX'))),
      isMaxParabolic2_of_coatom θ hθker.le hD.parabolic hD.ne_top hZY hco,
      isPSL2_modO2 hE hf2' α hαs hαker,
      Or.inl ⟨↥(orbitField TwistTag.D4 F σ.toRingHom fa1), inferInstance, Fintype.ofFinite _,
        by rw [Fintype.card_eq_nat_card, hE], hnat⟩⟩

theorem d4_holds :
    ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
      ∀ f : ℕ, 1 ≤ f → Is3D4 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V :=
  fun A _ _ K Y M₀ V hD => d4_holds_base A K Y M₀ V hD.toBase

end CFSG.Quasithin.C35Pf
