module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmRank
public import CFSG.LocalAnalysis.StandardType.GGTBJOmRow
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR5O2
public import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeftGlue
public import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeftD
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
public import CFSG.LocalAnalysis.StandardType.MarkingClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJOrthLeft_rowR5O1_with_fixed_centralizer
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O1 p lab) p Bs L) :
    (GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J) ∧
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ GGTBRowR5O1 p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggO1Row_labelAll_adjoint hp hlab hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r0, m, n, K, _, _, _, b, c, e, hlift, hm, hn, hK,
    hbc, hpq, hIc⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr0, h30⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr0 h30
  have hIc' : ∀ φ ∈ I, MulAut.congr e φ ∈ Set.range (MulAut.conj :
      OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)) := by
    intro φ hφ
    obtain ⟨g, hg⟩ := hIc hφ
    exact ⟨e g, by
      rw [← hg]
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply]⟩
  have hTB' := GGTorusTBGroup.mulEquiv (I' := Set.range (MulAut.conj :
      OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c))) e hIc' hTB
  haveI hCP : CharP K 2 := charP_two_of_card hK
  let ψ₀ : ↥L →* OrthRest.RMinus K m b c := e.toMonoidHom.comp (ggQuotHom θ)
  obtain ⟨r, E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hW⟩ :=
    ggTBJ_om_stdModel hp hp2 hbc hm (by rw [hK]; exact hpq) ψ₀ _ hTB'
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qMinusForm K m b c)).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm m hbc
  have hT : ∃ T : Submodule K (LargeEvenMinusIdx m → K), Module.finrank K T = 3 ∧
      ∀ v ∈ T, TableBOrth.qMinusForm K m b c v = 0 :=
    (OrthTorus.charSum_qMinusForm m hbc).2 hm
  have hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L) :=
    (OrthExc.center_data_omegaMinus hp hp2 hm hbc).2 ↥L ψ₀ hTB'.1 hTB'.2.1 hTB'.2.2.1
  have hcardA : Nat.card ↥(ggGamma L hBsN).range = p ^ r := by
    rw [← Nat.card_congr Θ.toEquiv]
    exact FrameBs.card_zmodFrame p r
  have hr : 2 ≤ r := by
    have h3r : p ^ 3 ≤ p ^ r := by
      have h3 := hTB'.2.2.2.2.2.2.1
      rwa [hcardA] at h3
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h3r
    omega
  exact OrthTorus.ggTBJOrthLeft_fixed_of_cfg_with_fixed_centralizer hcfg hBsN hQ hT hTB'.1 hTB'.2.1 hZc hψσ hΘ
    hWeyl hW hr

theorem ggTBJOrthLeft_rowR5O1
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O1 p lab) p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  exact (ggTBJOrthLeft_rowR5O1_with_fixed_centralizer hH hL).1

theorem ggTBJOrthLeft_center_eq_bot_of_nativeModel
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {n : ℕ}
    (hn : 4 ≤ n) (hK : 4 ≤ Nat.card K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RMinus K (n - 1) b c) :
    Subgroup.center L = ⊥ :=
  OrthTorus.center_eq_bot_of_statedOmegaMinus (n := n) hK (by omega) hbc
    (θ.trans (omegaMinusProjEquiv n b c))

theorem exists_mulEquiv_comp_of_bijective {A B C : Type*} [Group A] [Group B] [Group C]
    (q : A →* B) (hq : Function.Bijective q) (e : B ≃* C) :
    ∃ χ : C ≃* A, ∀ c, q (χ c) = e.symm c := by
  let e0 : A ≃* B := MulEquiv.ofBijective q hq
  refine ⟨(e0.trans e).symm, fun c => ?_⟩
  exact MulEquiv.ofBijective_apply_symm_apply (n := e.symm c) q hq

theorem ggTBJOrthLeft_chi_of_nativeModel
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hperf : commutator ↥L = ⊤)
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {n f p : ℕ}
    (hn : 4 ≤ n) (hf : 2 ≤ f) (hKcard : Nat.card K = 2 ^ f)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* OrthRest.RMinus K (n - 1) b c)
    {E : Subgroup ((LargeEvenMinusIdx (n - 1) → K) ≃ₗ[K]
      (LargeEvenMinusIdx (n - 1) → K))}
    (Δ : OrthTorus.TBJOmData (TableBOrth.qMinusForm K (n - 1) b c) p E (n - 1))
    (hE : E ≤ orthDerived (TableBOrth.qMinusForm K (n - 1) b c))
    {σ : (Fin (n - 1) → Multiplicative (ZMod p)) →* ↥L}
    (hψσ : ∀ w, ggQuotHom θ (σ w) =
      (OrthTorus.rMinusEquiv K (n - 1) b c).symm (Δ.τΩ hE w)) :
    Subgroup.center ↥L = ⊥ ∧
      ∃ χ : ↥(orthDerived (TableBOrth.qMinusForm K (n - 1) b c)) ≃* ↥L,
        (∀ g, ggQuotHom θ (χ g) =
          (OrthTorus.rMinusEquiv K (n - 1) b c).symm g) ∧
        (∀ w, χ (Δ.τΩ hE w) = σ w) := by
  classical
  haveI : Group.IsPerfect ↥L := ⟨hperf⟩
  have hK : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hZL : Subgroup.center ↥L = ⊥ :=
    ggTBJOrthLeft_center_eq_bot_of_nativeModel hn hK hbc θ
  let qL : ↥L →* OrthRest.RMinus K (n - 1) b c := ggQuotHom θ
  have hqLker : qL.ker = ⊥ := by
    change (ggQuotHom θ).ker = ⊥
    rw [ker_ggQuotHom, hZL]
  have hqLinj : Function.Injective qL := (MonoidHom.ker_eq_bot_iff qL).mp hqLker
  let eR : OrthRest.RMinus K (n - 1) b c ≃*
      ↥(orthDerived (TableBOrth.qMinusForm K (n - 1) b c)) :=
    OrthTorus.rMinusEquiv K (n - 1) b c
  obtain ⟨χ, hqLχ⟩ :=
    exists_mulEquiv_comp_of_bijective qL ⟨hqLinj, ggQuotHom_surjective θ⟩ eR
  have hχτ : ∀ w, χ (Δ.τΩ hE w) = σ w := by
    intro w
    exact hqLinj ((hqLχ (Δ.τΩ hE w)).trans (hψσ w).symm)
  exact ⟨hZL, χ, hqLχ, hχτ⟩

theorem ggTBJOrthLeft_chart_of_nativeModel
    {G : Type} [Group G] [Finite G] {L J : Subgroup G}
    (hperf : commutator ↥L = ⊤)
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {n f p : ℕ}
    (hn : 4 ≤ n) (hf : 2 ≤ f) (hKcard : Nat.card K = 2 ^ f)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* OrthRest.RMinus K (n - 1) b c)
    (hJL : J ≤ L)
    {E : Subgroup ((LargeEvenMinusIdx (n - 1) → K) ≃ₗ[K]
      (LargeEvenMinusIdx (n - 1) → K))}
    (Δ : OrthTorus.TBJOmData (TableBOrth.qMinusForm K (n - 1) b c) p E (n - 1))
    (hE : E ≤ orthDerived (TableBOrth.qMinusForm K (n - 1) b c))
    {σ : (Fin (n - 1) → Multiplicative (ZMod p)) →* ↥L}
    (hψσ : ∀ w, ggQuotHom θ (σ w) =
      (OrthTorus.rMinusEquiv K (n - 1) b c).symm (Δ.τΩ hE w)) :
    Subgroup.center ↥L = ⊥ ∧
      ∃ (χ : ↥(orthDerived (TableBOrth.qMinusForm K (n - 1) b c)) ≃* ↥L)
        (κ : ↥(orthDerived (TableBOrth.qMinusForm K (n - 1) b c)) →* G),
        (∀ g, ggQuotHom θ (χ g) =
          (OrthTorus.rMinusEquiv K (n - 1) b c).symm g) ∧
        (∀ w, χ (Δ.τΩ hE w) = σ w) ∧
        (∀ w, κ (Δ.τΩ hE w) = ((σ w : ↥L) : G)) ∧
        Function.Injective κ ∧
        κ.range = L ∧
        (∀ H : Subgroup G, H ≤ L →
          (((H.subgroupOf L).map (ggQuotHom θ)).map
            (OrthTorus.rMinusEquiv K (n - 1) b c).toMonoidHom).map κ = H) ∧
        ((((J.subgroupOf L).map (ggQuotHom θ)).map
            (OrthTorus.rMinusEquiv K (n - 1) b c).toMonoidHom).map κ = J) := by
  classical
  obtain ⟨hZL, χ, hqLχ, hχτ⟩ :=
    ggTBJOrthLeft_chi_of_nativeModel hperf hn hf hKcard hbc θ Δ hE hψσ
  let eR : OrthRest.RMinus K (n - 1) b c ≃*
      ↥(orthDerived (TableBOrth.qMinusForm K (n - 1) b c)) :=
    OrthTorus.rMinusEquiv K (n - 1) b c
  let κ : ↥(orthDerived (TableBOrth.qMinusForm K (n - 1) b c)) →* G :=
    L.subtype.comp χ.toMonoidHom
  have hqLinj : Function.Injective (ggQuotHom θ) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_ggQuotHom, hZL]
  have hκτ : ∀ w, κ (Δ.τΩ hE w) = ((σ w : ↥L) : G) := by
    intro w
    change ((χ (Δ.τΩ hE w) : ↥L) : G) = ((σ w : ↥L) : G)
    rw [hχτ]
  have hκinj : Function.Injective κ := by
    intro a b h
    exact χ.injective (Subtype.ext h)
  have hκrange : κ.range = L := by
    rw [show κ = L.subtype.comp χ.toMonoidHom from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr χ.surjective, Subgroup.map_top, Subgroup.range_subtype]
  have hcomp : (κ.comp eR.toMonoidHom).comp (ggQuotHom θ) = L.subtype := by
    ext l
    change ((χ (eR (ggQuotHom θ l)) : ↥L) : G) = (l : G)
    have hq : ggQuotHom θ (χ (eR (ggQuotHom θ l))) = ggQuotHom θ l := by
      rw [hqLχ, MulEquiv.symm_apply_apply]
    have hχ : χ (eR (ggQuotHom θ l)) = l := hqLinj hq
    exact congrArg Subtype.val hχ
  have hHmap : ∀ H : Subgroup G, H ≤ L →
      (((H.subgroupOf L).map (ggQuotHom θ)).map eR.toMonoidHom).map κ = H := by
    intro H hHL
    rw [Subgroup.map_map, Subgroup.map_map, hcomp, Subgroup.map_subgroupOf_eq_of_le hHL]
  exact ⟨hZL, χ, κ, hqLχ, hχτ, hκτ, hκinj, hκrange, hHmap, hHmap J hJL⟩

theorem ggTBJOrthLeft_nativeModel_of_twD
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hBsB : Bs = B)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hL : GGInnerDiagOnLabel (fun p lab => lab = ⟨.twD, n, f⟩ ∧ GGTBRowR5O1 p lab) p Bs L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K),
      Nat.card K = 2 ^ f ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (θ : ↥L ⧸ Subgroup.center ↥L ≃* OrthRest.RMinus K (n - 1) b c)
        (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
        ∃ (E : Subgroup ((LargeEvenMinusIdx (n - 1) → K) ≃ₗ[K]
            (LargeEvenMinusIdx (n - 1) → K)))
          (Δ : OrthTorus.TBJOmData (TableBOrth.qMinusForm K (n - 1) b c) p E (n - 1))
          (hE : E ≤ orthDerived (TableBOrth.qMinusForm K (n - 1) b c))
          (σ : (Fin (n - 1) → Multiplicative (ZMod p)) →* ↥L)
          (ΘA : (Fin (n - 1) → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hN).range)
          (Θ : ((Fin (n - 1) → Multiplicative (ZMod p)) ×
              ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) ≃* ↥Bs),
          (∀ w, ggQuotHom θ (σ w) =
            (OrthTorus.rMinusEquiv K (n - 1) b c).symm (Δ.τΩ hE w)) ∧
          (∀ w, ((ΘA w : ↥(ggGamma L hN).range) : MulAut ↥L) = MulAut.conj (σ w)) ∧
          (∀ (w : Fin (n - 1) → Multiplicative (ZMod p))
             (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
             ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥L) : G) * c) ∧
          ((TypeBDatum.signedAut (n - 1) p).map (TypeBDatum.liftBs Θ)).map
              (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 ∧
          (∀ H : Subgroup G, H ≤ L →
            ggAutomizer H Bs =
              (FrameBs.sectionFrameAut (L.subtype.comp σ) H).map (TypeBDatum.liftBs Θ)) ∧
          (∃ v : LargeEvenMinusIdx (n - 1) → K, v ≠ 0 ∧ ∀ a ∈ E, a v = v) ∧
          (¬ CFSG.GroupTheory.WeirSylow.IsPlusType
              (TableBOrth.qMinusForm K (n - 1) b c) ∧
            Module.finrank K (LargeEvenMinusIdx (n - 1) → K) = 2 * ((n - 1) + 1) ∧
            (p ∣ Nat.card K - 1 ∨ Odd (n - 1) ∧ p ∣ Nat.card K + 1)) ∧
          Subgroup.center ↥L = ⊥ ∧
          ∃ (χ : ↥(orthDerived (TableBOrth.qMinusForm K (n - 1) b c)) ≃* ↥L)
            (κ : ↥(orthDerived (TableBOrth.qMinusForm K (n - 1) b c)) →* G),
            (∀ g, ggQuotHom θ (χ g) =
              (OrthTorus.rMinusEquiv K (n - 1) b c).symm g) ∧
            (∀ w, χ (Δ.τΩ hE w) = σ w) ∧
            (∀ w, κ (Δ.τΩ hE w) = ((σ w : ↥L) : G)) ∧
            Function.Injective κ ∧
            κ.range = L ∧
            (∀ H : Subgroup G, H ≤ L →
              (((H.subgroupOf L).map (ggQuotHom θ)).map
                (OrthTorus.rMinusEquiv K (n - 1) b c).toMonoidHom).map κ = H) ∧
            ((((J.subgroupOf L).map (ggQuotHom θ)).map
                (OrthTorus.rMinusEquiv K (n - 1) b c).toMonoidHom).map κ = J) := by
  classical
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  have hp : p.Prime := hcfg.tableB_facts.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨R₀, _, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hlab_eq : lab = ⟨.twD, n, f⟩ := hP₀.1.1
  subst lab
  obtain ⟨K, fieldK, finiteK, b, c, hK, hbc, hQraw⟩ :=
    largeEvenRawDatum_twD_exact (n := n) (f := f) hn hraw
  letI : Field K := fieldK
  letI : Finite K := finiteK
  haveI hCP : CharP K 2 := charP_two_of_card hK
  obtain ⟨hs, hna, θ, hP⟩ := hQraw
  have hrowR5 : GGTBRowR5O1 p (⟨.twD, n, f⟩ : LargeEvenLabel) := hP.1.2
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hP.2.1
  have hInd := hP.2.2
  obtain ⟨-, h4, hrowPar⟩ := hrowR5
  have hm : 3 ≤ n - 1 := by omega
  have hpq : p ∣ Nat.card K - 1 ∨ (Odd (n - 1) ∧ p ∣ Nat.card K + 1) := by
    rcases hrowPar with hpq | ⟨heven, hpq⟩
    · exact Or.inl (by rwa [hK])
    · refine Or.inr ⟨?_, by rwa [hK]⟩
      obtain ⟨k, rfl⟩ := heven
      exact ⟨k - 1, by omega⟩
  let R : Type := OrthRest.RMinus K (n - 1) b c
  let ψ₀ : ↥L →* R := ggQuotHom θ
  let A : Subgroup (MulAut ↥L) := (ggGamma L hN).range
  have hlift : GGTorusLift p 0 R :=
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus hm b c hbc)
  have hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut L θ ⟨b, hN hb⟩ ∈ Set.range (MulAut.conj : R →* MulAut R) :=
    fun b hb => ggLAut_mem_of_induces L θ hN hInd hb
  have hTB : GGTorusTBGroup p 0 R
      (Set.range (MulAut.conj : R →* MulAut R)) ↥L ψ₀ A :=
    ggTorusTBGroup_of_marking hp hBs hSC hperf θ hN hBsI (by
      rw [pow_zero]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
        (Nat.card_pos (α := ↥A)))) (card_range_ggGamma_bstar_ge hcfg hperf θ hN hlift).2
  obtain ⟨r, E, Δ, hE, σ, ΘA, hψσ, hΘA, hWeyl, hW⟩ :=
    ggTBJ_om_stdModel (K := K) hp hp2 hbc hm hpq ψ₀ A hTB
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qMinusForm K (n - 1) b c)).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm (n - 1) hbc
  have hT : ∃ T : Submodule K (LargeEvenMinusIdx (n - 1) → K),
      Module.finrank K T = 3 ∧
        ∀ v ∈ T, TableBOrth.qMinusForm K (n - 1) b c v = 0 :=
    (OrthTorus.charSum_qMinusForm (n - 1) hbc).2 hm
  have hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L) :=
    (OrthExc.center_data_omegaMinus hp hp2 hm hbc).2 ↥L ψ₀ hTB.1 hTB.2.1 hTB.2.2.1
  have hZ : ∀ z ∈ Subgroup.center ↥L, z ^ p = 1 → z = 1 :=
    ggTBJ_noPElt_center_of_not_dvd hZc
  obtain ⟨Θ, hΘ, hAut⟩ :=
    FrameBs.ggAutomizer_eq_map_liftBs_sectionFrameAut hBs hSC hN hZ σ ΘA hΘA
  have hXaut : ggAutomizer L Bs =
      (TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ) := by
    rw [hAut L le_rfl, FrameBs.sectionFrameAut_subtype_comp σ le_rfl,
      Subgroup.subgroupOf_self,
      OrthTorus.sectionFrameAut_top_fixed hp2 hQ hT hTB.1 hTB.2.1 hZ hψσ hW]
  have hcoord : ((TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 := by
    rw [← hXaut]
    exact hLB
  have hcardBs : Nat.card ↥Bs = p ^ n := by
    rw [Nat.card_congr eta.toEquiv]
    exact FrameBs.card_zmodFrame p n
  have hcardFrame : Nat.card ↥Bs = p ^ r * p := by
    rw [← Nat.card_congr Θ.toEquiv, Nat.card_prod, FrameBs.card_zmodFrame p r,
      hcfg.card_bstar_inf_centralizer_L]
  have hpow : p ^ n = p ^ (r + 1) := by
    rw [← hcardBs, hcardFrame, ← pow_succ]
  have hnr : n = r + 1 := Nat.pow_right_injective hp.two_le hpow
  have hr_eq : r = n - 1 := by omega
  subst r
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (TableBOrth.qMinusForm K (n - 1) b c) := by
    intro hplus
    have hplus' : CFSG.GroupTheory.WeirSylow.IsPlusType
        (CFSG.LieType.Universal.Spin.quadMinus ((n - 1) + 1) K b c) :=
      (CFSG.GroupTheory.WeirSylow.isPlusType_congr
        (TableBOrth.qMinusIsometry (n - 1) b c)).1 hplus
    have hplus'' : CFSG.GroupTheory.WeirSylow.IsPlusType
        (CFSG.LieType.Universal.Spin.quadMinus n K b c) := by
      have hsub : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
      exact hsub ▸ hplus'
    exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := n) (by omega) hbc hplus''
  have hfinrank : Module.finrank K (LargeEvenMinusIdx (n - 1) → K) =
      2 * ((n - 1) + 1) := by
    rw [Module.finrank_fintype_fun_eq_card K]
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    ring
  have hrow : p ∣ Nat.card K - 1 ∨ Odd (n - 1) ∧ p ∣ Nat.card K + 1 := by
    rcases hrowPar with hpq | ⟨heven, hpq⟩
    · exact Or.inl (by rwa [hK])
    · refine Or.inr ⟨?_, by rwa [hK]⟩
      obtain ⟨k, rfl⟩ := heven
      exact ⟨k - 1, by omega⟩
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨hZL, χ, κ, hqLχ, hχτ, hκτ, hκinj, hκrange, hHmap, hJmap⟩ :=
    ggTBJOrthLeft_chart_of_nativeModel (p := p) (J := J)
      hperf hn hf hK hbc θ hJL Δ hE hψσ
  exact ⟨K, fieldK, finiteK, hCP, b, c, hK, hbc, θ, hN, E, Δ, hE, σ, ΘA, Θ,
    hψσ, hΘA, hΘ, hcoord, hAut, hW, ⟨hminus, hfinrank, hrow⟩, hZL, χ, κ,
    hqLχ, hχτ, hκτ, hκinj, hκrange, hHmap, hJmap⟩

theorem ggTBJOrthLeft_rowR5O2_with_fixed_centralizer
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O2 p lab) p Bs L) :
    (GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J) ∧
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, -, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ GGTBRowR5O2 p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggO2Row_labelAll_adjoint hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r0, m, n, K, _, _, b, c, e, hlift, hK, hn, hbc,
    hm, hme, hpn, hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr0, h30⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr0 h30
  have hTB' := GGTorusTBGroup.mulEquiv
    (I' := Set.range (MulAut.conj : OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hI φ hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  haveI hCP : CharP K 2 := charP_two_of_card hK
  let ψ₀ : ↥L →* OrthRest.RMinus K m b c := e.toMonoidHom.comp (ggQuotHom θ)
  obtain ⟨r, E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hnf⟩ :=
    ggTBJ_om_stdModel_nf hp hp2 hbc hm hme (by rw [hK]; exact hpn) ψ₀ _ hTB'
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qMinusForm K m b c)).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm m hbc
  have hT : ∃ T : Submodule K (LargeEvenMinusIdx m → K), Module.finrank K T = 3 ∧
      ∀ v ∈ T, TableBOrth.qMinusForm K m b c v = 0 :=
    (OrthTorus.charSum_qMinusForm m hbc).2 hm
  have hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L) :=
    (OrthExc.center_data_omegaMinus hp hp2 hm hbc).2 ↥L ψ₀ hTB'.1 hTB'.2.1 hTB'.2.2.1
  have hdimV : Module.finrank K (LargeEvenMinusIdx m → K) = 2 * m + 2 := by
    rw [Module.finrank_fintype_fun_eq_card K]
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    ring
  have hle : 2 * m + 2 ≤ 2 * r := by
    have := Δ.finrank_le_two_mul_of_noFixed hnf
    rwa [hdimV] at this
  have hr : 4 ≤ r := by omega
  exact OrthTorus.ggTBJOrthLeft_nf_of_cfg_with_fixed_centralizer hcfg hBsN hQ hT hTB'.1 hTB'.2.1 hZc hψσ hΘ
    hWeyl hnf hr

theorem ggTBJOrthLeft_rowR5O2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O2 p lab) p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  exact (ggTBJOrthLeft_rowR5O2_with_fixed_centralizer hH hL).1

end CFSG.StandardType

end
