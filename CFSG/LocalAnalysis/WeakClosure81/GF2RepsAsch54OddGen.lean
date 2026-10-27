module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54OddDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunThree

import CFSG.GH74.SectionalRankExtension
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Alm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieOddRankFourHolds
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
import CFSG.Open.WalterAbelianSylowTwoTauCeti
import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieCover
import CFSG.GH74.GLS.C3.Layer1.PU3Thm5
import CFSG.Quasithin.Background.GoldschmidtShultLink
import CFSG.Quasithin.Vol2.Ch4Sec4L448
import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F2
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open scoped commutatorElement
open CFSG.ClassicalInvolution.ModelFacts
  (nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups)

theorem sectionalTwoRankLE_of_isCompositionFactor {X : Type} [Group X] [Finite X] {M : Type}
    [Group M] (h : E1.IsCompositionFactor X M) (hX : CFSG.GH74.SectionalTwoRankLE X 2) :
    CFSG.GH74.SectionalTwoRankLE M 2 := by
  obtain ⟨N, M', hNM, -, -, -, -, ⟨e⟩⟩ := h
  exact CFSG.GH74.SectionalTwoRankLE.of_mulEquiv e
    (sectionalTwoRankLE_section hX M' (N.subgroupOf M'))

theorem sectionalTwoRankLE_of_isCompositionFactor_iSup {G : Type} [Group G] [Finite G]
    (S : Finset (Subgroup G)) (hcomm : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ⁅A, B⁆ = ⊥)
    (hsec : ∀ A ∈ S, CFSG.GH74.SectionalTwoRankLE ↥A 2) {M : Type} [Group M]
    (h : E1.IsCompositionFactor ↥(⨆ A ∈ S, A) M) : CFSG.GH74.SectionalTwoRankLE M 2 := by
  classical
  induction S using Finset.induction_on generalizing M with
  | empty =>
    exfalso
    obtain ⟨N, M', _, -, -, -, hs, -⟩ := h
    have hbot : (⨆ A ∈ (∅ : Finset (Subgroup G)), A) = ⊥ := by simp
    have hsub : Subsingleton ↥(⨆ A ∈ (∅ : Finset (Subgroup G)), A) :=
      ⟨fun a b => Subtype.ext (by
        have ha : (a : G) ∈ (⊥ : Subgroup G) := hbot ▸ a.2
        have hb : (b : G) ∈ (⊥ : Subgroup G) := hbot ▸ b.2
        rw [mem_bot] at ha hb
        rw [ha, hb])⟩
    have := hs
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥M' ⧸ N.subgroupOf M')
    induction x using QuotientGroup.induction_on with
    | H y =>
      apply hx
      rw [Subsingleton.elim y 1]
      rfl
  | insert A S hA ih =>
    set N' := ⨆ B ∈ S, B with hN'
    have hN : (⨆ B ∈ insert A S, B) = A ⊔ N' := Finset.iSup_insert A S id
    rw [hN] at h
    have hcen : N' ≤ centralizer (A : Set G) := by
      refine iSup₂_le fun B hB => ?_
      exact commutator_eq_bot_iff_le_centralizer.1
        (hcomm B (Finset.mem_insert_of_mem hB) A (Finset.mem_insert_self A S)
          (fun h => hA (h ▸ hB)))
    have hAc : A ≤ centralizer (N' : Set G) := le_centralizer_iff.1 hcen
    have hAn : A ≤ normalizer (N' : Set G) := hAc.trans (centralizer_le_normalizer N')
    have hnorm : A ⊔ N' ≤ normalizer (N' : Set G) := sup_le hAn le_normalizer
    have hN'n : (N'.subgroupOf (A ⊔ N')).Normal :=
      (normal_subgroupOf_iff_le_normalizer le_sup_right).2 hnorm
    rcases isCompositionFactor_of_normal (N'.subgroupOf (A ⊔ N')) h with h1 | h2
    · exact ih (fun B hB C hC => hcomm B (Finset.mem_insert_of_mem hB) C
          (Finset.mem_insert_of_mem hC))
        (fun B hB => hsec B (Finset.mem_insert_of_mem hB))
        ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
          (subgroupOfEquivOfLe le_sup_right)).1 h1)
    · let f : ↥A →* ↥(A ⊔ N') ⧸ N'.subgroupOf (A ⊔ N') :=
        (QuotientGroup.mk' (N'.subgroupOf (A ⊔ N'))).comp (inclusion le_sup_left)
      have hf : Function.Surjective f := by
        intro x
        induction x using QuotientGroup.induction_on with
        | H y =>
          have hy : (y : G) ∈ ((A ⊔ N' : Subgroup G) : Set G) := y.2
          rw [coe_mul_of_left_le_normalizer_right A N' hAn] at hy
          obtain ⟨a, ha, n, hn, hy'⟩ := hy
          refine ⟨⟨a, ha⟩, ?_⟩
          change (QuotientGroup.mk (inclusion le_sup_left ⟨a, ha⟩) :
            ↥(A ⊔ N') ⧸ N'.subgroupOf (A ⊔ N')) = QuotientGroup.mk y
          rw [QuotientGroup.eq]
          change ((inclusion le_sup_left ⟨a, ha⟩ : ↥(A ⊔ N'))⁻¹ * y : G) ∈ N'
          simp only [coe_inclusion, InvMemClass.coe_inv] at *
          rw [← hy', ← mul_assoc, inv_mul_cancel, one_mul]
          exact hn
      exact sectionalTwoRankLE_of_isCompositionFactor
        (CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective f hf h2)
        (hsec A (Finset.mem_insert_self A S))


theorem characteristic_eq_of_namesTag {d : TauCeti.LieTypeIndex}
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {p f : ℕ} (h : CFSG.Models.NamesTag d t p f) :
    d.characteristic = p := by
  cases d <;> cases t <;> simp_all [CFSG.Models.NamesTag]

theorem exists_sl2_surjective_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (h : CFSG.Blueprint.LieModel X .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), (2 : F) ≠ 0 ∧
      ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* X, Function.Surjective φ := by
  obtain ⟨hp, -, -, -, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data h
  refine ⟨F, inferInstance, inferInstance, ?_,
    e.symm.toMonoidHom.comp (QuotientGroup.mk' _),
    e.symm.surjective.comp (QuotientGroup.mk'_surjective _)⟩
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype F := Fintype.ofFinite F
  have := charP_of_card_eq_prime_pow (R := F) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  intro h2
  have h2' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2
  rw [CharP.cast_eq_zero_iff F p] at h2'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2')


theorem isFundamentalOver_map_mulEquiv {X : Type} [Group X] {q : ℕ} {K : Subgroup X}
    (hK : CFSG.LocalAnalysis.UniquenessCase.IsFundamentalOver q K) (φ : X ≃* X) :
    CFSG.LocalAnalysis.UniquenessCase.IsFundamentalOver q (K.map φ.toMonoidHom) := by
  obtain ⟨t, n, p, e, hp, hp2, hq, hfund, hadm, ψ, hsurj, hker, R, hR, rfl⟩ := hK
  refine ⟨t, n, p, e, hp, hp2, hq, hfund, hadm, φ.toMonoidHom.comp ψ, φ.surjective.comp hsurj,
    fun x hx => hker ?_, R, hR, map_map _ _ _⟩
  rw [MonoidHom.mem_ker] at hx ⊢
  exact (map_eq_one_iff φ φ.injective).1 hx

theorem map_mem_funSet {X : Type} [Group X] [Finite X] {q : ℕ} {P K : Subgroup X}
    (hK : K ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.F14.FunSet
      (CFSG.LocalAnalysis.UniquenessCase.fundPred q) X P)
    (φ : X ≃* X) (hφ : P.map φ.toMonoidHom = P) :
    K.map φ.toMonoidHom ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.F14.FunSet
      (CFSG.LocalAnalysis.UniquenessCase.fundPred q) X P := by
  obtain ⟨hf, hs⟩ := hK
  refine ⟨isFundamentalOver_map_mulEquiv hf φ, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hs ⊢
  obtain ⟨-, hp, hdvd⟩ := hs
  have hmap : (P ⊓ K).map φ.toMonoidHom = P ⊓ K.map φ.toMonoidHom := by
    rw [map_inf_eq _ _ _ φ.injective, hφ]
  refine ⟨inf_le_right, ?_, ?_⟩
  · rw [← hmap]
    exact hp.map _
  · rw [← hmap, relIndex_map_map_of_injective _ _ φ.injective]
    exact hdvd

theorem sectionalTwoRankLE_of_isFundamentalOver {X : Type} [Group X] {q : ℕ} {K : Subgroup X}
    (hK : CFSG.LocalAnalysis.UniquenessCase.IsFundamentalOver q K) :
    CFSG.GH74.SectionalTwoRankLE ↥K 2 := by
  obtain ⟨t, n, p, e, hp, hp2, -, hfund, hadm, ψ, -, -, R, hR, rfl⟩ := hK
  have : Fact p.Prime := ⟨hp⟩
  have h2 : ∀ e' : ℕ, (2 : GaloisField p e') ≠ 0 := fun e' h => by
    have h2 : ((2 : ℕ) : GaloisField p e') = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p e') p] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hsec : CFSG.GH74.SectionalTwoRankLE ↥R 2 ∧ Finite ↥R := by
    rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hR with
      hφ | ⟨-, hφ⟩
    · obtain ⟨φ⟩ := hφ
      exact ⟨CFSG.GH74.SectionalTwoRankLE.of_mulEquiv φ.symm
        (CFSG.GH74.SectionalTwoRankLE.specialLinearGroup _ (h2 e)),
        Finite.of_equiv _ φ.symm.toEquiv⟩
    · obtain ⟨φ⟩ := hφ
      exact ⟨CFSG.GH74.SectionalTwoRankLE.of_mulEquiv φ.symm
        (CFSG.GH74.SectionalTwoRankLE.specialLinearGroup _ (h2 (3 * e))),
        Finite.of_equiv _ φ.symm.toEquiv⟩
  have := hsec.2
  exact CFSG.GH74.SectionalTwoRankLE.of_surjective (ψ.subgroupMap R) (ψ.subgroupMap_surjective R)
    hsec.1

theorem exists_sl2_range_of_isFundamentalOver {X : Type} [Group X] {q : ℕ} {K : Subgroup X}
    (hK : CFSG.LocalAnalysis.UniquenessCase.IsFundamentalOver q K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), (2 : F) ≠ 0 ∧
      ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* X, φ.range = K := by
  obtain ⟨t, n, p, e, hp, hp2, -, hfund, hadm, ψ, -, -, R, hR, rfl⟩ := hK
  have : Fact p.Prime := ⟨hp⟩
  have h2 : ∀ e' : ℕ, (2 : GaloisField p e') ≠ 0 := fun e' h => by
    have h2 : ((2 : ℕ) : GaloisField p e') = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p e') p] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hrange : ∀ {F : Type} [Field F] (φ : ↥R ≃* Matrix.SpecialLinearGroup (Fin 2) F),
      (ψ.comp (R.subtype.comp φ.symm.toMonoidHom)).range = R.map ψ := by
    intro F _ φ
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 φ.symm.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hR with
    hφ | ⟨-, hφ⟩
  · obtain ⟨φ⟩ := hφ
    exact ⟨GaloisField p e, inferInstance, inferInstance, h2 e, _, hrange φ⟩
  · obtain ⟨φ⟩ := hφ
    exact ⟨GaloisField p (3 * e), inferInstance, inferInstance, h2 (3 * e), _, hrange φ⟩


theorem exists_blueprint_of_oddLieType {X : Type} [Group X] (h : CFSG.Models.OddLieType X) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n f : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n r f ∧ CFSG.Blueprint.LieModel X t n r f := by
  obtain ⟨t, n, p, f, hp2, hadm, hcl | ⟨-, d, hN, ⟨e⟩⟩⟩ := h
  · have ht : t ∈ CFSG.Blueprint.classicalTags := by
      obtain ⟨-, h2⟩ := hcl
      cases t <;> first | decide | exact h2.elim
    exact ⟨p, hadm.1, hp2, t, n, f, hadm, CFSG.Models.LieModel.toBlueprint ht ⟨hadm, .inl hcl⟩⟩
  · have hch : d.1.characteristic = p := characteristic_eq_of_namesTag hN
    obtain ⟨t', n', f', hm⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.exists_blueprint_lieModel_of_odd d
        (by rw [hch]; exact hp2) e
    rw [hch] at hm
    exact ⟨p, hadm.1, hp2, t', n', f', hm.admissible, hm⟩

open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL2Over17 IsL3EpsOdd17 IsReeOver17)

theorem oddLie_generic_pRank_of_not_sl2Image
    (hFC : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommute)
    (hFC3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommuteThree)
    {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q} [hLn : L.Normal]
    (hLs : IsSimpleGroup ↥L) (hLnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hodd : CFSG.Models.OddLieType ↥L)
    (hSL2 : ¬ ∃ (F : Type) (_ : Field F) (_ : Finite F), (2 : F) ≠ 0 ∧
      ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥L, Function.Surjective φ)
    (hree : ¬ ∃ f : ℕ, CFSG.Models.LieModel ↥L .twistedG2 0 3 f)
    (hsmall : ¬ ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ Asch511SmallLie ↥L r) (hT : IsSylowIn 2 T ⊤) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) ∧
      1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T) := by
  have := hLs
  obtain ⟨r, hr, hr2, t, n, f, hadm, hBL⟩ := exists_blueprint_of_oddLieType hodd
  have : Fact r.Prime := ⟨hr⟩
  have hZ : center ↥L = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_simple hLnab
  have hLZ : ∀ {t' : CFSG.Assembly.LowTwoRank.StatedLieTag} {n' p' f' : ℕ},
      CFSG.Blueprint.LieModel (↥L ⧸ center ↥L) t' n' p' f' →
        CFSG.Blueprint.LieModel ↥L t' n' p' f' :=
    fun h => CFSG.Blueprint.LieModel.of_quotient_center hZ h
  have hBLZ : CFSG.Blueprint.LieModel (↥L ⧸ center ↥L) t n r f :=
    CFSG.Blueprint.LieModel.quotient_center hZ hBL
  have hmod : ∃ (t' : CFSG.Assembly.LowTwoRank.StatedLieTag) (n' f' : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t' n' r f' ∧ r ^ f = r ^ f' ∧
        CFSG.Blueprint.LieModel (↥L ⧸ center ↥L) t' n' r f' := ⟨t, n, f, hadm, rfl, hBLZ⟩
  have hQS : CFSG.Open.IsQuasisimple ↥L := CFSG.GH74.GLS.PU3.Thm5.isQuasisimple_of_simple hLnab
  have hoddZ : Odd (Nat.card (center ↥L)) := by rw [hZ]; simp
  have hnL2 : ¬ IsL2Over17 (↥L ⧸ center ↥L) (r ^ f) := by
    rintro ⟨r', f', -, hr'2, -, -, hm⟩
    exact hSL2 (exists_sl2_surjective_of_lieModel_psl_two hr'2 (hLZ hm))
  have hnL3 : ¬ IsL3EpsOdd17 (↥L ⧸ center ↥L) r := fun h =>
    hsmall ⟨r, hr, hr2, Or.inr (Or.inr (h.imp hLZ hLZ))⟩
  have hnRee : ¬ IsReeOver17 ↥L (r ^ f) := by
    rintro ⟨m, -, hm⟩
    exact hree ⟨2 * m + 1, CFSG.Open.models_lieModel_twistedG2_of_blueprint hm⟩
  have h4 : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥L) := by
    rcases CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_LieOddRankFour_holds ↥L r (r ^ f)
        hr hr2 hmod hQS hoddZ hnL2 hnL3 hnRee with h | ⟨-, hGP, -⟩
    · exact h
    · exact absurd ⟨r, hr, hr2,
        hGP.elim (fun h => Or.inl (hLZ h)) (fun h => Or.inr (Or.inl (hLZ h)))⟩ hsmall
  have hTL : IsSylowIn 2 (T ⊓ L) L := CFSG.Quasithin.Shult.isSylowTwoOf_inf_normal hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Sylow 2 ↥L := hTL.toSylow with hPdef
  have hPco : (P : Subgroup ↥L) = (T ⊓ L).subgroupOf L := rfl
  obtain ⟨⟨E, K₁, K₂, hK₁, hK₂, hEel, hEcard, hEle⟩, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_FunRankTwo_holds ↥L r (r ^ f) hr hr2
      hmod hQS hoddZ (Or.inr (by rw [hZ]; simpa using hr.ne_one)) hnL2 hnL3 hnRee P
  have hf1 : 1 ≤ f := hadm.2.1
  have hq3 : 3 ≤ r ^ f :=
    le_trans (hr.two_le.lt_of_ne (Ne.symm hr2)) (Nat.le_self_pow (by omega) r)
  have hcomm : ∀ A ∈ FunSet (fundPred (r ^ f)) ↥L (P : Subgroup ↥L),
      ∀ B ∈ FunSet (fundPred (r ^ f)) ↥L (P : Subgroup ↥L), A ≠ B → ⁅A, B⁆ = ⊥ := by
    rcases Nat.lt_or_eq_of_le hq3 with hlt | heq
    · exact hFC ↥L r (r ^ f) hr hr2 hmod hQS hoddZ hnL2 hnL3 hnRee hlt P
    · exact hFC3 ↥L r (r ^ f) hr hr2 hmod hQS hoddZ hnL2 hnL3 hnRee heq.symm P
  set F := FunSet (fundPred (r ^ f)) ↥L (P : Subgroup ↥L) with hF
  have hFfin : F.Finite := Set.toFinite F
  set N : Subgroup ↥L := ⨆ A ∈ hFfin.toFinset, A with hN
  have hleN : ∀ A ∈ F, A ≤ N := fun A hA => le_iSup₂_of_le A (hFfin.mem_toFinset.2 hA) le_rfl
  have hNcf : ∀ {M : Type} [Group M], E1.IsCompositionFactor ↥N M →
      CFSG.GH74.SectionalTwoRankLE M 2 := fun h =>
    sectionalTwoRankLE_of_isCompositionFactor_iSup hFfin.toFinset
      (fun A hA B hB => hcomm A (hFfin.mem_toFinset.1 hA) B (hFfin.mem_toFinset.1 hB))
      (fun A hA => sectionalTwoRankLE_of_isFundamentalOver (hFfin.mem_toFinset.1 hA).1) h
  have hφN : ∀ φ : ↥L ≃* ↥L, (P : Subgroup ↥L).map φ.toMonoidHom = P →
      N ≤ N.comap φ.toMonoidHom := by
    intro φ hφ
    refine iSup₂_le fun A hA => ?_
    rw [← map_le_iff_le_comap]
    exact hleN _ (map_mem_funSet (hFfin.mem_toFinset.1 hA) φ hφ)
  have hconjP : ∀ g ∈ T, (P : Subgroup ↥L).map (MulAut.conjNormal g).toMonoidHom = P := by
    intro g hg
    refine le_antisymm ?_ fun x hx => ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : Q) ∈ T ⊓ L := by rw [hPco] at hx; exact hx
      show (MulAut.conjNormal g) x ∈ (P : Subgroup ↥L)
      rw [hPco, mem_subgroupOf]
      change g * (x : Q) * g⁻¹ ∈ T ⊓ L
      exact ⟨T.mul_mem (T.mul_mem hg hx'.1) (T.inv_mem hg), hLn.conj_mem _ x.2 g⟩
    · have hx' : (x : Q) ∈ T ⊓ L := by rw [hPco] at hx; exact hx
      refine ⟨(MulAut.conjNormal g).symm x, ?_, by simp⟩
      show (MulAut.conjNormal g).symm x ∈ (P : Subgroup ↥L)
      rw [hPco, mem_subgroupOf, MulAut.conjNormal_symm_apply]
      refine ⟨T.mul_mem (T.mul_mem (T.inv_mem hg) hx'.1) hg, ?_⟩
      have h := hLn.conj_mem _ x.2 g⁻¹
      rwa [inv_inv] at h
  set NQ : Subgroup Q := N.map L.subtype with hNQ
  have hconjNQ : ∀ g ∈ T, ∀ x ∈ NQ, g * x * g⁻¹ ∈ NQ := by
    rintro g hg _ ⟨n, hn, rfl⟩
    have h1 := hφN (MulAut.conjNormal g) (hconjP g hg) hn
    exact ⟨_, h1, by simp⟩
  have hTnorm : T ≤ normalizer (NQ : Set Q) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconjNQ g hg x, fun hx => ?_⟩
    have h := hconjNQ g⁻¹ (T.inv_mem hg) _ hx
    simpa [mul_assoc] using h
  set H : Subgroup Q := T ⊔ NQ with hH
  have hHnorm : H ≤ normalizer (NQ : Set Q) := sup_le hTnorm le_normalizer
  have hNQn : (NQ.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).2 hHnorm
  have hHq : Group.IsSolvable (↥H ⧸ NQ.subgroupOf H) := by
    let φ : ↥T →* ↥H ⧸ NQ.subgroupOf H :=
      (QuotientGroup.mk' (NQ.subgroupOf H)).comp (inclusion le_sup_left)
    have hφ : Function.Surjective φ := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H y =>
        have hy : (y : Q) ∈ ((T ⊔ NQ : Subgroup Q) : Set Q) := y.2
        rw [coe_mul_of_left_le_normalizer_right T NQ hTnorm] at hy
        obtain ⟨a, ha, b, hb, hy'⟩ := hy
        refine ⟨⟨a, ha⟩, ?_⟩
        change (QuotientGroup.mk (inclusion le_sup_left ⟨a, ha⟩) :
          ↥H ⧸ NQ.subgroupOf H) = QuotientGroup.mk y
        rw [QuotientGroup.eq]
        change ((inclusion le_sup_left ⟨a, ha⟩ : ↥H)⁻¹ * y : Q) ∈ NQ
        simp only [coe_inclusion, InvMemClass.coe_inv] at *
        rw [← hy', ← mul_assoc, inv_mul_cancel, one_mul]
        exact hb
    have : Group.IsNilpotent ↥T := hT.isPGroup.isNilpotent
    exact Group.isSolvable_of_surjective hφ
  have hHno : ¬ HasCompFactor H IsCalL0 := by
    rintro ⟨M, _, hcf, hM⟩
    have : Finite M := isCompositionFactor_finite hcf
    obtain ⟨hnab, hMsec⟩ := isCalL0_nonabelian_not_sectionalTwoRankLE M hM
    have h1 := isCompositionFactor_subgroupOf_of_isSolvable_quot hHq
      ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr Subgroup.topEquiv).2 hcf) hnab
    let e : ↥((NQ.subgroupOf H).subgroupOf ⊤) ≃* ↥N :=
      ((subgroupOfEquivOfLe le_top).trans (subgroupOfEquivOfLe le_sup_right)).trans
        (equivMapOfInjective N L.subtype L.subtype_injective).symm
    exact hMsec (hNcf ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).1 h1))
  have hKne : ∀ K ∈ F, K ≠ ⊤ := by
    intro K hK hKt
    obtain ⟨F', _, _, h2', φ, hφ⟩ := exists_sl2_range_of_isFundamentalOver hK.1
    exact hSL2 ⟨F', inferInstance, inferInstance, h2', φ, MonoidHom.range_eq_top.1 (hφ.trans hKt)⟩
  have hEne : E ≠ ⊥ := by
    intro hE
    rw [hE] at hEcard
    simp only [card_bot] at hEcard
    have : 1 < r ^ 2 := Nat.one_lt_pow (by norm_num) hr.one_lt
    omega
  have hHlt : H < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have hNn : N.Normal := by
      refine ⟨fun n hn l => ?_⟩
      have hl : (l : Q) ∈ normalizer (NQ : Set Q) := hHnorm (htop ▸ mem_top (l : Q))
      obtain ⟨m, hm, hmeq⟩ := (mem_normalizer_iff.1 hl (n : Q)).1 ⟨n, hn, rfl⟩
      have hml : m = l * n * l⁻¹ := Subtype.ext (by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        exact hmeq)
      rw [← hml]
      exact hm
    have := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
    · apply hEne
      refine eq_bot_iff.2 (hEle.trans (sup_le ?_ ?_))
      · exact (hleN K₁ hK₁).trans hb.le
      · exact (hleN K₂ hK₂).trans hb.le
    · have hKnorm : ∀ K ∈ F, K.Normal := by
        intro K hK
        rw [← normalizer_eq_top_iff, eq_top_iff, ← ht]
        refine iSup₂_le fun A hA => ?_
        by_cases hAK : A = K
        · rw [hAK]
          exact le_normalizer
        · exact (commutator_eq_bot_iff_le_centralizer.1
            (hcomm A (hFfin.mem_toFinset.1 hA) K hK hAK)).trans (centralizer_le_normalizer K)
      have := hKnorm K₁ hK₁
      have := hKnorm K₂ hK₂
      have hb₁ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal K₁).resolve_right (hKne K₁ hK₁)
      have hb₂ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal K₂).resolve_right (hKne K₂ hK₂)
      apply hEne
      rw [eq_bot_iff, ← sup_bot_eq (⊥ : Subgroup ↥L)]
      calc E ≤ K₁ ⊔ K₂ := hEle
        _ = ⊥ ⊔ ⊥ := by rw [hb₁, hb₂]
  have hlGen : H ≤ lGen IsCalL0 ⊤ T := le_iSup₂_of_le H ⟨le_sup_left, hHlt, hHno⟩ le_rfl
  refine ⟨r, hr, hr2, ?_, ?_⟩
  ·
    have hc : commutator ↥L = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := hLnab
        apply hab
        have hm : ⁅a, b⁆ ∈ commutator ↥L := commutator_mem_commutator (mem_top a) (mem_top b)
        rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
        exact hm
      · exact h
    have hperf : ⁅L, L⁆ = L := by
      have e := congrArg (Subgroup.map L.subtype) hc
      rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at e
    have hLle : L ≤ CFSG.Quasithin.perfectCore (⊤ : Subgroup Q) :=
      CFSG.Quasithin.le_perfectCore_of_perfect le_top hperf
    have h1 := CFSG.SectionRank.pRank_mono hr.one_lt hLle
    rw [← CFSG.Quasithin.pRank_top_subtype] at h1
    omega
  ·
    have hE' : E.map L.subtype ≤ lGen IsCalL0 ⊤ T :=
      (map_mono (hEle.trans (sup_le (hleN K₁ hK₁) (hleN K₂ hK₂)))).trans
        (le_sup_right.trans hlGen)
    have hEel' := CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_map_of_injective L.subtype
      L.subtype_injective hEel
    have hcard : Nat.card (E.map L.subtype) = r ^ 2 := by
      rw [card_map_of_injective L.subtype_injective]
      exact hEcard
    have h2 := CFSG.Quasithin.H13.Ch4.le_pRank_of_isElemAbelian hr.one_lt hE' hEel' hcard
    omega

theorem oddLie_generic_pRank
    (hFC : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommute)
    (hFC3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommuteThree)
    {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q} [hLn : L.Normal]
    (hLs : IsSimpleGroup ↥L) (hLnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hodd : CFSG.Models.OddLieType ↥L) (hsec : ¬ CFSG.GH74.SectionalTwoRankLE ↥L 2)
    (hree : ¬ ∃ f : ℕ, CFSG.Models.LieModel ↥L .twistedG2 0 3 f)
    (hsmall : ¬ ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ Asch511SmallLie ↥L r) (hT : IsSylowIn 2 T ⊤) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) ∧
      1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T) :=
  oddLie_generic_pRank_of_not_sl2Image hFC hFC3 hLs hLnab hodd
    (fun ⟨F, _, _, h2, φ, hφ⟩ => hsec (CFSG.GH74.SectionalTwoRankLE.of_surjective φ hφ
      (CFSG.GH74.SectionalTwoRankLE.specialLinearGroup F h2))) hree hsmall hT

theorem asch54Case_oddLie_generic
    (hFC : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommute)
    (hFC3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_FunCommuteThree) :
    Asch54Case fun X _ => CFSG.Models.OddLieType X ∧ ¬ CFSG.GH74.SectionalTwoRankLE X 2 ∧
      (¬ ∃ f : ℕ, CFSG.Models.LieModel X .twistedG2 0 3 f) ∧
      ¬ ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ Asch511SmallLie X r := by
  intro Q _ _ L T _ hLn hLs hLnab _ ⟨hodd, hsec, hree, hsmall⟩ _ hT _
  exact Or.inr (oddLie_generic_pRank hFC hFC3 hLs hLnab hodd hsec hree hsmall hT)

end CFSG.LocalAnalysis.WeakClosure81
