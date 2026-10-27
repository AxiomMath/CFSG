module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveTwentyThree

theorem autI_mem_aSet_of_mem_gammaSet {V S A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hSN : S ≤ normalizer (V : Set G)) {i n : ℕ} (hin : i + n < E3.sParam hV)
    (hA : A ∈ E3.gammaSet V i S) (hA1 : autI hV A ≠ ⊥) :
    autI hV A ∈ E3.aSet (n + 1) (autI hV ⊤) := by
  obtain ⟨hAS, g, hAg, hm⟩ := hA
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
  have hAN : A ≤ normalizer (V : Set G) := hAS.trans hSN
  refine ⟨autI_mono hV le_top, hA1, isElemAbelian2_autI hV hAel hAN, ?_⟩
  intro B' hB' hlt
  have hlt' : E3.mQuot A (preI hV A hAN B') ≤ n := by
    rw [← E3.mQuot_autI_preI hV hAN hB']
    omega
  have hBA : preI hV A hAN B' ≤ A := preI_le hV
  have hadd := E3.mQuot_add (V := conjSubgroup V g) hBA hAg
  have hlt2 : E3.mQuot (conjSubgroup V g) (preI hV A hAN B') < E3.sParam hVg := by
    rw [E3.sParam_conj hV g hVg]
    omega
  have hCB := (E3.e3_6 hVg hBA hAg hlt2 (B2F.isPGroup_of_isElemAbelian hV)).1
  have hpre : autI hV (preI hV A hAN B') = B' := autI_preI hV hB'
  have hBN : preI hV A hAN B' ≤ normalizer (V : Set G) := hBA.trans hAN
  ext v
  have e1 : v ∈ fixV B' ↔ v.val ∈ centralizer (preI hV A hAN B' : Set G) := by
    conv_lhs => rw [← hpre]
    exact mem_fixV_autI hV hBN v
  have e2 : v ∈ fixV (autI hV A) ↔ v.val ∈ centralizer (A : Set G) :=
    mem_fixV_autI hV hAN v
  rw [e1, e2]
  have hv : v.val ∈ V := v.val_mem
  constructor
  · intro hc
    have : v.val ∈ V ⊓ centralizer (preI hV A hAN B' : Set G) := Subgroup.mem_inf.2 ⟨hv, hc⟩
    rw [← hCB] at this
    exact (Subgroup.mem_inf.1 this).2
  · intro hc
    have : v.val ∈ V ⊓ centralizer (A : Set G) := Subgroup.mem_inf.2 ⟨hv, hc⟩
    rw [hCB] at this
    exact (Subgroup.mem_inf.1 this).2

theorem barSub_bot_eq_map_autI (V : Subgroup G) (hV : IsElemAbelian 2 V) (K : Subgroup G) :
    barSub (⊥ : Subgroup G) V hV K =
      (autI hV K).map (MulAut.congr (TwelveShort.mkTilEquiv V hV)).toMonoidHom := by
  ext ψ
  rw [mem_barSub, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hgK, rfl⟩
    refine ⟨convI hV ⟨(g : G), g.2.1⟩, (mem_autI hV).2 ⟨⟨(g : G), g.2.1⟩, hgK, rfl⟩, ?_⟩
    exact (TwelveShort.actTil_bot_eq_congr V hV g).symm
  · rintro ⟨χ, hχ, rfl⟩
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 hχ
    have hg0 : (g : G) ∈ normalizer (⊥ : Subgroup G) := by
      rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _
    let g' : stabTil (⊥ : Subgroup G) V := ⟨(g : G), ⟨g.2, hg0⟩⟩
    exact ⟨g', hgK, TwelveShort.actTil_bot_eq_congr V hV g'⟩

theorem actTil_bot_eq_one_iff (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g : stabTil (⊥ : Subgroup G) V) :
    actTil ⊥ V hV g = 1 ↔ (g : G) ∈ centralizer (V : Set G) := by
  rw [actTil_eq_one_iff, Subgroup.mem_centralizer_iff]
  refine forall₂_congr fun v _ => ?_
  rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, eq_comm]

theorem pCoreOf_le_centralizer_of_twoReduced {M V : Subgroup G}
    (hV : M ≤ normalizer (V : Set G)) (hred : TwoReduced M V) :
    pCoreOf 2 M ≤ centralizer (V : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hpc := (uc22br4_pCore_bot_iff M V hV).2 hred
  have hnorm := uc22br4_mbarImage_normal M V (pCoreOf 2 M) hPM
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hp : IsPGroup 2 ↥(mbarImage M V (pCoreOf 2 M)) :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).of_equiv
      (Subgroup.subgroupOfEquivOfLe hPM).symm).map _
  have hle : mbarImage M V (pCoreOf 2 M) ≤ CFSG.pCore 2 (MBar M V) := le_sSup ⟨hnorm, hp⟩
  rw [hpc, le_bot_iff] at hle
  exact (uc22br4_mbarImage_eq_bot_iff M V _ hV hPM).1 hle

theorem commutator_mem_pCoreOf {M L K A : Subgroup G} (hL : CFSG.Open.IsSubnormal L M)
    (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L)) (hKM : K ≤ M)
    (hKn : M ≤ normalizer (K : Set G)) (hPK : pCoreOf 2 M ≤ K) (hLK : ¬ L ≤ K)
    (hAM : A ≤ M) (hXA : ∀ x ∈ UC22.conjClosure M L, ∀ a ∈ A, ⁅x, a⁆ ∈ K) :
    ∀ x ∈ UC22.conjClosure M L, ∀ a ∈ A, ⁅x, a⁆ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  set π : ↥M →* UC22.Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ m : ↥M, π m = 1 ↔ (m : G) ∈ pCoreOf 2 M := by
    intro m
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem M.subtype_injective).symm
  have hKs : ((K.subgroupOf M).map π).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hKn).map π hπs
  have hLM : L ≤ M := hL.le
  have hXM : UC22.conjClosure M L ≤ M := TwelveTwentyThree.conjClosure_le hLM
  have hconj : ∀ g ∈ M, ∀ y ∈ L.map (MulAut.conj g).toMonoidHom, ∀ a ∈ A,
      ⁅y, a⁆ ∈ pCoreOf 2 M := by
    intro g hg
    have hLgX : L.map (MulAut.conj g).toMonoidHom ≤ UC22.conjClosure M L :=
      le_iSup₂_of_le (f := fun K (_ : K ∈ UC22.conjSetOf M L) => K) _ ⟨g, hg, rfl⟩ le_rfl
    have hLgM : L.map (MulAut.conj g).toMonoidHom ≤ M := hLgX.trans hXM
    set C := ((L.map (MulAut.conj g).toMonoidHom).subgroupOf M).map π
    have hLgK : ¬ L.map (MulAut.conj g).toMonoidHom ≤ K := by
      intro hle
      apply hLK
      intro l hl
      have h1 : g * l * g⁻¹ ∈ K := hle ⟨l, hl, by simp [MulAut.conj_apply]⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 (hKn (M.inv_mem hg)) _).1 h1
      simpa [mul_assoc] using h2
    have hCK : ¬ C ≤ (K.subgroupOf M).map π := by
      intro hle
      apply hLgK
      intro y hy
      have hyM := hLgM hy
      obtain ⟨k, hk, hkπ⟩ := hle ⟨⟨y, hyM⟩, hy, rfl⟩
      have h1 : π (k⁻¹ * ⟨y, hyM⟩) = 1 := by rw [map_mul, map_inv, hkπ, inv_mul_cancel]
      rw [hker] at h1
      have h2 : ((k⁻¹ * ⟨y, hyM⟩ : ↥M) : G) ∈ K := hPK h1
      have h3 : (k : G) ∈ K := hk
      have h4 : y = (k : G) * ((k⁻¹ * ⟨y, hyM⟩ : ↥M) : G) := by simp
      rw [h4]
      exact K.mul_mem h3 h2
    have hCne : C ≠ ⊥ := fun h0 => hCK (h0 ▸ bot_le)
    have hMg : M.map (MulAut.conj g).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
    have hLgsn : CFSG.Open.IsSubnormal (L.map (MulAut.conj g).toMonoidHom) M := by
      simpa only [hMg] using hL.map (MulAut.conj g).toMonoidHom
    have hCsn : CFSG.Open.IsSubnormal C ⊤ := by
      have h1 := (hLgsn.comap M.subtype).map π
      have e1 : M.comap M.subtype = ⊤ := Subgroup.subgroupOf_self M
      rw [e1, Subgroup.map_top_of_surjective π hπs] at h1
      exact h1
    let e := L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    let φ : ↥L →* ↥C := ((π.comp (Subgroup.inclusion hLgM)).comp e.toMonoidHom).codRestrict C
      (fun l => ⟨Subgroup.inclusion hLgM (e l), (e l).2, rfl⟩)
    have hφ : Function.Surjective φ := by
      rintro ⟨c, hc⟩
      obtain ⟨m, hm, rfl⟩ := hc
      obtain ⟨l, hl, hlm⟩ := hm
      refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
      show π (Subgroup.inclusion hLgM (e ⟨l, hl⟩)) = π m
      congr 1
      exact Subtype.ext hlm
    have hkerφ : CFSG.pCore 2 ↥L ≤ φ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      refine Subtype.ext ?_
      show π (Subgroup.inclusion hLgM (e x)) = 1
      rw [hker]
      have hxP : (x : G) ∈ pCoreOf 2 M := A4.pCoreOf_le_of_subnormal 2 hL ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg) _).1 hxP
    haveI : Nontrivial ↥C := (Subgroup.nontrivial_iff_ne_bot _).2 hCne
    let ψ : UC22.Bar2 L →* ↥C := QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hkerφ
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨x, rfl⟩ := hφ y
      exact ⟨QuotientGroup.mk x, rfl⟩
    have hCq : CFSG.Open.IsQuasisimple ↥C := uc22br4_isQuasisimple_of_surjective hLq ψ hψ
    have hCc : CFSG.IsComponent C := A3.isComponentOf_top_iff.1 ⟨le_top, hCsn, hCq⟩
    have hCKs : ⁅C, (K.subgroupOf M).map π⁆ = ⊥ :=
      (CFSG.LocalCores.component_normal_subgroup hCc hKs).resolve_left hCK
    have hCA : ⁅C, (A.subgroupOf M).map π⁆ ≤ (K.subgroupOf M).map π := by
      rw [Subgroup.commutator_le]
      rintro _ ⟨y, hy, rfl⟩ _ ⟨a, ha, rfl⟩
      rw [← map_commutatorElement]
      exact ⟨⁅y, a⁆, hXA _ (hLgX hy) _ ha, rfl⟩
    have h2 : ⁅⁅C, (A.subgroupOf M).map π⁆, C⁆ = ⊥ := by
      refine le_bot_iff.1 ((Subgroup.commutator_mono hCA le_rfl).trans ?_)
      rw [Subgroup.commutator_comm, hCKs]
    have h3 := CFSG.LocalCores.perfect_double_commutator hCc.1.1 h2
    intro y hy a ha
    have hmem : ⁅π ⟨y, hLgM hy⟩, π ⟨a, hAM ha⟩⁆ ∈ ⁅C, (A.subgroupOf M).map π⁆ :=
      Subgroup.commutator_mem_commutator ⟨⟨y, hLgM hy⟩, hy, rfl⟩ ⟨⟨a, hAM ha⟩, ha, rfl⟩
    rw [h3, Subgroup.mem_bot, ← map_commutatorElement, hker] at hmem
    exact hmem
  have hXZ : UC22.conjClosure M L ≤
      ((centralizer (((A.subgroupOf M).map π : Subgroup (UC22.Bar2 M)) : Set (UC22.Bar2 M))).comap
        π).map M.subtype := by
    refine iSup₂_le fun K' hK' => ?_
    obtain ⟨g, hg, rfl⟩ := hK'
    intro y hy
    have hyM : y ∈ M := (le_iSup₂_of_le (f := fun K (_ : K ∈ UC22.conjSetOf M L) => K) _
      ⟨g, hg, rfl⟩ le_rfl |>.trans hXM) hy
    refine Subgroup.mem_map.2 ⟨⟨y, hyM⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hconj g hg y hy (a : G) ha
    have h2 : π ⁅(⟨y, hyM⟩ : ↥M), a⁆ = 1 := (hker _).2 h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  intro x hx a ha
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 (hXZ hx)
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hm
  have h1 := hm (π ⟨a, hAM ha⟩) ⟨⟨a, hAM ha⟩, ha, rfl⟩
  have h2 : π ⁅m, (⟨a, hAM ha⟩ : ↥M)⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h1.symm
  exact (hker _).1 h2

theorem le_normalizer_wClos {V T X : Subgroup G} {i : ℕ}
    (h : ∀ x ∈ X, ∀ A ∈ E3.gammaSet V i T, ∀ a ∈ A, ⁅x, a⁆ ∈ T) :
    X ≤ normalizer (E3.wClos V i T : Set G) := by
  have key : ∀ x ∈ X, conjSubgroup (E3.wClos V i T) x ≤ E3.wClos V i T := by
    intro x hx
    rw [E3.conjSubgroup_le_iff_le_inv]
    refine E3.wClos_le_of_forall fun A hA => ?_
    rw [E3.le_conjSubgroup_iff_inv_le, inv_inv]
    refine E3.le_wClos ⟨?_, E3.gammaMember_conj x hA.2⟩
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have h1 := h x⁻¹ (X.inv_mem hx) A hA _ hy
    have h2 : y = ⁅x⁻¹, x * y * x⁻¹⁆ * (x * y * x⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact T.mul_mem h1 (hA.1 hy)
  intro x hx
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  refine le_antisymm (key x hx) ?_
  have := key x⁻¹ (X.inv_mem hx)
  rw [E3.conjSubgroup_le_iff_le_inv, inv_inv] at this
  exact this

end TwelveTwentyThree

theorem twelve_twentyThree_one (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ = ⊥) {L : Subgroup G} (hLM : CFSG.Open.IsSubnormal L D.M)
    (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L)) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hU : UniqueMax D.M (UC22.conjClosure D.M L)) :
    mBar D.M V₀ V h.isElemAbelian ≤
      bBar (UC22.conjClosure D.M L) D.M V₀ V h.isElemAbelian + D.k := by
  by_contra hlt
  rw [not_le] at hlt
  have hm : MBarGT D.M V₀ V (D.k + bBar (UC22.conjClosure D.M L) D.M V₀ V h.isElemAbelian) :=
    (h.mBarGT_iff_lt_mBar _).2 (by omega)
  have hm0 : MBarGT D.M V₀ V (D.k + 0) := (h.mBarGT_iff_lt_mBar _).2 (by omega)
  have h10 := twelve_ten_two D hx h61 h126 h111 h hV₀ hm0
  subst hV₀
  have hrk := mBar_le_rk (M := D.M) h.isElemAbelian (bot_le : (⊥ : Subgroup G) ≤ V)
  set X := UC22.conjClosure D.M L
  set b := bBar X D.M ⊥ V h.isElemAbelian
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  obtain ⟨hW, -⟩ : InCalWStar D.M D.T V ∧ (⊥ : Subgroup G) = ⊥ := by
    rcases h.1 with h1 | ⟨h0, -, -⟩
    · exact h1
    · exact absurd rfl h0.1.1
  have hV1 : InCalV1 D.M D.T V := hW.1.1
  have hVV : InCalV D.M V := hV1.1
  have hMN : D.M ≤ normalizer (V : Set G) := hVV.2.2.1
  have hred : TwoReduced D.M V := hW.1.2.2
  have hlt' : D.k + b < E3.sParam hV := by
    by_cases hm2 : MBarGT D.M ⊥ V 2
    · exact TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm2 hm
    · have hki : D.k + b = 1 := by
        have h1 := TwelveShort.one_le_k D
        by_contra hc
        exact hm2 (TwelveShort.mBarGT_mono hm (by omega))
      have hr : ((D.k + b : ℕ) : ℕ∞) < E3.rParam V := by
        have h1 := TwelveTen.one_lt_rMV D hx h61 hVV (by have := hW.1.2.1; omega)
        rw [rMV_eq_rParam_of_inCalV D hVV] at h1
        rw [hki]
        exact_mod_cast h1
      exact E3.lt_sParam_of_lt hV hr ((TwelveShort.mBarGT_bot_iff_lt_mParam_autI D hVV _).1 hm)
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTS : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D hTM
  have hT2 : IsPGroup 2 D.T := hTS.isPGroup
  have hTN : D.T ≤ normalizer (V : Set G) := hTM.trans hMN
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le hLM.le
  have hMS : D.M ≤ stabTil ⊥ V :=
    le_stabTil hMN (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hMbar : barSub ⊥ V hV D.M =
      (autI hV ⊤).map (MulAut.congr (TwelveShort.mkTilEquiv V hV)).toMonoidHom :=
    TwelveShort.barSub_bot_eq_map_congr D.M V hV (normalizer_eq_of_inCalV D hVV).symm
  have hcomm : ∀ A ∈ E3.gammaSet V D.k D.T, ∀ x ∈ X, ∀ a ∈ A,
      ⁅x, a⁆ ∈ D.M ⊓ centralizer (V : Set G) := by
    intro A hA x hxX a ha
    have hAM : A ≤ D.M := hA.1.trans hTM
    have hbar : ⁅barSub ⊥ V hV X, barSub ⊥ V hV A⁆ = ⊥ := by
      by_cases hA1 : autI hV A = ⊥
      · have h0 : barSub ⊥ V hV A = ⊥ := by
          rw [TwelveTwentyThree.barSub_bot_eq_map_autI V hV A, hA1,
            Subgroup.map_bot]
        rw [h0, Subgroup.commutator_bot_right]
      · have hmem := TwelveTwentyThree.autI_mem_aSet_of_mem_gammaSet hV hTN hlt' hA hA1
        have hA' : barSub ⊥ V hV A ∈ calABar (b + 1) D.M ⊥ V hV := by
          show barSub ⊥ V hV A ∈ E3.aSet (b + 1) (barSub ⊥ V hV D.M)
          rw [hMbar, TwelveTwentyThree.barSub_bot_eq_map_autI V hV A]
          exact (H.map_mem_aSet_iff _).2 hmem
        exact (bBar_lt_iff hV (Nat.succ_pos b)).1 (Nat.lt_succ_self b) _ hA'
    have hxS : x ∈ stabTil ⊥ V := hMS (hXM hxX)
    have haS : a ∈ stabTil ⊥ V := hMS (hAM ha)
    have hmem : ⁅actTil ⊥ V hV ⟨x, hxS⟩, actTil ⊥ V hV ⟨a, haS⟩⁆ ∈
        ⁅barSub ⊥ V hV X, barSub ⊥ V hV A⁆ :=
      Subgroup.commutator_mem_commutator (actTil_mem_barSub ⊥ V hV hxX hxS)
        (actTil_mem_barSub ⊥ V hV ha haS)
    rw [hbar, Subgroup.mem_bot, ← map_commutatorElement,
      TwelveTwentyThree.actTil_bot_eq_one_iff] at hmem
    refine ⟨?_, hmem⟩
    rw [commutatorElement_def]
    exact D.M.mul_mem (D.M.mul_mem (D.M.mul_mem (hXM hxX) (hAM ha)) (D.M.inv_mem (hXM hxX)))
      (D.M.inv_mem (hAM ha))
  have hKn : D.M ≤ normalizer ((D.M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
    A1a.le_normalizer_inf Subgroup.le_normalizer (A1a.le_normalizer_centralizer hMN)
  have hPK : pCoreOf 2 D.M ≤ D.M ⊓ centralizer (V : Set G) :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
      (TwelveTwentyThree.pCoreOf_le_centralizer_of_twoReduced hMN hred)
  have hLK : ¬ L ≤ D.M ⊓ centralizer (V : Set G) := by
    intro hle
    apply hL1
    refine le_bot_iff.1 fun φ hφ => ?_
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ V _ L φ).1 hφ
    rw [Subgroup.mem_bot, TwelveTwentyThree.actTil_bot_eq_one_iff]
    exact (hle hgL).2
  have hPT : pCoreOf 2 D.M ≤ D.T := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hTS.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)).2
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  have hN : X ≤ normalizer (E3.wClos V D.k D.T : Set G) := by
    refine TwelveTwentyThree.le_normalizer_wClos fun x hxX A hA a ha => hPT ?_
    exact TwelveTwentyThree.commutator_mem_pCoreOf hLM hLq inf_le_left hKn hPK hLK
      (hA.1.trans hTM) (hcomm A hA) x hxX a ha
  have hUN : InCalU D.M (D.M ⊓ normalizer (E3.wClos V D.k D.T : Set G)) :=
    InCalU.mono D.maxLocal hU (le_inf hXM hN) inf_le_left
  have hk : D.k < rk ↥V := by omega
  obtain ⟨h1, h2⟩ := six_fifteen_three hV D.maxLocal hT2 (TwelveShort.wClos_zero_ne_bot D hVV)
    hk hUN
  rcases h10 with h10 | h10
  · exact h10 (h1 0 (by omega))
  · exact h10 (by simpa using h2 0 (Nat.zero_le _))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
