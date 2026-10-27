module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndKey
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPushUp
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.Walter.Bender1970.S3.CoreExchangeTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem exists_maximal_two_le_M
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hAQ : F.A ≤ Subgroup.normalizer (Q : Set G)) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ F.A ≤ Subgroup.normalizer (S : Set G) ∧ Q ≤ S ∧
      S ≤ D.M ∧ CFSG.Open.pCoreOf 2 c.L ≤ S := by
  classical
  let fam : Set (Subgroup G) :=
    {S | IsPGroup 2 S ∧ F.A ≤ Subgroup.normalizer (S : Set G) ∧ Q ≤ S}
  have hne : fam.Nonempty := ⟨Q, hQ, hAQ, le_rfl⟩
  have hfin : fam.Finite := Set.toFinite fam
  obtain ⟨S, hSmax⟩ := hfin.exists_maximalFor (fun S : Subgroup G => Nat.card S) fam hne
  obtain ⟨hS2, hAS, hQS⟩ := hSmax.prop
  have hSM : S ≤ D.M := F.le_M_of_isPGroup_two hF hC hS2 hAS
  have hMO2 : D.M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    c.le_normalizer_L.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L)
  have hO2M : CFSG.Open.pCoreOf 2 c.L ≤ D.M :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L).trans c.hyp81.1
  have hO22 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 c.L
  have hSO2 : S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) := hSM.trans hMO2
  have hO2S : CFSG.Open.pCoreOf 2 c.L ≤ S := by
    have hsup2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 c.L ⊔ S) :=
      IsPGroup.to_sup_of_normal_left' hO22 hS2 hSO2
    have hAsup : F.A ≤
        Subgroup.normalizer ((CFSG.Open.pCoreOf 2 c.L ⊔ S : Subgroup G) : Set G) :=
      (le_inf (F.A_le_M.trans hMO2) hAS).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    have hsupfam : CFSG.Open.pCoreOf 2 c.L ⊔ S ∈ fam :=
      ⟨hsup2, hAsup, hQS.trans le_sup_right⟩
    have hcard : Nat.card ↥(CFSG.Open.pCoreOf 2 c.L ⊔ S) ≤ Nat.card ↥S := hSmax.le hsupfam
    have heq : CFSG.Open.pCoreOf 2 c.L ⊔ S = S :=
      (Subgroup.eq_of_le_of_card_ge le_sup_right hcard).symm
    rw [← heq]
    exact le_sup_left
  exact ⟨S, hS2, hAS, hQS, hSM, hO2S⟩

private theorem pCoreOf_le_inf_ker (F : A10Frame c) {S : Subgroup G}
    (hO2S : CFSG.Open.pCoreOf 2 c.L ≤ S) :
    CFSG.Open.pCoreOf 2 c.L ≤ S ⊓ F.phiA.ker.map D.M.subtype := by
  refine le_inf hO2S fun x hx => ?_
  have hxL : x ∈ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L hx
  have hxM : x ∈ D.M := c.hyp81.1 hxL
  have himg : F.phiA ⟨x, hxM⟩ = 1 := by
    refine (F.phiA_eq_one_iff hxL).mpr ?_
    simpa [CFSG.Open.pCoreOf] using hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, himg, rfl⟩

private theorem map_inf_ker_eq_bot (F : A10Frame c) {S : Subgroup G} :
    ((S ⊓ F.phiA.ker.map D.M.subtype).subgroupOf D.M).map F.phiA = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
  have hrR : (r : G) ∈ S ⊓ F.phiA.ker.map D.M.subtype := Subgroup.mem_subgroupOf.mp hr
  obtain ⟨m, hm, hmr⟩ := Subgroup.mem_map.mp hrR.2
  have hms : m = r := Subtype.ext hmr
  rw [← hms]
  exact hm

private theorem relIndex_inf_ker_le_four (F : A10Frame c) {S : Subgroup G}
    (hSM : S ≤ D.M) (hS2 : IsPGroup 2 S) (hAS : F.A ≤ Subgroup.normalizer (S : Set G)) :
    (S ⊓ F.phiA.ker.map D.M.subtype).relIndex S ≤ 4 := by
  classical
  obtain ⟨k, hWk⟩ := F.exists_map_le_kleinV hSM hS2 hAS
  let R : Subgroup G := S ⊓ F.phiA.ker.map D.M.subtype
  change R.relIndex S ≤ 4
  have hRS : R ≤ S := inf_le_left
  let ψ : ↥S →* Equiv.Perm (Fin 10) := F.phiA.comp (Subgroup.inclusion hSM)
  have hker : ψ.ker = R.subgroupOf S := by
    ext s
    change F.phiA ⟨(s : G), hSM s.2⟩ = 1 ↔ (s : G) ∈ R
    simp only [R, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · intro h
      exact ⟨s.2, ⟨⟨(s : G), hSM s.2⟩, h, rfl⟩⟩
    · rintro ⟨-, ⟨m, hm, hmr⟩⟩
      rw [show m = ⟨(s : G), hSM s.2⟩ from Subtype.ext hmr] at hm
      exact hm
  have hrange : ψ.range = (S.subgroupOf D.M).map F.phiA := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact s.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hW4 : Nat.card ↥((S.subgroupOf D.M).map F.phiA) ≤ 4 := by
    have hdvd : Nat.card ↥((S.subgroupOf D.M).map F.phiA) ∣ Nat.card (A10Perm.kleinV k) :=
      Subgroup.card_dvd_of_le hWk
    rw [A10Perm.card_kleinV] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hkerR : Nat.card ↥(R.subgroupOf S) = Nat.card ↥R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv
  have hcardψ := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange, hkerR] at hcardψ
  have hrelcard : R.relIndex S * Nat.card ↥R = Nat.card ↥S := by
    have h := Subgroup.relIndex_mul_card R S
    rwa [inf_eq_left.mpr hRS] at h
  have hpos : 0 < Nat.card ↥R :=
    Nat.pos_of_ne_zero (Nat.card_ne_zero.mpr ⟨⟨1, R.one_mem⟩, inferInstance⟩)
  have heqrel : R.relIndex S = Nat.card ↥((S.subgroupOf D.M).map F.phiA) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hrelcard,
      mul_comm (Nat.card ↥((S.subgroupOf D.M).map F.phiA)) (Nat.card ↥R), hcardψ]
  simpa [heqrel] using hW4

private theorem iSup_conj_le_normalizer {V Z : Subgroup G} (hZV : Z ≤ V) (hZne : Z ≠ ⊥)
    (hLV : c.L ≤ Subgroup.normalizer (V : Set G)) :
    (⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom) ≤ V ∧
      (⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom) ≠ ⊥ ∧
      c.L ≤ Subgroup.normalizer
        ((⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom : Subgroup G) : Set G) := by
  have hUV : (⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom) ≤ V := by
    refine iSup_le fun l => ?_
    rintro x ⟨z, hz, rfl⟩
    have hzV : z ∈ V := hZV hz
    have := (Subgroup.mem_normalizer_iff.mp (hLV l.2) z).mp hzV
    simpa [MulAut.conj_apply] using this
  have hZU : Z ≤ ⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom := by
    refine le_trans ?_ (le_iSup (fun l : c.L => Z.map (MulAut.conj (l : G)).toMonoidHom) 1)
    intro z hz
    exact Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩
  have hUne : (⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom) ≠ ⊥ :=
    fun h => hZne (le_bot_iff.mp (hZU.trans (le_of_eq h)))
  have hmapU : ∀ l : c.L,
      (⨆ l' : c.L, Z.map (MulAut.conj (l' : G)).toMonoidHom).map
        (MulAut.conj (l : G)).toMonoidHom ≤
        ⨆ l' : c.L, Z.map (MulAut.conj (l' : G)).toMonoidHom := by
    intro l
    rw [Subgroup.map_iSup]
    refine iSup_le fun l' => ?_
    rw [Subgroup.map_map]
    have hterm :
        Z.map ((MulAut.conj (l : G)).toMonoidHom.comp (MulAut.conj (l' : G)).toMonoidHom) =
          Z.map (MulAut.conj ((l * l' : c.L) : G)).toMonoidHom := by
      congr 1
      ext x
      change (MulAut.conj (l : G)) ((MulAut.conj (l' : G)) x) =
        (MulAut.conj ((l : G) * (l' : G))) x
      rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hterm]
    exact le_iSup (fun l'' : c.L => Z.map (MulAut.conj (l'' : G)).toMonoidHom) (l * l')
  have hLU : c.L ≤ Subgroup.normalizer
      ((⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun l hl u hu => ?_
    have hmem : (MulAut.conj (l : G)).toMonoidHom u ∈
        (⨆ l' : c.L, Z.map (MulAut.conj (l' : G)).toMonoidHom).map
          (MulAut.conj (l : G)).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have := hmapU ⟨l, hl⟩ hmem
    simpa [MulAut.conj_apply] using this
  exact ⟨hUV, hUne, hLU⟩

private theorem le_centralizer_iSup_conj {Z R : Subgroup G}
    (hZR : Z ≤ Subgroup.centralizer (R : Set G))
    (hLR : c.L ≤ Subgroup.normalizer (R : Set G)) :
    R ≤ Subgroup.centralizer
      ((⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom : Subgroup G) : Set G) := by
  have hZmapC : ∀ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom ≤
      Subgroup.centralizer (R : Set G) := by
    intro l
    have hCmap : (Subgroup.centralizer (R : Set G)).map
        (MulAut.conj (l : G)).toMonoidHom = Subgroup.centralizer (R : Set G) := by
      rw [CFSG.Walter.map_centralizer_mulEquiv]
      congr 1
      ext x
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hLR l.2) r).mp hr
      · intro hx
        refine ⟨l⁻¹ * x * l, ?_, ?_⟩
        · simpa [Subgroup.coe_inv] using
            (Subgroup.mem_normalizer_iff.mp (hLR (Subgroup.inv_mem _ l.2)) x).mp hx
        · rw [MulAut.conj_apply]
          simp only [Subgroup.coe_inv]
          group
    calc Z.map (MulAut.conj (l : G)).toMonoidHom
        ≤ (Subgroup.centralizer (R : Set G)).map (MulAut.conj (l : G)).toMonoidHom :=
          Subgroup.map_mono hZR
      _ = Subgroup.centralizer (R : Set G) := hCmap
  rw [Subgroup.le_centralizer_iff]
  exact iSup_le hZmapC

private theorem inf_centralizer_ne_bot_of_two (F : A10Frame c) {V S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSM : S ≤ D.M) (hV : UC22.InCalV D.M V) :
    V ⊓ Subgroup.centralizer (S : Set G) ≠ ⊥ :=
  CFSG.Walter.inf_centralizer_ne_bot_of_isPGroup Nat.prime_two hS2 hV.2.2.2.isPGroup
    (hSM.trans hV.2.2.1) hV.1

private theorem relIndex_centralizer_le_four {Q R S : Subgroup G} {w : G}
    (hQRw : Q ⊓ R ≤ Subgroup.centralizer ({w} : Set G)) (hQS : Q ≤ S)
    (hrel : R.relIndex S ≤ 4) :
    (Subgroup.centralizer ({w} : Set G)).relIndex Q ≤ 4 := by
  have hne1 : (Q ⊓ R).relIndex Q ≠ 0 := by
    intro h0
    have hc := Subgroup.relIndex_mul_card (Q ⊓ R) Q
    rw [h0, zero_mul] at hc
    exact (Nat.card_ne_zero.mpr ⟨⟨1, Q.one_mem⟩, inferInstance⟩) hc.symm
  have hne2 : R.relIndex S ≠ 0 := by
    intro h0
    have hc := Subgroup.relIndex_mul_card R S
    rw [h0, zero_mul] at hc
    exact (Nat.card_ne_zero.mpr ⟨⟨1, S.one_mem⟩, inferInstance⟩) hc.symm
  have step1 : (Subgroup.centralizer ({w} : Set G)).relIndex Q ≤ (Q ⊓ R).relIndex Q :=
    Subgroup.relIndex_le_of_le_left hQRw hne1
  have step2 : (Q ⊓ R).relIndex Q ≤ R.relIndex Q := by
    have h := Subgroup.relIndex_inf_le (H := R) (K := Q) (L := Q)
    rw [Subgroup.relIndex_self] at h
    simpa [inf_comm, mul_one] using h
  have step3 : R.relIndex Q ≤ R.relIndex S :=
    Subgroup.relIndex_le_of_le_right hQS hne2
  exact step1.trans (step2.trans (step3.trans hrel))

theorem exists_le_relIndex_le_four
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {V : Subgroup G} (hV : UC22.InCalV D.M V) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hAQ : F.A ≤ Subgroup.normalizer (Q : Set G)) :
    ∃ U : Subgroup G, U ≤ V ∧ U ≠ ⊥ ∧ c.L ≤ Subgroup.normalizer (U : Set G) ∧
      ∀ w ∈ U, (Subgroup.centralizer ({w} : Set G)).relIndex Q ≤ 4 := by
  classical
  obtain ⟨S, hS2, hAS, hQS, hSM, hO2S⟩ := exists_maximal_two_le_M F hF hC hQ hAQ
  let R : Subgroup G := S ⊓ F.phiA.ker.map D.M.subtype
  have hRS : R ≤ S := inf_le_left
  have hO2R : CFSG.Open.pCoreOf 2 c.L ≤ R := pCoreOf_le_inf_ker F hO2S
  have hR1 : (R.subgroupOf D.M).map F.phiA = ⊥ := map_inf_ker_eq_bot F
  have hLR : c.L ≤ Subgroup.normalizer (R : Set G) :=
    F.L_le_normalizer (hRS.trans hSM) hR1 hO2R
  have hrel : R.relIndex S ≤ 4 := relIndex_inf_ker_le_four F hSM hS2 hAS
  let Z : Subgroup G := V ⊓ Subgroup.centralizer (S : Set G)
  have hZne : Z ≠ ⊥ := inf_centralizer_ne_bot_of_two F hS2 hSM hV
  have hZV : Z ≤ V := inf_le_left
  have hLV : c.L ≤ Subgroup.normalizer (V : Set G) := c.hyp81.1.trans hV.2.2.1
  obtain ⟨hUV, hUne, hLU⟩ := iSup_conj_le_normalizer hZV hZne hLV
  have hZR : Z ≤ Subgroup.centralizer (R : Set G) :=
    (inf_le_right : Z ≤ Subgroup.centralizer (S : Set G)).trans
      (Subgroup.centralizer_le (by intro x hx; exact hRS hx))
  have hRU : R ≤ Subgroup.centralizer
      ((⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom : Subgroup G) : Set G) :=
    le_centralizer_iSup_conj hZR hLR
  refine ⟨⨆ l : c.L, Z.map (MulAut.conj (l : G)).toMonoidHom, hUV, hUne, hLU, ?_⟩
  intro w hw
  have hCRw : R ≤ Subgroup.centralizer ({w} : Set G) :=
    hRU.trans (Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rwa [hx]))
  have hQRw : Q ⊓ R ≤ Subgroup.centralizer ({w} : Set G) := inf_le_right.trans hCRw
  exact relIndex_centralizer_le_four hQRw hQS hrel

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
