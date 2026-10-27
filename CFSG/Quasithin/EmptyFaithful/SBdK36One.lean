module

public import CFSG.Quasithin.EmptyFaithful.SBdK36Gen
public import CFSG.Quasithin.EmptyFaithful.SBdK36Model
public import CFSG.Quasithin.EmptyFaithful.S153IClose

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace SBd

theorem O2Z_le_oTwoPhi {G : Type} [Group G] [Finite G] {Y H : Subgroup G} (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hP : IsPOnePlusTwo 3 (OTwoQuot Y)) :
    O2Z Y ≤ oTwoPhi H := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_imageOTwoQuot hYH hHY
  have hP' : IsPOnePlusTwo 3 ↥(imageOTwoQuot H Y) := A36B.isPOnePlusTwo_of_mulEquiv φ hP
  have hΦ : frattini ↥(imageOTwoQuot H Y) = Subgroup.center ↥(imageOTwoQuot H Y) :=
    A1c.frattini_eq_center_of_isPOnePlusTwo hP'
  have hNnorm : (imageOTwoQuot H Y).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    have h := imageOTwoQuot_le_normalizer (M := H) (X := H) (Y := Y) le_rfl hHY
    rw [imageOTwoQuot_self'] at h
    exact top_le_iff.mp h
  intro y hy
  obtain ⟨hyY, hyc⟩ := mem_O2Z_iff.mp hy
  have hcen : φ (QuotientGroup.mk ⟨y, hyY⟩) ∈ Subgroup.center ↥(imageOTwoQuot H Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subgroup.mem_center_iff.mp hyc a)
  rw [← hΦ] at hcen
  have hmem := frattini_map_le_of_normal (imageOTwoQuot H Y) ⟨_, hcen, rfl⟩
  rw [mem_oTwoPhi_iff]
  refine ⟨hYH hyY, ?_⟩
  have := hφ ⟨y, hyY⟩
  rw [← this]
  exact hmem

theorem input15336OneCaseOne_proved (h113 : StageLemma14113) : Input15336OneCaseOne := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hr hY I hI
  subst hY
  have hh : Hyp153 G T Mc M := h.hyp
  have D : Decomp153 T M V₁ V₂ t := h.decomp
  have hYM : Y153 Mc M ≤ M := Y153_le Mc M
  have hTM : T ≤ M := hh.T_le
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := hh.le_normalizer
  have hTY : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) := hTM.trans (le_normalizer_Y153 Mc M)
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) := hh.T_le_normalizer_Sgp153 D
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hTM
  have hSY : Sgp153 T V₁ ≤ Subgroup.normalizer (Y153 Mc M : Set G) := inf_le_left.trans hTY
  have hYSH : Y153 Mc M ⊔ Sgp153 T V₁ ≤ M := sup_le hYM hSM
  have hHN : Y153 Mc M ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (VZ T M : Set G) := hYSH.trans hMV
  have hsylbar := hh.isSylowTwoOf_autI
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -, -⟩ := D.model
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := hh.autOn_Y153 h113
  have hX : autI hV (Y153 Mc M ⊔ Sgp153 T ((commV L₁).map (inclMod hV))) = L₁ ⊔ L₂ :=
    autI_sup_nS_eq hV hS hsylbar hTM hMV hYM hYbar
  obtain ⟨e, -, -⟩ := exists_mulEquiv_sup_perm hS
  set H : Subgroup G := Y153 Mc M ⊔ Sgp153 T ((commV L₁).map (inclMod hV)) with hHdef
  let ρ : ↥H →* MulAut (IntMod (VZ T M) hV) := convHom hV H hHN
  have hρr : ρ.range = L₁ ⊔ L₂ := (range_convHom hV H hHN).trans hX
  have hρmem : ∀ x : ↥H, ρ x ∈ L₁ ⊔ L₂ := fun x => by
    have : ρ x ∈ ρ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
    rwa [hρr] at this
  let ρ' : ↥H →* ↥(L₁ ⊔ L₂) := ρ.codRestrict (L₁ ⊔ L₂) hρmem
  let φ : ↥H →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) := e.toMonoidHom.comp ρ'
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨l, rfl⟩ := e.surjective q
    have : (l : MulAut (IntMod (VZ T M) hV)) ∈ ρ.range := by rw [hρr]; exact l.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, by simp [φ, ρ', hx]⟩
  have hφk : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) := by
    intro x
    have h1 : φ x = 1 ↔ ρ x = 1 := by
      constructor
      · intro h
        have : ρ' x = 1 := e.injective (by simpa [φ] using h)
        exact congrArg Subtype.val this
      · intro h
        have : ρ' x = 1 := Subtype.ext h
        simp [φ, this]
    rw [h1]
    exact convI_eq_one_iff hV ⟨x, hHN x.2⟩
  have hRC : pCoreOf 2 H ≤ Subgroup.centralizer (VZ T M : Set G) := by
    have hTH : T ≤ Subgroup.normalizer (H : Set G) := F1.le_normalizer_sup hTY hTS
    have hTR : T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      hTH.trans (normalizer_le_normalizer_pCoreOf 2 H)
    have hYR : Y153 Mc M ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      le_sup_left.trans (le_normalizer_pCoreOf 2 H)
    have hYTR : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := sup_le hYR hTR
    have hRM : pCoreOf 2 H ≤ M := (pCoreOf_le 2 H).trans hYSH
    have hRN : pCoreOf 2 H ≤ Subgroup.normalizer (VZ T M : Set G) := hRM.trans hMV
    have hYTN : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (VZ T M : Set G) :=
      sup_le (hYM.trans hMV) (hTM.trans hMV)
    have hnorm : autOn (Y153 Mc M ⊔ T) (VZ T M) ≤
        Subgroup.normalizer (autOn (pCoreOf 2 H) (VZ T M) : Set (MulAut ↥(VZ T M))) :=
      autOn_le_normalizer_autOn hYTN hRN hYTR
    rw [hh.autOn_Y153_sup_T h113] at hnorm
    have hbot : autI hV (pCoreOf 2 H) = ⊥ :=
      hS.eq_bot_of_normal_isPGroup hsylbar (autI_mono hV hRM) hnorm
        (B2F.isPGroup_autI hV (pCoreOf_isPGroup 2 H) hRN)
    exact (autI_eq_bot_iff hV hRN).1 hbot
  have hle1 : oTwoPhi H ≤ H ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    intro x hx
    have hO : CFSG.Open.pCore 2 ↥H ≤ φ.ker := by
      intro z hz
      rw [MonoidHom.mem_ker, hφk]
      exact hRC ((Subgroup.mem_map_iff_mem H.subtype_injective).mpr hz)
    obtain ⟨hxH, h1⟩ := oTwoPhi_le_ker H φ hφs hO frattini_perm_three_prod hx
    exact ⟨hxH, (hφk ⟨x, hxH⟩).mp h1⟩
  have hPR : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 H := by
    have hP : pCoreOf 2 (Y153 Mc M ⊔ T) = T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
      hh.lemma_15_3_7_pCore h113
    have hV₁V : ((commV L₁).map (inclMod hV) : Subgroup G) ≤ VZ T M := map_inclMod_le hV _
    have hPS : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ Sgp153 T ((commV L₁).map (inclMod hV)) :=
      inf_centralizer_le_nS T _ hV₁V
    have hHYT : H ≤ Y153 Mc M ⊔ T := sup_le_sup_left inf_le_left _
    have hHP : H ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) :
        Set G) := by
      rw [← hP]
      exact hHYT.trans (le_normalizer_pCoreOf 2 _)
    exact le_pCoreOf_of_le_normalizer 2 (hPS.trans le_sup_right) hHP (hP ▸ pCoreOf_isPGroup 2 _)
  have hle2 : H ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ oTwoPhi H := by
    rintro x ⟨hxH, hxC⟩
    obtain ⟨a, haY, b, hbS, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hSY).1 hxH
    have haN : a ∈ Subgroup.normalizer (VZ T M : Set G) := hMV (hYM haY)
    have hbN : b ∈ Subgroup.normalizer (VZ T M : Set G) := hMV (hSM hbS)
    have h1 : convI hV ⟨a, haN⟩ * convI hV ⟨b, hbN⟩ = 1 := by
      rw [← map_mul]
      have : (⟨a, haN⟩ * ⟨b, hbN⟩ : Subgroup.normalizer (VZ T M : Set G)) =
          ⟨x, hMV (hYSH hxH)⟩ := Subtype.ext hab.symm
      rw [this]
      exact (convI_eq_one_iff hV _).2 hxC
    have habar : convI hV ⟨a, haN⟩ ∈ oTwoUpper (autI hV M) := hYbar ▸ convI_mem_autI hV haY haN
    have hT2 : IsPGroup 2 ↥T := hh.isSylowTwoOf.2.1
    have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := hTM.trans hMV
    have hbTbar : convI hV ⟨b, hbN⟩ ∈ autI hV T := convI_mem_autI hV hbS.1 hbN
    obtain ⟨k, hk⟩ := B2F.isPGroup_autI hV hT2 hTN ⟨convI hV ⟨b, hbN⟩, hbTbar⟩
    have hdvd : orderOf (convI hV ⟨b, hbN⟩) ∣ 2 ^ k := by
      refine orderOf_dvd_of_pow_eq_one ?_
      simpa using congrArg Subtype.val hk
    have hodd : Odd (orderOf (convI hV ⟨b, hbN⟩)) := by
      have := hS.odd_orderOf_of_mem_oTwoUpper habar
      rwa [eq_inv_of_mul_eq_one_left h1, orderOf_inv] at this
    have hcop : Nat.Coprime (orderOf (convI hV ⟨b, hbN⟩)) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
    have hord1 : orderOf (convI hV ⟨b, hbN⟩) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    have hb1 : convI hV ⟨b, hbN⟩ = 1 := orderOf_eq_one_iff.mp hord1
    have ha1 : convI hV ⟨a, haN⟩ = 1 := by
      rw [eq_inv_of_mul_eq_one_left h1, hb1, inv_one]
    have haC : a ∈ Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV _).1 ha1
    have hbC : b ∈ Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV _).1 hb1
    have hbR : b ∈ oTwoPhi H := pCoreOf_le_oTwoPhi H (hPR ⟨hbS.1, hbC⟩)
    have haΦ : a ∈ oTwoPhi H := by
      rcases hh.lemma_15_3_7_cases h113 with ⟨hP1, -⟩ | ⟨hP2, hO2⟩
      · have : a ∈ pCoreOf 2 (Y153 Mc M) := by rw [hP1]; exact ⟨haY, haC⟩
        have hYH : Y153 Mc M ≤ H := le_sup_left
        have hHYn : H ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
          sup_le Subgroup.le_normalizer hSY
        exact pCoreOf_le_oTwoPhi H
          (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hYH)
            (hHYn.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _) this)
      · exact O2Z_le_oTwoPhi le_sup_left (sup_le Subgroup.le_normalizer hSY) hP2
          (by rw [hO2]; exact ⟨haY, haC⟩)
    rw [hab]
    exact (oTwoPhi H).mul_mem haΦ hbR
  have hkey : H ⊓ Subgroup.centralizer (VZ T M : Set G) = oTwoPhi H := le_antisymm hle2 hle1
  refine ⟨φ, hφs, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf, ← hkey, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

end SBd

end CFSG.Quasithin
