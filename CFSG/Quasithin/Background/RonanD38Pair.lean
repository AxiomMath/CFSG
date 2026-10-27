module

public import CFSG.Quasithin.Background.RonanD38Sz
public import CFSG.Quasithin.Background.RonanD38Restrict

public section

namespace CFSG.Quasithin.RonanD38

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch10.SecA

section General

variable {W : Type} [CommGroup W]

theorem card_autSub_dvd {X : Subgroup (MulAut W)} {U : Subgroup W} (hX : X ≤ stabSub U) :
    Nat.card ↥(autSub X U) ∣ Nat.card ↥X :=
  Dvd.intro _ (card_autSub_mul hX)

end General

section Pair

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d38_exists_ne (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hV0 : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hL38 : A38Types ↥L) :
    ∃ l ∈ L, ∃ v ∈ V, l v ≠ v := by
  obtain ⟨hVne, -, hcommV⟩ := insp5a_V_facts hD htT htL hMp hV0 hL38
  by_contra hcon
  push Not at hcon
  apply hVne
  rw [← hcommV, commSub_eq_bot_iff.mpr fun v hv l hl => hcon l hl v hv]

theorem d38_normalizes (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hV0 : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hL38 : A38Types ↥L) :
    (Mp ⊔ T) ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  obtain ⟨hVne, hstab, hcommV⟩ := insp5a_V_facts hD htT htL hMp hV0 hL38
  have hMpN := insp5a_Mp_le_normalizer hD htT htL hMp hL38
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    hD.Mp_eq ▸ le_normalizer_conjClosure L T
  have hS : ∀ s ∈ T, s ∈ stabSub V → s ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro s hsT hsV
    by_contra hsn
    have hLs : conjAutSub s L = conjAutSub t L :=
      (insp5a_conj_cases hD htT hMp hL38 s hsT).resolve_left fun h =>
        hsn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hfix : V ≤ fixV L := by
      intro v hv l hl
      have hsl : s * l * s⁻¹ ∈ conjAutSub t L := by
        rw [← hLs]
        exact ⟨l, hl, by simp [MulAut.conj_apply]⟩
      have h := hV0 (s v) ((hsV v).2 hv) _ hsl
      simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h
      exact s.injective h
    exact hVne (by rw [← hcommV, commSub_eq_bot_iff.mpr hfix])
  intro y hy
  obtain ⟨hyMT, hyV⟩ := Subgroup.mem_inf.mp hy
  have hy' : y ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hyMT
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T hTn] at hy'
  obtain ⟨m, hm, s, hs, rfl⟩ := hy'
  have hsV : s ∈ stabSub V := by
    have : m⁻¹ * (m * s) ∈ stabSub V :=
      (stabSub V).mul_mem ((stabSub V).inv_mem (hstab hm)) hyV
    simpa using this
  exact (Subgroup.normalizer (L : Set (MulAut W))).mul_mem (hMpN hm) (hS s hs hsV)

theorem d38_qsec (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hV0 : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hL38 : A38Types ↥L)
    (hN : (Mp ⊔ T) ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    InternalSec.QSec (autSub (Mp ⊔ T) V) (autSub L V) ((V ⊓ fixV Mp).subgroupOf V) := by
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hact := insp5a_sec_act hD hMp hV0 hN
  have hns : ¬ Group.IsSolvable ↥L := not_isSolvable_of_mem_cComp hD.comp
  have hex := d38_exists_ne hD htT htL hMp hV0 hL38
  have hne : autSub L V ≠ ⊥ := autSub_ne_bot_of_exists hLs le_rfl hex
  have hle : autSub L V ≤ autSub (Mp ⊔ T) V :=
    autSub_mono ((insp5a_sec_L_le_Mp hD).trans le_sup_left) V
  have hstab := insp5a_sec_stab hD
  have hfix := insp5a_sec_fix hD
  have hsimple := insp5a_sec_isSimpleGroup hL38
  have hO2 : pCoreOf 2 (autSub L V) = ⊥ := pCoreOf_autSub_eq_bot_of_isSimple hLs hns hne
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.exp])
  have hfaith : L ⊓ centSub V = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hsimple hLs fun h => by
    obtain ⟨l, hl, v, hv, hlv⟩ := hex
    exact hlv (h hl v hv)
  let e := autSubEquivOfFaithful hLs hfaith
  exact
    { le := hle
      normal := insp5a_sec_normal hN
      two := insp5a_sec_two hD hact hN
      stab := hstab
      fix := hfix
      comm := insp5a_sec_comm hLs (insp5a_sec_commSub_eq hD hact)
      lt := insp5a_sec_lt hD
      irr := insp5a_sec_irr hD hact
      faithful := InternalSec.inf_centSec_eq_bot_of_pCoreOf hexp (hle.trans hstab) hfix hO2
      quasi := CFSG.LocalCores.isQuasisimple_of_mulEquiv e (insp5a_sec_isQuasisimple hD hL38) }

theorem d38_sqtk (hA21 : AsA21SQTKSection) (hD : D31 M Mp T L V)
    (hex : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v) (hL38 : A38Types ↥L) : SQTKGroup ↥(autSub L V) := by
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hLq : CFSG.IsQuasisimple ↥L := insp5a_sec_isQuasisimple hD hL38
  have hq : CFSG.IsQuasisimple ↥(autSub L V) := lred3_isQuasisimple_autSub hLs hLq hex
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hD.qsqtk
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
  have hSL : SQTKGroup ↥L := B69.sqtk_subgroup hA21 hS φ hφ (le_of_mem_cComp hD.comp) hLq
  exact B69.sqtk_autSub hA21 hLs hSL hq

theorem d38_pair
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Facts10_1) (hD : D3Std M Mp T L V)
    (htT : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) {n : ℕ} (hszL : CFSG.Blueprint.SuzukiModel ↥L 2 n)
    (hc : D36cConcl Mp T L V t) :
    BinaryNaturalSz L V (V ⊓ fixV L) n ∧
      IsSumMod (orbSup T V ⊓ fixV Mp) V (V.map t.toMonoidHom) (orbSup T V) ∧
      V = commSub (orbSup T V) L ∧ V ≤ fixV (conjAutSub t L) ∧
      fixV (conjAutSub t L) ⊓ orbSup T V = V ⊔ (orbSup T V ⊓ fixV Mp) := by
  have h3 : ¬ 3 ∣ Nat.card ↥L :=
    CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hszL
  have hL38 : A38Types ↥L := Or.inr (Or.inl ⟨n, hszL⟩)
  have hLs : IsSimpleGroup ↥L := insp5a_sec_isSimpleGroup hL38
  have hLMp : L ≤ Mp := insp5a_sec_L_le_Mp hD.hyp
  have hLtMp : conjAutSub t L ≤ Mp := le_of_le_of_eq le_sup_right hMp.symm
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := insp5a_sec_T_le_normalizer hD.hyp
  have hLY : L ≤ stabSub (orbSup T V) := (hLMp.trans le_sup_left).trans (d38r_sup_le_stabSub hD)
  obtain ⟨hV0, ⟨hsum0, -⟩, hqU, hU⟩ := hc
  have hUV : commSub (orbSup T V) L = V := hU.resolve_right fun h =>
    h3 (dvd_trans (H13.three_dvd_card_of_isPSL_three_two h.1) (card_autSub_dvd hLY))
  have hsum : IsSumMod (orbSup T V ⊓ fixV Mp) V (V.map t.toMonoidHom) (orbSup T V) := by
    have h := hsum0
    rw [hUV] at h
    exact h
  have hVfix : V ≤ fixV (conjAutSub t L) := fun v hv g hg => hV0 v hv g hg
  have key : ∀ y ∈ V.map t.toMonoidHom, y ∈ fixV (conjAutSub t L) →
      y ∈ orbSup T V ⊓ fixV Mp := by
    rintro _ ⟨v₀, hv₀, rfl⟩ hy
    have hv₀L : v₀ ∈ fixV L := by
      intro l hl
      have h1 := hy (t * l * t⁻¹) (H13.conj_mem_conjAutSub hl)
      simp only [MulAut.mul_apply, MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self] at h1
      exact t.injective h1
    have hv₀Mp : v₀ ∈ fixV Mp := by
      rw [hMp, fixV_sup_eq_inf_fixV]
      exact ⟨hv₀L, hVfix hv₀⟩
    refine ⟨map_le_orbSup htT ⟨v₀, hv₀, rfl⟩, fun m hm => ?_⟩
    have hm' : t⁻¹ * m * t ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (hTn htT) m).mp hm
    have h2 := hv₀Mp _ hm'
    simp only [MulAut.mul_apply] at h2
    show m (t v₀) = t v₀
    have h3 : t (t⁻¹ (m (t v₀))) = t v₀ := by rw [h2]
    simpa using h3
  have hfixeq : fixV (conjAutSub t L) ⊓ orbSup T V = V ⊔ (orbSup T V ⊓ fixV Mp) := by
    apply le_antisymm
    · rintro x ⟨hxf, hxY⟩
      have hxY' : x ∈ V ⊔ V.map t.toMonoidHom ⊔ (orbSup T V ⊓ fixV Mp) := by
        rw [← hsum.1]
        exact hxY
      obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup.mp hxY'
      obtain ⟨v, hv, v', hv', rfl⟩ := Subgroup.mem_sup.mp hy
      have hcf : c ∈ fixV (conjAutSub t L) := fun g hg => hc.2 g (hLtMp hg)
      have hvf : v ∈ fixV (conjAutSub t L) := hVfix hv
      have hv'f : v' ∈ fixV (conjAutSub t L) := by
        have e : v' = v⁻¹ * (v * v' * c) * c⁻¹ := by group
        rw [e]
        exact (fixV _).mul_mem ((fixV _).mul_mem ((fixV _).inv_mem hvf) hxf) ((fixV _).inv_mem hcf)
      have hv'C := key v' hv' hv'f
      rw [mul_assoc]
      exact Subgroup.mul_mem_sup hv ((orbSup T V ⊓ fixV Mp).mul_mem hv'C hc)
    · exact sup_le (le_inf hVfix (le_orbSup T V))
        (le_inf (fun c hc g hg => hc.2 g (hLtMp hg)) inf_le_left)
  have hN := d38_normalizes hD.hyp htT htn hMp hV0 hL38
  have hex := d38_exists_ne hD.hyp htT htn hMp hV0 hL38
  have hQ := d38_qsec hD.hyp htT htn hMp hV0 hL38 hN
  have hS := d38_sqtk hA21 hD.hyp hex hL38
  have hLV : L ≤ stabSub V := insp5a_le_stabSub hD.hyp
  have hfaith : L ⊓ centSub V = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hLs hLV fun h => by
    obtain ⟨l, hl, v, hv, hlv⟩ := hex
    exact hlv (h hl v hv)
  let e := autSubEquivOfFaithful hLV hfaith
  have hsK : IsSimpleGroup ↥(autSub L V) := e.symm.isSimpleGroup
  have hszK : CFSG.Blueprint.SuzukiModel ↥(autSub L V) 2 n := H13.suzukiModel_congr e.symm hszL
  have hexpV : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [← qhatOf_autSub_congr hUV]
    exact hqU
  obtain ⟨f, hf⟩ := binaryNaturalSz_autSec_of_suzuki hB45 hF hexpV hQ hS hsK ⟨n, hszK⟩ hqV
  have hfn : f = n := by
    let e' : ↥(autSub L V) ≃* ↥(autSec (autSub L V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
      B5.secEquiv _ (InternalSec.le_stabSub_top _) hQ.stabKC hQ.faithful
    exact eq_of_binaryNaturalSz_of_suzukiModel hf (H13.suzukiModel_congr e'.symm hszK)
  have hLZ : L ≤ stabSub (V ⊓ fixV Mp) := le_stabSub_of_forall_mem fun l hl z hz => by
    rw [hz.2 l (hLMp hl)]
    exact hz
  have hBN := binaryNaturalSz_of_qsec hLV hLZ inf_le_left hfaith hQ hf
  have hfixVL : V ⊓ fixV Mp = V ⊓ fixV L := by
    rw [hMp, fixV_sup_eq_inf_fixV]
    exact le_antisymm (inf_le_inf_left _ inf_le_left)
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hVfix)))
  rw [hfixVL, hfn] at hBN
  exact ⟨hBN, hsum, hUV.symm, hVfix, hfixeq⟩

theorem d38_lt_of_pair (h37 : D37) (hD : D3Std M Mp T L V)
    (htT : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) {n : ℕ} (hszL : CFSG.Blueprint.SuzukiModel ↥L 2 n) :
    V < orbSup T V := by
  refine lt_of_le_of_ne (le_orbSup T V) fun hVT => ?_
  have h3 : ¬ 3 ∣ Nat.card ↥L :=
    CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hszL
  have hdvd : Nat.card ↥(autSub L V) ∣ Nat.card ↥L := card_autSub_dvd (insp5a_le_stabSub hD.hyp)
  rcases h37 W M Mp T L V hD hVT t htT htn hMp with ⟨m, hm, -⟩ | ⟨hm, -⟩
  · exact h3 (dvd_trans (H13.three_dvd_card_of_isPSL_two_two hm) hdvd)
  · exact h3 (dvd_trans (H13.three_dvd_card_of_isPSL_three_two hm) hdvd)

theorem d38_VT_of_eq (h35 : D35)
    (hD : D3Std M Mp T L V) (hMp : Mp = L) (hLs : IsSimpleGroup ↥L) {n : ℕ}
    (hszL : CFSG.Blueprint.SuzukiModel ↥L 2 n) : V = orbSup T V := by
  have h3 : ¬ 3 ∣ Nat.card ↥L :=
    CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hszL
  have hL38 : A38Types ↥L := Or.inr (Or.inl ⟨n, hszL⟩)
  by_contra hne
  have hlt : V < orbSup T V := lt_of_le_of_ne (le_orbSup T V) hne
  have hLV : Mp ≤ stabSub V := insp5a_sec_Mp_le_stabSub hD.hyp
  have hMps : IsSimpleGroup ↥Mp := by rw [hMp]; exact hLs
  have hne' : ¬ Mp ≤ centSub V := fun h => by
    obtain ⟨l, hl, v, hv, hlv⟩ := lred3_exists_ne hD.hyp hMp
    exact hlv (h (by rw [hMp]; exact hl) v hv)
  have hfaith : Mp ⊓ centSub V = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hMps hLV hne'
  have hcent : ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g := by
    intro g hg hgV x _
    have hg1 : g ∈ Mp ⊓ centSub V := ⟨hg, hgV⟩
    rw [hfaith, Subgroup.mem_bot] at hg1
    rw [hg1, one_mul, mul_one]
  obtain ⟨-, -, -, h5⟩ := h35 W M Mp T L V hD hlt hcent
  exact h3 (H13.three_dvd_card_of_isPSL_three_two (d36A38_holds W L V hL38 h5).1)

theorem d38_eq_case (h35 : D35)
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Facts10_1) (hD : D3Std M Mp T L V)
    (hMp : Mp = L) (hLs : IsSimpleGroup ↥L) {n : ℕ} (hszL : CFSG.Blueprint.SuzukiModel ↥L 2 n) :
    orbSup T V = V ∧ BinaryNaturalSz L V (V ⊓ fixV L) n := by
  have hVT := d38_VT_of_eq h35 hD hMp hLs hszL
  have hT : T ≤ stabSub V := by
    rw [hVT]
    exact le_stabSub_orbSup T V
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT
  have hQ := lred3_qsec hD.hyp hMp hO2
  have hS := lred3_sqtk hA21 hD.hyp hMp
  have hLMp : L ≤ Mp := le_of_eq hMp.symm
  have hLV : L ≤ stabSub V := insp5a_le_stabSub hD.hyp
  have hfaith : L ⊓ centSub V = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hLs hLV fun h => by
    obtain ⟨l, hl, v, hv, hlv⟩ := lred3_exists_ne hD.hyp hMp
    exact hlv (h hl v hv)
  let e := autSubEquivOfFaithful hLV hfaith
  have hsK : IsSimpleGroup ↥(autSub L V) := e.symm.isSimpleGroup
  have hszK : CFSG.Blueprint.SuzukiModel ↥(autSub L V) 2 n := H13.suzukiModel_congr e.symm hszL
  have hexpV : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  obtain ⟨f, hf⟩ := binaryNaturalSz_autSec_of_suzuki hB45 hF hexpV hQ hS hsK ⟨n, hszK⟩
    (lred3_qhatOf_autSub hD hT)
  have hfn : f = n := by
    let e' : ↥(autSub L V) ≃* ↥(autSec (autSub L V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
      B5.secEquiv _ (InternalSec.le_stabSub_top _) hQ.stabKC hQ.faithful
    exact eq_of_binaryNaturalSz_of_suzukiModel hf (H13.suzukiModel_congr e'.symm hszK)
  have hLZ : L ≤ stabSub (V ⊓ fixV Mp) := le_stabSub_of_forall_mem fun l hl z hz => by
    rw [hz.2 l (hLMp hl)]
    exact hz
  have hBN := binaryNaturalSz_of_qsec hLV hLZ inf_le_left hfaith hQ hf
  rw [hMp, hfn] at hBN
  exact ⟨hVT.symm, hBN⟩

end Pair

end CFSG.Quasithin.RonanD38
