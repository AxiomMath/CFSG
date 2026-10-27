module

public import CFSG.Quasithin.Background.F918J2
public import CFSG.Quasithin.Background.F918M5
public import CFSG.Quasithin.Background.InternalSecFF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Bridge

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

private theorem lred3_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (h : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : H ≤ Subgroup.normalizer (N : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h g hg n, fun hn => ?_⟩
  have h1 := h g⁻¹ (H.inv_mem hg) _ hn
  have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
  rwa [e] at h1

omit [Finite W] in
theorem lred3_sup_le_normalizer (hD : D31 M Mp T L V) (hMp : Mp = L) :
    Mp ⊔ T ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
  (insp5a_sec_sup_le_normalizer hD).trans (by rw [hMp])

omit [Finite W] in
theorem lred3_act (hMp : Mp = L) : ∀ a ∈ Mp, ∃ l ∈ L, ∀ u ∈ V, a u = l u :=
  fun a ha => ⟨a, hMp ▸ ha, fun _ _ => rfl⟩

omit [Finite W] in
theorem lred3_exists_ne (hD : D31 M Mp T L V) (hMp : Mp = L) : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp hD.irr
  apply hlt.not_ge
  intro v hv
  exact ⟨hv, fun m hm => hcon m (hMp ▸ hm) v hv⟩

omit [Finite W] in
theorem lred3_isQuasisimple_autSub (hLs : L ≤ stabSub V) (hq : CFSG.IsQuasisimple ↥L)
    (hne : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v) : CFSG.IsQuasisimple ↥(autSub L V) := by
  obtain ⟨l, hl, v, hv, hlv⟩ := hne
  have hq' : CFSG.IsQuasisimple ↥(resHomOn V hLs).range := by
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := (resHomOn V hLs).rangeRestrict)
      hq (MonoidHom.rangeRestrict_surjective _) ⟨⟨l, hl⟩, fun h => hlv ?_⟩
    have h1 : resHomOn V hLs ⟨l, hl⟩ = 1 := congrArg Subtype.val h
    exact congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : W)) h1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLs)).symm hq'

theorem lred3_pCoreOf_autSub_eq_bot {X : Subgroup (MulAut W)} (hLX : L ≤ X)
    (hN : X ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W))) (hO2 : pCoreOf 2 (autSub X V) = ⊥) :
    pCoreOf 2 (autSub L V) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : autSub L V ≤ autSub X V := autSub_mono hLX V
  have hnorm : autSub X V ≤ Subgroup.normalizer ((autSub L V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
    lred3_le_normalizer (insp5a_sec_normal hN)
  have h1 : pCoreOf 2 (autSub L V) ≤ pCoreOf 2 (autSub X V) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hle)
      (hnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [hO2] at h1
  exact le_bot_iff.1 h1

theorem lred3_pCoreOf_autSub_sup_eq_bot (hD : D31 M Mp T L V) (hT : T ≤ stabSub V) :
    pCoreOf 2 (autSub (Mp ⊔ T) V) = ⊥ := by
  have h := D31.pCoreOf_autSub_orbSup_eq_bot hD
  have hVT : orbSup T V = V := orbSup_eq_of_stab fun t ht => hT ht
  revert h
  generalize orbSup T V = U at hVT ⊢
  subst hVT
  exact id

theorem lred3_qsec (hD : D31 M Mp T L V) (hMp : Mp = L)
    (hO2 : pCoreOf 2 (autSub (Mp ⊔ T) V) = ⊥) :
    InternalSec.QSec (autSub (Mp ⊔ T) V) (autSub L V) ((V ⊓ fixV Mp).subgroupOf V) := by
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hact := lred3_act (V := V) hMp
  have hN : (Mp ⊔ T) ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    inf_le_left.trans (lred3_sup_le_normalizer hD hMp)
  have hLMp : L ≤ Mp ⊔ T := (insp5a_sec_L_le_Mp hD).trans le_sup_left
  have hle : autSub L V ≤ autSub (Mp ⊔ T) V := autSub_mono hLMp V
  have hstab := insp5a_sec_stab hD
  have hfix := insp5a_sec_fix hD
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.exp])
  have hO2K : pCoreOf 2 (autSub L V) = ⊥ := lred3_pCoreOf_autSub_eq_bot hLMp hN hO2
  exact
    { le := hle
      normal := insp5a_sec_normal hN
      two := insp5a_sec_two hD hact hN
      stab := hstab
      fix := hfix
      comm := insp5a_sec_comm hLs (insp5a_sec_commSub_eq hD hact)
      lt := insp5a_sec_lt hD
      irr := insp5a_sec_irr hD hact
      faithful := InternalSec.inf_centSec_eq_bot_of_pCoreOf hexp (hle.trans hstab) hfix hO2K
      quasi := lred3_isQuasisimple_autSub hLs hD.quasi (lred3_exists_ne hD hMp) }

theorem lred3_sqtk (hA21 : AsA21SQTKSection) (hD : D31 M Mp T L V) (hMp : Mp = L) :
    SQTKGroup ↥(autSub L V) := by
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hq := lred3_isQuasisimple_autSub hLs hD.quasi (lred3_exists_ne hD hMp)
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hD.qsqtk
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
  have hSL : SQTKGroup ↥L := B69.sqtk_subgroup hA21 hS φ hφ (le_of_mem_cComp hD.comp) hD.quasi
  exact B69.sqtk_autSub hA21 hLs hSL hq

theorem lred3_b4Hyp (hA21 : AsA21SQTKSection) (hD : D31 M Mp T L V) (hMp : Mp = L)
    (hO2 : pCoreOf 2 (autSub (Mp ⊔ T) V) = ⊥) :
    B4Hyp (autSec (autSub (Mp ⊔ T) V) ⊤ ((V ⊓ fixV Mp).subgroupOf V))
      (autSec (autSub L V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) := by
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.exp])
  exact (lred3_qsec hD hMp hO2).b4Hyp hexp (lred3_sqtk hA21 hD hMp)

private theorem lred3_qOf_autSub_congr {X : Subgroup (MulAut W)} {U U' : Subgroup W} (h : U = U') :
    qOf (autSub X U) = qOf (autSub X U') := by
  subst h
  rfl

theorem lred3_qhatOf_autSub (hD : D3Std M Mp T L V) (hT : T ≤ stabSub V) :
    qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have h := hD.qhat
  rwa [qhatOf_autSub_congr (orbSup_eq_of_stab fun t ht => hT ht)] at h

theorem lred3_qOf_autSub (hT : T ≤ stabSub V)
    (hq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    qOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
  rwa [lred3_qOf_autSub_congr (orbSup_eq_of_stab fun t ht => hT ht)] at hq

theorem lred3_qhatOf_autSec (hD : D3Std M Mp T L V) (hMp : Mp = L) (hT : T ≤ stabSub V) :
    qhatOf (autSec (autSub (Mp ⊔ T) V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  exact ((lred3_qsec hD.hyp hMp (lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT)).qhatOf_autSec_le hexp).trans
    (lred3_qhatOf_autSub hD hT)

theorem lred3_qOf_autSec (hD : D3Std M Mp T L V) (hMp : Mp = L) (hT : T ≤ stabSub V)
    (hq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    qOf (autSec (autSub (Mp ⊔ T) V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  exact ((lred3_qsec hD.hyp hMp (lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT)).qOf_autSec_le hexp).trans
    (lred3_qOf_autSub hT hq)

end Bridge

end CFSG.Quasithin
