module

public import CFSG.Quasithin.Background.RonanF918Cases
public import CFSG.Quasithin.Background.RonanF918Kstar
public import CFSG.Quasithin.Background.RonanF918A7
public import CFSG.Quasithin.Background.F918C9
public import CFSG.Quasithin.Background.RonanF918A6

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

section FourCases

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

@[expose] def NatSLU (d n : ℕ) (Ks : Type) [Group Ks] {X : Type} [Group X] (Y A : Subgroup X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧ Nonempty (Ks ≃* ↥(StatedSL d F)) ∧
    ModelOnU (FFModel.nat (StatedSL d F)) Y A

@[expose] def NatSp4U (n : ℕ) (Ks : Type) [Group Ks] {X : Type} [Group X] (Y A : Subgroup X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧ Nonempty (Ks ≃* ↥(StatedSp 2 F)) ∧
    ModelOnU (FFModel.nat (StatedSp 2 F)) Y A

@[expose] def NatA6U (Ks : Type) [Group Ks] {X : Type} [Group X] (Y A : Subgroup X) : Prop :=
  Nonempty (Ks ≃* alternatingGroup (Fin 6)) ∧ ModelOnU (FFModel.altDn 6) Y A

@[expose] def F918NatChoice4U (V₁ Vp H K T I : Subgroup G) : Prop :=
  (∃ n : ℕ, NatSLU 3 n ↥(autIH V₁ Vp H K)
    (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)) ∨
    (∃ n : ℕ, NatSp4U n ↥(autIH V₁ Vp H K)
      (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)) ∨
    NatA6U ↥(autIH V₁ Vp H K)
      (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I) ∨
    NatSLU 4 1 ↥(autIH V₁ Vp H K)
      (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I) ∨
    NatSLU 5 1 ↥(autIH V₁ Vp H K)
      (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I) ∨
    (Nonempty (↥(autIH V₁ Vp H K) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥(tildeOf V₁ I) = 2 ^ 4)

theorem not_isPerfect_statedSp_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    ¬ Group.IsPerfect ↥(StatedSp 2 F) := by
  intro hP
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have e := CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm F hF'
  have hPerm : Group.IsPerfect (Equiv.Perm (Fin 6)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have h1 : commutator (Equiv.Perm (Fin 6)) = ⊤ := hPerm.commutator_eq_top
  have h2 := alternatingGroup.commutator_perm_le (α := Fin 6)
  rw [h1] at h2
  have h3 : Equiv.swap (0 : Fin 6) 1 ∈ alternatingGroup (Fin 6) := h2 (Subgroup.mem_top _)
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at h3
  exact absurd h3 (by decide)

theorem one_le_of_card_field {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    1 ≤ n := by
  by_contra h0
  have hn : n = 0 := by omega
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF, hn] at h1
  exact absurd h1 (by norm_num)

theorem alt_mulEquiv_of_surj {n : ℕ} (hn : 5 ≤ n) {Y : Type} [Group Y] {A : Subgroup Y}
    (hA : A ≠ ⊥) (π : ↥(alternatingGroup (Fin n)) →* ↥A) (hπ : Function.Surjective π) :
    Nonempty (↥(alternatingGroup (Fin n)) ≃* ↥A) := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  have hne : ∃ s, π s ≠ 1 := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
    obtain ⟨s, rfl⟩ := hπ a
    exact ⟨s, ha1⟩
  exact ⟨MulEquiv.ofBijective π ⟨injective_of_isSimpleGroup π hne, hπ⟩⟩

variable [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem natChoice4U_of_alt
    (hGA : CFSG.Open.GriessAllModelsStatement) (h : HypF918 T V L V₁ Vp H K)
    (hK : conjClosure K T = K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (hAV : autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) I))
    (hcomm : commSub (subM V₁ (conjClosure I H) I) (autIH V₁ I H (conjClosure K T)) =
      subM V₁ (conjClosure I H) I)
    (hFine7 : IsAlt 7 (↥(autIH V₁ Vp H K) ⧸ Subgroup.center ↥(autIH V₁ Vp H K)) →
      ¬ IsHat ↥(autIH V₁ Vp H K) ↥(alternatingGroup (Fin 7)))
    (hA6 : AlternatingNatural (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))) 6 →
      ¬ IsHat ↥(autIH V₁ Vp H K) ↥(alternatingGroup (Fin 6)))
    (hnat : (∃ n, BinaryNaturalSL (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))) 3 n) ∨
      (∃ n, BinaryNaturalSp4 (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))) n) ∨
      AlternatingNatural (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))) 6 ∨
      BinaryNaturalSL (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))) 4 1 ∨
      BinaryNaturalSL (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))) 5 1 ∨
      A7Four (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T)))) :
    F918NatChoice4U V₁ Vp H K T I := by
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK]
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hAne : autIH V₁ I H (conjClosure K T) ≠ ⊥ := by
    rw [hMp, autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  have hhatK : hat' V₁ Vp H K T K = hat' V₁ Vp H K T (conjClosure K T) :=
    congrArg (hat' V₁ Vp H K T) hK.symm
  have hperfA := F918Fine4Pf.isPerfect_autIH h I
  have hEl : IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)) := Fact.out
  have hW2 : ∀ w : ↥(tildeOf V₁ (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hEl.2 (w : GtOf V₁) w.2)
  unfold F918NatChoice4U
  rw [hhatK]
  rcases hnat with ⟨n, F, hFld, hFin, hcard, hreal⟩ | ⟨n, F, hFld, hFin, hcard, hreal⟩ | halt6 |
    ⟨F, hFld, hFin, hcard, hreal⟩ | ⟨F, hFld, hFin, hcard, hreal⟩ | halt7
  ·
    left
    refine ⟨n, F, hFld, hFin, hcard, ?_, modelOnU_of_realizes h hIU hKI hAV hreal⟩
    obtain ⟨π, hπ⟩ := hreal
    have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    let πe : ↥(StatedSL 3 F) ≃* ↥(autIH V₁ I H (conjClosure K T)) :=
      MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    exact kstar_equiv_sl3 hGA h hK hIU hnt (one_le_of_card_field hcard) hcard
      (πe.trans (MulEquiv.subgroupCongr hMp))
  ·
    right; left
    refine ⟨n, F, hFld, hFin, hcard, ?_, modelOnU_of_realizes h hIU hKI hAV hreal⟩
    obtain ⟨π, hπ⟩ := hreal
    have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    let πe : ↥(StatedSp 2 F) ≃* ↥(autIH V₁ I H (conjClosure K T)) :=
      MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    have hn2 : 2 ≤ n := by
      have h1 := one_le_of_card_field hcard
      by_contra hlt
      have hn1 : n = 1 := by omega
      subst hn1
      apply not_isPerfect_statedSp_card_two (F := F) (by simpa using hcard)
      haveI : Group.IsPerfect ↥(autIH V₁ I H (conjClosure K T)) := by
        rw [hMp]; exact hperfA
      exact Group.IsPerfect.ofSurjective (f := πe.symm.toMonoidHom) πe.symm.surjective
    exact kstar_equiv_sp4 hGA h hIU hnt hn2 hcard (πe.trans (MulEquiv.subgroupCongr hMp))
  ·
    right; right; left
    refine ⟨?_, modelOnU_of_realizes h hIU hKI hAV halt6⟩
    obtain ⟨π, hπ⟩ := halt6
    obtain ⟨πe⟩ := alt_mulEquiv_of_surj (n := 6) (by norm_num) hAne π hπ.1
    exact kstar_equiv_alt (Or.inl rfl) h hK hIU hnt (πe.trans (MulEquiv.subgroupCongr hMp))
      (hA6 ⟨π, hπ⟩)
  ·
    right; right; right; left
    refine ⟨F, hFld, hFin, hcard, ?_, modelOnU_of_realizes h hIU hKI hAV hreal⟩
    obtain ⟨π, hπ⟩ := hreal
    have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    let πe : ↥(StatedSL 4 F) ≃* ↥(autIH V₁ I H (conjClosure K T)) :=
      MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    exact kstar_equiv_sl4 hGA h hK hIU hnt hcard (πe.trans (MulEquiv.subgroupCongr hMp))
  ·
    right; right; right; right; left
    refine ⟨F, hFld, hFin, hcard, ?_, modelOnU_of_realizes h hIU hKI hAV hreal⟩
    obtain ⟨π, hπ⟩ := hreal
    have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    let πe : ↥(StatedSL 5 F) ≃* ↥(autIH V₁ I H (conjClosure K T)) :=
      MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    exact kstar_equiv_sl5 hGA h hIU hnt hcard (πe.trans (MulEquiv.subgroupCongr hMp))
  ·
    right; right; right; right; right
    obtain ⟨α, π, hπ⟩ := halt7
    obtain ⟨πe⟩ := alt_mulEquiv_of_surj (n := 7) (by norm_num) hAne π hπ.1
    obtain ⟨e₁⟩ := kstar_quot_equiv h hIU hnt
    obtain ⟨eA⟩ := quotCenter_alt (n := 7) (by norm_num) (πe.trans (MulEquiv.subgroupCongr hMp))
    refine ⟨kstar_equiv_alt (Or.inr rfl) h hK hIU hnt (πe.trans (MulEquiv.subgroupCongr hMp))
      (fun hHat => hFine7 ⟨e₁.trans eA⟩ hHat), ?_⟩
    have h16 := a7Four_card_sixteen hW2 (fun g hg v hv => (hAV hg v).mpr hv) hcomm ⟨α, π, hπ⟩
    have hle : tildeOf V₁ I ≤ tildeOf V₁ (conjClosure I H) := secImg_mono (le_conjClosure I H)
    have h2 : Nat.card ↥(subM V₁ (conjClosure I H) I) = Nat.card ↥(tildeOf V₁ I) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [← h2]
    exact h16

theorem four_cases_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement) (h : HypF918 T V L V₁ Vp H K)
    (hK : conjClosure K T = K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirr : IsIrrPlusTildeT h hIU) (hFour : F918Four h hIU)
    (hFine7 : IsAlt 7 (↥(autIH V₁ Vp H K) ⧸ Subgroup.center ↥(autIH V₁ Vp H K)) →
      ¬ IsHat ↥(autIH V₁ Vp H K) ↥(alternatingGroup (Fin 7)))
    (hH : SQTKGroup ↥H) (hHat6 : F918Fine4Hat6) :
    H ≤ Subgroup.normalizer (I : Set G) ∨
      (tildeOf V₁ (conjClosure I T) = tildeOf V₁ I ∧
        ∃ hV : IsElemAbelian 2 (hat' V₁ Vp H K T I),
          IsFFInt (hat' V₁ Vp H K T (K ⊔ T)) (hat' V₁ Vp H K T I) hV) ∨
      (F918NatChoice4U V₁ Vp H K T I ∧
        (∃ t : G, t ∈ T ∧ t ∉ Subgroup.normalizer (I : Set G)) ∧
        ∀ t : G, t ∈ T → t ∉ Subgroup.normalizer (I : Set G) →
          HatDSumU V₁ Vp H K T (conjClosure I H) I t ∧
          ¬ ModIso (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)
            (hat' V₁ Vp H K T (conjSub t⁻¹ I))) := by
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK]
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hinv := hirr'.1.2.1
  have hAV : autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) I) := by
    intro l hl u
    constructor
    · intro hu
      have := hinv ⟨l⁻¹, (autIH V₁ I H (conjClosure K T)).inv_mem hl⟩ _ hu
      simpa using this
    · intro hu
      exact hinv ⟨l, hl⟩ u hu
  have hcomm : commSub (subM V₁ (conjClosure I H) I) (autIH V₁ I H (conjClosure K T)) =
      subM V₁ (conjClosure I H) I := by
    rw [← commOf_eq_commSub]
    exact hirr'.1.2.2.1
  have hhatK : hat' V₁ Vp H K T K = hat' V₁ Vp H K T (conjClosure K T) :=
    congrArg (hat' V₁ Vp H K T) hK.symm
  have hF4 : H ≤ Subgroup.normalizer (I : Set G) ∨
      ModFourRest (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
        (subM V₁ (conjClosure I H) I) := hFour
  rcases hF4 with hH | hrest
  · exact Or.inl hH
  refine Or.inr ?_
  rcases hrest with ⟨hVT, hFF⟩ | hD
  ·
    refine Or.inl ⟨?_, ?_⟩
    · have h1 : subM V₁ (conjClosure I H) I = subM V₁ (conjClosure I H) (conjClosure I T) :=
        hVT.trans (wOf_eq h hV₁I hIU)
      have hle1 : tildeOf V₁ I ≤ tildeOf V₁ (conjClosure I H) := secImg_mono (le_conjClosure I H)
      have hle2 : tildeOf V₁ (conjClosure I T) ≤ tildeOf V₁ (conjClosure I H) :=
        secImg_mono (conjClosure_mono le_rfl h.T_le_H)
      have h2 := Subgroup.subgroupOf_inj.mp h1
      rw [inf_eq_left.mpr hle1, inf_eq_left.mpr hle2] at h2
      exact h2.symm
    · rw [← hMp] at hFF
      obtain ⟨hV, hFFint⟩ := isFFInt_hat_of_isFFModule h hIU hFF
      have e : K ⊔ T = conjClosure K T ⊔ T := by rw [hK]
      refine ⟨hV, ?_⟩
      rw [e]
      exact hFFint
  ·
    refine Or.inr ?_
    rw [← hMp] at hD
    obtain ⟨hnat, ⟨t₀, ht₀T, ht₀⟩, hall⟩ := hD
    have hA6 : AlternatingNatural (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))) 6 →
        ¬ IsHat ↥(autIH V₁ Vp H K) ↥(alternatingGroup (Fin 6)) := fun halt6 =>
      hat6_exclusion hHat6 hH h hK hIU hnt ht₀T halt6 (hall t₀ ht₀T ht₀).2
    refine ⟨natChoice4U_of_alt hGA h hK hIU hnt hKI hAV hcomm hFine7 hA6 hnat, ?_, ?_⟩
    · have ht₀' : t₀ ∈ (T.subgroupOf H).map
          (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
        rw [← autIH_eq_map h h.T_le_H]
        exact ht₀T
      obtain ⟨⟨s, hsH⟩, hs, hst⟩ := ht₀'
      refine ⟨s, Subgroup.mem_subgroupOf.mp hs, fun hsN => ht₀ ?_⟩
      rw [← hst]
      exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
        (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) ⟨s, hsH⟩).mpr hsN
    · intro t htT htN
      have htH : t ∈ H := h.T_le_H htT
      have ht''T : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          ⟨t⁻¹, H.inv_mem htH⟩ ∈ autIH V₁ I H T := by
        rw [autIH_eq_map h h.T_le_H]
        exact ⟨⟨t⁻¹, H.inv_mem htH⟩, Subgroup.mem_subgroupOf.mpr (T.inv_mem htT), rfl⟩
      have ht''N : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          ⟨t⁻¹, H.inv_mem htH⟩ ∉ stabSub (subM V₁ (conjClosure I H) I) := fun hst =>
        htN ((Subgroup.inv_mem_iff _).mp
          ((actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
            (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) ⟨t⁻¹, H.inv_mem htH⟩).mp hst))
      obtain ⟨hsum, hsec⟩ := hall _ ht''T ht''N
      have hmap := map_actH_subM h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
        (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) (⟨t⁻¹, H.inv_mem htH⟩ : ↥H)
      have hmap' : (subM V₁ (conjClosure I H) I).map
          (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
            ⟨t⁻¹, H.inv_mem htH⟩).toMonoidHom = subM V₁ (conjClosure I H) (conjSub t⁻¹ I) := hmap
      rw [hmap'] at hsum hsec
      refine ⟨hatDSumU_of_isSumMod h hIU htH hsum, ?_⟩
      rw [hhatK]
      exact not_modIso_of_not_secIsoL h hV₁I hIU hKI htH hsec

end FourCases

end CFSG.Quasithin.RonanF918
