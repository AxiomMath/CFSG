module

public import CFSG.LocalAnalysis.WeakClosure81.SixTen
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_cTilde_iff_centralizes {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) {m : G} :
    m ∈ F11.CTilde M V₀ V ↔ m ∈ M ∧ CentralizesMod V₀ V m := by
  rw [mem_cTilde_iff hV hM]
  constructor
  · rintro ⟨hmM, h, h1⟩
    exact ⟨hmM, (actTil_eq_one_iff V₀ V hV ⟨m, h⟩).1 h1⟩
  · rintro ⟨hmM, hc⟩
    exact ⟨hmM, ⟨hM hmM, hM₀ hmM⟩, (actTil_eq_one_iff V₀ V hV ⟨m, hM hmM, hM₀ hmM⟩).2 hc⟩

theorem centralizesMod_of_mem_cTilde {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) {m : G}
    (hm : m ∈ F11.CTilde M V₀ V) : CentralizesMod V₀ V m :=
  ((mem_cTilde_iff_centralizes hV hM hM₀).1 hm).2

theorem exists_sq_mem_of_not_le {Q C : Subgroup G} (hCQ : C ≤ Q) (hQ2 : IsPGroup 2 Q)
    (h : ¬ Q ≤ C) : ∃ q ∈ Q, q ∉ C ∧ q * q ∈ C := by
  obtain ⟨q, hqQ, hqC⟩ : ∃ q ∈ Q, q ∉ C := by
    rw [SetLike.le_def] at h
    push Not at h
    exact h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := (IsPGroup.iff_orderOf).1 hQ2 ⟨q, hqQ⟩
  have hqs : q ^ (2 ^ s) = 1 := by
    have := hs ▸ pow_orderOf_eq_one (⟨q, hqQ⟩ : Q)
    simpa using congrArg Subtype.val this
  classical
  let P : ℕ → Prop := fun k => q ^ (2 ^ k) ∈ C
  have hex : ∃ k, P k := ⟨s, by show q ^ (2 ^ s) ∈ C; rw [hqs]; exact C.one_mem⟩
  have hkP : P (Nat.find hex) := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    exact hqC (by simpa [P, h0] using hkP)
  have hkpos : 1 ≤ Nat.find hex := Nat.one_le_iff_ne_zero.2 hk0
  have hkm1 : ¬ P (Nat.find hex - 1) := Nat.find_min hex (by omega)
  refine ⟨q ^ (2 ^ (Nat.find hex - 1)), Q.pow_mem hqQ _, ?_, ?_⟩
  · simpa [P] using hkm1
  · show q ^ (2 ^ (Nat.find hex - 1)) * q ^ (2 ^ (Nat.find hex - 1)) ∈ C
    rw [← pow_two, ← pow_mul,
      show 2 ^ (Nat.find hex - 1) * 2 = 2 ^ Nat.find hex by
        rw [← pow_succ, Nat.sub_add_cancel hkpos]]
    exact hkP

theorem betaN_le_of_mem {n : ℕ} {M V U : Subgroup G} (hU : U ∈ calBn n M V) :
    betaN n M V ≤ (E3.mQuot V U : ℕ∞) :=
  le_trans (iInf_le (fun U => ⨅ _ : U ∈ calBn n M V, (E3.mQuot V U : ℕ∞)) U)
    (iInf_le (fun _ : U ∈ calBn n M V => (E3.mQuot V U : ℕ∞)) hU)

theorem le_cTilde_of_lt_mBar {M V₀ V Q W : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    {n : ℕ} (hn : n < mBar M V₀ V hV) (hW : W ≤ V)
    (hQM : Q ≤ M) (hQ2 : IsPGroup 2 Q) (hQW : Q ≤ centralizer (W : Set G))
    (hmW : E3.mQuot V W ≤ n) :
    Q ≤ F11.CTilde M V₀ V := by
  have hGT := (mBarGT_iff_lt_mBar M V₀ V hV hV₀ hM hM₀ n).2 hn
  intro q hq
  by_contra hqc
  have hnot : ¬ Q ≤ Q ⊓ F11.CTilde M V₀ V := fun h => hqc (Subgroup.mem_inf.1 (h hq)).2
  obtain ⟨q', hq'Q, hq'C, hq'C2⟩ := exists_sq_mem_of_not_le inf_le_left hQ2 hnot
  have hq'M : q' ∈ M := hQM hq'Q
  have hnotcent : ¬ CentralizesMod V₀ V q' := fun hc =>
    hq'C (Subgroup.mem_inf.2 ⟨hq'Q, (mem_cTilde_iff_centralizes hV hM hM₀).2 ⟨hq'M, hc⟩⟩)
  have hcent2 : CentralizesMod V₀ V (q' * q') :=
    centralizesMod_of_mem_cTilde hV hM hM₀ (Subgroup.mem_inf.1 hq'C2).2
  have hcard := hGT.1 q' hq'M hnotcent hcent2
  have hWle : W ≤ centMod V₀ V q' := by
    intro w hw
    refine ⟨hW hw, ?_⟩
    have hcomm : w * q' = q' * w :=
      (Subgroup.mem_centralizer_iff.1 (hQW hq'Q)) w hw
    have hone : q' * w * q'⁻¹ * w⁻¹ = 1 := by
      rw [← hcomm]
      group
    rw [hone]
    exact V₀.one_mem
  have hcardW : Nat.card W ≤ Nat.card (centMod V₀ V q') :=
    Nat.card_le_card_of_injective
      (fun w : W => (⟨(w : G), hWle w.2⟩ : ↥(centMod V₀ V q')))
      (fun a b hab => Subtype.ext (by
        have h := congrArg (fun y : ↥(centMod V₀ V q') => (y : G)) hab
        simpa using h))
  have h2 : 2 ^ (n + 1) * Nat.card W ≤ Nat.card V :=
    (Nat.mul_le_mul_left _ hcardW).trans hcard
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hpow := E3.card_eq_two_pow_mul hV2 hW
  rw [hpow] at h2
  have hle1 : 2 ^ (n + 1) ≤ 2 ^ (E3.mQuot V W) :=
    Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  have hle2 : n + 1 ≤ E3.mQuot V W :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle1
  omega

theorem commElt_eq_bot_iff {A : Subgroup G} {t : G} :
    commElt A t = ⊥ ↔ ∀ a ∈ A, a⁻¹ * t⁻¹ * a * t = 1 := by
  constructor
  · intro h a ha
    have : a⁻¹ * t⁻¹ * a * t ∈ commElt A t := Subgroup.subset_closure ⟨a, ha, rfl⟩
    rw [h] at this
    simpa using this
  · intro h
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨a, ha, rfl⟩
    rw [h a ha]
    exact Subgroup.one_mem _

theorem betaN_le_of_cent_ne {M V A Q B : Subgroup G} {i k n : ℕ}
    (hAV : A ≤ V) (hAi : E3.mQuot V A ≤ i)
    (hBA : B ≤ A) (hBAm : E3.mQuot A B ≤ k) (hn : n = k + i)
    (hQM : Q ≤ M) (hQW : Q ≤ centralizer (B : Set G)) (hQ2 : IsPGroup 2 Q)
    {t : G} (htQ : t ∈ Q) (htAt : commElt A t ≠ ⊥)
    (hPropB : PropB M (commElt A t)) :
    ¬ ((n : ℕ∞) < betaN i M V) := by
  intro hbeta
  set U := A ⊓ centralizer ({t} : Set G) with hU
  have hUV : U ≤ V := (inf_le_left : U ≤ A).trans hAV
  have htM : t ∈ M := hQM htQ
  have htCU : t ∈ centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hu).2) t
      (Set.mem_singleton t)).symm
  have hAnotC : ¬ A ≤ centralizer ({t} : Set G) := by
    intro hAC
    apply htAt
    rw [commElt_eq_bot_iff]
    intro a ha
    have hcomm : a * t = t * a :=
      ((Subgroup.mem_centralizer_iff.1 (hAC ha)) t (Set.mem_singleton t)).symm
    have e : a⁻¹ * t⁻¹ * a * t = (t * a)⁻¹ * (a * t) := by group
    rw [e, ← hcomm, inv_mul_cancel]
  have hBU : B ≤ U := by
    refine le_inf hBA ?_
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ((Subgroup.mem_centralizer_iff.1 (hQW htQ)) b hb).symm
  have hUmem : U ∈ calBn i M V := by
    unfold calBn propN
    refine ⟨hUV, t, ⟨htM, htCU⟩, ?_, A, hAV, hAi, inf_le_left, ?_, hPropB⟩
    · obtain ⟨s, hs⟩ := (IsPGroup.iff_orderOf).1 hQ2 ⟨t, htQ⟩
      refine ⟨s, ?_⟩
      rw [Subgroup.orderOf_mk t htQ] at hs
      exact hs
    · intro hAt
      exact hAnotC (hAt.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (by simp))))
  have hmU : E3.mQuot V U ≤ n := by
    have hadd := E3.mQuot_add (V := V) (U := U) (U' := A) inf_le_left hAV
    have h1 : E3.mQuot A U ≤ E3.mQuot A B := E3.mQuot_mono hBU
    omega
  have hle := betaN_le_of_mem hUmem
  have : (n : ℕ∞) < (E3.mQuot V U : ℕ∞) := lt_of_lt_of_le hbeta hle
  have : n < E3.mQuot V U := by exact_mod_cast this
  omega

theorem exists_not_isPGroup_pair_of_not_mem_pCore {H : Subgroup G} {a : G} (haH : a ∈ H)
    (h2 : IsPGroup 2 (Subgroup.zpowers (⟨a, haH⟩ : H)))
    (hane : (⟨a, haH⟩ : H) ∉ pCore 2 H) :
    ∃ g : H, ¬ IsPGroup 2
      (Subgroup.closure ({(⟨a, haH⟩ : H), g * ⟨a, haH⟩ * g⁻¹} : Set H)) := by
  by_contra h
  push Not at h
  exact hane (CFSG.BaerSuzuki.baer_suzuki (p := 2) (⟨a, haH⟩ : H) h2 h)

theorem exists_not_isPGroup_sup_conj_of_not_le_pCore {E H : Subgroup G}
    (hEH : E ≤ H) (hE2 : IsPGroup 2 E) (hEne : ¬ E ≤ pCoreOf 2 H) :
    ∃ g ∈ H, ¬ IsPGroup 2 (E ⊔ conjSubgroup E g : Subgroup G) := by
  obtain ⟨a, haE, haO⟩ : ∃ a ∈ E, a ∉ pCoreOf 2 H := by
    rw [SetLike.le_def] at hEne
    push Not at hEne
    exact hEne
  have haH : a ∈ H := hEH haE
  have hane : (⟨a, haH⟩ : H) ∉ pCore 2 H := by
    intro hmem
    apply haO
    show a ∈ (pCore 2 H).map H.subtype
    exact Subgroup.mem_map_of_mem H.subtype hmem
  have hx2 : IsPGroup 2 (Subgroup.zpowers (⟨a, haH⟩ : H)) := by
    obtain ⟨s, hs⟩ := isPGroup_iff_orderOf_dvd_pow.1 hE2 ⟨a, haE⟩
    refine IsPGroup.of_card_dvd_pow (n := s) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk a haH]
    rw [Subgroup.orderOf_mk a haE] at hs
    exact hs
  obtain ⟨g, hg⟩ := exists_not_isPGroup_pair_of_not_mem_pCore haH hx2 hane
  refine ⟨(g : G)⁻¹, H.inv_mem g.2, ?_⟩
  intro hsup
  apply hg
  have hle : (Subgroup.closure ({(⟨a, haH⟩ : H), g * ⟨a, haH⟩ * g⁻¹} : Set H)).map H.subtype ≤
      (E ⊔ conjSubgroup E (g : G)⁻¹ : Subgroup G) := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨z, hz, rfl⟩
    rcases hz with rfl | hz
    · exact Subgroup.mem_sup_left haE
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      refine Subgroup.mem_sup_right ?_
      refine mem_conjSubgroup_iff.2 ?_
      have hval : H.subtype (g * ⟨a, haH⟩ * g⁻¹) = (g : G) * a * (g : G)⁻¹ := by
        simp only [map_mul, map_inv]
        rfl
      rw [hval]
      rwa [show (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) * ((g : G)⁻¹)⁻¹ = a by group]
  have himg : IsPGroup 2
      ((Subgroup.closure ({(⟨a, haH⟩ : H), g * ⟨a, haH⟩ * g⁻¹} : Set H)).map H.subtype) :=
    hsup.to_le hle
  have hc := IsPGroup.comap_of_injective himg H.subtype H.subtype_injective
  rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at hc

private theorem conjSubgroup_inv_le_iff (B M : Subgroup G) (g : G) :
    conjSubgroup B g⁻¹ ≤ M ↔ B ≤ conjSubgroup M g := by
  have h := E3.conjSubgroup_le_conjSubgroup_iff (A := conjSubgroup B g⁻¹) (B := M) g
  have e : conjSubgroup (conjSubgroup B g⁻¹) g = B := by
    rw [conjSubgroup_conjSubgroup, show g⁻¹ * g = 1 by group, conjSubgroup_one]
  rw [e] at h
  exact h.symm

theorem isPGroup_sup_conj_of_conj_le_normalizer {V A M : Subgroup G} {g : G}
    (hV : IsPGroup 2 V) (hAV : A ≤ V)
    (hMV : M ≤ normalizer (V : Set G)) (hVg : conjSubgroup V g ≤ M) :
    IsPGroup 2 (A ⊔ conjSubgroup A g : Subgroup G) := by
  have hsup : IsPGroup 2 (V ⊔ conjSubgroup V g : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hV (E3.isPGroup_conjSubgroup hV g) (hVg.trans hMV)
  exact hsup.to_le (sup_le_sup hAV (E3.conjSubgroup_mono_left g hAV))

theorem isPGroup_sup_conj_of_le_conj_normalizer {V A M : Subgroup G} {g : G}
    (hV : IsPGroup 2 V) (hAV : A ≤ V)
    (hMnorm : normalizer (V : Set G) = M) (hVMg : V ≤ conjSubgroup M g) :
    IsPGroup 2 (A ⊔ conjSubgroup A g : Subgroup G) := by
  have hMg_eq : conjSubgroup M g = Subgroup.normalizer (conjSubgroup V g : Set G) := by
    rw [← E3.conjSubgroup_normalizer, hMnorm]
  have hsup : IsPGroup 2 (V ⊔ conjSubgroup V g : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hV (E3.isPGroup_conjSubgroup hV g)
      (hVMg.trans (le_of_eq hMg_eq))
  exact hsup.to_le (sup_le_sup hAV (E3.conjSubgroup_mono_left g hAV))

theorem not_conjSubgroup_le_normalizer_of_not_isPGroup {V A M : Subgroup G} {g : G}
    (hV : IsPGroup 2 V) (hAV : A ≤ V) (hMV : M ≤ normalizer (V : Set G))
    (h : ¬ IsPGroup 2 (A ⊔ conjSubgroup A g : Subgroup G)) :
    ¬ conjSubgroup V g ≤ M :=
  fun hle => h (isPGroup_sup_conj_of_conj_le_normalizer hV hAV hMV hle)

theorem not_le_conjSubgroup_of_not_isPGroup {V A M : Subgroup G} {g : G}
    (hV : IsPGroup 2 V) (hAV : A ≤ V) (hMnorm : normalizer (V : Set G) = M)
    (h : ¬ IsPGroup 2 (A ⊔ conjSubgroup A g : Subgroup G)) :
    ¬ V ≤ conjSubgroup M g :=
  fun hle => h (isPGroup_sup_conj_of_le_conj_normalizer hV hAV hMnorm hle)

theorem exists_commElt_ne_bot_of_commutator_ne_bot {A Q : Subgroup G} (h : ⁅A, Q⁆ ≠ ⊥) :
    ∃ q ∈ Q, commElt A q ≠ ⊥ := by
  have h' : ¬ A ≤ Subgroup.centralizer (Q : Set G) := by
    rwa [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  obtain ⟨a, haA, haQ⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (Q : Set G) := by
    rw [SetLike.le_def] at h'
    push Not at h'
    exact h'
  rw [Subgroup.mem_centralizer_iff] at haQ
  push Not at haQ
  obtain ⟨q, hqQ, hq⟩ := haQ
  refine ⟨q, hqQ, ?_⟩
  intro hbot
  apply hq
  have hgen : a⁻¹ * q⁻¹ * a * q = 1 := by
    have hmem : a⁻¹ * q⁻¹ * a * q ∈ commElt A q := Subgroup.subset_closure ⟨a, haA, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  have h2 : q⁻¹ * a * q = a := by
    have := congrArg (fun x => a * x) hgen
    simpa [mul_assoc] using this
  have h3 : a * q = q * a := by
    have := congrArg (fun x => q * x) h2
    simpa [mul_assoc] using this
  exact h3.symm

theorem mQuot_bot (B : Subgroup G) : E3.mQuot B ⊥ = rk ↥B := by
  unfold E3.mQuot rk
  rw [Subgroup.relIndex_bot_left]

theorem exists_le_mQuot_eq {B : Subgroup G} (hB : IsElemAbelian 2 B) {c : ℕ}
    (hc : c ≤ rk ↥B) : ∃ D : Subgroup G, D ≤ B ∧ E3.mQuot B D = c := by
  rcases lt_or_eq_of_le hc with hlt | heq
  · obtain ⟨D, hDB, -, hDc⟩ := E3.exists_mem_le_mQuot_eq hB hlt (Subgroup.one_mem B)
    exact ⟨D, hDB, hDc⟩
  · exact ⟨⊥, bot_le, by rw [heq, mQuot_bot]⟩

theorem six_nine_two_core {M V H S A : Subgroup G}
    (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hMnorm : normalizer (V : Set G) = M)
    (hS : IsSylowIn 2 S H) {i k n : ℕ} (hn : n = k + i)
    (hA : A ∈ E3.gammaSet V i S) (hAV : A ≤ V) (hAne : ¬ A ≤ pCoreOf 2 H)
    (hK : E1.IsE k H S A H) (hkV : n < rk ↥V)
    (hr : (n : ℕ∞) < E3.rParam V)
    (hne : ⁅twoResidual H, E3.cClos V n S⁆ ≠ ⊥)
    (hbeta : (n : ℕ∞) < betaN i M V) :
    ∃ g ∈ H, InCalO2 n M ⊥ V g := by
  obtain ⟨hAS, x, hAx, hmx⟩ := hA
  have hAi : E3.mQuot V A ≤ i := (E3.mQuot_conj_eq hV hAV hAx).trans_le hmx.le
  have hASH : A ≤ H := hAS.trans hS.le
  have hijk : i + k ≤ n := by omega
  set Q := E3.cClos V n (pCoreOf 2 H) with hQ
  set W := E3.wClos V n (pCoreOf 2 H) with hW
  set B := A ⊓ pCoreOf 2 H with hB
  have hBW : B ≤ W := E3.e3_17_B_le hV hS hijk hkV hAS hAV hAi hK
  have hmB : E3.mQuot V B ≤ n := by
    have h := E3.e3_17_mQuot hV hS hAS hAV hAi hK
    rw [hB]; omega
  have hcentle : Subgroup.centralizer (W : Set G) ≤ M := by
    rw [← hMnorm]
    exact E3.e3_17_cent_le hV hS hijk hr hkV hAS hAV hAi hK
  have hQM : Q ≤ M := (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans hcentle
  have hQW : Q ≤ centralizer (B : Set G) :=
    (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans (Subgroup.centralizer_le hBW)
  have hQ2 : IsPGroup 2 Q := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hcomm := E3.e3_17_comm_ne hV hS hijk hr hkV hAS hAV hAi hK hne
  have hEne : ⁅A, Q⁆ ≠ ⊥ := hcomm.2
  have hAab : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAV hV
  have hBab : IsElemAbelian 2 B := B2F.isElemAbelian_mono inf_le_left hAab
  have hB2 : IsPGroup 2 B := B2F.isPGroup_of_isElemAbelian hBab
  have hBAm : E3.mQuot A B ≤ k := by
    obtain ⟨-, hcard⟩ := E3.card_le_of_isE hS hAS hAab hK
    have hA2 : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAab
    have e := E3.card_eq_two_pow_mul hA2 (inf_le_left : B ≤ A)
    rw [e] at hcard
    have := Nat.le_of_mul_le_mul_right hcard Nat.card_pos
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
  have hCGE : centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) ≤ M := by
    by_contra hCGE
    obtain ⟨t, htQ, htAt⟩ := exists_commElt_ne_bot_of_commutator_ne_bot hEne
    have hcommE : commElt A t ≤ ⁅A, Q⁆ :=
      (commElt_le_commutator A t).trans
        (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.2 htQ))
    have hPropB : PropB M (commElt A t) := fun hle =>
      hCGE ((Subgroup.centralizer_le hcommE).trans hle)
    exact (betaN_le_of_cent_ne hAV hAi (inf_le_left : B ≤ A) hBAm hn hQM hQW hQ2 htQ htAt
      hPropB) hbeta
  have hE_le_V : ⁅A, Q⁆ ≤ V := by
    refine (Subgroup.commutator_mono hAV le_rfl).trans ?_
    refine Subgroup.commutator_le.2 ?_
    intro v hv q hq
    have hqN : q ∈ Subgroup.normalizer (V : Set G) := hMnorm.symm ▸ hQM hq
    have h1 : q * v * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hqN v).1 hv
    have h2 : q * v⁻¹ * q⁻¹ ∈ V := by
      have := V.inv_mem h1
      convert this using 1
      group
    have e : ⁅v, q⁆ = v * (q * v⁻¹ * q⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hv h2
  have hA2 : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAab
  obtain ⟨g, hgH, hgnon2⟩ := exists_not_isPGroup_sup_conj_of_not_le_pCore hASH hA2 hAne
  have hWnorm : H ≤ Subgroup.normalizer (W : Set G) := by
    rw [hW]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
      (E3.normalizer_le_normalizer_wClos (V := V) (i := n) (pCoreOf 2 H))
  have hQnorm : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
      (E3.normalizer_le_normalizer_cClos (V := V) (i := n) (pCoreOf 2 H))
  have hE_le_Q : ⁅A, Q⁆ ≤ Q := by
    refine Subgroup.commutator_le.2 ?_
    intro a ha q hq
    have haN : a ∈ Subgroup.normalizer (Q : Set G) := hQnorm (hASH ha)
    have h1 : a * q * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 haN q).1 hq
    have e : ⁅a, q⁆ = (a * q * a⁻¹) * q⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact Q.mul_mem h1 (Q.inv_mem hq)
  have hQg : conjSubgroup Q g = Q := conjSubgroup_eq_iff_mem_normalizer.2 (hQnorm hgH)
  have hQg_inv : conjSubgroup Q g⁻¹ = Q :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hQnorm (H.inv_mem hgH))
  have hWg : conjSubgroup W g = W := conjSubgroup_eq_iff_mem_normalizer.2 (hWnorm hgH)
  have hWg_inv : conjSubgroup W g⁻¹ = W :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hWnorm (H.inv_mem hgH))
  have hEg_le_Q : conjSubgroup (⁅A, Q⁆) g ≤ Q :=
    (E3.conjSubgroup_mono_left g hE_le_Q).trans (le_of_eq hQg)
  have hEginv_le_Q : conjSubgroup (⁅A, Q⁆) g⁻¹ ≤ Q :=
    (E3.conjSubgroup_mono_left g⁻¹ hE_le_Q).trans (le_of_eq hQg_inv)
  have hEg_le_M : conjSubgroup (⁅A, Q⁆) g ≤ M := hEg_le_Q.trans hQM
  have hEginv_le_M : conjSubgroup (⁅A, Q⁆) g⁻¹ ≤ M := hEginv_le_Q.trans hQM
  have hBg_le_W : conjSubgroup B g ≤ W := (E3.conjSubgroup_mono_left g hBW).trans (le_of_eq hWg)
  have hBginv_le_W : conjSubgroup B g⁻¹ ≤ W :=
    (E3.conjSubgroup_mono_left g⁻¹ hBW).trans (le_of_eq hWg_inv)
  have heC_of_Q : ∀ {e : G}, e ∈ Q → e ∈ centralizer (W : Set G) := by
    intro e he
    exact (Subgroup.mem_inf.1 (hQ ▸ he)).2
  have hBg_le_CGE : conjSubgroup B g ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1 (heC_of_Q (hE_le_Q he)) b (hBg_le_W hb))).symm
  have hBginv_le_CGE : conjSubgroup B g⁻¹ ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1 (heC_of_Q (hE_le_Q he)) b (hBginv_le_W hb))).symm
  have hBg_le_M : conjSubgroup B g ≤ M := hBg_le_CGE.trans hCGE
  have hBginv_le_M : conjSubgroup B g⁻¹ ≤ M := hBginv_le_CGE.trans hCGE
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hnotVg : ¬ conjSubgroup V g ≤ M :=
    not_conjSubgroup_le_normalizer_of_not_isPGroup hV2 hAV hM hgnon2
  have hnotVMg : ¬ V ≤ conjSubgroup M g :=
    not_le_conjSubgroup_of_not_isPGroup hV2 hAV hMnorm hgnon2
  have hB_le_Mg : B ≤ conjSubgroup M g := (conjSubgroup_inv_le_iff B M g).1 hBginv_le_M
  have hE_le_Mg : ⁅A, Q⁆ ≤ conjSubgroup M g :=
    (conjSubgroup_inv_le_iff (⁅A, Q⁆) M g).1 hEginv_le_M
  have hmVg : E3.mQuot V (conjSubgroup M g) ≤ n :=
    (le_of_eq (mQuot_inf_left V (conjSubgroup M g)).symm).trans
      ((E3.mQuot_mono (le_inf (inf_le_left.trans hAV) hB_le_Mg)).trans hmB)
  have hmVg2 : E3.mQuot (conjSubgroup V g) M ≤ n := by
    have hBg_le_M' : conjSubgroup B g ≤ conjSubgroup V g ⊓ M :=
      le_inf (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV)) hBg_le_M
    have h1 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M) ≤ E3.mQuot V B :=
      (E3.mQuot_mono hBg_le_M').trans_eq (E3.mQuot_conjSubgroup V B g)
    exact (le_of_eq (mQuot_inf_left (conjSubgroup V g) M).symm).trans (h1.trans hmB)
  have hInCalO : InCalO n M ⊥ V g := by
    refine ⟨⟨hnotVg, hmVg, ?_⟩, hnotVMg, hmVg2, ?_⟩
    · intro h; exact absurd rfl h
    · intro h; exact absurd rfl h
  have hrkB : rk ↥V = E3.mQuot V B + rk ↥B := by
    have h := E3.card_eq_two_pow_mul (B2F.isPGroup_of_isElemAbelian hV)
      (inf_le_left.trans hAV : B ≤ V)
    rw [card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV),
      card_eq_two_pow_of_isPGroup hB2, ← pow_add] at h
    exact Nat.pow_right_injective (le_refl 2) h
  have hTwoFirst : TwoFirst n M V g := by
    have hc : n - E3.mQuot V B ≤ rk ↥B := by omega
    obtain ⟨I, hIB, hI⟩ := exists_le_mQuot_eq hBab hc
    have hIV : E3.mQuot V I = n := by
      have h := E3.mQuot_add (V := V) (U := I) (U' := B) hIB (inf_le_left.trans hAV)
      rw [hI] at h
      omega
    refine ⟨I, ?_, ?_⟩
    · refine ⟨le_inf (hIB.trans (inf_le_left.trans hAV)) (hIB.trans hB_le_Mg), 1, ?_, ?_⟩
      · simpa [conjSubgroup_one] using hIB.trans (inf_le_left.trans hAV)
      · simpa [conjSubgroup_one] using hIV
    · intro hle
      have hEg_le_CV : conjSubgroup (⁅A, Q⁆) g ≤ centralizer (V : Set G) := by
        refine (le_inf (le_inf (E3.conjSubgroup_mono_left g hE_le_V) hEg_le_M) ?_).trans hle
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro i hi
        exact (Subgroup.mem_centralizer_iff.1 (heC_of_Q (hEg_le_Q he)) i
          (hIB.trans hBW hi))
      have hV_le_C : V ≤ centralizer ((conjSubgroup (⁅A, Q⁆) g : Subgroup G) : Set G) :=
        (Subgroup.le_centralizer_iff).2 hEg_le_CV
      have hCg : centralizer ((conjSubgroup (⁅A, Q⁆) g : Subgroup G) : Set G) ≤
          conjSubgroup M g := by
        rw [← E3.conjSubgroup_centralizer]
        exact E3.conjSubgroup_mono_left g hCGE
      exact hnotVMg (hV_le_C.trans hCg)
  have hTwoDual : TwoDual n M V g := by
    have hBg2 : IsPGroup 2 (conjSubgroup B g) := E3.isPGroup_conjSubgroup hB2 g
    have hc : n - E3.mQuot (conjSubgroup V g) (conjSubgroup B g) ≤ rk ↥(conjSubgroup B g) := by
      have hB' : E3.mQuot (conjSubgroup V g) (conjSubgroup B g) = E3.mQuot V B :=
        E3.mQuot_conjSubgroup V B g
      have h1 : rk ↥(conjSubgroup V g) = E3.mQuot (conjSubgroup V g) (conjSubgroup B g) +
          rk ↥(conjSubgroup B g) := by
        have h := E3.card_eq_two_pow_mul
          (E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g)
          (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV) : conjSubgroup B g ≤ conjSubgroup V g)
        rw [card_eq_two_pow_of_isPGroup (E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g),
          card_eq_two_pow_of_isPGroup hBg2, ← pow_add] at h
        exact Nat.pow_right_injective (le_refl 2) h
      rw [E3.rk_conjSubgroup] at h1
      omega
    obtain ⟨I, hIB, hI⟩ := exists_le_mQuot_eq (E3.isElemAbelian_conjSubgroup hBab g) hc
    have hIVg : E3.mQuot (conjSubgroup V g) I = n := by
      have h := E3.mQuot_add (V := conjSubgroup V g) (U := I) (U' := conjSubgroup B g) hIB
        (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV))
      rw [hI] at h
      have hB' : E3.mQuot (conjSubgroup V g) (conjSubgroup B g) = E3.mQuot V B :=
        E3.mQuot_conjSubgroup V B g
      rw [hB'] at h
      omega
    refine ⟨I, ?_, ?_⟩
    · refine ⟨le_inf (hIB.trans (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV)))
          (hIB.trans hBg_le_M), 1, ?_, ?_⟩
      · simpa [conjSubgroup_one] using hIB.trans (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV))
      · simpa [conjSubgroup_one] using hIVg
    · intro hle
      have hE_le_CVg : ⁅A, Q⁆ ≤ centralizer (conjSubgroup V g : Set G) := by
        refine (le_inf (le_inf hE_le_V hE_le_Mg) ?_).trans hle
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro i hi
        exact (Subgroup.mem_centralizer_iff.1 (heC_of_Q (hE_le_Q he)) i
          (hIB.trans hBg_le_W hi))
      have hVg_le_C : conjSubgroup V g ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) :=
        (Subgroup.le_centralizer_iff).2 hE_le_CVg
      exact hnotVg (hVg_le_C.trans hCGE)
  have hnon2 : ¬ IsPGroup 2 (V ⊔ conjSubgroup V g : Subgroup G) := fun h =>
    hgnon2 (h.to_le (sup_le_sup hAV (E3.conjSubgroup_mono_left g hAV)))
  exact ⟨g, hgH, hInCalO, hTwoFirst, hTwoDual, hnon2⟩

end CFSG.LocalAnalysis.WeakClosure81
