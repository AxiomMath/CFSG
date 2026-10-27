module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreReps
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreLift
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem seven_eight_core_weight_commutator_zpowers_le {Q : Type} [Group Q] {Xb : Subgroup Q}
    {a : Q} (ha : a ∈ Subgroup.normalizer (Xb : Set Q)) :
    ⁅Xb, Subgroup.zpowers a⁆ ≤ Xb :=
  CFSG.Quasithin.E1.commutator_le_of_le_normalizer (Subgroup.zpowers_le.mpr ha)


theorem Hyp78.exists_map_conj_eq {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] [Finite Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H J φ) {v : G} (hv : v ∈ V) (hvJ : v ∉ J) {Xb : Subgroup Q}
    (hXK : Xb ≤ barSub H φ (kSub V H E))
    (hXL : barSub H φ L ≤ Subgroup.normalizer (Xb : Set Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hXab : ∀ x ∈ Xb, ∀ y ∈ Xb, x * y = y * x) (hexp : ∀ x ∈ Xb, x ^ p = 1)
    (hgen : (⨆ a : ↥(deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩)),
      ⁅Xb, Subgroup.zpowers (a : Q)⁆) = Xb)
    (hcent : ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩),
      ∀ a' ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩), a ≠ a' →
        ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, a' * m = m * a')
    (hcard : ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩),
      Nat.card ↥(⁅Xb, Subgroup.zpowers a⁆ : Subgroup Q) = p)
    {U₀ : Subgroup G} (hU₀ : U₀ ∈ omegaSet V H E) (hU₀L : U₀ ≤ L) {g₀ : G} (hg₀ : g₀ ∈ U₀)
    (hg₀J : g₀ ∉ J) :
    ∃ k l : ↥(deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩)),
      (⨆ j : ↥(deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩)),
          ⨆ (_ : j ≠ k), ⁅Xb, Subgroup.zpowers (j : Q)⁆).map
          (MulAut.conj (φ ⟨g₀, h.omega_le U₀ hU₀ hg₀⟩)).toMonoidHom =
        ⨆ j : ↥(deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩)),
          ⨆ (_ : j ≠ l), ⁅Xb, Subgroup.zpowers (j : Q)⁆ := by
  have hvH : v ∈ H := h.omega_le V h.mem hv
  have hg₀H : g₀ ∈ H := h.omega_le U₀ hU₀ hg₀
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.jnormal
  haveI : (J.subgroupOf H).Normal := h.jnormal
  let Ob : Subgroup Q := barSub H φ (pCoreOf 2 L)
  let vb : Q := φ ⟨v, hvH⟩
  let Δ : Type := ↥(deltaSet Ob vb)
  let dbar : Q := φ ⟨g₀, hg₀H⟩
  have hXp : IsPGroup p Xb := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hexp (x : Q) x.2)⟩
  have hoddXb : Odd (Nat.card Xb) := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXp
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hF : SevenEightFrame (barSub H φ L) Ob
      (barSet H φ {u | ∃ U ∈ omegaWithin V H E L, u ∈ U ∧ u ∉ J}) vb :=
    h.sevenEightFrame hV2 hφ hv hvJ
  have hnorm : ∀ a : Δ, (a : Q) ∈ Subgroup.normalizer (Xb : Set Q) := by
    intro a
    exact hXL (hF.mul_self_and_mem_of_mem_deltaSet a.2).2
  have hMbar_le_Xb : ∀ a : Δ, ⁅Xb, Subgroup.zpowers (a : Q)⁆ ≤ Xb :=
    fun a => seven_eight_core_weight_commutator_zpowers_le (hnorm a)
  let hCbar : Δ → Subgroup Q := fun a =>
    ⨆ j : Δ, ⨆ (_ : j ≠ a), ⁅Xb, Subgroup.zpowers (j : Q)⁆
  have hCbar_le_Xb : ∀ a : Δ, hCbar a ≤ Xb :=
    fun a => iSup_le fun j => iSup_le fun _ => hMbar_le_Xb j
  have hne : ∀ a ∈ deltaSet Ob vb, ⁅Xb, Subgroup.zpowers a⁆ ≠ ⊥ := by
    intro a ha hbot
    have h1 : Nat.card ↥(⁅Xb, Subgroup.zpowers a⁆) = p := hcard a ha
    rw [hbot, Subgroup.card_bot] at h1
    exact hp.ne_one h1.symm
  have hD : ∀ a : Δ,
      ⁅Xb, Subgroup.zpowers (a : Q)⁆ ⊓ hCbar a = ⊥ ∧
      ⁅Xb, Subgroup.zpowers (a : Q)⁆ ⊔ hCbar a = Xb ∧
      (∀ x ∈ Xb, (a : Q) * x = x * (a : Q) → x ∈ hCbar a) := by
    intro a
    exact inf_eq_bot_and_sup_eq_of_iSup_eq hoddXb hXab (fun j : Δ => (j : Q))
      (fun j => (hF.mul_self_and_mem_of_mem_deltaSet j.2).1) hnorm
      (fun i j hij => hcent (j : Q) j.2 (i : Q) i.2 (fun h => (Ne.symm hij) (Subtype.ext h)))
      hgen a
  have hsup : ∀ a : Δ, ⁅Xb, Subgroup.zpowers (a : Q)⁆ ⊔ hCbar a = Xb := fun a => (hD a).2.1
  have hinf : ∀ a : Δ, ⁅Xb, Subgroup.zpowers (a : Q)⁆ ⊓ hCbar a = ⊥ := fun a => (hD a).1
  have hfixpts : ∀ a : Δ, ∀ x ∈ Xb, (a : Q) * x = x * (a : Q) → x ∈ hCbar a :=
    fun a => (hD a).2.2
  have hXb_norm_Cbar : ∀ a : Δ, Xb ≤ Subgroup.normalizer (hCbar a : Set Q) := by
    intro a
    have hcentXb : Xb ≤ Subgroup.centralizer (Xb : Set Q) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (IsMulCommutative.of_comm (fun x y : Xb => Subtype.ext (hXab x x.2 y y.2)))
    exact hcentXb.trans ((Subgroup.centralizer_le (show (hCbar a : Set Q) ⊆ (Xb : Set Q) from
      hCbar_le_Xb a)).trans (Subgroup.centralizer_le_normalizer _))
  have hMbar_le_norm : ∀ a : Δ, ⁅Xb, Subgroup.zpowers (a : Q)⁆ ≤
      Subgroup.normalizer (hCbar a : Set Q) :=
    fun a => (hMbar_le_Xb a).trans (hXb_norm_Cbar a)
  have hcentC : ∀ a : Δ, ∀ m ∈ hCbar a, (a : Q) * m = m * (a : Q) := by
    intro a m hm
    have hc : hCbar a ≤ Subgroup.centralizer ({(a : Q)} : Set Q) := by
      refine iSup_le fun j => iSup_le fun (hj : j ≠ a) => ?_
      intro m' hm'
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcent (j : Q) j.2 (a : Q) a.2 (fun h => hj (Subtype.ext h)) m' hm'
    exact (Subgroup.mem_centralizer_iff.mp (hc hm)) (a : Q) (Set.mem_singleton _)
  have hCbar_rel : ∀ a : Δ, (hCbar a).relIndex Xb = p := by
    intro a
    have h1 : (hCbar a).relIndex Xb =
        (hCbar a).relIndex (⁅Xb, Subgroup.zpowers (a : Q)⁆ ⊔ hCbar a) := by rw [hsup a]
    have h2 : (hCbar a).relIndex (⁅Xb, Subgroup.zpowers (a : Q)⁆ ⊔ hCbar a) =
        (hCbar a).relIndex ⁅Xb, Subgroup.zpowers (a : Q)⁆ :=
      relIndex_sup_right_of_le_normalizer (hMbar_le_norm a)
    have h3 : (hCbar a).relIndex ⁅Xb, Subgroup.zpowers (a : Q)⁆ =
        (hCbar a ⊓ ⁅Xb, Subgroup.zpowers (a : Q)⁆).relIndex
          ⁅Xb, Subgroup.zpowers (a : Q)⁆ :=
      (Subgroup.inf_relIndex_right (hCbar a) ⁅Xb, Subgroup.zpowers (a : Q)⁆).symm
    have hbot : hCbar a ⊓ ⁅Xb, Subgroup.zpowers (a : Q)⁆ = ⊥ := by
      rw [inf_comm]; exact hinf a
    rw [h1, h2, h3, hbot, Subgroup.relIndex_bot_left, hcard (a : Q) a.2]
  have hvbΔ : vb ∈ deltaSet Ob vb := ⟨1, Ob.one_mem, by rw [one_mul, inv_one, mul_one]⟩
  by_cases hcommbot : ⁅Xb, Subgroup.zpowers dbar⁆ = ⊥
  · refine ⟨⟨vb, hvbΔ⟩, ⟨vb, hvbΔ⟩, ?_⟩
    change (hCbar ⟨vb, hvbΔ⟩).map (MulAut.conj dbar).toMonoidHom = hCbar ⟨vb, hvbΔ⟩
    have hXb_cent : Xb ≤ Subgroup.centralizer (Subgroup.zpowers dbar : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot
    have hfix : ∀ m ∈ hCbar ⟨vb, hvbΔ⟩, (MulAut.conj dbar).toMonoidHom m = m := by
      intro m hm
      have hmX : m ∈ Xb := hCbar_le_Xb ⟨vb, hvbΔ⟩ hm
      have hcomm : dbar * m = m * dbar :=
        (Subgroup.mem_centralizer_iff.mp (hXb_cent hmX)) dbar (Subgroup.mem_zpowers dbar)
      change dbar * m * dbar⁻¹ = m
      rw [hcomm]; group
    apply le_antisymm
    · intro y hy
      obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hy
      rw [← hmx, hfix m hm]
      exact hm
    · intro m hm
      exact Subgroup.mem_map.mpr ⟨m, hm, hfix m hm⟩
  · have hne₀ : ⁅Xb, Subgroup.zpowers dbar⁆ ≠ ⊥ := hcommbot
    obtain ⟨Y, hYc, hYK⟩ := Hyp73.exists_isHallCompl_le_kSub h.toHyp73 hφ hXK hp hp2 hexp
    obtain ⟨w, hwH, hwφ, hw2, hwY, hwcent⟩ :=
      Hyp78.exists_normalizing_reps h hV2 hφ hv hvJ hXL hp hp2 hXp hexp hne hYc
    have hIJ : iSub V H E ≤ J := by
      rw [← hYc.inf_J]; exact inf_le_right
    have hIleH : iSub V H E ≤ H := hIJ.trans hJH
    have hHnormI : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
      le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le h.normal)
    have hI : IsElemAbelian 2 (iSub V H E) :=
      seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
    have hYI : Y ≤ Subgroup.normalizer (iSub V H E : Set G) :=
      (hYc.le_X.trans (barPre_le H φ Xb)).trans hHnormI
    have hrelIY : (iSub V H E).relIndex Y = Nat.card Xb := by
      have h := hYc.relIndex_inf_barPre hφ hJH h.jnormal (Ab := Xb) le_rfl
      rwa [inf_eq_left.mpr hYc.le_X] at h
    have hodd : Odd ((iSub V H E).relIndex Y) := by rw [hrelIY]; exact hoddXb
    have hYab : ⁅Y, Y⁆ ≤ iSub V H E := by
      rw [Subgroup.commutator_le]
      intro y hy y' hy'
      obtain ⟨hyH, hyX⟩ := mem_barPre.mp (hYc.le_X hy)
      obtain ⟨hy'H, hy'X⟩ := mem_barPre.mp (hYc.le_X hy')
      have hcommH : ⁅y, y'⁆ ∈ H := by
        rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem hyH hy'H) (H.inv_mem hyH)) (H.inv_mem hy'H)
      have hφcomm : φ ⟨⁅y, y'⁆, hcommH⟩ = 1 := by
        rw [show (⟨⁅y, y'⁆, hcommH⟩ : ↥H) =
            ⁅(⟨y, hyH⟩ : ↥H), (⟨y', hy'H⟩ : ↥H)⁆ from Subtype.ext rfl,
          map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm.mpr (hXab _ hyX _ hy'X)]
      have hJmem : ⁅y, y'⁆ ∈ J := (hφ.ker_iff ⟨_, hcommH⟩).mp hφcomm
      have hcommY : ⁅y, y'⁆ ∈ Y := by
        rw [commutatorElement_def]
        exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy hy') (Y.inv_mem hy)) (Y.inv_mem hy')
      rw [← hYc.inf_J]
      exact Subgroup.mem_inf.mpr ⟨hcommY, hJmem⟩
    have hexpY : ∀ y ∈ Y, y ^ p ∈ iSub V H E := by
      intro y hy
      obtain ⟨hyH, hyX⟩ := mem_barPre.mp (hYc.le_X hy)
      have hpowH : y ^ p ∈ H := H.pow_mem hyH p
      have hφpow : φ ⟨y ^ p, hpowH⟩ = 1 := by
        rw [show (⟨y ^ p, hpowH⟩ : ↥H) = (⟨y, hyH⟩ : ↥H) ^ p from Subtype.ext rfl,
          map_pow, hexp _ hyX]
      have hJmem : y ^ p ∈ J := (hφ.ker_iff ⟨_, hpowH⟩).mp hφpow
      rw [← hYc.inf_J]
      exact Subgroup.mem_inf.mpr ⟨Y.pow_mem hy p, hJmem⟩
    have hYne : iSub V H E ≠ Y := by
      intro hIY
      have hcardXb : Nat.card Xb = 1 := by
        rw [← hrelIY, hIY, Subgroup.relIndex_self]
      have hXbbot : Xb = ⊥ := Subgroup.eq_bot_of_card_eq Xb hcardXb
      exact hne vb hvbΔ (by rw [hXbbot, Subgroup.commutator_bot_left])
    have hfaith : Y ⊓ Subgroup.centralizer (iSub V H E : Set G) ≤ iSub V H E := by
      have hWleK : Y ⊓ Subgroup.centralizer (iSub V H E : Set G) ≤
          kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) :=
        le_inf (inf_le_left.trans hYK) inf_le_right
      have h7 := seven_four h.elemAbelian h.ti h.abelian h.le h.normal h.omega_le
      have hoddCore : CFSG.QuasithinUnique.oddCoreIn (kSub V H E) = ⊥ := h.oddCore
      rw [hoddCore, sup_bot_eq] at h7
      have hW2 : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (iSub V H E : Set G)) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kSub V H E)).to_le (hWleK.trans h7)
      have hIW : iSub V H E ≤ Y ⊓ Subgroup.centralizer (iSub V H E : Set G) :=
        le_inf hYc.iSub_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr hI.1)
      have hdvd : (iSub V H E).relIndex (Y ⊓ Subgroup.centralizer (iSub V H E : Set G)) ∣
          (iSub V H E).relIndex Y :=
        ⟨(Y ⊓ Subgroup.centralizer (iSub V H E : Set G)).relIndex Y,
          (Subgroup.relIndex_mul_relIndex (iSub V H E)
            (Y ⊓ Subgroup.centralizer (iSub V H E : Set G)) Y hIW inf_le_left).symm⟩
      exact le_of_isPGroup_of_odd_relIndex hW2 (Odd.of_dvd_nat hodd hdvd)
    let Mf : Δ → Subgroup G := fun i => Y ⊓ barPre H φ (⁅Xb, Subgroup.zpowers (i : Q)⁆)
    let Cf : Δ → Subgroup G := fun i => Y ⊓ barPre H φ (hCbar i)
    have hIC : ∀ i : Δ, iSub V H E ≤ Cf i :=
      fun i => le_inf hYc.iSub_le (hIJ.trans (le_barPre hJH hφ (hCbar i)))
    have hCY : ∀ i : Δ, Cf i ≤ Y := fun i => inf_le_left
    have hIM : ∀ i : Δ, iSub V H E ≤ Mf i :=
      fun i => le_inf hYc.iSub_le
        (hIJ.trans (le_barPre hJH hφ (⁅Xb, Subgroup.zpowers (i : Q)⁆)))
    have hMY : ∀ i : Δ, Mf i ≤ Y := fun i => inf_le_left
    have hM : ∀ i : Δ, (iSub V H E).relIndex (Mf i) = p :=
      fun i => (hYc.relIndex_inf_barPre hφ hJH h.jnormal (hMbar_le_Xb i)).trans
        (hcard (i : Q) i.2)
    have hC : ∀ i : Δ, (Cf i).relIndex Y = p := by
      intro i
      have hmul := Subgroup.relIndex_mul_relIndex (iSub V H E) (Cf i) Y (hIC i) (hCY i)
      have hrelIC : (iSub V H E).relIndex (Cf i) = Nat.card (hCbar i) :=
        hYc.relIndex_inf_barPre hφ hJH h.jnormal (hCbar_le_Xb i)
      have hmulX := Subgroup.relIndex_mul_relIndex ⊥ (hCbar i) Xb bot_le (hCbar_le_Xb i)
      rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at hmulX
      have hpos : Nat.card (hCbar i) ≠ 0 := by
        haveI : Nonempty (hCbar i) := ⟨1⟩
        exact Nat.card_pos.ne'
      have key : Nat.card (hCbar i) * (Cf i).relIndex Y = Nat.card (hCbar i) * p := by
        calc Nat.card (hCbar i) * (Cf i).relIndex Y
            = (iSub V H E).relIndex (Cf i) * (Cf i).relIndex Y := by rw [hrelIC]
          _ = (iSub V H E).relIndex Y := hmul
          _ = Nat.card Xb := hrelIY
          _ = Nat.card (hCbar i) * (hCbar i).relIndex Xb := hmulX.symm
          _ = Nat.card (hCbar i) * p := by rw [hCbar_rel i]
      exact mul_left_cancel₀ hpos key
    have hYv : ∀ i : Δ, ∀ y ∈ Y, ⁅y, w i⁆ ∈ Mf i := by
      intro i y hy
      have hwa : w i * y⁻¹ * (w i)⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hwY i) y⁻¹).mp (Y.inv_mem hy)
      have hcommY : ⁅y, w i⁆ ∈ Y := by
        rw [commutatorElement_def]
        rw [show y * w i * y⁻¹ * (w i)⁻¹ = y * (w i * y⁻¹ * (w i)⁻¹) by group]
        exact Y.mul_mem hy hwa
      refine Subgroup.mem_inf.mpr ⟨hcommY, ?_⟩
      obtain ⟨hyH, hyX⟩ := mem_barPre.mp (hYc.le_X hy)
      have hcommH : ⁅y, w i⁆ ∈ H := by
        rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem hyH (hwH i)) (H.inv_mem hyH)) (H.inv_mem (hwH i))
      refine mem_barPre.mpr ⟨hcommH, ?_⟩
      have hφcomm : φ ⟨⁅y, w i⁆, hcommH⟩ = ⁅φ ⟨y, hyH⟩, (i : Q)⁆ := by
        rw [show (⟨⁅y, w i⁆, hcommH⟩ : ↥H) =
            ⁅(⟨y, hyH⟩ : ↥H), (⟨w i, hwH i⟩ : ↥H)⁆ from Subtype.ext rfl,
          map_commutatorElement, hwφ i]
      rw [hφcomm]
      exact Subgroup.commutator_mem_commutator hyX (Subgroup.mem_zpowers (i : Q))
    have hCv : ∀ i : Δ, ∀ c ∈ Cf i, ⁅c, w i⁆ ∈ iSub V H E := by
      intro i c hc
      obtain ⟨hcY, hcbar⟩ := Subgroup.mem_inf.mp hc
      obtain ⟨hcH, hcCbar⟩ := mem_barPre.mp hcbar
      have hwa : w i * c⁻¹ * (w i)⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hwY i) c⁻¹).mp (Y.inv_mem hcY)
      have hcommY : ⁅c, w i⁆ ∈ Y := by
        rw [commutatorElement_def]
        rw [show c * w i * c⁻¹ * (w i)⁻¹ = c * (w i * c⁻¹ * (w i)⁻¹) by group]
        exact Y.mul_mem hcY hwa
      have hcommH : ⁅c, w i⁆ ∈ H := by
        rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem hcH (hwH i)) (H.inv_mem hcH)) (H.inv_mem (hwH i))
      have hcommφ : φ ⟨⁅c, w i⁆, hcommH⟩ = 1 := by
        rw [show (⟨⁅c, w i⁆, hcommH⟩ : ↥H) =
            ⁅(⟨c, hcH⟩ : ↥H), (⟨w i, hwH i⟩ : ↥H)⁆ from Subtype.ext rfl,
          map_commutatorElement, hwφ i,
          commutatorElement_eq_one_iff_mul_comm.mpr (hcentC i _ hcCbar).symm]
      have hJmem : ⁅c, w i⁆ ∈ J := (hφ.ker_iff ⟨_, hcommH⟩).mp hcommφ
      rw [← hYc.inf_J]
      exact Subgroup.mem_inf.mpr ⟨hcommY, hJmem⟩
    have hCfix : ∀ i : Δ, ∀ y ∈ Y, ⁅y, w i⁆ ∈ iSub V H E → y ∈ Cf i := by
      intro i y hy hyI
      obtain ⟨hyH, hyX⟩ := mem_barPre.mp (hYc.le_X hy)
      refine Subgroup.mem_inf.mpr ⟨hy, ?_⟩
      have hφcomm : φ ⟨⁅y, w i⁆, hIleH hyI⟩ = ⁅φ ⟨y, hyH⟩, (i : Q)⁆ := by
        rw [show (⟨⁅y, w i⁆, hIleH hyI⟩ : ↥H) =
            ⁅(⟨y, hyH⟩ : ↥H), (⟨w i, hwH i⟩ : ↥H)⁆ from Subtype.ext rfl,
          map_commutatorElement, hwφ i]
      have hφ1 : φ ⟨⁅y, w i⁆, hIleH hyI⟩ = 1 :=
        (hφ.ker_iff ⟨_, hIleH hyI⟩).mpr (hIJ hyI)
      have hcomm1 : ⁅φ ⟨y, hyH⟩, (i : Q)⁆ = 1 := by rw [← hφcomm]; exact hφ1
      refine mem_barPre.mpr ⟨hyH, ?_⟩
      exact hfixpts i _ hyX (commutatorElement_eq_one_iff_mul_comm.mp hcomm1).symm
    have hcentW : ∀ i : Δ, ∀ c ∈ Cf i, ∀ z ∈ iSub V H E,
        c * ⁅z, w i⁆ = ⁅z, w i⁆ * c := by
      intro i c hc z hz
      let T : Subgroup G :=
        iSub V H E ⊔ ⨆ b : Δ, ⨆ (_ : b ≠ i), ⁅Y, Subgroup.zpowers (w b)⁆
      have hTY : T ≤ Y := by
        refine sup_le hYc.iSub_le ?_
        refine iSup_le fun b => iSup_le fun _ => ?_
        exact CFSG.Quasithin.E1.commutator_le_of_le_normalizer (Subgroup.zpowers_le.mpr (hwY b))
      have hCbar_le_barSubT : hCbar i ≤ barSub H φ T := by
        refine iSup_le fun j => iSup_le fun (hj : j ≠ i) => ?_
        have hMbar_eq : ⁅Xb, Subgroup.zpowers (j : Q)⁆ =
            ⁅Xb, Subgroup.zpowers (φ ⟨w j, hwH j⟩)⁆ := by rw [hwφ j]
        rw [hMbar_eq]
        refine (hYc.commutator_zpowers_le_barSub hφ hJH h.jnormal (hwH j)).trans ?_
        have hinner : ⁅Y, Subgroup.zpowers (w j)⁆ ≤
            ⨆ b : Δ, ⨆ (_ : b ≠ i), ⁅Y, Subgroup.zpowers (w b)⁆ :=
          (le_iSup (fun (_ : j ≠ i) => ⁅Y, Subgroup.zpowers (w j)⁆) hj).trans
            (le_iSup (fun b : Δ => ⨆ (_ : b ≠ i), ⁅Y, Subgroup.zpowers (w b)⁆) j)
        have hTle : ⁅Y, Subgroup.zpowers (w j)⁆ ≤ T := hinner.trans le_sup_right
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hTle)
      have hCT : Cf i ≤ T := hYc.inf_barPre_le hφ le_sup_left hTY hCbar_le_barSubT
      have hcommI : ⁅iSub V H E, Subgroup.zpowers (w i)⁆ ≤ iSub V H E :=
        CFSG.Quasithin.E1.commutator_le_of_le_normalizer
          (Subgroup.zpowers_le.mpr (hHnormI (hwH i)))
      have hT_cent : T ≤ Subgroup.centralizer
          ((⁅iSub V H E, Subgroup.zpowers (w i)⁆ : Subgroup G) : Set G) := by
        refine sup_le ?_ ?_
        · exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr hI.1).trans
            (Subgroup.centralizer_le (show (⁅iSub V H E, Subgroup.zpowers (w i)⁆ :
              Subgroup G) ≤ iSub V H E from hcommI))
        · refine iSup_le fun b => iSup_le fun (hb : b ≠ i) => ?_
          intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro z' hz'
          exact (hwcent i b (Ne.symm hb) y hy z' hz').symm
      have hzmem : ⁅z, w i⁆ ∈ ⁅iSub V H E, Subgroup.zpowers (w i)⁆ :=
        Subgroup.commutator_mem_commutator hz (Subgroup.mem_zpowers (w i))
      exact (Subgroup.mem_centralizer_iff.mp (hT_cent (hCT hc)) ⁅z, w i⁆ hzmem).symm
    have hgenM : (⨆ i : Δ, Mf i) = Y := by
      apply le_antisymm
      · exact iSup_le fun i => inf_le_left
      · have hIT' : iSub V H E ≤ ⨆ i : Δ, Mf i :=
          (hIM ⟨vb, hvbΔ⟩).trans (le_iSup Mf ⟨vb, hvbΔ⟩)
        have hXb_le : Xb ≤ barSub H φ (⨆ i : Δ, Mf i) := by
          rw [← hgen]
          refine iSup_le fun i => ?_
          have hbar : barSub H φ (Mf i) = ⁅Xb, Subgroup.zpowers (i : Q)⁆ :=
            hYc.barSub_inf_barPre hφ hJH h.jnormal (hMbar_le_Xb i)
          rw [← hbar]
          exact Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_iSup Mf i))
        have h := hYc.inf_barPre_le hφ hIT' (iSup_le fun i => inf_le_left) hXb_le
        rwa [inf_eq_left.mpr hYc.le_X] at h
    obtain ⟨U', hU', hU'U, g₁, hg₁U, hg₁J, hg₁Y, hg₀g₁J⟩ :=
      Hyp78.exists_normalizing_rep_of_mem_omegaSet h hV2 hφ hXL hp hp2 hexp hYc hU₀ hU₀L
        hg₀ hg₀J hne₀
    have hg₁H : g₁ ∈ H := h.omega_le U' hU' hg₁U
    have hφg₁ : φ ⟨g₁, hg₁H⟩ = dbar := by
      have hker : φ ⟨g₀⁻¹ * g₁, H.mul_mem (H.inv_mem hg₀H) hg₁H⟩ = 1 :=
        (hφ.ker_iff ⟨_, H.mul_mem (H.inv_mem hg₀H) hg₁H⟩).mpr hg₀g₁J
      have h1 : φ ⟨g₀⁻¹ * g₁, H.mul_mem (H.inv_mem hg₀H) hg₁H⟩ =
          (φ ⟨g₀, hg₀H⟩)⁻¹ * φ ⟨g₁, hg₁H⟩ := by
        rw [show (⟨g₀⁻¹ * g₁, H.mul_mem (H.inv_mem hg₀H) hg₁H⟩ : ↥H) =
            (⟨g₀, hg₀H⟩ : ↥H)⁻¹ * ⟨g₁, hg₁H⟩ from Subtype.ext rfl, map_mul, map_inv]
      rw [h1] at hker
      calc φ ⟨g₁, hg₁H⟩ = dbar * (dbar⁻¹ * φ ⟨g₁, hg₁H⟩) := by group
        _ = dbar * 1 := by rw [hker]
        _ = dbar := mul_one _
    have hg₁I : g₁ ∈ Subgroup.normalizer (iSub V H E : Set G) := hHnormI hg₁H
    obtain ⟨k, l, hweights⟩ := exists_map_conj_eq_of_weights hp hp2 hI hYc.iSub_le hYI hodd
      hYab hexpY hYne hfaith w Mf Cf hIC hCY hC hIM hMY hM hw2 hwY
      (fun i => hHnormI (hwH i)) hYv hCv hCfix hcentW hgenM hg₁Y hg₁I
    have hbarC : ∀ i : Δ, barSub H φ (Cf i) = hCbar i :=
      fun i => hYc.barSub_inf_barPre hφ hJH h.jnormal (hCbar_le_Xb i)
    have hmapbar := congrArg (barSub H φ) hweights
    rw [barSub_map_conj φ (Cf k) ⟨g₁, hg₁H⟩, hbarC k, hbarC l, hφg₁] at hmapbar
    refine ⟨k, l, ?_⟩
    change (hCbar k).map (MulAut.conj dbar).toMonoidHom = hCbar l
    exact hmapbar


end CFSG.LocalAnalysis.WeakClosure81
