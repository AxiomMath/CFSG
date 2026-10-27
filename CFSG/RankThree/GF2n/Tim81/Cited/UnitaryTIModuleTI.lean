module

public import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryTIModuleComm
public import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryTIModuleSU
public import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryTIModulePpd
import CFSG.Timmesfeld.Transvection.ModelSUTransitiveWitt
public import CFSG.Timmesfeld.Transvection.ModelSUBlock

public section

namespace CFSG.RankThree.GF2n.Tim81.TIModule

open Matrix CFSG.RankThree.FFModules CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

noncomputable abbrev transvComm
    (σ : Representation (ZMod 2) (SU (unitaryInvolution F 2 f) (m + 2)) W) (v : Fin (m + 2) → F) :
    Submodule (ZMod 2) W :=
  commSpan σ (transvGroup (unitaryInvolution F 2 f) (m + 2) v)

@[expose] def IsTIRep (σ : Representation (ZMod 2) (SU (unitaryInvolution F 2 f) (m + 2)) W) :
    Prop :=
  ∀ a b : Fin (m + 2) → F, a ≠ 0 → uForm (unitaryInvolution F 2 f) a a = 0 → b ≠ 0 →
    uForm (unitaryInvolution F 2 f) b b = 0 →
      transvComm σ a = transvComm σ b ∨ transvComm σ a ⊓ transvComm σ b = ⊥

section Basic

variable (hF : Nat.card F = (2 ^ f) ^ 2)
  (σ : Representation (ZMod 2) (SU (unitaryInvolution F 2 f) (m + 2)) W)

include hF in
theorem map_transvComm {v : Fin (m + 2) → F} (hv : uForm (unitaryInvolution F 2 f) v v = 0)
    (g : SU (unitaryInvolution F 2 f) (m + 2)) :
    (transvComm σ v).map (σ g) = transvComm σ (suMat (unitaryInvolution F 2 f) (m + 2) g *ᵥ v) := by
  rw [transvComm, map_commSpan_conjSub, conjSub_transvGroup (unitaryInvolution_involutive hF) hv]

include hF in
theorem transvComm_smul {v : Fin (m + 2) → F} (hv : uForm (unitaryInvolution F 2 f) v v = 0)
    {l : F} (hl : l ≠ 0) : transvComm σ (l • v) = transvComm σ v := by
  rw [transvComm, transvGroup_smul (unitaryInvolution_involutive hF) hv hl]

include hF in
theorem natCard_transvComm (hm : 1 ≤ m) {v w : Fin (m + 2) → F} (hv0 : v ≠ 0)
    (hv : uForm (unitaryInvolution F 2 f) v v = 0) (hw0 : w ≠ 0)
    (hw : uForm (unitaryInvolution F 2 f) w w = 0) :
    Nat.card (transvComm σ v) = Nat.card (transvComm σ w) := by
  obtain ⟨g, hg⟩ := exists_suMat_mulVec_eq_of_iso hF (by omega) hv0 hv hw0 hw
  rw [← hg, ← map_transvComm hF σ hv g, natCard_map_apply]

include hF in
theorem top_le_iSup_transvGroup (hm : 2 ≤ m) :
    (⊤ : Subgroup (SU (unitaryInvolution F 2 f) (m + 2))) ≤
      ⨆ v : {v : Fin (m + 2) → F // v ≠ 0 ∧ uForm (unitaryInvolution F 2 f) v v = 0},
        transvGroup (unitaryInvolution F 2 f) (m + 2) v.1 := by
  have hσF := unitaryInvolution_involutive hF
  refine (eq_top_of_forall_isUTransGroup_le hF (by omega) fun v X hvv hX => ?_).ge
  by_cases hv0 : v = 0
  · intro x hx
    obtain ⟨c, -, hxc⟩ := (hX.1 x).1 hx
    have hx1 : x = 1 := by
      apply suMat_injective (unitaryInvolution F 2 f)
      rw [hxc, hv0, map_one]
      simp [uTrans, uNil]
    rw [hx1]
    exact Subgroup.one_mem _
  · rw [← transvGroup_eq hσF hvv hX]
    exact le_iSup (fun v : {v : Fin (m + 2) → F // v ≠ 0 ∧
      uForm (unitaryInvolution F 2 f) v v = 0} =>
        transvGroup (unitaryInvolution F 2 f) (m + 2) v.1) ⟨v, hv0, hvv⟩

include hF in
theorem commSpan_top_le (hm : 2 ≤ m) :
    commSpan σ ⊤ ≤ ⨆ v : {v : Fin (m + 2) → F // v ≠ 0 ∧ uForm (unitaryInvolution F 2 f) v v = 0},
      transvComm σ v.1 :=
  commSpan_le_iSup_of_le _ (top_le_iSup_transvGroup hF hm)

include hF in
theorem transvComm_ne_bot (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w) {v : Fin (m + 2) → F}
    (hv0 : v ≠ 0) (hv : uForm (unitaryInvolution F 2 f) v v = 0) : transvComm σ v ≠ ⊥ := by
  intro hbot
  have hall : ∀ u : {v : Fin (m + 2) → F // v ≠ 0 ∧ uForm (unitaryInvolution F 2 f) v v = 0},
      transvComm σ u.1 = ⊥ := by
    intro u
    have h := natCard_transvComm hF σ (by omega) hv0 hv u.2.1 u.2.2
    rw [hbot] at h
    rw [Submodule.eq_bot_iff]
    intro y hy
    haveI : Subsingleton ↥(transvComm σ u.1) := by
      have h1 : Nat.card ↥(transvComm σ u.1) = 1 := by
        rw [← h]
        exact Nat.card_unique
      exact (Nat.card_eq_one_iff_unique.1 h1).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨y, hy⟩ : ↥(transvComm σ u.1)) 0)
  obtain ⟨x, w, hxw⟩ := hσ
  have hle := commSpan_top_le hF σ hm
  rw [iSup_eq_bot.2 hall, le_bot_iff] at hle
  have hmem := sub_mem_commSpan (σ := σ) (Subgroup.mem_top x) w
  rw [hle, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hxw hmem

end Basic

section Pairs

private theorem conj_mem_self {G : Type*} [Group G] {T : Subgroup G} {x : G} (hx : x ∈ T) :
    ∀ t ∈ T, x * t * x⁻¹ ∈ T :=
  fun t ht => T.mul_mem (T.mul_mem hx ht) (T.inv_mem hx)

private theorem conj_mem_of_commuting {G : Type*} [Group G] {X T : Subgroup G}
    (hc : Commuting X T) {x : G} (hx : x ∈ X) : ∀ t ∈ T, x * t * x⁻¹ ∈ T := fun t ht => by
  rw [(hc x hx t ht).eq, mul_inv_cancel_right]
  exact ht

private theorem eq_one_of_mem_transvGroup_zero {σ' : F ≃+* F} (hσ' : ∀ c, σ' (σ' c) = c)
    {n : ℕ} {x : SU σ' n} (hx : x ∈ transvGroup σ' n 0) : x = 1 := by
  obtain ⟨c, -, hxc⟩ := ((isUTransGroup_transvGroup hσ' (by simp [uForm_eq])).1 x).1 hx
  apply suMat_injective σ'
  rw [hxc, map_one]
  simp [uTrans, uNil]

variable (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
  (σ : Representation (ZMod 2) (SU (unitaryInvolution F 2 f) (m + 2)) W)

include hF hf in
theorem transvComm_zero_ne_last (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w) :
    transvComm σ (Pi.single 0 1) ≠ transvComm σ (Pi.single (Fin.last (m + 1)) 1) := by
  intro hE
  have hσF := unitaryInvolution_involutive hF
  set e₀ : Fin (m + 2) → F := Pi.single 0 1 with he₀def
  set eL : Fin (m + 2) → F := Pi.single (Fin.last (m + 1)) 1 with heLdef
  set i₁ : Fin (m + 2) := ⟨1, by omega⟩ with hi₁
  set e₁ : Fin (m + 2) → F := Pi.single i₁ 1 with he₁def
  have h0r : (0 : Fin (m + 2)) ≠ Fin.rev 0 := by
    rw [Fin.rev_zero]
    intro h
    have := congrArg Fin.val h
    simp at this
  have hLr : Fin.last (m + 1) ≠ Fin.rev (Fin.last (m + 1)) := by
    rw [Fin.rev_last]
    intro h
    have := congrArg Fin.val h
    simp at this
  have h1r : i₁ ≠ Fin.rev i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [hi₁, Fin.val_rev] at this
    omega
  have hi₁L : i₁ ≠ Fin.last (m + 1) := by
    intro h
    have := congrArg Fin.val h
    simp [hi₁] at this
    omega
  have hri₁ : Fin.rev i₁ ≠ Fin.last (m + 1) := by
    intro h
    have := congrArg Fin.val h
    simp [hi₁, Fin.val_rev] at this
  have he₀ : uForm (unitaryInvolution F 2 f) e₀ e₀ = 0 := uForm_single_self h0r
  have heL : uForm (unitaryInvolution F 2 f) eL eL = 0 := uForm_single_self hLr
  have he₁ : uForm (unitaryInvolution F 2 f) e₁ e₁ = 0 := uForm_single_self h1r
  have he₀1 : uForm (unitaryInvolution F 2 f) e₀ e₁ = 0 := by
    rw [he₀def, uForm_single_left, Fin.rev_zero, he₁def, Pi.single_eq_of_ne hi₁L.symm]
  have he₁L : uForm (unitaryInvolution F 2 f) e₁ eL = 0 := by
    rw [he₁def, uForm_single_left, heLdef, Pi.single_eq_of_ne hri₁]
  have he₀0 : e₀ ≠ 0 := single_one_ne_zero 0
  have he₁0 : e₁ ≠ 0 := single_one_ne_zero i₁
  have heL0 : eL ≠ 0 := single_one_ne_zero _
  have hT₀ := isUTransGroup_transvGroup hσF he₀
  have hTL := isUTransGroup_transvGroup hσF heL
  set E := transvComm σ e₀ with hEdef
  have hE0 : E ≠ ⊥ := transvComm_ne_bot hF σ hm hσ he₀0 he₀
  have hstab : stabSub σ E = ⊤ := by
    refine eq_top_of_uTransLe_outer hF hm ?_ ?_ ?_
    · rw [uTransLe_iff hT₀]
      intro x hx
      exact mem_stabSub_of_forall fun u hu => apply_mem_commSpan (conj_mem_self hx) hu
    · rw [uTransLe_iff hTL]
      intro x hx
      refine mem_stabSub_of_forall fun u hu => ?_
      have hu' : u ∈ transvComm σ eL := hE ▸ hu
      have := apply_mem_commSpan (σ := σ) (conj_mem_self hx) hu'
      exact hE ▸ this
    · intro v hvv hv
      rw [uTransLe_iff (isUTransGroup_transvGroup hσF hvv)]
      intro x hx
      have hc : Commuting (transvGroup (unitaryInvolution F 2 f) (m + 2) v)
          (transvGroup (unitaryInvolution F 2 f) (m + 2) e₀) :=
        (isUTransGroup_transvGroup hσF hvv).commuting hσF hT₀ (uForm_eq_zero_comm hσF hv)
      exact mem_stabSub_of_forall fun u hu => apply_mem_commSpan (conj_mem_of_commuting hc hx) hu
  have hinv : ∀ (g : SU (unitaryInvolution F 2 f) (m + 2)) (u : W), u ∈ E → σ g u ∈ E :=
    fun g u hu => apply_mem_of_mem_stabSub (hstab ▸ Subgroup.mem_top g) hu
  have hall : ∀ v : Fin (m + 2) → F, v ≠ 0 → uForm (unitaryInvolution F 2 f) v v = 0 →
      transvComm σ v = E := by
    intro v hv0 hvv
    obtain ⟨g, hg⟩ := exists_suMat_mulVec_eq_of_iso hF (by omega) he₀0 he₀ hv0 hvv
    rw [← hg, ← map_transvComm hF σ he₀ g]
    exact mem_stabSub.1 (hstab ▸ Subgroup.mem_top g)
  have htop : commSpan σ ⊤ = E :=
    le_antisymm ((commSpan_top_le hF σ hm).trans (iSup_le fun v => (hall v.1 v.2.1 v.2.2).le))
      (commSpan_mono le_top)
  have hperf : commutator (SU (unitaryInvolution F 2 f) (m + 2)) = ⊤ :=
    Group.isPerfect_def.mp (isQuasisimple_SU_of_two_le hF hf (by omega)).1
  have hEE : commSpanOn σ ⊤ E = E := by
    have := commSpanOn_commSpan_of_perfect (σ := σ) hperf
    rwa [htop] at this
  have hswap : ∀ v w : Fin (m + 2) → F, v ≠ 0 → uForm (unitaryInvolution F 2 f) v v = 0 →
      w ≠ 0 → uForm (unitaryInvolution F 2 f) w w = 0 → uForm (unitaryInvolution F 2 f) v w = 0 →
      commSpanOn σ (transvGroup (unitaryInvolution F 2 f) (m + 2) v) E =
        commSpanOn σ (transvGroup (unitaryInvolution F 2 f) (m + 2) w) E := by
    intro v w hv0 hvv hw0 hww hvw
    have hc := (isUTransGroup_transvGroup hσF hvv).commuting hσF
      (isUTransGroup_transvGroup hσF hww) hvw
    have h : commSpanOn σ (transvGroup (unitaryInvolution F 2 f) (m + 2) v) (transvComm σ w) =
        commSpanOn σ (transvGroup (unitaryInvolution F 2 f) (m + 2) w) (transvComm σ v) :=
      commSpanOn_commSpan_comm fun t ht t' ht' => (hc t' ht' t ht).eq.symm
    rwa [hall w hw0 hww, hall v hv0 hvv] at h
  set F' := commSpanOn σ (transvGroup (unitaryInvolution F 2 f) (m + 2) e₀) E with hF'def
  have hF'stab : stabSub σ F' = ⊤ := by
    refine eq_top_of_uTransLe_outer hF hm ?_ ?_ ?_
    · rw [uTransLe_iff hT₀]
      intro x hx
      exact mem_stabSub_of_forall fun u hu =>
        apply_mem_commSpanOn (conj_mem_self hx) (fun y hy => hinv x y hy) hu
    · rw [uTransLe_iff hTL]
      intro x hx
      have h1 : F' = commSpanOn σ (transvGroup (unitaryInvolution F 2 f) (m + 2) eL) E :=
        (hswap e₀ e₁ he₀0 he₀ he₁0 he₁ he₀1).trans (hswap e₁ eL he₁0 he₁ heL0 heL he₁L)
      refine mem_stabSub_of_forall fun u hu => ?_
      rw [h1] at hu ⊢
      exact apply_mem_commSpanOn (conj_mem_self hx) (fun y hy => hinv x y hy) hu
    · intro v hvv hv
      rw [uTransLe_iff (isUTransGroup_transvGroup hσF hvv)]
      intro x hx
      by_cases hv0 : v = 0
      · subst hv0
        rw [eq_one_of_mem_transvGroup_zero hσF hx]
        exact Subgroup.one_mem _
      · have h1 : F' = commSpanOn σ (transvGroup (unitaryInvolution F 2 f) (m + 2) v) E :=
          hswap e₀ v he₀0 he₀ hv0 hvv hv
        refine mem_stabSub_of_forall fun u hu => ?_
        rw [h1] at hu ⊢
        exact apply_mem_commSpanOn (conj_mem_self hx) (fun y hy => hinv x y hy) hu
  have hle : commSpanOn σ ⊤ E ≤ F' := by
    refine commSpanOn_le_of_le (fun v : {v : Fin (m + 2) → F // v ≠ 0 ∧
        uForm (unitaryInvolution F 2 f) v v = 0} =>
          transvGroup (unitaryInvolution F 2 f) (m + 2) v.1) (top_le_iSup_transvGroup hF hm)
      (fun x _ u hu => hinv x u hu) fun v => ?_
    obtain ⟨g, hg⟩ := exists_suMat_mulVec_eq_of_iso hF (by omega) he₀0 he₀ v.2.1 v.2.2
    have h1 : commSpanOn σ (transvGroup (unitaryInvolution F 2 f) (m + 2) v.1) E =
        F'.map (σ g) := by
      rw [hF'def, map_commSpanOn_conjSub, conjSub_transvGroup hσF he₀ g, hg,
        mem_stabSub.1 (hstab ▸ Subgroup.mem_top g)]
    rw [h1, mem_stabSub.1 (hF'stab ▸ Subgroup.mem_top g)]
  have hF'E : F' ≤ E := commSpanOn_le_iff.2 fun t _ u hu => E.sub_mem (hinv t u hu) hu
  have heq : F' = E := le_antisymm hF'E (calc E = commSpanOn σ ⊤ E := hEE.symm
    _ ≤ F' := hle)
  exact commSpanOn_ne_of_isPGroup (isPGroup_transvGroup hσF he₀) (fun p _ e he => hinv p e he)
    hE0 heq

include hF hf in
theorem transvComm_ne_of_uForm_ne_zero (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w)
    {a d : Fin (m + 2) → F} (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d ≠ 0) :
    transvComm σ a ≠ transvComm σ d := by
  have hσF := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  set d' : Fin (m + 2) → F := (uForm (unitaryInvolution F 2 f) a d)⁻¹ • d with hd'def
  have hd'd' : uForm (unitaryInvolution F 2 f) d' d' = 0 := by
    rw [hd'def, uForm_smul_left, uForm_smul_right, hdd, mul_zero, mul_zero]
  have had' : uForm (unitaryInvolution F 2 f) a d' = 1 := by
    rw [hd'def, uForm_smul_right, inv_mul_cancel₀ had]
  have hd' : transvComm σ d' = transvComm σ d := transvComm_smul hF σ hdd (inv_ne_zero had)
  obtain ⟨x, l, hl, hx0, hxL⟩ := exists_suMat_mulVec_eq_pair hσF htr haa hd'd' had'
  have h0r : (0 : Fin (m + 2)) ≠ Fin.rev 0 := by
    rw [Fin.rev_zero]
    intro h
    have := congrArg Fin.val h
    simp at this
  have hLr : Fin.last (m + 1) ≠ Fin.rev (Fin.last (m + 1)) := by
    rw [Fin.rev_last]
    intro h
    have := congrArg Fin.val h
    simp at this
  have he₀ : uForm (unitaryInvolution F 2 f) (Pi.single (0 : Fin (m + 2)) 1 : Fin (m + 2) → F)
      (Pi.single 0 1) = 0 := uForm_single_self h0r
  have heL : uForm (unitaryInvolution F 2 f)
      (Pi.single (Fin.last (m + 1)) 1 : Fin (m + 2) → F) (Pi.single (Fin.last (m + 1)) 1) = 0 :=
    uForm_single_self hLr
  have hinj : Function.Injective (σ x) := fun v w h => by
    have := congrArg (σ x⁻¹) h
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, Module.End.one_apply] at this
  intro heq
  apply transvComm_zero_ne_last hF hf σ hm hσ
  have h1 : (transvComm σ (Pi.single 0 1)).map (σ x) = transvComm σ a := by
    rw [map_transvComm hF σ he₀ x, hx0, transvComm_smul hF σ haa hl]
  have h2 : (transvComm σ (Pi.single (Fin.last (m + 1)) 1)).map (σ x) = transvComm σ d := by
    rw [map_transvComm hF σ heL x, hxL,
      transvComm_smul hF σ hd'd' (inv_ne_zero ((map_ne_zero _).2 hl)), hd']
  exact Submodule.map_injective_of_injective hinj (h1.trans (heq.trans h2.symm))

include hF hf in
theorem transvComm_ne_of_uForm_eq_zero (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w)
    {a v : Fin (m + 2) → F} (ha0 : a ≠ 0) (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hvv : uForm (unitaryInvolution F 2 f) v v = 0) (hav : uForm (unitaryInvolution F 2 f) a v = 0)
    (hva : ∀ c : F, v ≠ c • a) : transvComm σ a ≠ transvComm σ v := by
  have hσF := unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c → ∃ e, e + unitaryInvolution F 2 f e = c :=
    fun c hc => exists_add_unitaryInvolution_eq hF hc
  obtain ⟨z, hzz, haz, hvz⟩ := exists_isotropic_perp_not_perp hσF htr ha0 haa hvv hav hva
  set z' : Fin (m + 2) → F := (uForm (unitaryInvolution F 2 f) a z)⁻¹ • z with hz'def
  have hz'z' : uForm (unitaryInvolution F 2 f) z' z' = 0 := by
    rw [hz'def, uForm_smul_left, uForm_smul_right, hzz, mul_zero, mul_zero]
  have haz' : uForm (unitaryInvolution F 2 f) a z' = 1 := by
    rw [hz'def, uForm_smul_right, inv_mul_cancel₀ haz]
  have hvz' : uForm (unitaryInvolution F 2 f) v z' = 0 := by
    rw [hz'def, uForm_smul_right, hvz, mul_zero]
  intro heq
  apply transvComm_ne_of_uForm_ne_zero hF hf σ hm hσ haa hz'z' (by rw [haz']; exact one_ne_zero)
  have hTa := isUTransGroup_transvGroup hσF haa
  have hTz := isUTransGroup_transvGroup hσF hz'z'
  obtain ⟨w, hw, hwc⟩ := exists_mem_sup_conjSub_eq hσF haa hz'z' haz' hTa hTz
  have hS1 : transvGroup (unitaryInvolution F 2 f) (m + 2) a ≤ stabSub σ (transvComm σ a) :=
    fun x hx => mem_stabSub_of_forall fun u hu => apply_mem_commSpan (conj_mem_self hx) hu
  have hS2 : transvGroup (unitaryInvolution F 2 f) (m + 2) z' ≤ stabSub σ (transvComm σ a) := by
    intro x hx
    have hc : Commuting (transvGroup (unitaryInvolution F 2 f) (m + 2) z')
        (transvGroup (unitaryInvolution F 2 f) (m + 2) v) :=
      hTz.commuting hσF (isUTransGroup_transvGroup hσF hvv) (uForm_eq_zero_comm hσF hvz')
    refine mem_stabSub_of_forall fun u hu => ?_
    have hu' : u ∈ transvComm σ v := heq ▸ hu
    exact heq ▸ apply_mem_commSpan (σ := σ) (conj_mem_of_commuting hc hx) hu'
  have hwS : w ∈ stabSub σ (transvComm σ a) := sup_le hS1 hS2 hw
  show transvComm σ a = commSpan σ (transvGroup (unitaryInvolution F 2 f) (m + 2) z')
  rw [← hwc, ← map_commSpan_conjSub]
  exact (mem_stabSub.1 hwS).symm

variable {σ}

include hF hf in
theorem transvComm_inf_eq_bot (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w) (hTI : IsTIRep σ)
    {a v : Fin (m + 2) → F} (ha0 : a ≠ 0) (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hv0 : v ≠ 0) (hvv : uForm (unitaryInvolution F 2 f) v v = 0) (hva : ∀ c : F, v ≠ c • a) :
    transvComm σ a ⊓ transvComm σ v = ⊥ := by
  rcases hTI a v ha0 haa hv0 hvv with h | h
  · exfalso
    by_cases hav : uForm (unitaryInvolution F 2 f) a v = 0
    · exact transvComm_ne_of_uForm_eq_zero hF hf σ hm hσ ha0 haa hvv hav hva h
    · exact transvComm_ne_of_uForm_ne_zero hF hf σ hm hσ haa hvv hav h
  · exact h

include hF hf in
theorem transvComm_le_fixSub (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w) (hTI : IsTIRep σ)
    {a v : Fin (m + 2) → F} (ha0 : a ≠ 0) (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hv0 : v ≠ 0) (hvv : uForm (unitaryInvolution F 2 f) v v = 0)
    (hav : uForm (unitaryInvolution F 2 f) a v = 0) (hva : ∀ c : F, v ≠ c • a) :
    transvComm σ a ≤ fixSub σ (transvGroup (unitaryInvolution F 2 f) (m + 2) v) := by
  have hσF := unitaryInvolution_involutive hF
  have hc : Commuting (transvGroup (unitaryInvolution F 2 f) (m + 2) v)
      (transvGroup (unitaryInvolution F 2 f) (m + 2) a) :=
    (isUTransGroup_transvGroup hσF hvv).commuting hσF (isUTransGroup_transvGroup hσF haa)
      (uForm_eq_zero_comm hσF hav)
  exact le_fixSub_of_inf_eq_bot
    (fun t ht u hu => apply_mem_commSpan (conj_mem_of_commuting hc ht) hu)
    (transvComm_inf_eq_bot hF hf hm hσ hTI ha0 haa hv0 hvv hva)

private theorem ne_smul_of_uForm_eq_one {a d : Fin (m + 2) → F}
    (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1) :
    ∀ c : F, d ≠ c • a := by
  rintro c rfl
  rw [uForm_smul_right, haa, mul_zero] at had
  exact zero_ne_one had

include hF hf in
theorem eq_zero_of_mem_transvComm_of_fix (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w) (hTI : IsTIRep σ)
    {a d : Fin (m + 2) → F} (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0) (had : uForm (unitaryInvolution F 2 f) a d = 1)
    {x : SU (unitaryInvolution F 2 f) (m + 2)}
    (hx : x ∈ transvGroup (unitaryInvolution F 2 f) (m + 2) a) (hx1 : x ≠ 1) {b : W}
    (hb : b ∈ transvComm σ d) (hbx : σ x b = b) : b = 0 := by
  have hσF := unitaryInvolution_involutive hF
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  obtain ⟨c, hc0, -, hxu⟩ := exists_ne_zero_of_mem_transvGroup hσF haa hx hx1
  have hxd : suMat (unitaryInvolution F 2 f) (m + 2) x *ᵥ d = d + c • a := by
    rw [hxu, had, mul_one]
  have hb' : b ∈ transvComm σ (d + c • a) := by
    rw [← hxd, ← map_transvComm hF σ hdd x]
    exact ⟨b, hb, hbx⟩
  have hiso : uForm (unitaryInvolution F 2 f) (d + c • a) (d + c • a) = 0 := by
    rw [← hxd, uForm_mulVec, hdd]
  have hne : d + c • a ≠ 0 := by
    rw [← hxd]
    exact suMat_mulVec_ne_zero _ x hd0
  have hnp : ∀ μ : F, d + c • a ≠ μ • d := by
    intro μ h
    have h1 := congrArg (uForm (unitaryInvolution F 2 f) a) h
    rw [uForm_add_right, uForm_smul_right, uForm_smul_right, haa, had, mul_zero, add_zero,
      mul_one] at h1
    rw [← h1, one_smul, add_eq_left, smul_eq_zero] at h
    rcases h with h | h
    · exact hc0 h
    · exact ha0 h
  have hinf := transvComm_inf_eq_bot hF hf hm hσ hTI hd0 hdd hne hiso hnp
  have hmem : b ∈ transvComm σ d ⊓ transvComm σ (d + c • a) := ⟨hb, hb'⟩
  rwa [hinf, Submodule.mem_bot] at hmem

include hF hf in
theorem transvComm_le_fixSub_self (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w) (hTI : IsTIRep σ)
    {a d : Fin (m + 2) → F} (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1) :
    transvComm σ a ≤ fixSub σ (transvGroup (unitaryInvolution F 2 f) (m + 2) a) := by
  have hσF := unitaryInvolution_involutive hF
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  intro u hu x hx
  by_cases hx1 : x = 1
  · rw [hx1, map_one, Module.End.one_apply]
  exact fix_of_sub_mem_of_inf_eq_bot (mul_self_eq_one_of_mem_transvGroup hσF haa hx)
    (transvComm_inf_eq_bot hF hf hm hσ hTI ha0 haa hd0 hdd (ne_smul_of_uForm_eq_one haa had))
    (natCard_transvComm hF σ (by omega) ha0 haa hd0 hdd) (fun w => sub_mem_commSpan hx w)
    (fun b hb hbx => eq_zero_of_mem_transvComm_of_fix hF hf hm hσ hTI haa hdd had hx hx1 hb hbx)
    u hu

include hF hf in
theorem commSpan_sup_inf_fixSub_eq_bot (hm : 2 ≤ m) (hσ : ∃ x w, σ x w ≠ w) (hTI : IsTIRep σ)
    {a d : Fin (m + 2) → F} (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1) :
    commSpan σ (transvGroup (unitaryInvolution F 2 f) (m + 2) a ⊔
        transvGroup (unitaryInvolution F 2 f) (m + 2) d) ⊓
      fixSub σ (transvGroup (unitaryInvolution F 2 f) (m + 2) a ⊔
        transvGroup (unitaryInvolution F 2 f) (m + 2) d) = ⊥ := by
  have hσF := unitaryInvolution_involutive hF
  have hda : uForm (unitaryInvolution F 2 f) d a = 1 := uForm_swap_eq_one hσF had
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  rw [commSpan_sup, fixSub_sup, eq_bot_iff]
  rintro v ⟨hv, hva, hvd⟩
  obtain ⟨α, hα, β, hβ, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨x, hx, hx1⟩ := exists_mem_transvGroup_ne_one hσF haa ha0
  obtain ⟨y, hy, hy1⟩ := exists_mem_transvGroup_ne_one hσF hdd hd0
  have hαx : σ x α = α := transvComm_le_fixSub_self hF hf hm hσ hTI haa hdd had hα x hx
  have hβy : σ y β = β := transvComm_le_fixSub_self hF hf hm hσ hTI hdd haa hda hβ y hy
  have hβx : σ x β = β := by
    have h := hva x hx
    rw [map_add, hαx] at h
    exact add_left_cancel h
  have hαy : σ y α = α := by
    have h := hvd y hy
    rw [map_add, hβy] at h
    exact add_right_cancel h
  have hβ0 := eq_zero_of_mem_transvComm_of_fix hF hf hm hσ hTI haa hdd had hx hx1 hβ hβx
  have hα0 := eq_zero_of_mem_transvComm_of_fix hF hf hm hσ hTI hdd haa hda hy hy1 hα hαy
  rw [hα0, hβ0, add_zero]
  exact Submodule.zero_mem _

end Pairs


end CFSG.RankThree.GF2n.Tim81.TIModule
