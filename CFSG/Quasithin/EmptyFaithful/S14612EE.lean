module

public import CFSG.Quasithin.EmptyFaithful.S14612ED
public import CFSG.Quasithin.EmptyFaithful.S14612DA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
open scoped commutatorElement

section Transport

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem uHi_le_normalizer (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (Hi : Subgroup G) (hHi : Hi ≤ H) :
    ⁅conjClosure (VZ T M) H, Hi⁆ ⊔ quasithinOmegaOneCenter T ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  sup_le ((S145.commutator_le_of_le_normalizer (hHi.trans (le_normalizer_conjClosure _ _))).trans
    (U_le_normalizer h)) Subgroup.le_normalizer

theorem mIdx_uHi_eq
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Lb : Subgroup (MulAut ↥(kOf (rhoH h)))} (hLb : Lb ≤ (resBeta (rhoH h)).range) :
    mIdx (⁅conjClosure (VZ T M) H, HLb (resBeta (rhoH h)) Lb⁆ ⊔ quasithinOmegaOneCenter T)
      (quasithinOmegaOneCenter T) = rk (commV Lb) := by
  have hd := tildeOf_comm_HLb h hsplit hLb
  have hYN := uHi_le_normalizer h (HLb (resBeta (rhoH h)) Lb) (HLb_le Lb)
  have h1 := relIndex_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (T := quasithinOmegaOneCenter T)
    (H := ⁅conjClosure (VZ T M) H, HLb (resBeta (rhoH h)) Lb⁆ ⊔ quasithinOmegaOneCenter T)
    le_rfl le_sup_right hYN
  have h2 : secImg (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  have h3 : (quasithinOmegaOneCenter T).relIndex
      (⁅conjClosure (VZ T M) H, HLb (resBeta (rhoH h)) Lb⁆ ⊔ quasithinOmegaOneCenter T) =
      Nat.card (commV Lb) := by
    rw [← h1]
    change Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) _) = _
    rw [hd, Subgroup.card_map_of_injective (valK_injective h)]
  have hV : ∀ v : ↥(kOf (rhoH h)), v ^ 2 = 1 := fun v => Subtype.ext (IntMod.sq_eq_one (v : UMod h))
  unfold mIdx
  rw [h3, card_eq_two_pow hV, padicValNat.prime_pow]

theorem isDecP_of_blocks
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hred : IsRedCE T M H PQ p)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    (hker : (resBeta (rhoH h)).ker.map H.subtype = pCoreOf 2 H)
    {L₁ L₂ : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hB : Blocks14612 (resBeta (rhoH h)).range ((T.subgroupOf H).map (resBeta (rhoH h)))
      ((PQ.subgroupOf H).map (resBeta (rhoH h))) p L₁ L₂) :
    ∃ H₀ H₁ H₂ : Subgroup G, ∃ t : G, IsDecP T M H p H₀ H₁ H₂ t := by
  classical
  set β := resBeta (rhoH h) with hβ
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  obtain ⟨τ, hτ, hτL⟩ := hB.swap
  obtain ⟨x, hxT, rfl⟩ := hτ
  have hxT' : (x : G) ∈ T := hxT
  have htH : (x : G) ∈ H := x.2
  have hxe : (⟨(x : G), htH⟩ : ↥H) = x := Subtype.ext rfl
  have hperm : ∀ y ∈ β.range, (conjBy y L₁ = L₁ ∧ conjBy y L₂ = L₂) ∨
      (conjBy y L₁ = L₂ ∧ conjBy y L₂ = L₁) := by
    intro y hy
    have hτr : β x ∈ β.range := ⟨x, rfl⟩
    have h2 : conjBy y L₂ = conjBy (y * β x) L₁ := by rw [← hτL, conjBy_conjBy]
    rcases hB.orb y hy with h1 | h1
    · left
      refine ⟨h1, ?_⟩
      rcases hB.orb (y * β x) (β.range.mul_mem hy hτr) with h3 | h3
      · exfalso
        have : conjBy y L₂ = conjBy y L₁ := by rw [h2, h3, h1]
        exact hB.ne (conjBy_injective y this)
      · rw [h2, h3]
    · right
      refine ⟨h1, ?_⟩
      rcases hB.orb (y * β x) (β.range.mul_mem hy hτr) with h3 | h3
      · rw [h2, h3]
      · exfalso
        have : conjBy y L₂ = conjBy y L₁ := by rw [h2, h3, h1]
        exact hB.ne (conjBy_injective y this)
  have hconjle : ∀ (g : MulAut ↥(kOf (rhoH h))) (A : Subgroup (MulAut ↥(kOf (rhoH h)))),
      g ∈ β.range → A ≤ β.range → conjBy g A ≤ β.range := by
    intro g A hg hA z hz
    rw [mem_conjBy_iff] at hz
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this]
    exact β.range.mul_mem (β.range.mul_mem hg (hA hz)) (β.range.inv_mem hg)
  have hNH : ∀ (s : G) (hs : s ∈ H) (A : Subgroup (MulAut ↥(kOf (rhoH h)))), A ≤ β.range →
      (s ∈ Subgroup.normalizer (HLb β A : Set G) ↔ conjBy (β ⟨s, hs⟩) A = A) := by
    intro s hs A hA
    have h2 : conjSub s (HLb β A) = HLb β (conjBy (β ⟨s, hs⟩) A) :=
      conjSub_HLb hs (fun z => mem_conjBy_iff)
    constructor
    · intro hn
      have h1 := conjSub_eq_of_mem_normalizer hn
      rw [h2] at h1
      exact HLb_injective (hconjle _ A ⟨⟨s, hs⟩, rfl⟩ hA) hA h1
    · intro hc
      rw [hc] at h2
      exact CosetGeom.mem_normalizer_of_conjSub_eq h2
  set H₁ := HLb β L₁ with hH₁
  set H₂ := HLb β L₂ with hH₂
  set H₀ := HLb β (L₁ ⊔ L₂) with hH₀
  have hconjSub : conjSub (x : G) H₁ = H₂ := by
    rw [hH₂]
    have hβx : β ⟨(x : G), htH⟩ = β x := congrArg β hxe
    exact conjSub_HLb htH (fun z => by
      rw [hβx, ← hτL, mem_conjBy_iff])
  have hLsup : L₁ ⊔ L₂ ≤ β.range := sup_le hB.le₁ hB.le₂
  have hdict₁ := tildeOf_comm_HLb h hsplit hB.le₁
  have hdict₂ := tildeOf_comm_HLb h hsplit hB.le₂
  have hYN₁ := uHi_le_normalizer h H₁ (HLb_le L₁)
  have hYN₂ := uHi_le_normalizer h H₂ (HLb_le L₂)
  refine ⟨H₀, H₁, H₂, (x : G), ?_⟩
  refine
    { le := HLb_le _
      normal := ?_
      eq := ?_
      indexT := ?_
      Q₁ := ?_
      Q₂ := ?_
      le₁ := HLb_mono le_sup_left
      le₂ := HLb_mono le_sup_right
      sup := HLb_sup hB.le₁ hB.le₂
      inf := ?_
      comm := ?_
      dihedral₁ := ?_
      dihedral₂ := ?_
      t_mem := hxT'
      t_not := ?_
      conj := hconjSub.symm
      dir_inf := ?_
      dir_sup := ?_
      cent₁ := ?_
      cent₂ := ?_
      rank₁ := ?_
      rank₂ := ?_ }
  ·
    intro y hy
    refine CosetGeom.mem_normalizer_of_conjSub_eq (conjSub_HLb hy (fun z => ?_))
    have hy' : β ⟨y, hy⟩ ∈ β.range := ⟨⟨y, hy⟩, rfl⟩
    have : conjBy (β ⟨y, hy⟩) (L₁ ⊔ L₂) = L₁ ⊔ L₂ := by
      have e : conjBy (β ⟨y, hy⟩) (L₁ ⊔ L₂) = conjBy (β ⟨y, hy⟩) L₁ ⊔ conjBy (β ⟨y, hy⟩) L₂ :=
        Subgroup.map_sup _ _ _
      rw [e]
      rcases hperm _ hy' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]
      · rw [e1, e2, sup_comm]
    rw [← mem_conjBy_iff, this]
  ·
    apply le_antisymm
    · rw [hred.eq]
      refine sup_le (fun y hy => ?_) (le_sup_right : T ≤ H₀ ⊔ T)
      have hyH : y ∈ H := hred.le hy
      refine le_sup_left (a := H₀) (b := T) ((mem_HLb_iff hyH).2 ?_)
      exact hB.P_le ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    · exact sup_le (HLb_le _) hTH
  ·
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨(x : G), hxT', fun b hb => ?_⟩
    have hbH : b ∈ H := hTH hb
    have hbtH : b * (x : G) ∈ H := H.mul_mem hbH htH
    have hbt : b * (x : G) ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) ↔
        conjBy (β ⟨b, hbH⟩) L₂ = L₁ := by
      rw [Subgroup.mem_inf, hNH _ hbtH L₁ hB.le₁]
      have e : (⟨b * (x : G), hbtH⟩ : ↥H) = ⟨b, hbH⟩ * x := Subtype.ext rfl
      rw [e, map_mul, ← conjBy_conjBy, hτL]
      exact ⟨fun h' => h'.2, fun h' => ⟨T.mul_mem hb hxT', h'⟩⟩
    have hb' : b ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) ↔ conjBy (β ⟨b, hbH⟩) L₁ = L₁ := by
      rw [Subgroup.mem_inf, hNH _ hbH L₁ hB.le₁]
      exact ⟨fun h' => h'.2, fun h' => ⟨hb, h'⟩⟩
    rw [hbt, hb']
    rcases hperm _ (⟨⟨b, hbH⟩, rfl⟩ : β ⟨b, hbH⟩ ∈ β.range) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · right
      exact ⟨e1, fun h' => hB.ne (by rw [← e2]; exact h')⟩
    · left
      exact ⟨e2, fun h' => hB.ne (by rw [← e1]; exact h')⟩
  ·
    intro y hy
    rw [← hker] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact mem_HLb_of_mem (by rw [MonoidHom.mem_ker.1 hz]; exact L₁.one_mem)
  · intro y hy
    rw [← hker] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact mem_HLb_of_mem (by rw [MonoidHom.mem_ker.1 hz]; exact L₂.one_mem)
  ·
    rw [hH₁, hH₂, ← HLb_inf, hB.inf, HLb_bot, hker]
  ·
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haH := HLb_le _ ha
    have hbH := HLb_le _ hb
    have habH : ⁅a, b⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem haH hbH) (H.inv_mem haH)) (H.inv_mem hbH)
    rw [← hker]
    refine ⟨⟨⁅a, b⁆, habH⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have ha' := (mem_HLb_iff haH).1 ha
    have hb' := (mem_HLb_iff hbH).1 hb
    have e : (⟨⁅a, b⁆, habH⟩ : ↥H) = ⟨a, haH⟩ * ⟨b, hbH⟩ * ⟨a, haH⟩⁻¹ * ⟨b, hbH⟩⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hB.comm _ ha' _ hb']
    simp
  · obtain ⟨e₁⟩ := hB.dih₁
    exact secIso_HLb hker hB.le₁ e₁
  · obtain ⟨e₂⟩ := hB.dih₂
    exact secIso_HLb hker hB.le₂ e₂
  ·
    intro hn
    have := (hNH (x : G) htH L₁ hB.le₁).1 hn
    rw [hxe, hτL] at this
    exact hB.ne this
  ·
    apply le_antisymm
    · rintro y ⟨hy1, hy2⟩
      have hyN : y ∈ Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G) := hYN₁ hy1
      have h1' : secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ ∈
          tildeOf (quasithinOmegaOneCenter T) (⁅conjClosure (VZ T M) H, H₁⁆ ⊔ (quasithinOmegaOneCenter T)) := secMk_mem_secImg hy1
      have h2' : secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ ∈
          tildeOf (quasithinOmegaOneCenter T) (⁅conjClosure (VZ T M) H, H₂⁆ ⊔ (quasithinOmegaOneCenter T)) := secMk_mem_secImg hy2
      rw [hdict₁] at h1'
      rw [hdict₂] at h2'
      have h3 : secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ ∈
          (commV L₁).map (valK h) ⊓ (commV L₂).map (valK h) := ⟨h1', h2'⟩
      rw [← Subgroup.map_inf _ _ _ (valK_injective h), hB.cinf, Subgroup.map_bot,
        Subgroup.mem_bot] at h3
      exact secMk_eq_one_iff.1 h3
    · exact le_inf le_sup_right le_sup_right
  ·
    apply le_antisymm
    · exact sup_le (sup_le_sup_right (Subgroup.commutator_mono le_rfl (HLb_le L₁)) (quasithinOmegaOneCenter T))
        (sup_le_sup_right (Subgroup.commutator_mono le_rfl (HLb_le L₂)) (quasithinOmegaOneCenter T))
    · intro y hy
      have hKN : ⁅conjClosure (VZ T M) H, H⁆ ≤ Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G) :=
        (S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _)).trans
          (U_le_normalizer h)
      have hyN : y ∈ Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G) := (sup_le hKN Subgroup.le_normalizer) hy
      have hZle : (quasithinOmegaOneCenter T) ≤ (⁅conjClosure (VZ T M) H, H₁⁆ ⊔ (quasithinOmegaOneCenter T)) ⊔ (⁅conjClosure (VZ T M) H, H₂⁆ ⊔ (quasithinOmegaOneCenter T)) :=
        le_sup_right.trans le_sup_left
      refine (secMk_mem_secImg_iff (A := Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (B := (quasithinOmegaOneCenter T)) hZle
        (x := ⟨y, hyN⟩)).1 ?_
      show _ ∈ tildeOf (quasithinOmegaOneCenter T) _
      rw [tildeOf_sup hYN₁ hYN₂, hdict₁, hdict₂, ← Subgroup.map_sup, hB.csup, Subgroup.map_top]
      have hHrange : HLb β β.range = H := by
        ext g
        exact ⟨fun hg => HLb_le _ hg, fun hg => (mem_HLb_iff hg).2 ⟨⟨g, hg⟩, rfl⟩⟩
      have hdictH := tildeOf_comm_HLb h hsplit (le_refl β.range)
      rw [hHrange] at hdictH
      have hmem : secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ ∈
          tildeOf (quasithinOmegaOneCenter T) (⁅conjClosure (VZ T M) H, H⁆ ⊔ (quasithinOmegaOneCenter T)) := secMk_mem_secImg hy
      rw [hdictH] at hmem
      obtain ⟨k, -, hk⟩ := hmem
      exact ⟨k, hk⟩
  ·
    rw [Subgroup.commutator_le]
    intro y hy g hg
    have hyN : y ∈ Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G) := hYN₁ hy
    have hgH : g ∈ H := HLb_le _ hg
    have hgL : β ⟨g, hgH⟩ ∈ L₂ := (mem_HLb_iff hgH).1 hg
    have hmem : secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ ∈
        tildeOf (quasithinOmegaOneCenter T) (⁅conjClosure (VZ T M) H, H₁⁆ ⊔ (quasithinOmegaOneCenter T)) := secMk_mem_secImg hy
    rw [hdict₁] at hmem
    obtain ⟨k, hk, hkv⟩ := hmem
    have hfix : β ⟨g, hgH⟩ k = k := hB.fix₁ hk _ hgL
    have h1 := valK_comm_gen h ⟨g, hgH⟩ k
    rw [hfix, mul_inv_cancel, map_one] at h1
    rw [hkv] at h1
    have h2 : secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ *
        secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) (Subgroup.inclusion h.H_normalizes_V₁ ⟨g, hgH⟩) =
        secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) (Subgroup.inclusion h.H_normalizes_V₁ ⟨g, hgH⟩) *
        secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ := by
      have h3 := h1.symm
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    exact commutator_mem_of_secMk_commute (x := ⟨y, hyN⟩)
      (y := Subgroup.inclusion h.H_normalizes_V₁ ⟨g, hgH⟩) h2
  ·
    rw [Subgroup.commutator_le]
    intro y hy g hg
    have hyN : y ∈ Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G) := hYN₂ hy
    have hgH : g ∈ H := HLb_le _ hg
    have hgL : β ⟨g, hgH⟩ ∈ L₁ := (mem_HLb_iff hgH).1 hg
    have hmem : secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ ∈
        tildeOf (quasithinOmegaOneCenter T) (⁅conjClosure (VZ T M) H, H₂⁆ ⊔ (quasithinOmegaOneCenter T)) := secMk_mem_secImg hy
    rw [hdict₂] at hmem
    obtain ⟨k, hk, hkv⟩ := hmem
    have hfix : β ⟨g, hgH⟩ k = k := hB.fix₂ hk _ hgL
    have h1 := valK_comm_gen h ⟨g, hgH⟩ k
    rw [hfix, mul_inv_cancel, map_one] at h1
    rw [hkv] at h1
    have h2 : secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ *
        secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) (Subgroup.inclusion h.H_normalizes_V₁ ⟨g, hgH⟩) =
        secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) (Subgroup.inclusion h.H_normalizes_V₁ ⟨g, hgH⟩) *
        secMk (Subgroup.normalizer ((quasithinOmegaOneCenter T) : Set G)) (quasithinOmegaOneCenter T) ⟨y, hyN⟩ := by
      have h3 := h1.symm
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    exact commutator_mem_of_secMk_commute (x := ⟨y, hyN⟩)
      (y := Subgroup.inclusion h.H_normalizes_V₁ ⟨g, hgH⟩) h2
  ·
    have hm : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = rk (commV L₁) :=
      mIdx_uHi_eq h hsplit hB.le₁
    refine ⟨fun h5 => ?_, fun h3 => ?_⟩
    · exact hm.trans ((hB.rank.1 h5))
    · rw [hm]
      exact (hB.rank.2 h3)
  · have hm : mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = rk (commV L₁) :=
      (mIdx_uHi_eq h hsplit hB.le₂).trans hB.rk_eq
    refine ⟨fun h5 => ?_, fun h3 => ?_⟩
    · exact hm.trans ((hB.rank.1 h5))
    · rw [hm]
      exact (hB.rank.2 h3)

end Transport

end CFSG.Quasithin
