module

public import CFSG.Quasithin.Background.F918C0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Dictionary

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] {V₁ IH H : Subgroup G}

theorem subM_le_iff (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {J J' : Subgroup G}
    (hV₁J : V₁ ≤ J) (hV₁J' : V₁ ≤ J') (hJI : J ≤ IH) :
    subM V₁ IH J ≤ subM V₁ IH J' ↔ J ≤ J' := by
  constructor
  · intro h a ha
    have hmem : modMk hIHN a (hJI ha) ∈ subM V₁ IH J :=
      (modMk_mem_subM_iff hIHN hV₁J (hJI ha)).mpr ha
    exact (modMk_mem_subM_iff hIHN hV₁J' (hJI ha)).mp (h hmem)
  · intro h w hw
    exact mem_subM_iff.2 (secImg_mono h (mem_subM_iff.1 hw))

theorem subM_inj (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {J J' : Subgroup G}
    (hV₁J : V₁ ≤ J) (hV₁J' : V₁ ≤ J') (hJI : J ≤ IH) (hJ'I : J' ≤ IH)
    (h : subM V₁ IH J = subM V₁ IH J') : J = J' :=
  le_antisymm ((subM_le_iff hIHN hV₁J hV₁J' hJI).1 h.le) ((subM_le_iff hIHN hV₁J' hV₁J hJ'I).1 h.ge)

theorem exists_subM_eq (hV₁IH : V₁ ≤ IH) (S : Subgroup ↥(tildeOf V₁ IH)) :
    ∃ J : Subgroup G, V₁ ≤ J ∧ J ≤ IH ∧ subM V₁ IH J = S := by
  set Y : Subgroup (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) :=
    S.map (tildeOf V₁ IH).subtype with hY
  have hYU : Y ≤ tildeOf V₁ IH := Subgroup.map_subtype_le _
  refine ⟨secPre (Subgroup.normalizer (V₁ : Set G)) V₁ Y,
    le_secPre Subgroup.le_normalizer Y, secPre_le hV₁IH hYU, ?_⟩
  unfold subM tildeOf
  rw [secImg_secPre]
  exact map_subtype_subgroupOf' S

variable [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]

theorem isInv_subM_of_normalizer (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    {X J : Subgroup G} (hXH : X ≤ H) (hV₁J : V₁ ≤ J) (hJI : J ≤ IH)
    (hXJ : X ≤ Subgroup.normalizer (J : Set G)) :
    XMod.IsInv ↥(autOn (tildeOf V₁ X) (tildeOf V₁ IH)) (subM V₁ IH J) := by
  intro a w hw
  have ha : (a : MulAut ↥(tildeOf V₁ IH)) ∈ (X.subgroupOf H).map (actH hV₁ hIH) := by
    rw [← autOn_tilde_eq_map_actH hV₁ hIH hXH]
    exact a.2
  obtain ⟨x, hx, hxa⟩ := ha
  have hst := (actH_mem_stabSub_subM_iff hV₁ hIHN hIH hV₁J hJI x).mpr
    (hXJ (Subgroup.mem_subgroupOf.mp hx))
  show (a : MulAut ↥(tildeOf V₁ IH)) w ∈ _
  rw [← hxa]
  exact (hst w).2 hw

theorem eq_or_eq_of_isIrrSec (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    {X C J J' : Subgroup G} (hXH : X ≤ H) (hV₁C : V₁ ≤ C) (hCJ' : C ≤ J') (hJ'J : J' ≤ J)
    (hJI : J ≤ IH) (hXJ' : X ≤ Subgroup.normalizer (J' : Set G))
    (hirr : XMod.IsIrrSec ↥(autOn (tildeOf V₁ X) (tildeOf V₁ IH)) (subM V₁ IH C) (subM V₁ IH J)) :
    J' = C ∨ J' = J := by
  have hV₁J' : V₁ ≤ J' := hV₁C.trans hCJ'
  have hV₁J : V₁ ≤ J := hV₁J'.trans hJ'J
  have hJ'I : J' ≤ IH := hJ'J.trans hJI
  have hCI : C ≤ IH := hCJ'.trans hJ'I
  have hinv := isInv_subM_of_normalizer hV₁ hIHN hIH hXH hV₁J' hJ'I hXJ'
  rcases hirr.2 (subM V₁ IH J') hinv ((subM_le_iff hIHN hV₁C hV₁J' hCI).2 hCJ')
      ((subM_le_iff hIHN hV₁J' hV₁J hJ'I).2 hJ'J) with h | h
  · exact Or.inl (subM_inj hIHN hV₁J' hV₁C hJ'I hCI h)
  · exact Or.inr (subM_inj hIHN hV₁J' hV₁J hJ'I hJI h)

omit [Fact (IsElemAbelian 2 (tildeOf V₁ IH))] in
theorem card_subM (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {J : Subgroup G}
    (hV₁J : V₁ ≤ J) (hJI : J ≤ IH) : Nat.card ↥(subM V₁ IH J) = V₁.relIndex J := by
  have h1 : tildeOf V₁ J ≤ tildeOf V₁ IH := secImg_mono hJI
  have h2 : Nat.card ↥(subM V₁ IH J) = Nat.card ↥(tildeOf V₁ J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv
  have h3 : (tildeOf V₁ V₁).relIndex (tildeOf V₁ J) = V₁.relIndex J :=
    relIndex_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) le_rfl hV₁J (hJI.trans hIHN)
  rw [tildeOf_eq_bot_of_le le_rfl, Subgroup.relIndex_bot_left] at h3
  rw [h2, h3]

omit [Fact (IsElemAbelian 2 (tildeOf V₁ IH))] in
theorem le_centralizerMod (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) {X J : Subgroup G}
    (hXH : X ≤ H) (hV₁J : V₁ ≤ J) : V₁ ≤ centralizerMod V₁ J X := fun v hv =>
  ⟨hV₁J hv, Subgroup.le_normalizer hv, fun u hu => by
    have h1 : u * v⁻¹ * u⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hV₁ (hXH hu)) v⁻¹).mp (V₁.inv_mem hv)
    have e : v * u * v⁻¹ * u⁻¹ = v * (u * v⁻¹ * u⁻¹) := by group
    rw [e]
    exact V₁.mul_mem hv h1⟩

omit [Fact (IsElemAbelian 2 (tildeOf V₁ IH))] in
theorem comm_mem_iff_conj {a x : G} (ha : a ∈ Subgroup.normalizer (V₁ : Set G)) :
    a * x * a⁻¹ * x⁻¹ ∈ V₁ ↔ (x * a * x⁻¹)⁻¹ * a ∈ V₁ := by
  have e : (x * a * x⁻¹)⁻¹ * a = (a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a)⁻¹ := by group
  rw [e, V₁.inv_mem_iff]
  constructor
  · intro h
    have h1 := V₁.inv_mem h
    have : a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a ∈ V₁ :=
      (Subgroup.mem_normalizer_iff''.mp ha _).mp (V₁.inv_mem h)
    exact this
  · intro h
    have h2 : (a * x * a⁻¹ * x⁻¹)⁻¹ ∈ V₁ := by
      have := (Subgroup.mem_normalizer_iff''.mp ha ((a * x * a⁻¹ * x⁻¹)⁻¹)).mpr h
      exact this
    simpa using V₁.inv_mem h2

theorem subM_centralizerMod (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    {X J : Subgroup G} (hXH : X ≤ H) (hV₁J : V₁ ≤ J) (hJI : J ≤ IH) :
    subM V₁ IH (centralizerMod V₁ J X) =
      XMod.fixed ↥(autOn (tildeOf V₁ X) (tildeOf V₁ IH)) (subM V₁ IH J) := by
  have hV₁C := le_centralizerMod hV₁ hXH hV₁J
  have hCI : centralizerMod V₁ J X ≤ IH := (centralizerMod_le_left V₁ J X).trans hJI
  ext w
  constructor
  · intro hw
    obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
    have hw' : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
    subst hw'
    have haC : (a : G) ∈ centralizerMod V₁ J X := (modMk_mem_subM_iff hIHN hV₁C haIH).mp hw
    refine ⟨(modMk_mem_subM_iff hIHN hV₁J haIH).mpr haC.1, fun b => ?_⟩
    obtain ⟨x, hx, hxb⟩ : (b : MulAut ↥(tildeOf V₁ IH)) ∈ (X.subgroupOf H).map (actH hV₁ hIH) := by
      rw [← autOn_tilde_eq_map_actH hV₁ hIH hXH]
      exact b.2
    show (b : MulAut ↥(tildeOf V₁ IH)) (modMk hIHN (a : G) haIH) = modMk hIHN (a : G) haIH
    rw [← hxb, actH_modMk hV₁ hIHN hIH x haIH]
    apply Subtype.ext
    show secMk _ _ ⟨(x : G) * (a : G) * (x : G)⁻¹, _⟩ = secMk _ _ ⟨(a : G), _⟩
    rw [secMk_eq_secMk_iff]
    exact (comm_mem_iff_conj (hIHN haIH)).mp (haC.2.2 x (Subgroup.mem_subgroupOf.mp hx))
  · rintro ⟨hwJ, hfix⟩
    obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
    have hw' : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
    subst hw'
    have haJ : (a : G) ∈ J := (modMk_mem_subM_iff hIHN hV₁J haIH).mp hwJ
    refine (modMk_mem_subM_iff hIHN hV₁C haIH).mpr ⟨haJ, hIHN haIH, fun u hu => ?_⟩
    have huH : u ∈ H := hXH hu
    have hmem : actH hV₁ hIH ⟨u, huH⟩ ∈ autOn (tildeOf V₁ X) (tildeOf V₁ IH) := by
      rw [autOn_tilde_eq_map_actH hV₁ hIH hXH]
      exact ⟨⟨u, huH⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    have h1 := hfix ⟨actH hV₁ hIH ⟨u, huH⟩, hmem⟩
    have h2 : actH hV₁ hIH ⟨u, huH⟩ (modMk hIHN (a : G) haIH) = modMk hIHN (a : G) haIH := h1
    rw [actH_modMk hV₁ hIHN hIH ⟨u, huH⟩ haIH] at h2
    have h3 := congrArg Subtype.val h2
    have h4 := secMk_eq_secMk_iff.mp h3
    exact (comm_mem_iff_conj (hIHN haIH)).mpr h4

end Dictionary

section Irr

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem tildeOf_commutator_eq (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (hcomm : XMod.commOf ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) =
      subM V₁ (conjClosure I H) I) :
    tildeOf V₁ ⁅I, conjClosure K T⁆ = tildeOf V₁ I := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  apply le_antisymm
  · refine secImg_mono (Subgroup.commutator_le.mpr fun i hi k hk => ?_)
    have h1 : k * i⁻¹ * k⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp (hKI hk) i⁻¹).mp (I.inv_mem hi)
    have e : i * k * i⁻¹ * k⁻¹ = i * (k * i⁻¹ * k⁻¹) := by group
    rw [commutatorElement_def, e]
    exact I.mul_mem hi h1
  · intro y hy
    have hyIH : y ∈ tildeOf V₁ (conjClosure I H) := secImg_mono (le_conjClosure I H) hy
    have hw : (⟨y, hyIH⟩ : ↥(tildeOf V₁ (conjClosure I H))) ∈ subM V₁ (conjClosure I H) I := hy
    rw [← hcomm] at hw
    have key : ∀ w ∈ XMod.commOf ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I),
        (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ ⁅I, conjClosure K T⁆ := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem c hc =>
        obtain ⟨a, l, hl, rfl⟩ := hc
        obtain ⟨x, hx, hxa⟩ : (a : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
            ((conjClosure K T).subgroupOf H).map
              (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
          rw [← autIH_eq_map h h.K₀_le_H]
          exact a.2
        obtain ⟨b, hbIH, hbl⟩ := exists_mk_of_mem_tilde l
        have hl' : l = modMk hIHN (b : G) hbIH := Subtype.ext hbl.symm
        have hbI : (b : G) ∈ I := (modMk_mem_subM_iff hIHN hV₁I hbIH).mp (hl' ▸ hl)
        have hxK : (x : G) ∈ conjClosure K T := Subgroup.mem_subgroupOf.mp hx
        have hcomm' : (x : G) * (b : G) * (x : G)⁻¹ * (b : G)⁻¹ ∈ ⁅I, conjClosure K T⁆ := by
          rw [← Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator hxK hbI
        have hxbI : (x : G) * (b : G) * (x : G)⁻¹ ∈ conjClosure I H :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure I H x.2) (b : G)).mp hbIH
        show ((((a : MulAut ↥(tildeOf V₁ (conjClosure I H))) l * l⁻¹ :
          ↥(tildeOf V₁ (conjClosure I H))) : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) ∈ _
        rw [← hxa, hl']
        have hmemIH : (x : G) * (b : G) * (x : G)⁻¹ * (b : G)⁻¹ ∈ conjClosure I H :=
          (conjClosure I H).mul_mem hxbI ((conjClosure I H).inv_mem hbIH)
        have hmk := secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
          (X := ⁅I, conjClosure K T⁆)
          (x := ⟨(x : G) * (b : G) * (x : G)⁻¹ * (b : G)⁻¹, hIHN hmemIH⟩) hcomm'
        have e : ((((actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x)
            (modMk hIHN (b : G) hbIH) * (modMk hIHN (b : G) hbIH)⁻¹ :
              ↥(tildeOf V₁ (conjClosure I H))) :
              ↥(tildeOf V₁ (conjClosure I H))) :
            SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
            secMk (Subgroup.normalizer (V₁ : Set G)) V₁
              ⟨(x : G) * (b : G) * (x : G)⁻¹ * (b : G)⁻¹, hIHN hmemIH⟩ := by
          rw [actH_modMk h.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) x hbIH]
          show secMk _ _ ⟨(x : G) * (b : G) * (x : G)⁻¹, _⟩ * (secMk _ _ ⟨(b : G), _⟩)⁻¹ = _
          rw [← map_inv, ← map_mul]
          rfl
        rw [e]
        exact hmk
      | one => exact one_mem _
      | mul c d hc hd ihc ihd => exact mul_mem ihc ihd
      | inv c hc ih => exact inv_mem ih
    exact key _ hw

theorem isIrrPlusTilde_of_module (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTildeT h hIU) :
    IsIrrPlusTilde V₁ (conjClosure K T) I := by
  have hF := factElem h hIU
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hC := subM_centralizerMod h.H_le_normalizer_V₁ hIHN hIH h.K₀_le_H hV₁I (le_conjClosure I H)
  have hirrSec : XMod.IsIrrSec ↥(autIH V₁ I H (conjClosure K T))
      (subM V₁ (conjClosure I H) (centralizerMod V₁ I (conjClosure K T)))
      (subM V₁ (conjClosure I H) I) := by
    rw [hC]
    exact hirr'.1.2.2.2
  refine ⟨hKI, tildeOf_commutator_eq h hV₁I hIU hKI hirr'.1.2.2.1, ?_, ?_⟩
  · refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun heq => ?_
    have hlt := hirrSec.1
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · intro J hV₁J hJI hKJ hCJ
    exact eq_or_eq_of_isIrrSec h.H_le_normalizer_V₁ hIHN hIH h.K₀_le_H
      (le_centralizerMod h.H_le_normalizer_V₁ h.K₀_le_H hV₁I) hCJ hJI (le_conjClosure I H) hKJ
      hirrSec

end Irr


end CFSG.Quasithin
