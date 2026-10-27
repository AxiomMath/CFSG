module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.B4L3FactA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin

namespace B48

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {W C : Subgroup V}

theorem smul_eq (g : ↥G) (v : V) : g • v = (g : MulAut V) v := rfl

theorem le_stabSub (h : XMod.IsInv ↥G W) : G ≤ stabSub W := by
  intro g hg u
  constructor
  · intro hu
    have h1 := h ⟨g⁻¹, G.inv_mem hg⟩ (g u) hu
    rw [smul_eq] at h1
    simpa using h1
  · intro hu
    exact h ⟨g, hg⟩ u hu

theorem sq_eq_one (hV : ∀ v : V, v ^ 2 = 1) (v : Sec W C) : v ^ 2 = 1 := by
  induction v using QuotientGroup.induction_on with
  | H w =>
    have hw : w ^ 2 = 1 := Subtype.ext (by simpa using hV (w : V))
    rw [← QuotientGroup.mk_pow, hw, QuotientGroup.mk_one]

theorem card_sec [Finite V] (hCW : C ≤ W) (hcard : Nat.card ↥W = 2 ^ 4 * Nat.card ↥C) :
    Nat.card (Sec W C) = 16 := by
  have h := card_sec_mul hCW
  rw [hcard] at h
  have hC : 0 < Nat.card ↥C := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hC (by rw [h]; ring)

section Sec

variable (hGW : G ≤ stabSub W) (hGC : G ≤ stabSub C)

theorem secHom_mk' (g : ↥G) (w : ↥W) :
    B5.secHom G hGW hGC g (QuotientGroup.mk w) =
      QuotientGroup.mk ⟨(g : MulAut V) (w : V), (hGW g.2 w).2 w.2⟩ :=
  B5.secHom_mk G hGW hGC g w

omit hGW hGC in
theorem modComm_le (hW : XMod.IsInv ↥G W) : modComm G W ≤ W := by
  rw [modComm, XMod.commOf, Subgroup.closure_le]
  rintro _ ⟨a, l, hl, rfl⟩
  exact W.mul_mem (hW a l hl) (W.inv_mem hl)

variable (C) in
@[expose] noncomputable def mu {U : Subgroup V} (hUW : U ≤ W) : ↥U →* Sec W C :=
  (QuotientGroup.mk' (C.subgroupOf W)).comp (Subgroup.inclusion hUW)

omit hGW hGC in
theorem mu_apply {U : Subgroup V} (hUW : U ≤ W) (u : ↥U) :
    mu C hUW u = QuotientGroup.mk ⟨u, hUW u.2⟩ := rfl

omit hGW hGC in
theorem mu_eq_one_iff {U : Subgroup V} (hUW : U ≤ W) (u : ↥U) : mu C hUW u = 1 ↔ (u : V) ∈ C := by
  rw [mu_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem range_mu (hW : XMod.IsInv ↥G W) (hCW : C ≤ W) :
    (mu C (sup_le (modComm_le hW) hCW)).range = commV (B5.secHom G hGW hGC).range := by
  apply le_antisymm
  · set S : Subgroup V := ((commV (B5.secHom G hGW hGC).range).comap
      (QuotientGroup.mk' (C.subgroupOf W))).map W.subtype with hS
    have hle : modComm G W ⊔ C ≤ S := by
      refine sup_le ?_ fun c hc => ⟨⟨c, hCW hc⟩, ?_, rfl⟩
      · rw [modComm, XMod.commOf, Subgroup.closure_le]
        rintro _ ⟨g, l, hl, rfl⟩
        refine ⟨⟨(g : MulAut V) l * l⁻¹, W.mul_mem (hW g l hl) (W.inv_mem hl)⟩, ?_, rfl⟩
        refine Subgroup.subset_closure ⟨_, ⟨g, rfl⟩, QuotientGroup.mk ⟨l, hl⟩, ?_⟩
        rw [secHom_mk']
        rfl
      · have h1 : QuotientGroup.mk' (C.subgroupOf W) ⟨c, hCW hc⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          exact hc
        change QuotientGroup.mk' (C.subgroupOf W) ⟨c, hCW hc⟩ ∈
          commV (B5.secHom G hGW hGC).range
        rw [h1]
        exact Subgroup.one_mem _
    rintro _ ⟨u, rfl⟩
    obtain ⟨w, hw, hwu⟩ := hle u.2
    have : (⟨u, (sup_le (modComm_le hW) hCW) u.2⟩ : ↥W) = w := Subtype.ext hwu.symm
    rw [mu_apply, this]
    exact hw
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨φ, ⟨g, rfl⟩, v, rfl⟩
    induction v using QuotientGroup.induction_on with
    | H w =>
      refine ⟨⟨(g : MulAut V) w * (w : V)⁻¹, Subgroup.mem_sup_left
        (Subgroup.subset_closure ⟨g, w, w.2, rfl⟩)⟩, ?_⟩
      rw [mu_apply, secHom_mk']
      rfl

omit hGW hGC in
theorem mem_pre_iff (Z : Subgroup (Sec W C)) (w : ↥W) :
    (w : V) ∈ (Z.comap (QuotientGroup.mk' (C.subgroupOf W))).map W.subtype ↔
      (QuotientGroup.mk w : Sec W C) ∈ Z := by
  constructor
  · intro h
    obtain ⟨w', hw', hw'w⟩ := Subgroup.mem_map.1 h
    have : w' = w := Subtype.ext hw'w
    rw [← this]
    exact hw'
  · intro h
    exact Subgroup.mem_map.2 ⟨w, h, rfl⟩

omit hGW hGC in
theorem le_pre (hCW : C ≤ W) (Z : Subgroup (Sec W C)) :
    C ≤ (Z.comap (QuotientGroup.mk' (C.subgroupOf W))).map W.subtype := by
  intro c hc
  refine (mem_pre_iff Z ⟨c, hCW hc⟩).2 ?_
  have h1 : (QuotientGroup.mk (⟨c, hCW hc⟩ : ↥W) : Sec W C) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hc
  rw [h1]
  exact Z.one_mem

theorem isInv_pre (Z : Subgroup (Sec W C))
    (hZ : ∀ φ ∈ (B5.secHom G hGW hGC).range, ∀ z ∈ Z, φ z ∈ Z) :
    XMod.IsInv ↥G ((Z.comap (QuotientGroup.mk' (C.subgroupOf W))).map W.subtype) := by
  intro g v hv
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hv
  refine (mem_pre_iff Z ⟨(g : MulAut V) w, (hGW g.2 w).2 w.2⟩).2 ?_
  have h1 := hZ _ ⟨g, rfl⟩ _ hw
  rw [QuotientGroup.mk'_apply, secHom_mk'] at h1
  exact h1

theorem isIndecomp (hCW : C ≤ W)
    (hind : ¬ ∃ A B : Subgroup V, C < A ∧ C < B ∧ XMod.IsInv ↥G A ∧ XMod.IsInv ↥G B ∧
      A ⊔ B = W ∧ A ⊓ B = C) :
    IsIndecompModule (B5.secHom G hGW hGC).range := by
  intro X Y hX hY hXY hXY'
  set A : Subgroup V := (X.comap (QuotientGroup.mk' (C.subgroupOf W))).map W.subtype with hA
  set B : Subgroup V := (Y.comap (QuotientGroup.mk' (C.subgroupOf W))).map W.subtype with hB
  have hAW : A ≤ W := Subgroup.map_subtype_le _
  have hBW : B ≤ W := Subgroup.map_subtype_le _
  have hsup : A ⊔ B = W := by
    refine le_antisymm (sup_le hAW hBW) fun w hw => ?_
    have h1 : (QuotientGroup.mk (⟨w, hw⟩ : ↥W) : Sec W C) ∈ X ⊔ Y := by
      rw [hXY']
      trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.1 h1
    obtain ⟨w₁, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨w₂, rfl⟩ := QuotientGroup.mk_surjective y
    have h2 : (QuotientGroup.mk (w₁ * w₂) : Sec W C) = QuotientGroup.mk ⟨w, hw⟩ := by
      rw [QuotientGroup.mk_mul]
      exact hxy
    have hc := QuotientGroup.eq.mp h2
    rw [Subgroup.mem_subgroupOf] at hc
    have hw₁ : (w₁ : V) ∈ A := (mem_pre_iff X w₁).2 hx
    have hw₂ : (w₂ : V) ∈ B := (mem_pre_iff Y w₂).2 hy
    have e : w = (w₁ : V) * (w₂ : V) * (((w₁ * w₂)⁻¹ * ⟨w, hw⟩ : ↥W) : V) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hw₁)
      (Subgroup.mem_sup_right hw₂)) (Subgroup.mem_sup_left (le_pre hCW X hc))
  have hinf : A ⊓ B = C := by
    refine le_antisymm (fun w hw => ?_) (le_inf (le_pre hCW X) (le_pre hCW Y))
    have hwW : w ∈ W := hAW hw.1
    have h1 : (QuotientGroup.mk (⟨w, hwW⟩ : ↥W) : Sec W C) ∈ X ⊓ Y :=
      ⟨(mem_pre_iff X ⟨w, hwW⟩).1 hw.1, (mem_pre_iff Y ⟨w, hwW⟩).1 hw.2⟩
    rw [hXY, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hbot : ∀ Z : Subgroup (Sec W C),
      (Z.comap (QuotientGroup.mk' (C.subgroupOf W))).map W.subtype = C → Z = ⊥ := by
    intro Z hZ
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := (mem_pre_iff Z w).2 hz
    rw [hZ] at h1
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact h1
  by_contra hne
  rw [not_or] at hne
  apply hind
  refine ⟨A, B, lt_of_le_of_ne (le_pre hCW X) fun h => hne.1 (hbot X h.symm),
    lt_of_le_of_ne (le_pre hCW Y) fun h => hne.2 (hbot Y h.symm),
    isInv_pre hGW hGC X hX, isInv_pre hGW hGC Y hY, hsup, hinf⟩

end Sec

end B48

end CFSG.Quasithin.Vol2.Ch10.SecB
