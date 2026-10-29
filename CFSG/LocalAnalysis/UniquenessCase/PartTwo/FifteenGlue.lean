module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNineLP
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Glue_wClos_zero_le {V X Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : ∀ g : G, conjSubgroup V g ≤ X → conjSubgroup V g ≤ Y) : E3.wClos V 0 X ≤ Y := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAX, g, hAg, hm⟩ := hA
  have hVg : IsPGroup 2 (conjSubgroup V g) := (E3.isElemAbelian_conjSubgroup hV g).isPGroup
  have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg hAg).1 hm
  rw [hAeq]
  exact h g (hAeq ▸ hAX)

theorem s15_Glue_mem_preTil_fixV_iff (V₀ V E : Subgroup G) (hV : IsElemAbelian 2 V)
    (hE : E ≤ stabTil V₀ V) {w : G} (hw : w ∈ V) :
    w ∈ preTil V₀ V hV (fixV (barSub V₀ V hV E)) ↔
      ∀ e ∈ E, e * w * e⁻¹ * w⁻¹ ∈ V₀ := by
  rw [mem_preTil_iff_of_mem V₀ V hV _ hw]
  constructor
  · intro hfix e he
    have := (mem_fixV.1 hfix) (actTil V₀ V hV ⟨e, hE he⟩)
      (actTil_mem_barSub V₀ V hV he (hE he))
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at this
    exact this
  · intro hall
    rw [mem_fixV]
    intro φ hφ
    obtain ⟨g, hgE, rfl⟩ := (mem_barSub V₀ V hV E φ).1 hφ
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
    exact hall g hgE

theorem s15_Glue_orbit_mem_of_fix {V V₁ E : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₁ : V₁ ≤ V) {v : G} (hv : v ∈ V) (hfix : ∀ e ∈ E, e * v * e⁻¹ * v⁻¹ ∈ V₁) :
    ∀ e ∈ E, v⁻¹ * (e⁻¹ * v * e) ∈ V₁ := by
  intro e he
  have hc := hfix e⁻¹ (E.inv_mem he)
  rw [inv_inv] at hc
  have hcV : e⁻¹ * v * e * v⁻¹ ∈ V := hV₁ hc
  have hcomm := B2F.isElemAbelian_comm hV hcV hv
  have key : v⁻¹ * (e⁻¹ * v * e) = e⁻¹ * v * e * v⁻¹ := by
    calc v⁻¹ * (e⁻¹ * v * e)
        = v⁻¹ * ((e⁻¹ * v * e * v⁻¹) * v) := by group
      _ = v⁻¹ * (v * (e⁻¹ * v * e * v⁻¹)) := by rw [hcomm]
      _ = e⁻¹ * v * e * v⁻¹ := by group
  rw [key]
  exact hc

theorem s15_Glue_inf_V_eq_bot (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} (hVg : ¬ V ≤ conjSubgroup D.M g) :
    conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ⊓ V = ⊥ := by
  have h151 := h.hyp151
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h151.hyp125 hV)
  have hAV : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤ conjSubgroup V g :=
    E3.conjSubgroup_mono_left g hWV
  have hVabel : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hV hx hy
  have hA2 : IsPGroup 2 (conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g) :=
    (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hAV
  have hKMg : rankThreeIsMaxTwoLocal (conjSubgroup D.M g) :=
    UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup D.M from D.maxLocal) g
  have hAUm : ∀ w ∈ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g, w ≠ 1 →
      UniqueMax (conjSubgroup D.M g) (conjSubgroup D.M g ⊓ centralizer ({w} : Set G)) :=
    fun w hw hw1 => uniqueMax_conjSubgroup_of_mem (g := g) h.unique₁ hw hw1
  exact inf_eq_bot_of_not_le_of_uniqueMax hKMg hA2 hAUm hVabel hVg

theorem s15_Glue_exists_hyperplane {B C : Subgroup G} (hB : IsPGroup 2 B) (hCB : C < B) :
    ∃ E : Subgroup G, C ≤ E ∧ E ≤ B ∧ E3.mQuot B E = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥B := hB.isNilpotent
  have hC' : C.subgroupOf B ≠ ⊤ := fun htop =>
    hCB.not_ge (Subgroup.subgroupOf_eq_top.1 htop)
  obtain ⟨E', hE'c, hCE'⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (C.subgroupOf B)).resolve_left hC'
  have hidx : E'.index = 2 := hB.isCoatom_iff_index_eq_prime.1 hE'c
  refine ⟨E'.map B.subtype, ?_, Subgroup.map_subtype_le E', ?_⟩
  · intro c hc
    exact ⟨⟨c, hCB.le hc⟩, hCE' (by simpa [Subgroup.mem_subgroupOf] using hc), rfl⟩
  · have hsub : (E'.map B.subtype).subgroupOf B = E' :=
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective E'
    unfold E3.mQuot Subgroup.relIndex
    rw [hsub, hidx]
    exact padicValNat_self

theorem s15_Glue_relIndex_inf_normalizer_le (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {E : Subgroup G} (hE : E ≤ D.M) :
    (E ⊓ normalizer (wSub V₀ V hV L : Set G)).relIndex E ≤ s15 D.M V₀ V hV L := by
  classical
  set W := wSub V₀ V hV L with hW
  set N := normalizer (W : Set G) with hN
  rw [← ncard_wConj D h hV]
  have key : ∀ e e' : E, e⁻¹ * e' ∈ (E ⊓ N).subgroupOf E ↔
      conjSubgroup W ((e : G)⁻¹) = conjSubgroup W ((e' : G)⁻¹) := by
    intro e e'
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨-, hn⟩
      ext x
      simp only [mem_conjSubgroup_iff, inv_inv]
      have h1 := (Subgroup.mem_normalizer_iff.1 (N.inv_mem hn)) ((e : G)⁻¹ * x * (e : G))
      simp only [inv_inv] at h1
      have h2 : ((e : G)⁻¹ * (e' : G))⁻¹ * ((e : G)⁻¹ * x * (e : G)) * ((e : G)⁻¹ * (e' : G)) =
          (e' : G)⁻¹ * x * (e' : G) := by group
      rw [h2] at h1
      exact h1
    · intro hEq
      refine ⟨E.mul_mem (E.inv_mem e.2) e'.2, ?_⟩
      rw [hN, Subgroup.mem_normalizer_iff]
      intro y
      have h1 : ∀ x : G, (e : G)⁻¹ * x * (e : G) ∈ W ↔ (e' : G)⁻¹ * x * (e' : G) ∈ W := by
        intro x
        have := SetLike.ext_iff.1 hEq x
        simpa [mem_conjSubgroup_iff] using this
      have h2 := h1 ((e' : G) * y * (e' : G)⁻¹)
      have ha : (e' : G)⁻¹ * ((e' : G) * y * (e' : G)⁻¹) * (e' : G) = y := by group
      have hb : (e : G)⁻¹ * ((e' : G) * y * (e' : G)⁻¹) * (e : G) =
          ((e : G)⁻¹ * (e' : G)) * y * ((e : G)⁻¹ * (e' : G))⁻¹ := by group
      rw [ha, hb] at h2
      exact h2.symm
  let f : E ⧸ (E ⊓ N).subgroupOf E → wConj D.M V₀ V hV L :=
    Quotient.lift (fun e : E => (⟨conjSubgroup W ((e : G)⁻¹), (e : G)⁻¹, D.M.inv_mem (hE e.2),
      rfl⟩ : wConj D.M V₀ V hV L))
      (fun e e' hee' => Subtype.ext ((key e e').1 (QuotientGroup.leftRel_apply.1 hee')))
  have hinj : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | _ e => ?_
    induction b using QuotientGroup.induction_on with | _ e' => ?_
    exact QuotientGroup.eq.2 ((key e e').2 (congrArg Subtype.val hab))
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_coe_set_eq] at hcard
  calc (E ⊓ N).relIndex E = Nat.card (E ⧸ (E ⊓ N).subgroupOf E) := Subgroup.index_eq_card _
    _ ≤ _ := hcard

theorem s15_Glue_mQuot_inf_normalizer_le_one (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {E : Subgroup G} (hE : E ≤ D.M)
    (hE2 : IsPGroup 2 E) (hs : s15 D.M V₀ V hV L = 2) :
    E3.mQuot E (E ⊓ normalizer (wSub V₀ V hV L : Set G)) ≤ 1 := by
  have h1 := s15_Glue_relIndex_inf_normalizer_le D h hV hE
  rw [hs, E3.relIndex_eq_two_pow hE2] at h1
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by rw [pow_one]; exact h1)

theorem fifteen_seven_G (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {B E : Subgroup G} (hBM : B ≤ D.M)
    (hB2 : IsPGroup 2 B) (hEB : E ≤ B)
    (hEN : B ⊓ normalizer (wSub V₀ V hV L : Set G) ≤ E) (hne : E ≠ B) :
    ∃ v ∈ V, (∀ e ∈ E, e * v * e⁻¹ * v⁻¹ ∈ v1Sub D.M V₀ V hV L) ∧
      (∃ b ∈ B, b * v * b⁻¹ * v⁻¹ ∉ v1Sub D.M V₀ V hV L) ∧
      (E ≤ normalizer (wSub V₀ V hV L : Set G) → v ∈ wSub V₀ V hV L) := by
  have h125 : Hyp125 D V₀ V := h.hyp125
  set V₁ := v1Sub D.M V₀ V hV L with hV₁
  set W := wSub V₀ V hV L with hW
  set Ws := wStar D.M V₀ V hV L with hWs
  have hMs : D.M ≤ stabTil V₁ V :=
    le_stabTil h125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h125 hV)
  have hBs : B ≤ stabTil V₁ V := hBM.trans hMs
  have hEs : E ≤ stabTil V₁ V := hEB.trans hBs
  have hAM : barSub V₁ V hV B ≤ Mbar D.M V₁ V hV := barSub_mono V₁ V hV hBM
  have hpre : ∀ g : ↥(stabTil V₁ V), (g : G) ∈ B → actTil V₁ V hV g ∈ stabSub Ws →
      (g : G) ∈ normalizer (W : Set G) := by
    intro g hgB hgs
    have h1 : (g : G) ∈ preBarSub D.M V₁ V hV (stabSub Ws) :=
      (mem_preBarSub D.M V₁ V hV _).2 ⟨hBM hgB, g.2, hgs⟩
    rw [preBarSub_stabSub_wStar D h hV, ← inf_normalizer_wSub_eq_nBar D h hV] at h1
    exact (Subgroup.mem_inf.1 h1).2
  have hBE : barSub V₁ V hV B ⊓ stabSub Ws ≤ barSub V₁ V hV E := by
    intro φ hφ
    obtain ⟨hφA, hφs⟩ := Subgroup.mem_inf.1 hφ
    obtain ⟨g, hgB, rfl⟩ := (mem_barSub V₁ V hV B φ).1 hφA
    exact (mem_barSub V₁ V hV E _).2 ⟨g, hEN ⟨hgB, hpre g hgB hφs⟩, rfl⟩
  have hEA : barSub V₁ V hV E < barSub V₁ V hV B := by
    refine lt_of_le_of_ne (barSub_mono V₁ V hV hEB) fun heq => hne ?_
    refine le_antisymm hEB fun b hb => ?_
    have hbs : b ∈ stabTil V₁ V := hBs hb
    have hmem : actTil V₁ V hV ⟨b, hbs⟩ ∈ barSub V₁ V hV E := by
      rw [heq]
      exact actTil_mem_barSub V₁ V hV hb hbs
    obtain ⟨e, heE, hee⟩ := (mem_barSub V₁ V hV E _).1 hmem
    have h1 : actTil V₁ V hV (⟨b, hbs⟩ * e⁻¹) = 1 := by
      rw [map_mul, map_inv, hee, mul_inv_cancel]
    have h2 : b * (e : G)⁻¹ ∈ normalizer (W : Set G) :=
      hpre (⟨b, hbs⟩ * e⁻¹) (B.mul_mem hb (B.inv_mem (hEB heE))) (by rw [h1]; exact one_mem _)
    have h3 : b * (e : G)⁻¹ ∈ E := hEN ⟨B.mul_mem hb (B.inv_mem (hEB heE)), h2⟩
    have h4 : b = b * (e : G)⁻¹ * (e : G) := by group
    rw [h4]
    exact E.mul_mem h3 heE
  have hW0 : Ws ≠ ⊥ := by
    intro hbot
    have h2 := two_le_gamma15 D h hV hL
    have h3 : gamma15 D.M V₀ V hV L = rk ↥Ws := rfl
    rw [h3, hbot] at h2
    simp [rk] at h2
  have hP : IsPGroup 2 ↥(barSub V₁ V hV B ⊓ stabSub Ws) :=
    (s15_LP_isPGroup_barSub hV hB2).to_le inf_le_left
  have hinv : ∀ x ∈ barSub V₁ V hV B ⊓ stabSub Ws, ∀ u ∈ Ws, x u ∈ Ws :=
    fun x hx u hu => ((Subgroup.mem_inf.1 hx).2 u).2 hu
  obtain ⟨w, hw, hw1, hwB⟩ := s15_Lin_exists_ne_one_mem_fixV hP
    (s15_Infra_vtil_sq_eq_one _ V hV) hW0 hinv
  have key := fifteen_seven_prime D h hV hAM rfl hBE hEA hw hw1 hwB
  set v' := ∏ᶠ u ∈ MulAction.orbit (barSub V₁ V hV E) w, u with hv'
  have hlift : ∀ x : IntMod V hV, mkTil V₁ V hV x = v' →
      (∀ e ∈ E, e * x.val * e⁻¹ * (x.val)⁻¹ ∈ V₁) ∧
        (∃ b ∈ B, b * x.val * b⁻¹ * (x.val)⁻¹ ∉ V₁) := by
    intro x hxv
    refine ⟨fun e he => ?_, ?_⟩
    · have := (mem_fixV.1 key.1) (actTil V₁ V hV ⟨e, hEs he⟩)
        (actTil_mem_barSub V₁ V hV he (hEs he))
      rw [← hxv, actTil_mk, mkTil_eq_iff, actStab_apply_val] at this
      exact this
    · by_contra hcon
      push Not at hcon
      apply key.2
      rw [mem_fixV]
      intro φ hφ
      obtain ⟨g, hgB, rfl⟩ := (mem_barSub V₁ V hV B φ).1 hφ
      rw [← hxv, actTil_mk, mkTil_eq_iff, actStab_apply_val]
      exact hcon g hgB
  by_cases hEW : E ≤ normalizer (W : Set G)
  ·
    have hstab : ∀ φ ∈ barSub V₁ V hV E, φ ∈ stabSub Ws := by
      intro φ hφ
      obtain ⟨g, hgE, rfl⟩ := (mem_barSub V₁ V hV E φ).1 hφ
      have h1 : (g : G) ∈ preBarSub D.M V₁ V hV (stabSub Ws) := by
        rw [preBarSub_stabSub_wStar D h hV, ← inf_normalizer_wSub_eq_nBar D h hV]
        exact Subgroup.mem_inf.2 ⟨hBM (hEB hgE), hEW hgE⟩
      obtain ⟨-, hg', hgs⟩ := (mem_preBarSub D.M V₁ V hV _).1 h1
      exact hgs
    have hv'W : v' ∈ Ws := by
      refine finprod_mem_induction (· ∈ Ws) Ws.one_mem (fun _ _ => Ws.mul_mem) ?_
      intro u hu
      obtain ⟨⟨φ, hφ⟩, rfl⟩ := hu
      exact ((hstab φ hφ) w).2 hw
    obtain ⟨x, hxW, hxv⟩ := (mem_imgTil V₁ V hV W v').1 hv'W
    obtain ⟨h1, h2⟩ := hlift x hxv
    exact ⟨x.val, x.val_mem, h1, h2, fun _ => hxW⟩
  · obtain ⟨x, hxv⟩ := mkTil_surjective V₁ V hV v'
    obtain ⟨h1, h2⟩ := hlift x hxv
    exact ⟨x.val, x.val_mem, h1, h2, fun hEW' => absurd hEW' hEW⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
