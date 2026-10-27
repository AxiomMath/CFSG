module

public import CFSG.Quasithin.Background.B3ThreeMain
public import CFSG.Quasithin.Background.B5Models
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.FFC5T2
public import CFSG.Quasithin.Vol2.Ch3B513NAltB
public import CFSG.Quasithin.Vol2.Ch3B513NC3A
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.B513N

open CFSG.Quasithin.B3
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem alt_coord {L : Subgroup (MulAut W)} {U Z : Subgroup W} {n : ℕ} {π : LG n →* ↥L}
    (hr : (FFModel.altDn n).RealizesVia L U Z π) :
    ∃ β : ↥U →* Mod.V n Mod.ut0, Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z) ∧
      ∀ (σ : LG n) (u : ↥U) (hu : ((π σ : ↥L) : MulAut W) (u : W) ∈ U),
        β ⟨((π σ : ↥L) : MulAut W) (u : W), hu⟩ = actL n Mod.ut0 σ (β u) := by
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := hr
  refine ⟨dnEquiv.toMonoidHom.comp β, dnEquiv.surjective.comp hβs, fun u => ?_,
    fun σ u hu => ?_⟩
  · show dnEquiv (β u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, hβk]
  · obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β u)
    have hx' : (FFModel.altDn n).act σ (x : (FFModel.altDn n).Amb) ∈ (FFModel.altDn n).sec :=
      hsec σ x x.2
    have h1 := hβe σ u x hu hx' hx.symm
    show dnEquiv (β ⟨_, hu⟩) = actL n Mod.ut0 σ (dnEquiv (β u))
    refine (congrArg dnEquiv h1).trans ?_
    rw [← hx]
    exact dnEquiv_mk_act σ x hx'

theorem hasGood_of_sym5 (hW : ∀ w : W, w ^ 2 = 1) {G Gi : Subgroup (MulAut W)} (hGi : Gi ≤ G)
    {Wi C : Subgroup W} (hC : C = fixV G) (hWi : Wi = commV Gi ⊔ C)
    (hS : SymmetricNatural Gi Wi C 5) : HasGood G := by
  set H : Subgroup (MulAut W) := ⁅Gi, Gi⁆ with hHdef
  have hHGi : H ≤ Gi := Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact Gi.mul_mem (Gi.mul_mem (Gi.mul_mem hg hh) (Gi.inv_mem hg)) (Gi.inv_mem hh)
  have hHG : H ≤ G := hHGi.trans hGi
  obtain ⟨π₀, hr₀⟩ := B5.alternatingNatural_derived (by norm_num) hS
  let π : LG 5 →* ↥H := π₀
  have hr : (FFModel.altDn 5).RealizesVia H Wi C π := hr₀
  obtain ⟨β, hβs, hβk, hβe⟩ := alt_coord hr
  obtain ⟨hfixG, hcommG, -⟩ := classify_odd (n := 5) (Or.inl rfl) (V_sq' Mod.ut0)
    (hasOneChief_natural (by norm_num)) (isIndec_natural (by norm_num))
  have hHU : commV H ≤ Wi := (commV_mono hHGi).trans (hWi ▸ le_sup_left)
  have hinvW : ∀ h : ↥H, ∀ u ∈ Wi, (h : MulAut W) u ∈ Wi := hr.2.2.2.1
  have hsup : commV H ⊔ C = Wi := by
    refine le_antisymm (sup_le hHU (hWi ▸ le_sup_right)) ?_
    let S : Subgroup (Mod.V 5 Mod.ut0) := ((commV H).subgroupOf Wi).map β
    have hS : S = ⊤ := by
      rw [eq_top_iff, ← hcommG]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨σ, m, -, rfl⟩
      obtain ⟨u, rfl⟩ := hβs m
      have hmem : ((π σ : ↥H) : MulAut W) (u : W) ∈ Wi := hinvW _ u u.2
      refine ⟨⟨_, Wi.mul_mem hmem (Wi.inv_mem u.2)⟩,
        Subgroup.subset_closure ⟨(π σ : MulAut W), (π σ).2, (u : W), rfl⟩, ?_⟩
      have e : (⟨_, Wi.mul_mem hmem (Wi.inv_mem u.2)⟩ : ↥Wi) = ⟨_, hmem⟩ * u⁻¹ := rfl
      rw [e, map_mul, map_inv, hβe σ u hmem]
    intro w hw
    have hw' : β ⟨w, hw⟩ ∈ S := by rw [hS]; trivial
    obtain ⟨x, hx, hxw⟩ := hw'
    have hC' : ((x⁻¹ * ⟨w, hw⟩ : ↥Wi) : W) ∈ C := by
      rw [← hβk, map_mul, map_inv, hxw, inv_mul_cancel]
    have e : w = (x : W) * ((x⁻¹ * ⟨w, hw⟩ : ↥Wi) : W) := by
      show w = (x : W) * ((x : W)⁻¹ * w)
      group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hx) hC'
  have hfix : fixV H ⊓ commV H ≤ C := by
    rintro u ⟨hu, huU⟩
    have huW : u ∈ Wi := hHU huU
    have h1 : β ⟨u, huW⟩ ∈ fixG (actL 5 Mod.ut0) := by
      intro σ
      have hmem : ((π σ : ↥H) : MulAut W) u ∈ Wi := hinvW _ u huW
      rw [← hβe σ ⟨u, huW⟩ hmem]
      congr 1
      exact Subtype.ext (hu _ (π σ).2)
    rw [hfixG, Subgroup.mem_bot] at h1
    exact (hβk _).1 h1
  have hinvH : ∀ h : ↥H, ∀ u ∈ commV H, (h : MulAut W) u ∈ commV H := fun h u hu =>
    FFC.commV_invariant_self H h h.2 u hu
  have hr' := FFC.realizesVia_restrict hr hsup hinvH
  have hZ : C ⊓ commV H = fixV H ⊓ commV H := by
    refine le_antisymm (inf_le_inf_right _ ?_) (le_inf hfix inf_le_right)
    rw [hC]
    intro c hc x hx
    exact hc x (hHG hx)
  rw [hZ] at hr'
  have hcomm : XMod.commOf ↥H (commV H) = commV H := by
    let ρ : LG 5 →* MulAut W := H.subtype.comp π
    have hρ : commG ρ = commV H := by
      apply le_antisymm
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨g, m, -, rfl⟩
        exact Subgroup.subset_closure ⟨(π g : MulAut W), (π g).2, m, rfl⟩
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨x, hx, v, rfl⟩
        obtain ⟨g, hg⟩ : ∃ g : LG 5, π g = ⟨x, hx⟩ := hr.1 ⟨x, hx⟩
        refine Subgroup.subset_closure ⟨g, v, trivial, ?_⟩
        show x v * v⁻¹ = ((π g : ↥H) : MulAut W) v * v⁻¹
        rw [hg]
    have hρ' : commOn ρ (commV H) = XMod.commOf ↥H (commV H) := by
      apply le_antisymm
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨g, m, hm, rfl⟩
        exact Subgroup.subset_closure ⟨π g, m, hm, rfl⟩
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨a, l, hl, rfl⟩
        obtain ⟨g, hg⟩ : ∃ g : LG 5, π g = a := hr.1 a
        refine Subgroup.subset_closure ⟨g, l, hl, ?_⟩
        show (a : MulAut W) l * l⁻¹ = ((π g : ↥H) : MulAut W) l * l⁻¹
        rw [hg]
    have h := commOn_commG (commutator_LG (n := 5) (by norm_num)) hW ρ
    rw [hρ, hρ'] at h
    exact h
  obtain ⟨a, haH, ha1, ha2, hcard⟩ := exists_inv_alt hW (Or.inl rfl) hr' hcomm
  exact HasGood.of_zpowers hW (hHG haH) ha1 ha2 hcard

theorem hasGood_of_transfer_two (hW : ∀ w : W, w ^ 2 = 1) {G G₁ G₂ : Subgroup (MulAut W)}
    (hJ : G = ffJ G) (hsup : G₁ ⊔ G₂ = G) (hd : G₁ ⊓ G₂ = ⊥)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hne : G₁ ≠ ⊥) {W₁ W₂ : Subgroup W}
    (hW12 : W₁ ⊔ W₂ = ⊤) (h2 : ∀ g ∈ G₂, ∀ w ∈ W₁, g w = w)
    (hsmall : ∀ E : Subgroup (MulAut W), E ≤ G₁ → IsElemAbelian2 E → Nat.card E ≤ 2)
    (hind : ∀ g ∈ G₁, Nat.card W₂ ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers g) ⊓ W₂)) :
    HasGood G := by
  obtain ⟨A, hA, hAG₂⟩ : ∃ A, IsFFStarOffender G A ∧ ¬ A ≤ G₂ := by
    by_contra hno
    push Not at hno
    apply hne
    have hGG₂ : G ≤ G₂ := by
      rw [hJ]
      exact iSup₂_le fun A hA => hno A hA
    rw [eq_bot_iff]
    intro g hg
    have hg' : g ∈ G₁ ⊓ G₂ := ⟨hg, hGG₂ (hsup ▸ Subgroup.mem_sup_left hg)⟩
    rw [hd] at hg'
    exact hg'
  have hAG : A ≤ G₁ ⊔ G₂ := hsup ▸ hA.1
  set B := prj G₁ G₂ A hc with hB
  have hBne : B ≠ ⊥ := by
    intro hbot
    apply hAG₂
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc (hAG hx)
    have haB : a ∈ B := ⟨ha, b, hb, hx⟩
    rw [hbot, Subgroup.mem_bot] at haB
    rw [haB, one_mul]
    exact hb
  have ht := card_mul_le_of_fix hA h2 (Y := W₁)
  have hcard := card_le_card_prj_mul hc hAG
  have hfix := fixV_prj_inf hc hAG h2 (Y := W₁)
  have hpos : 0 < Nat.card ↥(A ⊓ G₂) := Nat.card_pos
  have hW₁ : Nat.card W₁ ≤ Nat.card B * Nat.card ↥(fixV B ⊓ W₁) := by
    rw [hfix]
    have : Nat.card W₁ * Nat.card ↥(A ⊓ G₂) ≤
        Nat.card B * Nat.card ↥(fixV A ⊓ W₁) * Nat.card ↥(A ⊓ G₂) := by
      calc Nat.card W₁ * Nat.card ↥(A ⊓ G₂) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ W₁) := ht
        _ ≤ Nat.card B * Nat.card ↥(A ⊓ G₂) * Nat.card ↥(fixV A ⊓ W₁) :=
            Nat.mul_le_mul_right _ hcard
        _ = Nat.card B * Nat.card ↥(fixV A ⊓ W₁) * Nat.card ↥(A ⊓ G₂) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hBel := isElemAbelian2_prj hc hd hA.2.2.1
  have hB2 : Nat.card B ≤ 2 := hsmall B (prj_le hc A) hBel
  obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
    by_contra h
    push Not at h
    exact hBne (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  have ht2 : t ^ 2 = 1 := hBel.2 t htB
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hzB : Subgroup.zpowers t = B := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 htB) ?_
    rw [Nat.card_zpowers, hord]
    exact hB2
  have htG₁ : t ∈ G₁ := prj_le hc A htB
  have h1 : Nat.card W₁ ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ W₁) := by
    rw [hzB]
    exact hW₁.trans (Nat.mul_le_mul_right _ hB2)
  have h2' := hind t htG₁
  have hmap : ∀ Y : Subgroup W, Nat.card Y ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ Y) →
      Nat.card ↥(Y.map (cmHom t)) ≤ 2 := by
    intro Y hY
    have e := B1More.card_map_mul_card_inf_ker Y (cmHom t)
    rw [ker_cmHom, inf_comm] at e
    have hpos' : 0 < Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ Y) := Nat.card_pos
    have : Nat.card ↥(Y.map (cmHom t)) * Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ Y) ≤
        2 * Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ Y) := by rw [e]; exact hY
    exact Nat.le_of_mul_le_mul_right this hpos'
  have hrange : (cmHom t).range = (W₁.map (cmHom t)) ⊔ (W₂.map (cmHom t)) := by
    rw [← Subgroup.map_sup, hW12, ← MonoidHom.range_eq_map]
  have hcardt : Nat.card (commV (Subgroup.zpowers t)) ≤ 4 := by
    calc Nat.card (commV (Subgroup.zpowers t)) ≤ Nat.card (cmHom t).range :=
          Subgroup.card_le_of_le (commV_zpowers_le_range t)
      _ ≤ Nat.card ↥(W₁.map (cmHom t)) * Nat.card ↥(W₂.map (cmHom t)) := by
          rw [hrange]
          exact card_sup_le _ _
      _ ≤ 2 * 2 := Nat.mul_le_mul (hmap W₁ h1) (hmap W₂ h2')
      _ = 4 := by norm_num
  exact HasGood.of_zpowers hW (hsup ▸ Subgroup.mem_sup_left htG₁) ht1 ht2 hcardt

end CFSG.Quasithin.B513N
