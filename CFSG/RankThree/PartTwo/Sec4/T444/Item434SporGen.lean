module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporGen

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open Item434Kit Item434Alt Item434Spor
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

section Props

variable {X : Type*} [Group X]

@[expose] def FixGen (P : Subgroup X) : Prop :=
  ∃ S : Set X, (⊤ : Subgroup X) ≤ Subgroup.closure S ∧
    ∀ σ ∈ S, Nat.Coprime (orderOf σ) 3 ∧ ∃ p ∈ P, p ≠ 1 ∧ p * σ = σ * p

@[expose] def NoSignalizer (P : Subgroup X) : Prop :=
  ∀ Y : Subgroup (MulAut X), ¬ 3 ∣ Nat.card Y →
    P.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥

theorem FixGen.map_conj {P : Subgroup X} (h : FixGen P) (g : X) :
    FixGen (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨S, hS, hgen⟩ := h
  set c := (MulAut.conj g).toMonoidHom with hc
  refine ⟨c '' S, ?_, ?_⟩
  · intro y _
    have hy : (MulAut.conj g).symm y ∈ Subgroup.closure S := hS (Subgroup.mem_top _)
    have h1 : c ((MulAut.conj g).symm y) ∈ (Subgroup.closure S).map c :=
      Subgroup.mem_map_of_mem c hy
    rw [MonoidHom.map_closure] at h1
    have h2 : c ((MulAut.conj g).symm y) = y := (MulAut.conj g).apply_symm_apply y
    rwa [h2] at h1
  · rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨h3, p, hp, hp1, hpσ⟩ := hgen σ hσ
    refine ⟨?_, c p, Subgroup.mem_map_of_mem c hp, ?_, ?_⟩
    · rw [hc, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact h3
    · intro h1
      exact hp1 ((map_eq_one_iff _ (MulAut.conj g).injective).mp h1)
    · rw [← map_mul, ← map_mul, hpσ]

theorem NoSignalizer.map_conj {P : Subgroup X} (h : NoSignalizer P) (g : X) :
    NoSignalizer (P.map (MulAut.conj g).toMonoidHom) := by
  intro Y hY3 hPY
  set f := (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom with hf
  have hY'card : Nat.card (Y.map f) = Nat.card Y :=
    Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj g)⁻¹).injective
  have hPY' : P.map (MulAut.conj : X →* MulAut X) ≤
      Subgroup.normalizer ((Y.map f : Subgroup (MulAut X)) : Set (MulAut X)) := by
    rintro _ ⟨p, hp, rfl⟩
    have hmem : MulAut.conj (MulAut.conj g p) ∈ Subgroup.normalizer (Y : Set (MulAut X)) :=
      hPY ⟨MulAut.conj g p, ⟨p, hp, rfl⟩, rfl⟩
    have h1 := Subgroup.le_normalizer_map f ⟨_, hmem, rfl⟩
    have heq : f (MulAut.conj (MulAut.conj g p)) = MulAut.conj p := by
      have hc : MulAut.conj (MulAut.conj g p) =
          MulAut.conj g * MulAut.conj p * (MulAut.conj g)⁻¹ := by
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
      rw [hc, hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [heq] at h1
  have hY'1 := h (Y.map f) (by rw [hY'card]; exact hY3) hPY'
  rw [← Subgroup.card_eq_one, ← hY'card, hY'1, Subgroup.card_bot]

end Props

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem layer_le_of_fixed_gens_of_card (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {S : Set X}
    (hS : (⊤ : Subgroup X) ≤ Subgroup.closure S)
    (hgen : ∀ σ ∈ S, Nat.Coprime (orderOf σ) 3 ∧ ∃ F : Subgroup (MulAut X),
      F ≤ A.map (quotConj e) ∧ 9 ≤ Nat.card (A ⊓ F.comap (quotConj e) : Subgroup G) ∧
        ∀ φ ∈ F, φ σ = σ) :
    layer G ≤ M := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  set φ := layerQuot e with hφ
  have hZ : IsPGroup 3 ((⊤ : Subgroup (layer G)) ⊓ φ.ker : Subgroup (layer G)) := by
    rw [top_inf_eq, hφ, ker_layerQuot]
    exact h.isPGroup_center_layer
  have hcen : ∀ z ∈ (⊤ : Subgroup (layer G)) ⊓ φ.ker, ∀ l ∈ (⊤ : Subgroup (layer G)),
      z * l = l * z := by
    intro z hz l _
    rw [top_inf_eq, hφ, ker_layerQuot] at hz
    exact (Subgroup.mem_center_iff.mp hz l).symm
  set R : Subgroup (layer G) := M.comap (layer G).subtype with hR
  have hlift : ∀ σ ∈ S, σ ∈ R.map φ := by
    intro σ hσ
    obtain ⟨hσ3, F, -, hB9, hFfix⟩ := hgen σ hσ
    obtain ⟨x, rfl⟩ := layerQuot_surjective e σ
    obtain ⟨y, -, hyx, hy3⟩ := exists_coprime_lift φ hZ (Subgroup.mem_top x) hσ3
    set B := A ⊓ F.comap (quotConj e) with hB
    have hyB : (y : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hconj : layerConj G b y = y := by
        refine eq_of_coprime_lift φ hZ hcen (Subgroup.mem_top _) (Subgroup.mem_top _) ?_ ?_ hy3
        · rw [hφ, ← quotConj_layerQuot, ← hφ, hyx]
          exact hFfix _ hb.2
        · rw [MulEquiv.orderOf_eq]
          exact hy3
      have h1 : b * (y : G) * b⁻¹ = y := by rw [← layerConj_apply_coe, hconj]
      calc b * (y : G) = b * y * b⁻¹ * b := by group
        _ = y * b := by rw [h1]
    exact ⟨y, (Subgroup.centralizer_le_normalizer _).trans (normalizer_le h inf_le_left hB9) hyB,
      hyx⟩
  have hker : φ.ker ≤ Subgroup.center (layer G) := by rw [hφ, ker_layerQuot]
  have hrange : φ.range ≤ R.map φ := by
    rw [MonoidHom.range_eq_top.mpr (layerQuot_surjective e)]
    exact hS.trans ((Subgroup.closure_le _).mpr hlift)
  have htop := eq_top_of_range_le_map φ hker hrange
  intro x hx
  have hmem : (⟨x, hx⟩ : layer G) ∈ R := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

theorem nine_le_card_inf_comap_zpowers (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (h9 : Nat.card (A.map (quotConj e)) = 9)
    {φ : MulAut X} (hφ : φ ∈ A.map (quotConj e)) (hφ1 : φ ≠ 1) :
    9 ≤ Nat.card (A ⊓ (Subgroup.zpowers φ).comap (quotConj e) : Subgroup G) := by
  set q := quotConj e with hq
  set B := A ⊓ (Subgroup.zpowers φ).comap q with hB
  have hker : q.ker = Subgroup.centralizer (layer G : Set G) := ker_quotConj h.isQuasisimple e
  have hA := card_eq_card_inf_ker_mul_card_map q A
  rw [h.isE27.2, h9] at hA
  have hAk : Nat.card (A ⊓ q.ker : Subgroup G) = 3 := by omega
  have hBk : B ⊓ q.ker = A ⊓ q.ker := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · intro c hc
      refine ⟨⟨hc.1, ?_⟩, hc.2⟩
      show q c ∈ Subgroup.zpowers φ
      rw [MonoidHom.mem_ker.mp hc.2]
      exact Subgroup.one_mem _
  have hBmap : B.map q = Subgroup.zpowers φ := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hb.2
    · intro ψ hψ
      have hψA : ψ ∈ A.map q :=
        (Subgroup.zpowers_le.mpr hφ) hψ
      obtain ⟨a, ha, rfl⟩ := hψA
      exact ⟨a, ⟨ha, hψ⟩, rfl⟩
  have hφ3 : orderOf φ = 3 := by
    have hpow : φ ^ 3 = 1 := (isElemAbelian_map_quotConj h e).2 φ hφ
    exact orderOf_eq_prime hpow hφ1
  have hB := card_eq_card_inf_ker_mul_card_map q B
  rw [hBk, hAk, hBmap, Nat.card_zpowers, hφ3] at hB
  omega

theorem layer_le_of_fixGen (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (h9 : Nat.card (A.map (quotConj e)) = 9)
    (hcen : Subgroup.center X = ⊥) {P : Subgroup X}
    (hP : P.map (MulAut.conj : X →* MulAut X) = A.map (quotConj e)) (hgen : FixGen P) :
    layer G ≤ M := by
  obtain ⟨S, hS, hgS⟩ := hgen
  refine layer_le_of_fixed_gens_of_card h e hS fun σ hσ => ?_
  obtain ⟨h3, p, hp, hp1, hpσ⟩ := hgS σ hσ
  have hφA : MulAut.conj p ∈ A.map (quotConj e) := by
    rw [← hP]
    exact Subgroup.mem_map_of_mem _ hp
  have hφ1 : MulAut.conj p ≠ 1 := by
    intro h1
    apply hp1
    exact conj_injective_of_center_eq_bot hcen (h1.trans (map_one _).symm)
  refine ⟨h3, Subgroup.zpowers (MulAut.conj p), Subgroup.zpowers_le.mpr hφA,
    nine_le_card_inf_comap_zpowers h e h9 hφA hφ1, ?_⟩
  intro ψ hψ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hψ
  have hfix : MulAut.conj p σ = σ := by
    rw [MulAut.conj_apply, hpσ, mul_inv_cancel_right]
  rw [← map_zpow]
  rw [MulAut.conj_apply]
  have hc : Commute (p ^ k) σ := (Commute.zpow_left (show Commute p σ from hpσ) k)
  rw [hc.eq, mul_inv_cancel_right]

theorem exists_inner_e9 (h : Ctx434Core G A M Q) (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hout : ¬ 3 ∣ Nat.card (Outer X)) (hcen : Subgroup.center X = ⊥)
    (h9 : Nat.card (A.map (quotConj e)) = 9) :
    ∃ P : Subgroup X, P.map (MulAut.conj : X →* MulAut X) = A.map (quotConj e) ∧
      CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P = 9 := by
  set P := (A.map (quotConj e)).comap (MulAut.conj : X →* MulAut X) with hPdef
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := map_comap_conj_eq h e hout
  have hinj := conj_injective_of_center_eq_bot hcen
  refine ⟨P, hPmap, isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj h e),
    ?_⟩
  rw [← Subgroup.card_map_of_injective hinj, hPmap, h9]

theorem false_of_kill9 (h : Ctx434Core G A M Q) (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hout : ¬ 3 ∣ Nat.card (Outer X)) (hcen : Subgroup.center X = ⊥)
    (hK : ∀ P : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 9 →
      FixGen P ∨ NoSignalizer P)
    (h9 : Nat.card h.layerStar = 9) : False := by
  have h9' : Nat.card (A.map (quotConj e)) = 9 := by rw [card_map_quotConj h e, h9]
  obtain ⟨P, hPmap, hPe, hP9⟩ := exists_inner_e9 h e hout hcen h9'
  rcases hK P hPe hP9 with hF | hN
  · exact h.not_le (layer_le_of_fixGen h e h9' hcen hPmap hF)
  · exact false_of_normalizer h e fun Y hY3 hAY => hN Y hY3 (hPmap ▸ hAY)

end Ctx

section Families


theorem item434SporAtCard_nine_of_kill9 {s : TauCeti.SporadicName} {X : Type} [Group X]
    (b : X ≃* Spor s) (hout : ¬ 3 ∣ Nat.card (Outer X)) (hX : ¬ (Nat.card X).Prime)
    (hK : ∀ P : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 9 →
      FixGen P ∨ NoSignalizer P) :
    Item434SporAtCard s 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := hc.isQuasisimple.2.1
  have : IsSimpleGroup X := (e₀.trans b.symm).symm.isSimpleGroup
  exact (false_of_kill9 hc (e₀.trans b.symm) hout (center_eq_bot_of_simple hX) hK h9).elim

end Families

end CFSG.RankThree.PartTwo.Sec4.Item434SporGen
