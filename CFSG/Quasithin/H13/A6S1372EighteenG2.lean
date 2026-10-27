module

public import CFSG.Quasithin.Background.SmithB42U33Off
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.B42U33

namespace A6G2

variable {W : Type} [CommGroup W] {K : Type} [Field K] [CharP K 2]

theorem realizeEquiv_zornQ_full {L₀ : Subgroup (MulAut W)}
    {π : (FFModel.zornQ (quasithinG2 K)).Gam →* ↥L₀}
    {β : ↥(⊤ : Subgroup W) →* (FFModel.zornQ (quasithinG2 K)).Mod}
    (h : H.Mathieu.RealizesBy (FFModel.zornQ (quasithinG2 K)) L₀ ⊤ ⊥ π β)
    (γ : ↥(quasithinG2 K)) (w : W) :
    (realizeEquiv (D := FFModel.zornQ (quasithinG2 K)) h) ((π γ : MulAut W) w) =
      g2QAct K γ ((realizeEquiv (D := FFModel.zornQ (quasithinG2 K)) h) w) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
  have hm' : (FFModel.zornQ (quasithinG2 K)).act γ (m : Multiplicative _) ∈
      (FFModel.zornQ (quasithinG2 K)).sec :=
    zornAct_mem_O0 _ le_rfl γ m.2
  have h1 := h.2.2.2.2.2.2.2.2.2 γ ⟨w, trivial⟩ m trivial hm' hm.symm
  change β ⟨(π γ : MulAut W) w, trivial⟩ = g2QAct K γ (β ⟨w, trivial⟩)
  rw [← hm]
  exact h1

omit [CharP K 2] in
theorem exists_equiv_of_g2Natural {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (h : G2Natural L ⊤ ⊥ 1) :
    ∃ e : V ≃* ModQ, ∀ x ∈ L, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range := by
  obtain ⟨F, _, _, hF, hR⟩ := h
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  have := charP_two_of_natCard_two hF2
  obtain ⟨π, β, hβ⟩ := (CFSG.Quasithin.H.Mathieu.realizes_iff _ L ⊤ ⊥).1 hR
  let e : V ≃* (FFModel.zornQ (quasithinG2 F)).Mod :=
    realizeEquiv (D := FFModel.zornQ (quasithinG2 F)) hβ
  have hLe : L.map (MulAut.congr e).toMonoidHom = (g2QAct F).range :=
    map_congr_eq_of_equivariant e π hβ.1 (g2QAct F) id (realizeEquiv_zornQ_full hβ) _
      fun g => MonoidHom.mem_range
  refine ⟨e.trans (modQEquivK hF2).symm, fun x hx => ?_⟩
  have hx' : MulAut.congr e x ∈ (g2QAct F).range := by
    rw [← hLe]
    exact ⟨x, hx, rfl⟩
  obtain ⟨g, hg⟩ := hx'
  have e1 : MulAut.congr (e.trans (modQEquivK hF2).symm) x =
      MulAut.congr (modQEquivK hF2).symm (MulAut.congr e x) := MulEquiv.ext fun _ => rfl
  rw [e1, ← hg, congr_modQEquivK_symm hF2 g]
  exact ⟨_, rfl⟩

end A6G2

theorem asB46ThirteenG2Two_holds :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → ∀ G L A : Subgroup (MulAut V),
      B4Hyp G L → IsFFStarOffender G A → G2Natural (ffJ G) ⊤ ⊥ 1 → 4 < Nat.card (commV A) := by
  intro V _ _ _ G L A _ hA hG2
  obtain ⟨e, he⟩ := A6G2.exists_equiv_of_g2Natural hG2
  have hAJ : A ≤ ffJ G := B6.le_ffJ hA
  have hA' : IsFFStarOffender (ffJ G) A := ⟨hAJ, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  obtain ⟨-, h8⟩ := offender_facts_of_equiv e he hA'
  have hφinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hle : A.map (MulAut.congr e).toMonoidHom ≤ (g2QAct (ZMod 2)).range := by
    rintro _ ⟨a, ha, rfl⟩
    exact he a (hAJ ha)
  have hne : A.map (MulAut.congr e).toMonoidHom ≠ ⊥ := fun h =>
    hA.2.1 ((Subgroup.map_eq_bot_iff_of_injective _ hφinj).1 h)
  have hff : Nat.card ModQ ≤ Nat.card (A.map (MulAut.congr e).toMonoidHom) *
      Nat.card (fixV (A.map (MulAut.congr e).toMonoidHom)) := by
    have h0 := hA.2.2.2 ⊥ bot_le
    rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul] at h0
    rw [Subgroup.card_map_of_injective hφinj, fixV_map_congr,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      ← Nat.card_congr e.toEquiv]
    exact h0
  have hcf := (g2OffenderZorn (ZMod 2) (Nat.card_zmod 2)).1 _ hle hne
    (isElemAbelian2_map_congr e hA.2.2.1) hff
  rw [commV_map_congr, fixV_map_congr] at hcf
  have hcf' : commV A = fixV A := Subgroup.map_injective (f := e.toMonoidHom) e.injective hcf
  rw [hcf', h8]
  norm_num

end CFSG.Quasithin.H13.A6
