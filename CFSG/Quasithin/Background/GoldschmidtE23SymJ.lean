module

public import CFSG.Quasithin.Background.GoldschmidtE23SymCtx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6 Equiv

namespace GE23

section J

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
  {Ps : Set (Subgroup (MulAut V))}
  {ψ : Subgroup (MulAut V) → Perm (Fin 5) →* MulAut V}
  {β : Subgroup (MulAut V) → ↥(coreMod 5) →* V}

theorem map_conj_esa : esa.map (MulAut.conj sr).toMonoidHom = esb := by
  have hle : esa.map (MulAut.conj sr).toMonoidHom ≤ esb := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_esb_iff.2 (sr_conj_esa y (mem_esa_iff.1 hy))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj sr).injective, card_esa, card_esb]

theorem map_conj_esb : esb.map (MulAut.conj sr).toMonoidHom = esa := by
  have hle : esb.map (MulAut.conj sr).toMonoidHom ≤ esa := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_esa_iff.2 (sr_conj_esb y (mem_esb_iff.1 hy))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj sr).injective, card_esa, card_esb]

namespace SymData

variable (hD : SymData X T M Ps ψ β)

include hD

theorem mem_le {A : Subgroup (MulAut V)} (hA : A ∈ Ps) : A ≤ T := (hD.stable.2.1 A hA).1

theorem d8_le_T {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) : d8.map (ψ H) ≤ T := by
  rw [← (hD.spec H hH).syl]
  exact inf_le_left

theorem map_mem_of_le {B : Subgroup (MulAut V)} (hB : B ∈ Ps) {H₀ : Subgroup (MulAut V)}
    (hH₀ : H₀ ∈ B69.blkFamily X) {es : Subgroup (Perm (Fin 5))}
    (hes : es ≤ restrPerm (β H₀) B) (hc2 : Nat.card ↥es = 2) (hf8 : Nat.card ↥(fixΔ es) = 8) :
    es.map (ψ H₀) ∈ Ps := by
  have hBoff := hD.stable.2.1 B hB
  obtain ⟨hcard, hBeq, -⟩ := hD.offender_struct hBoff
  have hAB : es.map (ψ H₀) ≤ B := by
    calc es.map (ψ H₀) ≤ (restrPerm (β H₀) B).map (ψ H₀) := Subgroup.map_mono hes
      _ ≤ ⨆ H ∈ B69.blkFamily X, (restrPerm (β H) B).map (ψ H) :=
          le_iSup₂_of_le (f := fun H (_ : H ∈ B69.blkFamily X) =>
            (restrPerm (β H) B).map (ψ H)) H₀ hH₀ le_rfl
      _ = B := hBeq.symm
  have hcA : Nat.card ↥(es.map (ψ H₀)) = 2 := by
    rw [Subgroup.card_map_of_injective (hD.spec H₀ hH₀).ψ_inj, hc2]
  have hA1 : IsA2 T (es.map (ψ H₀)) := by
    refine ⟨hAB.trans hBoff.1, ?_, ?_, ?_⟩
    · intro h
      rw [h, Subgroup.card_bot] at hcA
      omega
    · exact fun a ha b hb => hBoff.2.2.1.1 a (hAB ha) b (hAB hb)
    · exact fun a ha => hBoff.2.2.1.2 a (hAB ha)
  have hsingle := hD.fam.card_fixV_single hH₀ (hD.fam.map_le hH₀ es)
  rw [(hD.spec H₀ hH₀).card_fix_map, hf8] at hsingle
  have hFF : FFLe T (es.map (ψ H₀)) B := by
    refine ⟨hA1, hBoff.isA2, hAB, ?_⟩
    rw [hcard, hcA]
    omega
  exact hD.stable.2.2.2 B hB _ hFF

theorem esa_esb_mem_of_one {H₀ : Subgroup (MulAut V)} (hH₀ : H₀ ∈ B69.blkFamily X)
    (h : esa.map (ψ H₀) ∈ Ps ∨ esb.map (ψ H₀) ∈ Ps) :
    esa.map (ψ H₀) ∈ Ps ∧ esb.map (ψ H₀) ∈ Ps := by
  have hsrT : ψ H₀ sr ∈ T :=
    hD.d8_le_T hH₀ (Subgroup.mem_map_of_mem _ sr_mem_d8)
  have hcomp : (MulAut.conj (ψ H₀ sr)).toMonoidHom.comp (ψ H₀) =
      (ψ H₀).comp (MulAut.conj sr).toMonoidHom := by
    ext σ
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  have key : ∀ es es' : Subgroup (Perm (Fin 5)), es.map (MulAut.conj sr).toMonoidHom = es' →
      es.map (ψ H₀) ∈ Ps → es'.map (ψ H₀) ∈ Ps := by
    intro es es' hee hA
    have := hD.stable.2.2.1 _ hA (ψ H₀ sr) hsrT
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hee] at this
    exact this
  rcases h with h | h
  · exact ⟨h, key esa esb map_conj_esa h⟩
  · exact ⟨key esb esa map_conj_esb h, h⟩

theorem esa_esb_mem {B : Subgroup (MulAut V)} (hB : B ∈ Ps) {H₀ : Subgroup (MulAut V)}
    (hH₀ : H₀ ∈ B69.blkFamily X) (hne : restrPerm (β H₀) B ≠ ⊥) :
    esa.map (ψ H₀) ∈ Ps ∧ esb.map (ψ H₀) ∈ Ps := by
  obtain ⟨-, -, hR⟩ := hD.offender_struct (hD.stable.2.1 B hB)
  obtain ⟨hRe4, hR16⟩ := hR H₀ hH₀
  refine hD.esa_esb_mem_of_one hH₀ ?_
  rcases gen_of_sub hRe4 hne hR16 with h | h
  · left
    refine hD.map_mem_of_le hB hH₀ ?_ card_esa card_fixΔ_esa
    exact (Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 h)
  · right
    refine hD.map_mem_of_le hB hH₀ ?_ card_esb card_fixΔ_esb
    exact (Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 h)

theorem e4_le_ffJP {B : Subgroup (MulAut V)} (hB : B ∈ Ps) {H₀ : Subgroup (MulAut V)}
    (hH₀ : H₀ ∈ B69.blkFamily X) (hne : restrPerm (β H₀) B ≠ ⊥) :
    e4.map (ψ H₀) ≤ ffJP Ps T := by
  obtain ⟨ha, hb⟩ := hD.esa_esb_mem hB hH₀ hne
  rw [e4_eq_sup, Subgroup.map_sup]
  exact sup_le (B19.le_ffJP ha (hD.mem_le ha)) (B19.le_ffJP hb (hD.mem_le hb))

theorem ffJP_eq : ffJP Ps T = ⨆ H ∈ B69.blkFamily X, e4.map (ψ H) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun A => iSup_le fun hA => iSup_le fun _ => ?_
    obtain ⟨-, hBeq, hR⟩ := hD.offender_struct (hD.stable.2.1 A hA)
    refine le_trans hBeq.le (iSup₂_le fun H hH => ?_)
    exact le_iSup₂_of_le (f := fun H' (_ : H' ∈ B69.blkFamily X) => e4.map (ψ H')) H hH
      (Subgroup.map_mono (hR H hH).1)
  · refine iSup_le fun H => iSup_le fun hH => ?_
    obtain ⟨B₀, hB₀⟩ := hD.stable.1
    have hB₀ne : B₀ ≠ ⊥ := (hD.stable.2.1 B₀ hB₀).2.1
    obtain ⟨-, hBeq, -⟩ := hD.offender_struct (hD.stable.2.1 B₀ hB₀)
    obtain ⟨H₀, hH₀, hne₀⟩ : ∃ H₀ ∈ B69.blkFamily X, restrPerm (β H₀) B₀ ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      apply hB₀ne
      refine le_bot_iff.1 (le_trans hBeq.le (iSup₂_le fun H' hH' => ?_))
      rw [hcon H' hH', Subgroup.map_bot]
    obtain ⟨ha, -⟩ := hD.esa_esb_mem hB₀ hH₀ hne₀
    obtain ⟨t, ht, hconj⟩ := (hD.ctx.sc).2.2.2.2.2.2.2.1 H₀ hH₀ H hH
    have hA₁ : B6.conjSub t (esa.map (ψ H₀)) ∈ Ps := hD.stable.2.2.1 _ ha t ht
    have hA₁H : B6.conjSub t (esa.map (ψ H₀)) ≤ H := by
      rw [← hconj]
      exact (B6.conjSub t).monotone (hD.fam.map_le hH₀ esa)
    have hA₁T : B6.conjSub t (esa.map (ψ H₀)) ≤ T := hD.mem_le hA₁
    have hA₁ne : B6.conjSub t (esa.map (ψ H₀)) ≠ ⊥ := by
      intro h
      have h3 : esa.map (ψ H₀) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (esa.map (ψ H₀))
          (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective).1 h
      have : Nat.card ↥(esa.map (ψ H₀)) = 1 := by rw [h3, Subgroup.card_bot]
      rw [Subgroup.card_map_of_injective (hD.spec H₀ hH₀).ψ_inj, card_esa] at this
      omega
    have hne₁ : restrPerm (β H) (B6.conjSub t (esa.map (ψ H₀))) ≠ ⊥ := by
      obtain ⟨⟨a, ha1⟩, ha2⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA₁ne
      have ha2' : a ≠ 1 := fun h => ha2 (Subtype.ext h)
      have haD : (a : MulAut V) ∈ d8.map (ψ H) := by
        rw [← (hD.spec H hH).syl]
        exact ⟨hA₁T ha1, hA₁H ha1⟩
      obtain ⟨σ, hσ, hσa⟩ := Subgroup.mem_map.1 haD
      refine (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨σ, ?_⟩, ?_⟩
      · exact (hD.spec H hH).mem_restrPerm_of_act ha1 (fun w _ => by rw [hσa])
      · intro h
        apply ha2'
        have : σ = 1 := congrArg Subtype.val h
        rw [← hσa, this, map_one]
    exact hD.e4_le_ffJP hA₁ hH hne₁

theorem ffJP_inf_eq {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) :
    ffJP Ps T ⊓ H = e4.map (ψ H) := by
  rw [hD.ffJP_eq]
  exact le_antisymm (hD.fam.inf_E_le hH)
    (le_inf (le_iSup₂_of_le (f := fun H' (_ : H' ∈ B69.blkFamily X) => e4.map (ψ H')) H hH le_rfl)
      (hD.fam.map_le hH _))

theorem card_le_J : Nat.card V ≤ Nat.card ↥(ffJP Ps T) * Nat.card ↥(fixV (ffJP Ps T)) := by
  rw [hD.ffJP_eq]
  exact hD.fam.card_E.ge

theorem ffJP_ne_bot : ffJP Ps T ≠ ⊥ := by
  obtain ⟨B, hB⟩ := hD.stable.1
  intro h
  have : B ≤ ffJP Ps T := B19.le_ffJP hB (hD.mem_le hB)
  rw [h] at this
  exact (hD.stable.2.1 B hB).2.1 (le_bot_iff.1 this)

end SymData

end J

end GE23

end CFSG.Quasithin
