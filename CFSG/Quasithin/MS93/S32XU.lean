module

public import CFSG.Quasithin.MS93.S32Main
public import CFSG.Quasithin.MS93.S32Gal
public import CFSG.Quasithin.Background.B15P4Res

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section TwoCopies

variable {V : Type} [CommGroup V] {F : Type} [Field F] {K : Subgroup (MulAut V)}
  {π : ↥(StatedSL 3 F) →* ↥K}

theorem mem_of_commV_le_of_inf_eq_bot {A B U : Subgroup V}
    (hA : (FFModel.nat (StatedSL 3 F)).RealizesVia K A ⊥ π)
    (hB : (FFModel.nat (StatedSL 3 F)).RealizesVia K B ⊥ π) (hUA : U ⊓ A = ⊥) (hUW : U ≤ A ⊔ B)
    (hUK : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) (hU0 : U ≠ ⊥) {v : V} (hv : v ∈ A ⊔ B)
    (hvU : ∀ k ∈ K, k v * v⁻¹ ∈ U) : v ∈ U := by
  have hAinv : ∀ k ∈ K, ∀ a ∈ A, k a ∈ A := fun k hk a ha => hA.2.2.2.1 ⟨k, hk⟩ a ha
  have hBinv : ∀ k ∈ K, ∀ b ∈ B, k b ∈ B := fun k hk b hb => hB.2.2.2.1 ⟨k, hk⟩ b hb
  set J := (U ⊔ A) ⊓ B with hJ
  have hJinv : ∀ k ∈ K, ∀ x ∈ J, k x ∈ J := by
    rintro k hk x ⟨hxUA, hxB⟩
    refine ⟨?_, hBinv k hk x hxB⟩
    obtain ⟨u, hu, a, ha, rfl⟩ := Subgroup.mem_sup.mp hxUA
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hUK k hk u hu) (hAinv k hk a ha)
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hU0
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (hUW u.2)
    intro hJb
    have hbJ : b ∈ J := by
      refine ⟨?_, hb⟩
      have : b = (u : V) * a⁻¹ := by rw [← hab, mul_comm a b, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.mul_mem_sup u.2 (A.inv_mem ha)
    rw [hJb, Subgroup.mem_bot] at hbJ
    rw [hbJ, mul_one] at hab
    have : (u : V) ∈ U ⊓ A := ⟨u.2, hab ▸ ha⟩
    rw [hUA, Subgroup.mem_bot] at this
    exact hu1 (Subtype.ext this)
  have hJB : J = B := by
    rcases natReal_inv_eq isTransNZ_statedSL3 hB hJinv bot_le inf_le_right with h | h
    · exact (hJ0 h).elim
    · exact h
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
  have hbJ : b ∈ J := hJB ▸ hb
  obtain ⟨u', hu', a', ha', hb'⟩ := Subgroup.mem_sup.mp hbJ.1
  have hv' : a * b = (a * a') * u' := by rw [← hb', mul_comm u' a', mul_assoc]
  have hc : ∀ k ∈ K, k (a * a') = a * a' := by
    intro k hk
    have hcA : k (a * a') * (a * a')⁻¹ ∈ A :=
      A.mul_mem (hAinv k hk _ (A.mul_mem ha ha')) (A.inv_mem (A.mul_mem ha ha'))
    have hcU : k (a * a') * (a * a')⁻¹ ∈ U := by
      have h1 := hvU k hk
      rw [hv'] at h1
      have e : k (a * a' * u') * (a * a' * u')⁻¹ =
          k (a * a') * (a * a')⁻¹ * (k u' * u'⁻¹) := by
        rw [map_mul k (a * a') u', mul_inv]
        ac_rfl
      rw [e] at h1
      have h2 : k u' * u'⁻¹ ∈ U := U.mul_mem (hUK k hk u' hu') (U.inv_mem hu')
      have := U.mul_mem h1 (U.inv_mem h2)
      rwa [mul_inv_cancel_right] at this
    have : k (a * a') * (a * a')⁻¹ ∈ U ⊓ A := ⟨hcU, hcA⟩
    rw [hUA, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  have hc1 := natReal_fixed isTransNZ_statedSL3 (exists_two_ne_zero F) hA (A.mul_mem ha ha') hc
  rw [Subgroup.mem_bot] at hc1
  rw [hv', hc1, one_mul]
  exact hu'

theorem mem_of_commV_le_of_two_copies {I : Fin 2 → Subgroup V}
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 F)).RealizesVia K (I i) ⊥ π) {U : Subgroup V}
    (hUI : U ≤ I 0 ⊔ I 1) (hUK : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) (hU0 : U ≠ ⊥)
    (hU1 : U ≠ I 0 ⊔ I 1) {v : V} (hv : v ∈ I 0 ⊔ I 1) (hvU : ∀ k ∈ K, k v * v⁻¹ ∈ U) :
    v ∈ U := by
  have hle : ∀ i, U ⊓ I i ≠ ⊥ → I i ≤ U := by
    intro i hi
    have hinv : ∀ k ∈ K, ∀ x ∈ U ⊓ I i, k x ∈ U ⊓ I i := fun k hk x hx =>
      ⟨hUK k hk x hx.1, (hreal i).2.2.2.1 ⟨k, hk⟩ x hx.2⟩
    rcases natReal_inv_eq isTransNZ_statedSL3 (hreal i) hinv bot_le inf_le_right with h | h
    · exact (hi h).elim
    · exact h ▸ inf_le_left
  by_cases h0 : U ⊓ I 0 = ⊥
  · exact mem_of_commV_le_of_inf_eq_bot (hreal 0) (hreal 1) h0 hUI hUK hU0 hv hvU
  by_cases h1 : U ⊓ I 1 = ⊥
  · rw [sup_comm] at hUI hv
    exact mem_of_commV_le_of_inf_eq_bot (hreal 1) (hreal 0) h1 hUI hUK hU0 hv hvU
  exact (hU1 (le_antisymm hUI (sup_le (hle 0 h0) (hle 1 h1)))).elim

end TwoCopies

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem autI_mem_intSub_Uq (h : PUHyp M T L) {K : Subgroup G} (hKM : K ≤ M) :
    ∀ k ∈ autI h.isElemAbelian_Xq K, ∀ u ∈ intSub h.isElemAbelian_Xq (Uq M T L),
      k u ∈ intSub h.isElemAbelian_Xq (Uq M T L) := by
  intro k hk u hu
  obtain ⟨g, hg, rfl⟩ := (mem_autI h.isElemAbelian_Xq).1 hk
  show (convI h.isElemAbelian_Xq g u).val ∈ Uq M T L
  rw [convI_apply_val]
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_Uq h.le_normalizer (hKM hg)) _).mp hu

theorem s32PartXU_of : S32PartXU := by
  intro G _ _ M T L h hii
  set hX := h.isElemAbelian_Xq with hXdef
  have hs := isSecW_Xq h
  obtain ⟨-, n, F, iF, fF, hF, I, π, hind, hsup, hreal, -, -⟩ := hii
  have h01 : (⨆ i, I i) = I 0 ⊔ I 1 := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup I 0) (le_iSup I 1)
  rw [h01] at hsup
  refine le_antisymm ?_ (Uq_le_commutator_Xq h)
  by_contra hne
  set U := intSub hX (Uq M T L) with hUdef
  have hMX : M ≤ Subgroup.normalizer (Xq M : Set G) := le_normalizer_Xq M
  have hTN : T ≤ Subgroup.normalizer (Xq M : Set G) := h.le.trans hMX
  have hUI : U ≤ I 0 ⊔ I 1 := by
    intro u hu
    rw [hsup, ← C124.mem_toG_iff_of_mem hX, toG_commV_Xq h]
    exact Uq_le_commutator_Xq h hu
  have hU0 : U ≠ ⊥ := by
    intro hb
    apply h.Uq_ne_bot
    rw [eq_bot_iff]
    intro x hx
    have hxU : IntMod.mk hX ⟨x, h.Uq_le_Xq hx⟩ ∈ U := hx
    rw [hb, Subgroup.mem_bot] at hxU
    exact congrArg IntMod.val hxU
  have hU1 : U ≠ I 0 ⊔ I 1 := by
    intro hUe
    apply hne
    intro x hx
    rw [← toG_commV_Xq h, ← hsup, ← hUe] at hx
    obtain ⟨w, hw, rfl⟩ := (C124.mem_toG hX).1 hx
    exact hw
  have hP : IsPGroup 2 ↥(autI hX T) :=
    IsPGroup.of_surjective h.isPGroup (toAutI hX hTN) (toAutI_surjective hX hTN)
  have hKX := hs.autI_L_le h
  have hXN := hs.autI_le_normalizer h
  obtain ⟨v, hv, hvU, hvT⟩ := exists_fixed_not_mem_of_two_copies IntMod.sq_eq_one hF hKX hXN
    (hs.cent h) hind hreal (fun x hx w hw => by
      rw [hsup] at hw ⊢
      exact B15P4.map_commV_mem (hXN hx) w hw)
    (autI_mono hX h.le) hP hUI (autI_mem_intSub_Uq h h.L_le) (autI_mem_intSub_Uq h h.le) hU0 hU1
  have hvZ : v.val ∈ Z0q M T := by
    have hvF : v ∈ fixV (autI hX T) := fun p hp => hvT p hp
    have := (C124.mem_toG_iff_of_mem hX v).2 hvF
    rw [toG_fixV hX hTN, ← h.omegaOneCenterOf_eq] at this
    exact omegaOneCenterOf_le_Z0q M T h.le this
  refine hvU (mem_of_commV_le_of_two_copies hreal hUI (autI_mem_intSub_Uq h h.L_le) hU0
    hU1 hv fun k hk => ?_)
  obtain ⟨l, hl, rfl⟩ := (mem_autI hX).1 hk
  show (convI hX l v).val * v.val⁻¹ ∈ Uq M T L
  rw [convI_apply_val]
  have hc := Subgroup.commutator_mem_commutator hl hvZ
  rw [Subgroup.commutator_comm] at hc
  exact hc

end CFSG.Quasithin.MS93.S32
