module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXAA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Free
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Frobenius

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem s13IsoComps_stable {X : Subgroup (MulAut W)} {U : Subgroup W} (hU : U ∈ s13IsoComps X) :
    StableUnder X U := by
  obtain ⟨U₀, -, -, hUeq⟩ := hU
  rw [hUeq]
  exact w16g_s13IsoSum_stable X U₀

theorem s13IsoComps_le_commSub (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) {U : Subgroup W} (hU : U ∈ s13IsoComps X) :
    U ≠ ⊥ ∧ U ≤ commSub ⊤ X := by
  obtain ⟨U₀, hIrr, hne, hUeq⟩ := hU
  have hle := w16g_le_s13IsoSum_self hIrr
  rw [hUeq]
  refine ⟨?_, ?_⟩
  · intro hbot
    have hU₀bot : U₀ = ⊥ := le_bot_iff.mp (hbot ▸ hle)
    exact hIrr.1.ne' hU₀bot
  · rw [s13IsoSum]
    refine iSup_le fun V₁ => iSup_le fun hV => ?_
    exact w16g_irr_le_commSub hW hX hIrr hne hV.1 hV.2

private theorem w16g_stableUnder_bot {X : Subgroup (MulAut W)} :
    StableUnder X (⊥ : Subgroup W) := by
  intro x hx u hu
  rw [Subgroup.mem_bot] at hu ⊢
  rw [hu, map_one]

private theorem w16g_secIsoOn_symm {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn X A ⊥ B ⊥) : SecIsoOn X B ⊥ A ⊥ := by
  classical
  obtain ⟨-, -, hSA, -, hSB, -, β, hβB, hβiff, hβsurj, hβeq⟩ := h
  have hβone : ∀ a : ↥A, β a = 1 ↔ (a : W) = 1 := fun a => by simpa using hβiff a
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥A) : W) = 1 := (hβone (a * b⁻¹)).mp h1
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have haux : ∀ b : ↥B, ∃ a : ↥A, β a = (b : W) := by
    intro b
    obtain ⟨a, ha⟩ := hβsurj (b : W) b.2
    exact ⟨a, mul_inv_eq_one.mp (by simpa using ha)⟩
  let aOf : ↥B → ↥A := fun b => Classical.choose (haux b)
  have haOf : ∀ b : ↥B, β (aOf b) = (b : W) := fun b => Classical.choose_spec (haux b)
  let γ : ↥B →* W :=
    { toFun := fun b => ((aOf b : ↥A) : W)
      map_one' := by
        have h1 : aOf 1 = 1 := by
          apply hβinj
          rw [haOf, map_one]
          rfl
        rw [h1]
        rfl
      map_mul' := by
        intro b b'
        have h1 : aOf (b * b') = aOf b * aOf b' := by
          apply hβinj
          rw [map_mul, haOf, haOf, haOf]
          rfl
        rw [h1]
        rfl }
  have hγ : ∀ b : ↥B, γ b = ((aOf b : ↥A) : W) := fun b => rfl
  refine ⟨bot_le, bot_le, hSB, w16g_stableUnder_bot, hSA, w16g_stableUnder_bot, γ, ?_, ?_,
    ?_, ?_⟩
  · intro b
    exact (aOf b).2
  · intro b
    rw [Subgroup.mem_bot, Subgroup.mem_bot, hγ]
    exact (hβone (aOf b)).symm.trans (by rw [haOf])
  · intro a ha
    refine ⟨⟨β ⟨a, ha⟩, hβB ⟨a, ha⟩⟩, ?_⟩
    have h1 : aOf ⟨β ⟨a, ha⟩, hβB ⟨a, ha⟩⟩ = ⟨a, ha⟩ := by
      apply hβinj
      rw [haOf]
    rw [hγ, h1, mul_inv_cancel]
    simp
  · intro x hx b b' hb'
    let a : ↥A := aOf b
    let a' : ↥A := aOf b'
    let a'' : ↥A := ⟨x (a : W), hSA x hx (a : W) a.2⟩
    have ha'' : (a'' : W) = x (a : W) := rfl
    have h1 : β a'' * (x (β a))⁻¹ ∈ ⊥ := hβeq x hx a a'' ha''
    have h2 : β a'' = x (β a) := mul_inv_eq_one.mp (by simpa using h1)
    have h3 : a'' = a' := by
      apply hβinj
      rw [h2, haOf b, haOf b']
      exact hb'.symm
    have h4 : ((aOf b' : ↥A) : W) = x ((aOf b : ↥A) : W) := by
      have h5 : (aOf b' : ↥A) = a'' := h3.symm
      rw [h5]
    have hgoal : γ b' * (x (γ b))⁻¹ = 1 := by
      rw [hγ b', hγ b, h4, mul_inv_cancel]
    simpa using hgoal

private theorem w16g_s13IsoSum_eq_of_secIsoOn {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : IsIrrOn X A ⊥) (hB : IsIrrOn X B ⊥) (h : SecIsoOn X A ⊥ B ⊥) :
    s13IsoSum X A = s13IsoSum X B := by
  apply le_antisymm
  · unfold s13IsoSum
    refine iSup_le fun V => iSup_le fun hV => ?_
    exact le_iSup₂ (f := fun V (_ : IsIrrOn X V ⊥ ∧ SecIsoOn X V ⊥ B ⊥) => V) V
      ⟨hV.1, secIsoOn_trans hV.2 h⟩
  · unfold s13IsoSum
    refine iSup_le fun V => iSup_le fun hV => ?_
    exact le_iSup₂ (f := fun V (_ : IsIrrOn X V ⊥ ∧ SecIsoOn X V ⊥ A ⊥) => V) V
      ⟨hV.1, secIsoOn_trans hV.2 (w16g_secIsoOn_symm h)⟩

private theorem w16g_secIsoOn_of_le_s13IsoSum (hW : ∀ w : W, w * w = 1)
    {X : Subgroup (MulAut W)} {U₀ V : Subgroup W} (hV : IsIrrOn X V ⊥)
    (hle : V ≤ s13IsoSum X U₀) : SecIsoOn X V ⊥ U₀ ⊥ := by
  classical
  let P : Subgroup W → Prop := fun V₁ => IsIrrOn X V₁ ⊥ ∧ SecIsoOn X V₁ ⊥ U₀ ⊥
  haveI : Finite (Subgroup W) := Finite.of_injective (fun S : Subgroup W => (S : Set W))
    SetLike.coe_injective
  have hsum : s13IsoSum X U₀ = ⨆ i : {V₁ : Subgroup W // P V₁}, (i.1 : Subgroup W) := by
    unfold s13IsoSum
    exact iSup_subtype' (p := P) (f := fun V₁ (_ : P V₁) => (V₁ : Subgroup W))
  have hle' : V ≤ ⊥ ⊔ ⨆ i : {V₁ : Subgroup W // P V₁}, (i.1 : Subgroup W) := by
    rw [bot_sup_eq, ← hsum]
    exact hle
  obtain ⟨i, hsec, -⟩ := exists_secIsoOn_of_le_iSup
    (hW := fun w => by rw [pow_two]; exact hW w) hV (fun i => i.2.1) hle'
  exact secIsoOn_trans hsec i.2.2

private theorem w16g_stableUnder_sSup {X : Subgroup (MulAut W)} {S : Set (Subgroup W)}
    (hS : ∀ U ∈ S, StableUnder X U) : StableUnder X (sSup S) := by
  rw [sSup_eq_iSup]
  exact stableUnder_iSup fun U => stableUnder_iSup fun hU => hS U hU

private theorem w16g_fixV_inf_commSub_eq_bot (hW : ∀ w : W, w * w = 1)
    {X : Subgroup (MulAut W)} (hX : Odd (Nat.card X)) : fixV X ⊓ commSub ⊤ X = ⊥ := by
  have h := (B1.coprime_decomp (fun w => by rw [pow_two]; exact hW w) hX (M := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _)).2
  rwa [top_inf_eq] at h

private theorem w16g_exists_stable_compl (hW : ∀ w : W, w * w = 1)
    {X : Subgroup (MulAut W)} (hX : Odd (Nat.card X)) {T M : Subgroup W}
    (hTM : T ≤ M) (hT : StableUnder X T) (hM : StableUnder X M) :
    ∃ T' : Subgroup W, StableUnder X T' ∧ T ⊓ T' = ⊥ ∧ T ⊔ T' = M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsElementaryAbelian 2 W :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        rw [pow_two]; exact hW x }
  letI : MulDistribMulAction ↥X W := MulDistribMulAction.compHom W X.subtype
  haveI : Fintype ↥X := Fintype.ofFinite ↥X
  have hcop : ¬ 2 ∣ Fintype.card ↥X := by
    rw [Fintype.card_eq_nat_card, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hX
  obtain ⟨T'', hcompl, hT''inv⟩ :=
    CFSG.RankThree.Coprime.exists_isCompl_invariant_subgroup_of_coprime (p := 2)
      (A := ↥X) (G := W) hcop T (fun a g hg => by
        change (a : MulAut W) g ∈ T
        exact hT (a : MulAut W) a.2 g hg)
  refine ⟨M ⊓ T'', ?_, ?_, ?_⟩
  · intro a ha g hg
    refine ⟨hM a ha g hg.1, ?_⟩
    change (a : MulAut W) g ∈ T''
    exact hT''inv ⟨a, ha⟩ g hg.2
  · rw [← inf_assoc, inf_eq_left.mpr hTM, hcompl.inf_eq_bot]
  · have h := sup_inf_assoc_of_le (y := T'') (x := T) (z := M) hTM
    rw [hcompl.sup_eq_top, top_inf_eq, inf_comm T'' M] at h
    exact h.symm

theorem s13IsoComps_sSupIndep (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) : sSupIndep (s13IsoComps X) := by
  classical
  intro U hU
  rw [disjoint_iff]
  by_contra hne
  set S : Subgroup W := sSup (s13IsoComps X \ {U}) with hSdef
  have hne' : U ⊓ S ≠ ⊥ := by simpa only [hSdef] using hne
  have hUstab : StableUnder X U := s13IsoComps_stable hU
  have hSstab : StableUnder X S := by
    rw [hSdef]
    exact w16g_stableUnder_sSup fun V hV => s13IsoComps_stable hV.1
  have hAstab : StableUnder X (U ⊓ S) := stableUnder_inf hUstab hSstab
  obtain ⟨V, hVA, hVirr⟩ := exists_isIrrOn_le (X := X) (N := ⊥) (A := U ⊓ S)
    (bot_lt_iff_ne_bot.mpr hne') hAstab w16g_stableUnder_bot
  have hVU : V ≤ U := hVA.trans inf_le_left
  obtain ⟨U₀, hIrr₀, hne₀, hUeq⟩ := hU
  have hVUsec : SecIsoOn X V ⊥ U₀ ⊥ :=
    w16g_secIsoOn_of_le_s13IsoSum hW hVirr (hUeq ▸ hVU)
  let ι := { W' : Subgroup W // IsIrrOn X W' ⊥ ∧ commSub W' X ≠ ⊥ ∧ s13IsoSum X W' ≠ U }
  have hSle : S ≤ ⨆ i : ι, (i.1 : Subgroup W) := by
    rw [hSdef]
    refine sSup_le fun U' hU' => ?_
    obtain ⟨U₀', hIrr₀', hne₀', hU'eq⟩ := hU'.1
    have hU'ne : s13IsoSum X U₀' ≠ U := by
      rw [← hU'eq]
      exact fun h => hU'.2 (by simpa using h)
    rw [hU'eq]
    unfold s13IsoSum
    refine iSup_le fun W' => iSup_le fun hW' => ?_
    refine le_iSup (fun i : ι => (i.1 : Subgroup W)) ⟨W', hW'.1, ?_, ?_⟩
    · intro h
      exact hne₀' (le_bot_iff.mp (secIsoOn_commSub_le hW'.2 le_rfl (le_of_eq h)))
    · rw [w16g_s13IsoSum_eq_of_secIsoOn hW'.1 hIrr₀' hW'.2]
      exact hU'ne
  have hVle : V ≤ ⊥ ⊔ ⨆ i : ι, (i.1 : Subgroup W) := by
    rw [bot_sup_eq]
    exact (hVA.trans inf_le_right).trans hSle
  obtain ⟨i, hiso, -⟩ := exists_secIsoOn_of_le_iSup
    (hW := fun w => by rw [pow_two]; exact hW w) (H := X) (C := ⊥) (A := V)
    (B := fun i : ι => (i.1 : Subgroup W)) hVirr (fun i => i.2.1) hVle
  have hsame1 : s13IsoSum X V = U := by
    rw [w16g_s13IsoSum_eq_of_secIsoOn hVirr hIrr₀ hVUsec, hUeq]
  have hsame2 : s13IsoSum X V = s13IsoSum X i.1 :=
    w16g_s13IsoSum_eq_of_secIsoOn hVirr i.2.1 hiso
  exact i.2.2.2 (hsame2 ▸ hsame1)

theorem iSup_s13IsoComps (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) : (⨆ U ∈ s13IsoComps X, U) = commSub ⊤ X := by
  classical
  apply le_antisymm
  · exact iSup_le fun U => iSup_le fun hU => (s13IsoComps_le_commSub hW hX hU).2
  · set T : Subgroup W := ⨆ U ∈ s13IsoComps X, U with hTdef
    set M : Subgroup W := commSub ⊤ X with hMdef
    have hTM : T ≤ M := by
      rw [hTdef, hMdef]
      exact iSup_le fun U => iSup_le fun hU => (s13IsoComps_le_commSub hW hX hU).2
    have hTstab : StableUnder X T := by
      rw [hTdef]
      exact stableUnder_iSup fun U => stableUnder_iSup fun hU => s13IsoComps_stable hU
    have hMstab : StableUnder X M := by
      rw [hMdef]
      exact stableUnder_commSub (fun h hh x hx => X.mul_mem (X.mul_mem hh hx) (X.inv_mem hh))
        (fun x hx m hm => Subgroup.mem_top m)
    obtain ⟨T', hT'stab, hT'inf, hT'sup⟩ := w16g_exists_stable_compl hW hX hTM hTstab hMstab
    have hT'leM : T' ≤ M := hT'sup ▸ le_sup_right
    have hT'bot : T' = ⊥ := by
      by_contra hne
      obtain ⟨V₁, hV₁T', hV₁irr⟩ := exists_isIrrOn_le (X := X) (N := ⊥) (A := T')
        (bot_lt_iff_ne_bot.mpr hne) hT'stab w16g_stableUnder_bot
      have hV₁M : V₁ ≤ M := hV₁T'.trans hT'leM
      have hfixbot : fixV X ⊓ M = ⊥ := by
        rw [hMdef]
        exact w16g_fixV_inf_commSub_eq_bot hW hX
      have hV₁fix : V₁ ⊓ fixV X = ⊥ := by
        apply le_bot_iff.mp
        calc V₁ ⊓ fixV X ≤ M ⊓ fixV X := inf_le_inf_right (fixV X) hV₁M
          _ = ⊥ := by rw [inf_comm, hfixbot]
      have hne₁ : commSub V₁ X ≠ ⊥ := by
        intro h
        have hle : V₁ ≤ fixV X := commSub_eq_bot_iff.mp h
        have hbot : V₁ ≤ (⊥ : Subgroup W) := by
          rw [← hV₁fix]
          exact le_inf le_rfl hle
        exact (not_le_of_gt hV₁irr.1) hbot
      have hV₁leT : V₁ ≤ T := by
        rw [hTdef]
        exact (w16g_le_s13IsoSum_self hV₁irr).trans
          (le_iSup₂ (f := fun U (_ : U ∈ s13IsoComps X) => U) (s13IsoSum X V₁)
            ⟨V₁, hV₁irr, hne₁, rfl⟩)
      have hbot : V₁ ≤ (⊥ : Subgroup W) := by
        rw [← hT'inf]
        exact le_inf hV₁leT hV₁T'
      exact (not_le_of_gt hV₁irr.1) hbot
    rw [← hT'sup, hT'bot, sup_bot_eq]

theorem s13KerOn_mem_hyperplanes (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {U : Subgroup W}
    (hU : U ∈ s13IsoComps X) :
    s13KerOn X U ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p X := by
  obtain ⟨U₀, hIrr₀, hne₀, hUeq⟩ := hU
  rw [hUeq, s13KerOn, w16g_inf_centSub_s13IsoSum_eq hIrr₀]
  exact ⟨inf_le_left, w16g_index_kerOn_eq_prime hW hp hp2 hX hIrr₀ hne₀⟩

theorem dParam_dvd_rk_s13IsoComps (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {U : Subgroup W}
    (hU : U ∈ s13IsoComps X) : dParam p ∣ rk ↥U := by
  obtain ⟨U₀, hIrr₀, hne₀, hUeq⟩ := hU
  have hnotfix : ¬ U₀ ≤ fixV X := fun h => hne₀ (commSub_eq_bot_iff.mpr h)
  have hex : ∃ u ∈ U₀, ∃ x ∈ X, x u ≠ u := by
    by_contra h
    apply hnotfix
    intro u hu
    rw [mem_fixV]
    intro x hx
    by_contra hne
    exact h ⟨u, hu, x, hx, hne⟩
  obtain ⟨u, hu, x, hxX, hxu⟩ := hex
  have hx1 : x ≠ 1 := fun h => hxu (by rw [h]; rfl)
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hX.2 x hxX)
  have hxorder : orderOf x = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf x) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hfix : s13IsoSum X U₀ ⊓ fixV (Subgroup.zpowers x) = ⊥ :=
    w16g_inf_fixV_zpowers_eq_bot hW hX.1 hIrr₀ hxX ⟨u, hu, hxu⟩
  rw [hUeq]
  refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.dParam_dvd_rk
    (fun w => by rw [pow_two]; exact hW w) hp hp2 hxorder ?_ hfix
  exact fun m hm => w16g_s13IsoSum_stable X U₀ x hxX m hm

end CFSG.LocalAnalysis.WeakClosure81
