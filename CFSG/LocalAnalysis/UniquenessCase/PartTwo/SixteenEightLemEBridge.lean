module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightLemETwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightLemECount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {T : Type*} [CommGroup T]

theorem s16f_relIndex_map (φ : MulAut T) (U W : Subgroup T) :
    ((U.map φ.toMonoidHom) ⊓ (W.map φ.toMonoidHom)).relIndex (W.map φ.toMonoidHom) =
      (U ⊓ W).relIndex W := by
  rw [← Subgroup.map_inf_eq U W φ.toMonoidHom φ.injective,
    Subgroup.relIndex_map_map_of_injective (U ⊓ W) W φ.injective]

end Generic

section Bridge

variable {G : Type} [Group G] [Finite G]

theorem s16f_mbar_faithful_mod (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) {φ : MulAut (Vtil V₀ V hV)}
    (hφ : φ ∈ Mbar D.M V₀ V hV)
    (hfix : ∀ v : Vtil V₀ V hV,
      φ v * v⁻¹ ∈ imgTil V₀ V hV (v1Sub D.M V₀ V hV L)) : φ = 1 := by
  obtain ⟨m, hm, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  have hcent : CentralizesMod (v1Sub D.M V₀ V hV L) V (m : G) := by
    intro v hv
    have hq := hfix (mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩))
    rw [actTil_mk, ← map_inv, ← map_mul] at hq
    obtain ⟨y, hy1, hyeq⟩ :=
      (mem_imgTil V₀ V hV (v1Sub D.M V₀ V hV L) _).1 hq
    have hmem := (mkTil_eq_iff V₀ V hV _ y).1 hyeq.symm
    have hzv : (actStab V₀ V hV m (IntMod.mk hV ⟨v, hv⟩) *
        (IntMod.mk hV ⟨v, hv⟩)⁻¹).val = m * v * m⁻¹ * v⁻¹ := by
      rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
      rfl
    rw [hzv] at hmem
    have hmem' : m * v * m⁻¹ * v⁻¹ * y.val⁻¹ ∈ v1Sub D.M V₀ V hV L :=
      s15_Infra_le_v1Sub D.M V₀ V hV L hmem
    have h2 : (m * v * m⁻¹ * v⁻¹ * y.val⁻¹) * y.val ∈ v1Sub D.M V₀ V hV L :=
      Subgroup.mul_mem _ hmem' hy1
    simpa [mul_assoc] using h2
  have key : ∀ X : Subgroup G, (m : G) ∈ normalizer (X : Set G) →
      ((m : G) ∈ F11.CTilde D.M X V ↔ CentralizesMod X V (m : G)) := by
    intro X hX
    unfold F11.CTilde
    simp only [Subgroup.mem_iInf]
    exact ⟨fun hc v hv => (hc v hv).2.2, fun hc v hv => ⟨hm, hX, hc v hv⟩⟩
  have hmem1 : (m : G) ∈ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V :=
    (key _ (s15_Infra_le_normalizer_v1Sub hset.hyp151.hyp125 hV hm)).2 hcent
  rw [fifteen_two_cent D h1217 hset.hyp151 hV] at hmem1
  have hcent0 : CentralizesMod V₀ V (m : G) :=
    (key V₀ (hset.hyp151.hyp125.pairFacts.le_normalizer₀ hm)).1 hmem1
  exact (actTil_eq_one_iff V₀ V hV m).2 hcent0

theorem s16f_mbar_map_v1 (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ Mbar D.M V₀ V hV) :
    (imgTil V₀ V hV (v1Sub D.M V₀ V hV L)).map φ.toMonoidHom =
      imgTil V₀ V hV (v1Sub D.M V₀ V hV L) := by
  obtain ⟨m, hm, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  have hnorm : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub hset.hyp151.hyp125 hV
  have hstep : ∀ (n : stabTil V₀ V), (n : G) ∈ D.M →
      ∀ q ∈ imgTil V₀ V hV (v1Sub D.M V₀ V hV L),
        actTil V₀ V hV n q ∈ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) := by
    intro n hn q hq
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil V₀ V hV (v1Sub D.M V₀ V hV L) q).1 hq
    rw [actTil_mk]
    exact (mem_imgTil V₀ V hV (v1Sub D.M V₀ V hV L) _).2
      ⟨actStab V₀ V hV n x, (Subgroup.mem_normalizer_iff.1 (hnorm hn) x.val).1 hx, rfl⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hy
    exact hstep m hm q hq
  · intro y hy
    have hm' : ((m⁻¹ : stabTil V₀ V) : G) ∈ D.M := by simpa using D.M.inv_mem hm
    have h := hstep m⁻¹ hm' y hy
    have hy' : actTil V₀ V hV m (actTil V₀ V hV m⁻¹ y) = y := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    exact ⟨actTil V₀ V hV m⁻¹ y, h, hy'⟩

theorem s16f_relIndex_wTil_inf_v1 (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) :
    (imgTil V₀ V hV (v1Sub D.M V₀ V hV L) ⊓ wTil V₀ V hV L).relIndex (wTil V₀ V hV L) =
      2 ^ gamma15 D.M V₀ V hV L := by
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hW2 : IsPGroup 2 (wSub V₀ V hV L) := hV.isPGroup.to_le hWV
  have hker : (mkTil V₀ V hV).ker = modNull V₀ V hV := QuotientGroup.ker_mk' _
  have hV0W : V₀ ≤ wSub V₀ V hV L := by
    intro g hg
    have hgV : g ∈ V := hset.hyp151.hyp125.pairFacts.le hg
    rw [show wSub V₀ V hV L = preTil V₀ V hV (wTil V₀ V hV L) from rfl,
      mem_preTil_iff_of_mem V₀ V hV _ hgV]
    have h1 : mkTil V₀ V hV (IntMod.mk hV ⟨g, hgV⟩) = 1 :=
      (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) (IntMod.mk hV ⟨g, hgV⟩)).2 hg
    rw [h1]
    exact Subgroup.one_mem _
  have hkerA : (mkTil V₀ V hV).ker ≤ intSub V hV (v1Sub D.M V₀ V hV L) := by
    rw [hker]
    intro x hx
    exact s15_Infra_le_v1Sub D.M V₀ V hV L hx
  have hkerB : (mkTil V₀ V hV).ker ≤ intSub V hV (wSub V₀ V hV L) := by
    rw [hker]
    intro x hx
    exact hV0W hx
  have hw : (intSub V hV (wSub V₀ V hV L)).map (mkTil V₀ V hV) = wTil V₀ V hV L :=
    imgTil_preTil V₀ V hV (wTil V₀ V hV L)
  have hA : imgTil V₀ V hV (v1Sub D.M V₀ V hV L) =
      (intSub V hV (v1Sub D.M V₀ V hV L)).map (mkTil V₀ V hV) := rfl
  rw [hA, ← hw, Subgroup.inf_relIndex_right, Subgroup.relIndex_map_map,
    sup_eq_left.2 hkerA, sup_eq_left.2 hkerB]
  have hAB : (intSub V hV (v1Sub D.M V₀ V hV L)).relIndex
      (intSub V hV (wSub V₀ V hV L)) =
      (v1Sub D.M V₀ V hV L).relIndex (wSub V₀ V hV L) :=
    Subgroup.relIndex_subgroupOf (H := v1Sub D.M V₀ V hV L)
      (K := wSub V₀ V hV L) (L := V) hWV
  rw [hAB, ← Subgroup.inf_relIndex_right, inf_comm, E3.relIndex_eq_two_pow hW2,
    s15_Six_mQuot_wSub_inf_v1Sub D hset.hyp151.hyp125 hV]

theorem s16f_pRank_mBar_lt_three (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 2) (hγ : gamma15 D.M V₀ V hV L ≤ 3) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) : CFSG.Open.pRank q (Mbar D.M V₀ V hV) < 3 := by
  obtain ⟨g, hg⟩ := s16f_pair_of_two D h1217 hV hset hL hs
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (Mbar D.M V₀ V hV)
  have hodd : Odd q := hq.odd_of_ne_two hq2
  have hst : ∀ e ∈ E, e ∈ stabSub (commSub ⊤ (lBar V₀ V hV L)) ∧
      e ∈ stabSub ((commSub ⊤ (lBar V₀ V hV L)).map g.toMonoidHom) := fun e he =>
    hg.stab_of_odd (hEM he) hodd (hE.2 e he)
  have h₁ : (imgTil V₀ V hV (v1Sub D.M V₀ V hV L) ⊓ commSub ⊤ (lBar V₀ V hV L)).relIndex
      (commSub ⊤ (lBar V₀ V hV L)) ≤ 8 := by
    rw [show commSub ⊤ (lBar V₀ V hV L) = wTil V₀ V hV L from rfl,
      s16f_relIndex_wTil_inf_v1 D hV hset]
    calc 2 ^ gamma15 D.M V₀ V hV L ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hγ
      _ = 8 := by norm_num
  have h₂ : ((imgTil V₀ V hV (v1Sub D.M V₀ V hV L)) ⊓
      (commSub ⊤ (lBar V₀ V hV L)).map g.toMonoidHom).relIndex
      ((commSub ⊤ (lBar V₀ V hV L)).map g.toMonoidHom) ≤ 8 := by
    rw [← s16f_mbar_map_v1 D hV hset hg.mem, s16f_relIndex_map]
    exact h₁
  have hcard := s16f_card_le_sq_of_faithful (s15_Infra_vtil_sq_eq_one V₀ V hV)
    (A := Mbar D.M V₀ V hV) (fun φ hφ => s16f_mbar_map_v1 D hV hset hφ)
    (fun φ hφ hfix => s16f_mbar_faithful_mod D h1217 hV hset hφ hfix) hg.sup h₁ h₂ hq hq2 hEM
    (fun e he => (hst e he).1) (fun e he => (hst e he).2) hEcard
  rw [hEcard] at hcard
  have := (Nat.pow_le_pow_iff_right hq.one_lt).1 hcard
  omega

end Bridge

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
