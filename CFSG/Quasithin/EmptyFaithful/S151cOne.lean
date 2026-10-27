module

public import CFSG.Quasithin.EmptyFaithful.S151cShape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section One151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc J : Subgroup (MulAut V)} {r : ℚ}

structure OneBlock151c (X Tb Xc J : Subgroup (MulAut V)) (r : ℚ) : Prop where
  setting : Setting151c X Tb Xc
  jdef : J = Jhat X
  qhat : qhatOf X = (r : WithTop ℚ)
  le_two : r ≤ 2
  hyp : D217Hyp J r
  normal : NormalIn X J
  fix_bot : fixV J = ⊥

namespace OneBlock151c

theorem le (B : OneBlock151c X Tb Xc J r) : J ≤ X := B.jdef ▸ Jhat_le X

theorem sq (B : OneBlock151c X Tb Xc J r) : ∀ v : V, v ^ 2 = 1 := B.setting.sq

theorem syl (B : OneBlock151c X Tb Xc J r) : Tb ∈ sylow2Of X := B.setting.syl

theorem tb_le (B : OneBlock151c X Tb Xc J r) : Tb ≤ X := B.setting.syl.1

theorem commV_top (B : OneBlock151c X Tb Xc J r) : commV J = ⊤ := by
  have h1 : commV (fittingOf J) ≤ commV J := commV_mono216 (fittingOf_le J)
  rw [eq_top_iff]
  exact (B.hyp.comm_fitting ▸ h1 : (⊤ : Subgroup V) ≤ commV J)

theorem d217 (B : OneBlock151c X Tb Xc J r) : QhatStar J = sylow2Of J ∧ D217Concl J r :=
  CFSG.Quasithin.d217 V B.sq J r B.hyp.qhat B.hyp.le_two B.hyp.jhat B.hyp.comm_fitting
    B.hyp.indecomposable B.hyp.fstar B.hyp.o2 B.hyp.sqtk

theorem offender (B : OneBlock151c X Tb Xc J r) {c : MulAut V} (hcX : c ∈ X) (hc1 : c ≠ 1)
    (hc2 : c ^ 2 = 1) (hrk : (rk (commV (Subgroup.zpowers c)) : ℚ) ≤ r) : c ∈ J := by
  rw [B.jdef]
  exact involution_mem_Jhat B.sq B.qhat B.le_two hcX hc1 hc2 hrk

theorem normalizes (B : OneBlock151c X Tb Xc J r) : ∀ x ∈ X, ∀ j ∈ J, x * j * x⁻¹ ∈ J := B.normal

end OneBlock151c

open Classical in
theorem oneBlock_of_single (h : Setting151c X Tb Xc) (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) (hLu : ∀ L' ∈ I, L' = L)
    (hfix : fixV (Jhat X) = ⊥) : OneBlock151c X Tb Xc (Jhat X) r := by
  have hJL : Jhat X = L := by
    apply le_antisymm
    · rw [hI.sup_eq]
      exact iSup₂_le fun L' hL' => (hLu L' hL').le
    · exact block_le_J hI hL
  have hLnorm : ∀ x ∈ X, conjBy x L = L := fun x hx =>
    hLu _ (block_conj_mem h hr hr2 hI hL hx)
  have hLn : NormalIn X (Jhat X) := fun x hx k hk => Jhat_conj_mem hx hk
  have hcop := commV_fitting_sup_fixV h.sq h.o2
  have hFJ : fittingOf (Jhat X) ≤ Jhat X := fittingOf_le _
  have hfix_eq : fixV (Jhat X) = fixV (fittingOf (Jhat X)) :=
    le_antisymm (fun c hc f hf => hc f (hFJ hf)) (fun c hc j hj => h.central c hc j hj)
  have hC0 : fixV (fittingOf (Jhat X)) = ⊥ := by rw [← hfix_eq]; exact hfix
  have hcomm : commV (fittingOf (Jhat X)) = ⊤ := by
    have := hcop.1
    rwa [hC0, sup_bot_eq] at this
  have hsolv := isSolvable_Jhat h.solv
  refine ⟨h, rfl, hr, hr2, ⟨(Jhat_compat hr hr2).1, hr2, ((Jhat_compat hr hr2).2).symm, hcomm, ?_,
    centralizer_fittingOf_le_of_solvable hsolv, pCoreOf_Jhat_eq_bot h.o2,
    isQuotientOfSQTK_of_le (Jhat_le X) h.sqtk⟩, hLn, hfix⟩
  have := hI.indec L hL
  rwa [← hJL] at this

theorem Setting151c.uStar_self (h : Setting151c X Tb Xc) : UStar X Tb Xc := by
  refine ⟨h.syl.2.1, ?_, fun B hB hBinv hle => h.star B hB hBinv hle⟩
  intro z hz hz1 ψ hψ hψz
  have hZ1 : Subgroup.zpowers z ≤ fixV Tb := Subgroup.zpowers_le.mpr hz
  have hZ1ne : Subgroup.zpowers z ≠ ⊥ := fun e => hz1 (Subgroup.zpowers_eq_bot.mp e)
  refine h.hU _ hZ1 hZ1ne ⟨hψ, ?_⟩
  intro u hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [map_zpow, hψz]

open Classical in
theorem oneBlock_not_shape6 (B : OneBlock151c X Tb Xc J r) (h6 : Shape6 J r) : False := by
  have hH := B.hyp
  have hsyl := B.d217.1
  obtain ⟨hE, hF27, ⟨A', hA'X, hA'2, hA'4, hXeq⟩, -, -⟩ := h6
  have hnorm : A' ≤ Subgroup.normalizer (fittingOf J : Set (MulAut V)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_fittingOf (hA'X ha) hy, fun hy => ?_⟩
    have := conj_mem_fittingOf (Subgroup.inv_mem _ (hA'X ha)) hy
    simpa [mul_assoc] using this
  have hinf : fittingOf J ⊓ A' = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h3 : x ^ 3 = 1 := hE.2 x hx.1
    have h2 : x ^ 2 = 1 := hA'2.2 x hx.2
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  have hcard := card_sup_of_normalizes hnorm hinf
  rw [← hXeq, hF27, hA'4] at hcard
  have hA'mem : A' ∈ QhatStar J := by
    rw [hsyl]
    exact mem_sylow2Of_of_card hA'X hA'2.isPGroup (m := 27) ⟨13, rfl⟩ (by rw [hcard, hA'4])
  have hrk : 1 < rk A' := by
    have h1 := card_eq_two_pow_of_isPGroup hA'2.isPGroup
    rw [hA'4] at h1
    have h2 : 2 ^ rk A' = 2 ^ 2 := by omega
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  obtain ⟨-, hFp, -, -, -, hW, hcases⟩ := d217_noncyclic_structure B.sq hH hA'mem hrk
  rcases hcases with ⟨Pi, d, hrg, hc9⟩ | ⟨Pi, d, hrg, hc27⟩
  · omega
  · have hfd : FDec J Pi :=
      { mem := fun i => ⟨by rw [hFp]; exact d.le_P i, by simpa using d.card_eq i,
          by simpa using d.rk_eq i⟩
        vindep := d.vindep
        vsup := iSup_commV_eq_top B.sq d hW
        triv := d.triv }
    have hperm : ∀ τ ∈ Tb, ∀ i, ∃ j, conjBy τ (Pi i) = Pi j :=
      perm_of_range_eq_Pfam hrg (fun τ hτ y hy => B.normal τ (B.tb_le hτ) y hy)
    have hPiX : ∀ i, Pi i ≤ X := fun i =>
      (d.le_P i).trans ((pCoreOf_le 3 _).trans B.le)
    exact hfd.false_of_three B.sq B.setting.uStar_self hPiX hperm

end One151c

end CFSG.Quasithin
