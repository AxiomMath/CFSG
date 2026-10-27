module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem f4f_le_stabSub {X : Subgroup (MulAut W)} {U : Subgroup W} (h : StableUnder X U) :
    X ≤ stabSub U := by
  intro x hx
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by simpa using h x⁻¹ (X.inv_mem hx) (x u) hu, fun hu => h x hx u hu⟩

omit [Finite W] in
theorem f4f_stableUnder_sup {A B : Subgroup (MulAut W)} {C : Subgroup W}
    (hA : StableUnder A C) (hB : StableUnder B C) : StableUnder (A ⊔ B) C := by
  intro x hx
  have hx' : x ∈ stabSub C := sup_le (f4f_le_stabSub hA) (f4f_le_stabSub hB) hx
  rw [mem_stabSub] at hx'
  intro u hu
  exact (hx' u).mpr hu

omit [Finite W] in
theorem f4f_stableUnder_bot (X : Subgroup (MulAut W)) : StableUnder X ⊥ := by
  intro x _ u hu
  rw [Subgroup.mem_bot] at hu ⊢
  rw [hu, map_one]

omit [Finite W] in
theorem f4f_inf_fixV_eq_bot {A B : Subgroup (MulAut W)}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {R : Subgroup W}
    (hirr : IsIrrOn (A ⊔ B) R ⊥) (hnt : ¬ ∀ a ∈ A, ∀ r ∈ R, a r = r) :
    R ⊓ fixV A = ⊥ := by
  have hAfix : StableUnder A (fixV A) :=
    stableUnder_fixV (fun y hy h hh => A.mul_mem (A.mul_mem hy hh) (A.inv_mem hy))
  have hBfix : StableUnder B (fixV A) :=
    stableUnder_fixV (fun y hy h hh => by
      have h' : y * h * y⁻¹ = h := by rw [← hAB h hh y hy]; group
      rw [h']; exact hh)
  have hAR : StableUnder A R :=
    fun a ha r hr => hirr.2.1 a (Subgroup.mem_sup_left ha) r hr
  have hBR : StableUnder B R :=
    fun b hb r hr => hirr.2.1 b (Subgroup.mem_sup_right hb) r hr
  have hCstab : StableUnder (A ⊔ B) (R ⊓ fixV A) :=
    f4f_stableUnder_sup (stableUnder_inf hAR hAfix) (stableUnder_inf hBR hBfix)
  rcases hirr.2.2.2 (R ⊓ fixV A) hCstab bot_le inf_le_left with h | h
  · exact h
  · exfalso
    apply hnt
    intro a ha r hr
    have hr' : r ∈ R ⊓ fixV A := by rw [h]; exact hr
    exact (mem_fixV.mp hr'.2) a ha

omit [Finite W] in
theorem f4f_map_stable {K K' : Subgroup (MulAut W)} {M : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) (hM : StableUnder K M)
    {k : MulAut W} (hk : k ∈ K') : StableUnder K (M.map k.toMonoidHom) := by
  intro a ha u hu
  rw [Subgroup.mem_map] at hu ⊢
  obtain ⟨v, hv, rfl⟩ := hu
  refine ⟨a v, hM a ha v hv, ?_⟩
  change k (a v) = a (k v)
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, hKK' a ha k hk]

omit [Finite W] in
theorem f4f_map_le_of_stable {K' : Subgroup (MulAut W)} {M R : Subgroup W}
    (hK'R : StableUnder K' R) (hMR : M ≤ R) {k : MulAut W} (hk : k ∈ K') :
    M.map k.toMonoidHom ≤ R := by
  intro u hu
  rw [Subgroup.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  exact hK'R k hk v (hMR hv)

omit [Finite W] in
theorem f4f_map_inv_map (k : MulAut W) (M : Subgroup W) :
    (M.map k.toMonoidHom).map (k⁻¹).toMonoidHom = M := by
  rw [Subgroup.map_map]
  have hcomp : (k⁻¹).toMonoidHom.comp k.toMonoidHom = MonoidHom.id W := by
    ext x
    simp
  rw [hcomp, Subgroup.map_id]

omit [Finite W] in
theorem f4f_map_inv_map' (k : MulAut W) (M : Subgroup W) :
    (M.map (k⁻¹).toMonoidHom).map k.toMonoidHom = M := by
  simpa using f4f_map_inv_map (k⁻¹) M

omit [Finite W] in
theorem f4f_rk_map (k : MulAut W) (M : Subgroup W) :
    rk ↥(M.map k.toMonoidHom) = rk ↥M := by
  unfold rk
  rw [Subgroup.card_map_of_injective k.injective]

omit [Finite W] in
theorem f4f_map_irr {K K' : Subgroup (MulAut W)} {M : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) (hirr : IsIrrOn K M ⊥)
    {k : MulAut W} (hk : k ∈ K') : IsIrrOn K (M.map k.toMonoidHom) ⊥ := by
  have hne : M.map k.toMonoidHom ≠ ⊥ := by
    intro hbot
    have hMbot : M = ⊥ := by
      have h := congrArg (Subgroup.map (k⁻¹).toMonoidHom) hbot
      rw [Subgroup.map_map, Subgroup.map_bot] at h
      have hcomp : (k⁻¹).toMonoidHom.comp k.toMonoidHom = MonoidHom.id W := by
        ext x
        simp
      rwa [hcomp, Subgroup.map_id] at h
    exact hirr.1.ne' hMbot
  refine ⟨bot_lt_iff_ne_bot.mpr hne, f4f_map_stable hKK' hirr.2.1 hk,
    f4f_stableUnder_bot K, ?_⟩
  intro J hJstab _ hJle
  have hJ'stab : StableUnder K (J.map (k⁻¹).toMonoidHom) :=
    f4f_map_stable hKK' hJstab (K'.inv_mem hk)
  have hJ'le : J.map (k⁻¹).toMonoidHom ≤ M := by
    calc J.map (k⁻¹).toMonoidHom ≤ (M.map k.toMonoidHom).map (k⁻¹).toMonoidHom :=
          Subgroup.map_mono hJle
      _ = M := f4f_map_inv_map k M
  rcases hirr.2.2.2 (J.map (k⁻¹).toMonoidHom) hJ'stab bot_le hJ'le with h | h
  · left
    have h1 : J = (J.map (k⁻¹).toMonoidHom).map k.toMonoidHom := (f4f_map_inv_map' k J).symm
    rw [h1, h, Subgroup.map_bot]
  · right
    have h1 : J = (J.map (k⁻¹).toMonoidHom).map k.toMonoidHom := (f4f_map_inv_map' k J).symm
    rw [h1, h]

omit [Finite W] in
theorem f4f_iSup_translates_eq {K K' : Subgroup (MulAut W)}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) {R M : Subgroup W}
    (hirr : IsIrrOn (K ⊔ K') R ⊥) (hMR : M ≤ R) (hMstab : StableUnder K M) (hMne : M ≠ ⊥) :
    (⨆ k : K', M.map (k : MulAut W).toMonoidHom) = R := by
  have hKR : StableUnder K R :=
    fun a ha r hr => hirr.2.1 a (Subgroup.mem_sup_left ha) r hr
  have hK'R : StableUnder K' R :=
    fun b hb r hr => hirr.2.1 b (Subgroup.mem_sup_right hb) r hr
  have hle : (⨆ k : K', M.map (k : MulAut W).toMonoidHom) ≤ R :=
    iSup_le fun k => f4f_map_le_of_stable hK'R hMR k.2
  have hKstab : StableUnder K (⨆ k : K', M.map (k : MulAut W).toMonoidHom) :=
    stableUnder_iSup fun k => f4f_map_stable hKK' hMstab k.2
  have hK'stab : StableUnder K' (⨆ k : K', M.map (k : MulAut W).toMonoidHom) := by
    intro x hx u hu
    refine Subgroup.iSup_induction (fun k : K' => M.map (k : MulAut W).toMonoidHom)
      (C := fun y => x y ∈ ⨆ k : K', M.map (k : MulAut W).toMonoidHom) hu ?_ ?_ ?_
    · intro k y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      refine Subgroup.mem_iSup_of_mem
        (⟨(x : MulAut W) * (k : MulAut W), K'.mul_mem hx k.2⟩ : K') ?_
      rw [Subgroup.mem_map]
      exact ⟨v, hv, rfl⟩
    · rw [map_one]; exact Subgroup.one_mem _
    · intro y z hy hz; rw [map_mul]; exact Subgroup.mul_mem _ hy hz
  have hStab : StableUnder (K ⊔ K') (⨆ k : K', M.map (k : MulAut W).toMonoidHom) :=
    f4f_stableUnder_sup hKstab hK'stab
  have hMone : M.map (((1 : K') : MulAut W)).toMonoidHom = M := by
    rw [show ((1 : K') : MulAut W) = 1 from rfl]
    change M.map (MonoidHom.id W) = M
    rw [Subgroup.map_id]
  have hSne : (⨆ k : K', M.map (k : MulAut W).toMonoidHom) ≠ ⊥ := by
    intro hbot
    have hMle : M ≤ (⨆ k : K', M.map (k : MulAut W).toMonoidHom) := by
      have h1 : M.map (((1 : K') : MulAut W)).toMonoidHom ≤
          (⨆ k : K', M.map (k : MulAut W).toMonoidHom) :=
        le_iSup (fun k : K' => M.map (k : MulAut W).toMonoidHom) 1
      rwa [hMone] at h1
    exact hMne (le_bot_iff.mp (hbot ▸ hMle))
  rcases hirr.2.2.2 (⨆ k : K', M.map (k : MulAut W).toMonoidHom) hStab bot_le hle with h | h
  · exact absurd h hSne
  · exact h

theorem f4f_exists_minimal {K : Subgroup (MulAut W)} {R : Subgroup W}
    (hRne : R ≠ ⊥) (hKR : StableUnder K R) :
    ∃ M : Subgroup W, M ≤ R ∧ StableUnder K M ∧ M ≠ ⊥ ∧ IsIrrOn K M ⊥ ∧
      (∀ N, N ≤ R → StableUnder K N → N ≠ ⊥ → N ≤ M → N = M) := by
  let cands : Set (Subgroup W) := {M | M ≤ R ∧ StableUnder K M ∧ M ≠ ⊥}
  have hRmem : R ∈ cands := ⟨le_rfl, hKR, hRne⟩
  obtain ⟨M, hMmem, hMmin⟩ := (wellFounded_lt (α := Subgroup W)).has_min cands ⟨R, hRmem⟩
  obtain ⟨hMR, hMstab, hMne⟩ := hMmem
  have hmin' : ∀ N, N ≤ R → StableUnder K N → N ≠ ⊥ → N ≤ M → N = M := by
    intro N hNR hNstab hNne hNM
    by_contra hne
    exact hMmin N ⟨hNR, hNstab, hNne⟩ (lt_of_le_of_ne hNM hne)
  refine ⟨M, hMR, hMstab, hMne, ?_, hmin'⟩
  refine ⟨bot_lt_iff_ne_bot.mpr hMne, hMstab, f4f_stableUnder_bot K, ?_⟩
  intro J hJstab _ hJle
  rcases eq_or_ne J ⊥ with rfl | hJne
  · exact Or.inl rfl
  · exact Or.inr (hmin' J (le_trans hJle hMR) hJstab hJne hJle)

omit [Finite W] in
theorem f4f_card_sec_bot (M : Subgroup W) : Nat.card (Sec M ⊥) = Nat.card ↥M := by
  change Nat.card (↥M ⧸ (⊥ : Subgroup W).subgroupOf M) = Nat.card ↥M
  rw [Subgroup.bot_subgroupOf]
  exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥M)).toEquiv

theorem f4f_inf_eq_bot_of_irr {K : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : IsIrrOn K A ⊥) (hB : IsIrrOn K B ⊥) (hne : A ≠ B)
    (hcard : Nat.card ↥A = Nat.card ↥B) : A ⊓ B = ⊥ := by
  rcases hA.2.2.2 (A ⊓ B) (stableUnder_inf hA.2.1 hB.2.1) bot_le inf_le_left with h | h
  · exact h
  · exfalso
    exact hne (eq_of_le_of_card_ge (h ▸ inf_le_right) (le_of_eq hcard.symm))

theorem f4f_rk_sup_of_inf_bot {A B : Subgroup W} (h : A ⊓ B = ⊥) :
    rk ↥(A ⊔ B) = rk ↥A + rk ↥B := by
  have h1 := rk_sup_add_rk_inf A B
  rw [h, rk_bot, add_zero] at h1
  exact h1

theorem f4f_indep_of (hW : ∀ w : W, w ^ 2 = 1) {A B C R : Subgroup W}
    (_hAB : A ⊓ B = ⊥) (_hAC : A ⊓ C = ⊥) (hBC : B ⊓ C = ⊥)
    (hrkA : rk ↥A = 3) (hrkB : rk ↥B = 3) (hrkC : rk ↥C = 3)
    (hsup : A ⊔ B ⊔ C = R) (hrkR : rk ↥R = 9) : A ⊓ (B ⊔ C) ≤ ⊥ := by
  have hBCsup : rk ↥(B ⊔ C) = 6 := by
    rw [f4f_rk_sup_of_inf_bot hBC, hrkB, hrkC]
  have hsup' : A ⊔ (B ⊔ C) = R := by rw [← sup_assoc]; exact hsup
  have h1 := rk_sup_add_rk_inf A (B ⊔ C)
  rw [hsup', hrkA, hBCsup, hrkR] at h1
  have hzero : rk ↥(A ⊓ (B ⊔ C)) = 0 := by omega
  exact le_bot_iff.mpr ((rk_eq_zero_iff hW).mp hzero)

omit [Finite W] in
theorem f4f_map_nt {K K' : Subgroup (MulAut W)} {M : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) {k : MulAut W} (hk : k ∈ K')
    (hnt : ∃ a ∈ K, ∃ u ∈ M, a u * u⁻¹ ∉ (⊥ : Subgroup W)) :
    ∃ a ∈ K, ∃ u ∈ M.map k.toMonoidHom, a u * u⁻¹ ∉ (⊥ : Subgroup W) := by
  obtain ⟨a, ha, u, hu, hntu⟩ := hnt
  have hu_ne : a u ≠ u := by
    intro h
    exact hntu (by rw [h, mul_inv_cancel]; exact Subgroup.one_mem _)
  refine ⟨a, ha, k u, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, ?_⟩
  intro hmem
  apply hu_ne
  have h1 : a (k u) = k u := mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
  have hki : (k⁻¹ : MulAut W) * a = a * k⁻¹ := by
    have h' : a * k = k * a := hKK' a ha k hk
    calc (k⁻¹ : MulAut W) * a = k⁻¹ * (a * k) * k⁻¹ := by group
      _ = k⁻¹ * (k * a) * k⁻¹ := by rw [h']
      _ = a * k⁻¹ := by group
  have h3 : k⁻¹ (a (k u)) = a (k⁻¹ (k u)) := by
    have hh := congrArg (fun f : MulAut W => f (k u)) hki
    simpa [MulAut.mul_apply] using hh
  calc a u = a (k⁻¹ (k u)) := by rw [MulAut.inv_apply_self W k u]
    _ = k⁻¹ (a (k u)) := h3.symm
    _ = k⁻¹ (k u) := congrArg (fun x : W => (k⁻¹ : MulAut W) x) h1
    _ = u := MulAut.inv_apply_self W k u

end CFSG.LocalAnalysis.WeakClosure81
