module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiNe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Clifford

variable {W : Type} [CommGroup W] [Finite W]

private theorem s15_semiBot_isIrrOn_map_rel {X N : Subgroup (MulAut W)}
    (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) {C J : Subgroup W} (hC : StableUnder X C)
    {x : MulAut W} (hx : x ∈ X) (hJ : IsIrrOn N J C) :
    IsIrrOn N (J.map x.toMonoidHom) C := by
  have hxinv : x⁻¹ ∈ X := X.inv_mem hx
  have hCmap : C.map x.toMonoidHom = C := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hC x hx c hc
    · intro c hc
      exact ⟨x⁻¹ c, hC x⁻¹ hxinv c hc, by simp [MulAut.mul_apply, MulAut.inv_apply]⟩
  have hlt : C < J.map x.toMonoidHom := by
    rw [← hCmap]
    exact (Subgroup.map_lt_map_iff_of_injective x.injective).2 hJ.1
  refine ⟨hlt, ?_, hJ.2.2.1, ?_⟩
  · rintro n hn y ⟨j, hj, rfl⟩
    exact ⟨(x⁻¹ * n * x) j, hJ.2.1 _ (hN x⁻¹ hxinv n hn) j hj,
      by simp [MulAut.mul_apply, MulAut.inv_apply]⟩
  · intro K hKstab hCK hKJ
    have hKcomap : StableUnder N (K.comap x.toMonoidHom) := by
      intro n hn y hy
      have hmem : (x * n * x⁻¹) (x y) ∈ K := hKstab _ (hN x hx n hn) _ hy
      have heq : x (n y) = (x * n * x⁻¹) (x y) := by
        simp [MulAut.mul_apply, MulAut.inv_apply]
      show x (n y) ∈ K
      rw [heq]
      exact hmem
    have hKC : C ≤ K.comap x.toMonoidHom := by
      intro c hc
      have hxc : x c ∈ C := by
        rw [← hCmap]
        exact ⟨c, hc, rfl⟩
      exact hCK hxc
    have hInter : StableUnder N (K.comap x.toMonoidHom ⊓ J) := fun n hn u hu =>
      ⟨hKcomap n hn u hu.1, hJ.2.1 n hn u hu.2⟩
    have hCinter : C ≤ K.comap x.toMonoidHom ⊓ J := fun c hc => ⟨hKC hc, hJ.1.le hc⟩
    rcases hJ.2.2.2 (K.comap x.toMonoidHom ⊓ J) hInter hCinter inf_le_right with h | h
    · left
      apply le_antisymm _ hCK
      intro y hy
      obtain ⟨j, hjJ, hjx⟩ := Subgroup.mem_map.1 (hKJ hy)
      have hjx' : x j = y := by simpa using hjx
      have hjK : j ∈ K.comap x.toMonoidHom := Subgroup.mem_comap.2 (hjx' ▸ hy)
      have hjC : j ∈ C := by rw [← h]; exact ⟨hjK, hjJ⟩
      have hxC : x j ∈ C := by
        rw [← hCmap]
        exact ⟨j, hjC, rfl⟩
      rwa [hjx'] at hxC
    · right
      have hJK : J ≤ K.comap x.toMonoidHom := by rw [← h]; exact inf_le_left
      apply le_antisymm hKJ
      rintro y ⟨j, hj, rfl⟩
      exact hJK hj

theorem s15_semiBot_sSup_irr_le_eq_rel {X N : Subgroup (MulAut W)} (hNX : N ≤ X)
    (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) {I C : Subgroup W} (hI : IsIrrOn X I C) :
    sSup {J : Subgroup W | IsIrrOn N J C ∧ J ≤ I} = I := by
  classical
  set F : Set (Subgroup W) := {J : Subgroup W | IsIrrOn N J C ∧ J ≤ I} with hF
  change sSup F = I
  have hle : sSup F ≤ I := sSup_le fun J hJ => hJ.2
  let S : Set (Subgroup W) := {J : Subgroup W | C < J ∧ J ≤ I ∧ StableUnder N J}
  have hSfin : S.Finite := Set.toFinite S
  obtain ⟨J0, hJ0S, hJ0min⟩ := Set.exists_min_image S (fun J => Nat.card J) hSfin
    ⟨I, hI.1, le_rfl, fun n hn u hu => hI.2.1 n (hNX hn) u hu⟩
  have hJ0F : J0 ∈ F := by
    refine ⟨⟨hJ0S.1, hJ0S.2.2, ?_, ?_⟩, hJ0S.2.1⟩
    · intro n hn c hc
      exact hI.2.2.1 n (hNX hn) c hc
    · intro K hKstab hCK hKJ
      by_cases hKC : K = C
      · exact Or.inl hKC
      · right
        have hKS : K ∈ S :=
          ⟨lt_of_le_of_ne hCK (Ne.symm hKC), hKJ.trans hJ0S.2.1, hKstab⟩
        exact Subgroup.eq_of_le_of_card_ge hKJ (hJ0min K hKS)
  have hstab : StableUnder X (sSup F) := by
    intro x hx u hu
    rw [sSup_eq_iSup'] at hu ⊢
    refine Subgroup.iSup_induction (fun J : F => (J : Subgroup W))
      (C := fun z => x z ∈ ⨆ J : F, (J : Subgroup W)) hu ?_ ?_ ?_
    · intro J uJ huJ
      have hJ' : J.1.map x.toMonoidHom ∈ F := by
        refine ⟨s15_semiBot_isIrrOn_map_rel hN hI.2.2.1 hx J.2.1, ?_⟩
        rintro _ ⟨j, hj, rfl⟩
        exact hI.2.1 x hx j (J.2.2 hj)
      exact Subgroup.mem_iSup_of_mem (⟨J.1.map x.toMonoidHom, hJ'⟩ : F)
        (show x uJ ∈ J.1.map x.toMonoidHom from ⟨uJ, huJ, rfl⟩)
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro a b ha hb
      rw [map_mul]
      exact mul_mem ha hb
  have hC_le : C ≤ sSup F := hJ0S.1.le.trans (le_sSup hJ0F)
  rcases hI.2.2.2 (sSup F) hstab hC_le hle with h | h
  · exact absurd (h ▸ le_sSup hJ0F) (not_le_of_gt hJ0S.1)
  · exact h

end Clifford

section Quotient

variable {W W' : Type} [CommGroup W] [CommGroup W'] [Finite W] [Finite W']

theorem s15_semiBot_isIrrOn_map_of_ker (κ : W →* W') {N : Subgroup (MulAut W)}
    {N' : Subgroup (MulAut W')} (hNN' : ∀ n ∈ N, ∃ n' ∈ N', ∀ w, κ (n w) = n' (κ w))
    (hN'N : ∀ n' ∈ N', ∃ n ∈ N, ∀ w, κ (n w) = n' (κ w)) {J C : Subgroup W}
    (hJ : IsIrrOn N J C) (hC : C ≤ κ.ker) (hJker : J ⊓ κ.ker ≤ C) :
    IsIrrOn N' (J.map κ) ⊥ := by
  have hne : J.map κ ≠ ⊥ := by
    intro hbot
    have hJker' : J ≤ κ.ker := (Subgroup.map_eq_bot_iff (H := J) (f := κ)).1 hbot
    have hJC : J ≤ C := fun j hj => hJker ⟨hj, hJker' hj⟩
    exact (not_le_of_gt hJ.1) hJC
  refine ⟨bot_lt_iff_ne_bot.2 hne, ?_, ?_, ?_⟩
  · rintro n' hn' y hy
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨n, hn, hnw⟩ := hN'N n' hn'
    exact Subgroup.mem_map.2 ⟨n j, hJ.2.1 n hn j hj, hnw j⟩
  · intro n' _ y hy
    rw [Subgroup.mem_bot] at hy ⊢
    rw [hy, map_one]
  · intro K hKstab hCK hKJ
    have hKcomap : StableUnder N (K.comap κ) := by
      intro n hn y hy
      obtain ⟨n', hn', hnw⟩ := hNN' n hn
      rw [Subgroup.mem_comap] at hy ⊢
      rw [hnw]
      exact hKstab n' hn' (κ y) hy
    have hInter : StableUnder N (K.comap κ ⊓ J) := fun n hn u hu =>
      ⟨hKcomap n hn u hu.1, hJ.2.1 n hn u hu.2⟩
    have hCinter : C ≤ K.comap κ ⊓ J := by
      intro c hc
      refine ⟨Subgroup.mem_comap.2 ?_, hJ.1.le hc⟩
      rw [MonoidHom.mem_ker.1 (hC hc)]
      exact Subgroup.one_mem _
    rcases hJ.2.2.2 (K.comap κ ⊓ J) hInter hCinter inf_le_right with h | h
    · left
      apply le_antisymm _ bot_le
      intro y hy
      obtain ⟨j, hjJ, hjx⟩ := Subgroup.mem_map.1 (hKJ hy)
      have hjx' : κ j = y := by simpa using hjx
      have hjK : j ∈ K.comap κ := Subgroup.mem_comap.2 (hjx' ▸ hy)
      have hjC : j ∈ C := by rw [← h]; exact ⟨hjK, hjJ⟩
      rw [Subgroup.mem_bot, ← hjx']
      exact MonoidHom.mem_ker.1 (hC hjC)
    · right
      have hJK : J ≤ K.comap κ := by rw [← h]; exact inf_le_left
      apply le_antisymm hKJ
      rintro y ⟨j, hj, rfl⟩
      exact hJK hj

theorem s15_semiBot_sSup_irr_of_irrSet (κ : W →* W') (hκ : Function.Surjective κ)
    {X N : Subgroup (MulAut W)} {N' : Subgroup (MulAut W')} (hNX : N ≤ X)
    (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hNN' : ∀ n ∈ N, ∃ n' ∈ N', ∀ w, κ (n w) = n' (κ w))
    (hN'N : ∀ n' ∈ N', ∃ n ∈ N, ∀ w, κ (n w) = n' (κ w)) (hker : κ.ker = fixV X)
    (hgen : ⨆ I ∈ irrSet X, I = ⊤) :
    sSup {J : Subgroup W' | IsIrrOn N' J ⊥} = ⊤ := by
  set S : Set (Subgroup W') := {J : Subgroup W' | IsIrrOn N' J ⊥} with hS
  change sSup S = ⊤
  refine le_antisymm le_top ?_
  have hmap : (⊤ : Subgroup W).map κ = (⊤ : Subgroup W') :=
    Subgroup.map_top_of_surjective κ hκ
  rw [← hmap, ← hgen]
  rw [Subgroup.map_iSup]
  refine iSup_le fun I => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hI => ?_
  have hIirr : IsIrrOn X I (I ⊓ fixV X) := hI.2
  have hrel := s15_semiBot_sSup_irr_le_eq_rel hNX hN hIirr
  rw [← hrel]
  rw [sSup_eq_iSup', Subgroup.map_iSup]
  refine iSup_le fun J => ?_
  refine le_sSup ?_
  refine s15_semiBot_isIrrOn_map_of_ker κ hNN' hN'N J.2.1 ?_ ?_
  · rw [hker]
    exact inf_le_right
  · rw [hker]
    exact le_inf (inf_le_left.trans J.2.2) inf_le_right

end Quotient

section Concrete

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}

theorem s15_semiBot_ker_kappa (V₁ : Subgroup G) (hV : IsElemAbelian 2 V) (h01 : V₀ ≤ V₁) :
    (s15T7Kappa V₀ V₁ V hV h01).ker = imgTil V₀ V hV V₁ := by
  ext q
  constructor
  · intro hq
    rw [MonoidHom.mem_ker] at hq
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    rw [s15_T7_kappa_mk] at hq
    rw [mem_imgTil]
    exact ⟨x, (mem_modNull V₁ V hV x).1
      ((QuotientGroup.eq_one_iff (N := modNull V₁ V hV) x).1 hq), rfl⟩
  · intro hq
    rw [mem_imgTil] at hq
    obtain ⟨x, hxV₁, hxq⟩ := hq
    rw [MonoidHom.mem_ker]
    rw [← hxq, s15_T7_kappa_mk]
    exact (QuotientGroup.eq_one_iff (N := modNull V₁ V hV) x).2
      ((mem_modNull V₁ V hV x).2 hxV₁)

theorem s15_semiBot_sSup_irr_star_of_irrSet (h : Hyp151 D V₀ V L)
    (hfix : imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) =
      fixV (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))))
    (hgen : ⨆ I ∈ irrSet (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))), I = ⊤) :
    sSup {I : Subgroup (vStar D.M V₀ V h.isElemAbelian L) |
      IsIrrOn (lStar D.M V₀ V h.isElemAbelian L) I ⊥} = ⊤ := by
  have hV := h.isElemAbelian
  have h01 := s15_Infra_le_v1Sub D.M V₀ V hV L
  have hM0 : D.M ≤ stabTil V₀ V := s15_Three_M_le_stabTil h
  have hM1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V := s15_Three_M_le_stabTil_star h
  refine s15_semiBot_sSup_irr_of_irrSet (s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV h01)
    (s15_T7_kappa_surjective V₀ (v1Sub D.M V₀ V hV L) V hV h01)
    (X := ⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G)))
    (N := barSub V₀ V hV L) (N' := lStar D.M V₀ V hV L) (s15_semi_le_iSup_barSub h) ?_ ?_ ?_ ?_
    hgen
  · intro x hx n hn
    exact (Subgroup.mem_normalizer_iff.1 (s15_semi_iSup_barSub_le_normalizer h hx) n).1 hn
  · intro n hn
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₀ V hV L n).1 hn
    refine ⟨actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hM1 (h.le hgL)⟩,
      (mem_barSub (v1Sub D.M V₀ V hV L) V hV L _).2 ⟨⟨g, hM1 (h.le hgL)⟩, hgL, rfl⟩, ?_⟩
    intro w
    exact s15_T7_kappa_act V₀ _ V hV h01 g.2 (hM1 (h.le hgL)) w
  · intro n' hn'
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV L n').1 hn'
    refine ⟨actTil V₀ V hV ⟨g, hM0 (h.le hgL)⟩,
      (mem_barSub V₀ V hV L _).2 ⟨⟨g, hM0 (h.le hgL)⟩, hgL, rfl⟩, ?_⟩
    intro w
    exact s15_T7_kappa_act V₀ _ V hV h01 (hM0 (h.le hgL)) g.2 w
  · rw [s15_semiBot_ker_kappa _ hV h01]
    exact hfix

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
