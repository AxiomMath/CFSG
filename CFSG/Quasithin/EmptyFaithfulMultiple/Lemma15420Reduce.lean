module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Setting
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {G : Type*} [Group G] [Finite G]

theorem isSylowTwoOf_map_conj {S H : Subgroup G} (g : G) (h : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom) := by
  rw [isSylowTwoOf_iff] at h ⊢
  obtain ⟨hle, hS, hc⟩ := h
  exact ⟨Subgroup.map_mono hle, (isPGroup_map_equiv_iff 2 _ S).mpr hS,
    by rw [card_map_equiv, twoPart_map_equiv, hc]⟩

theorem exists_lt_of_not_isSylowTwoOf {R H : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R)
    (hns : ¬ IsSylowTwoOf R H) :
    ∃ Q : Subgroup G, R ≤ Q ∧ Q ≤ H ⊓ Subgroup.normalizer (R : Set G) ∧ IsPGroup 2 Q ∧
      Nat.card R < Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hRP, hP⟩ := exists_isSylowTwoOf_of_le hRH hR
  have hne : R ≠ P := fun h => hns (h ▸ hP)
  obtain ⟨x, hx, hxR⟩ := exists_mem_inf_normalizer_of_ne hP.isPGroup hRP hne
  refine ⟨P ⊓ Subgroup.normalizer (R : Set G), le_inf hRP Subgroup.le_normalizer,
    inf_le_inf_right _ hP.le, hP.isPGroup.to_le inf_le_left, ?_⟩
  have hlt : R < P ⊓ Subgroup.normalizer (R : Set G) :=
    lt_of_le_of_ne (le_inf hRP Subgroup.le_normalizer) fun h => hxR (h ▸ hx)
  exact Subgroup.card_lt_of_lt hlt

end General

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

omit [Finite G] in
theorem Setting15419.T₀_le_I (s : Setting15419 G T) : s.T₀ ≤ s.I :=
  le_sup_right.trans le_sup_left

theorem conj_step (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (h16 : Stmt15416 G T) (s s' : Setting15419 G T) (hs' : s'.T₀ = s.T₀) {J : Subgroup G}
    (hJ : InH s'.I J) (hns : ¬ IsSylowTwoOf s.T₀ J) (hR : ¬ IsSylowTwoOf (T ⊓ J) J) :
    ∃ (s'' : Setting15419 G T) (J'' : Subgroup G), s''.T₀ = s.T₀ ∧ InH s''.I J'' ∧
      ¬ IsSylowTwoOf s.T₀ J'' ∧
        Nat.card (T ⊓ J : Subgroup G) < Nat.card (T ⊓ J'' : Subgroup G) := by
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  set S := baum T with hSdef
  have hT₀J : s.T₀ ≤ J := hs' ▸ (s'.T₀_le_I.trans hJ.1)
  have hT₀R : s.T₀ ≤ T ⊓ J := le_inf s.T₀_le hT₀J
  obtain ⟨Q, hRQ, hQ, hQ2, hlt⟩ :=
    exists_lt_of_not_isSylowTwoOf inf_le_right (hT2.to_le inf_le_left) hR
  have hbaum : S = baum (T ⊓ J) := baum_eq_of_le (s.baum_le_T₀.trans hT₀R) inf_le_left
  have hQS : Q ≤ Subgroup.normalizer (S : Set G) := by
    rw [hbaum]
    exact (hQ.trans inf_le_right).trans (normalizer_le_normalizer_baum _)
  have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hTSyl : IsSylowTwoOf T (Subgroup.normalizer (S : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTS
  obtain ⟨P, hQP, hP⟩ := exists_isSylowTwoOf_of_le hQS hQ2
  obtain ⟨n, hn, hPn⟩ := hTSyl.exists_conj hP
  set g := n⁻¹ with hg
  have hgS : g ∈ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hn
  have hgM : g ∈ s'.M₁ ⊓ s'.M₂ := le_inf (h16 _ s'.inM₁) (h16 _ s'.inM₂) hgS
  have hQgT : Q.map (MulAut.conj g).toMonoidHom ≤ T := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (hQP.trans hPn.le)
    rwa [hg, ← map_conj_mul, inv_mul_cancel, map_conj_one] at h1
  have hT₀g : s.T₀.map (MulAut.conj g).toMonoidHom = s.T₀ := by
    have hT₀g_le : s.T₀.map (MulAut.conj g).toMonoidHom ≤ s.T₀ := by
      rw [← hs']
      have hX := s'.permutesX hyp h12 hgM.1
      have hY := s'.permutesY hyp h12 hgM.2
      have hTM₁ : T ≤ s'.M₁ := s'.inM₁.2
      have hTM₂ : T ≤ s'.M₂ := s'.inM₂.2
      have hT₀X₁ : s'.T₀ ≤ Subgroup.normalizer (s'.X₁ : Set G) := inf_le_right
      have hT₀Y₁ : s'.T₀ ≤ Subgroup.normalizer (s'.Y₁ : Set G) := inf_le_left.trans inf_le_right
      have hT₀X₂ : s'.T₀ ≤ Subgroup.normalizer (s'.X₂ : Set G) := fun t ht =>
        ((s'.permutesX hyp h12 (hTM₁ (s'.T₀_le ht))).mem_normalizer_iff s'.dataX.ne).mp
          (hT₀X₁ ht)
      have hT₀Y₂ : s'.T₀ ≤ Subgroup.normalizer (s'.Y₂ : Set G) := fun t ht =>
        ((s'.permutesY hyp h12 (hTM₂ (s'.T₀_le ht))).mem_normalizer_iff s'.dataY.ne).mp
          (hT₀Y₁ ht)
      have hmap : ∀ {A B : Subgroup G}, PermutesPair g A B →
          s'.T₀ ≤ Subgroup.normalizer (A : Set G) → s'.T₀ ≤ Subgroup.normalizer (B : Set G) →
          s'.T₀.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set G) := by
        intro A B hAB hA hB
        rcases hAB with ⟨h1, -⟩ | ⟨-, h2⟩
        · have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hA
          rwa [← normalizer_map_equiv, h1] at this
        · have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hB
          rwa [← normalizer_map_equiv, h2] at this
      refine le_inf (le_inf ?_ (hmap hY hT₀Y₁ hT₀Y₂)) (hmap hX hT₀X₁ hT₀X₂)
      rw [hs']
      exact (Subgroup.map_mono (hT₀R.trans hRQ)).trans hQgT
    exact Subgroup.eq_of_le_of_card_ge hT₀g_le (by rw [card_map_equiv])
  have hgT₀ : g ∈ Subgroup.normalizer (s.T₀ : Set G) := mem_normalizer_iff_map_conj.mpr hT₀g
  have hgT₀' : g ∈ Subgroup.normalizer (s'.T₀ : Set G) := hs' ▸ hgT₀
  refine ⟨s'.conjL hyp h12 g hgM, J.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact hs'
  · rw [Setting15419.conjL_I hyp h12 s' g hgM hgT₀']
    refine ⟨Subgroup.map_mono hJ.1, ?_⟩
    rw [pCoreOf_map_equiv, Ne, map_equiv_eq_bot_iff]
    exact hJ.2
  · intro hsyl
    apply hns
    have := isSylowTwoOf_map_conj g⁻¹ hsyl
    rwa [← map_conj_mul, inv_mul_cancel, map_conj_one,
      map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ hgT₀)] at this
  · have hQg : Q.map (MulAut.conj g).toMonoidHom ≤ T ⊓ J.map (MulAut.conj g).toMonoidHom :=
      le_inf hQgT (Subgroup.map_mono (hQ.trans inf_le_left))
    calc Nat.card (T ⊓ J : Subgroup G) < Nat.card Q := hlt
      _ = Nat.card (Q.map (MulAut.conj g).toMonoidHom) := (card_map_equiv _ Q).symm
      _ ≤ Nat.card (T ⊓ J.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
        Subgroup.card_le_of_le hQg

theorem exists_config (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (h16 : Stmt15416 G T) (s : Setting15419 G T) {I₀ : Subgroup G} (hI₀ : InH s.I I₀)
    (hns : ¬ IsSylowTwoOf s.T₀ I₀) :
    ∃ (s' : Setting15419 G T) (J : Subgroup G), s'.T₀ = s.T₀ ∧ InH s'.I J ∧
      IsSylowTwoOf (T ⊓ J) J ∧ s.T₀ < T ⊓ J ∧
      ∀ J' : Subgroup G, InH s'.I J' → T ⊓ J ≤ J' → IsSylowTwoOf (T ⊓ J) J' := by
  classical
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  let 𝒮 : Set (Subgroup G) :=
    {J | ∃ s' : Setting15419 G T, s'.T₀ = s.T₀ ∧ InH s'.I J ∧ ¬ IsSylowTwoOf s.T₀ J}
  have hne : 𝒮.Nonempty := ⟨I₀, s, rfl, hI₀, hns⟩
  obtain ⟨J, ⟨s', hs', hJ, hJns⟩, hmax⟩ :=
    Set.exists_max_image 𝒮 (fun J => Nat.card (T ⊓ J : Subgroup G)) (Set.toFinite 𝒮) hne
  have hsyl : ∀ J' ∈ 𝒮, Nat.card (T ⊓ J : Subgroup G) ≤ Nat.card (T ⊓ J' : Subgroup G) →
      IsSylowTwoOf (T ⊓ J') J' := by
    rintro J' ⟨s'', hs'', hJ', hJ'ns⟩ hle
    by_contra hR
    obtain ⟨s₃, J₃, hs₃, hJ₃, hJ₃ns, hlt⟩ := conj_step hyp h12 h16 s s'' hs'' hJ' hJ'ns hR
    have := hmax J₃ ⟨s₃, hs₃, hJ₃, hJ₃ns⟩
    omega
  have hJsyl : IsSylowTwoOf (T ⊓ J) J := hsyl J ⟨s', hs', hJ, hJns⟩ le_rfl
  have hT₀J : s.T₀ ≤ J := hs' ▸ (s'.T₀_le_I.trans hJ.1)
  have hT₀R : s.T₀ ≤ T ⊓ J := le_inf s.T₀_le hT₀J
  have hlt : s.T₀ < T ⊓ J := lt_of_le_of_ne hT₀R (fun h => hJns (h ▸ hJsyl))
  refine ⟨s', J, hs', hJ, hJsyl, hlt, fun J' hJ' hRJ' => ?_⟩
  have hJ'ns : ¬ IsSylowTwoOf s.T₀ J' := by
    intro h
    have h1 : Nat.card (T ⊓ J : Subgroup G) ≤ Nat.card s.T₀ := by
      rw [h.card_eq]
      exact card_le_twoPart hRJ' (hT2.to_le inf_le_left)
    have h2 := Subgroup.card_lt_of_lt hlt
    omega
  have hJ'mem : J' ∈ 𝒮 := ⟨s', hs', hJ', hJ'ns⟩
  have hle : Nat.card (T ⊓ J : Subgroup G) ≤ Nat.card (T ⊓ J' : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf inf_le_left hRJ')
  have hsyl' := hsyl J' hJ'mem hle
  have heq : T ⊓ J' = T ⊓ J :=
    (Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hRJ') (hmax J' hJ'mem)).symm
  rwa [heq] at hsyl'

theorem Setting15419.le_T₀_of_le_normalizer (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) (s : Setting15419 G T) {R : Subgroup G} (hRT : R ≤ T)
    (h₁ : R ≤ Subgroup.normalizer (s.L₁ : Set G)) (h₂ : R ≤ Subgroup.normalizer (s.L₂ : Set G)) :
    R ≤ s.T₀ := by
  intro r hr
  have hrM₁ : r ∈ s.M₁ := s.inM₁.2 (hRT hr)
  have hrM₂ : r ∈ s.M₂ := s.inM₂.2 (hRT hr)
  have hX : r ∈ Subgroup.normalizer (s.X₁ : Set G) := by
    rcases s.choice₁ with h | h
    · exact h ▸ h₁ hr
    · exact ((s.permutesX hyp h12 hrM₁).mem_normalizer_iff s.dataX.ne).mpr (h ▸ h₁ hr)
  have hY : r ∈ Subgroup.normalizer (s.Y₁ : Set G) := by
    rcases s.choice₂ with h | h
    · exact h ▸ h₂ hr
    · exact ((s.permutesY hyp h12 hrM₂).mem_normalizer_iff s.dataY.ne).mpr (h ▸ h₂ hr)
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hRT hr, hY⟩, hX⟩

end CFSG.Quasithin.EmptyFaithfulMultiple
