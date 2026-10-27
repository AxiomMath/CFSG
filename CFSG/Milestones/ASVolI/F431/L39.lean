module

public import CFSG.Milestones.ASVolI.F431.Odd
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def burnsideF4m_LieCoreSp : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 .Sp4 2 f Gp M₁ M₂ → 2 ≤ f →
    burnsideF4m_Core1 Gp M₁ ∧ burnsideF4m_Core2 .Sp4 Gp M₂ ∧
      pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁) ∧ pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) ∧
      pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))

@[expose] def burnsideF4m_F439Sp2 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 .Sp4 1 Gp M₁ M₂ β ε z → ¬ IsL43 M →
    ∀ u : ↥(M₁ ⊓ M₂), (u : E) ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → u ≠ 1 → u * u = 1 →
      (u : E) ∉ ctr (oPPrime 2 (Gp ⊓ M₁)) → (u : E) ∉ ctr (oPPrime 2 (Gp ⊓ M₂)) →
      Subgroup.centralizer ({bM β ε u} : Set M) ≤ MiOne β ε ⊓ MiTwo β ε

theorem burnsideF4m_spGSetup_c2 {Mb G : Type} [Group Mb] [Group G] [Finite Mb] [Finite G]
    {N1 N2 T : Subgroup Mb} {I : Finset Mb} {b1 : ↥N1 →* G} {b2 : ↥N2 →* G}
    {M1 M2 : Subgroup G} (S : SpGSetup N1 N2 b1 b2 M1 M2) (L : F431SpLie T N1 N2 I) {x : Mb}
    (hx : x ∈ centerOf T) (hxo : orderOf x = 2) (hx1 : x ∉ spZ N1 N2 0)
    (hx2 : x ∉ spZ N1 N2 1) :
    Subgroup.centralizer ({amalgamMap b1 b2 x} : Set G) ≤ M1 ⊓ M2 := by
  obtain ⟨i, hiI, hic, hiφ⟩ := L.W.exists_conj S.comp hx.1 hxo
  have hiC : Subgroup.centralizer ({i} : Set Mb) ≤ N1 ⊓ N2 := by
    rcases L.I_type i hiI with ⟨hZ, -⟩ | ⟨hZ, -⟩ | hC
    · exact absurd (L.Z_cls 0 i hZ x hx hic) hx1
    · exact absurd (L.Z_cls 1 i hZ x hx hic) hx2
    · exact hC
  have hci := S.centralizer_c2 L hiI hiC
  have hiN1 : i ∈ N1 := L.W.T_le₁ (L.W.mem_T i hiI)
  have hxN1 : x ∈ N1 := L.W.T_le₁ hx.1
  have hcu : amalgamMap b1 b2 i ∈ centerOf (subImg b1 T) := by
    rw [amalgamMap_of_mem₁ b1 b2 hiN1, subImg_centerOf S.comp.inj₁ L.W.T_le₁]
    exact mem_subImg_of_mem b1 hiN1 (L.I_center i hiI)
  have hcv : amalgamMap b1 b2 x ∈ centerOf (subImg b1 T) := by
    rw [amalgamMap_of_mem₁ b1 b2 hxN1, subImg_centerOf S.comp.inj₁ L.W.T_le₁]
    exact mem_subImg_of_mem b1 hxN1 hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hiφ
  obtain ⟨n, hn, hnuv⟩ := exists_normalizer_conj_of_central (S.sylow L) hcu hcv hg
  obtain ⟨hn1, hn2⟩ := S.normalizer_le L hn
  rw [← hnuv]
  intro y hy
  have hy' : n⁻¹ * y * n ∈ Subgroup.centralizer ({amalgamMap b1 b2 i} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc n⁻¹ * y * n * amalgamMap b1 b2 i
        = n⁻¹ * (y * (n * amalgamMap b1 b2 i * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * amalgamMap b1 b2 i * n⁻¹) * y) * n := by rw [hy]
      _ = amalgamMap b1 b2 i * (n⁻¹ * y * n) := by group
  obtain ⟨hy1, hy2⟩ := hci hy'
  have e : y = n * (n⁻¹ * y * n) * n⁻¹ := by group
  rw [e]
  exact ⟨M1.mul_mem (M1.mul_mem hn1 hy1) (M1.inv_mem hn1),
    M2.mul_mem (M2.mul_mem hn2 hy2) (M2.inv_mem hn2)⟩

section F439

set_option linter.unusedSectionVars false


variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_map_eq_of_iff {K' : Type} [Group K'] (θ : E ≃* K') {N : Subgroup K'}
    {P : Subgroup E} (h : ∀ e, θ e ∈ N ↔ e ∈ P) : P.map θ.toMonoidHom = N := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (h e).2 he
  · intro hx
    refine ⟨θ.symm x, (h (θ.symm x)).1 (by simpa using hx), ?_⟩
    simp

theorem burnsideF4m_odd_of [Finite E] {κ : GLKind} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp))
    (hodd : Odd Gp.index) :
    Odd (Nat.card ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K / Nat.card ↥Gp) := by
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hK : Nat.card ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K = Nat.card E := by
    have : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K = (burnsideF4d_rho Gp).range :=
      burnsideF4d_K_eq hyp.toHypF_4_4g hyam
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  rw [hK]
  have := Subgroup.card_mul_index Gp
  have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
  rw [show Nat.card E / Nat.card ↥Gp = Gp.index by
    rw [← this, Nat.mul_div_cancel_left _ hpos]]
  exact hodd

theorem burnsideF4m_spGSetup {K' : Type} [Group K'] (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z)
    (hZ1 : burnsideF4m_Core1 Gp M₁) (hZ2 : burnsideF4m_Core2 .Sp4 Gp M₂)
    (hQ1 : pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁)) (hQ2 : pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂))
    (hQ12 : pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (θ : E ≃* K') {N1 N2 : Subgroup K'} (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁)
    (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂) :
    SpGSetup N1 N2 ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
      ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) (MiOne β ε) (MiTwo β ε) := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  obtain ⟨hC, hr1, hr2, hint⟩ := burnsideF4m_comp_data hyp θ h1 h2
  have hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := by
    rw [hQ12]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hSinM : SinM Gp β ε = pCoreOf 2 (MiOne β ε ⊓ MiTwo β ε) :=
    burnsideF4d_SinM_eq_pCore Gp β hyp.faithful ε hyp.inj hle
  refine ⟨hC, hr1, hr2, hint, ?_, ?_, fun x hx hx2 => burnsideF4m_cent_MiOne hyp (by decide)
    hZ1 hx hx2, fun x hx hx2 => burnsideF4m_cent_MiTwo hyp hZ2 hx hx2, ?_, ?_⟩
  · rw [burnsideF4m_centerOf_pCore_MiOne hyp hQ1]
    exact (hyp.ha (Or.inl rfl)).1
  · rw [burnsideF4m_centerOf_pCore_MiTwo hyp hQ2]
    exact (hyp.ha (Or.inl rfl)).2
  · intro w hw hw2
    have hw' : w ∈ ctr (SinM Gp β ε) := by rw [hSinM]; exact hw
    have hw1 : w ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hw2
      exact absurd hw2 (by decide)
    have hww : w * w = 1 := by
      have := pow_orderOf_eq_one w
      rw [hw2, pow_two] at this
      exact this
    exact burnsideF4m_charTwo_of_fstar ((hyp.hc rfl).2 w hw' hw1 hww)
  · intro h
    exact (Nat.not_even_iff_odd.mpr (hyp.hd rfl)) (even_iff_two_dvd.mpr h)

theorem burnsideF4m_F_4_39_K {K' : Type} [Group K'] [Finite K']
    (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) (hZ1 : burnsideF4m_Core1 Gp M₁)
    (hZ2 : burnsideF4m_Core2 .Sp4 Gp M₂) (hQ1 : pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁))
    (hQ2 : pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂))
    (hQ12 : pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (θ : E ≃* K') {N1 N2 : Subgroup K'} (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁)
    (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂) {T : Subgroup K'} {I : Finset K'} (L : F431SpLie T N1 N2 I)
    (u : ↥(M₁ ⊓ M₂)) (hu : (u : E) ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) (hu1 : u ≠ 1)
    (hu2 : u * u = 1) (hu₁ : (u : E) ∉ ctr (oPPrime 2 (Gp ⊓ M₁)))
    (hu₂ : (u : E) ∉ ctr (oPPrime 2 (Gp ⊓ M₂))) :
    Subgroup.centralizer ({bM β ε u} : Set M) ≤ MiOne β ε ⊓ MiTwo β ε := by
  haveI := hyp.finite_M
  have hS := burnsideF4m_spGSetup hyp hZ1 hZ2 hQ1 hQ2 hQ12 θ h1 h2
  have hN1 : M₁.map θ.toMonoidHom = N1 := burnsideF4m_map_eq_of_iff θ h1
  have hN2 : M₂.map θ.toMonoidHom = N2 := burnsideF4m_map_eq_of_iff θ h2
  have hT : (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))).map θ.toMonoidHom = T := by
    rw [← L.O2N12, ← hN1, ← hN2, ← Subgroup.map_inf_eq _ _ θ.toMonoidHom θ.injective, ← hQ12]
    exact (burnsideF4j_pCoreOf_map θ.toMonoidHom θ.injective _).symm
  have hu'T : θ u ∈ centerOf T := by
    rw [← hT, D4q.Struct.centerOf_map_eq]
    exact Subgroup.mem_map_of_mem _ hu
  have hu1E : (u : E) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2E : (u : E) * u = 1 := congrArg Subtype.val hu2
  have hu'1 : θ u ≠ 1 := fun h => hu1E (θ.injective (h.trans (map_one θ).symm))
  have hu'o : orderOf (θ u) = 2 := by
    refine orderOf_eq_prime ?_ hu'1
    rw [pow_two, ← map_mul, hu2E, map_one]
  have hmapZ : ∀ (P : Subgroup E) (N : Subgroup K'), P.map θ.toMonoidHom = N →
      θ u ∈ centerOf (perfectCore N) → (u : E) ∈ centerOf (perfectCore P) := by
    intro P N hPN hmem
    rw [← hPN, G2.OutK.perfectCore_map_inj θ.toMonoidHom θ.injective,
      G2.OutK.centerOf_map_inj θ.toMonoidHom θ.injective] at hmem
    obtain ⟨e, he, hee⟩ := Subgroup.mem_map.mp hmem
    have : e = (u : E) := θ.injective hee
    rw [← this]
    exact he
  have hx1 : θ u ∉ spZ N1 N2 0 := fun h => hu₁ (hZ1 _ (hmapZ M₁ N1 hN1 h) hu1E hu2E)
  have hx2 : θ u ∉ spZ N1 N2 1 := fun h => hu₂ (hZ2 _ (hmapZ M₂ N2 hN2 h) hu1E hu2E).2
  have hbu : amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
      ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) (θ u) = bM β ε u := by
    rw [amalgamMap_of_mem₁ _ _ (L.W.T_le₁ hu'T.1)]
    show burnsideF4d_bOne β ε (burnsideF4m_psi θ h1 ⟨θ u, _⟩) =
      burnsideF4d_bOne β ε ⟨u, u.2.1⟩
    congr 1
    exact Subtype.ext (by rw [burnsideF4m_psi_apply]; simp)
  rw [← hbu]
  exact burnsideF4m_spGSetup_c2 hS L hu'T hu'o hx1 hx2

theorem burnsideF4m_F_4_39_odd (hcore : burnsideF4m_LieCoreSp)
    (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) (hodd : Odd Gp.index)
    (u : ↥(M₁ ⊓ M₂)) (hu : (u : E) ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) (hu1 : u ≠ 1)
    (hu2 : u * u = 1) (hu₁ : (u : E) ∉ ctr (oPPrime 2 (Gp ⊓ M₁)))
    (hu₂ : (u : E) ∉ ctr (oPPrime 2 (Gp ⊓ M₂))) :
    Subgroup.centralizer ({bM β ε u} : Set M) ≤ MiOne β ε ⊓ MiTwo β ε := by
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  obtain ⟨hZ1, hZ2, hQ1, hQ2, hQ12⟩ := hcore f E Gp M₁ M₂ hyp.amalgam hf
  obtain ⟨marking, h1m, h2m⟩ := burnsideF4g_marking (c := .Sp4) hyp.amalgam.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamSp4 hf marking
  rw [← h1m, ← h2m] at hTD
  have hmodel := burnsideF4g_lieModel_Sp4 hf hyp.amalgam.model
  obtain ⟨θ, h1, h2⟩ := burnsideF4m_exists_theta hyp.amalgam hTD
  haveI : Finite ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hTD).K :=
    Finite.of_equiv E θ.toEquiv
  obtain ⟨T, I, L⟩ := f431SpLieProp f ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hTD).toLieAmalgamExt
    (burnsideF4m_odd_of hyp.amalgam hTD hodd)
  exact burnsideF4m_F_4_39_K hyp hZ1 hZ2 hQ1 hQ2 hQ12 θ h1 h2 L u hu hu1 hu2 hu₁ hu₂

theorem burnsideF4m_odd_index_Sp4_of (hcore : burnsideF4m_LieCoreSp)
    (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) : Odd Gp.index := by
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  by_contra hodd
  obtain ⟨hZ1, hZ2, hQ1, hQ2, hQ12⟩ := hcore f E Gp M₁ M₂ hyp.amalgam hf
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp.amalgam.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamSp4 hf marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_Sp4 hf hyp.amalgam.model
  have hnodd := burnsideF4m_not_odd hyp.amalgam hTD hodd
  refine burnsideF4m_false_of_spOut hyp hf hZ1 hZ2 hQ1 hQ2 hQ12 hTD ?_
  by_cases hf2 : f = 2
  · subst hf2
    exact Or.inr (f431SpOut4Lie ↥Gp hmodel _ hnodd)
  · exact Or.inl (f431SpOutLieProp (by omega) ↥Gp hmodel _ hnodd)

theorem burnsideF4m_F_4_39_of (hcore : burnsideF4m_LieCoreSp) (h2 : burnsideF4m_F439Sp2) :
    F_4_39 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hκ u hu hu1 hu2 hu₁ hu₂
  subst hκ
  have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
  by_cases hf2 : 2 ≤ f
  · exact burnsideF4m_F_4_39_odd hcore hyp hf2 (burnsideF4m_odd_index_Sp4_of hcore hyp hf2) u hu
      hu1 hu2 hu₁ hu₂
  · have hf : f = 1 := by omega
    subst hf
    exact h2 E Gp M₁ M₂ Y β M ε z hyp hL43 u hu hu1 hu2 hu₁ hu₂

end F439

end CFSG.ASVolI
