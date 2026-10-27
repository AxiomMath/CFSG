module

public import CFSG.Milestones.ASVolI.F431.L39
public import CFSG.Milestones.ASVolI.F431.Final

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

theorem burnsideF4m_spShape_subImg {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    {b : ↥N →* G} (hb : Function.Injective b) {S : Subgroup Mb} {Q : Fin 2 → Subgroup Mb}
    (hS : SpShape S Q) (hSN : S ≤ N) :
    SpShape (subImg b S) (fun j => subImg b (Q j)) where
  Q_le j := subImg_mono b (hS.Q_le j)
  Q_norm j := subImg_le_normalizer b (hS.Q_norm j)
  Q_abel j := by
    intro x hx y hy
    obtain ⟨x', hx'N, hx'Q, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy'N, hy'Q, rfl⟩ := mem_subImg.mp hy
    exact (commute_iff_of_injective hb hy'N hx'N).mpr (hS.Q_abel j x' hx'Q y' hy'Q)
  Z_le j := by
    rw [subImg_centerOf hb hSN]
    exact subImg_mono b (hS.Z_le j)
  Z_sq := by
    intro z hz
    rw [subImg_centerOf hb hSN] at hz
    obtain ⟨z', hz'N, hz'Z, rfl⟩ := mem_subImg.mp hz
    exact (sq_eq_one_iff_of_injective hb hz'N).mpr (hS.Z_sq z' hz'Z)
  inv_mem := by
    intro x hx hx2
    obtain ⟨x', hx'N, hx'T, rfl⟩ := mem_subImg.mp hx
    obtain ⟨j, hj⟩ := hS.inv_mem x' hx'T ((sq_eq_one_iff_of_injective hb hx'N).mp hx2)
    exact ⟨j, mem_subImg_of_mem b hx'N hj⟩
  cen j := by
    intro x hx hxZ y hy hcomm
    obtain ⟨x', hx'N, hx'Q, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy'N, hy'T, rfl⟩ := mem_subImg.mp hy
    have hx'Z : x' ∉ centerOf S := fun h => hxZ (by
      rw [subImg_centerOf hb hSN]
      exact mem_subImg_of_mem b hx'N h)
    have hcomm' : y' * x' = x' * y' := (commute_iff_of_injective hb hx'N hy'N).mp hcomm
    exact mem_subImg_of_mem b hy'N (hS.cen j x' hx'Q hx'Z y' hy'T hcomm')
  ex j := by
    obtain ⟨x, hxQ, hxZ, hx2⟩ := hS.ex j
    have hxN : x ∈ N := hSN (hS.Q_le j hxQ)
    refine ⟨b ⟨x, hxN⟩, mem_subImg_of_mem b hxN hxQ, fun h => hxZ ?_,
      (sq_eq_one_iff_of_injective hb hxN).mpr hx2⟩
    rw [subImg_centerOf hb hSN] at h
    exact (mem_subImg_iff_of_injective hb hxN).mp h

@[expose] def burnsideF4m_Sp2Facts : Prop :=
  ∀ (E : Type) [Group E] (M₁ M₂ : Subgroup E), HypF_4_4 .Sp4 2 1 ⊤ M₁ M₂ →
    SpShape (pCoreOf 2 (M₁ ⊓ M₂)) ![pCoreOf 2 M₁, pCoreOf 2 M₂] ∧
    (∀ u ∈ centerOf (pCoreOf 2 (M₁ ⊓ M₂)), u ≠ 1 → u * u = 1 →
      u ∉ ctr (oPPrime 2 M₁) → u ∉ ctr (oPPrime 2 M₂) →
      Subgroup.centralizer ({u} : Set E) ≤ M₁ ⊓ M₂) ∧
    (∃ z₁ ∈ ctr (oPPrime 2 M₁), z₁ ≠ 1 ∧ z₁ ∈ centerOf (pCoreOf 2 (M₁ ⊓ M₂))) ∧
    (∃ z₂ ∈ ctr (oPPrime 2 M₂), z₂ ≠ 1 ∧ z₂ ∈ centerOf (pCoreOf 2 (M₁ ⊓ M₂)))

@[expose] def burnsideF4m_TopSp2 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 .Sp4 2 1 Gp M₁ M₂ → Gp = ⊤

section F439Two

set_option linter.unusedSectionVars false


theorem burnsideF4m_F439Sp2_of (hfacts : burnsideF4m_Sp2Facts) (htop : burnsideF4m_TopSp2) :
    burnsideF4m_F439Sp2 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 u hu hu1 hu2 hu₁ hu₂
  have hGp := htop E Gp M₁ M₂ hyp.amalgam
  subst hGp
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  simp only [top_inf_eq] at hu hu₁ hu₂
  obtain ⟨hsh, hc2, ⟨z₁, hz₁, hz₁1, hz₁S⟩, ⟨z₂, hz₂, hz₂1, hz₂S⟩⟩ :=
    hfacts E M₁ M₂ hyp.amalgam
  have hb1 : Function.Injective (burnsideF4d_bOne β ε) := burnsideF4j_bOne_injective hyp
  have hb2 : Function.Injective (burnsideF4d_bTwo β ε) := burnsideF4j_bTwo_injective hyp
  have hSM1 : pCoreOf 2 (M₁ ⊓ M₂) ≤ M₁ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hSM2 : pCoreOf 2 (M₁ ⊓ M₂) ≤ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hQ1S : pCoreOf 2 M₁ ≤ pCoreOf 2 (M₁ ⊓ M₂) := hsh.Q_le 0
  have hQ2S : pCoreOf 2 M₂ ≤ pCoreOf 2 (M₁ ⊓ M₂) := hsh.Q_le 1
  have hshM := burnsideF4m_spShape_subImg hb1 hsh hSM1
  have hT : IsSylowTwoOf (subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (M₁ ⊓ M₂))) ⊤ := by
    have hS0 := (burnsideF4j_sylow_data hyp.amalgam).1
    simp only [top_inf_eq] at hS0
    have hS1 : IsSylowTwoOf (pCoreOf 2 (M₁ ⊓ M₂)) (M₁ ⊓ M₂) :=
      F7.isSylowTwoOf_mono_right hS0 (CFSG.LieType.BorelTits.pCoreOf_le 2 _) le_top
    have hS2 := (burnsideF4j_isSylow_subImg_iff (burnsideF4d_bOne β ε) hb1 hSM1
      inf_le_left).mpr hS1
    rw [← burnsideF4d_inter_eq β hyp.faithful ε hyp.inj] at hS2
    exact burnsideF4m_F_4_33 .Sp4 1 E ⊤ M₁ M₂ Y β M ε z hyp _ hS2
  have hN1 : Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₁) : Subgroup M) : Set M) = MiOne β ε := by
    have e : ctr (pCoreOf 2 (GiOne ⊤ β ε)) = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₁) := by
      rw [burnsideF4d_GiOne_eq, top_inf_eq, subImg_pCoreOf hb1 le_rfl]
      show centerOf _ = _
      rw [subImg_centerOf hb1 (hQ1S.trans hSM1),
        centerOf_eq_of_abelian (X := pCoreOf 2 M₁) (hsh.Q_abel 0)]
    rw [← e]
    exact (hyp.ha (Or.inl rfl)).1
  have hag : ∀ g (h1 : g ∈ M₁) (h2 : g ∈ M₂),
      burnsideF4d_bOne β ε ⟨g, h1⟩ = burnsideF4d_bTwo β ε ⟨g, h2⟩ :=
    fun g h1 h2 => burnsideF4m_bOne_eq_bTwo β ε g h1 h2
  have hN2 : Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₂) : Subgroup M) : Set M) = MiTwo β ε := by
    have e : ctr (pCoreOf 2 (GiTwo ⊤ β ε)) = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₂) := by
      rw [burnsideF4d_GiTwo_eq, top_inf_eq, subImg_pCoreOf hb2 le_rfl]
      show centerOf _ = _
      rw [subImg_centerOf hb2 (CFSG.LieType.BorelTits.pCoreOf_le 2 _),
        centerOf_eq_of_abelian (X := pCoreOf 2 M₂) (hsh.Q_abel 1)]
      exact (subImg_eq_of_agree hag (hQ2S.trans hSM1) (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).symm
    rw [← e]
    exact (hyp.ha (Or.inl rfl)).2
  have hNT : ∀ n ∈ Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (M₁ ⊓ M₂)) : Subgroup M) : Set M),
      n ∈ MiOne β ε ∧ n ∈ MiTwo β ε := by
    intro n hn
    have h0 : n ∈ Subgroup.normalizer
        ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₁) : Subgroup M) : Set M) :=
      hshM.normalizer_le hT hn 0
    have h1 : n ∈ Subgroup.normalizer
        ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₂) : Subgroup M) : Set M) :=
      hshM.normalizer_le hT hn 1
    rw [hN1] at h0
    rw [hN2] at h1
    exact ⟨h0, h1⟩
  have hbu : bM β ε u = burnsideF4d_bOne β ε ⟨u, u.2.1⟩ := rfl
  have hu1E : (u : E) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2E : (u : E) * u = 1 := congrArg Subtype.val hu2
  have huZ : bM β ε u ∈ centerOf (subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (M₁ ⊓ M₂))) := by
    rw [hbu, subImg_centerOf hb1 hSM1]
    exact mem_subImg_of_mem _ u.2.1 hu
  have hu'1 : bM β ε u ≠ 1 := by
    rw [hbu]
    intro h
    exact hu1E (congrArg Subtype.val (hb1 (h.trans (map_one _).symm)))
  have hu'2 : bM β ε u * bM β ε u = 1 := by
    rw [← map_mul, hu2, map_one]
  have hSinM : SinM ⊤ β ε = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (M₁ ⊓ M₂)) := by
    rw [burnsideF4d_SinM_eq, top_inf_eq]
  have huS : bM β ε u ∈ ctr (SinM ⊤ β ε) := by
    rw [hSinM]
    exact huZ
  have hchar := burnsideF4m_charTwo_of_fstar ((hyp.hc rfl).2 _ huS hu'1 hu'2)
  have hinter := burnsideF4d_inter_eq β hyp.faithful ε hyp.inj
  have hcu : Subgroup.centralizer ({(u : E)} : Set E) ≤ M₁ ⊓ M₂ :=
    hc2 _ hu hu1E hu2E hu₁ hu₂
  rcases hshM.centralizer_cases hT huZ hchar with ⟨j, hj⟩ | hZ
  ·
    intro y hy
    rw [hinter]
    fin_cases j
    · have hyN : y ∈ Subgroup.normalizer
          ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₁) : Subgroup M) : Set M) := hj hy
      rw [hN1, burnsideF4d_MiOne_eq] at hyN
      obtain ⟨y', hy'N, -, rfl⟩ := mem_subImg.mp hyN
      have hc : y' ∈ Subgroup.centralizer ({(u : E)} : Set E) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := Subgroup.mem_centralizer_singleton_iff.mp hy
        rw [hbu] at h
        exact (commute_iff_of_injective hb1 u.2.1 hy'N).mp h
      exact mem_subImg_of_mem _ hy'N (hcu hc)
    · have hyN : y ∈ Subgroup.normalizer
          ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₂) : Subgroup M) : Set M) := hj hy
      rw [hN2, burnsideF4d_MiTwo_eq] at hyN
      obtain ⟨y', hy'N, -, rfl⟩ := mem_subImg.mp hyN
      have hc : y' ∈ Subgroup.centralizer ({(u : E)} : Set E) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := Subgroup.mem_centralizer_singleton_iff.mp hy
        rw [hbu, hag _ u.2.1 u.2.2] at h
        exact (commute_iff_of_injective hb2 u.2.2 hy'N).mp h
      have hy'12 := hcu hc
      rw [← hag _ hy'12.1 hy'N]
      exact mem_subImg_of_mem _ hy'12.1 hy'12
  ·
    intro g hg
    have hz₁M : z₁ ∈ M₁ := hSM1 hz₁S.1
    have hz₂M : z₂ ∈ M₁ := hSM1 hz₂S.1
    have hz₂M2 : z₂ ∈ M₂ := hSM2 hz₂S.1
    have hw : ∀ (x : E) (hx : x ∈ M₁), x ∈ centerOf (pCoreOf 2 (M₁ ⊓ M₂)) →
        burnsideF4d_bOne β ε ⟨x, hx⟩ ∈
          centerOf (subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (M₁ ⊓ M₂))) := by
      intro x hx hxS
      rw [subImg_centerOf hb1 hSM1]
      exact mem_subImg_of_mem _ hx hxS
    have key : ∀ (x : E) (hx : x ∈ M₁), x ∈ centerOf (pCoreOf 2 (M₁ ⊓ M₂)) →
        ∃ n, (n ∈ MiOne β ε ∧ n ∈ MiTwo β ε) ∧ n⁻¹ * g ∈
          Subgroup.centralizer ({burnsideF4d_bOne β ε ⟨x, hx⟩} : Set M) := by
      intro x hx hxS
      have h1 := hw x hx hxS
      obtain ⟨n, hn, hnw⟩ := exists_normalizer_conj_of_central hT h1 (hZ g hg _ h1) rfl
      refine ⟨n, hNT n hn, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n⁻¹ * g * burnsideF4d_bOne β ε ⟨x, hx⟩
          = n⁻¹ * (g * burnsideF4d_bOne β ε ⟨x, hx⟩ * g⁻¹) * g := by group
        _ = n⁻¹ * (n * burnsideF4d_bOne β ε ⟨x, hx⟩ * n⁻¹) * g := by rw [hnw]
        _ = burnsideF4d_bOne β ε ⟨x, hx⟩ * (n⁻¹ * g) := by group
    obtain ⟨n₁, ⟨hn₁, -⟩, hc₁⟩ := key z₁ hz₁M hz₁S
    obtain ⟨n₂, ⟨-, hn₂⟩, hc₂⟩ := key z₂ hz₂M hz₂S
    have hC1 : Subgroup.centralizer ({burnsideF4d_bOne β ε ⟨z₁, hz₁M⟩} : Set M) ≤ MiOne β ε := by
      refine burnsideF4j_centralizer_Z1_le hyp (by decide) ?_ ?_
      · rw [burnsideF4j_Z1_eq hyp]
        exact mem_subImg_of_mem _ hz₁M (by rw [top_inf_eq]; exact hz₁)
      · intro h
        exact hz₁1 (congrArg Subtype.val (hb1 (h.trans (map_one _).symm)))
    have hC2 : Subgroup.centralizer ({burnsideF4d_bOne β ε ⟨z₂, hz₂M⟩} : Set M) ≤ MiTwo β ε := by
      rw [hag _ hz₂M hz₂M2]
      refine (hyp.hc rfl).1 _ ?_ ?_
      · rw [burnsideF4j_Z2_eq hyp]
        exact mem_subImg_of_mem _ hz₂M2 (by rw [top_inf_eq]; exact hz₂)
      · intro h
        exact hz₂1 (congrArg Subtype.val (hb2 (h.trans (map_one _).symm)))
    have e₁ : g = n₁ * (n₁⁻¹ * g) := by group
    have e₂ : g = n₂ * (n₂⁻¹ * g) := by group
    have hg1 : g ∈ MiOne β ε := by
      rw [e₁]
      exact (MiOne β ε).mul_mem hn₁ (hC1 hc₁)
    have hg2 : g ∈ MiTwo β ε := by
      rw [e₂]
      exact (MiTwo β ε).mul_mem hn₂ (hC2 hc₂)
    exact ⟨hg1, hg2⟩

theorem burnsideF4m_F_4_39_of' (hcore : burnsideF4m_LieCoreSp) (hfacts : burnsideF4m_Sp2Facts)
    (htop : burnsideF4m_TopSp2) : F_4_39 :=
  burnsideF4m_F_4_39_of hcore (burnsideF4m_F439Sp2_of hfacts htop)

end F439Two

end CFSG.ASVolI
