module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsE823
public import CFSG.Quasithin.Background.HFL3Tw
public import CFSG.Quasithin.Vol2.Ch11SecE3LieSzLow
public import CFSG.Quasithin.Vol2.Ch8Sec2L825C
public import CFSG.Quasithin.Vol2.Ch8Sec2L825I

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

section L823Div

theorem card_le_two_of_inf_eq_bot_l3 {V : Type} [CommGroup V] [Finite V]
    {L M : Subgroup (MulAut V)} (hLM : Mathieu.IsOver L M) {n : ℕ} (hn : 1 ≤ n)
    (hL : BinaryNineTensor L ⊤ ⊥ n) {E : Subgroup (MulAut V)} (hEM : E ≤ M)
    (hEe : IsElemAbelian2 E) (hEL : E ⊓ L = ⊥) : Nat.card E ≤ 2 := by
  obtain ⟨K, _, _, _, hK, e, hLe, hMN⟩ := exists_model_l3nine hLM hL
  rw [← card_map_congrHom e E]
  refine L3Nine.card_le_two_of_inf_img_eq_bot hn hK ((Subgroup.map_mono hEM).trans hMN)
    ((isElemAbelian2_map_congrHom e).2 hEe) ?_
  have h := Subgroup.map_inf_eq E L (congrHom e) (congrHom_injective e)
  rw [hEL, Subgroup.map_bot] at h
  rw [← hLe]
  exact h.symm

theorem eq_one_of_odd_cent_sz_82 {X : Type} [Group X] {k : ℕ} (hX : IsSz k X) {x s : X}
    (hxo : Odd (orderOf x)) (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) (hxs : x * s * x⁻¹ = s) :
    x = 1 := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  have := CFSG.LieType.Ree.finite_suzukiGroup hK
  by_contra hx1
  have hex1 : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  have hord : ∀ y : X, orderOf (e y) = orderOf y := fun y =>
    orderOf_injective e.toMonoidHom e.injective y
  have hexo : Odd (orderOf (e x)) := by rwa [hord]
  obtain ⟨-, hodd⟩ :=
    CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK
  have hC := (hodd (e x) hex1 hexo).1
  have hes : e s ∈ Subgroup.centralizer {e x} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x * s = s * x := by
      calc x * s = x * s * x⁻¹ * x := by group
        _ = s * x := by rw [hxs]
    rw [← map_mul, ← map_mul, h1]
  have hs2' : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have h2 : orderOf (⟨e s, hes⟩ : ↥(Subgroup.centralizer {e x})) = 2 := by
    rw [Subgroup.orderOf_mk, hord, hs2']
  have h3 := orderOf_dvd_natCard (⟨e s, hes⟩ : ↥(Subgroup.centralizer {e x}))
  rw [h2] at h3
  exact (Nat.not_even_iff_odd.mpr hC) (even_iff_two_dvd.mpr h3)

variable {G : Type} [Group G]

theorem eq_one_of_cent_cartan_sz_82 {M I V X : Subgroup G} {k : ℕ} (hV : IsElemAbelian 2 V)
    (hI : IsSz k (E2.StarQuot (M ⊓ I) I)) (hV1 : E2.star (M ⊓ I) I V ≠ ⊥)
    (hXMI : X ≤ M ⊓ I) (hXK : X ⊓ kerIn (M ⊓ I) I = ⊥) (hXodd : Odd (Nat.card ↥X))
    {x : G} (hx : x ∈ X) (hxV : x ∈ Subgroup.centralizer (V : Set G)) : x = 1 := by
  set π := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hπ
  have hxI : x ∈ I := (hXMI hx).2
  have hxo : Odd (orderOf (π ⟨x, hxI⟩)) := by
    refine Odd.of_dvd_nat hXodd ((orderOf_map_dvd π _).trans ?_)
    have h1 : orderOf (⟨x, hxI⟩ : ↥I) = orderOf (⟨x, hx⟩ : ↥X) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    rw [h1]
    exact orderOf_dvd_natCard _
  obtain ⟨⟨s, hsV⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨v, hvV, rfl⟩ := hsV
  have hv : (v : G) ∈ V := hvV
  have hxs : π ⟨x, hxI⟩ * π v * (π ⟨x, hxI⟩)⁻¹ = π v := by
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    show x * (v : G) * x⁻¹ = v
    rw [(Subgroup.mem_centralizer_iff.mp hxV v hv).symm, mul_inv_cancel_right]
  have hs2 : π v ^ 2 = 1 := by
    rw [← map_pow]
    have hv2 : v ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hV.2 (v : G) hv)
    rw [hv2, map_one]
  have h1 := eq_one_of_odd_cent_sz_82 hI hxo hs1' hs2 hxs
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  have : x ∈ X ⊓ kerIn (M ⊓ I) I := ⟨hx, h1⟩
  rw [hXK, Subgroup.mem_bot] at this
  exact this

variable [Finite G]

theorem nParam_eq_of_isSz_82 {Y : Type} [Group Y] [Finite Y] {k : ℕ} (hY : IsSz k Y)
    {S : Subgroup Y} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) :
    E1.nParam (⊤ : Subgroup Y) = k := by
  have hs : IsSimpleGroup Y := (CFSG.LieType.Simplicity.fam_2b2_simplicity Y 2 k hY).2
  have hF : CFSG.generalizedFitting Y = ⊤ := generalizedFitting_eq_top_82
  have hL : IsSz k ↥(CFSG.generalizedFitting Y) := by
    rw [hF]
    exact CFSG.SectionRank.suzukiModel_of_mulEquiv Subgroup.topEquiv hY
  have hFs : IsSimpleGroup ↥(CFSG.generalizedFitting Y) := by
    rw [hF]
    exact Subgroup.topEquiv.isSimpleGroup
  have hT : quasithinIsSylowTwo S := by
    refine ⟨hS.2.1, ?_⟩
    have h2 := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h2
  exact Vol2.Ch11.SecE3.nParam_eq_of_isSz hL hFs hT (by rw [hF]; exact top_sup_eq _)

theorem exists_faithful_cartan_82 {T M V : Subgroup G} {h : G} {k : ℕ} (hV : IsElemAbelian 2 V)
    (hk : 2 ≤ k) (hhI : h ∈ ch82I V h)
    (hSyl : QuasithinUnique.IsSylowTwoOf (T ⊓ ch82I V h) (ch82I V h))
    (hMIeq : M ⊓ ch82I V h = ch82I V h ⊓ Subgroup.normalizer (V : Set G))
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hI : IsPSL 2 2 k (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) ∨
      IsSz k (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)))
    (hVZ : E2.star (M ⊓ ch82I V h) (ch82I V h) V ≤
      E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h))
    (hBor : E2.star (M ⊓ ch82I V h) (ch82I V h) (M ⊓ ch82I V h) =
      Subgroup.normalizer (E2.star (M ⊓ ch82I V h) (ch82I V h) (T ⊓ ch82I V h) :
        Set (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)))) :
    ∃ x ∈ M ⊓ ch82I V h, ∃ hxN : x ∈ Subgroup.normalizer (V : Set G),
      orderOf (convI hV ⟨x, hxN⟩) = 2 ^ k - 1 := by
  have hK : IsPGroup 2 ↥(kerIn (M ⊓ ch82I V h) (ch82I V h)) := by
    rw [hker]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (ch82I V h)
  obtain ⟨X, hXMI, hXcyc, hXc, hXK⟩ := exists_cartan_82 hK hSyl hBor hk hI
  obtain ⟨x, hxX, -, hxo⟩ := exists_zpowers_eq_82 hXcyc
  rw [hXc] at hxo
  have hNV : M ⊓ ch82I V h ≤ Subgroup.normalizer (V : Set G) := by
    rw [hMIeq]
    exact inf_le_right
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hXMI.trans hNV
  have hnt : Nontrivial (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) := by
    rcases hI with hP | hS
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 k hP).1
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 k hS).1
  have hV1 := star_ne_bot_82 hhI hker hnt
  have hodd : Odd (Nat.card ↥X) := by
    rw [hXc]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hf : ∀ y ∈ X, y ∈ Subgroup.centralizer (V : Set G) → y = 1 := by
    intro y hy hyc
    rcases hI with hP | hS
    · exact eq_one_of_cent_cartan_82 hk hP hSyl hBor hVZ hV1 hXMI hXK hodd hy hyc
    · exact eq_one_of_cent_cartan_sz_82 hV hS hV1 hXMI hXK hodd hy hyc
  exact ⟨x, hXMI hxX, hXN hxX, (orderOf_convI_82 hV hXN hf hxX).trans hxo⟩

theorem step823L3Div_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (hE214 : AS_E_2_14) : Step823L3Div := by
  intro G _ _ T L I hyp h731 h821 hc hcase H h k hH hhH hC n hrow hnk
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hLM := isOver_autI_82 hV hNM
  have hn1 : 1 ≤ n := hrow.1
  have hk : 2 ≤ k := by omega
  obtain ⟨-, hhI, hIC, hZ1, -, hSyl, hMIeq, hker, -, hcases, hVZ, hBor, hA7, -, -, -, -, -,
    h28, hchar, hTI⟩ := hC
  have hVZ' : E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) (fsuV T I) ≤
      E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
        (T ⊓ ch82I (fsuV T I) h) := by
    rw [hVZ]
    exact inf_le_left
  have hI : IsPSL 2 2 k (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) ∨
      IsSz k (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) := by
    rcases hcases with ⟨h21, -⟩ | hP | hS
    · omega
    · exact Or.inl hP
    · exact Or.inr hS
  obtain ⟨x, hxMI, hxN, hxo⟩ := exists_faithful_cartan_82 hV hk hhI hSyl hMIeq hker hI hVZ' hBor
  obtain ⟨-, h6, h7, -, -⟩ :=
    e214_82 hE214 hV hhI hIC hZ1 h28 hchar hTI (Or.inr (hI.imp (⟨k, ·⟩) (⟨k, ·⟩)))
  obtain ⟨hAel, hAN⟩ := ch82A_facts_82 hV hA7
  have hAel2 := isElemAbelian2_autI hV hAel hAN
  have hAM : autI hV (ch82A (fsuV T I) h) ≤ autI hV ⊤ := autI_mono hV le_top
  by_cases hR : autI hV (ch82A (fsuV T I) h) ⊓ autI hV (fsuL0 T L) = ⊥
  ·
    exfalso
    have hc2 := card_le_two_of_inf_eq_bot_l3 hLM hn1 hrow.2 hAM hAel2 hR
    have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨hAc, -⟩ := h7 k hI (hc2.trans (by omega))
      (one_lt_qOf_82 hV (ch82I (fsuV T I) h) (not_isFFModule_of_hyp702 hyp hV hNM))
    omega
  ·
    set xb := convI hV ⟨x, hxN⟩ with hxb
    have hxbM : xb ∈ autI hV ⊤ := convI_mem_autI hV (Subgroup.mem_top x) hxN
    have hxbA : xb ∈ Subgroup.normalizer
        (autI hV (ch82A (fsuV T I) h) : Set (MulAut (IntMod (fsuV T I) hV))) :=
      h6 (convI_mem_autI hV hxMI.2 hxN)
    have hxbL : xb ∈ Subgroup.normalizer
        (autI hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) hV))) := hLM.2 hxbM
    have hxbR : xb ∈ Subgroup.normalizer ((autI hV (ch82A (fsuV T I) h) ⊓
        autI hV (fsuL0 T L) : Subgroup (MulAut (IntMod (fsuV T I) hV))) :
          Set (MulAut (IntMod (fsuV T I) hV))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hxbA g,
        Subgroup.mem_normalizer_iff.mp hxbL g]
    have hodd : Odd (orderOf xb) := by
      rw [hxo]
      exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    have h823 := (hL3Nine823_holds (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤)
      hLM n hn1 hrow.2).2 xb hxbM hodd _ inf_le_right
      ((IsElemAbelian2.isPGroup hAel2).to_le inf_le_left) hR hxbR
    rwa [hxo] at h823

end L823Div

end CFSG.Quasithin.H13
