module

public import CFSG.Quasithin.Vol2.Ch12Sec5L8
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3K1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125
open scoped commutatorElement

namespace S125K1

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem exists_lift_of_prod {M L₁ : Subgroup G}
    (π : ↥M →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hπ : Function.Surjective π) (hker : IsPGroup 2 ↥π.ker) (hL₁M : L₁ ≤ M)
    (hL₁n : M ≤ Subgroup.normalizer (L₁ : Set G)) (hperf : ⁅L₁, L₁⁆ = L₁)
    (hL₁2 : ¬ IsPGroup 2 ↥L₁) :
    (∀ x, ∃ l ∈ L₁.subgroupOf M, π l = (x, 1)) ∧ ∀ l ∈ L₁.subgroupOf M, (π l).2 = 1 := by
  set L' : Subgroup ↥M := L₁.subgroupOf M with hL'
  have hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hL₁M).mpr hL₁n
  have hL'map : L'.map M.subtype = L₁ := by
    rw [hL', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL₁M]
  have hL'p : ⁅L', L'⁆ = L' := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, hL'map, hperf]
  set P := L'.map π with hP
  have hPn : P.Normal := hL'n.map π hπ
  have hPp : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hL'p]
  have hPsnd := S125Fin.le_ker_snd_of_perfect hPp
  have hP1 : P.map (MonoidHom.fst _ _) = ⊤ := by
    have hn : (P.map (MonoidHom.fst (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))).Normal :=
      hPn.map _ Prod.fst_surjective
    have hs := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (P.map (MonoidHom.fst (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))) with h | h
    · exfalso
      apply hL₁2
      have hPb : P = ⊥ := by
        rw [eq_bot_iff]
        intro p hp
        have h1 : p.1 ∈ P.map (MonoidHom.fst _ _) := ⟨p, hp, rfl⟩
        rw [h, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.mpr (Prod.ext h1 (hPsnd hp))
      have hL'k : L' ≤ π.ker := by
        intro x hx
        have : π x ∈ P := ⟨x, hx, rfl⟩
        rw [hPb, Subgroup.mem_bot] at this
        exact this
      intro l
      obtain ⟨j, hj⟩ := hker ⟨⟨l, hL₁M l.2⟩, hL'k (show ⟨(l : G), hL₁M l.2⟩ ∈ L' from l.2)⟩
      refine ⟨j, Subtype.ext ?_⟩
      have := congrArg (fun z : ↥π.ker => ((z : ↥M) : G)) hj
      simpa using this
    · exact h
  refine ⟨fun x => ?_, fun l hl => hPsnd ⟨l, hl, rfl⟩⟩
  obtain ⟨p, hp, hpx⟩ : x ∈ P.map (MonoidHom.fst _ _) := hP1 ▸ Subgroup.mem_top x
  obtain ⟨l, hl, rfl⟩ := hp
  exact ⟨l, hl, Prod.ext hpx (hPsnd ⟨l, hl, rfl⟩)⟩

theorem l1_inner (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) {t : G}
    (ht : t ∈ T) : ∃ b ∈ li L F.V1, ∀ x ∈ li L F.V1,
      (b⁻¹ * t) * x * (b⁻¹ * t)⁻¹ * x⁻¹ ∈ pCoreOf 2 (li L F.V1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have h2 := lemma12_5_2_of h1222 G T L V F hH
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hf.normalizes hf.T_le
  have hMV : mi T L F.V1 ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hLTV
  have hC : IsPGroup 2 ↥(mi T L F.V1 ⊓ Subgroup.centralizer (V : Set G)) :=
    (S125Tr2.isPGroup_centralizer hH hf).to_le (inf_le_inf_right _ inf_le_left)
  obtain ⟨ψ⟩ := h2.1.2.1
  obtain ⟨π, hπ, hker⟩ := S125Fin.exists_surj_of_quot hMV hC ψ
  have hTV₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hTM : T ≤ mi T L F.V1 := le_inf le_sup_right hTV₁
  have hL₁M : li L F.V1 ≤ mi T L F.V1 :=
    (Subgroup.map_subtype_le _).trans (inf_le_inf_right _ le_sup_left)
  have hML : mi T L F.V1 ≤ Subgroup.normalizer (li L F.V1 : Set G) :=
    S125K6.le_normalizer_li (inf_le_left.trans (sup_le Subgroup.le_normalizer hH.hyp.normalizes))
      inf_le_right
  have hperf : ⁅li L F.V1, li L F.V1⁆ = li L F.V1 := S125K6.commutator_li L _
  have hB := l1_mem_lFamily h1222 F hH
  have hL₁2 : ¬ IsPGroup 2 ↥(li L F.V1) := U3.not_isPGroup_of_perfect hperf hB.1
  obtain ⟨hPx, hPsnd⟩ := exists_lift_of_prod π hπ hker hL₁M hML hperf hL₁2
  set t' : ↥(mi T L F.V1) := ⟨t, hTM ht⟩ with ht'
  obtain ⟨l, hl, hlx⟩ := hPx (π t').1
  have hlL : ((l : ↥(mi T L F.V1)) : G) ∈ li L F.V1 := hl
  refine ⟨(l : G), hlL, fun x hx => ?_⟩
  set x' : ↥(mi T L F.V1) := ⟨x, hL₁M hx⟩ with hx'
  have hcomm : π ((l⁻¹ * t') * x' * (l⁻¹ * t')⁻¹ * x'⁻¹) = 1 := by
    have hx2 : (π x').2 = 1 := hPsnd x' hx
    simp only [map_mul, map_inv, hlx]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.fst_inv, Prod.fst_one]
      group
    · simp only [Prod.snd_mul, Prod.snd_inv, Prod.snd_one, hx2]
      group
  set Q : Subgroup G := π.ker.map (mi T L F.V1).subtype ⊓ li L F.V1 with hQ
  have hQ2 : IsPGroup 2 ↥Q :=
    (hker.map (mi T L F.V1).subtype).to_le inf_le_left
  have hQn : li L F.V1 ≤ Subgroup.normalizer (Q : Set G) := by
    intro y hy
    have hyM := hL₁M hy
    have hN1 :
        y ∈ Subgroup.normalizer ((π.ker.map (mi T L F.V1).subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨⟨y, hyM⟩ * w * ⟨y, hyM⟩⁻¹, (π.normal_ker).conj_mem w hw _, ?_⟩
        simp
      · intro hz
        obtain ⟨w, hw, hwz⟩ := hz
        refine ⟨⟨y, hyM⟩⁻¹ * w * ⟨y, hyM⟩, ?_, ?_⟩
        · have := (π.normal_ker).conj_mem w hw (⟨y, hyM⟩⁻¹)
          simpa using this
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hwz ⊢
          rw [hwz]
          group
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hN1, Subgroup.le_normalizer hy⟩
  have hxy : ((l : G)⁻¹ * t) * x * ((l : G)⁻¹ * t)⁻¹ * x⁻¹ ∈ li L F.V1 := by
    have hlt : (l : G)⁻¹ * t ∈ Subgroup.normalizer (li L F.V1 : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hlL)) (hML (hTM ht))
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hlt x).mp hx)
      (Subgroup.inv_mem _ hx)
  have hmem : ((l : G)⁻¹ * t) * x * ((l : G)⁻¹ * t)⁻¹ * x⁻¹ ∈ Q :=
    ⟨⟨(l⁻¹ * t') * x' * (l⁻¹ * t')⁻¹ * x'⁻¹, hcomm, rfl⟩, hxy⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hQn hQ2 hmem

open L1293 in
theorem list_of
    (h1222 : Stmt12_2_2) (h36 : A36ForSQTK) (h312 : A312ForSQTK) (hDyn : DynkinFact1293)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G))) (hLK : li L F.V1 < K₁)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G)) :
    IsList1293Two (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨ IsList1293Three (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have hTG₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hTL₁ := T_le_normalizer_l1 h1222 F hH
  have hBH : li L F.V1 ≤ Subgroup.normalizer (F.V1 : Set G) := S125K6.li_le_normalizer L _
  have hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (F.V1 : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTG₁
  have hcard := S125L9a.card_V1 F
  have hO : pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) ≠ ⊥ := by
    intro hb
    have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 F.V1 (IsPGroup.of_card (n := 1)
      (by rw [hcard, pow_one]))
    rw [hb, le_bot_iff] at h1
    rw [h1, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hB := l1_mem_lFamily h1222 F hH
  have hKc : K₁ ∈ cComp (Subgroup.normalizer (F.V1 : Set G)) := hK
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hKc
  have hBK : modO2Image (Subgroup.normalizer (F.V1 : Set G)) (li L F.V1) ≤
      modO2Image (Subgroup.normalizer (F.V1 : Set G)) K₁ :=
    Subgroup.map_mono (fun x hx => hLK.le hx)
  obtain ⟨eL⟩ := S125Fin.lOne_quot_equiv h1222 hH (lemma12_5_2_of h1222 G T L V F hH) hTL₁
  obtain ⟨eB⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hBH
  have hD := data1293_of (B := modO2Image (Subgroup.normalizer (F.V1 : Set G)) (li L F.V1))
    (k := 3) (Or.inl rfl) (eB.symm.trans eL)
  obtain ⟨eK⟩ := modO2_mulEquiv hKc
  rcases lemma_1_2_4_list hyp.qtke hyp.simple hyp.nonabelian h312 hO hS hBH hB hKc hLK.le with
    heq | hcase | hnq
  ·
    exfalso
    refine hLK.ne (eq_of_modO2Image_eq hLK.le hK₁G₁ (perfect_of_mem_cComp hKc) ?_ heq)
    have hP : pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) ≤ T :=
      pCoreOf_two_le_of_isSylowTwoOf hS
    exact L1295.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer (hP.trans hTL₁)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _) le_sup_right le_rfl
  ·
    have hnoDyn : ¬ DynkinPair1293
        (modO2Image (Subgroup.normalizer (F.V1 : Set G)) (li L F.V1))
        (modO2Image (Subgroup.normalizer (F.V1 : Set G)) K₁) := by
      intro hpair
      have hTbar : QuasithinUnique.IsSylowTwoOf
          (modO2Image (Subgroup.normalizer (F.V1 : Set G)) T) ⊤ :=
        isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS) _
          (QuotientGroup.mk'_surjective _)
      have hKn : (modO2Image (Subgroup.normalizer (F.V1 : Set G)) K₁).Normal :=
        Subgroup.Normal.map ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₁G₁).2 hK₁n) _
          (QuotientGroup.mk'_surjective _)
      have hSK := F7.isSylowTwoOf_inf_normal hTbar le_top (le_top.trans
        (Subgroup.normalizer_eq_top
          (H := modO2Image (Subgroup.normalizer (F.V1 : Set G)) K₁)).ge)
      obtain ⟨s, hs, hout⟩ := hDyn _ _ _ _ hBK hpair hSK
        (inf_le_left.trans (modO2Image_le_normalizer hTL₁))
      obtain ⟨t, ht, rfl⟩ := hs.1
      have htT : (t : G) ∈ T := ht
      obtain ⟨b, hb, hbx⟩ := l1_inner h1222 F hH htT
      obtain ⟨xbar, hxbar, hnot⟩ := hout _ ⟨⟨b, hBH hb⟩, hb, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hxbar
      have hxL : (x : G) ∈ li L F.V1 := hx
      apply hnot
      have hc : ⁅(t : G) * b⁻¹, (x : G)⁆ ∈ pCoreOf 2 (li L F.V1) := by
        have hy : b⁻¹ * (x : G) * b ∈ li L F.V1 :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) hxL) hb
        have h1 := hbx _ hy
        have h2 := (Subgroup.mem_normalizer_iff.mp
          (LieType.BorelTits.le_normalizer_pCoreOf 2 (li L F.V1) hb) _).mp h1
        rw [commutatorElement_def]
        convert h2 using 1
        group
      have hPbar : modO2Image (Subgroup.normalizer (F.V1 : Set G)) (pCoreOf 2 (li L F.V1)) ≤
          pCoreOf 2 (modO2Image (Subgroup.normalizer (F.V1 : Set G)) (li L F.V1)) :=
        LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          (Subgroup.map_mono (fun y hy => LieType.BorelTits.pCoreOf_le 2 (li L F.V1) hy))
          (modO2Image_le_normalizer (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
          ((A4.isPGroup_subgroupOf_of_le ((LieType.BorelTits.pCoreOf_le 2 _).trans hBH)
            (LieType.BorelTits.pCoreOf_isPGroup 2 _)).map _)
      refine hPbar ⟨⁅t * (⟨b, hBH hb⟩ : ↥(Subgroup.normalizer (F.V1 : Set G)))⁻¹, x⁆, ?_, ?_⟩
      · show ((⁅t * (⟨b, hBH hb⟩ : ↥(Subgroup.normalizer (F.V1 : Set G)))⁻¹, x⁆ :
          ↥(Subgroup.normalizer (F.V1 : Set G))) : G) ∈ pCoreOf 2 (li L F.V1)
        simpa [commutatorElement_def] using hc
      · rw [map_commutatorElement, map_mul, map_inv]
    rcases hD.list_of_case hnoDyn hcase with h2 | ⟨-, h3⟩
    · exact Or.inl (h2.of_mulEquiv eK.symm)
    · exact Or.inr (h3.of_mulEquiv eK.symm)
  ·
    right
    have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hO
    obtain ⟨-, hSL⟩ := hD.list_of_nonquasi hBK (h36 _ hQ _ (modO2Image_mem_cComp hKc)) hnq
    have h3 : IsList1293Three ↥(modO2Image (Subgroup.normalizer (F.V1 : Set G)) K₁) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hSL))))))
    exact h3.of_mulEquiv eK.symm

end S125K1

end CFSG.Quasithin.H13
