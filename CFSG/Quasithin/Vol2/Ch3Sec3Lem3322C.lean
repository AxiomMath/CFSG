module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3322B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3322A

public section

namespace CFSG.Quasithin.H13.L3322

open Equiv Equiv.Perm
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique hiding evenWeight
open CFSG.Quasithin.H13.A7 (IsCoordAct vec natLam)
open CFSG.Quasithin.SteinbergCB (permAct7 evenWeight sevenP)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

omit [Finite G] in
theorem inf_centralizer_mul_eq {c : G} (hc : c ∈ Subgroup.centralizer (L : Set G)) (e : G) :
    L ⊓ Subgroup.centralizer ({c * e} : Set G) = L ⊓ Subgroup.centralizer ({e} : Set G) := by
  ext l
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hl => ?_
  have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.1 hc l hl
  constructor
  · intro h
    have h1 : c * (e * l) = c * (l * e) := by
      calc c * (e * l) = c * e * l := by group
        _ = l * (c * e) := h.symm
        _ = c * (l * e) := by rw [← mul_assoc, hcl, mul_assoc]
    exact (mul_left_cancel h1).symm
  · intro h
    rw [← mul_assoc, hcl, mul_assoc, h, ← mul_assoc]

omit [Finite G] in
theorem lTheta_mul_eq {c : G} (hc : c ∈ Subgroup.centralizer (L : Set G)) (e : G) :
    lTheta L (c * e) = lTheta L e := by
  rw [lTheta, lTheta, inf_centralizer_mul_eq hc]

section C23

variable {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

theorem normalizer_le_M (h5 : Stmt3_3_5) (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    {X : Subgroup G} (hX1 : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hLT : L ⊔ T ≤ Subgroup.normalizer (X : Set G)) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_M h5 h hML hLT fun hb => hX1 ?_
  have hle : X ≤ pCoreOf 2 (Subgroup.normalizer (X : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hX2
  rw [hb] at hle
  exact le_bot_iff.1 hle

theorem hypC23_centralizer (h5 : Stmt3_3_5) (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    {Lθ : Subgroup G} {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hzH : pCoreOf 2
      (Subgroup.centralizer ({z} : Set G)) ≠ ⊥)
    (hLθ : Lθ = oTwoUpper Lθ) (hLθL : Lθ ≤ L) (hLθz : Lθ ≤ Subgroup.centralizer ({z} : Set G))
    (hMz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Lθ : Set G))
    (hR : pCoreOf 2 (Lθ ⊔ T) = pCoreOf 2 (L ⊔ T)) (hR1 : pCoreOf 2 (L ⊔ T) ≠ ⊥) :
    HypC23 (Subgroup.centralizer ({z} : Set G)) (pCoreOf 2 (L ⊔ T))
      (M ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Gz := Subgroup.centralizer ({z} : Set G) with hGz
  set Mz := M ⊓ Gz with hMzdef
  set R := pCoreOf 2 (L ⊔ T) with hRdef
  have hRp : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRT : R ≤ T := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
  have hTz : T ≤ Gz := fun t ht => Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T ht) z hz).symm
  have hTMz : T ≤ Mz := le_inf h.TM hTz
  have hRGz : R ≤ Gz := hRT.trans hTz
  have hLTR : L ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hNR : Subgroup.normalizer (R : Set G) ≤ M := normalizer_le_M h5 h hML hR1 hRp hLTR
  have hLθMz : Lθ ≤ Mz := le_inf (hLθL.trans h.LM) hLθz
  have hsub : IsSubnormal Lθ Mz :=
    A4.subnormal_of_normal hLθMz ((Subgroup.normal_subgroupOf_iff_le_normalizer hLθMz).2 hMz)
  have hT' : IsSylowTwoOf T (Mz ⊓ Subgroup.normalizer (Lθ : Set G)) := by
    rw [inf_eq_left.2 hMz]
    exact isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hTMz
  have hRmax : IsMaxSignalizer Mz Lθ R := hR ▸ a4_2_5 hLθ hsub hT'
  refine ⟨?_, ⟨hRGz, hR1, ?_⟩, inf_le_right, ?_, ?_⟩
  · exact sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hzH
  ·
    refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf hRGz Subgroup.le_normalizer) inf_le_right hRp) ?_
    set P := pCoreOf 2 (Gz ⊓ Subgroup.normalizer (R : Set G)) with hPdef
    have hPp : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hPN : Gz ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (P : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hRP : R ≤ Subgroup.normalizer (P : Set G) :=
      (le_inf hRGz Subgroup.le_normalizer).trans hPN
    have hLθN : Lθ ≤ Gz ⊓ Subgroup.normalizer (R : Set G) :=
      le_inf hLθz ((hLθL.trans le_sup_left).trans hLTR)
    have hsig : IsSignalizer Mz Lθ (P ⊔ R) := by
      refine ⟨sup_le ?_ (hRT.trans hTMz), IsPGroup.to_sup_of_normal_left' hPp hRp hRP, ?_⟩
      · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
          (le_inf (inf_le_right.trans hNR) inf_le_left)
      · intro l hl
        have e1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp ((hLθN.trans hPN) hl)
        have e2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (((hLθL.trans le_sup_left).trans hLTR) hl)
        rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, e1, e2]
    have heq := hRmax.eq_of_le hsig le_sup_right
    exact le_sup_left.trans heq.le
  ·
    refine iSup₂_le fun C hCR => iSup₂_le fun hC1 hCc => ?_
    have hCN : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) := by
      have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := R) (C.subgroupOf R)
      rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h1
    exact le_inf (inf_le_right.trans (normalizer_le_M h5 h hML hC1 (hRp.to_le hCR)
      (hLTR.trans hCN))) inf_le_left
  ·
    have hRsyl : IsSylowTwoOf R (centralizerSection Mz Lθ (pCoreOf 2 Lθ)) :=
      (a4_2_4 hLθ hsub R).mp hRmax
    have hle : conjClosure R Mz ≤ centralizerSection Mz Lθ (pCoreOf 2 Lθ) := by
      refine conjClosure_le fun m hm r hr => ?_
      have hmX := hMz hm
      exact conj_mem_centralizerSection (Subgroup.le_normalizer hm) hmX
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lθ hmX) (hRsyl.1 hr)
    exact A4.isSylowTwoOf_mono hRsyl (le_conjClosure R Mz) hle

end C23

section Comp

variable {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

theorem lTheta_mem_lFamily (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hc : Coord322 T L ψ) {e : ↥⁅vPlus L T, L⁆} (he : vec ψ e = A7.vecSix)
    (heZ : (e : G) ∈ quasithinOmegaOneCenter T) :
    lTheta L e ∈ lFamily T ∧ CFSG.IsQuasisimple (↥(lTheta L e) ⧸ CFSG.pCore 2 ↥(lTheta L e)) ∧
      Nonempty ((↥(lTheta L e) ⧸ CFSG.pCore 2 ↥(lTheta L e)) ⧸
        Subgroup.center (↥(lTheta L e) ⧸ CFSG.pCore 2 ↥(lTheta L e)) ≃*
          alternatingGroup (Fin 6)) := by
  obtain ⟨hq, hA6⟩ := A7.quasisimple_Le_six (L3317.le_normalizer_commV h) hc.Lact hc.Lonto h.Lq
    he rfl
  refine ⟨?_, hq, hA6⟩
  show lTheta L e ∈ cComp (lTheta L e ⊔ T)
  refine mem_cComp_of_quasisimple_quotient
    (fun N _ hN => A7.oTwoUpper_eq_top_of_isPGroup_quotient _ N hN) hq
    (A3.subnormal_of_normal le_sup_left ?_)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
    (sup_le Subgroup.le_normalizer (T_le_normalizer_lTheta hTL heZ))

theorem le_thetaOf_L (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) : L ≤ thetaOf L := by
  have hLW := L3317.le_normalizer_commV h
  have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hmap : (L.subgroupOf L).map (natLam hLW hc.Lact) = ⊤ := by
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact A7.natLam_surjective hLW hc.Lact hc.Lonto
  refine le_thetaOf_of_altFive_le le_rfl h.Lmax.1.2.1.2.1 (natLam hLW hc.Lact)
    (mul_mem_pCore_of_natLam_eq_one hLW hc.Lact hc.Lonto h.Lq) ?_ ?_
  · rw [hmap]
    exact Subgroup.topEquiv.isSimpleGroup
  · rw [hmap]
    exact le_top

theorem lTheta_le_thetaOf (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hc : Coord322 T L ψ) {e : ↥⁅vPlus L T, L⁆} (he : vec ψ e = A7.vecSix)
    (heZ : (e : G) ∈ quasithinOmegaOneCenter T) : lTheta L e ≤ thetaOf (lTheta L e) := by
  have hLW := L3317.le_normalizer_commV h
  obtain ⟨hF, -, -⟩ := lTheta_mem_lFamily h hTL hc he heZ
  have hmap : ((lTheta L (e : G)).subgroupOf L).map (natLam hLW hc.Lact) = A7.stabA7 A7.vecSix :=
    A7.natLam_map_Le_six hLW hc.Lact hc.Lonto he
  refine le_thetaOf_of_altFive_le (lTheta_le L _) (perfect_of_mem_cComp hF) (natLam hLW hc.Lact)
    (mul_mem_pCore_of_natLam_eq_one hLW hc.Lact hc.Lonto h.Lq) ?_ ?_
  · rw [hmap]
    exact A7.isSimpleGroup_stabA7_vecSix
  · rw [hmap]
    intro σ hσ
    rw [A7.mem_stabA7, A7.permAct7_vecSix_iff]
    exact (A7.mem_altFive.1 hσ).2

theorem thetaOf_centralizer_le
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h14 : Stmt3_3_14)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h38' : A38ForSQTK) (hF : A318Facts)
    (hC27 : ASC27Statement G) (hI1 : A7.Insp1236) (hI2 : A7.InspSL2NoA6)
    (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) {e : ↥⁅vPlus L T, L⁆}
    (he : vec ψ e = A7.vecSix) (heZ : (e : G) ∈ quasithinOmegaOneCenter T) {c : G}
    (hcZ : c ∈ quasithinOmegaOneCenter T) (hcL : c ∈ Subgroup.centralizer (L : Set G)) :
    thetaOf (Subgroup.centralizer ({c * (e : G)} : Set G)) ≤ lTheta L e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  set z := c * (e : G) with hzdef
  set Gz := Subgroup.centralizer ({z} : Set G) with hGz
  set Mz := M ⊓ Gz with hMzdef
  set Lθ := lTheta L (e : G) with hLθdef
  set R := pCoreOf 2 (L ⊔ T) with hRdef
  have he1 : (e : G) ≠ 1 := by
    intro h1
    have h2 : e = 1 := Subtype.ext h1
    rw [h2, A7.vec_one] at he
    exact absurd he (by decide)
  have hzZ : z ∈ quasithinOmegaOneCenter T := Subgroup.mul_mem _ hcZ heZ
  have hz1 : z ≠ 1 := by
    intro h1
    have hec : (e : G) = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine he1 (congrArg Subtype.val (eq_one_of_centralizer hc e fun l hl => ?_))
    rw [hec]
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ hcL) l hl
  have hz2 : orderOf z = 2 := orderOf_eq_prime (sq_eq_one_of_mem_omegaOneCenter T hzZ) hz1
  have hTz : T ≤ Gz := fun t ht => Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T ht) z hzZ).symm
  have hLθeq : lTheta L z = Lθ := lTheta_mul_eq hcL _
  have hLθz : Lθ ≤ Gz := hLθeq ▸ lTheta_le_centralizer L z
  have hLθL : Lθ ≤ L := lTheta_le L _
  have hLθMz : Lθ ≤ Mz := le_inf (hLθL.trans h.LM) hLθz
  have hMz : Mz ≤ Subgroup.normalizer (Lθ : Set G) := by
    rw [← hLθeq]
    intro m hm
    have h1 : m ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :
        Set G) := CFSG.Quasithin.A4.mem_normalizer_inf (hMN hm.1) (Subgroup.le_normalizer hm.2)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    rw [← oTwoUpper_map, h1]
  have hTLθ : T ≤ Subgroup.normalizer (Lθ : Set G) := T_le_normalizer_lTheta hTL heZ
  have hR : pCoreOf 2 (Lθ ⊔ T) = R := pCoreOf_lTheta_sup h7 h hML hTL hc he heZ
  have hR1 : R ≠ ⊥ := by
    intro hb
    have heR : (e : G) ∈ R :=
      ((Hyp331.vPlus_reduced h.toSetup331).1 (L3317.commV_le_vPlus h e.2)).1
    rw [hb, Subgroup.mem_bot] at heR
    exact he1 heR
  have hH2 : pCoreOf 2 Gz ≠ ⊥ := by
    have hle : Subgroup.zpowers z ≤ pCoreOf 2 Gz := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)) ?_
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one]))
      rw [A7.normalizer_zpowers_eq_centralizer' hz2]
    intro hbot
    apply hz1
    have := hle (Subgroup.mem_zpowers z)
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  obtain ⟨hLθF, hLθq, hA6⟩ := lTheta_mem_lFamily h hTL hc he heZ
  have hLθO : Lθ = oTwoUpper Lθ := eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hLθF)
  have hC23 : HypC23 Gz R Mz :=
    hypC23_centralizer h5 h hML hzZ hH2 hLθO hLθL hLθz hMz hR hR1
  have hLocal : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke).1
  have hSylH : QuasithinUnique.IsSylowTwoOf T Gz := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hTz
  obtain ⟨K, ⟨hK, hLθK⟩, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_4_existsUnique hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved h39 hH2 hSylH hLθz hLθF
  have hKn := QuasithinUnique.Vol2Native.lemma_1_2_4_normal hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved h38 hH2 hSylH hLθF hLθK hK hTLθ
  have hKH : K ≤ Gz := le_of_mem_cComp hK
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    hTz.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).1 hKn)
  have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    obtain ⟨hcases, -, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_1_four_core hLocal
      QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved hH2 hK
    rcases hcases with hc' | h34
    · obtain ⟨eK⟩ := modO2_mulEquiv hK
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hc'.1
    · exfalso
      obtain ⟨e6⟩ := hA6
      refine A7.not_case34_of_le hI2 hK hLθK (g := e6.toMonoidHom.comp
        ((QuotientGroup.mk' _).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Lθ)))) ?_ h34
      exact e6.surjective.comp ((QuotientGroup.mk'_surjective _).comp
        (QuotientGroup.mk'_surjective _))
  have hHchar : QuasithinUnique.CharTwo Gz := by
    obtain ⟨Ts, hTs⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
      ⟨_, IsPGroup.toSylow_coe h.sylow.1 h.sylow.2⟩
    exact h.qtke.2.1 _ (A7.isTwoLocal_centralizer' hz2) ⟨Ts, hTs ▸ hTz⟩
  have hKchar : QuasithinUnique.CharTwo K :=
    A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hHchar
  have hLθK' : Lθ = K := by
    by_contra hne
    have hlt : Lθ < K := lt_of_le_of_ne hLθK hne
    have hKMz : ¬ K ≤ Mz := by
      intro hKMz
      have hn : (Lθ.subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLθK).2 (hKMz.trans hMz)
      exact hK.2.2.2 _ hlt hLθF.1 (perfect_of_mem_cComp hLθF)
        (IsSubnormal.step hLθK hn (subnormal_of_mem_cComp hK))
    have hRT : R ≤ T := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
    have hRK : R ≤ Subgroup.normalizer (K : Set G) := hRT.trans hTK
    have hconcl : C27Concl Gz R Mz K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
      hC27 _ _ _ K _ hC23 hK hKq hKchar hKMz hRK rfl
    exact hI1 G _ _ _ K _ T Lθ hC23 hK hKq hKchar hKMz hRK rfl hconcl hSylH hRT hTK
      (le_inf hLθK hLθMz) hTLθ hLθq hA6
  rw [← hLθK'] at hK hKn
  exact A7.thetaOf_le_of_A6 hF h38' h.qtke h.simple h.nonabelian hH2 hK hKn hLθq hA6

end Comp

end CFSG.Quasithin.H13.L3322
