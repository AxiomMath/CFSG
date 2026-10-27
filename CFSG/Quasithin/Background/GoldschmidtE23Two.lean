module

public import CFSG.Quasithin.Background.GoldschmidtE23NatX
public import CFSG.Quasithin.Background.GoldschmidtE23Baum
public import CFSG.Quasithin.EmptyFaithful.LRed10Frat
public import CFSG.Quasithin.Vol2.Ch3yB69
public import CFSG.Quasithin.Background.GoldschmidtE23E22
public import CFSG.Quasithin.Background.GoldschmidtE23Glue

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace GE23

theorem two_pow_mul_ne_120 (n : ℕ) : 2 ^ n * (4 ^ n - 1) ≠ 120 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h64 : 64 ≤ 4 ^ n := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have : 63 ≤ 4 ^ n - 1 := by omega
    nlinarith

section Card

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}

theorem card_isL2Natural {C : Subgroup W} {n : ℕ} (h : E2.IsL2Natural L C n) :
    Nat.card ↥L = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  have hK : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hK]
  have h4 : ((2 : ℕ) ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4]

theorem card_isA5Module (h : E2.IsA5Module L) : Nat.card ↥L = 120 := by
  obtain ⟨θ, -⟩ := h
  rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

end Card

section Lift

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M V : Subgroup Γ}

theorem twoResidual_le_sup_pCoreOf_of_noN (he22 : E2.E22StatementNoN) (h : MinParabolic H T M)
    (hsq : SQTKGroup ↥H) (hns : ¬ Group.IsSolvable ↥H) {Y : Subgroup Γ} (hYH : Y ≤ H)
    (hY : twoResidual H ≤ Y ⊔ kerIn M H) : twoResidual H ≤ Y ⊔ pCoreOf 2 H := by
  obtain ⟨⟨C, -, hHC, hqs, hcases⟩, -⟩ := he22 Γ H T M h hsq hns
  rcases hcases with ⟨hJQ, -⟩ | ⟨hTC, hJ, -⟩
  · rw [hJQ] at hY
    exact hY
  · exact LRed10.twoResidual_le_sup_pCoreOf_of_case_two h hHC hqs.1 hTC hJ hYH hY

variable (hV : IsElemAbelian 2 V)

theorem exists_twoResidual_le_of_gen (he22 : E2.E22StatementNoN) (h : MinParabolic H T M)
    (hsq : SQTKGroup ↥H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ)) (hns : ¬ Group.IsSolvable ↥H)
    {gs : MulAut (IntMod V hV)} (hgsK : gs ∈ autI hV (twoResidual H))
    (hgs : autI hV (twoResidual H) ≤
      autI hV (thompsonJ T) ⊔ (autI hV (thompsonJ T)).map (MulAut.conj gs).toMonoidHom) :
    ∃ g ∈ twoResidual H, g ∈ Subgroup.normalizer (V : Set Γ) ∧
      twoResidual H ≤ thompsonJ T ⊔ cjSub g (thompsonJ T) := by
  have hT := h.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set Γ) := hred.2.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 hgsK
  have hgN : (g : Γ) ∈ Subgroup.normalizer (V : Set Γ) := g.2
  set I₀ := thompsonJ T ⊔ cjSub (g : Γ) (thompsonJ T) with hI₀
  have hJTH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans hT.1
  have hI₀H : I₀ ≤ H := by
    refine sup_le hJTH fun z hz => ?_
    rw [mem_cjSub] at hz
    have := H.mul_mem (H.mul_mem (hKH hgK) (hJTH hz)) (H.inv_mem (hKH hgK))
    simpa [mul_assoc] using this
  have hKI : autI hV (twoResidual H) ≤ autI hV I₀ := by
    rw [hI₀, autI_sup hV ((thompsonJ_le_self T).trans (hT.1.trans hHN))
      (fun z hz => hHN (hI₀H (Subgroup.mem_sup_right hz))), ← autI_cjSub hV hgN]
    exact hgs
  have hKIJ : twoResidual H ≤ I₀ ⊔ kerIn M H := by
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (V : Set Γ) := hHN (hKH hk)
    obtain ⟨i, hiI, hik⟩ := (mem_autI hV).1 (hKI (convI_mem_autI hV hk hkN))
    have hc : (i : Γ)⁻¹ * k ∈ Subgroup.centralizer (V : Set Γ) := by
      have := (convI_eq_one_iff hV (i⁻¹ * ⟨k, hkN⟩)).1 (by rw [map_mul, map_inv, hik,
        inv_mul_cancel])
      simpa using this
    have hiH : (i : Γ) ∈ H := hI₀H hiI
    have hcJ : (i : Γ)⁻¹ * k ∈ kerIn M H :=
      h.inf_centralizer_le_kerIn hred (E2.not_le_centralizer h hJ)
        ⟨H.mul_mem (H.inv_mem hiH) (hKH hk), hc⟩
    have : k = (i : Γ) * ((i : Γ)⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hiI) (Subgroup.mem_sup_right hcJ)
  have hKIQ := twoResidual_le_sup_pCoreOf_of_noN he22 h hsq hns hI₀H hKIJ
  have hI₀N : I₀ ≤ Subgroup.normalizer (pCoreOf 2 H : Set Γ) :=
    hI₀H.trans (le_normalizer_pCoreOf 2 H)
  have hcl : conjClosure (thompsonJ T) H ≤ I₀ := by
    refine conjClosure_le fun y hy z hz => ?_
    have hH : H = twoResidual H ⊔ T := by rw [sup_comm]; exact (sup_twoResidual_eq hT).symm
    have hTK : T ≤ Subgroup.normalizer (twoResidual H : Set Γ) :=
      hT.1.trans (le_normalizer_twoResidual H)
    have hy' : y ∈ ((twoResidual H ⊔ T : Subgroup Γ) : Set Γ) := by rw [← hH]; exact hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at hy'
    obtain ⟨k, hk, t, ht, rfl⟩ := hy'
    have hk' : k ∈ ((I₀ ⊔ pCoreOf 2 H : Subgroup Γ) : Set Γ) := hKIQ hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hI₀N] at hk'
    obtain ⟨i, hi, q, hq, rfl⟩ := hk'
    have hqT : q ∈ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT hq
    have hJTN : T ≤ Subgroup.normalizer (thompsonJ T : Set Γ) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
    have hz' : (q * t) * z * (q * t)⁻¹ ∈ thompsonJ T :=
      (Subgroup.mem_normalizer_iff.mp (hJTN (T.mul_mem hqT ht)) z).mp hz
    have e : i * q * t * z * (i * q * t)⁻¹ = i * ((q * t) * z * (q * t)⁻¹) * i⁻¹ := by group
    rw [e]
    exact I₀.mul_mem (I₀.mul_mem hi (Subgroup.mem_sup_left hz')) (I₀.inv_mem hi)
  have hclJ : ¬ conjClosure (thompsonJ T) H ≤ kerIn M H := by
    intro hle
    apply hJ
    have h1 : thompsonJ T ≤ pCoreOf 2 H :=
      h.le_pCoreOf_of_isPGroup_of_le_kerIn (hT.2.1.to_le (thompsonJ_le_self T))
        ((le_conjClosure _ _).trans hle)
    exact h1.trans (MinParabolic.pCoreOf_le_centralizer hred)
  have hclH : conjClosure (thompsonJ T) H ≤ H :=
    conjClosure_le fun y hy z hz => H.mul_mem (H.mul_mem hy (hJTH hz)) (H.inv_mem hy)
  have hKcl := (h.le_kerIn_or_twoResidual_le hclH (le_normalizer_conjClosure _ _)).resolve_left
    hclJ
  exact ⟨g, hgK, hgN, hKcl.trans hcl⟩

theorem pCoreOf_top_star (hred : IsTwoReducedIn H V) :
    pCoreOf 2 (⊤ : Subgroup ↥(autI hV H)) = ⊥ := by
  set X := autI hV H with hX
  set Q : Subgroup ↥X := pCoreOf 2 (⊤ : Subgroup ↥X) with hQ
  have hQn : Q.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_pCoreOf 2 (⊤ : Subgroup ↥X)))
  have hnorm' : X ≤ Subgroup.normalizer ((Q.map X.subtype : Subgroup (MulAut (IntMod V hV))) :
      Set (MulAut (IntMod V hV))) := by
    have hnorm : ((Q.map X.subtype).subgroupOf X).Normal := by
      have e : (Q.map X.subtype).subgroupOf X = Q :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q
      rw [e]
      exact hQn
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le Q)).1 hnorm
  have hle : Q.map X.subtype ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le Q) hnorm'
      ((pCoreOf_isPGroup 2 (⊤ : Subgroup ↥X)).map X.subtype)
  have hQ' : Q.map X.subtype = ⊥ := by
    have h0 : pCoreOf 2 X = ⊥ := pCoreOf_star hV hred
    rw [h0] at hle
    exact le_bot_iff.1 hle
  exact (Subgroup.map_eq_bot_iff_of_injective Q X.subtype_injective).mp hQ'

theorem e23_two_nat (hP4 : AsB15Part4) (hComp : B69.AsB69Component)
    (hone : B69One) (h22 : E2.E22StatementNoN) (h : MinParabolic H T M) (hsq : SQTKGroup ↥H)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ))
    (hns : ¬ Group.IsSolvable ↥H)
    (hnat : ∀ L ∈ B69.blkFamily (autI hV H),
      ∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n) :
    autI hV (baum T) = autI hV (thompsonJ T) ∧
      IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) ∧
      IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) ∧
      conjClosure (omegaOneCenterOf (thompsonJ T)) (twoResidual H) =
        ⁅V, twoResidual H⁆ ⊔
          (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set Γ)) := by
  classical
  have hT := h.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set Γ) := hred.2.1
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set Γ) := hT.1.trans hHN
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_self T).trans (hT.1.trans hle))
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans hle)
  obtain ⟨hFF, hstab, hJeqH, -⟩ := B2_7_of_not_le hV hred.1 hHN hJH
  have hB := blkCtx_star hV hP4 hComp h hsq hred hJ hns
  have hmp := minParabolic_star hV h hred hHV
  have hnsX := not_isSolvable_star hV h hred hHV hns
  have hX := isRankTwoQuotient_star hV hsq hHN
  have hsqX := sqtk_star hV hsq hHN
  have hk2 : ∀ {H' : Subgroup (MulAut (IntMod V hV))} {k : ℕ}, SymBlk (autI hV H) H' k → k = 2 :=
    fun hS => hS.k_eq_two h22 hmp hsqX hX
  have hone' : ¬ IsStrongFFModule (autI hV H) :=
    hone (IntMod V hV) (fun v => IntMod.sq_eq_one v) (autI hV H) _ _ hsqX
      (minParabolic_star_top hV h hred hHV) (pCoreOf_top_star hV hred)
  have hnatC : ∀ L, CFSG.Open.IsComponentOf L (autI hV H) → NatComp (autI hV H) L := by
    intro L hL
    rcases comp_type' hB hL with hN | ⟨k, hS⟩
    · exact hN
    · exfalso
      have hk := hk2 hS
      subst hk
      have hmem : B69.blk (autI hV H) L ∈ B69.blkFamily (autI hV H) :=
        B69.mem_blkFamily.2 ⟨L, hL, rfl⟩
      obtain ⟨n, hn⟩ := hnat _ hmem
      exact two_pow_mul_ne_120 n ((card_isL2Natural hn).symm.trans
        (card_isA5Module (hS.isA5Module hB)))
  have hC : NatCtx (autI hV H) (autI hV T) (autI hV M) :=
    ⟨hB, hmp, hFF, hnsX, hone', hk2, hnatC⟩
  have hPs : IsStableFF (autI hV T) (offenderImages hV T) :=
    (B2_7_of_not_le hV hVT hTN hJ).2.1
  have hJeq : autI hV (thompsonJ T) = ffJP (offenderImages hV T) (autI hV T) :=
    autI_thompsonJ hV hTN
  have hJHeq : autI hV (thompsonJ H) = ffJ (autI hV H) := by
    rw [hJeqH, ffJP_eq_ffJ hB hmp hnsX hstab]
  have hKeq : autI hV (twoResidual H) = ffJ (autI hV H) := by
    rw [autI_twoResidual_eq hV hHN, hC.twoResidual_eq_ffJ]
  have hJN : thompsonJ T ≤ Subgroup.normalizer (V : Set Γ) := (thompsonJ_le_self T).trans hTN
  have hS : autI hV (baum T) = autI hV (thompsonJ T) := by
    refine le_antisymm ?_ (autI_mono hV (B2F.thompsonJ_le_baum T))
    have hbaum : autI hV (baum T) ≤ autI hV T ⊓ centSub (fixV (autI hV (thompsonJ T))) := by
      refine le_inf (autI_mono hV (B2F.baum_le T)) ?_
      intro φ hφ
      obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hφ
      rw [mem_centSub]
      intro u hu
      have hu2 := (mem_fixV_autI hV hJN u).1 hu
      have hE : u.val ∈ omegaOneCenterOf (thompsonJ T) :=
        inf_centralizer_thompsonJ_le hV hVT ⟨u.val_mem, hu2⟩
      have hcomm : (x : Γ) * u.val = u.val * x :=
        (Subgroup.mem_centralizer_iff.1 hx.2 u.val hE).symm
      refine IntMod.val_injective ?_
      rw [convI_apply_val, hcomm, mul_inv_cancel_right]
    have := hbaum
    rw [hJeq] at this ⊢
    rwa [hC.centSub_eq hPs] at this
  have hsyl : IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) := by
    obtain ⟨P, -, -, hJsyl, -⟩ := hC.J_sylow hPs
    rw [hJeq, hJHeq]
    exact hJsyl
  obtain ⟨gs, hgsK, hgs⟩ := hC.generation hPs
  have hgsK' : gs ∈ autI hV (twoResidual H) := by rw [hKeq]; exact hgsK
  have hgs' : autI hV (twoResidual H) ≤
      autI hV (thompsonJ T) ⊔ (autI hV (thompsonJ T)).map (MulAut.conj gs).toMonoidHom := by
    rw [hKeq, (hC.sc).2.1, hJeq]
    exact iSup₂_le fun H' hH' => hgs H' hH'
  have hgen := exists_twoResidual_le_of_gen hV h22 h hsq hred hJ hns hgsK' hgs'
  have hrank : 2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤
      rkIdx (fixV (autI hV (twoResidual H))) := by
    rw [hJeq, hKeq]
    exact hC.two_mul_rkIdx_le hPs
  have hnost : ∀ B, ¬ IsStrongFFStarOffender (autI hV T) B := fun B hB' =>
    hone' ((isStrongFFModule_iff (fun v : IntMod V hV => IntMod.sq_eq_one v)).2
      ⟨B, (isFFStarOffender_mono hmp.isSylow.1 hB'.1).isA2, hB'.2⟩)
  have hfixK : fixV (autI hV (twoResidual H)) ≤ fixV (autI hV (thompsonJ H)) := by
    rw [hKeq, hJHeq]
  have hVK : V = ⁅V, twoResidual H⁆ ⊔ (V ⊓ Subgroup.centralizer (twoResidual H : Set Γ)) := by
    have hKN : twoResidual H ≤ Subgroup.normalizer (V : Set Γ) := (twoResidual_le H).trans hHN
    have hdec : fixV (autI hV (twoResidual H)) ⊔ commSub ⊤ (autI hV (twoResidual H)) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      obtain ⟨w, hw, c, hc, rfl⟩ := blocks_split hB hmp hFF hk2 (B69.blkFamily (autI hV H))
        (fun _ h => h) v
      have hc' : c ∈ fixV (autI hV (twoResidual H)) := by
        rw [hKeq, (hC.sc).2.1]
        exact hc
      have hw' : w ∈ commSub (⊤ : Subgroup (IntMod V hV)) (autI hV (twoResidual H)) := by
        have hsub : (⨆ H' ∈ B69.blkFamily (autI hV H), commV H') ≤
            commSub (⊤ : Subgroup (IntMod V hV)) (autI hV (twoResidual H)) := by
          refine iSup₂_le fun H' hH' => ?_
          rw [commV_eq_commSub]
          have hH'K : H' ≤ autI hV (twoResidual H) := by
            rw [hKeq, (hC.sc).2.1]
            exact le_iSup₂_of_le (f := fun H'' (_ : H'' ∈ B69.blkFamily (autI hV H)) => H'')
              H' hH' le_rfl
          exact commSub_mono le_top hH'K
        exact hsub hw
      rw [mul_comm]
      exact Subgroup.mul_mem_sup hc' hw'
    refine le_antisymm ?_ (sup_le (E2.commutator_le_self hKN) inf_le_left)
    calc V = (⊤ : Subgroup (IntMod V hV)).map (E2.valHom hV) := E2.map_valHom_top.symm
      _ = (fixV (autI hV (twoResidual H)) ⊔ commSub ⊤ (autI hV (twoResidual H))).map
            (E2.valHom hV) := by rw [hdec]
      _ = (fixV (autI hV (twoResidual H))).map (E2.valHom hV) ⊔
            (commSub ⊤ (autI hV (twoResidual H))).map (E2.valHom hV) := Subgroup.map_sup _ _ _
      _ ≤ _ := by
        rw [E2.map_valHom_fixV hKN]
        exact sup_le le_sup_right (E2.map_valHom_commSub_le.trans le_sup_left)
  obtain ⟨hS3, hconj⟩ := e23_two_of_data hV h hred hJ hnost hgen hrank hS hsyl hfixK hVK
  exact ⟨hS, hsyl, hS3, hconj⟩

end Lift

end GE23

end CFSG.Quasithin
