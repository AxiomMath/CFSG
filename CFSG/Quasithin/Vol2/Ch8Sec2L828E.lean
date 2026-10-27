module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828C
public import CFSG.Quasithin.Vol2.Ch8Sec2L828D
public import CFSG.Quasithin.Vol2.Ch7Lem734Loc
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210F
public import CFSG.Quasithin.Vol2.Ch8Sec2L828B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section L828E

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem setup_828 (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hyp : Hyp7_0_2 G T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hC : Concl822 T L I H h k) (hC5 : Concl825 T L I h k) :
    IsElemAbelian 2 (fsuV T I) ∧ fsuL0 T L = L ∧ T ≤ Subgroup.normalizer (L : Set G) ∧
      L ≤ Subgroup.normalizer (fsuV T I : Set G) ∧ ch82A (fsuV T I) h ≤ T ∧
      ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G) ∧ IsPGroup 2 ↥(ch82A (fsuV T I) h) ∧
      IsElemAbelian 2 (ch82A (fsuV T I) h) ∧
      T ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ∧
      ch82I (fsuV T I) h ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) ∧
      ch82U (fsuV T I) h ≠ ⊥ ∧
      T ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G) := by
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (le_fsuL0 T L).trans (le_sup_left.trans hN)
  obtain ⟨-, -, -, hZ1, -, hSyl, -, -, -, -, -, -, hA7, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, hTU, -, -, hUZ, -, hIU⟩ := hC5
  have hAT : ch82A (fsuV T I) h ≤ T := fun x hx =>
    (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl hx.2).1
  have hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hA7]
    exact inf_le_right
  have hTp : IsPGroup 2 ↥T := hyp.fsu.sylow.1
  have hLUT : T ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G) := by
    intro t ht
    apply normalizer_le_normalizer_perfectCore
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hTL ht, Subgroup.le_normalizer (hTU ht)⟩
  exact ⟨hV, hL0, hTL, hLN, hAT, hAN, hAT.trans hTL, hTp.to_le hAT,
    isElemAbelian_of_le_conjSub_82 hV inf_le_left, hTU, hIU, hUZ ▸ hZ1, hLUT⟩

omit [Finite G] in
theorem autSub_eq_bot_828 {X V U : Subgroup G} [IsMulCommutative ↥V]
    (hXU : X ≤ Subgroup.centralizer (U : Set G)) :
    autSub (autOn X V) (U.subgroupOf V) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
  obtain ⟨x, hx, hgx⟩ := Subgroup.mem_map.mp hg
  have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun w => ?_
  have hw : ((w : ↥V) : G) ∈ U := Subgroup.mem_subgroupOf.mp w.2
  apply Subtype.ext
  apply Subtype.ext
  show (((g : MulAut ↥V) (w : ↥V) : ↥V) : G) = ((w : ↥V) : G)
  rw [← hgx, CFSG.QuasithinUnique.Setup.coe_conjAct_apply,
    ← Subgroup.mem_centralizer_iff.mp (hXU hxX) _ hw, mul_inv_cancel_right]

theorem lu_facts_828 (hLU : HLU82) (hcard : Mathieu.StmtH13Card) (hyp : Hyp7_0_2 G T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) {h : G} {k : ℕ}
    (hC5 : Concl825 T L I h k) (hV : IsElemAbelian 2 (fsuV T I)) (hL0 : fsuL0 T L = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h)) (hAe : IsElemAbelian 2 (ch82A (fsuV T I) h))
    (hLUT : T ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G)) :
    ch82LU L (ch82U (fsuV T I) h) ∈ lFamily T ∧
      ¬ ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) ∧
      (Row711M24Cocode T L I → autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)) = ⊤) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, h5, h6, h3⟩ := hlu82_82 hLU hcard hrow hL0 hV hLN hC5 hAN hAL hAp hAe
  have hfix : fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      (ch82U (fsuV T I) h).subgroupOf (fsuV T I) := fixV_autOn_82 hAN
  have hLUN : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hLN)
  have hperfL : ⁅L, L⁆ = L := hyp.fsu.maximal.1.2.1.2.1
  have hsolv : Group.IsSolvable ↥(ch82LU L (ch82U (fsuV T I) h) ⊓
      Subgroup.centralizer (fsuV T I : Set G)) := by
    have hLs := isSolvable_inf_centralizer_828 hyp.fsu.quasisimple hperfL hLN
      (not_le_centralizer_fsuV hyp hTL)
    have hle : ch82LU L (ch82U (fsuV T I) h) ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
        L ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      inf_le_inf_right _ ((perfectCore_le _).trans inf_le_left)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hsub : IsSubnormal (ch82LU L (ch82U (fsuV T I) h)) (ch82LU L (ch82U (fsuV T I) h) ⊔ T) :=
    A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hLUT))
  have hfam : ch82LU L (ch82U (fsuV T I) h) ∈ lFamily T :=
    mem_cComp_of_autOn_828 (perfectCore_perfect _) hLUN hsolv hq hsub
  have hne : autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
      (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) ≠ ⊥ := by
    rcases hrow with hr | hr | hr | hr
    · exact ne_bot_of_alternatingNatural_828 (Or.inl rfl) (h5 (Or.inl hr))
    · exact ne_bot_of_alternatingNatural_828 (Or.inl rfl) (h5 (Or.inr hr))
    · exact ne_bot_of_alternatingNatural_828 (Or.inr rfl) (h6 hr)
    ·
      rw [h3 hr]
      intro htop
      obtain ⟨-, -, -, hU3⟩ := hC5.2.2.2.2.2.2.1 hr
      have hU2 : IsPGroup 2 ↥(ch82U (fsuV T I) h) := fun x => ⟨1, Subtype.ext (by
        rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
        exact hV.2 _ x.2.1)⟩
      obtain ⟨n, hn⟩ := hU2.exists_card_eq
      have hn3 : n = 3 := by
        rw [← hU3]
        unfold rk
        rw [hn, padicValNat.prime_pow]
      have h4 : 4 ≤ Nat.card ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) := by
        have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
        rw [hfix, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv, hn, hn3]
        norm_num
      have hW : ∀ w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))), w * w = 1 := by
        intro w
        apply Subtype.ext
        apply Subtype.ext
        show ((w : ↥(fsuV T I)) : G) * ((w : ↥(fsuV T I)) : G) = 1
        rw [← pow_two]
        exact hV.2 _ (w : ↥(fsuV T I)).2
      obtain ⟨φ, hφ⟩ := exists_mulAut_ne_one_828 hW h4
      have hφ' : φ ∈ (⊥ : Subgroup (MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))))) :=
        htop ▸ Subgroup.mem_top φ
      exact hφ (Subgroup.mem_bot.mp hφ')
  refine ⟨hfam, fun hC => hne ?_, fun hr => ?_⟩
  · rw [hfix]
    exact autSub_eq_bot_828 hC
  · rw [← hfix]
    exact h3 hr

theorem exists_k_828 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hyp : Hyp7_0_2 G T L I) {U B : Subgroup G} (hU2 : IsPGroup 2 ↥U) (hU1 : U ≠ ⊥)
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hB : B ∈ lFamily T) (hBT : T ≤ Subgroup.normalizer (B : Set G)) :
    ∃ K : Subgroup G, K ∈ cComp (Subgroup.normalizer (U : Set G)) ∧ B ≤ K ∧
      (K.subgroupOf (Subgroup.normalizer (U : Set G))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : pCoreOf 2 (Subgroup.normalizer (U : Set G)) ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff, ← hbot]
    exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 U hU2
  have hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (U : Set G)) :=
    ⟨hTU, hyp.fsu.sylow.1, fun h2 =>
      hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTU))⟩
  obtain ⟨K, hK, hBK⟩ := lemma_1_2_4_exists hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37
    h39 hH hS hBU hB
  exact ⟨K, hK, hBK, lemma_1_2_4_normal hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38
    hH hS hB hBK hK hBT⟩

theorem eq_of_autSub_eq_top_828 {V U B K T : Subgroup G} [IsMulCommutative ↥V] (hUV : U ≤ V)
    (hB : B ∈ cComp (B ⊔ T)) (hBK : B ≤ K) (hK : K ∈ cComp (Subgroup.normalizer (U : Set G)))
    (hKn : (K.subgroupOf (Subgroup.normalizer (U : Set G))).Normal)
    (hTS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (U : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hBC : ¬ B ≤ Subgroup.centralizer (U : Set G))
    (htop : autSub (autOn B V) (U.subgroupOf V) = ⊤) : K = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := le_of_mem_cComp hK
  have hNC : Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hKBC : ∀ k ∈ K, ∃ b ∈ B, b⁻¹ * k ∈ K ⊓ Subgroup.centralizer (U : Set G) := by
    intro k hk
    let e : ↥(U.subgroupOf V) ≃* ↥U := Subgroup.subgroupOfEquivOfLe hUV
    let ψ : MulAut ↥(U.subgroupOf V) := (e.trans (conjAct U ⟨k, hKN hk⟩)).trans e.symm
    have hψ : ψ ∈ autSub (autOn B V) (U.subgroupOf V) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨g, hg, hgψ⟩ := mem_autSub.mp hψ
    obtain ⟨b, hb, hgb⟩ := Subgroup.mem_map.mp hg
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    refine ⟨b, hbB, Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem (hBK hbB)) hk, ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := congrArg (fun φ : MulAut ↥(U.subgroupOf V) =>
      (((φ ⟨⟨u, hUV hu⟩, Subgroup.mem_subgroupOf.mpr hu⟩ : ↥(U.subgroupOf V)) : ↥V) : G)) hgψ
    have h2 : (((resHom (U.subgroupOf V) g ⟨⟨u, hUV hu⟩, Subgroup.mem_subgroupOf.mpr hu⟩ :
        ↥(U.subgroupOf V)) : ↥V) : G) = b * u * (b : G)⁻¹ := by
      rw [resHom_apply, ← hgb, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
    have h3 : (((ψ ⟨⟨u, hUV hu⟩, Subgroup.mem_subgroupOf.mpr hu⟩ : ↥(U.subgroupOf V)) : ↥V) :
        G) = k * u * k⁻¹ := by
      show (((conjAct U ⟨k, hKN hk⟩ (e ⟨⟨u, hUV hu⟩, Subgroup.mem_subgroupOf.mpr hu⟩)) : ↥U) :
        G) = k * u * k⁻¹
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
      rfl
    rw [h2, h3] at h1
    calc u * ((b : G)⁻¹ * k) = (b : G)⁻¹ * (b * u * (b : G)⁻¹) * k := by group
      _ = (b : G)⁻¹ * (k * u * k⁻¹) * k := by rw [h1]
      _ = (b : G)⁻¹ * k * u := by group
  have hCn : ((K ⊓ Subgroup.centralizer (U : Set G)).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf Subgroup.le_normalizer (hKN.trans hNC)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hCne : K ⊓ Subgroup.centralizer (U : Set G) ≠ K := fun e =>
    hBC (hBK.trans (by rw [← e]; exact inf_le_right))
  have hKBO := le_sup_pCoreOf_828 hq (perfect_of_mem_cComp hK) hBK inf_le_left hCn hCne hKBC
  have hNK : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mp hKn
  have hOT : pCoreOf 2 K ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKN)
      (hNK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)).trans
      (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTS)
  exact eq_of_le_sup_828 hB hK hBK (hKBO.trans (sup_le_sup_left hOT B))

end L828E

end CFSG.Quasithin.H13
