module

public import CFSG.Quasithin.Vol2.Ch3xC58NSLocal
public import CFSG.Quasithin.Vol2.Ch3xC58NSBlocks
public import CFSG.Quasithin.Vol2.Ch3xC58NSGlobal
public import CFSG.Quasithin.Vol2.Ch3xC58

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.AppC CFSG.QuasithinUnique.A5.Delta5 CFSG.Quasithin.C58 Subgroup

variable {G : Type} [Group G] [Finite G]

namespace GammaSetupNS

variable {H T R K₁ : Subgroup G} {t x : G} (hs : GammaSetupNS H T R K₁ t x)
include hs

theorem comm_J_γ (h126 : TheoremC126) (hSQ : IsSQTKTC H) {M : Subgroup G}
    (hmin : MinParabolic H T M) : ⁅K₁, thompsonJ (T ⊓ normalizer (K₁ : Set G))⁆ = K₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  have hT₁2 : IsPGroup 2 T₁ := hs.sylow.1.to_le inf_le_left
  have hT₁N : T₁ ≤ normalizer (K₁ : Set G) := inf_le_right
  have hminX := hs.minParabolic_γ hmin
  have hXH : K₁ ⊔ T₁ ≤ H := sup_le hs.cfg.le_H (inf_le_left.trans hs.TH)
  have hKX : K₁ ≤ K₁ ⊔ T₁ := le_sup_left
  have hT₁1 : T₁ ≠ ⊥ := by
    intro h
    have h1 := hs.cfg.short.2.2.2.2.1
    have h2 : blockU K₁ = ⊥ := le_bot_iff.mp (h ▸ hs.U_le_T₁)
    rw [h2] at h1
    exact (not_lt_bot h1).elim
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) theoremC118
  obtain ⟨h1ne, h1Z, h1char, h2ne, h2B, h2char, -⟩ := hC.pair T₁ hT₁2 hT₁1
  rcases h126 G C₁ C₂ hC (K₁ ⊔ T₁) T₁ (C1GN.IsSQTKTC.mono hXH hSQ) hminX.isSylow hs.charTwo_γ
      (minParabolic_iff.mp hminX).1 with h1 | h2 | ⟨r, K, -, hK, -, hres, -, -⟩
  · exfalso
    have hC₁T : C₁ T₁ ≤ T₁ := h1Z.trans (C1GN.omegaOneCenterOf_le_self T₁)
    refine hs.no_common_normal hC₁T h1ne
      (normalizer_le_normalizer_of_characteristic hC₁T h1char) ?_
    have hXC : K₁ ⊔ T₁ ≤ centralizer (C₁ T₁ : Set G) :=
      Subgroup.le_centralizer_iff.mpr (h1.trans inf_le_right)
    exact (hKX.trans hXC).trans (Subgroup.centralizer_le_normalizer _)
  · exfalso
    have hC₂T : C₂ T₁ ≤ T₁ := h2B.trans (C1GN.baum_le T₁)
    exact hs.no_common_normal hC₂T h2ne
      (normalizer_le_normalizer_of_characteristic hC₂T
        (C1GN.characteristic_subgroupOf_trans (C1GN.baum_le T₁) h2B
          (C1GN.characteristic_baum T₁) h2char)) (hKX.trans h2)
  · have hres' : twoResidual (K₁ ⊔ T₁) = K₁ := by
      rw [F6.twoResidual_eq_oTwoUpper]
      refine le_antisymm (oTwoUpper_le_of_le_sup le_rfl hT₁2 hT₁N) ?_
      calc K₁ = oTwoUpper K₁ := C1Pack.isShort2_eq_oTwoUpper hs.cfg.short
        _ ≤ oTwoUpper (K₁ ⊔ T₁) := oTwoUpper_mono hKX
    have hJN : thompsonJ T₁ ≤ normalizer (K₁ : Set G) :=
      (GammaExtra.thompsonJ_le_self T₁).trans hT₁N
    refine le_antisymm (C1GN.commutator_le_of_le_normalizer hJN) ?_
    have hKi : ∀ i, K i ≤ K₁ := fun i => by rw [← hres', hres]; exact le_iSup K i
    calc K₁ = ⨆ i, K i := hres'.symm.trans hres
      _ ≤ ⁅K₁, thompsonJ T₁⁆ := iSup_le fun i =>
        calc K i = ⁅K i, thompsonJ T₁⁆ := (hK i).2.symm
          _ ≤ ⁅K₁, thompsonJ T₁⁆ := Subgroup.commutator_mono (hKi i) le_rfl

theorem facts_γ (h126 : TheoremC126) (hSQ : IsSQTKTC H) {M : Subgroup G}
    (hmin : MinParabolic H T M) :
    blockU K₁ ≤ baum (T ⊓ normalizer (K₁ : Set G)) ∧
      (∀ v ∈ baum (T ⊓ normalizer (K₁ : Set G)) ⊓ centralizer (blockU K₁ : Set G),
        ∃ u ∈ blockU K₁, ∃ d ∈ centralizer (K₁ : Set G), v = u * d) ∧
      (∀ y ∈ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G),
        Odd (orderOf y) → conjSubgroup (blockU K₁) y ≤ centralizer (blockU K₁ : Set G)) ∧
      ∃ e ∈ blockU K₁, e ∈ conjSubgroup (blockU K₁) x ∧ e ∉ blockZ K₁ ∧
        ∀ y ∈ T ⊓ normalizer (K₁ : Set G), y * e = e * y := by
  have hJγ := hs.comm_J_γ h126 hSQ hmin
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  set S := baum T₁ with hS
  have hT₁2 : IsPGroup 2 T₁ := hs.sylow.1.to_le inf_le_left
  have hT₁N : T₁ ≤ normalizer (K₁ : Set G) := inf_le_right
  have hS2 : IsPGroup 2 S := hT₁2.to_le inf_le_left
  have hSN : S ≤ normalizer (K₁ : Set G) := inf_le_left.trans hT₁N
  have hNS : normalizer (T₁ : Set G) ≤ normalizer (S : Set G) := normalizer_le_normalizer_baum T₁
  have hxS : x ∈ normalizer (S : Set G) := hNS hs.xN
  have hUK : blockU K₁ ≤ K₁ := blockU_le hs.cfg.short
  rcases hs.cfg.typ with ⟨n, hn, hlin⟩ | h5
  · obtain ⟨hsyl, hc542⟩ := lin2_single hs.cfg.short hn hlin hT₁2 hT₁N hs.syl₁ hJγ
    have hUS := (rank1_of_lin2 hs.cfg.short hn hlin hS2 hSN hsyl hc542).2.2.1
    have hP := pairDataZ_of_lin2 hs.cfg.short hn hlin hS2 hSN hsyl hc542 hxS hs.xU
    refine ⟨hUS, fun v hv => ?_, fun y hy hodd => ?_, ?_⟩
    · obtain ⟨u, hu, d, hd, rfl⟩ := hP.mem_UD hv
      exact ⟨u, hu, d, hd.2, rfl⟩
    · exact lin2_conj_le_of_odd hs.cfg.short hn hlin hS2 hSN hsyl hc542 (hNS hy) hodd
    · obtain ⟨e, heW, heZ, hec⟩ :=
        lin2_exists_central hs.cfg.short (by omega) hlin hT₁2 hT₁N hs.syl₁
      refine ⟨e, heW.1, hP.W_le_conj ⟨heW.1, ?_⟩, heZ, hec⟩
      exact Subgroup.centralizer_le
        (SetLike.coe_subset_coe.2 (inf_le_inf_right K₁ (inf_le_left : S ≤ T₁))) heW.2
  · have hsylT₁ := hs.isSylowTwoOf_γ
    have hUS := a5_blockU_le_baum hs.cfg.short h5 hT₁2 hT₁N hsylT₁
    have hQD := a5_baum_inf_centralizer hs.cfg.short h5 hT₁2 hT₁N hsylT₁
    obtain ⟨P₀⟩ := nonempty_a5pi hs.cfg.short h5
    obtain ⟨P, -, hPB, -⟩ := exists_a5Pi_std hs.cfg.short hT₁N hs.U_le_T₁ hsylT₁ hJγ P₀
    have hc : A5Cfg K₁ T₁ S P :=
      { short := hs.cfg.short
        alt := h5
        SR := inf_le_left
        RS := Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T₁)
        SN := hSN
        US := hUS
        QD := hQD
        SE := hPB
        syl := hs.syl₁
        perm := fun g hg hgN => absurd hg.2 hgN }
    refine ⟨hUS, fun v hv => ?_, fun y hy hodd => hc.conj_le_of_odd (hNS hy) hy hodd, ?_⟩
    · rw [hQD] at hv
      have hcomm : ∀ a ∈ blockU K₁, ∀ b ∈ S ⊓ centralizer (K₁ : Set G), a * b = b * a :=
        fun a ha b hb => mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 a (hUK ha)
      obtain ⟨u, hu, d, hd, rfl⟩ := mem_sup_of_commute hcomm hv
      exact ⟨u, hu, d, hd.2, rfl⟩
    ·
      set U₁ := blockU K₁ with hU₁
      set E := U₁ ⊓ conjSubgroup U₁ x with hE
      have hUT₁ : U₁ ≤ T₁ := hs.U_le_T₁
      have hT₁U : T₁ ≤ normalizer (U₁ : Set G) := T₁_le_normalizer_U
      have hUxT₁ : conjSubgroup U₁ x ≤ T₁ := by
        have h1 := conjSubgroup_mono hUT₁ x
        rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hs.xN] at h1
      have hT₁Ux : T₁ ≤ normalizer ((conjSubgroup U₁ x : Subgroup G) : Set G) := by
        have h1 := conjSubgroup_mono hT₁U x
        rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hs.xN, conjSubgroup_normalizer] at h1
      have hEne : E ≠ ⊥ := by
        intro hbot
        apply hs.xU
        intro v hv
        rw [mem_centralizer_iff]
        intro u hu
        have h1 : u * v * u⁻¹ * v⁻¹ ∈ E := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have h2 : v * u⁻¹ * v⁻¹ ∈ U₁ :=
              (mem_normalizer_iff.mp (hT₁U (hUxT₁ hv)) u⁻¹).mp (inv_mem hu)
            have e : u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) := by group
            rw [e]; exact mul_mem hu h2
          · have h2 : u * v * u⁻¹ ∈ conjSubgroup U₁ x :=
              (mem_normalizer_iff.mp (hT₁Ux (hUT₁ hu)) v).mp hv
            exact mul_mem h2 (inv_mem hv)
        rw [hbot, mem_bot] at h1
        calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
          _ = v * u := by rw [h1, one_mul]
      obtain ⟨e, heE, he1, hec⟩ := DoubleA3.exists_central_of_normal hEne
        (inf_le_left.trans hUT₁) (fun g hg => mem_normalizer_inf (hT₁U hg) (hT₁Ux hg)) hT₁2
      refine ⟨e, heE.1, heE.2, fun h => he1 ?_, hec⟩
      rw [AppC.blockZ_eq_bot_of_alt5 hs.cfg.short h5] at h
      exact h

end GammaSetupNS

theorem theorem311Nonsolvable_of (h126 : TheoremC126) (hMPB : MinParabolicBlockSubnormal)
    (hEmb : EmbedLocal) : Theorem311Nonsolvable := by
  intro G _ _ T hsimple hnonab hqtke hT M₀ H R hM₀ hH hnsolv ⟨N, hN⟩ hR1 hRT hRsyl hM₀R
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hNC : NoCommonNormal R H M₀ := fun X hXR hX1 hHX hM₀X =>
    hcon ⟨X, hX1, hXR, sup_le hM₀X hHX⟩
  have hT2 : IsPGroup 2 T := hT.1
  have hTH : T ≤ H := hH.1
  have hTsylH : IsSylowTwoOf T H :=
    ⟨hTH, hT2, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have hTR : T ≤ normalizer (R : Set G) := hM₀.1.trans hM₀R
  set K := oTwoUpper H with hK
  have hKH : K ≤ H := oTwoUpper_le H
  have hKT : K ⊔ T = H := by
    rw [sup_comm, hK, ← F6.twoResidual_eq_oTwoUpper]; exact sup_twoResidual_eq hTsylH
  have hHKR : H ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) := by
    calc H = K ⊔ T := hKT.symm
      _ ≤ _ := sup_le (le_sup_left.trans Subgroup.le_normalizer)
        (fun t ht => C1.mem_normalizer_sup (le_normalizer_oTwoUpper H (hTH ht)) (hTR ht))
  by_cases hTn : H ≤ normalizer (T : Set G)
  ·
    have hle : T ⊓ (K ⊔ R) ≤ R := by
      refine IsSylowIn.le_of_normal (p := 2) hRsyl inf_le_right ?_ (hT2.to_le inf_le_left)
      refine (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun y hy => ?_
      exact C5.mem_normalizer_inf (hTn ((sup_le hKH (hRT.trans hTH)) hy))
        (Subgroup.le_normalizer hy)
    have hReq : R = T ⊓ (K ⊔ R) := le_antisymm (le_inf hRT le_sup_right) hle
    refine hNC R le_rfl hR1 ?_ hM₀R
    rw [hReq]
    exact fun h hh => C5.mem_normalizer_inf (hTn hh) (hHKR hh)
  have hmin : MinParabolic H T N := ⟨hTsylH, hTn, hN⟩
  have hchar : CharTwo H := charTwo_of_inH hqtke.2.1 (hT2.toSylow hT.2) hH
  have hSQ : IsSQTKTC H :=
    ⟨kGroup_of_pCoreOf_ne_bot hqtke hsimple hnonab hH.2,
      stronglyQuasithin_of_pCoreOf_ne_bot hqtke hH.2⟩
  obtain ⟨K₁, hcfg⟩ :=
    exists_blockConfigNS h126 hMPB hTsylH hchar hSQ hN hTn hnsolv hR1 hRT hRsyl hM₀.1 hM₀R hNC
  have hTsylM₀ : IsSylowTwoOf T M₀ :=
    ⟨hM₀.1, hT2, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hM₀.1))⟩
  obtain ⟨hns, x, -, hxN, hxU⟩ :=
    hcfg.exists_good_elt hNC hTsylM₀ hM₀R hRT hTH hRsyl hKT.ge
  obtain ⟨t, htT, htK⟩ := IsConcreteLE.not_le_iff_exists.mp hns
  have hs : GammaSetupNS H T R K₁ t x :=
    ⟨hcfg, hchar, hT, hqtke.2.1, hRT, hTH, htT, htK, hxN, hxU⟩
  obtain ⟨hUB, hQD, hodd, hWe⟩ := hs.facts_γ h126 hSQ hmin
  exact hs.false_of_embed hsimple hnonab hqtke hEmb hmin hUB hQD hodd hWe

end CFSG.Quasithin.C58NS
