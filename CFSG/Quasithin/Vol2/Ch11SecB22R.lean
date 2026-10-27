module

public import CFSG.Quasithin.Vol2.Ch11SecB22Setup
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Background.E6Thirteen
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem pCoreOf_ne_bot_of_faithfulLocal {L : Subgroup G} (h : quasithinIsFaithfulLocal T L) :
    pCoreOf 2 L ≠ ⊥ := by
  intro h2
  apply h.2.2.2
  rw [quasithinV2, h2]
  have hb : Subgroup.closure {z : G | z ∈ (⊥ : Subgroup G) ⊓
      Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ∧ z ^ 2 = 1} = ⊥ :=
    le_bot_iff.mp ((Subgroup.closure_le _).mpr fun _ hz => hz.1.1)
  rw [hb, Subgroup.commutator_bot_left]

theorem inf_centralizer_le_normalizer (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n)
    {U : Subgroup G} (hUV : U ≤ fsuV T I) (hU1 : U ≠ ⊥) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G) := by
  intro x hx
  by_contra hxN
  have hbot := (h1103 G T L I n hyp).2.2.2.1.2 x hx.1 hxN
  apply hU1
  rw [eq_bot_iff, ← hbot]
  intro u hu
  refine ⟨hUV hu, mem_conjSubgroup_iff.mpr ?_⟩
  rw [← Subgroup.mem_centralizer_iff.mp hx.2 u hu, mul_inv_cancel_right]
  exact hUV hu

theorem twoPrimeResidual_le_of_lt_mParam (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n)
    {U : Subgroup G} (hUV : U ≤ fsuV T I) (hU1 : U ≠ ⊥)
    (hk : E3.mQuot (fsuV T I) U <
      E3.mParam (autI (isElemAbelian_fsuV hyp) (Subgroup.normalizer (L : Set G)))) :
    twoPrimeResidual (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G)) ≤
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hV := isElemAbelian_fsuV hyp
  set H := M ⊓ Subgroup.centralizer (U : Set G) with hHdef
  have hHN := inf_centralizer_le_normalizer h1103 hyp hUV hU1
  obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two H
  have hSC : S ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    by_contra hSC
    have hSN : S ≤ Subgroup.normalizer (fsuV T I : Set G) := hS.1.trans hHN
    have hA1 : autI hV S ≠ ⊥ := (autI_eq_bot_iff hV hSN).not.2 hSC
    have hle := E3.mParam_le_rkIdx_fixV (autI_mono hV (hS.1.trans inf_le_left))
      (B6.isPGroup_autOn hS.2.1 (fsuV T I)) hA1
    rw [E3.rkIdx_fixV_autI hV hSN] at hle
    have hUS : U ≤ fsuV T I ⊓ Subgroup.centralizer (S : Set G) := by
      intro u hu
      refine ⟨hUV hu, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp (hS.1 hs).2 u hu).symm
    have := E3.mQuot_mono (V := fsuV T I) hUS
    omega
  refine (iInf₂_le (H ⊓ Subgroup.centralizer (fsuV T I : Set G))
    ⟨inf_le_left, B2F.le_normalizer_inf Subgroup.le_normalizer
      (B2F.le_normalizer_centralizer hHN), fun h2 => ?_⟩).trans (inf_le_inf_right _ inf_le_left)
  exact hS.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left H (le_inf hS.1 hSC)))

theorem isUniqueM_L (h4213 : TmpL6_4_2_13) (hN : FactNot4213) (h331 : Stmt3_3_1)
    (hyp : Hyp11 G T L I n) : IsUniqueM L (Subgroup.normalizer (L : Set G)) := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hH421 : Ch10.TmpL6_Hyp4_2_1 G T M L :=
    ⟨hyp.fsu.simple, hyp.fsu.nonabelian, hyp.fsu.qtke, hyp.fsu.sylow, isMaxTwoLocal_M h331 hyp,
      hyp.normal, hyp.fsu.maximal, hyp.fsu.faithful, Subgroup.le_normalizer,
      hyp.fsu.quasisimple⟩
  have hconj : ∀ X : Subgroup G, X ≤ Subgroup.normalizer (L : Set G) →
      conjSubgroupsBy X L = {L} := by
    intro X hX
    ext K
    simp only [conjSubgroupsBy, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      ext y
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hX hx) z).mp hz
      · intro hy
        refine ⟨x⁻¹ * y * x, ?_, by simp [mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hX hx)) y).mp hy
        simpa [mul_assoc] using this
    · rintro rfl
      refine ⟨1, X.one_mem, ?_⟩
      ext y
      simp
  have hNot : IsNotation4211 T M L L := by
    refine ⟨Subgroup.le_normalizer, fun x hx => Set.mem_mul.mpr ⟨x, hx, 1,
      (pCoreOf 2 (L ⊔ T)).one_mem, mul_one x⟩, ?_, pCoreOf_ne_bot_of_faithfulLocal hyp.fsu.faithful⟩
    rw [hconj T hyp.normal, hconj L Subgroup.le_normalizer]
  rcases h4213 G T M L L hH421 hNot with h | ⟨hC, -⟩ | hO
  · exact h
  · exact absurd (Or.inl hC) (hN G T M L _ n hyp.one_lt hyp.shape)
  · exact absurd (Or.inr hO) (hN G T M L _ n hyp.one_lt hyp.shape)

theorem card_le_two_of_inf_eq_bot {V A U : Subgroup G} (hV : IsPGroup 2 V) (hAV : A ≤ V)
    (hU : E3.mQuot V U = 1) (hAU : A ⊓ U = ⊥) : Nat.card A ≤ 2 := by
  have h2 : U.relIndex V = 2 := by rw [E3.relIndex_eq_two_pow hV U, hU, pow_one]
  have hle := Subgroup.relIndex_le_of_le_right (H := U) hAV (by rw [h2]; norm_num)
  have hbot : U.subgroupOf A = ⊥ := Subgroup.subgroupOf_eq_bot.mpr
    (disjoint_iff.mpr (by rw [inf_comm]; exact hAU))
  rw [Subgroup.relIndex, hbot, Subgroup.index_bot, h2] at hle
  exact hle

theorem le_rParam (hFM : FactMParam) (hFH : FactHyperplaneT) (hS44 : FactSp4FourExt)
    (hN : FactNot4213) (h4213 : TmpL6_4_2_13) (h311 : Theorem311Stmt)
    (h63 : ASInputs.AS_E_6_3) (h664 : ASInputs.AS_E_6_6_four) (h614 : ASInputs.AS_E_6_14)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n)
    {m : ℕ} (hm : KindG2 L (fsuV T I) n ∧ m = 2 * n ∨ ¬ KindG2 L (fsuV T I) n ∧ m = n) :
    (m : ℕ∞) ≤ E3.rParam (fsuV T I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hV := isElemAbelian_fsuV hyp
  have hV2 : IsPGroup 2 ↥(fsuV T I) := isPGroup_fsuV hyp
  have hLV := L_le_normalizer_fsuV hyp
  have hTV := T_le_normalizer_fsuV T I
  have hVL := commutator_fsuV_eq_self hyp
  have hnat := natModuleOf_fsuV h1102 hyp
  have hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  have hMN : M ⊓ Subgroup.normalizer (fsuV T I : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left
  obtain ⟨hmP, hdim⟩ :=
    hFM G L (fsuV T I) M n m hV hyp.one_lt hLV hVL hnat hm Subgroup.le_normalizer hMN
  have hE := hypE61_of h331 h1102 h1103 hyp
  by_cases h2 : 2 < m
  · have := (h63 G T M (fsuV T I) hV hE (hmP ▸ h2)).1
    rwa [hmP] at this
  have hn2 : n = 2 ∧ m = 2 ∧ ¬ KindG2 L (fsuV T I) n := by
    have := hyp.one_lt
    rcases hm with ⟨-, rfl⟩ | ⟨hG, rfl⟩
    · omega
    · exact ⟨by omega, by omega, hG⟩
  obtain ⟨hn, hm2, hnG2⟩ := hn2
  subst hn hm2
  unfold E3.rParam
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hUC⟩ := hU
  by_contra hlt
  have hk : E3.mQuot (fsuV T I) U ≤ 1 := by
    push Not at hlt
    have : E3.mQuot (fsuV T I) U < 2 := by exact_mod_cast hlt
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h0 | h1
  · exact hUC (((E3.mQuot_eq_zero_iff hV2 hUV).mp h0) ▸ Subgroup.centralizer_le_normalizer _)
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    omega
  have hres := twoPrimeResidual_le_of_lt_mParam h1103 hyp hUV hU1 (by rw [hmP, h1]; norm_num)
  have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ M := fun h =>
    hUC fun x hx => inf_centralizer_le_normalizer h1103 hyp hUV hU1 ⟨h hx, hx⟩
  by_cases hCL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥
  ·
    obtain ⟨g, hgL, hTg⟩ := hFH G L (fsuV T I) T hV hLV hVL hnat hnG2 hCL hTS hTV hyp.normal U
      hUV h1
    have hgN : g ∈ Subgroup.normalizer (fsuV T I : Set G) := hLV hgL
    have hU'V : conjSubgroup U g ≤ fsuV T I := by
      intro x hx
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp
        (hUV (mem_conjSubgroup_iff.mp hx))
      simpa [mul_assoc] using h
    have hVg : conjSubgroup (fsuV T I) g = fsuV T I := by
      ext x
      rw [mem_conjSubgroup_iff]
      exact (Subgroup.mem_normalizer_iff.mp hgN x).symm
    have hk' : E3.mQuot (fsuV T I) (conjSubgroup U g) = 1 := by
      rw [← hVg, E3.mQuot_conjSubgroup, h1]
    have hU'1 : conjSubgroup U g ≠ ⊥ := by
      intro h
      rw [h] at hk'
      omega
    have hres' := twoPrimeResidual_le_of_lt_mParam h1103 hyp hU'V hU'1
      (by rw [hmP, hk']; norm_num)
    have hC' := E6.e6_13 h311 hE hU'V hU'1 hres' hTg
    apply hUC
    intro x hx
    have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer (conjSubgroup U g : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      have hc := Subgroup.mem_centralizer_iff.mp hx _ (mem_conjSubgroup_iff.mp hu)
      calc u * (g⁻¹ * x * g) = g⁻¹ * ((g * u * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * u * g⁻¹)) * g := by rw [hc]
        _ = g⁻¹ * x * g * u := by group
    have hxN := inf_centralizer_le_normalizer h1103 hyp hU'V hU'1 ⟨hC' hx', hx'⟩
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hxN) (Subgroup.inv_mem _ hgN)
  have hSp4 : KindSp4 L (fsuV T I) 2 := by
    rcases (h1103 G T L I 2 hyp).2.2.1 with ⟨h, -⟩ | ⟨h | h, -⟩
    · exact absurd h hCL
    · exact h
    · exact absurd h hnG2
  have hUL : U ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra hne
    have hP2 : IsPGroup 2 ↥(U ⊓ Subgroup.centralizer (L : Set G)) :=
      hV2.to_le (inf_le_left.trans hUV)
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (⟨_, hne, hP2, rfl⟩ :
      IsTwoLocal (Subgroup.normalizer
        ((U ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)))
    have hLC : L ≤ Subgroup.normalizer
        ((U ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp hw.2 l hl).symm
    have hMeq := (isUniqueM_L h4213 hN h331 hyp).2 M' ⟨hM', hLC.trans hle⟩
    apply hCM
    have hle' : Subgroup.normalizer
        ((U ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) ≤ M := by
      rw [hMdef, ← hMeq]
      exact hle
    exact (Subgroup.centralizer_le inf_le_left).trans
      ((Subgroup.centralizer_le_normalizer _).trans hle')
  have hCLU : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ⊓ U = ⊥ :=
    le_bot_iff.mp (hUL ▸ le_inf inf_le_right (inf_le_left.trans inf_le_right))
  have hcard : Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    have hle := card_le_two_of_inf_eq_bot hV2 inf_le_left h1 hCLU
    have hge := (Subgroup.one_lt_card_iff_ne_bot _).mpr hCL
    omega
  obtain ⟨hTL, hUs⟩ := hS44 G L (fsuV T I) T hV hLV hVL hnat hSp4 hcard
    (isPGroup_cL_fsuV h1102 hyp) hTS hTV hyp.normal
  obtain ⟨hmax, hidx, Y, hY, hY3, hYC⟩ := hUs U hUV h1 hUL
  have hZU : U ⊓ (fsuV T I ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro hbot
    have hle := card_le_two_of_inf_eq_bot hV2 (inf_le_left : fsuV T I ⊓
      Subgroup.centralizer (T : Set G) ≤ fsuV T I) h1 (by rw [inf_comm]; exact hbot)
    have hCLT : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤
        fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
      intro z hz
      refine ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      by_cases hz1 : z = 1
      · rw [hz1, mul_one, one_mul]
      have htz : t * z * t⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (B2F.le_normalizer_inf hTV
          (B2F.le_normalizer_centralizer hyp.normal) ht) z).mp hz
      have htz1 : t * z * t⁻¹ ≠ 1 := fun h => hz1 (by
        have := congrArg (fun y => t⁻¹ * y * t) h
        simpa [mul_assoc] using this)
      have hz2 : ∀ w ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G), w ≠ 1 → w = z := by
        intro w hw hw1
        by_contra hwz
        have h3 : 3 ≤ Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer (L : Set G)) := by
          classical
          have hfin : Finite ↥(fsuV T I ⊓ Subgroup.centralizer (L : Set G)) := inferInstance
          have := Fintype.ofFinite ↥(fsuV T I ⊓ Subgroup.centralizer (L : Set G))
          rw [Nat.card_eq_fintype_card]
          refine le_trans ?_ (Finset.card_le_univ
            ({⟨1, Subgroup.one_mem _⟩, ⟨z, hz⟩, ⟨w, hw⟩} :
              Finset ↥(fsuV T I ⊓ Subgroup.centralizer (L : Set G))))
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · exact fun h => hwz (congrArg Subtype.val h).symm
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hz1 (congrArg Subtype.val h).symm,
              fun h => hw1 (congrArg Subtype.val h).symm⟩
        omega
      have := hz2 _ htz htz1
      calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [this]
    obtain ⟨v, hv, hvL⟩ : ∃ v ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G),
        v ∉ Subgroup.centralizer (L : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hTL fun x hx => hcon x hx
    have hlt : fsuV T I ⊓ Subgroup.centralizer (L : Set G) <
        fsuV T I ⊓ Subgroup.centralizer (T : Set G) :=
      lt_of_le_of_ne hCLT fun h => hvL (h ▸ hv).2
    have := Subgroup.card_lt_of_lt hlt
    omega
  have hΓ : ASInputs.GammaE64 M (fsuV T I) U := ⟨hU1, hUV, hCM, hres⟩
  have hchar := h664 G T M (fsuV T I) U hE hΓ hZU
  have hQ : L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer h1102 hyp le_rfl (sup_le hLV hTV)
  exact hCM (h614 G T M (fsuV T I) U (L ⊔ T) hE hU1 hUV hres hchar
    (Or.inr ⟨Y, hY.trans inf_le_right, hY3, hYC⟩) le_sup_right hQ (isUniqueM_LT h331 hyp)
    hmax hidx)

end CFSG.Quasithin.Vol2.Ch11.SecB
