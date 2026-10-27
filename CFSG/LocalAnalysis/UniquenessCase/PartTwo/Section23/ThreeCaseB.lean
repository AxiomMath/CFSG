module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne
public import CFSG.Quasithin.H13.NQS13410B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

theorem quasithin_conjClosure_eq (Z H : Subgroup G) :
    Quasithin.conjClosure Z H = conjClosure H Z := by
  rw [Quasithin.conjClosure, conjClosure]
  refine le_antisymm ?_ (iSup₂_le ?_)
  · rw [Subgroup.closure_le]
    rintro _ ⟨h, hh, z, hz, rfl⟩
    refine (le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf H Z) => K)
      (Z.map (MulAut.conj h).toMonoidHom) ⟨h, hh, rfl⟩ le_rfl) ?_
    exact Subgroup.mem_map_of_mem _ hz
  · rintro K hK
    obtain ⟨g, hg, rfl⟩ := hK
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.subset_closure ⟨g, hg, z, hz, by simp [MulAut.conj_apply]⟩

theorem eSub_U_eq_W23_1 (c : Ctx23L D Ch) :
    CFSG.LocalAnalysis.WeakClosure81.eSub D.U (c.L0 ⊔ D.T) D.T = W23_1 c := by
  rw [CFSG.LocalAnalysis.WeakClosure81.eSub, D.u_inf_centralizer_T,
    CFSG.Quasithin.H13.NQS134.conjClosure_sup_eq c.hL0.1.1
      (uc22main1_T_le_centralizer D),
    quasithin_conjClosure_eq]
  rfl

private theorem mQuot_bot_autI_eq_rk {E A₀ : Subgroup G} (hE : IsElemAbelian 2 E)
    (hAN : A₀ ≤ normalizer (E : Set G))
    (hdisj : A₀ ⊓ Subgroup.centralizer (E : Set G) = ⊥) :
    E3.mQuot (autI hE A₀) ⊥ = rk ↥A₀ := by
  have hcard : Nat.card (autI hE A₀) = Nat.card A₀ := by
    have h := card_autI_mul_card_inf hE hAN
    rw [hdisj, Subgroup.card_bot, mul_one] at h
    exact h
  rw [CFSG.Quasithin.H.mQuot_bot_eq_rk]
  unfold rk
  rw [hcard]

private theorem fixV_eq_of_centralizer_eq {E A₀ : Subgroup G}
    (hE : IsElemAbelian 2 E) (hAN : A₀ ≤ normalizer (E : Set G))
    (hdisj : A₀ ⊓ Subgroup.centralizer (E : Set G) = ⊥)
    (hfix : ∀ u ∈ A₀, u ≠ 1 →
      E ⊓ Subgroup.centralizer (A₀ : Set G) = E ⊓ Subgroup.centralizer ({u} : Set G))
    {B : Subgroup (MulAut (IntMod E hE))} (hBA : B ≤ autI hE A₀)
    (hlt : E3.mQuot (autI hE A₀) B < rk ↥A₀) :
    fixV B = fixV (autI hE A₀) := by
  have hmq := mQuot_bot_autI_eq_rk hE hAN hdisj
  have hBne : B ≠ ⊥ := by
    intro hB
    rw [hB, hmq] at hlt
    exact Nat.lt_irrefl _ hlt
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hbA : (b : MulAut (IntMod E hE)) ∈ autI hE A₀ := hBA b.2
  obtain ⟨g, hgA₀, hg⟩ := (mem_autI hE).mp hbA
  have hg1 : (g : G) ≠ 1 := by
    intro hge
    have hg_eq : g = 1 := Subtype.ext hge
    apply hb
    apply Subtype.ext
    rw [← hg, hg_eq, map_one]
    rfl
  refine le_antisymm ?_ (fixV_anti hBA)
  intro v hv
  rw [mem_fixV_autI hE hAN]
  have hbv : (b : MulAut (IntMod E hE)) v = v := (mem_fixV.mp hv) b b.2
  rw [← hg] at hbv
  have hcomm : (g : G) * v.val = v.val * (g : G) := by
    have h1 := congrArg IntMod.val hbv
    rw [convI_apply_val] at h1
    calc (g : G) * v.val = (g : G) * v.val * (g : G)⁻¹ * (g : G) := by group
      _ = v.val * (g : G) := by rw [h1]
  have hvg : v.val ∈ Subgroup.centralizer ({(g : G)} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hcomm)
  have hmemg : v.val ∈ E ⊓ Subgroup.centralizer ({(g : G)} : Set G) :=
    ⟨v.val_mem, hvg⟩
  rw [← hfix (g : G) hgA₀ hg1] at hmemg
  exact hmemg.2

private theorem mem_aSet_autI {H E A₀ : Subgroup G} (hE : IsElemAbelian 2 E)
    (hA₀ : IsElemAbelian 2 A₀) (hAH : A₀ ≤ H) (hAN : A₀ ≤ normalizer (E : Set G))
    (hdisj : A₀ ⊓ Subgroup.centralizer (E : Set G) = ⊥) (hbot : A₀ ≠ ⊥)
    (hfix : ∀ u ∈ A₀, u ≠ 1 →
      E ⊓ Subgroup.centralizer (A₀ : Set G) = E ⊓ Subgroup.centralizer ({u} : Set G)) :
    autI hE A₀ ∈ E3.aSet (rk ↥A₀) (autI hE H) := by
  have hAne : autI hE A₀ ≠ ⊥ := by
    intro h
    have hle : A₀ ≤ A₀ ⊓ Subgroup.centralizer (E : Set G) :=
      le_inf le_rfl ((autI_eq_bot_iff hE hAN).mp h)
    rw [hdisj] at hle
    exact hbot (le_bot_iff.mp hle)
  refine ⟨autI_mono hE hAH, hAne, isElemAbelian2_autI hE hA₀ hAN, ?_⟩
  intro B hBA hlt
  exact fixV_eq_of_centralizer_eq hE hAN hdisj hfix hBA hlt

theorem le_aBar_of_case_b {H E A₀ : Subgroup G} (hE : IsElemAbelian 2 E)
    (hA₀ : IsElemAbelian 2 A₀) (hAH : A₀ ≤ H) (hAN : A₀ ≤ normalizer (E : Set G))
    (hdisj : A₀ ⊓ Subgroup.centralizer (E : Set G) = ⊥)
    (hfix : ∀ u ∈ A₀, u ≠ 1 →
      E ⊓ Subgroup.centralizer (A₀ : Set G) = E ⊓ Subgroup.centralizer ({u} : Set G)) :
    rk ↥A₀ ≤ aBar H ⊥ E hE := by
  classical
  by_cases hbot : A₀ = ⊥
  · rw [hbot, rk_bot]
    exact Nat.zero_le _
  have hmem := mem_aSet_autI hE hA₀ hAH hAN hdisj hbot hfix
  have hbar := TwelveTwentyThree.barSub_bot_eq_map_autI E hE H
  have hmem' : (autI hE A₀).map (MulAut.congr (TwelveShort.mkTilEquiv E hE)).toMonoidHom ∈
      E3.aSet (rk ↥A₀) (barSub ⊥ E hE H) := by
    rw [hbar]
    exact (CFSG.Quasithin.H.map_mem_aSet_iff (TwelveShort.mkTilEquiv E hE)).mpr hmem
  exact E3.le_aParam_of_mem_aSet (by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hbot ((rk_eq_zero_iff_of_isPGroup
      (B2F.isPGroup_of_isElemAbelian hA₀)).mp h)) hmem'

theorem le_aBar_W23_1 (c : Ctx23L D Ch) {A₀ : Subgroup G}
    (hE : IsElemAbelian 2 (W23_1 c)) (hA₀ : IsElemAbelian 2 A₀)
    (hAH : A₀ ≤ c.L0 ⊔ D.T)
    (hdisj : A₀ ⊓ Subgroup.centralizer (W23_1 c : Set G) = ⊥)
    (hfix : ∀ u ∈ A₀, u ≠ 1 →
      W23_1 c ⊓ Subgroup.centralizer (A₀ : Set G) =
        W23_1 c ⊓ Subgroup.centralizer ({u} : Set G)) :
    rk ↥A₀ ≤ aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hE := by
  have hAN : A₀ ≤ Subgroup.normalizer (W23_1 c : Set G) := by
    refine hAH.trans ?_
    rw [← eSub_U_eq_W23_1 c]
    exact Quasithin.le_normalizer_conjClosure _ _
  exact le_aBar_of_case_b hE hA₀ hAH hAN hdisj hfix

theorem exists_relIndex_eq_two_of_one_le_rk {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hrk : 1 ≤ rk ↥V) :
    ∃ A : Subgroup G, A ≤ V ∧ A.relIndex V = 2 := by
  have hP : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hcardV : Nat.card V = 2 ^ rk ↥V := card_eq_two_pow_of_isPGroup hP
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := ↥V)
    (n := rk ↥V - 1) (by rw [hcardV]; exact pow_dvd_pow 2 (Nat.sub_le _ _))
  refine ⟨K.map V.subtype, Subgroup.map_subtype_le K, ?_⟩
  have hcardK : Nat.card (K.map V.subtype) = 2 ^ (rk ↥V - 1) := by
    rw [Subgroup.card_map_of_injective V.subtype_injective, hK]
  have hrel := Subgroup.relIndex_mul_card (H := K.map V.subtype) (K := V)
  rw [inf_eq_left.mpr (Subgroup.map_subtype_le K), hcardK, hcardV] at hrel
  have hp : 0 < 2 ^ (rk ↥V - 1) := pow_pos (by norm_num) _
  refine Nat.eq_of_mul_eq_mul_right hp ?_
  rw [hrel, ← pow_succ', Nat.sub_add_cancel (by omega)]

theorem wClos_one_ne_bot (c : Ctx23L D Ch) (h2 : 2 ≤ rk ↥D.U) :
    E3.wClos D.U 1 D.T ≠ ⊥ := by
  obtain ⟨A, hAU, hArel⟩ :=
    exists_relIndex_eq_two_of_one_le_rk (uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).2 (one_le_two.trans h2)
  have hAU' : A ≤ D.U := by simpa [Data.U] using hAU
  have hArel' : A.relIndex D.U = 2 := by simpa [Data.U] using hArel
  have hAΓ : A ∈ E3.gammaSet D.U 1 D.T := by
    refine ⟨hAU'.trans D.u_le_T, 1, by rw [conjSubgroup_one]; exact hAU', ?_⟩
    rw [conjSubgroup_one]
    show E3.mQuot (uCore D.M D.T) A = 1
    unfold E3.mQuot
    rw [hArel]
    norm_num
  have hAle : A ≤ E3.wClos D.U 1 D.T := E3.le_wClos hAΓ
  have hcardA : 2 ≤ Nat.card A := by
    have hrel := Subgroup.relIndex_mul_card (H := A) (K := D.U)
    rw [inf_eq_left.mpr hAU', hArel'] at hrel
    have hcardU : Nat.card D.U = 2 ^ rk ↥D.U :=
      card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian
        (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2)
    rw [hcardU] at hrel
    have h4 : 4 ≤ 2 ^ rk ↥D.U := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ rk ↥D.U := Nat.pow_le_pow_right (by norm_num) h2
    omega
  intro hbot
  have hA1 : A = ⊥ := le_bot_iff.mp (hbot ▸ hAle)
  have : Nat.card A = 1 := by rw [hA1, Subgroup.card_bot]
  omega

theorem center_wClos_one_ne_bot (c : Ctx23L D Ch) (h2 : 2 ≤ rk ↥D.U) :
    E3.wClos D.U 1 D.T ⊓
      Subgroup.centralizer (E3.wClos D.U 1 D.T : Set G) ≠ ⊥ := by
  have hWne : E3.wClos D.U 1 D.T ≠ ⊥ := wClos_one_ne_bot c h2
  have hW2 : IsPGroup 2 (E3.wClos D.U 1 D.T) :=
    D.sylowM.isPGroup.to_le (E3.wClos_le 1 D.T)
  haveI : Nontrivial ↥(E3.wClos D.U 1 D.T) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hWne
  haveI := hW2.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(center ↥(E3.wClos D.U 1 D.T)))
  intro hbot
  have hzmem : ((z : ↥(E3.wClos D.U 1 D.T)) : G) ∈
      E3.wClos D.U 1 D.T ⊓
        Subgroup.centralizer (E3.wClos D.U 1 D.T : Set G) := by
    refine ⟨(z : ↥(E3.wClos D.U 1 D.T)).2,
      Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2) ⟨h, hh⟩)
  rw [hbot, Subgroup.mem_bot] at hzmem
  exact hz (Subtype.ext (Subtype.ext hzmem))

theorem normalizer_center_wClos_one_mem_hSet (c : Ctx23L D Ch)
    (h2 : 2 ≤ rk ↥D.U)
    (hL0W : c.L0 ≤ Subgroup.normalizer (E3.wClos D.U 1 D.T : Set G)) :
    Subgroup.normalizer (E3.wClos D.U 1 D.T ⊓
      Subgroup.centralizer (E3.wClos D.U 1 D.T : Set G) : Subgroup G) ∈ hSet D.T D.M := by
  set W : Subgroup G := E3.wClos D.U 1 D.T with hW
  set ZW : Subgroup G := W ⊓ Subgroup.centralizer (W : Set G) with hZW
  have hZWne : ZW ≠ ⊥ := by
    simpa [W, ZW] using center_wClos_one_ne_bot c h2
  have hW2 : IsPGroup 2 W := D.sylowM.isPGroup.to_le (E3.wClos_le 1 D.T)
  have hL0ZW : c.L0 ≤ Subgroup.normalizer (ZW : Set G) := by
    rw [hZW]
    exact (le_inf hL0W (hL0W.trans
      (normalizer_le_normalizer_centralizer W))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨?_, fun h => Ctx23L.L0_not_le_M c (hL0ZW.trans h), ?_⟩
  · intro t ht
    exact uc22p22ta_mem_normalizer_center (E3.normalizer_le_normalizer_wClos
      (V := D.U) (i := 1) D.T (Subgroup.le_normalizer ht))
  · exact D.standing.charTwo _ ⟨ZW, hZWne, hW2.to_le inf_le_left, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
