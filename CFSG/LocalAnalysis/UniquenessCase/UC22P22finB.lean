module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace P22fin

theorem mbarImage_sup {M V K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    mbarImage M V (K ⊔ K') = mbarImage M V K ⊔ mbarImage M V K' := by
  rw [mbarImage, mbarImage, mbarImage, Subgroup.subgroupOf_sup hK hK', Subgroup.map_sup]

theorem mbarImage_conj {M V K : Subgroup G} {t : G} (ht : t ∈ M) (hK : K ≤ M) :
    mbarImage M V (K.map (MulAut.conj t).toMonoidHom) =
      (mbarImage M V K).map
        (MulAut.conj (QuotientGroup.mk' (kerAct M V).normalCore ⟨t, ht⟩)).toMonoidHom := by
  ext x
  simp only [mbarImage, Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨k, hk, hky⟩, rfl⟩
    refine ⟨_, ⟨⟨k, hK hk⟩, hk, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hky)
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨⟨t, ht⟩ * k * ⟨t, ht⟩⁻¹, ⟨(k : G), hk, by simp⟩, by simp [map_mul, map_inv]⟩

theorem commute_mbarImage_of_ne (D : Data G) {V : Subgroup G} (hVU : V ≤ D.U)
    (hVM : D.M ≤ normalizer (V : Set G)) {K K' : Subgroup G} (hK : K ∈ calC D.M)
    (hK' : K' ∈ calC D.M) (hne : K ≠ K') :
    ∀ a ∈ mbarImage D.M V K, ∀ b ∈ mbarImage D.M V K', Commute a b := by
  obtain ⟨hsn, hp, hqs, -⟩ := UC6S846.calC_subgroupOf hK
  obtain ⟨hsn', hp', hqs', -⟩ := UC6S846.calC_subgroupOf hK'
  let π : ↥D.M →* ↥D.M ⧸ CFSG.pCore 2 ↥D.M := QuotientGroup.mk' _
  have hne' : K.subgroupOf D.M ≠ K'.subgroupOf D.M := by
    intro h
    apply hne
    have := congrArg (Subgroup.map D.M.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hK.1.le,
      Subgroup.map_subgroupOf_eq_of_le hK'.1.le] at this
  have hne'' : (K.subgroupOf D.M).map π ≠ (K'.subgroupOf D.M).map π :=
    fun h => hne' (UC6S846.image_injective hsn hp hsn' hp' h)
  have hcomm : ⁅(K.subgroupOf D.M).map π, (K'.subgroupOf D.M).map π⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute (UC6S846.isComponent_image hsn hqs)
      (UC6S846.isComponent_image hsn' hqs')).resolve_left hne''
  have hO2 : CFSG.pCore 2 ↥D.M ≤ (kerAct D.M V).normalCore := by
    haveI := kerAct_normal D.M V hVM
    rw [Subgroup.normalCore_eq_self]
    intro z hz
    rw [kerAct, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro v hv
    have hU :=
      (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).1 (hVU hv)
    have hzO : (z : G) ∈ pCoreOf 2 D.M := ⟨z, hz, rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 hU.2 _ hzO).symm
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hxy : ⁅x, y⁆ ∈ CFSG.pCore 2 ↥D.M := by
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem π hx)
      (Subgroup.mem_map_of_mem π hy)
    rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement] at h
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have h1 : (QuotientGroup.mk' (kerAct D.M V).normalCore) ⁅x, y⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).2 (hO2 hxy)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h1
  exact h1

theorem exists_elemAbelian_mbar (D : Data G) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V) {p : ℕ} (hp : p ∈ D.sig)
    {k : ℕ} (hk : k + 1 ≤ CFSG.Open.pRank p D.M) :
    ∃ E : Subgroup (MBar D.M V), IsElemAbelian p E ∧ p ^ k ≤ Nat.card E := by
  have hpP : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpP⟩
  obtain ⟨E₀, hEM, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hpP.one_lt D.M
  have hAel : IsElemAbelian p (E₀ ⊓ centralizer (V : Set G)) :=
    uc22p22n_isElemAbelian_of_le inf_le_left hEel
  have hAcard : Nat.card ↥(E₀ ⊓ centralizer (V : Set G)) ≤ p := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hAel)
    have h1 : j ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (V : Set G)) :=
      CFSG.SectionRank.le_pRank hpP.one_lt (le_inf (inf_le_left.trans hEM) inf_le_right) hAel
        hj
    have h2 := uc22p22n_pRank_centralizer_le_one D h61 hV hTI p hp
    rw [hj]
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hpP.pos (by omega)
      _ = p := pow_one p
  obtain ⟨P, hPE, hPA, hcardP⟩ := uc22p22nb_exists_complement hpP hEel inf_le_left hAcard
  have hPM : P ≤ D.M := hPE.trans hEM
  have hPel : IsElemAbelian p P := uc22p22n_isElemAbelian_of_le hPE hEel
  have hPV : P ⊓ centralizer (V : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : x ∈ P ⊓ (E₀ ⊓ centralizer (V : Set G)) := ⟨hx.1, hPE hx.1, hx.2⟩
    rw [hPA] at hmem
    exact hmem
  haveI : (kerAct D.M V).Normal := kerAct_normal D.M V hV.2.2.1
  let φ : ↥P →* MBar D.M V :=
    (QuotientGroup.mk' (kerAct D.M V).normalCore).comp (Subgroup.inclusion hPM)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    change (QuotientGroup.mk' (kerAct D.M V).normalCore) (Subgroup.inclusion hPM a) = 1 at ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.normalCore_eq_self] at ha
    have hc : (a : G) ∈ centralizer (V : Set G) := Subgroup.mem_subgroupOf.mp ha
    have hmem : (a : G) ∈ P ⊓ centralizer (V : Set G) := ⟨a.2, hc⟩
    rw [hPV] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.mp hmem))
  have htop : IsElemAbelian p (⊤ : Subgroup ↥P) := by
    have := hPel.1
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩,
      fun x _ => Subtype.ext (hPel.2 x x.2)⟩
    exact hPel.comm a.1.2 b.1.2
  refine ⟨(⊤ : Subgroup ↥P).map φ, htop.map φ, ?_⟩
  rw [Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  rw [hEcard] at hcardP
  have h3 : p ^ (k + 1) ≤ p ^ CFSG.Open.pRank p D.M := Nat.pow_le_pow_right hpP.pos hk
  have h4 : p * p ^ k ≤ p * Nat.card P := by rw [← pow_succ']; exact h3.trans hcardP
  exact Nat.le_of_mul_le_mul_left h4 hpP.pos

theorem card_le_sq_of_mbar_eq_pElementSubgroup (D : Data G) {V : Subgroup G} (hVU : V ≤ D.U)
    (hVM : D.M ≤ normalizer (V : Set G)) {p : ℕ} (hpP : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup G} (hK : K ∈ calC D.M) {n : ℕ} (hL : IsL2 ↥(mbarImage D.M V K) n) {t : G}
    (htM : t ∈ D.M) (htN : t ∉ normalizer (K : Set G))
    (hX : mbarImage D.M V (K ⊔ K.map (MulAut.conj t).toMonoidHom) =
      CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup (MBar D.M V)))
    {E : Subgroup (MBar D.M V)} (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  haveI : Fact p.Prime := ⟨hpP⟩
  have hKM : K ≤ D.M := hK.1.le
  have hMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer htM)
  have hK' : K.map (MulAut.conj t).toMonoidHom ∈ calC D.M := UC6S846.calC_map D.M _ hMt hK
  have hne : K ≠ K.map (MulAut.conj t).toMonoidHom :=
    fun h => htN (UC6S846.mem_normalizer_iff_map_conj.2 h.symm)
  have hL2 := (isL2Ev_of_isL2 hL).1
  have hL2' : IsL2Ev ↥(mbarImage D.M V (K.map (MulAut.conj t).toMonoidHom)) n := by
    rw [mbarImage_conj htM hKM]
    exact isL2Ev_of_mulEquiv hL2 (Subgroup.equivMapOfInjective _ _ (MulAut.conj _).injective)
  have hcomm := commute_mbarImage_of_ne D hVU hVM hK hK' hne
  have hi :
      mbarImage D.M V K ⊓ mbarImage D.M V (K.map (MulAut.conj t).toMonoidHom) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    have hxZ : (⟨x, hx⟩ : ↥(mbarImage D.M V K)) ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2 x hx').eq
    rw [P22y.center_eq_bot_of_isL2Ev hL2, Subgroup.mem_bot] at hxZ
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hxZ)
  have hEle :
      E ≤ mbarImage D.M V K ⊔ mbarImage D.M V (K.map (MulAut.conj t).toMonoidHom) := by
    rw [← mbarImage_sup hKM hK'.1.le, hX]
    exact le_pElementSubgroup_of_elemAbelian hpP hEel
  exact card_le_sq_of_commute hcomm hi
    (fun S => P22y.isCyclic_of_isPGroup_of_isL2Ev hL2 hpP hp2 _ S.isPGroup')
    (fun S => P22y.isCyclic_of_isPGroup_of_isL2Ev hL2' hpP hp2 _ S.isPGroup') hEel hEle

end P22fin

open P22fin in
theorem s22_fin_of_four (D : Data G) (Ch : Choice2011 G) (h61 : UC6.R6_1 D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h15 : S22_15 D Ch) : S22_fin D Ch := by
  intro h1930 c p hp K n hK t htT htN hX
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have hV : InCalV D.M c.V := uc22p22o_inCalV_of_le_U D c.hVU c.hVne c.hVM
  have hTI := uc22p22o_not_isTI_of_hC D hV c.hC
  obtain ⟨E, hEel, hEcard⟩ := exists_elemAbelian_mbar D h61 hV hTI hp (k := 3) (h4 p hp)
  have h2 := card_le_sq_of_mbar_eq_pElementSubgroup D c.hVU c.hVM hpP hp2 hK.1
    (h15 h1930 c p hp K n hK) (D.sylowM.le htT) htN hX hEel
  have h32 : p ^ 3 ≤ p ^ 2 := hEcard.trans h2
  have := (Nat.pow_le_pow_iff_right hpP.one_lt).1 h32
  omega

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4) in
theorem s22_fin_dataOfSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G)
    (S : Setup4 G) (Ch : Choice2011 G) :
    S22_8 (UC6.dataOfSetup4 hS hU S) Ch → S22_15 (UC6.dataOfSetup4 hS hU S) Ch →
      S22_17 (UC6.dataOfSetup4 hS hU S) Ch → S22_fin (UC6.dataOfSetup4 hS hU S) Ch :=
  fun _ h15 _ => s22_fin_of_four _ Ch (UC6.r6_1_dataOfSetup4 hS hU S)
    (fun _ hp => UC6.four_le_pRank_of_sigma hp) h15

end CFSG.LocalAnalysis.UniquenessCase.UC22
