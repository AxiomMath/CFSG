module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1U58
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LSp13
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesSp64
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp64
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
open CFSG.RankThree.PartTwo.Sec21.TablesSp64
open CFSG.RankThree.PartTwo.Sec21.TablesL44 (ω ω_pow_three)
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)
open Matrix

theorem orderSuzuki_dvd_Sp64 {m : ℕ} (hm : 1 ≤ m)
    (h : CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) ∣ 4106059776000) : m = 1 := by
  by_contra hne
  by_cases h5 : 5 ≤ m
  · have h2 : 2 ^ 22 ∣ 4106059776000 := by
      refine (pow_dvd_pow 2 (by omega : 22 ≤ 4 * m + 2)).trans ?_
      refine Dvd.dvd.trans ?_ ((sq_dvd_orderSuzuki _).trans h)
      rw [← pow_mul, show (2 * m + 1) * 2 = 4 * m + 2 by ring]
    norm_num at h2
  · interval_cases m
    · exact hne rfl
    all_goals norm_num [CFSG.Open.orderSuzuki] at h

theorem exists_conj_mem_A0_sp {s : Sp} (hs3 : s ^ 3 = 1) : ∃ x : Sp, x * s * x⁻¹ ∈ A0 := by
  obtain ⟨T, hTe, hfuse⟩ := hasFusionTarget_Sp
  obtain ⟨y, hy⟩ := hfuse A0 isElemAbelian_A0
  obtain ⟨z, hz⟩ := hfuse _ (CFSG.Open.isElemAbelian_zpowers hs3)
  have hT27 : Nat.card T ≤ 3 ^ 3 := maxEA_Sp.1 T hTe
  have hyT : A0.map (MulAut.conj y).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hy (by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, card_A0]
      exact hT27)
  have h1 : z * s * z⁻¹ ∈ T := hz ⟨s, Subgroup.mem_zpowers s, rfl⟩
  rw [← hyT] at h1
  obtain ⟨a, ha, hya⟩ := h1
  have hya' : y * a * y⁻¹ = z * s * z⁻¹ := hya
  refine ⟨y⁻¹ * z, ?_⟩
  have e : y⁻¹ * z * s * (y⁻¹ * z)⁻¹ = a := by
    calc y⁻¹ * z * s * (y⁻¹ * z)⁻¹ = y⁻¹ * (z * s * z⁻¹) * y := by group
      _ = y⁻¹ * (y * a * y⁻¹) * y := by rw [hya']
      _ = a := by group
  rw [e]
  exact ha

theorem card_F4_eq : Nat.card F4 = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem eq_one_of_commute_A0_pow_thirteen (v : Multiplicative (Fin 3 → ZMod 3))
    (hv : δ v ≠ 1) (g : Sp) (hg : g * δ v = δ v * g) (h13 : g ^ 13 = 1) : g = 1 := by
  by_contra hg1
  apply hv
  set b : Fin 3 → F4ˣ := CFSG.RankThree.PartTwo.KFacts.KS21.DFT.powVec ω ω_pow_three v with hbdef
  have hδ : δ v = CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom b := rfl
  have hb3 : ∀ i, b i ^ 3 = 1 := by
    have hv3 : v ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    have h := congrArg (fun x => x) (show b ^ 3 = 1 by rw [hbdef, ← map_pow, hv3, map_one])
    intro i
    exact congrFun h i
  have hmat : mat (δ v) = diagonal (Sum.elim (fun i => (b i : F4)) fun i => ((b i)⁻¹ : F4ˣ)) := by
    rw [hδ]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_torusHom b
  have hB13 : mat g ^ 13 = 1 := by
    have := congrArg mat h13
    simpa [mat] using this
  have hB1 : mat g ≠ 1 := by
    intro h
    exact hg1 (Subtype.ext (Units.ext h))
  have hAB : diagonal (Sum.elim (fun i => (b i : F4)) fun i => ((b i)⁻¹ : F4ˣ)) * mat g =
      mat g * diagonal (Sum.elim (fun i => (b i : F4)) fun i => ((b i)⁻¹ : F4ˣ)) := by
    rw [← hmat]
    have := congrArg mat hg
    simp only [mat, Subgroup.coe_mul, Units.val_mul] at this
    exact this.symm
  have hall := sp_trivial_of_commute_pow_thirteen' card_F4_eq hB13 hB1 hb3 hAB
  have hb1 : b = 1 := funext hall
  rw [hδ, hb1, map_one]

section Comps


theorem lieCompsExport_sp64 (s : Sp) (hs3 : s ^ 3 = 1) : LieCompsExport 2 (MulAut.conj s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q : PrimePower := ⟨2, 2, Nat.prime_two, by norm_num⟩ with hqdef
  have hv : (LieTypeIndex.B 3 q).Valid := valid_B_of_three_le le_rfl (by norm_num)
  obtain ⟨eB⟩ := Census.bridgeSp6Four q hv rfl rfl
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv rfl
    (by norm_num) (equivSp.symm.trans eB.symm)
  obtain ⟨⟨hℓ, hf, hr, hne⟩, K, _, _, hK, ⟨e'⟩⟩ := hm
  have hne' : ¬(3 = 2 ∧ q.p ^ q.exponent = 2) := fun h => absurd h.1 (by norm_num)
  set t := e' s with ht
  have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, hs3, map_one]
  obtain ⟨x, hx, hx3⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (r := 3) (K := K)
    (by norm_num) Nat.prime_three (by norm_num) ht3
  have h1 := lieCompExport_conj_sp slFactorFacts_holds slAltSixFacts_holds
    suFactorFacts_holds suAltSixFacts_holds spFactorFacts_holds spAltSixFacts_holds
    spFourTwoFacts_holds hℓ hf hK hr hne' (by norm_num) x hx3
  rw [hx] at h1
  have hcongr : MulAut.congr e' (MulAut.conj s) = MulAut.conj t := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply, ht]
  have h2 : LieCompExport q.p (MulAut.conj s) := by
    refine LieCompExport.of_congr e' ?_
    rw [hcongr]
    exact h1
  exact h2.toComps

end Comps

theorem sp64_noSz (hb : LieOrderBridge) (hs : IsSimpleGroup Sp)
    (hinn : ∀ β : MulAut Sp, β ^ 3 = 1 → IsInnerAut β)
    (hcomps : ∀ s : Sp, s ^ 3 = 1 → LieCompsExport 2 (MulAut.conj s)) :
    ∀ β : MulAut Sp, β ^ 3 = 1 → ∀ C Y : Subgroup Sp, (∀ z, z ∈ C ↔ β z = z) → Y ≤ C →
      (Y.subgroupOf C).IsSubnormal → Group.IsPerfect ↥Y → ¬ 3 ∣ Nat.card Y → Y = ⊥ := by
  intro β hβ C Y hC hYC hsub hp h3
  have hCeq : C = Sec4.autFix β := Subgroup.ext fun z => (hC z).trans Sec4.mem_autFix.symm
  subst hCeq
  have h3S : 3 ∣ Nat.card Sp := by
    rw [card_Sp_eq]
    norm_num
  by_cases hβ1 : β = 1
  · subst hβ1
    have htop : Sec4.autFix (1 : MulAut Sp) = ⊤ :=
      Subgroup.ext fun x => ⟨fun _ => Subgroup.mem_top x, fun _ => Sec4.mem_autFix.2 rfl⟩
    exact eq_bot_of_equiv_simple ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hs h3S
      hYC hsub h3
  have hZ : Subgroup.center Sp = ⊥ := by
    haveI := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Sp) with h | h
    · exact h
    · exfalso
      apply hβ1
      obtain ⟨s, rfl⟩ := hinn β hβ
      ext y
      have hs : s ∈ Subgroup.center Sp := h ▸ Subgroup.mem_top s
      rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.1 hs y).symm]
      group
  have hinj : Function.Injective (MulAut.conj : Sp →* MulAut Sp) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center Sp := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut Sp => φ g) hab
      simp only [MulAut.conj_apply] at h1
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    calc a = a * (a⁻¹ * b) := by rw [hc, mul_one]
      _ = b := by group
  obtain ⟨s, rfl⟩ := hinn β hβ
  have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hβ, map_one])
  have hs1 : s ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  rw [RonanK429.RowV.autFix_conj_eq_centralizer] at hYC hsub
  obtain ⟨x, hx⟩ := exists_conj_mem_A0_sp hs3
  obtain ⟨v, hv⟩ := hx
  refine noSz_centralizer_of_mulEquiv (MulAut.conj x) s ?_ Y hYC hsub hp h3
  intro Y' hY' hsn' hp' h3'
  have hs' : (MulAut.conj x) s = δ v := by rw [MulAut.conj_apply, hv]
  rw [hs'] at hY' hsn'
  have hδ1 : δ v ≠ 1 := by
    rw [← hs']
    intro h
    exact hs1 ((MulAut.conj x).injective (by rw [h, map_one]))
  have hδ3 : δ v ^ 3 = 1 := by rw [← hs', ← map_pow, hs3, map_one]
  have hY'' : Y' ≤ Sec4.autFix (MulAut.conj (δ v)) := by
    rw [RonanK429.RowV.autFix_conj_eq_centralizer]
    exact hY'
  have hsn'' : (Y'.subgroupOf (Sec4.autFix (MulAut.conj (δ v)))).IsSubnormal := by
    rw [RonanK429.RowV.autFix_conj_eq_centralizer]
    exact hsn'
  refine eq_bot_of_comps_noSz hb (hcomps _ hδ3) (fun m hm J hJ hd => ?_) hY'' hsn'' hp' h3'
  have hJS : Nat.card J ∣ 4106059776000 := by
    have := Subgroup.card_subgroup_dvd_card J
    rw [card_Sp_eq] at this
    norm_num at this ⊢
    exact this
  have hm1 := orderSuzuki_dvd_Sp64 hm (hd.trans hJS)
  subst hm1
  refine false_of_dvd_of_noElt (by norm_num : Nat.Prime 13)
    (fun g hg hg13 => eq_one_of_commute_A0_pow_thirteen v hδ1 g ?_ hg13) hJ ?_
  · rw [MulAut.conj_apply] at hg
    calc g * δ v = δ v * g * (δ v)⁻¹ * δ v := by rw [hg]
      _ = δ v * g := by group
  · exact (show 13 ∣ CFSG.Open.orderSuzuki (2 ^ (2 * 1 + 1)) by
      norm_num [CFSG.Open.orderSuzuki]).trans hd

section Row


theorem kT1_eight_Sp6_4 : RowOf143 (projSp 3 (GaloisField 2 2)) := by
  intro S _ _ hs hna ⟨e⟩ _
  let τ : S ≃* Sp := e.trans equivSp
  have hOut : Group.IsSolvable (Outer S) := by
    have : Group.IsSolvable (Outer Sp) :=
      CFSG.SeitzReduction.SymplecticPilot.isSolvable_outer_statedSp (K := F4) (n := 3) (by norm_num)
    exact solvable_of_surjective (f := (equivalence τ).symm.toMonoidHom)
      (equivalence τ).symm.surjective
  have hsSp : IsSimpleGroup Sp := (MulEquiv.isSimpleGroup_congr τ).1 hs
  have hinn : ∀ β : MulAut Sp, β ^ 3 = 1 → IsInnerAut β := by
    intro β h3
    have h3' : MulAut.congr equivSp.symm β ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    exact (isInnerAut_congr equivSp.symm β).mp
      (cubeInner_of_not_three_dvd_card_outer RonanK432.not_three_dvd_card_outer_projSp6 _ h3')
  refine row143_of_inner_kgroup hs hna
    (fun P _ hPp _ => le_inner_of_perfect_outSolvable hOut P hPp)
    fun β hβ Y hY hsn _ hp h3Y => ?_
  exact sp4R148_bot_of_mulEquiv τ
    (sp64_noSz lieOrderBridge_holds hsSp hinn fun s hs3 => lieCompsExport_sp64 s hs3) β hβ
    (Sec4.autFix β) Y (fun z => Iff.rfl) hY hsn hp h3Y

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
