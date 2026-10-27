module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Sz
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU58
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearUnitaryComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Gen
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV
open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesU58
open CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem noSz_centralizer_of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] (φ : S ≃* T)
    (z : S)
    (h : ∀ Y : Subgroup T, Y ≤ Subgroup.centralizer ({φ z} : Set T) →
      (Y.subgroupOf (Subgroup.centralizer ({φ z} : Set T))).IsSubnormal →
      Group.IsPerfect ↥Y → ¬ 3 ∣ Nat.card Y → Y = ⊥)
    (Y : Subgroup S) (hY : Y ≤ Subgroup.centralizer ({z} : Set S))
    (hsn : (Y.subgroupOf (Subgroup.centralizer ({z} : Set S))).IsSubnormal)
    (hp : Group.IsPerfect ↥Y) (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  set C := Subgroup.centralizer ({z} : Set S) with hCdef
  have hCφ : C.map (φ : S →* T) = Subgroup.centralizer ({φ z} : Set T) :=
    Ronan148S.map_centralizer_singleton_equiv φ z
  have hYφ : Y.map (φ : S →* T) ≤ Subgroup.centralizer ({φ z} : Set T) := by
    rw [← hCφ]
    exact Subgroup.map_mono hY
  let eC : ↥C ≃* ↥(C.map (φ : S →* T)) := C.equivMapOfInjective _ φ.injective
  have heq : (Y.subgroupOf C).map (eC : ↥C →* ↥(C.map (φ : S →* T))) =
      (Y.map (φ : S →* T)).subgroupOf (C.map (φ : S →* T)) := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨y, hyY, hyx⟩
      refine ⟨y, hyY, ?_⟩
      have := congrArg Subtype.val hyx
      simpa [eC] using this
    · rintro ⟨y, hyY, rfl⟩
      refine ⟨⟨y, hY hyY⟩, hyY, Subtype.ext ?_⟩
      simp [eC]
  have hsn' : ((Y.map (φ : S →* T)).subgroupOf (C.map (φ : S →* T))).IsSubnormal := by
    rw [← heq]
    exact hsn.map eC.surjective
  rw [hCφ] at hsn'
  have eY : ↥Y ≃* ↥(Y.map (φ : S →* T)) := Y.equivMapOfInjective _ φ.injective
  have hp' : Group.IsPerfect ↥(Y.map (φ : S →* T)) :=
    Group.IsPerfect.ofSurjective (f := eY.toMonoidHom) eY.surjective
  have h3' : ¬ 3 ∣ Nat.card (Y.map (φ : S →* T)) := by
    rwa [← Nat.card_congr eY.toEquiv]
  have hb := h _ hYφ hsn' hp' h3'
  rwa [Subgroup.map_eq_bot_iff_of_injective _ φ.injective] at hb

theorem orderSuzuki_dvd_U58 {m : ℕ} (hm : 1 ≤ m)
    (h : CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) ∣ 4656663745464977326080) : m = 1 := by
  by_contra hne
  by_cases h8 : 8 ≤ m
  · have h2 : 2 ^ 34 ∣ 4656663745464977326080 := by
      refine (pow_dvd_pow 2 (by omega : 34 ≤ 4 * m + 2)).trans ?_
      refine Dvd.dvd.trans ?_ ((sq_dvd_orderSuzuki _).trans h)
      rw [← pow_mul, show (2 * m + 1) * 2 = 4 * m + 2 by ring]
    norm_num at h2
  · interval_cases m
    · exact hne rfl
    all_goals norm_num [CFSG.Open.orderSuzuki] at h

section U58

theorem no7_of_outer {σ : MulAut SUI} (hσ3 : σ ^ 3 = 1)
    (hout : σ ∉ (MulAut.conj : SUI →* MulAut SUI).range) :
    ∀ t : SUI, σ t = t → t ^ 7 = 1 → t = 1 := by
  obtain ⟨A, hA, φ, hσA, hφk⟩ := exists_unitary_field σ
  have hφ3 : φ ^ 3 = 1 := by
    have h := hφk 1 (by rw [pow_one]; exact hσ3)
    rwa [pow_one] at h
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    obtain ⟨g₀, hg₀⟩ := exists_SUI_conj_eq hA
    apply hout
    refine ⟨g₀, MulEquiv.ext fun x => Subtype.ext ?_⟩
    have h1 : glAut 1 ((x : SUI) : GL (Fin 5) K) = ((x : SUI) : GL (Fin 5) K) := by
      rw [map_one]
      rfl
    rw [MulAut.conj_apply, hσA x, h1, hg₀]
    simp
  have hφform : (∀ x : K, φ x = x ^ 4) ∨ ∀ x : K, φ x = x ^ 16 := by
    obtain ⟨σf, hσf, hord, hzp⟩ := RonanK432.exists_frob_gen
    haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [card_ringAut_K]; norm_num)
    have hφmem : φ ∈ Submonoid.powers σf := by
      rw [mem_powers_iff_mem_zpowers, hzp]
      exact Subgroup.mem_top φ
    obtain ⟨n, hn⟩ := hφmem
    have hn' : σf ^ n = φ := hn
    have h6 : σf ^ (3 * n) = 1 := by rw [pow_mul', hn', hφ3]
    have hdvd : 6 ∣ 3 * n := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one h6
    have hφ : σf ^ (n % 6) = φ := by rw [← hord, pow_mod_orderOf, hn']
    have hn6 : n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 4 := by omega
    rcases hn6 with h0 | h2 | h4
    · exfalso
      rw [h0, pow_zero] at hφ
      exact hφ1 hφ.symm
    · left
      intro x
      rw [← hφ, h2, RonanK432.frob_pow_apply hσf]
      norm_num
    · right
      intro x
      rw [← hφ, h4, RonanK432.frob_pow_apply hσf]
      norm_num
  intro t hσt ht7
  have h := hσA t
  rw [hσt] at h
  have h2 : ((t : SUI) : GL (Fin 5) K) * A = A * glAut φ ((t : SUI) : GL (Fin 5) K) := by
    calc ((t : SUI) : GL (Fin 5) K) * A =
          (A * glAut φ ((t : SUI) : GL (Fin 5) K) * A⁻¹) * A := by rw [← h]
      _ = A * glAut φ ((t : SUI) : GL (Fin 5) K) := by group
  have hAB := congrArg (fun X : GL (Fin 5) K => (X : Matrix (Fin 5) (Fin 5) K)) h2
  simp only [Units.val_mul, coe_glAut] at hAB
  apply mU_injective
  rw [mU_one]
  exact eq_one_of_twisted_pow_seven' card_K_eq (A := (A : Matrix (Fin 5) (Fin 5) K))
    (B := mU t) φ.toRingHom hφform (Units.isUnit A) hAB.symm (mU_mem t).2
    (by rw [← mU_pow, ht7, mU_one])

theorem bs3_noSz (Y : Subgroup SUI) (hY : Y ≤ Subgroup.centralizer ({bs 3} : Set SUI))
    (hsn : (Y.subgroupOf (Subgroup.centralizer ({bs 3} : Set SUI))).IsSubnormal)
    (hp : Group.IsPerfect ↥Y) (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have hf : Function.Injective (![0, 1, 2, 3] : Fin 4 → Fin 5) := by decide
  have hfib : Set.range (![0, 1, 2, 3] : Fin 4 → Fin 5) = {i | ext9 (us 3) i = 3} :=
    range_eq_setOf (by decide)
  have hq := isQuasisimple_idOutsideSU _ hf hfib (by norm_num)
  have hYH : Y ≤ idOutsideSU {i | ext9 (us 3) i = 3} := by
    rw [← commutator_self_eq_of_isPerfect hp]
    exact Subgroup.commutator_le.mpr fun a ha b hb =>
      commutator_mem_idOutsideSU (u := us 3) fib3_single fib3_const (hY ha) (hY hb)
  have h3H : 3 ∣ Nat.card (idOutsideSU {i | ext9 (us 3) i = 3}) := by
    rw [card_idOutsideSU _ hf hfib (by norm_num), card_SU4_eight]
    norm_num
  exact eq_bot_of_le_quasisimple hYH (idOutsideSU_le_centralizer (u := us 3) 3) hsn hq h3H hp h3

theorem bs_no5 {i : Fin 4} (hi : i ≠ 3) (g : SUI)
    (hg : g ∈ Subgroup.centralizer ({bs i} : Set SUI)) (hg5 : g ^ 5 = 1) : g = 1 := by
  rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) i with rfl | rfl | rfl | rfl
  · exact eq_one_of_mem_centralizer_of_pow (u := us 0) hg (Or.inl ⟨rfl, fib0_lt⟩) hg5
  · exact eq_one_of_mem_centralizer_of_pow (u := us 1) hg (Or.inl ⟨rfl, fib1_lt⟩) hg5
  · exact eq_one_of_mem_centralizer_of_pow (u := us 2) hg
      (Or.inl ⟨rfl, fun κ => (fib2_lt κ).trans (by norm_num)⟩) hg5
  · exact absurd rfl hi

theorem u58_noSz (hb : LieOrderBridge) (hs : IsSimpleGroup SUI)
    (hcomps : ∀ β : MulAut SUI, β ^ 3 = 1 → β ≠ 1 → LieCompsExport 2 β) :
    ∀ β : MulAut SUI, β ^ 3 = 1 → ∀ C Y : Subgroup SUI, (∀ z, z ∈ C ↔ β z = z) → Y ≤ C →
      (Y.subgroupOf C).IsSubnormal → Group.IsPerfect ↥Y → ¬ 3 ∣ Nat.card Y → Y = ⊥ := by
  intro β hβ C Y hC hYC hsub hp h3
  have hCeq : C = Sec4.autFix β := Subgroup.ext fun z => (hC z).trans Sec4.mem_autFix.symm
  subst hCeq
  have h3S : 3 ∣ Nat.card SUI := by
    rw [card_SUI]
    norm_num
  by_cases hβ1 : β = 1
  · subst hβ1
    have htop : Sec4.autFix (1 : MulAut SUI) = ⊤ :=
      Subgroup.ext fun x => ⟨fun _ => Subgroup.mem_top x, fun _ => Sec4.mem_autFix.2 rfl⟩
    exact eq_bot_of_equiv_simple ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hs h3S
      hYC hsub h3
  have hinj : Function.Injective (MulAut.conj : SUI →* MulAut SUI) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center SUI := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut SUI => φ g) hab
      simp only [MulAut.conj_apply] at h1
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * g := by group
    rw [center_SUI, Subgroup.mem_bot] at hc
    calc a = a * (a⁻¹ * b) := by rw [hc, mul_one]
      _ = b := by group
  by_cases hin : β ∈ (MulAut.conj : SUI →* MulAut SUI).range
  ·
    obtain ⟨s, rfl⟩ := hin
    have hs3 : s ^ 3 = 1 := hinj (by rw [map_pow, hβ, map_one])
    have hs1 : s ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    rw [autFix_conj_eq_centralizer] at hYC hsub
    obtain ⟨x, v, hv⟩ := exists_conj_mem_A0 hs3
    have hv0 : Multiplicative.toAdd v ≠ 0 := by
      intro h0
      apply hs1
      have hv1 : v = 1 := Multiplicative.toAdd.injective h0
      rw [hv1, map_one] at hv
      have e : s = x⁻¹ * (x * s * x⁻¹) * x := by group
      rw [e, ← hv]
      group
    obtain ⟨π, -, i, hπ⟩ := exists_perm_std _ hv0
    set ψ : SUI ≃* SUI := (MulAut.conj x).trans (reindexSU π) with hψ
    have hψs : ψ s = bs i ∨ ψ s = bs i ^ 2 := by
      have e : ψ s = reindexSU π (δ (Multiplicative.ofAdd (Multiplicative.toAdd v))) := by
        rw [hψ, MulEquiv.trans_apply, MulAut.conj_apply, ← hv]
        rfl
      rw [e, reindexSU_δ]
      rcases hπ with h | h
      · left
        rw [h, res3_ext3]
      · right
        rw [h, res3_ext3, δ_two_smul]
    have hcent : Subgroup.centralizer ({ψ s} : Set SUI) =
        Subgroup.centralizer ({bs i} : Set SUI) := by
      rcases hψs with h | h
      · rw [h]
      · rw [h, centralizer_sq_eq (δ_pow_three _)]
    refine noSz_centralizer_of_mulEquiv ψ s ?_ Y hYC hsub hp h3
    intro Y' hY' hsn' hp' h3'
    rw [hcent] at hY' hsn'
    by_cases hi3 : i = 3
    · subst hi3
      exact bs3_noSz Y' hY' hsn' hp' h3'
    ·
      have hbi1 : bs i ≠ 1 := by
        intro h1
        apply hs1
        apply ψ.injective
        rw [map_one]
        rcases hψs with h | h
        · rw [h, h1]
        · rw [h, h1, one_pow]
      have hbi3 : bs i ^ 3 = 1 := δ_pow_three _
      have hc3 : MulAut.conj (bs i) ^ 3 = 1 := by rw [← map_pow, hbi3, map_one]
      have hc1 : MulAut.conj (bs i) ≠ 1 := fun h => hbi1 (hinj (by rw [h, map_one]))
      have hY'' : Y' ≤ Sec4.autFix (MulAut.conj (bs i)) := by
        rw [autFix_conj_eq_centralizer]
        exact hY'
      have hsn'' : (Y'.subgroupOf (Sec4.autFix (MulAut.conj (bs i)))).IsSubnormal := by
        rw [autFix_conj_eq_centralizer]
        exact hsn'
      refine eq_bot_of_comps_noSz hb (hcomps _ hc3 hc1) (fun m _ J hJ hd => ?_) hY'' hsn'' hp' h3'
      refine false_of_dvd_of_noElt Nat.prime_five (fun g hg hg5 => bs_no5 hi3 g ?_ hg5) hJ
        ((five_dvd_orderSuzuki m).trans hd)
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply] at hg
      calc g * bs i = bs i * g * (bs i)⁻¹ * bs i := by rw [hg]
        _ = bs i * g := by group
  ·
    have hno7 := no7_of_outer hβ hin
    refine eq_bot_of_comps_noSz hb (hcomps β hβ hβ1) (fun m hm J hJ hd => ?_) hYC hsub hp h3
    have hJS : Nat.card J ∣ 4656663745464977326080 := by
      have := Subgroup.card_subgroup_dvd_card J
      rw [card_SUI] at this
      norm_num at this ⊢
      exact this
    have hm1 := orderSuzuki_dvd_U58 hm (hd.trans hJS)
    subst hm1
    refine false_of_dvd_of_noElt (by norm_num : Nat.Prime 7) hno7 hJ ?_
    exact (show 7 ∣ CFSG.Open.orderSuzuki (2 ^ (2 * 1 + 1)) by
      norm_num [CFSG.Open.orderSuzuki]).trans hd

end U58

section Row


theorem kT1_eight_SU5_8 : RowOf143 (projSU 5 2 3) := by
  intro S _ _ hs hna ⟨e⟩ _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q : PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩ with hqdef
  have hv : (LieTypeIndex.twistedA 4 q).Valid := valid_twistedA (by norm_num) (by omega)
  let eX := (Census.typeTwistedAGroupEquivProjSU 4 q hv).symm
  have hOut : Group.IsSolvable (Outer S) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 _ hv (e.trans eX))).2
  let τ : S ≃* SUI := e.trans equivSUI
  have hsU : IsSimpleGroup SUI := (MulEquiv.isSimpleGroup_congr τ).1 hs
  have hnaU : ∃ a b : SUI, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨τ a, τ b, fun h => hab (τ.injective (by rw [map_mul, map_mul, h]))⟩
  have hcomps : ∀ β : MulAut SUI, β ^ 3 = 1 → β ≠ 1 → LieCompsExport 2 β := fun β hβ hβ1 =>
    lieCompsOn_linearUnitary Nat.prime_three (by norm_num) SUI hsU hnaU ⟨_, hv⟩ rfl
      ⟨equivSUI.symm.trans eX⟩ β hβ hβ1 (Or.inl (by simp [lieIndexChar, hqdef]))
  refine row143_of_inner_kgroup hs hna
    (fun P _ hPp _ => le_inner_of_perfect_outSolvable hOut P hPp)
    fun β hβ Y hY hsn _ hp h3Y => ?_
  exact sp4R148_bot_of_mulEquiv τ (u58_noSz lieOrderBridge_holds hsU hcomps) β hβ
    (Sec4.autFix β) Y (fun z => Iff.rfl) hY hsn hp h3Y

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
