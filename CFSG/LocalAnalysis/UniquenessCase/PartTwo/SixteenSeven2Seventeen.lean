module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue3
public import CFSG.Quasithin.Background.OddCoprimeFixV
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Pairing
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Transfer
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124BlkTransfer
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.H16TwoM22
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.RonanH143Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_not_comm_of_counterex (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hC : Counterex16 D V₀ V L hV) (h2 : Case168_2 D V₀ V hV L) :
    ¬ IsMulCommutative ↥(lBar V₀ V hV L) := by
  rintro hcomm
  haveI := hcomm
  obtain ⟨e⟩ := h2.1
  have hcenter : ∀ σ : Equiv.Perm (Fin 3), (∀ τ, σ * τ = τ * σ) → σ = 1 := by decide
  have hLM : L ≤ D.M := hC.setting.hyp151.le
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hLM
  have htriv : ∀ a : ↥(lBar V₀ V hV L), (a : MulAut (Vtil V₀ V hV)) = 1 := by
    intro a
    have haM : (a : MulAut (Vtil V₀ V hV)) ∈ Mbar D.M V₀ V hV := hle a.2
    have haC : (a : MulAut (Vtil V₀ V hV)) ∈
        Subgroup.centralizer ((lBar V₀ V hV L : Subgroup _) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg (fun x : ↥(lBar V₀ V hV L) => (x : MulAut (Vtil V₀ V hV)))
        (mul_comm' ⟨b, hb⟩ a)
    have hak : (a : MulAut (Vtil V₀ V hV)) ∈ kBar D.M V₀ V hV L :=
      Subgroup.mem_inf.2 ⟨haM, haC⟩
    have hctr : ∀ τ : Equiv.Perm (Fin 3), e ⟨(a : MulAut (Vtil V₀ V hV)), hak⟩ * τ =
        τ * e ⟨(a : MulAut (Vtil V₀ V hV)), hak⟩ := by
      intro τ
      obtain ⟨k, hk⟩ := e.surjective τ
      rw [← hk]
      have hAK : (⟨(a : MulAut (Vtil V₀ V hV)), hak⟩ : ↥(kBar D.M V₀ V hV L)) * k =
          k * ⟨(a : MulAut (Vtil V₀ V hV)), hak⟩ := by
        apply Subtype.ext
        have hkC : (k : MulAut (Vtil V₀ V hV)) ∈
            Subgroup.centralizer ((lBar V₀ V hV L : Subgroup _) : Set _) :=
          (Subgroup.mem_inf.1 k.2).2
        exact (Subgroup.mem_centralizer_iff.1 hkC) (a : MulAut (Vtil V₀ V hV)) a.2
      calc e ⟨(a : MulAut (Vtil V₀ V hV)), hak⟩ * e k =
            e (⟨(a : MulAut (Vtil V₀ V hV)), hak⟩ * k) := (map_mul e _ _).symm
        _ = e (k * ⟨(a : MulAut (Vtil V₀ V hV)), hak⟩) := by rw [hAK]
        _ = e k * e ⟨(a : MulAut (Vtil V₀ V hV)), hak⟩ := map_mul e _ _
    have hea1 : e ⟨(a : MulAut (Vtil V₀ V hV)), hak⟩ = 1 := hcenter _ hctr
    have hsub : (⟨(a : MulAut (Vtil V₀ V hV)), hak⟩ : ↥(kBar D.M V₀ V hV L)) = 1 :=
      e.injective (by rw [hea1, map_one])
    exact congrArg (fun x : ↥(kBar D.M V₀ V hV L) => (x : MulAut (Vtil V₀ V hV))) hsub
  apply hC.ne_bot
  rw [← le_bot_iff]
  intro a ha
  exact Subgroup.mem_bot.2 (htriv ⟨a, ha⟩)

theorem s16c167_exclusive_two (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D V₀ V L hV) (h2 : Case168_2 D V₀ V hV L) :
    ¬ Case168_4At D V₀ V hV L 3 3 ∧ ¬ Case168_9 D V₀ V hV L ∧ ¬ Case168_10 D V₀ V hV L := by
  have hnc := s16c167_not_comm_of_counterex D hC h2
  have hsig3 : D.sig = {3} := h2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hab, -, -⟩
    obtain ⟨e⟩ := hab
    exact hnc (IsMulCommutative.of_comm fun x y => by
      apply e.injective
      rw [map_mul, map_mul]
      exact mul_comm _ _)
  · intro h9
    have h37 : (3 : ℕ) = 7 :=
      Set.singleton_eq_singleton_iff.mp (hsig3 ▸ h9.2.2.2.2)
    exact absurd h37 (by norm_num)
  · rintro ⟨p, -, h10at⟩
    haveI : IsCyclic ↥(lBar V₀ V hV L) := h10at.1.1
    exact hnc inferInstance

theorem s16c167_exclusive_four (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h4 : Case168_4At D V₀ V hV L 3 3) :
    ¬ Case168_9 D V₀ V hV L ∧ ¬ Case168_10 D V₀ V hV L := by
  obtain ⟨hab, -, h3sig⟩ := h4
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 27 := by
    obtain ⟨e⟩ := hab
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card]
  refine ⟨?_, ?_⟩
  · intro h9
    have h37 : (3 : ℕ) = 7 :=
      Set.mem_singleton_iff.mp (h9.2.2.2.2 ▸ h3sig)
    exact absurd h37 (by norm_num)
  · rintro ⟨p, -, h10at⟩
    have hp3 : p = 3 := by
      have h3p : (3 : ℕ) ∈ ({p} : Set ℕ) := by
        rw [← h10at.2.2.2.1]
        exact h3sig
      exact (Set.mem_singleton_iff.mp h3p).symm
    have hcardp : Nat.card ↥(lBar V₀ V hV L) = p := h10at.1.2
    rw [hcard, hp3] at hcardp
    exact absurd hcardp (by norm_num)

theorem s16c167_v1Sub_eq_bot_of_inf_fixV (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h0 : V₀ = ⊥)
    (h : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥) : v1Sub D.M V₀ V hV L = ⊥ := by
  subst h0
  have hwSub : wSub (⊥ : Subgroup G) V hV L ⊓ centralizer (L : Set G) = ⊥ := by
    refine le_bot_iff.1 fun w hw => ?_
    obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨x, rfl, hx⟩ :=
      (mem_preTil (⊥ : Subgroup G) V hV (wTil (⊥ : Subgroup G) V hV L)).1 hwW
    have hxfix : mkTil (⊥ : Subgroup G) V hV x ∈ fixV (lBar (⊥ : Subgroup G) V hV L) := by
      rw [mem_fixV]
      intro φ hφ
      obtain ⟨g, hg, rfl⟩ := (mem_barSub (⊥ : Subgroup G) V hV L φ).1 hφ
      rw [actTil_mk]
      have hxfixval : actStab (⊥ : Subgroup G) V hV g x = x := by
        refine IntMod.val_injective ?_
        rw [actStab_apply_val]
        have hcomm : (g : G) * x.val = x.val * (g : G) :=
          (Subgroup.mem_centralizer_iff.1 hwC) (g : G) hg
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [hxfixval]
    have hxbot : mkTil (⊥ : Subgroup G) V hV x ∈
        (⊥ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) := by
      rw [← h]
      exact Subgroup.mem_inf.2 ⟨hx, hxfix⟩
    have hone : mkTil (⊥ : Subgroup G) V hV x = 1 := Subgroup.mem_bot.1 hxbot
    have h1 : mkTil (⊥ : Subgroup G) V hV x =
        mkTil (⊥ : Subgroup G) V hV (1 : IntMod V hV) := by
      rw [map_one]
      exact hone
    have h2 := (mkTil_eq_iff (⊥ : Subgroup G) V hV x 1).1 h1
    simpa using h2
  rw [v1Sub_of_eq_bot D.M (⊥ : Subgroup G) V hV L rfl]
  exact iSup_eq_bot.2 fun m => conjSubgroup_eq_bot_iff.2 hwSub

theorem s16c167_wTil_inf_fixV_eq_bot_of_odd {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (L : Subgroup G) (hodd : Odd (Nat.card ↥(lBar V₀ V hV L))) :
    wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥ := by
  have h := commV_inf_fixV_eq_bot_of_odd_card (s15_Infra_vtil_sq_eq_one V₀ V hV)
    (barSub V₀ V hV L) hodd
  rwa [commV_eq_commSub] at h

theorem s16c167_v1Sub_eq_bot_of_case10 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h0 : V₀ = ⊥) (h10 : Case168_10At D V₀ V hV L 3) :
    v1Sub D.M V₀ V hV L = ⊥ := by
  refine s16c167_v1Sub_eq_bot_of_inf_fixV D hV h0 (s16c167_wTil_inf_fixV_eq_bot_of_odd hV L ?_)
  rw [h10.1.2]
  decide

theorem s16c167_delta_wConj (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hC : Counterex16 D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 2) (hV1 : v1Sub D.M V₀ V hV L = ⊥) :
    (wConj D.M V₀ V hV L).ncard = 2 ∧ (∀ I ∈ wConj D.M V₀ V hV L, I ≤ V) ∧
      sSupIndep (wConj D.M V₀ V hV L) ∧ sSup (wConj D.M V₀ V hV L) = V := by
  have h151 : Hyp151 D V₀ V L := hC.setting.hyp151
  refine ⟨?_, ?_, s15_Glue3_indep D h151 hV hC.ne_bot hV1, ?_⟩
  · rw [ncard_wConj D h151 hV, hs]
  · rintro X ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h151.hyp125 hV hm
  · rw [sSup_eq_iSup]
    exact iSup_wConj_eq D h1217 h151 hV hC.ne_bot

theorem s16c167_seventeen_sumOfNat_two {W : Type} [CommGroup W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    {U : Subgroup W} (h : SumOfNat N H U ⊥ 2) :
    ∃ I : Fin 2 → Subgroup W, (∀ i, N H (I i) ⊥) ∧ I 0 ⊓ I 1 = ⊥ ∧ I 0 ⊔ I 1 = U := by
  obtain ⟨I, -, hind, hsup, hN⟩ := h
  have h01 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun j => iSup_le fun hj => ?_
      fin_cases j
      · exact absurd rfl hj
      · exact le_rfl
    · exact le_iSup₂ (f := fun j (_ : j ≠ 0) => I j) 1 (by decide)
  have hsup2 : (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup (fun i => I i) 0) (le_iSup (fun i => I i) 1)
  refine ⟨I, hN, ?_, ?_⟩
  · have h0 := hind 0
    rw [bot_sup_eq, h01] at h0
    exact le_bot_iff.1 h0
  · rw [bot_sup_eq, hsup2] at hsup
    exact hsup

theorem s16c167_case2_irr (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h2 : Case168_2 D V₀ V hV L) :
    ∃ I : Fin 2 → Subgroup (Vtil V₀ V hV), (∀ i, I i ∈ irrSet (lBar V₀ V hV L)) ∧
      I 0 ⊓ I 1 = ⊥ ∧ I 0 ⊔ I 1 = ⊤ := by
  obtain ⟨-, ⟨L₀, -, hfam⟩, -⟩ := h2
  rcases hfam with ⟨n, hn5, -, -, -, hsum⟩ | ⟨m, hm3, -, -, -, hsum⟩ | ⟨-, -, hsum⟩ |
    ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩
  · obtain ⟨I, hnat, h01, hsup⟩ := s16c167_seventeen_sumOfNat_two hsum
    exact ⟨I, fun i => s16c167_mem_irrSet_alt hn5 (hnat i), h01, hsup⟩
  · obtain ⟨I, hnat, h01, hsup⟩ := s16c167_seventeen_sumOfNat_two hsum
    exact ⟨I, fun i => s16c167_mem_irrSet_ln (by omega) (hnat i), h01, hsup⟩
  · obtain ⟨I, hnat, h01, hsup⟩ := s16c167_seventeen_sumOfNat_two hsum
    exact ⟨I, fun i => s16c167_mem_irrSet_sp (by norm_num) (hnat i), h01, hsup⟩
  · obtain ⟨I, hnat, h01, hsup⟩ := s16c167_seventeen_sumOfNat_two hsum
    exact ⟨I, fun i => s16c167_mem_irrSet_omegaMinus (Or.inl rfl) (hnat i), h01, hsup⟩
  · obtain ⟨I, hnat, h01, hsup⟩ := s16c167_seventeen_sumOfNat_two hsum
    exact ⟨I, fun i => s16c167_mem_irrSet_omegaMinus (Or.inr rfl) (hnat i), h01, hsup⟩

theorem s16c167_delta_case2 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h0 : V₀ = ⊥) (h2 : Case168_2 D V₀ V hV L) :
    ∃ Δ : Set (Subgroup G), Δ.ncard = 2 ∧ (∀ I ∈ Δ, I ≤ V) ∧ sSupIndep Δ ∧ sSup Δ = V ∧
      ∀ I ∈ Δ, imgTil V₀ V hV I ∈ irrBar L V₀ V hV := by
  obtain ⟨I, hirr, h01, hsup⟩ := s16c167_case2_irr D h2
  have hI0 : I 0 ≠ ⊥ := fun h => by
    have hlt := (hirr 0).2.1
    rw [h, bot_inf_eq] at hlt
    exact lt_irrefl _ hlt
  have hne : I 0 ≠ I 1 := fun h => hI0 (by
    have h00 : I 0 ⊓ I 0 = ⊥ := by
      nth_rewrite 2 [h]
      exact h01
    rwa [inf_idem] at h00)
  have hn : ({I 0, I 1} : Set (Subgroup (Vtil V₀ V hV))).ncard = 2 := Set.ncard_pair hne
  have hi : sSupIndep ({I 0, I 1} : Set (Subgroup (Vtil V₀ V hV))) :=
    (sSupIndep_pair hne).2 (disjoint_iff.2 h01)
  have hs : sSup ({I 0, I 1} : Set (Subgroup (Vtil V₀ V hV))) = ⊤ := by
    rw [sSup_pair]
    exact hsup
  obtain ⟨hn', hle, hind, hsup'⟩ := s16c167_preTil_decomp hV h0 hn hi hs
  refine ⟨preTil V₀ V hV '' {I 0, I 1}, hn', hle, hind, hsup', ?_⟩
  rintro _ ⟨S, hS, rfl⟩
  rw [imgTil_preTil]
  rcases hS with rfl | hS
  · exact hirr 0
  · rw [Set.mem_singleton_iff] at hS
    rw [hS]
    exact hirr 1

theorem s16c167_case4_pairing (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h4 : Case168_4At D V₀ V hV L 3 3) (g : G) :
    ∃ Δt : Set (Subgroup (Vtil V₀ V hV)), Δt.ncard = 2 ∧ sSupIndep Δt ∧ sSup Δt = ⊤ ∧
      (∀ I ∈ Δt, rk ↥I = 4) ∧
      (∀ φ ∈ barSub V₀ V hV (conjSubgroup V g⁻¹ ⊓ D.M), ∀ I ∈ Δt,
        I.map φ.toMonoidHom ∈ Δt) ∧
      PairsOfConj (Mbar D.M V₀ V hV) (dParam 3) Δt := by
  obtain ⟨-, hsym, -⟩ := h4
  have hd : dParam 3 = 2 := by
    unfold dParam
    exact orderOf_eq_prime (by decide) (by decide)
  have hP : IsPGroup 2 ↥(barSub V₀ V hV (conjSubgroup V g⁻¹ ⊓ D.M)) := by
    intro φ
    obtain ⟨u, hu, hu_eq⟩ :=
      (mem_barSub V₀ V hV (conjSubgroup V g⁻¹ ⊓ D.M) φ.1).1 φ.2
    obtain ⟨huV, -⟩ := Subgroup.mem_inf.1 hu
    have hconj : g⁻¹ * (u : G) * g ∈ V := by
      simpa using (mem_conjSubgroup_iff.1 huV)
    have hu2 : (u : G) ^ 2 = 1 := by
      have h2 : (g⁻¹ * (u : G) * g) ^ 2 = 1 := hV.2 _ hconj
      have hconjpow : g * (g⁻¹ * (u : G) * g) ^ 2 * g⁻¹ = (u : G) ^ 2 := by
        rw [← conj_pow (a := g) (b := g⁻¹ * (u : G) * g) (i := 2)]
        congr 1
        group
      rw [← hconjpow, h2]
      group
    have hu2' : u ^ 2 = 1 := Subtype.ext hu2
    have hφ2 : φ ^ 2 = 1 := by
      apply Subtype.ext
      change φ.1 ^ 2 = 1
      rw [← hu_eq]
      rw [← map_pow, hu2', map_one]
    exact ⟨1, by simpa using hφ2⟩
  obtain ⟨Δt, hn, hi, hs, hrk, hperm, hpairs⟩ :=
    s16c167_pairing_core (W := Vtil V₀ V hV) hsym (barSub_mono V₀ V hV inf_le_right) hP
  refine ⟨Δt, hn, hi, hs, ?_, hperm, hpairs⟩
  intro I hI
  rw [hrk I hI, hd]

theorem s16c167_delta_case4 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D V₀ V L hV) (h0 : V₀ = ⊥) (g : G)
    (h4 : Case168_4At D V₀ V hV L 3 3) :
    ∃ Δ : Set (Subgroup G), Δ.ncard = 2 ∧ (∀ I ∈ Δ, I ≤ V) ∧ sSupIndep Δ ∧ sSup Δ = V ∧
      (∀ I ∈ Δ, rk ↥I = 4) ∧
      (∀ u ∈ V ⊓ conjSubgroup D.M g, ∀ J ∈ deltaConj Δ g, conjSubgroup J u ∈ deltaConj Δ g) ∧
      PairsOfConj (Mbar D.M V₀ V hV) (dParam 3) (imgTil V₀ V hV '' Δ) := by
  obtain ⟨Δt, hn, hi, hs, hrk, hinv, hpairs⟩ := s16c167_case4_pairing D h4 g
  obtain ⟨hn', hle, hind, hsup⟩ := s16c167_preTil_decomp hV h0 hn hi hs
  have hP := hC.setting.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  refine ⟨preTil V₀ V hV '' Δt, hn', hle, hind, hsup, ?_, ?_, ?_⟩
  · rintro _ ⟨S, hS, rfl⟩
    rw [s16c167_rk_preTil hV h0]
    exact hrk S hS
  · intro u hu J hJ
    obtain ⟨huV, huM⟩ := Subgroup.mem_inf.1 hu
    obtain ⟨_, ⟨S, hS, rfl⟩, rfl⟩ := hJ
    have hm : g * u * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 huM
    have hmV : g * u * g⁻¹ ∈ conjSubgroup V g⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have e : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
      rw [e]
      exact huV
    have hmP : (g * u * g⁻¹)⁻¹ ∈ conjSubgroup V g⁻¹ ⊓ D.M :=
      Subgroup.mem_inf.2 ⟨Subgroup.inv_mem _ hmV, Subgroup.inv_mem _ hm⟩
    have hmst : g * u * g⁻¹ ∈ stabTil V₀ V := hMst hm
    have hφ := actTil_mem_barSub V₀ V hV hmP ((stabTil V₀ V).inv_mem hmst)
    have hcalc : conjSubgroup (conjSubgroup (preTil V₀ V hV S) g) u =
        conjSubgroup (conjSubgroup (preTil V₀ V hV S) (g * u * g⁻¹)) g := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [hcalc, s16c167_conjSubgroup_preTil hV hmst]
    exact ⟨_, ⟨_, hinv _ hφ S hS, rfl⟩, rfl⟩
  · have himg : imgTil V₀ V hV '' (preTil V₀ V hV '' Δt) = Δt := by
      rw [Set.image_image]
      simp [imgTil_preTil]
    rw [himg]
    exact hpairs

theorem sixteen_seven2_seventeen (D : Data G) (h1217 : R1217 D) (h12 : R16_12 D)
    (h15 : R16_15 D) : R16_17 D := by
  intro V₀ V L hV hC A hA g hAg
  obtain ⟨-, h0, h1⟩ := h12 V₀ V L hV hC
  obtain ⟨-, hcfg⟩ := h15 V₀ V L hV hC A hA
  rcases hcfg with h2 | h4 | h10 | h9
  · obtain ⟨Δ, hn, hle, hind, hsup, hirr⟩ := s16c167_delta_case2 D h0 h2
    obtain ⟨hx4, hx9, hx10⟩ := s16c167_exclusive_two D hC h2
    exact ⟨Δ, hn, hle, hind, hsup, fun _ => hirr, fun h => absurd h hx4,
      fun h => (h.elim hx9 hx10).elim⟩
  · obtain ⟨Δ, hn, hle, hind, hsup, hrk, hinv, hpairs⟩ := s16c167_delta_case4 D hC h0 g h4
    obtain ⟨hx9, hx10⟩ := s16c167_exclusive_four D h4
    exact ⟨Δ, hn, hle, hind, hsup,
      fun h2 => absurd h4 (s16c167_exclusive_two D hC h2).1, fun _ => ⟨hrk, hinv, hpairs⟩,
      fun h => (h.elim hx9 hx10).elim⟩
  · have h10' : Case168_10 D V₀ V hV L := ⟨3, Or.inl rfl, h10⟩
    obtain ⟨hn, hle, hind, hsup⟩ := s16c167_delta_wConj D h1217 hC h10.2.2.1
      (s16c167_v1Sub_eq_bot_of_case10 D hV h0 h10)
    exact ⟨wConj D.M V₀ V hV L, hn, hle, hind, hsup,
      fun h2 => absurd h10' (s16c167_exclusive_two D hC h2).2.2,
      fun h4 => absurd h10' (s16c167_exclusive_four D h4).2, fun _ => rfl⟩
  · obtain ⟨hn, hle, hind, hsup⟩ := s16c167_delta_wConj D h1217 hC h9.2.2.1 (h1 h9)
    exact ⟨wConj D.M V₀ V hV L, hn, hle, hind, hsup,
      fun h2 => absurd h9 (s16c167_exclusive_two D hC h2).2.1,
      fun h4 => absurd h9 (s16c167_exclusive_four D h4).1, fun _ => rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
