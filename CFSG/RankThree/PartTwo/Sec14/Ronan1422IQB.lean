module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422IQBSuzuki
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422IQBUnique
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422IQBCenter
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofOdd
import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem layer_quotient_eq_bot_of_eq {X : Type*} [Group X] {N M : Subgroup X} [N.Normal]
    [M.Normal] (h : N = M) (hM : CFSG.layer (X ⧸ M) = ⊥) : CFSG.layer (X ⧸ N) = ⊥ := by
  subst h
  exact hM

theorem card_center_thetaQuot_le_three
    (h46 : Sec4.Item4_6) {M J : Subgroup G}
    (hM : SectionFourHyp M) (hZ : 3 ∣ Nat.card (Subgroup.center M))
    (hJ : J ∈ thetaComponentsIn M) :
    Nat.card (Subgroup.center (↥J ⧸ aschbacherSolvableCore 3 ↥J)) ≤ 3 := by
  obtain ⟨hJM, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  have hl := h46 ↥M hM hZ _ hJ'
  have hq := hJ'.2.2
  have hle := card_center_le_three_of_isList46 hl hq
  set e := (Subgroup.subgroupOfEquivOfLe hJM).symm
  set φ : (↥J ⧸ aschbacherSolvableCore 3 ↥J) ≃*
      ↥(J.subgroupOf M) ⧸ aschbacherSolvableCore 3 ↥(J.subgroupOf M) :=
    QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)
  rwa [Nat.card_congr (Subgroup.centerCongr φ).toEquiv]

theorem map_subgroupOf_eq_of_mem_autIn {A B J L' : Subgroup G}
    (hJN : Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (J : Set G))
    {σ : MulAut ↥B} (hσ : σ ∈ Sec4.autIn (L' ⊓ Subgroup.normalizer (A : Set G)) B) :
    (J.subgroupOf B).map σ.toMonoidHom = J.subgroupOf B := by
  obtain ⟨h, hN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  have hhJ := hJN hN
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨⟨x, hx⟩, hxJ, hxy⟩
    have hxy' : h * x * h⁻¹ = y := congrArg Subtype.val hxy
    have hxJ' : x ∈ J := Subgroup.mem_subgroupOf.mp hxJ
    apply Subgroup.mem_subgroupOf.mpr
    change y ∈ J
    rw [← hxy']
    exact (Subgroup.mem_normalizer_iff.mp hhJ x).mp hxJ'
  · intro hyJ
    rw [Subgroup.mem_subgroupOf] at hyJ
    have hyB' : h⁻¹ * y * h ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) y).mp hy
      rwa [inv_inv] at this
    have hyJ' : h⁻¹ * y * h ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhJ) y).mp hyJ
      rwa [inv_inv] at this
    refine ⟨⟨h⁻¹ * y * h, hyB'⟩, Subgroup.mem_subgroupOf.mpr hyJ', ?_⟩
    apply Subtype.ext
    change h * (h⁻¹ * y * h) * h⁻¹ = y
    group

theorem false_of_mem_thetaComponentsIn_of_three_dvd
    (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) {A L' : Subgroup G} {c' : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hc'A : c' ∈ A)
    (hAF : A ∈ partTwoF G) (hEF : ∀ E ∈ partTwoE G, E ∈ partTwoF G)
    (hS4 : SectionFourHyp (Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G)))
    (hB9 : Nat.card (A ⊓ L' : Subgroup G) = 9) (hAB : A = Subgroup.zpowers c' ⊔ (A ⊓ L'))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (L' ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L')))
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ L' : Subgroup G) : Set G))
    (htr : ∀ d ∈ A ⊓ L', ∃ w ∈ Subgroup.normalizer (A : Set G),
      w * d = d * w ∧ w * c' * w⁻¹ = c' * d)
    {J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn (Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G)))
    (hJ3 : 3 ∣ Nat.card J) : False := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  set B := A ⊓ L' with hBdef
  set C := Subgroup.centralizer (B : Set G) with hCdef
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm _ x.2.1 _ y.2.1)⟩⟩, fun x hx => hAe.2 x hx.1⟩
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
    hcomm b hb.1 a ha
  have hBC : B ≤ C := inf_le_left.trans hAC
  have hJC : J ≤ C := le_of_mem_thetaComponentsIn hJ
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hJN : Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (J : Set G) := by
    intro g hg
    have hgC := GF2n.mem_normalizer_centralizer hg
    have hJg : J.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsIn C := by
      have := map_mem_thetaComponentsIn (MulAut.conj g) hJ
      rwa [Late.map_conj_eq_of_mem_normalizer hgC] at this
    have h3g : 3 ∣ Nat.card (J.map (MulAut.conj g).toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (eq_of_mem_thetaComponentsIn_of_three_dvd hBe hB9 hEF hJg hJ h3g hJ3)
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hS4 hAC hAe
      ⟨3, le_rfl, by rw [hA27]; norm_num⟩ J hJ
  obtain ⟨v, ⟨hvJ, hvA'⟩, hv3⟩ := KFacts.exists_mem_centralizer_orderOf_eq hA3 hAJ hJ3
  have hvA : v ∈ A := Sec15.mem_of_mem_partTwoF hAF (by rw [← hv3]; exact pow_orderOf_eq_one v)
    fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hvA' a ha)
  have hv1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hv3; norm_num at hv3
  have hinv : ∀ σ ∈ Sec4.autIn (L' ⊓ Subgroup.normalizer (A : Set G)) B,
      (J.subgroupOf B).map σ.toMonoidHom = J.subgroupOf B := fun σ hσ =>
    map_subgroupOf_eq_of_mem_autIn hJN hσ
  have hBJ : B ≤ J := by
    rcases hirr (J.subgroupOf B) hinv with h | h
    · exfalso
      have hBJ1 : ∀ x ∈ B, x ∈ J → x = 1 := fun x hxB hxJ => by
        have : (⟨x, hxB⟩ : ↥B) ∈ J.subgroupOf B := Subgroup.mem_subgroupOf.mpr hxJ
        rw [h, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      have hvB : v ∉ B := fun hvB => hv1 (hBJ1 v hvB hvJ)
      have hc'B : Subgroup.zpowers c' ≤ Subgroup.normalizer (B : Set G) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b hb.1 c' hc'A)
      have hAset : (A : Set G) = (Subgroup.zpowers c' : Set G) * (B : Set G) := by
        rw [hAB]
        exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hc'B
      have hvmem : v ∈ (Subgroup.zpowers c' : Set G) * (B : Set G) := hAset ▸ hvA
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hvmem
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨d, hdB, hd1, hdb⟩ : ∃ d ∈ B, d ≠ 1 ∧ (b ≠ 1 → d = b) := by
        by_cases hb1 : b = 1
        · have hBne : B ≠ ⊥ := by
            intro hB
            rw [hB, Subgroup.card_bot] at hB9
            norm_num at hB9
          obtain ⟨d, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
          exact ⟨d, d.2, fun h => hd1 (Subtype.ext h), fun h => absurd hb1 h⟩
        · exact ⟨b, hb, hb1, fun _ => rfl⟩
      obtain ⟨w, hwA, hwd, hwc'⟩ := htr d hdB
      have hwB : w ∈ Subgroup.normalizer (B : Set G) := hWB hwA
      have hwJ : w ∈ Subgroup.normalizer (J : Set G) := hJN hwB
      have hwvJ : w * v * w⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hwJ v).mp hvJ
      have hwb : w * b * w⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hwB b).mp hb
      have hdA : d ∈ A := hdB.1
      have hbA : b ∈ A := hb.1
      have hc'iA : c' ^ i ∈ A := A.zpow_mem hc'A i
      have hwbA : w * b * w⁻¹ ∈ A := hwb.1
      have hconj : w * v * w⁻¹ = (c' * d) ^ i * (w * b * w⁻¹) := by
        rw [← hab]
        have hz : w * c' ^ i * w⁻¹ = (w * c' * w⁻¹) ^ i := by
          have := map_zpow (MulAut.conj w) c' i
          simpa only [MulAut.conj_apply] using this
        calc w * (c' ^ i * b) * w⁻¹ = (w * c' ^ i * w⁻¹) * (w * b * w⁻¹) := by group
          _ = (c' * d) ^ i * (w * b * w⁻¹) := by rw [hz, hwc']
      set u := (w * v * w⁻¹) * v⁻¹ with hu
      have huJ : u ∈ J := J.mul_mem hwvJ (J.inv_mem hvJ)
      have hdi : (c' * d) ^ i = c' ^ i * d ^ i := (Commute.mul_zpow (hcomm c' hc'A d hdA) i)
      have hYA : d ^ i * (w * b * w⁻¹) * b⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem (A.zpow_mem hdA i) hwbA) (A.inv_mem hbA)
      have hu_eq : u = d ^ i * (w * b * w⁻¹) * b⁻¹ := by
        have hc := hcomm (c' ^ i) hc'iA _ hYA
        calc u = c' ^ i * (d ^ i * (w * b * w⁻¹) * b⁻¹) * (c' ^ i)⁻¹ := by
              rw [hu, hconj, hdi, ← hab]
              group
          _ = d ^ i * (w * b * w⁻¹) * b⁻¹ := by rw [hc]; group
      have huB : u ∈ B := by
        rw [hu_eq]
        exact B.mul_mem (B.mul_mem (B.zpow_mem hdB i) hwb) (B.inv_mem hb)
      have hu1 : u = 1 := hBJ1 u huB huJ
      have hd3 : orderOf d = 3 := orderOf_eq_prime (hBe.2 d hdB) hd1
      have h3i : (3 : ℤ) ∣ i := by
        have hdi1 : d ^ i = 1 := by
          by_cases hb1 : b = 1
          · rw [hu_eq, hb1] at hu1
            simpa using hu1
          · have hdb' := hdb hb1
            subst hdb'
            have : w * d * w⁻¹ = d := by rw [hwd, mul_inv_cancel_right]
            rw [hu_eq, this, mul_inv_cancel_right] at hu1
            exact hu1
        have := orderOf_dvd_iff_zpow_eq_one.mpr hdi1
        rwa [hd3] at this
      have hc'i : c' ^ i = 1 := by
        obtain ⟨k, rfl⟩ := h3i
        have hc'3 : c' ^ (3 : ℤ) = 1 := by exact_mod_cast hAe.2 c' hc'A
        rw [zpow_mul, hc'3, one_zpow]
      apply hvB
      rw [← hab, hc'i, one_mul]
      exact hb
    · intro b hb
      have : (⟨b, hb⟩ : ↥B) ∈ J.subgroupOf B := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have hZC : 3 ∣ Nat.card (Subgroup.center C) := by
    have hle : B.subgroupOf C ≤ Subgroup.center C := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp g.2 x (Subgroup.mem_subgroupOf.mp hx)).symm
    have hcard : Nat.card (B.subgroupOf C) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hB9]
    have := Subgroup.card_dvd_of_le hle
    rw [hcard] at this
    exact (show (3 : ℕ) ∣ 9 by norm_num).trans this
  have hcen := card_center_thetaQuot_le_three h46 hS4 hZC hJ
  have hθJ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥J) :=
    (solvable_prime_complement_core_characterization (H := ↥J) h3).2.2.1
  set B' := B.subgroupOf J with hB'
  set f : ↥B' →* ↥J ⧸ aschbacherSolvableCore 3 ↥J :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J)).comp B'.subtype with hf
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    by_contra hx1
    have hx3 : (B'.subtype x) ^ 3 = 1 := by
      have := hBe.2 _ (Subgroup.mem_subgroupOf.mp x.2)
      exact Subtype.ext this
    have hx1' : B'.subtype x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hord : orderOf (⟨B'.subtype x, hx⟩ : aschbacherSolvableCore 3 ↥J) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hx3 hx1'
    have hdvd := orderOf_dvd_natCard (⟨B'.subtype x, hx⟩ : aschbacherSolvableCore 3 ↥J)
    rw [hord] at hdvd
    exact hθJ3 hdvd
  have hrange : f.range ≤ Subgroup.center (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hJC l.2) _ (Subgroup.mem_subgroupOf.mp x.2)).symm
  have hcardr : Nat.card f.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, hB',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBJ).toEquiv, hB9]
  have := Subgroup.card_le_of_le hrange
  omega

theorem layer_eq_bot_of_m22
    (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (hSz : KFacts.KPSz)
    (hM22 : Sec21.Hering214Even.M22E9NoInvol) {A L' : Subgroup G} {c' : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hc'A : c' ∈ A)
    (hAF : A ∈ partTwoF G) (hEF : ∀ E ∈ partTwoE G, E ∈ partTwoF G)
    (hS4 : SectionFourHyp (Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G)))
    (hL' : L' ∈ thetaComponentsAt 3 c')
    (huniq : ∀ K ∈ thetaComponentsAt 3 c', 3 ∣ Nat.card K → K = L')
    (φ : ↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22)
    (hB9 : Nat.card (A ⊓ L' : Subgroup G) = 9) (hAB : A = Subgroup.zpowers c' ⊔ (A ⊓ L'))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (L' ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L')))
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ L' : Subgroup G) : Set G))
    (htr : ∀ d ∈ A ⊓ L', ∃ w ∈ Subgroup.normalizer (A : Set G),
      w * d = d * w ∧ w * c' * w⁻¹ = c' * d)
    (hodd : ¬ 2 ∣ Nat.card ↥(Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L')) :
    CFSG.layer (↥(Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G)) ⧸
      CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G))) = ⊥ := by
  set C := Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G) with hCdef
  have h3all : ∀ K ∈ thetaComponentsIn C, 3 ∣ Nat.card K := fun K hK => by
    by_contra hK3
    exact false_of_mem_thetaComponentsIn_of_not_three_dvd h45 hSz hM22 hAe hA27 hc'A hS4 hL'
      huniq φ hB9 hodd hK hK3
  have hθ : aschbacherSolvableCore 3 ↥C = CFSG.pPrimeCore 3 ↥C := by
    apply aschbacherSolvableCore_eq_pPrimeCore_of_forall
    intro J hJ
    have hJin : J.map C.subtype ∈ thetaComponentsIn C := ⟨J, hJ, rfl⟩
    have := h3all _ hJin
    rwa [Subgroup.card_map_of_injective C.subtype_injective] at this
  apply layer_quotient_eq_bot_of_eq hθ.symm
  apply LocalCores.layer_eq_bot_of_forall
  intro K hK
  obtain ⟨hJ, -⟩ := perfectResidual_comap_mem_thetaComponents Nat.prime_three hK
  have hJin := (⟨_, hJ, rfl⟩ : (inSubgroup perfectResidual
    (K.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥C)))).map C.subtype ∈
      thetaComponentsIn C)
  exact false_of_mem_thetaComponentsIn_of_three_dvd h45 h46 hAe hA27 hc'A hAF hEF hS4 hB9 hAB
    hirr hWB htr hJin (h3all _ hJin)

theorem step1422IQBLayerR_of
    (h131 : Item131) (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (hSz : KFacts.KPSz)
    (h1413 : Item1413CR) (hM22 : Sec21.Hering214Even.M22E9NoInvol) : Step1422IQBLayerR := by
  intro G _ _ A c L hR hfail c' hc'Γ L' hL' hφ hWB htr U hUC hU2 hAU hUA
  obtain ⟨φ⟩ := hφ
  have hS' : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'Γ.1 hL'
  have hD' := hS'.toSec13Data
  obtain ⟨-, hB9, hAB, hirr⟩ := Proof1413Res2.m22_point h131 hD' φ
  have hAE : A ∈ partTwoE G := hD'.mem_partTwoE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := (Late.isE27_of_mem_partTwoE hAE).1
  have hA27 : Nat.card A = 27 := (Late.isE27_of_mem_partTwoE hAE).2
  have hc'A : c' ∈ A := (mem_omegaA_iff.mp hc'Γ.1).1 (Subgroup.mem_zpowers c')
  have hEF : ∀ E ∈ partTwoE G, E ∈ partTwoF G := fun E hE => by
    rw [(hD'.toTheoremFourHyp.partTwoF_eq_partTwoE hD'.partTwoS_eq).1]
    exact hE
  set B := A ⊓ L' with hBdef
  have hCtop : Subgroup.centralizer (B : Set G) ≠ ⊤ := by
    intro hCt
    have hBne : B ≠ ⊥ := by
      intro hB
      rw [hB, Subgroup.card_bot] at hB9
      norm_num at hB9
    obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
    have hbZ : b ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ Subgroup.centralizer (B : Set G) := hCt ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg b hbB).symm
    rcases hD'.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hZ | hZ
    · rw [hZ, Subgroup.mem_bot] at hbZ
      exact hb1 (Subtype.ext hbZ)
    · obtain ⟨x, y, hxy⟩ := hD'.nonabelian
      exact hxy (Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top y) x)
  have hS4 := hD'.toTheoremFourHyp.sectionFourHyp hCtop
  have huniq := (hS'.chosen136.2 c' hc'Γ.1 L' hL').2
  have hodd := (h1413 G A c L hR hfail c' hc'Γ L' hL').1
  apply Proof1418Res3.actsTrivOnLayer3_of_layer_eq_bot
  exact layer_eq_bot_of_m22 h45 h46 hSz hM22 hAe hA27 hc'A hD'.mem_partTwoF hEF hS4 hL'.1 huniq
    φ hB9 hAB hirr hWB htr hodd

end CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB
