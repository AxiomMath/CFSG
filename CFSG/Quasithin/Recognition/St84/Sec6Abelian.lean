module

public import CFSG.Quasithin.Recognition.St84.Sec6Normalizer
public import CFSG.Quasithin.Recognition.St84.PushUp
public import CFSG.GroupTheory.PResidualNormalizer
public import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Syl

import CFSG.Quasithin.Recognition.St84.Gen.PushZL2

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.Quasithin.F6 (sqClosure sqClosure_le normalizer_le_normalizer_sqClosure)

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

private theorem sqClosure_characteristic (P : Subgroup G) :
    ((sqClosure P).subgroupOf P).Characteristic := by
  have hgen : (sqClosure P).subgroupOf P =
      Subgroup.closure {y : ↥P | ∃ a : ↥P, a * a = y} := by
    refine le_antisymm ?_ ?_
    · have hle : sqClosure P ≤
          (Subgroup.closure {y : ↥P | ∃ a : ↥P, a * a = y}).map P.subtype := by
        rw [sqClosure, Subgroup.closure_le]
        rintro x ⟨a, haP, rfl⟩
        have hmem : (⟨a, haP⟩ : ↥P) ^ 2 ∈
            Subgroup.closure {y : ↥P | ∃ b : ↥P, b * b = y} :=
          Subgroup.subset_closure ⟨⟨a, haP⟩, (pow_two _).symm⟩
        simpa using Subgroup.mem_map_of_mem P.subtype hmem
      intro x hx
      have hx' : x ∈ ((Subgroup.closure {y : ↥P | ∃ a : ↥P, a * a = y}).map
          P.subtype).subgroupOf P := Subgroup.mem_subgroupOf.mpr (hle hx)
      change x ∈ ((Subgroup.closure {y : ↥P | ∃ a : ↥P, a * a = y}).map
          P.subtype).comap P.subtype at hx'
      rwa [Subgroup.comap_map_eq_self_of_injective P.subtype_injective] at hx'
    · rw [Subgroup.closure_le]
      rintro y ⟨a, rfl⟩
      show ((a * a : ↥P) : G) ∈ sqClosure P
      exact Subgroup.subset_closure ⟨(a : G), a.2, by simp [pow_two]⟩
  rw [hgen, Subgroup.characteristic_iff_map_eq]
  intro φ
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨a, rfl⟩, hzy⟩
    exact ⟨φ a, by rw [← map_mul]; exact hzy⟩
  · rintro ⟨a, rfl⟩
    exact ⟨φ.symm a * φ.symm a, ⟨φ.symm a, rfl⟩, by simp⟩

private theorem conjSub_sqClosure (g : G) (A : Subgroup G) :
    conjSub g (sqClosure A) = sqClosure (conjSub g A) := by
  have hS : (MulAut.conj g).toMonoidHom '' {x : G | ∃ a ∈ A, a ^ 2 = x} =
      {y : G | ∃ b ∈ conjSub g A, b ^ 2 = y} := by
    ext y
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨(MulAut.conj g).toMonoidHom a, Subgroup.mem_map_of_mem _ ha, ?_⟩
      exact (map_pow (MulAut.conj g).toMonoidHom a 2).symm
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      exact ⟨a ^ 2, ⟨a, ha, rfl⟩, map_pow (MulAut.conj g).toMonoidHom a 2⟩
  rw [sqClosure, conjSub, MonoidHom.map_closure, hS, sqClosure]

private theorem sqClosure_eq_bot_iff {A : Subgroup G} :
    sqClosure A = ⊥ ↔ ∀ x ∈ A, x ^ 2 = 1 := by
  constructor
  · intro h x hx
    have hmem : x ^ 2 ∈ sqClosure A := Subgroup.subset_closure ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot] at hmem
  · intro h
    refine le_antisymm ?_ bot_le
    rw [sqClosure, Subgroup.closure_le]
    rintro x ⟨a, ha, rfl⟩
    exact Subgroup.mem_bot.mpr (h a ha)

private theorem isElemAbelian_of_sqClosure_eq_bot {A : Subgroup G}
    (h : sqClosure A = ⊥) : IsElemAbelian 2 A := by
  have hsq := sqClosure_eq_bot_iff.mp h
  exact ⟨⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun g : A => orderOf_dvd_of_pow_eq_one (Subtype.ext (hsq g g.2))) a b).eq⟩⟩, hsq⟩

private theorem sqClosure_mono {A B : Subgroup G} (h : A ≤ B) : sqClosure A ≤ sqClosure B := by
  rw [sqClosure, sqClosure, Subgroup.closure_le]
  rintro x ⟨a, ha, rfl⟩
  exact Subgroup.subset_closure ⟨a, h ha, rfl⟩

private theorem noCharNormal_Lst {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0) :
    NoCharNormal (X.skP U) (X.Lst U 0) :=
  IsSKMax.noCharNormal_of_le X hU (X.isSylowTwoOf_skP_Lst hU.1).1 (oTwoPrime_le _)
    (X.normGi_eq_Lst_sup_K hU.1 (X.not_skP_le_Q_zero_or_of_isSKMax hU hP))

theorem normGi_le_normalizer_E (U : Subgroup G) (i : ℤ) :
    X.normGi U i ≤ Subgroup.normalizer (X.E U i : Set G) := by
  intro m hm
  obtain ⟨hmM, hmGi⟩ := Subgroup.mem_inf.mp hm
  have hQ : conjSub m (X.Q i) = X.Q i :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i) hmGi)
  have hM : conjSub m (Subgroup.normalizer (U : Set G)) =
      Subgroup.normalizer (U : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hmM)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub m (X.Q i ⊓ Subgroup.normalizer (U : Set G)) =
    X.Q i ⊓ Subgroup.normalizer (U : Set G)
  rw [conjSub_inf, hQ, hM]

private theorem normGi_le_normalizer_Yst (U : Subgroup G) (i : ℤ) :
    X.normGi U i ≤ Subgroup.normalizer (X.Yst U i : Set G) :=
  (le_normalizer_oTwoPrime (X.normGi U i)).trans
    (normalizer_le_normalizer_pResidualOf 2 (X.Lst U i))

private theorem normGi_le_normalizer_commutator (U : Subgroup G) :
    X.normGi U 0 ≤
      Subgroup.normalizer ((⁅X.E U 0, X.Yst U 0⁆ : Subgroup G) : Set G) :=
  CFSG.Quasithin.D14.le_normalizer_commutator (X.normGi_le_normalizer_E U 0)
    (X.normGi_le_normalizer_Yst U 0)

private theorem commutator_E_Yst_le_E (U : Subgroup G) :
    ⁅X.E U 0, X.Yst U 0⁆ ≤ X.E U 0 :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((Subgroup.map_subtype_le _).trans ((oTwoPrime_le _).trans
      (X.normGi_le_normalizer_E U 0)))

theorem E_le_skP {U : Subgroup G} (hU : X.IsSK U) : X.E U 0 ≤ X.skP U :=
  (X.E_eq_inf_skP hU).le.trans inf_le_right

private theorem E_two_le_skP {U : Subgroup G} (hU : X.IsSK U) : X.E U 2 ≤ X.skP U := by
  obtain ⟨t, ht, ht02, -, -⟩ := IsSK.exists_t X hU
  have htM1 : t ∈ X.normGi U 1 := ht.1
  rw [show X.E U 2 = conjSub t (X.E U 0) from (IsSK.conjSub_E_zero X htM1 ht02).symm]
  calc conjSub t (X.E U 0) ≤ conjSub t (X.skP U) :=
        conjSub_mono t (X.E_le_skP hU)
    _ = X.skP U := IsSK.conjSub_skP X htM1 ht02

private theorem conjSub_E_two {U : Subgroup G} {t : G} (ht : t ∈ X.normGi U 1)
    (ht02 : t • X.vert 0 = X.vert 2) (ht2 : t ^ 2 ∈ X.normGi U 0) :
    conjSub t (X.E U 2) = X.E U 0 := by
  rw [← IsSK.conjSub_E_zero X ht ht02, ← conjSub_mul]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (X.normGi_le_normalizer_E U 0 (by simpa [pow_two] using ht2))

private theorem normGi_two_le_normalizer {U C : Subgroup G} {t : G}
    (ht : t ∈ X.normGi U 1) (ht02 : t • X.vert 0 = X.vert 2)
    (h0 : X.normGi U 0 ≤ Subgroup.normalizer (C : Set G))
    (htC : t ∈ Subgroup.normalizer (C : Set G)) :
    X.normGi U 2 ≤ Subgroup.normalizer (C : Set G) := by
  rw [← IsSK.conjSub_normGi_zero X ht ht02]
  intro m hm
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hm
  exact Subgroup.mul_mem (Subgroup.normalizer (C : Set G))
    (Subgroup.mul_mem (Subgroup.normalizer (C : Set G)) htC (h0 ha))
    ((Subgroup.normalizer (C : Set G)).inv_mem htC)

private theorem mem_normGi_zero_of_le_normalizer {U C : Subgroup G} (hU : X.IsSKMax U)
    (hC : C ≠ ⊥) (hCT : C ≤ X.skP U) (h0 : X.normGi U 0 ≤ Subgroup.normalizer (C : Set G))
    {t : G} (ht : t ∈ X.normGi U 1) (ht02 : t • X.vert 0 = X.vert 2)
    (htC : t ∈ Subgroup.normalizer (C : Set G)) {g : G}
    (hgC : g ∈ Subgroup.normalizer (C : Set G)) (hg0 : g ∈ X.Gi 0) : g ∈ X.normGi U 0 := by
  have harc : C ≤ X.arcStab 0 2 := by
    rw [X.arcStab_eq_inf (by norm_num : (0 : ℤ) ≤ 2)]
    refine le_inf ?_ ?_
    · exact hCT.trans (inf_le_right.trans (X.normGi_le_Gi U 0))
    · exact hCT.trans (inf_le_left.trans ((X.Q_le_Gi_adj 1).trans inf_le_right))
  have hSK : X.IsSK C := by
    refine ⟨hC, harc, (hU.1.K_le_normGi 0).trans h0, ?_, ?_, ⟨t, htC, ht02⟩⟩
    · intro a b ha hb
      obtain ⟨m, hm, hmab⟩ := hU.1.trans0 a b ha hb
      exact ⟨m, Subgroup.mem_inf.mpr ⟨h0 hm, hm.2⟩, hmab⟩
    · intro a b ha hb
      obtain ⟨m, hm, hmab⟩ := hU.1.trans2 a b ha hb
      exact ⟨m, Subgroup.mem_inf.mpr
        ⟨X.normGi_two_le_normalizer ht ht02 h0 htC hm, hm.2⟩, hmab⟩
  have hle : X.normGi U 0 ≤ X.normGi C 0 := fun m hm =>
    Subgroup.mem_inf.mpr ⟨h0 hm, hm.2⟩
  exact hU.2 C hSK hle (Subgroup.mem_inf.mpr ⟨hgC, hg0⟩)

private theorem mem_normalizer_E {U : Subgroup G} (hU : X.IsSK U) {g : G} (hg0 : g ∈ X.Gi 0)
    (hgT : g ∈ Subgroup.normalizer (X.skP U : Set G)) :
    g ∈ Subgroup.normalizer (X.E U 0 : Set G) := by
  rw [X.E_eq_inf_skP hU]
  exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr
    ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) hg0, hgT⟩)

theorem isElemAbelian_E_of_commutator_eq_bot {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0)
    (hV : ⁅X.E U 0, X.Yst U 0⁆ = ⊥) :
    IsElemAbelian 2 (X.E U 0) := by
  have hP' := X.not_skP_le_Q_zero_or_of_isSKMax hU hP
  let P : Subgroup G := X.skP U
  let L : Subgroup G := X.Lst U 0
  by_contra hE
  have hEP : X.E U 0 ≤ P := X.E_eq_inf_skP hU.1 ▸ inf_le_right
  have hCne : sqClosure P ≠ ⊥ := by
    intro hbot
    apply hE
    have hmono : sqClosure (X.E U 0) ≤ sqClosure P :=
      sqClosure_mono (by rw [show P = X.skP U from rfl]; exact hEP)
    rw [hbot] at hmono
    exact isElemAbelian_of_sqClosure_eq_bot (le_antisymm hmono bot_le)
  have hP_C : P ≤ Subgroup.normalizer (sqClosure P : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_sqClosure P)
  have hY_C : X.Yst U 0 ≤ Subgroup.normalizer (sqClosure P : Set G) := by
    have hV' : ⁅X.Yst U 0, X.E U 0⁆ = ⊥ := by
      rwa [Subgroup.commutator_comm] at hV
    have hY : X.Yst U 0 ≤ Subgroup.centralizer (X.E U 0 : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hV'
    have hYc : X.Yst U 0 ≤ Subgroup.centralizer (sqClosure P : Set G) :=
      hY.trans (Subgroup.centralizer_le (s := (sqClosure P : Set G))
        (t := (X.E U 0 : Set G)) (fun x hx => sqClosure_skP_le_E X hU.1 hP' hx))
    exact hYc.trans (Subgroup.centralizer_le_normalizer _)
  have hCL : L ≤ Subgroup.normalizer (sqClosure P : Set G) := by
    rw [show L = X.Lst U 0 from rfl, X.Lst_eq_Yst_sup_skP hU.1]
    exact sup_le hY_C hP_C
  exact noCharNormal_Lst X hU hP (sqClosure P) (sqClosure_le P) hCne
    (sqClosure_characteristic P) hCL

theorem commutator_le_centerOf_E {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0)
    (hV : ⁅X.E U 0, X.Yst U 0⁆ ≠ ⊥) :
    ⁅X.E U 0, X.Yst U 0⁆ ≤ centerOf (X.E U 0) ∧
      IsElemAbelian 2 ⁅X.E U 0, X.Yst U 0⁆ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' := X.not_skP_le_Q_zero_or_of_isSKMax hU hP
  have hn : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
  let L : Subgroup G := X.Lst U 0
  let P : Subgroup G := X.skP U
  let E : Subgroup G := X.E U 0
  let Y : Subgroup G := X.Yst U 0
  haveI : Finite ↥L := finite_of_le_stabilizer X.hyp (H := L)
    ((oTwoPrime_le (X.normGi U 0)).trans (X.normGi_le_Gi U 0))
  have hPL : P ≤ L := by
    rw [show L = X.Lst U 0 from rfl, X.Lst_eq_Yst_sup_skP hU.1]
    exact le_sup_right
  have hEpc : E = pCoreOf 2 L := (X.pCoreOf_Lst_eq_E hU.1).symm
  have hEL : E ≤ L := hEpc ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hYL : Y ≤ L := Subgroup.map_subtype_le _
  have hchar : CharTwo (⊤ : Subgroup ↥L) := by
    have hc : CharTwo L := X.charTwo_Lst hU.1 hP' hV
    exact CFSG.Quasithin.Rk2.charTwo_of_equiv (Subgroup.topEquiv (G := ↥L)).symm hc
  have hquot : IsL2Quot (X.n 0) (oTwoQuot ↥(⊤ : Subgroup ↥L)) := by
    obtain ⟨e⟩ := X.isL2Quot_Lst hU.1 hP'
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr (Subgroup.topEquiv (G := ↥L))).trans e⟩
  have hPsyl : IsSylowTwoOf (P.subgroupOf L) ⊤ :=
    CFSG.Quasithin.X1512.sylow_subgroupOf_top (X.isSylowTwoOf_skP_Lst hU.1)
  have hnc : NoCharNormal (P.subgroupOf L) ⊤ :=
    CFSG.Quasithin.F53Push.noCharNormal_subgroupOf hPL (noCharNormal_Lst X hU hP)
  have hbaum := baumannC_pushZ_L2 hn hchar hquot hPsyl hnc
  have hEtop : pCoreOf 2 (⊤ : Subgroup ↥L) = E.subgroupOf L := by
    rw [CFSG.Quasithin.F53Push.pCoreOf_top_eq, ← CFSG.openPCoreOf_subgroupOf 2 L, hEpc]
  have hYtop : pResidualOf 2 (⊤ : Subgroup ↥L) = Y.subgroupOf L := by
    rw [CFSG.GroupTheory.pResidualOf_top_eq_subgroupOf]
    rfl
  have hEtop' : (E.subgroupOf L).map L.subtype = E :=
    Subgroup.map_subgroupOf_eq_of_le hEL
  have hYtop' : (Y.subgroupOf L).map L.subtype = Y :=
    Subgroup.map_subgroupOf_eq_of_le hYL
  have hcomm : ((⁅pCoreOf 2 (⊤ : Subgroup ↥L), pResidualOf 2 (⊤ : Subgroup ↥L)⁆ :
      Subgroup ↥L)).map L.subtype = ⁅E, Y⁆ := by
    rw [hEtop, hYtop, Subgroup.map_commutator, hEtop', hYtop']
  have hVle : ⁅E, Y⁆ ≤ (pushZ (⊤ : Subgroup ↥L) (P.subgroupOf L)).map L.subtype := by
    rw [← hcomm]
    exact Subgroup.map_mono (f := L.subtype) (show ⁅pCoreOf 2 ⊤, pResidualOf 2 ⊤⁆ ≤ _ from hbaum)
  have hW := pushZ_le_centerOf_pCoreOf hchar hPsyl
  have hcenter : (centerOf (pCoreOf 2 (⊤ : Subgroup ↥L))).map L.subtype = centerOf E := by
    rw [centerOf, hEtop, CFSG.Quasithin.C58.map_inf_centralizer_of_injective L.subtype_injective,
      hEtop', centerOf]
  refine ⟨hVle.trans ?_, IsElemAbelian.mono (hW.2.map L.subtype) hVle⟩
  rw [← hcenter]
  exact Subgroup.map_mono (f := L.subtype)
    (show pushZ (⊤ : Subgroup ↥L) (P.subgroupOf L) ≤ centerOf (pCoreOf 2 ⊤) from hW.1)

private theorem cj_conjJoin_le_of_le {H Z : Subgroup G} {g : G}
    (hH : CFSG.Quasithin.F53Push.cj g H ≤ H) (hZ : CFSG.Quasithin.F53Push.cj g Z ≤ Z) :
    CFSG.Quasithin.F53Push.cj g (CFSG.Quasithin.F53Push.conjJoin H Z) ≤
      CFSG.Quasithin.F53Push.conjJoin H Z := by
  rw [CFSG.Quasithin.F53Push.cj, Subgroup.map_le_iff_le_comap]
  refine CFSG.Quasithin.F53Push.conjJoin_le fun h hh => ?_
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_comap]
  have hgh : g * h * g⁻¹ ∈ H := hH (Subgroup.mem_map_of_mem _ hh)
  have hgz : g * z * g⁻¹ ∈ Z := hZ (Subgroup.mem_map_of_mem _ hz)
  have hmem := CFSG.Quasithin.F53Push.cj_le_conjJoin (J := Z) hgh
    (Subgroup.mem_map_of_mem (MulAut.conj (g * h * g⁻¹)).toMonoidHom hgz)
  show g * (h * z * h⁻¹) * g⁻¹ ∈ CFSG.Quasithin.F53Push.conjJoin H Z
  convert hmem using 1
  show g * (h * z * h⁻¹) * g⁻¹ =
    g * h * g⁻¹ * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹
  group

private theorem cj_closure_t'_K_skP {U : Subgroup G} (hU : X.IsSK U) {t t' : G}
    (ht : t ∈ X.normGi U 1 ⊓ Subgroup.normalizer (X.K : Set G))
    (ht02 : t • X.vert 0 = X.vert 2) (htt' : ⁅t, t'⁆ ∈ X.skP U) :
    CFSG.Quasithin.F53Push.cj t
      (Subgroup.closure (({t'} : Set G) ∪ (X.K : Set G) ∪ (X.skP U : Set G))) ≤
      Subgroup.closure (({t'} : Set G) ∪ (X.K : Set G) ∪ (X.skP U : Set G)) := by
  let H : Subgroup G :=
    Subgroup.closure (({t'} : Set G) ∪ (X.K : Set G) ∪ (X.skP U : Set G))
  change CFSG.Quasithin.F53Push.cj t H ≤ H
  have hKH : X.K ≤ H := fun k hk => Subgroup.subset_closure (by simp [hk])
  have hPH : X.skP U ≤ H := fun p hp => Subgroup.subset_closure (by simp [hp])
  have ht'H : t' ∈ H := Subgroup.subset_closure (by simp)
  show (H.map (MulAut.conj t).toMonoidHom) ≤ H
  rw [show H = Subgroup.closure (({t'} : Set G) ∪ (X.K : Set G) ∪ (X.skP U : Set G))
    from rfl, MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  rcases hy with (hy | hy) | hy
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    change t * t' * t⁻¹ ∈
      Subgroup.closure ({t'} ∪ (X.K : Set G) ∪ (X.skP U : Set G))
    have h1 : t * t' * t⁻¹ = ⁅t, t'⁆ * t' := conj_eq_commutatorElement_mul
    rw [show t * t' * t⁻¹ = ⁅t, t'⁆ * t' from h1]
    exact H.mul_mem (hPH htt') ht'H
  · have h := Subgroup.mem_normalizer_iff.mp ht.2 (y : G)
    exact hKH ((h).mp hy)
  · have hmem := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hy
    rw [show (X.skP U).map (MulAut.conj t).toMonoidHom = X.skP U from
      IsSK.conjSub_skP X ht.1 ht02] at hmem
    exact Subgroup.subset_closure (Or.inr hmem)

private theorem closure_t'_K_skP_le_normalizer {U : Subgroup G} (hU : X.IsSK U)
    {t' : G} (ht'G0 : t' ∈ X.Gi 0)
    (ht'P : t' ∈ Subgroup.normalizer (X.skP U : Set G)) :
    Subgroup.closure (({t'} : Set G) ∪ (X.K : Set G) ∪ (X.skP U : Set G)) ≤
      Subgroup.normalizer (X.E U 0 : Set G) := by
  have hPM0 : X.skP U ≤ X.normGi U 0 := inf_le_right
  have ht'Enorm : t' ∈ Subgroup.normalizer (X.E U 0 : Set G) :=
    X.mem_normalizer_E hU ht'G0 ht'P
  rw [Subgroup.closure_le]
  rintro x ((hx | hx) | hx)
  · rw [Set.mem_singleton_iff] at hx
    rwa [hx]
  · exact ((hU.K_le_normGi 0).trans (X.normGi_le_normalizer_E U 0)) hx
  · exact (X.normGi_le_normalizer_E U 0) (hPM0 hx)

private theorem cj_sup_cj_eq {V : Subgroup G} {t : G}
    (hV : t * t ∈ Subgroup.normalizer (V : Set G)) :
    CFSG.Quasithin.F53Push.cj t (V ⊔ CFSG.Quasithin.F53Push.cj t V) =
      V ⊔ CFSG.Quasithin.F53Push.cj t V := by
  have h2 : (CFSG.Quasithin.F53Push.cj t V).map (MulAut.conj t).toMonoidHom = V := by
    change CFSG.Quasithin.F53Push.cj t (CFSG.Quasithin.F53Push.cj t V) = V
    rw [CFSG.Quasithin.F53Push.cj_cj,
      CFSG.Quasithin.F53Push.cj_eq_of_mem_normalizer hV]
  change (V ⊔ CFSG.Quasithin.F53Push.cj t V).map (MulAut.conj t).toMonoidHom =
    V ⊔ CFSG.Quasithin.F53Push.cj t V
  rw [Subgroup.map_sup, h2]
  change CFSG.Quasithin.F53Push.cj t V ⊔ V = V ⊔ CFSG.Quasithin.F53Push.cj t V
  rw [sup_comm]

private theorem mem_normalizer_conjJoin_of_cj {H Z : Subgroup G} {t : G}
    (hHnR : H ≤ Subgroup.normalizer
      (CFSG.Quasithin.F53Push.conjJoin H Z : Set G))
    (hctH : CFSG.Quasithin.F53Push.cj t H ≤ H)
    (hZfix : CFSG.Quasithin.F53Push.cj t Z = Z) (ht2 : t ^ 2 ∈ H) :
    t ∈ Subgroup.normalizer
      (CFSG.Quasithin.F53Push.conjJoin H Z : Set G) := by
  set R : Subgroup G := CFSG.Quasithin.F53Push.conjJoin H Z with hRdef
  have hctR : CFSG.Quasithin.F53Push.cj t R ≤ R := by
    simpa [hRdef] using cj_conjJoin_le_of_le hctH (le_of_eq hZfix)
  have hqN : (t ^ 2)⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normalizer (R : Set G)).inv_mem (by rw [hRdef]; exact hHnR ht2)
  have hctinvR : CFSG.Quasithin.F53Push.cj t⁻¹ R ≤ R := by
    have htinv : t⁻¹ = t * (t ^ 2)⁻¹ := by group
    rw [htinv, ← CFSG.Quasithin.F53Push.cj_cj,
      CFSG.Quasithin.F53Push.cj_eq_of_mem_normalizer hqN]
    exact hctR
  simpa [hRdef] using F7.mem_normalizer_of_conj_le hctR hctinvR

theorem not_commutator_le_E_two {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0) (hV : ⁅X.E U 0, X.Yst U 0⁆ ≠ ⊥) :
    ¬ ⁅X.E U 0, X.Yst U 0⁆ ≤ X.E U 2 := by
  intro hVE2
  have hP' := X.not_skP_le_Q_zero_or_of_isSKMax hU hP
  let M0 : Subgroup G := X.normGi U 0
  let P : Subgroup G := X.skP U
  let E : Subgroup G := X.E U 0
  let E2 : Subgroup G := X.E U 2
  let Y : Subgroup G := X.Yst U 0
  let V : Subgroup G := ⁅E, Y⁆
  have hPM0 : P ≤ M0 := inf_le_right
  have hEP : E ≤ P := X.E_le_skP hU.1
  have hVnormM0 : M0 ≤ Subgroup.normalizer (V : Set G) :=
    X.normGi_le_normalizer_commutator U
  obtain ⟨t, ht, ht02, -, ht2P⟩ := IsSK.exists_t X hU.1
  have htM1 : t ∈ X.normGi U 1 := ht.1
  have hlt : X.skP U ≠ X.Q 1 := X.skP_ne_Q_one hU hP hV
  obtain ⟨t', ht'Q1, ht'M0, ht'P, -, htt'P⟩ :=
    X.exists_t' hU.1 ht.1 ht2P hlt
  have ht'G0 : t' ∈ X.Gi 0 := (X.Q_le_Gi_adj 1).trans inf_le_left ht'Q1
  have hHnormE := X.closure_t'_K_skP_le_normalizer hU.1 ht'G0 ht'P
  let H : Subgroup G := Subgroup.closure (({t'} : Set G) ∪ (X.K : Set G) ∪ (P : Set G))
  have hKH : X.K ≤ H := fun k hk => Subgroup.subset_closure (by simp [hk])
  have hPH : P ≤ H := fun p hp => Subgroup.subset_closure (by simp [hp])
  have ht'H : t' ∈ H := Subgroup.subset_closure (by simp)
  have ht2M0 : t ^ 2 ∈ M0 := hPM0 ht2P
  have ht2M0' : t * t ∈ M0 := by simpa [pow_two] using ht2M0
  have hEt2 : conjSub t E2 = E := X.conjSub_E_two htM1 ht02 ht2M0
  have hVtE : CFSG.Quasithin.F53Push.cj t V ≤ E := by
    calc CFSG.Quasithin.F53Push.cj t V ≤ CFSG.Quasithin.F53Push.cj t E2 :=
          CFSG.Quasithin.F53Push.cj_mono t hVE2
      _ = E := hEt2
  have hVE : V ≤ E := X.commutator_E_Yst_le_E U
  let Z : Subgroup G := V ⊔ CFSG.Quasithin.F53Push.cj t V
  have hZ_E : Z ≤ E := sup_le hVE hVtE
  have hctH := X.cj_closure_t'_K_skP hU.1 ht ht02 htt'P
  have hZfix : CFSG.Quasithin.F53Push.cj t Z = Z := cj_sup_cj_eq (hVnormM0 ht2M0')
  set R : Subgroup G := CFSG.Quasithin.F53Push.conjJoin H Z with hRdef
  have hHnR : H ≤ Subgroup.normalizer (R : Set G) := by
    simpa [hRdef] using CFSG.Quasithin.F53Push.le_normalizer_conjJoin H Z
  have htN : t ∈ Subgroup.normalizer (R : Set G) :=
    mem_normalizer_conjJoin_of_cj hHnR hctH hZfix (hPH ht2P)
  have hRE : R ≤ E := by
    rw [hRdef]
    exact CFSG.Quasithin.F53Push.conjJoin_le_of_le hZ_E hHnormE
  have hVR : V ≤ R := by
    rw [hRdef]
    exact le_trans (le_sup_left : V ≤ Z)
      (CFSG.Quasithin.F53Push.le_conjJoin (X := H) (J := Z))
  have hRY : ⁅R, Y⁆ ≤ R := by
    have h1 : ⁅R, Y⁆ ≤ ⁅E, Y⁆ := Subgroup.commutator_mono hRE le_rfl
    exact h1.trans hVR
  have hYnR : Y ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hRY
  have hM0nR : M0 ≤ Subgroup.normalizer (R : Set G) := by
    rw [show M0 = X.normGi U 0 from rfl,
      X.normGi_eq_Yst_sup_K_sup_skP hU.1 hP']
    exact sup_le (sup_le hYnR (hKH.trans hHnR)) (hPH.trans hHnR)
  have hRne : R ≠ ⊥ := fun hbot => hV (le_bot_iff.mp (hbot ▸ hVR))
  exact ht'M0 (X.mem_normGi_zero_of_le_normalizer hU hRne (hRE.trans hEP) hM0nR
    htM1 ht02 htN (hHnR ht'H) ht'G0)

private theorem sqClosure_sup_eq_right_of_central {H K : Subgroup G}
    (hHK : H ≤ Subgroup.centralizer (K : Set G)) (hH : sqClosure H = ⊥) :
    sqClosure (H ⊔ K) = sqClosure K := by
  refine le_antisymm ?_ (sqClosure_mono le_sup_right)
  rw [sqClosure, Subgroup.closure_le]
  rintro x ⟨a, ha, rfl⟩
  have ha' : a ∈ ((H ⊔ K : Subgroup G) : Set G) := ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H K
    (hHK.trans (Subgroup.centralizer_le_normalizer _))] at ha'
  obtain ⟨h, hh, k, hk, rfl⟩ := Set.mem_mul.mp ha'
  have hcomm : k * h = h * k := Subgroup.mem_centralizer_iff.mp (hHK hh) k hk
  have hh2 : h * h = 1 := by
    have := sqClosure_eq_bot_iff.mp hH h hh
    simpa [pow_two] using this
  have hsq : (h * k) ^ 2 = k * k := by
    rw [pow_two]
    calc (h * k) * (h * k) = h * (k * h) * k := by group
      _ = h * (h * k) * k := by rw [hcomm]
      _ = (h * h) * (k * k) := by group
      _ = k * k := by rw [hh2, one_mul]
  rw [hsq]
  exact Subgroup.subset_closure ⟨k, hk, by rw [pow_two]⟩

private theorem skP_eq_sup_commutator_E2 {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0) (hV : ⁅X.E U 0, X.Yst U 0⁆ ≠ ⊥) :
    X.skP U = ⁅X.E U 0, X.Yst U 0⁆ ⊔ X.E U 2 := by
  let M0 : Subgroup G := X.normGi U 0
  let P : Subgroup G := X.skP U
  let E : Subgroup G := X.E U 0
  let E2 : Subgroup G := X.E U 2
  let Y : Subgroup G := X.Yst U 0
  let V : Subgroup G := ⁅E, Y⁆
  have hEP : E ≤ P := X.E_le_skP hU.1
  have hVnormM0 : M0 ≤ Subgroup.normalizer (V : Set G) :=
    X.normGi_le_normalizer_commutator U
  have hVE : V ≤ E := X.commutator_E_Yst_le_E U
  have hE2P : E2 ≤ P := X.E_two_le_skP hU.1
  have hE2N : X.normGi U 2 ≤ Subgroup.normalizer (E2 : Set G) :=
    X.normGi_le_normalizer_E U 2
  have hK_V : X.K ≤ Subgroup.normalizer (V : Set G) :=
    (hU.1.K_le_normGi 0).trans hVnormM0
  have hK_E2 : X.K ≤ Subgroup.normalizer (E2 : Set G) :=
    (hU.1.K_le_normGi 2).trans hE2N
  have hK_A : X.K ≤ Subgroup.normalizer (V ⊔ E2 : Subgroup G) :=
    CFSG.Quasithin.D14.le_normalizer_sup hK_V hK_E2
  have hA : V ⊔ E2 ≤ P := sup_le (hVE.trans hEP) hE2P
  have hneA : ¬ V ⊔ E2 ≤ E2 := fun h =>
    not_commutator_le_E_two X hU hP hV (le_trans le_sup_left h)
  exact (X.eq_skP_of_K_invariant_two hU.1 le_sup_right hA hK_A hneA).symm

private theorem E_eq_sup_inf_E2 {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0) (hV : ⁅X.E U 0, X.Yst U 0⁆ ≠ ⊥) :
    X.E U 0 = ⁅X.E U 0, X.Yst U 0⁆ ⊔ (X.E U 0 ⊓ X.E U 2) := by
  let M0 : Subgroup G := X.normGi U 0
  let P : Subgroup G := X.skP U
  let E : Subgroup G := X.E U 0
  let E2 : Subgroup G := X.E U 2
  let Y : Subgroup G := X.Yst U 0
  let V : Subgroup G := ⁅E, Y⁆
  let D : Subgroup G := E ⊓ E2
  have hEP : E ≤ P := X.E_le_skP hU.1
  have hPM0 : P ≤ M0 := inf_le_right
  have hVnormM0 : M0 ≤ Subgroup.normalizer (V : Set G) :=
    X.normGi_le_normalizer_commutator U
  have hVE : V ≤ E := X.commutator_E_Yst_le_E U
  have hE2P : E2 ≤ P := X.E_two_le_skP hU.1
  have hVE2 : E2 ≤ Subgroup.normalizer (V : Set G) :=
    (hE2P.trans hPM0).trans hVnormM0
  have hP_eq := skP_eq_sup_commutator_E2 X hU hP hV
  have hDed := Subgroup.inf_sup_assoc_of_le (H := E2) (K := E) (N := V)
    hVE2 hVE
  calc E = E ⊓ P := (inf_eq_left.mpr hEP).symm
    _ = E ⊓ (V ⊔ E2) := by
        change E ⊓ X.skP U = E ⊓ (V ⊔ E2)
        rw [hP_eq]
    _ = (E ⊓ E2) ⊔ V := by
        rw [sup_comm (V) (E2)]
        exact hDed.symm
    _ = V ⊔ D := by rw [show D = E ⊓ E2 from rfl, sup_comm]

private theorem sqClosure_E_eq_sqClosure_E2 {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0) (hV : ⁅X.E U 0, X.Yst U 0⁆ ≠ ⊥) :
    sqClosure (X.E U 0) = sqClosure (X.E U 2) := by
  let M0 : Subgroup G := X.normGi U 0
  let P : Subgroup G := X.skP U
  let E : Subgroup G := X.E U 0
  let E2 : Subgroup G := X.E U 2
  let Y : Subgroup G := X.Yst U 0
  let V : Subgroup G := ⁅E, Y⁆
  let D : Subgroup G := E ⊓ E2
  have hPM0 : P ≤ M0 := inf_le_right
  have hDed : E = V ⊔ D := by
    rw [show E = X.E U 0 from rfl, show V = ⁅X.E U 0, X.Yst U 0⁆ from rfl,
      show D = X.E U 0 ⊓ X.E U 2 from rfl]
    exact E_eq_sup_inf_E2 X hU hP hV
  have hVZ : V ≤ centerOf E := (X.commutator_le_centerOf_E hU hP hV).1
  have hVea : IsElemAbelian 2 V := (X.commutator_le_centerOf_E hU hP hV).2
  have hVcentD : V ≤ Subgroup.centralizer (D : Set G) := by
    have h1 : V ≤ Subgroup.centralizer (E : Set G) :=
      hVZ.trans (by rw [centerOf]; exact inf_le_right)
    exact h1.trans (Subgroup.centralizer_le (s := (D : Set G)) (t := (E : Set G))
      (fun x hx => hx.1))
  have hVsq : sqClosure V = ⊥ :=
    sqClosure_eq_bot_iff.mpr (fun x hx => hVea.2 x hx)
  have hPhiE : sqClosure E = sqClosure D := by
    rw [hDed]
    exact sqClosure_sup_eq_right_of_central hVcentD hVsq
  obtain ⟨t, ht, ht02, -, ht2P⟩ := IsSK.exists_t X hU.1
  have htM1 : t ∈ X.normGi U 1 := ht.1
  have hEt2 : conjSub t E = E2 := IsSK.conjSub_E_zero X htM1 ht02
  have hE2t : conjSub t E2 = E := X.conjSub_E_two htM1 ht02 (hPM0 ht2P)
  have hDt : conjSub t D = D := by
    rw [show D = E ⊓ E2 from rfl, conjSub_inf, hEt2, hE2t, inf_comm]
  have hPhiE2 : sqClosure E2 = sqClosure D := by
    calc sqClosure E2 = sqClosure (conjSub t E) := by rw [hEt2]
      _ = conjSub t (sqClosure E) := (conjSub_sqClosure t E).symm
      _ = conjSub t (sqClosure D) := by rw [hPhiE]
      _ = sqClosure (conjSub t D) := conjSub_sqClosure t D
      _ = sqClosure D := by rw [hDt]
  rw [hPhiE, hPhiE2]

theorem isElemAbelian_E_of_commutator_ne_bot {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0) (hV : ⁅X.E U 0, X.Yst U 0⁆ ≠ ⊥) :
    IsElemAbelian 2 (X.E U 0) := by
  let M0 : Subgroup G := X.normGi U 0
  let P : Subgroup G := X.skP U
  let E : Subgroup G := X.E U 0
  let E2 : Subgroup G := X.E U 2
  have hEP : E ≤ P := X.E_le_skP hU.1
  obtain ⟨t, ht, ht02, -, ht2P⟩ := IsSK.exists_t X hU.1
  have htM1 : t ∈ X.normGi U 1 := ht.1
  have hlt : X.skP U ≠ X.Q 1 := X.skP_ne_Q_one hU hP hV
  obtain ⟨t', ht'Q1, ht'M0, ht'P, -, -⟩ :=
    X.exists_t' hU.1 ht.1 ht2P hlt
  have ht'G0 : t' ∈ X.Gi 0 := (X.Q_le_Gi_adj 1).trans inf_le_left ht'Q1
  have ht'Enorm : t' ∈ Subgroup.normalizer (E : Set G) :=
    X.mem_normalizer_E hU.1 ht'G0 ht'P
  have hPhi : sqClosure E = sqClosure E2 :=
    sqClosure_E_eq_sqClosure_E2 X hU hP hV
  have hEt2 : conjSub t E = E2 := IsSK.conjSub_E_zero X htM1 ht02
  set H0 : Subgroup G := sqClosure E with hH0
  have hH0E : H0 ≤ E := by rw [hH0]; exact sqClosure_le E
  have hM0N : M0 ≤ Subgroup.normalizer (H0 : Set G) :=
    (X.normGi_le_normalizer_E U 0).trans (normalizer_le_normalizer_sqClosure E)
  have htN : t ∈ Subgroup.normalizer (H0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub t H0 = H0
    rw [hH0, conjSub_sqClosure, hEt2, ← hPhi]
  have ht'N : t' ∈ Subgroup.normalizer (H0 : Set G) :=
    normalizer_le_normalizer_sqClosure E ht'Enorm
  have hBot : H0 = ⊥ := by
    by_contra hne
    exact ht'M0 (X.mem_normGi_zero_of_le_normalizer hU hne (hH0E.trans hEP) hM0N htM1 ht02
      htN ht'N ht'G0)
  exact isElemAbelian_of_sqClosure_eq_bot (by rw [← hH0]; exact hBot)

theorem isElemAbelian_E {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0) :
    IsElemAbelian 2 (X.E U 0) := by
  by_cases hV : ⁅X.E U 0, X.Yst U 0⁆ = ⊥
  · exact isElemAbelian_E_of_commutator_eq_bot X hU hP hV
  · exact isElemAbelian_E_of_commutator_ne_bot X hU hP hV

end Setup

end CFSG.Quasithin.St84
