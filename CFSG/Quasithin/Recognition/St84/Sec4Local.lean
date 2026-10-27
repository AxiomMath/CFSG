module

public import CFSG.GroupTheory.SylowTwoOfConj
public import CFSG.Quasithin.Recognition.St84.Sec4Setup
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.GH74.QTGen4.DSGen4.Defs

import CFSG.Quasithin.Recognition.St84.Gen.Sec6TorusCent
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

@[expose] noncomputable def vertZ (v : V) : Subgroup G :=
  ⨆ (P : Subgroup G) (_ : IsSylowTwoOf P (MulAction.stabilizer G v)),
    centerOf P ⊓ pCoreOf 2 (MulAction.stabilizer G v)

theorem vertZ_smul (g : G) (v : V) : vertZ (g • v) = conjSub g (vertZ v) := by
  unfold vertZ
  rw [stabilizer_smul_eq_conjSub]
  exact Setup.iSup_sylow_center_conj g (MulAction.stabilizer G v)

theorem vertZ_le_pCoreOf (v : V) :
    vertZ (G := G) v ≤ pCoreOf 2 (MulAction.stabilizer G v) :=
  iSup₂_le fun _ _ => inf_le_right

theorem centerOf_conjSub (g : G) (H : Subgroup G) :
    centerOf (conjSub g H) = conjSub g (centerOf H) :=
  (CFSG.Quasithin.centerOf_map_mulEquiv (MulAut.conj g) H).symm

theorem le_normalizer_centerOf_self (L : Subgroup G) :
    L ≤ Subgroup.normalizer (centerOf L : Set G) :=
  Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf L)

private theorem normal_subgroupOf_of_le_centerOf {H K : Subgroup G}
    (hK : K ≤ centerOf H) : (K.subgroupOf H).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer ((Subgroup.le_centralizer_iff.mp
    (hK.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _))

namespace Setup

variable (X : Setup Γ G)
variable {r : ℕ}

theorem Z_eq_vertZ (i : ℤ) : X.Z i = vertZ (X.vert i) := rfl

theorem Q_le_L (i : ℤ) : X.Q i ≤ X.L i :=
  le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi i)) (X.Q_le_Gi i)

theorem isSylowTwoOf_edgeSylow_Gi (i : ℤ) : IsSylowTwoOf (X.edgeSylow i) (X.Gi i) :=
  isSylowTwoOf_of_edgeStab X.hyp (X.adj i) (X.isSylowTwoOf_edgeSylow i)

theorem isSylowTwoOf_edgeSylow_Gi_succ (i : ℤ) :
    IsSylowTwoOf (X.edgeSylow i) (X.Gi (i + 1)) := by
  have h' : IsSylowTwoOf (X.edgeSylow i) (X.Gi (i + 1) ⊓ X.Gi i) := by
    simpa [inf_comm] using X.isSylowTwoOf_edgeSylow i
  exact isSylowTwoOf_of_edgeStab X.hyp (X.adj i).symm h'

theorem le_edgeSylow_of_le_inf {U : Subgroup G} (k : ℤ) (hU : IsPGroup 2 U)
    (hG : U ≤ X.Gi k ⊓ X.Gi (k + 1)) : U ≤ X.edgeSylow k := by
  haveI : Finite ↥(X.Gi k ⊓ X.Gi (k + 1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi k ⊓ X.Gi (k + 1)) inf_le_left
  exact le_of_normal_isSylowTwoOf (S := X.edgeSylow k) (H := X.Gi k ⊓ X.Gi (k + 1))
    (X.isSylowTwoOf_edgeSylow k) (X.edgeSylow_subgroupOf_normal k) hG hU

theorem pCoreOf_arcStab_le_Q_of_lt_of_lt {a c j : ℤ} (haj : a < j) (hjc : j < c) :
    pCoreOf 2 (X.arcStab a c) ≤ X.Q j := by
  have hP : pCoreOf 2 (X.arcStab a c) ≤ X.arcStab a c :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hac : a ≤ c := (lt_trans haj hjc).le
  have hPa : pCoreOf 2 (X.arcStab a c) ≤ X.Gi a :=
    hP.trans (X.arcStab_le_Gi_of_between le_rfl hac)
  have hPc : pCoreOf 2 (X.arcStab a c) ≤ X.Gi c :=
    hP.trans (X.arcStab_le_Gi_of_between hac le_rfl)
  have hPGi : pCoreOf 2 (X.arcStab a c) ≤ X.Gi j :=
    hP.trans (X.arcStab_le_Gi_of_between haj.le hjc.le)
  refine le_pCoreOf_of_isPGroup_fixes_two X.hyp (pCoreOf_isPGroup' (X.arcStab a c)) hPGi
    (X.toTrack.adj_pred j) (X.adj j) (X.toTrack.ne_pred_succ j) ?_ ?_
  · intro y hy
    exact MulAction.mem_stabilizer_iff.mp
      (X.mem_Gi_of_between (hPa hy) (hPc hy) (by omega) (by omega))
  · intro y hy
    exact MulAction.mem_stabilizer_iff.mp
      (X.mem_Gi_of_between (hPa hy) (hPc hy) (by omega) (by omega))

theorem exists_generator_Ki (i : ℤ) (hn : 2 ≤ X.n i) :
    ∃ k ∈ X.Ki i, k ≠ 1 ∧ orderOf k = 2 ^ X.n i - 1 ∧ Subgroup.zpowers k = X.Ki i := by
  haveI : IsCyclic ↥(X.Ki i) := X.isCyclic_Ki i
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := ↥(X.Ki i))
  have hkKi : (k : G) ∈ X.Ki i := k.2
  have hkord : orderOf (k : G) = 2 ^ X.n i - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hk, X.card_Ki i]
  have hk1 : (k : G) ≠ 1 := by
    intro h
    have hne : 2 ^ X.n i - 1 ≠ 1 := by
      have h4 : 4 ≤ 2 ^ X.n i := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ X.n i := Nat.pow_le_pow_right (by norm_num) hn
      omega
    exact hne (by rw [← hkord, h, orderOf_one])
  refine ⟨(k : G), hkKi, hk1, hkord, ?_⟩
  haveI : Finite ↥(X.Ki i) :=
    finite_of_le_stabilizer X.hyp (inf_le_right.trans (X.L_le_Gi i))
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkKi) ?_
  rw [Nat.card_zpowers, hkord, X.card_Ki i]

theorem K_le_normalizer_Q_inf_centralizer_Ki (i : ℤ) :
    X.K ≤ Subgroup.normalizer
      ((X.Q i ⊓ Subgroup.centralizer (X.Ki i : Set G) : Subgroup G) : Set G) :=
  (le_inf ((X.K_le_Gi i).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i)))
    (B6.le_normalizer_centralizer
      ((le_inf Subgroup.le_normalizer
          ((X.K_le_Gi i).trans (le_normalizer_oTwoPrime (X.Gi i)))).trans
        Subgroup.inf_normalizer_le_normalizer_inf))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem HasB.Z_le_Gi {X : Setup Γ G} {i j : ℤ} {d : ℕ} (hd : X.HasB i d)
    (hj : (j - i).natAbs ≤ d) : X.Z i ≤ X.Gi j := by
  simpa [show i + (j - i) = j by ring] using hd.1 (j - i) hj

theorem HasB.unique {X : Setup Γ G} {i : ℤ} {d d' : ℕ} (hd : X.HasB i d)
    (hd' : X.HasB i d') : d = d' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hd.2.1 (by simpa [add_assoc] using hd'.1 ((d : ℤ) + 1) (by omega))
  · exact hd'.2.1 (by simpa [add_assoc] using hd.1 ((d' : ℤ) + 1) (by omega))

theorem K_inf_Q_eq_bot (i : ℤ) : X.K ⊓ X.Q i = ⊥ :=
  eq_bot_mono (inf_le_inf_left _ (X.Q_le_edgeSylow_left i)) (X.K_inf_edgeSylow i)

private theorem map_subgroupOf_L_eq_pointSylow (i : ℤ) {A : Subgroup G} {a : V}
    (hA : IsSylowTwoOf A (X.L i)) (hAfix : A ≤ MulAction.stabilizer G a)
    (ha : Γ.Adj (X.vert i) a) :
    (A.subgroupOf (X.L i)).map (X.hyp.isLocL2_oTwoPrime (X.vert i)).phi =
      ((X.hyp.isLocL2_oTwoPrime (X.vert i)).pointSylow X.hyp.adj_smul
        (X.hyp.finite_stab _) (X.hyp.valency (X.vert i)).2
        (X.hyp.valency (X.vert i)).1 a :
        Subgroup (PSL(2, GaloisField 2 (X.n i)))) := by
  have hN : IsLocL2 Γ G (X.vert i) (X.n i) (X.L i) := X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hadj := X.hyp.adj_smul
  have hfin : Finite (MulAction.stabilizer G (X.vert i)) := X.hyp.finite_stab _
  haveI : Finite ↥(X.L i) := finite_of_le_stabilizer X.hyp (X.L_le_Gi i)
  have hcard : Nat.card (Γ.neighborSet (X.vert i)) = 2 ^ X.n i + 1 :=
    (X.hyp.valency (X.vert i)).2
  have hn1 : 1 ≤ X.n i := (X.hyp.valency (X.vert i)).1
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow hA
  let U : Sylow 2 (PSL(2, GaloisField 2 (X.n i))) := S.mapSurjective hN.phi_surjective
  have hUcoe : (U : Subgroup (PSL(2, GaloisField 2 (X.n i)))) =
      (A.subgroupOf (X.L i)).map hN.phi := by
    show (S.mapSurjective hN.phi_surjective :
      Subgroup (PSL(2, GaloisField 2 (X.n i)))) = _
    rw [Sylow.coe_mapSurjective, hS]
  have hUleBorel : (U : Subgroup (PSL(2, GaloisField 2 (X.n i)))) ≤ hN.pointBorel a := by
    intro z hz
    have hz' : z ∈ (A.subgroupOf (X.L i)).map hN.phi := hUcoe ▸ hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz'
    have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
    have hypoint : y ∈ hN.pointSubgroup a := by
      rw [hN.pointSubgroup_eq_stabilizer hadj ha, MulAction.mem_stabilizer_iff]
      exact Subtype.ext (hAfix hyA)
    rwa [hN.pointSubgroup_eq_comap_pointBorel hadj hfin hcard hn1 ha] at hypoint
  have hUeq : U = hN.pointSylow hadj hfin hcard hn1 a := by
    refine IsLocL2.sylow_eq_of_le_normalizer hn1 ?_
    rwa [hN.pointBorel_eq_normalizer hadj hfin hcard hn1 ha] at hUleBorel
  rw [← hUcoe, hUeq]

theorem edgeSylow_sup_edgeSylow (i : ℤ) : X.edgeSylow (i - 1) ⊔ X.edgeSylow i = X.L i := by
  symm
  have hN : IsLocL2 Γ G (X.vert i) (X.n i) (X.L i) := X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hadj := X.hyp.adj_smul
  have hfin : Finite (MulAction.stabilizer G (X.vert i)) := X.hyp.finite_stab _
  have hcard : Nat.card (Γ.neighborSet (X.vert i)) = 2 ^ X.n i + 1 :=
    (X.hyp.valency (X.vert i)).2
  have hn1 : 1 ≤ X.n i := (X.hyp.valency (X.vert i)).1
  have hleft : Γ.Adj (X.vert i) (X.vert (i - 1)) := X.toTrack.adj_pred i
  have hright : Γ.Adj (X.vert i) (X.vert (i + 1)) := X.adj i
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := X.toTrack.ne_pred_succ i
  have hAsyl : IsSylowTwoOf (X.edgeSylow (i - 1)) (X.L i) := by
    have h := X.isSylowTwoOf_edgeSylow_L_succ (i - 1)
    rwa [show i - 1 + 1 = i by omega] at h
  have hBsyl : IsSylowTwoOf (X.edgeSylow i) (X.L i) := X.isSylowTwoOf_edgeSylow_L i
  have hAfix : X.edgeSylow (i - 1) ≤ MulAction.stabilizer G (X.vert (i - 1)) :=
    (X.isSylowTwoOf_edgeSylow (i - 1)).1.trans inf_le_left
  have hBfix : X.edgeSylow i ≤ MulAction.stabilizer G (X.vert (i + 1)) :=
    (X.isSylowTwoOf_edgeSylow i).1.trans inf_le_right
  have hmapA := X.map_subgroupOf_L_eq_pointSylow i hAsyl hAfix hleft
  have hmapB := X.map_subgroupOf_L_eq_pointSylow i hBsyl hBfix hright
  have hpointne : hN.pointSylow hadj hfin hcard hn1 (X.vert (i - 1)) ≠
      hN.pointSylow hadj hfin hcard hn1 (X.vert (i + 1)) := by
    intro h
    have hbij := hN.pointSylow_bijective hadj hfin hcard hn1
    have hΔ : (⟨X.vert (i - 1), hleft⟩ : ↥(hN.neighborAction hadj)) =
        ⟨X.vert (i + 1), hright⟩ := hbij.1 h
    exact hne (congrArg Subtype.val hΔ)
  have hmapTop : ((X.edgeSylow (i - 1)).subgroupOf (X.L i) ⊔
      (X.edgeSylow i).subgroupOf (X.L i)).map hN.phi = ⊤ := by
    rw [Subgroup.map_sup, hmapA, hmapB]
    exact psl2_sylow_two_sup_eq_top hn1 hpointne
  apply le_antisymm _ (sup_le hAsyl.1 hBsyl.1)
  intro x hx
  have hxmem : hN.phi ⟨x, hx⟩ ∈
      ((X.edgeSylow (i - 1)).subgroupOf (X.L i) ⊔
        (X.edgeSylow i).subgroupOf (X.L i)).map hN.phi := by
    rw [hmapTop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyφ⟩ := Subgroup.mem_map.mp hxmem
  have hyAB : (y : G) ∈ X.edgeSylow (i - 1) ⊔ X.edgeSylow i := by
    have hsub : (X.edgeSylow (i - 1)).subgroupOf (X.L i) ⊔
        (X.edgeSylow i).subgroupOf (X.L i) =
        (X.edgeSylow (i - 1) ⊔ X.edgeSylow i).subgroupOf (X.L i) :=
      (Subgroup.subgroupOf_sup hAsyl.1 hBsyl.1).symm
    rw [hsub] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  have hxQ : x * (y : G)⁻¹ ∈ X.Q i := by
    have hmemL : x * (y : G)⁻¹ ∈ X.L i :=
      (X.L i).mul_mem hx ((X.L i).inv_mem y.2)
    have h1 : hN.phi ⟨x * (y : G)⁻¹, hmemL⟩ = 1 := by
      have hmul : (⟨x * (y : G)⁻¹, hmemL⟩ : ↥(X.L i)) = ⟨x, hx⟩ * (y)⁻¹ := rfl
      rw [hmul, map_mul, map_inv, hyφ, mul_inv_cancel]
    have := (hN.phi_ker ⟨x * (y : G)⁻¹, hmemL⟩).mp h1
    simpa [Setup.Q] using this
  have hQleA : X.Q i ≤ X.edgeSylow (i - 1) := by
    have h := X.Q_le_edgeSylow (i - 1)
    rwa [show i - 1 + 1 = i by omega] at h
  have hdec : x = (x * (y : G)⁻¹) * (y : G) := by group
  rw [hdec]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hQleA hxQ)) hyAB

theorem le_centerOf_L (hc : CharTwoStab (V := V) (G := G)) (i : ℤ)
    {U : Subgroup G} (hU : U ≤ X.Gi i)
    (h₁ : X.edgeSylow (i - 1) ≤ Subgroup.centralizer (U : Set G))
    (h₂ : X.edgeSylow i ≤ Subgroup.centralizer (U : Set G)) :
    U ≤ centerOf (X.L i) := by
  have hcentQ : U ≤ Subgroup.centralizer (X.Q i : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (h₂ (X.Q_le_edgeSylow_left i hq)) u hu).symm
  have hUL : U ≤ X.L i := by
    intro u hu
    have hQ : u ∈ X.Q i := (hc (X.vert i)) ⟨hU hu, hcentQ hu⟩
    exact X.Q_le_L i hQ
  refine le_inf hUL ?_
  rw [Subgroup.le_centralizer_iff]
  rw [(X.edgeSylow_sup_edgeSylow i).symm]
  exact sup_le h₁ h₂

theorem centerOf_L_le_Z (hc : CharTwoStab (V := V) (G := G)) (i : ℤ) :
    centerOf (X.L i) ≤ X.Z i := by
  intro z hz
  obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzGi : z ∈ X.Gi i := X.L_le_Gi i hzL
  have hQL : X.Q i ≤ X.L i := X.Q_le_L i
  have hzQ : z ∈ X.Q i :=
    (hc (X.vert i)) ⟨hzGi, (Subgroup.centralizer_le hQL) hzC⟩
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  obtain ⟨P, hP, -⟩ := exists_isSylowTwoOf_ge_of_finite
    (J := X.Gi i) (pCoreOf_isPGroup' (X.Gi i)) (X.Q_le_Gi i)
  have hPL : P ≤ X.L i := le_oTwoPrime_of_isPGroup hP.2.1 hP.1
  have hterm : z ∈ centerOf P ⊓ X.Q i :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨pCoreOf_le_of_isSylowTwoOf hP hzQ,
        (Subgroup.centralizer_le hPL) hzC⟩, hzQ⟩
  exact (le_iSup₂_of_le
    (f := fun P (_ : IsSylowTwoOf P (X.Gi i)) => centerOf P ⊓ X.Q i)
    (a := centerOf P ⊓ X.Q i) P hP le_rfl) hterm

theorem L_eq_commutator_sup_Q {n : ℕ} (i : ℤ) (hn : 2 ≤ n)
    (hq : IsL2Quot n (oTwoQuot ↥(X.L i))) : X.L i = ⁅X.L i, X.L i⁆ ⊔ X.Q i := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num) hn)
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI hperf : Group.IsPerfect (oTwoQuot ↥(X.L i)) := by
    obtain ⟨e⟩ := hq
    exact CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 (F := GaloisField 2 n) h4
      (e.trans (CFSG.Quasithin.pslTwoGf2EquivSl n))
  let π : ↥(X.L i) →* oTwoQuot ↥(X.L i) := QuotientGroup.mk' (pCore 2 ↥(X.L i))
  have hmap : (commutator ↥(X.L i)).map π = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  have hsup : commutator ↥(X.L i) ⊔ pCore 2 ↥(X.L i) = ⊤ := by
    have h := Subgroup.comap_map_eq π (commutator ↥(X.L i))
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hsupG : ⁅X.L i, X.L i⁆ ⊔ pCoreOf 2 (X.L i) = X.L i := by
    have hmap := congrArg (Subgroup.map (X.L i).subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_subtype_commutator,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    simpa [pCoreOf] using hmap
  have hfin := hsupG.symm
  rwa [(X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq] at hfin

theorem mem_centerOf_L_of_commutator_mem {i : ℤ} (hL : X.L i = ⁅X.L i, X.L i⁆ ⊔ X.Q i)
    {v : G} (hv : v ∈ centerOf (X.Q i))
    (hvL : ∀ l ∈ X.L i, ⁅v, l⁆ ∈ centerOf (X.L i)) : v ∈ centerOf (X.L i) := by
  have hvQ : v ∈ X.Q i := (Subgroup.mem_inf.mp hv).1
  have hvL0 : v ∈ X.L i :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi i)) (X.Q_le_Gi i) hvQ
  let φ : ↥(X.L i) →* ↥(centerOf (X.L i)) :=
    { toFun := fun a => ⟨⁅v, (a : G)⁆, hvL a a.2⟩
      map_one' := by
        refine Subtype.ext ?_
        simp
      map_mul' := by
        intro a b
        refine Subtype.ext ?_
        have hcent : (⁅v, (b : G)⁆ : G) ∈ centerOf (X.L i) := hvL b b.2
        have hcomm : Commute (a : G) ⁅v, (b : G)⁆ := by
          have hc := (Subgroup.mem_inf.mp hcent).2
          exact Subgroup.mem_centralizer_iff.mp hc (a : G) a.2
        have hb' : (a : G) * ⁅v, (b : G)⁆ * (a : G)⁻¹ = ⁅v, (b : G)⁆ := by
          rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
        show ⁅v, ((a : G) * (b : G))⁆ = ⁅v, (a : G)⁆ * ⁅v, (b : G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        calc ⁅v, (a : G)⁆ * (a : G) * ⁅v, (b : G)⁆ * (a : G)⁻¹ =
            ⁅v, (a : G)⁆ * ((a : G) * ⁅v, (b : G)⁆ * (a : G)⁻¹) := by group
          _ = ⁅v, (a : G)⁆ * ⁅v, (b : G)⁆ := by rw [hb'] }
  have hcomm_top : ⁅(⊤ : Subgroup ↥(X.L i)), (⊤ : Subgroup ↥(X.L i))⁆ ≤ φ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker]
    have h1 := map_commutatorElement φ a b
    have h2 : ⁅φ a, φ b⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      refine Subtype.ext ?_
      have ha := (Subgroup.mem_inf.mp (φ a).2).2
      have hb := (Subgroup.mem_inf.mp (φ b).2).1
      exact (Subgroup.mem_centralizer_iff.mp ha (φ b : G) hb).symm
    rw [h1, h2]
  have hL0' : ∀ a ∈ ⁅X.L i, X.L i⁆, ⁅v, a⁆ = 1 := by
    intro a ha
    rw [← Subgroup.map_subtype_commutator (X.L i)] at ha
    obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp ha
    have hker := hcomm_top hc
    rw [MonoidHom.mem_ker] at hker
    have hval : ⁅v, (c : G)⁆ = 1 := congrArg Subtype.val hker
    rw [← hca]
    exact hval
  have hQ0' : ∀ a ∈ X.Q i, ⁅v, a⁆ = 1 := by
    intro a ha
    have hc : v ∈ Subgroup.centralizer (X.Q i : Set G) := (Subgroup.mem_inf.mp hv).2
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hc a ha).symm
  have hLall : X.L i ≤ Subgroup.centralizer ({v} : Set G) := by
    rw [hL]
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commutatorElement_eq_one_iff_mul_comm.mp (hL0' a ha)).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commutatorElement_eq_one_iff_mul_comm.mp (hQ0' a ha)).symm
  refine Subgroup.mem_inf.mpr ⟨hvL0, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h := hLall hl
  rwa [Subgroup.mem_centralizer_singleton_iff] at h

theorem centerOf_L_add (m i : ℤ) :
    centerOf (X.L (i + 2 * m)) = conjSub (X.τ ^ m) (centerOf (X.L i)) := by
  rw [X.L_add, centerOf_conjSub]

theorem Z_eq_centerOf_of_even_sub {i j : ℤ} (hij : Even (j - i))
    (h : X.Z i = centerOf (X.L i)) : X.Z j = centerOf (X.L j) := by
  obtain ⟨m, hm⟩ := hij
  obtain rfl : j = i + 2 * m := by omega
  rw [X.Z_add m i, X.centerOf_L_add m i, h]

theorem Gi_le_normalizer_centerOf_L (i : ℤ) :
    X.Gi i ≤ Subgroup.normalizer (centerOf (X.L i) : Set G) :=
  (le_normalizer_oTwoPrime (X.Gi i)).trans
    (CFSG.Quasithin.normalizer_le_normalizer_centerOf (X.L i))

theorem centerOf_L_inf_succ (hc : CharTwoStab (V := V) (G := G)) (i : ℤ) :
    centerOf (X.L i) ⊓ centerOf (X.L (i + 1)) = ⊥ := by
  apply eq_bot_of_normal_in_oTwoPrime X.hyp (X.adj i)
  · exact inf_le_left.trans inf_le_left
  · exact normal_subgroupOf_of_le_centerOf inf_le_left
  · exact inf_le_right.trans inf_le_left
  · exact normal_subgroupOf_of_le_centerOf inf_le_right

theorem centerOf_L_le_Q_adj (hc : CharTwoStab (V := V) (G := G)) (i : ℤ) :
    centerOf (X.L (i + 1)) ≤ X.Q i ∧ centerOf (X.L i) ≤ X.Q (i + 1) := by
  constructor
  · intro z hz
    have hzL : z ∈ X.L (i + 1) := (Subgroup.mem_inf.mp hz).1
    have hzC : z ∈ Subgroup.centralizer (X.L (i + 1) : Set G) := (Subgroup.mem_inf.mp hz).2
    have hzQ : z ∈ X.Q (i + 1) := X.Z_le_Q (i + 1) (X.centerOf_L_le_Z hc (i + 1) hz)
    have hzGi : z ∈ X.Gi i := by
      have h := (Subgroup.mem_inf.mp ((X.Q_le_Gi_adj (i + 1)) hzQ)).1
      simpa using h
    have hQi : X.Q i ≤ X.L (i + 1) :=
      le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi i))
        (fun x hx => by
          have h := (Subgroup.mem_inf.mp ((X.Q_le_Gi_adj i) hx)).2
          simpa using h)
    exact (hc (X.vert i)) ⟨hzGi, (Subgroup.centralizer_le hQi) hzC⟩
  · intro z hz
    have hzL : z ∈ X.L i := (Subgroup.mem_inf.mp hz).1
    have hzC : z ∈ Subgroup.centralizer (X.L i : Set G) := (Subgroup.mem_inf.mp hz).2
    have hzQ : z ∈ X.Q i := X.Z_le_Q i (X.centerOf_L_le_Z hc i hz)
    have hzGi : z ∈ X.Gi (i + 1) := by
      have h := (Subgroup.mem_inf.mp ((X.Q_le_Gi_adj i) hzQ)).2
      simpa using h
    have hQi : X.Q (i + 1) ≤ X.L i :=
      le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi (i + 1)))
        (fun x hx => by
          have h := (Subgroup.mem_inf.mp ((X.Q_le_Gi_adj (i + 1)) hx)).1
          simpa using h)
    exact (hc (X.vert (i + 1))) ⟨hzGi, (Subgroup.centralizer_le hQi) hzC⟩

theorem centerOf_sylow_le_Z (hc : CharTwoStab (V := V) (G := G)) (i : ℤ)
    {P : Subgroup G} (hP : IsSylowTwoOf P (X.Gi i)) :
    centerOf P ≤ X.Z i ∧
      X.Z i ⊓ Subgroup.centralizer (P : Set G) = centerOf P := by
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  have hQP : X.Q i ≤ P := pCoreOf_le_of_isSylowTwoOf hP
  have hle : centerOf P ≤ centerOf P ⊓ X.Q i := by
    refine le_inf le_rfl ?_
    intro z hz
    obtain ⟨hzP, hzC⟩ := Subgroup.mem_inf.mp hz
    exact (hc (X.vert i)) ⟨hP.1 hzP, (Subgroup.centralizer_le hQP) hzC⟩
  have hfirst : centerOf P ≤ X.Z i :=
    hle.trans (le_iSup₂_of_le
      (f := fun P (_ : IsSylowTwoOf P (X.Gi i)) => centerOf P ⊓ X.Q i)
      (a := centerOf P ⊓ X.Q i) P hP le_rfl)
  refine ⟨hfirst, le_antisymm ?_ ?_⟩
  · exact le_inf (fun x hx => hQP (X.Z_le_Q i (Subgroup.mem_inf.mp hx).1)) inf_le_right
  · exact le_inf hfirst inf_le_right

theorem Z_eq_centerOf_of_centralizes (hc : CharTwoStab (V := V) (G := G)) (i : ℤ)
    {P : Subgroup G} (hP : IsSylowTwoOf P (X.Gi i))
    (hL : X.L i ≤ Subgroup.centralizer (centerOf P : Set G)) :
    X.Z i = centerOf P ∧ X.Z i = centerOf (X.L i) := by
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  haveI : Finite ↥(X.L i) := finite_of_le_stabilizer X.hyp (X.L_le_Gi i)
  have hPL : P ≤ X.L i := le_oTwoPrime_of_isPGroup hP.2.1 hP.1
  have hPsyl : IsSylowTwoOf P (X.L i) :=
    F7.isSylowTwoOf_mono_right hP hPL (X.L_le_Gi i)
  have hconj : ∀ {P' : Subgroup G}, IsSylowTwoOf P' (X.Gi i) →
      ∃ g ∈ X.L i, P' = conjSub g P := by
    intro P' hP'
    exact CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf hPsyl
      (F7.isSylowTwoOf_mono_right hP' (le_oTwoPrime_of_isPGroup hP'.2.1 hP'.1) (X.L_le_Gi i))
  have hZle : X.Z i ≤ centerOf P := by
    unfold Setup.Z
    apply iSup_le
    intro P'
    apply iSup_le
    intro hP'
    intro x hxterm
    obtain ⟨hxP', -⟩ := Subgroup.mem_inf.mp hxterm
    obtain ⟨g, hgL, hP'eq⟩ := hconj hP'
    rw [hP'eq, centerOf_conjSub] at hxP'
    have hfix : conjSub g (centerOf P) = centerOf P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.centralizer_le_normalizer (centerOf P : Set G) (hL hgL))
    rwa [hfix] at hxP'
  have hZeq : X.Z i = centerOf P :=
    le_antisymm hZle (X.centerOf_sylow_le_Z hc i hP).1
  refine ⟨hZeq, ?_⟩
  rw [hZeq]
  refine le_antisymm ?_ ?_
  · intro z hz
    change z ∈ X.L i ⊓ Subgroup.centralizer (X.L i : Set G)
    obtain ⟨hzP, hzC⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hPL hzP, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hL hl) z hz).symm
  · intro z hz
    exact hZle (X.centerOf_L_le_Z hc i hz)

theorem Gi_smul (X Y : Setup Γ G) {g : G} {i j : ℤ}
    (h : g • X.vert i = Y.vert j) : Y.Gi j = conjSub g (X.Gi i) := by
  unfold Setup.Gi
  rw [← h, stabilizer_smul_eq_conjSub]

theorem Q_smul (X Y : Setup Γ G) {g : G} {i j : ℤ}
    (h : g • X.vert i = Y.vert j) : Y.Q j = conjSub g (X.Q i) := by
  unfold Setup.Q
  rw [Gi_smul X Y h, pCoreOf_conjSub]

theorem L_smul (X Y : Setup Γ G) {g : G} {i j : ℤ}
    (h : g • X.vert i = Y.vert j) : Y.L j = conjSub g (X.L i) := by
  unfold Setup.L
  rw [Gi_smul X Y h, conjSub_oTwoPrime]

theorem Z_smul (X Y : Setup Γ G) {g : G} {i j : ℤ}
    (h : g • X.vert i = Y.vert j) : Y.Z j = conjSub g (X.Z i) := by
  unfold Setup.Z Setup.Q
  rw [Gi_smul X Y h]
  exact Setup.iSup_sylow_center_conj g (X.Gi i)

theorem S_smul (X Y : Setup Γ G) {g : G} (h0 : g • X.vert 0 = Y.vert 0)
    (h1 : g • X.vert 1 = Y.vert 1) : Y.S = conjSub g X.S := by
  unfold Setup.S
  rw [Gi_smul X Y h0, Gi_smul X Y h1, ← conjSub_inf, pCoreOf_conjSub]

theorem card_eq_card_K_mul_card_pCoreOf (i : ℤ) {A : Subgroup G} (hKA : X.K ≤ A)
    (hA : A ≤ X.Gi i ⊓ X.Gi (i + 1)) :
    Nat.card A = Nat.card X.K * Nat.card (pCoreOf 2 A) := by
  have hPinf := X.pCoreOf_eq_inf_edgeSylow i hKA hA
  have hdisj : Disjoint X.K (pCoreOf 2 A) := disjoint_iff.mpr (eq_bot_mono
    (inf_le_inf_left _ (hPinf.1.le.trans inf_le_right)) (X.K_inf_edgeSylow i))
  have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (pCoreOf 2 A)
    X.K (hKA.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A)) hdisj.symm
  rwa [sup_comm, hPinf.2, mul_comm] at h

private theorem card_arcStab_zero_one_eq_prod (hs : IsSingularity Γ G s) {k : ℕ}
    (hk1 : 1 ≤ k) (hks : k ≤ s) :
    Nat.card (X.arcStab 0 1) =
      (∏ r ∈ Finset.Icc 1 (k - 1), (2 : ℕ) ^ X.n (r : ℤ)) *
        Nat.card (X.arcStab 0 (k : ℤ)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · norm_num
    · have hks' : k ≤ s := by omega
      have hIH := ih (by omega) hks'
      have hle : X.arcStab 0 ((k + 1 : ℕ) : ℤ) ≤ X.arcStab 0 (k : ℤ) :=
        X.arcStab_anti le_rfl (by omega)
      have htr : X.RightTransAt 0 (k : ℤ) := by
        simpa using (X.trans_of_lt hs 0 hkpos (by omega)).2
      have hrel : (X.arcStab 0 ((k + 1 : ℕ) : ℤ)).relIndex
          (X.arcStab 0 (k : ℤ)) = 2 ^ X.n (k : ℤ) := by
        simpa [Nat.cast_add, Nat.cast_one] using
          X.relIndex_arcStab_succ 0 (k : ℤ) (by omega) htr
      have hcard := Subgroup.relIndex_mul_card
        (H := X.arcStab 0 ((k + 1 : ℕ) : ℤ)) (K := X.arcStab 0 (k : ℤ))
      have hinf : X.arcStab 0 ((k + 1 : ℕ) : ℤ) ⊓ X.arcStab 0 (k : ℤ) =
          X.arcStab 0 ((k + 1 : ℕ) : ℤ) := inf_eq_left.mpr hle
      rw [hinf, hrel] at hcard
      have hprod : (∏ r ∈ Finset.Icc 1 k, (2 : ℕ) ^ X.n (r : ℤ)) =
          (∏ r ∈ Finset.Icc 1 (k - 1), (2 : ℕ) ^ X.n (r : ℤ)) *
            2 ^ X.n (k : ℤ) := by
        rw [show k = (k - 1) + 1 by omega, Finset.prod_Icc_succ_top (by omega),
          Nat.add_sub_cancel]
      rw [hIH, hcard.symm, show (k + 1) - 1 = k by omega, hprod]
      ring

theorem card_S_eq_prod (hs : IsSingularity Γ G s) :
    Nat.card X.S =
      (∏ r ∈ Finset.Icc 1 (s - 1), (2 : ℕ) ^ X.n (r : ℤ)) *
        Nat.card (pCoreOf 2 (X.arcStab 0 s)) := by
  have hs1 : 1 ≤ s := hs.1
  haveI : Finite ↥(X.K) := finite_of_le_stabilizer X.hyp (X.K_le_Gi 0)
  have harc1 : X.arcStab 0 1 = X.Gi 0 ⊓ X.Gi 1 :=
    X.arcStab_eq_inf (show (0 : ℤ) ≤ 1 by norm_num)
  have hKle : X.K ≤ X.arcStab 0 (s : ℤ) := by
    intro k hk
    rw [Setup.arcStab, Fan86.mem_fixSet]
    rintro _ ⟨j, -, rfl⟩
    exact X.K_fix k hk j
  have hArcG : X.arcStab 0 (s : ℤ) ≤ X.Gi 0 ⊓ X.Gi 1 := by
    rw [← harc1]
    exact X.arcStab_anti le_rfl (by exact_mod_cast hs1)
  have hcardKS : Nat.card (X.arcStab 0 1) = Nat.card X.K * Nat.card X.S := by
    have h := card_mul_pCoreOf_edgeStab X.hyp (X.adj 0) X.K_le_inf X.K_inf X.K_sup
    rw [harc1]
    simpa [Setup.Gi, Setup.S, mul_comm] using h.symm
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥X.K)) ?_
  rw [← hcardKS, X.card_arcStab_zero_one_eq_prod hs hs1 le_rfl,
    X.card_eq_card_K_mul_card_pCoreOf 0 hKle hArcG]
  ring

theorem prod_Icc_two_mul (m : ℕ) :
    (∏ r ∈ Finset.Icc 1 (2 * m), (2 : ℕ) ^ X.n (r : ℤ)) =
      2 ^ (m * (X.n 0 + X.n 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega), ih]
    rw [show ((2 * m + 1 : ℕ) : ℤ) = 1 + 2 * (m : ℤ) by push_cast; ring, X.n_add]
    rw [show ((2 * m + 1 + 1 : ℕ) : ℤ) = 0 + 2 * ((m : ℤ) + 1) by push_cast; ring,
      X.n_add]
    rw [← pow_add, ← pow_add]
    congr 1
    ring

theorem card_S_eq_pow (hs : IsSingularity Γ G s) (hodd : Odd s) :
    Nat.card X.S =
      (2 ^ X.n 0 * 2 ^ X.n 1) ^ ((s - 1) / 2) *
        Nat.card (pCoreOf 2 (X.arcStab 0 s)) := by
  obtain ⟨m, rfl⟩ := hodd
  have hm : (2 * m) / 2 = m := by
    rw [Nat.mul_comm, Nat.mul_div_cancel _ (by norm_num)]
  rw [X.card_S_eq_prod hs, show 2 * m + 1 - 1 = 2 * m by omega,
    X.prod_Icc_two_mul, hm, ← pow_add, ← pow_mul, mul_comm m]

private theorem fixes_neighbors_of_centralizes (i : ℤ)
    {U P : Subgroup G} (hU : U ≤ X.K)
    (hPS : P ⊔ X.Q i = X.edgeSylow i ∨ P ⊔ X.Q i = X.edgeSylow (i - 1))
    (hPU : P ≤ Subgroup.centralizer (U : Set G)) :
    ∀ w, Γ.Adj (X.vert i) w → ∀ u ∈ U, u • w = w := by
  have hleft : Γ.Adj (X.vert i) (X.vert (i - 1)) := X.toTrack.adj_pred i
  have hright : Γ.Adj (X.vert i) (X.vert (i + 1)) := X.adj i
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := X.toTrack.ne_pred_succ i
  have hPleGi : P ≤ X.Gi i := by
    rcases hPS with he | he
    · exact (le_sup_left.trans (le_of_eq he)).trans
        ((X.isSylowTwoOf_edgeSylow i).1.trans inf_le_left)
    · have hPleS : P ≤ X.edgeSylow (i - 1) := le_sup_left.trans (le_of_eq he)
      have hSle : X.edgeSylow (i - 1) ≤ X.Gi i :=
        ((X.isSylowTwoOf_edgeSylow (i - 1)).1).trans (by simpa using inf_le_right)
      exact hPleS.trans hSle
  have hPnormQ : P ≤ Subgroup.normalizer (X.Q i : Set G) :=
    hPleGi.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i))
  have hdecomp : ∀ {e : ℤ}, P ⊔ X.Q i = X.edgeSylow e →
      ∀ s ∈ X.edgeSylow e, ∃ p ∈ P, ∃ q ∈ X.Q i, p * q = s := by
    intro e he s hs
    have hs' : s ∈ P ⊔ X.Q i := by rwa [← he] at hs
    have hmul : (↑(P ⊔ X.Q i) : Set G) = (P : Set G) * (X.Q i : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right P (X.Q i) hPnormQ
    have hx : s ∈ (P : Set G) * (X.Q i : Set G) := by rw [← hmul]; exact hs'
    exact Set.mem_mul.mp hx
  have hfix : ∀ w, Γ.Adj (X.vert i) w → ∀ u ∈ U, u • w = w := by
    intro w hw u hu
    rcases hPS with he | he
    · by_cases hw1 : w = X.vert (i + 1)
      · rw [hw1]
        exact X.K_fix u (hU hu) (i + 1)
      · obtain ⟨p, hp, hpx⟩ : ∃ p ∈ P, p • X.vert (i - 1) = w := by
          obtain ⟨s, hs, hsw⟩ := X.edgeSylow_transitive_left i (X.vert (i - 1)) w
            hleft hne hw hw1
          obtain ⟨p, hp, q, hq, hpq⟩ := hdecomp he s hs
          refine ⟨p, hp, ?_⟩
          have hqfix : q • X.vert (i - 1) = X.vert (i - 1) :=
            X.Q_fixes_neighbors_vert i _ hleft q hq
          calc p • X.vert (i - 1) = (p * q) • X.vert (i - 1) := by rw [mul_smul, hqfix]
            _ = s • X.vert (i - 1) := by rw [hpq]
            _ = w := hsw
        calc u • w = u • (p • X.vert (i - 1)) := by rw [hpx]
          _ = p • (u • X.vert (i - 1)) := by
              rw [← mul_smul, ← mul_smul]
              congr 1
              exact Subgroup.mem_centralizer_iff.mp (hPU hp) u hu
          _ = p • X.vert (i - 1) := by rw [X.K_fix u (hU hu) (i - 1)]
          _ = w := hpx
    · by_cases hw1 : w = X.vert (i - 1)
      · rw [hw1]
        exact X.K_fix u (hU hu) (i - 1)
      · obtain ⟨p, hp, hpx⟩ : ∃ p ∈ P, p • X.vert (i + 1) = w := by
          obtain ⟨s, hs, hsw⟩ := X.edgeSylow_transitive_right i (X.vert (i + 1)) w
            hright hne.symm hw hw1
          have hsE : s ∈ X.edgeSylow (i - 1) := by
            simpa [Setup.edgeSylow, show i - 1 + 1 = i by omega] using hs
          obtain ⟨p, hp, q, hq, hpq⟩ := hdecomp he s hsE
          refine ⟨p, hp, ?_⟩
          have hqfix : q • X.vert (i + 1) = X.vert (i + 1) :=
            X.Q_fixes_neighbors_vert i _ hright q hq
          calc p • X.vert (i + 1) = (p * q) • X.vert (i + 1) := by rw [mul_smul, hqfix]
            _ = s • X.vert (i + 1) := by rw [hpq]
            _ = w := hsw
        calc u • w = u • (p • X.vert (i + 1)) := by rw [hpx]
          _ = p • (u • X.vert (i + 1)) := by
              rw [← mul_smul, ← mul_smul]
              congr 1
              exact Subgroup.mem_centralizer_iff.mp (hPU hp) u hu
          _ = p • X.vert (i + 1) := by rw [X.K_fix u (hU hu) (i + 1)]
          _ = w := hpx
  exact hfix

private theorem exists_mul_mem_normalizer_of_conj_le {F N U : Subgroup G} [Finite ↥F]
    (l : G) (hNF : N ≤ F) (hNnorm : (N.subgroupOf F).Normal) (hSylow : IsSylowTwoOf N F)
    (hUF : U ≤ F) (hlF : conjSub l U ≤ F) (hlN : l ∈ Subgroup.normalizer (N : Set G))
    (hNU : N ⊔ U = F) (hdisj : N ⊓ U = ⊥) :
    ∃ n ∈ N, n * l ∈ Subgroup.normalizer (U : Set G) := by
  have hFnormN : F ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNF).mp hNnorm
  have hconjNinv : conjSub l⁻¹ N = N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hlN)
  have hdisjK : N ⊓ conjSub l U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxK⟩ := Subgroup.mem_inf.mp hx
    have hxU : l⁻¹ * x * l ∈ U := mem_conjSub.mp hxK
    have hxN' : l⁻¹ * x * l ∈ N := by
      have hmem : l⁻¹ * x * l ∈ conjSub l⁻¹ N := by
        rw [mem_conjSub]
        convert hxN using 1
        group
      rwa [hconjNinv] at hmem
    have hxbot : l⁻¹ * x * l ∈ N ⊓ U := Subgroup.mem_inf.mpr ⟨hxN', hxU⟩
    rw [hdisj] at hxbot
    have h1 := Subgroup.mem_bot.mp hxbot
    calc x = l * (l⁻¹ * x * l) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hcardF : Nat.card F = Nat.card N * Nat.card U := by
    rw [← hNU]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer N U
      (hUF.trans hFnormN) (disjoint_iff.mpr hdisj)
  have hcardNK : Nat.card ↥(N ⊔ conjSub l U) = Nat.card F := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer N (conjSub l U)
      (hlF.trans hFnormN) (disjoint_iff.mpr hdisjK), card_conjSub, ← hcardF]
  have hNKle : N ⊔ conjSub l U ≤ F := sup_le hNF hlF
  have hNK : N ⊔ conjSub l U = F :=
    Subgroup.eq_of_le_of_card_ge hNKle (le_of_eq hcardNK.symm)
  obtain ⟨n, hnN, hn⟩ := exists_conj_eq_of_complement
    (F := F) (N := N) hNF hNnorm hSylow hUF hlF hNU hNK hdisj hdisjK
  have hnl : n * l ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc conjSub (n * l) U = conjSub n (conjSub l U) := conjSub_mul n l U
      _ = conjSub n (conjSub n⁻¹ U) := by rw [hn]
      _ = U := conjSub_inv_conjSub n U
  exact ⟨n, hnN, hnl⟩

private theorem commutator_mem_Q_of_fixes_nbrs (i : ℤ) {k : G} (hk : k ∈ X.Gi i)
    (hfix : ∀ w, Γ.Adj (X.vert i) w → k • w = w) : ∀ l ∈ X.L i, ⁅k, l⁆ ∈ X.Q i := by
  intro l hl
  have hconjL : k * l * k⁻¹ ∈ X.L i :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoPrime (X.Gi i) hk) l).mp hl
  have hcL : ⁅k,l⁆ ∈ X.L i :=
    (X.L i).mul_mem hconjL ((X.L i).inv_mem hl)
  have hkinv : ∀ w, Γ.Adj (X.vert i) w → k⁻¹ • w = w := by
    intro w hw
    simpa using (congrArg (fun z => k⁻¹ • z) (hfix w hw)).symm
  have hv : ∀ w, Γ.Adj (X.vert i) w → (l * k⁻¹ * l⁻¹) • w = w := by
    intro w hw
    have hlfix : l⁻¹ • X.vert i = X.vert i := by
      have h := MulAction.mem_stabilizer_iff.mp (X.L_le_Gi i hl)
      simpa using (congrArg (fun v => l⁻¹ • v) h).symm
    have hw' : Γ.Adj (X.vert i) (l⁻¹ • w) := by
      simpa [hlfix] using (X.hyp.adj_smul l⁻¹ (X.vert i) w).mpr hw
    calc (l * k⁻¹ * l⁻¹) • w = l • (k⁻¹ • (l⁻¹ • w)) := by simp [mul_smul]
      _ = l • (l⁻¹ • w) := by rw [hkinv _ hw']
      _ = w := by simp
  have hcFix : ∀ w, Γ.Adj (X.vert i) w → ⁅k,l⁆ • w = w := by
    intro w hw
    calc ⁅k,l⁆ • w = (k * (l * k⁻¹ * l⁻¹)) • w := by
            congr 1
            simp only [commutatorElement_def]
            group
      _ = k • ((l * k⁻¹ * l⁻¹) • w) := by rw [mul_smul]
      _ = k • w := by rw [hv w hw]
      _ = w := hfix w hw
  have hN := X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hmem := hN.N_fixes_neighbors_mem_Q X.hyp.adj_smul
    (X.hyp.finite_stab (X.vert i)) (X.hyp.valency (X.vert i)).2
    (X.hyp.valency (X.vert i)).1 (x := ⟨⁅k,l⁆, hcL⟩) (by
      intro w hw
      exact hcFix w hw)
  simpa [Setup.Q, Setup.Gi] using hmem

private theorem exists_eq_mul_of_mem_L (i : ℤ) {U : Subgroup G} (hU : U ≤ X.K)
    (hULQ : ∀ u ∈ U, ∀ l ∈ X.L i, ⁅u, l⁆ ∈ X.Q i) :
    ∀ l ∈ X.L i, ∃ g ∈ Subgroup.normalizer (U : Set G), ∃ q ∈ X.Q i, l = q * g := by
  have hUodd : Odd (Nat.card ↥U) :=
    X.odd_card_K.of_dvd_nat (Subgroup.card_dvd_of_le hU)
  have hUleGi : U ≤ X.Gi i := hU.trans (X.K_le_Gi i)
  have hUnormQ : U ≤ Subgroup.normalizer (X.Q i : Set G) :=
    hUleGi.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i))
  have hUQ : U ⊓ X.Q i = ⊥ :=
    eq_bot_mono (inf_le_inf_right _ hU) (X.K_inf_Q_eq_bot i)
  haveI : Finite ↥(X.Q i) :=
    finite_of_le_stabilizer X.hyp (H := X.Q i) (X.Q_le_Gi i)
  haveI : Finite ↥(U ⊔ X.Q i) :=
    finite_of_le_stabilizer X.hyp (H := U ⊔ X.Q i) (sup_le hUleGi (X.Q_le_Gi i))
  have hFnormQ : U ⊔ X.Q i ≤ Subgroup.normalizer (X.Q i : Set G) :=
    sup_le hUnormQ Subgroup.le_normalizer
  have hcardF : Nat.card ↥(U ⊔ X.Q i) = Nat.card ↥U * Nat.card ↥(X.Q i) := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (X.Q i) U hUnormQ (disjoint_iff.mpr (by rw [inf_comm]; exact hUQ))
    rw [sup_comm, h, mul_comm]
  have hrelF : (X.Q i).relIndex (U ⊔ X.Q i) = Nat.card ↥U := by
    have h := Subgroup.relIndex_mul_card (H := X.Q i) (K := U ⊔ X.Q i)
    rw [inf_of_le_left le_sup_right, hcardF] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(X.Q i))) h
  have hSylowF : IsSylowTwoOf (X.Q i) (U ⊔ X.Q i) := by
    refine F7.isSylowTwoOf_of_relIndex le_sup_right (pCoreOf_isPGroup' (X.Gi i)) ?_
    rw [hrelF]
    exact fun h2 => hUodd.not_two_dvd_nat h2
  intro l hl
  have hUF : U ≤ U ⊔ X.Q i := le_sup_left
  have hQF : X.Q i ≤ U ⊔ X.Q i := le_sup_right
  have hlGi : l ∈ X.Gi i := X.L_le_Gi i hl
  have hlNQ : l ∈ Subgroup.normalizer (X.Q i : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i)) hlGi
  have hlF : conjSub l U ≤ U ⊔ X.Q i := by
    intro x hx
    have hy : l⁻¹ * x * l ∈ U := mem_conjSub.mp hx
    have hcommQ : ⁅(l⁻¹ * x * l)⁻¹, l⁆ ∈ X.Q i :=
      hULQ _ ((U).inv_mem hy) l hl
    have hxeq : x = (l⁻¹ * x * l) * ⁅(l⁻¹ * x * l)⁻¹, l⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hy hcommQ
  obtain ⟨n, hnQ, hnl⟩ := exists_mul_mem_normalizer_of_conj_le
    (F := U ⊔ X.Q i) (N := X.Q i) (U := U) l hQF
    (Subgroup.normal_subgroupOf_of_le_normalizer hFnormQ) hSylowF
    hUF hlF hlNQ (by rw [sup_comm (X.Q i) U]) (by rw [inf_comm]; exact hUQ)
  exact ⟨n * l, hnl, n⁻¹, (X.Q i).inv_mem hnQ, by group⟩

theorem fix_nbrs_of_centralizes (hc : CharTwoStab (V := V) (G := G)) (i : ℤ)
    {U P : Subgroup G} (hU : U ≤ X.K) (hP : IsPGroup 2 P)
    (hPS : P ⊔ X.Q i = X.edgeSylow i ∨ P ⊔ X.Q i = X.edgeSylow (i - 1))
    (hPU : P ≤ Subgroup.centralizer (U : Set G)) :
    (∀ w, Γ.Adj (X.vert i) w → ∀ u ∈ U, u • w = w) ∧
      (∀ a b, Γ.Adj (X.vert i) a → Γ.Adj (X.vert i) b →
        ∃ g ∈ Subgroup.normalizer (U : Set G) ⊓ X.Gi i, g • a = b) := by
  have hfix := X.fixes_neighbors_of_centralizes i hU hPS hPU
  refine ⟨hfix, ?_⟩
  have hULQ : ∀ u ∈ U, ∀ l ∈ X.L i, ⁅u, l⁆ ∈ X.Q i := fun u hu =>
    X.commutator_mem_Q_of_fixes_nbrs i (hU.trans (X.K_le_Gi i) hu)
      (fun w hw => hfix w hw u hu)
  have htransN := X.exists_eq_mul_of_mem_L i hU hULQ
  intro a b ha hb
  obtain ⟨l, hlL, hlab⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert i)).trans a b ha hb
  obtain ⟨g, hgN, q, hqQ, rfl⟩ := htransN l hlL
  have hqGi : q ∈ X.Gi i := X.Q_le_Gi i hqQ
  have hgGi : g ∈ X.Gi i := by
    have h : q * g ∈ X.Gi i := X.L_le_Gi i hlL
    have := (X.Gi i).mul_mem ((X.Gi i).inv_mem hqGi) h
    simpa [mul_assoc] using this
  have hgfix : g • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp hgGi
  have hgadj : Γ.Adj (X.vert i) (g • a) := by
    rw [← hgfix]
    exact (X.hyp.adj_smul g (X.vert i) a).mpr ha
  refine ⟨g, ⟨hgN, hgGi⟩, ?_⟩
  calc g • a = q • (g • a) := by
        rw [X.Q_fixes_neighbors_vert i (g • a) hgadj q hqQ]
    _ = (q * g) • a := by rw [mul_smul]
    _ = b := hlab

theorem le_Q_of_fixes_nbrs (i : ℤ) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPG : P ≤ X.Gi i) (hfix : ∀ w, Γ.Adj (X.vert i) w → ∀ p ∈ P, p • w = w) :
    P ≤ X.Q i := by
  have hleft : Γ.Adj (X.vert i) (X.vert (i - 1)) := X.toTrack.adj_pred i
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := X.toTrack.ne_pred_succ i
  exact le_pCoreOf_of_isPGroup_fixes_two X.hyp hP hPG hleft (X.adj i) hne
    (hfix _ hleft) (hfix _ (X.adj i))

end Setup

theorem conjSub_relCent (g : G) {E Z A : Subgroup G}
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) :
    conjSub g (relCent E Z A) =
      relCent (conjSub g E) (conjSub g Z) (conjSub g A) := by
  have hEZ' : conjSub g E ≤ Subgroup.normalizer (conjSub g Z : Set G) := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ E := by rwa [mem_conjSub] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hiff := Subgroup.mem_normalizer_iff.mp (hEZ hx') (g⁻¹ * z * g)
    constructor
    · intro hz
      rw [mem_conjSub] at hz
      have h2 : g⁻¹ * x * g * (g⁻¹ * z * g) * (g⁻¹ * x * g)⁻¹ ∈ Z := hiff.mp hz
      rw [mem_conjSub]
      convert h2 using 1 <;> group
    · intro hz
      rw [mem_conjSub] at hz
      have h2 : g⁻¹ * x * g * (g⁻¹ * z * g) * (g⁻¹ * x * g)⁻¹ ∈ Z := by
        convert hz using 1 <;> group
      have h3 := hiff.mpr h2
      rw [← mem_conjSub] at h3
      exact h3
  ext x
  rw [mem_conjSub, mem_relCent hEZ, mem_relCent hEZ']
  constructor
  · rintro ⟨he, hc⟩
    refine ⟨?_, ?_⟩
    · rwa [mem_conjSub]
    · intro a ha
      rw [mem_conjSub] at ha ⊢
      have hcomm : g⁻¹ * ⁅x, a⁆ * g = ⁅g⁻¹ * x * g, g⁻¹ * a * g⁆ := by
        simp only [commutatorElement_def]; group
      rw [hcomm]
      exact hc (g⁻¹ * a * g) ha
  · rintro ⟨he, hc⟩
    refine ⟨?_, ?_⟩
    · exact mem_conjSub.mp he
    · intro a ha
      have ha' : g * a * g⁻¹ ∈ conjSub g A := by
        rw [mem_conjSub]
        convert ha using 1 <;> group
      have h := hc (g * a * g⁻¹) ha'
      rw [mem_conjSub] at h
      convert h using 1
      simp only [commutatorElement_def]; group

theorem NatQuot.conj {L E Z : Subgroup G} {n : ℕ} (h : NatQuot L E Z n) (g : G) :
    NatQuot (conjSub g L) (conjSub g E) (conjSub g Z) n := by
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := fun x hx => (h.normal (h.E_le hx)).2
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := MulEquiv.injective _
  have hrel : ∀ {X Y : Subgroup G}, (conjSub g X).relIndex (conjSub g Y) = X.relIndex Y := by
    intro X Y
    exact Subgroup.relIndex_map_map_of_injective X Y hinj
  have hpull : ∀ {A : Subgroup G}, IsSylowTwoOf A (conjSub g L) →
      ∃ A', IsSylowTwoOf A' L ∧ A = conjSub g A' := by
    intro A hA
    refine ⟨conjSub g⁻¹ A, ?_, ?_⟩
    · have := (F7.isSylowTwoOf_conj_iff (g := g⁻¹) (T := A)
        (H := conjSub g L)).mpr hA
      simpa [conjSub_conjSub_inv] using this
    · exact (conjSub_inv_conjSub g A).symm
  refine ⟨conjSub_mono g h.Z_le, conjSub_mono g h.E_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_inf ?_ ?_
    · exact conjSub_le_normalizer (g := g) (H := L) (K := E) fun x hx => (h.normal hx).1
    · exact conjSub_le_normalizer (g := g) (H := L) (K := Z) fun x hx => (h.normal hx).2
  · rw [hrel]
    exact h.index
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := hpull hA
    rw [← conjSub_relCent g hEZ, hrel]
    exact h.line A' hA'
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := hpull hA
    rw [conjSub_commutator, ← conjSub_sup, ← conjSub_relCent g hEZ, h.comm_eq A' hA']
  · intro A A' hA hA' hnot
    obtain ⟨B, hB, rfl⟩ := hpull hA
    obtain ⟨B', hB', rfl⟩ := hpull hA'
    have hnot' : ¬ B ≤ B' ⊔ E := by
      intro hle
      apply hnot
      rw [← conjSub_sup]
      exact conjSub_mono g hle
    obtain ⟨hinf, hsup⟩ := h.lines_inf B B' hB hB' hnot'
    constructor
    · rw [← conjSub_relCent g hEZ, ← conjSub_relCent g hEZ, ← conjSub_inf, hinf]
    · rw [← conjSub_relCent g hEZ, ← conjSub_relCent g hEZ, ← conjSub_sup, hsup]
  · intro x hxL hxodd hxE e heE hcomm
    have hxL' : g⁻¹ * x * g ∈ L := by rwa [mem_conjSub] at hxL
    have hxE' : g⁻¹ * x * g ∉ E := by
      intro hmem
      apply hxE
      rw [mem_conjSub]
      convert hmem using 1 <;> group
    have heE' : g⁻¹ * e * g ∈ E := by rwa [mem_conjSub] at heE
    have hcomm' : ⁅g⁻¹ * e * g, g⁻¹ * x * g⁆ ∈ Z := by
      have h := hcomm
      rw [mem_conjSub] at h
      convert h using 1 <;> (simp only [commutatorElement_def]; group)
    have hodd : Odd (orderOf (g⁻¹ * x * g)) := by
      have hconj : orderOf (g⁻¹ * x * g) = orderOf x :=
        (SemiconjBy.orderOf_eq (a := g⁻¹) (x := x) (y := g⁻¹ * x * g)
          (by unfold SemiconjBy; group)).symm
      rwa [hconj]
    have hz := h.fpf (g⁻¹ * x * g) hxL' hodd hxE' (g⁻¹ * e * g) heE' hcomm'
    rw [mem_conjSub]
    convert hz using 1 <;> group
  · intro A hZA hAE hnorm
    obtain ⟨A', rfl⟩ : ∃ A', A = conjSub g A' :=
      ⟨conjSub g⁻¹ A, (conjSub_inv_conjSub g A).symm⟩
    have hZA' : Z ≤ A' := (Subgroup.map_le_map_iff_of_injective hinj).mp hZA
    have hAE' : A' ≤ E := (Subgroup.map_le_map_iff_of_injective hinj).mp hAE
    have hnorm' : L ≤ Subgroup.normalizer (A' : Set G) := by
      have h := hnorm
      rw [conjSub_normalizer] at h
      exact (Subgroup.map_le_map_iff_of_injective hinj).mp h
    rcases h.irred A' hZA' hAE' hnorm' with hA' | hA'
    · left
      rw [hA']
    · right
      rw [hA']

theorem NatQuot.exists_commutatorElement_notMem {L E Z A : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (h : NatQuot L E Z n) (hA : IsSylowTwoOf A L) : ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ Z := by
  by_contra! hcon
  have hle : ⁅E, A⁆ ≤ Z := Subgroup.commutator_le.mpr fun e he a ha => by
    simpa [commutatorElement_inv] using Z.inv_mem (hcon a (hA.1 ha) e he)
  have hEq : relCent E Z A = Z := by
    rw [← h.comm_eq A hA]
    exact sup_eq_right.mpr hle
  have hrel := h.line A hA
  rw [hEq, Subgroup.relIndex_self] at hrel
  have h2 : (2 : ℕ) ^ n ≠ 1 :=
    (Nat.one_lt_two_pow (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 1) hn))).ne'
  exact h2 hrel.symm

theorem NatQuot.natSec {G' : Type} [Group G'] {L E Z : Subgroup G'} {n : ℕ}
    (h : NatQuot L E Z n) (hE : IsPGroup 2 E) : NatSec L Z E := by
  intro x hxL hx3 e heE hcomm
  have hodd : Odd (orderOf x) := by rw [hx3]; norm_num
  have hxE : x ∉ E := by
    intro hxE
    obtain ⟨k, hk⟩ := hE.exists_orderOf_dvd_pow (⟨x, hxE⟩ : E)
    have hk' : orderOf x ∣ 2 ^ k := by simpa [Subgroup.orderOf_coe] using hk
    rw [hx3] at hk'
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      ((by norm_num : Nat.Coprime 3 2).pow_right k) hk'
  exact h.fpf x hxL hodd hxE e heE hcomm

end CFSG.Quasithin.St84
