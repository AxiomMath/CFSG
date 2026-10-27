module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalBall
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFCount
public import CFSG.Quasithin.Recognition.Kleidman.F204.CritCases
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalDich
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalQ

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem mem_normalizer_of_mem_centralizer {C : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (C : Set G)) : g ∈ Subgroup.normalizer (C : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : g * h * g⁻¹ = h := by
      rw [← Subgroup.mem_centralizer_iff.mp hg h hh]
      group
    rw [e]; exact hh
  · intro hh
    have hginv : g⁻¹ ∈ Subgroup.centralizer (C : Set G) := inv_mem hg
    have hc := Subgroup.mem_centralizer_iff.mp hginv _ hh
    have e : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = (g * h * g⁻¹) * g⁻¹ * g := by rw [hc]
        _ = g * h * g⁻¹ := by group
    rw [e]; exact hh

theorem conj_mem_centralizer_of_mem {B : Subgroup G} {g n : G} (hg : g ∈ B)
    (hn : n ∈ Subgroup.centralizer (B : Set G)) :
    g * n * g⁻¹ ∈ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro h hh
  have h' := hn (g⁻¹ * h * g) (B.mul_mem (B.mul_mem (inv_mem hg) hh) hg)
  calc h * (g * n * g⁻¹) = g * ((g⁻¹ * h * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * h * g)) * g⁻¹ := by rw [h']
    _ = g * n * g⁻¹ * h := by group

theorem mem_centralizer_omegaOne {T : Subgroup G} {t : G} (ht : t ∈ T) :
    t ∈ Subgroup.centralizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G) := by
  have key : quasithinOmegaOneCenter T ≤ Subgroup.centralizer ({t} : Set G) := by
    unfold quasithinOmegaOneCenter
    rw [Subgroup.closure_le]
    intro z hz
    obtain ⟨⟨hzT, hzC⟩, -⟩ := hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp hzC) t ht
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact ((Subgroup.mem_centralizer_iff.mp (key (SetLike.mem_coe.mp hy))) t
    (Set.mem_singleton t)).symm

theorem centralizes_Zv_of_zcentral {H M : Subgroup G} {w : Geo H M} (hw : ZCentral w)
    {T : Subgroup G} (hT : IsSylowTwoOf T (stab w)) {t : G} (ht : t ∈ T) :
    t ∈ Subgroup.centralizer (Zv w : Set G) := by
  rw [hw T hT]
  exact mem_centralizer_omegaOne ht

section H1

variable (F : Frame L1 L2 S D X)

include F

theorem H1 (hT1 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = false)
    {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true) :
    Zv x ⊓ Subgroup.centralizer (stab x : Set G) = ⊥ := by
  have hA := Amal.of_frame F
  obtain ⟨w, hw⟩ := exists_adj x
  have hxw : (graph _ _ _).Adj x w := hw
  have hwf : vtype w = false :=
    Bool.eq_false_iff.mpr fun h => vtype_ne_of_adj hxw (by rw [hx, h])
  have hwZ : ZCentral w := (hT1 w).mpr hwf
  obtain ⟨T, hTx, hTw, hTle⟩ := hA.exists_common_sylow hw
  set C : Subgroup G := Zv x ⊓ Subgroup.centralizer (stab x : Set G) with hCdef
  have hCT : C ≤ T := fun c hc =>
    isSylowTwoOf_pCoreOf_le hTx (hA.Zv_le_Qv x (Subgroup.mem_inf.mp hc).1)
  have hCZ : C ≤ Zv w := by
    intro c hc
    have hc' := Subgroup.mem_inf.mp hc
    rw [hwZ T hTw]
    apply Subgroup.subset_closure
    refine ⟨⟨hCT hc, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
        (Subgroup.mem_centralizer_iff.mp hc'.2) h (hTx.1 hh)
    · exact (hA.isElemAbelian_Zv x).2 c hc'.1
  obtain ⟨g, hg1, hg2⟩ := exists_conj_stab_false (L1 := L1) (L2 := L2) (S := S) hwf
  obtain ⟨q, hqQ2, hqQ1⟩ : ∃ q ∈ Q2 L1 L2 S, q ∉ Q1 L1 L2 S := by
    have h := not_Q2_le_Q1 F
    rw [IsConcreteLE.not_le_iff_exists] at h
    obtain ⟨q, hq, hq'⟩ := h
    exact ⟨q, hq, hq'⟩
  have hqS : q ∈ P1 L1 L2 S := F.sylow_P1.1 (F.Q2_le_S hqQ2)
  have hTw' : conjSub g⁻¹ (P1 L1 L2 S) = stab w := by
    have key : conjSub g⁻¹ (conjSub g (stab w)) = stab w := by
      ext y
      rw [mem_conjSub, mem_conjSub, inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    rw [hg1] at key
    exact key
  have hT' : IsSylowTwoOf (conjSub g⁻¹ S) (stab w) := by
    have h := isSylowTwoOf_conj F.sylow_P1 g⁻¹
    rwa [hTw'] at h
  have htw : g⁻¹ * q * g ∈ stab w := by
    have : q ∈ conjSub g (stab w) := by rw [hg1]; exact hqS
    exact mem_conjSub.mp this
  have htQ : g⁻¹ * q * g ∉ Qv w := by
    intro h
    apply hqQ1
    rw [← hg2]
    exact mem_conjSub.mpr h
  have htT : g⁻¹ * q * g ∈ conjSub g⁻¹ S := by
    rw [mem_conjSub, inv_inv, show g * (g⁻¹ * q * g) * g⁻¹ = q by group]
    exact F.Q2_le_S hqQ2
  obtain ⟨n, hn⟩ := hT'.2.1 ⟨_, htT⟩
  have htn : (g⁻¹ * q * g) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcent := centralizes_Zv_of_zcentral hwZ hT' htT
  have h5 := five_centralizes_Zv_of_two F hwf htw htn hcent htQ
  have hcard : Nat.card (stab w) = 15 * Nat.card S := by
    have h := card_conjSub g (stab w)
    rw [hg1, card_P1 F] at h
    exact h.symm
  have hS5 : ¬ 5 ∣ Nat.card S := by
    intro h5S
    obtain ⟨m, hm⟩ := (isPGroup_iff_card_dvd_pow).mp F.sylow_P1.2.1
    have h52 : 5 ∣ 2 ^ m := h5S.trans hm
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h52
    norm_num at this
  have hxw' : x ∈ nbrs w := hxw.symm
  have h1 : 5 * Nat.card (stab w ⊓ stab x : Subgroup G) = Nat.card (stab w) := by
    have := Subgroup.relIndex_mul_card (H := stab w ⊓ stab x) (K := stab w)
    rw [relIndex_stab_inf_nbr F hxw', inf_eq_left.mpr inf_le_left] at this
    exact this
  have hK3 : Nat.card (stab w ⊓ stab x : Subgroup G) = 3 * Nat.card S := by
    rw [hcard] at h1
    omega
  have hK5 : ¬ 5 ∣ Nat.card (stab w ⊓ stab x : Subgroup G) := by
    rw [hK3]
    intro h
    exact hS5 (by omega)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype (stab w) := Fintype.ofFinite _
  obtain ⟨f5, hf5⟩ : ∃ f5 : stab w, orderOf f5 = 5 :=
    exists_prime_orderOf_dvd_card 5
      (by
        rw [← Nat.card_eq_fintype_card, hcard]
        exact Dvd.dvd.mul_right (by norm_num) _)
  obtain ⟨f, hfw, hfo⟩ : ∃ f ∈ stab w, orderOf f = 5 :=
    ⟨f5, f5.2, by rw [Subgroup.orderOf_coe, hf5]⟩
  have hf5pow : f ^ 5 = 1 := by
    rw [← hfo]
    exact pow_orderOf_eq_one f
  have hfx : f ∉ stab x := by
    intro hfx
    have hmem : f ∈ stab w ⊓ stab x := ⟨hfw, hfx⟩
    have h5K : 5 ∣ Nat.card (stab w ⊓ stab x : Subgroup G) := by
      have := orderOf_dvd_natCard (⟨f, hmem⟩ : ↥(stab w ⊓ stab x))
      rwa [Subgroup.orderOf_mk, hfo] at this
    exact hK5 h5K
  have hfc : f ∈ Subgroup.centralizer (Zv w : Set G) := h5 f hfw hf5pow
  have hsup : Subgroup.zpowers f ⊔ (stab w ⊓ stab x) = stab w :=
    stab_eq_sup_of_not_le F hxw' (Subgroup.zpowers_le.mpr hfw)
      (fun h => hfx (h (Subgroup.mem_zpowers f)))
  have hsw : stab w ≤ Subgroup.centralizer (C : Set G) := by
    rw [← hsup]
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun c hc => ?_)
      exact (Subgroup.mem_centralizer_iff.mp hfc) c (hCZ (SetLike.mem_coe.mp hc))
    · intro k hk
      refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
      have hc' := Subgroup.mem_inf.mp (SetLike.mem_coe.mp hc)
      exact ((Subgroup.mem_centralizer_iff.mp hc'.2) k (Subgroup.mem_inf.mp hk).2).symm
  have hα : stab x ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hn
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv x hg) n).mp h1,
          conj_mem_centralizer_of_mem hg h2⟩
    · intro hn
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hn
      have h3 := conj_mem_centralizer_of_mem (inv_mem hg) h2
      have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
      rw [e] at h3
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv x hg) n).mpr h1, h3⟩
  have hβ : stab w ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_of_mem_centralizer (hsw hg)
  have hU : C ≤ stab x ⊓ stab w := fun c hc => hTle (hCT hc)
  exact hA.eq_bot_of_normalizes_both hxw hU hα hβ

end H1

section H2

variable (F : Frame L1 L2 S D X)

include F

theorem H2 {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = false) (hZF : ZFaithful x)
    {A : Subgroup G} (hA2 : IsElemAbelian 2 A) (hAx : A ≤ stab x) (hAQ : ¬ A ≤ Qv x)
    (hidx : (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) ≤
      (A ⊓ Qv x).relIndex A) :
    False := by
  have hA := Amal.of_frame F
  obtain ⟨a, haA, haQ⟩ : ∃ a ∈ A, a ∉ Qv x := by
    rw [IsConcreteLE.not_le_iff_exists] at hAQ
    exact hAQ
  have hasq : a ^ 2 = 1 := hA2.2 a haA
  have ha_stab : a ∈ stab x := hAx haA
  have hsa : ({a} : Set G) ⊆ (A : Set G) := Set.singleton_subset_iff.mpr haA
  have hsub : Zv x ⊓ Subgroup.centralizer (A : Set G) ≤
      Zv x ⊓ Subgroup.centralizer ({a} : Set G) :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le hsa))
  have hne : (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hmono : (Zv x ⊓ Subgroup.centralizer ({a} : Set G)).relIndex (Zv x) ≤
      (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) :=
    Subgroup.relIndex_le_of_le_left hsub hne
  have hidx2 : (Zv x ⊓ Subgroup.centralizer ({a} : Set G)).relIndex (Zv x) ≤ 2 :=
    hmono.trans (hidx.trans (relIndex_inf_Qv_le_two F hx hAx hA2))
  have ha2Q : a ^ 2 ∈ Qv x := by
    rw [hasq]
    exact (Qv x).one_mem
  have h5 : ∀ y ∈ stab x, y ^ 5 = 1 → y ∈ Subgroup.centralizer (Zv x : Set G) :=
    fun y hy hy5 => five_centralizes_of_transvection F hx (hA.isElemAbelian_Zv x)
      (hA.stab_le_normalizer_Zv x) (Qv_le_centralizer_Zv F x) ha_stab haQ ha2Q hidx2 hy hy5
  have hZ : ZCentral x := fun T hT => Zv_eq_omega_of_five F hx h5 hT
  obtain ⟨T0, hT0, -⟩ := hA.exists_sylow_stab x
  have hsq : ∀ y ∈ Subgroup.zpowers a, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hasq, one_zpow]
  have hPgrp : IsPGroup 2 (Subgroup.zpowers a) := fun y =>
    ⟨1, by simpa using Subtype.ext (hsq y y.2)⟩
  have hPH : Subgroup.zpowers a ≤ stab x := Subgroup.zpowers_le.mpr ha_stab
  obtain ⟨g, hg, hPle⟩ := isSylowTwoOf_exists_conj_le hT0 hPH hPgrp
  have hT : IsSylowTwoOf (conjSub g T0) (stab x) := by
    have h := isSylowTwoOf_conj hT0 g
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at h
  have haT : a ∈ conjSub g T0 := hPle (Subgroup.mem_zpowers a)
  have haC : a ∈ Subgroup.centralizer (Zv x : Set G) := centralizes_Zv_of_zcentral hZ hT haT
  have haQ' : a ∈ conjSub g T0 ⊓ Subgroup.centralizer (Zv x : Set G) :=
    Subgroup.mem_inf.mpr ⟨haT, haC⟩
  rw [hZF _ hT] at haQ'
  exact haQ haQ'

end H2

section H3

variable (F : Frame L1 L2 S D X)

include F

theorem H3 (hT1 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = false)
    {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    {A : Subgroup G} (hAx : A ≤ stab x) (hA : IsPGroup 2 (A.subgroupOf (stab x)))
    (hAnt : ∃ a ∈ A, ∃ v ∈ Zv x, a * v ≠ v * a)
    (hidx : (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) ≤
      (A ⊓ Qv x).relIndex A) :
    Nat.card (Zv x) = 16 ∧ (A ⊓ Qv x).relIndex A = 4 ∧
      Nat.card (Zv x ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) = 4 := by
  have hA' := Amal.of_frame F
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hx
  have hV2 : ∀ a ∈ Zv x, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact (hA'.isElemAbelian_Zv x).2 a ha
  have hLV : stab x ≤ Subgroup.normalizer (Zv x : Set G) := hA'.stab_le_normalizer_Zv x
  have hker : ∀ l : ↥(stab x), φ l = 1 → (l : G) ∈ Subgroup.centralizer (Zv x : Set G) := by
    intro l hl
    have hlk : l ∈ φ.ker := MonoidHom.mem_ker.mpr hl
    rw [hφk] at hlk
    exact Qv_le_centralizer_Zv F x (Subgroup.mem_subgroupOf.mp hlk)
  have hCL : ∀ v ∈ Zv x, (∀ l : ↥(stab x), v * (l : G) = (l : G) * v) → v = 1 := by
    intro v hv hvc
    have hmem : v ∈ Zv x ⊓ Subgroup.centralizer (stab x : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hv, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact (hvc ⟨h, hh⟩).symm
    rw [H1 F hT1 hx] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hbridge : (A ⊓ Qv x).relIndex A = Nat.card ((A.subgroupOf (stab x)).map φ) := by
    calc (A ⊓ Qv x).relIndex A = (Qv x).relIndex A := by
          rw [inf_comm]; exact Subgroup.inf_relIndex_right (H := Qv x) (K := A)
      _ = ((Qv x).subgroupOf (stab x)).relIndex (A.subgroupOf (stab x)) :=
          (Subgroup.relIndex_subgroupOf hAx).symm
      _ = φ.ker.relIndex (A.subgroupOf (stab x)) := by rw [hφk]
      _ = Nat.card ((A.subgroupOf (stab x)).map φ) := Subgroup.relIndex_ker _ φ
  have hAmap : ((A.subgroupOf (stab x)).map (stab x).subtype : Subgroup G) = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAx]
  have hAnt' : ∃ a ∈ A.subgroupOf (stab x), ∃ v ∈ Zv x, (a : G) * v ≠ v * (a : G) := by
    obtain ⟨a, haA, v, hv, hne⟩ := hAnt
    exact ⟨⟨a, hAx haA⟩, Subgroup.mem_subgroupOf.mpr haA, v, hv, hne⟩
  have hidx' : (Zv x ⊓ Subgroup.centralizer
      (((A.subgroupOf (stab x)).map (stab x).subtype : Subgroup G) : Set G)).relIndex (Zv x) ≤
      Nat.card ((A.subgroupOf (stab x)).map φ) := by
    rw [hAmap, ← hbridge]
    exact hidx
  obtain ⟨h1, h2, h3, -⟩ := fa5_ff_card hV2 hLV φ hφs hker hCL hA hAnt' hidx'
  refine ⟨h1, ?_, ?_⟩
  · rw [hbridge]
    exact h2
  · rw [hAmap] at h3
    exact h3

end H3

theorem isPGroup_two_of_sq_gen {K : Type} [Group K] {U : Subgroup K} (hU : ∀ u ∈ U, u ^ 2 = 1) :
    IsPGroup 2 U := by
  intro y
  exact ⟨1, by simpa using Subtype.ext (hU y y.2)⟩

section H4

variable (F : Frame L1 L2 S D X)

include F

theorem inf_centralizer_eq_inf_Qv {x y : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hZy : ZFaithful y) (hsy : Zv x ≤ stab y) :
    Zv x ⊓ Subgroup.centralizer (Zv y : Set G) = Zv x ⊓ Qv y := by
  have hA := Amal.of_frame F
  have hV2 : ∀ a ∈ Zv x, a ^ 2 = 1 := fun a ha => (hA.isElemAbelian_Zv x).2 a ha
  apply le_antisymm
  · intro u hu
    have hU : Zv x ⊓ Subgroup.centralizer (Zv y : Set G) ≤ Qv y :=
      hA.le_Qv_of_ZFaithful hZy (fun v hv => hsy (Subgroup.mem_inf.mp hv).1)
        (isPGroup_two_of_sq_gen fun v hv => hV2 v (Subgroup.mem_inf.mp hv).1)
        (fun v hv => (Subgroup.mem_inf.mp hv).2)
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hu).1, hU hu⟩
  · intro u hu
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hu).1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact ((Subgroup.mem_centralizer_iff.mp ((hA.Zv_le_centerOf_Qv y hz).2))
      u (Subgroup.mem_inf.mp hu).2).symm

theorem exists_noncomm_of_not_le {x y : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hE : Zv x ⊓ Subgroup.centralizer (Zv y : Set G) = Zv x ⊓ Qv y) (hnot : ¬ Zv x ≤ Qv y) :
    ∃ a ∈ Zv y, ∃ v ∈ Zv x, a * v ≠ v * a := by
  by_contra hcon
  push Not at hcon
  apply hnot
  intro v hv
  have hvC : v ∈ Zv x ⊓ Subgroup.centralizer (Zv y : Set G) :=
    Subgroup.mem_inf.mpr ⟨hv, Subgroup.mem_centralizer_iff.mpr fun a ha => hcon a ha v hv⟩
  rw [hE] at hvC
  exact (Subgroup.mem_inf.mp hvC).2

theorem H4_pair (hT1 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = false)
    {x y : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hx : vtype x = true) (hy : vtype y = true) (hZx : ZFaithful x) (hZy : ZFaithful y)
    (hsx : Zv y ≤ stab x) (hsy : Zv x ≤ stab y)
    (hnot1 : ¬ Zv x ≤ Qv y) (hnot2 : ¬ Zv y ≤ Qv x)
    (hdis : (Zv x ⊓ Subgroup.centralizer (Zv y : Set G)).relIndex (Zv x) ≤
      (Zv y ⊓ Qv x).relIndex (Zv y)) :
    Nat.card (Zv x) = 16 ∧ Nat.card (Zv y) = 16 ∧
      (Zv x ⊓ Qv y).relIndex (Zv x) = 4 ∧ (Zv y ⊓ Qv x).relIndex (Zv y) = 4 := by
  have hA := Amal.of_frame F
  have hV2x : ∀ a ∈ Zv x, a ^ 2 = 1 := fun a ha => (hA.isElemAbelian_Zv x).2 a ha
  have hV2y : ∀ a ∈ Zv y, a ^ 2 = 1 := fun a ha => (hA.isElemAbelian_Zv y).2 a ha
  have hEx := inf_centralizer_eq_inf_Qv F hZy hsy
  have hEy := inf_centralizer_eq_inf_Qv F hZx hsx
  have hAy : IsPGroup 2 ((Zv y).subgroupOf (stab x)) :=
    isPGroup_two_of_sq_gen fun u hu => Subtype.ext (by
      simpa using hV2y _ (Subgroup.mem_subgroupOf.mp hu))
  obtain ⟨hcx, hq, hcZC⟩ := H3 F hT1 hx hsx hAy
    (exists_noncomm_of_not_le F hEx hnot1) hdis
  have hcZQ : Nat.card (Zv x ⊓ Qv y : Subgroup G) = 4 := by
    rw [← hEx]; exact hcZC
  have hp : (Zv x ⊓ Qv y).relIndex (Zv x) = 4 := by
    have h := card_eq_relIndex_mul (V := Zv x) (Z := Qv y)
    rw [hcx, hcZQ] at h
    omega
  have hAx' : IsPGroup 2 ((Zv x).subgroupOf (stab y)) :=
    isPGroup_two_of_sq_gen fun u hu => Subtype.ext (by
      simpa using hV2x _ (Subgroup.mem_subgroupOf.mp hu))
  have hidy : (Zv y ⊓ Subgroup.centralizer (Zv x : Set G)).relIndex (Zv y) ≤
      (Zv x ⊓ Qv y).relIndex (Zv x) := by
    simp only [hEy, hq, hp, le_refl]
  obtain ⟨hcy, -, -⟩ := H3 F hT1 hy hsy hAx'
    (exists_noncomm_of_not_le F hEy hnot2) hidy
  exact ⟨hcx, hcy, hp, hq⟩

theorem H4 (hT1 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = false)
    {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α')
    (h : ¬ Zv α' ≤ Qv α) :
    vtype α = true ∧ vtype α' = true ∧ Nat.card (Zv α) = 16 ∧ Nat.card (Zv α') = 16 ∧
      (Zv α ⊓ Qv α').relIndex (Zv α) = 4 ∧ (Zv α' ⊓ Qv α).relIndex (Zv α') = 4 := by
  have hA := Amal.of_frame F
  obtain ⟨hb, hZα, hZα'⟩ := hA.caseI (fun δ => dichotomy F δ) hc h
  have hvα : vtype α = true := by
    cases hv : vtype α with
    | false => exact absurd ((hT1 α).mpr hv) (hA.not_ZCentral_of_bAt hc.bAt_eq)
    | true => rfl
  have hvα' : vtype α' = true := by
    cases hv : vtype α' with
    | false => exact absurd ((hT1 α').mpr hv) (hA.not_ZCentral_of_bAt hb)
    | true => rfl
  have hsx : Zv α' ≤ stab α :=
    hA.Zv_le_stab_of_dist_le (by rw [CosetGeom.dist_comm, hc.dist_eq, hb])
  have hsy : Zv α ≤ stab α' :=
    hA.Zv_le_stab_of_dist_le (by rw [hc.dist_eq, hc.bAt_eq])
  rcases hA.offender_or α α' with h1 | h2
  · obtain ⟨c1, c2, r1, r2⟩ := H4_pair F hT1 hvα hvα' hZα hZα' hsx hsy hc.not_le h h1
    exact ⟨hvα, hvα', c1, c2, r1, r2⟩
  · obtain ⟨c1, c2, r1, r2⟩ := H4_pair F hT1 hvα' hvα hZα' hZα hsy hsx h hc.not_le h2
    exact ⟨hvα, hvα', c2, c1, r2, r1⟩

end H4

end CFSG.Quasithin.Kleidman.F204
