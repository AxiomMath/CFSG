module

public import CFSG.Quasithin.Background.AutOnPerfect
public import CFSG.Quasithin.H13.A7Nat1233ModAbs
public import CFSG.Quasithin.H13.A7Nat1233FourInputs
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem facts1233Four (h1222 : Stmt12_2_2) {T L V : Subgroup G} (hyp : Hyp1223 G T L V) :
    V ≤ T ∧ T ≤ normalizer (V : Set G) ∧ IsMulCommutative ↥V ∧ ∀ v ∈ V, v ^ 2 = 1 := by
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, hab, -⟩ := hall V hyp.irrPlus
  refine ⟨hVT, hTV, hab, ?_⟩
  obtain ⟨-, hEA, -⟩ := hred
  intro v hv
  have hv' : (⟨v, le_sup_right (b := T) (a := L) (hVT hv)⟩ : ↥(L ⊔ T)) ∈
      V.subgroupOf (L ⊔ T) := hv
  have h1 := (BlueprintB2.isElementaryAbelian_iff.1 hEA).2 _ hv'
  exact congrArg Subtype.val h1

omit [Finite G] in
theorem card_autOn_of_ker {L V : Subgroup G} (hLV : L ≤ normalizer (V : Set G))
    {φ : ↥L →* ↥(alternatingGroup (Fin 7))} (hφs : Function.Surjective φ)
    (hφk : φ.ker = (centralizer (V : Set G)).subgroupOf L) : Nat.card (autOn L V) = 2520 := by
  have hrange : (A4.actionOn V L hLV).range = autOn L V := by
    ext a
    rw [MonoidHom.mem_range, A4.mem_autOn_iff hLV]
  have hker : (A4.actionOn V L hLV).ker = φ.ker := by
    rw [hφk]
    ext l
    rw [MonoidHom.mem_ker, A4.actionOn_eq_one_iff, mem_subgroupOf]
  rw [← hrange, ← Subgroup.index_ker, hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hφs,
    card_top, CFSG.Quasithin.H.A7.card_A7]

omit [Finite G] in
theorem autOn_inf_centralizer_eq {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ normalizer (V : Set G)) {z : G} (hz : z ∈ V) :
    autOn (L ⊓ centralizer ({z} : Set G)) V = fourStab (autOn L V) ⟨z, hz⟩ := by
  have hLzV : L ⊓ centralizer ({z} : Set G) ≤ normalizer (V : Set G) := inf_le_left.trans hLV
  ext a
  rw [A4.mem_autOn_iff hLzV, mem_inf, A4.mem_autOn_iff hLV, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨⟨l, hlL, hlz⟩, rfl⟩
    refine ⟨⟨⟨l, hlL⟩, rfl⟩, Subtype.ext ?_⟩
    change l * z * l⁻¹ = z
    rw [mem_centralizer_singleton_iff.1 hlz, mul_inv_cancel_right]
  · rintro ⟨⟨⟨l, hlL⟩, rfl⟩, hfix⟩
    refine ⟨⟨l, hlL, mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
    have h1 : l * z * l⁻¹ = z := congrArg Subtype.val hfix
    calc l * z = l * z * l⁻¹ * l := by group
      _ = z * l := by rw [h1]

theorem autOn_oTwoUpper_eq {X V : Subgroup G} (hX : X ≤ normalizer (V : Set G)) :
    autOn (oTwoUpper X) V = oTwoUpper (autOn X V) := by
  set N := normalizer (V : Set G)
  have h1 : (oTwoUpper (X.subgroupOf N)).map N.subtype = oTwoUpper X := by
    rw [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le hX]
  have h2 : oTwoUpper (X.subgroupOf N) = (oTwoUpper X).subgroupOf N := by
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective N.subtype_injective _).symm
  unfold autOn
  rw [← h2, oTwoUpper_map]

theorem autOn_perfectCore_eq {X V : Subgroup G} (hX : X ≤ normalizer (V : Set G)) :
    autOn (perfectCore X) V = perfectCore (autOn X V) :=
  CFSG.Quasithin.AutOn.autOn_perfectCore_eq hX

theorem autOn_pCoreOf_le_four {X V : Subgroup G} (hX : X ≤ normalizer (V : Set G)) :
    autOn (pCoreOf 2 X) V ≤ pCoreOf 2 (autOn X V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPX := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (A4.autOn_mono hPX)
    (autOn_le_normalizer_autOn (hPX.trans hX) hX
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)) ?_
  exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_of_injective _
    (normalizer (V : Set G)).subtype_injective).map (conjAct V)

theorem pCoreOf_le_centralizer_of_autOn {K V : Subgroup G} (hKV : K ≤ normalizer (V : Set G))
    {S : Subgroup (MulAut ↥V)} (hKS : autOn K V = S) (hSp : pCoreOf 2 S = ⊥) :
    pCoreOf 2 K ≤ centralizer (V : Set G) := by
  have hPV : pCoreOf 2 K ≤ normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKV
  intro x hx
  have h1 : A4.actionOn V (pCoreOf 2 K) hPV ⟨x, hx⟩ ∈ autOn (pCoreOf 2 K) V :=
    (A4.mem_autOn_iff hPV).2 ⟨⟨x, hx⟩, rfl⟩
  have h2 := autOn_pCoreOf_le_four hKV h1
  rw [hKS, hSp, mem_bot] at h2
  exact (A4.actionOn_eq_one_iff hPV ⟨x, hx⟩).1 h2

omit [Finite G] in
theorem map_commV_autOn_le {X V : Subgroup G} [IsMulCommutative ↥V]
    (hX : X ≤ normalizer (V : Set G)) : (commV (autOn X V)).map V.subtype ≤ ⁅V, X⁆ := by
  rw [commV, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨a, ha, v, rfl⟩, rfl⟩
  obtain ⟨x, rfl⟩ := (A4.mem_autOn_iff hX).1 ha
  rw [Subgroup.commutator_comm]
  have h := Subgroup.commutator_mem_commutator x.2 v.2
  rw [commutatorElement_def] at h
  change (x : G) * v * (x : G)⁻¹ * (v : G)⁻¹ ∈ ⁅X, V⁆
  exact h

omit [Finite G] in
theorem eq_commutator_of_commV_eq_top {X V : Subgroup G} [IsMulCommutative ↥V]
    (hX : X ≤ normalizer (V : Set G)) (h : commV (autOn X V) = ⊤) : V = ⁅V, X⁆ := by
  refine le_antisymm ?_ ((le_normalizer_iff_commutator_le_left).1 hX)
  have := map_commV_autOn_le hX
  rwa [h, Subgroup.map_top, Subgroup.range_subtype] at this

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_ker {L V : Subgroup G}
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {φ : ↥L →* ↥(alternatingGroup (Fin 7))}
    (hφs : Function.Surjective φ) (hφk : φ.ker = (centralizer (V : Set G)).subgroupOf L)
    {x y : G} (hxL : x ∈ L) (hxV : x ∈ centralizer (V : Set G)) (hyL : y ∈ L) :
    x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hF1 : CFSG.pCore 2 ↥L ≤ φ.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    have hN : ((CFSG.pCore 2 ↥L).map φ).Normal := CFSG.pCore_normal.map φ hφs
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hA7s _ hN with h1 | h1
    · exact h1
    · exfalso
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥L).map φ) := CFSG.pCore_isPGroup.map φ
      rw [h1] at h2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
      rw [Subgroup.card_top, CFSG.Quasithin.H.A7.card_A7] at hk
      have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  set φ' : (↥L ⧸ CFSG.pCore 2 ↥L) →* alternatingGroup (Fin 7) :=
    QuotientGroup.lift _ φ hF1 with hφ'
  have hφ's : Function.Surjective φ' := fun a => by
    obtain ⟨l, rfl⟩ := hφs a
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hK : φ'.ker ≤ center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq φ'.normal_ker with h1 | h1
    · exfalso
      have h2 : ∀ a, a = (1 : alternatingGroup (Fin 7)) := by
        intro a
        obtain ⟨q, rfl⟩ := hφ's a
        exact (MonoidHom.mem_ker).1 (h1 ▸ mem_top q)
      have h3 : Nat.card (alternatingGroup (Fin 7)) = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h2 a).trans (h2 b).symm⟩, inferInstance⟩
      rw [CFSG.Quasithin.H.A7.card_A7] at h3
      norm_num at h3
    · exact h1
  have hxk : (QuotientGroup.mk ⟨x, hxL⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ φ'.ker := by
    rw [MonoidHom.mem_ker]
    change φ ⟨x, hxL⟩ = 1
    rw [← MonoidHom.mem_ker, hφk, mem_subgroupOf]
    exact hxV
  have hc := mem_center_iff.1 (hK hxk) (QuotientGroup.mk ⟨y, hyL⟩)
  have h1 : (⟨x, hxL⟩ : ↥L) * ⟨y, hyL⟩ * (⟨x, hxL⟩ : ↥L)⁻¹ * (⟨y, hyL⟩ : ↥L)⁻¹ ∈
      CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hc]
    group
  rw [pCoreOf_eq_map_cfsgPCore]
  exact ⟨_, h1, rfl⟩

theorem Kv_quasisimple_four {T L V : Subgroup G} (hyp : Hyp1223 G T L V)
    (hLV : L ≤ normalizer (V : Set G)) {φ : ↥L →* ↥(alternatingGroup (Fin 7))}
    (hφs : Function.Surjective φ) (hφk : φ.ker = (centralizer (V : Set G)).subgroupOf L)
    {z : G} {S : Subgroup (MulAut ↥V)} (hKz : autOn (Kv hyp z) V = S) [IsSimpleGroup S]
    (hSnc : ∃ a b : S, a * b ≠ b * a) (hSp : pCoreOf 2 S = ⊥) :
    CFSG.IsQuasisimple (↥(Kv hyp z) ⧸ CFSG.pCore 2 ↥(Kv hyp z)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKL : Kv hyp z ≤ L := Kv_le_L hyp z
  have hKV : Kv hyp z ≤ normalizer (V : Set G) := hKL.trans hLV
  have hθ₀ : ∀ k : Kv hyp z, A4.actionOn V (Kv hyp z) hKV k ∈ S := fun k =>
    hKz ▸ (A4.mem_autOn_iff hKV).2 ⟨k, rfl⟩
  set θ : ↥(Kv hyp z) →* ↥S := (A4.actionOn V (Kv hyp z) hKV).codRestrict S hθ₀ with hθdef
  have hθs : Function.Surjective θ := by
    rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := (A4.mem_autOn_iff hKV).1 (hKz.symm ▸ hs)
    exact ⟨k, Subtype.ext hk⟩
  have hθ1 : ∀ k : Kv hyp z, θ k = 1 ↔ (k : G) ∈ centralizer (V : Set G) := fun k => by
    rw [← A4.actionOn_eq_one_iff hKV k]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hPV := pCoreOf_le_centralizer_of_autOn hKV hKz hSp
  have hO2 : CFSG.pCore 2 ↥(Kv hyp z) ≤ θ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hθ1]
    apply hPV
    rw [pCoreOf_eq_map_cfsgPCore]
    exact ⟨x, hx, rfl⟩
  set θ' : (↥(Kv hyp z) ⧸ CFSG.pCore 2 ↥(Kv hyp z)) →* ↥S := QuotientGroup.lift _ θ hO2
    with hθ'def
  have hθ's : Function.Surjective θ' :=
    QuotientGroup.lift_surjective_of_surjective _ _ hθs hO2
  have hcen : θ'.ker ≤ center (↥(Kv hyp z) ⧸ CFSG.pCore 2 ↥(Kv hyp z)) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx1 : θ x = 1 := hq
    have hxV := (hθ1 x).1 hx1
    rw [mem_center_iff]
    intro r
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
    have hc := commutator_mem_pCoreOf_of_ker hyp.quasisimple hφs hφk (hKL x.2) hxV (hKL y.2)
    have hKN : Kv hyp z ≤ normalizer (pCoreOf 2 L ⊓ Kv hyp z : Set G) := by
      intro k hk
      exact A4.mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hKL hk))
        (le_normalizer hk)
    have hcK : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 (Kv hyp z) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hKN
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left)
        ⟨hc, (Kv hyp z).mul_mem ((Kv hyp z).mul_mem ((Kv hyp z).mul_mem x.2 y.2)
          ((Kv hyp z).inv_mem x.2)) ((Kv hyp z).inv_mem y.2)⟩
    rw [pCoreOf_eq_map_cfsgPCore] at hcK
    obtain ⟨w, hw, hweq⟩ := hcK
    have hw' : w = x * y * x⁻¹ * y⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hweq)
    rw [hw'] at hw
    have h1 : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) :
        ↥(Kv hyp z) ⧸ CFSG.pCore 2 ↥(Kv hyp z)) = 1 := (QuotientGroup.eq_one_iff _).2 hw
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    calc (QuotientGroup.mk y : ↥(Kv hyp z) ⧸ CFSG.pCore 2 ↥(Kv hyp z)) * QuotientGroup.mk x
        = ((QuotientGroup.mk x * QuotientGroup.mk y * (QuotientGroup.mk x)⁻¹ *
            (QuotientGroup.mk y)⁻¹)⁻¹ * (QuotientGroup.mk x * QuotientGroup.mk y)) := by group
      _ = QuotientGroup.mk x * QuotientGroup.mk y := by rw [h1, inv_one, one_mul]
  have hKperf : Group.IsPerfect ↥(Kv hyp z) := (Subgroup.isPerfect_iff).2 (Kv_perfect hyp z)
  have hperf : Group.IsPerfect (↥(Kv hyp z) ⧸ CFSG.pCore 2 ↥(Kv hyp z)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥(Kv hyp z)))
      (QuotientGroup.mk'_surjective _)
  have hSq : CFSG.IsQuasisimple ↥S := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnc).1
  exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf θ' hθ's hcen).2 hSq

theorem insp1233Mod_of
    (h1222 : Stmt12_2_2) (h1225 : Stmt12_2_5) : Insp1233Mod := by
  intro G _ _ T L V hyp hS z hzV hz1 hzZ
  classical
  obtain ⟨-, hcard, φ, hφs, hφk⟩ := hS
  obtain ⟨hVT, hTV, hab, hsq⟩ := facts1233Four h1222 hyp
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hΓ : Nat.card (autOn L V) = 2520 := card_autOn_of_ker hLV hφs hφk
  have hW2 : ∀ w : ↥V, w * w = 1 := fun w => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
    exact hsq w w.2)
  have hz' : (⟨z, hzV⟩ : ↥V) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hSs := isSimpleGroup_fourStab hW2 hcard hΓ hz'
  have htrans : ∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, v = l * z * l⁻¹ := by
    intro v hv hv1
    obtain ⟨γ, hγ, hγz⟩ := exists_apply_eq_four hcard hΓ hz'
      (show (⟨v, hv⟩ : ↥V) ≠ 1 from fun h => hv1 (congrArg Subtype.val h))
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).1 hγ
    exact ⟨l, l.2, (congrArg Subtype.val hγz).symm⟩
  have hCzV : L ⊓ centralizer ({z} : Set G) ≤ normalizer (V : Set G) := inf_le_left.trans hLV
  have hLzV : hyp.Lv z ≤ normalizer (V : Set G) := (oTwoUpper_le _).trans hCzV
  have hLz : autOn (hyp.Lv z) V = fourStab (autOn L V) ⟨z, hzV⟩ := by
    change autOn (oTwoUpper (L ⊓ centralizer ({z} : Set G))) V = _
    rw [autOn_oTwoUpper_eq hCzV, autOn_inf_centralizer_eq hLV hzV,
      oTwoUpper_fourStab hW2 hcard hΓ hz']
  have hSperf := commutator_fourStab hW2 hcard hΓ hz'
  have hKz : autOn (Kv hyp z) V = fourStab (autOn L V) ⟨z, hzV⟩ := by
    change autOn (perfectCore (hyp.Lv z)) V = _
    rw [autOn_perfectCore_eq hLzV, hLz, perfectCore_eq_self_of_perfect hSperf]
  have hTzV : hyp.Tv z ≤ normalizer (V : Set G) := inf_le_left.trans hTV
  have hTz : autOn (hyp.Tv z) V ≤ fourStab (autOn L V) ⟨z, hzV⟩ := by
    intro a ha
    obtain ⟨t, rfl⟩ := (A4.mem_autOn_iff hTzV).1 ha
    refine ⟨mem_of_mem_normalizer_four hW2 hcard hΓ
      (autOn_le_normalizer_autOn hLV hTV hyp.normalizes
        ((A4.mem_autOn_iff hTV).2 ⟨⟨t, t.2.1⟩, rfl⟩)), MulAction.mem_stabilizer_iff.2 ?_⟩
    apply Subtype.ext
    change (t : G) * z * (t : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.1 t.2.2, mul_inv_cancel_right]
  have hLTz : autOn (hyp.Lv z ⊔ hyp.Tv z) V = fourStab (autOn L V) ⟨z, hzV⟩ := by
    rw [autOn_sup_eq_sup_autOn hLzV hTzV, hLz]
    exact sup_eq_left.2 hTz
  have hcomm := commV_fourStab_eq_top hW2 hcard hΓ hz'
  have hSp := pCoreOf_fourStab hW2 hcard hΓ hz'
  refine ⟨htrans, by rw [hLTz]; exact hSp, by rw [hLz, perfectCore_eq_self_of_perfect hSperf],
    eq_commutator_of_commV_eq_top hLzV (by rw [hLz]; exact hcomm), ?_⟩
  have hTK : T ≤ normalizer (Kv hyp z : Set G) := T_le_normalizer_Kv hyp h1225 hzV hz1 hzZ
  have hKV : Kv hyp z ≤ normalizer (V : Set G) := (Kv_le_L hyp z).trans hLV
  have hq := Kv_quasisimple_four hyp hLV hφs hφk hKz (fourStab_noncomm hW2 hcard hΓ hz') hSp
  have hmemL : Kv hyp z ∈ lFamily T := by
    show Kv hyp z ∈ cComp (Kv hyp z ⊔ T)
    refine mem_cComp_of_quasisimple_quotient
      (fun N _ hN => eq_top_of_perfect_of_isPGroup (Kv_perfect hyp z) N hN) hq
      (A3.subnormal_of_normal le_sup_left ?_)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hTK)
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ centralizer ({z} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hzZ) t ht))
  have hz2 : orderOf z = 2 := orderOf_eq_prime (hsq z hzV) hz1
  have hloc : quasithinIsLocal T (Kv hyp z) :=
    ⟨hyp.sylow.1, hmemL, (isSylowTwoOf_of_le hyp.sylow le_sup_right).2.2,
      pCoreOf_ne_bot_of_le_centralizer hz2 ((le_sup_right : T ≤ Kv hyp z ⊔ T) (hVT hzV))
        (sup_le (Kv_le_centralizer hyp z) hTe)⟩
  have hVY : VY (Kv hyp z) ≠ ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hVc : V = ⁅V, Kv hyp z⁆ :=
      eq_commutator_of_commV_eq_top hKV (by rw [hKz]; exact hcomm)
    have hVle : V ≤ Kv hyp z :=
      hVc.le.trans ((Subgroup.le_normalizer_iff_commutator_le_right).1 (hVT.trans hTK))
    have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hsq x x.2)⟩
    have hVP : V ≤ pCoreOf 2 (Kv hyp z) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVle hKV hV2
    have hPV := pCoreOf_le_centralizer_of_autOn hKV hKz hSp
    have hVZ : V ≤ omegaOneCenterOf (pCoreOf 2 (Kv hyp z)) := fun v hv =>
      Subgroup.subset_closure ⟨⟨hVP hv, (Subgroup.le_centralizer_iff.1 hPV) hv⟩, hsq v hv⟩
    intro hbot
    have h1 : ⁅V, Kv hyp z⁆ ≤ VY (Kv hyp z) := Subgroup.commutator_mono hVZ le_rfl
    rw [hbot, ← hVc] at h1
    exact hyp.irrPlus.2.1 (le_bot_iff.1 h1)
  exact isFaithfulLocal_iff_isXf.2 ⟨hloc, isXClass_of_isLocal hyp.qtke hyp.sylow hloc, hVY⟩

end CFSG.Quasithin.H13.A7
