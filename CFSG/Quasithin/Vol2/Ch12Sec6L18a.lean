module

public import CFSG.Quasithin.Vol2.KGFact12618
public import CFSG.Quasithin.EmptyFaithful.S146zGDich
public import CFSG.Quasithin.Vol2.Ch12Sec6L14d
public import CFSG.Quasithin.Vol2.KGFact12617List

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

section Index

variable {G : Type} [Group G] [Finite G]

theorem relIndex_autOn_le {U H K : Subgroup G} (hHK : H ≤ K)
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) :
    (autOn H U).relIndex (autOn K U) ≤ H.relIndex K := by
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := hHK.trans hKU
  have hle : autOn H U ≤ autOn K U := InternalSec.autOn_le_autOn_of_le hHK
  have hcK := CFSG.Quasithin.card_autOn_eq_relIndex hKU
  have hcH := CFSG.Quasithin.card_autOn_eq_relIndex hHU
  have h1 := Subgroup.relIndex_mul_card (autOn H U) (autOn K U)
  rw [inf_eq_left.2 hle] at h1
  have h2 := Subgroup.relIndex_mul_card (K ⊓ Subgroup.centralizer (U : Set G)) K
  rw [inf_eq_left.2 inf_le_left] at h2
  have h3 := Subgroup.relIndex_mul_card (H ⊓ Subgroup.centralizer (U : Set G)) H
  rw [inf_eq_left.2 inf_le_left] at h3
  have h4 := Subgroup.relIndex_mul_card H K
  rw [inf_eq_left.2 hHK] at h4
  have hcd : Nat.card ↥(H ⊓ Subgroup.centralizer (U : Set G)) ≤
      Nat.card ↥(K ⊓ Subgroup.centralizer (U : Set G)) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hHK)
  have hpos : 0 < Nat.card ↥(H ⊓ Subgroup.centralizer (U : Set G)) := Nat.card_pos
  have hpos' : 0 < Nat.card ↥(autOn H U) := Nat.card_pos
  rw [← hcK] at h2
  rw [← hcH] at h3
  have e : H.relIndex K * Nat.card ↥(H ⊓ Subgroup.centralizer (U : Set G)) =
      (autOn H U).relIndex (autOn K U) * Nat.card ↥(K ⊓ Subgroup.centralizer (U : Set G)) := by
    apply Nat.eq_of_mul_eq_mul_left hpos'
    calc Nat.card ↥(autOn H U) * (H.relIndex K * Nat.card ↥(H ⊓ Subgroup.centralizer (U : Set G)))
        = H.relIndex K * (Nat.card ↥(autOn H U) *
            Nat.card ↥(H ⊓ Subgroup.centralizer (U : Set G))) := by ring
      _ = Nat.card ↥K := by rw [h3, h4]
      _ = Nat.card ↥(autOn K U) * Nat.card ↥(K ⊓ Subgroup.centralizer (U : Set G)) := h2.symm
      _ = _ := by rw [← h1]; ring
  by_contra hlt
  push Not at hlt
  have h5 : H.relIndex K * Nat.card ↥(H ⊓ Subgroup.centralizer (U : Set G)) <
      (autOn H U).relIndex (autOn K U) * Nat.card ↥(H ⊓ Subgroup.centralizer (U : Set G)) :=
    Nat.mul_lt_mul_of_pos_right hlt hpos
  have h6 : (autOn H U).relIndex (autOn K U) * Nat.card ↥(H ⊓ Subgroup.centralizer (U : Set G)) ≤
      (autOn H U).relIndex (autOn K U) * Nat.card ↥(K ⊓ Subgroup.centralizer (U : Set G)) :=
    Nat.mul_le_mul_left _ hcd
  omega

theorem pCoreOf_autOn_le {U H : Subgroup G} (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hC : IsPGroup 2 ↥(H ⊓ Subgroup.centralizer (U : Set G))) :
    pCoreOf 2 (autOn H U) ≤ autOn (pCoreOf 2 H) U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (autOn H U) with hP
  let N : Subgroup G :=
    { carrier := {h | ∃ hh : h ∈ H, conjAct U ⟨h, hHU hh⟩ ∈ P}
      one_mem' := ⟨H.one_mem, by
        rw [show (⟨1, hHU H.one_mem⟩ : ↥(Subgroup.normalizer (U : Set G))) = 1 from rfl, map_one]
        exact P.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, hPa⟩ ⟨hb, hPb⟩
        refine ⟨H.mul_mem ha hb, ?_⟩
        rw [show (⟨a * b, hHU (H.mul_mem ha hb)⟩ : ↥(Subgroup.normalizer (U : Set G))) =
          ⟨a, hHU ha⟩ * ⟨b, hHU hb⟩ from rfl, map_mul]
        exact P.mul_mem hPa hPb
      inv_mem' := by
        rintro a ⟨ha, hPa⟩
        refine ⟨H.inv_mem ha, ?_⟩
        rw [show (⟨a⁻¹, hHU (H.inv_mem ha)⟩ : ↥(Subgroup.normalizer (U : Set G))) =
          (⟨a, hHU ha⟩)⁻¹ from rfl, map_inv]
        exact P.inv_mem hPa }
  have hNH : N ≤ H := fun x hx => hx.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    intro h hh
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨hnH, hnP⟩ := hn
    refine ⟨H.mul_mem (H.mul_mem hh hnH) (H.inv_mem hh), ?_⟩
    have hhA : conjAct U ⟨h, hHU hh⟩ ∈ autOn H U :=
      QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨h, hHU hh⟩, hh, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 ((le_normalizer_pCoreOf 2 (autOn H U)) hhA) _).1 hnP
    rw [show (⟨h * n * h⁻¹, hHU (H.mul_mem (H.mul_mem hh hnH) (H.inv_mem hh))⟩ :
        ↥(Subgroup.normalizer (U : Set G))) = ⟨h, hHU hh⟩ * ⟨n, hHU hnH⟩ * (⟨h, hHU hh⟩)⁻¹ from rfl,
      map_mul, map_mul, map_inv]
    exact h1
  have hN2 : IsPGroup 2 ↥N := by
    intro x
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (autOn H U)) ⟨_, x.2.2⟩
    have hk' : conjAct U ⟨(x : G), hHU x.2.1⟩ ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hxk : (x : G) ^ 2 ^ k ∈ H ⊓ Subgroup.centralizer (U : Set G) := by
      refine ⟨H.pow_mem x.2.1 _, ?_⟩
      have h2 : conjAct U (⟨(x : G), hHU x.2.1⟩ ^ 2 ^ k) = 1 := by rw [map_pow, hk']
      exact (QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (U : Set G)) le_rfl
        _).1 h2
    obtain ⟨j, hj⟩ := hC ⟨_, hxk⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have hj' : ((x : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [Subgroup.coe_pow, pow_add, pow_mul, hj', Subgroup.coe_one]
  have hNO : N ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hNH hHN hN2
  intro φ hφ
  have hφH : φ ∈ autOn H U := pCoreOf_le 2 _ hφ
  obtain ⟨⟨h, hhN⟩, hhH, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hφH
  exact QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨h, hhN⟩, hNO ⟨hhH, hφ⟩, rfl⟩

end Index

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem autOn_Lv_lt_Kv (hD2 : Lemma12_6_4_5) (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    autOn (Lv L v) (Usec Kv S) < autOn Kv (Usec Kv S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLK := (hD5 G T L V F v Kv S hC).1
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  obtain ⟨-, -, -, -, -, hOR, hRN, -, -⟩ := hD2 G T L V F v Kv S hC
  refine lt_of_le_of_ne (InternalSec.autOn_le_autOn_of_le hC.lv_le) fun heq => hLK.ne ?_
  set P := Kv ⊓ pCoreOf 2 (Kv ⊔ S) with hP
  have hPN : P ≤ Subgroup.normalizer (Lv L v : Set G) := (inf_le_right.trans hOR).trans hRN
  have hle : Kv ≤ Lv L v ⊔ P := by
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (Usec Kv S : Set G) := Kv_le_normalizer_Usec hC hk
    have hkA : conjAct (Usec Kv S) ⟨k, hkN⟩ ∈ autOn (Lv L v) (Usec Kv S) := by
      rw [heq]
      exact QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, hk, rfl⟩
    obtain ⟨⟨l, hlN⟩, hlL, hlk⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hkA
    have hc : ((⟨l, hlN⟩⁻¹ * ⟨k, hkN⟩ : ↥(Subgroup.normalizer (Usec Kv S : Set G))) : G) ∈
        Subgroup.centralizer (Usec Kv S : Set G) := by
      rw [← QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (Usec Kv S : Set G))
        le_rfl]
      show conjAct (Usec Kv S) (⟨l, hlN⟩⁻¹ * ⟨k, hkN⟩) = 1
      rw [map_mul, map_inv, hlk, inv_mul_cancel]
    have hlK : l ∈ Kv := hC.lv_le hlL
    have hcP : l⁻¹ * k ∈ P := ⟨Kv.mul_mem (Kv.inv_mem hlK) hk, by
      rw [hO]
      exact ⟨(Kv ⊔ S).mul_mem ((Kv ⊔ S).inv_mem ((le_sup_left : Kv ≤ Kv ⊔ S) hlK))
        ((le_sup_left : Kv ≤ Kv ⊔ S) hk), hc⟩⟩
    have e : k = l * (l⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hcP)
  have hn : ∀ k ∈ Kv, ∀ n ∈ Lv L v, k * n * k⁻¹ ∈ Lv L v := by
    intro k hk n hn
    have hkN : k ∈ Subgroup.normalizer (Lv L v : Set G) :=
      (sup_le Subgroup.le_normalizer hPN) (hle hk)
    exact (Subgroup.mem_normalizer_iff.1 hkN n).1 hn
  have hP2 : IsPGroup 2 ↥P := (pCoreOf_isPGroup 2 _).to_le inf_le_right
  exact le_antisymm hC.lv_le (perfect_le_of_le_sup_pGroup (perfect_of_mem_cComp hC.cComp)
    hC.lv_le hn hP2 inf_le_left hle)

omit [IsMulCommutative ↥V] in
theorem pCoreOf_Lv_le_Rv (hH : Hyp126 G T L V) (v : G) : pCoreOf 2 (Lv L v) ≤ Rv T L v := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hN : (L ⊔ T) ⊓ Gv v ≤ Subgroup.normalizer (Lv L v : Set G) := fun x hx =>
    normalizer_le_normalizer_perfectCore _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hXL hx.1, Subgroup.le_normalizer hx.2⟩)
  exact le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 _).trans (le_inf ((Lv_le_L L v).trans le_sup_left) (Lv_le_Gv L v)))
    (hN.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem pCoreOf_Lv_le_Qv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    pCoreOf 2 (Lv L v) ≤ Qv T V := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hXV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hRT : Rv T L v ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_Tv h1222 F hH hv hβ)).trans inf_le_left
  intro x hx
  have hxL : x ∈ L := Lv_le_L L v (pCoreOf_le 2 _ hx)
  have h1 : psiP F hH ⟨x, hxL⟩ = 1 := psi_pCore_eq_one h1222 F hH hv hβ hx
  have hact : ActsAs F x 1 := by
    have := actsAs_psiP F hH ⟨x, hxL⟩
    rwa [h1] at this
  have hxX : x ∈ L ⊔ T := Subgroup.mem_sup_left hxL
  exact ⟨hRT (pCoreOf_Lv_le_Rv hH v hx),
    mem_centralizer_of_actsAs_one F hVL hLV (hXL hxX) (hXV hxX) hact⟩

theorem comm_pCoreOf_Lv_le_Vv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hL : CFSG.QuasithinUnique.IsShort2 L) :
    ⁅pCoreOf 2 (Lv L v), Lv L v⁆ ≤ Vv L V v := by
  have hQL := comm_Qv_L_le_V h1222 hH hL
  have hOQ := pCoreOf_Lv_le_Qv h1222 F hH hv hβ
  have hOV : ⁅pCoreOf 2 (Lv L v), Lv L v⁆ ≤ V :=
    (Subgroup.commutator_mono hOQ (Lv_le_L L v)).trans hQL
  calc ⁅pCoreOf 2 (Lv L v), Lv L v⁆ ≤ ⁅⁅pCoreOf 2 (Lv L v), Lv L v⁆, Lv L v⁆ :=
        le_comm_comm_of_perfect (perfectCore_perfect _)
          ((pCoreOf_le 2 _).trans Subgroup.le_normalizer) (le_normalizer_pCoreOf 2 _)
    _ ≤ Vv L V v := Subgroup.commutator_mono hOV le_rfl

theorem comm_pCoreOf_autOn_Lv_eq_bot (h1222 : Stmt12_2_2) (hD7 : Lemma12_6_13)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hL : CFSG.QuasithinUnique.IsShort2 L) :
    ⁅pCoreOf 2 (autOn (Lv L v) (Usec Kv S)), autOn (Lv L v) (Usec Kv S)⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  obtain ⟨⟨-, hO⟩, -, hVU⟩ := hD7 G T L V F v Kv S hC
  set U := Usec Kv S with hU
  have hKU : Kv ≤ Subgroup.normalizer (U : Set G) := Kv_le_normalizer_Usec hC
  have hLvU : Lv L v ≤ Subgroup.normalizer (U : Set G) := hC.lv_le.trans hKU
  have hUe := isElemAbelian_Usec Kv S
  have hC2 : IsPGroup 2 ↥(Lv L v ⊓ Subgroup.centralizer (U : Set G)) := by
    refine (pCoreOf_isPGroup 2 (Kv ⊔ S)).to_le ?_
    rw [hO]
    exact inf_le_inf_right _ (hC.lv_le.trans le_sup_left)
  have hP := pCoreOf_autOn_le hLvU hC2
  have hcomm := comm_pCoreOf_Lv_le_Vv h1222 F hH hv hβ hL
  have hUK : ⁅U, Kv⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have h1 : k * u⁻¹ * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hKU hk) _).1 (U.inv_mem hu)
    have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
    rw [commutatorElement_def, e]
    exact U.mul_mem hu h1
  have hVvU : Vv L V v ≤ U := hVU.trans hUK
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨⟨x, hxN⟩, hxO, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 (hP ha)
  obtain ⟨⟨l, hlN⟩, hlL, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hb
  have hxl : x * l * x⁻¹ * l⁻¹ ∈ U := by
    have := hcomm (Subgroup.commutator_mem_commutator hxO hlL)
    rw [commutatorElement_def] at this
    exact hVvU this
  have hc : x * l * x⁻¹ * l⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hlN) (Subgroup.inv_mem _ hxN))
      (Subgroup.inv_mem _ hlN)
  have he : ⁅conjAct U ⟨x, hxN⟩, conjAct U ⟨l, hlN⟩⁆ = conjAct U ⟨x * l * x⁻¹ * l⁻¹, hc⟩ := by
    rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [Subgroup.mem_bot, he]
  refine (QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (U : Set G)) le_rfl
    _).2 (Subgroup.mem_centralizer_iff.2 fun w hw => ?_)
  exact (hUe.1.is_comm.comm ⟨w, hw⟩ ⟨_, hxl⟩ |> congrArg Subtype.val)

theorem k4_cases (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (h56 : AsB56) (hD2 : Lemma12_6_4_5) (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13)
    (hD9 : Lemma12_6_15) (hK4 : FactKv12618) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hL : CFSG.QuasithinUnique.IsShort2 L) :
    (IsAlt 7 ↥(autOn Kv (Usec Kv S)) ∧
      ¬ 2 ∣ (autOn (Kv ⊔ S) (Usec Kv S) ⊓ Subgroup.normalizer (autOn (Lv L v) (Usec Kv S) :
        Set (MulAut ↥(Usec Kv S)))).relIndex (autOn (Kv ⊔ S) (Usec Kv S)) ∧
      centralizerSection (autOn S (Usec Kv S)) (autOn (Lv L v) (Usec Kv S))
        (pCoreOf 2 (autOn (Lv L v) (Usec Kv S))) = ⊥) ∨
    (IsAlt 8 ↥(autOn Kv (Usec Kv S)) ∧
      (autOn (Tv T v) (Usec Kv S)).relIndex (autOn S (Usec Kv S)) = 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hyp := hH.hyp
  obtain ⟨-, -, hTvS4, -, -, -, -, -, -⟩ := hD2 G T L V F v Kv S hC
  set U := Usec Kv S with hU
  set X := Kv ⊔ S with hX
  have hUe := isElemAbelian_Usec Kv S
  have : IsMulCommutative ↥U := hUe.1
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_Usec Kv S)
  have hKvU : Kv ≤ Subgroup.normalizer (U : Set G) := Kv_le_normalizer_Usec hC
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := (le_sup_right : S ≤ X).trans hXU
  have hLvU : Lv L v ≤ Subgroup.normalizer (U : Set G) := hC.lv_le.trans hKvU
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hKS : X ≤ Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hSX : CFSG.QuasithinUnique.IsSylowTwoOf S X :=
    A4.isSylowTwoOf_mono hC.sylow le_sup_right hKS
  have hred := isTwoReducedIn_Usec hD7 hC
  have hO2 : pCoreOf 2 (autOn X U) = ⊥ := QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hH2 : pCoreOf 2 (Gv v) ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥X := InternalSec.sqtkGroup_mono
    (sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2) hKS
  have hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ Kv := by
    intro x hx
    have hx' : x ∈ (↑(Kv ⊔ S) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Kv S hSK] at hx'
    obtain ⟨y, hy, t, ht, hyt⟩ := hx'
    obtain ⟨j, hj⟩ := hC.sylow.2.1 ⟨t, ht⟩
    have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
    obtain ⟨y', hy', hp⟩ := A4.exists_pow_mul_eq hy (hSK ht) (2 ^ j)
    refine ⟨j, ?_⟩
    rw [← hyt, hp, hj', mul_one]
    exact hy'
  have hKs : IsSimpleGroup ↥(autOn Kv U) :=
    (MulEquiv.isSimpleGroup_congr (autOn_Kv_equiv hD7 hC)).1 (isSimple_Kv h1222 h36 hC)
  have hBK := autOn_Lv_lt_Kv hD2 hD5 hD7 hC
  have hBiso := o2Iso_autOn_Lv h1222 hD7 hC
  have hK168 : 168 < Nat.card ↥(autOn Kv U) := by
    obtain ⟨φ, hφs, -⟩ := hBiso
    have h1 : Nat.card ↥(alternatingGroup (Fin 6)) ≤ Nat.card ↥(autOn (Lv L v) U) :=
      Nat.card_le_card_of_surjective φ hφs
    have h2 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have h3 : Nat.card ↥(autOn (Lv L v) U) ≤ Nat.card ↥(autOn Kv U) :=
      Subgroup.card_le_of_le hBK.le
    omega
  obtain ⟨hU', hFF⟩ := hD9 G T L V F v Kv S hC
  have hlist := KG12614.b56QL_of_isFFModule h56 (fun w hw => hUe.2 w hw) hXU hSQ hO2
    le_sup_left (sup_le Subgroup.le_normalizer hSK) hKs hK168 hpow hFF
  have hidx : (autOn (Tv T v) U).relIndex (autOn S U) ≤ 4 :=
    (relIndex_autOn_le hC.tv_le hSU).trans
      (hTvS4.trans (le_of_eq (relIndex_Tv h1222 F hH hv hβ)))
  exact hK4 (MulAut ↥U) (autOn X U) (autOn Kv U) (autOn S U) (autOn (Tv T v) U)
    (autOn (Lv L v) U) (InternalSec.autOn_le_autOn_of_le le_sup_left)
    (autOn_le_normalizer (sup_le Subgroup.le_normalizer hSK)) hKs hlist
    (QuasithinUnique.Setup.isSylowTwoOf_autOn hSX hXU) (autOn_sup_eq hKvU hSU) hO2 hBK
    (InternalSec.autOn_le_autOn_of_le hC.tv_le) hidx
    (autOn_le_normalizer (Tv_le_normalizer_Lv hH v))
    (autOn_perfect hLvU (perfectCore_perfect _)) hBiso
    (comm_pCoreOf_autOn_Lv_eq_bot h1222 hD7 hC hL)

end S126T2

end CFSG.Quasithin.H13
