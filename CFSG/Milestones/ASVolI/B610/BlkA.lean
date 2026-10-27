module

public import CFSG.Quasithin.Background.E2SolvBlocks
public import CFSG.Quasithin.Background.B19Setup
public import CFSG.Quasithin.Background.B610
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.B610T.TwoBlk

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def burnsideB610_valHom {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem burnsideB610_valHom_apply {V : Subgroup G} (hV : IsElemAbelian 2 V) (u : IntMod V hV) :
    burnsideB610_valHom hV u = u.val := rfl

theorem burnsideB610_valHom_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (burnsideB610_valHom hV) :=
  fun _ _ h => IntMod.val_injective h

theorem burnsideB610_commutator_eq_map {V : Subgroup G} (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V, Y⁆ = (commV (autI hV Y)).map (burnsideB610_valHom hV) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv y hy
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hYN hy
    set w₀ : IntMod V hV := IntMod.mk hV ⟨v, hv⟩ with hw₀
    have hx : convI hV ⟨y, hyN⟩ ∈ autI hV Y := convI_mem_autI hV hy hyN
    refine ⟨convI hV ⟨y, hyN⟩ w₀⁻¹ * w₀, Subgroup.subset_closure ⟨_, hx, w₀⁻¹, by simp⟩, ?_⟩
    have h1 : (convI hV ⟨y, hyN⟩ w₀⁻¹).val = y * v⁻¹ * y⁻¹ :=
      convI_apply_val hV ⟨y, hyN⟩ w₀⁻¹
    have h2 : w₀.val = v := rfl
    have hcomm : (convI hV ⟨y, hyN⟩ w₀⁻¹).val * v = v * (convI hV ⟨y, hyN⟩ w₀⁻¹).val :=
      IntMod.val_comm _ w₀
    show (convI hV ⟨y, hyN⟩ w₀⁻¹ * w₀).val = ⁅v, y⁆
    rw [IntMod.val_mul, h2, hcomm, h1, commutatorElement_def]
    group
  · rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hx
    have h1 : (convI hV g w).val = (g : G) * w.val * (g : G)⁻¹ := convI_apply_val hV g w
    show burnsideB610_valHom hV (convI hV g w * w⁻¹) ∈ ⁅V, Y⁆
    rw [burnsideB610_valHom_apply, IntMod.val_mul, h1, IntMod.val_inv]
    have : (g : G) * w.val * (g : G)⁻¹ * w.val⁻¹ = ⁅(g : G), w.val⁆ := by
      rw [commutatorElement_def]
    rw [this, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hg w.val_mem

theorem burnsideB610_mk_mem_commV {V : Subgroup G} (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) {w : G} (hw : w ∈ ⁅V, Y⁆) (hwV : w ∈ V) :
    IntMod.mk hV ⟨w, hwV⟩ ∈ commV (autI hV Y) := by
  rw [burnsideB610_commutator_eq_map hV hYN] at hw
  obtain ⟨m, hm, hmw⟩ := hw
  have : m = IntMod.mk hV ⟨w, hwV⟩ := IntMod.val_injective hmw
  rw [← this]
  exact hm

theorem burnsideB610_val_mem_commutator {V : Subgroup G} (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) {m : IntMod V hV} (hm : m ∈ commV (autI hV Y)) :
    m.val ∈ ⁅V, Y⁆ := by
  rw [burnsideB610_commutator_eq_map hV hYN]
  exact ⟨m, hm, rfl⟩

theorem burnsideB610_card_commutator {V : Subgroup G} (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (⁅V, Y⁆ : Subgroup G) = Nat.card (commV (autI hV Y)) := by
  rw [burnsideB610_commutator_eq_map hV hYN,
    Subgroup.card_map_of_injective (burnsideB610_valHom_injective hV)]

theorem burnsideB610_inf_centralizer_eq_bot {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {Y : Subgroup G} (hYN : Y ≤ Subgroup.normalizer (V : Set G))
    (h : commV (autI hV Y) ⊓ fixV (autI hV Y) = ⊥) :
    ⁅V, Y⁆ ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  have huV : u ∈ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hYN hu.1
  have h1 : IntMod.mk hV ⟨u, huV⟩ ∈ commV (autI hV Y) := burnsideB610_mk_mem_commV hV hYN hu.1 huV
  have h2 : IntMod.mk hV ⟨u, huV⟩ ∈ fixV (autI hV Y) := (mem_fixV_autI hV hYN _).2 hu.2
  have h3 : IntMod.mk hV ⟨u, huV⟩ ∈ commV (autI hV Y) ⊓ fixV (autI hV Y) := ⟨h1, h2⟩
  rw [h, Subgroup.mem_bot] at h3
  exact congrArg IntMod.val h3

theorem burnsideB610_autI_le_normalizer {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {X Y : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    autI hV X ≤ Subgroup.normalizer (autI hV Y : Set (MulAut (IntMod V hV))) := by
  have key : ∀ φ ∈ autI hV X, ∀ ψ ∈ autI hV Y, φ * ψ * φ⁻¹ ∈ autI hV Y := by
    intro φ hφ ψ hψ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨h, hh, rfl⟩ := (mem_autI hV).1 hψ
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (mem_autI hV).2 ⟨_, (Subgroup.mem_normalizer_iff.mp (hXY hg) h).mp hh, rfl⟩
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  refine ⟨key φ hφ ψ, fun h => ?_⟩
  have := key φ⁻¹ (Subgroup.inv_mem _ hφ) _ h
  rwa [inv_inv, show φ⁻¹ * (φ * ψ * φ⁻¹) * φ = ψ by group] at this

theorem burnsideB610_isSubnormal_autI {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {A B : Subgroup G} (h : IsSubnormal A B) : IsSubnormal (autI hV A) (autI hV B) := by
  induction h with
  | refl A => exact IsSubnormal.refl _
  | @step A M B hAM hn _ ih =>
    refine IsSubnormal.step (autI_mono hV hAM) ?_ ih
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (autI_mono hV hAM)]
    exact burnsideB610_autI_le_normalizer hV
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mp hn)

theorem burnsideB610_pCoreOf_le_of_isSubnormal {Γ : Type*} [Group Γ] [Finite Γ] (p : ℕ)
    [Fact p.Prime] {A B : Subgroup Γ} (h : IsSubnormal A B) : pCoreOf p A ≤ pCoreOf p B := by
  induction h with
  | refl A => exact le_rfl
  | @step A M B hAM hn _ ih =>
    refine le_trans ?_ ih
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
      ((CFSG.LieType.BorelTits.pCoreOf_le p A).trans hAM) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p A)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mp hn).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p A)

theorem burnsideB610_le_pCoreOf_of_isSubnormal {Γ : Type*} [Group Γ] [Finite Γ] (p : ℕ)
    [Fact p.Prime] {A B : Subgroup Γ} (h : IsSubnormal A B) (hA : IsPGroup p A) :
    A ≤ pCoreOf p B :=
  (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p le_rfl Subgroup.le_normalizer hA).trans
    (burnsideB610_pCoreOf_le_of_isSubnormal p h)

theorem burnsideB610_setting {W : Type*} [CommGroup W] [Finite W] (X : Subgroup (MulAut W)) :
    B19.Setting X (pCoreOf 3 X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 3 X, fun g hg f hf => ?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 X hg) f).mp hf
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 X)
    rw [hk]
    exact Odd.pow (by decide)
  · have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 X).isNilpotent
    infer_instance

theorem burnsideB610_le_autI_twoResidual [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {H : Subgroup G} {B : Subgroup (MulAut (IntMod V hV))} (hBH : B ≤ autI hV H)
    (hB : Odd (Nat.card B)) : B ≤ autI hV (twoResidual H) := by
  intro y hy
  have h1 : orderOf (⟨y, hy⟩ : ↥B) ∣ Nat.card B := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact E2.mem_autI_twoResidual_of_odd (hBH hy) (Odd.of_dvd_nat hB h1)

theorem burnsideB610_exists_gen {Γ : Type*} [Group Γ] {A : Subgroup Γ} (hA : Nat.card A = 3) :
    ∃ x ∈ A, x ^ 3 = 1 ∧ x ≠ 1 ∧ A = Subgroup.zpowers x := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA
    norm_num at hA
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have h1 : orderOf (⟨x, hx⟩ : ↥A) ∣ Nat.card A := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hA] at h1
  have hord : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1'
    · exact h
  refine ⟨x, hx, by rw [← hord]; exact pow_orderOf_eq_one x, hx1', ?_⟩
  have : Finite (Subgroup.zpowers x) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx)
    (by rw [hA, Nat.card_zpowers, hord])).symm

theorem burnsideB610_natTwo_data {L V : Subgroup G} (h : IsNaturalL2Prime 1 L V) :
    ∃ Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)), Nat.card Γ = 3 ∧
      IsNaturalSection L ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G))
        ((L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L) Γ := by
  rcases h with ⟨h1, -⟩ | ⟨-, h⟩
  · omega
  · exact h

theorem burnsideB610_card_autI_eq_three [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {L : Subgroup G} (hLN : L ≤ Subgroup.normalizer (V : Set G)) (h : IsNaturalL2Prime 1 L V) :
    Nat.card (autI hV L) = 3 := by
  obtain ⟨Γ, hΓ, -, α, hα, hαk, -⟩ := burnsideB610_natTwo_data h
  have e1 := card_autI_mul_card_inf hV hLN
  have e2 := Subgroup.card_ker_mul_card_range α
  rw [MonoidHom.range_eq_top.mpr hα, Subgroup.card_top, hΓ, hαk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : L ⊓ Subgroup.centralizer (V : Set G) ≤ L)).toEquiv] at e2
  have hpos : 0 < Nat.card ↥(L ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have key : Nat.card (autI hV L) * Nat.card ↥(L ⊓ Subgroup.centralizer (V : Set G)) =
      3 * Nat.card ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [e1, ← e2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos key

theorem burnsideB610_card_commutator_eq_four [Finite G] {L V : Subgroup G}
    (h : IsNaturalL2Prime 1 L V) (hfix : ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Nat.card (⁅V, L⁆ : Subgroup G) = 4 := by
  obtain ⟨Γ, -, -, -, -, -, β, hβ, hβk, -⟩ := burnsideB610_natTwo_data h
  have e := Subgroup.card_ker_mul_card_range β
  rw [MonoidHom.range_eq_top.mpr hβ, Subgroup.card_top, hβk, hfix] at e
  have h1 : ((⊥ : Subgroup G).subgroupOf ⁅V, L⁆) = ⊥ := Subgroup.bot_subgroupOf _
  rw [h1, Subgroup.card_bot, one_mul] at e
  rw [← e, Nat.card_eq_fintype_card]
  rfl

end CFSG.Quasithin.B610T.TwoBlk
