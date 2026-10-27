module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.SzF53B3NGeo
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.NatAPI

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

def stabW (c : Fin 4 → ZMod 2) : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | CFSG.Quasithin.F53Mod.natAct σ c = c}
  one_mem' := by
    show CFSG.Quasithin.F53Mod.natAct 1 c = c
    exact CFSG.Quasithin.F53Mod.natAct_one c
  mul_mem' := fun {σ τ} hσ hτ => by
    show CFSG.Quasithin.F53Mod.natAct (σ * τ) c = c
    rw [CFSG.Quasithin.F53Mod.natAct_mul]
    show CFSG.Quasithin.F53Mod.natAct σ (CFSG.Quasithin.F53Mod.natAct τ c) = c
    have h1 : CFSG.Quasithin.F53Mod.natAct τ c = c := hτ
    have h2 : CFSG.Quasithin.F53Mod.natAct σ c = c := hσ
    rw [h1, h2]
  inv_mem' := fun {σ} hσ => by
    show CFSG.Quasithin.F53Mod.natAct σ⁻¹ c = c
    have h2 : CFSG.Quasithin.F53Mod.natAct σ c = c := hσ
    have := CFSG.Quasithin.F53Mod.natAct_mul σ⁻¹ σ c
    rw [inv_mul_cancel, CFSG.Quasithin.F53Mod.natAct_one, show CFSG.Quasithin.F53Mod.natAct σ c = c from h2] at this
    exact this.symm

private theorem fact_card_stab : ∀ c : Fin 4 → ZMod 2, c ≠ 0 →
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 5) => CFSG.Quasithin.F53Mod.natAct σ c = c)).card = 8 := by
  decide +kernel

theorem card_stabW (c : Fin 4 → ZMod 2) (hc : c ≠ 0) : Nat.card (stabW c) = 8 := by
  have h := fact_card_stab c hc
  rw [← h, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rfl

theorem card_of_isSylowTwoOf_top {T : Subgroup (Equiv.Perm (Fin 5))}
    (hT : IsSylowTwoOf T ⊤) : Nat.card T = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT.2.1
  have hidx : Nat.card T * (T.subgroupOf ⊤).index = 120 := by
    have h1 := Subgroup.card_mul_index T
    have h2 : (T.subgroupOf ⊤).index = T.index := by
      exact (Subgroup.relIndex_top_right (H := T) :)
    rw [h2, h1, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hodd := hT.2.2
  rw [hk] at hidx ⊢
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans ⟨_, hidx.symm⟩
    omega
  interval_cases k <;> simp_all <;> omega


theorem mul_inv_mem_of_relIndex_two' {W P : Subgroup G} (h : W.relIndex P = 2) {a b : G}
    (ha : a ∈ P) (hb : b ∈ P) (haW : a ∉ W) (hbW : b ∉ W) : a * b⁻¹ ∈ W := by
  have h2 : (W.subgroupOf P).index = 2 := h
  have hiff : ((⟨a, ha⟩ : P) ∈ W.subgroupOf P ↔ (⟨b, hb⟩ : P)⁻¹ ∈ W.subgroupOf P) := by
    rw [inv_mem_iff]
    exact ⟨fun h' => absurd (Subgroup.mem_subgroupOf.mp h') haW,
      fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hbW⟩
  have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨a, ha⟩ : P))
    (b := (⟨b, hb⟩ : P)⁻¹)).2 hiff
  exact Subgroup.mem_subgroupOf.mp h3

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem mem_stab_of_comm_mem_Cv {δ ℓ : Geo H M} (hδ : vtype δ = false) (hℓ : ℓ ∈ nbrs δ)
    {z x : G} (hz : z ∈ Zv ℓ) (hzC : z ∉ F53B3.Cv δ) (hx : x ∈ stab δ)
    (hxz : x * z * x⁻¹ * z⁻¹ ∈ F53B3.Cv δ) : x ∈ stab ℓ := by
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData hδ
  have hvℓ : vtype ℓ = true := vtype_true_of_mem_nbrs_false hℓ hδ
  have hzV : z ∈ Vn δ :=
    CFSG.Quasithin.F53B3.N37.Zv_le_Vn_of_adj (show (graph (H ⊔ M) H M).Adj δ ℓ from hℓ) hz
  have hstabN := CFSG.Quasithin.F53B3.N37.stab_le_normalizer_Cv (H := H) (M := M) δ
  have hzs : z ∈ stab δ :=
    CFSG.Quasithin.F53B3.N37.Qv_le_stab_self δ (C.Vn_le_Qv_self hδ hzV)
  have hL : ∀ g ∈ stab δ, ∀ l : G, l ∈ F53B3.Cv δ ↔ g * l * g⁻¹ ∈ F53B3.Cv δ := fun g hg l =>
    Subgroup.mem_normalizer_iff.mp (hstabN hg) l
  obtain ⟨v, hv⟩ := hsd.surj (QuotientGroup.mk (⟨z, hzV⟩ : ↥(Vn δ)))
  have fixiff : ∀ (y : G) (hy : y ∈ stab δ),
      nat.act (θ ⟨y, hy⟩) v = v ↔ y * z * y⁻¹ * z⁻¹ ∈ F53B3.Cv δ := by
    intro y hy
    obtain ⟨hkx, h⟩ := hsd.equiv ⟨y, hy⟩ v ⟨z, hzV⟩ hv
    have hq : (F53B3.Cv δ).subgroupOf (Vn δ) = (F53B3.Cv δ).subgroupOf (Vn δ) := rfl
    have key : z⁻¹ * (y * z * y⁻¹) ∈ F53B3.Cv δ ↔ y * z * y⁻¹ * z⁻¹ ∈ F53B3.Cv δ := by
      have := hL z hzs (z⁻¹ * (y * z * y⁻¹))
      rw [show z * (z⁻¹ * (y * z * y⁻¹)) * z⁻¹ = y * z * y⁻¹ * z⁻¹ by group] at this
      exact this
    constructor
    · intro hf
      rw [hf, hv, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      exact key.mp h
    · intro hc
      apply hsd.inj
      rw [h, hv]
      symm
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact key.mpr hc
  have hv1 : v ≠ 1 := by
    intro h1
    rw [h1, map_one] at hv
    have := (QuotientGroup.eq_one_iff _).mp hv.symm
    exact hzC (Subgroup.mem_subgroupOf.mp this)
  obtain ⟨c0, hc0def⟩ : ∃ c0 : Fin 4 → ZMod 2,
      Multiplicative.ofAdd c0 = (v : Multiplicative (Fin 4 → ZMod 2)) :=
    ⟨Multiplicative.toAdd (v : Multiplicative (Fin 4 → ZMod 2)), rfl⟩
  have hmemstab : ∀ σ : Equiv.Perm (Fin 5), σ ∈ stabW c0 ↔ nat.act σ v = v := by
    intro σ
    show CFSG.Quasithin.F53Mod.natAct σ c0 = c0 ↔ _
    constructor
    · intro h
      have h' : nat.act σ v = Multiplicative.ofAdd (CFSG.Quasithin.F53Mod.natAct σ c0) := by
        rw [← hc0def]; rfl
      rw [h', h, hc0def]
    · intro h
      have h' : nat.act σ v = Multiplicative.ofAdd (CFSG.Quasithin.F53Mod.natAct σ c0) := by
        rw [← hc0def]; rfl
      rw [h'] at h
      have := congrArg Multiplicative.toAdd (h.trans hc0def.symm)
      exact this
  have hc0 : c0 ≠ 0 := by
    intro h
    apply hv1
    have : (v : Multiplicative (Fin 4 → ZMod 2)) = 1 := by rw [← hc0def, h]; rfl
    exact this
  have hS := CFSG.Quasithin.F53.sylow_stab_inf_left C.hA hℓ
  have hT := CFSG.QuasithinUnique.Setup.Wreath.isSylowTwoOf_map_hom hS θ
  rw [MonoidHom.range_eq_top.mpr hθs] at hT
  have hcardT := card_of_isSylowTwoOf_top hT
  have hrel2 : (Zv δ).relIndex (Zv ℓ) = 2 := by
    have h := Subgroup.relIndex_mul_card (Zv δ) (Zv ℓ)
    rw [inf_of_le_left (C.Zv_le_Zv_of_mem_nbrs hvℓ (mem_nbrs_comm hℓ)), C.card_Zv_false hδ,
      C.card_Zv_true hvℓ] at h
    omega
  have hZδL : Zv δ ≤ F53B3.Cv δ := C.Zv_le_Cv hδ
  have hle : ((stab δ ⊓ stab ℓ).subgroupOf (stab δ)).map θ ≤ stabW c0 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_subgroupOf.mp hy
    rw [hmemstab, fixiff (y : G) y.2]
    have ha : (y : G) * z * (y : G)⁻¹ ∈ Zv ℓ :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv C.hA ℓ hy'.2) z).mp hz
    have haL : (y : G) * z * (y : G)⁻¹ ∉ F53B3.Cv δ := by
      intro h
      apply hzC
      have := (hL ((y : G)⁻¹) (inv_mem y.2) _).mp h
      simpa [mul_assoc] using this
    have hzδ : z ∉ Zv δ := fun h => hzC (hZδL h)
    have haδ : (y : G) * z * (y : G)⁻¹ ∉ Zv δ := fun h => haL (hZδL h)
    have := mul_inv_mem_of_relIndex_two' hrel2 ha hz haδ hzδ
    exact hZδL this
  have hEq := Subgroup.eq_of_le_of_card_ge hle (by rw [card_stabW c0 hc0, hcardT])
  have hxmem : θ ⟨x, hx⟩ ∈ stabW c0 := (hmemstab _).mpr ((fixiff x hx).mpr hxz)
  rw [← hEq] at hxmem
  obtain ⟨y, hy, hyx⟩ := hxmem
  have hy' := Subgroup.mem_subgroupOf.mp hy
  have hker : (y⁻¹ * ⟨x, hx⟩ : ↥(stab δ)) ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx]; simp
  rw [hθk, Subgroup.mem_subgroupOf] at hker
  have hQ : (y : G)⁻¹ * x ∈ Qv δ := hker
  have := (CFSG.Quasithin.F53.Qv_le_stab_of_mem_nbrs C.hA hℓ) hQ
  have hxy := mul_mem hy'.2 this
  simpa using hxy

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
