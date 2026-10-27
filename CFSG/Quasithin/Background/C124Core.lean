module

public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.Background.F1Models

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure EntryPlus (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V) : Prop extends
    Entry X T V L R m hV where
  Lq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  Csyl : IsSylowTwoOf (pCoreOf 2 X) (X ⊓ Subgroup.centralizer (V : Set G))

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV)

include E

theorem hXN : X ≤ Subgroup.normalizer (V : Set G) := E.red.2.1

theorem hLX : L ≤ X := le_of_mem_cComp E.comp

theorem hLN : L ≤ Subgroup.normalizer (V : Set G) := E.hLX.trans E.hXN

theorem perf : ⁅L, L⁆ = L := perfect_of_mem_cComp E.comp

theorem Q_le_C : pCoreOf 2 X ≤ X ⊓ Subgroup.centralizer (V : Set G) :=
  le_inf (pCoreOf_le 2 X) (pCoreOf_le_centralizer E.red)

theorem C_le_sup : X ⊓ Subgroup.centralizer (V : Set G) ≤ L ⊔ pCoreOf 2 X := by
  intro c hc
  have hcX : c ∈ X := hc.1
  obtain ⟨k, hk⟩ := exists_pow_mem_of_prod E.hLX E.normal E.sylow.1 E.sylow.2.1 hcX
    (E.prod c hcX)
  set C : Subgroup G := X ⊓ Subgroup.centralizer (V : Set G) with hC
  have hQn : ((pCoreOf 2 X).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer E.Q_le_C]
    exact inf_le_left.trans (le_normalizer_pCoreOf 2 X)
  have hpow : c ^ ((pCoreOf 2 X).subgroupOf C).index ∈ pCoreOf 2 X := by
    have := Subgroup.pow_index_mem ((pCoreOf 2 X).subgroupOf C) (⟨c, hc⟩ : ↥C)
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hodd : ¬ 2 ∣ ((pCoreOf 2 X).subgroupOf C).index := E.Csyl.2.2
  have hcop : IsCoprime ((2 : ℤ) ^ k) (((pCoreOf 2 X).subgroupOf C).index : ℤ) := by
    have h1 : Nat.Coprime (2 ^ k) ((pCoreOf 2 X).subgroupOf C).index :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    exact_mod_cast Nat.isCoprime_iff_coprime.2 h1
  obtain ⟨u, v, huv⟩ := hcop
  have e : c = (c ^ 2 ^ k) ^ u * (c ^ ((pCoreOf 2 X).subgroupOf C).index) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have h1 : ((2 ^ k : ℕ) : ℤ) * u + (((pCoreOf 2 X).subgroupOf C).index : ℤ) * v = 1 := by
      have h2 : (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) := by push_cast; rfl
      rw [h2] at huv
      linarith
    rw [h1, zpow_one]
  rw [e]
  exact Subgroup.mul_mem_sup (zpow_mem hk u) (zpow_mem hpow v)

theorem comm_C_L : ∀ d ∈ X ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ L,
    d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
  commutator_centralizer_le_pCoreOf E.red E.hLX E.normal E.VL
    (Or.inl (B1Red.isQuasisimple_to_open E.Lq))

end EntryPlus

end CFSG.Quasithin.C124
