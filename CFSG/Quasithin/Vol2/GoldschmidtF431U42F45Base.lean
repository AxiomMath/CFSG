module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuGrp
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F45Ru

section Core

variable {X : Type*} [Group X]

theorem pCoreOf_eq_coreIn {G S : Subgroup X} (hS : IsSylowTwoOf S G) :
    pCoreOf 2 G = coreIn S G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro x hx
    refine ⟨pCoreOf_le 2 G hx, fun g hg => ?_⟩
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ pCoreOf 2 G :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 G (G.inv_mem hg)) x).1 hx
    have := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS h1
    simpa using this
  · exact le_pCoreOf_of_le_normalizer 2 (coreIn_le_left S G) (le_normalizer_coreIn S G)
      (hS.2.1.to_le (coreIn_le_right S G))

end Core

section Base

variable {X : Type*} [Group X] [Finite X] {V : Type*} [MulAction X V] {Γ : SimpleGraph V}
  [GraphAction X Γ]

theorem core_fixes_nbrs {a : V} (hn : 3 ≤ Nat.card (Γ.neighborSet a))
    (hodd : ¬ 2 ∣ Nat.card (Γ.neighborSet a))
    (two : ∀ b c b' c', Γ.Adj a b → Γ.Adj a c → b ≠ c → Γ.Adj a b' → Γ.Adj a c' → b' ≠ c' →
      ∃ g : X, g • a = a ∧ g • b = b' ∧ g • c = c')
    {w : V} (hw : Γ.Adj a w) {q : X} (hq : q ∈ pCoreOf 2 (MulAction.stabilizer X a))
    {u : V} (hu : Γ.Adj a u) : q • u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G := MulAction.stabilizer X a with hG
  have hflag : ∀ b, Γ.Adj a b → ∃ y : X, y • a = a ∧ y • w = b := fun b hb => by
    obtain ⟨c, hc, hcw⟩ := exists_nbr_ne_of_card hn w
    obtain ⟨c', hc', hc'b⟩ := exists_nbr_ne_of_card hn b
    obtain ⟨g, hg1, hg2, -⟩ := two w c b c' hw hc (Ne.symm hcw) hb hc' (Ne.symm hc'b)
    exact ⟨g, hg1, hg2⟩
  have horb : MulAction.orbit G w = Γ.neighborSet a := by
    ext v
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      have hg' : g • a = a := MulAction.mem_stabilizer_iff.mp hg
      have := (GraphAction.adj_smul g a w).mpr hw
      rwa [hg'] at this
    · intro hv
      obtain ⟨y, hy1, hy2⟩ := hflag v hv
      exact ⟨⟨y, MulAction.mem_stabilizer_iff.mpr hy1⟩, hy2⟩
  have hnorm : ((pCoreOf 2 G).subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 G)).2 (le_normalizer_pCoreOf 2 G)
  have hpg : IsPGroup 2 ((pCoreOf 2 G).subgroupOf G) :=
    IsPGroup.of_equiv (pCoreOf_isPGroup 2 G) (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 G)).symm
  have hd : ¬ 2 ∣ Nat.card (MulAction.orbit G w) := by
    rw [Nat.card_coe_set_eq, horb, ← Nat.card_coe_set_eq]
    exact hodd
  have huo : u ∈ MulAction.orbit G w := by
    rw [horb]
    exact hu
  have hfin : Finite (MulAction.orbit G w) := (Set.finite_range (fun g : G => g • w)).to_subtype
  have := normal_pgroup_fixes (Ω := MulAction.orbit G w) ((pCoreOf 2 G).subgroupOf G) hpg hd
    ⟨q, pCoreOf_le 2 G hq⟩ (Subgroup.mem_subgroupOf.mpr hq) ⟨u, huo⟩
  exact congrArg Subtype.val this

theorem modelBase_of_core {a : V} {m : ℕ} {S : Subgroup X}
    (hS : IsSylowTwoOf S (MulAction.stabilizer X a)) (Rs : Set X)
    (hRs : ∀ r ∈ Rs, r ∈ MulAction.stabilizer X a)
    (hdec : ∀ g ∈ MulAction.stabilizer X a,
      ∃ r ∈ Rs, r⁻¹ * g ∈ Subgroup.normalizer (S : Set X)) {b₀ : V}
    (hfar : ∀ b, Γ.dist a b = m →
      ∃ q ∈ S, (∀ r ∈ Rs, r⁻¹ * q * r ∈ S) ∧ q • b₀ = b)
    (hfree : ∀ q ∈ S, (∀ r ∈ Rs, r⁻¹ * q * r ∈ S) → q • b₀ = b₀ → q = 1)
    (hn : 3 ≤ Nat.card (Γ.neighborSet a)) (hodd : ¬ 2 ∣ Nat.card (Γ.neighborSet a))
    (two : ∀ b c b' c', Γ.Adj a b → Γ.Adj a c → b ≠ c → Γ.Adj a b' → Γ.Adj a c' → b' ≠ c' →
      ∃ g : X, g • a = a ∧ g • b = b' ∧ g • c = c') :
    ModelBase Γ m a (pCoreOf 2 (MulAction.stabilizer X a)) := by
  set G := MulAction.stabilizer X a with hG
  have hQ : pCoreOf 2 G = coreIn S G := pCoreOf_eq_coreIn hS
  have hSG : S ≤ G := hS.1
  have hmem : ∀ x, x ∈ coreIn S G ↔ x ∈ G ∧ ∀ r ∈ Rs, r⁻¹ * x * r ∈ S := by
    intro x
    constructor
    · rintro ⟨hxG, h⟩
      exact ⟨hxG, fun r hr => h r (hRs r hr)⟩
    · rintro ⟨hxG, h⟩
      refine ⟨hxG, fun g hg => ?_⟩
      obtain ⟨r, hr, hn⟩ := hdec g hg
      have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) _).1 (h r hr)
      have e : g⁻¹ * x * g = (r⁻¹ * g)⁻¹ * (r⁻¹ * x * r) * (r⁻¹ * g)⁻¹⁻¹ := by group
      rw [e]
      exact h2
  have hcore : ∀ q ∈ S, (∀ r ∈ Rs, r⁻¹ * q * r ∈ S) → q ∈ coreIn S G := fun q hq h =>
    (hmem q).2 ⟨hSG hq, h⟩
  refine ⟨fun w hw q hq => core_fixes_nbrs hn hodd two hw hq hw, ?_, ?_, two⟩
  · intro b c hb hc
    obtain ⟨qb, hqbS, hqbR, hqb⟩ := hfar b hb
    obtain ⟨qc, hqcS, hqcR, hqc⟩ := hfar c hc
    refine ⟨qc * qb⁻¹, ?_, ?_⟩
    · rw [hQ]
      exact (coreIn S G).mul_mem (hcore _ hqcS hqcR)
        ((coreIn S G).inv_mem (hcore _ hqbS hqbR))
    · rw [mul_smul, ← hqb, inv_smul_smul, hqc]
  · intro b hb q hq hqb
    obtain ⟨q₁, hq₁S, hq₁R, hq₁⟩ := hfar b hb
    rw [hQ] at hq
    have hq₁c := hcore _ hq₁S hq₁R
    have hp : q₁⁻¹ * q * q₁ ∈ coreIn S G :=
      (coreIn S G).mul_mem ((coreIn S G).mul_mem ((coreIn S G).inv_mem hq₁c) hq) hq₁c
    have hpS : q₁⁻¹ * q * q₁ ∈ S := coreIn_le_right _ _ hp
    have hpR : ∀ r ∈ Rs, r⁻¹ * (q₁⁻¹ * q * q₁) * r ∈ S := fun r hr => hp.2 r (hRs r hr)
    have hfix : (q₁⁻¹ * q * q₁) • b₀ = b₀ := by
      rw [mul_smul, mul_smul, hq₁, hqb, inv_smul_eq_iff]
      exact hq₁.symm
    have h1 := hfree _ hpS hpR hfix
    calc q = q₁ * (q₁⁻¹ * q * q₁) * q₁⁻¹ := by group
      _ = 1 := by rw [h1]; group

end Base

end CFSG.Quasithin.H13.F431.U42
