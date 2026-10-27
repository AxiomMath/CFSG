module

public import CFSG.RankThree.GF2n.Tim81.Sec4.OrthW
public import CFSG.RankThree.GF2n.Tim81.Sec4.SecRep
public import CFSG.RankThree.GF2n.Tim81.Sec2.NatSum
public import CFSG.RankThree.GF2n.Tim81.Sec4.W0Orth

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def KModWNatSum (V H : Subgroup G) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) : Prop :=
  ∀ hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H),
    haveI : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hs.normal
    ∀ hmod : Module (ZMod 2) (SecMod hs),
      letI := hmod
      Sec2.IsNatSumModule (repSec hs hs.comm SL(2, F) ψ)

structure Sec45ShapeWith (M V H : Subgroup G) (F : Type) [Field F] [Fintype F] [CharP F 2]
    (l : ℕ) (hl : Fintype.card F = 2 ^ (2 * l)) (ψ : HBar V H ≃* SL(2, F)) : Prop where
  one_le : 1 ≤ l
  card_V : Nat.card V = 2 ^ l
  card_W : Nat.card (Tim79a.xOf V H) = 2 ^ (4 * l)
  orth : ∀ (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
      (hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))),
      letI := hmod
      Sec2.IsOrthModule hl (repW hW ψ)
  center_K : kOf V H ⊓ Subgroup.centralizer (kOf V H : Set G) = Tim79a.xOf V H
  center_PK : Pc M V ⊓ kOf V H ⊓
      Subgroup.centralizer ((Pc M V ⊓ kOf V H : Subgroup G) : Set G) = Pc M V ⊓ Tim79a.xOf V H
  sq_mem : ∀ k ∈ kOf V H, k * k ∈ Tim79a.xOf V H
  natSum : KModWNatSum V H ψ
  alt : kOf V H = Tim79a.xOf V H ∨
    (⁅kOf V H, kOf V H⁆ = Tim79a.xOf V H ∧ inSubgroup frattini (kOf V H) = Tim79a.xOf V H)

structure Sec45Shape (M V H : Subgroup G) (h₀ : G) : Prop where
  hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)
  mem : IsHMember M V H
  le_pCore : V ≤ inSubgroup (pCore 2) H
  kFact : KFactorization M V H h₀
  shape : ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2) (l : ℕ)
    (hl : Fintype.card F = 2 ^ (2 * l)) (ψ : HBar V H ≃* SL(2, F)),
    Sec45ShapeWith M V H F l hl ψ

@[expose] def Sec45At (M V : Subgroup G) : Prop :=
  ∀ h₀ : G, IsHMember M V (Pc M V ⊔ conjSubgroup h₀ (Pc M V)) →
    Sec45Shape M V (Pc M V ⊔ conjSubgroup h₀ (Pc M V)) h₀

@[expose] def Sec45Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G), RootHyp M V → Sec45At M V

namespace Sec45ShapeWith

variable {M V H : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
  {hl : Fintype.card F = 2 ^ (2 * l)} {ψ : HBar V H ≃* SL(2, F)}

theorem orth' (hw : Sec45ShapeWith M V H F l hl ψ)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] :
    Sec2.IsOrthModule hl (repW (hW := hW) ψ) :=
  hw.orth hW inferInstance

theorem orth_subRepW (hw : Sec45ShapeWith M V H F l hl ψ)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] :
    Sec2.IsOrthModule hl
      (subRepW (hW := hW) ψ (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H)
        (Tim79a.H_le_normalizer_xOf V H)) := by
  obtain ⟨j, β, hβ⟩ := hw.orth' hW
  let U : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    subW (hW := hW) (Tim79a.xOf V H)
  have hUt : U = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      rw [← ofW_toW hW x, mem_subW_iff]
      exact (toW hW x).2
  let e : U ≃ₗ[ZMod 2] Additive (IntMod (Tim79a.xOf V H) hW) :=
    (LinearEquiv.ofEq U ⊤ hUt).trans Submodule.topEquiv
  refine ⟨j, e.toAddEquiv.trans β, ?_⟩
  intro g u
  have hsub : e (subRepW (hW := hW) ψ (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H)
      (Tim79a.H_le_normalizer_xOf V H) g u) = repW (hW := hW) ψ g (e u) := by
    change ((CFSG.Quasithin.B45U33.subRep (repW (hW := hW) ψ)
        (subW (hW := hW) (Tim79a.xOf V H))
        ((normalizer_subW_iff hW ψ (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H)).mp
          (Tim79a.H_le_normalizer_xOf V H)) g u : U) :
          Additive (IntMod (Tim79a.xOf V H) hW)) = repW (hW := hW) ψ g (e u)
    rw [CFSG.Quasithin.B45U33.subRep_apply]
    rw [show e u = (u : Additive (IntMod (Tim79a.xOf V H) hW)) from rfl]
  calc (e.toAddEquiv.trans β) (subRepW (hW := hW) ψ
        (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H)
        (Tim79a.H_le_normalizer_xOf V H) g u)
      = β (e (subRepW (hW := hW) ψ (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H)
          (Tim79a.H_le_normalizer_xOf V H) g u)) := rfl
    _ = β (repW (hW := hW) ψ g (e u)) := by rw [hsub]
    _ = hermAct l (sig_sig hl)
        (CFSG.QuasithinUnique.Setup.SL2Modules.fieldAut F j g) (β (e u)) := hβ g (e u)
    _ = hermAct l (sig_sig hl)
        (CFSG.QuasithinUnique.Setup.SL2Modules.fieldAut F j g)
        ((e.toAddEquiv.trans β) u) := rfl

theorem isOrthModule_repW_of_one
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [inst : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (ψ : HBar V H ≃* SL(2, F)) (hl : Fintype.card F = 2 ^ (2 * l))
    (horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ))
    (hW' : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    (hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW'))) :
    letI := hmod
    Sec2.IsOrthModule hl (repW (hW := hW') ψ) := by
  letI := hmod
  have hW'eq : hW' = hW := Subsingleton.elim _ _
  subst hW'eq
  have hmod_eq : hmod = inst := Subsingleton.elim _ _
  subst hmod_eq
  exact horth

end Sec45ShapeWith

namespace Sec45Shape

variable {M V H : Subgroup G} {h₀ : G}

theorem Pc_le (hS : Sec45Shape M V H h₀) : Pc M V ≤ H :=
  hS.mem.2.1

theorem not_le (hS : Sec45Shape M V H h₀) : ¬ H ≤ M :=
  hS.mem.2.2

theorem isElemAbelian (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    Assembly.IsElemAbelian 2 (Tim79a.xOf V H) :=
  h.isElemAbelian_xOf hS.Pc_le hS.le_pCore

theorem quotModHyp (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H) where
  le := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  comm := by
    intro n hn n' hn'
    obtain ⟨_, _, _, _, _, _, _, hw⟩ := hS.shape
    rcases hw.alt with hK | ⟨hK, -⟩
    · have hcomm : n * n' = n' * n := by
        have h1 := (hS.isElemAbelian h).1.is_comm.comm
          (⟨n, hK ▸ hn⟩ : ↥(Tim79a.xOf V H)) (⟨n', hK ▸ hn'⟩ : ↥(Tim79a.xOf V H))
        exact congrArg Subtype.val h1
      have hone : n * n' * n⁻¹ * n'⁻¹ = 1 := by
        rw [hcomm]
        group
      rw [hone]
      exact (Tim79a.xOf V H).one_mem
    · have hmem : ⁅n, n'⁆ ∈ ⁅kOf V H, kOf V H⁆ :=
        Subgroup.commutator_mem_commutator hn hn'
      rw [show n * n' * n⁻¹ * n'⁻¹ = ⁅n, n'⁆ from rfl, ← hK]
      exact hmem
  conj := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_kOf V H hg) n).1 hn
  conj₀ := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.1 (Tim79a.H_le_normalizer_xOf V H hg) n).1 hn

theorem kOf_le_M (h : RootHyp M V) (hS : Sec45Shape M V H h₀) : kOf V H ≤ M := by
  have := h.kOf_le_conjSubgroup_of_mem (V := V) (H := H) (y := 1) H.one_mem
  simpa [conjSubgroup_one] using this

theorem card_inf_Pc_xOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    Nat.card ↥(Pc M V ⊓ Tim79a.xOf V H) = Nat.card V ^ 3 := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW := hS.isElemAbelian h
  letI := moduleOfElemAbelian hW
  have hcard := h.card_inf_Pc_W0_eq_pow_of_isOrthModule (hW := hW) hS.Pc_le hS.le_pCore
    hS.hH hS.not_le (W₀ := Tim79a.xOf V H) ψ hl le_rfl
    (Tim79a.H_le_normalizer_xOf V H) (hw.orth_subRepW hW)
  rw [hcard, hw.card_V, ← pow_mul, mul_comm]

theorem card_Pc_inf_kOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card V ^ 2 = Nat.card ↥(Pc M V) := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hcard := h.card_imgK_eq_two_pow hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ hl
  have hsplit := RootHyp.card_imgK_mul_card_inf (V := V) (H := H) (X := Pc M V) hS.Pc_le
  rw [hcard] at hsplit
  have hV : Nat.card V ^ 2 = 2 ^ (2 * l) := by
    rw [hw.card_V, ← pow_mul]
    congr 1
    omega
  rw [hV, mul_comm]
  exact hsplit

theorem inf_Pc_xOf_eq_commutator (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    Pc M V ⊓ Tim79a.xOf V H = ⁅Tim79a.xOf V H, Pc M V⁆ := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hW := hS.isElemAbelian h
  letI := moduleOfElemAbelian hW
  exact h.inf_Pc_W0_eq_commutator_of_isOrthModule (hW := hW) hS.Pc_le hS.le_pCore
    hS.hH hS.not_le (W₀ := Tim79a.xOf V H) ψ hl le_rfl
    (Tim79a.H_le_normalizer_xOf V H) (hw.orth_subRepW hW)

theorem pCore_eq_and (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    inSubgroup (pCore 2) M = Pc M V ∧
      inSubgroup Subgroup.center (inSubgroup (pCore 2) M) = V ∧
      inSubgroup frattini (inSubgroup (pCore 2) M) = V ∧
      inSubgroup commutator (inSubgroup (pCore 2) M) = V := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  letI := moduleOfElemAbelian hW
  exact h.pCore_eq_Pc_and_of_isOrthModule hS.mem hS.le_pCore hS.hH hW ψ hl (hw.orth' hW)

theorem commutator_Pc (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    ⁅Pc M V, Pc M V⁆ = V := by
  have hC := (hS.pCore_eq_and h).2.2.2
  have hQ := (hS.pCore_eq_and h).1
  change (_root_.commutator (inSubgroup (pCore 2) M)).map
    (inSubgroup (pCore 2) M).subtype = V at hC
  rw [Subgroup.map_subtype_commutator] at hC
  rwa [hQ] at hC

theorem le_Pc_of_commutator_le (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {X : Subgroup G} (hXM : X ≤ M) (hXV : X ≤ Subgroup.centralizer (V : Set G))
    (hXP : ⁅Pc M V, X⁆ ≤ V) : X ≤ Pc M V := by
  have hle := h.toHyp.le_pCore_of_commutator_le hXM hXV hXP
  rwa [(hS.pCore_eq_and h).1] at hle

theorem exists_mem_conj_of_mem_classD (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {d : G}
    (hdW : d ∈ Tim79a.xOf V H) (hdD : d ∈ Tim78.classD V) :
    ∃ y ∈ H, d ∈ conjSubgroup y V := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  letI := moduleOfElemAbelian hW
  exact ((h.mem_conjSubgroup_iff_of_isOrthModule hS.Pc_le hS.le_pCore hS.hH hS.not_le
    hW ψ hl (hw.orth' hW) hdW).mp hdD).2

end Sec45Shape

end CFSG.RankThree.GF2n.Tim81
