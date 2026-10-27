module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinB
public import CFSG.Quasithin.Vol2.Ch12Sec7FinE
public import CFSG.RankThree.PartOne.S12.TerminalWeylPerm
public import CFSG.Quasithin.EmptyFaithful.S153WJFin
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.F1Models
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits

namespace S127

open Equiv

theorem exists_embed_s5 {Y : Type} [Group Y] [Finite Y]
    (hpsl : IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup Y)))
    (hC : Subgroup.centralizer (oTwoUpper (⊤ : Subgroup Y) : Set Y) = ⊥) :
    ∃ π : Y →* Perm (Fin 5), Function.Injective π ∧
      (oTwoUpper (⊤ : Subgroup Y)).map π = alternatingGroup (Fin 5) := by
  obtain ⟨e⟩ := Vol2.Ch10.SecB.C11AmS.nonempty_equiv_aFive hpsl
  have hn := oTwoUpper_top_normal (Y := Y)
  obtain ⟨π, hπ1, hπ2⟩ := CFSG.RankThree.PartOne.TerminalPerm.exists_pi_of_equiv
    (Γ := (⊤ : Subgroup Y)) e le_top (fun g _ y hy => hn.conj_mem y hy g)
  refine ⟨π.comp (Subgroup.topEquiv (G := Y)).symm.toMonoidHom, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hc := hπ2 _ hg
    have hgC : g ∈ Subgroup.centralizer (oTwoUpper (⊤ : Subgroup Y) : Set Y) :=
      Subgroup.mem_centralizer_iff.2 fun y hy => (hc y hy).symm
    rw [hC] at hgC
    exact hgC
  · ext σ
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := hπ1 y hy
      show π ⟨y, Subgroup.mem_top y⟩ ∈ alternatingGroup (Fin 5)
      rw [h]
      exact (e ⟨y, hy⟩).2
    · intro hσ
      refine ⟨(e.symm ⟨σ, hσ⟩ : Y), (e.symm ⟨σ, hσ⟩).2, ?_⟩
      have h := hπ1 _ (e.symm ⟨σ, hσ⟩).2
      show π ⟨_, Subgroup.mem_top _⟩ = σ
      rw [h]
      simp

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isElemAbelian_map_two {Y : Type*} [Group Y] (f : X →* Y) {A : Subgroup X}
    (hA : IsElemAbelian 2 A) : IsElemAbelian 2 (A.map f) := CFSG.Open.IsElemAbelian.map hA _

theorem card_map_le_four
    (hpsl : IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X))))
    {A : Subgroup X} (hA : IsElemAbelian 2 A) :
    Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 X))) ≤ 4 := by
  have hO : CFSG.Open.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
    exact pCore_two_quotient_pCore_two X
  have hC := centralizer_oTwoUpper_eq_bot hO (isSimpleGroup_of_isPSL hpsl)
    (nonabelian_of_isPSL hpsl)
  obtain ⟨π, hπi, -⟩ := exists_embed_s5 hpsl hC
  have h := W153.card_le_four_of_isElemAbelian_perm5 _
    (isElemAbelian_map_two π (isElemAbelian_map_two (QuotientGroup.mk' (CFSG.pCore 2 X)) hA))
  rwa [Subgroup.card_map_of_injective hπi] at h

theorem exists_le_map_sup_conj
    (hpsl : IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X))))
    {A : Subgroup X} (hA : IsElemAbelian 2 A)
    (hA4 : Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 X))) = 4) :
    ∃ k : X, oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) ≤
      (A ⊔ A.map (MulAut.conj k).toMonoidHom).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
  classical
  set φ := QuotientGroup.mk' (CFSG.pCore 2 X) with hφ
  set K := oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) with hK
  have hO : CFSG.Open.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
    exact pCore_two_quotient_pCore_two X
  have hs : IsSimpleGroup ↥K := isSimpleGroup_of_isPSL hpsl
  have hnc := nonabelian_of_isPSL hpsl
  have hC := centralizer_oTwoUpper_eq_bot hO hs hnc
  obtain ⟨π, hπi, hπK⟩ := exists_embed_s5 hpsl hC
  set E := (A.map φ).map π with hE
  have hE4 : Nat.card E = 4 := by
    rw [hE, Subgroup.card_map_of_injective hπi, hA4]
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← pow_two, hA.2 a ha, map_one, map_one]
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have h := congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)
    simp only [Subgroup.coe_mul] at h
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h]
  have hex : ∀ s : Finset (Perm (Fin 5)), s.card < 4 → ∃ x ∈ E, x ∉ s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set (Perm (Fin 5))) ⊆ (s : Set (Perm (Fin 5))) := fun x hx => hcon x hx
    have h1 : Nat.card E ≤ Nat.card (s : Set (Perm (Fin 5))) := Nat.card_mono s.finite_toSet hsub
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hE4] at h1
    omega
  obtain ⟨x, hx, hx1⟩ := hex {1} (by rw [Finset.card_singleton]; omega)
  obtain ⟨y, hy, hy1⟩ := hex {1, x}
    (by have := Finset.card_le_two (a := (1 : Perm (Fin 5))) (b := x); omega)
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hx1 hy1
  obtain ⟨k, hk, hle⟩ := exists_alt_five_le_sup hx hy
    ⟨hEsq x hx, hx1, hEsq y hy, hy1.1, Ne.symm hy1.2, hEc x hx y hy⟩
  have hkA : k ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hk
  rw [← hπK] at hkA
  obtain ⟨kb, -, rfl⟩ := hkA
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) kb
  refine ⟨k₀, ?_⟩
  rw [← Subgroup.map_le_map_iff_of_injective hπi, hπK]
  refine hle.trans ?_
  rw [Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le_sup le_rfl ?_
  rintro _ ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
  refine ⟨φ (k₀ * a * k₀⁻¹), ⟨k₀ * a * k₀⁻¹, ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  rfl

end S127

end CFSG.Quasithin.H13
