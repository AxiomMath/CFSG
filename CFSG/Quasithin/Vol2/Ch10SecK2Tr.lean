module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tl
public import CFSG.Quasithin.Vol2.Ch10SecK2Tm
public import CFSG.Quasithin.Vol2.Ch11SecCB51Cases

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA
open scoped IsMulCommutative

section Psi

variable {Γ : Type} [Group Γ] {J W : Subgroup Γ} (hJW : J ≤ Subgroup.normalizer (W : Set Γ))
  (hO : pCoreOf 2 J ≤ Subgroup.centralizer (W : Set Γ))

@[expose] noncomputable def psiW : ↥J ⧸ CFSG.pCore 2 ↥J →* ↥(autOn J W) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥J) (InternalSec.autOnHom hJW) fun j hj =>
    (InternalSec.mem_ker_autOnHom hJW j).2 (hO ((C1Pack.coe_mem_pCoreOf_iff J j).mpr hj))

theorem psiW_surjective : Function.Surjective (psiW hJW hO) := by
  intro x
  obtain ⟨j, rfl⟩ := InternalSec.autOnHom_surjective hJW x
  exact ⟨QuotientGroup.mk j, rfl⟩

theorem map_psiW {A : Subgroup Γ} (hAJ : A ≤ J) :
    (((A.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).map (psiW hJW hO)).map
      (autOn J W).subtype = autOn A W := by
  ext φ
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
    exact Setup.mem_autOn_iff.mpr ⟨⟨j, hJW j.2⟩, hj, rfl⟩
  · intro h
    obtain ⟨g, hgA, rfl⟩ := Setup.mem_autOn_iff.mp h
    exact ⟨_, ⟨_, ⟨⟨g, hAJ hgA⟩, hgA, rfl⟩, rfl⟩, rfl⟩

theorem ker_psiW_le_center (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hJ : ¬ J ≤ Subgroup.centralizer (W : Set Γ)) :
    (psiW hJW hO).ker ≤ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (psiW hJW hO).normal_ker with h | h
  · refine (hJ fun j hj => ?_).elim
    have : (QuotientGroup.mk ⟨j, hj⟩ : ↥J ⧸ CFSG.pCore 2 ↥J) ∈ (psiW hJW hO).ker := by
      rw [h]
      trivial
    exact (InternalSec.mem_ker_autOnHom hJW ⟨j, hj⟩).1 this
  · exact h

end Psi

section Valid

variable {Γ : Type} [Group Γ] {W : Subgroup Γ}

theorem not_isPGroup_of_perfect {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : ⁅K, K⁆ = K) (hne : K ≠ ⊥) : ¬ IsPGroup 2 ↥K := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  have : Group.IsNilpotent ↥K := h2.isNilpotent
  have hs : Group.IsSolvable ↥K := inferInstance
  exact Group.IsPerfect.not_isSolvable _ hs

theorem pCore_autOn_fix {L : Subgroup Γ} (hLW : L ≤ Subgroup.normalizer (W : Set Γ))
    {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hnot : ¬ IsPGroup 2 ↥(autOn L W)) {X : Subgroup Γ}
    (hOX : pCoreOf 2 L ≤ Subgroup.centralizer (X : Set Γ)) :
    ∀ x : ↥(autOn L W), x ∈ CFSG.pCore 2 ↥(autOn L W) →
      ∀ m ∈ X.subgroupOf W, (x : MulAut ↥W) m = m := by
  intro x hx m hm
  rw [(pCore_eq_map_of_levi (InternalSec.autOnHom_surjective hLW) h4 e hnot).2] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  have hlc : (l : Γ) ∈ Subgroup.centralizer (X : Set Γ) :=
    hOX ((C1Pack.coe_mem_pCoreOf_iff L l).mpr hl)
  apply Subtype.ext
  rw [Ch11.SecC.B51.coe_autOnHom_apply]
  have := Subgroup.mem_centralizer_iff.mp hlc (m : Γ) hm
  rw [← this, mul_inv_cancel_right]

variable [IsMulCommutative ↥W]

theorem validM_of {J A L X : Subgroup Γ} (hJW : J ≤ Subgroup.normalizer (W : Set Γ))
    (hLJ : L ≤ J) (hXW : X ≤ W) (hAX : A ≤ Subgroup.normalizer (X : Set Γ))
    (hLX : L ≤ Subgroup.normalizer (X : Set Γ)) (hcomm : ⁅X, L⁆ = X)
    (hO : ∀ x : ↥(autOn L W), x ∈ CFSG.pCore 2 ↥(autOn L W) →
      ∀ m ∈ X.subgroupOf W, (x : MulAut ↥W) m = m)
    {q : ℕ} (hcard : (Subgroup.centralizer (L : Set Γ) ⊓ X).relIndex X ≤ q ^ 2) :
    ValidM (autOn A W) (autOn L W) q (X.subgroupOf W) := by
  have hLW : L ≤ Subgroup.normalizer (W : Set Γ) := hLJ.trans hJW
  have hinv : ∀ {B : Subgroup Γ}, B ≤ Subgroup.normalizer (X : Set Γ) →
      ∀ s ∈ autOn B W, ∀ x ∈ X.subgroupOf W, s x ∈ X.subgroupOf W := by
    intro B hBX s hs x hx
    obtain ⟨g, hgB, rfl⟩ := Setup.mem_autOn_iff.mp hs
    rw [Subgroup.mem_subgroupOf, Setup.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hBX hgB) _).mp hx
  refine ⟨hinv hAX, hinv hLX, ?_, hO, ?_⟩
  ·
    intro w hw
    have hle : ⁅X, L⁆ ≤ (commS (autOn L W) (X.subgroupOf W)).map W.subtype := by
      rw [Subgroup.commutator_le]
      intro a ha l hl
      have haW : a ∈ W := hXW ha
      have hai : (⟨a, haW⟩ : ↥W)⁻¹ ∈ X.subgroupOf W := X.inv_mem ha
      refine ⟨conjAct W ⟨l, hLW hl⟩ (⟨a, haW⟩ : ↥W)⁻¹ * ((⟨a, haW⟩ : ↥W)⁻¹)⁻¹,
        Subgroup.subset_closure ⟨_, InternalSec.conjAct_mem_autOn hLW hl, _, hai, rfl⟩, ?_⟩
      have hc : (conjAct W ⟨l, hLW hl⟩ (⟨a, haW⟩ : ↥W)⁻¹ * ((⟨a, haW⟩ : ↥W)⁻¹)⁻¹ : ↥W) =
          (⟨a, haW⟩ : ↥W) * conjAct W ⟨l, hLW hl⟩ (⟨a, haW⟩ : ↥W)⁻¹ := by
        rw [inv_inv, mul_comm]
      rw [Subgroup.coe_subtype, hc, Subgroup.coe_mul, Setup.coe_conjAct_apply,
        commutatorElement_def]
      simp [mul_assoc]
    have hw' : (w : Γ) ∈ (commS (autOn L W) (X.subgroupOf W)).map W.subtype :=
      hle (by rw [hcomm]; exact hw)
    obtain ⟨y, hy, hyw⟩ := hw'
    rwa [show y = w from Subtype.ext hyw] at hy
  · rw [Ch11.SecC.B51.fixV_autOn hLW, Ch11.SecC.B51.inf_subgroupOf_eq,
      Subgroup.relIndex_subgroupOf hXW]
    exact hcard

end Valid

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
