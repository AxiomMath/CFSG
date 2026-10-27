module

public import CFSG.Quasithin.Background.RonanH143Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code

theorem h143_conjHom_injective (c : P24) :
    Function.Injective (MulAut.conj c).toMonoidHom :=
  (MulAut.conj c).injective

theorem mem_conjSubg_iff {c x : P24} {A : Subgroup P24} :
    x ∈ conjSubg c A ↔ c⁻¹ * x * c ∈ A := by
  unfold conjSubg
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conjSubg_le_conjSubg_iff {c : P24} {A B : Subgroup P24} :
    conjSubg c A ≤ conjSubg c B ↔ A ≤ B := by
  unfold conjSubg
  exact Subgroup.map_le_map_iff_of_injective (h143_conjHom_injective c)

theorem conjSubg_inj {c : P24} {A B : Subgroup P24} :
    conjSubg c A = conjSubg c B ↔ A = B := by
  unfold conjSubg
  exact (Subgroup.map_injective (h143_conjHom_injective c)).eq_iff

theorem conjSubg_inf (c : P24) (A B : Subgroup P24) :
    conjSubg c (A ⊓ B) = conjSubg c A ⊓ conjSubg c B := by
  unfold conjSubg
  exact Subgroup.map_inf A B (MulAut.conj c).toMonoidHom (h143_conjHom_injective c)

theorem conjSubg_conjSubg_inv (c : P24) (A : Subgroup P24) :
    conjSubg c⁻¹ (conjSubg c A) = A := by
  ext x
  rw [mem_conjSubg_iff, mem_conjSubg_iff]
  have e : c⁻¹ * ((c⁻¹)⁻¹ * x * c⁻¹) * c = x := by group
  rw [e]

theorem conjSubg_inv_conjSubg (c : P24) (A : Subgroup P24) :
    conjSubg c (conjSubg c⁻¹ A) = A := by
  ext x
  rw [mem_conjSubg_iff, mem_conjSubg_iff]
  have e : (c⁻¹)⁻¹ * (c⁻¹ * x * c) * c⁻¹ = x := by group
  rw [e]

theorem conjSubg_bot (c : P24) : conjSubg c (⊥ : Subgroup P24) = ⊥ := by
  unfold conjSubg
  exact Subgroup.map_bot (MulAut.conj c).toMonoidHom

theorem conjSubg_sup (c : P24) (A B : Subgroup P24) :
    conjSubg c (A ⊔ B) = conjSubg c A ⊔ conjSubg c B := by
  unfold conjSubg
  exact Subgroup.map_sup A B (MulAut.conj c).toMonoidHom

theorem card_conjSubg (c : P24) (A : Subgroup P24) :
    Nat.card ↥(conjSubg c A) = Nat.card ↥A := by
  unfold conjSubg
  exact Subgroup.card_map_of_injective (h143_conjHom_injective c)

theorem h143_stabilizer_smul {α : Type*} [MulAction P24 α] (c : P24) (Y : α) :
    MulAction.stabilizer P24 (c • Y) = conjSubg c (MulAction.stabilizer P24 Y) :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj c Y

theorem MY_conjSubg {α : Type*} [MulAction P24 α] (c : P24) (Γ : Subgroup P24) (Y : α) :
    MY (conjSubg c Γ) (c • Y) = conjSubg c (MY Γ Y) := by
  unfold MY
  rw [conjSubg_inf, h143_stabilizer_smul]

theorem pCoreOf_conjSubg (c : P24) (H : Subgroup P24) :
    pCoreOf 2 (conjSubg c H) = conjSubg c (pCoreOf 2 H) := by
  have hpc : CFSG.pCore 2 ↥(H.map (MulAut.conj c).toMonoidHom) =
      (CFSG.pCore 2 ↥H).map (H.equivMapOfInjective (MulAut.conj c).toMonoidHom
        (h143_conjHom_injective c)).toMonoidHom :=
    (CFSG.pCore_map_iso 2 (H.equivMapOfInjective (MulAut.conj c).toMonoidHom
        (h143_conjHom_injective c))).symm
  have hcomp : (H.map (MulAut.conj c).toMonoidHom).subtype.comp
      (H.equivMapOfInjective (MulAut.conj c).toMonoidHom (h143_conjHom_injective c)).toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp H.subtype := by
    ext x
    rfl
  unfold pCoreOf conjSubg
  rw [hpc, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem KY_conjSubg {α : Type*} [MulAction P24 α] (c : P24) (Γ : Subgroup P24) (Y : α) :
    KY (conjSubg c Γ) (c • Y) = conjSubg c (KY Γ Y) := by
  unfold KY
  rw [MY_conjSubg, pCoreOf_conjSubg]

theorem perfectCore_conjSubg (c : P24) (H : Subgroup P24) :
    perfectCore (conjSubg c H) = conjSubg c (perfectCore H) :=
  (CFSG.Quasithin.map_perfectCore (MulAut.conj c).toMonoidHom H).symm

theorem h143_isElemAbelian_conjSubg {p : ℕ} (c : P24) {A : Subgroup P24}
    (hA : IsElemAbelian p A) : IsElemAbelian p (conjSubg c A) := by
  obtain ⟨hc, hx⟩ := hA
  unfold IsElemAbelian conjSubg
  refine ⟨?_, ?_⟩
  · haveI := hc
    exact Subgroup.map_isMulCommutative _ _
  · intro x hxmem
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxmem
    rw [← map_pow, hx y hy, map_one]

theorem h143_isElemAbelian_conjSubg_iff {p : ℕ} (c : P24) (A : Subgroup P24) :
    IsElemAbelian p (conjSubg c A) ↔ IsElemAbelian p A := by
  refine ⟨fun h => ?_, h143_isElemAbelian_conjSubg c⟩
  have h' := h143_isElemAbelian_conjSubg c⁻¹ h
  rwa [conjSubg_conjSubg_inv] at h'

theorem IsE2k_conjSubg_iff (c : P24) (k : ℕ) (A : Subgroup P24) :
    IsE2k k (conjSubg c A) ↔ IsE2k k A := by
  unfold IsE2k
  rw [h143_isElemAbelian_conjSubg_iff, card_conjSubg]

theorem h143_conjSubg_AutPerm {c : P24} (hc : c ∈ AutPerm) : conjSubg c AutPerm = AutPerm := by
  ext x
  rw [mem_conjSubg_iff]
  constructor
  · intro h
    have h2 := mul_mem (mul_mem hc h) (inv_mem hc)
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [e] at h2
  · intro h
    exact mul_mem (mul_mem (inv_mem hc) h) hc

theorem M22g_conj {c : P24} (hc : c ∈ AutPerm) (a b : Fin 24) :
    conjSubg c (M22g a b) = M22g (c a) (c b) := by
  have ha : conjSubg c (MulAction.stabilizer P24 a) = MulAction.stabilizer P24 (c a) :=
    (h143_stabilizer_smul c a).symm
  have hb : conjSubg c (MulAction.stabilizer P24 b) = MulAction.stabilizer P24 (c b) :=
    (h143_stabilizer_smul c b).symm
  unfold M22g
  rw [conjSubg_inf, conjSubg_inf, h143_conjSubg_AutPerm hc, ha, hb]

theorem h143_smul_pair (c : P24) (a b : Fin 24) :
    c • ({a, b} : Finset (Fin 24)) = {c a, c b} := by
  simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, Equiv.Perm.smul_def]

theorem M2ab_conj {c : P24} (hc : c ∈ AutPerm) (a b : Fin 24) :
    conjSubg c (M2ab a b) = M2ab (c a) (c b) := by
  have h : conjSubg c (MulAction.stabilizer P24 ({a, b} : Finset (Fin 24))) =
      MulAction.stabilizer P24 ({c a, c b} : Finset (Fin 24)) := by
    rw [← h143_stabilizer_smul, h143_smul_pair]
  unfold M2ab
  rw [conjSubg_inf, h143_conjSubg_AutPerm hc, h]

theorem smul_erase_finset (c : P24) (O : Finset (Fin 24)) (a : Fin 24) :
    c • O.erase a = (c • O).erase (c a) := by
  ext x
  simp only [Finset.mem_smul_finset, Finset.mem_erase]
  constructor
  · rintro ⟨y, ⟨hya, hyO⟩, rfl⟩
    exact ⟨fun h => hya (Equiv.injective c h), y, hyO, rfl⟩
  · rintro ⟨hx, y, hyO, rfl⟩
    exact ⟨y, ⟨fun h => hx (congrArg (fun z : Fin 24 => c • z) h), hyO⟩, rfl⟩

theorem smul_erase_finset_finset (c : P24) (S : Finset (Finset (Fin 24))) (B : Finset (Fin 24)) :
    c • S.erase B = (c • S).erase (c • B) := by
  ext X
  simp only [Finset.mem_smul_finset, Finset.mem_erase]
  constructor
  · rintro ⟨Y, ⟨hYB, hYS⟩, rfl⟩
    exact ⟨fun h => hYB ((smul_left_cancel_iff c).mp h), Y, hYS, rfl⟩
  · rintro ⟨hX, Y, hYS, rfl⟩
    exact ⟨Y, ⟨fun h => hX (congrArg (fun Z : Finset (Fin 24) => c • Z) h), hYS⟩, rfl⟩

theorem M22g_comm (a b : Fin 24) : M22g a b = M22g b a := by
  unfold M22g
  exact inf_right_comm _ _ _

end CFSG.Quasithin.RonanH143
