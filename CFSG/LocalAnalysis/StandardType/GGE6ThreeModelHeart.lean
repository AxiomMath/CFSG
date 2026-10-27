module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelClosure
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

section Heart

variable {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

private def hypE6Fin : AddSubgroup (Fin 6 → ZMod 3) := NoOffRest.hypE6

private noncomputable def adActFin (u : WeylGroup .E6) (x : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  adAct .E6 3 u x

private theorem adAct_sub_mem_hypE6Fin (u : WeylGroup .E6) (x : Fin 6 → ZMod 3) :
    adActFin u x - x ∈ hypE6Fin :=
  adAct_sub_mem_hypE6 u x

private def hypE6Equiv :
    hypE6Fin.toSubgroup ≃ hypE6Fin where
  toFun x := ⟨Multiplicative.toAdd x.1,
    (Multiplicative.mem_toSubgroup hypE6Fin x.1).mp x.2⟩
  invFun v := ⟨Multiplicative.ofAdd v.1,
    (Multiplicative.mem_toSubgroup hypE6Fin (Multiplicative.ofAdd v.1)).mpr (by
      rw [toAdd_ofAdd]
      exact v.2)⟩
  left_inv x := Subtype.ext (ofAdd_toAdd x.1)
  right_inv v := Subtype.ext (toAdd_ofAdd v.1)

private theorem heartCardAux (h : GGE6ThreeData Z A Φ T w) :
    Nat.card (heartOf Φ) = 3 ^ 5 := by
  have hle : hypE6Fin.toSubgroup ≤ Φ.range := by
    intro y hy
    rw [Multiplicative.mem_toSubgroup] at hy
    obtain ⟨a, ha⟩ := h.exists_eq_of_mem_hypE6 (v := Multiplicative.toAdd y) hy
    exact ⟨a, by rw [ha]; rfl⟩
  change Nat.card (Subgroup.map A.subtype (Subgroup.comap Φ hypE6Fin.toSubgroup)) = 3 ^ 5
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  rw [← Subgroup.card_map_of_injective h.injective]
  rw [Subgroup.map_comap_eq_self hle]
  exact (Nat.card_congr hypE6Equiv).trans NoOffRest.card_hypE6

theorem GGE6ThreeData.heart_ne_bot (h : GGE6ThreeData Z A Φ T w) : heartOf Φ ≠ ⊥ := by
  intro hbot
  have hcard := heartCardAux h
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem GGE6ThreeData.card_heart (h : GGE6ThreeData Z A Φ T w) :
    Nat.card (heartOf Φ) = 3 ^ 5 :=
  heartCardAux h

theorem GGE6ThreeData.card_le_three_mul_card_heart (h : GGE6ThreeData Z A Φ T w) :
    Nat.card A ≤ 3 * Nat.card (heartOf Φ) := by
  rw [heartCardAux h]
  rcases h.card_cases with ⟨hA, _⟩ | ⟨hA, _⟩
  · rw [hA]; norm_num
  · rw [hA]; norm_num

theorem GGE6ThreeData.heart_conj_mem (h : GGE6ThreeData Z A Φ T w) {n : L'}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∀ x ∈ heartOf Φ, MulAut.conj n * x * (MulAut.conj n)⁻¹ ∈ heartOf Φ := by
  intro x hx
  rw [mem_heartOf_iff] at hx ⊢
  obtain ⟨hxA, hxhyp⟩ := hx
  have hconjA : MulAut.conj n * x * (MulAut.conj n)⁻¹ ∈ A :=
    (Subgroup.mem_set_normalizer_iff.mp hn x).mp hxA
  obtain ⟨u, hu⟩ := h.inner n hn
  refine ⟨hconjA, ?_⟩
  have hb := hu ⟨x, hxA⟩ ⟨MulAut.conj n * x * (MulAut.conj n)⁻¹, hconjA⟩ rfl
  rw [hb]
  exact NoOffRest.adAct_mem_hypE6 u hxhyp

theorem GGE6ThreeData.heart_le_of_invariant (h : GGE6ThreeData Z A Φ T w)
    {A' : Subgroup (MulAut L')} (hA' : A' ≤ A) (hne : A' ≠ ⊥)
    (hinv : ∀ i, ∀ a ∈ A', MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹ ∈ A') :
    heartOf Φ ≤ A' := by
  intro x hx
  rw [mem_heartOf_iff] at hx
  obtain ⟨hxA, hxhyp⟩ := hx
  have hSne : imageAdd Φ A' ≠ ⊥ := imageAdd_ne_bot h.injective hA' hne
  have hSinv : ∀ i, ∀ v ∈ imageAdd Φ A', adRefl .E6 3 i v ∈ imageAdd Φ A' :=
    fun i v hv => h.imageAdd_adRefl hinv i hv
  have hle : NoOffRest.hypE6 ≤ imageAdd Φ A' :=
    hypE6_le_of_invariant (imageAdd Φ A') hSinv hSne
  exact (mem_imageAdd_iff h.injective ⟨x, hxA⟩).mp (hle hxhyp)

theorem GGE6ThreeData.eq_one_of_forall_conj_eq (h : GGE6ThreeData Z A Φ T w) {a : MulAut L'}
    (ha : a ∈ A) (hfix : ∀ i, MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹ = a) : a = 1 := by
  have hv : ∀ i, adRefl .E6 3 i (Multiplicative.toAdd (Φ ⟨a, ha⟩)) =
      Multiplicative.toAdd (Φ ⟨a, ha⟩) := by
    intro i
    obtain ⟨b, hb, hbΦ⟩ := h.act i ⟨a, ha⟩
    have hba : b = (⟨a, ha⟩ : A) := Subtype.ext (hb.symm.trans (hfix i))
    rw [← hbΦ, hba]
  have hzero := eq_zero_of_forall_adRefl_eq hv
  have hΦ1 : Φ ⟨a, ha⟩ = 1 := hzero
  have hsub : (⟨a, ha⟩ : A) = 1 := h.injective (by rw [hΦ1, map_one])
  exact congrArg Subtype.val hsub

theorem GGE6ThreeData.comm_mem_heart (h : GGE6ThreeData Z A Φ T w) {n : L'}
    (hn : n ∈ Subgroup.closure (Set.range w)) {a : MulAut L'} (ha : a ∈ A) :
    MulAut.conj n * a * (MulAut.conj n)⁻¹ * a⁻¹ ∈ heartOf Φ := by
  obtain ⟨u, hu⟩ := h.closure_act hn
  obtain ⟨b, hb, hbΦ⟩ := hu ⟨a, ha⟩
  have hb' : (b : MulAut L') = MulAut.conj n * a * (MulAut.conj n)⁻¹ := by
    rw [hb]
  have hc : MulAut.conj n * a * (MulAut.conj n)⁻¹ * a⁻¹ ∈ A := by
    rw [← hb']
    exact A.mul_mem b.2 (A.inv_mem ha)
  rw [mem_heartOf_iff]
  refine ⟨hc, ?_⟩
  have heq : (⟨MulAut.conj n * a * (MulAut.conj n)⁻¹ * a⁻¹, hc⟩ : A) =
      b * (⟨a, ha⟩ : A)⁻¹ := by
    apply Subtype.ext
    change MulAut.conj n * a * (MulAut.conj n)⁻¹ * a⁻¹ = (b : MulAut L') * a⁻¹
    rw [hb']
  rw [heq, map_mul, toAdd_mul, map_inv, toAdd_inv, hbΦ]
  change adActFin u (Multiplicative.toAdd (Φ ⟨a, ha⟩)) +
    -Multiplicative.toAdd (Φ ⟨a, ha⟩) ∈ hypE6Fin
  convert adAct_sub_mem_hypE6Fin u (Multiplicative.toAdd (Φ ⟨a, ha⟩)) using 1
  rw [sub_eq_add_neg]
  rfl

end Heart

end CFSG.StandardType
