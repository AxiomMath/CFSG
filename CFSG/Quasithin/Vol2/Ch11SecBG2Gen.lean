module

public import CFSG.Quasithin.Vol2.Ch11SecBHBComm
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem mem_normalizer_iSup₂ {P : G → Prop} {S : G → Subgroup G} {o : G}
    (h : ∀ x, P x → o ∈ Subgroup.normalizer (S x : Set G)) :
    o ∈ Subgroup.normalizer ((⨆ (x : G) (_ : P x), S x : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_conj_eq ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun x => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hx => map_conj_eq_self_of_mem_normalizer (h x hx)

omit [Finite G] in
theorem mem_normalizer_of_mem_centralizer {W V : Subgroup G} (hWV : W ≤ V) {o : G}
    (ho : o ∈ Subgroup.centralizer (V : Set G)) : o ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have h1 := Subgroup.mem_centralizer_iff.mp ho w (hWV hw)
    rw [← h1, mul_inv_cancel_right]
    exact hw
  · intro hw
    have h1 := Subgroup.mem_centralizer_iff.mp ho _ (hWV hw)
    have h2 : w = o * w * o⁻¹ := by
      have h3 : o * w = o * (o * w * o⁻¹) := by simpa [mul_assoc] using h1
      exact mul_left_cancel h3
    rw [h2]
    exact hw

theorem eq_of_le_sup_centralizer (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {P : G → Prop}
    {W : G → Subgroup G} (hW : ∀ x, P x → W x ≤ fsuV T I)
    (hL : L ≤ (⨆ (x : G) (_ : P x), LOf L (W x)) ⊔
      (L ⊓ Subgroup.centralizer (fsuV T I : Set G))) :
    (⨆ (x : G) (_ : P x), LOf L (W x)) = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := ⨆ (x : G) (_ : P x), LOf L (W x) with hYdef
  have hYL : Y ≤ L := iSup₂_le fun x _ => (perfectCore_le _).trans inf_le_left
  have hCN : L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
    intro o ho
    refine mem_normalizer_iSup₂ fun x hx => ?_
    have hoW : o ∈ Subgroup.normalizer (W x : Set G) :=
      mem_normalizer_of_mem_centralizer (hW x hx) ho.2
    exact normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer ⟨ho.1, hoW⟩)
  have hLN : L ≤ Subgroup.normalizer (Y : Set G) := hL.trans (sup_le Subgroup.le_normalizer hCN)
  have hO2 : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    rw [centralizer_eq_pCoreOf h1102 hyp]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hsup : (L ⊓ Subgroup.centralizer (fsuV T I : Set G)) ⊔ Y = L :=
    le_antisymm (sup_le inf_le_left hYL) (by rw [sup_comm]; exact hL)
  have h2 := B6.isTwoQuotient_of_sup_eq hO2 hLN hsup
  exact hyp.fsu.faithful.2.1 Y hYL ((Subgroup.normal_subgroupOf_iff_le_normalizer hYL).mpr hLN) h2

end CFSG.Quasithin.Vol2.Ch11.SecB
