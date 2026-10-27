module

public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAVi
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_sup {A B : Subgroup G} {t : G} (hA : t ∈ Subgroup.normalizer (A : Set G))
    (hB : t ∈ Subgroup.normalizer (B : Set G)) :
    t ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_le ?_
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]

theorem mem_normalizer_inf {A B : Subgroup G} {t : G} (hA : t ∈ Subgroup.normalizer (A : Set G))
    (hB : t ∈ Subgroup.normalizer (B : Set G)) :
    t ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_le ?_
  intro x hx
  rw [mem_map_conj] at hx
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp hA _).mp h1
    simpa [mul_assoc] using this
  · have := (Subgroup.mem_normalizer_iff.mp hB _).mp h2
    simpa [mul_assoc] using this

theorem exists_hall_of_normal_sylow' {K P : Subgroup G} (hP : QuasithinUnique.IsSylowTwoOf P K)
    (hN : K ≤ Subgroup.normalizer (P : Set G)) :
    ∃ D : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf D K := by
  have : (P.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hP.1).mpr hN
  have hcardP : Nat.card (P.subgroupOf K) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv
  obtain ⟨e, he⟩ := hP.2.1.exists_card_eq
  have hidx : ¬ 2 ∣ (P.subgroupOf K).index := hP.2.2
  have hcop : Nat.Coprime (Nat.card (P.subgroupOf K)) (P.subgroupOf K).index := by
    rw [hcardP, he]
    exact Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
  obtain ⟨D', hD'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hmul : Nat.card (P.subgroupOf K) * Nat.card D' = Nat.card K := hD'.card_mul_card
  have hmul' : (P.subgroupOf K).index * Nat.card (P.subgroupOf K) = Nat.card K :=
    Subgroup.index_mul_card _
  have hDcard : Nat.card D' = (P.subgroupOf K).index := by
    have hpos : 0 < Nat.card (P.subgroupOf K) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hmul, ← hmul', mul_comm]
  have hDindex : D'.index = 2 ^ e := by
    have h1 : D'.index * Nat.card D' = Nat.card K := Subgroup.index_mul_card _
    have hpos : 0 < Nat.card D' := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← hmul, hcardP, he]
  refine ⟨D'.map K.subtype, Subgroup.map_subtype_le D', ?_, ⟨e, ?_⟩⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hDcard]
    exact Nat.odd_iff.mpr (by omega)
  · change ((D'.map K.subtype).comap K.subtype).index = 2 ^ e
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective, hDindex]

variable {T L I : Subgroup G} {n : ℕ}

theorem exists_isCartanX (h : Hyp11 G T L I n) : ∃ X : Subgroup G, IsCartanX T L X := by
  have hS := isSylowTwoOf_inf_L h
  have hTnL : T ⊓ L ≤ Subgroup.normalizer ((TL T L : Subgroup G) : Set G) := by
    intro t ht
    have htT := (Subgroup.mem_inf.mp ht).1
    have htL : t ∈ Subgroup.normalizer (L : Set G) := h.normal htT
    have htO : t ∈ Subgroup.normalizer ((pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_right htT)
    exact mem_normalizer_inf (Subgroup.le_normalizer htT) (mem_normalizer_sup htL htO)
  have hle : T ⊓ L ≤ L ⊓ Subgroup.normalizer ((TL T L : Subgroup G) : Set G) :=
    le_inf inf_le_right hTnL
  have hS' := A4.isSylowTwoOf_mono hS hle inf_le_left
  have hN : L ⊓ Subgroup.normalizer ((TL T L : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
    have e : TL T L ⊓ L = T ⊓ L := by
      rw [TL, inf_assoc, inf_eq_right.mpr (le_sup_left : L ≤ L ⊔ pCoreOf 2 (L ⊔ T))]
    rw [← e]
    exact mem_normalizer_inf hxN (Subgroup.le_normalizer hxL)
  exact exists_hall_of_normal_sylow' hS' hN

theorem commutator_fsuV_eq (h : Hyp11 G T L I n) : ⁅fsuV T I, L⁆ = fsuV T I := by
  have hL := L_le_normalizer_fsuV h
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    have h1 : l * v⁻¹ * l⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (hL hl) v⁻¹).mp ((fsuV T I).inv_mem hv)
    rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
    exact (fsuV T I).mul_mem hv h1
  · have hI : ⁅I, L⁆ = I := by
      have := h.fsu.irrPlus.2.2.2.1
      rwa [conjClosure_eq_self h] at this
    refine conjClosure_le fun t ht z hz => ?_
    have htL : t ∈ Subgroup.normalizer (L : Set G) := h.normal ht
    have h1 : (⁅I, L⁆).map (MulAut.conj t).toMonoidHom ≤ ⁅fsuV T I, L⁆ := by
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer htL]
      refine Subgroup.commutator_mono (Subgroup.map_le_iff_le_comap.mpr fun i hi => ?_) le_rfl
      show t * i * t⁻¹ ∈ fsuV T I
      exact mem_conjClosure ht hi
    rw [hI] at h1
    exact h1 ⟨z, hz, by simp⟩

theorem commV_autOn_eq_top (h : Hyp11 G T L I n) [IsMulCommutative ↥(fsuV T I)] :
    commV (autOn L (fsuV T I)) = ⊤ := by
  have hL := L_le_normalizer_fsuV h
  have key : ⁅fsuV T I, L⁆ ≤ (commV (autOn L (fsuV T I))).map (fsuV T I).subtype := by
    rw [Subgroup.commutator_le]
    intro a ha l hl
    set v : ↥(fsuV T I) := ⟨a⁻¹, (fsuV T I).inv_mem ha⟩
    set x := conjV (fsuV T I) l (hL hl)
    refine ⟨x v * v⁻¹, Subgroup.subset_closure ⟨x, conjV_mem_autOn hl _, v, rfl⟩, ?_⟩
    have hcomm : ((x v : ↥(fsuV T I)) : G) * a = a * ((x v : ↥(fsuV T I)) : G) := by
      have := mul_comm (x v) ⟨a, ha⟩
      exact congrArg Subtype.val this
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, v, inv_inv]
    rw [hcomm, conjV_apply_coe, commutatorElement_def]
    have hv : ((v : ↥(fsuV T I)) : G) = a⁻¹ := rfl
    rw [hv]
    group
  rw [eq_top_iff]
  intro v _
  have hv : (v : G) ∈ ⁅fsuV T I, L⁆ := by
    rw [commutator_fsuV_eq h]
    exact v.2
  obtain ⟨w, hw, hwv⟩ := key hv
  rwa [show v = w from Subtype.ext hwv.symm]

end CFSG.Quasithin.Vol2.Ch11.SecA
