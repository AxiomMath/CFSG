module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGAt
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
import CFSG.CharacterTheory.PSL2Table.Partition
import CFSG.CharacterTheory.PSL2Table.Classes
import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.PSL2Table CFSG.GorensteinWalter Subgroup

theorem s1667_kgl2_centralizer_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nonempty (↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({e x} : Set H))) :=
  ⟨{ toFun := fun y => ⟨e y.1, Subgroup.mem_centralizer_singleton_iff.mpr (by
        simpa only [map_mul] using congrArg e
          (Subgroup.mem_centralizer_singleton_iff.mp y.2))⟩
     invFun := fun y => ⟨e.symm y.1, Subgroup.mem_centralizer_singleton_iff.mpr (by
        simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm
          (Subgroup.mem_centralizer_singleton_iff.mp y.2))⟩
     left_inv := fun y => by ext; simp
     right_inv := fun y => by ext; simp
     map_mul' := fun y z => by ext; simp }⟩

private theorem s1667_kgl2_centralizer_split {F : Type} [Field F] [Fintype F]
    {y : PSL2 F} (hyT : y ∈ splitTorus F) (hyord : orderOf y = 3) :
    centralizer ({y} : Set (PSL2 F)) = splitTorus F := by
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    omega
  apply le_antisymm
  · intro g hg
    have hgy : g * y * g⁻¹ = y := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [h]
        _ = y := by group
    have hmem : g * y * g⁻¹ ∈ splitTorus F := by rw [hgy]; exact hyT
    rcases (splitTorus_conj_mem_iff hyT hy1 g).mp hmem with h | h
    · exact h
    · exfalso
      obtain ⟨t, htmem, ht⟩ := h
      let t' : PSL2 F := mk t
      have ht'T : t' ∈ splitTorus F := ⟨t, htmem, rfl⟩
      have hg_eq : g = splitWeyl F * t' := by
        calc g = splitWeyl F * (splitWeyl F)⁻¹ * g := by group
          _ = splitWeyl F * ((splitWeyl F)⁻¹ * g) := by group
          _ = splitWeyl F * t' := by rw [show t' = (splitWeyl F)⁻¹ * g from ht]
      have hty : t' * y * t'⁻¹ = y := by
        rw [splitTorus_mul_comm ht'T hyT, mul_assoc, mul_inv_cancel, mul_one]
      have hinv : g * y * g⁻¹ = y⁻¹ := by
        rw [hg_eq]
        calc splitWeyl F * t' * y * (splitWeyl F * t')⁻¹
            = splitWeyl F * (t' * y * t'⁻¹) * (splitWeyl F)⁻¹ := by group
          _ = splitWeyl F * y * (splitWeyl F)⁻¹ := by rw [hty]
          _ = y⁻¹ := splitWeyl_conj hyT
      have hyy : y = y⁻¹ := hgy.symm.trans hinv
      have hy2 : y * y = 1 := (eq_inv_iff_mul_eq_one).mp hyy
      have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact splitTorus_mul_comm hg hyT

private theorem s1667_kgl2_centralizer_nonsplit {F : Type} [Field F] [Fintype F]
    (hF2 : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) {y : PSL2 F} (hyT : y ∈ nonsplitTorus ν)
    (hyord : orderOf y = 3) : centralizer ({y} : Set (PSL2 F)) = nonsplitTorus ν := by
  obtain ⟨w, -, -, hw_inv, hw_iff⟩ := exists_nonsplitWeyl hF2 hν
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    omega
  apply le_antisymm
  · intro g hg
    have hgy : g * y * g⁻¹ = y := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [h]
        _ = y := by group
    have hmem : g * y * g⁻¹ ∈ nonsplitTorus ν := by rw [hgy]; exact hyT
    rcases (hw_iff y hyT hy1 g).mp hmem with h | h
    · exact h
    · exfalso
      obtain ⟨t, htmem, ht⟩ := h
      let t' : PSL2 F := mk t
      have ht'T : t' ∈ nonsplitTorus ν := ⟨t, htmem, rfl⟩
      have hg_eq : g = w * t' := by
        calc g = w * w⁻¹ * g := by group
          _ = w * (w⁻¹ * g) := by group
          _ = w * t' := by rw [show t' = w⁻¹ * g from ht]
      have hty : t' * y * t'⁻¹ = y := by
        rw [nonsplitTorus_mul_comm ht'T hyT, mul_assoc, mul_inv_cancel, mul_one]
      have hinv : g * y * g⁻¹ = y⁻¹ := by
        rw [hg_eq]
        calc w * t' * y * (w * t')⁻¹ = w * (t' * y * t'⁻¹) * w⁻¹ := by group
          _ = w * y * w⁻¹ := by rw [hty]
          _ = y⁻¹ := hw_inv y hyT
      have hyy : y = y⁻¹ := hgy.symm.trans hinv
      have hy2 : y * y = 1 := (eq_inv_iff_mul_eq_one).mp hyy
      have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact nonsplitTorus_mul_comm hg hyT

theorem s1667_kgl2_centralizer_psl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) (h3 : ¬ 3 ∣ Nat.card F) {x : PSL2 F} (hx : orderOf x = 3) :
    IsCyclic ↥(centralizer ({x} : Set (PSL2 F))) ∧
      (2 * Nat.card ↥(centralizer ({x} : Set (PSL2 F))) = Nat.card F - 1 ∨
        2 * Nat.card ↥(centralizer ({x} : Set (PSL2 F))) = Nat.card F + 1) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := by
    intro h
    have h' := (FiniteField.even_card_iff_char_two (F := F)).mp h
    rw [← Nat.card_eq_fintype_card] at h'
    have h'' := Nat.odd_iff.mp hodd
    omega
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have h5 : 5 ≤ Nat.card F := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hq5 : 5 ≤ Fintype.card F := by
    simpa [Nat.card_eq_fintype_card] using h5
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF2
  rcases mem_conjSet_cases hF2 hq5 hν x with h1 | hU | hT | hS
  · exact absurd h1 hx1
  · exfalso
    obtain ⟨-, g, hg⟩ := hU
    have hxconj : orderOf (g * x * g⁻¹) = 3 := by
      change orderOf ((MulAut.conj g) x) = 3
      rw [MulEquiv.orderOf_eq, hx]
    let p := ringChar F
    have hp : p.Prime := CharP.char_is_prime F p
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨f, hfpos, hFcard⟩ := FiniteField.card F p
    have hUcard : Nat.card (unipotent F) = p ^ (f : ℕ) := by
      rw [card_unipotent h2F, hFcard]
    have hUp : IsPGroup p (unipotent F) := IsPGroup.of_card hUcard
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hUp ⟨g * x * g⁻¹, hg⟩
    rw [Subgroup.orderOf_mk] at hk
    have h3eq : 3 = p ^ k := by rw [← hxconj, hk]
    have hp3 : p = 3 := by
      rcases k with _ | k
      · simp at h3eq
      · have hpdvd : p ∣ 3 := ⟨p ^ k, by simpa [pow_succ'] using h3eq⟩
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpdvd
    have hpdvdF : p ∣ Nat.card F := by
      rw [Nat.card_eq_fintype_card, hFcard]
      exact dvd_pow_self p f.pos.ne'
    exact h3 (hp3 ▸ hpdvdF)
  · obtain ⟨-, g, hg⟩ := hT
    have hyord : orderOf (g * x * g⁻¹) = 3 := by
      change orderOf ((MulAut.conj g) x) = 3
      rw [MulEquiv.orderOf_eq, hx]
    have hC := s1667_kgl2_centralizer_split hg hyord
    obtain ⟨φ⟩ := s1667_kgl2_centralizer_equiv (MulAut.conj g) x
    have hcard : Nat.card ↥(centralizer ({x} : Set (PSL2 F))) = Nat.card (splitTorus F) := by
      rw [Nat.card_congr φ.toEquiv]
      change Nat.card ↥(centralizer ({g * x * g⁻¹} : Set (PSL2 F))) = _
      rw [hC]
    refine ⟨?_, Or.inl ?_⟩
    · have hcyc : IsCyclic ↥(splitTorus F) := splitTorus_isCyclic
      have hcyc' : IsCyclic ↥(centralizer ({g * x * g⁻¹} : Set (PSL2 F))) := by
        rw [hC]
        exact hcyc
      exact φ.isCyclic.mpr hcyc'
    · rw [hcard, mul_comm, card_splitTorus h2F, Nat.card_eq_fintype_card]
  · obtain ⟨-, g, hg⟩ := hS
    have hyord : orderOf (g * x * g⁻¹) = 3 := by
      change orderOf ((MulAut.conj g) x) = 3
      rw [MulEquiv.orderOf_eq, hx]
    have hC := s1667_kgl2_centralizer_nonsplit hF2 hν hg hyord
    obtain ⟨φ⟩ := s1667_kgl2_centralizer_equiv (MulAut.conj g) x
    have hcard : Nat.card ↥(centralizer ({x} : Set (PSL2 F))) = Nat.card (nonsplitTorus ν) := by
      rw [Nat.card_congr φ.toEquiv]
      change Nat.card ↥(centralizer ({g * x * g⁻¹} : Set (PSL2 F))) = _
      rw [hC]
    refine ⟨?_, Or.inr ?_⟩
    · have hcyc : IsCyclic ↥(nonsplitTorus ν) :=
        CFSG.Glauberman.Dickson.MaxStructure.nonsplitTorus_isCyclic hν
      have hcyc' : IsCyclic ↥(centralizer ({g * x * g⁻¹} : Set (PSL2 F))) := by
        rw [hC]
        exact hcyc
      exact φ.isCyclic.mpr hcyc'
    · rw [hcard, mul_comm, card_nonsplitTorus hF2 hν, Nat.card_eq_fintype_card]

theorem s1667_kgl2_centralizer_lieModel {J : Type} [Group J] [Finite J] {p f : ℕ}
    (h : CFSG.Blueprint.LieModel J .PSL 2 p f) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {x : J}
    (hx : orderOf x = 3) :
    IsCyclic ↥(centralizer ({x} : Set J)) ∧
      (2 * Nat.card ↥(centralizer ({x} : Set J)) = p ^ f - 1 ∨
        2 * Nat.card ↥(centralizer ({x} : Set J)) = p ^ f + 1) := by
  obtain ⟨hp, hf1, -, -, F, hF, hFin, hcard, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data h
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    exact (by omega : 4 ≤ p).trans (Nat.le_self_pow (by omega) p)
  have h3 : ¬ 3 ∣ Nat.card F := by
    intro hd
    rw [hcard] at hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)).symm
  have hex : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  obtain ⟨hcyc, hord⟩ := s1667_kgl2_centralizer_psl2 hodd h4 h3 hex
  obtain ⟨φ⟩ := s1667_kgl2_centralizer_equiv e x
  rw [hcard] at hord
  refine ⟨φ.isCyclic.mpr hcyc, ?_⟩
  rw [Nat.card_congr φ.toEquiv]
  exact hord

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
