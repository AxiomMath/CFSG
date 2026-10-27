module

public import CFSG.RankThree.GF2n.Parrott.Basic
public import CFSG.GroupTheory.Extraspecial2PG

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_decomposition (h : Tim79a.ParrottHyp z) :
    ∃ T F : Subgroup G, Nat.card T = 2 ∧ IsExtraspecial2 F ∧ Nat.card F = 2 ^ 9 ∧
      T ⊓ F = ⊥ ∧ (∀ t ∈ T, ∀ f ∈ F, Commute t f) ∧
      T ⊔ F = J z := by
  obtain ⟨h1, ⟨T, F, hT, hF, hFc, hdisj, hcomm, hsup⟩, hrest⟩ := h
  exact ⟨T, F, hT, hF, hFc, hdisj, hcomm, by simpa [J, H] using hsup⟩

theorem J_eq_sup_T_F {T F : Subgroup G} (h : Tim79a.ParrottHyp z)
    (hTF : T ⊔ F = J z) : J z = T ⊔ F := hTF.symm

private theorem commute_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) : Commute a b := by
  have hcomm : IsMulCommutative A := by
    haveI : IsCyclic A := isCyclic_of_prime_card (p := 2) hA
    infer_instance
  have h : a ∈ Subgroup.centralizer (A : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).mpr hcomm ha
  exact (Subgroup.mem_centralizer_iff.mp h b hb).symm

theorem commutator_mem_centerIn_J (h : Tim79a.ParrottHyp z) {x y : G}
    (hx : x ∈ J z) (hy : y ∈ J z) : ⁅x, y⁆ ∈ centerIn (J z) := by
  obtain ⟨T, F, hT, hF, hFc, hdisj, hcomm, hTF⟩ := exists_decomposition h
  have hTT : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' :=
    fun t ht t' ht' => commute_of_card_two hT ht ht'
  have hcenter : centerIn (J z) = T ⊔ (Subgroup.center F).map F.subtype := by
    rw [J_eq_sup_T_F h hTF]
    exact CFSG.centerIn_sup_eq_sup_center hTT hcomm hdisj
  have hle : ⁅J z, J z⁆ ≤ (Subgroup.center F).map F.subtype := by
    rw [J_eq_sup_T_F h hTF]
    calc ⁅T ⊔ F, T ⊔ F⁆ ≤ ⁅F, F⁆ := CFSG.commutator_sup_le_commutator_right hTT hcomm
      _ = (Subgroup.center F).map F.subtype := hF.2.1
  have hmem : ⁅x, y⁆ ∈ ⁅J z, J z⁆ :=
    Subgroup.commutator_mem_commutator hx hy
  rw [hcenter]
  exact Subgroup.mem_sup_right (hle hmem)

theorem sq_mem_centerIn_J (h : Tim79a.ParrottHyp z) {x : G} (hx : x ∈ J z) :
    x * x ∈ centerIn (J z) := by
  obtain ⟨T, F, hT, hF, hFc, hdisj, hcomm, hTF⟩ := exists_decomposition h
  have hTT : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' :=
    fun t ht t' ht' => commute_of_card_two hT ht ht'
  have hcenter : centerIn (J z) = T ⊔ (Subgroup.center F).map F.subtype := by
    rw [J_eq_sup_T_F h hTF]
    exact CFSG.centerIn_sup_eq_sup_center hTT hcomm hdisj
  rw [J_eq_sup_T_F h hTF] at hx
  obtain ⟨t, ht, f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hx
  have ht2 : t * t = 1 := by
    have h1 : (⟨t, ht⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
    rw [hT] at h1
    have := congrArg Subtype.val h1
    simpa [pow_two] using this
  have hff : f * f ∈ (Subgroup.center F).map F.subtype :=
    CFSG.IsExtraspecial2.mul_self_mem_center_map hF hf
  rw [hcenter]
  have heq : (t * f) * (t * f) = f * f := by
    have htf : Commute t f := hcomm t ht f hf
    calc (t * f) * (t * f) = t * (f * (t * f)) := by rw [mul_assoc]
      _ = t * ((f * t) * f) := by rw [mul_assoc]
      _ = t * ((t * f) * f) := by rw [htf.eq]
      _ = (t * t) * (f * f) := by group
      _ = f * f := by rw [ht2, one_mul]
  rw [heq]
  exact Subgroup.mem_sup_right hff

theorem centerIn_J_sq (h : Tim79a.ParrottHyp z) {x : G} (hx : x ∈ centerIn (J z)) :
    x * x = 1 := by
  obtain ⟨T, F, hT, hF, hFc, hdisj, hcomm, hTF⟩ := exists_decomposition h
  have hTT : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' :=
    fun t ht t' ht' => commute_of_card_two hT ht ht'
  have hcenter : centerIn (J z) = T ⊔ (Subgroup.center F).map F.subtype := by
    rw [J_eq_sup_T_F h hTF]
    exact CFSG.centerIn_sup_eq_sup_center hTT hcomm hdisj
  rw [hcenter] at hx
  have hcommTC : ∀ t ∈ T, ∀ c ∈ (Subgroup.center F).map F.subtype, Commute t c := by
    intro t ht c hc
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
    exact hcomm t ht c' c'.2
  obtain ⟨t, ht, c, hc, rfl⟩ := (CFSG.mem_sup_of_commute hcommTC).mp hx
  have ht2 : t * t = 1 := by
    have h1 : (⟨t, ht⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
    rw [hT] at h1
    have := congrArg Subtype.val h1
    simpa [pow_two] using this
  have hc2 : c * c = 1 := by
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
    have h1 : (⟨c', hc'⟩ : Subgroup.center F) ^ Nat.card (Subgroup.center F) = 1 :=
      pow_card_eq_one'
    have hcard : Nat.card (Subgroup.center F) = 2 := by
      have h := hF.2.2
      rw [hF.2.1, Subgroup.card_map_of_injective F.subtype_injective] at h
      exact h
    rw [hcard] at h1
    have hval : ((⟨c', hc'⟩ : Subgroup.center F) : F) ^ 2 = 1 := by
      simpa using congrArg (fun u : Subgroup.center F => (u : F)) h1
    have hval' : (c' : G) * (c' : G) = 1 := by
      have := congrArg (fun u : F => (u : G)) hval
      simpa [pow_two] using this
    exact hval'
  have htc : Commute t c := hcommTC t ht c hc
  calc (t * c) * (t * c) = t * (c * (t * c)) := by rw [mul_assoc]
    _ = t * ((c * t) * c) := by rw [mul_assoc]
    _ = t * ((t * c) * c) := by rw [htc.eq]
    _ = (t * t) * (c * c) := by group
    _ = 1 := by rw [ht2, hc2, mul_one]

end CFSG.RankThree.GF2n.Parrott
