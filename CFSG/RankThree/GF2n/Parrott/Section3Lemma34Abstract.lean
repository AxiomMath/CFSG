module

public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.GF2n.Parrott.Section3Lemma34IndexTwo
import CFSG.RankThree.GF2n.Parrott.Section3Lemma34Config
import CFSG.GroupTheory.SmallFixedTwoGroup.PropBTransfer
import CFSG.Quasithin.Recognition.L34CIT.Count

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

private theorem exists_config_of_index_two {Y : Type} [Group Y] [Finite Y] {M D : Subgroup Y}
    (hDM : D ≤ M) (hD : IsElemAbelian 2 D) (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥M →* Equiv.Perm (Fin 5), Function.Surjective π ∧ π.ker = D.subgroupOf M)
    (hCent : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set Y) ≤ M)
    (hC128 : ∀ d ∈ D, d ≠ 1 → Nat.card (Subgroup.centralizer ({d} : Set Y)) = 128)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ M, g * a * g⁻¹ = b)
    {K : Subgroup Y} [K.Normal] (hK2 : K.index = 2) (hDK : D ≤ K)
    (hrel : K.relIndex M = 2) (hcard960 : Nat.card (K ⊓ M : Subgroup Y) = 960)
    (hrelK : (K ⊓ M).relIndex K = M.index) (hodd : Odd M.index) (hfus : 1 < M.index) :
    ∃ C : CFSG.Quasithin.L34CIT.Config ↥K, C.L = D.subgroupOf K := by
  obtain ⟨φ, hφs, hφk⟩ := exists_hom_alternatingGroup_of_relIndex_two hDM hπ hDK hrel
  have hDKM : D ≤ K ⊓ M := le_inf hDK hDM
  have hφtr : ∀ a ∈ φ.ker, ∀ b ∈ φ.ker, a ≠ 1 → b ≠ 1 →
      ∃ g : ↥(K ⊓ M), g * a * g⁻¹ = b := by
    intro a ha b hb ha1 hb1
    rw [hφk, Subgroup.mem_subgroupOf] at ha hb
    obtain ⟨g, hg, hgab⟩ :=
      exists_mem_inf_conj_eq_of_index_two hCent hC128 hTrans hK2 hcard960 a ha b hb
        (fun h => ha1 (Subtype.ext h)) (fun h => hb1 (Subtype.ext h))
    exact ⟨⟨g, hg⟩, Subtype.ext hgab⟩
  let e : ↥((K ⊓ M).subgroupOf K) ≃* ↥(K ⊓ M) :=
    Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ M ≤ K)
  have hπ₀ : ∃ π₀ : ↥((K ⊓ M).subgroupOf K) →* alternatingGroup (Fin 5),
      Function.Surjective π₀ ∧
        π₀.ker = (D.subgroupOf K).subgroupOf ((K ⊓ M).subgroupOf K) := by
    refine ⟨φ.comp e.toMonoidHom, hφs.comp e.surjective, ?_⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφk,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hTrans₀ : ∀ a ∈ D.subgroupOf K, ∀ b ∈ D.subgroupOf K, a ≠ 1 → b ≠ 1 →
      ∃ g ∈ (K ⊓ M).subgroupOf K, g * a * g⁻¹ = b := by
    intro a ha b hb ha1 hb1
    have haB : a ∈ (K ⊓ M).subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr (hDKM (Subgroup.mem_subgroupOf.mp ha))
    have hbB : b ∈ (K ⊓ M).subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr (hDKM (Subgroup.mem_subgroupOf.mp hb))
    have hda : e ⟨a, haB⟩ ∈ φ.ker := by
      rw [hφk, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_subgroupOf.mp ha
    have hdb : e ⟨b, hbB⟩ ∈ φ.ker := by
      rw [hφk, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_subgroupOf.mp hb
    have hne : ∀ x : ↥((K ⊓ M).subgroupOf K), x ≠ 1 → e x ≠ 1 := fun x hx h =>
      hx (e.injective (by simpa using h))
    obtain ⟨g, hgab⟩ :=
      hφtr (e ⟨a, haB⟩) hda (e ⟨b, hbB⟩) hdb (hne _ fun h => ha1 (by simpa using h))
        (hne _ fun h => hb1 (by simpa using h))
    refine ⟨e.symm g, (e.symm g).2, ?_⟩
    have hB : e.symm g * ⟨a, haB⟩ * (e.symm g)⁻¹ = ⟨b, hbB⟩ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
      exact hgab
    simpa using congrArg Subtype.val hB
  have hCent₀ : ∀ d ∈ D.subgroupOf K, d ≠ 1 →
      Subgroup.centralizer ({d} : Set ↥K) ≤ (K ⊓ M).subgroupOf K := by
    intro d hd hd1 c hc
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨c.2, hCent (d : Y) (Subgroup.mem_subgroupOf.mp hd) ?_ ?_⟩
    · intro h
      exact hd1 (Subtype.ext h)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun z : ↥K => (z : Y))
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hidx : ((K ⊓ M).subgroupOf K).index = M.index := hrelK
  have hD₀ : IsElemAbelian 2 (D.subgroupOf K) := hD.subgroupOf K
  have hD16₀ : Nat.card (D.subgroupOf K) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv).trans hD16
  have hDB₀ : D.subgroupOf K ≤ (K ⊓ M).subgroupOf K := Subgroup.subgroupOf_mono K hDKM
  exact exists_config_of_e16_alt5 hDB₀ hD₀ hD16₀ hπ₀ hTrans₀ hCent₀ (hidx ▸ hodd)
    (by rw [hidx]; exact hfus)

theorem lemma34_abstract {Y : Type} [Group Y] [Finite Y] (M D : Subgroup Y)
    (hDM : D ≤ M)
    (hD : IsElemAbelian 2 D) (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥M →* Equiv.Perm (Fin 5), Function.Surjective π ∧ π.ker = D.subgroupOf M)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ M, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set Y) ≤ M)
    (hodd : Odd M.index) (hfus : 1 < M.index) :
    ∃ K : Subgroup Y, K.Normal ∧ K.index = 2 ∧ D ≤ K ∧ ¬ M ≤ K ∧
      (∀ L : Subgroup Y, D ≤ L → L ≤ M → L.relIndex M = 2 → L = K ⊓ M) ∧
      Nat.card K = 20160 ∧
      ∀ L : Subgroup Y, L ≤ K → L.relIndex K ≠ 2 := by
  obtain ⟨hM1920, -, -, hC128⟩ := local_data_of_permFive hDM hD16 hπ hTrans hCent
  obtain ⟨K, hKn, hK2⟩ := exists_normal_index_two_of_permFive hDM hD hD16 hπ hTrans hCent hodd
  have hMK : ¬ M ≤ K := not_le_of_odd_index_of_index_two hodd hK2
  have hDK : D ≤ K := @le_of_index_two_of_transitive Y _ _ M D hD16 hTrans K hKn hK2
  have hrel : K.relIndex M = 2 := @relIndex_eq_two_of_index_two Y _ _ M K hKn hMK hK2
  have hcard960 : Nat.card (K ⊓ M : Subgroup Y) = 960 :=
    card_inf_eq_of_relIndex_two hM1920 hrel
  have hKcard : Nat.card K * 2 = 1920 * M.index := by
    have h1 := Subgroup.card_mul_index K
    have h2 := Subgroup.card_mul_index M
    rw [hK2] at h1
    rw [hM1920] at h2
    omega
  have hrelK : (K ⊓ M).relIndex K = M.index := by
    have h := Subgroup.relIndex_mul_card (H := K ⊓ M) (K := K)
    rw [inf_of_le_left (inf_le_left : K ⊓ M ≤ K), hcard960] at h
    omega
  obtain ⟨C, -⟩ := @exists_config_of_index_two Y _ _ M D hDM hD hD16 hπ hCent hC128 hTrans
    K hKn hK2 hDK hrel hcard960 hrelK hodd hfus
  obtain ⟨π, hs, hk⟩ := hπ
  refine ⟨K, hKn, hK2, hDK, hMK, eq_inf_of_relIndex_two hs hk hDK hrel, C.card_eq, ?_⟩
  intro L hLK hL2
  exact CFSG.GroupTheory.SmallFixedTwoGroup.index_ne_two_of_commutator_eq_top
    (C.commutator_eq_top C.card_eq) (L.subgroupOf K) hL2

end CFSG.RankThree.GF2n.Parrott
