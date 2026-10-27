module

public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalBorel
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Data
import CFSG.Quasithin.Recognition.St84.Gen.D4qTrialityVertexTwo
import CFSG.Quasithin.Recognition.St84.Gen.L2WeylComplement
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
public import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
  CFSG.LocalAnalysis.EvenBN.TrialityD4
open CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

open Subgroup

variable {G X : Type} [Group G] [Group X] [Finite G] [Finite X]
  {L1 L2 S H : Subgroup G} {f : ℕ}

private theorem mem_map_subtype_comp {G X : Type*} [Group G] [Group X]
    {P : Subgroup G} {NV : Subgroup X} (ψ : ↥P ≃* ↥NV) (Q : Subgroup G) (hQ : Q ≤ P)
    {x : ↥P} :
    (ψ x : X) ∈ (Q.subgroupOf P).map (NV.subtype.comp ψ.toMonoidHom) ↔ (x : G) ∈ Q := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hxy' : ψ y = ψ x := Subtype.ext hxy
    rw [ψ.injective hxy'] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  · intro hx
    exact Subgroup.mem_map_of_mem (NV.subtype.comp ψ.toMonoidHom)
      (Subgroup.mem_subgroupOf.mpr hx)

private theorem card_map_subtype_comp {G X : Type*} [Group G] [Group X]
    {P : Subgroup G} {NV : Subgroup X} (ψ : ↥P ≃* ↥NV) (Q : Subgroup G) (hQ : Q ≤ P) :
    Nat.card ((Q.subgroupOf P).map (NV.subtype.comp ψ.toMonoidHom)) = Nat.card Q := by
  have hinj : Function.Injective (NV.subtype.comp ψ.toMonoidHom) := by
    intro a b h
    exact ψ.injective (Subtype.ext h)
  rw [Subgroup.card_map_of_injective hinj,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv]

private theorem mem_normalizer_map_subtype_comp {G X : Type*} [Group G] [Group X]
    {P : Subgroup G} {NV : Subgroup X} (ψ : ↥P ≃* ↥NV) (Q : Subgroup G) (hQ : Q ≤ P)
    {x : ↥P} (hx : (x : G) ∈ Subgroup.normalizer (Q : Set G)) :
    (ψ x : X) ∈ Subgroup.normalizer
      ((Q.subgroupOf P).map (NV.subtype.comp ψ.toMonoidHom) : Set X) := by
  have hx' : x ∈ Subgroup.normalizer (Q.subgroupOf P) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hQ]
    exact Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.le_normalizer_map (NV.subtype.comp ψ.toMonoidHom)
    (Subgroup.mem_map_of_mem _ hx')

private theorem exists_preimage_of_iff {G X : Type*} [Group G] [Group X]
    {P : Subgroup G} {NV : Subgroup X} (ψ : ↥P ≃* ↥NV) {Q : Subgroup G} {T : Subgroup X}
    (hiff : ∀ x : ↥P, (x : G) ∈ Q ↔ (ψ x : X) ∈ T) {y : X} (hy : y ∈ T) (hyNV : y ∈ NV) :
    ∃ x : ↥P, (x : G) ∈ Q ∧ (ψ x : X) = y := by
  refine ⟨ψ.symm ⟨y, hyNV⟩, ?_, ?_⟩
  · exact (hiff _).mpr (by
      rw [show (ψ (ψ.symm ⟨y, hyNV⟩) : X) = y from
        congrArg Subtype.val (ψ.apply_symm_apply ⟨y, hyNV⟩)]
      exact hy)
  · exact congrArg Subtype.val (ψ.apply_symm_apply ⟨y, hyNV⟩)

private theorem commutator_mem_pCoreOf_right_of_mem_S (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) {s t : G} (hs : s ∈ S) (ht : t ∈ S) :
    ⁅s, t⁆ ∈ pCoreOf 2 L2 := by
  obtain ⟨c2⟩ := hD.exists_coordRight hH
  letI := c2.field
  letI := c2.fintype
  have hsL2 : s ∈ L2 := hD.le_right hH hs
  have htL2 : t ∈ L2 := hD.le_right hH ht
  have hstL2 : ⁅s, t⁆ ∈ L2 :=
    L2.mul_mem (L2.mul_mem (L2.mul_mem hsL2 htL2) (L2.inv_mem hsL2))
      (L2.inv_mem htL2)
  have hsU : c2.α ⟨s, hsL2⟩ ∈ utri c2.F := (c2.memS _).mp hs
  have htU : c2.α ⟨t, htL2⟩ ∈ utri c2.F := (c2.memS _).mp ht
  have hcommU : c2.α ⟨s, hsL2⟩ * c2.α ⟨t, htL2⟩ =
      c2.α ⟨t, htL2⟩ * c2.α ⟨s, hsL2⟩ := by
    obtain ⟨u, hu⟩ := mem_utri_iff_eq_unitri.mp hsU
    obtain ⟨v, hv⟩ := mem_utri_iff_eq_unitri.mp htU
    rw [eq_utriElt_of_eq_unitri hu, eq_utriElt_of_eq_unitri hv, ← utriElt_add,
      ← utriElt_add, add_comm]
  have hca : c2.α ⟨⁅s, t⁆, hstL2⟩ = 1 := by
    have hsub : (⟨⁅s, t⁆, hstL2⟩ : ↥L2) =
        ⁅(⟨s, hsL2⟩ : ↥L2), (⟨t, htL2⟩ : ↥L2)⁆ := rfl
    rw [hsub, map_commutatorElement]
    rw [commutatorElement_def, hcommU]
    group
  exact (c2.ker ⟨⁅s, t⁆, hstL2⟩).mp hca

private theorem commutator_S_le_image (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hQ2comm : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ pCoreOf 2 L2) :
    ⁅d.S, d.S⁆ ≤ ((pCoreOf 2 L2).subgroupOf (L1 ⊔ bigB L1 L2 S)).map
      ((Subgroup.normalizer (d.V : Set X)).subtype.comp ψ.toMonoidHom) := by
  classical
  let F : ↥(L1 ⊔ bigB L1 L2 S) →* X :=
    (Subgroup.normalizer (d.V : Set X)).subtype.comp ψ.toMonoidHom
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haNV : a ∈ Subgroup.normalizer (d.V : Set X) := d.S_le_normalizer_V ha
  have hbNV : b ∈ Subgroup.normalizer (d.V : Set X) := d.S_le_normalizer_V hb
  let s : ↥(L1 ⊔ bigB L1 L2 S) := ψ.symm ⟨a, haNV⟩
  let t : ↥(L1 ⊔ bigB L1 L2 S) := ψ.symm ⟨b, hbNV⟩
  have hsψ : (ψ s : X) = a := congrArg Subtype.val (ψ.apply_symm_apply ⟨a, haNV⟩)
  have htψ : (ψ t : X) = b := congrArg Subtype.val (ψ.apply_symm_apply ⟨b, hbNV⟩)
  have hsS : (s : G) ∈ S := (hψS s).mpr (by rw [hsψ]; exact ha)
  have htS : (t : G) ∈ S := (hψS t).mpr (by rw [htψ]; exact hb)
  have hstQ : ⁅(s : G), (t : G)⁆ ∈ pCoreOf 2 L2 := hQ2comm s hsS t htS
  have hmemN : (ψ ⁅s, t⁆ : X) ∈ ((pCoreOf 2 L2).subgroupOf
      (L1 ⊔ bigB L1 L2 S)).map ((Subgroup.normalizer (d.V : Set X)).subtype.comp
        ψ.toMonoidHom) :=
    Subgroup.mem_map_of_mem F (Subgroup.mem_subgroupOf.mpr hstQ)
  have hmap : (ψ ⁅s, t⁆ : X) = ⁅(ψ s : X), (ψ t : X)⁆ :=
    map_commutatorElement F s t
  rw [hsψ, htψ] at hmap
  rw [← hmap]
  exact hmemN

theorem D4qLocalData.mem_pCoreOf_right_iff_mem_M (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (hHB : H ≤ bigB L1 L2 S)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (x : ↥(L1 ⊔ bigB L1 L2 S)) :
    (x : G) ∈ pCoreOf 2 L2 ↔ (ψ x : X) ∈ d.M := by
  classical
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hQ2P : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S :=
    hH.pCoreOf_le_right.trans (hSB.trans hBP)
  let N : Subgroup X :=
    ((pCoreOf 2 L2).subgroupOf (L1 ⊔ bigB L1 L2 S)).map
      ((Subgroup.normalizer (d.V : Set X)).subtype.comp ψ.toMonoidHom)
  have hNcard : Nat.card N = (2 ^ f) ^ 11 := by
    rw [show N = ((pCoreOf 2 L2).subgroupOf (L1 ⊔ bigB L1 L2 S)).map
        ((Subgroup.normalizer (d.V : Set X)).subtype.comp ψ.toMonoidHom) from rfl,
      card_map_subtype_comp ψ (pCoreOf 2 L2) hQ2P, hD.card_right]
    rw [← pow_mul, Nat.mul_comm]
  have hNS : N ≤ d.S := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact (hψS z).mp (hH.pCoreOf_le_right (Subgroup.mem_subgroupOf.mp hz))
  have hQ2comm : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ pCoreOf 2 L2 :=
    fun s hs t ht => commutator_mem_pCoreOf_right_of_mem_S hH hD hs ht
  have hFN : d.F ≤ N := by
    rw [← d.commutator_S_eq]
    exact commutator_S_le_image d ψ hψS hQ2comm
  have hJN : d.J₂ ≤ Subgroup.normalizer (N : Set X) := by
    intro j hj
    have hjJ : j ∈ d.J := (Subgroup.mem_inf.mp hj).1
    have hjNV : j ∈ Subgroup.normalizer (d.V : Set X) := d.J_le_normalizer_V hjJ
    let h : ↥(L1 ⊔ bigB L1 L2 S) := ψ.symm ⟨j, hjNV⟩
    have hψ : (ψ h : X) = j := congrArg Subtype.val (ψ.apply_symm_apply ⟨j, hjNV⟩)
    have hhH : (h : G) ∈ H := (hψH h).mpr (by rw [hψ]; exact hjJ)
    have hhNQ : (h : G) ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
      hH.bigB_le_normalizer_pCoreOf_right (hHB hhH)
    have himg := mem_normalizer_map_subtype_comp ψ (pCoreOf 2 L2) hQ2P hhNQ
    rwa [hψ] at himg
  have hNM : N = d.M := eq_M_of_F_le_of_le_S d hFN hNS hJN hNcard
  constructor
  · intro hx
    have hmem : (ψ x : X) ∈ N :=
      (mem_map_subtype_comp ψ (pCoreOf 2 L2) hQ2P (x := x)).mpr hx
    rwa [hNM] at hmem
  · intro hx
    have hmem : (ψ x : X) ∈ N := by rwa [hNM]
    exact (mem_map_subtype_comp ψ (pCoreOf 2 L2) hQ2P (x := x)).mp hmem

theorem D4qLocalData.mem_torus_right_iff_mem_J₂ (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (x : ↥(L1 ⊔ bigB L1 L2 S)) :
    (x : G) ∈ H ⊓ trivOTwoQuot L2 ↔ (ψ x : X) ∈ d.J₂ := by
  classical
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hQ2P : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S :=
    hH.pCoreOf_le_right.trans (hSB.trans hBP)
  let H0 : Subgroup G := H ⊓ trivOTwoQuot L2
  have hH0P : H0 ≤ L1 ⊔ bigB L1 L2 S := (inf_le_left.trans hHB).trans hBP
  let F : ↥(L1 ⊔ bigB L1 L2 S) →* X :=
    (Subgroup.normalizer (d.V : Set X)).subtype.comp ψ.toMonoidHom
  let N : Subgroup X := (H0.subgroupOf (L1 ⊔ bigB L1 L2 S)).map F
  have hTR := hD.torus_right_of_hall hf hH h1 hHB hSH hSinfH hHcard hHcomm
  have hH0card : Nat.card H0 = 2 ^ (3 * f) - 1 := hTR.2.1
  have hforward : ∀ y : ↥(L1 ⊔ bigB L1 L2 S), (y : G) ∈ H0 → (ψ y : X) ∈ d.J₂ := by
    intro y hy
    have hyH : (y : G) ∈ H := (Subgroup.mem_inf.mp hy).1
    have hyJ : (ψ y : X) ∈ d.J := (hψH y).mp hyH
    refine (mem_J₂_iff_forall_mem_M d hyJ).mpr ?_
    intro s hs
    obtain ⟨t, htS, htψ⟩ := exists_preimage_of_iff ψ hψS hs (d.S_le_normalizer_V hs)
    have htL : (t : G) ∈ L2 := hD.le_right hH htS
    have hyH0 : (y : G) ∈ trivOTwoQuot L2 := (Subgroup.mem_inf.mp hy).2
    have hyt : ⁅(y : G), (t : G)⁆ ∈ pCoreOf 2 L2 :=
      (mem_trivOTwoQuot.mp hyH0).2 (t : G) htL
    have hmemM : (ψ ⁅y, t⁆ : X) ∈ d.M :=
      (D4qLocalData.mem_pCoreOf_right_iff_mem_M hH hD hHB d ψ hψS hψH ⁅y, t⁆).mp hyt
    have hmap : (ψ ⁅y, t⁆ : X) = (ψ y : X) * s * (ψ y : X)⁻¹ * s⁻¹ := by
      rw [← htψ]
      simpa [commutatorElement_def] using map_commutatorElement F y t
    rw [← hmap]
    exact hmemM
  have hNJ : N ≤ d.J₂ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact hforward z (Subgroup.mem_subgroupOf.mp hz)
  have hNcard : Nat.card N = 2 ^ (3 * f) - 1 := by
    rw [show N = (H0.subgroupOf (L1 ⊔ bigB L1 L2 S)).map F from rfl,
      card_map_subtype_comp ψ H0 hH0P, hH0card]
  have hq3 : (2 ^ f) ^ 3 = 2 ^ (3 * f) := by rw [← pow_mul, Nat.mul_comm]
  have hJ₂card : Nat.card d.J₂ = 2 ^ (3 * f) - 1 := by
    rw [← hq3]
    exact d.yamada_three_five_one.2.2.2.2.2
  have hNJeq : N = d.J₂ :=
    Subgroup.eq_of_le_of_card_ge hNJ (Nat.le_of_eq (hJ₂card.trans hNcard.symm))
  constructor
  · intro hx
    have hmem : (ψ x : X) ∈ N :=
      (mem_map_subtype_comp ψ H0 hH0P (x := x)).mpr hx
    rwa [hNJeq] at hmem
  · intro hx
    have hmem : (ψ x : X) ∈ N := by rwa [hNJeq]
    exact (mem_map_subtype_comp ψ H0 hH0P (x := x)).mp hmem

private theorem mem_centerOf_right_iff_mem_Y (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (hHB : H ≤ bigB L1 L2 S)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (x : ↥(L1 ⊔ bigB L1 L2 S)) :
    (x : G) ∈ centerOf (pCoreOf 2 L2) ↔ (ψ x : X) ∈ d.Y := by
  classical
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hQ2P : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S :=
    hH.pCoreOf_le_right.trans (hSB.trans hBP)
  let F : ↥(L1 ⊔ bigB L1 L2 S) →* X :=
    (Subgroup.normalizer (d.V : Set X)).subtype.comp ψ.toMonoidHom
  have hinj : Function.Injective F := by
    intro a b h
    exact ψ.injective (Subtype.ext h)
  constructor
  · intro hy
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyM : (ψ x : X) ∈ d.M :=
      (D4qLocalData.mem_pCoreOf_right_iff_mem_M hH hD hHB d ψ hψS hψH x).mp hyQ
    have hyCM : (ψ x : X) ∈ Subgroup.centralizer (d.M : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      obtain ⟨q, hqQ, hqψ⟩ := exists_preimage_of_iff ψ
        (D4qLocalData.mem_pCoreOf_right_iff_mem_M hH hD hHB d ψ hψS hψH) hm
        (d.S_le_normalizer_V (d.M_le_S hm))
      have hcomm : (q : G) * (x : G) = (x : G) * (q : G) :=
        (Subgroup.mem_centralizer_iff.mp hyC) q hqQ
      have hcommP : q * x = x * q := Subtype.ext hcomm
      calc m * (ψ x : X) = (ψ q : X) * (ψ x : X) := by rw [hqψ]
        _ = (ψ (q * x) : X) := (map_mul F q x).symm
        _ = (ψ (x * q) : X) := by rw [hcommP]
        _ = (ψ x : X) * (ψ q : X) := map_mul F x q
        _ = (ψ x : X) * m := by rw [hqψ]
    rw [← d.M_inf_centralizer_M]
    exact ⟨hyM, hyCM⟩
  · intro hyY
    rw [← d.M_inf_centralizer_M] at hyY
    obtain ⟨hyM, hyCM⟩ := Subgroup.mem_inf.mp hyY
    have hyQ : (x : G) ∈ pCoreOf 2 L2 :=
      (D4qLocalData.mem_pCoreOf_right_iff_mem_M hH hD hHB d ψ hψS hψH x).mpr hyM
    have hyC : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 L2 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      let q' : ↥(L1 ⊔ bigB L1 L2 S) := ⟨q, hQ2P hq⟩
      have hqM : (ψ q' : X) ∈ d.M :=
        (D4qLocalData.mem_pCoreOf_right_iff_mem_M hH hD hHB d ψ hψS hψH q').mp hq
      have hcomm : (ψ q' : X) * (ψ x : X) = (ψ x : X) * (ψ q' : X) :=
        (Subgroup.mem_centralizer_iff.mp hyCM) (ψ q' : X) hqM
      have heq : q' * x = x * q' := hinj (by
        calc F (q' * x) = F q' * F x := map_mul F q' x
          _ = F x * F q' := hcomm
          _ = F (x * q') := (map_mul F x q').symm)
      exact congrArg Subtype.val heq
    exact Subgroup.mem_inf.mpr ⟨hyQ, hyC⟩

private theorem mem_mid_right_iff_mem_W (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (hHB : H ≤ bigB L1 L2 S)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    {W2 : Subgroup G} (hWQ : W2 ≤ pCoreOf 2 L2)
    (hWcard : Nat.card W2 = 2 ^ (5 * f))
    (hWcomm : ⁅W2, L2⁆ ≤ centerOf (pCoreOf 2 L2))
    (x : ↥(L1 ⊔ bigB L1 L2 S)) :
    (x : G) ∈ W2 ↔ (ψ x : X) ∈ d.W := by
  classical
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hQ2P : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S :=
    hH.pCoreOf_le_right.trans (hSB.trans hBP)
  let F : ↥(L1 ⊔ bigB L1 L2 S) →* X :=
    (Subgroup.normalizer (d.V : Set X)).subtype.comp ψ.toMonoidHom
  have hW2P : W2 ≤ L1 ⊔ bigB L1 L2 S := hWQ.trans hQ2P
  have hZY := mem_centerOf_right_iff_mem_Y hH hD hHB d ψ hψS hψH
  have hle : (W2.subgroupOf (L1 ⊔ bigB L1 L2 S)).map F ≤ d.W := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hwQ : (w : G) ∈ pCoreOf 2 L2 := hWQ (Subgroup.mem_subgroupOf.mp hw)
    have hwS : (w : G) ∈ S := hH.pCoreOf_le_right hwQ
    refine (d.mem_W_iff_forall).mpr ⟨(hψS w).mp hwS, ?_⟩
    intro s hs
    obtain ⟨t, htS, htψ⟩ := exists_preimage_of_iff ψ hψS hs (d.S_le_normalizer_V hs)
    have htL : (t : G) ∈ L2 := hD.le_right hH htS
    have hwt : ⁅(w : G), (t : G)⁆ ∈ centerOf (pCoreOf 2 L2) :=
      (Subgroup.commutator_le.mp hWcomm) w (Subgroup.mem_subgroupOf.mp hw) t htL
    have hmemY : (ψ ⁅w, t⁆ : X) ∈ d.Y := (hZY ⁅w, t⁆).mp hwt
    have hmap : (ψ ⁅w, t⁆ : X) = (ψ w : X) * s * (ψ w : X)⁻¹ * s⁻¹ := by
      rw [← htψ]
      simpa [commutatorElement_def] using map_commutatorElement F w t
    change (ψ w : X) * s * (ψ w : X)⁻¹ * s⁻¹ ∈ d.Y
    rw [← hmap]
    exact hmemY
  have hcard : Nat.card ((W2.subgroupOf (L1 ⊔ bigB L1 L2 S)).map F) = Nat.card d.W := by
    rw [card_map_subtype_comp ψ W2 hW2P, hWcard, d.card_W, ← pow_mul, Nat.mul_comm]
  have heq : (W2.subgroupOf (L1 ⊔ bigB L1 L2 S)).map F = d.W :=
    Subgroup.eq_of_le_of_card_ge hle (Nat.le_of_eq hcard.symm)
  rw [← heq]
  exact (mem_map_subtype_comp ψ W2 hW2P (x := x)).symm

theorem D4qLocalData.mem_inf_right_iff_mem_J₄ (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    (x : ↥(L1 ⊔ bigB L1 L2 S)) :
    (x : G) ∈ H ⊓ L2 ↔ (ψ x : X) ∈ d.J₄ := by
  classical
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hQ2P : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S :=
    hH.pCoreOf_le_right.trans (hSB.trans hBP)
  let F : ↥(L1 ⊔ bigB L1 L2 S) →* X :=
    (Subgroup.normalizer (d.V : Set X)).subtype.comp ψ.toMonoidHom
  obtain ⟨W2, -, hWQ, hWcard, hWcomm⟩ := hD.mid_right
  have hZY := mem_centerOf_right_iff_mem_Y hH hD hHB d ψ hψS hψH
  have hWN := mem_mid_right_iff_mem_W hH hD hHB d ψ hψS hψH hWQ hWcard hWcomm
  have hforward : ∀ y : ↥(L1 ⊔ bigB L1 L2 S),
      (y : G) ∈ H ⊓ L2 → (ψ y : X) ∈ d.J₄ := by
    intro y hy
    obtain ⟨hyH, hyL⟩ := Subgroup.mem_inf.mp hy
    have hyJ : (ψ y : X) ∈ d.J := (hψH y).mp hyH
    refine (mem_J₄_iff_forall_mem_Y d hyJ).mpr ?_
    intro w hw
    obtain ⟨w2, hw2W, hw2ψ⟩ := exists_preimage_of_iff ψ hWN hw
      (d.W_le_S.trans d.S_le_normalizer_V hw)
    have hw2L : (w2 : G) ∈ L2 := hD.le_right hH (hH.pCoreOf_le_right (hWQ hw2W))
    have hcommZ : ⁅(y : G), (w2 : G)⁆ ∈ centerOf (pCoreOf 2 L2) := by
      have h : ⁅(w2 : G), (y : G)⁆ ∈ centerOf (pCoreOf 2 L2) :=
        (Subgroup.commutator_le.mp hWcomm) w2 hw2W y hyL
      have hinv : ⁅(y : G), (w2 : G)⁆ = ⁅(w2 : G), (y : G)⁆⁻¹ :=
        (commutatorElement_inv (w2 : G) (y : G)).symm
      rw [hinv]
      exact (centerOf (pCoreOf 2 L2)).inv_mem h
    have hmemY : (ψ ⁅y, w2⁆ : X) ∈ d.Y := (hZY ⁅y, w2⁆).mp hcommZ
    have hmap : (ψ ⁅y, w2⁆ : X) = (ψ y : X) * w * (ψ y : X)⁻¹ * w⁻¹ := by
      rw [← hw2ψ]
      simpa [commutatorElement_def] using map_commutatorElement F y w2
    rw [← hmap]
    exact hmemY
  have hHL2P : H ⊓ L2 ≤ L1 ⊔ bigB L1 L2 S := (inf_le_left.trans hHB).trans hBP
  let N : Subgroup X := ((H ⊓ L2).subgroupOf (L1 ⊔ bigB L1 L2 S)).map F
  have hNJ : N ≤ d.J₄ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact hforward z (Subgroup.mem_subgroupOf.mp hz)
  have hTR := hD.torus_right_of_hall hf hH h1 hHB hSH hSinfH hHcard hHcomm
  have hNcard : Nat.card N = 2 ^ f - 1 := by
    rw [show N = ((H ⊓ L2).subgroupOf (L1 ⊔ bigB L1 L2 S)).map F from rfl,
      card_map_subtype_comp ψ (H ⊓ L2) hHL2P, hTR.1]
  have hJ₄card : Nat.card d.J₄ = 2 ^ f - 1 := d.card_J₄
  have hNJeq : N = d.J₄ :=
    Subgroup.eq_of_le_of_card_ge hNJ (Nat.le_of_eq (hJ₄card.trans hNcard.symm))
  constructor
  · intro hx
    have hmem : (ψ x : X) ∈ N :=
      (mem_map_subtype_comp ψ (H ⊓ L2) hHL2P (x := x)).mpr hx
    rwa [hNJeq] at hmem
  · intro hx
    have hmem : (ψ x : X) ∈ N := by rwa [hNJeq]
    exact (mem_map_subtype_comp ψ (H ⊓ L2) hHL2P (x := x)).mp hmem

theorem D4qLocalData.eq_one_of_mem_pCoreOf_right_of_commute (hf : 2 ≤ f)
    (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J)
    {x : G} (hx : x ∈ pCoreOf 2 L2)
    (hxH : ∀ h ∈ H ⊓ trivOTwoQuot L2, h * x * h⁻¹ = x) : x = 1 := by
  classical
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hQ2P : pCoreOf 2 L2 ≤ L1 ⊔ bigB L1 L2 S :=
    hH.pCoreOf_le_right.trans (hSB.trans hBP)
  let F : ↥(L1 ⊔ bigB L1 L2 S) →* X :=
    (Subgroup.normalizer (d.V : Set X)).subtype.comp ψ.toMonoidHom
  let H0 : Subgroup G := H ⊓ trivOTwoQuot L2
  let x' : ↥(L1 ⊔ bigB L1 L2 S) := ⟨x, hQ2P hx⟩
  have hxM : (ψ x' : X) ∈ d.M :=
    (D4qLocalData.mem_pCoreOf_right_iff_mem_M hH hD hHB d ψ hψS hψH x').mp hx
  have hxcent : (ψ x' : X) ∈ Subgroup.centralizer (d.J₂ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjJ : j ∈ d.J := (Subgroup.mem_inf.mp hj).1
    obtain ⟨h, hhH0, hhψ⟩ := exists_preimage_of_iff ψ
      (D4qLocalData.mem_torus_right_iff_mem_J₂ hf hH hD h1 hHB hSH hSinfH hHcard
        hHcomm d ψ hψS hψH) hj (d.J_le_normalizer_V hjJ)
    have hcomm : (h : G) * x = x * (h : G) := by
      calc (h : G) * x = ((h : G) * x * (h : G)⁻¹) * (h : G) := by group
        _ = x * (h : G) := by rw [hxH h hhH0]
    have hcommP : h * x' = x' * h := Subtype.ext hcomm
    calc j * (ψ x' : X) = (ψ h : X) * (ψ x' : X) := by rw [hhψ]
      _ = (ψ (h * x') : X) := (map_mul F h x').symm
      _ = (ψ (x' * h) : X) := by rw [hcommP]
      _ = (ψ x' : X) * (ψ h : X) := map_mul F x' h
      _ = (ψ x' : X) * j := by rw [hhψ]
  have hbot : d.M ⊓ Subgroup.centralizer (d.J₂ : Set X) = ⊥ :=
    M_inf_centralizer_J₂ hf d
  have hmem : (ψ x' : X) ∈ (⊥ : Subgroup X) := by
    rw [← hbot]
    exact ⟨hxM, hxcent⟩
  rw [Subgroup.mem_bot] at hmem
  have hx'1 : x' = 1 := by
    apply ψ.injective
    apply Subtype.ext
    simpa using hmem
  exact congrArg Subtype.val hx'1

private theorem vertexTwo_complement (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J) :
    (pCoreOf 2 L2 ⊔ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) :
        Set G)) = L2 ∧
      pCoreOf 2 L2 ⊓ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) :
        Set G)) = ⊥) ∧
    H ⊓ L2 ≤ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) := by
  classical
  set Q2 : Subgroup G := pCoreOf 2 L2 with hQ2
  set H0 : Subgroup G := H ⊓ trivOTwoQuot L2 with hH0
  set K2 : Subgroup G := L2 ⊓ Subgroup.centralizer (H0 : Set G) with hK2
  have hH0B : H0 ≤ bigB L1 L2 S := inf_le_left.trans hHB
  have hTR := hD.torus_right_of_hall hf hH h1 hHB hSH hSinfH hHcard hHcomm
  have hH0card : Nat.card H0 = 2 ^ (3 * f) - 1 := hTR.2.1
  have hH0odd : Odd (2 ^ (3 * f) - 1) := by
    have h2 : Even (2 ^ (3 * f)) :=
      (show Even 2 by norm_num).pow_of_ne_zero (by omega)
    exact Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one
  have hcop : Nat.Coprime (Nat.card H0) (Nat.card Q2) := by
    rw [hH0card, hD.card_right]
    exact Nat.Coprime.pow_right (11 * f) (Nat.coprime_two_left.mpr hH0odd).symm
  have hcomm : ∀ h ∈ H0, ∀ l ∈ L2, h * l * h⁻¹ * l⁻¹ ∈ Q2 := by
    intro h hh l hl
    exact (mem_trivOTwoQuot.mp (Subgroup.mem_inf.mp hh).2).2 l hl
  have hHQ : H0 ≤ Subgroup.normalizer (Q2 : Set G) :=
    hH0B.trans hH.bigB_le_normalizer_pCoreOf_right
  have hsupQK : Q2 ⊔ K2 = L2 :=
    sup_inf_centralizer_eq_of_coprime (pCoreOf_le 2 L2) (le_normalizer_pCoreOf 2 L2)
      hHQ hcop hcomm
  have hfix : ∀ x ∈ Q2, (∀ h ∈ H0, h * x * h⁻¹ = x) → x = 1 :=
    fun x hx hxh => D4qLocalData.eq_one_of_mem_pCoreOf_right_of_commute hf hH hD h1 hHB
      hSH hSinfH hHcard hHcomm d ψ hψS hψH hx hxh
  have hinfQK : Q2 ⊓ K2 = ⊥ := by
    have h := inf_centralizer_inf_eq_bot_of_fixed (L := L2) (Q := Q2) (H := H0) hfix
    rwa [inf_comm] at h
  have hHle : H ⊓ L2 ≤ K2 := by
    intro x hx
    obtain ⟨hxH, hxL⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hHcomm x hxH h (Subgroup.mem_inf.mp hh).1).symm
  exact ⟨⟨hsupQK, hinfQK⟩, hHle⟩

private theorem vertexTwo_disjoint (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S)
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hsupQK : pCoreOf 2 L2 ⊔ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 :
        Subgroup G) : Set G)) = L2)
    (hinfQK : pCoreOf 2 L2 ⊓ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 :
        Subgroup G) : Set G)) = ⊥)
    (hH0infL : (H ⊓ trivOTwoQuot L2 : Subgroup G) ⊓ L2 = ⊥) :
    Disjoint (pCoreOf 2 L2)
      ((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L2)) := by
  classical
  set Q2 : Subgroup G := pCoreOf 2 L2 with hQ2
  set H0 : Subgroup G := H ⊓ trivOTwoQuot L2 with hH0
  set K2 : Subgroup G := L2 ⊓ Subgroup.centralizer (H0 : Set G) with hK2
  have hH0B : H0 ≤ bigB L1 L2 S := inf_le_left.trans hHB
  have hBNL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (hD.bigB_le_normalizer hH h1).trans (inf_le_left.trans inf_le_right)
  have hH0NL2 : H0 ≤ Subgroup.normalizer (L2 : Set G) := hH0B.trans hBNL2
  have hH0cent : H0 ≤ Subgroup.centralizer (H0 : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hHcomm h (Subgroup.mem_inf.mp hh).1 k (Subgroup.mem_inf.mp hk).1).symm
  have hH0Cnorm : H0 ≤ Subgroup.normalizer (Subgroup.centralizer (H0 : Set G) : Set G) :=
    hH0cent.trans Subgroup.le_normalizer
  have hH0NK : H0 ≤ Subgroup.normalizer (K2 : Set G) := by
    have h := (le_inf hH0NL2 hH0Cnorm).trans Subgroup.inf_normalizer_le_normalizer_inf
    simpa [hK2] using h
  rw [disjoint_iff]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxKH⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hkK, h, hhH0, hxk⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hH0NK).mp hxKH
  have hhL : (h : G) ∈ L2 := by
    have hhval : h = k⁻¹ * x := by rw [hxk]; group
    rw [hhval]
    exact L2.mul_mem (L2.inv_mem (Subgroup.mem_inf.mp hkK).1) (pCoreOf_le 2 L2 hxQ)
  have hh1 : h = 1 := by
    have hmem : h ∈ H0 ⊓ L2 := ⟨hhH0, hhL⟩
    rwa [hH0infL, Subgroup.mem_bot] at hmem
  have hxK : x ∈ K2 := by
    rw [hxk, hh1, mul_one]
    exact hkK
  have hmem : x ∈ Q2 ⊓ K2 := ⟨hxQ, hxK⟩
  rw [hinfQK] at hmem
  exact hmem

private theorem vertexTwo_faithful (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S)
    (hdisjQ : Disjoint (pCoreOf 2 L2)
      ((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L2))) :
    ∀ r ∈ ((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L2)), (∀ x ∈ pCoreOf 2 L2, r * x = x * r) → r = 1 := by
  classical
  set Q2 : Subgroup G := pCoreOf 2 L2 with hQ2
  set H0 : Subgroup G := H ⊓ trivOTwoQuot L2 with hH0
  set K2 : Subgroup G := L2 ⊓ Subgroup.centralizer (H0 : Set G) with hK2
  have hH0B : H0 ≤ bigB L1 L2 S := inf_le_left.trans hHB
  have hK2L : K2 ≤ L2 := inf_le_left
  intro r hr hrc
  have hVeq : L2 ⊔ bigB L1 L2 S = L2 ⊔ S ⊔ borelOf L1 S := by
    rw [sup_bigB_right_of_le (hD.le_right hH), sup_eq_left.mpr (hD.le_right hH)]
  have hK2L2B : K2 ≤ L2 ⊔ bigB L1 L2 S := hK2L.trans le_sup_left
  have hH0L2B : H0 ≤ L2 ⊔ bigB L1 L2 S := hH0B.trans le_sup_right
  have hrV : r ∈ L2 ⊔ bigB L1 L2 S := (sup_le hK2L2B hH0L2B) hr
  have hmem : r ∈ (L2 ⊔ S ⊔ borelOf L1 S) ⊓
      Subgroup.centralizer (pCoreOf 2 (L2 ⊔ S ⊔ borelOf L1 S) : Set G) := by
    refine ⟨?_, ?_⟩
    · rw [← hVeq]
      exact hrV
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro x hx
      rw [← hVeq] at hx
      rw [hD.pCoreOf_sup_bigB_right hH h1] at hx
      exact (hrc x hx).symm
  have hrQ : r ∈ Q2 := by
    have hchar := hH.h2.charTwo hmem
    rw [← hVeq, hD.pCoreOf_sup_bigB_right hH h1] at hchar
    exact hchar
  have hbotmem : r ∈ (⊥ : Subgroup G) := by
    rw [← disjoint_iff.mp hdisjQ]
    exact ⟨hrQ, hr⟩
  rwa [Subgroup.mem_bot] at hbotmem

private theorem vertexTwo_card (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f)
    (hsupQK : pCoreOf 2 L2 ⊔ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 :
        Subgroup G) : Set G)) = L2)
    (hinfQK : pCoreOf 2 L2 ⊓ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 :
        Subgroup G) : Set G)) = ⊥)
    (hH0card : Nat.card (H ⊓ trivOTwoQuot L2 : Subgroup G) = 2 ^ (3 * f) - 1)
    (hH0infL : (H ⊓ trivOTwoQuot L2 : Subgroup G) ⊓ L2 = ⊥)
    (hH0NK : (H ⊓ trivOTwoQuot L2 : Subgroup G) ≤ Subgroup.normalizer
      ((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) :
        Set G)) :
    Nat.card ↥(((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
      (H ⊓ trivOTwoQuot L2))) = 2 ^ f * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := by
  classical
  set Q2 : Subgroup G := pCoreOf 2 L2 with hQ2
  set H0 : Subgroup G := H ⊓ trivOTwoQuot L2 with hH0
  set K2 : Subgroup G := L2 ⊓ Subgroup.centralizer (H0 : Set G) with hK2
  have hK2L : K2 ≤ L2 := inf_le_left
  have hK2H0bot : K2 ⊓ H0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxH0⟩ := Subgroup.mem_inf.mp hx
    have hxL : (x : G) ∈ L2 := (Subgroup.mem_inf.mp hxK).1
    have hmem : (x : G) ∈ H0 ⊓ L2 := ⟨hxH0, hxL⟩
    rw [hH0infL] at hmem
    exact hmem
  have hdisjKH : Disjoint K2 H0 := disjoint_iff.mpr hK2H0bot
  obtain ⟨c2⟩ := hD.exists_coordRight hH
  letI := c2.field
  letI := c2.fintype
  obtain ⟨eK, -⟩ := exists_mulEquiv_of_complement (L := L2) (Q := Q2) (K := K2)
    c2.α c2.surj (pCoreOf_le 2 L2) hK2L c2.ker hsupQK hinfQK
  have hK2cardSL : Nat.card K2 = Nat.card (Matrix.SpecialLinearGroup (Fin 2) c2.F) :=
    Nat.card_congr eK.toEquiv
  have hK2card : Nat.card K2 = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [hK2cardSL, CFSG.GorensteinWalter.sl2_card_formula, c2.card]
  have hcardKH : Nat.card ↥(K2 ⊔ H0) =
      2 ^ f * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer K2 H0 hH0NK
      hdisjKH, hK2card, hH0card]
    rw [show 2 ^ (3 * f) = (2 ^ f) ^ 3 from by rw [← pow_mul, Nat.mul_comm]]
  exact hcardKH

theorem D4qLocalData.vertexTwo_right (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (d : TrialityD4Data X (2 ^ f))
    (ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(Subgroup.normalizer (d.V : Set X)))
    (hψS : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔ (ψ x : X) ∈ d.S)
    (hψH : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔ (ψ x : X) ∈ d.J) :
    (pCoreOf 2 L2 ⊔ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) :
        Set G)) = L2 ∧
      pCoreOf 2 L2 ⊓ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) :
        Set G)) = ⊥) ∧
    H ⊓ L2 ≤ (L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ∧
    pCoreOf 2 L2 ⊔ ((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) :
        Set G)) ⊔ (H ⊓ trivOTwoQuot L2)) = L2 ⊔ bigB L1 L2 S ∧
    Disjoint (pCoreOf 2 L2)
      ((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L2)) ∧
    ((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L2)) ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) ∧
    (∀ r ∈ ((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L2)), (∀ x ∈ pCoreOf 2 L2, r * x = x * r) → r = 1) ∧
    Nat.card ↥(((L2 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L2 : Subgroup G) : Set G)) ⊔
      (H ⊓ trivOTwoQuot L2))) = 2 ^ f * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := by
  classical
  set Q2 : Subgroup G := pCoreOf 2 L2 with hQ2
  set H0 : Subgroup G := H ⊓ trivOTwoQuot L2 with hH0
  set K2 : Subgroup G := L2 ⊓ Subgroup.centralizer (H0 : Set G) with hK2
  have hH0B : H0 ≤ bigB L1 L2 S := inf_le_left.trans hHB
  have hK2L : K2 ≤ L2 := inf_le_left
  have hTR := hD.torus_right_of_hall hf hH h1 hHB hSH hSinfH hHcard hHcomm
  have hH0card : Nat.card H0 = 2 ^ (3 * f) - 1 := hTR.2.1
  have hH0infL : H0 ⊓ L2 = ⊥ := hTR.2.2.2.1
  have hL2B : L2 ⊔ bigB L1 L2 S = L2 ⊔ H0 := hTR.2.2.2.2
  have hBNL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (hD.bigB_le_normalizer hH h1).trans (inf_le_left.trans inf_le_right)
  obtain ⟨⟨hsupQK, hinfQK⟩, hHle⟩ :=
    vertexTwo_complement hf hH hD h1 hHB hSH hSinfH hHcard hHcomm d ψ hψS hψH
  have hsupKH : Q2 ⊔ (K2 ⊔ H0) = L2 ⊔ bigB L1 L2 S := by
    rw [← sup_assoc, hsupQK]
    exact hL2B.symm
  have hdisjQ : Disjoint Q2 (K2 ⊔ H0) :=
    vertexTwo_disjoint hH hD h1 hHB hHcomm hsupQK hinfQK hH0infL
  have hNorm : K2 ⊔ H0 ≤ Subgroup.normalizer (Q2 : Set G) :=
    sup_le (hK2L.trans (le_normalizer_pCoreOf 2 L2))
      (hH0B.trans hH.bigB_le_normalizer_pCoreOf_right)
  have hFaith : ∀ r ∈ K2 ⊔ H0, (∀ x ∈ Q2, r * x = x * r) → r = 1 :=
    vertexTwo_faithful hH hD h1 hHB hdisjQ
  have hH0NL2 : H0 ≤ Subgroup.normalizer (L2 : Set G) := hH0B.trans hBNL2
  have hH0cent : H0 ≤ Subgroup.centralizer (H0 : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hHcomm h (Subgroup.mem_inf.mp hh).1 k (Subgroup.mem_inf.mp hk).1).symm
  have hH0Cnorm : H0 ≤ Subgroup.normalizer (Subgroup.centralizer (H0 : Set G) : Set G) :=
    hH0cent.trans Subgroup.le_normalizer
  have hH0NK : H0 ≤ Subgroup.normalizer (K2 : Set G) := by
    have h := (le_inf hH0NL2 hH0Cnorm).trans Subgroup.inf_normalizer_le_normalizer_inf
    simpa [hK2] using h
  have hcardKH := vertexTwo_card hH hD hsupQK hinfQK hH0card hH0infL hH0NK
  exact ⟨⟨hsupQK, hinfQK⟩, hHle, hsupKH, hdisjQ, hNorm, hFaith, hcardKH⟩

end CFSG.Quasithin.F112R.St84

end
