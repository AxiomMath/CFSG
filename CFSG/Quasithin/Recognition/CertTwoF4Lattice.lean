module

public import CFSG.Quasithin.Recognition.CertTwoF4Pi
public import CFSG.Quasithin.Recognition.CertIndexTwoLattice
public import CFSG.Quasithin.Recognition.CertTitsTwoLocal

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Sporadic.Schreier.Tits

theorem titsD_overgroups_ambient
    (Y : Subgroup (Equiv.Perm (Fin 1755))) (hS : titsS ≤ Y)
    (hD : Y ≤ titsD) : Y = titsS ∨ Y = titsH ∨ Y = titsN ∨ Y = titsD := by
  have hX : titsSD ≤ Y.subgroupOf titsD := fun _ hx => hS hx
  rcases titsD_overgroups _ hX with h | h | h | h
  · left
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hD, inf_eq_left.2 titsS_le_titsD] at this
  · right; left
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hD, inf_eq_left.2 titsH_le_titsD] at this
  · right; right; left
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hD, inf_eq_left.2 titsN_le_titsD] at this
  · right; right; right
    exact le_antisymm hD (Subgroup.subgroupOf_eq_top.1 h)

theorem tπ_sq_S
    : tπ * tπ ∈ titsS := titsJ_le_titsS tπ_sq_J

theorem tπ_sq_H
    : tπ * tπ ∈ titsH := titsS_le_titsH tπ_sq_S

theorem tπ_sq_N
    : tπ * tπ ∈ titsN := titsS_le_titsN tπ_sq_S

section Translate

variable {G : Type*} [Group G] {M A : Subgroup G}

theorem eq_subgroupOf_of_map_eq (X : Subgroup M) (hA : A ≤ M) (h : X.map M.subtype = A) :
    X = A.subgroupOf M :=
  Subgroup.map_injective M.subtype_injective (h.trans (Subgroup.map_subgroupOf_eq_of_le hA).symm)

theorem mem_normalizer_subgroupOf {g : M} (h : (g : G) ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  exact Subgroup.mem_normalizer_iff.1 h (m : G)

theorem subgroupOf_le_iff {B : Subgroup G} (hA : A ≤ M) :
    A.subgroupOf M ≤ B.subgroupOf M ↔ A ≤ B :=
  ⟨fun h x hx => h (show (⟨x, hA hx⟩ : M) ∈ A.subgroupOf M from hx), fun h _ hx => h hx⟩

end Translate

@[expose] def twoF4M
    : Subgroup (Equiv.Perm (Fin 1755)) := extSub titsD tπ tπ_norm_D tπ_sq_D

theorem titsD_le_twoF4M
    : titsD ≤ twoF4M := le_extSub

theorem tπ_mem_twoF4M
    : tπ ∈ twoF4M := q_mem_extSub

@[expose] def twoF4Q
    : twoF4M := ⟨tπ, tπ_mem_twoF4M⟩

theorem index_titsD_twoF4M
    : (titsD.subgroupOf twoF4M).index = 2 :=
  relIndex_extSub tπ_not_mem_D

theorem titsS_le_twoF4M
    : titsS ≤ twoF4M := titsS_le_titsD.trans titsD_le_twoF4M

theorem titsH_le_twoF4M
    : titsH ≤ twoF4M := titsH_le_titsD.trans titsD_le_twoF4M

theorem titsN_le_twoF4M
    : titsN ≤ twoF4M := titsN_le_titsD.trans titsD_le_twoF4M

theorem titsJ_le_twoF4M
    : titsJ ≤ twoF4M := titsJ_le_titsD.trans titsD_le_twoF4M

theorem titsK_le_twoF4M
    : titsK ≤ twoF4M := titsK_le_titsD.trans titsD_le_twoF4M

theorem twoF4_lattice
    (X : Subgroup ↥twoF4M) (hS : titsS.subgroupOf twoF4M ≤ X)
    (hD : X ≤ titsD.subgroupOf twoF4M) :
    X = titsS.subgroupOf twoF4M ∨ X = titsH.subgroupOf twoF4M ∨ X = titsN.subgroupOf twoF4M ∨
      X = titsD.subgroupOf twoF4M := by
  have hS' : titsS ≤ X.map twoF4M.subtype := fun x hx =>
    ⟨⟨x, titsS_le_twoF4M hx⟩, hS (show (⟨x, titsS_le_twoF4M hx⟩ : twoF4M) ∈
      titsS.subgroupOf twoF4M from hx), rfl⟩
  have hD' : X.map twoF4M.subtype ≤ titsD := by
    rintro _ ⟨y, hy, rfl⟩
    exact hD hy
  rcases titsD_overgroups_ambient _ hS' hD' with h | h | h | h
  · exact Or.inl (eq_subgroupOf_of_map_eq X titsS_le_twoF4M h)
  · exact Or.inr (Or.inl (eq_subgroupOf_of_map_eq X titsH_le_twoF4M h))
  · exact Or.inr (Or.inr (Or.inl (eq_subgroupOf_of_map_eq X titsN_le_twoF4M h)))
  · exact Or.inr (Or.inr (Or.inr (eq_subgroupOf_of_map_eq X titsD_le_twoF4M h)))

theorem card_titsS_ne_titsH
    : Nat.card titsS ≠ Nat.card titsH := by
  rw [titsQS_facts.2.2.2, titsQH_facts.2.2.2]
  omega

theorem card_titsS_ne_titsN
    : Nat.card titsS ≠ Nat.card titsN := by
  rw [titsQS_facts.2.2.2, titsQN_facts.2.2.2]
  omega

theorem titsS_ne_titsH'
    : titsS.subgroupOf twoF4M ≠ titsH.subgroupOf twoF4M := fun h => by
  have h1 := Subgroup.subgroupOf_inj.1 h
  rw [inf_eq_left.2 titsS_le_twoF4M, inf_eq_left.2 titsH_le_twoF4M] at h1
  exact card_titsS_ne_titsH (by rw [h1])

theorem titsS_ne_titsN'
    : titsS.subgroupOf twoF4M ≠ titsN.subgroupOf twoF4M := fun h => by
  have h1 := Subgroup.subgroupOf_inj.1 h
  rw [inf_eq_left.2 titsS_le_twoF4M, inf_eq_left.2 titsN_le_twoF4M] at h1
  exact card_titsS_ne_titsN (by rw [h1])

theorem not_titsH_le_titsN'
    : ¬ titsH.subgroupOf twoF4M ≤ titsN.subgroupOf twoF4M := fun h => by
  have := Subgroup.card_dvd_of_le ((subgroupOf_le_iff titsH_le_twoF4M).1 h)
  rw [titsQH_facts.2.2.2, titsQN_facts.2.2.2] at this
  omega

theorem not_titsN_le_titsH'
    : ¬ titsN.subgroupOf twoF4M ≤ titsH.subgroupOf twoF4M := fun h => by
  have := Subgroup.card_dvd_of_le ((subgroupOf_le_iff titsN_le_twoF4M).1 h)
  rw [titsQH_facts.2.2.2, titsQN_facts.2.2.2] at this
  omega

theorem twoF4_sylowS_p
    : IsPGroup 2 (titsS.subgroupOf twoF4M) :=
  IsPGroup.of_card (n := 11) (by
    rw [card_subgroupOf_eq titsS_le_twoF4M, titsQS_facts.2.2.2]
    norm_num)

theorem twoF4_sylowS_idx :
    ¬ 2 ∣ ((titsS.subgroupOf twoF4M).subgroupOf (titsD.subgroupOf twoF4M)).index := by
  have h := Subgroup.relIndex_subgroupOf (H := titsS) (K := titsD) (L := twoF4M) titsD_le_twoF4M
  change ¬ 2 ∣ (titsS.subgroupOf twoF4M).relIndex (titsD.subgroupOf twoF4M)
  rw [h]
  change ¬ 2 ∣ (titsS.subgroupOf titsD).index
  rw [titsS_index]
  decide

theorem twoF4_normS
    (x : twoF4M) (hx : x ∈ titsD.subgroupOf twoF4M)
    (hn : x ∈ Subgroup.normalizer ((titsS.subgroupOf twoF4M : Subgroup twoF4M) : Set twoF4M)) :
    x ∈ titsS.subgroupOf twoF4M := by
  have hxD : (x : Equiv.Perm (Fin 1755)) ∈ titsD := hx
  have h1 : (⟨x.1, hxD⟩ : titsD) ∈ Subgroup.normalizer (titsSD : Set titsD) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact Subgroup.mem_normalizer_iff.1 hn ⟨y.1, titsD_le_twoF4M y.2⟩
  exact titsSD_normalizer_le h1

theorem twoF4_noNormal
    (Q : Subgroup twoF4M) (hQ : Q.Normal)
    (hQD : Q ≤ titsD.subgroupOf twoF4M) (hp : IsPGroup 2 Q) : Q = ⊥ := by
  let ι : titsD →* twoF4M := Subgroup.inclusion titsD_le_twoF4M
  have hQ' : (Q.comap ι).Normal := hQ.comap ι
  have hp' : IsPGroup 2 (Q.comap ι) := hp.comap_of_injective ι (Subgroup.inclusion_injective _)
  have h := titsD_no_normal_two_subgroup _ hQ' hp'
  rw [eq_bot_iff]
  intro x hx
  have hxD : (x : Equiv.Perm (Fin 1755)) ∈ titsD := hQD hx
  have h2 : (⟨x.1, hxD⟩ : titsD) ∈ Q.comap ι := hx
  rw [h] at h2
  have h3 : (⟨x.1, hxD⟩ : titsD) = 1 := Subgroup.mem_bot.1 h2
  have h5 := congrArg Subtype.val h3
  have h4 : x = 1 := Subtype.ext h5
  rw [h4]
  exact Subgroup.one_mem _

theorem twoF4_centD
    (x : twoF4M) (h : ∀ d ∈ titsD.subgroupOf twoF4M, x * d = d * x) : x = 1 :=
  Subtype.ext (centralizer_titsD_eq_one x.1 fun g hg =>
    congrArg Subtype.val (h ⟨g, titsD_le_twoF4M hg⟩ hg))

theorem twoF4_loc₁
    : ∃ Q : Subgroup twoF4M, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
    titsH.subgroupOf twoF4M ≤ Subgroup.normalizer (Q : Set twoF4M) ∧
    twoF4Q ∈ Subgroup.normalizer (Q : Set twoF4M) := by
  obtain ⟨-, -, -, -, -, -, hJn, -⟩ := AT_Tits_intrinsic_local_pair
  have hHJ : titsH ≤ Subgroup.normalizer (titsJ : Set (Equiv.Perm (Fin 1755))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer titsJ_le_titsH).1 hJn
  refine ⟨titsJ.subgroupOf twoF4M, ?_, ?_, fun h hh => mem_normalizer_subgroupOf (hHJ hh),
    mem_normalizer_subgroupOf tπ_norm_J⟩
  · intro h
    have h1 := card_subgroupOf_eq titsJ_le_twoF4M
    rw [h, Subgroup.card_bot, titsQJ_facts.2.2.2] at h1
    omega
  · exact IsPGroup.of_card (n := 9) (by
      rw [card_subgroupOf_eq titsJ_le_twoF4M, titsQJ_facts.2.2.2]
      norm_num)

theorem twoF4_loc₂
    : ∃ Q : Subgroup twoF4M, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
    titsN.subgroupOf twoF4M ≤ Subgroup.normalizer (Q : Set twoF4M) ∧
    twoF4Q ∈ Subgroup.normalizer (Q : Set twoF4M) := by
  obtain ⟨-, -, -, -, -, -, -, hKn, -⟩ := AT_Tits_intrinsic_local_pair
  have hNK : titsN ≤ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer titsK_le_titsN).1 hKn
  refine ⟨titsK.subgroupOf twoF4M, ?_, ?_, fun h hh => mem_normalizer_subgroupOf (hNK hh),
    mem_normalizer_subgroupOf tπ_norm_K⟩
  · intro h
    have h1 := card_subgroupOf_eq titsK_le_twoF4M
    rw [h, Subgroup.card_bot, titsQK_facts.2.2.2] at h1
    omega
  · exact IsPGroup.of_card (n := 10) (by
      rw [card_subgroupOf_eq titsK_le_twoF4M, titsQK_facts.2.2.2]
      norm_num)

@[expose] def twoF4Data
    : IndexTwoLatticeData ↥twoF4M where
  D := titsD.subgroupOf twoF4M
  S := titsS.subgroupOf twoF4M
  P₁ := titsH.subgroupOf twoF4M
  P₂ := titsN.subgroupOf twoF4M
  q := twoF4Q
  D_normal := Subgroup.normal_of_index_eq_two index_titsD_twoF4M
  D_index := index_titsD_twoF4M
  q_not_mem := by
    rw [show twoF4Q = ⟨tπ, tπ_mem_twoF4M⟩ from rfl, Subgroup.mem_subgroupOf]
    exact tπ_not_mem_D
  S_le_P₁ := fun _ hx => titsS_le_titsH hx
  S_le_P₂ := fun _ hx => titsS_le_titsN hx
  P₁_le_D := fun _ hx => titsH_le_titsD hx
  P₂_le_D := fun _ hx => titsN_le_titsD hx
  lattice := twoF4_lattice
  S_ne_P₁ := titsS_ne_titsH'
  S_ne_P₂ := titsS_ne_titsN'
  P₁_not_le_P₂ := not_titsH_le_titsN'
  P₂_not_le_P₁ := not_titsN_le_titsH'
  sylowS_p := twoF4_sylowS_p
  sylowS_idx := twoF4_sylowS_idx
  normS := twoF4_normS
  noNormal := twoF4_noNormal
  centD := twoF4_centD
  q_norm_S := mem_normalizer_subgroupOf tπ_norm_S
  q_norm_P₁ := mem_normalizer_subgroupOf tπ_norm_H
  q_norm_P₂ := mem_normalizer_subgroupOf tπ_norm_N
  loc₁ := twoF4_loc₁
  loc₂ := twoF4_loc₂

@[expose] def twoF4Lattice
    : TwoLocalLattice ↥twoF4M := twoF4Data.toLattice

end CFSG.Quasithin
