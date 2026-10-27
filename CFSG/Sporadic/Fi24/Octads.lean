module

public import Certificates.Certificate7023
public import Certificates.Certificate7059

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native CFSG.Perm CFSG.Perm.Native CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] rAction

theorem octad_facts :
    OctadFacts :=
  Certificates.certificate7059

theorem bbarData_inj : ∀ i < 24, ∀ j < 24, bbarData[i]! = bbarData[j]! → i = j := by decide

@[expose] noncomputable def bbar
    (i : Fin 24) :
    R := cls (bbarPt i)

theorem bbarPt_injective : Function.Injective bbarPt := fun i j h =>
  Fin.ext (bbarData_inj i.val i.isLt j.val j.isLt (congrArg Fin.val h))

theorem bbar_injective :
    Function.Injective bbar := fun _ _ h =>
  bbarPt_injective (cls_injective h)

theorem bbar_sq (i : Fin 24) :
    bbar i * bbar i = 1 := cls_mul_cls _

theorem bbar_comm
    (i j : Fin 24) :
    bbar i * bbar j = bbar j * bbar i := octad_facts.comm i j

theorem bbar_pair
    (i j k l : Fin 24)
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) : bbar i * bbar j ≠ bbar k * bbar l :=
  octad_facts.pair i j k l hij hkl hik hil hjk hjl

theorem prod_octO0 :
    (octO0.map (bbar ∘ toFin24)).prod = 1 :=
  eq_one_of_smul_eq octad_facts.prod

@[expose] noncomputable def normElt
    (l : Fin 2) : R :=
  (octad_facts.norm l).choose

theorem realizes_normElt
    (l : Fin 2) :
    Realizes bbar (normElt l) (permE l) :=
  (octad_facts.norm l).choose_spec

theorem octad_comb : (∀ k, (octF k).card = 8) ∧
    (∀ k k', k ≠ k' → (octF k ∩ octF k').card ≤ 4) ∧
    (∀ k : Fin 759, k.val ≠ 0 →
      (octParF k).val < k.val ∧ octF k = (octF (octParF k)).image (permF (octLabF k))) ∧
    octF 0 = (Finset.univ.filter fun i => permF 0 i = i) ∧
    octF 0 = (octO0.map toFin24).toFinset :=
  Certificates.certificate7023

theorem octF_card : ∀ k, (octF k).card = 8 := octad_comb.1

theorem octF_inter :
    ∀ k k', k ≠ k' → (octF k ∩ octF k').card ≤ 4 := octad_comb.2.1

theorem octF_tree : ∀ k : Fin 759, k.val ≠ 0 →
    (octParF k).val < k.val ∧ octF k = (octF (octParF k)).image (permF (octLabF k)) :=
  octad_comb.2.2.1

theorem octF_zero_fix :
    octF 0 = Finset.univ.filter fun i => permF 0 i = i := octad_comb.2.2.2.1

theorem octF_zero_eq :
    octF 0 = (octO0.map toFin24).toFinset := octad_comb.2.2.2.2

theorem octO0_nodup : (octO0.map toFin24).Nodup := by decide

theorem permF_zero_invol : ∀ i, permF 0 (permF 0 i) = i := by decide

theorem octF_injective : Function.Injective octF := by
  intro k k' h
  by_contra hne
  have := octF_inter k k' hne
  rw [h, Finset.inter_self, octF_card] at this
  omega

theorem card_octads : octads.card = 759 := by
  rw [octads, Finset.card_image_of_injective _ octF_injective, Finset.card_univ, Fintype.card_fin]

theorem card_of_mem_octads {O : Finset (Fin 24)} (hO : O ∈ octads) :
    O.card = 8 := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hO
  exact octF_card k

theorem inter_of_mem_octads {O O' : Finset (Fin 24)}
    (hO : O ∈ octads) (hO' : O' ∈ octads)
    (hne : O ≠ O') : (O ∩ O').card ≤ 4 := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hO
  obtain ⟨k', -, rfl⟩ := Finset.mem_image.1 hO'
  exact octF_inter k k' fun h => hne (h ▸ rfl)

theorem steiner_octads :
    ∀ Y : Finset (Fin 24), Y.card = 5 → ∃! O, O ∈ octads ∧ Y ⊆ O :=
  steiner_of_inter octads (fun _ hO => card_of_mem_octads hO)
    (fun _ hO _ hO' hne => inter_of_mem_octads hO hO' hne)
    (by rw [card_octads, Fintype.card_fin]; decide)

theorem octF_mem (k : Fin 759) : octF k ∈ octads := Finset.mem_image_of_mem _ (Finset.mem_univ k)

theorem image_permF (l : Fin 2) (S : Finset (Fin 24)) :
    S.image (permF l) = S.map (permE l).toEmbedding := by
  rw [Finset.map_eq_image]
  rfl

theorem htrans_octads :
    ∀ O ∈ octads,
    ∃ r τ, Realizes bbar r τ ∧ O = (octF 0).map (Equiv.toEmbedding τ) := by
  have h := @exists_realizes_of_tree R inferInstance (Fin 24) bbar 758 2 octF octParF octLabF
    permE normElt realizes_normElt fun k hk => by
      obtain ⟨h1, h2⟩ := octF_tree k hk
      exact ⟨h1, h2.trans (image_permF _ _)⟩
  intro O hO
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hO
  exact h k

theorem permE_zero_mul_self : permE 0 * permE 0 = 1 := by
  ext i
  rw [Equiv.Perm.mul_apply, permE_apply, permE_apply, permF_zero_invol, Equiv.Perm.one_apply]

theorem fix_permE_zero :
    (Finset.univ.filter fun i => permE 0 i = i) = octF 0 := by
  rw [octF_zero_fix]
  rfl

theorem famProd_octF_zero :
    @famProd R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm (octF 0) = 1 := by
  rw [octF_zero_eq, @famProd_toFinset R inferInstance (Fin 24) inferInstance inferInstance bbar
    bbar_comm _ octO0_nodup, List.map_map]
  exact prod_octO0

@[expose] noncomputable def Bbar :
    Set R := Set.range bbar

theorem Bbar_subset_D24 :
    Bbar ⊆ D24 := by
  rintro _ ⟨i, rfl⟩
  exact cls_mem _

theorem ncard_Bbar :
    Bbar.ncard = 24 := by
  rw [Bbar, Set.ncard_range_of_injective bbar_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem Bbar_commute :
    ∀ x ∈ Bbar, ∀ y ∈ Bbar, x * y = y * x := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact bbar_comm i j

theorem ncard_fixSets_Bbar :
    (fixSets (inducedPerms Bbar) 8).ncard = 759 := by
  rw [Bbar, @ncard_fixSets_range R inferInstance (Fin 24) inferInstance inferInstance bbar
    bbar_comm bbar_sq bbar_injective bbar_pair octads
    (fun _ hO => card_of_mem_octads hO) steiner_octads (octF 0) (octF_mem 0) famProd_octF_zero
    htrans_octads (normElt 0) (permE 0) (realizes_normElt 0) permE_zero_mul_self fix_permE_zero,
    card_octads]

end CFSG.Sporadic.Fi24
