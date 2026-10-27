module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ECode
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Out
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Fi24Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open Subgroup CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Fi24 CFSG.Sporadic.Mathieu
  CFSG.Fischer CFSG.EvenSporadicStandard.TwoFi22.DS81

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "bP" => @famProd R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm

private theorem ncard_card_eq (k : ℕ) :
    {T : Finset (Fin 24) | T.card = k}.ncard = Nat.choose 24 k := by
  rw [show {T : Finset (Fin 24) | T.card = k} =
      (Finset.powersetCard k (Finset.univ : Finset (Fin 24)) : Set (Finset (Fin 24))) by
    ext T
    rw [Finset.mem_coe, Finset.mem_powersetCard_univ, Set.mem_setOf_eq],
    Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private theorem ncard_tetrads : {T : Finset (Fin 24) | T.card = 4 ∧ 0 ∈ T}.ncard = 1771 := by
  have e : {T : Finset (Fin 24) | T.card = 4 ∧ 0 ∈ T} =
      insert 0 '' (Finset.powersetCard 3 ((Finset.univ : Finset (Fin 24)).erase 0) :
        Set (Finset (Fin 24))) := by
    ext T
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Finset.mem_powersetCard]
    constructor
    · rintro ⟨h4, h0⟩
      refine ⟨T.erase 0, ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩,
        Finset.insert_erase h0⟩
      rw [Finset.card_erase_of_mem h0, h4]
    · rintro ⟨U, ⟨hU, h3⟩, rfl⟩
      have h0 : 0 ∉ U := fun h => (Finset.mem_erase.1 (hU h)).1 rfl
      exact ⟨by rw [Finset.card_insert_of_notMem h0, h3], Finset.mem_insert_self _ _⟩
  have hinj : Set.InjOn (insert 0)
      (Finset.powersetCard 3 ((Finset.univ : Finset (Fin 24)).erase 0) :
        Set (Finset (Fin 24))) := by
    intro U hU V hV h
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU hV
    have hU0 : (0 : Fin 24) ∉ U := fun h => (Finset.mem_erase.1 (hU.1 h)).1 rfl
    have hV0 : (0 : Fin 24) ∉ V := fun h => (Finset.mem_erase.1 (hV.1 h)).1 rfl
    rw [← Finset.erase_insert hU0, ← Finset.erase_insert hV0, h]
  rw [e, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  rfl

section Elt


@[expose] noncomputable def fi24EOf (S : Finset (Fin 24)) (hS : Even S.card) : CFSG.Sporadic.Fi24.J :=
  ⟨(bP S : R), (mem_JR_iff _).1 ((bbarProd_mem_JR_iff S).2 hS)⟩

theorem jR_fi24EOf (S : Finset (Fin 24)) (hS : Even S.card) : jR (fi24EOf S hS) = bP S :=
  Subtype.ext (coe_jR _)

theorem fi24EOf_mem (S : Finset (Fin 24)) (hS : Even S.card) : fi24EOf S hS ∈ fi24E := by
  rw [mem_fi24E_iff, jR_fi24EOf]
  exact bbarProd_mem S

@[expose] noncomputable def fi24Et : CFSG.Sporadic.Fi24.J := fi24EOf {0, 1} (by decide)

@[expose] noncomputable def fi24Ey : CFSG.Sporadic.Fi24.J := fi24EOf {0, 1, 2, 3} (by decide)


theorem jR_conj_eq {n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)} {x : CFSG.Sporadic.Fi24.J} {S : Finset (Fin 24)}
    (hx : jR x = bP S) : jR ((n : CFSG.Sporadic.Fi24.J) * x * (n : CFSG.Sporadic.Fi24.J)⁻¹) = bP (S.map (fi24Pi n).toEmbedding) := by
  rw [@famProd_map R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm
    (fi24Pi n) (jR n) (realizes_fi24Pi n) S, map_mul, map_mul, map_inv, hx]

end Elt

section Rel


theorem fi24Et_ne_one : fi24Et ≠ 1 := fun h => by
  have e := congrArg jR h
  rw [fi24Et, jR_fi24EOf, map_one] at e
  exact bbarProd_ne_one (Or.inl (by decide)) e

theorem fi24Ey_ne_one : fi24Ey ≠ 1 := fun h => by
  have e := congrArg jR h
  rw [fi24Ey, jR_fi24EOf, map_one] at e
  exact bbarProd_ne_one (Or.inr (Or.inl (by decide))) e

theorem exists_card_le_four (S : Finset (Fin 24)) :
    ∃ T : Finset (Fin 24), T.card ≤ 4 ∧ bP T = bP S := by
  suffices h : ∀ m, ∀ S : Finset (Fin 24), S.card = m →
      ∃ T : Finset (Fin 24), T.card ≤ 4 ∧ bP T = bP S from h _ S rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hS
    by_cases hm : m ≤ 4
    · exact ⟨S, hS.le.trans hm, rfl⟩
    obtain ⟨Y, hYS, hY⟩ := Finset.exists_subset_card_eq (show 5 ≤ S.card by omega)
    obtain ⟨O, hO, hYO⟩ := exists_octad_of_card_five hY
    have hc := card_symmDiff_add_two_mul S O
    have hi := Finset.card_le_card (Finset.subset_inter hYS hYO)
    rw [card_of_mem_octads hO] at hc
    obtain ⟨T, hT, hTe⟩ := ih _ (by omega) (symmDiff S O) rfl
    exact ⟨T, hT, by rw [hTe, bbarProd_symmDiff, bbarProd_octad hO, mul_one]⟩

theorem exists_zero_mem {S : Finset (Fin 24)} (hS : S.card = 4) :
    ∃ T : Finset (Fin 24), (T.card = 4 ∧ 0 ∈ T) ∧ bP T = bP S := by
  by_cases h0 : (0 : Fin 24) ∈ S
  · exact ⟨S, ⟨hS, h0⟩, rfl⟩
  obtain ⟨O, hO, hSO⟩ := exists_octad_of_card_five (Y := insert 0 S)
    (by rw [Finset.card_insert_of_notMem h0, hS])
  have hS' : S ⊆ O := (Finset.subset_insert 0 S).trans hSO
  refine ⟨O \ S, ⟨?_, Finset.mem_sdiff.2 ⟨hSO (Finset.mem_insert_self 0 S), h0⟩⟩, ?_⟩
  · rw [Finset.card_sdiff_of_subset hS', card_of_mem_octads hO, hS]
  · rw [← symmDiff_of_ge hS', bbarProd_symmDiff, bbarProd_octad hO, one_mul]

theorem injOn_tetrads : Set.InjOn bP {T : Finset (Fin 24) | T.card = 4 ∧ 0 ∈ T} := by
  rintro S ⟨hS, hS0⟩ T ⟨hT, hT0⟩ h
  refine eq_of_bbarProd_eq ?_ h
  have hc := card_symmDiff_add_two_mul S T
  have hi : 0 < (S ∩ T).card := Finset.card_pos.2 ⟨0, Finset.mem_inter.2 ⟨hS0, hT0⟩⟩
  omega

theorem image_tetrads :
    bP '' {T : Finset (Fin 24) | T.card = 4} = bP '' {T | T.card = 4 ∧ 0 ∈ T} := by
  refine le_antisymm ?_ (Set.image_mono fun T hT => hT.1)
  rintro _ ⟨S, hS, rfl⟩
  obtain ⟨T, hT, he⟩ := exists_zero_mem hS
  exact ⟨T, hT, he⟩

theorem exists_fi24Pi_map {S T : Finset (Fin 24)} (hST : S.card = T.card) (h4 : S.card ≤ 4) :
    ∃ n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J), S.map (fi24Pi n).toEmbedding = T := by
  have hlt : ∀ j : Fin S.card, j.val < 24 := fun j => j.isLt.trans_le (h4.trans (by norm_num))
  have key : ∀ U : Finset (Fin 24), ∀ hU : U.card = S.card, ∃ g : NativeSporadic.M24,
      ∀ j : Fin S.card, (g : Equiv.Perm (Fin 24)) ⟨j, hlt j⟩ =
        fi24EC⁻¹ (U.orderEmbOfFin hU j) := by
    intro U hU
    obtain ⟨g, hg⟩ := CFSG.Sporadic.Mathieu.maps m24_hyp S.card (h4.trans (by decide))
      (fun j => if h : j < S.card then fi24EC⁻¹ (U.orderEmbOfFin hU ⟨j, h⟩) else 0) (by
        intro i hi j hj e
        simp only [dif_pos hi, dif_pos (hj.trans hi)] at e
        exact absurd (Fin.mk.inj_iff.1 ((U.orderEmbOfFin hU).injective (fi24EC⁻¹.injective e)))
          (Nat.ne_of_gt hj))
    refine ⟨g, fun j => ?_⟩
    have := hg j.val j.isLt ⟨j.val, hlt j⟩ rfl
    simp only [Subgroup.smul_def, Equiv.Perm.smul_def, dif_pos j.isLt] at this
    exact this
  obtain ⟨g₁, hg₁⟩ := key S rfl
  obtain ⟨g₂, hg₂⟩ := key T hST.symm
  obtain ⟨n, hn⟩ : fi24EC * ((g₂ * g₁⁻¹ : NativeSporadic.M24) : Equiv.Perm (Fin 24)) *
      fi24EC⁻¹ ∈ fi24Pi.range := by
    rw [range_fi24Pi]
    exact ⟨_, (g₂ * g₁⁻¹).2, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  refine ⟨n, ?_⟩
  calc S.map (fi24Pi n).toEmbedding =
        (Finset.univ.image (S.orderEmbOfFin rfl)).map (fi24Pi n).toEmbedding := by
        rw [Finset.image_orderEmbOfFin_univ]
    _ = Finset.univ.image (T.orderEmbOfFin hST.symm) := by
        rw [Finset.map_eq_image, Finset.image_image]
        refine Finset.image_congr fun j _ => ?_
        rw [Function.comp_apply, Equiv.coe_toEmbedding, hn, Subgroup.coe_mul, Subgroup.coe_inv,
          Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hg₁ j,
          Equiv.Perm.coe_inv, Equiv.symm_apply_apply, hg₂ j, Equiv.Perm.coe_inv,
          Equiv.apply_symm_apply]
    _ = T := Finset.image_orderEmbOfFin_univ T hST.symm

theorem image_normClass {x : CFSG.Sporadic.Fi24.J} {S : Finset (Fin 24)} {k : ℕ} (hx : jR x = bP S)
    (hk : S.card = k) (h4 : k ≤ 4) : jR '' normClass fi24E x = bP '' {T | T.card = k} := by
  ext r
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨_, by rw [Set.mem_setOf_eq, Finset.card_map, hk],
      (jR_conj_eq (n := ⟨n, hn⟩) hx).symm⟩
  · rintro ⟨T, (hT : T.card = k), rfl⟩
    obtain ⟨n, hn⟩ := exists_fi24Pi_map (hk.trans hT.symm) (hk.le.trans h4)
    exact ⟨_, ⟨n, n.2, rfl⟩, by rw [jR_conj_eq hx, hn]⟩

theorem image_normClass_fi24Et :
    jR '' normClass fi24E fi24Et = bP '' {T | T.card = 2} :=
  image_normClass (jR_fi24EOf _ _) (by decide) (by norm_num)

theorem image_normClass_fi24Ey :
    jR '' normClass fi24E fi24Ey = bP '' {T | T.card = 4} :=
  image_normClass (jR_fi24EOf _ _) (by decide) (by norm_num)

theorem ncard_normClass_fi24Et : (normClass fi24E fi24Et).ncard = 276 := by
  have hinj : Set.InjOn bP {T : Finset (Fin 24) | T.card = 2} := by
    rintro S (hS : S.card = 2) T (hT : T.card = 2) h
    exact bbarProd_inj (by omega) (by omega) h
  rw [← Set.ncard_image_of_injective _ jR_injective, image_normClass_fi24Et, hinj.ncard_image,
    ncard_card_eq]
  rfl

theorem ncard_normClass_fi24Ey : (normClass fi24E fi24Ey).ncard = 1771 := by
  rw [← Set.ncard_image_of_injective _ jR_injective, image_normClass_fi24Ey, image_tetrads,
    injOn_tetrads.ncard_image, ncard_tetrads]

theorem fi24Ey_not_mem : fi24Ey ∉ normClass fi24E fi24Et := fun h => by
  have h' : jR fi24Ey ∈ jR '' normClass fi24E fi24Et := ⟨_, h, rfl⟩
  rw [image_normClass_fi24Et, fi24Ey, jR_fi24EOf] at h'
  obtain ⟨T, (hT : T.card = 2), hTe⟩ := h'
  have hc := card_symmDiff_add_two_mul T {0, 1, 2, 3}
  have h4 : ({0, 1, 2, 3} : Finset (Fin 24)).card = 4 := by decide
  have e := eq_of_bbarProd_eq (by rw [hT, h4] at hc; omega) hTe
  rw [e] at hT
  exact absurd hT (by decide)

theorem mem_normClass_fi24Ey {w : CFSG.Sporadic.Fi24.J} (hw : w ∈ fi24E) (h1 : w ≠ 1)
    (ht : w ∉ normClass fi24E fi24Et) : w ∈ normClass fi24E fi24Ey := by
  obtain ⟨S, hS⟩ := exists_bbarProd (mem_fi24E_iff.1 hw)
  obtain ⟨T, hT4, hTS⟩ := exists_card_le_four S
  rw [hS] at hTS
  have he : Even T.card := (bbarProd_mem_JR_iff T).1 (by rw [hTS]; exact jR_mem_JR w)
  have hcases : T.card = 0 ∨ T.card = 2 ∨ T.card = 4 := by
    obtain ⟨k, hk⟩ := he
    omega
  rcases hcases with h0 | h2 | h4
  · rw [Finset.card_eq_zero.1 h0, bbarProd_empty] at hTS
    exact absurd (jR_injective (hTS.symm.trans (map_one jR).symm)) h1
  · refine absurd (jR_injective.mem_set_image.1 ?_) ht
    rw [image_normClass_fi24Et]
    exact ⟨T, h2, hTS⟩
  · refine jR_injective.mem_set_image.1 ?_
    rw [image_normClass_fi24Ey]
    exact ⟨T, h4, hTS⟩

theorem m24Out_fi24E : M24Out (↥CFSG.Sporadic.Fi24.J) fi24E fi24Et where
  card_E := card_fi24E
  E_sq := fi24E_sq
  centralizer_eq := centralizer_fi24E
  quotient := quotient_fi24E
  t_mem := fi24EOf_mem _ _
  t_ne_one := fi24Et_ne_one
  ncard_t := ncard_normClass_fi24Et
  rest := ⟨fi24Ey, fi24EOf_mem _ _, fi24Ey_ne_one, fi24Ey_not_mem, ncard_normClass_fi24Ey,
    fun _ hw h1 ht => mem_normClass_fi24Ey hw h1 ht⟩

end Rel

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
