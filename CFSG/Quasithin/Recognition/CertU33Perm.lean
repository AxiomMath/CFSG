module

public import CFSG.Quasithin.Recognition.CertU33Pres
public import CFSG.Quasithin.Recognition.CertChain
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertU33PermInputs
public import Certificates.Certificate8080
public import Certificates.Certificate8081

public section

namespace CFSG.Quasithin

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def u33Img : Fin 5 → Equiv.Perm (Fin 28)
  | 0 => List.formPerm [0, 14, 13, 15] * List.formPerm [1, 20, 25, 9] *
      List.formPerm [2, 27, 22, 11] * List.formPerm [3, 6, 16, 26] *
      List.formPerm [4, 7, 19, 10] * List.formPerm [8, 18, 23, 21]
  | 1 => List.formPerm [0, 7, 9, 8] * List.formPerm [1, 18, 14, 19] *
      List.formPerm [2, 11, 22, 27] * List.formPerm [4, 25, 21, 15] *
      List.formPerm [5, 24, 12, 17] * List.formPerm [10, 20, 23, 13]
  | 2 => List.formPerm [1, 10] * List.formPerm [2, 11] * List.formPerm [3, 12] *
      List.formPerm [4, 18] * List.formPerm [5, 16] * List.formPerm [6, 17] *
      List.formPerm [7, 14] * List.formPerm [8, 15] * List.formPerm [9, 13] *
      List.formPerm [22, 27] * List.formPerm [23, 25] * List.formPerm [24, 26]
  | 3 => List.formPerm [0, 1, 10] * List.formPerm [2, 26, 12] * List.formPerm [3, 24, 11] *
      List.formPerm [4, 21, 18] * List.formPerm [5, 22, 6] * List.formPerm [7, 20, 14] *
      List.formPerm [8, 9, 25] * List.formPerm [13, 15, 23] * List.formPerm [16, 17, 27]
  | 4 => List.formPerm [0, 12, 10] * List.formPerm [1, 13, 6] * List.formPerm [2, 27, 22] *
      List.formPerm [3, 7, 18] * List.formPerm [4, 16, 23] * List.formPerm [5, 8, 20] *
      List.formPerm [9, 26, 15] * List.formPerm [14, 21, 24] * List.formPerm [17, 25, 19]

theorem u33Chain_check :
    u33Gens.size = 5 ∧ CFSG.YGroups.ModelNative.permsOK 28 u33Gens = true ∧
    u33Gens.size ≤ u33Strong.size ∧ (∀ i < u33Gens.size, u33Strong[i]! = u33Gens[i]!) ∧
    rawChainOK 28 (u33Strong.extract 0 u33Gens.size) u33Strong (u33Base.map Fin.val).toArray
      u33RawWords 1 = true ∧
    rawOrbitSizes 28 u33Strong (u33Base.map Fin.val).toArray = [28, 27, 2, 4] :=
  Certificates.certificate8080

theorem u33Gens_rep : ∀ i : Fin 5, ∀ x : Fin 28, (u33Gens[(i : ℕ)]!)[(x : ℕ)]! = (u33Img i x : ℕ) := by
  decide +kernel

theorem u33Img_relators : ∀ w ∈ u33PresRels,
    (w.map fun l => cond l.2 (u33Img l.1) (u33Img l.1)⁻¹).prod = 1 := by
  decide +kernel

noncomputable def u33PresHom : PG 5 u33PresRels →* Equiv.Perm (Fin 28) :=
  PresentedGroup.toGroup (f := u33Img) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact u33Img_relators w hw)

theorem u33PresHom_of (i : Fin 5) : u33PresHom (PresentedGroup.of i) = u33Img i := by
  rw [u33PresHom, PresentedGroup.toGroup.of]

private theorem u33Base_nodup : u33Base.Nodup := by decide

theorem permOfArr_u33Gens
    (k : Fin 5) : permOfArr 28 u33Gens[(k : ℕ)]! = u33Img k := by
  obtain ⟨hsz, hperms, -⟩ := u33Chain_check
  have hinv : isInvA 28 u33Gens[(k : ℕ)]! (invCand 28 u33Gens[(k : ℕ)]!) = true :=
    allLt_spec hperms (by rw [hsz]; exact k.2)
  exact (rep_permOfArr hinv).1.unique (u33Gens_rep k)

theorem range_u33PresHom : u33PresHom.range = Subgroup.closure
    {g | ∃ k < u33Gens.size, permOfArr 28 u33Gens[k]! = g} := by
  obtain ⟨hsz, -⟩ := u33Chain_check
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    {r : FreeGroup (Fin 5) | r ∈ u33PresRels.map FreeGroup.mk}, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [hsz]; exact i.2, by rw [u33PresHom_of, permOfArr_u33Gens]⟩
  · rintro ⟨k, hk, rfl⟩
    rw [hsz] at hk
    exact ⟨_, ⟨⟨k, hk⟩, rfl⟩, by rw [u33PresHom_of, ← permOfArr_u33Gens ⟨k, hk⟩]⟩

theorem card_u33Perm :
    Nat.card (Subgroup.closure {g | ∃ k < u33Gens.size, permOfArr 28 u33Gens[k]! = g} :
      Subgroup (Equiv.Perm (Fin 28))) = 6048 := by
  obtain ⟨-, -, hOS, hSO, hchain, horb⟩ := u33Chain_check
  have hc := card_closure_permOfArr_of_rawChainOK (n := 28) (by norm_num) (O := u33Gens)
    (S := u33Strong) (W := u33RawWords) u33Base_nodup (chunks := 1) (by norm_num) hOS hSO hchain
  rw [horb] at hc
  rw [hc]
  norm_num

theorem card_u33Pres :
    Nat.card (PG 5 u33PresRels) = 6048 := by
  obtain ⟨hfin, hle⟩ := u33Pres_finite_card_le
  have h1 : Nat.card u33PresHom.range ≤ Nat.card (PG 5 u33PresRels) :=
    Nat.card_le_card_of_surjective _ u33PresHom.rangeRestrict_surjective
  rw [range_u33PresHom, card_u33Perm] at h1
  omega

theorem u33PresHom_injective :
    Function.Injective u33PresHom := by
  obtain ⟨hfin, hle⟩ := u33Pres_finite_card_le
  have hbij : Function.Bijective u33PresHom.rangeRestrict :=
    u33PresHom.rangeRestrict_surjective.bijective_of_nat_card_le (by
      rw [range_u33PresHom, card_u33Perm]; exact hle)
  intro x y hxy
  exact hbij.1 (Subtype.ext hxy)

theorem u33Pres_mulEquiv_perm :
    Nonempty (PG 5 u33PresRels ≃*
    (Subgroup.closure {g | ∃ k < u33Gens.size, permOfArr 28 u33Gens[k]! = g} :
      Subgroup (Equiv.Perm (Fin 28)))) := by
  obtain ⟨hfin, hle⟩ := u33Pres_finite_card_le
  exact ⟨(MulEquiv.ofBijective u33PresHom.rangeRestrict
    (u33PresHom.rangeRestrict_surjective.bijective_of_nat_card_le (by
      rw [range_u33PresHom, card_u33Perm]; exact hle))).trans
    (MulEquiv.subgroupCongr range_u33PresHom)⟩

end CFSG.Quasithin
