module

public import CFSG.Quasithin.Background.JonesParshallG2Two
public import CFSG.Quasithin.Background.B5FinOutAlt
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Quasithin.Recognition.CertU33Perm
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import CFSG.Quasithin.Background.B5FinG2U33Inputs
public import Certificates.Certificate17002
public import Certificates.Certificate17028
public import Certificates.Certificate17951
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import Certificates.Certificate19953


public section

namespace CFSG.Quasithin

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CosetTable CFSG.Open
open scoped commutatorElement

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

theorem cmat_u33ImgL (i : Fin 5) : cmat (u33ImgL i) = u33Mats i :=
  Certificates.certificate17002.1 i

theorem u33Mats_mul_inv (i : Fin 5) :
    u33Mats i * u33MatsInv i = 1 ∧ u33MatsInv i * u33Mats i = 1 :=
  Certificates.certificate17002.2.1 i

theorem cmat_u33ImgL_inv
    (i : Fin 5) : cmat (u33ImgL i)⁻¹ = u33MatsInv i := by
  calc cmat (u33ImgL i)⁻¹ = (u33MatsInv i * u33Mats i) * cmat (u33ImgL i)⁻¹ := by
        rw [(u33Mats_mul_inv i).2, Matrix.one_mul]
    _ = u33MatsInv i * (cmat (u33ImgL i) * cmat (u33ImgL i)⁻¹) := by
        rw [Matrix.mul_assoc, cmat_u33ImgL]
    _ = u33MatsInv i := by rw [← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]

theorem cmat_u33ImgL_cond (i : Fin 5) (b : Bool) :
    cmat (cond b (u33ImgL i) (u33ImgL i)⁻¹) = cond b (u33Mats i) (u33MatsInv i) := by
  cases b
  · exact cmat_u33ImgL_inv i
  · exact cmat_u33ImgL i

theorem u33Mats_rels : ∀ w ∈ u33PresRels,
    (w.map fun x : Fin 5 × Bool => cond x.2 (u33Mats x.1) (u33MatsInv x.1)).prod = 1 :=
  Certificates.certificate17002.2.2

noncomputable def u33HomL : U33G →* ↥(cayleyGroup (ZMod 2)) :=
  PresentedGroup.toGroup (f := u33ImgL) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    apply cmat_injective
    rw [FreeGroup.lift_mk, map_list_prod, List.map_map, map_one]
    have hl : (cmat ∘ fun x : Fin 5 × Bool => cond x.2 (u33ImgL x.1) (u33ImgL x.1)⁻¹) =
        fun x : Fin 5 × Bool => cond x.2 (u33Mats x.1) (u33MatsInv x.1) :=
      funext fun x => cmat_u33ImgL_cond x.1 x.2
    rw [hl]
    exact u33Mats_rels w hw)

theorem u33HomL_of
    (i : Fin 5) : u33HomL (PresentedGroup.of i) = u33ImgL i := by
  rw [u33HomL, PresentedGroup.toGroup.of]

theorem u33HomL_injective
    : Function.Injective u33HomL := by
  have := isSimpleGroup_u33Pres
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal u33HomL.ker with h | h
  · exact h
  · exfalso
    have hmem : (PresentedGroup.of (2 : Fin 5) : U33G) ∈ u33HomL.ker := by
      rw [h]
      trivial
    have h1 : u33HomL (PresentedGroup.of (2 : Fin 5)) = 1 := hmem
    rw [u33HomL_of] at h1
    have h2 := congrArg cmat h1
    rw [cmat_u33ImgL, map_one] at h2
    exact absurd h2 Certificates.certificate17951.1

theorem u33Pres_nonabelian :
    ∃ x y : U33G, x * y ≠ y * x := by
  refine ⟨PresentedGroup.of 3, PresentedGroup.of 2, fun h => ?_⟩
  have h1 := congrArg (fun z : U33G => cmat (u33HomL z)) h
  simp only [map_mul, u33HomL_of, cmat_u33ImgL] at h1
  exact absurd h1 Certificates.certificate17951.2.1

theorem center_u33Pres_eq_bot
    : Subgroup.center U33G = ⊥ := by
  have := isSimpleGroup_u33Pres
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U33G) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := u33Pres_nonabelian
    have hx : x ∈ Subgroup.center U33G := by
      rw [h]
      trivial
    exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)

theorem wordEval_mem_of_forall_mem {G : Type*} [Group G] (S : Subgroup G) {k : ℕ}
    (gens : Fin k → G) (h : ∀ i, gens i ∈ S) (w : List (Fin k)) : wordEval gens w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons i w ih => exact S.mul_mem (h i) ih

theorem map_wordEval_hom {G H : Type*} [Group G] [Group H] (f : G →* H) {k : ℕ}
    (gens : Fin k → G) (w : List (Fin k)) :
    f (wordEval gens w) = wordEval (fun i => f (gens i)) w := by
  induction w with
  | nil => exact map_one f
  | cons i w ih => exact (map_mul f _ _).trans (congrArg _ ih)

theorem g2a_eq_word
    : g2a = wordEval u33ImgL [2, 3, 4, 3, 3, 4] := by
  apply cmat_injective
  rw [cmat_g2a, cmat_wordEval u33ImgL u33Mats cmat_u33ImgL]
  exact Certificates.certificate17951.2.2.1

theorem g2b_eq_word
    : g2b = wordEval u33ImgL [1, 4, 3, 2, 4, 3, 4, 3, 1, 0] := by
  apply cmat_injective
  rw [cmat_g2b, cmat_wordEval u33ImgL u33Mats cmat_u33ImgL]
  exact Certificates.certificate17951.2.2.2

noncomputable def u33HomA
    : U33G →* Amb := (cayleyGroup (ZMod 2)).subtype.comp u33HomL

theorem u33HomA_injective
    : Function.Injective u33HomA :=
  Subtype.val_injective.comp u33HomL_injective

theorem u33ImgL_mem_subG2 (i : Fin 5) : ((u33ImgL i : ↥(cayleyGroup (ZMod 2))) : Amb) ∈ subG2 := by
  rw [u33ImgL, coe_wordEval_sub]
  refine wordEval_mem_of_forall_mem subG2 _ (fun j => ?_) _
  fin_cases j
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem range_u33HomA :
    u33HomA.range = subG2 := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map,
      ← PresentedGroup.closure_range_of {r : FreeGroup (Fin 5) | r ∈ u33PresRels.map FreeGroup.mk},
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact (by simpa [u33HomA, u33HomL_of] using u33ImgL_mem_subG2 i)
  · rw [subG2, Subgroup.closure_le]
    have hw : ∀ w : List (Fin 5), ((wordEval u33ImgL w : ↥(cayleyGroup (ZMod 2))) : Amb) ∈
        u33HomA.range := by
      intro w
      refine ⟨wordEval (fun i => (PresentedGroup.of i : U33G)) w, ?_⟩
      rw [u33HomA, MonoidHom.comp_apply, map_wordEval_hom]
      simp only [u33HomL_of]
      rfl
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, g2a_eq_word]
      exact hw _
    · rw [SetLike.mem_coe, g2b_eq_word]
      exact hw _

noncomputable def u33EquivSubG2
    : U33G ≃* ↥subG2 :=
  (MonoidHom.ofInjective u33HomA_injective).trans (MulEquiv.subgroupCongr range_u33HomA)

theorem outAbelian_u33Pres
    : OutAbelian U33G := by
  have : Finite U33G := (Nat.finite_of_card_ne_zero (by rw [card_u33Pres]; norm_num))
  exact outAbelian_of_card_mulAut_le center_u33Pres_eq_bot
    (by rw [card_u33Pres]; exact card_mulAut_u33Pres_le)

theorem outAbelian_subG2
    : OutAbelian ↥subG2 :=
  outAbelian_of_mulEquiv u33EquivSubG2 outAbelian_u33Pres

end CFSG.Quasithin
