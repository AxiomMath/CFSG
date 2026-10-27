module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Frame
public import CFSG.SignalizerFunctorTheorem.McBride.Models.AutItems
import CFSG.SignalizerFunctorTheorem.NearModels.Main
import CFSG.SignalizerFunctorTheorem.McBride.Models.Conj
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.A4
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Arithmetic
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Aut
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Dickson
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Items
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Setup
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Structure
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Transvection

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride

open PSL2Three CFSG.SignalizerFunctorTheorem.NearModels

theorem exists_aut_psl2Three {p : ℕ} (hp : p.Prime)
    (_hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p))) :
    ∃ f : MulAut PSL(2, GaloisField 3 p), orderOf f = p := by
  obtain ⟨σ, hσ⟩ := PSL2Three.exists_std_aut hp
  exact ⟨_, hσ⟩

theorem frame_psl2Three
    {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) : Frame p 2 f :=
  frame_of_isA4 hp hf hcop (isSimpleGroup_of_prime hp)
    (nearSimpleModel_fixedSubgroup_solvable hp (Or.inr (Or.inl ⟨MulEquiv.refl _⟩)) hcop f hf)
    (isA4_fixed hp hcop f hf) (eq_fixed_of_overgroup hp hcop f hf)
    (card_sylow_two hp (odd_of_coprime hp hcop))

theorem isCoatom_fixedNormalizer_psl2Three
    {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) :
    IsCoatom (fixedNormalizer f) := by
  have hF := frame_psl2Three hp hcop f hf
  have hMtop : fixedNormalizer f ≠ ⊤ := by
    intro htop
    have hnorm : (fixedFitting f).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hF.simple.eq_bot_or_eq_top_of_normal (fixedFitting f) with h1 | h1
    · exact hF.C0_ne_bot h1
    · exact hF.C0_ne (le_antisymm (fixedFitting_le f) (h1 ▸ le_top))
  refine ⟨hMtop, fun b hb => ?_⟩
  by_contra hbtop
  exact not_le_of_gt hb (hF.overgroup b ((fixed_le_fixedNormalizer f).trans hb.le) hbtop)

theorem fixedNormalizer_psl2Three {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) :
    fixedNormalizer f = signalizerFixedSubgroup f :=
  fixedNormalizer_eq_fixed hp hcop f hf

theorem fixedCore1_psl2Three {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) :
    fixedCore1 f = signalizerFixedSubgroup f :=
  (isA4_fixed hp hcop f hf).fixedCore1_eq

theorem itemC_psl2Three {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) : ItemC p f := by
  obtain ⟨σ, hσ⟩ := PSL2Three.exists_std_aut hp
  exact ItemC.forall_of_one hp (psl2_card_pSubgroup_dvd 3 hp hcop) hσ
    (itemC_of_transvecs hp (psl2FieldAut_transvecUp σ) (psl2FieldAut_transvecLow σ)) f hf

theorem itemG_psl2Three {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) : ItemG p f := by
  obtain ⟨σ, hσ⟩ := PSL2Three.exists_std_aut hp
  exact ItemG.forall_of_one hp (psl2_card_pSubgroup_dvd 3 hp hcop) hσ
    (itemG_of_transvecs hp (isA4_fixed hp hcop _ hσ) (fixedNormalizer_eq_fixed hp hcop _ hσ)
      (psl2FieldAut_transvecUp σ) (psl2FieldAut_transvecLow σ)) f hf

theorem itemO_psl2Three {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) : ItemO f := by
  exact itemO_of_card_normalizer hp (odd_of_coprime hp hcop) (by
    rw [fixedNormalizer_eq_fixed hp hcop f hf]
    exact (isA4_fixed hp hcop f hf).card)

theorem outer_perfect_psl2Three {p : ℕ} (hp : p.Prime)
    (_hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p))) :
    ∀ P : Subgroup (MulAut PSL(2, GaloisField 3 p)), Group.IsPerfect P →
      P ≤ (MulAut.conj : PSL(2, GaloisField 3 p) →*
        MulAut PSL(2, GaloisField 3 p)).range := by
  have : NeZero p := ⟨hp.ne_zero⟩
  exact fun P hP => perfect_le_range_conj _ P hP

theorem outer_coprime_pow_six_psl2Three {p : ℕ} (hp : p.Prime)
    (_hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p))) :
    ∀ g : MulAut PSL(2, GaloisField 3 p), Nat.Coprime p (orderOf g) →
      g ^ 6 ∈ (MulAut.conj : PSL(2, GaloisField 3 p) →*
        MulAut PSL(2, GaloisField 3 p)).range := by
  intro g hg
  obtain ⟨y, rfl⟩ := exists_pglAction_of_coprime_orderOf hp g hg
  obtain ⟨x, hx⟩ := sq_mem_range_toPGL y
  refine ⟨x ^ 3, ?_⟩
  rw [map_pow, ← CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL,
    ← map_pow, ← hx, ← map_pow, ← pow_mul]

end CFSG.SignalizerFunctorTheorem.McBride
