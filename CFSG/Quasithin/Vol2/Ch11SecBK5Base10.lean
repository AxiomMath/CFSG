module

public import CFSG.Quasithin.Vol2.Ch11SecBK5Base7
public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.Vol2.KGNat
open scoped IsMulCommutative

variable {G : Type} [Group G] {L V X : Subgroup G} [IsMulCommutative ↥V]
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {D : FFModel}
  {LM : LinModel D K (ι → K)} {π : D.Gam →* ↥(autOn L V)} {f : ↥V → (ι → K)}
  {Γ : Subgroup (GL ι K)}


theorem autOn_le_normZH_self : autOn L V ≤ normZH (autOn L V) (cZ L V) :=
  autOn_le_normZH (X := L) (inf_le_left.trans Subgroup.le_normalizer)

theorem map_autOn_eq_natImage (φ : D.Gam →* ↥Γ) (hφ : Function.Surjective φ)
    (hlin : ∀ γ x, LM.lin γ x = ((φ γ : GL ι K) : Matrix ι ι K).mulVec x)
    (hf : IsCoord LM (autOn L V) (cZ L V) π f) :
    ((autOn L V).subgroupOf (normZH (autOn L V) (cZ L V))).map (psiZ hf) = natImage Γ := by
  have hN := autOn_le_normZH_self (L := L) (V := V)
  have key : ∀ γ : D.Gam, psiZ hf ⟨_, hN (π γ).2⟩ = natAut Γ (φ γ) := fun γ =>
    MulEquiv.ext fun x => by
      rw [← ofAdd_toAdd x, psiZ_pi hf γ (hN (π γ).2), hlin]
      rfl
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨γ, hγ⟩ := hf.onto ⟨σ, hσ⟩
    have hσγ : σ = ⟨_, hN (π γ).2⟩ := Subtype.ext (by rw [hγ])
    rw [hσγ, key]
    exact ⟨φ γ, rfl⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨γ, rfl⟩ := hφ g
    exact ⟨⟨_, hN (π γ).2⟩, (π γ).2, key γ⟩

theorem exists_nPrime_eq_of_mat (φ : D.Gam →* ↥Γ) (hφi : Function.Injective φ)
    (hφs : Function.Surjective φ)
    (hlin : ∀ γ x, LM.lin γ x = ((φ γ : GL ι K) : Matrix ι ι K).mulVec x)
    (hf : IsCoord LM (autOn L V) (cZ L V) π f)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hcomm : ⁅V, L⁆ = V) (hLX : L ≤ X)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ Y : Subgroup (MulAut (StdMod ι K)), E3.nPrime (autOn X V) = E3.nPrime Y ∧
      natImage Γ ≤ Y ∧ Y ≤ natNorm Γ := by
  have hfaith : ∀ γ, (∀ x, LM.lin γ x = x) → π γ = 1 := by
    intro γ hγ
    have h1 : φ γ = 1 := by
      apply Subtype.ext
      apply Units.ext
      refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← hlin, hγ, OneMemClass.coe_one,
        Units.val_one, Matrix.one_mulVec]
    rw [show γ = 1 from hφi (h1.trans (map_one φ).symm), map_one]
  have hL := map_autOn_eq_natImage φ hφs hlin hf
  refine ⟨_, nPrime_autOn_eq_map hf hfaith hLV hcomm hXN, ?_, ?_⟩
  · rw [← hL]
    exact map_autOn_le hf hLX
  · have h := map_le_normalizer hf hXN
    rw [hL] at h
    exact h

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
