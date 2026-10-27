module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanI
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rHpCartan
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanG
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanH
public import CFSG.Quasithin.Background.HTriSolv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_normalizer_inf_of_mem {C H : Subgroup G} {b : G}
    (hbC : b ∈ Subgroup.normalizer (C : Set G)) (hbH : b ∈ H) :
    b ∈ Subgroup.normalizer ((C ⊓ H : Subgroup G) : Set G) := by
  change b ∈ Subgroup.normalizer ((C ⊓ H : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxC, hxH⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hbC x).mp hxC,
      H.mul_mem (H.mul_mem hbH hxH) (H.inv_mem hbH)⟩
  · intro hx
    obtain ⟨hxC, hxH⟩ := Subgroup.mem_inf.mp hx
    have h1 : b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ = x := by group
    rw [← h1]
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (inv_mem hbC) _).mp hxC,
        H.mul_mem (H.mul_mem (H.inv_mem hbH) hxH) (H.inv_mem (H.inv_mem hbH))⟩

theorem uc22r3e5c_exists_cartan_inv
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2)
    {n : ℕ} (hn : 2 < n) (hSz : IsSz (Bar2 L) n)
    {b : G} (hbB : b ∈ c.B0) (hb3 : orderOf b = 3) :
    ∃ C : Subgroup G, C ≤ conjClosure D.M L ∧ Odd (Nat.card C) ∧
      IsMulCommutative ↥C ∧ Permutes C D.T ∧ Group.IsSolvable ↥(C ⊔ D.T) ∧
      b ∈ normalizer (C : Set G) ∧
      b ∈ normalizer ((C ⊓ H₁ : Subgroup G) : Set G) ∧
      b ∈ normalizer ((C ⊓ H₂ : Subgroup G) : Set G) ∧
      (C : Set G) = ((C ⊓ H₁ : Subgroup G) : Set G) * ((C ⊓ H₂ : Subgroup G) : Set G) ∧
      ∃ K : Subgroup G, K ≠ L ∧ K ∈ calC D.M ∧ conjSetOf D.M L = {L, K} ∧
        IsSz (Bar2 K) n ∧
        ∃ (e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K) (DL : Subgroup (Bar2 L))
          (DK : Subgroup (Bar2 K)),
          (∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
            e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1)) ∧
          (∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
            e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K))) ∧
          (barImage (conjClosure D.M L) C).map e.toMonoidHom = DL.prod DK ∧
          DL ≤ normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L)) ∧
          DK ≤ normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K)) ∧
          Nat.card DL = 2 ^ n - 1 ∧ Nat.card DK = 2 ^ n - 1 := by
  classical
  obtain ⟨K, hKne, hset, hKC⟩ := uc22s21ru4e_exists_second_member hc2 hL
  obtain ⟨C, hCβ, hoddC, hcardC, hbC, hβPC⟩ :=
    uc22r3e5c_exists_cartan_hall h5 h1930 c hL hc2 hn hSz hbB hb3
  have hCX : C ≤ conjClosure D.M L := hCβ.trans inf_le_left
  obtain ⟨e, DL, DK, heL, heK, hEeq, hDLle, hDKle, hDLcard, hDKcard, hCcomm⟩ :=
    uc22r3e5c_exists_cartan_image hL hKC hKne hset hSz hCX hCβ hcardC hoddC
  have hPerm : Permutes C D.T := uc22r3e5c_permutes_cartan hCβ hβPC
  have hCab : ∀ a ∈ C, ∀ d ∈ C, a * d = d * a := by
    intro a ha d hd
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨d, hd⟩)
  have hSolv : Group.IsSolvable ↥(C ⊔ D.T) :=
    CFSG.Quasithin.H.Tri.isSolvable_sup_of_permute hCab hoddC
      (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.1 hPerm
  have hCXM : C ≤ D.M := hCX.trans
    (uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) hL.1.le)
  have hYCT : ((C ⊔ D.T : Subgroup G) : Set G) = (C : Set G) * (D.T : Set G) :=
    CFSG.Quasithin.A4.coe_sup_eq_mul_of_mul_comm hPerm.symm
  have hfac : (C : Set G) =
      ((C ⊓ H₁ : Subgroup G) : Set G) * ((C ⊓ H₂ : Subgroup G) : Set G) :=
    uc22s21rhp_cartan_eq_mul D hH₁ hH₂ hfX (sup_le hCXM D.sylowM.le) le_sup_right hSolv
      le_sup_left hYCT hoddC
  have hbH := Subgroup.mem_inf.mp (hL0 (c.hB0.1 hbB))
  exact ⟨C, hCX, hoddC, hCcomm, hPerm, hSolv, hbC,
    uc22r3e5c_normalizer_inf_of_mem hbC hbH.1,
    uc22r3e5c_normalizer_inf_of_mem hbC hbH.2, hfac,
    K, hKne, hKC, hset, uc22r3e5c_isSz_of_mem_conjSetOf (by rw [hset]; simp) hSz,
    e, DL, DK, heL, heK, hEeq, hDLle, hDKle, hDLcard, hDKcard⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
