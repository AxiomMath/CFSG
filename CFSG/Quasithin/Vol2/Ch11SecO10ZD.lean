module

public import CFSG.Quasithin.Vol2.Ch11SecO10U
public import CFSG.Quasithin.Vol2.Ch11SecA15MS3
public import CFSG.Quasithin.Vol2.Ch11SecD551B
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT3

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem le_of_isSylowTwoOf {Y : Type*} [Group Y] [Finite Y] {P Q H : Subgroup Y}
    (hP : QuasithinUnique.IsSylowTwoOf P H) (hPQ : P ≤ Q) (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) :
    Q ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.relIndex_mul_relIndex P Q H hPQ hQH
  obtain ⟨k, hk⟩ := hQ.index (P.subgroupOf Q)
  have h2 : P.relIndex Q = 2 ^ k := hk
  rcases k with _ | k
  · exact Subgroup.relIndex_eq_one.1 (by rw [h2, pow_zero])
  · exfalso
    apply hP.2.2
    show 2 ∣ P.relIndex H
    rw [← h1, h2]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

theorem le_lOf_sup_rOf (hB42 : AsB42) (h1102 : Stmt11_0_2) (h8 : Ch10.TmpL6_3_2_2_eight)
    (hF15 : SecA.Facts15) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ : Subgroup G}
    (hU : IsVi T L I n 1 V₁) {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ LOf L V₁ ⊔ ROf T L V₁ := by
  intro a ha
  have haT := hA.1 ha
  have haV : a ∈ Subgroup.normalizer (fsuV T I : Set G) := SecA.T_le_normalizer_fsuV T I haT
  have h1 : SecA.conjV (fsuV T I) a haV ∈ autOn L (fsuV T I) :=
    autOn_le_of_isMaxElemAbelian hB42 h1102 h8 h hcV hA (SecA.conjV_mem_autOn ha haV)
  have h2 : SecA.conjV (fsuV T I) a haV ∈ autOn (T ⊓ L) (fsuV T I) := by
    have hle := le_of_isSylowTwoOf (SecA.isSylowTwoOf_P h)
      (le_inf (SecA.autOn_mono inf_le_right) (SecA.autOn_mono inf_le_left)) inf_le_left
      ((isPGroup_autOn_of h.fsu.sylow.1).to_le inf_le_right)
    exact hle ⟨h1, SecA.conjV_mem_autOn haT haV⟩
  obtain ⟨s, hs, hsV, hse⟩ := SecA.mem_autOn_iff.mp h2
  have hc : s⁻¹ * a ∈ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    ⟨T.mul_mem (T.inv_mem hs.1) haT, SecS.inv_mul_mem_centralizer hse.symm⟩
  have h3 := SecD.inf_centralizer_le_ROf h1102 h hU hc
  have h4 := SecA.inf_L_le_lOf_sup_ROf hF15 h1102 h hU hs
  have := Subgroup.mul_mem _ h4 (Subgroup.mem_sup_right h3)
  rwa [mul_inv_cancel_left] at this

theorem comm_mem_pCoreOf_lOf (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hU : IsVi T L I n 1 V₁) {r l : G} (hr : r ∈ ROf T L V₁) (hl : l ∈ LOf L V₁) :
    r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 (LOf L V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRT : ROf T L V₁ ≤ T := SecD.ROf_le_T h V₁
  have hTL₁ : T ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun t ht =>
    SecD.mem_normalizer_lOf (h.normal ht) (SecA.IsVi.le_normalizer hU ht)
  have hLR : LOf L V₁ ≤ Subgroup.normalizer (ROf T L V₁ : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hx)
  have hmemL : r * l * r⁻¹ * l⁻¹ ∈ LOf L V₁ :=
    (LOf L V₁).mul_mem ((Subgroup.mem_normalizer_iff.1 (hTL₁ (hRT hr)) l).1 hl)
      ((LOf L V₁).inv_mem hl)
  have hmemR : r * l * r⁻¹ * l⁻¹ ∈ ROf T L V₁ := by
    have h1 : l * r⁻¹ * l⁻¹ ∈ ROf T L V₁ :=
      (Subgroup.mem_normalizer_iff.1 (hLR hl) _).1 ((ROf T L V₁).inv_mem hr)
    have h2 := (ROf T L V₁).mul_mem hr h1
    simpa [mul_assoc] using h2
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun x hx => SecD.mem_normalizer_inf (Subgroup.le_normalizer hx) (hLR hx)) ?_
    ⟨hmemL, hmemR⟩
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right

end CFSG.Quasithin.Vol2.Ch11.O10
