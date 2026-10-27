module

public import CFSG.RankThree.PartOne.S12.Sec1510Defs
public import CFSG.RankThree.PartOne.S12.Sec12A
public import CFSG.RankThree.PartOne.S15K.L0cCore
public import CFSG.RankThree.PartOne.K159.CoverLift

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne

variable {G : Type} [Group G]

theorem inf_mul_inf_of_inner [Finite G] {p : ℕ} (hp : p.Prime) {E Y : Subgroup G}
    (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEpow : ∀ x ∈ E, x ^ p = 1)
    (hmax : ∀ F : Subgroup G, (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x ^ p = 1) →
      (∀ x ∈ F, ∀ y ∈ E, x * y = y * x) → E ≤ F → F ≤ E)
    (hinn : ∀ e ∈ E, ∃ x ∈ Y, ∃ y ∈ Subgroup.centralizer (Y : Set G), e = x * y)
    (hZ : ¬ p ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer (Y : Set G))) :
    ∀ x ∈ E, ∃ l ∈ E ⊓ Y, ∃ c ∈ E ⊓ Subgroup.centralizer (Y : Set G), x = l * c := by
  classical
  obtain ⟨P, hPY, hPcomm, hPpow, -, hEP, -⟩ :=
    S15K.exists_complement_of_inner hp hEcomm hEpow hinn hZ
  set C : Subgroup G := Subgroup.centralizer (Y : Set G) with hC
  have hCmem : ∀ y ∈ C, ∀ w ∈ Y, w * y = y * w := fun y hy w hw =>
    Subgroup.mem_centralizer_iff.1 hy w hw
  have hPE : ∀ x ∈ P, ∀ e ∈ E, x * e = e * x := by
    intro x hx e he
    obtain ⟨x', hx', y', hy', rfl⟩ := hEP e he
    calc x * (x' * y') = (x * x') * y' := by group
      _ = (x' * x) * y' := by rw [hPcomm x hx x' hx']
      _ = x' * (x * y') := by group
      _ = x' * (y' * x) := by rw [hCmem y' hy' x (hPY hx)]
      _ = (x' * y') * x := by group
  let T : Set G := {y | y ∈ C ∧ ∃ x ∈ P, x * y ∈ E}
  have hTcomm : ∀ y ∈ T, ∀ e ∈ E, y * e = e * y := by
    rintro y ⟨-, x, hxP, hxy⟩ e he
    have h1 : y = x⁻¹ * (x * y) := by group
    have h2 : Commute x⁻¹ e := (show Commute x e from hPE x hxP e he).inv_left
    have h3 : Commute (x * y) e := hEcomm _ hxy _ he
    rw [h1]
    exact (h2.mul_left h3).eq
  have hTT : ∀ y₁ ∈ T, ∀ y₂ ∈ T, y₁ * y₂ = y₂ * y₁ := by
    rintro y₁ ⟨-, x₁, hx₁P, hx₁y⟩ y₂ ⟨-, x₂, hx₂P, hx₂y⟩
    have e1 : y₁ = x₁⁻¹ * (x₁ * y₁) := by group
    have e2 : y₂ = x₂⁻¹ * (x₂ * y₂) := by group
    set e₁ := x₁ * y₁ with he₁
    set e₂ := x₂ * y₂ with he₂
    have c1 : Commute x₁⁻¹ x₂⁻¹ := (hPcomm _ (P.inv_mem hx₁P) _ (P.inv_mem hx₂P))
    have c2 : Commute x₁⁻¹ e₂ := (show Commute x₁ e₂ from hPE x₁ hx₁P e₂ hx₂y).inv_left
    have c3 : Commute e₁ x₂⁻¹ := (show Commute x₂ e₁ from hPE x₂ hx₂P e₁ hx₁y).symm.inv_right
    have c4 : Commute e₁ e₂ := hEcomm _ hx₁y _ hx₂y
    rw [e1, e2]
    exact ((c1.mul_right c2).mul_left ((c3.mul_right c4))).eq
  have hTpow : ∀ y ∈ T, y ^ p = 1 := by
    rintro y ⟨-, x, hxP, hxy⟩
    have h1 : y = x⁻¹ * (x * y) := by group
    have hc : Commute x⁻¹ (x * y) := (show Commute x (x * y) from hPE x hxP _ hxy).inv_left
    rw [h1, hc.mul_pow, inv_pow, hPpow x hxP, hEpow _ hxy]
    simp
  set S : Set G := (E : Set G) ∪ T with hS
  have hScomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t := by
    rintro s (hs | hs) t (ht | ht)
    · exact hEcomm s hs t ht
    · exact (hTcomm t ht s hs).symm
    · exact hTcomm s hs t ht
    · exact hTT s hs t ht
  have hSpow : ∀ s ∈ S, s ^ p = 1 := by
    rintro s (hs | hs)
    · exact hEpow s hs
    · exact hTpow s hs
  set F : Subgroup G := Subgroup.closure S with hF
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    (commute_of_mem_closure' hScomm hx hy).eq
  have hFpow : ∀ x ∈ F, x ^ p = 1 := fun x hx => pow_eq_one_of_mem_closure' hScomm hSpow hx
  have hFE : ∀ x ∈ F, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hle : F ≤ Subgroup.centralizer ({y} : Set G) := by
      refine (Subgroup.closure_le _).2 fun s hs => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hs with hs | hs
      · exact hEcomm s hs y hy
      · exact hTcomm s hs y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hEF : E ≤ F := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hFle : F ≤ E := hmax F hFcomm hFpow hFE hEF
  intro x hx
  obtain ⟨ξ, hξP, y, hyC, hxy⟩ := hEP x hx
  have hyT : y ∈ T := ⟨hyC, ξ, hξP, hxy ▸ hx⟩
  have hyE : y ∈ E := hFle (Subgroup.subset_closure (Or.inr hyT))
  have hξE : ξ ∈ E := by
    have : ξ = x * y⁻¹ := by rw [hxy]; group
    rw [this]
    exact E.mul_mem hx (E.inv_mem hyE)
  exact ⟨ξ, ⟨hξE, hPY hξP⟩, y, ⟨hyE, hyC⟩, hxy⟩

@[expose] def KFInnLayerInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) → E = A →
    ∀ e ∈ E, e ≠ 1 → (∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E) →
      (∀ x ∈ E, ∃ l ∈ thetaLayer p e, ∃ c' ∈ Subgroup.centralizer (thetaLayer p e : Set G),
        x = l * c') ∧
      ¬ p ∣ Nat.card ↥(thetaLayer p e ⊓ Subgroup.centralizer (thetaLayer p e : Set G))

theorem kfInnLayer_of_inner (hinn : KFInnLayerInner) : KFInnLayer := by
  intro G _ _ p A c L E h15 hF hout hEA e he he1 hZ x hx
  obtain ⟨hI1, hI2⟩ := hinn G p A c L E h15 hF hout hEA e he he1 hZ
  have h := h15.h12
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
  refine inf_mul_inf_of_inner h.prime hEcomm hEpow ?_ hI1 hI2 x hx
  intro F hFc hFp hFE hEF
  have hEA' : E ≤ Subgroup.centralizer (A : Set G) := h.E_le
  have hFA : F ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hFE x hx a (hEA ▸ ha)).symm
  have hFel : IsElementaryAbelian p ↥F :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hFc a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hFp a a.2) }
  exact (h.E_max F hFel hFA hEF).le

end CFSG.RankThree.PartOne.K159
