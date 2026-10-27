module

public import CFSG.Quasithin.EmptyFaithful.S153EN8D
public import CFSG.Quasithin.EmptyFaithful.S153E59T
public import CFSG.Quasithin.EmptyFaithful.S153EN8C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t} {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem Q_le_T (c : Chain15358 cx N₁ N₂ g s y t₁) :
    M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ T := by
  intro x hx
  refine S153E59.inf_Mc_le_T cx c ⟨hx.1, ?_⟩
  rw [← S153E59.centralizer_Z_eq cx]
  exact Subgroup.centralizer_le cx.c.hyp.Z_le_VZ hx.2

theorem Q_le_pCoreY (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 (Y153 Mc M) := fun _ hx =>
  S153E59.centralizer_T_le_pCoreOf_Y cx h113 c.toChain15354 c.h58.two_s ⟨Q_le_T c hx, hx.2⟩

theorem Q_le_P (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ Pgp153 T M V₁ Mc g := fun _ hx =>
  S153E59.pCoreOf_Y_le_P cx c.h54.one (Q_le_pCoreY h113 c hx)

section Dpart

variable (h113 : StageLemma14113) (c : Chain15359 cx N₁ N₂ g s y t₁) (B : BarModel cx)
  {d : G} (hdM : d ∈ M)

theorem P_le_centralizer (c : Chain15354 cx N₁ N₂ g s) :
    Pgp153 T M V₁ Mc g ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((Subgroup.mem_centralizer_iff.mp (c.h54.two_center hv).2 p hp)).symm

theorem P_le_Ni (c : Chain15354 cx N₁ N₂ g s) (N : Subgroup (MulAut ↥(VZ T M))) :
    Pgp153 T M V₁ Mc g ≤ Ni153 T Mc M V₁ N := by
  intro e he
  have hI := c.h54.one
  have heC := P_le_centralizer c he
  have heN : e ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.centralizer_le_normalizer (VZ T M : Set G) heC
  refine S153E.mem_preAut153.2 ⟨S153E55.P_le_YU hI he, heN, ?_⟩
  have : conjAct (VZ T M) ⟨e, heN⟩ = 1 := (S153E59.conjAct_eq_one_iff _ _).2 heC
  rw [this]
  exact N.one_mem

include c in
theorem barM_ne_one (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) : barM cx hdM ≠ 1 := by
  intro h
  have hdQ : d ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G) := ⟨hdM, (barM_eq_one_iff hdM).1 h⟩
  have hdT := Q_le_T c.toChain15358 hdQ
  have hT2 : IsPGroup 2 T := cx.hF.sylow_H.2.1
  obtain ⟨k, hk⟩ := hT2 ⟨d, hdT⟩
  have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := by
    have h4 := orderOf_dvd_of_pow_eq_one hk'
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rwa [orderOf_eq_prime hd3 hd1] at h4
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem barM_cube (hd3 : d ^ 3 = 1) : (barM cx hdM) ^ 3 = 1 := by
  have : barM cx (M.pow_mem hdM 3) = 1 :=
    (barM_eq_one_iff _).2 (by rw [hd3]; exact Subgroup.one_mem _)
  rwa [barM_pow] at this

include h113 c hdM in
theorem mem_Y (hd3 : d ^ 3 = 1) : d ∈ Y153 Mc M := by
  have hV := cx.c.hyp.elemAbelian
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  have hbY : barM cx hdM ∈ autI hV (Y153 Mc M) := by
    rw [hYbar]
    exact Subgroup.subset_closure ⟨barM_mem_autI hdM, odd_orderOf_of_cube (barM_cube hdM hd3)⟩
  obtain ⟨y', hy'Y, hy'⟩ := (mem_autI hV).1 hbY
  have hy'M : (y' : G) ∈ M := Y153_le Mc M hy'Y
  have hbe : barM cx hdM = barM cx hy'M := hy'.symm
  have h1 : d⁻¹ * y' ∈ Subgroup.centralizer (VZ T M : Set G) := (barM_eq_iff hdM hy'M).1 hbe
  have h2 : d⁻¹ * y' ∈ pCoreOf 2 (Y153 Mc M) :=
    Q_le_pCoreY h113 c.toChain15358 ⟨M.mul_mem (M.inv_mem hdM) hy'M, h1⟩
  have h3 : d⁻¹ * y' ∈ Y153 Mc M := pCoreOf_le 2 _ h2
  have e : d = y' * (d⁻¹ * y')⁻¹ := by group
  rw [e]
  exact (Y153 Mc M).mul_mem hy'Y ((Y153 Mc M).inv_mem h3)

end Dpart

end S153EN8

end CFSG.Quasithin
