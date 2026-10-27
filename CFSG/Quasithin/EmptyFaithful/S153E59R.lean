module

public import CFSG.Quasithin.EmptyFaithful.S153E59Q
public import CFSG.Quasithin.EmptyFaithful.S153E59F
public import CFSG.Quasithin.EmptyFaithful.S153E59J

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section Generic

theorem card_eq_two_pow_of_sylow {X : Type*} [Group X] [Finite X] {S H : Subgroup X}
    (hS : IsSylowTwoOf S H) {a m : ℕ} (hm : ¬ 2 ∣ m) (hcard : Nat.card H = 2 ^ a * m) :
    Nat.card S = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, hp, hodd⟩ := hS
  obtain ⟨s, hs⟩ := hp.exists_card_eq
  have h1 := Subgroup.card_mul_index (S.subgroupOf H)
  have hc : Nat.card ↥(S.subgroupOf H) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  rw [hc, hs, hcard] at h1
  have hi0 : (S.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  have h2 := congrArg (padicValNat 2) h1
  rw [padicValNat.mul (by positivity) hi0, padicValNat.mul (by positivity) hm0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hodd,
    padicValNat.eq_zero_of_not_dvd hm] at h2
  rw [hs]
  congr 1

end Generic

section Count

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
  {y t₁ : G}

include cx in
theorem relIndex_centralizer_T :
    (T ⊓ Subgroup.centralizer (VZ T M : Set G)).relIndex T = 8 := by
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := S153E.exists_bar_model cx
  have hT8 : Nat.card ↥(autI cx.c.hyp.elemAbelian T) = 8 :=
    hS.card_T cx.c.hyp.isSylowTwoOf_autI
  rw [← card_autOn_eq_relIndex (S153E.T_le_N cx)]
  exact hT8

include cx in
theorem pCoreOf_Y_le_P (hI : Igp153 T M V₁ Mc g = Y153 Mc M ⊔ UH153 T M V₁ Mc) :
    pCoreOf 2 (Y153 Mc M) ≤ Pgp153 T M V₁ Mc g := by
  rw [S153E55.P_eq hI]
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) ?_ (pCoreOf_isPGroup 2 _)
  exact sup_le (le_normalizer_pCoreOf 2 _)
    ((S153E55.U_le_normalizer_Y cx).trans (normalizer_le_normalizer_pCoreOf 2 _))

include cx in
theorem card_T_le (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card T ≤ 2 ^ 11 := by
  have h1 := Subgroup.relIndex_mul_card (T ⊓ Subgroup.centralizer (VZ T M : Set G)) T
  have e : (T ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊓ T = T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    inf_eq_left.2 inf_le_left
  rw [e, relIndex_centralizer_T cx] at h1
  have hBR : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 (Y153 Mc M) :=
    centralizer_T_le_pCoreOf_Y cx h113 c.toChain15354 c.h58.two_s
  have hBP : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ Pgp153 T M V₁ Mc g :=
    hBR.trans (pCoreOf_Y_le_P cx c.h54.one)
  have h2 : Nat.card ↥(T ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤
      Nat.card ↥(Pgp153 T M V₁ Mc g) := Subgroup.card_le_of_le hBP
  rw [card_P cx h113 c] at h2
  omega

include cx in
theorem card_T_eq (hH : HStarFacts cx) : Nat.card T = 16 * Nat.card ↥(pCoreOf 2 Mc) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 Mc).exists_card_eq
  have hker : (rho cx).ker = (pCoreOf 2 Mc).subgroupOf Mc := by
    ext x
    rw [MonoidHom.mem_ker, rho_eq_one_iff cx x, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_ker_mul_card_range (rho cx)
  rw [hker, range_rho cx, hH.card_Hs] at h1
  have hc : Nat.card ↥((pCoreOf 2 Mc).subgroupOf Mc) = Nat.card ↥(pCoreOf 2 Mc) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 Mc)).toEquiv
  rw [hc, hb] at h1
  have hMc : Nat.card ↥Mc = 2 ^ (b + 4) * 21 := by
    rw [← h1]
    ring
  have h2 := card_eq_two_pow_of_sylow cx.hF.sylow_H (by omega : ¬ 2 ∣ 21) hMc
  rw [h2, hb]
  ring

include cx in
theorem eq_pCoreOf_Mc (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    UH153 T M V₁ Mc = pCoreOf 2 Mc := by
  have hH := hstarFacts cx c.h58 c.ht₁.1 c.ht₁.2
  have h16 := card_T_eq cx hH
  have hle := card_T_le cx h113 c
  have hU := card_U cx c
  refine Subgroup.eq_of_le_of_card_ge (S153E.U_le_Q cx) ?_
  rw [hU]
  omega

end Count

end S153E59

end CFSG.Quasithin
