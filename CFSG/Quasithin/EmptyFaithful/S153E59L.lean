module

public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.S153E59B
public import CFSG.Quasithin.EmptyFaithful.S153EInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section Card

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tildeOf_self_eq_bot (Z : Subgroup G) : tildeOf Z Z = ⊥ := by
  ext y
  rw [Subgroup.mem_bot]
  constructor
  · intro hy
    obtain ⟨x, hxZ, rfl⟩ := mem_secImg.1 hy
    exact secMk_eq_one_iff.2 hxZ
  · rintro rfl
    exact one_mem _

omit [Finite G] in
theorem card_tilde_mul {Z B : Subgroup G} (hZ : Nat.card Z = 2) (hZB : Z ≤ B)
    (hBN : B ≤ Subgroup.normalizer (Z : Set G)) :
    Nat.card ↥(tildeOf Z B) * 2 = Nat.card B := by
  have h := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (T := Z) (H := B)
    le_rfl hZB hBN
  have hbot : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := tildeOf_self_eq_bot Z
  rw [hbot, Subgroup.relIndex_bot_left] at h
  have e := Subgroup.relIndex_mul_card Z B
  rw [inf_eq_left.2 hZB, hZ] at e
  change Nat.card ↥(secImg (Subgroup.normalizer (Z : Set G)) Z B) * 2 = Nat.card B
  rw [h]
  exact e

end Card

section EData

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
  {y t₁ : G}

omit [Finite G] in
theorem E_le_U : Egp153 T M V₁ Mc y ≤ UH153 T M V₁ Mc := inf_le_left.trans inf_le_left

omit [Finite G] in
theorem Et_le_U (ht : t₁ ∈ Mc) : conjSubgroup (Egp153 T M V₁ Mc y) t₁ ≤ UH153 T M V₁ Mc := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h1 := S153E.U_conj_mem (Mc.inv_mem ht) (E_le_U hx)
  have e : x = t₁⁻¹ * (t₁ * x * t₁⁻¹) * t₁⁻¹⁻¹ := by group
  rw [e]
  exact h1

include cx in
theorem Z_le_Et (ht : t₁ ∈ Mc) (hZE : quasithinOmegaOneCenter T ≤ Egp153 T M V₁ Mc y) :
    quasithinOmegaOneCenter T ≤ conjSubgroup (Egp153 T M V₁ Mc y) t₁ := by
  intro z hz
  rw [mem_conjSubgroup_iff]
  have : t₁ * z * t₁⁻¹ = z := by rw [Z_central cx ht hz]; group
  rw [this]
  exact hZE hz

omit [Finite G] in
theorem relIndex_eq_two_pow {Z E : Subgroup G} (hE : ∀ e ∈ E, e ^ 2 = 1) {n : ℕ}
    (hn : mIdx E Z = n) [Finite G] : Z.relIndex E = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥E := isPGroup_two_of_sq_eq_one (fun v => Subtype.ext (by simpa using hE v v.2))
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hmul := Subgroup.relIndex_mul_card Z E
  have hdvd : Z.relIndex E ∣ 2 ^ k := by
    rw [← hk, ← hmul]
    exact Dvd.intro _ rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [mIdx, hj, padicValNat.prime_pow] at hn
  rw [hj, hn]

theorem card_E (c : Chain15358 cx N₁ N₂ g s y t₁) : Nat.card ↥(Egp153 T M V₁ Mc y) = 16 := by
  obtain ⟨hZE, hsq, hm⟩ := c.h56.E_sing
  have hs : s = 1 := c.h58.two_s
  have h8 : (quasithinOmegaOneCenter T).relIndex (Egp153 T M V₁ Mc y) = 2 ^ 3 :=
    relIndex_eq_two_pow hsq (by rw [hm, hs])
  have e := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)
  rw [inf_eq_left.2 hZE, h8, card_Z cx] at e
  omega

theorem card_Et (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(conjSubgroup (Egp153 T M V₁ Mc y) t₁) = 16 := by
  rw [card_conjSubgroup', card_E cx c]

theorem card_tilde_E (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)) = 8 := by
  have h := card_tilde_mul (card_Z cx) c.h56.E_sing.1
    ((E_le_U.trans (U_le_Mc cx)).trans cx.hF.H_normalizes_V₁)
  rw [card_E cx c] at h
  omega

theorem card_tilde_Et (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)) = 8 := by
  have ht : t₁ ∈ Mc := S153E.T_le_Mc cx c.ht₁.1
  have h := card_tilde_mul (card_Z cx) (Z_le_Et cx ht c.h56.E_sing.1)
    (((Et_le_U ht).trans (U_le_Mc cx)).trans cx.hF.H_normalizes_V₁)
  rw [card_Et cx c] at h
  omega

end EData

section V0Data

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
  {y t₁ : G}

include cx

theorem conj_Z_le_VZ (hyN : y ∈ Subgroup.normalizer (VZ T M : Set G)) :
    conjSubgroup (quasithinOmegaOneCenter T) y ≤ VZ T M := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hV : y * x * y⁻¹ ∈ VZ T M := cx.c.hyp.Z_le_VZ hx
  have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (VZ T M : Set G)).inv_mem hyN)
    (y * x * y⁻¹)).mp hV
  have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem V0_le_Mc (hyN : y ∈ Subgroup.normalizer (VZ T M : Set G)) :
    quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤ Mc :=
  sup_le ((cx.c.hyp.Z_le_VZ).trans (VZ_le_Mc cx)) ((conj_Z_le_VZ cx hyN).trans (VZ_le_Mc cx))

theorem card_V0_le (hyN : y ∈ Subgroup.normalizer (VZ T M : Set G)) :
    Nat.card ↥(quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y) ≤ 4 := by
  have hZc : quasithinOmegaOneCenter T ≤
      Subgroup.normalizer (conjSubgroup (quasithinOmegaOneCenter T) y : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Z_central cx ((conj_Z_le_VZ cx hyN |>.trans (VZ_le_Mc cx)) hw) hz)
  have h := card_sup_mul_card_inf_of_normalizes hZc
  rw [card_Z cx, card_conjSubgroup', card_Z cx] at h
  have hpos : 0 < Nat.card ↥(quasithinOmegaOneCenter T ⊓ conjSubgroup (quasithinOmegaOneCenter T) y) :=
    Nat.card_pos
  nlinarith

theorem card_tilde_V0_le (hyN : y ∈ Subgroup.normalizer (VZ T M : Set G)) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T)
      (quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y)) ≤ 2 := by
  have h := card_tilde_mul (card_Z cx) (le_sup_left : quasithinOmegaOneCenter T ≤ _)
    ((V0_le_Mc cx hyN).trans cx.hF.H_normalizes_V₁)
  have h4 := card_V0_le cx hyN
  omega

end V0Data

section SubgroupOf

variable {Γ : Type*} [Group Γ]

theorem card_subgroupOf_le (A B : Subgroup Γ) [Finite ↥B] :
    Nat.card ↥(B.subgroupOf A) ≤ Nat.card ↥B :=
  Nat.card_le_card_of_injective (fun x => (⟨x.1.1, x.2⟩ : ↥B)) (fun a b h => by
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h)

end SubgroupOf

end S153E59

end CFSG.Quasithin
