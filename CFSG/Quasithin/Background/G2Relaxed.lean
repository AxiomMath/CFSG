module

public import CFSG.Quasithin.Background.G2L2Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type*} [Group G]

structure AlmostSpecialBase (V V₁ L T H : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  ne_bot : V₁ ≠ ⊥
  le_V : V₁ ≤ V
  oTwo_eq : L = oTwoUpper L
  V_le_T : V ≤ T
  T_le_normV₁ : T ≤ Subgroup.normalizer (V₁ : Set G)
  T_le_normV : T ≤ Subgroup.normalizer (V : Set G)
  T_le_normL : T ≤ Subgroup.normalizer (L : Set G)
  sylow_LT : IsSylowTwoOf T (L ⊔ T)
  H_le : H ≤ Subgroup.normalizer (V₁ : Set G)
  lOne_sup_le : lOne L V₁ ⊔ T ≤ H
  sylow_H : IsSylowTwoOf T H
  charTwo : CharTwo H

theorem AlmostSpecialHyp.toBase {V V₁ L T H : Subgroup G} (h : AlmostSpecialHyp V V₁ L T H) :
    AlmostSpecialBase V V₁ L T H :=
  ⟨h.elemAbelian, h.ne_bot, h.le_V, h.oTwo_eq, h.V_le_T, h.T_le_normV₁, h.T_le_normV,
    h.T_le_normL, h.sylow_LT, h.H_le, h.lOne_sup_le, h.sylow_H, h.charTwo⟩

structure G22Conclusion (V V₁ T H : Subgroup G) : Prop where
  one : tildeOf V₁ V ≤ tildeOf V₁ (conjClosure V H) ∧
    tildeOf V₁ (conjClosure V H) ≤ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H))
  two : frattiniOf (conjClosure V H) ≤ V₁
  three : conjClosure V H ≤ T ∧ T ≤ Subgroup.normalizer (conjClosure V H : Set G)
  four : IsTwoReducedIn (tildeOf V₁ H) (tildeOf V₁ (conjClosure V H))

theorem AlmostSpecialHyp.g22 [Finite G] {V V₁ L T H : Subgroup G}
    (h : AlmostSpecialHyp V V₁ L T H) : G22Conclusion V V₁ T H :=
  ⟨h.G22_one, h.G22_two, h.G22_three, h.G22_four⟩

namespace AlmostSpecialBase

variable {V V₁ L T H : Subgroup G} (hb : AlmostSpecialBase V V₁ L T H)

include hb

theorem T_le_H : T ≤ H := le_sup_right.trans hb.lOne_sup_le

theorem isPGroup_T : IsPGroup 2 T := hb.sylow_H.2.1

theorem V_le_N : V ≤ Subgroup.normalizer (V₁ : Set G) := hb.V_le_T.trans hb.T_le_normV₁

theorem conjClosure_le_N : conjClosure V H ≤ Subgroup.normalizer (V₁ : Set G) :=
  conjClosure_le fun _ hh _ hv =>
    (Subgroup.normalizer (V₁ : Set G)).mul_mem
      ((Subgroup.normalizer (V₁ : Set G)).mul_mem (hb.H_le hh) (hb.V_le_N hv))
      ((Subgroup.normalizer (V₁ : Set G)).inv_mem (hb.H_le hh))

end AlmostSpecialBase

namespace G22Conclusion

variable {V V₁ L T H : Subgroup G}

theorem commutator_mem (hb : AlmostSpecialBase V V₁ L T H) (hg : G22Conclusion V V₁ T H)
    {x y : G} (hx : x ∈ conjClosure V H) (hy : y ∈ conjClosure V H) :
    x * y * x⁻¹ * y⁻¹ ∈ V₁ := by
  have hU := hg.one.2
  have hcc := hb.conjClosure_le_N
  have hmemY : ∀ u (hu : u ∈ conjClosure V H),
      tmk V₁ ⟨u, hcc hu⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
    fun u hu => (secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu
  have hyQ : tmk V₁ ⟨y, hcc hy⟩ ∈ tildeOf V₁ (pCoreOf 2 H) :=
    omegaOneCenterOf_le _ (hmemY y hy)
  have hxy : tmk V₁ ⟨x, hcc hx⟩ * tmk V₁ ⟨y, hcc hy⟩ =
      tmk V₁ ⟨y, hcc hy⟩ * tmk V₁ ⟨x, hcc hx⟩ :=
    (mem_centralizer_of_mem_omegaOneCenterOf (hmemY x hx) hyQ).symm
  exact commutator_mem_of_secMk_commute hxy

theorem sq_mem (hb : AlmostSpecialBase V V₁ L T H) (hg : G22Conclusion V V₁ T H)
    {x : G} (hx : x ∈ conjClosure V H) : x ^ 2 ∈ V₁ := by
  have hU := hg.one.2
  have hcc := hb.conjClosure_le_N
  have h1 := sq_eq_one_of_mem_omegaOneCenterOf ((secImg_le_iff.1 hU) ⟨x, hcc hx⟩ hx)
  rw [← map_pow] at h1
  simpa using secMk_eq_one_iff.1 h1

end G22Conclusion

theorem le_normalizer_sup_of_conj_mem {X A B : Subgroup G}
    (hA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A ⊔ B) (hB : ∀ x ∈ X, ∀ b ∈ B, x * b * x⁻¹ ∈ A ⊔ B) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun x hx w hw => ?_
  rw [Subgroup.sup_eq_closure] at hw
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hA x hx y hy
    · exact hB x hx y hy
  | one => simp
  | mul y z _ _ ihy ihz =>
    have : x * (y * z) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ih =>
    have : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ih

theorem le_normalizer_conjClosure_of_normalizes {V₁ L X : Subgroup G}
    (h1 : X ≤ Subgroup.normalizer (V₁ : Set G)) (h2 : X ≤ Subgroup.normalizer (L : Set G)) :
    X ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) := by
  refine le_normalizer_of_conj_mem fun x hx w hw => ?_
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, z, hz, rfl⟩ := hy
    have hxl : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h2 hx) l).1 hl
    have hxz : x * z * x⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 (h1 hx) z).1 hz
    have : x * (l * z * l⁻¹) * x⁻¹ = (x * l * x⁻¹) * (x * z * x⁻¹) * (x * l * x⁻¹)⁻¹ := by group
    rw [this]
    exact mem_conjClosure hxl hxz
  | one => simp
  | mul y z _ _ ihy ihz =>
    have : x * (y * z) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ih =>
    have : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ih

theorem conjClosure_le_sup_of_normalizes {V₁ L U : Subgroup G} (hV₁U : V₁ ≤ U)
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) : conjClosure V₁ L ≤ L ⊔ U := by
  refine conjClosure_le fun l hl z hz => ?_
  have hzL : z * l⁻¹ * z⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hUL (hV₁U hz)) l⁻¹).1 (L.inv_mem hl)
  have h1 : l * (z * l⁻¹ * z⁻¹) ∈ L := L.mul_mem hl hzL
  have : l * z * l⁻¹ = (l * (z * l⁻¹ * z⁻¹)) * z := by group
  rw [this]
  exact Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ U) h1) ((le_sup_right : U ≤ L ⊔ U) (hV₁U hz))

theorem I_eq_sup_of_hom [Finite G] {L U I O : Subgroup G} {M : Type*} [Group M]
    (Φ : ↥(L ⊔ U) →* M) {g : G} (hL : L = oTwoUpper L) (hgL : g ∈ L)
    (hI : I = U ⊔ rconj U g) (hOU : O ≤ Subgroup.normalizer (U : Set G)) (hO2 : IsPGroup 2 O)
    (hker : ∀ x : ↥(L ⊔ U), Φ x = 1 → (x : G) ∈ O)
    (hgen : ∀ x : ↥(L ⊔ U), ∃ i : ↥(L ⊔ U), (i : G) ∈ I ∧ Φ i = Φ x) : I = L ⊔ U := by
  refine eq_sup_of_normal_closure (T₀ := O ⊓ (L ⊔ U)) hL hgL hI (fun x hx => hOU hx.1)
    (hO2.to_le inf_le_left) inf_le_right ?_
  intro x hx
  obtain ⟨i, hiI, hi⟩ := hgen ⟨x, hx⟩
  refine ⟨x * (i : G)⁻¹, ⟨?_, ?_⟩, i, hiI, by group⟩
  · have h1 : Φ (⟨x, hx⟩ * i⁻¹) = 1 := by rw [map_mul, map_inv, ← hi, mul_inv_cancel]
    exact hker _ h1
  · exact Subgroup.mul_mem _ hx (inv_mem i.2)

theorem inf_le_of_central_odd_index [Finite G] {L Sx P C : Subgroup G} (hL : L = oTwoUpper L)
    (hPSx : P ≤ Sx) (hPn : L ≤ Subgroup.normalizer (P : Set G))
    (hcent : ∀ k ∈ L ⊓ Sx, ∀ y ∈ L, k * y * k⁻¹ * y⁻¹ ∈ P) (hSx2 : IsPGroup 2 ↥(L ⊓ Sx))
    (hCP : L ⊓ Sx ⊓ C ≤ P)
    (hodd : ¬ 2 ∣ ((L ⊓ Sx).subgroupOf L ⊔ C.subgroupOf L).index) : L ⊓ Sx ≤ P := by
  have hBn : ((L ⊓ P).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hPn hl⟩
  have key := le_of_central_modulo_two_splitting (Γ := L) (B := (L ⊓ P).subgroupOf L)
    (K := (L ⊓ Sx).subgroupOf L) (C := C.subgroupOf L)
    (fun b hb => Subgroup.mem_subgroupOf.2 ⟨b.2, hPSx (Subgroup.mem_subgroupOf.1 hb).2⟩)
    (fun k hk y => by
      have hk' := Subgroup.mem_subgroupOf.1 hk
      exact Subgroup.mem_subgroupOf.2
        ⟨(k * y * k⁻¹ * y⁻¹ : L).2, hcent _ hk' _ y.2⟩)
    (hSx2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm)
    (by
      intro x hx
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
      have h1' := Subgroup.mem_subgroupOf.1 h1
      have h2' := Subgroup.mem_subgroupOf.1 h2
      exact Subgroup.mem_subgroupOf.2 ⟨x.2, hCP ⟨h1', h2'⟩⟩)
    hodd (fun N _ hN => eq_top_of_oTwoUpper_eq hL N hN)
  intro k hk
  have h1 : (⟨k, hk.1⟩ : L) ∈ (L ⊓ Sx).subgroupOf L := Subgroup.mem_subgroupOf.2 hk
  exact (Subgroup.mem_subgroupOf.1 (key h1)).2

theorem commutator_inter_le_of {U I VL V₁ : Subgroup G} {g : G} (hI : I = U ⊔ rconj U g)
    (hIVL : I ≤ Subgroup.normalizer (VL : Set G))
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V₁) (hV₁VL : V₁ ≤ VL)
    (hgV : rconj V₁ g ≤ VL) : ⁅U ⊓ rconj U g, I⁆ ≤ VL := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  show x * y * x⁻¹ * y⁻¹ ∈ VL
  have hy' : y ∈ U ⊔ rconj U g := hI ▸ hy
  clear hy
  rw [Subgroup.sup_eq_closure] at hy'
  induction hy' using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hV₁VL (hcomm x hx.1 y hy)
    · apply hgV
      have hx2 : g * x * g⁻¹ ∈ U := mem_rconj.1 hx.2
      have hy2 : g * y * g⁻¹ ∈ U := mem_rconj.1 hy
      rw [mem_rconj]
      have h := hcomm _ hx2 _ hy2
      have : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
          (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
      rwa [this]
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hyI : y ∈ I := by
      rw [hI, Subgroup.sup_eq_closure]; exact hy
    have h1 : y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ ∈ VL :=
      (Subgroup.mem_normalizer_iff.1 (hIVL hyI) _).1 ihz
    have : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
    rw [this]
    exact VL.mul_mem ihy h1
  | inv y hy ih =>
    have hyI : y ∈ I := by
      rw [hI, Subgroup.sup_eq_closure]; exact hy
    have h1 : y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y ∈ VL := by
      have := (Subgroup.mem_normalizer_iff.1 (hIVL (I.inv_mem hyI)) _).1 (VL.inv_mem ih)
      simpa [mul_assoc] using this
    have : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y := by group
    rw [this]
    exact h1

theorem sx_facts_gen [Finite G] {L U I T : Subgroup G} (hI' : I = L ⊔ U) (hUT : U ≤ T)
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLT : IsSylowTwoOf T (L ⊔ T)) :
    I ≤ L ⊔ T ∧ pCoreOf 2 I ≤ pCoreOf 2 (L ⊔ T) ∧ pCoreOf 2 I ≤ T ∧
      (∀ x ∈ I, ∀ y ∈ pCoreOf 2 I, x * y * x⁻¹ ∈ pCoreOf 2 I) ∧
      (∀ y ∈ pCoreOf 2 I, ∀ x ∈ U, y * x * y⁻¹ ∈ U) := by
  have hIle : I ≤ L ⊔ T := hI' ▸ sup_le_sup_left hUT L
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hTnorm : T ≤ Subgroup.normalizer (I : Set G) := by
    rw [hI']
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_sup L U (Subgroup.mem_inf.2 ⟨hTL ht, hTU ht⟩)
  have hLTn : L ⊔ T ≤ Subgroup.normalizer (I : Set G) :=
    sup_le (hLI.trans Subgroup.le_normalizer) hTnorm
  have hSxO : pCoreOf 2 I ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 I).trans hIle)
      (hLTn.trans (normalizer_le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
  have hSxT : pCoreOf 2 I ≤ T := hSxO.trans (pCoreOf_two_le_of_isSylowTwoOf hLT)
  exact ⟨hIle, hSxO, hSxT,
    fun x hx y hy => (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 I hx) y).1 hy,
    fun y hy x hx => (Subgroup.mem_normalizer_iff.1 (hTU (hSxT hy)) x).1 hx⟩

theorem eq_one_of_pow_three_of_pow_two_pow {M : Type*} [Group M] {x : M} {k : ℕ}
    (h3 : x ^ 3 = 1) (h2 : x ^ 2 ^ k = 1) : x = 1 := by
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h : x ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨h3, h2⟩
  rwa [hcop, pow_one] at h

theorem pCoreOf_I_eq_of_le {U I : Subgroup G} {g : G} (hI : I = U ⊔ rconj U g) (hgI : g ∈ I)
    (hINorm : ∀ x ∈ I, ∀ y ∈ pCoreOf 2 I, x * y * x⁻¹ ∈ pCoreOf 2 I)
    (hSxU : ∀ y ∈ pCoreOf 2 I, ∀ x ∈ U, y * x * y⁻¹ ∈ U)
    (hle : pCoreOf 2 I ≤ (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g) :
    pCoreOf 2 I = (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g ∧
      ((pCoreOf 2 I : Subgroup G) : Set G) =
        ((U ⊓ pCoreOf 2 I : Subgroup G) : Set G) *
          ((rconj (U ⊓ pCoreOf 2 I) g : Subgroup G) : Set G) := by
  have hUI : U ≤ I := hI ▸ le_sup_left
  have heq : pCoreOf 2 I = (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g :=
    le_antisymm hle (sup_le inf_le_right (rconj_inf_le_Sx hgI hINorm))
  refine ⟨heq, ?_⟩
  have hnorm := W_le_normalizer_rconj hgI hINorm hUI hSxU
  conv_lhs => rw [heq]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm

end CFSG.Quasithin
