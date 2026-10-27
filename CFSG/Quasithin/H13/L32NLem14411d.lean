module

public import CFSG.Quasithin.H13.L32NLem14411c
public import CFSG.Quasithin.H13.L32NSet14Gen
public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenZ
public import CFSG.Quasithin.H13.L32NS7Model3
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13.L14411

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert L1442M

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

omit [Finite G] in
theorem L1H : lOne L (fsuV1 T V) ≤ l32nH T V :=
  (oTwoUpper_le _).trans inf_le_right

omit [Finite G] in
theorem L1_eq : lOne L (fsuV1 T V) = oTwoUpper (lOne L (fsuV1 T V)) := by
  unfold lOne
  exact (oTwoUpper_idem _).symm

namespace Ctx

variable (C : Ctx G T L V V₂ g D e)
include C

theorem T_L1 : T ≤ Subgroup.normalizer (lOne L (fsuV1 T V) : Set G) := by
  obtain ⟨_, S⟩ := C.set14
  rw [lOne_eq_L₁Of]
  exact S.T_Lp

theorem relIndex_L1_inf : (lOne L (fsuV1 T V) ⊓ T).relIndex (lOne L (fsuV1 T V)) = 3 := by
  obtain ⟨_, S⟩ := C.set14
  have hP3 : (pCoreOf 2 (lOne L (fsuV1 T V))).relIndex (lOne L (fsuV1 T V)) = 3 := by
    rw [lOne_eq_L₁Of]
    exact S.Lp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPT : pCoreOf 2 (lOne L (fsuV1 T V)) ≤ T :=
    le_of_normalizes (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans L1H)
      (C.T_L1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hPle : pCoreOf 2 (lOne L (fsuV1 T V)) ≤ lOne L (fsuV1 T V) ⊓ T :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hPT
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (lOne L (fsuV1 T V)))
    (lOne L (fsuV1 T V) ⊓ T) (lOne L (fsuV1 T V)) hPle inf_le_left
  rw [hP3] at hmul
  have hdvd : (lOne L (fsuV1 T V) ⊓ T).relIndex (lOne L (fsuV1 T V)) ∣ 3 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
  · exfalso
    have hle : lOne L (fsuV1 T V) ≤ T :=
      (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
    obtain ⟨n, hn⟩ := (C.hyp.fsu.sylow.1.to_le hle).exists_card_eq
    have h3d : 3 ∣ Nat.card (lOne L (fsuV1 T V)) := by
      rw [← hP3]
      exact Dvd.intro _ (Subgroup.relIndex_mul_card _ _)
    rw [hn] at h3d
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3d) (by norm_num)
  · exact h3

theorem relIndex_L1T : T.relIndex (lOne L (fsuV1 T V) ⊔ T) = 3 := by
  have h1 := L32NSet14.card_sup_mul_card_inf C.T_L1
  rw [sup_comm, inf_comm] at h1
  have h2 := Subgroup.relIndex_mul_card (lOne L (fsuV1 T V) ⊓ T) (lOne L (fsuV1 T V))
  rw [C.relIndex_L1_inf, inf_right_comm, inf_idem] at h2
  have h3 := Subgroup.relIndex_mul_card T (lOne L (fsuV1 T V) ⊔ T)
  rw [inf_eq_left.mpr le_sup_right] at h3
  have hpos : 0 < Nat.card ↥(lOne L (fsuV1 T V) ⊓ T) := Nat.card_pos
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have h4 : Nat.card ↥(lOne L (fsuV1 T V) ⊔ T) = 3 * Nat.card T := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, ← h2]
    ring
  rw [h4] at h3
  exact Nat.eq_of_mul_eq_mul_right hTpos (by rw [h3])

theorem L1TH : lOne L (fsuV1 T V) ⊔ T ≤ l32nH T V := sup_le L1H C.TH

theorem exists_L1_move {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) :
    ∃ l, ∃ hl : l ∈ lOne L (fsuV1 T V), D.ρ ⟨l, HN (L1H hl)⟩ (D.π a) ≠ D.π a := by
  obtain ⟨_, S⟩ := C.set14
  by_contra hall
  push Not at hall
  have hN : ∀ l ∈ lOne L (fsuV1 T V), l ∈ Subgroup.normalizer (V₂ : Set G) := fun l hl =>
    C.mem_normalizer_of_fix ha haV (L1H hl) (hall l hl)
  have hle : conjClosure V₂ (L₁Of L (fsuV1 T V)) ≤ V₂ :=
    conjClosure_le fun x hx v hv =>
      (Subgroup.mem_normalizer_iff.mp (hN x (by rw [lOne_eq_L₁Of]; exact hx)) v).mp hv
  rw [S.gen] at hle
  have h := Subgroup.card_le_of_le hle
  rw [S.card_V, C.plane.1.2.1] at h
  norm_num at h

theorem L1_eq_oTwoUpper : lOne L (fsuV1 T V) = oTwoUpper (lOne L (fsuV1 T V) ⊔ T) :=
  eq_oTwoUpper_of_pow_mem le_sup_left
    (fun _ hx => L128P.exists_two_pow_mem_of_le_sup C.hyp.fsu.sylow.1 C.T_L1 le_rfl hx) L1_eq

end Ctx

@[expose] noncomputable def preY (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
    (k : ℕ) : Subgroup G :=
  ((M7 k).comap (hom8 D e (L14332.l32nH_le_normalizer_fsuU T V))).map (l32nH T V).subtype

@[expose] noncomputable def xk (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
    (k : ℕ) : Subgroup G :=
  oTwoUpper (preY (T := T) (V := V) D e k)

omit [Finite G] in
theorem mem_preY {k : ℕ} {y : G} (hyH : y ∈ l32nH T V) :
    y ∈ preY D e k ↔ matOf e (D.ρ ⟨y, HN hyH⟩) ∈ M7 k := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro hy
    exact ⟨⟨y, hyH⟩, hy, rfl⟩

omit [Finite G] in
theorem preY_le_H (k : ℕ) : preY (T := T) (V := V) D e k ≤ l32nH T V :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem xk_le_H (k : ℕ) : xk (T := T) (V := V) D e k ≤ l32nH T V :=
  (oTwoUpper_le _).trans (preY_le_H k)

omit [Finite G] in
theorem oTwoUpper_xk (k : ℕ) : oTwoUpper (xk (T := T) (V := V) D e k) = xk D e k :=
  oTwoUpper_idem _

namespace Ctx

variable (C : Ctx G T L V V₂ g D e)
include C

theorem T_le_preY (k : ℕ) : T ≤ preY D e k := fun t ht =>
  (mem_preY (C.TH ht)).mpr (P7_le_M7 k (by
    rw [← C.imgT]
    exact (mem_img8 D e).mpr ⟨t, ht, _, rfl⟩))

theorem Q_le_preY (k : ℕ) : pCoreOf 2 (l32nH T V) ≤ preY D e k := fun q hq => by
  have hqH : q ∈ l32nH T V := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  rw [mem_preY hqH, (C.matOf_eq_one_iff hqH).mpr hq]
  exact one_mem _

theorem T_le_normalizer_xk (k : ℕ) : T ≤ Subgroup.normalizer (xk D e k : Set G) :=
  (C.T_le_preY k).trans (le_normalizer_oTwoUpper _)

theorem U_le_normalizer_xk (k : ℕ) : fsuU T V ≤ Subgroup.normalizer (xk D e k : Set G) :=
  (C.UQ.trans (C.Q_le_preY k)).trans (le_normalizer_oTwoUpper _)

end Ctx

section Cert


namespace Ctx

variable (C : Ctx G T L V V₂ g D e)
include C

theorem card_img_L1T : Nat.card (img8 D e (lOne L (fsuV1 T V) ⊔ T)) = 48 := by
  rw [card_img8, C.card_img_eq C.L1TH,
    ← Subgroup.relIndex_mul_relIndex (pCoreOf 2 (l32nH T V)) T (lOne L (fsuV1 T V) ⊔ T) C.QT
      le_sup_right, ← C.card_img_eq C.TH, ← card_img8 D e, C.imgT, card_P7, C.relIndex_L1T]

theorem exists_j : ∃ j, (j = 1 ∨ j = 2) ∧ img8 D e (lOne L (fsuV1 T V) ⊔ T) = M7 j := by
  obtain ⟨a, ha, haV⟩ := C.abs.exists_mem_not_mem
  have hle : img8 D e (lOne L (fsuV1 T V) ⊔ T) ≤ s7 := (img8_mono D e C.L1TH).trans C.imgH.le
  have hP : P7 ≤ img8 D e (lOne L (fsuV1 T V) ⊔ T) :=
    C.imgT.ge.trans (img8_mono D e le_sup_right)
  obtain ⟨j, hj, hjeq⟩ := eq_M7_of hle hP C.card_img_L1T
  refine ⟨j, ?_, hjeq⟩
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | h | h
  · exfalso
    obtain ⟨l, hl, hmove⟩ := C.exists_L1_move ha haV
    have hmem : matOf e (D.ρ ⟨l, HN (L1H hl)⟩) ∈ M7 0 := by
      rw [← hjeq]
      exact (mem_img8 D e).mpr ⟨l, Subgroup.mem_sup_left hl, _, rfl⟩
    have := M7_zero_fix hmem
    rw [← C.e_pi_a ha haV, matOf_mulVec] at this
    exact hmove (e.injective this)
  · exact Or.inl h
  · exact Or.inr h

theorem img_L1 {j : ℕ} (hj : j = 1 ∨ j = 2)
    (hjeq : img8 D e (lOne L (fsuV1 T V) ⊔ T) = M7 j) : img8 D e (lOne L (fsuV1 T V)) = O7 j := by
  rw [C.L1_eq_oTwoUpper, img8_oTwoUpper D e (C.L1TH.trans HN), hjeq, oTwoUpper_M7 (by omega)]

theorem img_preY {k : ℕ} (hk : k < 3) : img8 D e (preY D e k) = M7 k := by
  apply le_antisymm
  · intro γ hγ
    obtain ⟨y, hy, hyN, rfl⟩ := (mem_img8 D e).mp hγ
    exact (mem_preY (preY_le_H k hy)).mp hy
  · intro γ hγ
    obtain ⟨h, hh, hhN, rfl⟩ := (mem_img8 D e).mp (by rw [C.imgH]; exact M7_le_s7 hk hγ)
    exact (mem_img8 D e).mpr ⟨h, (mem_preY hh).mpr hγ, hhN, rfl⟩

theorem img_xk {k : ℕ} (hk : k < 3) : img8 D e (xk D e k) = O7 k := by
  rw [xk, img8_oTwoUpper D e ((preY_le_H k).trans HN), C.img_preY hk, oTwoUpper_M7 hk]

theorem relIndex_xk {k : ℕ} (hk : k = 1 ∨ k = 2) :
    (pCoreOf 2 (xk D e k)).relIndex (xk D e k) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk3 : k < 3 := by omega
  have hXN := (xk_le_H (T := T) (V := V) (D := D) (e := e) k).trans HN
  let f : ↥(xk D e k) →* ↥(O7 k) := (hom8 D e hXN).codRestrict (O7 k) fun x => by
    rw [← C.img_xk hk3, ← range_hom8 D e hXN]
    exact ⟨x, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨γ, hγ⟩
    rw [← C.img_xk hk3, ← range_hom8 D e hXN] at hγ
    obtain ⟨x, rfl⟩ := hγ
    exact ⟨x, rfl⟩
  have hker : IsPGroup 2 f.ker := by
    rintro ⟨x, hx⟩
    have hx1 : hom8 D e hXN x = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa [f] using this
    have hxQ : (x : G) ∈ pCoreOf 2 (l32nH T V) := (C.matOf_eq_one_iff (xk_le_H k x.2)).mp hx1
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (l32nH T V) ⟨x, hxQ⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hidx : (CFSG.Open.pCore 2 ↥(xk D e k)).index = 3 := by
    rw [pCore_eq_comap_of_surj f hf hker, Subgroup.index_comap_of_surjective _ hf,
      index_pCore_O7 hk]
  have hsub : ((CFSG.Open.pCore 2 ↥(xk D e k)).map (xk D e k).subtype).subgroupOf (xk D e k) =
      CFSG.Open.pCore 2 ↥(xk D e k) :=
    Subgroup.comap_map_eq_self_of_injective (xk D e k).subtype_injective _
  unfold Subgroup.relIndex pCoreOf
  rw [hsub, hidx]

end Ctx

end Cert

end CFSG.Quasithin.H13.L14411
