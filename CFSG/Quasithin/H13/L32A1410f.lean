module

public import CFSG.Quasithin.H13.L32A1410e
public import CFSG.Walter.Cited.CentralSplit
public import CFSG.Quasithin.H13.L32A1410d
public import CFSG.Quasithin.H13.L32NLem144Bc

public section

namespace CFSG.Quasithin.H13.G5ACert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert S8Cert G5Cert CFSG.Quasithin

theorem MA5_one_gens_fix (b : Bool) :
    ∀ c ∈ pGA b ++ [(mRA b).getD 1 one8], mv8 c vA = vA := by
  cases b <;> decide +kernel

theorem MA5_one_fixA (b : Bool) {γ : GL (Fin 8) (ZMod 2)} (hγ : γ ∈ MA5 b 1) :
    (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vA) = vec8 vA := by
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rw [mulVec_vec8, MA5_one_gens_fix b _ hx]
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hy, hx]
  | inv x _ hx =>
    calc ((x⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vA)
        = ((x⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
            ((x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vA)) := by rw [hx]
      _ = vec8 vA := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]

theorem kAG_cols : kAG = [colsOf (g5aA0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2))] := by
  decide +kernel

theorem g5aA1_mem_KA5 : g5aA1 ∈ KA5 :=
  Subgroup.subset_closure (show colsOf (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ kAG by
    rw [kAG_cols]; simp)

theorem colsOf_g5aA1 :
    colsOf (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = [3, 5, 9, 1, 48, 80, 144, 16] := by
  decide +kernel

theorem g5aA1_fpf {x : Fin 8 → ZMod 2}
    (hx : (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x = x) : x = 0 := by
  have hchk : ∀ v < 256, mv8 [3, 5, 9, 1, 48, 80, 144, 16] v = v → v = 0 := by decide +kernel
  rw [← vec8_code8 x, mulVec_vec8, colsOf_g5aA1] at hx
  have h := vec8_inj (mv8_lt ⟨rfl, by decide⟩ _) (code8_lt x) hx
  rw [← vec8_code8 x, hchk _ (code8_lt x) h, vec8_zero]

theorem exists_fpf_preimage (y : Fin 8 → ZMod 2) :
    ∃ x, (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x + x = y := by
  have hinj : Function.Injective fun x : Fin 8 → ZMod 2 =>
      (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x + x := by
    intro x₁ x₂ h
    simp only at h
    have h2 : (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (x₁ - x₂) = x₁ - x₂ := by
      rw [Matrix.mulVec_sub]
      have h3 : (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x₁ -
          (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x₂ = x₂ - x₁ := by
        calc (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x₁ -
            (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x₂
            = ((g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x₁ + x₁) - x₁ -
              (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x₂ := by abel
          _ = ((g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x₂ + x₂) - x₁ -
              (g5aA1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x₂ := by rw [h]
          _ = x₂ - x₁ := by abel
      rw [h3]
      ext i
      have h2 : ∀ a c : ZMod 2, a - c = c - a := by decide
      simp only [Pi.sub_apply]
      exact h2 _ _
    exact sub_eq_zero.mp (g5aA1_fpf h2)
  exact (Finite.injective_iff_surjective.mp hinj) y

theorem eq_bot_or_eq_KA5 {N : Subgroup (GL (Fin 8) (ZMod 2))}
    (hNK : N ≤ KA5) (hKN : KA5 ≤ Subgroup.normalizer (N : Set (GL (Fin 8) (ZMod 2)))) :
    N = ⊥ ∨ N = KA5 := by
  have : IsSimpleGroup ↥KA5 := isSimpleGroup_KA5
  have hn : (N.subgroupOf KA5).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf KA5) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hNK] at h
    exact h
  · right
    exact le_antisymm hNK (Subgroup.subgroupOf_eq_top.mp h)

theorem normal_two_KA5 :
    ∀ N : Subgroup ↥KA5, N.Normal → IsPGroup 2 ↥N → N = ⊥ := by
  intro N hN h2
  have : IsSimpleGroup ↥KA5 := isSimpleGroup_KA5
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    subst h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    rw [Subgroup.card_top, card_KA5] at hn
    have hn6 : n ≤ 6 := by
      by_contra hc
      push Not at hc
      have : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
      omega
    interval_cases n <;> norm_num at hn

end CFSG.Quasithin.H13.G5ACert

namespace CFSG.Quasithin.H13.Q1410

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B Mat8Cert G5ACert
  L1442M

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {b : Bool}

theorem H_le_normalizer_preM {M : Subgroup (GL (Fin 8) (ZMod 2))}
    (hM : img8 D e (l32nH T V) ≤ Subgroup.normalizer (M : Set (GL (Fin 8) (ZMod 2)))) :
    l32nH T V ≤ Subgroup.normalizer (preM D e M : Set G) := by
  intro h hh
  refine Subgroup.mem_normalizer_fintype fun k hk => ?_
  have hkH := preM_le_H e M hk
  have hhk : h * k * h⁻¹ ∈ l32nH T V :=
    (l32nH T V).mul_mem ((l32nH T V).mul_mem hh hkH) ((l32nH T V).inv_mem hh)
  show h * k * h⁻¹ ∈ preM D e M
  rw [mem_preM hhk]
  have e1 : matOf e (D.ρ ⟨h, HN hh⟩) * matOf e (D.ρ ⟨k, HN hkH⟩) *
      (matOf e (D.ρ ⟨h, HN hh⟩))⁻¹ = matOf e (D.ρ ⟨h * k * h⁻¹, HN hhk⟩) := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [← e1]
  exact (Subgroup.mem_normalizer_iff.mp (hM ((mem_img8 D e).mpr ⟨h, hh, _, rfl⟩)) _).mp
    ((mem_preM hkH).mp hk)

namespace CtxA

variable (C : CtxA G T L V V₂ g D e b)
include C

theorem KA5_le_imgH : KA5 ≤ img8 D e (l32nH T V) := by
  rw [C.imgH]; exact KA5_le b

theorem img_K0 : img8 D e (preM D e KA5) = KA5 := img_preM C.KA5_le_imgH

theorem H_le_normalizer_K0 : l32nH T V ≤ Subgroup.normalizer (preM D e KA5 : Set G) :=
  H_le_normalizer_preM (by rw [C.imgH]; exact KA5_normal b)

theorem T_le_normalizer_K0 : T ≤ Subgroup.normalizer (preM D e KA5 : Set G) :=
  C.base.TH.trans C.H_le_normalizer_K0

theorem Q_le_K0 : pCoreOf 2 (l32nH T V) ≤ preM D e KA5 := C.base.Q_le_preM e KA5

theorem exists_hom_K0 : ∃ f : ↥(preM D e KA5) →* ↥KA5, Function.Surjective f ∧
    IsPGroup 2 ↥f.ker ∧ ∀ x : ↥(preM D e KA5), x ∈ f.ker ↔ (x : G) ∈ pCoreOf 2 (l32nH T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN := (preM_le_H (D := D) e KA5).trans HN
  have hr : (hom8 D e hXN).range = KA5 := by rw [range_hom8 D e hXN, C.img_K0]
  let f : ↥(preM D e KA5) →* ↥KA5 := (hom8 D e hXN).codRestrict KA5 fun x => hr.le ⟨x, rfl⟩
  have hker : ∀ x : ↥(preM D e KA5), x ∈ f.ker ↔ (x : G) ∈ pCoreOf 2 (l32nH T V) := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx1 : hom8 D e hXN x = 1 := by
        have := congrArg Subtype.val hx
        simpa [f] using this
      exact (C.base.matOf_eq_one_iff D e (preM_le_H e KA5 x.2)).mp hx1
    · intro hx
      apply Subtype.ext
      exact (C.base.matOf_eq_one_iff D e (preM_le_H e KA5 x.2)).mpr hx
  refine ⟨f, ?_, ?_, hker⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨x, hx⟩ := hr.ge hγ
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨x, hx⟩
    have hxQ : (x : G) ∈ pCoreOf 2 (l32nH T V) := (hker x).mp hx
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (l32nH T V) ⟨x, hxQ⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn

theorem nonempty_quot_K0 : Nonempty (oTwoQuot ↥(preM D e KA5) ≃* ↥KA5) := by
  obtain ⟨f, hf, hk, -⟩ := C.exists_hom_K0
  exact nonempty_quot_equiv_of_surj f hf hk normal_two_KA5

theorem pCoreOf_K0 : pCoreOf 2 (preM D e KA5) = pCoreOf 2 (l32nH T V) := by
  obtain ⟨f, hf, hk, hker⟩ := C.exists_hom_K0
  have h := pCore_eq_ker_of_surj f hf hk normal_two_KA5
  show (CFSG.Open.pCore 2 ↥(preM D e KA5)).map (preM D e KA5).subtype = _
  rw [h]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hker y).mp hy
  · intro hx
    exact ⟨⟨x, C.Q_le_K0 hx⟩, (hker _).mpr hx, rfl⟩

theorem card_oTwoQuot_K0 : Nat.card (oTwoQuot ↥(preM D e KA5)) = 60 := by
  obtain ⟨φ⟩ := C.nonempty_quot_K0
  rw [Nat.card_congr φ.toEquiv, card_KA5]

theorem isRankOneListed_K0 :
    IsRankOneListed (oTwoQuot ↥(preM D e KA5)) := by
  obtain ⟨φ⟩ := C.nonempty_quot_K0
  have : IsSimpleGroup ↥KA5 := isSimpleGroup_KA5
  obtain ⟨ψ⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 card_KA5
  exact Or.inl ⟨2, by norm_num, ⟨φ.trans ψ⟩⟩

theorem card_K0_gt : 48 < Nat.card (preM D e KA5) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥(preM D e KA5))
  have h60 : Nat.card (↥(preM D e KA5) ⧸ CFSG.Open.pCore 2 ↥(preM D e KA5)) = 60 :=
    C.card_oTwoQuot_K0
  rw [h60] at h
  have : 0 < Nat.card ↥(CFSG.Open.pCore 2 ↥(preM D e KA5)) := Nat.card_pos
  omega

theorem isSylowTwoOf_K0 : IsSylowTwoOf (T ⊓ preM D e KA5) (preM D e KA5) :=
  A4.isSylowTwoOf_inf_normal
    (isSylowTwoOf_of_quasithinIsSylowTwo C.base.hyp.fsu.sylow le_sup_right) le_sup_left
    (sup_le Subgroup.le_normalizer C.T_le_normalizer_K0)

theorem borelOf_K0_le : borelOf (preM D e KA5) T ≤ Subgroup.normalizer (V₂ : Set G) := by
  intro x hx
  have hxK : x ∈ preM D e KA5 := (Subgroup.mem_inf.mp hx).1
  have hxN := (Subgroup.mem_inf.mp hx).2
  have hxH := preM_le_H e KA5 hxK
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  have hγK : matOf e (D.ρ ⟨x, HN hxH⟩) ∈ KA5 := (mem_preM hxH).mp hxK
  have hγM : matOf e (D.ρ ⟨x, HN hxH⟩) ∈ MA5 b 1 := by
    refine KA5_borel b hγK fun q hq => ?_
    have hqP : q ∈ img8 D e T := by rw [C.imgT]; exact (Subgroup.mem_inf.mp hq).2
    obtain ⟨t, htT, htN, rfl⟩ := (mem_img8 D e).mp hqP
    have htH := C.base.TH htT
    have htK : t ∈ preM D e KA5 := (mem_preM htH).mpr (Subgroup.mem_inf.mp hq).1
    have hc : x * t * x⁻¹ ∈ T ⊓ preM D e KA5 :=
      (Subgroup.mem_normalizer_iff.mp hxN t).mp (Subgroup.mem_inf.mpr ⟨htT, htK⟩)
    have hcH : x * t * x⁻¹ ∈ l32nH T V := C.base.TH (Subgroup.mem_inf.mp hc).1
    have e1 : matOf e (D.ρ ⟨x, HN hxH⟩) * matOf e (D.ρ ⟨t, htN⟩) *
        (matOf e (D.ρ ⟨x, HN hxH⟩))⁻¹ = matOf e (D.ρ ⟨x * t * x⁻¹, HN hcH⟩) := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    refine Subgroup.mem_inf.mpr ⟨(mem_preM hcH).mp (Subgroup.mem_inf.mp hc).2, ?_⟩
    rw [← C.imgT]
    exact (mem_img8 D e).mpr ⟨_, (Subgroup.mem_inf.mp hc).1, _, rfl⟩
  have hfix : D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hxH⟩ (D.π a) = D.π a := by
    apply e.injective
    rw [← matOf_mulVec, C.e_pi_a ha haV]
    exact MA5_one_fixA b hγM
  exact C.base.mem_normalizer_of_fix D ha haV hxH hfix

theorem exists_K0_moves : ∃ a ∈ V₂, ∃ k ∈ preM D e KA5, k * a * k⁻¹ ≠ a := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  obtain ⟨γ, hγ, hγv⟩ := exists_KA5_moves
  have hγ' : γ ∈ img8 D e (preM D e KA5) := by rw [C.img_K0]; exact hγ
  obtain ⟨k, hk, hkN, rfl⟩ := (mem_img8 D e).mp hγ'
  refine ⟨a, ha, k, hk, fun h => hγv ?_⟩
  have h2 : (D.ρ ⟨k, hkN⟩) (D.π a) = D.π a := by
    rw [D.ρ_π _ a (C.base.V2U ha)]
    exact congrArg D.π h
  rw [← C.e_pi_a ha haV, matOf_mulVec, h2]

end CtxA

end CFSG.Quasithin.H13.Q1410

end
