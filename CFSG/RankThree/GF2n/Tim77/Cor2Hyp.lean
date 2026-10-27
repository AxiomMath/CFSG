module

public import CFSG.RankThree.GF2n.Tim77Prop24Conj
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_conj {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A) (g : G) :
    IsElemAbelian p (conjSubgroup g A) := by
  obtain ⟨hc, h2⟩ := hA
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    have h := congrArg Subtype.val (hc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg _ h
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, h2 x' hx', map_one]

theorem Prop24Setup.not_isPGroup
    {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
    (hP : IsPGroup 2 ↥(A ⊔ Ab)) : False := by
  have hMX : M ≤ A ⊔ Ab := by
    rw [S.hM]
    exact sup_le_sup S.L_le S.Lb_le
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥(A ⊔ Ab) := hP.isNilpotent
  haveI hN : (M.subgroupOf (A ⊔ Ab)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMX).mpr S.sup_le_normalizer_M
  have hne : M.subgroupOf (A ⊔ Ab) ≠ ⊥ := by
    intro h
    apply S.ne_bot
    rw [eq_bot_iff]
    intro l hl
    have hlX : l ∈ A ⊔ Ab := hMX (S.L_le_M hl)
    have : (⟨l, hlX⟩ : ↥(A ⊔ Ab)) ∈ M.subgroupOf (A ⊔ Ab) := S.L_le_M hl
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  obtain ⟨⟨m, hm⟩, hm1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hmM, hmZ⟩ := Subgroup.mem_inf.mp hm
  obtain ⟨a, ha, haL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hcomm : ∀ x ∈ A ⊔ Ab, x * (m : G) = m * x := by
    intro x hx
    have := Subgroup.mem_center_iff.mp hmZ ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hmM' : (m : G) ∈ M := hmM
  have h1 := S.mem_L_of_commute_M ha haL hmM' (hcomm a (Subgroup.mem_sup_left ha))
  have h2 := S.symm.mem_L_of_commute_M hb hbL hmM' (hcomm b (Subgroup.mem_sup_right hb))
  have h3 : (m : G) ∈ A ⊓ Ab := Subgroup.mem_inf.mpr ⟨S.L_le h1, S.Lb_le h2⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot] at h3
  exact hm1 (Subtype.ext (Subtype.ext h3))

theorem commute_of_isPGroup {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A) {g h : G}
    (hP : IsPGroup 2 ↥(conjSubgroup g A ⊔ conjSubgroup h A))
    (hN : normalizerIn (conjSubgroup g A) (conjSubgroup h A) ≠ ⊥) :
    ∀ x ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup h A, x * y = y * x := by
  set B := conjSubgroup g A with hB
  set C := conjSubgroup h A with hC
  have hBel : IsElemAbelian 2 B := isElemAbelian_conj hA g
  have hBTI : IsTI B := isTI_conjSubgroup hTI g
  have hCB : C = conjSubgroup (h * g⁻¹) B := by
    rw [hB, hC, ← conjSubgroup_mul, inv_mul_cancel_right]
  by_cases hL : normalizerIn B C = B
  ·
    have hCel : IsElemAbelian 2 C := isElemAbelian_conj hA h
    have hCTI : IsTI C := isTI_conjSubgroup hTI h
    have hBC : B = conjSubgroup (g * h⁻¹) C := by
      rw [hB, hC, ← conjSubgroup_mul, inv_mul_cancel_right]
    have hle : conjSubgroup (g * h⁻¹) C ≤ normalizer (C : Set G) := by
      rw [← hBC, ← hL]
      exact inf_le_right
    have hel := tim77_2_3 hCel hCTI hle
    intro x hx y hy
    have hx' : x ∈ C ⊔ conjSubgroup (g * h⁻¹) C := Subgroup.mem_sup_right (hBC ▸ hx)
    have hy' : y ∈ C ⊔ conjSubgroup (g * h⁻¹) C := Subgroup.mem_sup_left hy
    exact congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx'⟩ ⟨y, hy'⟩)
  · exfalso
    have S : Prop24Setup B C (normalizerIn B C) (normalizerIn C B)
        (normalizerIn B C ⊔ normalizerIn C B) :=
      { elem := hBel
        ti := hBTI
        conj := ⟨h * g⁻¹, hCB⟩
        hL := rfl
        hLb := rfl
        hM := rfl
        ne_bot := hN
        ne := hL }
    exact S.not_isPGroup hP

omit [Finite G] in
theorem sq_mem_commutator_weakClosure {A : Subgroup G} (hA : IsElemAbelian 2 A) (C : Subgroup G)
    {w : G} (hw : w ∈ weakClosure A C) :
    w ^ 2 ∈ ⁅weakClosure A C, weakClosure A C⁆ := by
  have hw' := hw
  unfold weakClosure at hw'
  induction hw' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, -, hxg⟩ := hx
    rw [(isElemAbelian_conj hA g).2 x hxg]
    exact one_mem _
  | one => rw [one_pow]; exact one_mem _
  | mul x y hx hy ihx ihy =>
    have hx' : x ∈ weakClosure A C := hx
    have hy' : y ∈ weakClosure A C := hy
    have e : (x * y) ^ 2 = x ^ 2 * ⁅x⁻¹, y⁆ * y ^ 2 := by
      rw [sq, sq, sq, commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem (ihx hx') (Subgroup.commutator_mem_commutator (inv_mem hx') hy'))
      (ihy hy')
  | inv x hx ihx =>
    have hx' : x ∈ weakClosure A C := hx
    rw [inv_pow]
    exact inv_mem (ihx hx')

omit [Finite G] in
theorem isPGroup_weakClosure {A : Subgroup G} (hA : IsElemAbelian 2 A) (C : Subgroup G)
    (hW : ⁅weakClosure A C, weakClosure A C⁆ ≤ A) : IsPGroup 2 ↥(weakClosure A C) := by
  rintro ⟨w, hw⟩
  refine ⟨2, Subtype.ext ?_⟩
  have h1 : w ^ 2 ∈ A := hW (sq_mem_commutator_weakClosure hA C hw)
  have h2 := hA.2 _ h1
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul]
  exact h2

omit [Finite G] in
theorem conj_le_weakClosure {A C : Subgroup G} {g : G} (hg : conjSubgroup g A ≤ C) :
    conjSubgroup g A ≤ weakClosure A C := by
  intro x hx
  unfold weakClosure
  exact Subgroup.subset_closure ⟨g, hg, hx⟩

theorem isRootTypeIn_centralizer {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hW : ⁅weakClosure A (centralizer (A : Set G)), weakClosure A (centralizer (A : Set G))⁆ ≤ A)
    {g : G} (hg : conjSubgroup g A ≤ centralizer (A : Set G)) :
    IsRootTypeIn 2 (centralizer (A : Set G)) (conjSubgroup g A) := by
  have hP := isPGroup_weakClosure hA _ hW
  have hconj : ∀ h ∈ centralizer (A : Set G),
      conjSubgroup h (conjSubgroup g A) ≤ centralizer (A : Set G) := by
    intro h hh x hx
    rw [mem_conjSubgroup] at hx
    have := mul_mem (mul_mem hh (hg hx)) (inv_mem hh)
    simpa [mul_assoc] using this
  refine ⟨hg, isElemAbelian_conj hA g, fun h _ => ?_, fun h hh hN => ?_⟩
  · rcases (isTI_conjSubgroup hTI g) h with e | e
    · exact Or.inr e
    · exact Or.inl e
  · have hhg := hconj h hh
    rw [← conjSubgroup_mul] at hhg hN ⊢
    have hle : conjSubgroup g A ⊔ conjSubgroup (h * g) A ≤
        weakClosure A (centralizer (A : Set G)) :=
      sup_le (conj_le_weakClosure hg) (conj_le_weakClosure hhg)
    exact commute_of_isPGroup hA hTI (hP.to_le hle) hN

end CFSG.RankThree.GF2n.Tim77

namespace CFSG.Timmesfeld.RootInvolutions

variable {G : Type} [Group G] [Finite G]

theorem ElementaryAbelianTIWeakClosureHypothesis.toRootCentralizer {A : Subgroup G}
    (h : ElementaryAbelianTIWeakClosureHypothesis A) :
    ElementaryAbelianTIRootCentralizerHypothesis A where
  elemAbelian := h.elemAbelian
  ti := h.ti
  sylow := h.sylow
  rootTypeInCentralizer _ hg :=
    CFSG.RankThree.GF2n.Tim77.isRootTypeIn_centralizer h.elemAbelian h.ti h.derived_le hg

end CFSG.Timmesfeld.RootInvolutions
