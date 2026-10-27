module

public import CFSG.LocalAnalysis.StandardType.GGHalfGraphCent
public import CFSG.LocalAnalysis.StandardType.GGHalfE6CertDefs
public import CFSG.Timmesfeld.LieEmbed.SLE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open scoped commutatorElement

@[expose] def GGHalfBlk.off : GGHalfBlk → ℕ
  | .L => 0
  | .K => 2
  | .M => 2

@[expose] def GGHalfBlk.lab (b : GGHalfBlk) (c : Fin 6) : Fin 8 :=
  ⟨b.off + c.val, by cases b <;> simp only [GGHalfBlk.off] <;> omega⟩

private theorem ggHalfGraphTheta_lab_mem (b : GGHalfBlk) (c : Fin 6) : b.Lab (b.lab c) := by
  cases b <;> fin_cases c <;>
    simp only [GGHalfBlk.Lab, GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk] <;> omega

private theorem ggHalfGraphTheta_lab_injective (b : GGHalfBlk) :
    Function.Injective (fun c : Fin 6 => b.lab c) := by
  intro c d h
  have hv : b.off + c.val = b.off + d.val := by
    simpa only [GGHalfBlk.lab, Fin.val_mk] using congrArg Fin.val h
  exact Fin.ext (by omega)

private theorem ggHalfGraphTheta_chain_commutator
    {k : Type} [Field k] [CharP k 2]
    {r : Fin 6 → Fin 6 → Fin (Tag.rank .E6) → ℤ}
    (hroot : ∀ i j, i ≠ j → IsRoot .E6 (r i j))
    (hadd : ∀ i j l, i ≠ j → j ≠ l → i ≠ l → r i j + r j l = r i l)
    (hne : ∀ i j k l, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → r i j + r k l ≠ 0)
    (hnot : ∀ i j k l, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → j ≠ k → i ≠ l →
      ¬ IsRoot .E6 (r i j + r k l))
    {i j k' l : Fin 6} (hij : i ≠ j) (hkl : k' ≠ l) (hex : ¬ (k' = j ∧ l = i)) (c d : k) :
    ⁅Minuscule.e6Data_valid.xm k (r i j) c, Minuscule.e6Data_valid.xm k (r k' l) d⁆ =
      if j = k' then Minuscule.e6Data_valid.xm k (r i l) (c * d)
      else if i = l then Minuscule.e6Data_valid.xm k (r k' j) (-(c * d)) else 1 := by
  obtain ⟨hroot', hnot'⟩ := Minuscule.e6Data_valid.commutator_xm k (hroot i j hij)
    (hroot k' l hkl) (hne i j k' l hij hkl hex)
  by_cases hjk : j = k'
  · subst hjk
    have hil : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
    rw [ite_eq_left rfl]
    have hs : r i j + r j l = r i l := hadd i j l hij hkl hil
    obtain ⟨σ, hσ, h⟩ := hroot' (hs ▸ hroot i l hil)
    rw [h, CFSG.Timmesfeld.LieEmbed.isSign_eq_one hσ, one_mul, hs]
  · rw [ite_eq_right hjk]
    by_cases hil : i = l
    · subst hil
      rw [ite_eq_left rfl]
      have hki : k' ≠ i := hkl
      have hkj : k' ≠ j := fun h => hjk h.symm
      have hs : r i j + r k' i = r k' j := by
        rw [add_comm, hadd k' i j hki hij hkj]
      obtain ⟨σ, hσ, h⟩ := hroot' (hs ▸ hroot k' j hkj)
      rw [h, CFSG.Timmesfeld.LieEmbed.isSign_eq_one hσ, one_mul, hs, CharTwo.neg_eq]
    · rw [ite_eq_right hil]
      exact hnot' (hnot i j k' l hij hkl hex hjk hil) c d

theorem ggHalfGraphTheta_exists_slToE6_of_chain
    {k : Type} [Field k] [CharP k 2] [Finite k]
    {r : Fin 6 → Fin 6 → Fin (Tag.rank .E6) → ℤ}
    (hroot : ∀ i j, i ≠ j → IsRoot .E6 (r i j))
    (hadd : ∀ i j l, r i j + r j l = r i l)
    (hne : ∀ i j k l, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → r i j + r k l ≠ 0)
    (hnot : ∀ i j k l, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → j ≠ k → i ≠ l →
      ¬ IsRoot .E6 (r i j + r k l)) :
    ∃ φ : SpecialLinearGroup (Fin 6) k →* ↥(Minuscule.e6Data_valid.minGroup k),
      ∀ (i j : Fin 6) (hij : i ≠ j) (c : k),
        φ (SpecialLinearGroup.transvection hij c) = Minuscule.e6Data_valid.xm k (r i j) c :=
  CFSG.Timmesfeld.LieEmbed.exists_hom_of_steinbergRels (m := 5) (by norm_num)
    (x := fun i j c => Minuscule.e6Data_valid.xm k (r i j) c)
    (fun i j _ c d => (Minuscule.e6Data_valid.xm_add k _ c d).symm)
    (fun i j k' l hij hkl hex c d =>
      ggHalfGraphTheta_chain_commutator hroot (fun i j l _ _ _ => hadd i j l) hne hnot
        hij hkl hex c d)

private theorem ggHalfGraphTheta_isSimpleGroup_sl6 :
    IsSimpleGroup (SpecialLinearGroup (Fin 6) F2) := by
  haveI : Fintype F2 := Fintype.ofFinite F2
  have hcard : Nat.card F2 = 2 := GaloisField.card 2 1 (by omega)
  have hZ : Subgroup.center (SpecialLinearGroup (Fin 6) F2) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    rw [Fintype.card_fin] at hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num : (6 : ℕ) ≠ 0)] at hr
      exact zero_ne_one hr
    have h1 : r = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one r hr0
      rwa [← Nat.card_eq_fintype_card, hcard, pow_one] at this
    rw [Subgroup.mem_bot]
    ext i j
    rw [← hrA, h1]
    simp
  have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 6) F2) :=
    (CFSG.LinearGroups.linear_projective_simple (K := F2) (n := 6) (by norm_num)
      (Or.inl (by norm_num))).2.1
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 6) F2 ≃* SpecialLinearGroup (Fin 6) F2 :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem GGHalfE6Model.exists_theta
   
    (m : GGHalfE6Model) (b : GGHalfBlk) (hb : m.FrameOK b) :
    ∃ θ : SpecialLinearGroup (Fin 6) F2 →* GGE6Two, Function.Injective θ ∧
      ∀ c d : Fin 6, c ≠ d → θ (slE c d) = ggE6x (m.frame b (b.lab c) (b.lab d)) := by
  rw [GGHalfE6Model.FrameOK] at hb
  obtain ⟨hroot0, hneg, hadd0, hne0, hnot0⟩ := hb
  have hlab : ∀ c, b.Lab (b.lab c) := ggHalfGraphTheta_lab_mem b
  have hlab_inj : Function.Injective (fun c : Fin 6 => b.lab c) :=
    ggHalfGraphTheta_lab_injective b
  let r : Fin 6 → Fin 6 → Fin (Tag.rank .E6) → ℤ :=
    fun i j => if i = j then 0 else m.frame b (b.lab i) (b.lab j)
  have hr_ne : ∀ {i j : Fin 6}, i ≠ j → r i j = m.frame b (b.lab i) (b.lab j) := by
    intro i j hij
    change (if i = j then (0 : Fin (Tag.rank .E6) → ℤ) else m.frame b (b.lab i) (b.lab j)) =
      m.frame b (b.lab i) (b.lab j)
    rw [if_neg hij]
  have hr_self : ∀ i : Fin 6, r i i = 0 := by
    intro i
    change (if i = i then (0 : Fin (Tag.rank .E6) → ℤ) else m.frame b (b.lab i) (b.lab i)) = 0
    rw [if_pos rfl]
  have hroot : ∀ i j, i ≠ j → IsRoot .E6 (r i j) := by
    intro i j hij
    rw [hr_ne hij]
    exact (mem_rootFinset).1 (hroot0 (b.lab i) (b.lab j) (hlab i) (hlab j)
      (hlab_inj.ne hij))
  have hadd : ∀ i j l, r i j + r j l = r i l := by
    intro i j l
    by_cases hij : i = j
    · subst hij; rw [hr_self, zero_add]
    by_cases hjl : j = l
    · subst hjl; rw [hr_self, add_zero]
    by_cases hil : i = l
    · rw [← hil, hr_self i, hr_ne hij, hr_ne (Ne.symm hij),
        hneg (b.lab i) (b.lab j) (hlab i) (hlab j) (hlab_inj.ne hij), add_neg_cancel]
    · rw [hr_ne hij, hr_ne hjl, hr_ne hil]
      exact hadd0 (b.lab i) (b.lab j) (b.lab l) (hlab i) (hlab j) (hlab l)
        (hlab_inj.ne hij) (hlab_inj.ne hjl) (hlab_inj.ne hil)
  have hne : ∀ i j k l, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → r i j + r k l ≠ 0 := by
    intro i j k l hij hkl hex
    rw [hr_ne hij, hr_ne hkl]
    exact hne0 (b.lab i) (b.lab j) (b.lab k) (b.lab l) (hlab i) (hlab j) (hlab k)
      (hlab l) (hlab_inj.ne hij) (hlab_inj.ne hkl)
      (fun h => hex ⟨hlab_inj h.1, hlab_inj h.2⟩)
  have hnot : ∀ i j k l, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → j ≠ k → i ≠ l →
      ¬ IsRoot .E6 (r i j + r k l) := by
    intro i j k l hij hkl hex hjk hil hsum
    rw [hr_ne hij, hr_ne hkl] at hsum
    exact hnot0 (b.lab i) (b.lab j) (b.lab k) (b.lab l) (hlab i) (hlab j) (hlab k)
      (hlab l) (hlab_inj.ne hij) (hlab_inj.ne hkl)
      (fun h => hex ⟨hlab_inj h.1, hlab_inj h.2⟩) (hlab_inj.ne hjk) (hlab_inj.ne hil)
      ((mem_rootFinset).2 hsum)
  obtain ⟨θ, hθ⟩ :=
    ggHalfGraphTheta_exists_slToE6_of_chain (k := GaloisField 2 1) hroot hadd hne hnot
  refine ⟨θ, ?_, ?_⟩
  · haveI : IsSimpleGroup (SpecialLinearGroup (Fin 6) F2) :=
      ggHalfGraphTheta_isSimpleGroup_sl6
    have h01 : (0 : Fin 6) ≠ 1 := by decide
    have hx0 : θ (slE 0 1) = ggE6x (m.frame b (b.lab 0) (b.lab 1)) := by
      rw [slE, dif_neg h01, hθ 0 1 h01 1, hr_ne h01]
      rfl
    have hxne : ggE6x (m.frame b (b.lab 0) (b.lab 1)) ≠ 1 := by
      change Minuscule.e6Data_valid.xm (GaloisField 2 1)
        (m.frame b (b.lab 0) (b.lab 1)) 1 ≠ 1
      have hγ : IsRoot .E6 (m.frame b (b.lab 0) (b.lab 1)) := by
        rw [← hr_ne h01]; exact hroot 0 1 h01
      intro h1
      have : (1 : F2) = 0 :=
        (Minuscule.e6Data_valid.xm_injective (GaloisField 2 1) hγ)
          (by rw [h1, Minuscule.e6Data_valid.xm_zero])
      exact one_ne_zero this
    have hθne : θ ≠ 1 := by
      intro hθ1
      have h1 : θ (slE 0 1) = 1 := by rw [hθ1]; rfl
      exact hxne (hx0.symm.trans h1)
    have hker : θ.ker = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal θ.ker with h | h
      · exact h
      · exfalso
        have hθ1 : θ = 1 := MonoidHom.ext fun x => by
          have hx : x ∈ θ.ker := by rw [h]; exact Subgroup.mem_top x
          simpa [MonoidHom.mem_ker] using hx
        exact hθne hθ1
    exact (MonoidHom.ker_eq_bot_iff θ).1 hker
  · intro c d hcd
    rw [slE, dif_neg hcd, hθ c d hcd 1, hr_ne hcd]
    rfl

end CFSG.StandardType

end
