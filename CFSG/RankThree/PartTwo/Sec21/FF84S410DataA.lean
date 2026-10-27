module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Dict
public import CFSG.RankThree.PartTwo.Sec21.FF84S48Gen
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {e : ↥S ≃* Multiplicative F6}
  {ψ : ↥(Nor S) →* OmG}

theorem toAdd_e_one : Multiplicative.toAdd (e (1 : ↥S)) = 0 := by simp

theorem eq_one_of_toAdd_e_zero {w : ↥S} (h : Multiplicative.toAdd (e w) = 0) : w = 1 :=
  (toAdd_e_eq_iff (e := e) w 1).1 (h.trans toAdd_e_one.symm)

theorem toAdd_e_mul (x y : ↥S) :
    Multiplicative.toAdd (e (x * y)) = Multiplicative.toAdd (e x) + Multiplicative.toAdd (e y) := by
  simp

@[expose] def wsub (e : ↥S ≃* Multiplicative F6) (W : Subgroup G) : Submodule (ZMod 2) F6 where
  carrier := {v | ∃ w : ↥S, (w : G) ∈ W ∧ Multiplicative.toAdd (e w) = v}
  add_mem' := by
    rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, by simp⟩
  zero_mem' := ⟨1, W.one_mem, by simp⟩
  smul_mem' := by
    rintro c _ ⟨w, hw, rfl⟩
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · exact ⟨1, W.one_mem, by simp⟩
    · exact ⟨w, hw, by simp⟩

variable {s t : ↥S}

theorem mem_T_of_vec (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) {w : ↥S}
    (hw : Multiplicative.toAdd (e w) = 0 ∨ Multiplicative.toAdd (e w) = sig0 ∨
      Multiplicative.toAdd (e w) = tau0 ∨ Multiplicative.toAdd (e w) = sig0 + tau0) :
    (w : G) ∈ Subgroup.closure ({(s : G), (t : G)} : Set G) := by
  rcases hw with h | h | h | h
  · rw [eq_one_of_toAdd_e_zero h]
    exact Subgroup.one_mem _
  · have : w = s := (toAdd_e_eq_iff (e := e) w s).1 (h.trans hes.symm)
    rw [this]
    exact Subgroup.subset_closure (by simp)
  · have : w = t := (toAdd_e_eq_iff (e := e) w t).1 (h.trans het.symm)
    rw [this]
    exact Subgroup.subset_closure (by simp)
  · have : w = s * t := by
      refine (toAdd_e_eq_iff (e := e) w (s * t)).1 ?_
      rw [toAdd_e_mul, hes, het]
      exact h
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem vec_of_mem_T (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) {x : G}
    (hx : x ∈ Subgroup.closure ({(s : G), (t : G)} : Set G)) : x ∈ S :=
  (Subgroup.closure_le S).2 (by
    intro y hy
    rcases hy with rfl | hy
    · exact s.2
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact t.2) hx

theorem data_basic (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) :
    (s : G) ≠ 1 ∧ (t : G) ≠ 1 ∧ (s : G) ≠ (t : G) ∧ S = Op 2 (Cen (s : G)) ∧
      S ≠ Op 2 (Cen (t : G)) ∧ S ≠ Op 2 (Cen ((s : G) * (t : G))) := by
  have hs1 : (s : G) ≠ 1 := fun h => by
    have : s = 1 := Subtype.ext h
    rw [this] at hes
    exact sig0_ne_zero (by rw [← hes]; simp)
  have ht1 : (t : G) ≠ 1 := fun h => by
    have : t = 1 := Subtype.ext h
    rw [this] at het
    exact tau0_ne_zero (by rw [← het]; simp)
  have hst : (s : G) ≠ (t : G) := fun h => by
    have : s = t := Subtype.ext h
    rw [this, het] at hes
    exact absurd hes.symm (by decide)
  have hstu : ((s * t : ↥S) : G) ≠ 1 := fun h => by
    have : s * t = 1 := Subtype.ext h
    have h2 := congrArg (fun w => Multiplicative.toAdd (e w)) this
    simp only [toAdd_e_mul, hes, het, toAdd_e_one] at h2
    exact absurd h2 (by decide)
  refine ⟨hs1, ht1, hst, ?_, ?_, ?_⟩
  · exact ((H.hq s hs1).1 (by rw [hes]; exact qMinus_sig0)).symm
  · intro h
    have := (H.hq t ht1).2 h.symm
    rw [het, qMinus_tau0] at this
    exact absurd this (by decide)
  · intro h
    have h2 := (H.hq (s * t) hstu).2 h.symm
    rw [toAdd_e_mul, hes, het, qMinus_sig0_add_tau0] at h2
    exact absurd h2 (by decide)

theorem M_le_nor (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) :
    CenS (Subgroup.closure ({(s : G), (t : G)} : Set G)) ≤ Nor S := by
  intro x hx
  have hs := (data_basic H hes het).2.2.2.1
  rw [cenS_pair, Subgroup.mem_centralizer_iff] at hx
  have hxs : x ∈ Cen (s : G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hx _ (by simp)).symm
  have := le_nor_op2 (Cen (s : G)) hxs
  rwa [← hs] at this

theorem mem_P2 {g : OmG} : g ∈ P2 ↔ g • sig0 = sig0 ∧ g • tau0 = tau0 := by
  rw [P2, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]

theorem M_psi (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) (n : ↥(Nor S)) :
    (n : G) ∈ CenS (Subgroup.closure ({(s : G), (t : G)} : Set G)) ↔ ψ n ∈ P2 := by
  rw [H.mem_cen_pair_iff, mem_P2, hes, het]

@[expose] noncomputable def phiM (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) :
    ↥(CenS (Subgroup.closure ({(s : G), (t : G)} : Set G))) →* ↥P2 :=
  (ψ.comp (Subgroup.inclusion (M_le_nor H hes het))).codRestrict P2
    (fun n => (M_psi H hes het ⟨n.1, M_le_nor H hes het n.2⟩).1 n.2)

theorem phiM_coe (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0)
    (n : ↥(CenS (Subgroup.closure ({(s : G), (t : G)} : Set G)))) :
    ((phiM H hes het n : ↥P2) : OmG) = ψ ⟨n.1, M_le_nor H hes het n.2⟩ := rfl

theorem phiM_surj (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) : Function.Surjective (phiM H hes het) := by
  intro g
  obtain ⟨n, hn⟩ := H.surj g.1
  have hmem : (n : G) ∈ CenS (Subgroup.closure ({(s : G), (t : G)} : Set G)) :=
    (M_psi H hes het n).2 (by rw [hn]; exact g.2)
  refine ⟨⟨n.1, hmem⟩, Subtype.ext ?_⟩
  rw [phiM_coe]
  exact hn

theorem phiM_ker (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) :
    (phiM H hes het).ker =
      S.subgroupOf (CenS (Subgroup.closure ({(s : G), (t : G)} : Set G))) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : ψ ⟨n.1, M_le_nor H hes het n.2⟩ = 1 := by
      have := congrArg Subtype.val h
      exact this
    exact (H.psi_eq_one_iff _).1 h1
  · intro h
    refine Subtype.ext ?_
    rw [phiM_coe]
    exact (H.psi_eq_one_iff _).2 h

theorem data_CM (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) :
    S ⊓ CenS (CenS (Subgroup.closure ({(s : G), (t : G)} : Set G))) =
      Subgroup.closure ({(s : G), (t : G)} : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.1 hx
    have hfix : ∀ g : OmG, g • sig0 = sig0 → g • tau0 = tau0 →
        g • Multiplicative.toAdd (e ⟨x, hxS⟩) = Multiplicative.toAdd (e ⟨x, hxS⟩) := by
      intro g hg1 hg2
      obtain ⟨⟨n, hn⟩, hnφ⟩ := phiM_surj H hes het ⟨g, mem_P2.2 ⟨hg1, hg2⟩⟩
      have hψ : ψ ⟨n, M_le_nor H hes het hn⟩ = g := by
        have := congrArg Subtype.val hnφ
        exact this
      have hcomm : (n : G) * x = x * n := (Subgroup.mem_centralizer_iff.1 hxC n hn)
      have := (H.comm_iff ⟨n, M_le_nor H hes het hn⟩ ⟨x, hxS⟩).1 hcomm
      rw [hψ] at this
      exact this
    exact mem_T_of_vec hes het (om_pair_fixed (hfix · · ·))
  · intro x hx
    refine Subgroup.mem_inf.2 ⟨vec_of_mem_T H hes het hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ CenS (Subgroup.closure ({(s : G), (t : G)} : Set G)) := hy
    exact (Subgroup.mem_centralizer_iff.1 hy' x hx).symm

theorem data_max (H : OmSet S e ψ) (hes : Multiplicative.toAdd (e s) = sig0)
    (het : Multiplicative.toAdd (e t) = tau0) (W : Subgroup G)
    (hTW : Subgroup.closure ({(s : G), (t : G)} : Set G) ≤ W) (hWS : W ≤ S)
    (hM : CenS (Subgroup.closure ({(s : G), (t : G)} : Set G)) ≤ Nor W) :
    W = Subgroup.closure ({(s : G), (t : G)} : Set G) ∨ W = S := by
  have hsW : (s : G) ∈ W := hTW (Subgroup.subset_closure (by simp))
  have htW : (t : G) ∈ W := hTW (Subgroup.subset_closure (by simp))
  have hσ : sig0 ∈ wsub e W := ⟨s, hsW, hes⟩
  have hτ : tau0 ∈ wsub e W := ⟨t, htW, het⟩
  have hinv : ∀ g : OmG, g • sig0 = sig0 → g • tau0 = tau0 → ∀ w ∈ wsub e W, g • w ∈ wsub e W := by
    intro g hg1 hg2 v hv
    obtain ⟨w, hwW, rfl⟩ := hv
    obtain ⟨⟨n, hn⟩, hnφ⟩ := phiM_surj H hes het ⟨g, mem_P2.2 ⟨hg1, hg2⟩⟩
    have hψ : ψ ⟨n, M_le_nor H hes het hn⟩ = g := by
      have := congrArg Subtype.val hnφ
      exact this
    have hnW : (n : G) * (w : G) * (n : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (hM hn) (w : G)).1 hwW
    refine ⟨⟨(n : G) * (w : G) * (n : G)⁻¹, (M_le_nor H hes het hn (w : G)).1 w.2⟩, hnW, ?_⟩
    rw [← hψ, H.smul_eq]
  rcases om_pair_irred hσ hτ hinv with hspan | htop
  · left
    refine le_antisymm (fun x hx => ?_) hTW
    have hxS : x ∈ S := hWS hx
    have hv : Multiplicative.toAdd (e ⟨x, hxS⟩) ∈ Submodule.span (ZMod 2) {sig0, tau0} := by
      rw [← hspan]
      exact ⟨⟨x, hxS⟩, hx, rfl⟩
    rw [Submodule.mem_span_pair] at hv
    obtain ⟨c, d, hcd⟩ := hv
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    refine mem_T_of_vec hes het (w := ⟨x, hxS⟩) ?_
    rcases hc c with rfl | rfl <;> rcases hc d with rfl | rfl
    · left; rw [← hcd]; simp
    · right; right; left; rw [← hcd]; simp
    · right; left; rw [← hcd]; simp
    · right; right; right; rw [← hcd]; simp
  · right
    refine le_antisymm hWS (fun x hx => ?_)
    have hv : Multiplicative.toAdd (e ⟨x, hx⟩) ∈ wsub e W := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨w, hwW, hw⟩ := hv
    have h1 : w = ⟨x, hx⟩ := (toAdd_e_eq_iff (e := e) w ⟨x, hx⟩).1 hw
    have h2 : (w : G) = x := congrArg Subtype.val h1
    rw [← h2]
    exact hwW

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
