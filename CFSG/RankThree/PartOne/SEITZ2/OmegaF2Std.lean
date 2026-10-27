module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Gen

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Transport

variable {b c : K} {F : OmegaFrame Q b c} {k : Subfield K} {Rat M : Subgroup (V ≃ₗ[K] V)}

theorem Phi_map {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (u w x y : V) :
    Phi Q (g u) (g w) (g x) (g y) = Phi Q u w x y := by
  unfold Phi
  simp only [polar_map_of_mem hg]

theorem std_of_line (R : RatGroupData F k Rat) (hRM : Rat ≤ M) {x y : V} (hx : F.IsRat k x)
    (hy : F.IsRat k y) (hQx : Q x = 0) (hQy : Q y = 0) (hxy : polar Q x y = 0) (hx0 : x ≠ 0)
    (hya : ∀ a : K, y ≠ a • x) (h : ∀ t : K, eichler Q x (t • y) ∈ M) (t : K) :
    eichler Q (F.e 0) (t • F.e 1) ∈ M := by
  obtain ⟨r, hrR, hrx, a, hry⟩ := R.trans x y hx hy hQx hQy hxy hx0 hya
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (R.le_elementary hrR)
  rw [eichler_std_conj hrO hQx hrx hry t]
  exact M.mul_mem (M.mul_mem (hRM hrR) (h t)) (M.inv_mem (hRM hrR))

end Transport

section Std

variable {k : Subfield K} {Rat : Subgroup (V ≃ₗ[K] V)}

theorem std_full_f2 [Finite K] [CharP K 2] (hcore : OmegaF2Core)
    {b c : K} {F : OmegaFrame Q b c} (hb : b = 1) (hc : c = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ p) (hk : Nat.card k = 2) (R : RatGroupData F k Rat)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hne : Rat.map (MulAut.conj g).toMonoidHom ≠ Rat) (t : K) :
    eichler Q (F.e 0) (t • F.e 1) ∈
      Subgroup.closure ((Rat : Set (V ≃ₗ[K] V)) ∪
        (Rat.map (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[K] V))) := by
  subst hb hc
  have hk' : ∀ x : K, x ∈ k ↔ x = 0 ∨ x = 1 := fun x => mem_subfield_two_iff hk
  set M := Subgroup.closure ((Rat : Set (V ≃ₗ[K] V)) ∪
    (Rat.map (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[K] V))) with hMdef
  have hRM : ∀ X ∈ Rat, X ∈ M := fun X hX => Subgroup.subset_closure (Or.inl hX)
  obtain ⟨u', w', x, y, hQu', hQw', huw', hMu, hx, hy, hQx, hQy, hxy, hΦ⟩ :=
    exists_good_line k.one_mem k.one_mem R hg hne
  have hM₁ : eichler Q u' w' ∈ M := by
    have := hMu 1 k.one_mem
    rw [one_smul] at this
    exact Subgroup.subset_closure (Or.inr this)
  have hx0 : x ≠ 0 := fun h0 => hΦ (by
    have : Phi Q u' w' x y = 0 := by
      simp [Phi, h0, polar_zero_left]
    rw [this]
    exact k.zero_mem)
  have hya : ∀ a : K, y ≠ a • x := fun a h => hΦ (by
    have : Phi Q u' w' x y = 0 := by
      rw [h, Phi_smul_right, Phi_self, mul_zero]
    rw [this]
    exact k.zero_mem)
  obtain ⟨r, hrR, hrx, a, hry⟩ := R.trans x y hx hy hQx hQy hxy hx0 hya
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (R.le_elementary hrR)
  have hM₂ : eichler Q (r u') (r w') ∈ M := by
    rw [← eichler_conj hrO]
    exact M.mul_mem (M.mul_mem (hRM _ hrR) hM₁) (M.inv_mem (hRM _ hrR))
  have hΦ' : Phi Q (r u') (r w') (F.e 0) (F.e 1) ∉ k := by
    have h1 := Phi_map hrO u' w' x y
    rw [hrx, hry, Phi_add_right, Phi_smul_right, Phi_self, mul_zero, zero_add] at h1
    rw [h1]
    exact hΦ
  have hRM' : Rat ≤ M := fun X hX => hRM X hX
  rcases lemmaB hk' hp hK R hRM' (by rw [map_of_mem hrO, hQu']) (by rw [map_of_mem hrO, hQw'])
      (by rw [polar_map_of_mem hrO, huw']) hM₂ hΦ' with
    h | ⟨T, u₃, w₃, hT, hQ₃, hQ₃', h₃, hgen, hM₃⟩
  · exact h t
  · have hxx : ∀ i j, i ≠ j → eichler Q (T.x i) (T.x j) ∈ M := fun i j _ =>
      hRM _ (R.eichler_mem _ _ (hT i).1 (hT j).1 (T.Q_x i) (T.polar_xx i j))
    have hxy' : ∀ i j, i ≠ j → eichler Q (T.x i) (T.y j) ∈ M := fun i j hij =>
      hRM _ (R.eichler_mem _ _ (hT i).1 (hT j).2 (T.Q_x i) (by rw [T.polar_xy]; simp [hij]))
    have hfull := hcore K V Q k p hp hp2 hK hk T u₃ w₃ hQ₃ hQ₃' h₃ hgen M hM₃
      (hxx 0 1 (by decide)) (hxx 0 2 (by decide)) (hxx 1 2 (by decide)) hxy'
    have hx0' : T.x 0 ≠ 0 := fun h => by
      have := T.polar_xy 0 0
      rw [h, polar_zero_left] at this
      simp at this
    have hya' : ∀ a : K, T.x 1 ≠ a • T.x 0 := fun a h => by
      have := T.polar_xy 1 1
      rw [h, polar_smul_left_eq, T.polar_xy 0 1] at this
      simp at this
    exact std_of_line R hRM' (hT 0).1 (hT 1).1 (T.Q_x 0) (T.Q_x 1) (T.polar_xx 0 1) hx0' hya'
      hfull t

theorem core_pair_f2 [Finite K] [CharP K 2] (hcore : OmegaF2Core)
    {b c : K} {F : OmegaFrame Q b c} (hb : b = 1) (hc : c = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ p) (hk : Nat.card k = 2)
    (hQnd : (polarBilin Q).Nondegenerate) (R : RatGroupData F k Rat) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hne : Rat.map (MulAut.conj g).toMonoidHom ≠ Rat) :
    Subgroup.closure ((Rat : Set (V ≃ₗ[K] V)) ∪
      (Rat.map (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[K] V))) = elementaryGroup Q := by
  have hck : c ∈ k := by rw [hc]; exact k.one_mem
  set M := Subgroup.closure ((Rat : Set (V ≃ₗ[K] V)) ∪
    (Rat.map (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[K] V))) with hMdef
  have hRM : Rat ≤ M := fun X hX => Subgroup.subset_closure (Or.inl hX)
  have hMle : M ≤ elementaryGroup Q := by
    rw [hMdef, Subgroup.closure_le]
    rintro _ (hX | ⟨X, hX, rfl⟩)
    · exact R.le_elementary hX
    · exact conj_mem_elementaryGroup hg (R.le_elementary hX)
  refine le_antisymm hMle ?_
  have hMO : M ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hMle.trans (elementaryGroup_le_orthogonalGroup Q)
  have hstd : ∀ t : K, eichler Q (F.e 0) (t • F.e 1) ∈ M := fun t =>
    std_full_f2 hcore hb hc hp hp2 hK hk R hg hne t
  have he00 : F.e 0 ≠ 0 := fun h0 => by
    have := F.polar_ef 0 0
    rw [h0, polar_zero_left] at this
    simp at this
  have hf00 : F.f 0 ≠ 0 := fun h0 => by
    have := F.polar_ef 0 0
    rw [h0, polar_zero_right] at this
    simp at this
  have he0 : IsRootCenter Q M (F.e 0) :=
    isRootCenter_of_span6 he00 (F.Q_e 0) F.six F.polar_e0_six
      (fun j t => full_all R hRM hstd (F.isRat_e 0) (F.six_isRat hck j) (F.Q_e 0) (F.six_Q j)
        (F.polar_e0_six j) he00 (fun a h => by
          have := F.polar_zt_six j
          rw [h, polar_smul_right_eq, F.polar_zt_e0, mul_zero] at this
          exact zero_ne_one this) t)
      F.perp_decomp_e0
  have hf0 : IsRootCenter Q M (F.f 0) :=
    isRootCenter_of_span6 hf00 (F.Q_f 0) F.six F.polar_f0_six
      (fun j t => full_all R hRM hstd (F.isRat_f 0) (F.six_isRat hck j) (F.Q_f 0) (F.six_Q j)
        (F.polar_f0_six j) hf00 (fun a h => by
          have := F.polar_zt_six j
          rw [h, polar_smul_right_eq, F.polar_zt_f0, mul_zero] at this
          exact zero_ne_one this) t)
      F.perp_decomp_f0
  exact elementaryGroup_le_of_hypPair hQnd hMO
    ⟨F.e 0, F.f 0, F.Q_e 0, F.Q_f 0, by simpa using F.polar_ef 0 0⟩ he0 hf0

end Std

end CFSG.RankThree.PartOne.SEITZ2
