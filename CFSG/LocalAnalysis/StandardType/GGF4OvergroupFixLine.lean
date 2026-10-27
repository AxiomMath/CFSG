module

public import CFSG.LocalAnalysis.StandardType.GGF4OvergroupBs

public section

namespace CFSG.StandardType.F4Over

open Matrix Multiplicative CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem crd_mul (f g : V5) : crd (f * g) = crd f + crd g := funext fun i => toAdd_mul (f i) (g i)

theorem crd_one : crd 1 = 0 := funext fun _ => toAdd_one

theorem crd_inv (f : V5) : crd f⁻¹ = -crd f := funext fun i => toAdd_inv (f i)

theorem crd_pow (f : V5) (n : ℕ) : crd (f ^ n) = n • crd f := funext fun i => toAdd_pow (f i) n

theorem crd_zpow (f : V5) (n : ℤ) : crd (f ^ n) = n • crd f :=
  funext fun i => toAdd_zpow (f i) n

theorem crd_e5_zpow (k : Fin 4) (n : ℤ) : crd (e5 k ^ n) = Pi.single k (n : ZMod 5) := by
  funext l
  rw [crd_zpow]
  show n • crd (e5 k) l = _
  rw [crd_e5, Pi.single_apply, Pi.single_apply]
  split_ifs
  · exact Int.smul_one_eq_cast n
  · exact zsmul_zero n

theorem zpowers_eq_of_crd_eq_smul {z w : V5} {S : ZMod 5} (hS : S ≠ 0)
    (h : crd z = S • crd w) : Subgroup.zpowers z = Subgroup.zpowers w := by
  have key : ∀ S : ZMod 5, S ≠ 0 → ∃ T : ZMod 5, T * S = 1 := by decide
  obtain ⟨T, hT⟩ := key S hS
  have hz : z = w ^ S.val := by
    refine crd_injective ?_
    rw [crd_pow, h, ← Nat.cast_smul_eq_nsmul (ZMod 5), ZMod.natCast_zmod_val]
  have hw : w = z ^ T.val := by
    refine crd_injective ?_
    rw [crd_pow, h, ← Nat.cast_smul_eq_nsmul (ZMod 5), ZMod.natCast_zmod_val, smul_smul, hT,
      one_smul]
  apply le_antisymm
  · rw [Subgroup.zpowers_le, hz]
    exact Subgroup.npow_mem_zpowers w _
  · rw [Subgroup.zpowers_le, hw]
    exact Subgroup.npow_mem_zpowers z _

@[expose] def qf (f : V5) : ZMod 5 := crd f ⬝ᵥ crd f

theorem qf_single (k : Fin 4) (a : ZMod 5) (f : V5) (hf : crd f = Pi.single k a) :
    qf f = a * a := by
  rw [qf, hf, dotProduct_single, Pi.single_eq_same]

theorem qf_of_mem_signedB4 {g : MulAut V5} (hg : g ∈ signedB4) (f : V5) : qf (g f) = qf f := by
  obtain ⟨π, ε, hε, hgf⟩ : SpCoord.IsSignedPerm ⇑g := hg
  simp only [qf, dotProduct, crd]
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hgf f i, mul_mul_mul_comm, SpCoord.coord_sign_mul_self (hε i), one_mul]

theorem halfMat_transpose_mul : ∀ t : Fin 8, (halfMat t)ᵀ * halfMat t = 1 := by decide +kernel

theorem dotProduct_mulVec_self {M : Mat5} (hM : Mᵀ * M = 1) (v : Vec5) :
    (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hM,
    Matrix.one_mulVec]

theorem qf_halfAut (t : Fin 8) (f : V5) : qf (halfAut t f) = qf f := by
  unfold qf
  rw [crd_apply, halfAut, toMat_matAut, dotProduct_mulVec_self (halfMat_transpose_mul t)]

theorem qf_of_mem_stdF4 {g : MulAut V5} (hg : g ∈ stdF4) (f : V5) : qf (g f) = qf f := by
  have hg' : g ∈ Subgroup.closure ((signedB4 : Set (MulAut V5)) ∪ Set.range halfAut) := hg
  clear hg
  induction hg' using Subgroup.closure_induction generalizing f with
  | mem g hg =>
    rcases hg with hg | ⟨t, rfl⟩
    · exact qf_of_mem_signedB4 hg f
    · exact qf_halfAut t f
  | one => rfl
  | mul g h _ _ hg hh => rw [MulAut.mul_apply, hg, hh]
  | inv g _ hg => rw [← hg (g⁻¹ f), MulAut.apply_inv_self]

theorem zpowers_eq_of_swap {r : MulAut V5} (hr : r ∈ stdF4) {i j : Fin 4} (hij : i ≠ j)
    (hri : r (e5 i) ∈ Subgroup.zpowers (e5 j)) (hrj : r (e5 j) ∈ Subgroup.zpowers (e5 i))
    {z : V5} (hz : z ∈ Subgroup.zpowers (e5 i) ⊔ Subgroup.zpowers (e5 j)) (hz1 : z ≠ 1)
    (hrz : r z = z) :
    Subgroup.zpowers z = Subgroup.zpowers (e5 i * e5 j) ∨
      Subgroup.zpowers z = Subgroup.zpowers (e5 i * (e5 j)⁻¹) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hri
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hrj
  obtain ⟨y, hy, w, hw, rfl⟩ := Subgroup.mem_sup.1 hz
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have ha : (n : ZMod 5) * n = 1 := by
    have h := qf_of_mem_stdF4 hr (e5 i)
    rw [← hn, qf_single j (n : ZMod 5) _ (crd_e5_zpow j n), qf_single i 1 _ (crd_e5 i),
      one_mul] at h
    exact h
  have hcrd : crd (e5 i ^ s * e5 j ^ t) = Pi.single i (s : ZMod 5) + Pi.single j (t : ZMod 5) := by
    rw [crd_mul, crd_e5_zpow, crd_e5_zpow]
  have hrcrd : crd (r (e5 i ^ s * e5 j ^ t)) =
      Pi.single j ((n : ZMod 5) * s) + Pi.single i ((m : ZMod 5) * t) := by
    rw [map_mul, map_zpow, map_zpow, ← hn, ← hm, ← _root_.zpow_mul, ← _root_.zpow_mul, crd_mul, crd_e5_zpow,
      crd_e5_zpow, Int.cast_mul, Int.cast_mul]
  have hts : (t : ZMod 5) = n * s := by
    have h := congrFun (hrcrd.symm.trans ((congrArg crd hrz).trans hcrd)) j
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_same,
      Pi.single_eq_of_ne hij.symm, Pi.single_eq_of_ne hij.symm, add_zero, zero_add] at h
    exact h.symm
  have hS : (s : ZMod 5) ≠ 0 := by
    intro h0
    apply hz1
    refine crd_injective ?_
    rw [hcrd, hts, h0, mul_zero, Pi.single_zero, Pi.single_zero, add_zero, crd_one]
  have hpm : ∀ a : ZMod 5, a * a = 1 → a = 1 ∨ a = -1 := by decide
  rcases hpm _ ha with h1 | h1
  · left
    refine zpowers_eq_of_crd_eq_smul hS ?_
    rw [hcrd, hts, h1, one_mul, crd_mul, crd_e5, crd_e5]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> ring
  · right
    refine zpowers_eq_of_crd_eq_smul hS ?_
    rw [hcrd, hts, h1, crd_mul, crd_inv, crd_e5, crd_e5]
    funext k
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> ring

theorem zpowers_eq_of_swap_congr {G : Type} [Group G] {Bs : Subgroup G} (κ : V5 ≃* ↥Bs)
    {r : MulAut ↥Bs} (hr : r ∈ stdF4.map (MulAut.congr κ).toMonoidHom) {i j : Fin 4}
    (hij : i ≠ j) (hri : r (κ (e5 i)) ∈ Subgroup.zpowers (κ (e5 j)))
    (hrj : r (κ (e5 j)) ∈ Subgroup.zpowers (κ (e5 i)))
    {z : ↥Bs} (hz : z ∈ Subgroup.zpowers (κ (e5 i)) ⊔ Subgroup.zpowers (κ (e5 j)))
    (hz1 : z ≠ 1) (hrz : r z = z) :
    Subgroup.zpowers z = Subgroup.zpowers (κ (e5 i * e5 j)) ∨
      Subgroup.zpowers z = Subgroup.zpowers (κ (e5 i * (e5 j)⁻¹)) := by
  obtain ⟨r₀, hr₀, rfl⟩ := Subgroup.mem_map.1 hr
  have hc : ∀ b : ↥Bs, (MulAut.congr κ).toMonoidHom r₀ b = κ (r₀ (κ.symm b)) := fun _ => rfl
  have hmem : ∀ (f : V5) (k : Fin 4), κ f ∈ Subgroup.zpowers (κ (e5 k)) →
      f ∈ Subgroup.zpowers (e5 k) := by
    intro f k h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨n, κ.injective (by rw [map_zpow, hn])⟩
  have hri₀ : r₀ (e5 i) ∈ Subgroup.zpowers (e5 j) := by
    refine hmem _ j ?_
    rw [hc, MulEquiv.symm_apply_apply] at hri
    exact hri
  have hrj₀ : r₀ (e5 j) ∈ Subgroup.zpowers (e5 i) := by
    refine hmem _ i ?_
    rw [hc, MulEquiv.symm_apply_apply] at hrj
    exact hrj
  have hsup : κ.symm z ∈ Subgroup.zpowers (e5 i) ⊔ Subgroup.zpowers (e5 j) := by
    have h := Subgroup.mem_map_of_mem κ.symm.toMonoidHom hz
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using h
  have hz₀ : κ.symm z ≠ 1 := fun h => hz1 (κ.symm.injective (h.trans (map_one κ.symm).symm))
  have hrz₀ : r₀ (κ.symm z) = κ.symm z := by
    have h := congrArg κ.symm hrz
    rwa [hc, MulEquiv.symm_apply_apply] at h
  have hmap : ∀ w : V5, (Subgroup.zpowers w).map κ.toMonoidHom = Subgroup.zpowers (κ w) :=
    fun w => MonoidHom.map_zpowers _ _
  have hz' : Subgroup.zpowers z = (Subgroup.zpowers (κ.symm z)).map κ.toMonoidHom := by
    rw [hmap, MulEquiv.apply_symm_apply]
  rcases zpowers_eq_of_swap hr₀ hij hri₀ hrj₀ hsup hz₀ hrz₀ with h | h
  · exact Or.inl (by rw [hz', h, hmap])
  · exact Or.inr (by rw [hz', h, hmap])

theorem ggF4_zpowers_eq_of_swap
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hEl : IsElemAbelian 5 Bs) (hNT : GGNoTransvection 5 Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    (hA : GGWeylOfType 5 CoxeterMatrix.F₄ A) (κ : V5 ≃* ↥Bs)
    (hH : signedB4.map (MulAut.congr κ).toMonoidHom ≤ A)
    {r : MulAut ↥Bs} (hr : r ∈ A) {i j : Fin 4} (hij : i ≠ j)
    (hri : r (κ (e5 i)) ∈ Subgroup.zpowers (κ (e5 j)))
    (hrj : r (κ (e5 j)) ∈ Subgroup.zpowers (κ (e5 i)))
    {x : G} (hxB : x ∈ Bs)
    (hx : x ∈ Subgroup.zpowers ((κ (e5 i) : ↥Bs) : G) ⊔ Subgroup.zpowers ((κ (e5 j) : ↥Bs) : G))
    (hx1 : x ≠ 1) (hrx : ((r ⟨x, hxB⟩ : ↥Bs) : G) = x) :
    Subgroup.zpowers x = Subgroup.zpowers (((κ (e5 i) : ↥Bs) : G) * (κ (e5 j) : ↥Bs)) ∨
      Subgroup.zpowers x =
        Subgroup.zpowers (((κ (e5 i) : ↥Bs) : G) * ((κ (e5 j) : ↥Bs) : G)⁻¹) := by
  have hr' : r ∈ stdF4.map (MulAut.congr κ).toMonoidHom := by
    rw [← ggF4_eq_stdF4_of_signedB4_le hEl hNT hAind hA κ hH]
    exact hr
  have hsub : ∀ b : ↥Bs, (Subgroup.zpowers b).map Bs.subtype = Subgroup.zpowers (b : G) :=
    fun b => MonoidHom.map_zpowers _ _
  have hx' : (⟨x, hxB⟩ : ↥Bs) ∈ Subgroup.zpowers (κ (e5 i)) ⊔ Subgroup.zpowers (κ (e5 j)) := by
    rw [← Subgroup.mem_map_iff_mem Bs.subtype_injective, Subgroup.map_sup, hsub, hsub]
    exact hx
  have hx1' : (⟨x, hxB⟩ : ↥Bs) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hrx' : r ⟨x, hxB⟩ = ⟨x, hxB⟩ := Subtype.ext hrx
  have hxs : (Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs)).map Bs.subtype = Subgroup.zpowers x :=
    MonoidHom.map_zpowers _ _
  rcases zpowers_eq_of_swap_congr κ hr' hij hri hrj hx' hx1' hrx' with h | h
  · left
    rw [← hxs, h, hsub, map_mul, Subgroup.coe_mul]
  · right
    rw [← hxs, h, hsub, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

end CFSG.StandardType.F4Over

end
