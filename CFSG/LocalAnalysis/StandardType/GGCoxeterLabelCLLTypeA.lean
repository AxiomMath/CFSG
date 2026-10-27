module

public import CFSG.LocalAnalysis.StandardType.GGWeylCasePrime
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Conj

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem conj_apply_of_reflection_formula {Q S : M →ₗ[R] M} {x y : M} {f g : Module.Dual R M}
    (hQ : ∀ w, Q w = w - f w • x) (hS : ∀ w, S w = w - g w • y) (hg : g y = 2) (z : M) :
    S (Q (S z)) = z - (f z - f y * g z) • (x - g x • y) := by
  rw [hS z, hQ, hS]
  simp only [map_sub, map_smul, smul_eq_mul, hg]
  module

end Conj

section Chain

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (m : ℕ) (hJ : ℕ → M)
  (αJ : ℕ → Module.Dual R M) (ha : M) (αa : Module.Dual R M)

noncomputable def ggChainCoroot (k : ℕ) : M := ha + ∑ j ∈ Finset.Ico k m, hJ j

noncomputable def ggChainRoot (k : ℕ) : Module.Dual R M := αa + ∑ j ∈ Finset.Ico k m, αJ j

variable {m hJ αJ ha αa}

structure GGChainPairing (m : ℕ) (hJ : ℕ → M) (αJ : ℕ → Module.Dual R M) (ha : M)
    (αa : Module.Dual R M) : Prop where
  jj : ∀ j k, j < m → k < m →
    αJ j (hJ k) = if j = k then 2 else if j + 1 = k ∨ k + 1 = j then -1 else 0
  ja : ∀ j, j < m → αJ j ha = if j + 1 = m then -1 else 0
  aj : ∀ j, j < m → αa (hJ j) = if j + 1 = m then -1 else 0
  aa : αa ha = 2

theorem GGChainPairing.sum_jj (hP : GGChainPairing m hJ αJ ha αa) {k : ℕ} (hk : k < m) :
    ∑ j ∈ Finset.Ico (k + 1) m, αJ k (hJ j) = if k + 1 = m then 0 else -1 := by
  split_ifs with hk1
  · rw [hk1, Finset.Ico_self, Finset.sum_empty]
  · rw [Finset.sum_eq_single (k + 1)]
    · rw [hP.jj k (k + 1) hk (by omega)]
      simp
    · intro j hj hjk
      rw [Finset.mem_Ico] at hj
      rw [hP.jj k j hk hj.2]
      split_ifs <;> first | rfl | (exfalso; omega)
    · intro h
      exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) h

theorem GGChainPairing.sum_aj (hP : GGChainPairing m hJ αJ ha αa) {k : ℕ} (hk : k < m) :
    ∑ j ∈ Finset.Ico (k + 1) m, αJ j (hJ k) = if k + 1 = m then 0 else -1 := by
  split_ifs with hk1
  · rw [hk1, Finset.Ico_self, Finset.sum_empty]
  · rw [Finset.sum_eq_single (k + 1)]
    · rw [hP.jj (k + 1) k (by omega) hk]
      simp
    · intro j hj hjk
      rw [Finset.mem_Ico] at hj
      rw [hP.jj j k hj.2 hk]
      split_ifs <;> first | rfl | (exfalso; omega)
    · intro h
      exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) h

theorem GGChainPairing.root_coroot_succ (hP : GGChainPairing m hJ αJ ha αa) {k : ℕ}
    (hk : k < m) : αJ k (ggChainCoroot m hJ ha (k + 1)) = -1 := by
  rw [ggChainCoroot, map_add, map_sum, hP.ja k hk, hP.sum_jj hk]
  split_ifs <;> simp

theorem GGChainPairing.chainRoot_succ_apply (hP : GGChainPairing m hJ αJ ha αa) {k : ℕ}
    (hk : k < m) : ggChainRoot m αJ αa (k + 1) (hJ k) = -1 := by
  rw [ggChainRoot, LinearMap.add_apply, LinearMap.sum_apply, hP.aj k hk, hP.sum_aj hk]
  split_ifs <;> simp

theorem ggChainCoroot_of_lt {k : ℕ} (hk : k < m) :
    ggChainCoroot m hJ ha k = hJ k + ggChainCoroot m hJ ha (k + 1) := by
  rw [ggChainCoroot, ggChainCoroot, Finset.sum_eq_sum_Ico_succ_bot hk]
  abel

theorem ggChainRoot_of_lt {k : ℕ} (hk : k < m) :
    ggChainRoot m αJ αa k = αJ k + ggChainRoot m αJ αa (k + 1) := by
  rw [ggChainRoot, ggChainRoot, Finset.sum_eq_sum_Ico_succ_bot hk]
  abel

theorem GGChainPairing.chainRoot_chainCoroot (hP : GGChainPairing m hJ αJ ha αa) :
    ∀ k ≤ m, ggChainRoot m αJ αa k (ggChainCoroot m hJ ha k) = 2 := by
  intro k hk
  obtain ⟨d, hd⟩ : ∃ d, m - k = d := ⟨_, rfl⟩
  induction d generalizing k with
  | zero =>
    have hkm : k = m := by omega
    subst hkm
    simp [ggChainRoot, ggChainCoroot, hP.aa]
  | succ d ih =>
    have hkm : k < m := by omega
    have h := ih (k + 1) (by omega) (by omega)
    rw [ggChainRoot_of_lt hkm, ggChainCoroot_of_lt hkm, LinearMap.add_apply, map_add, map_add,
      h, hP.root_coroot_succ hkm, hP.chainRoot_succ_apply hkm, hP.jj k k hkm hkm]
    simp only [ite_true]
    norm_num

theorem GGChainPairing.sum_ja (hP : GGChainPairing m hJ αJ ha αa) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Ico 0 m, αJ j ha = -1 := by
  rw [Finset.sum_eq_single (m - 1)]
  · rw [hP.ja (m - 1) (by omega)]
    simp [show m - 1 + 1 = m by omega]
  · intro j hj hjm
    rw [Finset.mem_Ico] at hj
    rw [hP.ja j hj.2]
    simp only [ite_eq_right_iff]
    intro h
    omega
  · intro h
    exact absurd (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩) h

theorem GGChainPairing.sum_aj' (hP : GGChainPairing m hJ αJ ha αa) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Ico 0 m, αa (hJ j) = -1 := by
  rw [Finset.sum_eq_single (m - 1)]
  · rw [hP.aj (m - 1) (by omega)]
    simp [show m - 1 + 1 = m by omega]
  · intro j hj hjm
    rw [Finset.mem_Ico] at hj
    rw [hP.aj j hj.2]
    simp only [ite_eq_right_iff]
    intro h
    omega
  · intro h
    exact absurd (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩) h

end Chain

section ChainProd

variable {N : Type*} [Monoid N]

noncomputable def ggChainProd (m : ℕ) (S : ℕ → N) (k : ℕ) : N :=
  ((List.range' k (m - k)).map S).prod

theorem ggChainProd_self (m : ℕ) (S : ℕ → N) : ggChainProd m S m = 1 := by
  simp [ggChainProd]

theorem ggChainProd_of_lt {m k : ℕ} (S : ℕ → N) (hk : k < m) :
    ggChainProd m S k = S k * ggChainProd m S (k + 1) := by
  obtain ⟨d, hd⟩ : ∃ d, m - k = d + 1 := ⟨m - k - 1, by omega⟩
  rw [ggChainProd, ggChainProd, hd, List.range'_succ, show m - (k + 1) = d by omega]
  simp

theorem map_ggChainProd {N' F : Type*} [Monoid N'] [FunLike F N N'] [MonoidHomClass F N N']
    (f : F) (m : ℕ) (S : ℕ → N) (k : ℕ) : f (ggChainProd m S k) = ggChainProd m (f ∘ S) k := by
  simp [ggChainProd, map_list_prod]

end ChainProd

section ChainConj

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {m : ℕ} {hJ : ℕ → M}
  {αJ : ℕ → Module.Dual R M} {ha : M} {αa : Module.Dual R M}

theorem ggChainConj_apply (hP : GGChainPairing m hJ αJ ha αa) (S : ℕ → (M ≃ₗ[R] M))
    (hS : ∀ j < m, ∀ w, S j w = w - αJ j w • hJ j) (T : M ≃ₗ[R] M)
    (hT : ∀ w, T w = w - αa w • ha) :
    ∀ k ≤ m, ∀ z, (ggChainProd m S k * T * (ggChainProd m S k)⁻¹) z =
      z - ggChainRoot m αJ αa k z • ggChainCoroot m hJ ha k := by
  intro k hk
  obtain ⟨d, hd⟩ : ∃ d, m - k = d := ⟨_, rfl⟩
  induction d generalizing k with
  | zero =>
    have hkm : k = m := by omega
    subst hkm
    intro z
    simp [ggChainProd_self, ggChainRoot, ggChainCoroot, hT]
  | succ d ih =>
    have hkm : k < m := by omega
    have ih' := ih (k + 1) (by omega) (by omega)
    have hkk : αJ k (hJ k) = 2 := by
      rw [hP.jj k k hkm hkm]
      simp
    have hinv : (S k)⁻¹ = S k := by
      rw [inv_eq_of_mul_eq_one_left]
      refine LinearEquiv.ext fun w => ?_
      rw [LinearEquiv.mul_apply, hS k hkm, hS k hkm, map_sub, map_smul, smul_eq_mul, hkk,
        LinearEquiv.coe_one, id_eq]
      module
    intro z
    rw [ggChainProd_of_lt S hkm, mul_inv_rev, hinv]
    have key := conj_apply_of_reflection_formula
      (Q := (ggChainProd m S (k + 1) * T * (ggChainProd m S (k + 1))⁻¹).toLinearMap)
      (S := (S k).toLinearMap) (fun w => ih' w) (fun w => hS k hkm w) hkk z
    simp only [LinearEquiv.coe_coe] at key
    simp only [LinearEquiv.mul_apply] at key ⊢
    rw [key, hP.chainRoot_succ_apply hkm, hP.root_coroot_succ hkm, ggChainRoot_of_lt hkm,
      ggChainCoroot_of_lt hkm, LinearMap.add_apply]
    module

end ChainConj

section GG

variable {G : Type} [Group G]

theorem inv_mem_ggInduced {H Bs : Subgroup G} {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced H Bs) :
    φ⁻¹ ∈ ggInduced H Bs := by
  obtain ⟨g, hgH, hgN, hg⟩ := hφ
  refine ⟨g⁻¹, H.inv_mem hgH, Subgroup.inv_mem _ hgN, fun b => ?_⟩
  have h := hg (φ⁻¹ b)
  rw [MulAut.apply_inv_self] at h
  rw [h]
  group

theorem ggChainProd_mem_ggInduced {H Bs : Subgroup G} {m : ℕ} {φ : ℕ → MulAut ↥Bs}
    (hφ : ∀ j < m, φ j ∈ ggInduced H Bs) (k : ℕ) : ggChainProd m φ k ∈ ggInduced H Bs := by
  obtain ⟨d, hd⟩ : ∃ d, m - k = d := ⟨_, rfl⟩
  induction d generalizing k with
  | zero =>
    rw [ggChainProd, hd]
    exact one_mem_ggInduced H Bs
  | succ d ih =>
    rw [ggChainProd_of_lt φ (by omega)]
    exact mul_mem_ggInduced (hφ k (by omega)) (ih (k + 1) (by omega))

variable {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V]

theorem ggNearEnd_reflection (ι : Additive ↥Bs ≃+ V) {m : ℕ} {φJ : ℕ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφJ : ∀ j < m, φJ j ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V}
    (hP : GGChainPairing m hJ αJ ha αa)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha) :
    ggChainProd m φJ 0 * φa * (ggChainProd m φJ 0)⁻¹ ∈ ggInduced ⊤ Bs ∧
      ∀ z, ggLin (p := p) ι (ggChainProd m φJ 0 * φa * (ggChainProd m φJ 0)⁻¹) z =
        z - ggChainRoot m αJ αa 0 z • ggChainCoroot m hJ ha 0 := by
  refine ⟨mul_mem_ggInduced (mul_mem_ggInduced (ggChainProd_mem_ggInduced hφJ 0) hφa)
    (inv_mem_ggInduced (ggChainProd_mem_ggInduced hφJ 0)), fun z => ?_⟩
  rw [map_mul, map_mul, map_inv, map_ggChainProd]
  exact ggChainConj_apply hP _ hlinJ _ hlina 0 (Nat.zero_le _) z

theorem ggTypeA_cross_iff (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) (ι : Additive ↥Bs ≃+ V)
    {m : ℕ} (hm : 1 ≤ m) {φJ : ℕ → MulAut ↥Bs} {φa φb : MulAut ↥Bs}
    (hφJ : ∀ j < m, φJ j ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hφb : φb ∈ ggInduced ⊤ Bs) {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V} {ha hb : V}
    {αa αb : Module.Dual (ZMod p) V} (hPa : GGChainPairing m hJ αJ ha αa)
    (hPb : GGChainPairing m hJ αJ hb αb)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hlinb : ∀ w, ggLin (p := p) ι φb w = w - αb w • hb) :
    (αa hb = 0 ↔ αb ha = 0) ∧ (αa hb = 1 ↔ αb ha = 1) := by
  have hLa : ggLin (p := p) ι φa = reflection hPa.aa := ggLin_eq_reflection ι hPa.aa hlina
  have hLb : ggLin (p := p) ι φb = reflection hPb.aa := ggLin_eq_reflection ι hPb.aa hlinb
  obtain ⟨hψ, hlinψ⟩ := ggNearEnd_reflection ι hφJ hφa hPa hlinJ hlina
  have hθ := hPa.chainRoot_chainCoroot 0 (Nat.zero_le _)
  have hLψ := ggLin_eq_reflection ι hθ hlinψ
  have hθb : ggChainRoot m αJ αa 0 hb = αa hb - 1 := by
    rw [ggChainRoot, LinearMap.add_apply, LinearMap.sum_apply, hPb.sum_ja hm]
    ring
  have hbθ : αb (ggChainCoroot m hJ ha 0) = αb ha - 1 := by
    rw [ggChainCoroot, map_add, map_sum, hPb.sum_aj' hm]
    ring
  refine ⟨⟨fun h => ggCross_eq_zero_of_noTransvection hp2 hNT ι hφa hφb hPa.aa hPb.aa hLa hLb h,
      fun h => ggCross_eq_zero_of_noTransvection hp2 hNT ι hφb hφa hPb.aa hPa.aa hLb hLa h⟩,
    ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : ggChainRoot m αJ αa 0 hb = 0 := by rw [hθb, h, sub_self]
    have := ggCross_eq_zero_of_noTransvection hp2 hNT ι hψ hφb hθ hPb.aa hLψ hLb h0
    rw [hbθ] at this
    exact sub_eq_zero.mp this
  · have h0 : αb (ggChainCoroot m hJ ha 0) = 0 := by rw [hbθ, h, sub_self]
    have := ggCross_eq_zero_of_noTransvection hp2 hNT ι hφb hψ hPb.aa hθ hLb hLψ h0
    rw [hθb] at this
    exact sub_eq_zero.mp this

theorem ggTypeA_label_cases (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) (ι : Additive ↥Bs ≃+ V)
    {m : ℕ} (hm : 1 ≤ m) {φJ : ℕ → MulAut ↥Bs} {φa φb : MulAut ↥Bs}
    (hφJ : ∀ j < m, φJ j ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hφb : φb ∈ ggInduced ⊤ Bs) {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V} {ha hb : V}
    {αa αb : Module.Dual (ZMod p) V} (hPa : GGChainPairing m hJ αJ ha αa)
    (hPb : GGChainPairing m hJ αJ hb αb)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hlinb : ∀ w, ggLin (p := p) ι φb w = w - αb w • hb) (hu : αa hb = 0 ∨ αa hb = 1) :
    (αa hb = 0 ∧ αb ha = 0) ∨
      (ggChainRoot m αJ αa 0 hb = 0 ∧ αb (ggChainCoroot m hJ ha 0) = 0) := by
  obtain ⟨h0, h1⟩ := ggTypeA_cross_iff hp2 hNT ι hm hφJ hφa hφb hPa hPb hlinJ hlina hlinb
  have hθb : ggChainRoot m αJ αa 0 hb = αa hb - 1 := by
    rw [ggChainRoot, LinearMap.add_apply, LinearMap.sum_apply, hPb.sum_ja hm]
    ring
  have hbθ : αb (ggChainCoroot m hJ ha 0) = αb ha - 1 := by
    rw [ggChainCoroot, map_add, map_sum, hPb.sum_aj' hm]
    ring
  rcases hu with hu | hu
  · exact Or.inl ⟨hu, h0.mp hu⟩
  · exact Or.inr ⟨by rw [hθb, hu, sub_self], by rw [hbθ, h1.mp hu, sub_self]⟩

end GG

@[expose] def GGTypeACrossLabelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGScalarsOrWeyl' p B Bs x D J →
        ∀ [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (ι : Additive ↥Bs ≃+ V) (m : ℕ), 2 ≤ m → ∀ (φJ : ℕ → MulAut ↥Bs) (φa φb : MulAut ↥Bs)
      (hJ : ℕ → V) (αJ : ℕ → Module.Dual (ZMod p) V) (ha hb : V)
      (αa αb : Module.Dual (ZMod p) V),
      GGChainPairing m hJ αJ ha αa → GGChainPairing m hJ αJ hb αb →
      (∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j) →
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
      (∀ w, ggLin (p := p) ι φb w = w - αb w • hb) →
      ggAutomizer L Bs = Subgroup.closure ((φJ '' Set.Iio m) ∪ {φb}) →
      ggAutomizer K Bs = Subgroup.closure ((φJ '' Set.Iio m) ∪ {φa}) →
      αa hb = 0 ∨ αa hb = 1

end CFSG.StandardType
