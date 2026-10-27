module

public import CFSG.Quasithin.Background.SmithB51LnSec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix Module
open scoped Matrix

variable {n : ℕ}

@[expose] def stabVec (x : Fin n → ZMod 2) : Subgroup ↥(StatedSL n (ZMod 2)) where
  carrier := {g | mat g *ᵥ x = x}
  one_mem' := by simp
  mul_mem' := fun {g h} hg hh => by
    show mat (g * h) *ᵥ x = x
    rw [mat_mul, ← mulVec_mulVec, hh, hg]
  inv_mem' := fun {g} hg => by
    show mat g⁻¹ *ᵥ x = x
    have := mulVec_inv_mulVec g x
    rwa [show mat g *ᵥ x = x from hg] at this

theorem exists_fixD_lt_fixN (hn : 3 ≤ n) :
    ∃ B : Subgroup ↥(StatedSL n (ZMod 2)),
      finrank (ZMod 2) (fixD B) < finrank (ZMod 2) (fixN B) := by
  classical
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set i2 : Fin n := ⟨2, by omega⟩ with hi2
  have h01 : i0 ≠ i1 := by rw [hi0, hi1]; intro h; simp [Fin.ext_iff] at h
  have h21 : i2 ≠ i1 := by rw [hi2, hi1]; intro h; simp [Fin.ext_iff] at h
  have h02 : i0 ≠ i2 := by rw [hi0, hi2]; intro h; simp [Fin.ext_iff] at h
  let f : Module.Dual (ZMod 2) (Fin n → ZMod 2) := LinearMap.proj i1
  have hf : ∀ x, f x = x i1 := fun _ => rfl
  set d0 : Fin n → ZMod 2 := Pi.single i0 1 with hd0
  set d2 : Fin n → ZMod 2 := Pi.single i2 1 with hd2
  set e1 : Fin n → ZMod 2 := Pi.single i1 1 with he1
  have hfd0 : f d0 = 0 := by rw [hf, hd0, Pi.single_eq_of_ne h01.symm]
  have hfd2 : f d2 = 0 := by rw [hf, hd2, Pi.single_eq_of_ne h21.symm]
  have hfe1 : f e1 = 1 := by rw [hf, he1, Pi.single_eq_same]
  have key : ∀ {d : Fin n → ZMod 2} (hd : f d = 0), ∃ g : ↥(StatedSL n (ZMod 2)),
      ∀ v, mat g *ᵥ v = v + f v • d := by
    intro d hd
    let t := LinearEquiv.transvection hd
    have hu : IsUnit (LinearMap.toMatrix' (t : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))) := by
      rw [Matrix.isUnit_iff_isUnit_det, LinearMap.det_toMatrix']
      exact LinearEquiv.isUnit_det' t
    refine ⟨ofGL hu.unit, fun v => ?_⟩
    rw [mat_ofGL, IsUnit.unit_spec, LinearMap.toMatrix'_mulVec]
    exact CFSG.GroupTheory.GLnTwoSplitting.transvection_apply hd v
  obtain ⟨g₁, hg₁⟩ := key hfd0
  obtain ⟨g₂, hg₂⟩ := key hfd2
  set B := Subgroup.closure ({g₁, g₂} : Set ↥(StatedSL n (ZMod 2))) with hB
  have hfix : LinearMap.ker f ≤ fixN B := by
    intro x hx g hg
    have hle : B ≤ stabVec x := by
      rw [hB, Subgroup.closure_le]
      intro g hg
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · show mat _ *ᵥ x = x
        rw [hg₁, LinearMap.mem_ker.1 hx, zero_smul, add_zero]
      · show mat _ *ᵥ x = x
        rw [hg₂, LinearMap.mem_ker.1 hx, zero_smul, add_zero]
    exact hle hg
  have hcomm : Submodule.span (ZMod 2) {d0, d2} ≤ commN B := by
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · have := sub_mem_commN (B := B) (Subgroup.subset_closure (Set.mem_insert g₁ _)) e1
      rwa [hg₁, hfe1, one_smul, add_sub_cancel_left] at this
    · have := sub_mem_commN (B := B)
        (Subgroup.subset_closure (Set.mem_insert_of_mem g₁ (Set.mem_singleton g₂))) e1
      rwa [hg₂, hfe1, one_smul, add_sub_cancel_left] at this
  have hker : n - 1 ≤ finrank (ZMod 2) (LinearMap.ker f) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun (ZMod 2)] at h1
    have h2 : finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range f)
      rwa [Module.finrank_self] at this
    omega
  have hspan :
      finrank (ZMod 2) (Submodule.span (ZMod 2) ({d0, d2} : Set (Fin n → ZMod 2))) = 2 := by
    have hli : LinearIndependent (ZMod 2) ![d0, d2] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h0 := congrFun hst i0
      have h2 := congrFun hst i2
      simp [hd0, hd2, h02, h02.symm] at h0 h2
      exact ⟨h0, h2⟩
    have := finrank_span_eq_card hli
    rw [Fintype.card_fin] at this
    have hrange : Set.range ![d0, d2] = {d0, d2} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      constructor
      · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
      · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
    rw [← hrange]
    exact this
  have h1 : n - 1 ≤ finrank (ZMod 2) (fixN B) := hker.trans (Submodule.finrank_mono hfix)
  have h2 : 2 ≤ finrank (ZMod 2) (commN B) := by
    have := Submodule.finrank_mono hcomm
    rw [hspan] at this
    exact this
  have h3 := finrank_fixD_add B
  exact ⟨B, by omega⟩

section Conj

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

@[expose] def conjL {g : MulAut V} (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L)
    (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L) : ↥L ≃* ↥L where
  toFun x := ⟨g * x * g⁻¹, hgL x x.2⟩
  invFun x := ⟨g⁻¹ * x * g, hgL' x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[expose] noncomputable def conjSL {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hπ : Function.Bijective π)
    {g : MulAut V} (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L) :
    ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2)) :=
  (MulEquiv.ofBijective π hπ).trans ((conjL hgL hgL').trans (MulEquiv.ofBijective π hπ).symm)

theorem conjSL_spec {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hπ : Function.Bijective π) {g : MulAut V}
    (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L)
    (γ : ↥(StatedSL n (ZMod 2))) :
    ((π (conjSL hπ hgL hgL' γ) : ↥L) : MulAut V) = g * ((π γ : ↥L) : MulAut V) * g⁻¹ := by
  show (((MulEquiv.ofBijective π hπ) ((MulEquiv.ofBijective π hπ).symm
    ((conjL hgL hgL') ((MulEquiv.ofBijective π hπ) γ))) : ↥L) : MulAut V) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

@[expose] def conjSub (g : MulAut V) (B : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  B.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g : MulAut V} {B : Subgroup (MulAut V)} {x : MulAut V} :
    x ∈ conjSub g B ↔ ∃ b ∈ B, g * b * g⁻¹ = x := by
  simp [conjSub, Subgroup.mem_map, MulAut.conj_apply]

theorem pre_conjSub {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hπ : Function.Bijective π) {g : MulAut V}
    (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L) {B : Subgroup (MulAut V)}
    (hBL : B ≤ L) :
    pre π (conjSub g B) = (pre π B).map (conjSL hπ hgL hgL').toMonoidHom := by
  ext γ
  rw [mem_pre, mem_conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, hbγ⟩
    obtain ⟨δ, hδ⟩ := hπ.2 ⟨b, hBL hb⟩
    refine ⟨δ, ?_, ?_⟩
    · rw [mem_pre, hδ]; exact hb
    · apply hπ.1
      apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, conjSL_spec, hδ]
      exact hbγ
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨_, hδ, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, conjSL_spec]
    rfl

theorem fixN_map_eq {B : Subgroup ↥(StatedSL n (ZMod 2))}
    {σ : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2))}
    {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} {P : GL (Fin n) (ZMod 2)}
    (hP : ∀ g, mat (σ g) = (P : Matrix (Fin n) (Fin n) (ZMod 2)) * M g *
      ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) :
    finrank (ZMod 2) (fixN (B.map σ.toMonoidHom)) = finrank (ZMod 2) (fixM M B) := by
  set e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin P) with he
  have hePx : ∀ x, e x = (P : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x := fun x => rfl
  have hPP : ∀ x, ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      ((P : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hPP' : ∀ x, (P : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      (((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have h1 : fixN (B.map σ.toMonoidHom) = (fixM M B).map (e : (Fin n → ZMod 2) →ₗ[ZMod 2] _) := by
    ext x
    rw [Submodule.mem_map]
    constructor
    · intro hx
      refine ⟨((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x, fun g hg => ?_,
        by rw [LinearEquiv.coe_coe, hePx, hPP']⟩
      have := hx _ ⟨g, hg, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hP, ← mulVec_mulVec, ← mulVec_mulVec] at this
      have h2 :=
        congrArg (((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ·) this
      simp only [hPP] at h2
      exact h2
    · rintro ⟨y, hy, rfl⟩ _ ⟨g, hg, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hP, LinearEquiv.coe_coe, hePx, ← mulVec_mulVec,
        ← mulVec_mulVec, hPP, hy g hg]
  rw [h1, LinearEquiv.finrank_map_eq]

end Conj

section Sums

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem inv_iSup {B : Subgroup (MulAut V)} {ι : Sort*} (I : ι → Subgroup V)
    (hinv : ∀ i, ∀ b ∈ B, ∀ x ∈ I i, b x ∈ I i) : ∀ b ∈ B, ∀ x ∈ ⨆ i, I i, b x ∈ ⨆ i, I i := by
  intro b hb x hx
  refine Subgroup.iSup_induction I (C := fun x => b x ∈ ⨆ i, I i) hx (fun i y hy => ?_) ?_ ?_
  · exact (le_iSup I i) (hinv i b hb y hy)
  · rw [map_one]; exact Subgroup.one_mem _
  · intro y z hy hz
    rw [map_mul]
    exact Subgroup.mul_mem _ hy hz

theorem rkSub_iSup {k : ℕ} {B : Subgroup (MulAut V)} (I : Fin k → Subgroup V)
    (hinv : ∀ i, ∀ b ∈ B, ∀ x ∈ I i, b x ∈ I i)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) :
    rkSub B (⨆ i, I i) = ∑ i, rkSub B (I i) := by
  classical
  have key : ∀ s : Finset (Fin k), rkSub B (⨆ i ∈ s, I i) = ∑ i ∈ s, rkSub B (I i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, iSup_of_empty, iSup_bot, Finset.sum_empty]
      simp [rkSub, rk_bot]
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha]
      have hinvs : ∀ b ∈ B, ∀ x ∈ ⨆ i ∈ s, I i, b x ∈ ⨆ i ∈ s, I i :=
        inv_iSup (fun i => ⨆ (_ : i ∈ s), I i) fun i =>
          inv_iSup (fun _ : i ∈ s => I i) fun _ => hinv i
      have hdisj : I a ⊓ (⨆ i ∈ s, I i) = ⊥ := by
        rw [eq_bot_iff, ← hind a]
        refine inf_le_inf_left _ (iSup₂_le fun i hi => ?_)
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        exact le_iSup₂_of_le i hia le_rfl
      rw [rkSub_sup (hinv a) hinvs hdisj, ih]
  have := key Finset.univ
  simpa using this

theorem RealM.rkSub_eq {L : Subgroup (MulAut V)} {X : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} (h : RealM L X ⊥ π M)
    {B : Subgroup (MulAut V)} (hBL : B ≤ L) :
    rkSub B X = n - finrank (ZMod 2) (fixM M (pre π B)) := by
  rw [← rkIdx_fixV_autSec_bot (hBL.trans h.hLW), h.rkIdx_fixV_autSec hBL]

end Sums

section Inner

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem mem_of_inner (h : B51Hyp G L) {a : MulAut V} (haG : a ∈ G) (ha2 : a ^ 2 = 1)
    {l : MulAut V} (hl : l ∈ L) (hinner : ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) : a ∈ L := by
  set c := l⁻¹ * a with hc
  have hcG : c ∈ G := G.mul_mem (G.inv_mem (le_G h hl)) haG
  have hcC : c ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hinner x hx
    rw [hc]
    calc x * (l⁻¹ * a) = l⁻¹ * (l * x * l⁻¹) * a := by group
      _ = l⁻¹ * (a * x * a⁻¹) * a := by rw [this]
      _ = l⁻¹ * a * x := by group
  have hodd := odd_orderOf_of_mem_centralizer h hcG hcC
  obtain ⟨k, hk⟩ := hodd
  have hcomm : Commute l c := Subgroup.mem_centralizer_iff.1 hcC l hl
  have ha : a = l * c := by rw [hc]; group
  have h1 : a ^ orderOf c = l ^ orderOf c := by
    rw [ha, hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
  have h2 : a ^ orderOf c = a := by
    rw [hk, pow_succ, pow_mul, ha2, one_pow, one_mul]
  rw [← h2, h1]
  exact L.pow_mem hl _

end Inner

end CFSG.Quasithin.B5.Ln
