module

public import CFSG.Quasithin.SteinbergCDRankOneLeviOddCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6FixedContainment
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup Matrix CFSG.ABGLocalTools

section BlockHom

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem isCyclic_of_le_commutator_of_ker_two {X : Type*} [Group X] {A : Type*} [CommGroup A]
    (ψ : X →* GL (Fin 2) F) (χ : X →* A)
    (hker : ∀ x : X, ψ x = 1 → χ x = 1 → ∃ n : ℕ, x ^ 2 ^ n = 1) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {E : Subgroup X} (hE : E ≤ commutator X) (hEr : IsPGroup r E) :
    IsCyclic E := by
  have hdet : ∀ x ∈ commutator X, (ψ x : Matrix (Fin 2) (Fin 2) F).det = 1 ∧ χ x = 1 := by
    intro x hx
    have h1 := Abelianization.commutator_subset_ker
      ((Matrix.GeneralLinearGroup.det.comp ψ).prod χ) hx
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at h1
    refine ⟨?_, h1.2⟩
    have h2 := congrArg Units.val h1.1
    simpa using h2
  have hinj : ∀ e ∈ E, ψ e = 1 → e = 1 := by
    intro e he hψ
    obtain ⟨n, hn⟩ := hker e hψ (hdet e (hE he)).2
    obtain ⟨m, hm⟩ := hEr ⟨e, he⟩
    have hm' : e ^ r ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have h1 : orderOf e ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have h2 : orderOf e ∣ r ^ m := orderOf_dvd_of_pow_eq_one hm'
    have hcop : Nat.Coprime (2 ^ n) (r ^ m) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two (Fact.out)).2 (Ne.symm hr2))
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  let κ : E →* SpecialLinearGroup (Fin 2) F :=
    { toFun := fun e => ⟨(ψ e : Matrix (Fin 2) (Fin 2) F), (hdet e (hE e.2)).1⟩
      map_one' := by
        ext i j
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [coe_mul, map_mul, Units.val_mul]
        rfl }
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : ψ e = 1 := by
      ext i j
      have h2 : ((κ e : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
          ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := by
        rw [he]
      exact h2
    exact Subtype.ext (hinj e e.2 h1)
  have hrange : IsPGroup r κ.range :=
    hEr.of_surjective κ.rangeRestrict κ.rangeRestrict_surjective
  have hcyc : IsCyclic κ.range :=
    CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hr2 _ hrange
  have e : E ≃* κ.range := MonoidHom.ofInjective hκ
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem isCyclic_of_le_commutator_of_ker_two' {G : Type*} [Group G] {X : Subgroup G}
    {A : Type*} [CommGroup A] (ψ : X →* GL (Fin 2) F) (χ : X →* A)
    (hker : ∀ x : X, ψ x = 1 → χ x = 1 → ∃ n : ℕ, x ^ 2 ^ n = 1) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {E : Subgroup G} (hE : E ≤ ⁅X, X⁆) (hEr : IsPGroup r E) : IsCyclic E := by
  have hEX : E ≤ X := hE.trans X.commutator_le_self
  have hE' : E.subgroupOf X ≤ commutator X := by
    intro x hx
    have h1 : (x : G) ∈ (commutator X).map X.subtype := by
      rw [X.map_subtype_commutator]
      exact hE hx
    obtain ⟨y, hy, hyx⟩ := h1
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  have hEr' : IsPGroup r (E.subgroupOf X) := hEr.comap_subtype
  have hcyc := isCyclic_of_le_commutator_of_ker_two ψ χ hker hr2 hE' hEr'
  have e : E.subgroupOf X ≃* E := subgroupOfEquivOfLe hEX
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

end BlockHom

section Conj

variable {G : Type*} [Group G]

theorem exists_conj_sup_of_isSylowOf [Finite G] {C U T B : Subgroup G} (hU : IsSylowOf 2 U C)
    (hT : IsSylowOf 2 T C) (hBT : B ⊔ T < C) :
    ∃ c ∈ C, U ≤ (B ⊔ T).map (MulAut.conj c⁻¹).toMonoidHom ∧
      (B ⊔ T).map (MulAut.conj c⁻¹).toMonoidHom < C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcC, hc⟩ := hU.exists_mem_conj hT
  refine ⟨c, hcC, fun u hu => ⟨c * u * c⁻¹, mem_sup_right ((hc _).2 (by simpa [mul_assoc]
    using hu)), by simp [mul_assoc]⟩, lt_of_le_of_ne ?_ fun h => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact C.mul_mem (C.mul_mem (C.inv_mem hcC) (hBT.le hx)) hcC
  · apply hBT.ne
    apply le_antisymm hBT.le
    intro x hx
    have h1 : c⁻¹ * x * c ∈ (B ⊔ T).map (MulAut.conj c⁻¹).toMonoidHom := by
      rw [h]
      exact C.mul_mem (C.mul_mem (C.inv_mem hcC) hx) hcC
    obtain ⟨y, hy, hyx⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hyx
    have : y = x := by
      calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
        _ = x := by rw [hyx]; group
    rw [← this]
    exact hy

theorem isCyclic_of_isCyclic_map_conj (c : G) {E : Subgroup G}
    (h : IsCyclic (E.map (MulAut.conj c⁻¹).toMonoidHom)) : IsCyclic E := by
  have e : E ≃* E.map (MulAut.conj c⁻¹).toMonoidHom :=
    E.equivMapOfInjective _ (MulAut.conj c⁻¹).injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end Conj

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {k : Type} [Field k]

theorem entry_eq_zero_of_mem_stabilizer_flagSpace {n d : ℕ} {g : SpecialLinearGroup (Fin n) k}
    (hg : g ∈ stabilizer (flagSpace n k d)) {i j : Fin n} (hj : (j : ℕ) < d)
    (hi : d ≤ (i : ℕ)) : (g : Matrix (Fin n) (Fin n) k) i j = 0 := by
  have h1 : (g : Matrix (Fin n) (Fin n) k) *ᵥ Pi.single j 1 ∈ flagSpace n k d := by
    rw [← mem_stabilizer.1 hg]
    exact ⟨Pi.single j 1, Submodule.subset_span ⟨j, hj, rfl⟩, rfl⟩
  have h2 := mem_flagSpace.1 h1 i hi
  simpa [mulVec_single_one] using h2

noncomputable def lowerBlockHom : stabilizer (flagSpace 3 k 1) →* Matrix (Fin 2) (Fin 2) k where
  toFun g := Matrix.of fun i j =>
    ((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i.succ j.succ
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' g h := by
    ext i j
    have h0 : ((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i.succ 0 = 0 :=
      entry_eq_zero_of_mem_stabilizer_flagSpace g.2 (by simp) (by simp)
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h0]

noncomputable def upperBlockHom : stabilizer (flagSpace 3 k 2) →* Matrix (Fin 2) (Fin 2) k where
  toFun g := Matrix.of fun i j =>
    ((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i.castSucc j.castSucc
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' g h := by
    ext i j
    have h0 : ((h : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 2 j.castSucc = 0 :=
      entry_eq_zero_of_mem_stabilizer_flagSpace h.2 j.isLt (by simp)
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, h0]

theorem sq_eq_one_of_lowerBlockHom_eq_one [CharP k 2] (g : stabilizer (flagSpace 3 k 1))
    (hg : lowerBlockHom g = 1) : g ^ 2 = 1 := by
  set m := ((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) with hm
  have hb : ∀ i j : Fin 2, m i.succ j.succ = (1 : Matrix (Fin 2) (Fin 2) k) i j := fun i j =>
    congrFun (congrFun hg i) j
  have h10 : m 1 0 = 0 :=
    entry_eq_zero_of_mem_stabilizer_flagSpace g.2 (i := 1) (j := 0) (by simp) (by simp)
  have h20 : m 2 0 = 0 :=
    entry_eq_zero_of_mem_stabilizer_flagSpace g.2 (i := 2) (j := 0) (by simp) (by simp)
  have h11 : m 1 1 = 1 := by simpa using hb 0 0
  have h12 : m 1 2 = 0 := by simpa using hb 0 1
  have h21 : m 2 1 = 0 := by simpa using hb 1 0
  have h22 : m 2 2 = 1 := by simpa using hb 1 1
  have hdet : m.det = 1 := (g : SpecialLinearGroup (Fin 3) k).2
  rw [Matrix.det_fin_three, h10, h20, h11, h12, h21, h22] at hdet
  have h00 : m 0 0 = 1 := by simpa using hdet
  have hsq : m * m = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h11, h12, h20, h21, h22,
        CharTwo.add_self_eq_zero]
  apply Subtype.ext
  ext i j
  have h := congrFun (congrFun hsq i) j
  simpa [pow_two, ← hm] using h

theorem sq_eq_one_of_upperBlockHom_eq_one [CharP k 2] (g : stabilizer (flagSpace 3 k 2))
    (hg : upperBlockHom g = 1) : g ^ 2 = 1 := by
  set m := ((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) with hm
  have hb : ∀ i j : Fin 2, m i.castSucc j.castSucc = (1 : Matrix (Fin 2) (Fin 2) k) i j :=
    fun i j => congrFun (congrFun hg i) j
  have h20 : m 2 0 = 0 :=
    entry_eq_zero_of_mem_stabilizer_flagSpace g.2 (i := 2) (j := 0) (by simp) (by simp)
  have h21 : m 2 1 = 0 :=
    entry_eq_zero_of_mem_stabilizer_flagSpace g.2 (i := 2) (j := 1) (by simp) (by simp)
  have h00 : m 0 0 = 1 := by simpa using hb 0 0
  have h01 : m 0 1 = 0 := by simpa using hb 0 1
  have h10 : m 1 0 = 0 := by simpa using hb 1 0
  have h11 : m 1 1 = 1 := by simpa using hb 1 1
  have hdet : m.det = 1 := (g : SpecialLinearGroup (Fin 3) k).2
  rw [Matrix.det_fin_three, h00, h01, h10, h11, h20, h21] at hdet
  have h22 : m 2 2 = 1 := by simpa using hdet
  have hsq : m * m = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h01, h10, h11, h20, h21, h22,
        CharTwo.add_self_eq_zero]
  apply Subtype.ext
  ext i j
  have h := congrFun (congrFun hsq i) j
  simpa [pow_two, ← hm] using h

theorem isCyclic_of_le_commutator_stabilizer_flagSpace [Finite k] [CharP k 2] {d : ℕ}
    (hd : d = 1 ∨ d = 2) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {E : Subgroup (stabilizer (flagSpace 3 k d))} (hE : E ≤ commutator _) (hEr : IsPGroup r E) :
    IsCyclic E := by
  rcases hd with rfl | rfl
  · refine isCyclic_of_le_commutator_of_ker_two lowerBlockHom.toHomUnits (1 : _ →* ℤˣ)
      (fun x hx _ => ⟨1, ?_⟩) hr2 hE hEr
    rw [pow_one]
    refine sq_eq_one_of_lowerBlockHom_eq_one x ?_
    have := congrArg Units.val hx
    simpa using this
  · refine isCyclic_of_le_commutator_of_ker_two upperBlockHom.toHomUnits (1 : _ →* ℤˣ)
      (fun x hx _ => ⟨1, ?_⟩) hr2 hE hEr
    rw [pow_one]
    refine sq_eq_one_of_upperBlockHom_eq_one x ?_
    have := congrArg Units.val hx
    simpa using this

theorem projStabilizer_perfect_odd_isCyclic [Finite k] [CharP k 2] {d : ℕ}
    (hd : d = 1 ∨ d = 2) {B : Subgroup (projectiveSL 3 k)}
    (hB : B ≤ projStabilizer (flagSpace 3 k d)) (hBp : Group.IsPerfect B) {r : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) {E : Subgroup (projectiveSL 3 k)} (hEB : E ≤ B)
    (hE : IsPGroup r E) : IsCyclic E := by
  set X := stabilizer (flagSpace 3 k d) with hXdef
  set p : X →* projectiveSL 3 k := (proj 3 k).comp X.subtype with hpdef
  have hpX : (commutator X).map p = ⁅projStabilizer (flagSpace 3 k d),
      projStabilizer (flagSpace 3 k d)⁆ := by
    rw [hpdef, ← Subgroup.map_map, X.map_subtype_commutator, Subgroup.map_commutator]
    rfl
  have hEc : E ≤ (commutator X).map p := by
    rw [hpX]
    calc E ≤ B := hEB
      _ = ⁅B, B⁆ := (Subgroup.isPerfect_iff.1 hBp).symm
      _ ≤ _ := Subgroup.commutator_mono hB hB
  set Y := commutator X ⊓ E.comap p with hYdef
  let pY : Y →* E := (p.comp Y.subtype).codRestrict E fun y => y.2.2
  have hpY : Function.Surjective pY := by
    intro e
    obtain ⟨x, hx, hxe⟩ := hEc e.2
    exact ⟨⟨x, hx, by show p x ∈ E; rw [hxe]; exact e.2⟩, Subtype.ext hxe⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow r Y))
  have hS'top : (S.mapSurjective hpY : Subgroup E) = ⊤ :=
    ((S.mapSurjective hpY).3 (hE.to_subgroup ⊤) le_top).symm
  have hScyc : IsCyclic (S : Subgroup Y) := by
    have h1 := isCyclic_of_le_commutator_stabilizer_flagSpace hd hr2
      (E := (S : Subgroup Y).map Y.subtype) (by rintro _ ⟨y, -, rfl⟩; exact y.2.1)
      (S.isPGroup'.map Y.subtype)
    have e : (S : Subgroup Y) ≃* (S : Subgroup Y).map Y.subtype :=
      (S : Subgroup Y).equivMapOfInjective _ Y.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hsurj : Function.Surjective (pY.comp (S : Subgroup Y).subtype) := by
    intro e
    have h1 : e ∈ (S.mapSurjective hpY : Subgroup E) := hS'top ▸ mem_top e
    rw [Sylow.coe_mapSurjective] at h1
    obtain ⟨y, hy, rfl⟩ := h1
    exact ⟨⟨y, hy⟩, rfl⟩
  exact isCyclic_of_surjective _ hsurj

theorem projectiveSL_three_perfect_odd_isCyclic [Finite k] [CharP k 2]
    (T : Sylow 2 (projectiveSL 3 k)) {B : Subgroup (projectiveSL 3 k)} (hBp : Group.IsPerfect B)
    (hBT : B ⊔ T < ⊤) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup (projectiveSL 3 k)}
    (hEB : E ≤ B) (hE : IsPGroup r E) : IsCyclic E := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, ⟨P, hP⟩, -⟩ :=
    linear_order (K := k) 2 (Nat.card k) rfl (n := 3) (by norm_num)
  have hUsyl : IsSylowOf 2 (projUnitriangular 3 k) ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right, ← hP]
    exact ⟨le_top, P.isPGroup', P.not_dvd_index⟩
  have hTsyl : IsSylowOf 2 (T : Subgroup (projectiveSL 3 k)) ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, T.isPGroup', T.not_dvd_index⟩
  obtain ⟨c, -, hU, hlt⟩ := exists_conj_sup_of_isSylowOf hUsyl hTsyl hBT
  obtain ⟨i, hi1, hi3, hle⟩ :=
    (CFSG.QuasithinUnique.Setup.X7a.linear_unitriangular_overgroup_subflag_containment
      (K := k) (n := 3)).2 _ hlt.ne hU
  have hd : i = 1 ∨ i = 2 := by omega
  have := hBp
  refine isCyclic_of_isCyclic_map_conj c ?_
  exact projStabilizer_perfect_odd_isCyclic hd ((map_mono le_sup_left).trans hle)
    (Group.IsPerfect.map _) hr2 (map_mono hEB) (hE.map _)

end Linear

section Symplectic

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {k : Type} [Field k]

@[expose] def spMat {r : ℕ} (g : StatedSp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
  ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)

theorem spMat_mul {r : ℕ} (g h : StatedSp r k) : spMat (g * h) = spMat g * spMat h := rfl

theorem spMat_one {r : ℕ} : spMat (1 : StatedSp r k) = 1 := rfl

theorem spMat_injective {r : ℕ} : Function.Injective (spMat (r := r) (k := k)) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem spMat_gram {r : ℕ} (g : StatedSp r k) :
    (spMat g)ᵀ * fromBlocks 0 1 (-1) 0 * spMat g = fromBlocks 0 1 (-1) 0 :=
  SymplecticTorusWeyl.mem_statedSp_iff.1 g.2

theorem sp_entry_of_mem_stabilizer {r d : ℕ} (hdr : d ≤ r) {g : StatedSp r k}
    (hg : g ∈ stabilizer r k (flag r k d)) {j : Fin r} (hj : (j : ℕ) < d) :
    (∀ l, spMat g (Sum.inr l) (Sum.inl j) = 0) ∧
      ∀ l : Fin r, d ≤ (l : ℕ) → spMat g (Sum.inl l) (Sum.inl j) = 0 := by
  have hflag : flag r k d = isoFlag r k d := by rw [flag, ite_eq_left hdr]
  have h1 : spMat g *ᵥ Pi.single (Sum.inl j) 1 ∈ isoFlag r k d := by
    rw [← hflag, ← mem_stabilizer.1 hg]
    refine ⟨Pi.single (Sum.inl j) 1, ?_, rfl⟩
    rw [hflag]
    exact Submodule.subset_span ⟨j, hj, rfl⟩
  rw [mem_isoFlag] at h1
  refine ⟨fun l => ?_, fun l hl => ?_⟩
  · simpa [mulVec_single_one] using h1.1 l
  · simpa [mulVec_single_one] using h1.2 l hl

def lagrangianBlockHom : stabilizer 2 k (flag 2 k 2) →* Matrix (Fin 2) (Fin 2) k where
  toFun g := Matrix.of fun i j => spMat (g : StatedSp 2 k) (Sum.inl i) (Sum.inl j)
  map_one' := by
    ext i j
    simp [spMat_one, Matrix.one_apply]
  map_mul' g h := by
    ext i j
    have h0 := (sp_entry_of_mem_stabilizer le_rfl h.2 (j := j) j.isLt).1
    simp [spMat_mul, Matrix.mul_apply, Fintype.sum_sum_type, h0]

theorem sq_eq_one_of_lagrangianBlockHom_eq_one [CharP k 2] (g : stabilizer 2 k (flag 2 k 2))
    (hg : lagrangianBlockHom g = 1) : g ^ 2 = 1 := by
  have hA : ∀ i j : Fin 2, spMat (g : StatedSp 2 k) (Sum.inl i) (Sum.inl j) =
      (1 : Matrix (Fin 2) (Fin 2) k) i j := fun i j => congrFun (congrFun hg i) j
  have hC : ∀ i j : Fin 2, spMat (g : StatedSp 2 k) (Sum.inr i) (Sum.inl j) = 0 := fun i j =>
    (sp_entry_of_mem_stabilizer le_rfl g.2 (j := j) j.isLt).1 i
  have hG := spMat_gram (g : StatedSp 2 k)
  have hD : ∀ i j : Fin 2, spMat (g : StatedSp 2 k) (Sum.inr i) (Sum.inr j) =
      (1 : Matrix (Fin 2) (Fin 2) k) i j := by
    intro i j
    have h1 := congrFun (congrFun hG (Sum.inl i)) (Sum.inr j)
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hA, hC] using h1
  have hsq : spMat (g : StatedSp 2 k) * spMat (g : StatedSp 2 k) = 1 := by
    ext x y
    rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hA, hC, hD,
        CharTwo.add_self_eq_zero]
  apply Subtype.ext
  apply spMat_injective
  rw [SubgroupClass.coe_pow, pow_two, spMat_mul, hsq]
  rfl

theorem sp_line_facts {g : StatedSp 2 k} (hg : g ∈ stabilizer 2 k (flag 2 k 1)) :
    spMat g (Sum.inl 1) (Sum.inl 0) = 0 ∧ (∀ l, spMat g (Sum.inr l) (Sum.inl 0) = 0) ∧
      spMat g (Sum.inl 0) (Sum.inl 0) * spMat g (Sum.inr 0) (Sum.inr 0) = 1 ∧
      spMat g (Sum.inr 0) (Sum.inl 1) = 0 ∧ spMat g (Sum.inr 0) (Sum.inr 1) = 0 := by
  obtain ⟨hC, hA⟩ := sp_entry_of_mem_stabilizer (r := 2) (d := 1) (by norm_num) hg
    (j := 0) (by norm_num)
  have h10 : spMat g (Sum.inl 1) (Sum.inl 0) = 0 := hA 1 (by norm_num)
  have hG := spMat_gram g
  have hrow : ∀ y, spMat g (Sum.inl 0) (Sum.inl 0) * spMat g (Sum.inr 0) y =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) (Sum.inl 0) y := by
    intro y
    have h1 := congrFun (congrFun hG (Sum.inl 0)) y
    rw [← h1]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hC, h10]
  have h00 := hrow (Sum.inr 0)
  have h01 := hrow (Sum.inl 1)
  have h11 := hrow (Sum.inr 1)
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h00 h01 h11
  have ha : spMat g (Sum.inl 0) (Sum.inl 0) ≠ 0 := left_ne_zero_of_mul_eq_one h00
  exact ⟨h10, hC, h00, (mul_eq_zero.1 h01).resolve_left ha, (mul_eq_zero.1 h11).resolve_left ha⟩

def midIdx : Fin 2 → Fin 2 ⊕ Fin 2 := ![Sum.inl 1, Sum.inr 1]

def midBlockHom : stabilizer 2 k (flag 2 k 1) →* Matrix (Fin 2) (Fin 2) k where
  toFun g := Matrix.of fun i j => spMat (g : StatedSp 2 k) (midIdx i) (midIdx j)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [midIdx, spMat_one, Matrix.one_apply]
  map_mul' g h := by
    obtain ⟨hg10, hgC, -, -, -⟩ := sp_line_facts g.2
    obtain ⟨-, -, -, hh01, hh11⟩ := sp_line_facts h.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [midIdx, spMat_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hg10,
        hgC, hh01, hh11]

def cornerHom : stabilizer 2 k (flag 2 k 1) →* k where
  toFun g := spMat (g : StatedSp 2 k) (Sum.inl 0) (Sum.inl 0)
  map_one' := by simp [spMat_one]
  map_mul' g h := by
    obtain ⟨hh10, hhC, -, -, -⟩ := sp_line_facts h.2
    simp [spMat_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hh10, hhC]

theorem pow_four_eq_one_of_line [CharP k 2] (g : stabilizer 2 k (flag 2 k 1))
    (hχ : cornerHom g = 1) (hψ : midBlockHom g = 1) : g ^ 2 ^ 2 = 1 := by
  obtain ⟨h10, hC, had, hr1, hr2⟩ := sp_line_facts g.2
  have ha : spMat (g : StatedSp 2 k) (Sum.inl 0) (Sum.inl 0) = 1 := hχ
  rw [ha, one_mul] at had
  have hM : ∀ i j : Fin 2, spMat (g : StatedSp 2 k) (midIdx i) (midIdx j) =
      (1 : Matrix (Fin 2) (Fin 2) k) i j := fun i j => congrFun (congrFun hψ i) j
  have m11 := hM 0 0
  have m12 := hM 0 1
  have m21 := hM 1 0
  have m22 := hM 1 1
  simp only [midIdx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at m11 m12 m21 m22
  have hC0 := hC 0
  have hC1 := hC 1
  set N := spMat (g : StatedSp 2 k) * spMat (g : StatedSp 2 k) with hN
  have hNe : ∀ x y : Fin 2 ⊕ Fin 2, x ≠ Sum.inl 0 ∨ y ≠ Sum.inr 0 →
      N x y = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) x y := by
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [hN, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, ha, h10, hC0, hC1,
        had, hr1, hr2, m11, m12, m21, m22, CharTwo.add_self_eq_zero] at hxy ⊢
  have hNN : N * N = 1 := by
    ext x y
    rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hNe,
        CharTwo.add_self_eq_zero]
  have h4 : (g : StatedSp 2 k) ^ 2 ^ 2 =
      ((g : StatedSp 2 k) * g) * ((g : StatedSp 2 k) * g) := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, pow_two]
  apply Subtype.ext
  apply spMat_injective
  rw [SubgroupClass.coe_pow, h4, spMat_mul, spMat_mul, ← hN, hNN]
  rfl

theorem sp_stabilizer_commutator_odd_isCyclic [Finite k] [CharP k 2] {d : ℕ}
    (hd : d = 1 ∨ d = 2) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {E : Subgroup (StatedSp 2 k)}
    (hE : E ≤ ⁅stabilizer 2 k (flag 2 k d), stabilizer 2 k (flag 2 k d)⁆) (hEr : IsPGroup r E) :
    IsCyclic E := by
  rcases hd with rfl | rfl
  · refine isCyclic_of_le_commutator_of_ker_two' midBlockHom.toHomUnits cornerHom.toHomUnits
      (fun x hψ hχ => ⟨2, pow_four_eq_one_of_line x ?_ ?_⟩) hr2 hE hEr
    · have := congrArg Units.val hχ
      simpa using this
    · have := congrArg Units.val hψ
      simpa using this
  · refine isCyclic_of_le_commutator_of_ker_two' lagrangianBlockHom.toHomUnits (1 : _ →* ℤˣ)
      (fun x hψ _ => ⟨1, ?_⟩) hr2 hE hEr
    rw [pow_one]
    refine sq_eq_one_of_lagrangianBlockHom_eq_one x ?_
    have := congrArg Units.val hψ
    simpa using this

theorem statedSp_two_perfect_odd_isCyclic [Finite k] [CharP k 2] (T : Sylow 2 (StatedSp 2 k))
    {B : Subgroup (StatedSp 2 k)} (hBp : Group.IsPerfect B) (hBT : B ⊔ T < ⊤) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup (StatedSp 2 k)} (hEB : E ≤ B)
    (hE : IsPGroup r E) : IsCyclic E := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨P, hP⟩, -, -, -⟩ :=
    symplectic_higher_order_and_Sylow (K := k) 2 (Nat.card k) rfl (r := 2) (by norm_num)
  have hUsyl : IsSylowOf 2 (unipotent 2 k) ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right, ← hP]
    exact ⟨le_top, P.isPGroup', P.not_dvd_index⟩
  have hTsyl : IsSylowOf 2 (T : Subgroup (StatedSp 2 k)) ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, T.isPGroup', T.not_dvd_index⟩
  obtain ⟨c, -, hU, hlt⟩ := exists_conj_sup_of_isSylowOf hUsyl hTsyl hBT
  obtain ⟨hle, hiff⟩ :=
    (CFSG.QuasithinUnique.Setup.X7a.symplectic_unitriangular_overgroup_subflag_containment
      (r := 2) (K := k)).1 _ hU
  have hne : SymplecticHigher.borelCuts k ((B ⊔ T).map (MulAut.conj c⁻¹).toMonoidHom) ≠ ∅ :=
    fun h => hlt.ne (hiff.1 h)
  obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨hi1, hi2⟩ := SymplecticHigher.borelCuts_le _ i hi
  have hd : i = 1 ∨ i = 2 := by omega
  have hMi : (B ⊔ T).map (MulAut.conj c⁻¹).toMonoidHom ≤ stabilizer 2 k (flag 2 k i) :=
    fun x hx => SymplecticHigher.mem_flagStabilizer.1 (hle hx) i hi
  have := hBp
  have hB' : Group.IsPerfect (B.map (MulAut.conj c⁻¹).toMonoidHom) := Group.IsPerfect.map _
  have hBX : B.map (MulAut.conj c⁻¹).toMonoidHom ≤ stabilizer 2 k (flag 2 k i) :=
    (map_mono le_sup_left).trans hMi
  refine isCyclic_of_isCyclic_map_conj c (sp_stabilizer_commutator_odd_isCyclic hd hr2 ?_
    (hE.map _))
  calc E.map (MulAut.conj c⁻¹).toMonoidHom ≤ B.map (MulAut.conj c⁻¹).toMonoidHom := map_mono hEB
    _ = ⁅B.map (MulAut.conj c⁻¹).toMonoidHom, B.map (MulAut.conj c⁻¹).toMonoidHom⁆ :=
      (Subgroup.isPerfect_iff.1 hB').symm
    _ ≤ _ := Subgroup.commutator_mono hBX hBX

end Symplectic

section RootWeight

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {k : Type} [Field k]

theorem encard_le_one_of_ne_univ {n : ℕ} (hn : n = 2) {J : Set (Fin n)} (hJ : J ≠ Set.univ) :
    J.encard ≤ 1 := by
  rw [Set.encard_le_one_iff]
  intro a b ha hb
  by_contra hab
  apply hJ
  refine Set.eq_univ_of_forall fun c => ?_
  have hc : c = a ∨ c = b := by
    have ha' := a.isLt
    have hb' := b.isLt
    have hc' := c.isLt
    have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
    rcases Nat.lt_or_ge (c : ℕ) 1 with h | h
    · subst hn
      omega
    · subst hn
      omega
  rcases hc with rfl | rfl
  · exact ha
  · exact hb

theorem rootWeight_unipotent_isSylowOf
    [Finite k] [CharP k 2] (D : RootWeightDatum k) :
    IsSylowOf 2 D.unipotent D.group := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  cases D with
  | ordinary τ =>
    exact (CFSG.QuasithinUnique.Setup.X6.unique_Chevalley_positive_Sylow (τ := τ) (K := k) 2).1
  | fixed t σ hσ =>
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
    obtain ⟨P, hP⟩ := (exceptional_fixed_Sylow_opposition t k 2 σ w₀ hw₀).1
    refine ⟨P, ?_⟩
    change ((P : Subgroup ↥(graphFixedRootGroup t k σ.toRingHom))).map
      (graphFixedRootGroup t k σ.toRingHom).subtype = graphFixedPosUnipotent t k σ.toRingHom
    rw [hP, subgroupOf_map_subtype,
      inf_eq_left.2 (graphFixedPosUnipotent_le_graphFixedRootGroup t k σ.toRingHom)]

theorem rootWeight_rank_two_perfect_odd_isCyclic
    [Finite k] [CharP k 2] (D : RootWeightDatum k)
    (hD : D.rank = 2) {T B : Subgroup (ModGL D.tag k)} (hT : IsSylowOf 2 T D.group)
    (hBC : B ≤ D.group) (hBp : Group.IsPerfect B) (hBT : B ⊔ T < D.group) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup (ModGL D.tag k)} (hEB : E ≤ B)
    (hE : IsPGroup r E) : IsCyclic E := by
  have : Finite (ModGL D.tag k) := finite_modGL
  obtain ⟨c, hcC, hU, hlt⟩ := exists_conj_sup_of_isSylowOf (rootWeight_unipotent_isSylowOf D) hT hBT
  have hMC : (B ⊔ T).map (MulAut.conj c⁻¹).toMonoidHom ≤ D.group := hlt.le
  obtain ⟨J, hJ, hMJ⟩ : ∃ J : Set (Fin D.rank), J ≠ Set.univ ∧
      (B ⊔ T).map (MulAut.conj c⁻¹).toMonoidHom ≤ D.parabolic J := by
    cases D with
    | ordinary τ =>
      obtain ⟨J, hJ, hle, -⟩ :=
        (CFSG.QuasithinUnique.Setup.X6.chevalley_positive_root_overgroup_parabolic_containment
          hMC hU).2.2 hlt.ne
      exact ⟨J, hJ, hle⟩
    | fixed t σ hσ =>
      obtain ⟨J, hJ, hle, -⟩ :=
        (CFSG.QuasithinUnique.Setup.X6.fixed_positive_root_overgroup_parabolic_containment t k σ
          hMC hU).2.2 hlt.ne
      exact ⟨J, hJ, hle⟩
  have := hBp
  refine isCyclic_of_isCyclic_map_conj c ?_
  exact CFSG.Quasithin.SteinbergCD.char_two_rank_one_levi_parabolic_perfect_odd_cyclic D
    (encard_le_one_of_ne_univ hD hJ) ((map_mono le_sup_left).trans hMJ) (Group.IsPerfect.map _)
    hr hr2 (map_mono hEB) (hE.map _)

end RootWeight

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem even_rank_two_proper_Sylow_overgroup_perfect_subgroups_have_cyclic_odd_subgroups
    {k : Type} [Field k] [Finite k] [CharP k 2] :
    (∀ (T : Sylow 2 (projectiveSL 3 k)) (B : Subgroup (projectiveSL 3 k)), Group.IsPerfect B →
      B ⊔ T < ⊤ → ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ E : Subgroup (projectiveSL 3 k), E ≤ B →
        IsPGroup r E → IsCyclic E) ∧
    (∀ (T : Sylow 2 (StatedSp 2 k)) (B : Subgroup (StatedSp 2 k)), Group.IsPerfect B →
      B ⊔ T < ⊤ → ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ E : Subgroup (StatedSp 2 k), E ≤ B →
        IsPGroup r E → IsCyclic E) ∧
    ∀ D : RootWeightDatum k, D.rank = 2 → ∀ T B : Subgroup (ModGL D.tag k),
      IsSylowOf 2 T D.group → B ≤ D.group → Group.IsPerfect B → B ⊔ T < D.group →
      ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ E : Subgroup (ModGL D.tag k), E ≤ B → IsPGroup r E →
        IsCyclic E :=
  ⟨fun T _ hBp hBT _ hr hr2 _ hEB hE =>
      projectiveSL_three_perfect_odd_isCyclic T hBp hBT hr hr2 hEB hE,
    fun T _ hBp hBT _ hr hr2 _ hEB hE =>
      statedSp_two_perfect_odd_isCyclic T hBp hBT hr hr2 hEB hE,
    fun D hD _ _ hT hBC hBp hBT _ hr hr2 _ hEB hE =>
      rootWeight_rank_two_perfect_odd_isCyclic D hD hT hBC hBp hBT hr hr2 hEB hE⟩

end CFSG.Quasithin.H13.QRC
