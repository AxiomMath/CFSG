module

public import CFSG.RankThree.PartTwo.J2Residue.C4725Module
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public import CFSG.GroupTheory.PCentralElement

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] noncomputable def eJP :
    ↥CFSG.ComponentClassification.J2Cover.Models.P ≃* J2 :=
  (MulEquiv.subgroupCongr CFSG.ComponentClassification.J2Cover.Models.P_eq_autP).trans
    CFSG.ComponentClassification.J2Cover.nativeEquivP.symm

@[expose] noncomputable def x0J :
    J2 :=
  eJP C4725.x0P

theorem threeCentral_map {G H : Type*} [Group G] [Group H] [Finite G] (f : G ≃* H) {a : G}
    (ha : ∃ S : Sylow 3 G, a ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ Subgroup.centralizer {a}) :
    ∃ S : Sylow 3 H, f a ∈ (S : Subgroup H) ∧ (S : Subgroup H) ≤ Subgroup.centralizer {f a} :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exists_sylow_mem_le_centralizer_map f.toMonoidHom f.surjective ha

theorem threeCentral_zJ :
    ∃ S : Sylow 3 Sec4.Sporadic.J2.GJ, Sec4.Sporadic.J2.zJ ∈ (S : Subgroup Sec4.Sporadic.J2.GJ) ∧
      (S : Subgroup Sec4.Sporadic.J2.GJ) ≤ Subgroup.centralizer {Sec4.Sporadic.J2.zJ} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥Sec4.Sporadic.J2.P3 =
      3 ^ (Nat.card Sec4.Sporadic.J2.GJ).factorization 3 := by
    rw [Sec4.Sporadic.J2.card_P3, Sec4.Sporadic.J2.card_GJ,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)]
    norm_num
  refine ⟨Sylow.ofCard _ hcard, ?_, ?_⟩
  · rw [Sylow.coe_ofCard, Sec4.Sporadic.J2.z_eq]
    exact Sec4.Sporadic.J2.z_mem_P3
  · rw [Sylow.coe_ofCard, Sec4.Sporadic.J2.P3, Subgroup.closure_le]
    rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff,
      Sec4.Sporadic.J2.z_eq]
    · exact Sec4.Sporadic.J2.z_comm_x.symm
    · exact Sec4.Sporadic.J2.z_comm_y.symm

theorem exists_conj_zJ_eq :
    ∃ g : Sec4.Sporadic.J2.GJ, g * Sec4.Sporadic.J2.zJ * g⁻¹ =
      MulEquiv.subgroupCongr CFSG.ComponentClassification.J2Cover.Models.P_eq_autP C4725.x0P := by
  set g : Sec4.Sporadic.J2.GJ := MulEquiv.subgroupCongr
    CFSG.ComponentClassification.J2Cover.Models.P_eq_autP (C4725.wordP C4725.gWord)
  have h := CFSG.Monster.B.Co2.eq_of_eqA
    (CFSG.Monster.B.Co2.rep_compA (CFSG.ComponentClassification.J2Cover.Models.rep_wordArr
      C4725.gWord) Sec4.Sporadic.J2.rep_z)
    (CFSG.Monster.B.Co2.rep_compA (CFSG.ComponentClassification.J2Cover.Models.rep_wordArr
      C4725.x0Word) (CFSG.ComponentClassification.J2Cover.Models.rep_wordArr C4725.gWord))
    C4725.conjCheck_spec.1
  refine ⟨g, mul_inv_eq_of_eq_mul (Subtype.ext ?_)⟩
  simp only [g, Subgroup.coe_mul, MulEquiv.subgroupCongr_apply, C4725.x0P, C4725.coe_wordP]
  exact h

theorem x0J_ne_one :
    x0J ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_conj_zJ_eq
  intro h
  apply Sec4.Sporadic.J2.zJ_ne_one
  have h1 : MulEquiv.subgroupCongr CFSG.ComponentClassification.J2Cover.Models.P_eq_autP
      C4725.x0P = 1 := by
    have := congrArg CFSG.ComponentClassification.J2Cover.nativeEquivP h
    rwa [x0J, eJP, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, map_one] at this
  rw [h1] at hg
  have := congrArg (fun x => g⁻¹ * x * g) hg
  simpa [mul_assoc] using this

theorem threeCentral_x0J :
    ∃ S : Sylow 3 J2, x0J ∈ (S : Subgroup J2) ∧ (S : Subgroup J2) ≤ Subgroup.centralizer {x0J} := by
  obtain ⟨g, hg⟩ := exists_conj_zJ_eq
  have h1 := threeCentral_map (MulAut.conj g) threeCentral_zJ
  rw [MulAut.conj_apply, hg] at h1
  exact threeCentral_map CFSG.ComponentClassification.J2Cover.nativeEquivP.symm h1

@[expose] noncomputable def mulAutToEnd (A : Type*) [CommGroup A] [Module (ZMod 2) (Additive A)] :
    MulAut A →* Module.End (ZMod 2) (Additive A) where
  toFun σ := AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive σ.toMonoidHom)
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

theorem mulAutToEnd_apply (A : Type*) [CommGroup A] [Module (ZMod 2) (Additive A)] (σ : MulAut A)
    (x : A) : mulAutToEnd A σ (Additive.ofMul x) = Additive.ofMul (σ x) :=
  rfl

theorem submodule_eq_bot_or_top {G A : Type*} [Group G] [CommGroup A]
    [Module (ZMod 2) (Additive A)] (σ : G →* MulAut A)
    (hirr : ∀ K : Subgroup A, (∀ x : G, ∀ a ∈ K, σ x a ∈ K) → K = ⊥ ∨ K = ⊤)
    (U : Submodule (ZMod 2) (Additive A))
    (hU : ∀ x : G, ∀ u ∈ U, (mulAutToEnd A).comp σ x u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let K : Subgroup A :=
    { carrier := {a | Additive.ofMul a ∈ U}
      mul_mem' := fun {a b} ha hb => by
        show Additive.ofMul (a * b) ∈ U
        rw [ofMul_mul]
        exact U.add_mem ha hb
      one_mem' := by
        show Additive.ofMul (1 : A) ∈ U
        rw [ofMul_one]
        exact U.zero_mem
      inv_mem' := fun {a} ha => by
        show Additive.ofMul a⁻¹ ∈ U
        rw [ofMul_inv]
        exact U.neg_mem ha }
  have hmem : ∀ u : Additive A, u ∈ U ↔ Additive.toMul u ∈ K := fun u => by
    show u ∈ U ↔ Additive.ofMul (Additive.toMul u) ∈ U
    rw [ofMul_toMul]
  rcases hirr K (fun x a ha => by
      show Additive.ofMul (σ x a) ∈ U
      rw [← mulAutToEnd_apply]
      exact hU x _ ha) with h | h
  · left
    refine (Submodule.eq_bot_iff U).2 fun u hu => ?_
    rw [hmem, h, Subgroup.mem_bot] at hu
    rw [← ofMul_toMul u, hu, ofMul_one]
  · right
    refine Submodule.eq_top_iff'.2 fun u => ?_
    rw [hmem, h]
    exact Subgroup.mem_top _

theorem eq_one_of_conj_fixes {L : Type*} [Group L] {M : Subgroup L} [M.Normal] {d : L}
    (hCd : M ⊓ Subgroup.centralizer ({d} : Set L) = ⊥) {g m : L} (hm : m ∈ M)
    (h : (g * d * g⁻¹) * m * (g * d * g⁻¹)⁻¹ = m ∨
      (g * d * g⁻¹)⁻¹ * m * (g * d * g⁻¹)⁻¹⁻¹ = m) : m = 1 := by
  set x := g⁻¹ * m * g
  have hxM : x ∈ M := by
    have := (inferInstance : M.Normal).conj_mem m hm g⁻¹
    rwa [inv_inv] at this
  have hxd : x * d = d * x := by
    rcases h with h | h
    · have e : d * x * d⁻¹ = g⁻¹ * ((g * d * g⁻¹) * m * (g * d * g⁻¹)⁻¹) * g := by
        simp only [x]
        group
      rw [h] at e
      calc x * d = d * x * d⁻¹ * d := by rw [e]
        _ = d * x := by group
    · have e : d⁻¹ * x * d = g⁻¹ * ((g * d * g⁻¹)⁻¹ * m * (g * d * g⁻¹)⁻¹⁻¹) * g := by
        simp only [x]
        group
      rw [h] at e
      calc x * d = d * (d⁻¹ * x * d) := by group
        _ = d * x := by rw [e]
  have hx1 : x ∈ M ⊓ Subgroup.centralizer ({d} : Set L) :=
    Subgroup.mem_inf.2 ⟨hxM, Subgroup.mem_centralizer_singleton_iff.2 hxd⟩
  rw [hCd, Subgroup.mem_bot] at hx1
  calc m = g * x * g⁻¹ := by simp only [x]; group
    _ = 1 := by rw [hx1]; group

end CFSG.RankThree.PartTwo.J2Residue
