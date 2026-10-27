module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

namespace NOne

open scoped Classical in
@[expose] noncomputable def rankOneMap {Ω : Type*} [Group Ω] (Q : Subgroup Ω) (w v : Ω) : Ω :=
  if v ∈ Q then 1 else w

theorem rankOneMap_of_mem {Ω : Type*} [Group Ω] {Q : Subgroup Ω} {w v : Ω} (h : v ∈ Q) :
    rankOneMap Q w v = 1 := by
  simp [rankOneMap, h]

theorem rankOneMap_of_not_mem {Ω : Type*} [Group Ω] {Q : Subgroup Ω} {w v : Ω} (h : v ∉ Q) :
    rankOneMap Q w v = w := by
  simp [rankOneMap, h]

private theorem zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem add_smulRight {W X : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    (f g : W →ₗ[ZMod 2] ZMod 2) (x : X) :
    (f + g).smulRight x = f.smulRight x + g.smulRight x := by
  ext v
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply, add_smul]

theorem mem_closure_rankOne {W X : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup X] [Module (ZMod 2) X] (S : Set (W →ₗ[ZMod 2] ZMod 2))
    (Ψ : W →ₗ[ZMod 2] X) (hΨ : ∀ v : W, (∀ f ∈ S, f v = 0) → Ψ v = 0) :
    Ψ ∈ AddSubgroup.closure {Φ : W →ₗ[ZMod 2] X | ∃ f ∈ S, ∃ x : X, Φ = f.smulRight x} := by
  let Φ₀ : AddSubgroup (W →ₗ[ZMod 2] X) :=
    AddSubgroup.closure {Φ : W →ₗ[ZMod 2] X | ∃ f ∈ S, ∃ x : X, Φ = f.smulRight x}
  have hgen : ∀ (K : W →ₗ[ZMod 2] ZMod 2) (x : X),
      (⨅ f ∈ S, LinearMap.ker f) ≤ LinearMap.ker K → K.smulRight x ∈ Φ₀ := by
    intro K x hK
    have hKspan : K ∈ Submodule.span (ZMod 2)
        (Set.range fun f : ↥S => (f : W →ₗ[ZMod 2] ZMod 2)) := by
      refine FiniteDimensional.mem_span_of_iInf_ker_le_ker (𝕜 := ZMod 2) (E := W) ?_
      rwa [iInf_subtype'] at hK
    have hspan_mem : ∀ K' ∈ Submodule.span (ZMod 2)
        (Set.range fun f : ↥S => (f : W →ₗ[ZMod 2] ZMod 2)), K'.smulRight x ∈ Φ₀ := by
      intro K' hK'
      refine Submodule.span_induction (p := fun K' _ => K'.smulRight x ∈ Φ₀) ?_ ?_ ?_ ?_ hK'
      · rintro f ⟨i, rfl⟩
        exact AddSubgroup.subset_closure ⟨i.1, i.2, x, rfl⟩
      · simpa using Φ₀.zero_mem
      · intro f g _ _ ihf ihg
        rw [add_smulRight f g x]
        exact Φ₀.add_mem ihf ihg
      · intro c f _ ih
        rcases zmod_two_eq_zero_or_one c with rfl | rfl
        · rw [zero_smul, LinearMap.zero_smulRight]
          exact Φ₀.zero_mem
        · rw [one_smul]
          exact ih
    exact hspan_mem K hKspan
  let B : Submodule (ZMod 2) X := LinearMap.range Ψ
  let b : Module.Basis (Fin (Module.finrank (ZMod 2) B)) (ZMod 2) B :=
    Module.finBasis (ZMod 2) B
  let K : Fin (Module.finrank (ZMod 2) B) → W →ₗ[ZMod 2] ZMod 2 :=
    fun j => (b.coord j).comp Ψ.rangeRestrict
  have hKmem : ∀ j, (K j).smulRight ((b j : B) : X) ∈ Φ₀ := by
    intro j
    refine hgen (K j) ((b j : B) : X) ?_
    intro v hv
    rw [LinearMap.mem_ker]
    have hvS : ∀ f ∈ S, f v = 0 := by
      simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hv
    have h0 : Ψ.rangeRestrict v = 0 := by
      apply Subtype.ext
      simpa using hΨ v hvS
    show (b.coord j) (Ψ.rangeRestrict v) = 0
    rw [h0, map_zero]
  have hΨsum : Ψ = ∑ j, (K j).smulRight ((b j : B) : X) := by
    ext v
    have hrepr : (∑ j, (b.coord j) (Ψ.rangeRestrict v) • (b j)) = Ψ.rangeRestrict v := by
      simpa only [Module.Basis.coord_apply] using b.sum_repr (Ψ.rangeRestrict v)
    have hco := congrArg (fun z : B => (z : X)) hrepr
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hco
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]
    exact hco.symm
  have hsum_mem : (∑ j, (K j).smulRight ((b j : B) : X)) ∈ Φ₀ :=
    AddSubgroup.sum_mem Φ₀ fun j _ => hKmem j
  rw [hΨsum]
  exact hsum_mem

open scoped Classical in
private noncomputable def bit (P : Prop) : ZMod 2 := if P then 0 else 1

private theorem neg_one_zmod_two : (-1 : ZMod 2) = 1 := by decide

private theorem one_add_one_zmod_two : (1 : ZMod 2) + 1 = 0 := by decide

private theorem bit_add (P Q : Prop) : bit P + bit Q = bit (P ↔ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [bit, hP, hQ, one_add_one_zmod_two]

theorem exists_list_prod_rankOne {Ω : Type*} [Group Ω] [Finite Ω] {E E₀ : Subgroup Ω}
    (hE : IsElemAbelian 2 E) (hE₀ : E₀ ≤ E) (𝒬 : Set (Subgroup Ω))
    (h𝒬 : ∀ Q ∈ 𝒬, E₀ ≤ Q ∧ Q ≤ E ∧ Q.relIndex E = 2)
    (hsep : ∀ v ∈ E, (∀ Q ∈ 𝒬, v ∈ Q) → v ∈ E₀) {Ψ : Ω → Ω} (hΨE : ∀ v ∈ E, Ψ v ∈ E₀)
    (hΨmul : ∀ v ∈ E, ∀ v' ∈ E, Ψ (v * v') = Ψ v * Ψ v') (hΨ1 : ∀ w ∈ E₀, Ψ w = 1) :
    ∃ l : List (Subgroup Ω × Ω), (∀ p ∈ l, p.1 ∈ 𝒬 ∧ p.2 ∈ E₀) ∧
      ∀ v ∈ E, Ψ v = (l.map fun p => rankOneMap p.1 p.2 v).prod := by
  classical
  letI : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := hE.1.is_comm.comm }
  letI : CommGroup ↥E₀ := { (inferInstance : Group ↥E₀) with
    mul_comm := fun a b => Subtype.ext (by
      have h := hE.1.is_comm.comm (⟨a.1, hE₀ a.2⟩ : ↥E) (⟨b.1, hE₀ b.2⟩ : ↥E)
      simpa using congrArg Subtype.val h) }
  letI : Module (ZMod 2) (Additive ↥E) := AddCommGroup.zmodModule (n := 2) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using hE.2 x.toMul x.toMul.2)
  letI : Module (ZMod 2) (Additive ↥E₀) := AddCommGroup.zmodModule (n := 2) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using hE.2 x.toMul (hE₀ x.toMul.2))
  let Ψ' : Additive ↥E →+ Additive ↥E₀ :=
    { toFun := fun v => Additive.ofMul ⟨Ψ v.toMul, hΨE v.toMul v.toMul.2⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        simpa using hΨ1 1 E₀.one_mem
      map_add' := fun v w => by
        apply Additive.toMul.injective
        apply Subtype.ext
        simpa using hΨmul v.toMul v.toMul.2 w.toMul w.toMul.2 }
  let Ψt : Additive ↥E →ₗ[ZMod 2] Additive ↥E₀ := AddMonoidHom.toZModLinearMap 2 Ψ'
  let lam : (Q : Subgroup Ω) → Q ≤ E → Q.relIndex E = 2 → Additive ↥E →ₗ[ZMod 2] ZMod 2 :=
    fun Q _ hQidx =>
      { toFun := fun z => bit ((z.toMul : Ω) ∈ Q)
        map_add' := fun a b => by
          have hkey : (a.toMul : Ω) * (b.toMul : Ω) ∈ Q ↔
              (((a.toMul : Ω) ∈ Q) ↔ ((b.toMul : Ω) ∈ Q)) := by
            have hidx : (Q.subgroupOf E).index = 2 := by
              simpa only [Subgroup.relIndex] using hQidx
            have hf := Subgroup.mul_mem_iff_of_index_two (H := Q.subgroupOf E) hidx
              (a := a.toMul) (b := b.toMul)
            simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using hf
          show bit (((a + b).toMul : Ω) ∈ Q) =
            bit ((a.toMul : Ω) ∈ Q) + bit ((b.toMul : Ω) ∈ Q)
          rw [show (a + b).toMul = a.toMul * b.toMul from rfl, Subgroup.coe_mul, hkey, bit_add]
        map_smul' := fun c z => by
          rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> simp [bit] }
  have lam_apply : ∀ (Q : Subgroup Ω) (hQE : Q ≤ E) (hQidx : Q.relIndex E = 2)
      (z : Additive ↥E), lam Q hQE hQidx z = bit ((z.toMul : Ω) ∈ Q) := fun _ _ _ _ => rfl
  let S : Set (Additive ↥E →ₗ[ZMod 2] ZMod 2) :=
    Set.range fun Q : ↥𝒬 => lam Q.1 (h𝒬 Q.1 Q.2).2.1 (h𝒬 Q.1 Q.2).2.2
  have hΨt : ∀ v : Additive ↥E, (∀ f ∈ S, f v = 0) → Ψt v = 0 := by
    intro v hv
    have hvQ : ∀ Q ∈ 𝒬, (v.toMul : Ω) ∈ Q := by
      intro Q hQ
      have hf : lam Q (h𝒬 Q hQ).2.1 (h𝒬 Q hQ).2.2 ∈ S := ⟨⟨Q, hQ⟩, rfl⟩
      have h0 : lam Q (h𝒬 Q hQ).2.1 (h𝒬 Q hQ).2.2 v = 0 := hv _ hf
      rw [lam_apply Q (h𝒬 Q hQ).2.1 (h𝒬 Q hQ).2.2] at h0
      unfold bit at h0
      by_contra hmem
      rw [if_neg hmem] at h0
      exact one_ne_zero h0
    have hvE₀ : (v.toMul : Ω) ∈ E₀ := hsep v.toMul v.toMul.2 hvQ
    have hwt : Ψt v = Additive.ofMul ⟨Ψ (v.toMul : Ω), hΨE v.toMul v.toMul.2⟩ := rfl
    rw [hwt, ofMul_eq_zero]
    exact Subtype.ext (hΨ1 v.toMul hvE₀)
  let T : Set (Additive ↥E →ₗ[ZMod 2] Additive ↥E₀) :=
    {Φ | ∃ f ∈ S, ∃ x, Φ = f.smulRight x}
  have hclos : Ψt ∈ AddSubgroup.closure T := mem_closure_rankOne S Ψt hΨt
  let P : (Additive ↥E →ₗ[ZMod 2] Additive ↥E₀) → Prop :=
    fun Φ => ∃ l : List (Subgroup Ω × Ω), (∀ p ∈ l, p.1 ∈ 𝒬 ∧ p.2 ∈ E₀) ∧
      ∀ v : ↥E, ((Φ (Additive.ofMul v)).toMul : Ω) =
        (l.map fun p => rankOneMap p.1 p.2 (v : Ω)).prod
  have hgen_apply : ∀ (Q : Subgroup Ω) (hQE : Q ≤ E) (hQidx : Q.relIndex E = 2)
      (x : Additive ↥E₀) (v : ↥E),
      (((lam Q hQE hQidx).smulRight x) (Additive.ofMul v)).toMul =
        rankOneMap Q (x.toMul : Ω) (v : Ω) := by
    intro Q hQE hQidx x v
    rw [LinearMap.smulRight_apply, lam_apply Q hQE hQidx]
    change (bit ((v : Ω) ∈ Q) • x).toMul = rankOneMap Q (x.toMul : Ω) (v : Ω)
    unfold bit
    by_cases hv : (v : Ω) ∈ Q
    · rw [if_pos hv, zero_smul, rankOneMap_of_mem hv]
      rfl
    · rw [if_neg hv, one_smul, rankOneMap_of_not_mem hv]
  have hP : P Ψt := by
    refine AddSubgroup.closure_induction
      (p := fun Φ (_ : Φ ∈ AddSubgroup.closure T) => P Φ) ?_ ?_ ?_ ?_ hclos
    · rintro Φ ⟨f, hf, x, rfl⟩
      rcases hf with ⟨Q, rfl⟩
      refine ⟨[(Q.1, (x.toMul : Ω))], ?_, ?_⟩
      · intro p hp
        rw [List.mem_singleton] at hp
        rcases hp with rfl
        exact ⟨Q.2, x.toMul.2⟩
      · intro v
        rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        exact hgen_apply Q.1 (h𝒬 Q.1 Q.2).2.1 (h𝒬 Q.1 Q.2).2.2 x v
    · refine ⟨[], ?_, ?_⟩
      · simp
      · intro v
        simp
    · intro Φ₁ Φ₂ _ _ ih₁ ih₂
      obtain ⟨l₁, hl₁, hval₁⟩ := ih₁
      obtain ⟨l₂, hl₂, hval₂⟩ := ih₂
      refine ⟨l₁ ++ l₂, ?_, ?_⟩
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact hl₁ p hp
        · exact hl₂ p hp
      · intro v
        rw [List.map_append, List.prod_append, LinearMap.add_apply, toMul_add,
          Subgroup.coe_mul, hval₁ v, hval₂ v]
    · intro Φ _ ih
      obtain ⟨l, hl, hval⟩ := ih
      refine ⟨l, hl, ?_⟩
      intro v
      have hneg : -Φ = Φ := by
        calc -Φ = (-1 : ZMod 2) • Φ := (neg_one_smul (ZMod 2) Φ).symm
          _ = (1 : ZMod 2) • Φ := congrArg (fun c : ZMod 2 => c • Φ) neg_one_zmod_two
          _ = Φ := one_smul (ZMod 2) Φ
      rw [hneg]
      exact hval v
  obtain ⟨l, hl, hval⟩ := hP
  refine ⟨l, hl, ?_⟩
  intro v hv
  have hwt : Ψt (Additive.ofMul (⟨v, hv⟩ : ↥E)) =
      Additive.ofMul ⟨Ψ v, hΨE v hv⟩ := rfl
  have h := hval ⟨v, hv⟩
  rw [hwt] at h
  simpa using h

end NOne

end CFSG.LocalAnalysis.WeakClosure81
