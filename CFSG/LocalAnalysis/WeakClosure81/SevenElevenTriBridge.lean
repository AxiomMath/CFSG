module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriAmb
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriQuot
public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenCMin

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

private lemma triaBr_ofMul_sub {M : Type*} [Group M] (a b : M) :
    (Additive.ofMul a : Additive M) - Additive.ofMul b = Additive.ofMul (a * b⁻¹) := by
  rw [sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul]

private lemma triaBr_mul_mul_eq_of_orderOf_mul {Q : Type*} [Group Q] {d e : Q}
    (hd : d * d = 1) (he : e * e = 1) (h3 : orderOf (d * e) = 3) :
    d * e * d = e * d * e := by
  have hd' : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hc : (d * e) ^ 3 = 1 := by
    rw [← h3]
    exact pow_orderOf_eq_one _
  have h : d * e * d * (e * d * e) = 1 := by
    rw [← hc, pow_three]
    group
  calc d * e * d = (e * d * e)⁻¹ := eq_inv_of_mul_eq_one_left h
    _ = e⁻¹ * d⁻¹ * e⁻¹ := by group
    _ = e * d * e := by rw [hd', he']

private lemma triaBr_commutator_mem {Q : Type*} [Group Q] {I K : Subgroup Q}
    (hKN : ∀ k : ↥K, ∀ x ∈ I, (k : Q) * x * (k : Q)⁻¹ ∈ I) (k : ↥K) (y : ↥I) :
    ⁅(k : Q), (y : Q)⁆ ∈ I := by
  rw [commutatorElement_def]
  exact mul_mem (hKN k (y : Q) y.2) (inv_mem y.2)


theorem exists_trialityRep (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module (ZMod 2) A) (_ : Finite A)
      (ρ : ↥(kSub V H E) →* Module.End (ZMod 2) A),
      TrialityIdent φ {k : ↥(kSub V H E) | (k : G) ∈ dSet V H E} ρ ∧
      (∀ g : ↥(kSub V H E), ρ g = 1 → φ g = 1) := by
  have hIel : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun U => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hIN : ((iSub V H E).subgroupOf H).Normal := iSub_subgroupOf_normal h.le h.normal
  have hKI : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hKN : ∀ k : ↥(kSub V H E), ∀ x ∈ iSub V H E,
      (k : G) * x * (k : G)⁻¹ ∈ iSub V H E := by
    intro k x hx
    have hmem := hIN.conj_mem (⟨x, hIleH hx⟩ : H)
      (Subgroup.mem_subgroupOf.mpr hx) (⟨(k : G), hKI k.2⟩ : H)
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  letI : CommGroup ↥(iSub V H E) :=
    { (inferInstance : Group ↥(iSub V H E)) with
      mul_comm := fun a b => hIel.1.is_comm.comm a b }
  have h2 : ∀ x : Additive ↥(iSub V H E), 2 • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective x
    have ha : a ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hIel.2 (a : G) a.2
    rw [← ofMul_pow, ha]
    rfl
  letI : Module (ZMod 2) (Additive ↥(iSub V H E)) :=
    AddCommGroup.zmodModule (n := 2) h2
  let conjMulEquiv : ↥(kSub V H E) → ↥(iSub V H E) ≃* ↥(iSub V H E) := fun k =>
    { toFun := fun x => ⟨(k : G) * x * (k : G)⁻¹, hKN k x x.2⟩
      invFun := fun x => ⟨(k : G)⁻¹ * x * (k : G), by
        simpa using hKN k⁻¹ x x.2⟩
      left_inv := fun x => Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
      right_inv := fun x => Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group) }
  have hconj : ∀ (k : ↥(kSub V H E)) (y : ↥(iSub V H E)),
      (conjMulEquiv k y : ↥(iSub V H E)) =
        ⟨(k : G) * (y : G) * (k : G)⁻¹, hKN k (y : G) y.2⟩ := fun k y => rfl
  let ρ : ↥(kSub V H E) →* Module.End (ZMod 2) (Additive ↥(iSub V H E)) :=
    { toFun := fun k => AddMonoidHom.toZModLinearMap 2
        ((conjMulEquiv k).toAdditive : Additive ↥(iSub V H E) →+ Additive ↥(iSub V H E))
      map_one' := by
        apply LinearMap.ext
        intro x
        obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
        change Additive.ofMul (conjMulEquiv 1 y) = Additive.ofMul y
        apply congrArg Additive.ofMul
        rw [hconj 1 y]
        apply Subtype.ext
        simp
      map_mul' := by
        intro k l
        apply LinearMap.ext
        intro x
        obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
        rw [Module.End.mul_apply]
        change Additive.ofMul (conjMulEquiv (k * l) y) =
          Additive.ofMul (conjMulEquiv k (conjMulEquiv l y))
        apply congrArg Additive.ofMul
        rw [hconj (k * l) y, hconj l y, hconj k]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group }
  have hρ_apply : ∀ (k : ↥(kSub V H E)) (y : ↥(iSub V H E)),
      ρ k (Additive.ofMul y) = Additive.ofMul (conjMulEquiv k y) := by
    intro k y
    rfl
  have hρsub : ∀ (k : ↥(kSub V H E)) (y : ↥(iSub V H E)),
      (ρ k - 1) (Additive.ofMul y) = Additive.ofMul
        ⟨⁅(k : G), (y : G)⁆, triaBr_commutator_mem hKN k y⟩ := by
    intro k y
    rw [LinearMap.sub_apply, Module.End.one_apply, hρ_apply]
    rw [triaBr_ofMul_sub]
    have hval : (conjMulEquiv k y : ↥(iSub V H E)) * y⁻¹ =
        ⟨⁅(k : G), (y : G)⁆, triaBr_commutator_mem hKN k y⟩ := by
      apply Subtype.ext
      change (k : G) * (y : G) * (k : G)⁻¹ * (y : G)⁻¹ = ⁅(k : G), (y : G)⁆
      rw [commutatorElement_def]
    rw [hval]
  refine ⟨Additive ↥(iSub V H E), inferInstance, inferInstance, inferInstance, ρ,
    ⟨?_, ?_⟩, ?_⟩
  · intro d hd e he hcommde
    obtain ⟨U, hU, hdU, hd1⟩ := mem_dSet.mp hd
    obtain ⟨W, hW, heW, he1⟩ := mem_dSet.mp he
    have hcu := commute_of_commuting_images h hφ hS hU hW hdU heW hd1 he1 hcommde
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
    rw [Module.End.mul_apply, hρsub e, hρsub d, LinearMap.zero_apply, ofMul_eq_zero]
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (hcu (d : G) hdU ⁅(e : G), (y : G)⁆
        (commutator_mem_inf_iSub_of_mem_omegaSet h hW y.2 heW).1)
  · intro d hd e he h3
    obtain ⟨U, hU, hdU, hd1⟩ := mem_dSet.mp hd
    obtain ⟨W, hW, heW, he1⟩ := mem_dSet.mp he
    obtain ⟨hde3, hUW⟩ :=
      orderOf_mul_eq_three_of_images h hφ hS hU hW hdU heW hd1 he1 h3
    have hd2G : (d : G) * (d : G) = 1 := by
      obtain ⟨g, hUg, -, -⟩ := mem_omegaSet.mp hU
      have hmem := (isElemAbelian_conjSubgroup' h.elemAbelian g).2 (d : G) (hUg ▸ hdU)
      simpa [pow_two] using hmem
    have he2G : (e : G) * (e : G) = 1 := by
      obtain ⟨g, hWg, -, -⟩ := mem_omegaSet.mp hW
      have hmem := (isElemAbelian_conjSubgroup' h.elemAbelian g).2 (e : G) (hWg ▸ heW)
      simpa [pow_two] using hmem
    have hd2 : d * d = 1 := Subtype.ext (by simpa using hd2G)
    have he2 : e * e = 1 := Subtype.ext (by simpa using he2G)
    have hbraidG : d * e * d = e * d * e :=
      triaBr_mul_mul_eq_of_orderOf_mul hd2 he2 hde3
    have hra : ρ d * ρ d = 1 := by rw [← map_mul, hd2, map_one]
    have hrb : ρ e * ρ e = 1 := by rw [← map_mul, he2, map_one]
    have hrab : ρ d * ρ e * ρ d = ρ e * ρ d * ρ e := by
      simp only [← map_mul, hbraidG]
    have hdisj : ∀ w : Additive ↥(iSub V H E),
        (∃ x, (ρ d - 1) x = w) → (∃ y, (ρ e - 1) y = w) → w = 0 := by
      intro w hxw hyw
      obtain ⟨x, hx⟩ := hxw
      obtain ⟨y, hy⟩ := hyw
      obtain ⟨x', rfl⟩ := Additive.ofMul.surjective x
      obtain ⟨y', rfl⟩ := Additive.ofMul.surjective y
      rw [hρsub d x'] at hx
      rw [hρsub e y'] at hy
      have hab : (⟨⁅(d : G), (x' : G)⁆, triaBr_commutator_mem hKN d x'⟩ :
            ↥(iSub V H E)) =
          ⟨⁅(e : G), (y' : G)⁆, triaBr_commutator_mem hKN e y'⟩ :=
        Additive.ofMul.injective (hx.trans hy.symm)
      have haU : ((⟨⁅(d : G), (x' : G)⁆, triaBr_commutator_mem hKN d x'⟩ :
            ↥(iSub V H E)) : G) ∈ U :=
        (commutator_mem_inf_iSub_of_mem_omegaSet h hU x'.2 hdU).1
      have hbW : ((⟨⁅(e : G), (y' : G)⁆, triaBr_commutator_mem hKN e y'⟩ :
            ↥(iSub V H E)) : G) ∈ W :=
        (commutator_mem_inf_iSub_of_mem_omegaSet h hW y'.2 heW).1
      have haW : ((⟨⁅(d : G), (x' : G)⁆, triaBr_commutator_mem hKN d x'⟩ :
            ↥(iSub V H E)) : G) ∈ W := by
        rw [hab]; exact hbW
      have hbot : (⟨⁅(d : G), (x' : G)⁆, triaBr_commutator_mem hKN d x'⟩ :
            ↥(iSub V H E)) = 1 := by
        have hmem : ((⟨⁅(d : G), (x' : G)⁆, triaBr_commutator_mem hKN d x'⟩ :
              ↥(iSub V H E)) : G) ∈ (⊥ : Subgroup G) := by
          rw [← hUW]
          exact ⟨haU, haW⟩
        exact Subtype.ext (Subgroup.mem_bot.mp hmem)
      calc w = Additive.ofMul (⟨⁅(d : G), (x' : G)⁆, triaBr_commutator_mem hKN d x'⟩ :
            ↥(iSub V H E)) := hx.symm
        _ = Additive.ofMul (1 : ↥(iSub V H E)) := by rw [hbot]
        _ = 0 := rfl
    exact braid_of_disjoint_range hra hrb hrab hdisj
  · intro g hg
    have hcent : (g : G) ∈ Subgroup.centralizer (iSub V H E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 : ρ g (Additive.ofMul (⟨x, hx⟩ : ↥(iSub V H E))) =
          Additive.ofMul (⟨x, hx⟩ : ↥(iSub V H E)) := by
        rw [hg]
        rfl
      rw [hρ_apply] at h1
      have h2 := Additive.ofMul.injective h1
      have h3 : (g : G) * x * (g : G)⁻¹ = x := by
        have h5 : (conjMulEquiv g (⟨x, hx⟩ : ↥(iSub V H E))) =
            ⟨(g : G) * x * (g : G)⁻¹, hKN g x hx⟩ := rfl
        have h4 := congrArg (fun y : ↥(iSub V H E) => (y : G)) h2
        rw [h5] at h4
        simpa using h4
      have h3' : (g : G) * x = x * (g : G) := by
        calc (g : G) * x = (g : G) * x * (g : G)⁻¹ * (g : G) := by group
          _ = x * (g : G) := by rw [h3]
      exact h3'.symm
    exact (hφ.ker_iff g).mpr (centralizer_iSub_le_pCoreOf h ⟨g.2, hcent⟩)

end CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri
