module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtCaseA

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

private theorem isCyclicRootTriple_action (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) :
    (∀ i, HardMathSupport.Kantor79.movedSpace (r i) = ZMod p ∙ e i) ∧
      (∀ i j : Fin 3, i ≠ j → ZMod p ∙ e i ≠ ZMod p ∙ e j) ∧
      (∀ i j, r i (e j) = if i = j then -e j else e j) := by
  have hli : LinearIndependent (ZMod p) e := hT.2.2.1
  have hne : ∀ i, e i ≠ 0 := fun i => hli.ne_zero i
  have hspan : ∀ i, HardMathSupport.Kantor79.movedSpace (r i) = ZMod p ∙ e i :=
    fun i => IsRefl.movedSpace_eq_span hp (hT.1 i).2.1 (hT.1 i).2.2 (hne i)
  have hmem : ∀ i, e i ∈ HardMathSupport.Kantor79.movedSpace (r i) := by
    intro i
    rw [hspan i]
    exact Submodule.subset_span (Set.mem_singleton (e i))
  have hspan_ne : ∀ i j : Fin 3, i ≠ j → ZMod p ∙ e i ≠ ZMod p ∙ e j := by
    intro i j hij h
    have hmem' : e j ∈ Submodule.span (ZMod p) (e '' ({i} : Set (Fin 3))) := by
      rw [Set.image_singleton, h]
      exact Submodule.subset_span (Set.mem_singleton (e j))
    exact (hli.notMem_span_image (s := {i}) (x := j) (by simpa [eq_comm] using hij)) hmem'
  refine ⟨hspan, hspan_ne, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst i
    rw [if_pos rfl]
    exact (hT.1 j).2.2
  · rw [if_neg hij]
    exact IsRefl.apply_eq_self_of_commute (hT.1 i).2.1 (hT.1 j).2.1 (hT.2.1 i j)
      (by rw [hspan i, hspan j]; exact hspan_ne i j hij) (e j) (hmem j)

private theorem isCyclicRootTriple_polar_eq_zero (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {Q : QuadraticForm (ZMod p) U} {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) (hoH : IsOrthOn p Q H) :
    ∀ i j : Fin 3, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0 := by
  obtain ⟨-, -, hact⟩ := isCyclicRootTriple_action hp hT
  intro i j hij
  exact IsIsom.polar_eq_zero_of_apply_eq_neg_of_apply_eq hp (hoH.isIsom (hT.1 i).1)
    (by rw [hact i i, if_pos rfl]) (by rw [hact i j, if_neg hij])

private theorem isCyclicRootTriple_norm_eq {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {Q : QuadraticForm (ZMod p) U} {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) (hoH : IsOrthOn p Q H) :
    ∀ i : Fin 3, Q (e i) = Q (e 0) := by
  have hsiso : IsIsom p Q s := hoH.isIsom hT.2.2.2.1
  have hstep : ∀ i : Fin 3, Q (e (i + 1)) = Q (e i) := by
    intro i
    have h := hsiso (e i)
    rwa [hT.2.2.2.2 i] at h
  intro i
  fin_cases i
  · rfl
  · simpa using hstep 0
  · simpa using (hstep 2).symm

private theorem isCyclicRootTriple_root_norm_ne_zero (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {Q : QuadraticForm (ZMod p) U}
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) : Q (e 0) ≠ 0 := by
  obtain ⟨hspan, -, -⟩ := isCyclicRootTriple_action hp hT
  obtain ⟨a, hQa, hha⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ (hT.1 0).2.1
    (hoH.isIsom (hT.1 0).1)
  have hamem : a ∈ HardMathSupport.Kantor79.movedSpace (r 0) :=
    HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hha
  have hamem' : a ∈ ZMod p ∙ e 0 := by
    rw [← hspan 0]
    exact hamem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hamem'
  have hcQ : Q (c • e 0) ≠ 0 := by rwa [← hc] at hQa
  rw [QuadraticMap.map_smul] at hcQ
  intro h0
  exact hcQ (by simp [h0])

private theorem isCyclicRootTriple_fix_root (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {h : U ≃ₗ[ZMod p] U} {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h) (hT : IsCyclicRootTriple p H r e s) :
    ∀ i : Fin 3, i ≠ 0 → h (e i) = e i := by
  obtain ⟨-, -, hact⟩ := isCyclicRootTriple_action hp hT
  intro i hi
  have h0i : (0 : Fin 3) ≠ i := fun h0 => hi h0.symm
  calc h (e i) = r 0 (e i) := by rw [hr]
    _ = e i := by rw [hact 0 i, if_neg h0i]

private theorem isCyclicRootTriple_mem_reflStab (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {h : U ≃ₗ[ZMod p] U} {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h) (hT : IsCyclicRootTriple p H r e s) :
    ∀ i : Fin 3, i ≠ 0 → r i ∈ reflStab p H h := by
  obtain ⟨hspan, -, -⟩ := isCyclicRootTriple_action hp hT
  have hfix := isCyclicRootTriple_fix_root hp hr hT
  intro i hi
  have hle : HardMathSupport.Kantor79.movedSpace (r i) ≤
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    rw [hspan i, Submodule.span_le]
    rintro x rfl
    exact LinearMap.mem_ker.mpr (by
      simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hfix i hi)
  show r i ∈ reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
  exact mem_reflSubgroupIn_of_movedSpace_le (hT.1 i).1 (hT.1 i).2.1 hle

theorem isCyclicRootTriple_root_mem_commutatorSpace (hp : p ≠ 2)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) (i : Fin 3) :
    e i ∈ HardMathSupport.Kantor79.commutatorSpace H := by
  have hspan : HardMathSupport.Kantor79.movedSpace (r i) = ZMod p ∙ e i :=
    IsRefl.movedSpace_eq_span hp (hT.1 i).2.1 (hT.1 i).2.2 (hT.2.2.1.ne_zero i)
  exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 i).1 (by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_singleton (e i)))

theorem finrank_span_pair_of_notMem {x z : U} (hx : x ≠ 0)
    (hz : z ∉ Submodule.span (ZMod p) ({x} : Set U)) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) ({x, z} : Set U)) = 2 := by
  have hz0 : z ≠ 0 := fun h => hz (h ▸ Submodule.zero_mem _)
  have hdisj : Submodule.span (ZMod p) ({x} : Set U) ⊓
      Submodule.span (ZMod p) ({z} : Set U) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v hv
    obtain ⟨cc, rfl⟩ := Submodule.mem_span_singleton.mp hv.2
    by_cases hc : cc = 0
    · rw [hc, zero_smul]
    · exfalso
      apply hz
      have hmem : cc • z ∈ Submodule.span (ZMod p) ({x} : Set U) := hv.1
      have hzmem : z = cc⁻¹ • (cc • z) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hzmem]
      exact Submodule.smul_mem _ _ hmem
  have hspan : Submodule.span (ZMod p) ({x, z} : Set U) =
      Submodule.span (ZMod p) ({x} : Set U) ⊔ Submodule.span (ZMod p) ({z} : Set U) := by
    rw [show ({x, z} : Set U) = insert x {z} from rfl,
      Submodule.span_insert x ({z} : Set U)]
  rw [hspan]
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span (ZMod p) ({x} : Set U)) (Submodule.span (ZMod p) ({z} : Set U))
  rw [hdisj, finrank_bot, finrank_span_singleton hx, finrank_span_singleton hz0] at h
  omega

private theorem finrank_span_pair_eq_two {e : Fin 3 → U} (he : LinearIndependent (ZMod p) e) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 1, e 2} : Set U)) = 2 := by
  have he1 : e 1 ≠ 0 := he.ne_zero 1
  have hli12 : LinearIndependent (ZMod p) ![e 1, e 2] := by
    have hinj : Function.Injective (![1, 2] : Fin 2 → Fin 3) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    have h := he.comp (![1, 2] : Fin 2 → Fin 3) hinj
    have hfun : e ∘ (![1, 2] : Fin 2 → Fin 3) = ![e 1, e 2] := by
      funext k
      fin_cases k <;> rfl
    rwa [hfun] at h
  refine finrank_span_pair_of_notMem he1 ?_
  intro hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  exact (LinearIndependent.pair_iff' he1).mp hli12 a ha

private theorem finrank_commutatorSpace_inf_ker_eq_two (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hsplit : SplitSupport H 3) (hr : r 0 = h) (hT : IsCyclicRootTriple p H r e s) :
    Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace H ⊓
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) = 2 := by
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = 3 :=
    hsplit.2.1
  have he0V : e 0 ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    isCyclicRootTriple_root_mem_commutatorSpace hp hT 0
  have hhe0 : h (e 0) = -e 0 := by
    have h := (hT.1 0).2.2
    rwa [hr] at h
  have he0ker : e 0 ∉ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    intro hmem0
    have hfix0 : h (e 0) = e 0 := by
      have := LinearMap.mem_ker.mp hmem0
      simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using this
    exact hT.2.2.1.ne_zero 0 (eq_zero_of_eq_neg (ZMod.prime_ne_zero p 2 hp)
      ((hhe0.symm.trans hfix0).symm))
  have h := IsRefl.finrank_inf_ker_sub_one_add_one hp hD.isRefl
    (A := HardMathSupport.Kantor79.commutatorSpace H) (a := e 0) he0V he0ker
  omega

private theorem isCyclicRootTriple_commutatorSpace_reflStab (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hD : LemmaTwoSevenData p G H B h)
    (h4 : Module.finrank (ZMod p) U = 4) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h) (hT : IsCyclicRootTriple p H r e s)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hoH : IsOrthOn p Q H) :
    HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      Submodule.span (ZMod p) ({e 1, e 2} : Set U) := by
  have hp3 : p ≠ 3 := by
    intro hp3
    have := hD.setting.five_le_of_eq_three hp3
    omega
  have hsplit : SplitSupport H 3 := by
    have h := hD.setting.sub.2.1
    rw [h4] at h
    norm_num at h
    exact h
  have hfix := isCyclicRootTriple_fix_root hp hr hT
  rw [commutatorSpace_reflStab (X := H) hp hQ hsplit (le_refl 3)
    (fun hp3' => absurd hp3' hp3) hoH hD.mem hD.isRefl]
  have hle : Submodule.span (ZMod p) ({e 1, e 2} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact ⟨isCyclicRootTriple_root_mem_commutatorSpace hp hT 1,
        LinearMap.mem_ker.mpr (by
          simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using
            hfix 1 (by norm_num))⟩
    · exact ⟨isCyclicRootTriple_root_mem_commutatorSpace hp hT 2,
        LinearMap.mem_ker.mpr (by
          simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using
            hfix 2 (by norm_num))⟩
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_pair_eq_two hT.2.2.1,
    finrank_commutatorSpace_inf_ker_eq_two hp hD hsplit hr hT]

theorem exists_frame_of_isCyclicRootTriple (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hr : r 0 = h)
    (hT : IsCyclicRootTriple p H r e s) :
    ∃ Q₁ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₁).Nondegenerate ∧
      IsOrthOn p Q₁ H ∧ Q₁ (e 0) ≠ 0 ∧ (∀ i, Q₁ (e i) = Q₁ (e 0)) ∧
      (∀ i j, i ≠ j → QuadraticMap.polar Q₁ (e i) (e j) = 0) ∧
      (∀ i j, r i (e j) = if i = j then -e j else e j) ∧
      (∀ i, i ≠ 0 → r i ∈ reflStab p H h) ∧
      HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
        Submodule.span (ZMod p) {e 1, e 2} := by
  obtain ⟨Q₁, -, hQ, hoH, -⟩ := exists_isOrthOn_root hp hD
  obtain ⟨-, -, hact⟩ := isCyclicRootTriple_action hp hT
  exact ⟨Q₁, hQ, hoH, isCyclicRootTriple_root_norm_ne_zero hp hT hQ hoH,
    isCyclicRootTriple_norm_eq hT hoH, isCyclicRootTriple_polar_eq_zero hp hT hoH, hact,
    isCyclicRootTriple_mem_reflStab hp hr hT,
    isCyclicRootTriple_commutatorSpace_reflStab hp hD h4 hr hT hQ hoH⟩

end CFSG.StandardType.ZS

end
