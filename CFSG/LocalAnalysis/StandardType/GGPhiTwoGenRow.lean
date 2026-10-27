module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem ggPhiTwoRow_conj_injective {X : Type} [Group X]
    (hZ : ∀ z : X, (∀ x : X, z * x = x * z) → z = 1) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro x y hxy
  have h : ∀ z : X, x * z * x⁻¹ = y * z * y⁻¹ := by
    intro z
    have := congrArg (fun f : MulAut X => f z) hxy
    simpa only [MulAut.conj_apply] using this
  have hc : ∀ z : X, (y⁻¹ * x) * z = z * (y⁻¹ * x) := by
    intro z
    calc (y⁻¹ * x) * z = y⁻¹ * (x * z * x⁻¹) * x := by group
      _ = y⁻¹ * (y * z * y⁻¹) * x := by rw [h z]
      _ = z * (y⁻¹ * x) := by group
  have h1 : y⁻¹ * x = 1 := hZ _ hc
  calc x = y * (y⁻¹ * x) := by group
    _ = y * 1 := by rw [h1]
    _ = y := by group

theorem exists_hyperplane_family_of_rootGenAvoidKG {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] {I : Set (MulAut R)} (hrow : GGTorusRootGenAvoidKG p r R I)
    {X : Type} [Group X] [Finite X] (θ : X ≃* R) (hX : commutator X = ⊤)
    (hZ : ∀ z : X, (∀ x : X, z * x = x * z) → z = 1) {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian p E)
    (hsc : ∀ g : X, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E)
    (hI : ∀ x : X, MulAut.conj (θ x) ∈ I) (hr : p ^ r ≤ Nat.card E) (h3 : p ^ 3 ≤ Nat.card E) :
    ∃ (ι : Type) (J : ι → Subgroup X) (C : ι → Subgroup X),
      (∀ i, C i ≤ E) ∧ (∀ i, Nat.card E = Nat.card (C i) * p) ∧
      (∀ i, ⁅J i, J i⁆ = J i) ∧ (∀ i, ∀ x ∈ J i, ∀ e ∈ C i, x * e = e * x) ∧
      (⨆ i, J i) = ⊤ := by
  classical
  let conjHom : X →* MulAut X := MulAut.conj
  have hconj_inj : Function.Injective conjHom := ggPhiTwoRow_conj_injective hZ
  set A : Subgroup (MulAut X) := E.map conjHom with hAdef
  have hcardA : Nat.card ↥A = Nat.card ↥E := by
    rw [hAdef]
    exact Subgroup.card_map_of_injective hconj_inj
  have hA : IsElemAbelian p A := by
    rw [hAdef]
    refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun a ha => ?_⟩
    · apply Subtype.ext
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
      change (↑a : MulAut X) * ↑b = ↑b * ↑a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      haveI : IsMulCommutative ↥E := hE.1
      have hcomm : x * y = y * x :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥E) ⟨y, hy⟩)
      rw [hcomm]
    · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
      rw [← hxa, ← map_pow, hE.2 x hx, map_one]
  have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : X, φ (θ l) = θ (a l) := by
    intro a ha
    rw [hAdef] at ha
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨MulAut.conj (θ e), hI e, fun l => ?_⟩
    change MulAut.conj (θ e) (θ l) = θ (MulAut.conj e l)
    simp only [MulAut.conj_apply, map_mul, map_inv]
  have hscA : GGTorusSelfCent p A := by
    intro n hn hnp
    rw [hAdef]
    refine Subgroup.mem_map_of_mem conjHom ?_
    apply hsc n
    · intro e he
      have hmem : conjHom e ∈ A := by
        rw [hAdef]
        exact Subgroup.mem_map_of_mem conjHom he
      have hfix : MulAut.conj e n = n := hn (conjHom e) hmem
      have h1 : e * n * e⁻¹ = n := by simpa only [MulAut.conj_apply] using hfix
      have h2 : e * n = n * e := by
        calc e * n = e * n * e⁻¹ * e := by group
          _ = n * e := by rw [h1]
      exact h2.symm
    · exact hnp
  have hker : θ.toMonoidHom.ker ≤ Subgroup.center X := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hl1 : l = 1 := θ.injective (by simpa using hl)
    subst hl1
    exact Subgroup.one_mem _
  have hrA : p ^ r ≤ Nat.card A := by rw [hcardA]; exact hr
  have h3A : p ^ 3 ≤ Nat.card A := by rw [hcardA]; exact h3
  have hT : GGTorusRootGenAvoid p A :=
    hrow X θ.toMonoidHom θ.surjective hker hX A hA hAI hrA h3A hscA
  have hgen1 := hT 1
  let eA : ↥E ≃* ↥A := E.equivMapOfInjective conjHom hconj_inj
  have eA_coe : ∀ x : ↥E, ((eA x : ↥A) : MulAut X) = MulAut.conj (x : X) :=
    fun x => Subgroup.coe_equivMapOfInjective_apply E conjHom hconj_inj x
  let P' : X × Subgroup X → Prop := fun q =>
    ∃ hn : MulAut.conj q.1 ∈ Subgroup.normalizer (A : Set (MulAut X)),
      GGTorusWeylElt p A q.1 ∧ GGIsReflection p (ggConjAut A hn) ∧ ggConjAut A hn ≠ 1 ∧
        q.1 ∈ q.2 ∧ IsComponentOf q.2 (ggHypCent A q.1) ∧ p ∣ Nat.card q.2
  let ι : Type := {q : X × Subgroup X // P' q}
  let Jfam : ι → Subgroup X := fun i => i.1.2
  let Cfam : ι → Subgroup X := fun i =>
    ((ggFix (ggConjAut A i.2.choose)).comap eA.toMonoidHom).map E.subtype
  have hsup_le : (⨆ i : ι, Jfam i) ≤
      (⨆ (n : X) (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut X)))
        (J' : Subgroup X)
        (_ : GGTorusWeylElt p A n ∧ GGIsReflection p (ggConjAut A hn) ∧ ggConjAut A hn ≠ 1 ∧
          n ∈ J' ∧ IsComponentOf J' (ggHypCent A n) ∧ p ∣ Nat.card J'), J') := by
    refine iSup_le fun i => ?_
    exact le_iSup_of_le i.1.1 (le_iSup_of_le i.2.choose
      (le_iSup_of_le i.1.2 (le_iSup_of_le i.2.choose_spec le_rfl)))
  have hsup_ge : (⨆ (n : X) (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut X)))
        (J' : Subgroup X)
        (_ : GGTorusWeylElt p A n ∧ GGIsReflection p (ggConjAut A hn) ∧ ggConjAut A hn ≠ 1 ∧
          n ∈ J' ∧ IsComponentOf J' (ggHypCent A n) ∧ p ∣ Nat.card J'), J') ≤
      (⨆ i : ι, Jfam i) := by
    refine iSup_le fun n => iSup_le fun hn => iSup_le fun J' => iSup_le fun h => ?_
    exact le_iSup (fun i : ι => Jfam i) ⟨(n, J'), ⟨hn, h⟩⟩
  have hsup_eq : (⨆ i : ι, Jfam i) =
      (⨆ (n : X) (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut X)))
        (J' : Subgroup X)
        (_ : GGTorusWeylElt p A n ∧ GGIsReflection p (ggConjAut A hn) ∧ ggConjAut A hn ≠ 1 ∧
          n ∈ J' ∧ IsComponentOf J' (ggHypCent A n) ∧ p ∣ Nat.card J'), J') :=
    le_antisymm hsup_le hsup_ge
  refine ⟨ι, Jfam, Cfam, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Subgroup.map_subtype_le _
  · intro i
    have hrefl := i.2.choose_spec.2.1
    have hCcard : Nat.card {b : ↥A // ggConjAut A i.2.choose b = b} = Nat.card (Cfam i) := by
      have h2 : Nat.card ↥((ggFix (ggConjAut A i.2.choose)).comap eA.toMonoidHom) =
          Nat.card {b : ↥A // ggConjAut A i.2.choose b = b} :=
        Nat.card_congr (Equiv.subtypeEquiv eA (fun x => Iff.rfl))
      exact h2.symm.trans (Subgroup.card_map_of_injective E.subtype_injective).symm
    calc Nat.card E = Nat.card ↥A := hcardA.symm
      _ = Nat.card {b : ↥A // ggConjAut A i.2.choose b = b} * p := hrefl.2.symm
      _ = Nat.card (Cfam i) * p := by rw [hCcard]
  · intro i
    have hcomp : IsComponentOf (Jfam i) (ggHypCent A i.1.1) := i.2.choose_spec.2.2.2.2.1
    have hcomm : commutator ↥(Jfam i) = ⊤ := hcomp.2.2.1
    have htop : (⊤ : Subgroup ↥(Jfam i)).map (Jfam i).subtype = Jfam i := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hmap : ((commutator ↥(Jfam i)).map (Jfam i).subtype) = ⁅Jfam i, Jfam i⁆ := by
      change (Subgroup.map (Jfam i).subtype ⁅(⊤ : Subgroup ↥(Jfam i)), ⊤⁆) = ⁅Jfam i, Jfam i⁆
      rw [Subgroup.map_commutator]
      simp only [htop]
    calc ⁅Jfam i, Jfam i⁆ = (commutator ↥(Jfam i)).map (Jfam i).subtype := hmap.symm
      _ = (⊤ : Subgroup ↥(Jfam i)).map (Jfam i).subtype := by rw [hcomm]
      _ = Jfam i := htop
  · intro i x hx e he
    have hcomp : IsComponentOf (Jfam i) (ggHypCent A i.1.1) := i.2.choose_spec.2.2.2.2.1
    have hxJ : x ∈ ggHypCent A i.1.1 := hcomp.1 hx
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp he
    rw [Subgroup.mem_comap] at hy
    have hcy : ggConjAut A i.2.choose (eA y) = eA y := hy
    have hconj_eq :
        MulAut.conj i.1.1 * MulAut.conj e = MulAut.conj e * MulAut.conj i.1.1 := by
      have hv := congrArg (fun z : ↥A => (z : MulAut X)) hcy
      rw [ggConjAut_apply A i.2.choose (eA y), eA_coe] at hv
      have heq : e = (y : X) := hye.symm
      rw [heq]
      calc MulAut.conj i.1.1 * MulAut.conj (y : X) =
            (MulAut.conj i.1.1 * MulAut.conj (y : X) * (MulAut.conj i.1.1)⁻¹) *
              MulAut.conj i.1.1 := by group
        _ = MulAut.conj (y : X) * MulAut.conj i.1.1 := by rw [hv]
    have heA : MulAut.conj e ∈ A := by
      have h1 : ((eA y : ↥A) : MulAut X) ∈ A := (eA y).2
      rw [eA_coe] at h1
      have hye' : (y : X) = e := hye
      rwa [hye'] at h1
    have hxfix : x ∈ ggFix (MulAut.conj e) := by
      have hxJ' : x ∈ ⨅ (a : MulAut X)
          (_ : a ∈ A ∧ MulAut.conj i.1.1 * a = a * MulAut.conj i.1.1), ggFix a := by
        rwa [ggHypCent] at hxJ
      exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hxJ' (MulAut.conj e)) ⟨heA, hconj_eq⟩
    have h2 : e * x * e⁻¹ = x := by
      have := hxfix
      simpa only [mem_ggFix, MulAut.conj_apply] using this
    have h3 : e * x = x * e := by
      calc e * x = e * x * e⁻¹ * e := by group
        _ = x * e := by rw [h2]
    exact h3.symm
  · rw [hsup_eq]
    exact hgen1

end CFSG.StandardType

end
