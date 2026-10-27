module

public import CFSG.RankThree.PartOne.FIS.ReducedChar
public import CFSG.RankThree.PartOne.FIS.CenterLift
public import CFSG.RankThree.PartOne.FIS.Item72
public import CFSG.RankThree.PartOne.FIS.Item73
public import CFSG.RankThree.PartOne.S12.InputsFischer

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7
open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification Equiv Equiv.Perm

theorem LocalIso.ne_and_comm_iff {X : Type} [Group X] {E : Set X} {e : X} {n : ℕ}
    (L : LocalIso E e n) (p q : ↥(LocalGroup E e)) :
    (L.φ p ≠ L.φ q ∧ L.φ p * L.φ q = L.φ q * L.φ p) ↔ ((p : X) ≠ q ∧ (p : X) * q = q * p) := by
  rw [← map_mul, ← map_mul, ne_eq, ne_eq, L.φ.injective.eq_iff, L.φ.injective.eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (Subtype.ext h), congrArg Subtype.val h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (congrArg Subtype.val h), Subtype.ext h2⟩

theorem LocalIso.exists_mem {X : Type} [Group X] {E : Set X} {e : X} {n : ℕ} (L : LocalIso E e n)
    (h2 : 2 ≤ n) : ∃ f, f ∈ LocalClass E e :=
  ⟨_, L.mem_of_swap (σ := swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
    ⟨_, _, by simp [Fin.ext_iff], rfl⟩⟩

theorem vSet_subset_singleton {G : Type} [Group G] {D : Set G} (hP : Pair G D) {n : ℕ}
    (h3 : 3 ≤ n) {d : G} (L : LocalIso D d n) {a : G} (ha : a ∈ vSet D d) : a = d := by
  by_contra hne
  have haD := ha.1
  have hcent : centralizerIn D a = centralizerIn D d := ha.2
  have had : a * d = d * a := by
    have : a ∈ centralizerIn D a := ⟨haD, rfl⟩
    rw [hcent] at this
    exact this.2
  have hloc : a ∈ LocalClass D d := ⟨haD, hne, had⟩
  have hcomm : ∀ e ∈ LocalClass D d, e * a = a * e := by
    intro e he
    have : e ∈ centralizerIn D d := ⟨he.1, he.2.2⟩
    rw [← hcent] at this
    exact this.2
  have h1 : L.φ ⟨a, mem_localGroup hloc⟩ = 1 := by
    apply perm_eq_one_of_commute_swaps h3
    intro τ hτ
    have hu := L.mem_of_swap hτ
    have hc : (⟨a, mem_localGroup hloc⟩ : ↥(LocalGroup D d)) * L.φ.symm τ =
        L.φ.symm τ * ⟨a, mem_localGroup hloc⟩ := Subtype.ext (hcomm _ hu).symm
    have h' := congrArg L.φ hc
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
  have h2 : (⟨a, mem_localGroup hloc⟩ : ↥(LocalGroup D d)) = 1 :=
    L.φ.injective (h1.trans (map_one _).symm)
  exact Pair.ne_one hP haD (congrArg Subtype.val h2)

theorem normal_le_center_of_fixes {G : Type} [Group G] {D : Set G} (hP : Pair G D)
    {M : Subgroup G} [hM : M.Normal] {d : G} (hd : d ∈ D) (h : ∀ y ∈ M, y * d * y⁻¹ = d) :
    M ≤ Subgroup.center G := by
  intro y hy
  refine (Pair.mem_center_iff hP).2 fun e he => ?_
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
  have hy' : g⁻¹ * y * g ∈ M := by simpa using hM.conj_mem y hy g⁻¹
  have hz : (g⁻¹ * y * g) * d = d * (g⁻¹ * y * g) := by
    calc (g⁻¹ * y * g) * d = (g⁻¹ * y * g) * d * (g⁻¹ * y * g)⁻¹ * (g⁻¹ * y * g) := by group
      _ = d * (g⁻¹ * y * g) := by rw [h _ hy']
  calc g * d * g⁻¹ * y = g * (d * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * d) * g⁻¹ := by rw [hz]
    _ = y * (g * d * g⁻¹) := by group

theorem wSet_subset_singleton {G : Type} [Group G] {D : Set G} (hP : Pair G D) {n : ℕ}
    (hI : PermInput n) (h4 : 4 ≤ n) {d : G} (hd : d ∈ D) (L : LocalIso D d n) {a : G}
    (ha : a ∈ wSet D d) : a = d := by
  by_contra hne
  have haD := ha.1
  have hloc : localSet D a = localSet D d := ha.2
  have had : a * d ≠ d * a := by
    intro h
    have hmem : a ∈ localSet D d := ⟨haD, h, hne⟩
    rw [← hloc] at hmem
    exact hmem.2.2 rfl
  obtain ⟨f, hfd⟩ : ∃ f, f ∈ localSet D d := by
    obtain ⟨f, hf⟩ := L.exists_mem (by omega)
    exact ⟨f, by rw [← localClass_eq_localSet]; exact hf⟩
  have hfa : f ∈ localSet D a := by rw [hloc]; exact hfd
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd hfd.1)
  obtain ⟨ι, hι⟩ := exists_localEquiv_conj hP d g
  let Lf : LocalIso D (g * d * g⁻¹) n := L.transport ι hι
  have hdf : d ∈ LocalClass D (g * d * g⁻¹) := ⟨hd, hfd.2.2.symm, hfd.2.1.symm⟩
  have haf : a ∈ LocalClass D (g * d * g⁻¹) := ⟨haD, hfa.2.2.symm, hfa.2.1.symm⟩
  have hnc : Lf.φ ⟨a, mem_localGroup haf⟩ * Lf.φ ⟨d, mem_localGroup hdf⟩ ≠
      Lf.φ ⟨d, mem_localGroup hdf⟩ * Lf.φ ⟨a, mem_localGroup haf⟩ := by
    intro h
    exact had ((Lf.ne_and_comm_iff ⟨a, mem_localGroup haf⟩ ⟨d, mem_localGroup hdf⟩).1
      ⟨fun h' => hne (congrArg Subtype.val (Lf.φ.injective h')), h⟩).2
  obtain ⟨t, ht, hdist⟩ := hI.distinguish h4 (Lf.swap_of_mem haf) (Lf.swap_of_mem hdf) hnc
  have hu := Lf.mem_of_swap ht
  have hteq : Lf.φ (Lf.φ.symm t) = t := Lf.φ.apply_symm_apply t
  rw [← hteq, Lf.ne_and_comm_iff (Lf.φ.symm t) ⟨d, mem_localGroup hdf⟩,
    Lf.ne_and_comm_iff (Lf.φ.symm t) ⟨a, mem_localGroup haf⟩] at hdist
  apply hdist
  have hmd : ((Lf.φ.symm t : ↥(LocalGroup D (g * d * g⁻¹))) : G) ∈ localSet D d ↔
      ((Lf.φ.symm t : ↥(LocalGroup D (g * d * g⁻¹))) : G) ≠ d ∧
        ((Lf.φ.symm t : ↥(LocalGroup D (g * d * g⁻¹))) : G) * d =
          d * ((Lf.φ.symm t : ↥(LocalGroup D (g * d * g⁻¹))) : G) :=
    ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨hu.1, h.2, h.1⟩⟩
  have hma : ((Lf.φ.symm t : ↥(LocalGroup D (g * d * g⁻¹))) : G) ∈ localSet D a ↔
      ((Lf.φ.symm t : ↥(LocalGroup D (g * d * g⁻¹))) : G) ≠ a ∧
        ((Lf.φ.symm t : ↥(LocalGroup D (g * d * g⁻¹))) : G) * a =
          a * ((Lf.φ.symm t : ↥(LocalGroup D (g * d * g⁻¹))) : G) :=
    ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨hu.1, h.2, h.1⟩⟩
  rw [← hmd, ← hma, hloc]

theorem inFischer44 : InFischer44 := by
  intro G _ _ D hD htr d hd n hn3 hn5 hiso
  obtain ⟨θ0⟩ := hiso
  have hI : PermInput n := permInput hn3 hn5
  have hP : Pair G D := pair_of_tt hD htr hd
  have hcl : Subgroup.closure (localSet D d) = LocalGroup D d := by
    rw [LocalGroup, localClass_eq_localSet]
  let L : LocalIso D d n := localIso_of_iso hI hP ((MulEquiv.subgroupCongr hcl.symm).trans θ0)
  obtain ⟨hV, hW, -⟩ := item72_proved G D hD htr d hd
  have hO2 : CFSG.pCore 2 G ≤ Subgroup.center G := by
    have : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
    refine normal_le_center_of_fixes hP hd fun y hy => ?_
    have hmem : y * d * y⁻¹ ∈ conjOrbit (CFSG.pCore 2 G) d := ⟨y, hy, rfl⟩
    rw [← hV] at hmem
    exact vSet_subset_singleton hP (by omega) L hmem
  by_cases hcase : n = 3 ∧ ¬ CFSG.pCore 3 G ≤ Subgroup.center G
  · exact Or.inr hcase
  refine Or.inl ?_
  have hO3 : CFSG.pCore 3 G ≤ Subgroup.center G := by
    by_cases h3 : n = 3
    · by_contra hh
      exact hcase ⟨h3, hh⟩
    · have : (CFSG.pCore 3 G).Normal := CFSG.pCore_normal
      refine normal_le_center_of_fixes hP hd fun y hy => ?_
      have hmem : y * d * y⁻¹ ∈ conjOrbit (CFSG.pCore 3 G) d := ⟨y, hy, rfl⟩
      rw [← hW] at hmem
      exact wSet_subset_singleton hP hI (by omega) hd L hmem
  obtain ⟨u, hu⟩ := L.exists_mem (by omega)
  have hdZ : d ∉ Subgroup.center G := by
    intro hdZ
    obtain ⟨c, hc⟩ := isConj_iff.1 (Pair.isConj hP hd hu.1)
    apply hu.2.1
    rw [← hc, Subgroup.mem_center_iff.1 hdZ c, mul_inv_cancel_right]
  have hnc : ∀ e ∈ D, e ∉ Subgroup.center G := by
    intro e he heZ
    obtain ⟨c, hc⟩ := isConj_iff.1 (Pair.isConj hP hd he)
    apply hdZ
    have hde : d = e := by
      have h1 : c * e = e * c := Subgroup.mem_center_iff.1 heZ c
      calc d = c⁻¹ * (c * d * c⁻¹) * c := by group
        _ = c⁻¹ * e * c := by rw [hc]
        _ = e := by rw [mul_assoc, ← h1, inv_mul_cancel_left]
    rwa [hde]
  set π := QuotientGroup.mk' (Subgroup.center G) with hπdef
  have hπ : ∀ g, π g = (g : G ⧸ Subgroup.center G) := fun _ => rfl
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπ1 : ∀ g, π g = 1 ↔ g ∈ Subgroup.center G := fun g => QuotientGroup.eq_one_iff g
  have hPbar : Pair (G ⧸ Subgroup.center G) (π '' D) :=
    pair_image hP π hπsurj fun e he h => hnc e he ((hπ1 e).1 h)
  have hZbar : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ :=
    Pair.center_quotient_center_eq_bot hP
  have hp2 : ∀ N : Subgroup (G ⧸ Subgroup.center G), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hN2
    have hle : N ≤ CFSG.pCore 2 (G ⧸ Subgroup.center G) := le_sSup ⟨hN, hN2⟩
    rw [pCore_quotient_center_eq_bot 2 hO2] at hle
    exact le_bot_iff.1 hle
  have hp3 : ∀ N : Subgroup (G ⧸ Subgroup.center G), N.Normal → IsPGroup 3 N → N = ⊥ := by
    intro N hN hN3
    have hle : N ≤ CFSG.pCore 3 (G ⧸ Subgroup.center G) := le_sSup ⟨hN, hN3⟩
    rw [pCore_quotient_center_eq_bot 3 hO3] at hle
    exact le_bot_iff.1 hle
  obtain ⟨hstar, hloc⟩ := star_map_center hP hnc π hπ hd
  obtain ⟨ι, -, hι⟩ := exists_localEquiv (E := D) (F := π '' D) (d := d) π
    (localGroup_inj_center (by omega) L π hπ) hstar hloc
  obtain ⟨ψ, hψ⟩ := reduced_char hPbar hZbar hp2 hp3 hI hn3 ⟨d, hd, rfl⟩ (L.transport ι hι)
  obtain ⟨Ψ, -⟩ := exists_mulEquiv_of_center_quotient hP hnc (n + 1) ψ hψ
  exact ⟨Ψ.symm⟩

theorem item73_proved : Item73 := item73_of_inFischer44 inFischer44

end CFSG.RankThree.PartOne.FIS
