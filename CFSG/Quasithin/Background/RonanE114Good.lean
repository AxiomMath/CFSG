module

public import CFSG.Quasithin.Background.RonanE114P7
public import CFSG.Quasithin.Background.RonanE114Pair

public section

namespace CFSG.Quasithin.RonanE114.Good

open CFSG.QuasithinUnique CFSG.Quasithin.B6 CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB
  CFSG.Quasithin.A1b

@[expose] def GoodPair (Γ : Type) [Group Γ] (U : Subgroup Γ) (𝒜 : Set (MulAut Γ)) : Prop :=
  ∃ P₀ P₁ : Subgroup Γ, U ≤ P₀ ∧ U ≤ P₁ ∧ Group.IsSolvable ↥P₀ ∧ P₀ ⊔ P₁ = ⊤ ∧
    (∀ α ∈ 𝒜, P₀.map α.toMonoidHom = P₀ ∧ P₁.map α.toMonoidHom = P₁) ∧
    ((∃ A B : Subgroup Γ, A ≤ P₁ ∧ B ≤ P₁ ∧ Group.IsSolvable ↥A ∧ Group.IsSolvable ↥B ∧
        A ⊔ B = P₁ ∧ ∀ α ∈ 𝒜, A.map α.toMonoidHom = A ∧ B.map α.toMonoidHom = B) ∨
      ((∀ X : Subgroup Γ, U ≤ X → X ≤ P₁ → (∀ α ∈ 𝒜, X.map α.toMonoidHom = X) → X = U ∨ X = P₁) ∧
        ∃ f : ↥P₁ →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
          Function.Surjective f ∧ IsPGroup 2 f.ker))

section Helpers

theorem isSylowIn_of_isSylowTwoOf {G : Type} [Group G] {T D : Subgroup G} (h : IsSylowTwoOf T D) :
    IsSylowIn 2 T D := ⟨h.1, h.2.1, h.2.2⟩

theorem mem_normalizer_inf' {G : Type} [Group G] {A B : Subgroup G} {s : G}
    (hA : s ∈ Subgroup.normalizer (A : Set G)) (hB : s ∈ Subgroup.normalizer (B : Set G)) :
    s ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hA x,
    Subgroup.mem_normalizer_iff.mp hB x]

variable {H : Type} [Group H] {K : Subgroup H} {Γ : Type} [Group Γ]

theorem isSolvable_pull (e : ↥K ≃* Γ) {P : Subgroup Γ} (hP : Group.IsSolvable ↥P) :
    Group.IsSolvable ↥((P.map e.symm.toMonoidHom).map K.subtype) := by
  let f : ↥P ≃* ↥((P.map e.symm.toMonoidHom).map K.subtype) :=
    (P.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      ((P.map e.symm.toMonoidHom).equivMapOfInjective K.subtype K.subtype_injective)
  exact Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective

end Helpers

section Transport

variable {Γ : Type} [Group Γ] [Finite Γ] {H : Type} [Group H] [Finite H] {K T : Subgroup H}

theorem nParam_le_one_of_goodPair
    {U : Subgroup Γ} (hU : IsSylowTwoOf U ⊤)
    (hgood : ∀ 𝒜 : Set (MulAut Γ), (∀ α ∈ 𝒜, U.map α.toMonoidHom = U) → GoodPair Γ U 𝒜)
    (hK : K.Normal) (e₀ : ↥K ≃* Γ) (hT : IsSylowTwoOf T ⊤) (hKT : K ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup H) ≤ 1 := by
  have hSK : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_normal hT le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e₀ hSK hU
  have hα : ∀ t ∈ T, U.map (autK e' t).toMonoidHom = U := fun t ht => by
    rw [← he']
    exact map_autK_of_mem_normalizer' e' inf_le_right (le_normalizer_inf hK ht)
  set 𝒜 : Set (MulAut Γ) := (fun t => autK e' t) '' (T : Set H) with h𝒜
  obtain ⟨P₀, P₁, hUP₀, hUP₁, hs₀, hgen, hinv, hcase⟩ :=
    hgood 𝒜 (by rintro _ ⟨t, ht, rfl⟩; exact hα t ht)
  have hS : ∀ {P : Subgroup Γ}, U ≤ P → T ⊓ K ≤ (P.map e'.symm.toMonoidHom).map K.subtype :=
    fun hUP => (le_pull_iff e' inf_le_right).mpr (he' ▸ hUP)
  have hn : ∀ {P : Subgroup Γ}, (∀ α ∈ 𝒜, P.map α.toMonoidHom = P) → ∀ t ∈ T,
      t ∈ Subgroup.normalizer (((P.map e'.symm.toMonoidHom).map K.subtype : Subgroup H) : Set H) :=
    fun h t ht => mem_normalizer_pull e' (h _ ⟨t, ht, rfl⟩)
  have hT' : IsSylowIn 2 T ⊤ := ⟨le_top, hT.2.1, hT.2.2⟩
  set Q₀ := (P₀.map e'.symm.toMonoidHom).map K.subtype with hQ₀
  set Q₁ := (P₁.map e'.symm.toMonoidHom).map K.subtype with hQ₁
  have hn₀ : T ≤ Subgroup.normalizer (Q₀ : Set H) := fun t ht =>
    hn (fun α hα => (hinv α hα).1) t ht
  have hn₁ : T ≤ Subgroup.normalizer (Q₁ : Set H) := fun t ht =>
    hn (fun α hα => (hinv α hα).2) t ht
  have hTQ : IsSylowTwoOf T (Q₁ ⊔ T) := B6.isSylowTwoOf_mono hT le_sup_right le_top
  have h0 : E1.nParam (Q₀ ⊔ T) ≤ 1 :=
    E1.solvable_nParam_le_one (isSolvable_sup_of_normalizes hT.2.1 hn₀ (isSolvable_pull e' hs₀))
  have h1 : E1.nParam (Q₁ ⊔ T) ≤ 1 := by
    rcases hcase with ⟨A, B, hAP, hBP, hsA, hsB, hAB, hinvAB⟩ | ⟨hlat, f, hfs, hfk⟩
    ·
      have hnA : T ≤ Subgroup.normalizer
          (((A.map e'.symm.toMonoidHom).map K.subtype : Subgroup H) : Set H) := fun t ht =>
        hn (fun α hα => (hinvAB α hα).1) t ht
      have hnB : T ≤ Subgroup.normalizer
          (((B.map e'.symm.toMonoidHom).map K.subtype : Subgroup H) : Set H) := fun t ht =>
        hn (fun α hα => (hinvAB α hα).2) t ht
      have hDA := isSolvable_sup_of_normalizes hT.2.1 hnA (isSolvable_pull e' hsA)
      have hDB := isSolvable_sup_of_normalizes hT.2.1 hnB (isSolvable_pull e' hsB)
      refine E1.nParam_le_of_generated
        (Δ := {(A.map e'.symm.toMonoidHom).map K.subtype ⊔ T,
          (B.map e'.symm.toMonoidHom).map K.subtype ⊔ T})
        (isSylowIn_of_isSylowTwoOf hTQ) ?_ ?_ ?_
      · rw [iSup_insert, iSup_singleton]
        refine le_antisymm (sup_le (sup_le ((pull_mono e' hAP).trans le_sup_left) le_sup_right)
          (sup_le ((pull_mono e' hBP).trans le_sup_left) le_sup_right)) ?_
        have hQ1 : Q₁ = (A.map e'.symm.toMonoidHom).map K.subtype ⊔
            (B.map e'.symm.toMonoidHom).map K.subtype := by
          rw [hQ₁, ← hAB, pull_sup]
        rw [hQ1]
        exact sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left))
          (le_sup_of_le_left le_sup_right)
      · intro D hD
        rcases hD with rfl | rfl <;> exact le_sup_right
      · intro D hD
        rcases hD with rfl | rfl
        · exact E1.solvable_nParam_le_one hDA
        · exact E1.solvable_nParam_le_one hDB
    ·
      let ι : ↥P₁ ≃* ↥Q₁ :=
        (P₁.equivMapOfInjective e'.symm.toMonoidHom e'.symm.injective).trans
          ((P₁.map e'.symm.toMonoidHom).equivMapOfInjective K.subtype K.subtype_injective)
      let f' : ↥Q₁ →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := f.comp ι.symm.toMonoidHom
      have hf' : Function.Surjective f' := hfs.comp ι.symm.surjective
      have hker' : IsPGroup 2 f'.ker := by
        intro x
        have hx : f (ι.symm x.1) = 1 := MonoidHom.mem_ker.mp x.2
        obtain ⟨n, hn'⟩ := hfk ⟨ι.symm x.1, MonoidHom.mem_ker.mpr hx⟩
        refine ⟨n, Subtype.ext (ι.symm.injective ?_)⟩
        have := congrArg Subtype.val hn'
        simpa using this
      refine P7.nParam_le_one_of_pgl7' hn₁ hTQ ?_ f' hf' hker'
      intro M hTM hMD
      have hYK : M ⊓ Q₁ ≤ K := inf_le_right.trans (pull_le e' P₁)
      have hnY : ∀ t ∈ T, t ∈ Subgroup.normalizer ((M ⊓ Q₁ : Subgroup H) : Set H) := fun t ht =>
        mem_normalizer_inf' (Subgroup.le_normalizer (hTM ht)) (hn₁ ht)
      have hSY : T ⊓ K ≤ M ⊓ Q₁ := le_inf (inf_le_left.trans hTM) (hS hUP₁)
      have hUX : U ≤ ((M ⊓ Q₁).subgroupOf K).map e'.toMonoidHom := by
        rw [← he']
        exact Subgroup.map_mono (Subgroup.comap_mono hSY)
      have hXP : ((M ⊓ Q₁).subgroupOf K).map e'.toMonoidHom ≤ P₁ :=
        (le_pull_iff e' hYK).mp inf_le_right
      have hinvX : ∀ α ∈ 𝒜, (((M ⊓ Q₁).subgroupOf K).map e'.toMonoidHom).map α.toMonoidHom =
          ((M ⊓ Q₁).subgroupOf K).map e'.toMonoidHom := by
        rintro _ ⟨t, ht, rfl⟩
        exact map_autK_of_mem_normalizer' e' hYK (hnY t ht)
      have hpm := pull_map e' hYK
      rcases hlat _ hUX hXP hinvX with hXU | hXP1
      ·
        left
        have hYS : M ⊓ Q₁ = T ⊓ K := by
          rw [hXU, ← he', pull_map e' inf_le_right] at hpm
          exact hpm.symm
        refine le_antisymm (fun m hm => ?_) hTM
        obtain ⟨p, hp, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hn₁ (hMD hm)
        have hpM : p ∈ M := by
          have := M.mul_mem hm (M.inv_mem (hTM ht))
          simpa using this
        have hpT : p ∈ T := (hYS ▸ (⟨hpM, hp⟩ : p ∈ M ⊓ Q₁) : p ∈ T ⊓ K).1
        exact T.mul_mem hpT ht
      ·
        right
        have hYQ : M ⊓ Q₁ = Q₁ := by
          rw [hXP1] at hpm
          exact hpm.symm
        refine le_antisymm hMD (sup_le ?_ hTM)
        rw [← hYQ]
        exact inf_le_left
  have hQ : Q₀ ⊔ Q₁ = K := by rw [hQ₀, hQ₁, ← pull_sup, hgen, pull_top]
  refine E1.nParam_le_of_generated (Δ := {Q₀ ⊔ T, Q₁ ⊔ T}) hT' ?_ ?_ ?_
  · rw [iSup_insert, iSup_singleton]
    refine eq_top_iff.mpr ?_
    rw [← hKT]
    have hK' : K ≤ (Q₀ ⊔ T) ⊔ (Q₁ ⊔ T) := by
      rw [← hQ]
      exact sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left)
    exact sup_le hK' (le_sup_of_le_left le_sup_right)
  · intro D hD
    rcases hD with rfl | rfl <;> exact le_sup_right
  · intro D hD
    rcases hD with rfl | rfl
    · exact h0
    · exact h1

end Transport

end CFSG.Quasithin.RonanE114.Good
