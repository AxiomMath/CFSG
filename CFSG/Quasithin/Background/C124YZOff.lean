module

public import CFSG.Quasithin.Background.C124YZBase
public import CFSG.Quasithin.Background.C124YZModel

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

section Offender

variable {W : Type*} [CommGroup W] [Finite W] {Q : Type*} [Group Q] {m : ℕ}
  {act : Perm (Fin m) →* MulAut Q} {Xs : Subgroup (MulAut W)} {U : Subgroup W}
  {ι : ↥Xs →* Perm (Fin m)} {β : ↥U →* Q}

theorem fixV_le_comap (hU : ∀ g ∈ Xs, ∀ u ∈ U, g u ∈ U)
    (hβe : ∀ (g : ↥Xs) (u : ↥U) (hu : (g : MulAut W) (u : W) ∈ U),
      β ⟨(g : MulAut W) (u : W), hu⟩ = act (ι g) (β u))
    {A : Subgroup (MulAut W)} (u : ↥U) (hu : (u : W) ∈ fixV A) :
    β u ∈ fixAct act (Bmap ι A) := by
  intro b hb
  obtain ⟨g, hgA, rfl⟩ := mem_Bmap.1 hb
  have := hβe g u (hU (g : MulAut W) g.2 (u : W) u.2)
  rw [← this]
  congr 1
  exact Subtype.ext (hu g hgA)

theorem index_fixAct_le (hU : ∀ g ∈ Xs, ∀ u ∈ U, g u ∈ U)
    (hβs : Function.Surjective β)
    (hβe : ∀ (g : ↥Xs) (u : ↥U) (hu : (g : MulAut W) (u : W) ∈ U),
      β ⟨(g : MulAut W) (u : W), hu⟩ = act (ι g) (β u))
    {A : Subgroup (MulAut W)} (hoff : Nat.card U ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U)) :
    (fixAct act (Bmap ι A)).index ≤ Nat.card A := by
  set F : Subgroup ↥U := (fixAct act (Bmap ι A)).comap β with hF
  set CU : Subgroup ↥U := (fixV A).subgroupOf U with hCU
  have hCF : CU ≤ F := fun v hv => fixV_le_comap hU hβe v hv
  have hFi : F.index = (fixAct act (Bmap ι A)).index :=
    Subgroup.index_comap_of_surjective _ hβs
  have hCi : CU.index ≤ Nat.card A := by
    have h1 := Subgroup.relIndex_mul_card (fixV A) U
    have h2 : CU.index * Nat.card ↥(fixV A ⊓ U) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U) :=
      h1.trans_le hoff
    exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  have hFC : F.index ≤ CU.index := Subgroup.index_antitone hCF
  omega

theorem mem_fixV_iff_of_offender (hU : ∀ g ∈ Xs, ∀ u ∈ U, g u ∈ U)
    (hβs : Function.Surjective β)
    (hβe : ∀ (g : ↥Xs) (u : ↥U) (hu : (g : MulAut W) (u : W) ∈ U),
      β ⟨(g : MulAut W) (u : W), hu⟩ = act (ι g) (β u))
    {A : Subgroup (MulAut W)} (hoff : Nat.card U ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U))
    (hge : Nat.card A ≤ (fixAct act (Bmap ι A)).index) (u : ↥U) :
    (u : W) ∈ fixV A ↔ β u ∈ fixAct act (Bmap ι A) := by
  refine ⟨fixV_le_comap hU hβe u, fun hu => ?_⟩
  set F : Subgroup ↥U := (fixAct act (Bmap ι A)).comap β with hF
  set CU : Subgroup ↥U := (fixV A).subgroupOf U with hCU
  have hCF : CU ≤ F := fun v hv => fixV_le_comap hU hβe v hv
  have hFi : F.index = (fixAct act (Bmap ι A)).index :=
    Subgroup.index_comap_of_surjective _ hβs
  have hCi : CU.index ≤ Nat.card A := by
    have h1 := Subgroup.relIndex_mul_card (fixV A) U
    have h2 : CU.index * Nat.card ↥(fixV A ⊓ U) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U) :=
      h1.trans_le hoff
    exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  have heq : CU = F := by
    by_contra hne
    have := Subgroup.index_strictAnti (lt_of_le_of_ne hCF hne)
    omega
  have h3 : u ∈ F := hu
  rw [← heq] at h3
  exact h3

end Offender

section Images

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem autI_normalizes {H K : Subgroup G} (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    autI hV H ≤ Subgroup.normalizer (autI hV K : Set (MulAut (IntMod V hV))) := by
  intro φ hφ
  obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hφ
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, hkK, rfl⟩ := (mem_autI hV).1 hn
  refine (mem_autI hV).2 ⟨g * k * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.1 (hK hgH) (k : G)).1 hkK
  simpa using this

theorem isPGroup_autI {R : Subgroup G} (hR : IsPGroup 2 R) : IsPGroup 2 (autI hV R) := by
  intro x
  obtain ⟨g, hg, hx⟩ := (mem_autI hV).1 x.2
  obtain ⟨k, hk⟩ := hR ⟨(g : G), hg⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (g : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : convI hV g ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : g ^ 2 ^ k = 1 := Subtype.ext h1
    rw [this, map_one]
  show (x : MulAut (IntMod V hV)) ^ 2 ^ k = 1
  rw [← hx]
  exact h2

end Images

section BmapFacts

variable {W : Type*} [CommGroup W] {m : ℕ} {Xs : Subgroup (MulAut W)}

theorem Bmap_isPGroup {ι : ↥Xs →* Perm (Fin m)} {A P : Subgroup (MulAut W)} (hAP : A ≤ P)
    (hP : IsPGroup 2 P) : IsPGroup 2 (Bmap ι A) := by
  intro x
  obtain ⟨g, hgA, hx⟩ := mem_Bmap.1 x.2
  obtain ⟨k, hk⟩ := hP ⟨(g : MulAut W), hAP hgA⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (g : MulAut W) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : g ^ 2 ^ k = 1 := Subtype.ext h1
  show (x : Perm (Fin m)) ^ 2 ^ k = 1
  rw [← hx, ← map_pow, h2, map_one]

theorem Bmap_elemAbelian {ι : ↥Xs →* Perm (Fin m)} {A : Subgroup (MulAut W)}
    (h : IsElemAbelian2 A) :
    (∀ b ∈ Bmap ι A, b * b = 1) ∧ ∀ a ∈ Bmap ι A, ∀ b ∈ Bmap ι A, a * b = b * a := by
  refine ⟨fun b hb => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨g, hgA, rfl⟩ := mem_Bmap.1 hb
    rw [← map_mul]
    have : g * g = 1 := Subtype.ext (by simpa [pow_two] using h.2 g hgA)
    rw [this, map_one]
  · obtain ⟨g, hg, rfl⟩ := mem_Bmap.1 ha
    obtain ⟨g', hg', rfl⟩ := mem_Bmap.1 hb
    rw [← map_mul, ← map_mul]
    exact congrArg ι (Subtype.ext (h.1 g hg g' hg'))

end BmapFacts

end CFSG.Quasithin.C124.YZ
