module

public import CFSG.RankThree.PartTwo.J2Residue.LinAlgE9
public import Mathlib.RepresentationTheory.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLineSum
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.J2Residue

section Restrict

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem mem_ker_sub_one {f : Module.End K V} {v : V} :
    v ∈ LinearMap.ker (f - 1) ↔ f v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

private theorem finrank_ker_restrict [FiniteDimensional K V] {f : V →ₗ[K] V} {W : Submodule K V}
    (hf : ∀ x ∈ W, f x ∈ W) :
    Module.finrank K ↥(LinearMap.ker ((f.restrict hf) - 1)) =
      Module.finrank K ↥(W ⊓ LinearMap.ker (f - 1)) := by
  have hf' : ∀ x ∈ W, (f - 1) x ∈ W := fun x hx => by
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact Submodule.sub_mem W (hf x hx) hx
  have hsub : (f.restrict hf) - 1 = (f - 1).restrict hf' := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.restrict_coe_apply, Module.End.one_apply,
      Submodule.coe_sub]
  rw [hsub, LinearMap.ker_restrict (hf := hf')]
  rw [← Submodule.map_comap_subtype (p := W) (p' := LinearMap.ker (f - 1))]
  exact (Submodule.equivMapOfInjective W.subtype W.subtype_injective _).finrank_eq

end Restrict

variable {K : Type*} [Field K] {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module K V]

private def fixSpace (ρ : Representation K Γ V) (T : Subgroup Γ) : Submodule K V :=
  ⨅ t : T, LinearMap.ker (ρ (t : Γ) - 1)

private theorem mem_fixSpace {ρ : Representation K Γ V} {T : Subgroup Γ} {v : V} :
    v ∈ fixSpace ρ T ↔ ∀ t ∈ T, ρ t v = v := by
  rw [fixSpace, Submodule.mem_iInf]
  constructor
  · intro h t ht
    have := h ⟨t, ht⟩
    rwa [mem_ker_sub_one] at this
  · intro h t
    rw [mem_ker_sub_one]
    exact h t t.2

private theorem fixSpace_anti {ρ : Representation K Γ V} {T₁ T₂ : Subgroup Γ} (h : T₁ ≤ T₂) :
    fixSpace ρ T₂ ≤ fixSpace ρ T₁ := by
  intro v hv
  exact mem_fixSpace.mpr (fun t ht => mem_fixSpace.mp hv t (h ht))

private theorem fixSpace_closure_pair {ρ : Representation K Γ V} {d s : Γ} (hd : ρ d = 1) :
    fixSpace ρ (Subgroup.closure ({d, s} : Set Γ)) = LinearMap.ker (ρ s - 1) := by
  refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
  · exact mem_ker_sub_one.mpr
      (mem_fixSpace.mp hv s (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  · have hv' : ρ s v = v := mem_ker_sub_one.mp hv
    rw [mem_fixSpace]
    have hd' : ρ d v = v := by rw [hd]; rfl
    let H : Subgroup Γ :=
      { carrier := {x | ρ x v = v}
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [map_mul, Module.End.mul_apply, hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          calc ρ x⁻¹ v = ρ x⁻¹ (ρ x v) := by rw [hx]
            _ = v := Representation.inv_self_apply ρ x v }
    have hle : Subgroup.closure ({d, s} : Set Γ) ≤ H := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · simpa [H] using hd'
      · simpa [H] using hv'
    exact fun t ht => hle ht

private theorem fixSpace_closure_triple {ρ : Representation K Γ V} {d s t : Γ} (hd : ρ d = 1) :
    fixSpace ρ (Subgroup.closure ({d, s, t} : Set Γ)) =
      LinearMap.ker (ρ s - 1) ⊓ LinearMap.ker (ρ t - 1) := by
  refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact mem_ker_sub_one.mpr
        (mem_fixSpace.mp hv s (Subgroup.subset_closure (by simp)))
    · exact mem_ker_sub_one.mpr
        (mem_fixSpace.mp hv t (Subgroup.subset_closure (by simp)))
  · rw [Submodule.mem_inf] at hv
    obtain ⟨hv₁, hv₂⟩ := hv
    have hv₁' : ρ s v = v := mem_ker_sub_one.mp hv₁
    have hv₂' : ρ t v = v := mem_ker_sub_one.mp hv₂
    rw [mem_fixSpace]
    have hd' : ρ d v = v := by rw [hd]; rfl
    let H : Subgroup Γ :=
      { carrier := {x | ρ x v = v}
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [map_mul, Module.End.mul_apply, hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          calc ρ x⁻¹ v = ρ x⁻¹ (ρ x v) := by rw [hx]
            _ = v := Representation.inv_self_apply ρ x v }
    have hle : Subgroup.closure ({d, s, t} : Set Γ) ≤ H := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · simpa [H] using hd'
      · simpa [H] using hv₁'
      · simpa [H] using hv₂'
    exact fun x hx => hle hx

private theorem fixSpace_map_conj_le {ρ : Representation K Γ V} {T₁ T₂ : Subgroup Γ} {n : Γ}
    (hn : T₁.map (MulAut.conj n).toMonoidHom = T₂) :
    Submodule.map (ρ n) (fixSpace ρ T₁) ≤ fixSpace ρ T₂ := by
  rintro _ ⟨v, hv, rfl⟩
  have hv' : ∀ u ∈ T₁, ρ u v = v := mem_fixSpace.mp hv
  rw [mem_fixSpace]
  intro t ht
  rw [← hn, Subgroup.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  have hconj : (MulAut.conj n).toMonoidHom u = n * u * n⁻¹ := MulAut.conj_apply n u
  simp only [hconj, map_mul, Module.End.mul_apply, Representation.inv_self_apply, hv' u hu]

private theorem finrank_fixSpace_le {ρ : Representation K Γ V} [FiniteDimensional K V]
    {T₁ T₂ : Subgroup Γ} {n : Γ} (hn : T₁.map (MulAut.conj n).toMonoidHom = T₂) :
    Module.finrank K ↥(fixSpace ρ T₁) ≤ Module.finrank K ↥(fixSpace ρ T₂) := by
  have hinj : Function.Injective (ρ n : V →ₗ[K] V) := (Representation.apply_bijective ρ n).1
  calc Module.finrank K ↥(fixSpace ρ T₁)
      = Module.finrank K ↥(Submodule.map (ρ n) (fixSpace ρ T₁)) :=
        (Submodule.equivMapOfInjective (ρ n) hinj (fixSpace ρ T₁)).finrank_eq
    _ ≤ Module.finrank K ↥(fixSpace ρ T₂) := Submodule.finrank_mono (fixSpace_map_conj_le hn)


theorem eight_le_finrank (h3 : (3 : K) ≠ 0) [FiniteDimensional K V] (ρ : Representation K Γ V)
    {S : Subgroup Γ} {d : Γ} (hdS : d ∈ S) (hd3 : orderOf d = 3) (hd : ρ d = 1)
    (hS27 : Nat.card S = 27) (hdc : S ≤ Subgroup.centralizer {d})
    (hexp : ∀ s ∈ S, s ^ 3 ∈ Subgroup.zpowers d) (hnt : ∃ s ∈ S, ρ s ≠ 1)
    (htrans : ∀ T₁ T₂ : Subgroup Γ, Subgroup.zpowers d < T₁ → T₁ < S →
      Subgroup.zpowers d < T₂ → T₂ < S →
        ∃ n ∈ Subgroup.normalizer (S : Set Γ), T₁.map (MulAut.conj n).toMonoidHom = T₂)
    (hinv : ∃ n ∈ Subgroup.normalizer (S : Set Γ),
      ∀ s ∈ S, n * s * n⁻¹ * s ∈ Subgroup.zpowers d) :
    8 ≤ Module.finrank K V := by
  classical
  set D : Subgroup Γ := Subgroup.zpowers d with hDdef
  have hdD : d ∈ D := by rw [hDdef]; exact Subgroup.mem_zpowers d
  have hDcard : Nat.card D = 3 := by rw [hDdef, Nat.card_zpowers, hd3]
  have hDS : D ≤ S := by rw [hDdef]; exact Subgroup.zpowers_le.mpr hdS
  have hDcent : D ≤ Subgroup.centralizer (S : Set Γ) := by
    rw [hDdef, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hdc hy)
  have hDcenter : D.subgroupOf S ≤ Subgroup.center S := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hDcent (Subgroup.mem_subgroupOf.mp hx)) (y : Γ) y.2)
  have hDnormal : (D.subgroupOf S).Normal := Subgroup.normal_of_le_center hDcenter
  have hDScard : Nat.card (D.subgroupOf S) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDS).toEquiv).trans hDcard
  have hQcard : Nat.card (S ⧸ (D.subgroupOf S)) = 9 := by
    have h := Subgroup.card_mul_index (D.subgroupOf S)
    rw [hDScard, hS27, Subgroup.index_eq_card] at h
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hQfin : Finite (S ⧸ (D.subgroupOf S)) :=
    Nat.finite_of_card_ne_zero (by rw [hQcard]; norm_num)
  have hQcomm : ∀ a b : S ⧸ (D.subgroupOf S), a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := S ⧸ (D.subgroupOf S))
      (by rw [hQcard]; norm_num)).is_comm.comm
  have hQexp : ∀ x : S ⧸ (D.subgroupOf S), x ^ 3 = 1 := by
    intro x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf S) x
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hexp (s : Γ) s.2)
  let φ : S →* S ⧸ (D.subgroupOf S) := QuotientGroup.mk' (D.subgroupOf S)
  have hφd : φ ⟨d, hdS⟩ = 1 := by
    show (QuotientGroup.mk' (D.subgroupOf S)) ⟨d, hdS⟩ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hdD
  have hDSne : D.subgroupOf S ≠ ⊤ := by
    intro h
    have h1 : Nat.card (D.subgroupOf S) = Nat.card (⊤ : Subgroup S) := by rw [h]
    rw [hDScard, Subgroup.card_top, hS27] at h1
    omega
  obtain ⟨σ₁, hσ₁⟩ : ∃ x : S, x ∉ D.subgroupOf S := by
    by_contra h
    push Not at h
    exact hDSne (le_antisymm le_top (fun x _ => h x))
  have hq1 : φ σ₁ ≠ 1 := fun h => hσ₁ ((QuotientGroup.eq_one_iff σ₁).mp h)
  have hq1ord : orderOf (φ σ₁) = 3 := orderOf_eq_prime (hQexp (φ σ₁)) hq1
  have hcycne : Subgroup.zpowers (φ σ₁) ≠ ⊤ := by
    intro h
    have h1 : Nat.card (Subgroup.zpowers (φ σ₁)) =
        Nat.card (⊤ : Subgroup (S ⧸ (D.subgroupOf S))) := by rw [h]
    rw [Nat.card_zpowers, hq1ord, Subgroup.card_top, hQcard] at h1
    omega
  obtain ⟨q₂, hq₂⟩ : ∃ x : S ⧸ (D.subgroupOf S), x ∉ Subgroup.zpowers (φ σ₁) := by
    by_contra h
    push Not at h
    exact hcycne (le_antisymm le_top (fun x _ => h x))
  obtain ⟨σ₂, hσ₂⟩ := QuotientGroup.mk'_surjective (D.subgroupOf S) q₂
  rw [← hσ₂] at hq₂
  have hclosure1 : ∀ a b : S ⧸ (D.subgroupOf S),
      Subgroup.closure ({1, a, b} : Set (S ⧸ (D.subgroupOf S))) =
        Subgroup.closure ({a, b} : Set (S ⧸ (D.subgroupOf S))) := by
    intro a b
    refine le_antisymm ?_ (Subgroup.closure_mono (by intro x hx; simp_all))
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hQtop : Subgroup.closure ({φ σ₁, φ σ₂} : Set (S ⧸ (D.subgroupOf S))) = ⊤ := by
    have hlt : Subgroup.zpowers (φ σ₁) < Subgroup.closure ({φ σ₁, φ σ₂} : Set _) := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) ?_
      intro heq
      refine hq₂ (heq ▸ Subgroup.subset_closure ?_)
      exact Or.inr rfl
    have hgt : 3 < Nat.card (Subgroup.closure ({φ σ₁, φ σ₂} : Set _)) := by
      have := Subgroup.card_lt_of_lt hlt
      rwa [Nat.card_zpowers, hq1ord] at this
    have hdvd : Nat.card (Subgroup.closure ({φ σ₁, φ σ₂} : Set _)) ∣ 9 := by
      have h := Subgroup.card_mul_index (Subgroup.closure ({φ σ₁, φ σ₂} : Set _))
      rw [hQcard] at h
      exact ⟨_, h.symm⟩
    have hle9 : Nat.card (Subgroup.closure ({φ σ₁, φ σ₂} : Set _)) ≤ 9 := by
      have h := Subgroup.card_le_of_le (H := Subgroup.closure ({φ σ₁, φ σ₂} : Set _)) le_top
      rw [Subgroup.card_top, hQcard] at h
      exact h
    have hcard : Nat.card (Subgroup.closure ({φ σ₁, φ σ₂} : Set _)) = 9 := by
      obtain ⟨m, hm⟩ : ∃ m, Nat.card (Subgroup.closure ({φ σ₁, φ σ₂} : Set _)) = m := ⟨_, rfl⟩
      rw [hm] at hdvd hgt hle9
      have hm9 : m = 9 := by
        interval_cases m <;> simp_all
      rw [hm9] at hm
      exact hm
    exact Subgroup.eq_top_of_card_eq _ (by rw [hcard, hQcard])
  set P : Subgroup S := Subgroup.closure ({⟨d, hdS⟩, σ₁, σ₂} : Set S) with hPdef
  have hPd : (⟨d, hdS⟩ : S) ∈ P := Subgroup.subset_closure (by simp)
  have hPσ1 : σ₁ ∈ P := Subgroup.subset_closure (by simp)
  have hPσ2 : σ₂ ∈ P := Subgroup.subset_closure (by simp)
  have hDsub_le : D.subgroupOf S ≤ P := by
    intro x hx
    have hxD : (x : Γ) ∈ Subgroup.zpowers d := by
      rw [← hDdef]; exact Subgroup.mem_subgroupOf.mp hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxD
    have hx' : x = (⟨d, hdS⟩ : S) ^ k := Subtype.ext hk.symm
    rw [hx']
    exact P.zpow_mem hPd k
  have hmapP : Subgroup.map φ P = ⊤ := by
    rw [hPdef, MonoidHom.map_closure]
    have himg : φ '' ({⟨d, hdS⟩, σ₁, σ₂} : Set S) = {1, φ σ₁, φ σ₂} := by
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, (rfl | rfl | rfl), rfl⟩
        · exact Or.inl hφd
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact ⟨_, Or.inl rfl, hφd⟩
        · exact ⟨σ₁, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨σ₂, Or.inr (Or.inr rfl), rfl⟩
    rw [himg, hclosure1, hQtop]
  have hPtop : P = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ Subgroup.map φ P := by rw [hmapP]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hmem : y⁻¹ * x ∈ D.subgroupOf S := by
      rw [← QuotientGroup.eq_one_iff]
      show φ (y⁻¹ * x) = 1
      rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have hyx' : x = y * (y⁻¹ * x) := by group
    rw [hyx']
    exact P.mul_mem hy (hDsub_le hmem)
  have hSgen : S = Subgroup.closure ({d, (σ₁ : Γ), (σ₂ : Γ)} : Set Γ) := by
    have hmap : (⊤ : Subgroup S).map S.subtype = S := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h1 : P.map S.subtype = S := by rw [hPtop]; exact hmap
    have h2 : P.map S.subtype = Subgroup.closure ({d, (σ₁ : Γ), (σ₂ : Γ)} : Set Γ) := by
      rw [hPdef, MonoidHom.map_closure]
      congr 1
      ext x
      simp
    exact h1.symm.trans h2

  set P₁ : Subgroup S := Subgroup.closure ({⟨d, hdS⟩, σ₁} : Set S) with hP₁def
  set T₁ : Subgroup Γ := P₁.map S.subtype with hT₁def
  set P₂ : Subgroup S := Subgroup.closure ({⟨d, hdS⟩, σ₂} : Set S) with hP₂def
  set T₂ : Subgroup Γ := P₂.map S.subtype with hT₂def
  set P₃ : Subgroup S := Subgroup.closure ({⟨d, hdS⟩, σ₁ * σ₂} : Set S) with hP₃def
  set T₃ : Subgroup Γ := P₃.map S.subtype with hT₃def
  set P₄ : Subgroup S := Subgroup.closure ({⟨d, hdS⟩, σ₁ ^ 2 * σ₂} : Set S) with hP₄def
  set T₄ : Subgroup Γ := P₄.map S.subtype with hT₄def
  have himg : ∀ x : S, S.subtype '' ({⟨d, hdS⟩, x} : Set S) = ({d, (x : Γ)} : Set Γ) := by
    intro x
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · rw [h]; exact ⟨⟨d, hdS⟩, Or.inl rfl, rfl⟩
      · rw [h]; exact ⟨x, Or.inr rfl, rfl⟩
  have hT1eq : T₁ = Subgroup.closure ({d, (σ₁ : Γ)} : Set Γ) := by
    rw [hT₁def, hP₁def, MonoidHom.map_closure, himg]
  have hT2eq : T₂ = Subgroup.closure ({d, (σ₂ : Γ)} : Set Γ) := by
    rw [hT₂def, hP₂def, MonoidHom.map_closure, himg]
  have hT3eq : T₃ = Subgroup.closure ({d, ((σ₁ * σ₂ : S) : Γ)} : Set Γ) := by
    rw [hT₃def, hP₃def, MonoidHom.map_closure, himg]
  have hT4eq : T₄ = Subgroup.closure ({d, ((σ₁ ^ 2 * σ₂ : S) : Γ)} : Set Γ) := by
    rw [hT₄def, hP₄def, MonoidHom.map_closure, himg]
  have hT1S : T₁ ≤ S := by rw [hT₁def]; exact Subgroup.map_subtype_le P₁
  have hT2S : T₂ ≤ S := by rw [hT₂def]; exact Subgroup.map_subtype_le P₂
  have hT3S : T₃ ≤ S := by rw [hT₃def]; exact Subgroup.map_subtype_le P₃
  have hT4S : T₄ ≤ S := by rw [hT₄def]; exact Subgroup.map_subtype_le P₄
  have hmap_pair : ∀ x : S, Subgroup.map φ (Subgroup.closure ({⟨d, hdS⟩, x} : Set S)) =
      Subgroup.zpowers (φ x) := by
    intro x
    rw [MonoidHom.map_closure]
    have hx : φ '' ({⟨d, hdS⟩, x} : Set S) = ({1, φ x} : Set (S ⧸ (D.subgroupOf S))) := by
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with rfl | rfl
        · exact Or.inl hφd
        · exact Or.inr rfl
      · rintro (h | h)
        · rw [h]; exact ⟨⟨d, hdS⟩, Or.inl rfl, hφd⟩
        · rw [h]; exact ⟨x, Or.inr rfl, rfl⟩
    have h1 : Subgroup.closure ({1, φ x} : Set (S ⧸ (D.subgroupOf S))) =
        Subgroup.zpowers (φ x) := by
      rw [Subgroup.zpowers_eq_closure]
      refine le_antisymm ?_ (Subgroup.closure_mono (by intro y hy; simp_all))
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
    rw [hx, h1]
  have hmap_top : Subgroup.map φ (⊤ : Subgroup S) = ⊤ :=
    Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective (D.subgroupOf S))
  have hlt_s_of_map : ∀ (Q : Subgroup S) (y : S ⧸ (D.subgroupOf S)),
      Subgroup.map φ Q = Subgroup.zpowers y → y ^ 3 = 1 → y ≠ 1 → Q.map S.subtype < S := by
    intro Q y hQy hy3 hy1
    refine lt_of_le_of_ne (Subgroup.map_subtype_le Q) ?_
    intro heq
    have hQtop : Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hmem : (x : Γ) ∈ Q.map S.subtype := by rw [heq]; exact x.2
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hmem
      rwa [← Subtype.ext hzx]
    have hmapQ : Subgroup.map φ Q = ⊤ := by rw [hQtop]; exact hmap_top
    have hcard : Nat.card (Subgroup.zpowers y) = 9 := by
      rw [← hQy, hmapQ, Subgroup.card_top, hQcard]
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1] at hcard
    omega
  have hnotD : ∀ x : S, φ x ≠ 1 → (x : Γ) ∉ D := by
    intro x hx hxD
    apply hx
    show (QuotientGroup.mk' (D.subgroupOf S)) x = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hxD
  have hq2ne : φ σ₂ ≠ 1 := fun h => hq₂ (h ▸ Subgroup.one_mem _)
  have hq3ne : φ (σ₁ * σ₂) ≠ 1 := by
    intro h
    apply hq₂
    have h' : φ σ₁ * φ σ₂ = 1 := by
      rw [← map_mul]; exact h
    have h2 : φ σ₂ = (φ σ₁)⁻¹ := eq_inv_of_mul_eq_one_right h'
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hq4ne : φ (σ₁ ^ 2 * σ₂) ≠ 1 := by
    intro h
    apply hq₂
    have h' : (φ σ₁) ^ 2 * φ σ₂ = 1 := by
      rw [← map_pow, ← map_mul]; exact h
    have h2 : φ σ₂ = ((φ σ₁) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h'
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2)
  have hT1lt : T₁ < S := by
    rw [hT₁def]
    exact hlt_s_of_map P₁ (φ σ₁) (hmap_pair σ₁) (hQexp _) hq1
  have hT2lt : T₂ < S := by
    rw [hT₂def]
    exact hlt_s_of_map P₂ (φ σ₂) (hmap_pair σ₂) (hQexp _) hq2ne
  have hT3lt : T₃ < S := by
    rw [hT₃def]
    exact hlt_s_of_map P₃ (φ (σ₁ * σ₂)) (hmap_pair (σ₁ * σ₂)) (hQexp _) hq3ne
  have hT4lt : T₄ < S := by
    rw [hT₄def]
    exact hlt_s_of_map P₄ (φ (σ₁ ^ 2 * σ₂)) (hmap_pair (σ₁ ^ 2 * σ₂)) (hQexp _) hq4ne
  have hdP : ∀ Q : Subgroup S, (⟨d, hdS⟩ : S) ∈ Q → D ≤ Q.map S.subtype := by
    intro Q hQ
    rw [hDdef, Subgroup.zpowers_le]
    exact Subgroup.mem_map_of_mem S.subtype hQ
  have hDlt : ∀ (Q : Subgroup S), (⟨d, hdS⟩ : S) ∈ Q → (∃ x ∈ Q, (x : Γ) ∉ D) →
      D < Q.map S.subtype := by
    intro Q hQ ⟨x, hxQ, hxD⟩
    refine lt_of_le_of_ne (hdP Q hQ) ?_
    intro heq
    exact hxD (heq ▸ Subgroup.mem_map_of_mem S.subtype hxQ)
  have hDP1 : (⟨d, hdS⟩ : S) ∈ P₁ := Subgroup.subset_closure (by simp)
  have hDP2 : (⟨d, hdS⟩ : S) ∈ P₂ := Subgroup.subset_closure (by simp)
  have hDP3 : (⟨d, hdS⟩ : S) ∈ P₃ := Subgroup.subset_closure (by simp)
  have hDP4 : (⟨d, hdS⟩ : S) ∈ P₄ := Subgroup.subset_closure (by simp)
  have hDT1 : D < T₁ := by
    rw [hT₁def]
    exact hDlt P₁ hDP1 ⟨σ₁, Subgroup.subset_closure (by simp), hnotD σ₁ hq1⟩
  have hDT2 : D < T₂ := by
    rw [hT₂def]
    exact hDlt P₂ hDP2 ⟨σ₂, Subgroup.subset_closure (by simp), hnotD σ₂ hq2ne⟩
  have hDT3 : D < T₃ := by
    rw [hT₃def]
    exact hDlt P₃ hDP3 ⟨σ₁ * σ₂, Subgroup.subset_closure (by simp), hnotD _ hq3ne⟩
  have hDT4 : D < T₄ := by
    rw [hT₄def]
    exact hDlt P₄ hDP4 ⟨σ₁ ^ 2 * σ₂, Subgroup.subset_closure (by simp), hnotD _ hq4ne⟩
  have hfix₁ : fixSpace ρ T₁ = LinearMap.ker (ρ (σ₁ : Γ) - 1) := by
    rw [hT1eq, fixSpace_closure_pair hd]
  have hfix₂ : fixSpace ρ T₂ = LinearMap.ker (ρ (σ₂ : Γ) - 1) := by
    rw [hT2eq, fixSpace_closure_pair hd]
  have hfix₃ : fixSpace ρ T₃ = LinearMap.ker (ρ ((σ₁ * σ₂ : S) : Γ) - 1) := by
    rw [hT3eq, fixSpace_closure_pair hd]
  have hfix₄ : fixSpace ρ T₄ = LinearMap.ker (ρ ((σ₁ ^ 2 * σ₂ : S) : Γ) - 1) := by
    rw [hT4eq, fixSpace_closure_pair hd]
  have hfixS : fixSpace ρ S =
      LinearMap.ker (ρ (σ₁ : Γ) - 1) ⊓ LinearMap.ker (ρ (σ₂ : Γ) - 1) :=
    (congrArg (fixSpace ρ) hSgen).trans (fixSpace_closure_triple hd)
  set a : Module.End K V := ρ (σ₁ : Γ) with hadef
  set b : Module.End K V := ρ (σ₂ : Γ) with hbdef
  have hDker : D ≤ MonoidHom.ker ρ := by
    rw [hDdef, Subgroup.zpowers_le, MonoidHom.mem_ker]
    exact hd
  have hρD : ∀ x ∈ D, ρ x = 1 := fun x hx => MonoidHom.mem_ker.mpr (hDker hx)
  have hcube : ∀ x : S, ρ ((x : Γ) ^ 3) = 1 :=
    fun x => hρD _ (by rw [hDdef]; exact hexp (x : Γ) x.2)
  have ha3 : a ^ 3 = 1 := by rw [hadef, ← map_pow]; exact hcube σ₁
  have hb3 : b ^ 3 = 1 := by rw [hbdef, ← map_pow]; exact hcube σ₂
  have hcomm : Commute a b := by
    show a * b = b * a
    have hq : φ (σ₁ * σ₂ * (σ₂ * σ₁)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hQcomm (φ σ₁) (φ σ₂), mul_inv_cancel]
    have hmem : (σ₁ * σ₂ * (σ₂ * σ₁)⁻¹ : S) ∈ D.subgroupOf S := by
      have hq' : ((σ₁ * σ₂ * (σ₂ * σ₁)⁻¹ : S) : S ⧸ (D.subgroupOf S)) = 1 := hq
      exact (QuotientGroup.eq_one_iff _).mp hq'
    have hmemD : (((σ₁ * σ₂ * (σ₂ * σ₁)⁻¹ : S)) : Γ) ∈ D :=
      Subgroup.mem_subgroupOf.mp hmem
    have hρ : ρ (((σ₁ * σ₂ * (σ₂ * σ₁)⁻¹ : S)) : Γ) = 1 := hρD _ hmemD
    have h12 : ρ ((σ₁ * σ₂ : S) : Γ) = ρ ((σ₂ * σ₁ : S) : Γ) := by
      have hsplit : ρ ((σ₁ * σ₂ : S) : Γ) =
          ρ ((σ₁ * σ₂ * (σ₂ * σ₁)⁻¹ : S) : Γ) * ρ ((σ₂ * σ₁ : S) : Γ) := by
        rw [← map_mul]
        congr 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hsplit, hρ, one_mul]
    rw [hadef, hbdef]
    simpa [Subgroup.coe_mul, map_mul] using h12
  have hc₂ : Module.finrank K ↥(fixSpace ρ T₂) = Module.finrank K ↥(fixSpace ρ T₁) := by
    refine le_antisymm ?_ ?_
    · obtain ⟨m, -, hm⟩ := htrans T₂ T₁ hDT2 hT2lt hDT1 hT1lt
      exact finrank_fixSpace_le hm
    · obtain ⟨m, -, hm⟩ := htrans T₁ T₂ hDT1 hT1lt hDT2 hT2lt
      exact finrank_fixSpace_le hm
  have hc₃ : Module.finrank K ↥(fixSpace ρ T₃) = Module.finrank K ↥(fixSpace ρ T₁) := by
    refine le_antisymm ?_ ?_
    · obtain ⟨m, -, hm⟩ := htrans T₃ T₁ hDT3 hT3lt hDT1 hT1lt
      exact finrank_fixSpace_le hm
    · obtain ⟨m, -, hm⟩ := htrans T₁ T₃ hDT1 hT1lt hDT3 hT3lt
      exact finrank_fixSpace_le hm
  have hc₄ : Module.finrank K ↥(fixSpace ρ T₄) = Module.finrank K ↥(fixSpace ρ T₁) := by
    refine le_antisymm ?_ ?_
    · obtain ⟨m, -, hm⟩ := htrans T₄ T₁ hDT4 hT4lt hDT1 hT1lt
      exact finrank_fixSpace_le hm
    · obtain ⟨m, -, hm⟩ := htrans T₁ T₄ hDT1 hT1lt hDT4 hT4lt
      exact finrank_fixSpace_le hm
  have hker1 : LinearMap.ker (a - 1) = fixSpace ρ T₁ := by
    simp only [hadef]; exact hfix₁.symm
  have hker2 : LinearMap.ker (b - 1) = fixSpace ρ T₂ := by
    simp only [hbdef]; exact hfix₂.symm
  have hab : a * b = ρ ((σ₁ * σ₂ : S) : Γ) := by
    rw [hadef, hbdef]
    simp [Subgroup.coe_mul, map_mul]
  have ha2b : a ^ 2 * b = ρ ((σ₁ ^ 2 * σ₂ : S) : Γ) := by
    rw [hadef, hbdef]
    simp [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow]
  have hker3 : LinearMap.ker (a * b - 1) = fixSpace ρ T₃ := by
    rw [hab, ← hfix₃]
  have hker4 : LinearMap.ker (a ^ 2 * b - 1) = fixSpace ρ T₄ := by
    rw [ha2b, ← hfix₄]
  have hkerS : LinearMap.ker (a - 1) ⊓ LinearMap.ker (b - 1) = fixSpace ρ S := by
    simp only [hadef, hbdef]
    exact hfixS.symm
  have hsum := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.finrank_lineSum
    (K := K) (V := V) h3 ha3 hb3 hcomm
  rw [hkerS] at hsum
  rw [hker1, hker2, hker3, hker4] at hsum
  rw [hc₂, hc₃, hc₄] at hsum
  have hle : Module.finrank K ↥(fixSpace ρ S) ≤ Module.finrank K ↥(fixSpace ρ T₁) :=
    Submodule.finrank_mono (fixSpace_anti hT1S)
  have hne : Module.finrank K ↥(fixSpace ρ T₁) ≠ Module.finrank K ↥(fixSpace ρ S) := by
    intro hcc
    have hV : Module.finrank K V = Module.finrank K ↥(fixSpace ρ S) := by omega
    have htop : fixSpace ρ S = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [hV]
    obtain ⟨s, hs, hns⟩ := hnt
    apply hns
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ fixSpace ρ S := by rw [htop]; exact Submodule.mem_top
    simpa using mem_fixSpace.mp hv s hs
  obtain ⟨n, hnnorm, hninv⟩ := hinv
  have hninv_mul : ρ (n⁻¹) * ρ n = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hnmul_inv : ρ n * ρ (n⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have ha_mul : a * ρ ((σ₁⁻¹ : S) : Γ) = 1 := by
    rw [hadef, ← map_mul]
    simp
  have hb_mul : b * ρ ((σ₂⁻¹ : S) : Γ) = 1 := by
    rw [hbdef, ← map_mul]
    simp
  have hconj₁ : ρ n * a * ρ (n⁻¹) = ρ ((σ₁⁻¹ : S) : Γ) := by
    have hρ : ρ (n * (σ₁ : Γ) * n⁻¹ * (σ₁ : Γ)) = 1 :=
      hρD _ (by rw [hDdef]; exact hninv (σ₁ : Γ) σ₁.2)
    have hL : ρ n * a * ρ (n⁻¹) * a = 1 := by
      rw [hadef]
      have hL2 : ρ n * ρ (σ₁ : Γ) * ρ (n⁻¹) * ρ (σ₁ : Γ) =
          ρ (n * (σ₁ : Γ) * n⁻¹ * (σ₁ : Γ)) := by
        simp only [map_mul]
      rw [hL2, hρ]
    calc ρ n * a * ρ (n⁻¹) = ρ n * a * ρ (n⁻¹) * (a * ρ ((σ₁⁻¹ : S) : Γ)) := by
          rw [ha_mul, mul_one]
      _ = (ρ n * a * ρ (n⁻¹) * a) * ρ ((σ₁⁻¹ : S) : Γ) := by rw [← mul_assoc]
      _ = ρ ((σ₁⁻¹ : S) : Γ) := by rw [hL, one_mul]
  have hconj₂ : ρ n * b * ρ (n⁻¹) = ρ ((σ₂⁻¹ : S) : Γ) := by
    have hρ : ρ (n * (σ₂ : Γ) * n⁻¹ * (σ₂ : Γ)) = 1 :=
      hρD _ (by rw [hDdef]; exact hninv (σ₂ : Γ) σ₂.2)
    have hL : ρ n * b * ρ (n⁻¹) * b = 1 := by
      rw [hbdef]
      have hL2 : ρ n * ρ (σ₂ : Γ) * ρ (n⁻¹) * ρ (σ₂ : Γ) =
          ρ (n * (σ₂ : Γ) * n⁻¹ * (σ₂ : Γ)) := by
        simp only [map_mul]
      rw [hL2, hρ]
    calc ρ n * b * ρ (n⁻¹) = ρ n * b * ρ (n⁻¹) * (b * ρ ((σ₂⁻¹ : S) : Γ)) := by
          rw [hb_mul, mul_one]
      _ = (ρ n * b * ρ (n⁻¹) * b) * ρ ((σ₂⁻¹ : S) : Γ) := by rw [← mul_assoc]
      _ = ρ ((σ₂⁻¹ : S) : Γ) := by rw [hL, one_mul]
  have hb3' : b * b = ρ ((σ₂⁻¹ : S) : Γ) := by
    have hbb : b * b * b = 1 := by
      simpa [pow_succ, pow_two] using hb3
    calc b * b = b * b * (b * ρ ((σ₂⁻¹ : S) : Γ)) := by rw [hb_mul, mul_one]
      _ = (b * b * b) * ρ ((σ₂⁻¹ : S) : Γ) := by rw [← mul_assoc]
      _ = ρ ((σ₂⁻¹ : S) : Γ) := by rw [hbb, one_mul]
  have hbV : ∀ x ∈ LinearMap.ker (a - 1), b x ∈ LinearMap.ker (a - 1) := by
    intro x hx
    rw [mem_ker_sub_one] at hx ⊢
    have h1 : a * b = b * a := hcomm.eq
    calc a (b x) = (a * b) x := (Module.End.mul_apply a b x).symm
      _ = (b * a) x := by rw [h1]
      _ = b (a x) := Module.End.mul_apply b a x
      _ = b x := by rw [hx]
  have hnV : ∀ x ∈ LinearMap.ker (a - 1), ρ n x ∈ LinearMap.ker (a - 1) := by
    intro x hx
    rw [mem_ker_sub_one] at hx ⊢
    have h1 : ρ n * a = ρ ((σ₁⁻¹ : S) : Γ) * ρ n := by
      have h := congrArg (fun f : Module.End K V => f * ρ n) hconj₁
      simpa [mul_assoc, hninv_mul] using h
    have h2 : ρ n (a x) = ρ ((σ₁⁻¹ : S) : Γ) (ρ n x) := by
      have h := congrArg (fun f : Module.End K V => f x) h1
      simpa [Module.End.mul_apply] using h
    rw [hx] at h2
    calc a (ρ n x) = a (ρ ((σ₁⁻¹ : S) : Γ) (ρ n x)) := congrArg a h2
      _ = (a * ρ ((σ₁⁻¹ : S) : Γ)) (ρ n x) := (Module.End.mul_apply a _ _).symm
      _ = ρ n x := by rw [ha_mul, Module.End.one_apply]
  set g : (LinearMap.ker (a - 1)) →ₗ[K] (LinearMap.ker (a - 1)) := b.restrict hbV with hgdef
  set hn : (LinearMap.ker (a - 1)) →ₗ[K] (LinearMap.ker (a - 1)) :=
    (ρ n).restrict hnV with hhdef
  have hb3fun : ∀ v : V, b (b (b v)) = v := by
    intro v
    have h := congrArg (fun f : Module.End K V => f v) hb3
    simpa [pow_succ, pow_two, Module.End.mul_apply] using h
  have hgg : g * g * g = 1 := by
    rw [hgdef]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show b (b (b (x : V))) = (x : V)
    exact hb3fun (x : V)
  have hhg : hn * g = g * g * hn := by
    rw [hgdef, hhdef]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show ρ n (b (x : V)) = b (b (ρ n (x : V)))
    have h1 : ρ n * b = ρ ((σ₂⁻¹ : S) : Γ) * ρ n := by
      have h := congrArg (fun f : Module.End K V => f * ρ n) hconj₂
      simpa [mul_assoc, hninv_mul] using h
    have h2 : ρ n (b (x : V)) = ρ ((σ₂⁻¹ : S) : Γ) (ρ n (x : V)) := by
      have h := congrArg (fun f : Module.End K V => f (x : V)) h1
      simpa [Module.End.mul_apply] using h
    rw [h2, ← hb3', Module.End.mul_apply]
  have hhu : IsUnit hn := by
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : (x : V) = 0 := by
      have h1 : ρ n (x : V) = 0 := by
        have h := congrArg Subtype.val hx
        simpa [hhdef, LinearMap.restrict_coe_apply] using h
      calc (x : V) = ρ (n⁻¹) (ρ n (x : V)) := (Representation.inv_self_apply ρ n (x : V)).symm
        _ = ρ (n⁻¹) 0 := by rw [h1]
        _ = 0 := map_zero _
    exact Subtype.ext hx'
  have key : Module.finrank K ↥(LinearMap.ker (a - 1)) ≠
      Module.finrank K ↥(LinearMap.ker (g - 1)) + 1 :=
    finrank_ne_finrank_ker_add_one (V := ↥(LinearMap.ker (a - 1))) h3 hgg hhg hhu
  have hbridge : Module.finrank K ↥(LinearMap.ker (g - 1)) =
      Module.finrank K ↥(fixSpace ρ S) := by
    have h := finrank_ker_restrict (f := b) (W := LinearMap.ker (a - 1)) hbV
    rw [hkerS] at h
    simpa [hgdef] using h
  have hc_eq : Module.finrank K ↥(LinearMap.ker (a - 1)) =
      Module.finrank K ↥(fixSpace ρ T₁) := by
    rw [hker1]
  have hne1 : Module.finrank K ↥(fixSpace ρ T₁) ≠
      Module.finrank K ↥(fixSpace ρ S) + 1 := by
    intro hcc
    exact key (by rw [hc_eq, hcc, hbridge])
  omega

end CFSG.RankThree.PartTwo.J2Residue
