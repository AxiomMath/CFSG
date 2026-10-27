module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210g

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A K W R : Subgroup Γ}

theorem eq_one_of_mem_inf
    (h : SemisimpleAction p A K) (hWK : W ≤ K) (hRK : R ≤ K)
    (hW : Admits (cenIn K (A : Set Γ) ⊔ A) W) (hperf : Group.IsPerfect ↥W)
    (hR : Group.IsSolvable ↥R) (hWR : Admits W R) {x : Γ} (hxW : x ∈ W) (hxR : x ∈ R) :
    x = 1 := by
  have hK : IsDirectProduct (lcal K) K := h.semisimple.isDirectProduct_lcal
  have hxK : x ∈ K := hWK hxW
  have h1 : (⟨x, hxK⟩ : ↥K) = 1 := by
    refine hK.ext_coord fun J hJ => ?_
    rw [map_one]
    obtain ⟨hJK, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
    by_cases hQ : Group.IsSolvable ↥(projIn (lcal K) J W)
    ·
      have hQeq : projIn (lcal K) J W =
          (W.subgroupOf K).map (J.subtype.comp (hK.coord hJ)) := by
        ext z
        rw [IsDirectProduct.mem_projIn_iff hK hJ, Subgroup.mem_map]
        constructor
        · rintro ⟨y, hyW, rfl⟩
          exact ⟨y, Subgroup.mem_subgroupOf.mpr hyW, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
      have hWperf' : Group.IsPerfect ↥(W.subgroupOf K) := by
        rw [Subgroup.isPerfect_iff]
        apply Subgroup.map_injective K.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hWK]
        exact Subgroup.isPerfect_iff.mp hperf
      have hperfQ : Group.IsPerfect ↥(projIn (lcal K) J W) := by
        rw [hQeq]
        exact Group.IsPerfect.map _
      have hQbot : projIn (lcal K) J W = ⊥ := by
        by_contra hne
        have : Nontrivial ↥(projIn (lcal K) J W) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
        exact Group.IsPerfect.not_isSolvable _ hQ
      have hmem : ((hK.coord hJ ⟨x, hxK⟩ : J) : Γ) ∈ projIn (lcal K) J W :=
        (IsDirectProduct.mem_projIn_iff hK hJ).mpr ⟨⟨x, hxK⟩, hxW, rfl⟩
      rw [hQbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    ·
      obtain ⟨hJW, -⟩ := thm210g h hWK hW hJ hQ
      set P : Subgroup Γ := (R.subgroupOf K).map (J.subtype.comp (hK.coord hJ)) with hPdef
      have hPJ : P ≤ J := by
        rintro _ ⟨y, -, rfl⟩
        exact (hK.coord hJ y).2
      have hRsolK : Group.IsSolvable ↥(R.subgroupOf K) :=
        Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hRK).symm.toMonoidHom)
          (MulEquiv.surjective _)
      have hPsolv : Group.IsSolvable ↥P :=
        Group.isSolvable_of_surjective
          (f := (J.subtype.comp (hK.coord hJ)).subgroupMap (R.subgroupOf K))
          ((J.subtype.comp (hK.coord hJ)).subgroupMap_surjective _)
      have hPconj : ∀ q ∈ P, ∀ j ∈ J, j * q * j⁻¹ ∈ P := by
        rintro _ ⟨r, hr, rfl⟩ j hj
        have hjQ : j ∈ projIn (lcal K) J W := by
          rw [hJW]
          exact hj
        obtain ⟨w, hwW, hwj⟩ := (IsDirectProduct.mem_projIn_iff hK hJ).mp hjQ
        have hr' : (r : Γ) ∈ R := Subgroup.mem_subgroupOf.mp hr
        have hwrK : w * r * w⁻¹ ∈ R.subgroupOf K :=
          Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hWR hwW) ↑r).mp hr')
        refine ⟨w * r * w⁻¹, hwrK, ?_⟩
        simp only [MonoidHom.comp_apply, map_mul, map_inv, Subgroup.coe_subtype]
        rw [hwj]
      have hPbot : P = ⊥ := by
        have hnorm : (P.subgroupOf J).Normal :=
          (Subgroup.normal_subgroupOf_iff hPJ).mpr fun q j hq hj => hPconj q hq j hj
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf J) with hb | ht
        · refine eq_bot_iff.mpr fun z hz => ?_
          have : (⟨z, hPJ hz⟩ : ↥J) ∈ P.subgroupOf J := hz
          rw [hb] at this
          simpa using congrArg Subtype.val (Subgroup.mem_bot.mp this)
        · exfalso
          have hJP : J ≤ P := Subgroup.subgroupOf_eq_top.mp ht
          have hJsol : Group.IsSolvable ↥J := Thm211.isSolvable_of_le hJP hPsolv
          exact hJnc (isMulCommutative_iff.mpr fun a b => by
            simpa using IsSimpleGroup.comm_iff_isSolvable.mpr hJsol a b)
      have hmem : ((hK.coord hJ ⟨x, hxK⟩ : J) : Γ) ∈ P :=
        ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr hxR, rfl⟩
      rw [hPbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
  exact congrArg Subtype.val h1

theorem inf_eq_bot_of_solvable
    (h : SemisimpleAction p A K) (hWK : W ≤ K) (hRK : R ≤ K)
    (hW : Admits (cenIn K (A : Set Γ) ⊔ A) W) (hperf : Group.IsPerfect ↥W)
    (hR : Group.IsSolvable ↥R) (hWR : Admits W R) : W ⊓ R = ⊥ :=
  eq_bot_iff.mpr fun _ hx => Subgroup.mem_bot.mpr
    (eq_one_of_mem_inf h hWK hRK hW hperf hR hWR hx.1 hx.2)

omit [Finite Γ] in
theorem commute_of_inf_eq_bot {W V L : Subgroup Γ} (hW : Admits L W) (hV : Admits L V)
    (hWL : W ≤ L) (hVL : V ≤ L) (hWV : W ⊓ V = ⊥) {w x : Γ} (hw : w ∈ W) (hx : x ∈ V) :
    Commute w x := by
  have h1 : w * x * w⁻¹ * x⁻¹ ∈ W ⊓ V := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have : x * w⁻¹ * x⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hW (hVL hx)) w⁻¹).mp (inv_mem hw)
      have e : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem hw this
    · have : w * x * w⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hV (hWL hw)) x).mp hx
      exact mul_mem this (inv_mem hx)
  rw [hWV, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_commute.mp (by rwa [commutatorElement_def])

theorem semisimpleAction_kOf {X : Subgroup Γ} (h : NearAsolvAction p A X) (hsol : sol X = ⊥)
    (hX : X ≠ ⊥) : SemisimpleAction p A (kOf X) :=
  { Thm211.nearAsolvAction_of_le h (kOf_le X)
      (h.admits.trans (Thm211.normalizer_le_normalizer_kOf X)) with
    semisimple := isSemisimple_kOf hsol
    ne_bot := Thm211.kOf_ne_bot hsol hX }

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a
