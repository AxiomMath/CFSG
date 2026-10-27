module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeTrans

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_Z_normal_form (hc : Nine3Choice V T A K S X p g x) {n : ℕ}
    {B : Fin (n + 1) → Subgroup G} {bb : Fin (n + 1) → G}
    (hB : ∀ k, k ≠ 0 → B k ∈ nineOmegaIn V K S)
    (hsurj : ∀ D ∈ nineOmegaIn V K S, ∃ k, k ≠ 0 ∧ B k = D)
    (hbb : ∀ k, k ≠ 0 → bb k ∈ B k ∧ bb k ∉ pCoreOf 2 K) (hbb0 : bb 0 = 1)
    {z : G} (hz : z ∈ nineZ V K S) :
    ∃ j₀ ∈ ⨆ D ∈ nineOmegaIn V K S, D ⊓ pCoreOf 2 K, ∃ ε : Fin (n + 1) → Bool, ε 0 = false ∧
      z = j₀ * ((List.finRange (n + 1)).map fun k => if ε k then bb k else 1).prod := by
  let W : Subgroup G := nineW V S
  have hZW : nineZ V K S ≤ W := by
    change nineZ V K S ≤ nineW V S
    rw [hc.core.nineW_eq]
    exact le_sup_right
  let J : Subgroup G := ⨆ D ∈ nineOmegaIn V K S, D ⊓ pCoreOf 2 K
  have hJZ : J ≤ nineZ V K S := by
    refine iSup₂_le fun D hD => ?_
    exact (inf_le_left : D ⊓ pCoreOf 2 K ≤ D).trans (le_iSup₂_of_le D hD le_rfl)
  have hJW : J ≤ W := hJZ.trans hZW
  haveI : IsMulCommutative ↥W := hc.core.nineW_isElemAbelian.1
  letI : CommGroup ↥W := IsMulCommutative.instCommGroup
  have hbbW : ∀ k, bb k ∈ W := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [hbb0]
      exact W.one_mem
    · exact hZW ((le_iSup₂_of_le (B k) (hB k hk) (le_rfl : B k ≤ B k) :
        B k ≤ nineZ V K S) ((hbb k hk).1))
  let bW : Fin (n + 1) → ↥W := fun k => ⟨bb k, hbbW k⟩
  have hbW : ∀ k, bW k * bW k = 1 := by
    intro k
    apply Subtype.ext
    show bb k * bb k = (1 : G)
    by_cases hk : k = 0
    · subst hk
      rw [hbb0, one_mul]
    · have h2 := (hc.core.nineOmegaIn_isElemAbelian (hB k hk)).2 (bb k) (hbb k hk).1
      rwa [pow_two] at h2
  let cW : (Fin (n + 1) → Bool) → ↥W := fun ε => ∏ k, if ε k then bW k else 1
  have cW_mul : ∀ ε ε' : Fin (n + 1) → Bool,
      cW ε * cW ε' = cW (fun k => ε k ^^ ε' k) := by
    intro ε ε'
    dsimp only [cW]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by
      rcases Bool.dichotomy (ε k) with h1 | h1 <;>
        rcases Bool.dichotomy (ε' k) with h2 | h2 <;>
        simp [h1, h2, hbW k]
  have cW_false : cW (fun _ => false) = 1 := by
    dsimp only [cW]
    simp
  have cW_self : ∀ ε, cW ε * cW ε = 1 := by
    intro ε
    rw [cW_mul ε ε]
    have h : (fun k => ε k ^^ ε k) = fun _ => false := funext fun k => Bool.xor_self (ε k)
    rw [h, cW_false]
  have cW_single : ∀ k, cW (fun k' => if k' = k then true else false) = bW k := by
    intro k
    dsimp only [cW]
    rw [show (∏ k', if (if k' = k then true else false) then bW k' else 1) =
        (∏ k', if k' = k then bW k' else 1) from
      Finset.prod_congr rfl fun k' _ => by by_cases h : k' = k <;> simp [h]]
    exact Fintype.prod_ite_eq' k bW
  let lp : (Fin (n + 1) → Bool) → G := fun ε =>
    ((List.finRange (n + 1)).map fun k => if ε k then bb k else 1).prod
  have hcast : ∀ ε, lp ε = (cW ε : G) := by
    intro ε
    dsimp only [lp, cW]
    change ((List.finRange (n + 1)).map (fun k => if ε k then bb k else 1)).prod =
      W.subtype (∏ k : Fin (n + 1), if ε k then bW k else 1)
    rw [Fin.prod_univ_def, MonoidHom.map_list_prod, List.map_map]
    have hlist : (List.finRange (n + 1)).map
          (W.subtype ∘ fun k => if ε k then bW k else 1) =
        (List.finRange (n + 1)).map (fun k => if ε k then bb k else 1) := by
      refine List.map_congr_left fun k _ => ?_
      rcases Bool.dichotomy (ε k) with hv | hv <;> simp [hv, bW]
    rw [← hlist]
  have hpfalse : lp (fun _ => false) = 1 := by
    rw [hcast (fun _ => false)]
    change ((cW (fun _ => false) : ↥W) : G) = 1
    rw [cW_false]
    rfl
  let Q : Subgroup G :=
    { carrier := {z | ∃ j₀ ∈ J, ∃ ε : Fin (n + 1) → Bool, ε 0 = false ∧ z = j₀ * lp ε}
      mul_mem' := by
        rintro z₁ z₂ ⟨j₁, hj₁, ε₁, hε₁, rfl⟩ ⟨j₂, hj₂, ε₂, hε₂, rfl⟩
        refine ⟨j₁ * j₂, J.mul_mem hj₁ hj₂, fun k => ε₁ k ^^ ε₂ k, ?_, ?_⟩
        · simp [hε₁, hε₂]
        · have hW1 : lp ε₁ ∈ W := by
            rw [hcast ε₁]
            exact (cW ε₁).2
          have hcomm : lp ε₁ * j₂ = j₂ * lp ε₁ :=
            hc.core.nineW_mul_comm hW1 (hJW hj₂)
          have hlp : lp ε₁ * lp ε₂ = lp (fun k => ε₁ k ^^ ε₂ k) := by
            rw [hcast ε₁, hcast ε₂, ← Subgroup.coe_mul, cW_mul, hcast (fun k => ε₁ k ^^ ε₂ k)]
          calc (j₁ * lp ε₁) * (j₂ * lp ε₂)
              = j₁ * (lp ε₁ * j₂) * lp ε₂ := by group
            _ = j₁ * (j₂ * lp ε₁) * lp ε₂ := by rw [hcomm]
            _ = (j₁ * j₂) * (lp ε₁ * lp ε₂) := by group
            _ = (j₁ * j₂) * lp (fun k => ε₁ k ^^ ε₂ k) := by rw [hlp]
      one_mem' := by
        refine ⟨1, J.one_mem, fun _ => false, rfl, ?_⟩
        rw [one_mul, hpfalse]
      inv_mem' := by
        rintro z ⟨j, hj, ε, hε, rfl⟩
        refine ⟨j⁻¹, J.inv_mem hj, ε, hε, ?_⟩
        have hWlp : lp ε ∈ W := by
          rw [hcast ε]
          exact (cW ε).2
        have hself : lp ε * lp ε = 1 := by
          rw [hcast ε, ← Subgroup.coe_mul, cW_self, Subgroup.coe_one]
        calc (j * lp ε)⁻¹ = (lp ε)⁻¹ * j⁻¹ := by group
          _ = lp ε * j⁻¹ := by rw [inv_eq_of_mul_eq_one_right hself]
          _ = j⁻¹ * lp ε := hc.core.nineW_mul_comm hWlp (hJW (J.inv_mem hj)) }
  have hmemJ : ∀ {D : Subgroup G}, D ∈ nineOmegaIn V K S → D ⊓ pCoreOf 2 K ≤ J :=
    fun hD => le_iSup₂_of_le _ hD le_rfl
  have hZQ : nineZ V K S ≤ Q := by
    refine iSup₂_le fun Bk hBk => ?_
    obtain ⟨k, hk, hBk_eq⟩ := hsurj Bk hBk
    rw [← hBk_eq] at hBk ⊢
    intro x hx
    have hxZ : x ∈ nineZ V K S :=
      (le_iSup₂_of_le (B k) hBk (le_rfl : B k ≤ B k) : B k ≤ nineZ V K S) hx
    by_cases hxR : x ∈ pCoreOf 2 K
    · refine ⟨x, ?_, fun _ => false, rfl, ?_⟩
      · exact hmemJ hBk (Subgroup.mem_inf.mpr ⟨hx, hxR⟩)
      · rw [hpfalse, mul_one]
    · have hbB : bb k ∈ B k := (hbb k hk).1
      have hbR : bb k ∉ pCoreOf 2 K := (hbb k hk).2
      have htB : (bb k)⁻¹ * x ∈ B k := (B k).mul_mem ((B k).inv_mem hbB) hx
      have htR : (bb k)⁻¹ * x ∈ pCoreOf 2 K :=
        hc.core.nineOmegaIn_inv_mul_mem hBk hbB hx hbR hxR
      have hsingle : lp (fun k' => if k' = k then true else false) = bb k := by
        rw [hcast (fun k' => if k' = k then true else false), cW_single k]
      refine ⟨(bb k)⁻¹ * x, ?_, fun k' => if k' = k then true else false, ?_, ?_⟩
      · exact hmemJ hBk (Subgroup.mem_inf.mpr ⟨htB, htR⟩)
      · simp [Ne.symm hk]
      · rw [hsingle]
        have hxW : x ∈ W := hZW hxZ
        have hbWk : bb k ∈ W := hbbW k
        have hxb : x * bb k = bb k * x := hc.core.nineW_mul_comm hxW hbWk
        calc x = (bb k)⁻¹ * bb k * x := by rw [inv_mul_cancel, one_mul]
          _ = (bb k)⁻¹ * (bb k * x) := by rw [mul_assoc]
          _ = (bb k)⁻¹ * (x * bb k) := by rw [hxb]
          _ = (bb k)⁻¹ * x * bb k := by rw [mul_assoc]
  have hzQ : z ∈ Q := hZQ hz
  change ∃ j₀ ∈ J, ∃ ε : Fin (n + 1) → Bool, ε 0 = false ∧ z = j₀ * lp ε at hzQ
  obtain ⟨j₀, hj₀, ε, hε, hw_eq'⟩ := hzQ
  exact ⟨j₀, hj₀, ε, hε, hw_eq'⟩

end CFSG.LocalAnalysis.WeakClosure81
