module

public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.Quasithin

open Subgroup

variable {X : Type*} [Group X]

theorem s151u_mem_center_of_comm_mem_center (hperf : Group.IsPerfect X) {x : X}
    (hx : ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center X) : x ∈ Subgroup.center X := by
  let φ : X →* Subgroup.center X :=
    { toFun := fun y => ⟨x * y * x⁻¹ * y⁻¹, hx y⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro y z
        apply Subtype.ext
        have hz : x * z * x⁻¹ * z⁻¹ ∈ Subgroup.center X := hx z
        have hc : y * (x * z * x⁻¹ * z⁻¹) = (x * z * x⁻¹ * z⁻¹) * y :=
          (Subgroup.mem_center_iff.mp hz y)
        show x * (y * z) * x⁻¹ * (y * z)⁻¹ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹)
        calc x * (y * z) * x⁻¹ * (y * z)⁻¹
            = (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹)) * y⁻¹ := by group
          _ = (x * y * x⁻¹ * y⁻¹) * ((x * z * x⁻¹ * z⁻¹) * y) * y⁻¹ := by rw [hc]
          _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group }
  have hker : commutator X ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [Group.isPerfect_def.mp hperf] at hker
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : φ y = 1 := hker (Subgroup.mem_top y)
  have h2 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
  calc y * x = (x * y * x⁻¹ * y⁻¹) * (y * x) := by rw [h2, one_mul]
    _ = x * y := by group

theorem s151u_centralizer_pCore_le_or_quasisimple [Finite X]
    (hperf : Group.IsPerfect X)
    (hq : CFSG.IsQuasisimple (X ⧸ CFSG.pCore 2 X))
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.pCore p X = ⊥) :
    Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X ∨ CFSG.IsQuasisimple X := by
  by_cases hC : Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X
  · exact Or.inl hC
  right
  set Q : Subgroup X := CFSG.pCore 2 X with hQdef
  set C : Subgroup X := Subgroup.centralizer (Q : Set X) with hCdef
  have hQn : Q.Normal := CFSG.pCore_normal
  have hCn : C.Normal := inferInstance
  have hmk : Function.Surjective (QuotientGroup.mk' Q) := QuotientGroup.mk'_surjective Q
  have hN : (C.map (QuotientGroup.mk' Q)).Normal := Subgroup.Normal.map hCn _ hmk
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (C.map (QuotientGroup.mk' Q))
    with hCen | hTop
  ·
    exfalso
    apply hC
    have hcomm : ∀ x ∈ C, ∀ y : X, x * y * x⁻¹ * y⁻¹ ∈ Q := by
      intro x hx y
      have hxc : QuotientGroup.mk' Q x ∈ Subgroup.center (X ⧸ Q) := hCen ⟨x, hx, rfl⟩
      have h := Subgroup.mem_center_iff.mp hxc (QuotientGroup.mk' Q y)
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' Q (x * y * x⁻¹ * y⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
      group
    have hnil : Group.IsNilpotent C := by
      refine ⟨⟨2, ?_⟩⟩
      rw [eq_top_iff]
      intro a _
      rw [Subgroup.mem_upperCentralSeries_succ_iff]
      intro b
      rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have hQmem : ((a * b * a⁻¹ * b⁻¹ : C) : X) ∈ Q := hcomm a a.2 b
      exact (Subgroup.mem_centralizer_iff.mp c.2 _ hQmem).symm
    have hCle : C ≤ CFSG.fittingSubgroup X := le_sSup ⟨hCn, hnil⟩
    rw [CFSG.fitting_eq_sup_pCore] at hCle
    refine hCle.trans (iSup_le fun p => ?_)
    by_cases hp : p.1.1 = 2
    · rw [hp]
    · have hpr : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
      rw [hodd _ hpr hp]
      exact bot_le
  ·
    have hdec : ∀ x : X, ∃ c ∈ C, ∃ q ∈ Q, x = c * q := by
      intro x
      have hmem : QuotientGroup.mk' Q x ∈ C.map (QuotientGroup.mk' Q) := by rw [hTop]; trivial
      obtain ⟨c, hc, hcx⟩ := hmem
      refine ⟨c, hc, c⁻¹ * x, ?_, by simp⟩
      have : (c : X ⧸ Q) = (x : X ⧸ Q) := hcx
      exact QuotientGroup.eq.mp this
    have hCtop : C = ⊤ := by
      let f : Q →* X ⧸ C := (QuotientGroup.mk' C).comp Q.subtype
      have hf : Function.Surjective f := by
        intro z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
        obtain ⟨c, hc, q, hq', rfl⟩ := hdec x
        refine ⟨⟨q, hq'⟩, ?_⟩
        show ((q : X) : X ⧸ C) = ((c * q : X) : X ⧸ C)
        rw [QuotientGroup.eq]
        have := hCn.conj_mem c hc q⁻¹
        simpa [mul_assoc] using this
      have hnil : Group.IsNilpotent Q := (CFSG.pCore_isPGroup (p := 2) (G := X)).isNilpotent
      have hsolv : Group.IsSolvable (X ⧸ C) := Group.isSolvable_of_surjective hf
      have hperfq : Group.IsPerfect (X ⧸ C) := inferInstance
      have hsub : Subsingleton (X ⧸ C) := by
        by_contra hns
        rw [not_subsingleton_iff_nontrivial] at hns
        exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (X ⧸ C)).ne
          (Group.isPerfect_def.mp hperfq)
      rw [eq_top_iff]
      intro x _
      have : (x : X ⧸ C) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).mp this
    have hQcen : Q ≤ Subgroup.center X := by
      intro q hq'
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := by rw [hCtop]; trivial
      exact (Subgroup.mem_centralizer_iff.mp hg q hq').symm
    let ψ : X →* (X ⧸ Q) ⧸ Subgroup.center (X ⧸ Q) :=
      (QuotientGroup.mk' (Subgroup.center (X ⧸ Q))).comp (QuotientGroup.mk' Q)
    have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hmk
    have hker : ψ.ker ≤ Subgroup.center X := by
      intro x hx
      apply s151u_mem_center_of_comm_mem_center hperf
      intro y
      apply hQcen
      have hx' : QuotientGroup.mk' Q x ∈ Subgroup.center (X ⧸ Q) := by
        have := (MonoidHom.mem_ker.mp hx)
        exact (QuotientGroup.eq_one_iff _).mp this
      have h := Subgroup.mem_center_iff.mp hx' (QuotientGroup.mk' Q y)
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' Q (x * y * x⁻¹ * y⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
      group
    let e : X ⧸ ψ.ker ≃* (X ⧸ Q) ⧸ Subgroup.center (X ⧸ Q) :=
      QuotientGroup.quotientKerEquivOfSurjective ψ hψ
    obtain ⟨-, hs, a, b, hab⟩ := hq
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient ψ.ker hker hperf
      ((MulEquiv.isSimpleGroup_congr e).mpr hs) ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this

end CFSG.Quasithin
