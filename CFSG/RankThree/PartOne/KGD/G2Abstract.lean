module

public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne.KGD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.LocalRank
open scoped Pointwise

theorem abelian_card_involutions_le_four {V : Type*} [Group V] {L : Type*} [Field L]
    (ψ : V →* (Fin 2 → Lˣ)) (hψ : Function.Injective ψ) :
    (∀ v w : V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  refine ⟨fun v w => hψ (by rw [map_mul, map_mul, mul_comm]), ?_⟩
  have hsq : ∀ c : Lˣ, c ^ 2 = 1 → c = 1 ∨ c = -1 := by
    intro c hc
    have h1 : (c : L) * (c : L) = 1 := by
      have := congrArg (fun u : Lˣ => (u : L)) hc
      simpa [sq] using this
    rcases mul_self_eq_one_iff.1 h1 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by simpa using h))
  let f : {v : V // v ^ 2 = 1} → (Fin 2 → Bool) := fun v i => decide (ψ v.1 i = 1)
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply hψ
    funext i
    have hv : (ψ v.1 i) ^ 2 = 1 := by
      have := congrArg (fun c : Fin 2 → Lˣ => c i) (show (ψ v.1) ^ 2 = 1 by
        rw [← map_pow, v.2, map_one])
      simpa using this
    have hw : (ψ w.1 i) ^ 2 = 1 := by
      have := congrArg (fun c : Fin 2 → Lˣ => c i) (show (ψ w.1) ^ 2 = 1 by
        rw [← map_pow, w.2, map_one])
      simpa using this
    have hvw := congrFun h i
    simp only [f, decide_eq_decide] at hvw
    by_cases h1 : ψ v.1 i = 1
    · rw [h1, hvw.1 h1]
    · have h2 : ¬ ψ w.1 i = 1 := fun h => h1 (hvw.2 h)
      rcases hsq _ hv with h | h
      · exact absurd h h1
      · rcases hsq _ hw with h' | h'
        · exact absurd h' h2
        · rw [h, h']
  calc Nat.card {v : V // v ^ 2 = 1} ≤ Nat.card (Fin 2 → Bool) :=
        Nat.card_le_card_of_injective _ hf
    _ = 4 := by simp [Nat.card_eq_fintype_card]


theorem solvable_normal_abelian_card_le {C : Type*} [Group C] [Finite C] {L : Type*} [Field L]
    (Y : Subgroup C)
    (hcase : (∃ φ : Y →* (Fin 2 → Lˣ), Function.Injective φ) ∨
      (CFSG.IsQuasisimple (⁅Y, Y⁆ : Subgroup C) ∧
        ∃ φ : (Y ⊓ centralizer ((⁅Y, Y⁆ : Subgroup C) : Set C) : Subgroup C) →*
            (Fin 2 → Lˣ), Function.Injective φ)) :
    ∀ V : Subgroup Y, V.Normal → Group.IsSolvable V →
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  intro V hVn hVs
  rcases hcase with ⟨φ, hφ⟩ | ⟨hRq, φ, hφ⟩
  · obtain ⟨hab, hcard⟩ := abelian_card_involutions_le_four (φ.comp V.subtype)
      (hφ.comp V.subtype_injective)
    exact ⟨fun v hv w hw => congrArg Subtype.val (hab ⟨v, hv⟩ ⟨w, hw⟩), hcard⟩
  · set N : Subgroup Y := ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ with hN
    have hNnormal : N.Normal := Subgroup.commutator_normal _ _
    have hNmap : N.map Y.subtype = ⁅Y, Y⁆ := by
      rw [hN, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    have eN : N ≃* (⁅Y, Y⁆ : Subgroup C) :=
      (Subgroup.equivMapOfInjective N Y.subtype Y.subtype_injective).trans
        (MulEquiv.subgroupCongr hNmap)
    have hNq : CFSG.IsQuasisimple N := CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hRq
    have hcomm : ⁅N, V⁆ = ⊥ :=
      (CFSG.LocalCores.component_solvable_centralizer hVs hVn.isSubnormal).1 N
        ⟨hNq, hNnormal.isSubnormal⟩
    have hNV : N ≤ centralizer (V : Set Y) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hvc : ∀ v : V, ((v : Y) : C) ∈ centralizer ((⁅Y, Y⁆ : Subgroup C) : Set C) := by
      intro v
      refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
      rw [← hNmap] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      have := Subgroup.mem_centralizer_iff.1 (hNV hr) (v : Y) v.2
      exact (congrArg Subtype.val this).symm
    let f : V →* ↥(Y ⊓ centralizer ((⁅Y, Y⁆ : Subgroup C) : Set C)) :=
      (Y.subtype.comp V.subtype).codRestrict _ fun v => ⟨(v : Y).2, hvc v⟩
    have hf : Function.Injective f := by
      intro a b h
      have h' : ((a : Y) : C) = ((b : Y) : C) :=
        congrArg (fun z : ↥(Y ⊓ centralizer ((⁅Y, Y⁆ : Subgroup C) : Set C)) => (z : C)) h
      exact Subtype.ext (Subtype.ext h')
    obtain ⟨hab, hcard⟩ := abelian_card_involutions_le_four (φ.comp f) (hφ.comp hf)
    exact ⟨fun v hv w hw => congrArg Subtype.val (hab ⟨v, hv⟩ ⟨w, hw⟩), hcard⟩

theorem not_isCyclic_of_exponent_sq {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (hpow : ∀ u : P, u ^ p = 1) (hcard : Nat.card P = p ^ 2) : ¬ IsCyclic P := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hpow g)
  rw [hg, hcard] at h1
  have h2 : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos h1
  have h3 := hp.two_le
  nlinarith

theorem plane_comap_conj {C : Type*} [Group C] [Finite C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {p : ℕ} (hp : p.Prime)
    {A : Subgroup (MulAut C)} (hA : IsElementaryAbelian p A) (hcard : Nat.card A = p ^ 2)
    (hAinn : A ≤ (MulAut.conj : C →* MulAut C).range) :
    ∃ P : Subgroup C, P.map (MulAut.conj : C →* MulAut C) = A ∧ Nat.card P = p ^ 2 ∧
      IsPGroup p P ∧ ∀ u ∈ P, u ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  set P : Subgroup C := A.comap (MulAut.conj : C →* MulAut C) with hP
  have hPmap : P.map (MulAut.conj : C →* MulAut C) = A := Subgroup.map_comap_eq_self hAinn
  have eP : P ≃* A :=
    (Subgroup.equivMapOfInjective P _ hinj).trans (MulEquiv.subgroupCongr hPmap)
  refine ⟨P, hPmap, ?_, ?_, ?_⟩
  · rw [Nat.card_congr eP.toEquiv, hcard]
  · exact (IsElementaryAbelian.isPGroup p A).of_equiv eP.symm
  · intro u hu
    have h := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) (MulAut.conj u) hu
    exact hinj (by rw [map_pow, h, map_one])

theorem exists_mem_theta_of_mem_autThetaT {M : Type*} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime) (B : Subgroup M) {A : Subgroup M} {s : M} (hs : s ∈ autThetaT p B A) {a : M}
    (haA : a ∈ A) (ha1 : a ≠ 1) (haB : a ∈ B) :
    ∃ s' ∈ inSubgroup (aschbacherSolvableCore p) (centralizer ({(⟨a, haB⟩ : B)} : Set B)),
      (s' : M) = s := by
  simp only [autThetaT, Subgroup.mem_iInf] at hs
  have h := hs a haA ha1
  rw [← map_subtype_theta_centralizer hp B ⟨a, haB⟩] at h
  obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 h
  exact ⟨s', hs', rfl⟩

theorem apply_conj_extension {G G₂ : Type*} [Group G] [Group G₂] (Fa bc : G →* G₂) (w₀ : G₂)
    (hFa : ∀ h, Fa h = w₀ * bc h * w₀⁻¹) (φ : MulAut G) (φ₂ : MulAut G₂)
    (hφ : ∀ h, φ₂ (bc h) = bc (φ h)) (y : G) :
    ∀ h : G, Fa ((MulAut.conj y * φ) h) =
      (MulAut.conj (Fa y * w₀ * (φ₂ w₀)⁻¹) * φ₂) (Fa h) := by
  intro h
  have h2 : bc h = w₀⁻¹ * Fa h * w₀ := by rw [hFa]; group
  have h3 : Fa (φ h) = w₀ * φ₂ (w₀⁻¹ * Fa h * w₀) * w₀⁻¹ := by
    rw [hFa (φ h), ← hφ, h2]
  show Fa (y * φ h * y⁻¹) =
    (Fa y * w₀ * (φ₂ w₀)⁻¹) * φ₂ (Fa h) * (Fa y * w₀ * (φ₂ w₀)⁻¹)⁻¹
  simp only [map_mul, map_inv]
  rw [h3]
  simp only [map_mul, map_inv]
  group

end CFSG.RankThree.PartOne.KGD
