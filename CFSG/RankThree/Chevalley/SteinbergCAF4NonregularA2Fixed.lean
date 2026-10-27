module

public import CFSG.RankThree.Chevalley.SteinbergCAF4NonregularSL3
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.RankThree.SteinbergR3ESL3RootPermutingFixed

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN
  Matrix.SpecialLinearGroup CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Twisted

variable {τ : Tag} {Ω : Type} [Field Ω]

theorem exists_subsystemGroup_twistedEquiv
    (F : Ω →+* Ω) (hbij : Function.Bijective F)
    {J : Set (Fin τ.rank)} {m : ModGL τ Ω}
    (hm : ∀ z ∈ subsystemGroup τ Ω J, m * z * m⁻¹ ∈ subsystemGroup τ Ω J)
    (hm' : ∀ z ∈ subsystemGroup τ Ω J, m⁻¹ * z * m ∈ subsystemGroup τ Ω J) :
    ∃ θQ : subsystemGroup τ Ω J ≃* subsystemGroup τ Ω J,
      ∀ z, (θQ z : ModGL τ Ω) = twistedEntrywise m F z := by
  classical
  set σ : Ω ≃+* Ω := RingEquiv.ofBijective F hbij with hσ
  have hσF : σ.toRingHom = F := RingHom.ext fun _ => rfl
  set Fi : Ω →+* Ω := σ.symm.toRingHom with hFi
  have hFFi : F.comp Fi = RingHom.id Ω := by
    ext c
    rw [hFi, ← hσF]
    simp
  have hθQ : ∀ z ∈ subsystemGroup τ Ω J, twistedEntrywise m F z ∈ subsystemGroup τ Ω J :=
    fun z hz => by
      rw [twistedEntrywise_apply]
      exact hm _ (baseChangeGL_mem_subsystemGroup F hz)
  let θ' : subsystemGroup τ Ω J →* subsystemGroup τ Ω J :=
    ((twistedEntrywise m F).comp (subsystemGroup τ Ω J).subtype).codRestrict _
      fun z => hθQ z z.2
  have hinj : Function.Injective θ' := fun a b h => by
    have h1 := congrArg Subtype.val h
    change m * Units.map (entrywiseHom F) (a : ModGL τ Ω) * m⁻¹ =
      m * Units.map (entrywiseHom F) (b : ModGL τ Ω) * m⁻¹ at h1
    rw [mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext ((baseChangeGL_injective (τ := τ) F) h1)
  have hsurj : Function.Surjective θ' := fun g => by
    set g' : ModGL τ Ω := (g : ModGL τ Ω) with hg'
    refine ⟨⟨Units.map (entrywiseHom Fi) (m⁻¹ * g' * m), baseChangeGL_mem_subsystemGroup Fi
      (hm' _ g.2)⟩, Subtype.ext ?_⟩
    change m * Units.map (entrywiseHom F) (Units.map (entrywiseHom Fi) (m⁻¹ * g' * m)) * m⁻¹ = g'
    have e : Units.map (entrywiseHom F) (Units.map (entrywiseHom Fi) (m⁻¹ * g' * m)) =
        m⁻¹ * g' * m := by
      apply Units.ext
      change entrywise F (entrywise Fi _) = _
      rw [entrywise_entrywise, hFFi, entrywise_id]
    rw [e]
    group
  exact ⟨MulEquiv.ofBijective θ' ⟨hinj, hsurj⟩, fun z => rfl⟩

end Twisted

section Monomial

variable {τ : Tag} {L : Type} [Field L]

theorem conj_mem_subsystemGroup_of_mapsRootLines
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {w₀ : WeylGroup τ} (hnw : MapsRootLines n w₀) {J : Set (Fin τ.rank)}
    (hJ : ∀ a ∈ J, w₀ • (Pi.single a 1 : Fin τ.rank → ℤ) = Pi.single a 1 ∨
      w₀ • (Pi.single a 1 : Fin τ.rank → ℤ) = -Pi.single a 1)
    {z : ModGL τ L} (hz : z ∈ subsystemGroup τ L J) : n * z * n⁻¹ ∈ subsystemGroup τ L J := by
  have key : ∀ a ∈ J, ∀ γ : Fin τ.rank → ℤ, (γ = Pi.single a 1 ∨ γ = -Pi.single a 1) →
      ∀ c, n * pinnedX τ L γ c * n⁻¹ ∈ subsystemGroup τ L J := by
    intro a ha γ hγ c
    have hγr : IsRoot τ γ := by
      rcases hγ with rfl | rfl
      exacts [isRoot_single τ a, isRoot_neg_single τ a]
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hγr
    rw [hμ c, weylQuotientHom_eq (g := ⟨n, hn⟩) hnw]
    have h : w₀ • γ = Pi.single a 1 ∨ w₀ • γ = -Pi.single a 1 := by
      rcases hγ with rfl | rfl <;> rcases hJ a ha with h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr (by rw [smul_neg, h])
      · exact Or.inl (by rw [smul_neg, h, neg_neg])
    rcases h with h | h
    · rw [h, pinnedX_single]
      exact xUnit_mem_subsystemGroup ha _
    · rw [h, pinnedX_neg_single]
      exact yUnit_mem_subsystemGroup ha _
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, c, rfl | rfl⟩ := hx
    · rw [← pinnedX_single]
      exact key a ha _ (Or.inl rfl) c
    · rw [← pinnedX_neg_single]
      exact key a ha _ (Or.inr rfl) c
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    rw [show n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group]
    exact inv_mem hx

end Monomial

theorem exists_A2_root_permuting
    (K : Type) [Field K] [Finite K] (Ω : Type) [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K)
    (κ : F4A2Kind) {m : ModGL Tag.F4 Ω} (hm : m ∈ monomialSubgroup Tag.F4 Ω)
    {w : WeylGroup Tag.F4} (hmw : MapsRootLines m w) {η δ : ℤ} (hη : η = 1 ∨ η = -1)
    (hδ : δ = 1 ∨ δ = -1)
    (hw : ∀ a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)), w • (Pi.single a 1 : Fin Tag.F4.rank → ℤ) =
      η • ((simple Tag.F4 κ.i * simple Tag.F4 κ.j) ^ δ • (Pi.single a 1 : Fin Tag.F4.rank → ℤ))) :
    ∃ θQ : subsystemGroup Tag.F4 Ω {κ.i, κ.j} ≃* subsystemGroup Tag.F4 Ω {κ.i, κ.j},
      (∀ z, (θQ z : ModGL Tag.F4 Ω) = twistedEntrywise m F z) ∧
      ∃ (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Ωˣ),
        (η = 1 → ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
          (((f4A2Equiv Ω κ).symm.trans (θQ.trans (f4A2Equiv Ω κ)) (transvection hij t) :
            SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
              1 + single (π i) (π j) ((b i j : Ω) * t ^ Nat.card K)) ∧
        (η = -1 → ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
          (((f4A2Equiv Ω κ).symm.trans (θQ.trans (f4A2Equiv Ω κ)) (transvection hij t) :
            SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
              1 + single (π j) (π i) ((b i j : Ω) * t ^ Nat.card K)) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hbij : Function.Bijective F := frobenius_bijective (k := K) F hF
  set Q := subsystemGroup Tag.F4 Ω {κ.i, κ.j} with hQ
  set r := f4A2Equiv Ω κ with hrdef
  have hr := isElemRep_f4A2Rep Ω κ
  obtain ⟨-, -, -, -, -, hbc, -⟩ := F4_native_long_and_short_A2_faithful_SL3_all_characteristics Ω κ
  obtain ⟨v, hvN, hvw, π, s, hs, hvmat⟩ := exists_f4A2_weyl_pair Ω κ hδ
  rw [← hrdef] at hvmat
  set m' : ModGL Tag.F4 Ω := (v : ModGL Tag.F4 Ω)⁻¹ * m with hm'
  have hm'N : m' ∈ monomialSubgroup Tag.F4 Ω := mul_mem (inv_mem hvN) hm
  set w' := ((simple Tag.F4 κ.i * simple Tag.F4 κ.j) ^ δ)⁻¹ * w with hw'
  have hm'w : MapsRootLines m' w' := hvw.inv.mul hmw
  have hw'a : ∀ a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      w' • (Pi.single a 1 : Fin Tag.F4.rank → ℤ) = η • Pi.single a 1 := fun a ha => by
    rw [hw', mul_smul, hw a ha]
    rcases hη with rfl | rfl
    · rw [one_smul, one_smul, inv_smul_smul]
    · rw [neg_smul, one_smul, neg_smul, one_smul, smul_neg, inv_smul_smul]
  have hpm : ∀ a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      w' • (Pi.single a 1 : Fin Tag.F4.rank → ℤ) = Pi.single a 1 ∨
        w' • (Pi.single a 1 : Fin Tag.F4.rank → ℤ) = -Pi.single a 1 := fun a ha => by
    rw [hw'a a ha]
    rcases hη with rfl | rfl
    · exact Or.inl (one_smul _ _)
    · exact Or.inr (by rw [neg_smul, one_smul])
  have hpm' : ∀ a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      w'⁻¹ • (Pi.single a 1 : Fin Tag.F4.rank → ℤ) = Pi.single a 1 ∨
        w'⁻¹ • (Pi.single a 1 : Fin Tag.F4.rank → ℤ) = -Pi.single a 1 := fun a ha => by
    rcases hpm a ha with h | h
    · exact Or.inl (by rw [inv_smul_eq_iff, h])
    · exact Or.inr (by rw [inv_smul_eq_iff, smul_neg, h, neg_neg])
  have hm'Q : ∀ z ∈ Q, m' * z * m'⁻¹ ∈ Q := fun z hz =>
    conj_mem_subsystemGroup_of_mapsRootLines hm'N hm'w hpm hz
  have hm'Q' : ∀ z ∈ Q, m'⁻¹ * z * m'⁻¹⁻¹ ∈ Q := fun z hz =>
    conj_mem_subsystemGroup_of_mapsRootLines (inv_mem hm'N) hm'w.inv hpm' hz
  have hmeq : m = v * m' := by rw [hm', mul_inv_cancel_left]
  have hmQ : ∀ z ∈ Q, m * z * m⁻¹ ∈ Q := fun z hz => by
    rw [hmeq, show (v : ModGL Tag.F4 Ω) * m' * z * ((v : ModGL Tag.F4 Ω) * m')⁻¹ =
      (v : ModGL Tag.F4 Ω) * (m' * z * m'⁻¹) * (v : ModGL Tag.F4 Ω)⁻¹ by group]
    exact mul_mem (mul_mem v.2 (hm'Q z hz)) (inv_mem v.2)
  have hmQ' : ∀ z ∈ Q, m⁻¹ * z * m ∈ Q := fun z hz => by
    rw [hmeq, show ((v : ModGL Tag.F4 Ω) * m')⁻¹ * z * (v * m') =
      m'⁻¹ * ((v : ModGL Tag.F4 Ω)⁻¹ * z * v) * m'⁻¹⁻¹ by group]
    exact hm'Q' _ (mul_mem (mul_mem (inv_mem v.2) hz) v.2)
  obtain ⟨θQ, hθQ⟩ := exists_subsystemGroup_twistedEquiv F hbij hmQ hmQ'
  refine ⟨θQ, hθQ, ?_⟩
  set ψQ : Q →* Q := ((MulAut.conj m').toMonoidHom.comp Q.subtype).codRestrict Q
    fun z => hm'Q z z.2 with hψQ
  set Ψ : SL(3, Ω) →* SL(3, Ω) := (r.toMonoidHom.comp ψQ).comp r.symm.toMonoidHom with hΨ
  have hgen : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ → ∃ μ : Ωˣ, ∀ c,
      m' * pinnedX Tag.F4 Ω γ c * m'⁻¹ = pinnedX Tag.F4 Ω (w' • γ) (μ * c) := fun γ hγ => by
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hm'N hγ
    rw [weylQuotientHom_eq (g := ⟨m', hm'N⟩) hm'w] at hμ
    exact ⟨μ, hμ⟩
  have hsymm : ∀ c : Ω, r.symm (t01 c) = qx (left_mem_pair κ.i κ.j) c ∧
      r.symm (t10 c) = qy (left_mem_pair κ.i κ.j) c ∧
      r.symm (t12 c) = qx (right_mem_pair κ.i κ.j) c ∧
      r.symm (t21 c) = qy (right_mem_pair κ.i κ.j) c := fun c => by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [MulEquiv.symm_apply_eq, hrdef, f4A2Equiv_apply]
    exacts [(hr c).1.symm, (hr c).2.1.symm, (hr c).2.2.1.symm, (hr c).2.2.2.symm]
  have hθ : ∀ z : Q, ∃ hσ : baseChangeGL F (z : ModGL Tag.F4 Ω) ∈ Q,
      θQ z = v * ψQ ⟨_, hσ⟩ * v⁻¹ := fun z => by
    refine ⟨baseChangeGL_mem_subsystemGroup F z.2, Subtype.ext ?_⟩
    rw [hθQ, twistedEntrywise_apply, units_map_entrywiseHom_eq_baseChangeGL_self]
    change m * baseChangeGL F (z : ModGL Tag.F4 Ω) * m⁻¹ =
      (v : ModGL Tag.F4 Ω) * (m' * baseChangeGL F (z : ModGL Tag.F4 Ω) * m'⁻¹) *
        (v : ModGL Tag.F4 Ω)⁻¹
    rw [hmeq]
    group
  have hFt : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω), ∃ hσ : baseChangeGL F
      ((r.symm (transvection hij t) : Q) : ModGL Tag.F4 Ω) ∈ Q,
        r ⟨_, hσ⟩ = transvection hij (t ^ Nat.card K) := fun i j hij t => by
    obtain ⟨hσ, h⟩ := hbc Ω F (r.symm (transvection hij t))
    refine ⟨hσ, Subtype.ext ?_⟩
    rw [h, MulEquiv.apply_symm_apply, ← hF]
    ext p q'
    simp only [Matrix.map_apply, CFSG.LinearGroups.coe_transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  have hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      (r.symm.trans (θQ.trans r)) (transvection hij t) =
        r v * Ψ (transvection hij (t ^ Nat.card K)) * (r v)⁻¹ := by
    intro i j hij t
    obtain ⟨hσ, hFz⟩ := hFt i j hij t
    obtain ⟨hσ', hθz⟩ := hθ (r.symm (transvection hij t))
    have e : r (ψQ ⟨_, hσ⟩) = Ψ (transvection hij (t ^ Nat.card K)) := by
      rw [← hFz, hΨ]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    change r (θQ (r.symm (transvection hij t))) = _
    rw [hθz, map_mul, map_mul, map_inv, ← e]
  have hΨ1 : ∀ c, Ψ (t01 c) = r (ψQ (qx (left_mem_pair κ.i κ.j) c)) := fun c => by
    rw [hΨ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, (hsymm c).1]
  have hΨ2 : ∀ c, Ψ (t10 c) = r (ψQ (qy (left_mem_pair κ.i κ.j) c)) := fun c => by
    rw [hΨ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, (hsymm c).2.1]
  have hΨ3 : ∀ c, Ψ (t12 c) = r (ψQ (qx (right_mem_pair κ.i κ.j) c)) := fun c => by
    rw [hΨ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, (hsymm c).2.2.1]
  have hΨ4 : ∀ c, Ψ (t21 c) = r (ψQ (qy (right_mem_pair κ.i κ.j) c)) := fun c => by
    rw [hΨ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, (hsymm c).2.2.2]
  have hxpin : ∀ a (ha : a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))), ∃ μ : Ωˣ, ∀ c,
      (ψQ (qx ha c) : ModGL Tag.F4 Ω) =
        pinnedX Tag.F4 Ω (w' • (Pi.single a 1 : Fin Tag.F4.rank → ℤ)) (μ * c) := fun a ha => by
    obtain ⟨μ, hμ⟩ := hgen _ (isRoot_single _ a)
    refine ⟨μ, fun c => ?_⟩
    rw [← hμ c, pinnedX_single]
    rfl
  have hypin : ∀ a (ha : a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))), ∃ μ : Ωˣ, ∀ c,
      (ψQ (qy ha c) : ModGL Tag.F4 Ω) =
        pinnedX Tag.F4 Ω (w' • -(Pi.single a 1 : Fin Tag.F4.rank → ℤ)) (μ * c) := fun a ha => by
    obtain ⟨μ, hμ⟩ := hgen _ (isRoot_neg_single _ a)
    refine ⟨μ, fun c => ?_⟩
    rw [← hμ c, pinnedX_neg_single]
    rfl
  rcases hη with rfl | rfl
  ·
    have hx : ∀ a (ha : a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))), ∃ μ : Ωˣ, ∀ c,
        ψQ (qx ha c) = qx ha (μ * c) := fun a ha => by
      obtain ⟨μ, hμ⟩ := hxpin a ha
      refine ⟨μ, fun c => Subtype.ext ?_⟩
      rw [hμ c, hw'a a ha, one_smul, pinnedX_single]
      rfl
    have hy : ∀ a (ha : a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))), ∃ μ : Ωˣ, ∀ c,
        ψQ (qy ha c) = qy ha (μ * c) := fun a ha => by
      obtain ⟨μ, hμ⟩ := hypin a ha
      refine ⟨μ, fun c => Subtype.ext ?_⟩
      rw [hμ c, smul_neg, hw'a a ha, one_smul, pinnedX_neg_single]
      rfl
    obtain ⟨μ₁, h₁⟩ := hx _ (left_mem_pair κ.i κ.j)
    obtain ⟨μ₂, h₂⟩ := hy _ (left_mem_pair κ.i κ.j)
    obtain ⟨μ₃, h₃⟩ := hx _ (right_mem_pair κ.i κ.j)
    obtain ⟨μ₄, h₄⟩ := hy _ (right_mem_pair κ.i κ.j)
    have hT := exists_transvection_eq_of_simple Ψ (μ₁ := μ₁) (μ₂ := μ₂) (μ₃ := μ₃) (μ₄ := μ₄)
      (fun c => by rw [hΨ1, h₁, hrdef, f4A2Equiv_apply, (hr _).1])
      (fun c => by rw [hΨ2, h₂, hrdef, f4A2Equiv_apply, (hr _).2.1])
      (fun c => by rw [hΨ3, h₃, hrdef, f4A2Equiv_apply, (hr _).2.2.1])
      (fun c => by rw [hΨ4, h₄, hrdef, f4A2Equiv_apply, (hr _).2.2.2])
    refine ⟨π, fun i j => if hij : i ≠ j then Units.mk0 (s i) (hs i) * (hT i j hij).choose *
      (Units.mk0 (s j) (hs j))⁻¹ else 1, fun _ i j hij t => ?_, fun h => absurd h (by decide)⟩
    rw [hΦ i j hij t, (hT i j hij).choose_spec, monomial_conj_transvection hvmat hs hij,
      CFSG.LinearGroups.coe_transvection]
    simp only [ne_eq, hij, not_false_eq_true, ↓reduceDIte, Units.val_mul, Units.val_mk0,
      Units.val_inv_eq_inv_val]
    congr 2
    ring
  ·
    have hx : ∀ a (ha : a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))), ∃ μ : Ωˣ, ∀ c,
        ψQ (qx ha c) = qy ha (μ * c) := fun a ha => by
      obtain ⟨μ, hμ⟩ := hxpin a ha
      refine ⟨μ, fun c => Subtype.ext ?_⟩
      rw [hμ c, hw'a a ha, neg_smul, one_smul, pinnedX_neg_single]
      rfl
    have hy : ∀ a (ha : a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))), ∃ μ : Ωˣ, ∀ c,
        ψQ (qy ha c) = qx ha (μ * c) := fun a ha => by
      obtain ⟨μ, hμ⟩ := hypin a ha
      refine ⟨μ, fun c => Subtype.ext ?_⟩
      rw [hμ c, smul_neg, hw'a a ha, neg_smul, one_smul, neg_neg, pinnedX_single]
      rfl
    obtain ⟨μ₁, h₁⟩ := hx _ (left_mem_pair κ.i κ.j)
    obtain ⟨μ₂, h₂⟩ := hy _ (left_mem_pair κ.i κ.j)
    obtain ⟨μ₃, h₃⟩ := hx _ (right_mem_pair κ.i κ.j)
    obtain ⟨μ₄, h₄⟩ := hy _ (right_mem_pair κ.i κ.j)
    have hT := exists_transvection_swap_eq_of_simple Ψ (μ₁ := μ₁) (μ₂ := μ₂) (μ₃ := μ₃)
      (μ₄ := μ₄)
      (fun c => by rw [hΨ1, h₁, hrdef, f4A2Equiv_apply, (hr _).2.1])
      (fun c => by rw [hΨ2, h₂, hrdef, f4A2Equiv_apply, (hr _).1])
      (fun c => by rw [hΨ3, h₃, hrdef, f4A2Equiv_apply, (hr _).2.2.2])
      (fun c => by rw [hΨ4, h₄, hrdef, f4A2Equiv_apply, (hr _).2.2.1])
    refine ⟨π, fun i j => if hij : i ≠ j then Units.mk0 (s j) (hs j) * (hT i j hij).choose *
      (Units.mk0 (s i) (hs i))⁻¹ else 1, fun h => absurd h (by decide), fun _ i j hij t => ?_⟩
    rw [hΦ i j hij t, (hT i j hij).choose_spec, monomial_conj_transvection hvmat hs hij.symm,
      CFSG.LinearGroups.coe_transvection]
    simp only [ne_eq, hij, not_false_eq_true, ↓reduceDIte, Units.val_mul, Units.val_mk0,
      Units.val_inv_eq_inv_val]
    congr 2
    ring

theorem exists_A2_inf_fixed_eq
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K) (hq : 2 < Nat.card K) (κ : F4A2Kind)
    {m : ModGL Tag.F4 Ω} (hm : m ∈ monomialSubgroup Tag.F4 Ω) {w : WeylGroup Tag.F4}
    (hmw : MapsRootLines m w) {η δ : ℤ} (hη : η = 1 ∨ η = -1) (hδ : δ = 1 ∨ δ = -1)
    (hw : ∀ a ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)), w • (Pi.single a 1 : Fin Tag.F4.rank → ℤ) =
      η • ((simple Tag.F4 κ.i * simple Tag.F4 κ.j) ^ δ • (Pi.single a 1 : Fin Tag.F4.rank → ℤ)))
    (R : Subgroup (ModGL Tag.F4 Ω)) (hR : R = subsystemGroup Tag.F4 Ω {κ.i, κ.j} ⊓
      (twistedEntrywise m F).eqLocus (MonoidHom.id _)) :
    ∃ a ∈ subsystemGroup Tag.F4 Ω {κ.i, κ.j},
      (η = 1 → ∀ z, z ∈ R ↔ ∃ Y : SL(3, K), z = a *
        ((f4A2Equiv Ω κ).symm (SpecialLinearGroup.map (algebraMap K Ω) Y) : ModGL Tag.F4 Ω) *
          a⁻¹) ∧
      (η = -1 → ∀ z, z ∈ R ↔ ∃ X : SL(3, Ω),
        SpecialLinearGroup.toGL X ∈ Classical2.unitarySet (Nat.card K) 3 ∧
          z = a * ((f4A2Equiv Ω κ).symm X : ModGL Tag.F4 Ω) * a⁻¹) ∧
      CFSG.IsQuasisimple R ∧
      (∀ (g : subsystemGroup Tag.F4 Ω {κ.i, κ.j}) (hg : (g : ModGL Tag.F4 Ω) ∈ R),
        (⟨g, hg⟩ : R) ∈ Subgroup.center R ↔
          ∃ c : Ω, ((f4A2Equiv Ω κ g : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c) ∧
      Nat.card (Subgroup.center R) = Int.gcd 3 ((Nat.card K : ℤ) - η) ∧
      ∃ b₀ ∈ subsystemGroup Tag.F4 Ω {κ.i, κ.j}, ∀ Y : SL(2, K),
        b₀ * simpleRootSL2 Tag.F4 Ω κ.i (SpecialLinearGroup.map (algebraMap K Ω) Y) * b₀⁻¹ ∈ R := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  set Q := subsystemGroup Tag.F4 Ω {κ.i, κ.j} with hQ
  set r := f4A2Equiv Ω κ with hrdef
  obtain ⟨θQ, hθQ, π, b, hsplit, hunit⟩ := exists_A2_root_permuting K Ω F hF κ hm hmw hη hδ hw
  set Φ : SL(3, Ω) ≃* SL(3, Ω) := r.symm.trans (θQ.trans r) with hΦdef
  have hRQ : R ≤ Q := by
    rw [hR]
    exact inf_le_left
  have hmemR : ∀ g : Q, (g : ModGL Tag.F4 Ω) ∈ R ↔ r g ∈ CFSG.RankThree.Classical2.fixSubgroup Φ :=
    fun g => by
      rw [hR, CFSG.RankThree.Classical2.mem_fixSubgroup]
      have hΦg : Φ (r g) = r (θQ g) := by
        rw [hΦdef]
        change r (θQ (r.symm (r g))) = _
        rw [MulEquiv.symm_apply_apply]
      rw [hΦg]
      constructor
      · rintro ⟨-, hg⟩
        have hg' : twistedEntrywise m F g = g := hg
        rw [show θQ g = g from Subtype.ext ((hθQ g).trans hg')]
      · intro hg
        refine ⟨g.2, ?_⟩
        change twistedEntrywise m F g = g
        rw [← hθQ g, r.injective hg]
  set ι : R →* SL(3, Ω) := r.toMonoidHom.comp (Subgroup.inclusion hRQ) with hι
  have hιinj : Function.Injective ι := r.injective.comp (Subgroup.inclusion_injective hRQ)
  have hιrange : ι.range = CFSG.RankThree.Classical2.fixSubgroup Φ := by
    ext X
    constructor
    · rintro ⟨z, rfl⟩
      exact (hmemR (Subgroup.inclusion hRQ z)).1 z.2
    · intro hX
      have h1 : ((r.symm X : Q) : ModGL Tag.F4 Ω) ∈ R :=
        (hmemR (r.symm X)).2 (by rwa [MulEquiv.apply_symm_apply])
      refine ⟨⟨_, h1⟩, ?_⟩
      change r (Subgroup.inclusion hRQ ⟨_, h1⟩) = X
      rw [show Subgroup.inclusion hRQ ⟨_, h1⟩ = r.symm X from rfl, MulEquiv.apply_symm_apply]
  set e : R ≃* CFSG.RankThree.Classical2.fixSubgroup Φ :=
    (MonoidHom.ofInjective hιinj).trans (MulEquiv.subgroupCongr hιrange) with he
  have he_apply : ∀ (g : Q) (hg : (g : ModGL Tag.F4 Ω) ∈ R),
      ((e ⟨g, hg⟩ : CFSG.RankThree.Classical2.fixSubgroup Φ) : SL(3, Ω)) = r g := fun g hg => rfl
  have hcenter_e : ∀ z : R, z ∈ Subgroup.center R ↔
      e z ∈ Subgroup.center (CFSG.RankThree.Classical2.fixSubgroup Φ) := fun z => by
    simp only [Subgroup.mem_center_iff]
    constructor
    · intro h y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, h y']
    · intro h y
      apply e.injective
      rw [map_mul, map_mul, h (e y)]
  have hdesc : ∀ (P : SL(3, Ω) → Prop) (H : SL(3, Ω)),
      (∀ X, X ∈ CFSG.RankThree.Classical2.fixSubgroup Φ ↔ ∃ Y, P Y ∧ X = H * Y * H⁻¹) →
      ∀ z, z ∈ R ↔ ∃ Y, P Y ∧ z = ((r.symm H : Q) : ModGL Tag.F4 Ω) *
        ((r.symm Y : Q) : ModGL Tag.F4 Ω) * ((r.symm H : Q) : ModGL Tag.F4 Ω)⁻¹ := by
    intro P H hP z
    constructor
    · intro hz
      obtain ⟨Y, hY, hXY⟩ := (hP _).1 ((hmemR ⟨z, hRQ hz⟩).1 hz)
      refine ⟨Y, hY, ?_⟩
      have h1 : (⟨z, hRQ hz⟩ : Q) = r.symm H * r.symm Y * (r.symm H)⁻¹ := by
        apply r.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hXY]
      exact congrArg Subtype.val h1
    · rintro ⟨Y, hY, rfl⟩
      exact (hmemR (r.symm H * r.symm Y * (r.symm H)⁻¹)).2 ((hP _).2 ⟨Y, hY, by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]⟩)
  have hblock : ∀ J₀ : SL(3, Ω), (∀ Y : SL(2, K), J₀ *
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL Ω 2 1
        (SpecialLinearGroup.map (algebraMap K Ω) Y) : SL(3, Ω)) * J₀⁻¹ ∈
          CFSG.RankThree.Classical2.fixSubgroup Φ) →
      ∃ b₀ ∈ Q, ∀ Y : SL(2, K),
        b₀ * simpleRootSL2 Tag.F4 Ω κ.i (SpecialLinearGroup.map (algebraMap K Ω) Y) * b₀⁻¹ ∈ R := by
    intro J₀ hJ₀
    refine ⟨r.symm J₀, (r.symm J₀).2, fun Y => ?_⟩
    have h1 := (hmemR (r.symm J₀ * f4A2Iota Ω κ (SpecialLinearGroup.map (algebraMap K Ω) Y) *
      (r.symm J₀)⁻¹)).2 (by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hrdef, f4A2Equiv_f4A2Iota,
          ← blockSL_eq_sl2BlockDiag]
        exact hJ₀ Y)
    rw [← coe_f4A2Iota]
    exact h1
  have hcent : (∀ x : CFSG.RankThree.Classical2.fixSubgroup Φ,
      x ∈ Subgroup.center (CFSG.RankThree.Classical2.fixSubgroup Φ) ↔
        ∃ c : Ω, ((x : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c) →
      ∀ (g : Q) (hg : (g : ModGL Tag.F4 Ω) ∈ R), (⟨g, hg⟩ : R) ∈ Subgroup.center R ↔
        ∃ c : Ω, ((r g : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = scalar (Fin 3) c :=
    fun h g hg => by rw [hcenter_e, h, he_apply]
  have hcard : Nat.card (Subgroup.center R) =
      Nat.card (Subgroup.center (CFSG.RankThree.Classical2.fixSubgroup Φ)) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_iff_ne_zero.2 (pow_pos hℓ.pos f).ne'
  rcases hη with rfl | rfl
  · obtain ⟨-, ⟨H, hH⟩, ⟨J₀, hJ₀⟩, -, hQs, hcen, hcd, -⟩ :=
      CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_split hℓ hf hK π Φ b
        fun i j hij t => by rw [hsplit rfl i j hij t, hK]
    refine ⟨r.symm H, (r.symm H).2, fun _ z => ?_, fun h => absurd h (by decide),
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQs, hcent hcen, ?_, hblock J₀ hJ₀⟩
    · rw [hdesc (fun Y => ∃ Y' : SL(3, K), Y = SpecialLinearGroup.map (algebraMap K Ω) Y') H
        (fun X => by
          rw [hH X]
          constructor
          · rintro ⟨Y', rfl⟩
            exact ⟨_, ⟨Y', rfl⟩, rfl⟩
          · rintro ⟨_, ⟨Y', rfl⟩, rfl⟩
            exact ⟨Y', rfl⟩)]
      constructor
      · rintro ⟨_, ⟨Y', rfl⟩, rfl⟩
        exact ⟨Y', rfl⟩
      · rintro ⟨Y', rfl⟩
        exact ⟨_, ⟨Y', rfl⟩, rfl⟩
    · rw [hcard, hcd, hK]
      have e1 : ((ℓ ^ f : ℕ) : ℤ) - 1 = ((ℓ ^ f - 1 : ℕ) : ℤ) := by
        push_cast [hq1]
        ring
      rw [e1, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, Int.gcd_natCast_natCast]
  · obtain ⟨-, ⟨H, hH⟩, ⟨J₀, hJ₀⟩, -, hbig⟩ :=
      CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary hℓ hf hK π Φ b
        fun i j hij t => by rw [hunit rfl i j hij t, hK]
    obtain ⟨hQs, hcen, hcd, -⟩ := hbig (hK ▸ hq)
    refine ⟨r.symm H, (r.symm H).2, fun h => absurd h (by decide), fun _ z => ?_,
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQs, hcent hcen, ?_, hblock J₀ hJ₀⟩
    · rw [hK]
      refine hdesc (fun Y => SpecialLinearGroup.toGL Y ∈ Classical2.unitarySet (ℓ ^ f) 3) H
        (fun X => ?_) z
      rw [hH X]
      constructor
      · rintro ⟨Y, hY, hXY⟩
        have hdet : (Y : Matrix (Fin 3) (Fin 3) Ω).det = 1 := hY.2.1
        set Y' : SL(3, Ω) := ⟨(Y : Matrix (Fin 3) (Fin 3) Ω), hdet⟩ with hY'def
        have hY' : SpecialLinearGroup.toGL Y' = Y := Units.ext rfl
        refine ⟨Y', by rw [hY']; exact hY, ?_⟩
        apply SpecialLinearGroup.toGL_injective
        rw [hXY, map_mul, map_mul, map_inv, hY']
      · rintro ⟨Y, hY, rfl⟩
        exact ⟨_, hY, by rw [map_mul, map_mul, map_inv]⟩
    · rw [hcard, hcd, hK]
      have e1 : ((ℓ ^ f : ℕ) : ℤ) - -1 = ((ℓ ^ f + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [e1, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, Int.gcd_natCast_natCast]

end CFSG.RankThree.Chevalley
