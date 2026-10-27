module

public import CFSG.RankThree.GF2n.Smith81.S81YGenDef
public import CFSG.RankThree.GF2n.Smith81.S81LV0
public import CFSG.RankThree.GF2n.Smith81.S81R213Basic
public import CFSG.RankThree.GF2n.Smith81.S81TBridge

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGen

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E3LBridge CFSG.RankThree.GF2n.Smith81.E3LCond
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.MinuscT
open scoped commutatorElement

variable {G : Type} [Group G]

section Pure

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {V : Type} [AddCommGroup V]
  [Module K V] {ψ : M₀.E ≃ₗ[K] V} {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)}
  {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)}
  {IsRt : (V ≃ₗ[K] V) → Prop} {z : G}

theorem isPure_of_isConj_gen (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) (Hs : StrothHyp M Q Z)
    {z a : G} (hz : z ∈ Z) (hza : IsConj z a) (haQ : a ∈ Q) (haZ : a ∉ Z) :
    IsPurePt Γ p₀ (ψ (M₀.π a)) := by
  have hζ0 : ψ (M₀.π a) ≠ 0 := fun h => haZ ((M₀.π_ker a haQ).mp (ψ.map_eq_zero_iff.mp h))
  obtain ⟨g, hg⟩ := isConj_iff.mp hza
  have haA : a ∈ conjSubgroup g Z := by
    rw [mem_conjSubgroup, ← hg]
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [e]
    exact hz
  have hAZ : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Z.one_mem)
  have hAQ : conjSubgroup g Z ≤ Q := by
    have := IsZConjugate.le_QB_of_mem Hs (IsZConjugate.self Z) hAZ ha1 haA
      (by rw [Hs.QB_Z]; exact haQ)
    rwa [Hs.QB_Z] at this
  have hAne : conjSubgroup g Z ≠ Z := fun e => haZ (e ▸ haA)
  obtain ⟨g₀, hg₀, himg, -⟩ := d.point _ hAZ hAQ hAne
  have hmem : ψ (M₀.π a) ∈ ((Submodule.span K {g₀ p₀} : Submodule K V) : Set V) := by
    rw [← himg]
    exact ⟨a, haA, rfl⟩
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨g₀, hg₀, s, ?_, hs.symm⟩
  rintro rfl
  apply hζ0
  rw [← hs, zero_smul]

theorem isConj_of_isPure_gen (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) (Hs : StrothHyp M Q Z)
    (hg : GlobalModelData M Q Z γ M₀) {z a : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (haQ : a ∈ Q)
    (haZ : a ∉ Z) (hpure : IsPurePt Γ p₀ (ψ (M₀.π a))) : IsConj z a := by
  have hζ0 : ψ (M₀.π a) ≠ 0 := fun h => haZ ((M₀.π_ker a haQ).mp (ψ.map_eq_zero_iff.mp h))
  obtain ⟨g₁, hg₁, c, -, hc⟩ := hpure
  have hroot := MinuscT.rootPt_of_orbit d Hs (v := ψ (M₀.π a)) hζ0 ⟨g₁, hg₁, c, hc⟩
  rw [LinearEquiv.symm_apply_apply] at hroot
  rcases hroot with h0 | ⟨A, hAZ, hAQ, -, a₁, ha₁A, hπ⟩
  · exact absurd ((M₀.π_ker a haQ).mp h0) haZ
  have ha₁Q : a₁ ∈ Q := hAQ ha₁A
  have hz₀ : a₁⁻¹ * a ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ ha₁Q haQ).mp hπ
  have ha₁Z : a₁ ∉ Z := fun h =>
    haZ ((M₀.π_ker a haQ).mp (by rw [← hπ]; exact (M₀.π_ker a₁ ha₁Q).mpr h))
  have ha₁1 : a₁ ≠ 1 := fun h => ha₁Z (h ▸ Z.one_mem)
  obtain ⟨g₂, hg₂⟩ := hAZ
  have hconj₁ : IsConj z a₁ := isConj_of_mem_conj Hs hz hz1 (g := g₂) (hg₂ ▸ ha₁A) ha₁1
  obtain ⟨q, hqQ, hq⟩ := exists_comm_eq_of_mem_Q hg ha₁Q ha₁Z hz₀
  have hZcent : ∀ y ∈ Z, ∀ w ∈ Q, w * y = y * w := fun y hy w hw => by
    have hy' : y ∈ Subgroup.centralizer (Q : Set G) := by rw [Hs.centralizer_Q]; exact hy
    exact Subgroup.mem_centralizer_iff.mp hy' w hw
  have hqa : q * a₁ * q⁻¹ = a := by
    have h1 : q * a₁ * q⁻¹ * a₁⁻¹ = a₁⁻¹ * a := by rw [← hq, commutatorElement_def]
    have h2 : a₁ * (a₁⁻¹ * a) = (a₁⁻¹ * a) * a₁ := hZcent _ hz₀ a₁ ha₁Q
    calc q * a₁ * q⁻¹ = (q * a₁ * q⁻¹ * a₁⁻¹) * a₁ := by group
      _ = (a₁⁻¹ * a) * a₁ := by rw [h1]
      _ = a₁ * (a₁⁻¹ * a) := h2.symm
      _ = a := by group
  exact hconj₁.trans (isConj_iff.mpr ⟨q, hqa⟩)

theorem concl_Q_left_gen (Dt : GDat M Q Z B K γ M₀ ψ φ Γ p₀ U₀ IsRt z) {x y : G}
    (hxc : IsConj z x) (hxQ : x ∈ Q) (hyc : IsConj z y) (hyM : y ∈ M) (hyQ : y ∉ Q) :
    (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
      (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2)) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  obtain ⟨r, hr, hrRt⟩ := Dt.acts_root hyc hyM hyQ
  obtain ⟨hyL, hyφ⟩ := hr
  have hyy : y * y = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hyc
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hyxQ : y * x * y⁻¹ ∈ Q := conj_mem_Q H hyM hxQ
  have hcQ : x * (y * x * y⁻¹) ∈ Q := Q.mul_mem hxQ hyxQ
  have hsq2 : (x * y) ^ 2 = x * (y * x * y⁻¹) := by rw [pow_two, hyinv]; group
  have hneg : ∀ v : V, -v = v := fun v => by
    have h2 : (2 : K) • v = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    rw [two_smul] at h2
    exact neg_eq_of_add_eq_zero_left h2
  have hψc : ψ (M₀.π (x * (y * x * y⁻¹))) = r (ψ (M₀.π x)) - ψ (M₀.π x) := by
    have hev : ψ (M₀.π (y * x * y⁻¹)) = r (ψ (M₀.π x)) := by
      have h := Dt.d.equivariant ⟨y, hyL⟩ x hxQ
      rw [hyφ] at h
      exact h
    rw [M₀.π_mul x hxQ _ hyxQ, map_add, hev, sub_eq_add_neg, hneg, add_comm]
  have hpure : ψ (M₀.π (x * (y * x * y⁻¹))) = 0 ∨
      IsPurePt Γ p₀ (ψ (M₀.π (x * (y * x * y⁻¹)))) := by
    rw [hψc]
    by_cases hxZ : x ∈ Z
    · left
      simp [(M₀.π_ker x hxQ).mpr hxZ]
    · exact Dt.mrf.pure_sub r hrRt _ (isPure_of_isConj_gen Dt.d H Dt.hz hxc hxQ hxZ)
  have hcl : (x * y) ^ 2 = 1 ∨ InZClass Z ((x * y) ^ 2) := by
    rw [hsq2]
    by_cases h0 : M₀.π (x * (y * x * y⁻¹)) = 0
    · have hcZ : x * (y * x * y⁻¹) ∈ Z := (M₀.π_ker _ hcQ).mp h0
      by_cases hc1 : x * (y * x * y⁻¹) = 1
      · exact Or.inl hc1
      · exact Or.inr ⟨1, _, hcZ, hc1, by group⟩
    · have hcZ : x * (y * x * y⁻¹) ∉ Z := fun h => h0 ((M₀.π_ker _ hcQ).mpr h)
      have hpc : IsPurePt Γ p₀ (ψ (M₀.π (x * (y * x * y⁻¹)))) :=
        hpure.resolve_left (fun h => h0 (ψ.map_eq_zero_iff.mp h))
      have hconj := isConj_of_isPure_gen Dt.d H Dt.hD Dt.hz Dt.hz1 hcQ hcZ hpc
      exact Or.inr (CFSG.RankThree.GF2n.Smith81.E3LRoot.inZClass_of_isConj Dt.hz Dt.hz1 hconj)
  have hsqsq : ((x * y) ^ 2) * ((x * y) ^ 2) = 1 := by
    rcases hcl with h | h
    · rw [h, one_mul]
    · exact InZClass.mul_self H h
  refine lin213_of_pow_four (by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two]; exact hsqsq) fun hne => ?_
  rcases hcl with h | h
  · exact absurd h hne
  · exact h

end Pure

end CFSG.RankThree.GF2n.Smith81.RootGen
