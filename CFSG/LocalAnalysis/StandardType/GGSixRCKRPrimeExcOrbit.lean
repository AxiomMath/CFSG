module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRelOneAt
import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
import CFSG.RankThree.PartOne.KE.CTTorusFixed
import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag IsElemAbelian)

section Components

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem rck_mem_comp_of_iform_ne {i : KernelComponent χ} {α β : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) (hβ : β ∈ kernelRoots χ) (h : iform α β ≠ 0) :
    β ∈ componentRoots χ i := by
  obtain ⟨hαk, hαi⟩ := hα
  exact ⟨hβ, (mk_eq_of_iform_ne_zero (α := ⟨α, hαk⟩) (β := ⟨β, hβ⟩) h).symm.trans hαi⟩

theorem rck_iform_eq_zero_of_not_mem {i : KernelComponent χ} {α β : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) (hβ : β ∈ kernelRoots χ) (hβi : β ∉ componentRoots χ i) :
    iform α β = 0 := by
  by_contra h
  exact hβi (rck_mem_comp_of_iform_ne hα hβ h)

end Components

theorem rck_orbitLength_eq_one {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {Ψ : Set (Fin τ.rank → ℤ)} (hfin : Ψ.Finite) (hstab : ∀ α ∈ Ψ, ρ α ∈ Ψ) :
    componentOrbitLength ρ Ψ = 1 := by
  have hsub : ρ '' Ψ ⊆ Ψ := by
    rintro _ ⟨α, hα, rfl⟩
    exact hstab α hα
  have himg : ρ '' Ψ = Ψ := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
    rw [Set.ncard_image_of_injective _ ρ.injective]
  have h1 : 1 ∈ {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ} :=
    ⟨Nat.one_pos, by simpa using himg⟩
  unfold componentOrbitLength
  exact le_antisymm (Nat.sInf_le h1) (Nat.sInf_mem ⟨1, h1⟩).1

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem rck_rootDiagUnit_coord
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L) :
    rootDiagUnit τ (rckTorusCoord y) = y := by
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  have h : rootDiagUnitHom τ L a = y := ha.symm
  exact Function.invFun_eq (f := rootDiagUnitHom τ L) ⟨a, h⟩

theorem rck_coord_pow
    {p : ℕ} {y : ModGL τ L} (hy : y ∈ torusGroup τ L) (hyp : y ^ p = 1) (i : Fin τ.rank) :
    rckTorusCoord y i ^ p = 1 := by
  have h1 : rootDiagUnit τ (rckTorusCoord y ^ p) = rootDiagUnit τ 1 := by
    have hmap : rootDiagUnit τ (rckTorusCoord y ^ p) = rootDiagUnit τ (rckTorusCoord y) ^ p :=
      (rootDiagUnitHom τ L).map_pow (rckTorusCoord y) p
    have hone : rootDiagUnit τ (1 : Fin τ.rank → Lˣ) = 1 := (rootDiagUnitHom τ L).map_one
    rw [hmap, rck_rootDiagUnit_coord hy, hyp, hone]
  exact congrFun (rootDiagUnit_injective h1) i

theorem rck_conj_pow
    {p : ℕ} {x : ModGL τ L} (g : ModGL τ L) (hx : x ^ p = 1) :
    (g⁻¹ * x * g) ^ p = 1 := by
  have hconj := conj_pow (a := g⁻¹) (b := x) (i := p)
  rw [inv_inv] at hconj
  rw [hconj, hx]
  group

end Torus

theorem rck_famChar_apply
    {t : StatedLieTag} {Dl : LangDatum (langTag t) GGL} {ι : Type}
    (x : ι → ModGL (langTag t) GGL) (α : Fin (langTag t).rank → ℤ) (i : ι) :
    rckFamChar Dl.g0 x (Multiplicative.ofAdd α) i =
      rootChar (rckTorusCoord (Dl.g0⁻¹ * x i * Dl.g0)) α := rfl

theorem rck_kernel_stable
    {t : StatedLieTag} {Dl : LangDatum (langTag t) GGL}
    {ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)}
    (hρ : FrobRootMap Dl ρ) {ι : Type} (x : ι → ModGL (langTag t) GGL)
    (hx : ∀ i, Dl.g0⁻¹ * x i * Dl.g0 ∈ Dl.torus) {γ : Fin (langTag t).rank → ℤ}
    (hγ : γ ∈ kernelRoots (rckFamChar Dl.g0 x)) :
    ρ γ ∈ kernelRoots (rckFamChar Dl.g0 x) := by
  obtain ⟨hr, h1⟩ := hγ
  refine ⟨(hρ.isRoot_iff γ).2 hr, ?_⟩
  funext i
  have hT : Dl.g0⁻¹ * x i * Dl.g0 ∈ torusGroup (langTag t) GGL :=
    (mem_twistedTorusOf.1 (hx i)).1
  have hmem : rootDiagUnit (langTag t) (rckTorusCoord (Dl.g0⁻¹ * x i * Dl.g0)) ∈ Dl.torus := by
    rw [rck_rootDiagUnit_coord hT]
    exact hx i
  have h2 := hρ.rootChar_eq _ hmem γ hr
  have h3 := congrFun h1 i
  rw [rck_famChar_apply] at h3 ⊢
  rw [h2, h3]
  simp

theorem rck_dvd_of_orderOf_two {p f : ℕ} (hp : p.Prime)
    (h : orderOf ((2 ^ f : ℕ) : ZMod p) = 2) : p ∣ 2 ^ f + 1 := by
  haveI := Fact.mk hp
  have hsq : (((2 ^ f : ℕ) : ZMod p)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (((2 ^ f : ℕ) : ZMod p))
    rwa [h] at this
  have hne : ((2 ^ f : ℕ) : ZMod p) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at h
    omega
  have hcm : ((2 ^ f : ℕ) : ZMod p) = -1 := by
    have hmul : (((2 ^ f : ℕ) : ZMod p) - 1) * (((2 ^ f : ℕ) : ZMod p) + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.1 hmul with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hne
    · exact eq_neg_of_add_eq_zero_left h1
  have h0 : ((2 ^ f + 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_add, Nat.cast_one, hcm]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 h0

theorem rck_beta_mem_kernel
    {t : StatedLieTag} {Dl : LangDatum (langTag t) GGL}
    {ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)} {S : Subgroup (ModGL (langTag t) GGL)}
    {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : Dl.q = 2 ^ f)
    (hρ : FrobRootMap Dl ρ) (hdvd : p ∣ 2 ^ f + 1)
    (hSt : ∀ x ∈ S, Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) (hSp : ∀ x ∈ S, x ^ p = 1)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β) (hρβ : ρ β = β) :
    β ∈ kernelRoots (rckFamChar Dl.g0 (fun x : S => (x : ModGL (langTag t) GGL))) := by
  refine ⟨hβ, ?_⟩
  funext x
  rw [rck_famChar_apply]
  set y := Dl.g0⁻¹ * (x : ModGL (langTag t) GGL) * Dl.g0 with hy
  have hyT : y ∈ torusGroup (langTag t) GGL := (mem_twistedTorusOf.1 (hSt x x.2)).1
  have hmem : rootDiagUnit (langTag t) (rckTorusCoord y) ∈ Dl.torus := by
    rw [rck_rootDiagUnit_coord hyT]
    exact hSt x x.2
  have h1 := hρ.rootChar_eq _ hmem β hβ
  rw [hρβ, hq] at h1
  have hyp : y ^ p = 1 := rck_conj_pow Dl.g0 (hSp x x.2)
  have hcp : rootChar (rckTorusCoord y) β ^ p = 1 :=
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_pow_eq_one (rck_coord_pow hyT hyp) β
  obtain ⟨k, hk⟩ := hdvd
  set c := rootChar (rckTorusCoord y) β with hc
  have hc1 : c ^ (2 ^ f + 1) = 1 := by rw [hk, pow_mul, hcp, one_pow]
  have hc2 : c ^ 2 = 1 := by
    have h2 : c ^ (2 ^ f + 1) = c ^ (2 ^ f) * c := pow_succ _ _
    rw [h2, ← h1] at hc1
    rw [sq]
    exact hc1
  obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have hcm : c ^ p = c := by rw [hm, pow_succ, pow_mul, hc2, one_pow, one_mul]
  exact hcm.symm.trans hcp

theorem rck_comp_stable
    {t : StatedLieTag} {Dl : LangDatum (langTag t) GGL}
    {ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)} {S : Subgroup (ModGL (langTag t) GGL)}
    {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : Dl.q = 2 ^ f)
    (hρ : FrobRootMap Dl ρ)
    (hcl : RCKExcClassShape (langTag t) (orderOf ((2 ^ f : ℕ) : ZMod p)) ρ)
    (hd4 : orderOf ((2 ^ f : ℕ) : ZMod p) ≠ 4)
    (hSt : ∀ x ∈ S, Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) (hSp : ∀ x ∈ S, x ^ p = 1)
    (i : KernelComponent (rckFamChar Dl.g0 (fun x : S => (x : ModGL (langTag t) GGL)))) :
    ∀ α ∈ componentRoots (rckFamChar Dl.g0 (fun x : S => (x : ModGL (langTag t) GGL))) i,
      ρ α ∈ componentRoots (rckFamChar Dl.g0 (fun x : S => (x : ModGL (langTag t) GGL))) i := by
  intro α hα
  obtain ⟨h1, h2, h3, h4⟩ := hcl
  have hkr : ∀ γ ∈ kernelRoots (rckFamChar Dl.g0 (fun x : S => (x : ModGL (langTag t) GGL))),
      ρ γ ∈ kernelRoots (rckFamChar Dl.g0 (fun x : S => (x : ModGL (langTag t) GGL))) :=
    fun γ hγ => rck_kernel_stable hρ (fun x : S => (x : ModGL (langTag t) GGL))
      (fun x : S => hSt (x : ModGL (langTag t) GGL) x.2) hγ
  have hαk := hα.1
  have hαroot : IsRoot (langTag t) α := hαk.1
  have hρroot : IsRoot (langTag t) (ρ α) := (hρ.isRoot_iff α).2 hαroot
  have hcomp := isRootComponent_componentRoots
    (χ := rckFamChar Dl.g0 (fun x : S => (x : ModGL (langTag t) GGL))) i
  by_cases hd1 : orderOf ((2 ^ f : ℕ) : ZMod p) = 1
  · rw [h1 hd1 α hαroot]
    exact hα
  by_cases hd2 : orderOf ((2 ^ f : ℕ) : ZMod p) = 2
  · rcases h2 hd2 with hneg | ⟨β, hβ, hβρ⟩
    · rw [hneg α hαroot]
      exact hcomp.neg_mem α hα
    · have hself : rootReflection β • β = -β := by
        rw [rootReflection_smul hβ β]
        have hc : corootPair β β = 2 := by
          unfold corootPair
          exact Int.mul_ediv_cancel 2 (iform_self_pos_of_isRoot hβ).ne'
        rw [hc, two_smul]
        abel
      have hρβ : ρ β = β := by
        rw [hβρ β hβ, hself, neg_neg]
      have hβk := rck_beta_mem_kernel hp hp2 hq hρ (rck_dvd_of_orderOf_two hp hd2) hSt hSp hβ hρβ
      by_cases hβi : β ∈ componentRoots
          (rckFamChar Dl.g0 (fun x : S => (x : ModGL (langTag t) GGL))) i
      · rw [hβρ α hαroot]
        exact hcomp.neg_mem _ (hcomp.reflection_mem α hα β hβi)
      · have h0 : iform α β = 0 := rck_iform_eq_zero_of_not_mem hα hβk hβi
        have hfix : rootReflection β • α = α := by
          rw [rootReflection_smul hβ α]
          have hc : corootPair β α = 0 := by
            unfold corootPair
            rw [iform_comm β α, h0]
            simp
          rw [hc, zero_smul, sub_zero]
        rw [hβρ α hαroot, hfix]
        exact hcomp.neg_mem α hα
  · obtain ⟨hE8, hd⟩ := h4 hd1 hd2
    have hd36 : orderOf ((2 ^ f : ℕ) : ZMod p) = 3 ∨ orderOf ((2 ^ f : ℕ) : ZMod p) = 6 := by
      rcases hd with h | h | h
      · exact Or.inl h
      · exact absurd h hd4
      · exact Or.inr h
    have hrel := h3 ⟨hE8, hd⟩ α hαroot
    have hc0 : rckChebC (orderOf ((2 ^ f : ℕ) : ZMod p)) ≠ 0 := by
      rcases hd36 with h | h <;> rw [h] <;> simp [rckChebC]
    by_contra hnot
    have hβk := hkr α hαk
    have hγk := hkr _ hβk
    have h0 : iform α (ρ α) = 0 := rck_iform_eq_zero_of_not_mem hα hβk hnot
    have hposα := iform_self_pos_of_isRoot hαroot
    have hposβ := iform_self_pos_of_isRoot hρroot
    have hγα : iform (ρ (ρ α)) α ≠ 0 := by
      have h5 := congrArg (fun v => iform v α) hrel
      simp only [iform_add_left, iform_smul_left] at h5
      rw [iform_comm (ρ α) α, h0] at h5
      intro h6
      rw [h6] at h5
      omega
    have hγΨ := rck_mem_comp_of_iform_ne hα hγk (by rw [iform_comm]; exact hγα)
    have hγβ : iform (ρ (ρ α)) (ρ α) ≠ 0 := by
      have h5 := congrArg (fun v => iform v (ρ α)) hrel
      simp only [iform_add_left, iform_smul_left] at h5
      rw [h0] at h5
      intro h6
      rw [h6] at h5
      have : rckChebC (orderOf ((2 ^ f : ℕ) : ZMod p)) * iform (ρ α) (ρ α) = 0 := by omega
      rcases mul_eq_zero.1 this with h7 | h7
      · exact hc0 h7
      · omega
    exact hnot (rck_mem_comp_of_iform_ne hγΨ hβk hγβ)

theorem rckExcOrbit_of_ne_four
    {t : StatedLieTag} {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Dl : LangDatum (langTag t) GGL} {ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)}
    (hq : Dl.q = 2 ^ f) (hρ : FrobRootMap Dl ρ)
    (hcl : RCKExcClassShape (langTag t) (orderOf ((2 ^ f : ℕ) : ZMod p)) ρ)
    (hd4 : orderOf ((2 ^ f : ℕ) : ZMod p) ≠ 4)
    {S₁ S₂ : Subgroup (ModGL (langTag t) GGL)} (hS : S₂ ≤ S₁) (hel : IsElemAbelian p S₁)
    (htor : ∀ x ∈ S₁, Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus)
    (iJ : KernelComponent (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag t) GGL))))
    (iK : KernelComponent (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL)))) :
    componentOrbitLength ρ
        (componentRoots (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag t) GGL))) iJ) =
      componentOrbitLength ρ
        (componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL))) iK) := by
  have hSp : ∀ x ∈ S₁, x ^ p = 1 := hel.2
  have hJ := rck_orbitLength_eq_one
    ((finite_setOf_isRoot (langTag t)).subset fun α hα =>
      (isRootComponent_componentRoots iJ).isRoot α hα)
    (rck_comp_stable hp hp2 hq hρ hcl hd4 htor hSp iJ)
  have hK := rck_orbitLength_eq_one
    ((finite_setOf_isRoot (langTag t)).subset fun α hα =>
      (isRootComponent_componentRoots iK).isRoot α hα)
    (rck_comp_stable hp hp2 hq hρ hcl hd4 (fun x hx => htor x (hS hx))
      (fun x hx => hSp x (hS hx)) iK)
  rw [hJ, hK]

@[expose] def RCKExcOrbitFour : Prop :=
  ∀ (f p : ℕ), 1 ≤ f → p.Prime → p ≠ 2 → orderOf ((2 ^ f : ℕ) : ZMod p) = 4 →
    ∀ (Dl : LangDatum (langTag .E8) GGL) (ρ : Equiv.Perm (Fin (langTag .E8).rank → ℤ)),
      Dl.Φ = ggPhi .E8 f → FrobRootMap Dl ρ → RCKExcClassShape (langTag .E8) 4 ρ →
      ∀ (S₁ S₂ : Subgroup (ModGL (langTag .E8) GGL)), S₂ ≤ S₁ → IsElemAbelian p S₁ →
        (∀ x ∈ S₁, Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) → Nat.card S₁ = p ^ 2 → Nat.card S₂ = p →
        ∀ (iJ : KernelComponent (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag .E8) GGL))))
          (iK : KernelComponent (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag .E8) GGL)))),
          componentRoots (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag .E8) GGL))) iJ ⊆
            componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag .E8) GGL))) iK →
          RCKExcShape ρ
            (componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag .E8) GGL))) iK) →
          componentOrbitLength ρ
              (componentRoots (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag .E8) GGL))) iJ) =
            componentOrbitLength ρ
              (componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag .E8) GGL))) iK)

theorem rckExcOrbitAt_of_four
    (hqΦ : ∀ (t : StatedLieTag) (f : ℕ) (Dl : LangDatum (langTag t) GGL),
      Dl.Φ = ggPhi t f → Dl.q = 2 ^ f)
    (h4 : RCKExcOrbitFour) : RCKExcOrbitAt (fun t => t = .F4 ∨ t = .E7 ∨ t = .E8) := by
  intro t ht f p hf hp hp2 Dl ρ hΦ hρ hcl S₁ S₂ hS hel htor hc₁ hc₂ iJ iK hsub hshape
  by_cases hd4 : orderOf ((2 ^ f : ℕ) : ZMod p) = 4
  · have hE8 : langTag t = .E8 := (hcl.2.2.2 (by omega) (by omega)).1
    have ht8 : t = .E8 := by
      rcases ht with rfl | rfl | rfl <;> first | rfl | exact absurd hE8 (by decide)
    subst ht8
    rw [hd4] at hcl
    exact h4 f p hf hp hp2 hd4 Dl ρ hΦ hρ hcl S₁ S₂ hS hel htor hc₁ hc₂ iJ iK hsub hshape
  · exact rckExcOrbit_of_ne_four hp hp2 (hqΦ t f Dl hΦ) hρ hcl hd4 hS hel htor iJ iK

end CFSG.StandardType.RCKRP
