module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreG1c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma114Layer

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.HallHigman
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem pSolv3_of_le_hom {X Y : Type} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (S : Subgroup X) (hker : IsPSolvable 3 ↥f.ker) (him : IsPSolvable 3 ↥(S.map f)) :
    IsPSolvable 3 ↥S := by
  set g : ↥S →* Y := f.comp S.subtype with hg
  have hker' : g.ker = f.ker.subgroupOf S := by
    ext s
    simp [hg, Subgroup.mem_subgroupOf]
  have hrange : g.range = S.map f := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 : IsPSolvable 3 ↥(f.ker ⊓ S) := isPSolvable_of_le hker inf_le_left
  have h2 : (f.ker.subgroupOf S).map S.subtype = f.ker ⊓ S := Subgroup.subgroupOf_map_subtype _ _
  rw [← h2] at h1
  have h3 : IsPSolvable 3 ↥(f.ker.subgroupOf S) :=
    isPSolvable_of_mulEquiv
      ((f.ker.subgroupOf S).equivMapOfInjective S.subtype S.subtype_injective).symm h1
  refine pSolv3_of_normal g.ker (by rw [hker']; exact h3) ?_
  exact isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivRange g).symm
    (by rw [hrange]; exact him)

theorem coprime_lift {D₀ Q : Subgroup G} (hQD : Q ≤ D₀) (hQ : IsPGroup 3 Q) {x : G} (hx : x ∈ D₀)
    (hh : ∀ q ∈ Q, q⁻¹ * x⁻¹ * q * x ∈ Opp 3 D₀) :
    ∃ o ∈ Opp 3 D₀, x * o⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : ∀ y ∈ pPrimeCore 3 ↥D₀, ¬ 3 ∣ orderOf y := fun y hy => by
    have hdvd : orderOf y ∣ Nat.card (pPrimeCore 3 ↥D₀) := Subgroup.orderOf_dvd_natCard _ hy
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 3)))
  haveI : (pPrimeCore 3 ↥D₀).Normal := CFSG.pPrimeCore_normal
  obtain ⟨o, ho, hc⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma114Layer.cz_centralizer (p := 3)
      (O := pPrimeCore 3 ↥D₀) (Q := Q.subgroupOf D₀) hO hQ.comap_subtype
      (h := (⟨x, hx⟩ : ↥D₀)) (by
        intro q' hq'
        have hq : (q' : G) ∈ Q := hq'
        obtain ⟨o', ho', hoe⟩ := Subgroup.mem_map.1 (hh q' hq)
        have : q'⁻¹ * (⟨x, hx⟩ : ↥D₀)⁻¹ * q' * ⟨x, hx⟩ = o' :=
          Subtype.ext (by simpa using hoe.symm)
        rw [this]; exact ho')
  refine ⟨(o : G), Subgroup.mem_map.2 ⟨o, ho, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have := (Subgroup.mem_centralizer_iff.1 hc) ⟨q, hQD hq⟩ hq
  exact congrArg Subtype.val this

theorem J₁_cen_lift (hb₂ : IsPGroup 3 (Subgroup.zpowers b₂)) {D₀ J₁ J₂ : Subgroup G}
    (hJ₁ : J₁ ≤ D₀) (hJ₂ : J₂ ≤ D₀) (hn₁ : ∀ g ∈ D₀, ∀ x ∈ J₁, g * x * g⁻¹ ∈ J₁)
    (hn₂ : ∀ g ∈ D₀, ∀ x ∈ J₂, g * x * g⁻¹ ∈ J₂) (hP₂J₂ : Subgroup.zpowers b₂ ≤ J₂)
    (hJO : J₁ ⊓ J₂ ≤ Opp 3 D₀) :
    ∀ x ∈ J₁, ∃ o ∈ Opp 3 D₀, x * o⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers b₂ : Set G) := by
  intro x hx
  refine coprime_lift (hP₂J₂.trans hJ₂) hb₂ (hJ₁ hx) ?_
  intro q hq
  have hqJ₂ : q ∈ J₂ := hP₂J₂ hq
  have hqD : q ∈ D₀ := hJ₂ hqJ₂
  have h1 : q⁻¹ * x⁻¹ * q * x ∈ J₁ := by
    have := hn₁ q⁻¹ (inv_mem hqD) x⁻¹ (inv_mem hx)
    rw [inv_inv] at this
    exact mul_mem this hx
  have h2 : q⁻¹ * x⁻¹ * q * x ∈ J₂ := by
    have := hn₂ x⁻¹ (inv_mem (hJ₁ hx)) q hqJ₂
    rw [inv_inv] at this
    have e : q⁻¹ * x⁻¹ * q * x = q⁻¹ * (x⁻¹ * q * x) := by group
    rw [e]
    exact mul_mem (inv_mem hqJ₂) this
  exact hJO ⟨h1, h2⟩

theorem J₁_psolv (h : FF84Sec4 b L B K b₁ b₂) (hA : A8Model L)
    {D₀ J₁ J₂ : Subgroup G} (hDD : D₀ ≤ Cen (b * b₁)) (hJ₁ : J₁ ≤ D₀) (hJ₂ : J₂ ≤ D₀)
    (hn₁ : ∀ g ∈ D₀, ∀ x ∈ J₁, g * x * g⁻¹ ∈ J₁) (hn₂ : ∀ g ∈ D₀, ∀ x ∈ J₂, g * x * g⁻¹ ∈ J₂)
    (hP₂J₂ : Subgroup.zpowers b₂ ≤ J₂) (hJO : J₁ ⊓ J₂ ≤ Opp 3 D₀) :
    IsPSolvable 3 ↥J₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb₂ : IsPGroup 3 (Subgroup.zpowers b₂) :=
    isPGroup_zpowers (p := 3) (k := 1) (by simpa using pow3_of_mem h (mem_b₂ h))
  have hlift := J₁_cen_lift hb₂ hJ₁ hJ₂ hn₁ hn₂ hP₂J₂ hJO
  set O' := pPrimeCore 3 ↥D₀ with hO'
  haveI : O'.Normal := CFSG.pPrimeCore_normal
  set f : ↥D₀ →* ↥D₀ ⧸ O' := QuotientGroup.mk' O' with hf
  set C' : Subgroup ↥D₀ := (D₀ ⊓ Cen b₂).subgroupOf D₀ with hC'
  have hC'solv : IsPSolvable 3 ↥C' := by
    let g : ↥C' →* ↥(Cen (b * b₁) ⊓ Cen b₂) :=
      { toFun := fun x => ⟨(x : ↥D₀), Subgroup.mem_inf.2
          ⟨hDD x.1.2, (Subgroup.mem_inf.1 x.2).2⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hg : Function.Injective g := by
      intro x y hxy
      have h1 : ((g x : ↥(Cen (b * b₁) ⊓ Cen b₂)) : G) = ((g y : ↥(Cen (b * b₁) ⊓ Cen b₂)) : G) :=
        congrArg Subtype.val hxy
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    exact pSolv3_of_injective g hg (pSolv3_G1 h hA)
  have hker : IsPSolvable 3 ↥f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    exact pSolv3_of_coprime (CFSG.pPrimeCore_coprime_card (p := 3))
  have hsub : (J₁.subgroupOf D₀).map f ≤ C'.map f := by
    rintro _ ⟨x', hx', rfl⟩
    obtain ⟨o, ho, hc⟩ := hlift (x' : G) hx'
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.1 ho
    refine ⟨x' * o'⁻¹, ?_, ?_⟩
    · show ((x' * o'⁻¹ : ↥D₀) : G) ∈ D₀ ⊓ Cen b₂
      refine Subgroup.mem_inf.2 ⟨(x' * o'⁻¹).2, ?_⟩
      have := Subgroup.mem_centralizer_iff.1 hc b₂ (Subgroup.mem_zpowers b₂)
      exact Subgroup.mem_centralizer_singleton_iff.2 (by simpa using this.symm)
    · have : f o' = 1 := (QuotientGroup.eq_one_iff o').2 ho'
      simp [map_mul, map_inv, this]
  have hHsolv : IsPSolvable 3 ↥((J₁.subgroupOf D₀)) :=
    pSolv3_of_le_hom f _ hker (isPSolvable_of_le (isPSolvable_map f hC'solv) hsub)
  exact isPSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ₁) hHsolv

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
