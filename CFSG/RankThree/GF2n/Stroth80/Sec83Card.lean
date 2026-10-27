module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs
public import CFSG.ClassicalGroups.Alternating.PointRadicalCard
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

theorem card_mul_card_isOppDecomp {G : Type} [Group G] [Finite G]
    {P I L₁ L₂ A₁ A₂ : Subgroup G} (h : IsOppDecomp P I L₁ L₂ A₁ A₂) :
    Nat.card P * Nat.card I = Nat.card A₁ * Nat.card A₂ := by
  obtain ⟨hI1, hA1P, -, hA2P, hsup, hinf, hcomm, -, -, -⟩ := h
  have hnorm : A₂ ≤ Subgroup.normalizer A₁ := by
    refine Subgroup.le_normalizer_iff.mpr fun y hy a ha => ?_
    have hc : ⁅y, a⁆ ∈ A₁ := hI1 (hcomm y (hA2P hy) a (hA1P ha))
    have key : y * a * y⁻¹ = ⁅y, a⁆ * a := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact A₁.mul_mem hc ha
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hsup, hinf] at hcard
  exact hcard

theorem card_mul_card_of_isChiIso {G : Type} [Group G] [Finite G] {Q R K₀ U T₀ : Subgroup G} {t : G}
    (h : IsChiIso Q R K₀ U T₀ t) (hK : K₀ ≤ Q) (hTU : T₀ ≤ U) [hN : (T₀.subgroupOf U).Normal] :
    Nat.card Q * Nat.card T₀ = Nat.card K₀ * Nat.card U := by
  unfold IsChiIso at h
  obtain ⟨c1, c2, c3, c4, -⟩ := h
  obtain ⟨ch, hch⟩ : ∃ ch : Q → U, ∀ x : Q, ((ch x : U) : G) = ⁅(x : G), t⁆ :=
    ⟨fun x => ⟨⁅(x : G), t⁆, c1 (x : G) x.2⟩, fun x => rfl⟩
  have hnorm : ∀ p q : U, (q : G) * (p : G)⁻¹ ∈ T₀ → q⁻¹ * p ∈ T₀.subgroupOf U := by
    intro p q hqp
    have hpq : p * q⁻¹ ∈ T₀.subgroupOf U := by
      rw [Subgroup.mem_subgroupOf]
      simpa using T₀.inv_mem hqp
    exact hN.mem_comm_iff.1 hpq
  obtain ⟨χ, hχ⟩ : ∃ χ : Q →* U ⧸ T₀.subgroupOf U,
      ∀ x : Q, χ x = QuotientGroup.mk (ch x) := by
    refine ⟨MonoidHom.mk' (fun x : Q => QuotientGroup.mk (ch x)) ?_, fun x => rfl⟩
    intro x y
    try dsimp only
    rw [← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.2 (hnorm (ch x * ch y) (ch (x * y)) ?_)
    simp only [hch, Subgroup.coe_mul]
    exact c3 (x : G) x.2 (y : G) y.2
  have hker : χ.ker = K₀.subgroupOf Q := by
    ext x
    simp only [MonoidHom.mem_ker, hχ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hch]
    exact c4 (x : G) x.2
  have hsurj : Function.Surjective χ := by
    intro z
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨x, hxQ, hx⟩ := c2 (u : G) u.2
    refine ⟨⟨x, hxQ⟩, ?_⟩
    rw [hχ]
    refine QuotientGroup.eq.2 (hnorm u (ch ⟨x, hxQ⟩) ?_)
    rw [hch]
    exact hx
  have hidx : χ.ker.index = Nat.card (U ⧸ T₀.subgroupOf U) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective χ hsurj).toEquiv
  have hcard : Nat.card χ.ker = Nat.card K₀ := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hQ : Nat.card K₀ * Nat.card (U ⧸ T₀.subgroupOf U) = Nat.card Q := by
    have hcm := Subgroup.card_mul_index χ.ker
    rw [hidx, hcard] at hcm
    exact hcm
  have hU : Nat.card (U ⧸ T₀.subgroupOf U) * Nat.card T₀ = Nat.card U := by
    have hcm := Subgroup.card_mul_index (T₀.subgroupOf U)
    rw [Subgroup.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTU).toEquiv] at hcm
    rw [mul_comm]
    exact hcm
  rw [← hQ, ← hU]
  ring

theorem card_of_naturalRep {G : Type} [Group G] [Finite G] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {X : Subgroup (GL ι K)} {R V Z N : Subgroup G}
    (h : NaturalRep K X R V Z N) (hZV : Z ≤ V) (hK : Nat.card K = Nat.card Z) :
    Nat.card V = Nat.card Z * Nat.card Z ^ Fintype.card ι := by
  obtain ⟨φ, -, -, -, hN, ψ, -⟩ := h
  haveI := hN
  have hcardQ : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card Z ^ Fintype.card ι := by
    rw [Nat.card_congr ψ.toEquiv,
      show Nat.card (Multiplicative (ι → K)) = Nat.card (ι → K) from rfl,
      Nat.card_fun, hK, Nat.card_eq_fintype_card (α := ι)]
  have hcardZ : Nat.card (Z.subgroupOf V) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V), hcardQ, hcardZ,
    mul_comm]

theorem card_inf_mul_card_map {G H : Type*} [Group G] [Group H] [Finite G] {R N L : Subgroup G}
    (hLR : L ≤ R) (φ : ↥R →* H) (hker : φ.ker = N.subgroupOf R) :
    Nat.card ↥(L ⊓ N) * Nat.card ↥((L.subgroupOf R).map φ) = Nat.card ↥L := by
  let ψ : ↥(L.subgroupOf R) →* H := φ.comp (L.subgroupOf R).subtype
  have hrange : ψ.range = (L.subgroupOf R).map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerEq : Nat.card ψ.ker = Nat.card ↥(L ⊓ N) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ψ.ker => (⟨((x : ↥(L.subgroupOf R)) : ↥R).1, ?_⟩ : ↥(L ⊓ N))) ⟨?_, ?_⟩)
    · have h1 : (((x : ↥(L.subgroupOf R)) : ↥R) : G) ∈ L :=
        Subgroup.mem_subgroupOf.mp (x : ↥(L.subgroupOf R)).2
      have h2 : ((x : ↥(L.subgroupOf R)) : ↥R) ∈ φ.ker := by
        have := x.2
        rwa [MonoidHom.mem_ker] at this ⊢
      rw [hker] at h2
      exact ⟨h1, Subgroup.mem_subgroupOf.mp h2⟩
    · intro x y hxy
      have := congrArg (fun z : ↥(L ⊓ N) => (z : G)) hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    · rintro ⟨y, hyL, hyN⟩
      have hyR : y ∈ R := hLR hyL
      refine ⟨⟨⟨⟨y, hyR⟩, Subgroup.mem_subgroupOf.mpr hyL⟩, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker]
      show φ ⟨y, hyR⟩ = 1
      rw [← MonoidHom.mem_ker, hker]
      exact Subgroup.mem_subgroupOf.mpr hyN
  have h1 : Nat.card (↥(L.subgroupOf R)) = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLR).toEquiv, hrange, hkerEq] at h1
  rw [h1, mul_comm]

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.ClassicalGroups.Alternating

theorem card_LspGL {m : ℕ} {K : Type} [Field K] [Finite K] {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) :
    Nat.card (LspGL m K u) = Nat.card K ^ (2 * m - 1) := by
  have hL : Nat.card (LspGL m K u) = Nat.card (Lsp (spForm m K) spForm_isAlt u) := by
    rw [LspGL, Subgroup.card_subtype, Subgroup.comap_equiv_eq_map_symm']
    exact Subgroup.card_map_of_injective (f := (spEquiv (m := m) (K := K)).symm.toMonoidHom)
      (spEquiv (m := m) (K := K)).symm.injective
  have hle := pointRadical_le_bilinIsometryGroup (spForm_isAlt (m := m) (K := K)) u
  have h1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [card_pointRadical (spForm_isAlt (m := m) (K := K))
    (spForm_nondegenerate (m := m) (K := K)) hu, finrank_spSpace] at h1
  rw [hL]
  exact h1

end CFSG.ClassicalGroups.Symplectic
