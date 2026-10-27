module

public import CFSG.RankThree.PartOne.CTP.SeitzOrthPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedCentralizer

public section

namespace CFSG.RankThree.PartOne.CTP

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_anisotropic_of_nondegenerate (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V] :
    ∃ a : V, Q a ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  apply hu
  apply eq_zero_of_polar_eq_zero hQ
  intro v
  rw [polar, h, h, h, sub_zero, sub_zero]

theorem sq_eq_one_of_mem_scalars (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs : g ∈ scalars K V) :
    g ^ 2 = 1 := by
  obtain ⟨a₀, ha₀⟩ := exists_anisotropic_of_nondegenerate hQ
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  have h1 := map_of_mem hg a₀
  rw [hc, map_smul_eq_sq] at h1
  have hc2 : c ^ 2 = 1 := by
    have : (c ^ 2 - 1) * Q a₀ = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right ha₀)
  apply LinearEquiv.ext
  intro v
  rw [pow_two, LinearEquiv.mul_apply, hc, hc, smul_smul, ← pow_two, hc2, one_smul]
  rfl

theorem scalarKernel_data (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    [Finite (V ≃ₗ[K] V)] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker ≤
        Subgroup.center (orthDerived Q) ∧
      Nat.Coprime (Nat.card (QuotientGroup.mk' ((scalars K V).subgroupOf
        (orthDerived Q))).ker) p := by
  set Z := (scalars K V).subgroupOf (orthDerived Q) with hZ
  have hΩO : ∀ g ∈ orthDerived Q, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    orthDerived_le_orthogonalGroup Q hg
  have hZc : (QuotientGroup.mk' Z).ker ≤ Subgroup.center (orthDerived Q) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_mem_scalars (Subgroup.mem_subgroupOf.mp hz) g).symm
  have hZsq : ∀ z : Z, z ^ 2 = 1 := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    exact sq_eq_one_of_mem_scalars hQ (hΩO _ (z : orthDerived Q).2)
      (Subgroup.mem_subgroupOf.mp z.2)
  refine ⟨hZc, ?_⟩
  rw [QuotientGroup.ker_mk', Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) p hdvd
  have h2 := orderOf_dvd_of_pow_eq_one (hZsq z)
  rw [hz] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem isElemAbelian_map_subtype {p : ℕ} (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1) :
    Assembly.IsElemAbelian p (E.map (orthDerived Q).subtype) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show (a : V ≃ₗ[K] V) * b = b * a
    exact congrArg (fun y : orthDerived Q => (y : V ≃ₗ[K] V)) (hcomm a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩
    show ((a : orthDerived Q) : V ≃ₗ[K] V) ^ p = 1
    have h := congrArg (fun y : orthDerived Q => (y : V ≃ₗ[K] V)) (hexp a ha)
    simpa using h

section Data

variable [Finite K] [FiniteDimensional K V] [Nontrivial V]

theorem exists_kernelLineData_of_le (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    KernelLineData Q p E ∧ 2 * Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ≤ finrank K V := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : (ringChar K).Prime :=
    (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
      (CharP.char_ne_zero_of_finite K (ringChar K))
  have : CharP K (ringChar K) := ringChar.charP K
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    DFunLike.coe_injective
  obtain ⟨hZc, hZp⟩ := scalarKernel_data hQ hp hp2
  set ρ : orthDerived Q →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  have hinj : ∀ x ∈ E, ∀ y ∈ E, ρ x = ρ y → x = y := fun x hx y hy hxy =>
    eq_of_map_eq_of_pow_eq_one_of_coprime ρ hZc hZp (a := 1) (b := 1)
      (by rw [pow_one]; exact hexp x hx) (by rw [pow_one]; exact hexp y hy) hxy
  set A : Subgroup (ProjOrthDerived Q) := E.map ρ with hA
  have hAcomm : IsMulCommutative A := ⟨⟨by
    rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    exact Subtype.ext (by
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, hcomm x hx y hy])⟩⟩
  have hAexp : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hAel : Assembly.IsElemAbelian p A := ⟨hAcomm, hAexp⟩
  have hAcard : Nat.card A = p ^ 2 := by
    let f : E →* A := (ρ.comp E.subtype).codRestrict A fun x => ⟨x, x.2, rfl⟩
    have hf : Function.Bijective f := by
      refine ⟨fun x y hxy => Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy)), ?_⟩
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    rw [← hcard]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  obtain ⟨Ã, -, -, e, he, huniq, hint, horth, hnd, -, hex2, -, hlcm, -, hζ⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition hℓ hp hp2 hpl Q hQ A hAel hAcard
  have hEle : E ≤ Ã := by
    intro x hx
    have hxA : ρ x ∈ A := ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := e.surjective ⟨ρ x, hxA⟩
    have hy1 : ρ (y : orthDerived Q) = ρ x := by
      rw [← he y]
      exact congrArg Subtype.val hy
    have hy2 : (y : orthDerived Q) ^ p = 1 := by
      have h : e (y ^ p) = 1 := by
        rw [map_pow]
        exact Subtype.ext (by simpa using hAexp _ (e y).2)
      have h' : y ^ p = 1 := e.injective (by rw [h, map_one])
      have := congrArg (fun z : Ã => (z : orthDerived Q)) h'
      simpa using this
    obtain ⟨z, -, hzu⟩ := huniq (ρ x) hxA
    have h1 := hzu x ⟨rfl, hexp x hx⟩
    have h2 := hzu y ⟨hy1, hy2⟩
    rw [h1, ← h2]
    exact y.2
  have hEeq : Ã = E := by
    refine (Subgroup.eq_of_le_of_card_ge hEle ?_).symm
    rw [hcard, Nat.card_congr e.toEquiv, hAcard]
  subst hEeq
  refine ⟨⟨fun x y => Subtype.ext (hcomm _ x.2 _ y.2), hcard, fun x => Subtype.ext (hexp _ x.2),
    hint, horth, hnd, hex2, fun ζ hζ' => (hζ ζ hζ').2⟩, hlcm⟩

end Data

theorem orthCentralizerSpan_eq_map (Ã : Subgroup (orthDerived Q)) :
    orthCentralizerSpan Q Ã =
      (Subgroup.closure {h : orthDerived Q | ∃ x ∈ Ã, x ≠ 1 ∧ h * x = x * h}).map
        (orthDerived Q).subtype := by
  have hset : (orthDerived Q).subtype '' {h : orthDerived Q | ∃ x ∈ Ã, x ≠ 1 ∧ h * x = x * h} =
      {g : V ≃ₗ[K] V | g ∈ orthDerived Q ∧
        ∃ x ∈ Ã.map (orthDerived Q).subtype, x ≠ 1 ∧ g * x = x * g} := by
    ext g
    constructor
    · rintro ⟨h, ⟨x, hx, hx1, hhx⟩, rfl⟩
      exact ⟨h.2, x.1, ⟨x, hx, rfl⟩, fun h' => hx1 (Subtype.ext h'), congrArg Subtype.val hhx⟩
    · rintro ⟨hg, _, ⟨x, hx, rfl⟩, hx1, hgx⟩
      exact ⟨⟨g, hg⟩, ⟨x, hx, fun h => hx1 (congrArg Subtype.val h), Subtype.ext hgx⟩, rfl⟩
  rw [MonoidHom.map_closure, hset]
  rfl

theorem closure_centralizers_eq_top_of_le (Ã : Subgroup (orthDerived Q))
    (h : orthDerived Q ≤ orthCentralizerSpan Q Ã) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ Ã, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  rw [orthCentralizerSpan_eq_map] at h
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨g', hg', hgg'⟩ := h g.2
  have : g' = g := Subtype.ext hgg'
  exact this ▸ hg'

theorem orthDerived_le_orthCentralizerSpan_of_iSup (Ã : Subgroup (orthDerived Q))
    (h : (⨆ (x : V ≃ₗ[K] V) (_ : x ∈ Ã.map (orthDerived Q).subtype ∧ x ≠ 1),
        derivedCentralizer (orthDerived Q) x) = orthDerived Q) :
    orthDerived Q ≤ orthCentralizerSpan Q Ã := by
  rw [← h]
  refine iSup_le fun x => iSup_le fun hx => ?_
  have hmem : ∀ g ∈ orthDerived Q ⊓ Subgroup.centralizer {x}, g ∈ orthCentralizerSpan Q Ã := by
    intro g hg
    refine Subgroup.subset_closure ⟨hg.1, x, hx.1, hx.2, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hg.2
  refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem g₁ hg₁) (hmem g₂ hg₂))
    (Subgroup.inv_mem _ (hmem g₁ hg₁))) (Subgroup.inv_mem _ (hmem g₂ hg₂))

end CFSG.RankThree.PartOne.CTP
