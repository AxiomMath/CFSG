module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGCentD4Alpha
public import CFSG.LocalAnalysis.StandardType.GGCentD4Fix
public import CFSG.LocalAnalysis.StandardType.GGCentD4RIdent
public import CFSG.LocalAnalysis.StandardType.GGCentD4Descent
public import CFSG.LocalAnalysis.StandardType.GGCentD4RatUntw
public import CFSG.LocalAnalysis.StandardType.GGCentD4RatTw
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import CFSG.LieType.Chevalley.SingleEdgePerfect

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.StandardType.Triality


theorem ntpD4_part_untw
    
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L) (hpair : OrderThreeOutsideConnected S a n)
    (i : KernelComponent (rootCharHom a)) (hi : ∀ j : KernelComponent (rootCharHom a), j = i)
    (hρker : ∀ γ ∈ rootCharKernel a, S.ρ γ ∈ rootCharKernel a)
    (K : Subgroup (ModGL .E6 L))
    (hRnorm : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj n).toMonoidHom =
      rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hRqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hKcomp : IsComponentOf K (rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓
      Subgroup.centralizer ({n} : Set (ModGL .E6 L))))
    (Y : Subgroup (ModGL .E6 L)) (hY : Y = rootSpan Tag.E6 L (rootCharKernel a))
    (hstepY : ∀ y ∈ Y, S.D.step y ∈ Y)
    (Ξ : ↥Y ≃* ↥(adjointGroup Tag.D4 L)) (g' : ↥(adjointGroup Tag.D4 L)) (ε : ℕ)
    (hε : ε = 1 ∨ ε = 2)
    {f : ℕ} (hf : 1 ≤ f) (hq : S.D.q = 2 ^ f) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f))
    (hΞstep : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : S.D.step y ∈ Y),
      (Ξ ⟨S.D.step y, hy'⟩ : ModGL Tag.D4 L) = Units.map (entrywiseHom Fr)
        (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L))
    (hΞn : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : n * y * n⁻¹ ∈ Y),
      Ξ ⟨n * y * n⁻¹, hy'⟩ = g' * d4Graph L ε (Ξ ⟨y, hy⟩) * g'⁻¹)
    (hcomm : ∀ x ∈ adjointGroup Tag.D4 L,
      Units.map (entrywiseHom Fr) ((g' : ModGL Tag.D4 L) * (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) *
        (g' : ModGL Tag.D4 L)⁻¹) =
      (g' : ModGL Tag.D4 L) * (d4P L ^ ε * Units.map (entrywiseHom Fr) x * (d4P L ^ ε)⁻¹) *
        (g' : ModGL Tag.D4 L)⁻¹) :
    NTPD4Labels (2 ^ f) K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F₀ : Subfield L := frobeniusFixedField L 2 f
  let F : Type := ↥F₀
  have hFcard : Nat.card F = 2 ^ f := by
    change Nat.card ↥(frobeniusFixedField L 2 f) = 2 ^ f
    exact card_frobeniusFixedField (k := L) (p := 2) (n := f) (by omega)
  haveI : Finite F :=
    Nat.finite_of_card_ne_zero (by rw [hFcard]; exact pow_ne_zero _ (by norm_num))
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hFcard
  set G₀ : Subgroup (ModGL Tag.D4 L) :=
    adjointGroup Tag.D4 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) with hG₀def
  have hG₀_eq : G₀ = adjointGroup Tag.D4 L ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := hG₀def
  have hG₀_mem : ∀ x : ModGL Tag.D4 L, x ∈ G₀ ↔
      x ∈ adjointGroup Tag.D4 L ∧
        d4P L ^ (0 : ℕ) * Units.map (entrywiseHom Fr) x * (d4P L ^ (0 : ℕ))⁻¹ = x := by
    intro x
    rw [hG₀def, Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, hx'⟩
      exact ⟨hx, by simpa using hx'⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨hx, by simpa using hx'⟩
  have hdesc : G₀ = (adjointGroup Tag.D4 F).map (baseChangeGL (algebraMap F L)) :=
    hG₀_eq.trans (ntpD4_descent_untwisted (f := f) hf (F := F) hFcard (L := L) Fr hFr)
  haveI : Group.IsPerfect ↥(adjointGroup Tag.D4 F) :=
    ⟨single_edge_perfect Tag.D4 F (Or.inr (Or.inl rfl))⟩
  have hperf : Group.IsPerfect ↥G₀ := by
    rw [hdesc]
    exact Group.IsPerfect.map (baseChangeGL (algebraMap F L))
  have hΞ0 : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : S.D.step y ∈ Y),
      (Ξ ⟨S.D.step y, hy'⟩ : ModGL Tag.D4 L) =
        d4P L ^ (0 : ℕ) * Units.map (entrywiseHom Fr) (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L) *
          (d4P L ^ (0 : ℕ))⁻¹ := by
    intro y hy hy'
    rw [hΞstep y hy hy']
    simp
  obtain ⟨hRleY, hRiff⟩ :=
    ntpD4_rident S a i hi hρker Y hY hstepY Ξ Fr 0 hΞ0 G₀ hG₀_mem hperf
  obtain ⟨e, γ, ε', hε', _hact, hval⟩ :=
    ntpD4_rat_untwisted (f := f) hf (F := F) hFcard (L := L) Fr hFr G₀ hG₀_eq hdesc
      g' ε hε hcomm
  let φ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →* ↥G₀ :=
    ((adjointGroup Tag.D4 L).subtype.comp (Ξ.toMonoidHom.comp
      (Subgroup.inclusion hRleY))).codRestrict
      G₀ (fun r => (hRiff r.1 (hRleY r.2)).1 r.2)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : (Ξ (Subgroup.inclusion hRleY a) : ModGL Tag.D4 L) =
        (Ξ (Subgroup.inclusion hRleY b) : ModGL Tag.D4 L) :=
      congrArg (fun t : ↥G₀ => (t : ModGL Tag.D4 L)) hab
    have h2 : (Ξ (Subgroup.inclusion hRleY a) : ↥(adjointGroup Tag.D4 L)) =
        Ξ (Subgroup.inclusion hRleY b) := Subtype.ext h1
    exact Subgroup.inclusion_injective hRleY (Ξ.injective h2)
  have hG₀le : G₀ ≤ adjointGroup Tag.D4 L := by
    rw [hG₀_eq]
    exact inf_le_left
  have hφsurj : Function.Surjective φ := by
    intro x
    have hxadj : (x : ModGL Tag.D4 L) ∈ adjointGroup Tag.D4 L := hG₀le x.2
    let x' : ↥(adjointGroup Tag.D4 L) := ⟨(x : ModGL Tag.D4 L), hxadj⟩
    obtain ⟨y, hy⟩ := Ξ.surjective x'
    have hΞy : (Ξ y : ModGL Tag.D4 L) = (x : ModGL Tag.D4 L) := by rw [hy]
    have hyR : (y : ModGL .E6 L) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
      rw [hRiff y.1 y.2]
      rw [show (Ξ ⟨y.1, y.2⟩ : ModGL Tag.D4 L) = (x : ModGL Tag.D4 L) from hΞy]
      exact x.2
    refine ⟨⟨y.1, hyR⟩, ?_⟩
    apply Subtype.ext
    show (Ξ (Subgroup.inclusion hRleY ⟨y.1, hyR⟩) : ModGL Tag.D4 L) =
      (x : ModGL Tag.D4 L)
    have hinc : Subgroup.inclusion hRleY ⟨y.1, hyR⟩ = y := Subtype.ext rfl
    rw [hinc]
    exact hΞy
  let eR : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃* Om8 F :=
    (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).trans e
  have hnR : ∀ r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      n * r * n⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro r hr
    have hm : (MulAut.conj n) r ∈
        (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hr
    rw [hRnorm] at hm
    simpa only [MulAut.conj_apply] using hm
  have hn3 : n ^ 3 = 1 := hpair.2.2.2.2.1
  have hγ : ∃ (γ : Om8 F) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      ∀ r : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
        eR ⟨n * r * n⁻¹, hnR r r.2⟩ =
          (MulAut.conj γ * theta ^ ε : MulAut (Om8 F)) (eR r) := by
    refine ⟨γ, ε', hε', fun r => ?_⟩
    change e (φ ⟨n * r * n⁻¹, hnR r r.2⟩) =
      (MulAut.conj γ * theta ^ ε' : MulAut (Om8 F)) (e (φ r))
    refine hval (φ r) (φ ⟨n * r * n⁻¹, hnR r r.2⟩) ?_
    have hmem : n * r.1 * n⁻¹ ∈ Y := hRleY (hnR r.1 r.2)
    have hinc : Subgroup.inclusion hRleY ⟨n * r * n⁻¹, hnR r r.2⟩ =
        ⟨n * r.1 * n⁻¹, hmem⟩ := Subtype.ext rfl
    calc (φ ⟨n * r * n⁻¹, hnR r r.2⟩ : ModGL Tag.D4 L)
        = (Ξ (Subgroup.inclusion hRleY ⟨n * r * n⁻¹, hnR r r.2⟩) :
            ModGL Tag.D4 L) := rfl
      _ = (Ξ ⟨n * r.1 * n⁻¹, hmem⟩ : ModGL Tag.D4 L) :=
            congrArg (fun t : ↥Y => (Ξ t : ModGL Tag.D4 L)) hinc
      _ = ((g' * d4Graph L ε (Ξ ⟨r.1, hRleY r.2⟩) * g'⁻¹ : ↥(adjointGroup Tag.D4 L)) :
            ModGL Tag.D4 L) := congrArg Subtype.val (hΞn r.1 (hRleY r.2) hmem)
      _ = (g' : ModGL Tag.D4 L) * (d4P L ^ ε *
            (φ r : ModGL Tag.D4 L) * (d4P L ^ ε)⁻¹) * (g' : ModGL Tag.D4 L)⁻¹ := rfl
  exact ntpD4_fix_untwisted (F := F) (f₀ := f) (X := ModGL .E6 L) hFcard hf
    (rationalComponent S.ρ S.Γ (rootCharHom a) i) n hnR hn3 eR hγ K hKcomp

end CFSG.StandardType.NTPlane

end
