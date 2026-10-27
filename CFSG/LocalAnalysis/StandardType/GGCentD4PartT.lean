module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGCentD4Alpha
public import CFSG.LocalAnalysis.StandardType.GGCentD4Fix
public import CFSG.LocalAnalysis.StandardType.GGCentD4RIdent
public import CFSG.LocalAnalysis.StandardType.GGCentD4RatTw

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

private noncomputable def d4pt_frobPowEquiv {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2] (n : ℕ) : K ≃+* K :=
  RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨(iterateFrobenius K 2 n).injective,
      Finite.surjective_of_injective (iterateFrobenius K 2 n).injective⟩

private theorem d4pt_frobPowEquiv_apply {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2] (n : ℕ) (c : K) :
    d4pt_frobPowEquiv (K := K) n c = c ^ 2 ^ n := by
  change iterateFrobenius K 2 n c = c ^ 2 ^ n
  exact iterateFrobenius_def 2 n c

private theorem d4pt_not_inner {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (c : G → G) (φ : MulAut H) (hrel : ∀ g : G, e (c g) = φ (e g))
    (hout : φ ∉ (MulAut.conj : H →* MulAut H).range) :
    ¬ ∃ r₀ : G, ∀ g : G, c g = r₀ * g * r₀⁻¹ := by
  rintro ⟨r₀, hr₀⟩
  apply hout
  refine ⟨e r₀, MulEquiv.ext fun y => ?_⟩
  obtain ⟨g, rfl⟩ := e.surjective y
  calc MulAut.conj (e r₀) (e g) = e r₀ * e g * (e r₀)⁻¹ := by rw [MulAut.conj_apply]
    _ = e (r₀ * g * r₀⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = e (c g) := by rw [hr₀ g]
    _ = φ (e g) := hrel g

theorem ntpD4_part_tw
    
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
    (r : ℕ) (hr : r = 1 ∨ r = 2)
    (hΞstep : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : S.D.step y ∈ Y),
      (Ξ ⟨S.D.step y, hy'⟩ : ModGL Tag.D4 L) = d4P L ^ r * Units.map (entrywiseHom Fr)
        (Ξ ⟨y, hy⟩ : ModGL Tag.D4 L) * (d4P L ^ r)⁻¹)
    (hΞn : ∀ (y : ModGL .E6 L) (hy : y ∈ Y) (hy' : n * y * n⁻¹ ∈ Y),
      Ξ ⟨n * y * n⁻¹, hy'⟩ = g' * d4Graph L ε (Ξ ⟨y, hy⟩) * g'⁻¹)
    (hcomm : ∀ x ∈ adjointGroup Tag.D4 L,
      d4P L ^ r * Units.map (entrywiseHom Fr) ((g' : ModGL Tag.D4 L) * (d4P L ^ ε * x *
        (d4P L ^ ε)⁻¹) * (g' : ModGL Tag.D4 L)⁻¹) * (d4P L ^ r)⁻¹ =
      (g' : ModGL Tag.D4 L) * (d4P L ^ ε * (d4P L ^ r * Units.map (entrywiseHom Fr) x *
        (d4P L ^ r)⁻¹) * (d4P L ^ ε)⁻¹) * (g' : ModGL Tag.D4 L)⁻¹) :
    NTPD4Labels (2 ^ f) K := by
  classical
  haveI hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K₃ : Subfield L := frobeniusFixedField L 2 (3 * f)
  have hK₃two : ((2 : ℕ) : K₃) = 0 := by
    apply (algebraMap K₃ L).injective
    push_cast
    exact CharP.cast_eq_zero L 2
  haveI hcharK₃ : CharP K₃ 2 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 hK₃two
  have hK₃ : Nat.card K₃ = (2 ^ f) ^ 3 := by
    change Nat.card (frobeniusFixedField L 2 (3 * f)) = (2 ^ f) ^ 3
    rw [card_frobeniusFixedField (k := L) (p := 2) (n := 3 * f) (by omega),
      show 2 ^ (3 * f) = (2 ^ f) ^ 3 by rw [mul_comm 3 f, pow_mul]]
  haveI hfinK₃ : Finite K₃ :=
    Nat.finite_of_card_ne_zero (by rw [hK₃]; exact pow_ne_zero _ (pow_ne_zero _ (by norm_num)))
  let σ : K₃ ≃+* K₃ := d4pt_frobPowEquiv (K := K₃) (f * r)
  have hσ : ∀ c : K₃, σ c = c ^ (((2 : ℕ) ^ f) ^ r) := by
    intro c
    change d4pt_frobPowEquiv (K := K₃) (f * r) c = _
    rw [d4pt_frobPowEquiv_apply, pow_mul]
  let H₀ : Subgroup (ModGL Tag.D4 K₃) := graphFixedRootGroup TwistTag.D4 K₃ σ.toRingHom
  let G₀ : Subgroup (ModGL Tag.D4 L) := H₀.map (baseChangeGL (algebraMap K₃ L))
  have hfs := fixedSet_D4_eq_map_baseChangeGL (ℓ := 2) (d := f) Nat.prime_two hf
    (K := K₃) hK₃ (Ω := L) r hr σ.toRingHom hσ Fr hFr
  have hG₀ : ∀ x : ModGL Tag.D4 L, x ∈ G₀ ↔
      x ∈ adjointGroup Tag.D4 L ∧
        d4P L ^ r * Units.map (entrywiseHom Fr) x * (d4P L ^ r)⁻¹ = x := by
    intro x
    have hx := Set.ext_iff.1 hfs x
    exact hx.symm
  let eG0' : ↥H₀ ≃* ↥G₀ :=
    Subgroup.equivMapOfInjective H₀ (baseChangeGL (algebraMap K₃ L))
      (baseChangeGL_injective (algebraMap K₃ L))
  have hsimple := CFSG.RankThree.PartOne.KD4L.isSimple_graphFixedRootGroup_triality
    (ℓ := 2) (d := f) Nat.prime_two hf (K := K₃) hK₃ r hr σ.toRingHom hσ
  have hperfH : Group.IsPerfect ↥H₀ := by
    rw [Group.isPerfect_def]
    obtain ⟨hsimp, hnab⟩ := hsimple
    haveI : IsSimpleGroup ↥H₀ := hsimp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥H₀) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h
      exact hxy (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top x)) y
        (Subgroup.mem_top y)).symm
    · exact h
  haveI : Group.IsPerfect ↥H₀ := hperfH
  have hperfG : Group.IsPerfect ↥G₀ :=
    Group.IsPerfect.ofSurjective (f := eG0'.toMonoidHom) eG0'.surjective
  let R : Subgroup (ModGL .E6 L) := rationalComponent S.ρ S.Γ (rootCharHom a) i
  have hRdef : R = rationalComponent S.ρ S.Γ (rootCharHom a) i := rfl
  have hrid := ntpD4_rident S a i hi hρker Y hY hstepY Ξ Fr r hΞstep G₀ hG₀ hperfG
  have hn3 : n ^ 3 = 1 := hpair.2.2.2.2.1
  have hnR : ∀ r ∈ R, n * r * n⁻¹ ∈ R := by
    intro r hr
    change n * r * n⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i
    rw [← hRnorm]
    refine ⟨r, hr, ?_⟩
    show MulAut.conj n r = n * r * n⁻¹
    rw [MulAut.conj_apply]
  have hG₀le : G₀ ≤ adjointGroup Tag.D4 L := fun x hx => ((hG₀ x).1 hx).1
  have hmap : (R.subgroupOf Y).map Ξ.toMonoidHom =
      G₀.subgroupOf (adjointGroup Tag.D4 L) := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hrid.2 y.1 y.2).1 hy
    · intro hg
      have hg' : ((g : ModGL Tag.D4 L)) ∈ G₀ := Subgroup.mem_subgroupOf.mp hg
      refine ⟨Ξ.symm g, ?_, Ξ.apply_symm_apply g⟩
      exact (hrid.2 (Ξ.symm g).1 (Ξ.symm g).2).2 (by simpa using hg')
  let eR0 : ↥R ≃* ↥(G₀.subgroupOf (adjointGroup Tag.D4 L)) :=
    (Subgroup.subgroupOfEquivOfLe hrid.1).symm.trans
      ((Subgroup.equivMapOfInjective (R.subgroupOf Y) Ξ.toMonoidHom Ξ.injective).trans
        (MulEquiv.subgroupCongr hmap))
  let eR0' : ↥R ≃* ↥G₀ := eR0.trans (Subgroup.subgroupOfEquivOfLe hG₀le)
  let eG0 : ↥G₀ ≃* ↥H₀ := eG0'.symm
  let e₀ : ↥R ≃* ↥H₀ := eR0'.trans eG0
  have heR0 : ∀ r : ↥R,
      (eR0' r).1 = (Ξ ⟨r.1, hrid.1 r.2⟩ : ModGL Tag.D4 L) := fun _ => rfl
  have hcoe : ∀ r : ↥R, baseChangeGL (algebraMap K₃ L) (e₀ r).1 = (eR0' r).1 := by
    intro r
    change baseChangeGL (algebraMap K₃ L) ((eG0'.symm (eR0' r)).1) = (eR0' r).1
    exact congrArg Subtype.val (eG0'.apply_symm_apply (eR0' r))
  obtain ⟨φ, hφbase, hφout⟩ :=
    ntpD4_rat_twisted (f := f) hf hK₃ r hr σ hσ Fr hFr g' ε hε hcomm
  have hkey₀ : ∀ r : ↥R, e₀ ⟨n * r * n⁻¹, hnR r r.2⟩ = φ (e₀ r) := by
    intro r
    apply Subtype.ext
    apply (baseChangeGL_injective (algebraMap K₃ L))
    rw [hcoe ⟨n * r * n⁻¹, hnR r r.2⟩, hφbase (e₀ r), hcoe r]
    rw [heR0 ⟨n * r * n⁻¹, hnR r r.2⟩, heR0 r]
    have hΞn' := congrArg Subtype.val
      (hΞn r.1 (hrid.1 r.2) (hrid.1 (⟨n * r * n⁻¹, hnR r r.2⟩ : ↥R).2))
    rw [hΞn']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_d4Graph]
  have hout₀ : ¬ ∃ r₀ : ↥R, ∀ r : ↥R,
      (⟨n * r * n⁻¹, hnR r r.2⟩ : ↥R) = r₀ * r * r₀⁻¹ :=
    d4pt_not_inner e₀ (fun r => ⟨n * r * n⁻¹, hnR r r.2⟩) φ hkey₀ hφout
  rcases hr with rfl | rfl
  · exact ntpD4_fix_triality (f₀ := f) hf hK₃ σ (fun c => by rw [hσ c, pow_one])
      R n hnR hn3 e₀ hout₀ K hKcomp
  · let Frq : K₃ ≃+* K₃ := d4pt_frobPowEquiv (K := K₃) f
    have hFrq : ∀ c : K₃, Frq c = c ^ (2 ^ f) := by
      intro c
      change d4pt_frobPowEquiv (K := K₃) f c = _
      rw [d4pt_frobPowEquiv_apply]
    let H₁ : Subgroup (ModGL Tag.D4 K₃) := graphFixedRootGroup TwistTag.D4 K₃ Frq.toRingHom
    open CFSG.HardMathSupport.Dickson.DefCharOuter.Export in
    obtain ⟨ψ⟩ : Nonempty (↥H₀ ≃* ↥H₁) :=
      exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4
        (K := K₃) (q := 2 ^ f) hK₃ σ Frq hσ hFrq
    let φ₁ : MulAut ↥H₁ := MulAut.congr ψ φ
    have hout₁ : φ₁ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥H₁ := by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr ψ]
      rintro ⟨a, ha, hconj⟩
      have haφ : a = φ :=
        (MulAut.congr ψ).injective (show (MulAut.congr ψ) a = (MulAut.congr ψ) φ from hconj)
      rw [haφ] at ha
      exact hφout ha
    let e₁ : ↥R ≃* ↥H₁ := e₀.trans ψ
    have hkey₁ : ∀ r : ↥R, e₁ ⟨n * r * n⁻¹, hnR r r.2⟩ = φ₁ (e₁ r) := by
      intro r
      change ψ (e₀ ⟨n * r * n⁻¹, hnR r r.2⟩) = (MulAut.congr ψ φ) (ψ (e₀ r))
      rw [hkey₀ r]
      show ψ (φ (e₀ r)) = (φ.trans ψ) (ψ.symm (ψ (e₀ r)))
      rw [MulEquiv.symm_apply_apply]
      rfl
    have hout₁' : ¬ ∃ r₀ : ↥R, ∀ r : ↥R,
        (⟨n * r * n⁻¹, hnR r r.2⟩ : ↥R) = r₀ * r * r₀⁻¹ :=
      d4pt_not_inner e₁ (fun r => ⟨n * r * n⁻¹, hnR r r.2⟩) φ₁ hkey₁ hout₁
    exact ntpD4_fix_triality (f₀ := f) hf hK₃ Frq hFrq R n hnR hn3 e₁ hout₁' K hKcomp

end CFSG.StandardType.NTPlane

end
