module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvE7
public import CFSG.LocalAnalysis.StandardType.FS81.CanonPos
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxStruct
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeylTypes
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoBstar
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {G : Type} [Group G] [Finite G]

theorem e7_inner
    {K : Subgroup G} (hrow : IsRow Row.E7 K) (hKz : Subgroup.center K = ⊥) (ψ : MulAut ↥K) :
    ∃ y : ↥K, ∀ x : ↥K, ψ x = y * x * y⁻¹ := by
  obtain ⟨lab, hlabP, hlab⟩ := exists_glaLabel hrow
  obtain ⟨t, r, n⟩ := lab
  have hn1 : n = 1 := hlabP.1
  subst hn1
  have ht : t = .E7 := by
    obtain ⟨-, hcases⟩ := hlabP
    rcases hcases with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hKz
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  obtain ⟨y', hy'⟩ :=
    TableBExcTwo.mem_range_conj_adjoint (Or.inl rfl) hGF (φ.symm.trans (ψ.trans φ))
  refine ⟨φ.symm y', fun x => φ.injective ?_⟩
  have h1 := congrArg (fun χ : MulAut _ => χ (φ x)) hy'
  simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem e7_isSimpleGroup {K : Subgroup G} (hrow : IsRow Row.E7 K) (hKz : Subgroup.center K = ⊥) :
    IsSimpleGroup ↥K := by
  obtain ⟨-, -, -, R, _, -, -, θ, hR, -, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists hrow
  have e0 : ↥K ≃* ↥K ⧸ Subgroup.center ↥K :=
    ((QuotientGroup.quotientMulEquivOfEq hKz).trans QuotientGroup.quotientBot).symm
  exact @MulEquiv.isSimpleGroup _ _ _ _ hR (e0.trans θ)

theorem e7_noOffenderA
    {b₀ : G} {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.E7)
    (htr : TransvAll b₀ K E) : NoOffenderA b₀ K E := by
  classical
  obtain ⟨-, ⟨⟨-, hKC, hKn, hKz, -, -, -, -⟩, -, -, -, -, -⟩, hrow, -, -, hEKmax, hEKcard, -⟩ :=
    hstd
  set A := E ⊓ K with hA
  have hAK : A ≤ K := inf_le_right
  have hKnorm : ∀ g ∈ Subgroup.centralizer ({b₀} : Set G), ∀ y ∈ K, g * y * g⁻¹ ∈ K :=
    fun g hg y hy => Subgroup.mem_subgroupOf.mp
      (hKn.conj_mem ⟨y, hKC hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩)
  have hcA : ∀ c ∈ Subgroup.centralizer ({b₀} : Set G), c ∈ Subgroup.normalizer (E : Set G) →
      ∀ a, a ∈ A ↔ c * a * c⁻¹ ∈ A := by
    intro c hc hcN a
    constructor
    · intro ha
      exact ⟨(Subgroup.mem_normalizer_iff.mp hcN a).mp ha.1, hKnorm c hc a ha.2⟩
    · intro ha
      have h1 := hKnorm c⁻¹ (Subgroup.inv_mem _ hc) _ ha.2
      have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) _).mp ha.1
      rw [show c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a by group] at h1 h2
      exact ⟨h2, h1⟩
  have hlift : ∀ c ∈ Subgroup.centralizer ({b₀} : Set G),
      ∃ y ∈ K, ∀ x ∈ K, c * x * c⁻¹ = y * x * y⁻¹ := by
    intro c hc
    let ψ : MulAut ↥K :=
      { toFun := fun x => ⟨c * x * c⁻¹, hKnorm c hc x x.2⟩
        invFun := fun x => ⟨c⁻¹ * x * c, by simpa using hKnorm c⁻¹ (Subgroup.inv_mem _ hc) x x.2⟩
        left_inv := fun x => Subtype.ext (show c⁻¹ * (c * (x : G) * c⁻¹) * c = x by group)
        right_inv := fun x => Subtype.ext (show c * (c⁻¹ * (x : G) * c) * c⁻¹ = x by group)
        map_mul' := fun x y => Subtype.ext
          (show c * ((x : G) * y) * c⁻¹ = c * x * c⁻¹ * (c * y * c⁻¹) by group) }
    obtain ⟨y, hy⟩ := e7_inner hrow hKz ψ
    exact ⟨y, y.2, fun x hx => congrArg Subtype.val (hy ⟨x, hx⟩)⟩
  have hyf : ∀ f ∈ Subgroup.normalizer (E : Set G), b₀⁻¹ * (f * b₀ * f⁻¹) ∈ A →
      ∃ y ∈ K, (∀ a ∈ K, a ∈ A ↔ y * a * y⁻¹ ∈ A) ∧ ∀ a ∈ A, f * a * f⁻¹ = y * a * y⁻¹ := by
    intro f hfN hfb
    obtain ⟨t, htN, htA, htb⟩ := htr.2 _ hfb
    have hcN : t⁻¹ * f ∈ Subgroup.normalizer (E : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) hfN
    have hcb : t⁻¹ * f * b₀ * (t⁻¹ * f)⁻¹ = b₀ := by
      have h1 : f * b₀ * f⁻¹ = t * b₀ * t⁻¹ := by rw [htb, mul_inv_cancel_left]
      rw [show t⁻¹ * f * b₀ * (t⁻¹ * f)⁻¹ = t⁻¹ * (f * b₀ * f⁻¹) * t by group, h1]
      group
    have hcC : t⁻¹ * f ∈ Subgroup.centralizer ({b₀} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff.mp hx]
        exact (mul_inv_eq_iff_eq_mul.mp hcb).symm
    obtain ⟨y, hyK, hy⟩ := hlift _ hcC
    refine ⟨y, hyK, fun a ha => ?_, fun a ha => ?_⟩
    · rw [← hy a ha]
      exact hcA _ hcC hcN a
    · have h1 : t⁻¹ * f * a * (t⁻¹ * f)⁻¹ ∈ A := (hcA _ hcC hcN a).mp ha
      calc f * a * f⁻¹ = t * (t⁻¹ * f * a * (t⁻¹ * f)⁻¹) * t⁻¹ := by group
        _ = t⁻¹ * f * a * (t⁻¹ * f)⁻¹ := htA _ h1
        _ = y * a * y⁻¹ := hy a ha.2
  have hEm : IsEm 7 (⊤ : Subgroup ↥K) :=
    largeEvenMarking_of_mulEquiv Subgroup.topEquiv (fs81_isEm_seven_of_isRow_E7 hrow)
  have hsK : IsSimpleGroup ↥K := e7_isSimpleGroup hrow hKz
  have hAel : IsElemAbelian 3 (A.subgroupOf K) := hEKmax.2.1.subgroupOf K
  have hAc : Nat.card ↥(A.subgroupOf K) = 3 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
    exact hEKcard
  obtain ⟨π, φ, -, -, hφ⟩ := tmStruct_E7 ↥K hEm hsK (A.subgroupOf K) hAel hAc
  have hmemN : ∀ {y : G} (hy : y ∈ K), (∀ a ∈ K, a ∈ A ↔ y * a * y⁻¹ ∈ A) →
      (⟨y, hy⟩ : ↥K) ∈ Subgroup.normalizer ((A.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    intro y hy hiff
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hiff h h.2
  let ι : ↥A → ↥(A.subgroupOf K) := fun a => ⟨⟨a, hAK a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩
  let κ : ↥A → (Fin Tag.E7.rank → ZMod 3) := fun a => Multiplicative.toAdd (φ (ι a))
  have hκinj : Function.Injective κ := fun a b h => by
    have h1 := φ.injective (Multiplicative.toAdd.injective h)
    exact Subtype.ext (congrArg (fun z : ↥(A.subgroupOf K) => ((z : ↥K) : G)) h1)
  have hκsurj : Function.Surjective κ := fun v => by
    refine ⟨⟨((φ.symm (Multiplicative.ofAdd v) : ↥K) : G),
      Subgroup.mem_subgroupOf.mp (φ.symm (Multiplicative.ofAdd v)).2⟩, ?_⟩
    show Multiplicative.toAdd (φ (ι _)) = v
    rw [show ι ⟨_, Subgroup.mem_subgroupOf.mp (φ.symm (Multiplicative.ofAdd v)).2⟩ =
      φ.symm (Multiplicative.ofAdd v) from rfl, MulEquiv.apply_symm_apply]
    rfl
  have hκconj : ∀ (y : ↥(Subgroup.normalizer ((A.subgroupOf K : Subgroup ↥K) : Set ↥K))) (a : ↥A)
      (ha : ((y : ↥K) : G) * a * ((y : ↥K) : G)⁻¹ ∈ A),
      κ ⟨_, ha⟩ = TableBExc.torusAct .E7 3 (π y) (κ a) := by
    intro y a ha
    have h1 := hφ y (ι a)
    have h2 : (A.subgroupOf K).normalizerMonoidHom y (ι a) = ι ⟨_, ha⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [h2] at h1
    show Multiplicative.toAdd (φ (ι ⟨_, ha⟩)) = _
    rw [h1, show φ (ι a) = Multiplicative.ofAdd (κ a) from rfl, ExcWeylOuter.torusMulAut_apply]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWinj : ∀ w w' : WeylGroup Tag.E7, (∀ a : ↥A, TableBExc.torusAct .E7 3 w (κ a) =
      TableBExc.torusAct .E7 3 w' (κ a)) → w = w' := by
    intro w w' h
    apply ExcWeylOuter.torusMulAut_injective (τ := .E7) (by norm_num : (3 : ℕ) ≠ 2)
    ext v
    obtain ⟨a, ha⟩ := hκsurj (Multiplicative.toAdd v)
    have hv : v = Multiplicative.ofAdd (κ a) := by
      rw [ha]
      rfl
    rw [hv, ExcWeylOuter.torusMulAut_apply, ExcWeylOuter.torusMulAut_apply, h a]
  intro F hFN hF hFb hFA
  set CA := Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) with hCA
  choose yf hyfK hyfN hyfa using fun f : ↥F => hyf f (hFN f.2) (hFb f f.2)
  let ŷ : ↥F → ↥(Subgroup.normalizer ((A.subgroupOf K : Subgroup ↥K) : Set ↥K)) :=
    fun f => ⟨⟨yf f, hyfK f⟩, hmemN (hyfK f) (hyfN f)⟩
  have hfA : ∀ (f : ↥F) (a : ↥A), (f : G) * a * (f : G)⁻¹ ∈ A := fun f a => by
    rw [hyfa f a a.2]
    exact (hyfN f a (hAK a.2)).mp a.2
  have hρact : ∀ (f : ↥F) (a : ↥A),
      κ ⟨_, hfA f a⟩ = TableBExc.torusAct .E7 3 (π (ŷ f)) (κ a) := by
    intro f a
    have hya : ((ŷ f : ↥K) : G) * a * ((ŷ f : ↥K) : G)⁻¹ ∈ A := (hyfN f a (hAK a.2)).mp a.2
    rw [← hκconj (ŷ f) a hya]
    congr 1
    exact Subtype.ext (hyfa f a a.2)
  let ρ : ↥F →* WeylGroup Tag.E7 :=
    { toFun := fun f => π (ŷ f)
      map_one' := hWinj _ _ fun a => by
        rw [← hρact 1 a, TableBExc.torusAct_one]
        congr 1
        exact Subtype.ext (by simp)
      map_mul' := fun f g => hWinj _ _ fun a => by
        rw [TableBExc.torusAct_mul, ← hρact g a, ← hρact f, ← hρact (f * g) a]
        congr 1
        exact Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hρ : ∀ (f : ↥F) (a : ↥A), κ ⟨_, hfA f a⟩ = TableBExc.torusAct .E7 3 (ρ f) (κ a) := hρact
  set U := ρ.range with hU
  have hFc : ∀ x y : ↥F, x * y = y * x := fun x y => hF.1.is_comm.comm x y
  have hF3 : ∀ x : ↥F, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hF.2 x x.2)
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
    rw [← map_mul, ← map_mul, hFc]
  have hU3 : ∀ x ∈ U, x ^ 3 = 1 := by
    rintro _ ⟨f, rfl⟩
    rw [← map_pow, hF3, map_one]
  have hUel : IsElemAbelian 3 U := ⟨⟨⟨fun a b => Subtype.ext (hUc _ a.2 _ b.2)⟩⟩, hU3⟩
  have hker : ∀ f : ↥F, ρ f = 1 → (f : G) ∈ CA := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := hρ f ⟨a, ha⟩
    rw [hf, TableBExc.torusAct_one] at h1
    have h2 := congrArg Subtype.val (hκinj h1)
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hFA
    intro f hf
    refine hker ⟨f, hf⟩ ?_
    have : ρ ⟨f, hf⟩ ∈ U := ⟨_, rfl⟩
    rw [hbot] at this
    exact this
  have hkerle : ρ.ker ≤ (F ⊓ CA).subgroupOf F := fun f hf =>
    Subgroup.mem_subgroupOf.mpr ⟨f.2, hker f hf⟩
  have hidx : (F ⊓ CA).relIndex F ≤ Nat.card U := by
    have h1 : (F ⊓ CA).relIndex F ∣ ρ.ker.index := Subgroup.index_dvd_of_le hkerle
    rw [Subgroup.index_ker] at h1
    exact Nat.le_of_dvd Nat.card_pos h1
  set C₀ := E ⊓ K ⊓ Subgroup.centralizer (F : Set G) with hC₀
  let ev : ↥C₀ → {x : Fin Tag.E7.rank → ZMod 3 // ∀ w ∈ U, TableBExc.torusAct .E7 3 w x = x} :=
    fun a => ⟨κ ⟨a, a.2.1⟩, by
      rintro _ ⟨f, rfl⟩
      rw [← hρ f ⟨a, a.2.1⟩]
      congr 1
      exact Subtype.ext (by
        show (f : G) * a * (f : G)⁻¹ = a
        rw [Subgroup.mem_centralizer_iff.mp a.2.2 f f.2, mul_inv_cancel_right])⟩
  have hev : Function.Injective ev := fun a b h => by
    have h1 := hκinj (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun z : ↥A => (z : G)) h1)
  have hfix := Nat.card_le_card_of_injective ev hev
  have hoff := NoOffExc.ggWeylNoOffender_E7 Nat.prime_three (by norm_num) U hUel hUne
  rw [hEKcard]
  calc Nat.card ↥C₀ * (F ⊓ CA).relIndex F
      ≤ Nat.card {x : Fin Tag.E7.rank → ZMod 3 // ∀ w ∈ U, TableBExc.torusAct .E7 3 w x = x} *
          Nat.card U := Nat.mul_le_mul hfix hidx
    _ = Nat.card U *
          Nat.card {x : Fin Tag.E7.rank → ZMod 3 // ∀ w ∈ U, TableBExc.torusAct .E7 3 w x = x} :=
        Nat.mul_comm _ _
    _ < 3 ^ Tag.E7.rank := hoff
    _ = 3 ^ Row.E7.n := rfl

theorem noTransvDataAt_E7 :
    NoTransvDataAt Row.E7 := by
  intro G _ _ b₀ K E hstd B hB hloc _ htr
  have hstd' := hstd
  obtain ⟨-, ⟨⟨hord, hKC, hKn, -⟩, -⟩, ⟨-, hdisj, -⟩⟩ := hstd
  obtain ⟨hsc, hdiag, hct, hKl, hd3, hds⟩ := e7SignData hB hord hdisj
    (fun g hg y hy => Subgroup.mem_subgroupOf.mp
      (hKn.conj_mem ⟨y, hKC hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩)) hloc
  exact ⟨hsc, hdiag, hct, hKl, hd3, hds, e7_noOffenderA hstd' htr⟩

end CFSG.StandardType.FrameRoute.FS81

end
