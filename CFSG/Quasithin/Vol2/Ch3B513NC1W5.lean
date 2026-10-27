module

public import CFSG.Quasithin.Vol2.Ch3B513NC1ii
public import CFSG.Quasithin.Background.SmithB42LnL5Off
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.FFC5Dich
public import CFSG.Quasithin.Background.FFC5Main
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Background.SmithB51P5Basic
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3

public section

namespace CFSG.Quasithin.B513N

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
open CFSG.Open (quasithinGenFitting)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem card_wedge5 : Nat.card (Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2))) = 2 ^ 10 := by
  rw [Nat.card_congr (Multiplicative.toAdd.trans (Equiv.ofBijective _
    (wedgeCoord_bijective (K := ZMod 2)))), Nat.card_fun, Nat.card_fin, Nat.card_zmod]

theorem c1wedge5_holds : C1Wedge5 := by
  intro W _ _ hW G hne hB53 h1 hGL hU hC hE5
  obtain ⟨π, hr⟩ := hE5
  obtain ⟨β, -, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hr
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have := (hβk x).1 hx
    rw [hC, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨D, hD⟩ := exists_isFFStarMin hne hB53.2.1
  have hDG : D ≤ G := hD.1.1
  let e := specialLinearGroupEquivStatedSL 5 (ZMod 2)
  let φ : G5 →* MulAut W := G.subtype.comp (π.comp e.toMonoidHom)
  have hπ : Function.Injective π :=
    FFC.injective_of_faithful_sec (G64.extSq_faithful (by norm_num)) hr
  have hφ : Function.Injective φ := G.subtype_injective.comp (hπ.comp e.injective)
  have hφr : ∀ g ∈ G, ∃ y, φ y = g := by
    intro g hg
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)), π γ = ⟨g, hg⟩ :=
      hr.1 _
    refine ⟨e.symm γ, ?_⟩
    show ((π (e (e.symm γ)) : ↥G) : MulAut W) = g
    rw [MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val hγ
  set Y : Subgroup G5 := D.comap φ with hY
  have hYD : Y.map φ = D := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun d hd => ?_
    obtain ⟨y, hy⟩ := hφr d (hDG hd)
    exact ⟨y, show φ y ∈ D by rw [hy]; exact hd, hy⟩
  have hYcard : Nat.card Y = Nat.card D := by
    rw [← hYD, Subgroup.card_map_of_injective hφ]
  have hel := hD.1.2.2.1
  have hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    hφ (by rw [map_mul, map_mul]; exact hel.1 _ ha _ hb)
  have hY2 : ∀ a ∈ Y, a * a = 1 := fun a ha =>
    hφ (by rw [map_mul, map_one, ← pow_two]; exact hel.2 _ ha)
  have hFix : Nat.card ↥(fixV D ⊓ commV G) ≤ Nat.card (B42Ln.FixW Y) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨wedgeCoord (Multiplicative.toAdd (β ⟨x, x.2.2⟩)), ?_⟩) ?_
    · intro u hu
      have hux : φ u ∈ D := hu
      have hfix : φ u (x : W) = x := x.2.1 _ hux
      have hmem : ((π (e u) : ↥G) : MulAut W) (x : W) ∈ commV G := by
        rw [show ((π (e u) : ↥G) : MulAut W) = φ u from rfl, hfix]
        exact x.2.2
      have h1 := hβe (e u) ⟨x, x.2.2⟩ hmem
      have h2 : (⟨((π (e u) : ↥G) : MulAut W) (x : W), hmem⟩ : ↥(commV G)) = ⟨x, x.2.2⟩ :=
        Subtype.ext hfix
      rw [h2] at h1
      rw [← wedgeCoord_map, ← specialLinearGroupEquivStatedSL_coe 5 (ZMod 2) u]
      show wedgeCoord (Multiplicative.toAdd (extSqAct (ZMod 2) 5 (e u) (β ⟨x, x.2.2⟩))) = _
      exact (congrArg (fun t : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) =>
        wedgeCoord (Multiplicative.toAdd t)) h1).symm
    · intro x y hxy
      have h1 : wedgeCoord (Multiplicative.toAdd (β ⟨x, x.2.2⟩)) =
          wedgeCoord (Multiplicative.toAdd (β ⟨y, y.2.2⟩)) :=
        congrArg (fun t : B42Ln.FixW Y => t.1) hxy
      have h2 := hβi (Multiplicative.toAdd.injective (wedgeCoord_bijective.1 h1))
      exact Subtype.ext (congrArg (fun t : ↥(commV G) => (t : W)) h2)
  have hUcard : Nat.card (commV G) = 2 ^ 10 := by
    rw [FFC.card_eq_of_realizes rfl hr, hC, Subgroup.card_bot, one_mul]
    show Nat.card ↥(⊤ : Subgroup (Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)))) = _
    rw [Subgroup.card_top, card_wedge5]
  have hoff : 2 ^ 10 ≤ Nat.card D * Nat.card ↥(fixV D ⊓ commV G) := by
    have h1 := Subgroup.relIndex_mul_card (fixV D) (commV G)
    have h2 := (relIndex_fixV_le_index D (commV G)).trans (index_fixV_le_card hD.1)
    rw [← hUcard, ← h1]
    exact Nat.mul_le_mul_right _ h2
  obtain ⟨hle, heq⟩ := B42Ln.card_mul_fixW_le' hYc hY2
  have hge : 2 ^ 10 ≤ Nat.card Y * Nat.card (B42Ln.FixW Y) := by
    rw [hYcard]
    exact hoff.trans (Nat.mul_le_mul_left _ hFix)
  have hYne : Y ≠ ⊥ := by
    intro hbot
    apply hD.1.2.1
    rw [← hYD, hbot, Subgroup.map_bot]
  obtain ⟨h, hRh⟩ := heq hge hYne
  have hD16 : Nat.card D = 16 := by
    rw [← hYcard, hRh,
      Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective,
      B42Ln.card_R4]
  refine hasGood_of_offender_le hW hD (commV_mono hDG) ?_
  rw [hD16]
  have h64 : Nat.card ↥(fixV D ⊓ commV G) * 16 ≤ 2 ^ 10 := by
    rw [mul_comm, ← hD16, ← hYcard]
    exact (Nat.mul_le_mul_left _ hFix).trans hle
  omega

end CFSG.Quasithin.B513N
