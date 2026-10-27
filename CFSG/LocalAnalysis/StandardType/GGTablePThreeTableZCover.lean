module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZCatalogue
import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZHopf
import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZTransport
import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZCentre
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

private theorem tztc_map_ker_le {H U : Type*} [Group H] [Group U] (κ : H →* U)
    (hker : ∀ x, x ∈ κ.ker ↔ x ∈ Subgroup.center H ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (φ : MulAut H) : κ.ker.map φ ≤ κ.ker := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨hyc, k, hyk⟩ := (hker y).mp hy
  rw [hker]
  refine ⟨?_, k, ?_⟩
  · rw [← Subgroup.map_center_eq φ]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom hyc
  · rw [← map_pow, hyk, map_one]

private theorem tztc_map_ker_eq {H U : Type*} [Group H] [Group U] (κ : H →* U)
    (hker : ∀ x, x ∈ κ.ker ↔ x ∈ Subgroup.center H ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (φ : MulAut H) : κ.ker.map φ = κ.ker := by
  refine le_antisymm (tztc_map_ker_le κ hker φ) ?_
  intro x hx
  have hmem : φ.symm x ∈ κ.ker :=
    tztc_map_ker_le κ hker φ.symm (Subgroup.mem_map_of_mem φ.symm.toMonoidHom hx)
  exact Subgroup.mem_map.mpr ⟨φ.symm x, hmem, by simp⟩

private theorem tztc_injective_on {H U : Type*} [Group H] [Group U] (κ : H →* U)
    (J : Subgroup H) (h : J ⊓ κ.ker = ⊥) : Function.Injective (κ.subgroupMap J) := by
  intro a b hab
  have h1 : κ (a : H) = κ (b : H) := by
    have := congrArg Subtype.val hab
    simpa only [MonoidHom.subgroupMap_apply_coe] using this
  have h2 : (a : H)⁻¹ * b ∈ κ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have h3 : (a : H)⁻¹ * b ∈ J := J.mul_mem (J.inv_mem a.2) b.2
  have h4 : (a : H)⁻¹ * b = 1 := by
    have hmem : (a : H)⁻¹ * b ∈ J ⊓ κ.ker := ⟨h3, h2⟩
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact Subtype.ext (inv_mul_eq_one.mp h4)

private noncomputable def tztc_equivMap {H U : Type*} [Group H] [Group U] (κ : H →* U)
    (J : Subgroup H) (h : J ⊓ κ.ker = ⊥) : J ≃* J.map κ :=
  MulEquiv.ofBijective (κ.subgroupMap J) ⟨tztc_injective_on κ J h, by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext (by simpa only [MonoidHom.subgroupMap_apply_coe] using hxy)⟩⟩

private theorem tztc_eq_one_of_map_eq_one {H U : Type*} [Group H] [Group U] (κ : H →* U)
    (hker : κ.ker ≤ Subgroup.center H) (hperf : commutator H = ⊤)
    {δ : MulAut H} {δ' : MulAut U} (hδ' : ∀ x, κ (δ x) = δ' (κ x))
    (hδ'1 : δ' = 1) : δ = 1 := by
  have hcx : ∀ x, x⁻¹ * δ x ∈ Subgroup.center H := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_inv, hδ' x, hδ'1, MulAut.one_apply, inv_mul_cancel]
  let f : H →* H :=
    { toFun := fun x => x⁻¹ * δ x
      map_one' := by simp
      map_mul' := fun x y => by
        have hz := (Subgroup.mem_center_iff.mp (hcx x)) y⁻¹
        simp only [map_mul]
        rw [mul_inv_rev]
        calc y⁻¹ * x⁻¹ * (δ x * δ y) = y⁻¹ * (x⁻¹ * δ x) * δ y := by group
          _ = (x⁻¹ * δ x) * y⁻¹ * δ y := by rw [hz]
          _ = (x⁻¹ * δ x) * (y⁻¹ * δ y) := by group }
  have hfle : commutator H ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.mp (hcx a)) (f b)).symm
  ext x
  have hx : f x = 1 := hfle (by rw [hperf]; exact Subgroup.mem_top x)
  have hx' : x⁻¹ * δ x = 1 := by simpa [f] using hx
  rw [inv_mul_eq_one] at hx'
  exact hx'.symm

private theorem tztc_descend {H U : Type} [Group H] [Group U] [Finite H] (κ : H →* U)
    (hκsurj : Function.Surjective κ)
    (hκker : ∀ x, x ∈ κ.ker ↔ x ∈ Subgroup.center H ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (hperf : commutator H = ⊤) (δ : MulAut H) (hδ3 : δ ^ 3 = 1) (hδne1 : δ ≠ 1) :
    ∃ δ' : MulAut U, (∀ x, κ (δ x) = δ' (κ x)) ∧ δ' ^ 3 = 1 ∧ δ' ≠ 1 := by
  have hδker : κ.ker.map δ = κ.ker := tztc_map_ker_eq κ hκker δ
  let eκ := QuotientGroup.liftEquiv (N := κ.ker) (φ := κ) hκsurj rfl
  let δq := QuotientGroup.congr κ.ker κ.ker δ hδker
  let δ' := eκ.symm.trans (δq.trans eκ)
  have heκ : ∀ x, eκ (QuotientGroup.mk x) = κ x := fun x =>
    QuotientGroup.liftEquiv_mk (N := κ.ker) (φ := κ) hκsurj rfl x
  have hδ'x : ∀ x, δ' (κ x) = eκ (δq (QuotientGroup.mk x)) := by
    intro x
    have hs : eκ.symm (κ x) = QuotientGroup.mk x := by
      rw [← heκ x, MulEquiv.symm_apply_apply]
    simp only [δ', MulEquiv.trans_apply, hs]
  have hδ' : ∀ x, κ (δ x) = δ' (κ x) := by
    intro x
    have hδqx : δq (QuotientGroup.mk x) = QuotientGroup.mk (δ x) := rfl
    calc κ (δ x) = eκ (QuotientGroup.mk (δ x)) := (heκ (δ x)).symm
      _ = eκ (δq (QuotientGroup.mk x)) := by rw [hδqx]
      _ = δ' (κ x) := (hδ'x x).symm
  have hδ'3 : δ' ^ 3 = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := hκsurj y
    have h3x : δ (δ (δ x)) = x := by
      simpa [pow_three', MulAut.mul_apply, MulAut.one_apply] using
        congrArg (fun f : MulAut H => f x) hδ3
    rw [pow_three', MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply,
      ← hδ' x, ← hδ' (δ x), ← hδ' (δ (δ x)), h3x]
  exact ⟨δ', hδ', hδ'3, fun hδ'1 =>
    hδne1 (tztc_eq_one_of_map_eq_one κ (fun x hx => ((hκker x).mp hx).1) hperf hδ' hδ'1)⟩

private theorem tztc_hconj_of_conj
    {K H R : Type} [Field K] [Finite K] [Group H]
    [Group R] {σ : K ≃+* K}
    (e : R ≃* ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K σ))
    (κ : H →* ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup K σ.toRingHom))
    (hκsurj : Function.Surjective κ)
    (θ : H ⧸ Subgroup.center H ≃* R)
    (hκeq : ∀ x, CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed σ.toRingHom (κ x) =
      ((e (θ (QuotientGroup.mk x)) : ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K σ)) :
        CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.TwistTag.E6.tag K))
    (δ : MulAut H) (δ' : MulAut ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup K σ.toRingHom))
    (hδ' : ∀ x, κ (δ x) = δ' (κ x))
    (h : ↥(CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K σ))
    (hh : CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ h =
      MulAut.congr e (ggInducedAut θ δ)) :
    ∀ y, CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed σ.toRingHom (δ' y) =
      h * CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed σ.toRingHom y * h⁻¹ := by
  intro y
  obtain ⟨x, rfl⟩ := hκsurj y
  have hz := (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_apply
    (K := K) (σ := σ) h (e (θ (QuotientGroup.mk x)))).symm
  rw [← hδ' x]
  rw [hκeq (δ x)]
  rw [hκeq x]
  simp only [Subgroup.coe_inv]
  conv_rhs => rw [hz, hh]
  congr 1
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    ggInducedAut_apply]

theorem tableZ_recipe
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    (hsc : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = (2 ^ n) ^ 2 →
      (∀ c, σ c = c ^ (2 ^ n)) → TwE6ScTableZAt K σ n)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    TwE6A2CentreCont n (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))
      (LargeEvenChevIDImage (LargeEvenCartanE 6) K _) (LargeEvenChevFieldImage (LargeEvenCartanE 6) K _) := by
  classical
  intro hfin θ δ hδ3 hδne1 hδI J hJcomp hJmark
  obtain ⟨K', instK'f, instK'fin, σ', hK', hσ', e, hIderived⟩ := tableZ_recipe_catalogue hn K hK
  letI : Field K' := instK'f
  letI : Finite K' := instK'fin
  haveI hCperf : Group.IsPerfect ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K' σ') :=
    ⟨CFSG.LieType.Chevalley.commutator_twistedE6RootGroup_eq_top (ℓ := 2) (f := n)
      Nat.prime_two hn hK' σ' hσ'⟩
  haveI hRperf : Group.IsPerfect
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI hHperf : Group.IsPerfect
      (HopfCover (LargeEvenCenterQuot
        (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))) := hopfCover_isPerfect
  have hHcom : commutator (HopfCover (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))) = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  obtain ⟨κ, hκsurj, hκeq, hκker⟩ := tableZ_cover K' σ' hn hK' hσ' h3 e θ
  let β : MulAut ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K' σ') := MulAut.congr e (ggInducedAut θ δ)
  have hβmem : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K' σ') := by
    simpa only [β] using hIderived (ggInducedAut θ δ) hδI
  have hγ3 : (ggInducedAut θ δ) ^ 3 = 1 := by
    rw [← map_pow (ggInducedAut θ) δ 3, hδ3, map_one]
  have hβ3 : β ^ 3 = 1 := by
    change (MulAut.congr e (ggInducedAut θ δ)) ^ 3 = 1
    rw [← map_pow (MulAut.congr e) (ggInducedAut θ δ) 3, hγ3, map_one]
  have hβ1 : β ≠ 1 := by
    intro hβ
    apply hδne1
    have hγ1 : ggInducedAut θ δ = 1 := by
      have h : MulAut.congr e (ggInducedAut θ δ) = 1 := by simpa only [β] using hβ
      exact (MulAut.congr e).injective (h.trans (map_one (MulAut.congr e)).symm)
    exact ggInducedAut_injective_of_perfect hHcom θ (by rw [hγ1, map_one])
  have hker : κ.ker ≤ Subgroup.center (HopfCover (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))) :=
    fun x hx => ((hκker x).mp hx).1
  have hker2 : ∀ x ∈ κ.ker, ∃ k : ℕ, x ^ (2 ^ k) = 1 :=
    fun x hx => ((hκker x).mp hx).2
  obtain ⟨δ', hδ', hδ'3, hδ'ne⟩ := tztc_descend κ hκsurj hκker hHcom δ hδ3 hδne1
  have hZ : Nat.card (Subgroup.center ↥J) ∣ 3 := card_center_dvd_three_of_twA hJmark
  obtain ⟨hcompMap, hbot⟩ :=
    tableZ_transport κ hκsurj hker hker2 δ hδ3 δ' hδ' J hJcomp hZ
  let eJ := tztc_equivMap κ J hbot
  have hmarkMap : LargeEvenMarking ↥(J.map κ)
      (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3 * n) :=
    largeEvenMarking_congr eJ.symm (fun _ _ _ _ _ _ h => h) hJmark
  obtain ⟨h, hhconj, -, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.Exc.exists_twE6Inndiag_of_mem_innAutDerived
      (q := ⟨2, n, Nat.prime_two, by omega⟩) hK' hσ' hβmem hβ3 hβ1
  have hconjmark : ∃ h ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K' σ',
      ∀ y, CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed σ'.toRingHom (δ' y) =
        h * CFSG.LieType.Steinberg.Isogeny.e6IsogenyFixed σ'.toRingHom y * h⁻¹ :=
    ⟨h, h.2, tztc_hconj_of_conj e κ hκsurj θ hκeq δ δ' hδ' h (by simpa only [β] using hhconj)⟩
  have hcenterMap : Subgroup.center ↥(J.map κ) = ⊥ :=
    hsc K' σ' hK' hσ' δ' hδ'3 hδ'ne hconjmark (J.map κ) hcompMap hmarkMap
  have hcJ := Subgroup.map_center_eq eJ
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : eJ x ∈ Subgroup.center ↥(J.map κ) :=
    hcJ ▸ Subgroup.mem_map_of_mem eJ.toMonoidHom hx
  rw [hcenterMap] at hx'
  exact eJ.injective (by rw [Subgroup.mem_bot.mp hx', map_one])

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny in
theorem labelAll_twE6A2CentreCont_of_sc
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    (hsc : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = (2 ^ n) ^ 2 →
      (∀ c, σ c = c ^ (2 ^ n)) → TwE6ScTableZAt K σ n)
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twE6) (hln : lab.n = n) :
    LargeEvenLabelAll lab (TwE6A2CentreCont n) := by
  obtain ⟨t, l, n'⟩ := lab
  dsimp only at htag hln
  subst htag
  subst n'
  intro Q hQ
  exact recipeTwisted_and (P := TwE6A2CentreCont n)
    (fun K _ _ hK => tableZ_recipe hn h3 hsc K hK) hQ

end CFSG.StandardType.TablePThreeKG

end
