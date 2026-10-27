module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


theorem exists_conj_torusGroup_of_odd_order_lift
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {m : ℕ} (hm : Odd m) {p : ℕ} (hp : p.Prime)
    {x : ModGL Tag.E6 L} (hx : x ∈ adjointGroup Tag.E6 L) (hxm : x ^ m = 1)
    (hcube : ∃ h ∈ adjointGroup Tag.E6 L, h⁻¹ * x ^ p * h ∈ torusGroup Tag.E6 L) :
    ∃ g ∈ adjointGroup Tag.E6 L, g⁻¹ * x * g ∈ torusGroup Tag.E6 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hpdvd : p ∣ m
  ·
    have hp2 : p ≠ 2 := hm.ne_two_of_dvd_nat hpdvd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨h, hh, hdT⟩ := hcube
    set x₀ : ModGL Tag.E6 L := h⁻¹ * x * h with hx₀
    have hx₀A : x₀ ∈ adjointGroup Tag.E6 L := mul_mem (mul_mem (inv_mem hh) hx) hh
    have hx₀p : x₀ ^ p = h⁻¹ * x ^ p * h := by
      rw [hx₀]
      simpa using conj_pow (a := h⁻¹) (b := x) (i := p)
    have hd : x₀ ^ p ∈ torusGroup Tag.E6 L := by rw [hx₀p]; exact hdT
    have hx₀m : x₀ ^ m = 1 := by
      rw [hx₀]
      have h := conj_pow (a := h⁻¹) (b := x) (i := m)
      rw [hxm] at h
      simpa using h
    haveI hBfin : Finite (Subgroup.zpowers x₀) :=
      finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm.pos, hx₀m⟩)
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hd
    set M : ℕ := (Nat.card (WeylGroup Tag.E6)).factorization p + 1 with hM
    have hWM : ¬ p ^ M ∣ Nat.card (WeylGroup Tag.E6) :=
      Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp
    let E₀ : Finset L := Finset.univ.image (fun i => (a i : L)) ∪
      Finset.univ.image (fun i => (((a i)⁻¹ : Lˣ) : L))
    obtain ⟨K₁, hK₁fin, hE₀K, hq, hdesc⟩ :=
      exists_descent_subgroup (τ := Tag.E6) (L := L) (ℓ := 2) (r := p) hp2.symm
        (by simpa using halg) (Subgroup.zpowers_le.2 hx₀A) (Set.toFinite _) E₀ (M := M)
        (by omega)
    haveI : Finite K₁ := hK₁fin
    set ι := K₁.subtype with hι
    have ha1 : ∀ i, (a i : L) ∈ K₁ := fun i =>
      hE₀K (Finset.mem_coe.2 (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
    have ha2 : ∀ i, (((a i)⁻¹ : Lˣ) : L) ∈ K₁ := fun i =>
      hE₀K (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun i => ((a i)⁻¹ : Lˣ) : Fin Tag.E6.rank → L)
          (Finset.mem_univ i))))
    let a' : Fin Tag.E6.rank → K₁ˣ := fun i =>
      ⟨⟨a i, ha1 i⟩, ⟨((a i)⁻¹ : Lˣ), ha2 i⟩, Subtype.ext (Units.mul_inv (a i)),
        Subtype.ext (Units.inv_mul (a i))⟩
    have ha' : (fun i => Units.map ι.toMonoidHom (a' i)) = a := by
      funext i
      exact Units.ext rfl
    have hda : baseChangeGL ι (rootDiagUnit Tag.E6 a') = rootDiagUnit Tag.E6 a := by
      rw [baseChangeGL_rootDiagUnit, ha']
    obtain ⟨y, hyA, hyx⟩ := hdesc x₀ (Subgroup.mem_zpowers x₀)
    have hy_pow : y ^ p = rootDiagUnit Tag.E6 a' := by
      apply baseChangeGL_injective (τ := Tag.E6) ι
      rw [map_pow, hyx, ha, hda]
    have hym : y ^ m = 1 := by
      apply baseChangeGL_injective (τ := Tag.E6) ι
      rw [map_pow, hyx, hx₀m, map_one]
    let C : Subgroup (ModGL Tag.E6 K₁) := familyCentralizer Tag.E6 K₁ (fun _ : Unit => a')
    let H : Subgroup (ModGL Tag.E6 K₁) := C ⊓ monomialSubgroup Tag.E6 K₁
    have hyC : y ∈ C := by
      refine mem_familyCentralizer.2 ⟨hyA, fun _ => ?_⟩
      rw [← hy_pow]
      group
    have hqr : ¬ p ∣ Nat.card K₁ := not_dvd_of_modEq_pow hp (by omega) hq
    set e : ℕ := m.factorization p with he
    set n₀ : ℕ := m / p ^ e with hn
    set z : ModGL Tag.E6 K₁ := y ^ n₀ with hz
    have hzpe : z ^ (p ^ e) = 1 := by
      rw [hz, ← pow_mul, Nat.div_mul_cancel (Nat.ordProj_dvd m p), hym]
    have hzp : IsPGroup p (Subgroup.zpowers z) := by
      intro w
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 w.2
      refine ⟨e, Subtype.ext ?_⟩
      have hw : (w : ModGL Tag.E6 K₁) ^ (p ^ e) = 1 := by
        rw [show (w : ModGL Tag.E6 K₁) = z ^ k from hk.symm, ← zpow_natCast, ← zpow_mul,
          mul_comm, zpow_mul, zpow_natCast, hzpe, one_zpow]
      simpa using hw
    have hzC : Subgroup.zpowers z ≤ C := by
      refine Subgroup.zpowers_le.2 ?_
      rw [hz]
      exact pow_mem hyC n₀
    obtain ⟨u, huC, huz⟩ :=
      exists_conj_le_monomial_of_isPGroup_family (τ := Tag.E6) (K := K₁) (ι := Unit)
        (a := fun _ : Unit => a') (r := p) (M := M) hqr hq hWM hzC hzp
    have hu_comm : u * y ^ p * u⁻¹ = y ^ p := by
      have h := (mem_familyCentralizer.1 huC).2 ()
      rw [← hy_pow] at h
      have hcomm : y ^ p * u = u * y ^ p := by
        calc y ^ p * u = (y ^ p * u * (y ^ p)⁻¹) * y ^ p := by group
          _ = u * y ^ p := by rw [h]
      rw [← hcomm]
      group
    have hA2 : Subgroup.zpowers (u * y ^ n₀ * u⁻¹) ≤ H := by
      refine Subgroup.zpowers_le.2 ?_
      simpa [H, hz] using huz z (Subgroup.mem_zpowers z)
    have hcop : Nat.Coprime p n₀ := by
      rw [hp.coprime_iff_not_dvd]
      intro hdiv
      have hmul : n₀ * p ^ e = m := Nat.div_mul_cancel (Nat.ordProj_dvd m p)
      have hdvd : p ^ (e + 1) ∣ m := by
        rw [pow_succ', ← hmul]
        exact mul_dvd_mul_right hdiv (p ^ e)
      exact Nat.pow_succ_factorization_not_dvd hm.pos.ne' hp hdvd
    have hconjpow_p : (u * y * u⁻¹) ^ (p : ℤ) = u * y ^ p * u⁻¹ := by
      rw [zpow_natCast, conj_pow]
    have hconjpow_n : (u * y * u⁻¹) ^ (n₀ : ℤ) = u * y ^ n₀ * u⁻¹ := by
      rw [zpow_natCast, conj_pow]
    have hsup : Subgroup.zpowers (u * y * u⁻¹) =
        Subgroup.zpowers (u * y ^ p * u⁻¹) ⊔ Subgroup.zpowers (u * y ^ n₀ * u⁻¹) := by
      rw [← hconjpow_p, ← hconjpow_n, Subgroup.zpowers_zpow_sup]
      have hg : Int.gcd (p : ℤ) (n₀ : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast, hcop.gcd_eq_one]
      rw [hg]
      simp
    have hbase_sup : baseChangeGL ι (u * y * u⁻¹) ∈
        Subgroup.zpowers (baseChangeGL ι (u * y ^ p * u⁻¹)) ⊔
          Subgroup.zpowers (baseChangeGL ι (u * y ^ n₀ * u⁻¹)) := by
      have hmem : u * y * u⁻¹ ∈
          Subgroup.zpowers (u * y ^ p * u⁻¹) ⊔ Subgroup.zpowers (u * y ^ n₀ * u⁻¹) := by
        rw [← hsup]
        exact Subgroup.mem_zpowers _
      have hmap := Subgroup.mem_map_of_mem (baseChangeGL ι) hmem
      rwa [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
    have hle1 : Subgroup.zpowers (baseChangeGL ι (u * y ^ p * u⁻¹)) ≤
        monomialSubgroup Tag.E6 L := by
      rw [hu_comm, hy_pow, hda]
      exact Subgroup.zpowers_le.2 (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup a))
    have hle2 : Subgroup.zpowers (baseChangeGL ι (u * y ^ n₀ * u⁻¹)) ≤
        monomialSubgroup Tag.E6 L := by
      refine Subgroup.zpowers_le.2 ?_
      exact baseChangeGL_mem_monomialSubgroup ι (Subgroup.mem_inf.1 (hA2
        (Subgroup.mem_zpowers _))).2
    have hbase_mono : baseChangeGL ι (u * y * u⁻¹) ∈ monomialSubgroup Tag.E6 L :=
      (sup_le hle1 hle2) hbase_sup
    set U : ModGL Tag.E6 L := baseChangeGL ι u with hU
    have hUA : U ∈ adjointGroup Tag.E6 L :=
      CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι (mem_familyCentralizer.1 huC).1
    set m₀ : ModGL Tag.E6 K₁ := u * y * u⁻¹ with hm₀
    have hm₀mono : baseChangeGL ι m₀ ∈ monomialSubgroup Tag.E6 L := by
      rw [hm₀]
      exact hbase_mono
    have hm₀pow : (baseChangeGL ι m₀) ^ p = rootDiagUnit Tag.E6 a := by
      rw [hm₀, ← map_pow, conj_pow, hu_comm, hy_pow, hda]
    have hw_p : weylQuotientHom Tag.E6 L
        ⟨baseChangeGL ι m₀, hm₀mono⟩ ^ p = 1 := by
      have hdN : rootDiagUnit Tag.E6 a ∈ monomialSubgroup Tag.E6 L :=
        Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup a)
      have h1 : weylQuotientHom Tag.E6 L
          ⟨(baseChangeGL ι m₀) ^ p, pow_mem hm₀mono p⟩ = 1 := by
        have e : (⟨(baseChangeGL ι m₀) ^ p, pow_mem hm₀mono p⟩ :
            monomialSubgroup Tag.E6 L) = ⟨rootDiagUnit Tag.E6 a, hdN⟩ :=
          Subtype.ext hm₀pow
        rw [e]
        exact weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup
          (rootDiagUnit_mem_torusGroup a))
      have h2 : (⟨baseChangeGL ι m₀, hm₀mono⟩ : monomialSubgroup Tag.E6 L) ^ p =
          ⟨(baseChangeGL ι m₀) ^ p, pow_mem hm₀mono p⟩ := Subtype.ext rfl
      calc weylQuotientHom Tag.E6 L ⟨baseChangeGL ι m₀, hm₀mono⟩ ^ p
          = weylQuotientHom Tag.E6 L (⟨baseChangeGL ι m₀, hm₀mono⟩ ^ p) := by rw [map_pow]
        _ = weylQuotientHom Tag.E6 L ⟨(baseChangeGL ι m₀) ^ p, pow_mem hm₀mono p⟩ := by
              rw [h2]
        _ = 1 := h1
    have hmon : MonomialToralAt Tag.E6 p :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp hp2
    have hLp : ringChar L ≠ p := by
      rw [ringChar.eq L 2]
      exact hp2.symm
    obtain ⟨v, hv, hvn⟩ := hmon L hLp Unit
      (1 : Multiplicative (Fin Tag.E6.rank → ℤ) →* Unit)
      (baseChangeGL ι m₀) hm₀mono
      (mem_kernelWeylGroup_one (weylQuotientHom Tag.E6 L
        ⟨baseChangeGL ι m₀, hm₀mono⟩)) hw_p
    have hvA : v ∈ adjointGroup Tag.E6 L := rootSpan_le_adjointGroup L _ hv
    have hm₀eq : baseChangeGL ι m₀ = U * x₀ * U⁻¹ := by
      rw [hm₀, map_mul, map_mul, map_inv, hyx]
    refine ⟨h * (v * U)⁻¹, mul_mem hh (inv_mem (mul_mem hvA hUA)), ?_⟩
    have hx_eq : x = h * x₀ * h⁻¹ := by rw [hx₀]; group
    have hgoal : (h * (v * U)⁻¹)⁻¹ * x * (h * (v * U)⁻¹) =
        v * baseChangeGL ι m₀ * v⁻¹ := by
      rw [hx_eq, hm₀eq]
      group
    rw [hgoal]
    exact hvn
  ·
    have hcop : Nat.Coprime p (orderOf x) := by
      rw [hp.coprime_iff_not_dvd]
      intro hdiv
      exact hpdvd (hdiv.trans (orderOf_dvd_of_pow_eq_one hxm))
    obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hcop
    obtain ⟨h, hh, hdT⟩ := hcube
    refine ⟨h, hh, ?_⟩
    have hx_eq : h⁻¹ * x * h = (h⁻¹ * x ^ p * h) ^ a := by
      calc h⁻¹ * x * h = h⁻¹ * (x ^ p) ^ a * h := by
            conv_lhs => rw [← ha]
        _ = (h⁻¹ * x ^ p * h) ^ a :=
              (conj_pow (a := h⁻¹) (b := x ^ p) (i := a)).symm
    rw [hx_eq]
    exact pow_mem hdT a

end CFSG.StandardType
