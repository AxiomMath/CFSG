module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTUnits
import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTSplitLaw
import CFSG.RankThree.Classical2.TwistedE6RationalOrder
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Sylow
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Order
import CFSG.LocalAnalysis.StandardType.GGTwE6OuterGenF4
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
import CFSG.LieType.SeitzGeneration.ExcParabolicModel
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangRankOne
public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Close

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.Open CFSG.RankThree.PartOne.KE

theorem twistedE6RootGroup_threeSubgroup_split
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (h3 : 3 ∣ ℓ ^ f - 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {E₀ : Subgroup (ModGL TwistTag.E6.tag K)}
    (hE₀ : E₀ ≤ twistedE6RootGroup K σ) (hel : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 4) :
    ∃ h ∈ twistedE6RootGroup K σ, ∀ x ∈ E₀, h⁻¹ * x * h ∈ torusGroup TwistTag.E6.tag K := by
  classical
  let k := RingHom.eqLocusField σ.toRingHom (RingHom.id K)
  have hkcard : Nat.card k = ℓ ^ f := by
    simpa [k] using
      CFSG.RankThree.Chevalley.card_eqLocusField_of_pow (p := ℓ) (f := f) hℓ hf
        (K := K) hK (σ := σ.toRingHom) hσ
  have hk2 : 2 ≤ Nat.card k := by
    rw [hkcard]
    exact Nat.one_lt_pow (by omega : f ≠ 0) hℓ.one_lt
  have hq1 : Nat.card k % 3 = 1 := by
    have hk3 : ((Nat.card k : ℕ) : ZMod 3) = 1 := by
      rw [hkcard]
      have h : ((ℓ ^ f : ℕ) : ZMod 3) = ((1 : ℕ) : ZMod 3) := by
        rw [ZMod.natCast_eq_natCast_iff]
        apply Nat.modEq_iff_dvd.mpr
        have h1 : 1 ≤ ℓ ^ f := Nat.succ_le_of_lt (pow_pos hℓ.pos f)
        have h'int : ((3 : ℤ) ∣ (ℓ ^ f : ℤ) - 1) := by
          have hcast : ((ℓ ^ f - 1 : ℕ) : ℤ) = (ℓ ^ f : ℤ) - 1 := by
            rw [Nat.cast_sub h1, Nat.cast_one]
            rfl
          rw [← hcast]
          exact_mod_cast h3
        rw [← neg_sub]
        exact dvd_neg.mpr h'int
      simpa using h
    rw [← ZMod.val_natCast 3 (Nat.card k), hk3]
    exact ZMod.val_one'' (by norm_num : (3 : ℕ) ≠ 1)
  have hσk : ∀ c : K, σ c = c ^ Nat.card k := by
    intro c
    rw [hσ, hkcard]
  have hKk : Nat.card K = Nat.card k ^ 2 := by
    rw [hK, hkcard]
  let : Finite k :=
    Finite.of_injective (fun x : k => (x : K)) Subtype.val_injective
  have hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c => c.2
  let E₀' : Subgroup (twistedE6RootGroup K σ) := E₀.subgroupOf (twistedE6RootGroup K σ)
  have hE₀' : ∀ x ∈ E₀', x ^ 3 = 1 := by
    intro x hx
    exact Subtype.ext (hel.2 (x : ModGL TwistTag.E6.tag K) hx)
  obtain ⟨g, hg⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.threeSubgroup_conj_into_F4
      (k := k) (K := K) σ hσk hKk hfix hq1 hk2 E₀' hE₀'
  let Γ : Subgroup (ModGL TwistTag.E6.tag k) :=
    twistedFixedGroup TwistTag.E6 k (RingHom.id k)
  let Y_pre : Subgroup Γ :=
    (E₀'.map (MulAut.conj g).toMonoidHom).comap
      (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix)
  let Y : Subgroup (ModGL TwistTag.E6.tag k) := Y_pre.map Γ.subtype
  have hY : Y ≤ Γ := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hrange : ((CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix).comp
      (CFSG.HardMathSupport.Lang.AnisoE6.e6FixedF4EquivAll k).symm.toMonoidHom).range ≤
      (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix).range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(CFSG.HardMathSupport.Lang.AnisoE6.e6FixedF4EquivAll k).symm x, rfl⟩
  have hg' : E₀'.map (MulAut.conj g).toMonoidHom ≤
      (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix).range := le_trans hg hrange
  have hYel : IsElemAbelian 3 Y := by
    have hH : IsElemAbelian 3 (E₀'.map (MulAut.conj g).toMonoidHom) :=
      (hel.subgroupOf _).map _
    have h1 : IsElemAbelian 3 Y_pre :=
      CFSG.LieType.SeitzGeneration.isElemAbelian_comap_of_injective
        (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix)
        (CFSG.HardMathSupport.Lang.AnisoE6.phiG_injective σ hfix) hH
    exact h1.map Γ.subtype
  have hYc : Nat.card Y = 3 ^ 4 := by
    have h1 : Nat.card Y = Nat.card Y_pre :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective Γ)
    have h2 : Nat.card Y_pre = Nat.card (E₀'.map (MulAut.conj g).toMonoidHom) :=
      (CFSG.HardMathSupport.Timmesfeld.LocalTwo.card_eq_card_comap_of_injective
        (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix)
        (CFSG.HardMathSupport.Lang.AnisoE6.phiG_injective σ hfix)
        (E₀'.map (MulAut.conj g).toMonoidHom) hg').symm
    have h3 : Nat.card (E₀'.map (MulAut.conj g).toMonoidHom) = Nat.card E₀' :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have h4 : Nat.card E₀' = Nat.card E₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀).toEquiv
    rw [h1, h2, h3, h4, hc]
  have h3k : 3 ∣ Nat.card k - 1 := by
    rw [hkcard]
    exact h3
  obtain ⟨γ, hγΓ, hγT⟩ :=
    CFSG.StandardType.TwE6OuterGen.exists_conj_mem_torusGroup_of_le
      (K := k) h3k hY hYel hYc
  let u : twistedE6RootGroup K σ :=
    CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix ⟨γ, hγΓ⟩ * g
  refine ⟨u⁻¹, inv_mem u.2, ?_⟩
  intro x hx
  let x' : twistedE6RootGroup K σ := ⟨x, hE₀ hx⟩
  have hx' : x' ∈ E₀' := hx
  have hx'' : (MulAut.conj g) x' ∈ E₀'.map (MulAut.conj g).toMonoidHom :=
    ⟨x', hx', rfl⟩
  have hxr : (MulAut.conj g) x' ∈
      (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix).range := hg' hx''
  obtain ⟨y_pre, hy_pre⟩ := hxr
  have hy_preY : y_pre.1 ∈ Y := by
    refine ⟨y_pre, ?_, rfl⟩
    change (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix) y_pre ∈
      E₀'.map (MulAut.conj g).toMonoidHom
    rw [hy_pre]
    exact hx''
  have hconj : γ * y_pre.1 * γ⁻¹ ∈ torusGroup TwistTag.E6.tag k :=
    hγT y_pre.1 hy_preY
  have hy_pre' : (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix y_pre :
      ModGL TwistTag.E6.tag K) = (MulAut.conj g) x' :=
    congrArg Subtype.val hy_pre
  have hbase := CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup
    (algebraMap k K) hconj
  rw [inv_inv]
  have h2 : g.1 * x * g.1⁻¹ =
      (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix y_pre :
        ModGL TwistTag.E6.tag K) := by
    rw [hy_pre']
    rfl
  have h_eq : (u : ModGL TwistTag.E6.tag K) * x * (u : ModGL TwistTag.E6.tag K)⁻¹ =
      baseChangeGL (algebraMap k K) (γ * y_pre.1 * γ⁻¹) := by
    have h1 : (u : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap k K) γ * g.1 := by
      simp [u, CFSG.HardMathSupport.Lang.AnisoE6.coe_phiG]
    rw [h1]
    have h2' : (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix y_pre :
        ModGL TwistTag.E6.tag K) = baseChangeGL (algebraMap k K) y_pre.1 :=
      CFSG.HardMathSupport.Lang.AnisoE6.coe_phiG σ hfix y_pre
    calc
      (baseChangeGL (algebraMap k K) γ * g.1) * x *
          (baseChangeGL (algebraMap k K) γ * g.1)⁻¹
        = baseChangeGL (algebraMap k K) γ * (g.1 * x * g.1⁻¹) *
            (baseChangeGL (algebraMap k K) γ)⁻¹ := by group
      _ = baseChangeGL (algebraMap k K) γ *
            (CFSG.HardMathSupport.Lang.AnisoE6.phiG σ hfix y_pre :
              ModGL TwistTag.E6.tag K) *
            (baseChangeGL (algebraMap k K) γ)⁻¹ := by rw [h2]
      _ = baseChangeGL (algebraMap k K) (γ * y_pre.1 * γ⁻¹) := by
        rw [h2', map_mul, map_mul, map_inv]
  rw [h_eq]
  exact hbase

theorem ggFixGp_twistedE6_eq_map_of_three_dvd
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1) :
    ggFixGp .twistedE6 f =
      (twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)).map
        (baseChangeGL (ggRatEmb (2 * f))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (2 * f)
  let : Algebra F GGL := (ggRatEmb (2 * f)).toAlgebra
  have : IsScalarTower (ZMod 2) F GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have : Algebra.IsAlgebraic F GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := F) (A := GGL)
  have : IsAlgClosure F GGL := ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hcardF : Nat.card F = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega : 2 * f ≠ 0), ← pow_mul, Nat.mul_comm]
  let σ : F →+* F := (iterateFrobeniusEquiv F 2 f).toRingHom
  have hσ : ∀ c, σ c = c ^ (2 ^ f) :=
    fun c => iterateFrobeniusEquiv_def F 2 f c
  let R : Subgroup (ModGL TwistTag.E6.tag GGL) := ggFixGp .twistedE6 f
  let C : Subgroup (ModGL TwistTag.E6.tag GGL) :=
    (twistedE6RootGroup F (iterateFrobeniusEquiv F 2 f)).map
      (baseChangeGL (ggRatEmb (2 * f)))
  change R = C
  obtain ⟨hfin, -, hder, -, -, hcardR, -⟩ :=
    (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf F hcardF σ hσ
      GGL (ggFrobT f) (ggFrobT_apply f))
  have hcardC : Nat.card C =
      Nat.card (twistedE6RootGroup F (iterateFrobeniusEquiv F 2 f)) :=
    Subgroup.card_map_of_injective
      (K := twistedE6RootGroup F (iterateFrobeniusEquiv F 2 f))
      (baseChangeGL_injective (τ := TwistTag.E6.tag) (ggRatEmb (2 * f)))
  have hcardTw : Nat.card (twistedE6RootGroup F (iterateFrobeniusEquiv F 2 f)) =
      ordTwistedE6 (2 ^ f) :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.card_twistedE6RootGroup_eq
      (ℓ := 2) (f := f) Nat.prime_two hf (iterateFrobeniusEquiv F 2 f) hcardF
      (fun c => iterateFrobeniusEquiv_def F 2 f c)
  have h3' : ¬ 3 ∣ 2 ^ f + 1 := by
    intro hdiv
    have hsub : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hdiv h3
    have hval : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by
      have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    rw [hval] at hsub
    have : ¬ (3 ∣ 2) := by norm_num
    exact this hsub
  have hgcd : Nat.gcd 3 (2 ^ f + 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3'
  have hcardCval : Nat.card C =
      (2 ^ f) ^ 36 * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 + 1) * ((2 ^ f) ^ 8 - 1) *
        ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 5 + 1) * ((2 ^ f) ^ 2 - 1) := by
    rw [hcardC, hcardTw]
    unfold ordTwistedE6
    rw [hgcd, Nat.div_one]
  have hcardR' : Nat.card R =
      (2 ^ f) ^ 36 * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 + 1) * ((2 ^ f) ^ 8 - 1) *
        ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 5 + 1) * ((2 ^ f) ^ 2 - 1) := by
    change Nat.card (twistedFixedGroup TwistTag.E6 GGL (ggFrobT f)) = _
    exact hcardR
  have hcard : Nat.card R = Nat.card C := by
    rw [hcardR', hcardCval]
  have hCR : C ≤ R := by
    have hder' : ⁅R, R⁆ = C := hder
    rw [← hder']
    exact Subgroup.commutator_le_self R
  let : Finite R := hfin
  exact (Subgroup.eq_of_le_of_card_ge hCR hcard.le).symm

theorem twE6_threeSubgroup_split
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1)
    {E : Subgroup (ModGL (langTag .twistedE6) GGL)} (hE : E ≤ ggFixGp .twistedE6 f)
    (hel : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 4) :
    ∃ g ∈ ggFixGp .twistedE6 f, ∀ x ∈ E, g⁻¹ * x * g ∈ torusGroup (langTag .twistedE6) GGL := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (2 * f)
  let σE := iterateFrobeniusEquiv F 2 f
  let C₀ : Subgroup (ModGL TwistTag.E6.tag F) := twistedE6RootGroup F σE
  let ι : ModGL TwistTag.E6.tag F →* ModGL TwistTag.E6.tag GGL :=
    baseChangeGL (ggRatEmb (2 * f))
  have hιinj : Function.Injective ι :=
    baseChangeGL_injective (τ := TwistTag.E6.tag) (f := ggRatEmb (2 * f))
  have hR : ggFixGp .twistedE6 f = C₀.map ι :=
    ggFixGp_twistedE6_eq_map_of_three_dvd hf h3
  have hcardF : Nat.card F = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega : 2 * f ≠ 0), ← pow_mul, Nat.mul_comm]
  let E' : Subgroup (ModGL TwistTag.E6.tag GGL) := E
  let E₀ : Subgroup (ModGL TwistTag.E6.tag F) := E'.comap ι
  have hE' : E' ≤ ggFixGp .twistedE6 f := hE
  have hEC : E' ≤ C₀.map ι := hE'.trans hR.le
  have hE₀le : E₀ ≤ C₀ := by
    intro x hx
    have hxE : ι x ∈ E' := hx
    have hxmap : ι x ∈ C₀.map ι := hEC hxE
    have hxcomap : x ∈ (C₀.map ι).comap ι := hxmap
    rwa [Subgroup.comap_map_eq_self_of_injective hιinj C₀] at hxcomap
  have hrange : E' ≤ ι.range := hEC.trans (Subgroup.map_le_range ι C₀)
  have hmap : E₀.map ι = E' := Subgroup.map_comap_eq_self (f := ι) (H := E') hrange
  have hcardE₀ : Nat.card E₀ = 3 ^ 4 := by
    have h1 : Nat.card (E₀.map ι) = Nat.card E₀ :=
      Subgroup.card_map_of_injective (f := ι) (K := E₀) hιinj
    rw [hmap] at h1
    have h2 : Nat.card E' = 3 ^ 4 := hc
    rw [h2] at h1
    exact h1.symm
  have hel₀ : IsElemAbelian 3 E₀ := by
    constructor
    · refine IsMulCommutative.of_comm ?_
      intro a b
      apply Subtype.ext
      apply hιinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        (isMulCommutative_iff.1 hel.1 ⟨ι a.1, a.2⟩ ⟨ι b.1, b.2⟩)
    · intro a ha
      apply hιinj
      rw [map_pow, map_one]
      exact hel.2 (ι a) ha
  obtain ⟨h, hhC, hsplit⟩ :=
    twistedE6RootGroup_threeSubgroup_split (ℓ := 2) (f := f) Nat.prime_two hf h3 hcardF
      σE (fun c => iterateFrobeniusEquiv_def F 2 f c) hE₀le hel₀ hcardE₀
  refine ⟨ι h, ?_, ?_⟩
  · rw [hR]
    exact Subgroup.mem_map_of_mem ι hhC
  · intro x hx
    change x ∈ E' at hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp (hmap ▸ hx)
    have hconj : (ι h)⁻¹ * ι x₀ * ι h = ι (h⁻¹ * x₀ * h) := by
      rw [← map_inv, ← map_mul, ← map_mul]
    change (ι h)⁻¹ * ι x₀ * ι h ∈ torusGroup TwistTag.E6.tag GGL
    rw [hconj]
    exact CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup
      (ι := ggRatEmb (2 * f)) (hsplit x₀ hx₀)

theorem twE6TTThreeSplit_holds :
    TwE6TTThreeSplit := by
  intro f hf h3 E hE hel hc
  obtain ⟨g, hg, hsplit⟩ := twE6_threeSubgroup_split hf h3 hE hel hc
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), 1, g, twE6LangPos_one_of_conj hE hg hsplit,
    ggWeylLaw_twistedE6_one h3 le_rfl⟩

end CFSG.StandardType.LieKnownR2.ExcPos
