module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlock
import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusWeyl
import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusWAux
import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusCenter
import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameBridge
import CFSG.LocalAnalysis.StandardType.GGTBJTypeBSupported
import CFSG.LocalAnalysis.StandardType.GGTBJTypeBTwisted

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.SuSplitRootGen CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial
open Multiplicative

theorem ggTBJ_uniMinus_sideDatum_of_frame
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {f m ε p : ℕ}
    [Fact p.Prime] (h : UnitaryFieldData 2 f F) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1)
    (hε : ε ≤ 1) (hm : 2 ≤ m) {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hζb : h.bar ζ = ζ)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    {φ : hypSU h m ε →* G} (hφX : φ.range = X) (hker : φ.ker ≤ Subgroup.center (hypSU h m ε))
    (hkp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1)
    (hinj : Function.Injective (hypFrame φ τ)) (hfr : ∀ v, hypFrame φ τ v ∈ Bs)
    (hmeet : ∀ v, hypFrame φ τ v ∈ Subgroup.centralizer (X : Set G) → v = 1)
    (hact : ∀ b ∈ Bs, ∃ v, ∀ g ∈ X, b * g * b⁻¹ = hypFrame φ τ v * g * (hypFrame φ τ v)⁻¹)
    {y : G} (hyB : y ∈ Bs) (hyX : y ∉ Subgroup.centralizer (X : Set G))
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer ({y} : Set G)))
    {z : G} (hzB : z ∈ Bs) (hzX : z ∈ Subgroup.centralizer (X : Set G)) (hz1 : z ≠ 1)
    (hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hp : p.Prime := Fact.out
  let Θ₁ : (Fin m → Multiplicative (ZMod p)) →* G := hypFrame φ τ
  have hinj₁ : Function.Injective Θ₁ := hinj
  have hfr₁ : ∀ v, Θ₁ v ∈ Bs := hfr
  have hmeet₁ : ∀ v, Θ₁ v ∈ Subgroup.centralizer (X : Set G) → v = 1 := hmeet
  have hrange : ∀ v, Θ₁ v ∈ φ.range := by
    intro v
    rw [show Θ₁ v = φ (τ (ofAdd (fun i => toAdd (v i)))) from
      hypFrame_eq_ofAdd φ τ v]
    exact ⟨_, rfl⟩
  obtain ⟨Θ, hΘ⟩ :=
    TypeBDatum.exists_prodEquiv_of_frame_centralizer hBs Θ₁ hinj₁ hfr₁ hmeet₁ hact
  obtain ⟨hlePart, hgePart⟩ :=
    SuSplitRootGen.uniMinus_signed_of_frame (hζ := hζ) (hτ := hτ) hker hkp
  have hle : ∀ x ∈ X, x ∈ Subgroup.normalizer (Bs : Set G) →
      ∃ σ ∈ SpJoin.spSignedGroup m p, ∀ v, x * Θ₁ v * x⁻¹ = Θ₁ (σ v) := by
    intro x hx hxN
    have hxr : x ∈ φ.range := by simpa [hφX] using hx
    refine hlePart x hxr ?_
    intro v
    have hxb : x * Θ₁ v * x⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hxN (Θ₁ v)).mp (hfr₁ v)
    obtain ⟨⟨v', c⟩, hvc⟩ := Θ.surjective ⟨x * Θ₁ v * x⁻¹, hxb⟩
    have hval : ((Θ (v', c) : ↥Bs) : G) = x * Θ₁ v * x⁻¹ := congrArg Subtype.val hvc
    have hdec : x * Θ₁ v * x⁻¹ = Θ₁ v' * (c : G) := by rw [← hval, hΘ]
    refine ⟨v', ?_⟩
    have hcBs : (c : G) ∈ Bs := c.2.1
    have hcC : (c : G) ∈ Subgroup.centralizer (X : Set G) := c.2.2
    have hcp : (c : G) ^ p = 1 := hBs.2 (c : G) hcBs
    have hcXmem : (c : G) ∈ X := by
      have h1 : Θ₁ v' ∈ X := by rw [← hφX]; exact hrange v'
      have h2 : x * Θ₁ v * x⁻¹ ∈ X :=
        X.mul_mem (X.mul_mem hx (by rw [← hφX]; exact hrange v)) (X.inv_mem hx)
      have heq : (c : G) = (Θ₁ v')⁻¹ * (x * Θ₁ v * x⁻¹) := by rw [hdec]; group
      rw [heq]
      exact X.mul_mem (X.inv_mem h1) h2
    have hcr : (c : G) ∈ φ.range := by simpa [hφX] using hcXmem
    have hcCr : (c : G) ∈ Subgroup.centralizer (φ.range : Set G) := by
      simpa [hφX] using hcC
    have hc1 : (c : G) = 1 :=
      SuSplitRootGen.eq_one_of_mem_centralizer_range_of_pow_eq_one h hp2 hpq (by omega) hker
        hcr hcCr hcp
    rw [hc1, mul_one] at hdec
    exact hdec
  have hge : ∀ i : Fin m, ∃ x ∈ X, x ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ v, x * Θ₁ v * x⁻¹ = Θ₁ (SpJoin.spReflPerm m p i v) := by
    intro i
    obtain ⟨x, hxr, hxact⟩ := hgePart i
    have hxX : x ∈ X := by simpa [hφX] using hxr
    obtain ⟨σ', hσ', hσ'eq⟩ :=
      TypeBDatum.exists_mem_signedAut_of_mem_spSignedGroup m p
        (SpJoin.spReflPerm_mem_spSignedGroup m p i)
    refine ⟨x, hxX, ?_, fun v => hxact v⟩
    refine TypeBDatum.mem_normalizer_of_frame_action (n := x) Θ₁ Θ hΘ hxX σ' ?_
    intro v
    rw [hxact v]
    exact congrArg Θ₁ (by
      have h := congrArg (fun e : Equiv.Perm (Fin m → Multiplicative (ZMod p)) => e v) hσ'eq
      exact h.symm)
  have hX : ggAutomizer X Bs = (TypeBDatum.signedAut m p).map (TypeBDatum.liftBs Θ) :=
    TypeBDatum.ggAutomizer_eq_map_liftBs Θ₁ Θ hΘ hle hge
  have hJX : J ≤ X := hJ.1.trans inf_le_left
  have hsigned : FrameBs.sectionFrameAut Θ₁ J ≤ TypeBDatum.signedAut m p :=
    TypeBDatum.sectionFrameAut_le_signedAut Θ₁ Θ hΘ hle hJX
  have hAJ : ggAutomizer J Bs = (FrameBs.sectionFrameAut Θ₁ J).map (TypeBDatum.liftBs Θ) :=
    TypeBDatum.ggAutomizer_eq_map_sectionFrameAut Θ₁ Θ hΘ hle hJX
  obtain ⟨v₀, hv₀⟩ := hact y hyB
  have hv₀1 : v₀ ≠ 1 := by
    rintro rfl
    apply hyX
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h := hv₀ g hg
    rw [map_one] at h
    have h' : y * g = g * y := by
      calc y * g = (y * g * y⁻¹) * y := by group
        _ = g * y := by rw [h]; group
    exact h'.symm
  have hcommJ : ∀ j ∈ J, Θ₁ v₀ * j = j * Θ₁ v₀ := by
    intro j hj
    have hjX : j ∈ X := hJX hj
    have hjy : y * j = j * y :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hJ.1 hj)).2 y rfl
    have h := hv₀ j hjX
    calc Θ₁ v₀ * j = Θ₁ v₀ * j * (Θ₁ v₀)⁻¹ * Θ₁ v₀ := by group
      _ = y * j * y⁻¹ * Θ₁ v₀ := by rw [h]
      _ = j * Θ₁ v₀ := by rw [hjy]; group
  have hC : ∀ c ∈ ({y} : Set G),
      ∃ v, ∀ g ∈ φ.range, c * g * c⁻¹ = hypFrame φ τ v * g * (hypFrame φ τ v)⁻¹ := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨v₀, fun g hg => hv₀ g (by simpa [hφX] using hg)⟩
  have hJc : IsComponentOf J (φ.range ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [hφX]; exact hJ
  rcases SuSplitRootGen.exists_alignedBlock_of_isComponentOf h hp2 hpq hε hζ hζb hτ hker hkp
    (C := ({y} : Set G)) hC hJc with ⟨S, hSne, hJzero⟩ | ⟨S, s, w, hsgn, hw, hS2, hJlevi⟩
  ·
    obtain ⟨hZ1, hZ2, hZ3⟩ := SuSplitRootGen.uniMinus_zeroBlock_automizer hζ hτ φ S
    have hZ1' : ∀ x ∈ J, ∀ v, (∀ i ∈ S, v i = 1) → x * Θ₁ v = Θ₁ v * x := by
      intro x hx v hv
      exact hZ1 x (by rw [← hJzero]; exact hx) v hv
    have hZ2' : ∀ i ∈ S, ∀ j ∈ S, ∃ z ∈ J, ∀ v,
        z * Θ₁ v * z⁻¹ = Θ₁ (SpCoord.permAut (p := p) (Equiv.swap i j) v) := by
      intro i hi j hj
      obtain ⟨z, hzM, hzv⟩ := hZ2 i hi j hj
      exact ⟨z, by rw [hJzero]; exact hzM, hzv⟩
    have hZ3' : ∀ i ∈ S, ∃ z ∈ J, ∀ v,
        z * Θ₁ v * z⁻¹ = Θ₁ (SpCoord.sgnAut (p := p) i v) := by
      intro i hi
      obtain ⟨z, hzM, hzv⟩ := hZ3 i hi
      exact ⟨z, by rw [hJzero]; exact hzM, hzv⟩
    have hfixZ : ∀ v, (∀ i ∈ S, v i = 1) → Θ₁ v ∈ Subgroup.centralizer (J : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact hZ1' j hj v hv
    have hcorank : m ≤ S.card + 2 :=
      le_card_add_two_of_zero_fix hBs Θ₁ hinj₁ hfr₁ hmeet₁ hzB hzX hz1 hJX hcard S hfixZ
    have hSlt : S.card < m := by
      have hle : S.card ≤ m := by simpa using S.card_le_univ
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exfalso
        have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using heq)
        have hall : ∀ i, v₀ i = 1 := by
          intro i
          have hi : i ∈ S := by rw [hSuniv]; exact Finset.mem_univ i
          obtain ⟨z', hz'J, hz'v⟩ := hZ3' i hi
          have hcw : z' * Θ₁ v₀ = Θ₁ v₀ * z' := (hcommJ z' hz'J).symm
          have h1 : Θ₁ (SpCoord.sgnAut (p := p) i v₀) = Θ₁ v₀ := by
            rw [← hz'v v₀]
            calc z' * Θ₁ v₀ * z'⁻¹ = (z' * Θ₁ v₀) * z'⁻¹ := rfl
              _ = (Θ₁ v₀ * z') * z'⁻¹ := by rw [hcw]
              _ = Θ₁ v₀ := by group
          have h2 : SpCoord.sgnAut (p := p) i v₀ = v₀ := hinj₁ h1
          have h3 : (v₀ i)⁻¹ = v₀ i := by
            have h4 := congrFun h2 i
            rw [SpCoord.sgnAut_apply, Function.update_self] at h4
            exact h4
          have hsq : v₀ i * v₀ i = 1 := by
            calc v₀ i * v₀ i = v₀ i * (v₀ i)⁻¹ := by rw [h3]
              _ = 1 := mul_inv_cancel _
          have h2ne : (2 : ZMod p) ≠ 0 := by
            intro h0
            have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h0)
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
          have h2mul : (2 : ZMod p) * toAdd (v₀ i) = 0 := by
            have hh := congrArg Multiplicative.toAdd hsq
            simp only [toAdd_mul, toAdd_one] at hh
            rw [two_mul]
            exact hh
          have hx0 : toAdd (v₀ i) = 0 := (mul_eq_zero.mp h2mul).resolve_left h2ne
          calc v₀ i = ofAdd (toAdd (v₀ i)) := (ofAdd_toAdd _).symm
            _ = 1 := by rw [hx0, ofAdd_zero]
        exact hv₀1 (funext hall)
    have hS1 : 1 ≤ S.card := by
      have h := Finset.card_pos.mpr hSne
      omega
    have hc1 : 1 ≤ m - S.card := by omega
    have hc3 : m - S.card ≤ 3 := by omega
    have hfix : ∀ x ∈ J, ∀ i ∉ S,
        x * Θ₁ (Pi.mulSingle i (ofAdd (1 : ZMod p))) * x⁻¹ = Θ₁ (Pi.mulSingle i (ofAdd 1)) := by
      intro x hx i hi
      have hv : ∀ i' ∈ S,
          (Pi.mulSingle i (ofAdd (1 : ZMod p)) : Fin m → Multiplicative (ZMod p)) i' = 1 := by
        intro i' hi'
        rw [Pi.mulSingle_apply, if_neg (show i' ≠ i by rintro rfl; exact hi hi')]
      have h := hZ1' x hx (Pi.mulSingle i (ofAdd (1 : ZMod p))) hv
      rw [h]; group
    have hswap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
        SpCoord.permAut (p := p) (Equiv.swap a b) ∈ FrameBs.sectionFrameAut Θ₁ J :=
      fun a ha b hb _ => hZ2' a ha b hb
    have hsgn' : ∀ i ∈ S, SpCoord.sgnAut (p := p) i ∈ FrameBs.sectionFrameAut Θ₁ J :=
      fun i hi => hZ3' i hi
    have heq : FrameBs.sectionFrameAut Θ₁ J = TypeBDatum.signedSupportedAut m p S :=
      TypeBDatum.sectionFrameAut_eq_signedSupportedAut hp hinj₁ S hsigned hfix hswap hsgn'
    have hJauto : ggAutomizer J Bs =
        (TypeBDatum.signedSupportedAut m p S).map (TypeBDatum.liftBs Θ) := by
      rw [hAJ, heq]
    have hres :=
      TypeBDatum.ggTBJTypeB_sideDatum_signedSupported hp2 hm hBs Θ hX hS1 hc1 hc3 hJauto
    by_cases h : m - S.card = 1
    · exact Or.inl (hres.1 h)
    · exact Or.inr (hres.2 (by omega))
  ·
    have hs : ∀ i, s i * s i = 1 := by
      intro i
      rcases hsgn i with h | h
      · rw [h, one_mul]
      · rw [h]
        show (-1 : ZMod p) * (-1) = 1
        simp
    let φ' : hypSU h m ε →* G := φ.comp (MulAut.conj w).toMonoidHom
    obtain ⟨hL1, hL2⟩ := SuSplitRootGen.uniMinus_leviBlock_automizer hτ φ' S
    have hframe' : ∀ v, hypFrame φ' τ v = Θ₁ (SpCoord.diagAut s hs v) := by
      intro v
      have h1 : hypFrame φ' τ v = φ (w * τ (ofAdd (fun i => toAdd (v i))) * w⁻¹) := by
        rw [hypFrame_eq_ofAdd φ' τ v]
        show φ ((MulAut.conj w) (τ (ofAdd (fun i => toAdd (v i))))) =
          φ (w * τ (ofAdd (fun i => toAdd (v i))) * w⁻¹)
        rw [MulAut.conj_apply]
      have h2 : Θ₁ (SpCoord.diagAut s hs v) = φ (τ (ofAdd (fun i => s i * toAdd (v i)))) := by
        have hΘ₁ : Θ₁ (SpCoord.diagAut s hs v) = hypFrame φ τ (SpCoord.diagAut s hs v) := rfl
        rw [hΘ₁, hypFrame_eq_ofAdd φ τ (SpCoord.diagAut s hs v)]
        congr 1
      rw [h1, h2, hw (fun i => toAdd (v i))]
    have hdiag : ∀ x, SpCoord.diagAut s hs (SpCoord.diagAut s hs x) = x := by
      intro x
      funext i
      rw [SpCoord.diagAut_apply, SpCoord.diagAut_apply, toAdd_ofAdd, ← mul_assoc, hs i,
        one_mul, ofAdd_toAdd]
    have hΘ'inj : Function.Injective (hypFrame φ' τ) := by
      intro u v huv
      have h1 : Θ₁ (SpCoord.diagAut s hs u) = Θ₁ (SpCoord.diagAut s hs v) := by
        rw [← hframe' u, ← hframe' v]
        exact huv
      have h2 : SpCoord.diagAut s hs u = SpCoord.diagAut s hs v := hinj₁ h1
      have h3 := congrArg (SpCoord.diagAut s hs) h2
      simpa [hdiag] using h3
    have hΘ'B : ∀ v, hypFrame φ' τ v ∈ Bs := by
      intro v
      rw [hframe']
      exact hfr₁ _
    have hΘ'X : ∀ v, hypFrame φ' τ v ∈ Subgroup.centralizer (X : Set G) → v = 1 := by
      intro v hv
      have h1 : SpCoord.diagAut s hs v = 1 := by
        refine hmeet₁ _ ?_
        rwa [← hframe']
      calc v = SpCoord.diagAut s hs (SpCoord.diagAut s hs v) := (hdiag v).symm
        _ = 1 := by rw [h1, map_one]
    have hfixL : ∀ v, (∀ i ∈ S, ∀ j ∈ S, v i = v j) →
        hypFrame φ' τ v ∈ Subgroup.centralizer (J : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hL1 x (by rw [← hJlevi]; exact hx) v hv
    have hcorank : m ≤ S.card + 1 :=
      le_card_add_one_of_levi_fix hBs (hypFrame φ' τ) hΘ'inj hΘ'B hΘ'X hzB hzX hz1 hJX hcard
        (Finset.card_pos.mp (by omega)) hfixL
    have hfix : ∀ x ∈ J, ∀ i ∉ S,
        x * Θ₁ (Pi.mulSingle i (ofAdd (1 : ZMod p))) * x⁻¹ = Θ₁ (Pi.mulSingle i (ofAdd 1)) := by
      intro x hx i hi
      have hv : ∀ i' ∈ S, ∀ j ∈ S,
          (SpCoord.diagAut s hs (Pi.mulSingle i (ofAdd (1 : ZMod p)))) i' =
            (SpCoord.diagAut s hs (Pi.mulSingle i (ofAdd (1 : ZMod p)))) j := by
        intro i' hi' j hj
        rw [SpCoord.diagAut_apply, SpCoord.diagAut_apply]
        have h1 : (Pi.mulSingle i (ofAdd (1 : ZMod p)) : Fin m → Multiplicative (ZMod p)) i' =
            1 := by
          rw [Pi.mulSingle_apply, if_neg (show i' ≠ i by rintro rfl; exact hi hi')]
        have h2 : (Pi.mulSingle i (ofAdd (1 : ZMod p)) : Fin m → Multiplicative (ZMod p)) j =
            1 := by
          rw [Pi.mulSingle_apply, if_neg (show j ≠ i by rintro rfl; exact hi hj)]
        rw [h1, h2, toAdd_one, mul_zero, mul_zero]
      have h := hL1 x (by rw [← hJlevi]; exact hx)
        (SpCoord.diagAut s hs (Pi.mulSingle i (ofAdd (1 : ZMod p)))) hv
      rw [hframe', hdiag] at h
      rw [h]; group
    have hvec : ∀ x ∈ J,
        x * Θ₁ (fun j => if j ∈ S then ofAdd (s j) else 1) * x⁻¹ =
          Θ₁ (fun j => if j ∈ S then ofAdd (s j) else 1) := by
      intro x hx
      have hv : ∀ i ∈ S, ∀ j ∈ S,
          (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) i =
            (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) j := by
        intro i hi j hj
        rw [show (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) i = ofAdd 1 from if_pos hi,
          show (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) j = ofAdd 1 from if_pos hj]
      have h := hL1 x (by rw [← hJlevi]; exact hx)
        (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) hv
      have hvec_eq : SpCoord.diagAut s hs (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) =
          fun j => if j ∈ S then ofAdd (s j) else 1 := by
        funext j
        rw [SpCoord.diagAut_apply]
        by_cases hj : j ∈ S
        · rw [if_pos hj, if_pos hj, toAdd_ofAdd, mul_one]
        · rw [if_neg hj, if_neg hj, toAdd_one, mul_zero, ofAdd_zero]
      rw [hframe', hvec_eq] at h
      rw [h]; group
    have hgen : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
        SpCoord.diagAut s hs * SpCoord.permAut (p := p) (Equiv.swap a b) *
          (SpCoord.diagAut s hs)⁻¹ ∈ FrameBs.sectionFrameAut Θ₁ J := by
      intro a ha b hb hab
      obtain ⟨z, hzJ, hzv⟩ := hL2 a ha b hb
      refine ⟨z, by rw [hJlevi]; exact hzJ, ?_⟩
      intro v
      have hv : hypFrame φ' τ ((SpCoord.diagAut s hs)⁻¹ v) = Θ₁ v := by
        rw [hframe', MulAut.apply_inv_self]
      have h := hzv ((SpCoord.diagAut s hs)⁻¹ v)
      rw [hv, hframe'] at h
      rw [h]
      congr 1
    have heq : FrameBs.sectionFrameAut Θ₁ J = TypeBDatum.twistedPermAut m p S s hs :=
      TypeBDatum.sectionFrameAut_eq_twistedPermAut hp hinj₁ S s hs hsgn hsigned hfix hvec hgen
    have hJauto : ggAutomizer J Bs =
        (TypeBDatum.twistedPermAut m p S s hs).map (TypeBDatum.liftBs Θ) := by
      rw [hAJ, heq]
    have hSm : S.card ≤ m := by simpa using S.card_le_univ
    have hc3 : m + 1 - S.card ≤ 3 := by omega
    have hres := TypeBDatum.ggTBJTypeB_sideDatum_twistedPerm hp2 hm hBs Θ hX hS2 hc3 hs
      hJauto
    by_cases h : m + 1 - S.card = 1
    · exact Or.inl (hres.1 h)
    · exact Or.inr (hres.2 (by omega))

end CFSG.StandardType

end
