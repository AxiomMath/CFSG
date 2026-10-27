module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSelModule
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitPermLe
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameModule
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCfg
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain
import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeSurj
import CFSG.LocalAnalysis.StandardType.GGNSJoinToralA

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnit_base_full {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G} {m : ℕ}
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] (hF0 : Nat.card F0 = 4)
    {ψ : Su F0 2 1 m →* G} (h : GGNSLocalHyp p B Bs F0 1 m ψ) (hψ : ψ.range = L)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs) (hcard : Nat.card ↥Bs = 3 ^ m)
    (hcent : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hx : orderOf x = 3) :
    ∀ c : Fin m → F0ˣ, ∃ b ∈ Bs, qTwoChartTwoThree_induces ψ b c := by
  have hmodel : QTwoOrdModel Bs L ψ :=
    ⟨hψ, h.ker, fun b => by
      obtain ⟨g, hg, hgu⟩ := hd (b : G) b.2
      exact ⟨g, hg, fun u => by
        obtain ⟨u', hu'1, hu'2⟩ := hgu.2 u
        exact ⟨u', hu'1, hu'2.symm⟩⟩⟩
  have hdiag : ∀ b : ↥Bs, ∃ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ (b : G) c :=
    fun b => qTwoChartTwoThree_induces_of_ordModel hmodel b
  have hcent' : Nat.card {b : ↥Bs // ∀ u : Su F0 2 1 m,
      (b : G) * ψ u * (b : G)⁻¹ = ψ u} ≤ 3 := by
    have hle : Nat.card {b : ↥Bs // ∀ u : Su F0 2 1 m,
        (b : G) * ψ u * (b : G)⁻¹ = ψ u} ≤
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := by
      refine Nat.card_le_card_of_injective
        (fun b => (⟨(b : G), Subgroup.mem_inf.mpr ⟨b.1.2, ?_⟩⟩ :
          ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))) ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [← hψ] at hy
        obtain ⟨u, rfl⟩ := hy
        exact (mul_inv_eq_iff_eq_mul.mp (b.2 u)).symm
      · intro b b' hb
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) => (z : G)) hb
    calc Nat.card {b : ↥Bs // ∀ u : Su F0 2 1 m,
          (b : G) * ψ u * (b : G)⁻¹ = ψ u}
        ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := hle
      _ = Nat.card ↥(Subgroup.zpowers x) := by rw [hcent]
      _ = orderOf x := Nat.card_zpowers x
      _ = 3 := hx
  intro c
  obtain ⟨b, hb⟩ := qTwoChartTwoThree_exists_induces_aux hF0
    (by have := h.four_le; omega) ψ hdiag hcard hcent' c
  exact ⟨b, b.2, hb⟩


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}

theorem ggQTwoDUnit_base_cent (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hp : p = 3) :
    x ∈ Bs ∧ orderOf x = 3 ∧ Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSStar : LargeEvenSStar p B x L := hcfg.1.1.1.1.2.2.2.2.2.2.1
  have hGstar : GGBstar p B Bs := hcfg.1.1.1.2.1
  have hxBs : x ∈ Bs := hGstar.1 hSStar.2.1
  have hxne : x ≠ 1 := hSStar.2.2.1
  have helem : CFSG.Open.IsElemAbelian p Bs := hGstar.2.1
  have hx3 : x ^ 3 = 1 := by
    have h := helem.2 x hxBs
    rwa [hp] at h
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  refine ⟨hxBs, hxord, ?_⟩
  have hcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hSStar.2.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hSStar.2.2.2.2
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hcomp.1 hl) x (Set.mem_singleton x)).symm
  set S : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G) with hSdef
  have hxS : x ∈ S := Subgroup.mem_inf.mpr ⟨hxBs, hxcent⟩
  have hSp : IsPGroup p S := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have hg := helem.2 (g : G) g.2.1
    simpa using hg
  have hScyc : IsCyclic S := hcyc S inf_le_right hSp
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hScyc
  have hcardS : Nat.card S = p := by
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      exact helem.2 (g : G) g.2.1
    have hdvd : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgp
    have hcard : Nat.card S = orderOf g := by
      rw [← Nat.card_zpowers g, hg, Subgroup.card_top]
    have hple : p ≤ Nat.card S := by
      have hzx : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxS
      calc p = orderOf x := hp.trans hxord.symm
        _ = Nat.card ↥(Subgroup.zpowers x) := (Nat.card_zpowers x).symm
        _ ≤ Nat.card S :=
            Nat.card_le_card_of_injective (Subgroup.inclusion hzx)
              (Subgroup.inclusion_injective hzx)
    have hdvd' : Nat.card S ∣ p := by rw [hcard]; exact hdvd
    exact le_antisymm (Nat.le_of_dvd (by omega) hdvd') hple
  have hzx : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxS
  have hcard_zx : Nat.card ↥(Subgroup.zpowers x) = Nat.card S := by
    rw [Nat.card_zpowers, hxord, hcardS, hp]
  exact (Subgroup.eq_of_le_of_card_ge hzx (le_of_eq hcard_zx.symm)).symm

theorem ggQTwoDUnit_base_n_eq (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hp : p = 3) (e' : Fin m ≃ ι) (hm : 5 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) (hψ : ψ.range = L)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer L Bs))
    (hperm : ∀ (σ : Equiv.Perm (Fin n)) (s : ↥Bs),
      ((((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s : ↥Bs) : G) =
        ψ (ggPermSU σ⁻¹) * (s : G) * (ψ (ggPermSU σ⁻¹))⁻¹)
    (hrefl : ∀ a b : Fin n, a ≠ b →
      GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) :
    n = m := by
  obtain ⟨β, -⟩ := ggQTwoD_selectedModule hTBF hWI (hp ▸ hcfg) e' (by omega) hM
  have hcardAdd : Nat.card (Additive ↥Bs) = Nat.card ↥Bs :=
    (Nat.card_congr (Additive.ofMul (α := ↥Bs))).symm
  have hcardDVec : Nat.card (DVec m) = 3 ^ m := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hcardBs : Nat.card ↥Bs = 3 ^ m := by
    rw [← hcardAdd, Nat.card_congr β.toEquiv, hcardDVec]
  have hcent := ggQTwoDUnit_base_cent hcfg hp
  have hcardCent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) = 3 := by
    rw [hψ, hcent.2.2, Nat.card_zpowers, hcent.2.1]
  have hle : 3 ^ m ≤ 3 ^ n := by
    calc 3 ^ m = Nat.card ↥Bs := hcardBs.symm
      _ ≤ p ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) :=
          ggNSDiag_toral_bound h hd
      _ = 3 ^ (n - 1) * 3 := by rw [hp, hcardCent]
      _ = 3 ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel (le_trans (by norm_num : 1 ≤ 4) h.four_le)]
  have hmn : m ≤ n := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hnm : n ≤ m := by
    subst hp
    subst hM
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hrc : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
    obtain ⟨V, iA, iM, ⟨ι'⟩⟩ := exists_ggLinData (ggRouteCfg_isElemAbelian hrc)
    haveI : Finite V := Finite.of_equiv _ ι'.toEquiv
    obtain ⟨Θ, ϑ, hϑ, hact⟩ :=
      ggQTwoDFrame_module hrc (by omega) e' hcfg.2.2.2.1 ι' (ggQTwoD_fix hTBF hWI hrc)
    let φ : Equiv.Perm (Fin n) →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
      { toFun := fun σ => (Θ.trans (ggLin (p := 3) ι'
          ((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))).trans Θ.symm
        map_one' := by
          refine LinearEquiv.ext fun v => ?_
          simp
        map_mul' := fun σ τ => by
          refine LinearEquiv.ext fun v => ?_
          simp [LinearEquiv.mul_apply] }
    have hφ : ∀ σ v, φ σ v = Θ.symm (ggLin (p := 3) ι'
        ((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) (Θ v)) := fun _ _ => rfl
    refine ggQTwoDUnit_perm_le (by omega) φ ?_ ?_
    · intro σ τ hστ
      apply ε.injective
      apply Subtype.ext
      apply ggLin_injective (p := 3) ι'
      refine LinearEquiv.ext fun w => ?_
      have h1 := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T (Θ.symm w)) hστ
      simp only [hφ, LinearEquiv.apply_symm_apply] at h1
      simpa using congrArg Θ h1
    · intro a b hab
      have hmemJ : ((ε (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈
          ggAutomizerJoin L Bs 𝒦 := le_sup_left (a := ggAutomizer L Bs) (ε (Equiv.swap a b)).2
      obtain ⟨sgn, a', b', hab', hv⟩ :=
        ggQTwoD_refl_conj hrc (by omega) e' hcfg.2.2.2.1 ι' hϑ hact hmemJ (hrefl a b hab)
      refine ⟨sgn, a', b', hab', LinearEquiv.ext fun v => ?_⟩
      rw [hφ, hv, LinearEquiv.symm_apply_apply]
  omega

end CFSG.StandardType.QTwo

end
