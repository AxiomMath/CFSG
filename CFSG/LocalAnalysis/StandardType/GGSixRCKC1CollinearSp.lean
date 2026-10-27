module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearShort
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Transport
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISpSurvivor
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISpBlock
public import CFSG.ClassicalGroups.Symplectic.ShortRootLineElt
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSp

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
  CFSG.ComponentClassification.RankTwoOddLie CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.StandardType.RCKK1IIISp

private theorem rckPSp_long_of_rank_le_one {m : ℕ} {F : Type} [Field F]
    {β : Fin m → ℤ} (hβ : β ∈ (Symplectic.rootDatum m F).roots) (hm : m ≤ 1) :
    GGLongRoot (Symplectic.rootDatum m F) β := by
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hβ
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · refine CFSG.StandardType.LieKnownR2.Geo.ggLongRoot_of_allEven hβ ?_
    intro a
    rw [← hr]
    change Even ((2 : ℤ) * (Pi.single i (1 : ℤ) : Fin m → ℤ) a)
    exact even_two_mul _
  · refine CFSG.StandardType.LieKnownR2.Geo.ggLongRoot_of_allEven hβ ?_
    intro a
    rw [← hr]
    change Even (-((2 : ℤ) * (Pi.single i (1 : ℤ) : Fin m → ℤ) a))
    exact Even.neg (even_two_mul _)
  · exact absurd (Fin.ext (by omega)) hij
  · exfalso
    omega
  · exfalso
    omega

theorem exists_spSiegel_of_mem_rootGroup {m : ℕ}
    {β : Fin (Symplectic.rootDatum m (GaloisField 2 1)).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum m (GaloisField 2 1)).roots)
    (hs : ¬ GGLongRoot (Symplectic.rootDatum m (GaloisField 2 1)) β)
    {x : ↥(CFSG.Open.StatedSp m (GaloisField 2 1))}
    (hx : x ∈ (Symplectic.rootDatum m (GaloisField 2 1)).rootGroup β) (hx1 : x ≠ 1) :
    ∃ a b : Fin m ⊕ Fin m → GaloisField 2 1,
      RCKK1IIISp.spB m a b = 0 ∧ RCKK1IIISp.SpSiegel a b x := by
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hβ
  obtain ⟨c, rfl⟩ := (SpExtras.mem_rootGroup_iff (F := GaloisField 2 1) hr).mp hx
  have hc : c ≠ 0 := by
    intro hc0
    exact hx1 (by rw [hc0, SpExtras.elt_zero])
  have hc1 : c = 1 := by
    rcases rck1416_gf2_eq_zero_or_one c with h0 | h1
    · exact absurd h0 hc
    · exact h1
  subst c
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · exfalso
    apply hs
    refine CFSG.StandardType.LieKnownR2.Geo.ggLongRoot_of_allEven hβ ?_
    intro a
    rw [← hr]
    change Even ((2 : ℤ) * (Pi.single i (1 : ℤ) : Fin m → ℤ) a)
    exact even_two_mul _
  · exfalso
    apply hs
    refine CFSG.StandardType.LieKnownR2.Geo.ggLongRoot_of_allEven hβ ?_
    intro a
    rw [← hr]
    change Even (-((2 : ℤ) * (Pi.single i (1 : ℤ) : Fin m → ℤ) a))
    exact Even.neg (even_two_mul _)
  · refine ⟨Pi.single (Sum.inr j) 1, Pi.single (Sum.inl i) 1, ?_, ?_⟩
    · rw [spB_eq_spBilin, spForm_apply_single_inl]
      simp [Pi.single_apply, Ne.symm hij]
    · intro v
      have h := spEquiv_elt_difference i j hij (1 : GaloisField 2 1)
      rw [show spAct (SpExtras.elt (.difference i j hij) 1) v =
          (spEquiv (SpExtras.elt (.difference i j hij) 1)).app v from rfl, h]
      rw [lineElt_app spForm_isAlt (by
        rw [spForm_apply_single_inr]
        simp [Pi.single_apply, hij])]
      rw [spB_symm (m := m) (Pi.single (Sum.inl i) 1) v,
        spB_symm (m := m) (Pi.single (Sum.inr j) 1) v]
      simpa only [spB_eq_spBilin]
  · refine ⟨Pi.single (Sum.inl j) 1, Pi.single (Sum.inl i) 1, ?_, ?_⟩
    · rw [spB_eq_spBilin, spForm_apply_single_inl]
      simp
    · intro v
      have h := spEquiv_elt_positiveSum i j hij (1 : GaloisField 2 1)
      rw [show spAct (SpExtras.elt (.positiveSum i j hij) 1) v =
          (spEquiv (SpExtras.elt (.positiveSum i j hij) 1)).app v from rfl, h]
      rw [lineElt_app spForm_isAlt (by
        rw [spForm_apply_single_inl]
        simp)]
      rw [spB_symm (m := m) (Pi.single (Sum.inl i) 1) v,
        spB_symm (m := m) (Pi.single (Sum.inl j) 1) v]
      simpa only [spB_eq_spBilin]
  · refine ⟨Pi.single (Sum.inr j) 1, Pi.single (Sum.inr i) 1, ?_, ?_⟩
    · rw [spB_eq_spBilin, spForm_apply_single_inr]
      simp
    · intro v
      have h := spEquiv_elt_negativeSum i j hij (1 : GaloisField 2 1)
      rw [show spAct (SpExtras.elt (.negativeSum i j hij) 1) v =
          (spEquiv (SpExtras.elt (.negativeSum i j hij) 1)).app v from rfl, h]
      rw [lineElt_app spForm_isAlt (by
        rw [spForm_apply_single_inr]
        simp)]
      rw [spB_symm (m := m) (Pi.single (Sum.inr i) 1) v,
        spB_symm (m := m) (Pi.single (Sum.inr j) 1) v]
      simpa only [spB_eq_spBilin]

private theorem rckPSp_collinear_one {m : ℕ} (hm : 2 ≤ m)
    {β : Fin m → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum m (GaloisField 2 1)).roots)
    (hs : ¬ GGLongRoot (Symplectic.rootDatum m (GaloisField 2 1)) β) :
    RCKCollinearVia ⟨StatedSp m (GaloisField 2 1),
      Symplectic.rootDatum m (GaloisField 2 1)⟩ β := by
  intro X _ _ K R V hR hR2 r hr hr1 hrV hVK hVab hV4 hconj
  obtain ⟨φ, hφrange, hφker, u, hRu⟩ := hR
  have hcenter : Subgroup.center (StatedSp m (GaloisField 2 1)) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := m) (by omega)
  have hφker' : φ.ker = ⊥ := le_bot_iff.mp (hφker.trans (le_of_eq hcenter))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hφker'
  let eφ : StatedSp m (GaloisField 2 1) ≃* ↥K :=
    (MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφrange)
  let e : ↥K ≃* StatedSp m (GaloisField 2 1) := eφ.symm
  have heφ_val (z : StatedSp m (GaloisField 2 1)) : (eφ z : X) = φ z := rfl
  have hRK : R ≤ K := by
    rw [hRu]
    exact (Subgroup.map_le_range φ _).trans (le_of_eq hφrange)
  have hrK : r ∈ K := hRK hr
  rw [hRu] at hr
  obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp hr
  obtain ⟨x0, hx0mem, hx0y⟩ := Subgroup.mem_map.mp hy
  have hrval : r = φ (u * x0 * u⁻¹) := by
    rw [← hyr, ← hx0y]
    change φ ((MulAut.conj u) x0) = φ (u * x0 * u⁻¹)
    rw [MulAut.conj_apply]
  have hx0ne : x0 ≠ 1 := by
    intro h1
    apply hr1
    rw [hrval, h1]
    simp
  obtain ⟨a, b, hBab, hx0Siegel⟩ :=
    exists_spSiegel_of_mem_rootGroup hβ hs hx0mem hx0ne
  have he_r : e ⟨r, hrK⟩ = u * x0 * u⁻¹ := by
    have h1 : eφ (u * x0 * u⁻¹) = ⟨r, hrK⟩ := by
      apply Subtype.ext
      rw [heφ_val]
      exact hrval.symm
    calc e ⟨r, hrK⟩ = e (eφ (u * x0 * u⁻¹)) := by rw [h1]
      _ = u * x0 * u⁻¹ := MulEquiv.symm_apply_apply eφ _
  have hpres : ∀ (g : StatedSp m (GaloisField 2 1)) (x y : SpMod m),
      spB m (spAct g x) (spAct g y) = spB m x y := by
    intro g x y
    rw [spB_eq_spForm, spB_eq_spForm, spAct_eq_natRep, spAct_eq_natRep]
    exact CFSG.LieType.BorelTits.isIsometric_natRep_statedSp m (GaloisField 2 1) g x y
  have hpure : ∀ v ∈ (V.subgroupOf K).map e.toMonoidHom, v ≠ 1 →
      ∃ x y : SpMod m, spB m x y = 0 ∧ SpSiegel x y v := by
    intro v hv hv1
    obtain ⟨vK, hvK, hv_eq⟩ := Subgroup.mem_map.mp hv
    have hvV : (vK : X) ∈ V := Subgroup.mem_subgroupOf.mp hvK
    have hvne : (vK : X) ≠ 1 := by
      intro h1
      apply hv1
      calc v = e vK := hv_eq.symm
        _ = e 1 := by rw [show vK = 1 from Subtype.ext h1]
        _ = 1 := map_one e
    obtain ⟨k, hkK, hvk⟩ := hconj (vK : X) hvV hvne
    have hv_eq2 : v = e ⟨k, hkK⟩ * e ⟨r, hrK⟩ * (e ⟨k, hkK⟩)⁻¹ := by
      calc v = e vK := hv_eq.symm
        _ = e (⟨k, hkK⟩ * ⟨r, hrK⟩ * ⟨k, hkK⟩⁻¹) := by
            congr 1
            exact Subtype.ext hvk
        _ = e ⟨k, hkK⟩ * e ⟨r, hrK⟩ * (e ⟨k, hkK⟩)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
    have he_r_siegel : SpSiegel (spAct u a) (spAct u b) (e ⟨r, hrK⟩) := by
      rw [he_r]
      exact spSiegel_conj hx0Siegel u
    refine ⟨spAct (e ⟨k, hkK⟩) (spAct u a), spAct (e ⟨k, hkK⟩) (spAct u b), ?_, ?_⟩
    · rw [hpres (e ⟨k, hkK⟩) (spAct u a) (spAct u b), hpres u a b, hBab]
    · rw [hv_eq2]
      exact spSiegel_conj he_r_siegel (e ⟨k, hkK⟩)
  have hVab' : IsElemAbelian 2 ((V.subgroupOf K).map e.toMonoidHom) :=
    (hVab.subgroupOf K).map e.toMonoidHom
  have hV4' : Nat.card ((V.subgroupOf K).map e.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv]
    exact hV4
  have hrV' : e ⟨r, hrK⟩ ∈ (V.subgroupOf K).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hrV
  have hr1' : e ⟨r, hrK⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨r, hrK⟩ : ↥K) = 1 := e.injective (by simpa using h1)
    exact hr1 (congrArg Subtype.val h2)
  exact k2At_of_pure_sp_model
    (three_le_rank_of_pure_shortRoot_fourGroup hrV' hr1' hVab' hV4' hpure)
    e hrK hrV hr1 hVK hVab hV4 hpure

theorem rckCollinearVia_PSp_short
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .PSp m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .PSp m g).D.roots) (hs : ¬ GGLongRoot (ggU .PSp m g).D β) :
    RCKCollinearVia (ggU .PSp m g) β := by
  change RCKCollinearVia ⟨StatedSp m (GaloisField 2 g),
    Symplectic.rootDatum m (GaloisField 2 g)⟩ β
  change β ∈ (Symplectic.rootDatum m (GaloisField 2 g)).roots at hβ
  change ¬ GGLongRoot (Symplectic.rootDatum m (GaloisField 2 g)) β at hs
  by_cases hm1 : m ≤ 1
  · exact absurd (rckPSp_long_of_rank_le_one hβ hm1) hs
  have hm2 : 2 ≤ m := by omega
  by_cases hg2 : 2 ≤ g
  · have hZ : CenterPPrime (StatedSp m (GaloisField 2 g)) 2 :=
      CFSG.ComponentClassification.RankTwoOddLie.centerPPrime_statedSp
        m (GaloisField 2 g)
    have hX : IsPGroup 2 ((Symplectic.rootDatum m (GaloisField 2 g)).rootGroup β) := by
      obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hβ
      intro x
      have hxmem : (x : StatedSp m (GaloisField 2 g)) ∈
          Symplectic.rootGroup m (GaloisField 2 g) β := x.2
      obtain ⟨c, hc⟩ :=
        (SpExtras.mem_rootGroup_iff (F := GaloisField 2 g) hr).mp hxmem
      refine ⟨1, ?_⟩
      apply Subtype.ext
      show (x : StatedSp m (GaloisField 2 g)) ^ 2 ^ 1 = 1
      rw [hc, pow_one, sq, ← SpExtras.elt_add, CharTwo.add_self_eq_zero,
        SpExtras.elt_zero]
    have hcard : Nat.card ((Symplectic.rootDatum m (GaloisField 2 g)).rootGroup β) =
        Nat.card (GaloisField 2 g) := by
      obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hβ
      let f : GaloisField 2 g →
          (Symplectic.rootDatum m (GaloisField 2 g)).rootGroup β := fun c =>
        ⟨SpExtras.elt r c,
          (SpExtras.mem_rootGroup_iff (F := GaloisField 2 g) hr).2 ⟨c, rfl⟩⟩
      have hf : Function.Injective f := by
        intro c d hcd
        exact SpExtras.elt_injective r (congrArg Subtype.val hcd)
      have hsurj : Function.Surjective f := by
        intro x
        obtain ⟨c, hc⟩ :=
          (SpExtras.mem_rootGroup_iff (F := GaloisField 2 g) hr).1 x.2
        exact ⟨c, Subtype.ext hc.symm⟩
      exact (Nat.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)).symm
    have hc2 : Nat.card ((Symplectic.rootDatum m (GaloisField 2 g)).rootGroup β) ≠ 2 := by
      rw [hcard, GaloisField.card 2 g (by omega)]
      have h4 : 4 ≤ 2 ^ g := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      omega
    exact rckCollinearVia_of_card_ne_two hZ hX hc2
  · have hg1 : g = 1 := by omega
    subst hg1
    exact rckPSp_collinear_one hm2 hβ hs

end CFSG.StandardType.RCKC1
