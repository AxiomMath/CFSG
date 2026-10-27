module

public import CFSG.LocalAnalysis.StandardType.KGLangT3Defs
public import CFSG.LocalAnalysis.StandardType.KGLangT3Bridge
public import CFSG.LocalAnalysis.StandardType.KGLangT3ShortSL2
public import CFSG.LocalAnalysis.StandardType.KGLangT3ShortConj
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec11


private lemma l02qj5b1_perfect_of_isComponent {G : Type*} [Group G] {J C : Subgroup G}
    (hJ : IsComponentOf J C) : ⁅J, J⁆ = J := by
  have hmap : (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
    unfold commutator
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have htop : (commutator ↥J).map J.subtype = J := by
    rw [hJ.2.2.1, Subgroup.map_top, Subgroup.range_subtype]
  rwa [hmap] at htop

private lemma l02qj5b1_centralizer_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G) :
    (Subgroup.centralizer ({z} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set H) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    calc e z * e y = e (z * y) := (map_mul e z y).symm
      _ = e (y * z) := by rw [hy z rfl]
      _ = e y * e z := map_mul e y z
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hx (e z) rfl

private lemma l02qj5b1_centralizer_conj {G : Type*} [Group G] (g z : G) :
    (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  rw [l02qj5b1_centralizer_map (MulAut.conj g) z, MulAut.conj_apply]

private noncomputable def l02qj5b1_centerQuotEquiv {G H : Type*} [Group G] [Group H]
    {J : Subgroup G} {J' : Subgroup H} (e : ↥J ≃* ↥J') :
    ↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J' :=
  QuotientGroup.congr (G' := Subgroup.center ↥J) (H' := Subgroup.center ↥J')
    e (Subgroup.map_center_eq e)

private theorem l02qj5b1_lemmaA {K : Type} [Field K] [Finite K] [CharP K 2]
    (q : ℕ) (σ : K ≃+* K) (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q)
    (h3q : ¬ 3 ∣ q) (hσ3 : σ ^ 3 = 1)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (J : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hJ : IsComponentOf J (Subgroup.centralizer ({z} :
      Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))))
    (E : Type) [Field E] [Finite E]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E)) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      g * z * g⁻¹ ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
  obtain ⟨g, hg | hg⟩ := KS11Lie6Proof.d4ThreeConj_holds K q σ hK hσ h3q z hz3 hz1
  · exact ⟨g, hg⟩
  · exfalso
    set z' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := g * z * g⁻¹ with hz'def
    have hz'3 : z' ^ 3 = 1 := by
      rw [hz'def]
      calc (g * z * g⁻¹) ^ 3 = ((MulAut.conj g) z) ^ 3 := by rw [MulAut.conj_apply]
        _ = (MulAut.conj g) (z ^ 3) := (map_pow (MulAut.conj g) z 3).symm
        _ = g * z ^ 3 * g⁻¹ := by rw [MulAut.conj_apply]
        _ = 1 := by rw [hz3]; group
    have hz'1 : z' ≠ 1 := by
      intro hh
      apply hz1
      have h := congrArg (fun t => g⁻¹ * t * g) hh
      rw [hz'def] at h
      have hz : z = 1 := by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := h
          _ = 1 := by group
      exact hz
    set J' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      J.map (MulAut.conj g).toMonoidHom with hJ'def
    have hcomp : IsComponentOf J' (Subgroup.centralizer ({z'} :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
      have h1 := isComponentOf_map_mulEquiv' (MulAut.conj g) hJ
      rw [← hJ'def, l02qj5b1_centralizer_conj g z] at h1
      rwa [← hz'def] at h1
    have hJ'le : J' ≤ Subgroup.centralizer ({z'} :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hcomp.1
    have hperf : ⁅J', J'⁆ = J' := l02qj5b1_perfect_of_isComponent hcomp
    have hBC := KS11Lie6Proof.d4ThreeBCent_holds K q σ hK hσ h3q z' hg hz'3 hz'1
    have hcommS : ⁅Subgroup.centralizer ({z'} :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          Subgroup.centralizer ({z'} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ ≤
        KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
      Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact hBC.1 x hx y hy
    have hJ'sub : J' ≤ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
      rw [← hperf]
      exact (Subgroup.commutator_mono hJ'le hJ'le).trans hcommS
    have hquo : ↥J' ⧸ Subgroup.center ↥J' ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin 3) E) :=
      (l02qj5b1_centerQuotEquiv (Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective)).symm.trans θ
    exact kgLangT3_not_psl3_in_short hσ3 J' hJ'sub E hquo

theorem kgLangT3_conj_z0 {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n)
    (D : TriD4LineKGXData n K k) (h : GGTriD4R n K) (h1 : h ≠ 1) (h3 : h ^ 3 = 1)
    (J₀ : Subgroup (GGTriD4R n K))
    (hJ : IsComponentOf J₀ (Subgroup.centralizer ({h} : Set (GGTriD4R n K))))
    (E : Type) [Field E] [Finite E]
    (θ₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E)) :
    ∃ g : GGTriD4R n K, g * h * g⁻¹ = D.z₀ := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 3 (pow_ne_zero n (by norm_num)))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite k := Nat.finite_of_card_ne_zero (by
    rw [hk]
    exact pow_ne_zero n (by norm_num))
  have hn1 : 1 ≤ n := by omega
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := CFSG.StandardType.TableBExcSmallRest.nonempty_triD4_equiv hn1 K hK σ hσ
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    show (σ ^ 3) c = c
    rw [RingAut.coe_pow]
    have hiter : (σ^[3]) c = σ (σ (σ c)) := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rw [hiter, hσ, hσ, hσ]
    have hpow : ((c ^ 2 ^ n) ^ 2 ^ n) ^ 2 ^ n = c ^ Nat.card K := by
      have hL : ((c ^ 2 ^ n) ^ 2 ^ n) ^ 2 ^ n = c ^ ((2 ^ n * 2 ^ n) * 2 ^ n) := by
        rw [pow_mul, pow_mul]
      rw [hL]
      have hexp : 2 ^ n * 2 ^ n * 2 ^ n = (2 ^ n) ^ 3 := by ring
      rw [hexp, ← hK]
    rw [hpow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have h3q : ¬ 3 ∣ 2 ^ n := by
    intro h
    have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h32
  have hJh_map : IsComponentOf (J₀.map e.toMonoidHom)
      ((Subgroup.centralizer ({h} : Set (GGTriD4R n K))).map e.toMonoidHom) :=
    isComponentOf_map_mulEquiv' e hJ
  have hJh : IsComponentOf (J₀.map e.toMonoidHom)
      (Subgroup.centralizer ({e h} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
    rwa [l02qj5b1_centralizer_map e h] at hJh_map
  have heh3 : (e h) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have heh1 : e h ≠ 1 := by
    intro hh
    exact h1 (e.injective (by rw [hh, map_one]))
  have hθh : ↥(J₀.map e.toMonoidHom) ⧸ Subgroup.center ↥(J₀.map e.toMonoidHom) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 3) E) :=
    (l02qj5b1_centerQuotEquiv (Subgroup.equivMapOfInjective J₀ e.toMonoidHom
      e.injective)).symm.trans θ₀
  obtain ⟨g₁, hg₁⟩ := l02qj5b1_lemmaA (2 ^ n) σ hK hσ h3q hσ3 heh3 heh1
    (J₀.map e.toMonoidHom) hJh E hθh
  have hz₀3 : D.z₀ ^ 3 = 1 := by
    rw [← D.orderOf_z₀]
    exact pow_orderOf_eq_one D.z₀
  have hz₀1 : D.z₀ ≠ 1 := by
    intro hh
    have h1' : orderOf D.z₀ = 1 := by rw [hh, orderOf_one]
    rw [D.orderOf_z₀] at h1'
    omega
  obtain ⟨Jz, hJz⟩ := kgLangT3_exists_component K k D
  obtain ⟨ιz, _⟩ := kgLangT3_component_equiv K k D Jz hJz
  have hJz_map : IsComponentOf (Jz.map e.toMonoidHom)
      ((Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))).map e.toMonoidHom) :=
    isComponentOf_map_mulEquiv' e hJz
  have hJz' : IsComponentOf (Jz.map e.toMonoidHom)
      (Subgroup.centralizer ({e D.z₀} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
    rwa [l02qj5b1_centralizer_map e D.z₀] at hJz_map
  have hez3 : (e D.z₀) ^ 3 = 1 := by rw [← map_pow, hz₀3, map_one]
  have hez1 : e D.z₀ ≠ 1 := by
    intro hh
    exact hz₀1 (e.injective (by rw [hh, map_one]))
  have hθz : ↥(Jz.map e.toMonoidHom) ⧸ Subgroup.center ↥(Jz.map e.toMonoidHom) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 3) k) :=
    (l02qj5b1_centerQuotEquiv (Subgroup.equivMapOfInjective Jz e.toMonoidHom
      e.injective)).symm.trans ιz
  obtain ⟨g₂, hg₂⟩ := l02qj5b1_lemmaA (2 ^ n) σ hK hσ h3q hσ3 hez3 hez1
    (Jz.map e.toMonoidHom) hJz' k hθz
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : orderOf (g₁ * (e h) * g₁⁻¹) = 3 := by
    have hconj : (g₁ * e h * g₁⁻¹) ^ 3 = g₁ * (e h) ^ 3 * g₁⁻¹ := by
      calc (g₁ * e h * g₁⁻¹) ^ 3 = ((MulAut.conj g₁) (e h)) ^ 3 := by rw [MulAut.conj_apply]
        _ = (MulAut.conj g₁) ((e h) ^ 3) := (map_pow (MulAut.conj g₁) (e h) 3).symm
        _ = g₁ * (e h) ^ 3 * g₁⁻¹ := by rw [MulAut.conj_apply]
    apply orderOf_eq_prime
    · rw [hconj, heh3]; group
    · intro hh
      apply heh1
      have h' := congrArg (fun t => g₁⁻¹ * t * g₁) hh
      have h'' : e h = 1 := by
        calc e h = g₁⁻¹ * (g₁ * e h * g₁⁻¹) * g₁ := by group
          _ = g₁⁻¹ * 1 * g₁ := h'
          _ = 1 := by group
      exact h''
  have hB3 : orderOf (g₂ * (e D.z₀) * g₂⁻¹) = 3 := by
    have hconj : (g₂ * e D.z₀ * g₂⁻¹) ^ 3 = g₂ * (e D.z₀) ^ 3 * g₂⁻¹ := by
      calc (g₂ * e D.z₀ * g₂⁻¹) ^ 3 = ((MulAut.conj g₂) (e D.z₀)) ^ 3 := by rw [MulAut.conj_apply]
        _ = (MulAut.conj g₂) ((e D.z₀) ^ 3) := (map_pow (MulAut.conj g₂) (e D.z₀) 3).symm
        _ = g₂ * (e D.z₀) ^ 3 * g₂⁻¹ := by rw [MulAut.conj_apply]
    apply orderOf_eq_prime
    · rw [hconj, hez3]; group
    · intro hh
      apply hez1
      have h' := congrArg (fun t => g₂⁻¹ * t * g₂) hh
      have h'' : e D.z₀ = 1 := by
        calc e D.z₀ = g₂⁻¹ * (g₂ * e D.z₀ * g₂⁻¹) * g₂ := by group
          _ = g₂⁻¹ * 1 * g₂ := h'
          _ = 1 := by group
      exact h''
  have h3K : 3 ∣ Nat.card K - 1 := by
    obtain ⟨m, rfl⟩ := hev
    have hbase : 3 ∣ 2 ^ (m + m) - 1 := by
      have h := Nat.sub_one_dvd_pow_sub_one 4 m
      have hm : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
      rw [← hm] at h
      norm_num at h
      exact h
    have hdiv : 2 ^ (m + m) - 1 ∣ (2 ^ (m + m)) ^ 3 - 1 :=
      Nat.sub_one_dvd_pow_sub_one (2 ^ (m + m)) 3
    rw [hK]
    exact hbase.trans hdiv
  obtain ⟨s, _hsS, hs⟩ := kgLangT3_order_three_conj_short hσ3 h3K hg₁ hg₂ hA3 hB3
  have hux : (g₂⁻¹ * s * g₁) * (e h) * (g₂⁻¹ * s * g₁)⁻¹ = e D.z₀ := by
    have hcalc : (g₂⁻¹ * s * g₁) * e h * (g₂⁻¹ * s * g₁)⁻¹
        = g₂⁻¹ * (s * (g₁ * e h * g₁⁻¹) * s⁻¹) * g₂ := by group
    rw [hcalc, hs]
    group
  refine ⟨e.symm (g₂⁻¹ * s * g₁), ?_⟩
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hux]

end CFSG.StandardType
