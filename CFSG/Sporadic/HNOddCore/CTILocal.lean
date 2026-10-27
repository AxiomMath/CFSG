module

public import CFSG.Sporadic.HNOddCore.AllExt
public import CFSG.Sporadic.HNOddCore.SixPair
public import CFSG.Sporadic.HNOddCore.FourPairComp
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
public import Certificates.Certificate2091
public import Certificates.Certificate2092
public import Certificates.Certificate2093
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native

@[expose] def centralizerMapEquiv {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (a : G) :
    Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({φ a} : Set G') where
  toFun x := ⟨φ x, by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 x.2]⟩
  invFun y := ⟨φ.symm y, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.1 y.2⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply _)
  right_inv y := Subtype.ext (φ.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul φ _ _)

theorem exists_component_of_conj {S G0 : Type*} [Group S] [Group G0] {J : Subgroup G0}
    (f : S ≃* J) (a : S) (c g : J) (hg : g * c * g⁻¹ = f a)
    (B : Subgroup (Subgroup.centralizer ({a} : Set S))) (hB : CFSG.IsComponent B) :
    ∃ B' : Subgroup (Subgroup.centralizer ({c} : Set J)), CFSG.IsComponent B' ∧
      Nat.card (B ⧸ Subgroup.center B) = Nat.card (B' ⧸ Subgroup.center B') := by
  have e2 : Subgroup.centralizer ({f a} : Set J) ≃* Subgroup.centralizer ({c} : Set J) :=
    (MulEquiv.subgroupCongr (show Subgroup.centralizer ({f a} : Set J) =
      Subgroup.centralizer {g * c * g⁻¹} by rw [hg])).trans (centralizerConjEquiv c g).symm
  set ψ := (centralizerMapEquiv f a).trans e2
  refine ⟨B.map ψ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv ψ hB, ?_⟩
  let φ := B.equivMapOfInjective ψ.toMonoidHom ψ.injective
  exact Nat.card_congr (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).toEquiv

theorem sub_isConj_iff {G0 : Type*} [Group G0] {J : Subgroup G0} {a b : J} :
    IsConj a b ↔ ∃ c : J, c * a * c⁻¹ = b :=
  isConj_iff

theorem map_involution {S G0 : Type*} [Group S] [Group G0] {J : Subgroup G0} (f : S ≃* J)
    {a : S} (ha : orderOf a = 2) : (f a) ^ 2 = 1 ∧ f a ≠ 1 := by
  refine ⟨by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one], fun h => ?_⟩
  have : a = 1 := f.injective (h.trans (map_one f).symm)
  rw [this, orderOf_one] at ha
  exact absurd ha (by norm_num)

theorem isConj_aJ_or_t4J
    {a : JH} (h2 : a ^ 2 = 1) (h1 : a ≠ 1) :
    IsConj aJ a ∨ IsConj t4J a := by
  have h2' : (jR a) ^ 2 = 1 := by rw [← map_pow, h2, map_one]
  have h1' : jR a ≠ 1 := fun e => h1 (jR_injective (e.trans (map_one jR).symm))
  rcases involution_cover_R h2' h1' with hc | hc | hc
  · exact absurd hc (not_isConj_c_jR a)
  · exact Or.inl (isConj_t2_aJ.symm.trans (isConj_J_of_R t2J_sq t2J_ne_one hc))
  · exact Or.inr (isConj_J_of_R t4J_sq' t4J_ne_one hc)

theorem cti_hn_involution_local_components_simple_quotient_order
    {S : Type*} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.HN) (a : S) (ha : orderOf a = 2)
    (B : Subgroup (Subgroup.centralizer ({a} : Set S))) (hB : CFSG.IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 44352000 := by
  set f : S ≃* JH := e.trans hnEquivJ
  obtain ⟨h2, h1⟩ := map_involution f ha
  rcases isConj_aJ_or_t4J h2 h1 with hc | hc
  · obtain ⟨g, hg⟩ := sub_isConj_iff.1 hc
    obtain ⟨B', hB', hcard⟩ := exists_component_of_conj f a aJ g hg B hB
    rw [hcard]
    exact cti_hn_six_pair_centralizer_component_simple_quotient_order B' hB'
  · obtain ⟨g, hg⟩ := sub_isConj_iff.1 hc
    obtain ⟨B', hB', -⟩ := exists_component_of_conj f a t4J g hg B hB
    exact absurd hB' (cti_hn_four_pair_centralizer_has_no_components.2 B')

end CFSG.Sporadic.HNOddCore
