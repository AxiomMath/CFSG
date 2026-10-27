module

public import CFSG.RankThree.PartOne.S12.Sec12Fus
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

namespace Sec12Fus

theorem exists_isSylowOf_ge [Finite G] {p : ℕ} [Fact p.Prime] {K X : Subgroup G} (hXK : X ≤ K)
    (hX : IsPGroup p X) : ∃ P : Subgroup G, IsSylowOf p P K ∧ X ≤ P := by
  have hX' : IsPGroup p (X.subgroupOf K) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  obtain ⟨Q, hQ⟩ := hX'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥K).map K.subtype, ⟨Subgroup.map_subtype_le _, ?_, ?_⟩, ?_⟩
  · exact Q.isPGroup'.map K.subtype
  · have hsub : ((Q : Subgroup ↥K).map K.subtype).subgroupOf K = (Q : Subgroup ↥K) :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    have : ((Q : Subgroup ↥K).map K.subtype).relIndex K = (Q : Subgroup ↥K).index := by
      unfold Subgroup.relIndex
      rw [hsub]
    rw [this]
    exact Q.not_dvd_index
  · intro x hx
    have hxK : x ∈ K := hXK hx
    have : (⟨x, hxK⟩ : ↥K) ∈ X.subgroupOf K := hx
    exact ⟨⟨x, hxK⟩, hQ this, rfl⟩

theorem pElement_normalizes_thetaComponentsAt_gen [Finite G] {p : ℕ}
    (hnorm : SelectedPrimeElementsNormalizeThetaComponents) (hrank : evenRank G ≤ 3)
    (hp : p.Prime) (hp3 : 3 < p) {a y : G} (hya : y * a = a * y)
    (hord : ∃ k : ℕ, orderOf y = p ^ k) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p a) :
    y ∈ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsAt_iff.mp hY
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hya
  have hH : evenRank (Subgroup.centralizer ({a} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans hrank
  have hord' : ∃ k : ℕ, orderOf (⟨y, hyC⟩ : Subgroup.centralizer ({a} : Set G)) = p ^ k := by
    obtain ⟨k, hk⟩ := hord
    exact ⟨k, by rw [← hk, ← Subgroup.orderOf_coe]⟩
  have hmem := hnorm.1 (Subgroup.centralizer ({a} : Set G)) hH p hp hp3 _ hord' _ hY'
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ Subgroup.centralizer ({a} : Set G)
  · have := Subgroup.mem_normalizer_iff.mp hmem ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hgY
      exact absurd (hYC hgY) hg
    · intro hygY
      have h1 : y * g * y⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := hYC hygY
      refine absurd ?_ hg
      have h2 := mul_mem (mul_mem (inv_mem hyC) h1) hyC
      simpa [mul_assoc] using h2

theorem mem_xPreimage_iff {p : ℕ} {E : Subgroup G} {w : G} :
    w ∈ xPreimage p E ↔ ∃ hw : w ∈ Subgroup.normalizer (E : Set G),
      E.normalizerMonoidHom ⟨w, hw⟩ ∈ (CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype := by
  unfold xPreimage
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact ⟨w'.2, hw'⟩
  · rintro ⟨hw, h⟩
    exact ⟨⟨w, hw⟩, h, rfl⟩

theorem le_xPreimage [Finite G] {p : ℕ} {E : Subgroup G} (hE : ∀ a b : E, a * b = b * a) :
    E ≤ xPreimage p E := by
  intro e he
  have hen : e ∈ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer he
  rw [mem_xPreimage_iff]
  refine ⟨hen, ?_⟩
  have h1 : E.normalizerMonoidHom ⟨e, hen⟩ = 1 := by
    refine MulEquiv.ext fun x => ?_
    apply Subtype.ext
    show e * (x : G) * e⁻¹ = x
    have := hE ⟨e, he⟩ x
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [h2]
    group
  rw [h1]
  exact Subgroup.one_mem _

theorem xPreimage_fixes {p : ℕ} {E : Subgroup G} {w b : G} (hw : w ∈ xPreimage p E)
    (hb : b ∈ pCoreFixed p E) : w * b * w⁻¹ = b := by
  obtain ⟨hwN, hmem⟩ := mem_xPreimage_iff.1 hw
  obtain ⟨hbE, hfix⟩ := mem_pCoreFixed.1 hb
  obtain ⟨φ, hφ, hφeq⟩ := hmem
  have h1 := hfix φ hφ
  have h2 : (E.normalizerMonoidHom ⟨w, hwN⟩ : MulAut E) ⟨b, hbE⟩ = ⟨b, hbE⟩ := by
    rw [← hφeq]
    exact h1
  have h3 := Equivariance.coe_conjAut hwN ⟨b, hbE⟩
  have h4 : (conjAut E w hwN) ⟨b, hbE⟩ = ⟨b, hbE⟩ := h2
  rw [h4] at h3
  exact h3.symm

end Sec12Fus

theorem node1212Choice_of_inputs (hsel : SelectedPrimeElementsNormalizeThetaComponents) :
    Node1212Choice := by
  classical
  intro G _ _ p A c L E ctx b K I hL
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hEel := h.E_elem
  have hEc : ∀ a b : E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  have hbE : b ∈ E := h.A_le_E hL.b_mem.1
  have hbfix : b ∈ pCoreFixed p E := by
    rw [ctx.ten.1]
    exact ⟨hbE, hL.b_mem.2.1⟩
  have hEWx : E ≤ xPreimage p E := Sec12Fus.le_xPreimage hEc
  have hWxb : xPreimage p E ≤ Subgroup.centralizer ({b} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Sec12Fus.xPreimage_fixes hw hbfix
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨X, hXs, hEX⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hEWx
    (IsElementaryAbelian.isPGroup p ↥E)
  obtain ⟨P, hPs, hXP⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) (hXs.1.trans hWxb) hXs.2.1
  refine ⟨X, P, (Subgroup.centralizer (I : Set G) ⊓ P) ⊔ (P ⊓ I), ⟨⟨hXs, hEX⟩, ⟨hPs, hXP⟩, rfl, ?_⟩⟩
  intro y hy
  have hyb : y * b = b * y := by
    have := hPs.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hord : ∃ k : ℕ, orderOf y = p ^ k := by
    obtain ⟨k, hk⟩ := hPs.2.1 ⟨y, hy⟩
    have hyk : y ^ (p ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hyk)
    exact ⟨m, hm⟩
  exact Sec12Fus.pElement_normalizes_thetaComponentsAt_gen hsel h.evenRank_eq.le hp h.three_lt hyb
    hord hL.I_mem

end CFSG.RankThree.PartOne
