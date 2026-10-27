module

public import CFSG.RankThree.PartOne.S11d.FourClaimAux
public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.RankThree.PartOne.S11.FivePlusInner
import CFSG.RankThree.PartOne.S12.Sec125Moved
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSubnormal_subgroupOf_of_le {E Y X : Subgroup G} (hYX : Y ≤ X)
    (h : (E.subgroupOf X).IsSubnormal) : (E.subgroupOf Y).IsSubnormal := by
  have := h.comap (Subgroup.inclusion hYX)
  rwa [Subgroup.comap_inclusion_subgroupOf] at this

omit [Finite G] in
theorem isSubnormal_subgroupOf_trans {E Y X : Subgroup G} (hEY : E ≤ Y) (hYX : Y ≤ X)
    (hE : (E.subgroupOf Y).IsSubnormal) (hY : (Y.subgroupOf X).IsSubnormal) :
    (E.subgroupOf X).IsSubnormal := by
  let ι : ↥(Y.subgroupOf X) →* ↥Y := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom
  have hcomap : (E.subgroupOf Y).comap ι = (E.subgroupOf X).subgroupOf (Y.subgroupOf X) := by
    ext g
    exact Iff.rfl
  have h1 : ((E.subgroupOf X).subgroupOf (Y.subgroupOf X)).IsSubnormal := by
    rw [← hcomap]
    exact hE.comap ι
  exact Subgroup.IsSubnormal.trans (fun x hx => hEY hx) h1 hY

omit [Finite G] in
theorem mem_normalizer_inf_centralizer {K : Subgroup G} {x d : G}
    (hx : x ∈ normalizer (K : Set G)) (hxd : x * d = d * x) :
    x ∈ normalizer ((K ⊓ centralizer ({d} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hxd' : Commute x d := hxd
  constructor
  · intro hg
    obtain ⟨hgK, hgd⟩ := Subgroup.mem_inf.mp hg
    have hgd' : Commute g d := Subgroup.mem_centralizer_singleton_iff.mp hgd
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hx g).mp hgK,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (hxd'.mul_left hgd').mul_left hxd'.inv_left
  · intro hg
    obtain ⟨hgK, hgd⟩ := Subgroup.mem_inf.mp hg
    have h1 : Commute (x * g * x⁻¹) d := Subgroup.mem_centralizer_singleton_iff.mp hgd
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hx g).mpr hgK,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h2 : Commute (x⁻¹ * (x * g * x⁻¹) * x) d :=
      (hxd'.inv_left.mul_left h1).mul_left hxd'
    have h3 : Commute g d := by simpa [mul_assoc] using h2
    exact h3

omit [Finite G] in
theorem component_subnormal {p : ℕ} {x d : G} {Y E : Subgroup G} (hY : Y ∈ thetaComponentsAt p x)
    (hE : IsComponentOf (Y ⊓ centralizer ({d} : Set G)) E) :
    (E.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({d} : Set G))).IsSubnormal := by
  set X := centralizer ({x} : Set G) ⊓ centralizer ({d} : Set G) with hX
  have hYC : Y ≤ centralizer ({x} : Set G) := (mem_thetaComponentsAt_iff.mp hY).1
  have hYsn : (Y.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
    isSubnormal_of_mem_thetaComponentsAt hY
  have hXC : X ≤ centralizer ({x} : Set G) := inf_le_left
  have h1 : (Y.subgroupOf X).IsSubnormal := isSubnormal_subgroupOf_of_le hXC hYsn
  have hYd : (Y ⊓ centralizer ({d} : Set G)).subgroupOf X = Y.subgroupOf X := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, g.2.2⟩⟩
  have h2 : ((Y ⊓ centralizer ({d} : Set G)).subgroupOf X).IsSubnormal := by
    rw [hYd]
    exact h1
  exact isSubnormal_subgroupOf_trans hE.1 (inf_le_inf hYC le_rfl) hE.2.2 h2

theorem normalizes_component {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {Y D : Subgroup G} {c : G}
    (hcY : c ∈ normalizer (Y : Set G)) (hcp : ∃ k : ℕ, orderOf c = p ^ k)
    (he : evenRank ↥(Y ⊔ zpowers c) ≤ 3) (hD : IsComponentOf Y D) :
    c ∈ normalizer (D : Set G) := by
  obtain ⟨hDY, hq, hsn⟩ := hD
  set X := Y ⊔ zpowers c with hX
  have hYX : Y ≤ X := le_sup_left
  have hcX : c ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hDX : D ≤ X := hDY.trans hYX
  have hqX : CFSG.IsQuasisimple ↥(D.subgroupOf X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDX).symm hq
  have hYn : (Y.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYX]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hcY)
  let ι : ↥(Y.subgroupOf X) →* ↥Y := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom
  have hcomap : (D.subgroupOf Y).comap ι = (D.subgroupOf X).subgroupOf (Y.subgroupOf X) := by
    ext g
    exact Iff.rfl
  have h1 : ((D.subgroupOf X).subgroupOf (Y.subgroupOf X)).IsSubnormal := by
    rw [← hcomap]
    exact hsn.comap ι
  have hle : D.subgroupOf X ≤ Y.subgroupOf X := fun x hx => hDY hx
  have hDsn : (D.subgroupOf X).IsSubnormal :=
    Subgroup.IsSubnormal.trans hle h1 hYn.isSubnormal
  have hmem : D.subgroupOf X ∈ thetaComponents p ↥X :=
    mem_thetaComponents_of_quasisimple hp hqX hDsn
  have hord : ∃ k : ℕ, orderOf (⟨c, hcX⟩ : ↥X) = p ^ k := by
    obtain ⟨k, hk⟩ := hcp
    exact ⟨k, by rw [← hk, ← Subgroup.orderOf_coe]⟩
  have hnorm := selected_prime_elements_normalize_theta_components.1 ↥X he p hp hp3 _ hord _ hmem
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ X
  · have := Subgroup.mem_normalizer_iff.mp hnorm ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hgD
      exact absurd (hDX hgD) hg
    · intro hcgD
      refine absurd ?_ hg
      have h2 : c * g * c⁻¹ ∈ X := hDX hcgD
      have h3 := mul_mem (mul_mem (inv_mem hcX) h2) hcX
      simpa [mul_assoc] using h3

theorem exists_involution_of_inner_action {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hK : CatalogPrimeTwoAutomorphismsInner) {K A R : Subgroup G} (hq : CFSG.IsQuasisimple ↥K)
    (hcat : Catalog (↥K ⧸ Subgroup.center ↥K)) (hAp : IsPGroup p A)
    (hAK : A ≤ normalizer (K : Set G)) (hRK : R ≤ normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ normalizer (R : Set G)) (hRA : ⁅R, A⁆ = R) {d : G} (hdK : d ∈ K)
    (hRd : R ≤ centralizer ({d} : Set G)) (hmove : ∃ r ∈ R, ∃ k ∈ K, r * k * r⁻¹ ≠ k) :
    ∃ t ∈ K ⊓ centralizer ({d} : Set G), orderOf t = 2 := by
  classical
  set N := normalizer (K : Set G) with hN
  set φ := K.normalizerMonoidHom with hφ
  set P : Subgroup (MulAut ↥K) := (A.subgroupOf N).map φ with hP
  set Q : Subgroup (MulAut ↥K) := (R.subgroupOf N).map φ with hQ
  have hP' : IsPGroup p P := (hAp.comap_subtype).map φ
  have hQ2 : IsPGroup 2 Q := (hR2.comap_subtype).map φ
  have hPQ : P ≤ normalizer (Q : Set (MulAut ↥K)) := by
    have h1 : A.subgroupOf N ≤ normalizer (R.subgroupOf N : Set N) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hAR (Subgroup.mem_subgroupOf.mp hx)) (h : G)
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map φ)
  have hQA' : ⁅R.subgroupOf N, A.subgroupOf N⁆ = R.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRK,
      Subgroup.map_subgroupOf_eq_of_le hAK]
    exact hRA
  have hQP : ⁅Q, P⁆ = Q := by
    rw [hQ, hP, ← Subgroup.map_commutator, hQA']
  have hinn : Q ≤ (MulAut.conj : ↥K →* MulAut ↥K).range :=
    hK ↥K hq hcat p P Q hp hp3 hP' hQ2 hPQ hQP
  obtain ⟨r, hr, k, hk, hrk⟩ := hmove
  have hrN : r ∈ N := hRK hr
  have hmem : φ ⟨r, hrN⟩ ∈ Q := Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hr)
  obtain ⟨j, hj⟩ := hinn hmem
  have hact : ∀ x : K, (r : G) * x * r⁻¹ = (j : G) * x * (j : G)⁻¹ := by
    intro x
    have := congrArg (fun σ : MulAut ↥K => (σ x : G)) hj
    simpa [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this.symm
  have hrd : r * d * r⁻¹ = d := by
    have : r * d = d * r := Subgroup.mem_centralizer_singleton_iff.mp (hRd hr)
    rw [this]
    group
  have hjd : (j : G) * d * (j : G)⁻¹ = d := by
    rw [← hact ⟨d, hdK⟩]
    exact hrd
  have hjk : (j : G) * k * (j : G)⁻¹ ≠ k := by
    rw [← hact ⟨k, hk⟩]
    exact hrk
  have hconj1 : (MulAut.conj j : MulAut ↥K) ≠ 1 := by
    intro h1
    apply hjk
    have := congrArg (fun σ : MulAut ↥K => (σ ⟨k, hk⟩ : G)) h1
    simpa [MulAut.conj_apply] using this
  have hord2 : ∃ m : ℕ, orderOf (MulAut.conj j : MulAut ↥K) = 2 ^ m := by
    have h1 : orderOf (φ ⟨r, hrN⟩) ∣ orderOf (⟨r, hrN⟩ : N) := orderOf_map_dvd φ _
    have h2 : orderOf (⟨r, hrN⟩ : N) = orderOf (⟨r, hr⟩ : R) := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe (⟨r, hr⟩ : R)]
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hR2) ⟨r, hr⟩
    rw [h2, hm] at h1
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨s, by rw [hj]; exact hs⟩
  obtain ⟨m, hm⟩ := hord2
  have hm1 : m ≠ 0 := by
    rintro rfl
    exact hconj1 (orderOf_eq_one_iff.mp (by simpa using hm))
  have h2j : 2 ∣ orderOf j := by
    have h1 : orderOf (MulAut.conj j : MulAut ↥K) ∣ orderOf j := orderOf_map_dvd MulAut.conj j
    rw [hm] at h1
    exact (dvd_pow_self 2 hm1).trans h1
  have hjpos : orderOf j ≠ 0 := (orderOf_pos j).ne'
  refine ⟨((j ^ (orderOf j / 2) : ↥K) : G), Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact (j ^ (orderOf j / 2)).2
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : Commute (j : G) d := by
      have : (j : G) * d = d * (j : G) := by
        calc (j : G) * d = ((j : G) * d * (j : G)⁻¹) * (j : G) := by group
          _ = d * (j : G) := by rw [hjd]
      exact this
    have h1 : Commute ((j : G) ^ (orderOf j / 2)) d := hcomm.pow_left _
    have h2 : ((j ^ (orderOf j / 2) : ↥K) : G) = (j : G) ^ (orderOf j / 2) := by simp
    rw [h2]
    exact h1.eq
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div hjpos h2j

theorem exists_thetaComponent_ge_of_subnormal (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {c d : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hdA : d ∈ A)
    (hd1 : d ≠ 1) {Y : Subgroup G} (hY : CFSG.IsQuasisimple ↥Y)
    (hYc : Y ≤ centralizer ({c} : Set G)) (hYd : Y ≤ centralizer ({d} : Set G))
    (hsn : (Y.subgroupOf (centralizer ({c} : Set G) ⊓ centralizer ({d} : Set G))).IsSubnormal) :
    ∃ I ∈ thetaComponentsAt p d, Y ≤ I := by
  classical
  have hp : p.Prime := sectionTenSetup_prime h
  have hp3 : 3 < p := sectionTenSetup_three_lt h
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have : IsSimpleGroup G := h.1
  set H := centralizer ({d} : Set G) with hH
  have hcd : c * d = d * c := congrArg Subtype.val (hAe.is_comm.comm ⟨c, hcA⟩ ⟨d, hdA⟩)
  have hcH : c ∈ H := EmbeddingFixedResidual.commute_mem_centralizer hcd
  set x : H := ⟨c, hcH⟩ with hx
  have hxord : orderOf x = p := by
    rw [← Subgroup.orderOf_coe]
    exact EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  have hHK : CFSG.IsKGroup H :=
    h.2.2.1 _ (EmbeddingFixedResidual.centralizer_ne_top_of_simple h.2.1 hd1)
  have hHE : CFSG.Assembly.evenRank H ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans (sectionTenSetup_evenRank_eq h).le
  set Cx := centralizer ({x} : Set H) with hCx
  set X := centralizer ({c} : Set G) ⊓ centralizer ({d} : Set G) with hXdef
  have hle : Y.subgroupOf H ≤ Cx := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYc (Subgroup.mem_subgroupOf.mp hg))
  have hmem : (Y.subgroupOf H).subgroupOf Cx ∈ thetaComponents p ↥Cx := by
    apply mem_thetaComponents_of_quasisimple hp
    · let e : ↥((Y.subgroupOf H).subgroupOf Cx) ≃* ↥Y :=
        (Subgroup.subgroupOfEquivOfLe hle).trans (Subgroup.subgroupOfEquivOfLe hYd)
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hY
    · let ι' : ↥Cx →* ↥X :=
        ((H.subtype).comp Cx.subtype).codRestrict X (by
          intro g
          exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2)), g.1.2⟩)
      have h1 := hsn.comap ι'
      have h2 : (Y.subgroupOf X).comap ι' = (Y.subgroupOf H).subgroupOf Cx := by
        ext g
        exact Iff.rfl
      rwa [h2] at h1
  have hY' : Y.subgroupOf H ∈ thetaComponentsAt p x := mem_thetaComponentsAt_iff.mpr ⟨hle, hmem⟩
  obtain ⟨K₁, hK₁, hEK⟩ := local_theta_component_embedding_frontier hS H hHK hHE p hp hp3 x hxord _
    hY'
  refine ⟨K₁.map H.subtype, ⟨K₁, hK₁, rfl⟩, fun e he => ?_⟩
  exact ⟨⟨e, hYd he⟩, hEK (Subgroup.mem_subgroupOf.mpr he), rfl⟩

theorem thetaComponent_eq_of_overlap {p : ℕ} (hp : p.Prime) {d : G} {I₁ I₂ E D : Subgroup G}
    (h1 : I₁ ∈ thetaComponentsAt p d) (h2 : I₂ ∈ thetaComponentsAt p d)
    (hE : CFSG.IsQuasisimple ↥E) (hEI : E ≤ I₁) (hDI : D ≤ I₂)
    (hov : ∃ x ∈ D, ∃ hxE : x ∈ E, (⟨x, hxE⟩ : ↥E) ∉ Subgroup.center ↥E) : I₁ = I₂ := by
  by_contra hne
  obtain ⟨x, hxD, hxE, hxc⟩ := hov
  apply hxc
  have hEd : E ≤ centralizer ({d} : Set G) := hEI.trans (mem_thetaComponentsAt_iff.mp h1).1
  have hcomm : ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈
      inSubgroup (aschbacherSolvableCore p) (centralizer ({d} : Set G)) := fun e he =>
    S11d.commutator_mem_theta_of_ne hp h2 h1 (Ne.symm hne) x (hDI hxD) e (hEI he)
  have hxN : x ∈ normalizer (E : Set G) := Subgroup.le_normalizer hxE
  have hcent := centralizes_of_commutators_mem_theta hp hE hEd hxN hcomm
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have := hcent y y.2
  calc ((y * ⟨x, hxE⟩ : ↥E) : G) = y * x := rfl
    _ = x * y := by
      calc (y : G) * x = (x * y * x⁻¹) * x := by rw [this]
        _ = x * y := by group
    _ = ((⟨x, hxE⟩ * y : ↥E) : G) := rfl

theorem fixedRes_eq_of_field {p : ℕ} {c f : G} {L K : Subgroup G}
    (hLc : L ∈ thetaComponentsAt p c) (hfL : InducesFieldAut p f L)
    (hcK : InducesFieldAut p c K)
    (hEK : inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ≤ K)
    (hKf : K ≤ centralizer ({f} : Set G)) :
    inSubgroup perfectResidual (K ⊓ centralizer ({c} : Set G)) =
      inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) := by
  set E := inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) with hE
  have hEq : CFSG.IsQuasisimple ↥E := fixedRes_isQuasisimple hfL
  have hEL : E ≤ L := (inSubgroup_perfectResidual_le _).trans inf_le_left
  have hLC : L ≤ centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.mp hLc).1
  have hEc : E ≤ centralizer ({c} : Set G) := hEL.trans hLC
  have hEp : Group.IsPerfect ↥E := EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
  have hEE₂ : E ≤ inSubgroup perfectResidual (K ⊓ centralizer ({c} : Set G)) :=
    EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect (le_inf hEK hEc) hEp
  have hE₂X : inSubgroup perfectResidual (K ⊓ centralizer ({c} : Set G)) ≤
      centralizer ({c} : Set G) ⊓ centralizer ({f} : Set G) := fun g hg =>
    have h1 := inSubgroup_perfectResidual_le _ hg
    ⟨h1.2, hKf h1.1⟩
  have hq₂ := fixedRes_isQuasisimple hcK
  have hsn := fixedRes_subnormal (f := f) hLc
  have hEne : E ≠ ⊥ := Sec125.ne_bot_of_isQuasisimple hEq
  have hE₂E := le_of_isSubnormal_of_quasisimple hq₂ hEE₂ hE₂X hsn hEp hEne
  exact le_antisymm hE₂E hEE₂

omit [Finite G] in
theorem FieldLike.zpow {p : ℕ} {a : G} {J : Subgroup G} (hp : p.Prime) (h : FieldLike p a J)
    (hap : a ^ p = 1) {i : ℤ} (hi : ¬ (p : ℤ) ∣ i) : FieldLike p (a ^ i) J := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hN, hnot, -, t, n, f, hf, hmodel⟩ := h
  have hzpow : ∀ n : ℤ, (p : ℤ) ∣ n → a ^ n = 1 := fun n hn => by
    obtain ⟨t', rfl⟩ := hn
    rw [zpow_mul, zpow_natCast, hap, one_zpow]
  refine ⟨Subgroup.zpow_mem _ hN i, ?_, ?_, t, n, f, hf, hmodel⟩
  · intro hmem
    apply hnot
    obtain ⟨m, hm⟩ := Sec11Indeed.exists_nat_mul_add_dvd (p := p) hi (-1)
    have h1 : (a ^ i) ^ (m : ℤ) = a := by
      rw [← zpow_mul]
      have h2 : a ^ (i * (m : ℤ) + -1) = 1 := hzpow _ hm
      calc a ^ (i * (m : ℤ)) = a ^ (i * (m : ℤ) + -1) * a := by
            rw [zpow_add, zpow_neg_one]
            group
        _ = a := by rw [h2, one_mul]
    rw [← h1]
    exact Subgroup.zpow_mem _ hmem _
  · have : (a ^ i) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
    rw [this]
    exact Subgroup.one_mem _

omit [Finite G] in
theorem FieldLike.mul_centralizer {p : ℕ} {u z : G} {J : Subgroup G} (h : FieldLike p u J)
    (hz : z ∈ centralizer (J : Set G)) (hp : (u * z) ^ p ∈ J ⊔ centralizer (J : Set G)) :
    FieldLike p (u * z) J := by
  obtain ⟨hN, hnot, -, t, n, f, hf, hmodel⟩ := h
  have hzN : z ∈ normalizer (J : Set G) := centralizer_le_normalizer _ hz
  have hzJ : z ∈ J ⊔ centralizer (J : Set G) := Subgroup.mem_sup_right hz
  refine ⟨Subgroup.mul_mem _ hN hzN, ?_, hp, t, n, f, hf, hmodel⟩
  intro hmem
  apply hnot
  have := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hzJ)
  simpa using this

theorem clash_of_components (hP4a : FieldOnComponentOuter) (hP4b : OutPCyclicTheta) {p : ℕ}
    {A : Subgroup G} (h : SteinbergBM.SectionTenSetup G p A) {d u v : G} (hdA : d ∈ A)
    (hd1 : d ≠ 1) (huA : u ∈ A) (hvA : v ∈ A) (hvu : v ∉ zpowers u) {I E D : Subgroup G}
    (hI : I ∈ thetaComponentsAt p d) (hE : IsComponentOf (I ⊓ centralizer ({v} : Set G)) E)
    (hD : IsComponentOf (I ⊓ centralizer ({u} : Set G)) D) (huE : u ∈ normalizer (E : Set G))
    (hvD : v ∈ normalizer (D : Set G)) (hufield : FieldLike p u E)
    (hvfield : FieldLike p v D) : False := by
  have hp : p.Prime := sectionTenSetup_prime h
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hup : u ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) u huA
  have hvp : v ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) v hvA
  have huv : Commute u v := hAcomm u huA v hvA
  have hvE : ∀ t : ℤ, v ^ t ∈ centralizer (E : Set G) := by
    intro t
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 : g * v = v * g := Subgroup.mem_centralizer_singleton_iff.mp (hE.1 hg).2
    exact (Commute.zpow_right (show Commute g v from h1) t).eq
  have hnot : ∀ b ∈ zpowers u ⊔ zpowers v, b ≠ 1 → ¬ InnerOnTheta p I b := by
    intro b hb hb1
    obtain ⟨s, t, hbst⟩ := (S11d.mem_zpowers_sup_zpowers_iff huv).mp hb
    have hbA : b ∈ A :=
      (sup_le (zpowers_le.mpr huA) (zpowers_le.mpr hvA) : zpowers u ⊔ zpowers v ≤ A) hb
    have hbp : b ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) b hbA
    by_cases hs : (p : ℤ) ∣ s
    · have hus : u ^ s = 1 := by
        obtain ⟨w, rfl⟩ := hs
        rw [zpow_mul, zpow_natCast, hup, one_zpow]
      have hbvt : b = v ^ t := by rw [hbst, hus, one_mul]
      have ht : ¬ (p : ℤ) ∣ t := by
        intro hdt
        apply hb1
        rw [hbvt]
        obtain ⟨w, rfl⟩ := hdt
        rw [zpow_mul, zpow_natCast, hvp, one_zpow]
      have hbfield : FieldLike p b D := by
        rw [hbvt]
        exact FieldLike.zpow hp hvfield hvp ht
      have hbN : b ∈ normalizer (D : Set G) := by
        rw [hbvt]
        exact zpow_mem hvD t
      exact hP4a G p A h d hdA hd1 I hI b hbA u huA D hD hbN hbfield
    · have hbfield : FieldLike p b E := by
        have h1 : FieldLike p (u ^ s) E := FieldLike.zpow hp hufield hup hs
        rw [hbst]
        refine h1.mul_centralizer (hvE t) ?_
        rw [← hbst, hbp]
        exact Subgroup.one_mem _
      have hbN : b ∈ normalizer (E : Set G) := by
        rw [hbst]
        exact mul_mem (zpow_mem huE s) (centralizer_le_normalizer _ (hvE t))
      exact hP4a G p A h d hdA hd1 I hI b hbA v hvA E hE hbN hbfield
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hufield.2.1 (Subgroup.one_mem _)
  obtain ⟨b, hb, hb1, hbinn⟩ := hP4b G p A h d hdA hd1 I hI u huA hu1 v hvA hvu
  exact hnot b hb hb1 hbinn

namespace Sec11Indeed

namespace Sit

variable {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G}

theorem exists_coords_of_witness (sit : Sit p A c L a d) {f : G} (hf : f ∈ zpowers a ⊔ zpowers c)
    (hf1 : f ≠ 1) {R : Subgroup G} (hR : WitnessAt A c f R) :
    ∃ i j : ℤ, f = a ^ i * c ^ j ∧ ¬ (p : ℤ) ∣ i := by
  have hp := sit.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcA := sit.c_mem
  have hcp : c ^ p = 1 := sit.pow_eq_one hcA
  have hap : a ^ p = 1 := sit.pow_eq_one sit.a_mem
  obtain ⟨i, j, hij⟩ := sit.exists_zpow_mul hf
  refine ⟨i, j, hij, ?_⟩
  intro hdiv
  have hai : a ^ i = 1 := by
    obtain ⟨t, rfl⟩ := hdiv
    rw [zpow_mul, zpow_natCast, hap, one_zpow]
  have hfc : f = c ^ j := by rw [hij, hai, one_mul]
  have hj : ¬ (p : ℤ) ∣ j := by
    intro hdj
    apply hf1
    rw [hfc]
    obtain ⟨t, rfl⟩ := hdj
    rw [zpow_mul, zpow_natCast, hcp, one_zpow]
  have hcent := S11d.centralizer_zpow_eq (G := G) hp hcp hj
  have hRc : R ≤ centralizer ({c} : Set G) := by
    rw [← hcent, ← hfc]
    exact hR.le_cent
  apply hR.ne_bot
  have h1 : ⁅R, zpowers c⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hrc : r * c = c * r := Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)
    exact (Commute.zpow_left (show Commute c r from hrc.symm) k).eq
  rw [hR.comm, h1]

end Sit

end Sec11Indeed

end CFSG.RankThree.PartOne
