module

public import CFSG.RankThree.PartOne.S11d.Sec11Common
public import CFSG.RankThree.PartOne.S11d.FixedRes

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem commutatorElement_mul_central {Q : Type*} [Group Q] {z w : Q}
    (hz : z ∈ Subgroup.center Q) (hw : w ∈ Subgroup.center Q) (x y : Q) :
    ⁅z * x, w * y⁆ = ⁅x, y⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc z * x * (w * y) * (z * x)⁻¹ * (w * y)⁻¹
      = z * (x * w * y * x⁻¹) * z⁻¹ * y⁻¹ * w⁻¹ := by group
    _ = (x * w * y * x⁻¹) * z * z⁻¹ * y⁻¹ * w⁻¹ := by rw [← hz' (x * w * y * x⁻¹)]
    _ = (w * x * y * x⁻¹ * y⁻¹) * w⁻¹ := by rw [hw' x]; group
    _ = w * (x * y * x⁻¹ * y⁻¹) * w⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * w * w⁻¹ := by rw [← hw' (x * y * x⁻¹ * y⁻¹)]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem mulAut_eq_id_of_perfect_central {Q : Type*} [Group Q] (hQ : Group.IsPerfect Q)
    (σ : MulAut Q) (h : ∀ x : Q, σ x * x⁻¹ ∈ Subgroup.center Q) : ∀ x : Q, σ x = x := by
  let H : Subgroup Q := MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id Q)
  have hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ H := by
    intro x y
    obtain ⟨z, hz, hzx⟩ : ∃ z ∈ Subgroup.center Q, σ x = z * x := ⟨σ x * x⁻¹, h x, by group⟩
    obtain ⟨w, hw, hwy⟩ : ∃ w ∈ Subgroup.center Q, σ y = w * y := ⟨σ y * y⁻¹, h y, by group⟩
    show σ ⁅x, y⁆ = ⁅x, y⁆
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hzx, hwy,
      ← commutatorElement_def]
    exact commutatorElement_mul_central hz hw x y
  intro x
  have hle : commutator Q ≤ H := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro u _ v _
    exact hcomm u v
  have htop : commutator Q = ⊤ := hQ.commutator_eq_top
  have hx : x ∈ H := hle (htop ▸ Subgroup.mem_top x)
  exact hx

theorem eq_top_of_isSubnormal_perfect_of_quasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) {N : Subgroup Q} (hN : N.IsSubnormal)
    (hNp : Group.IsPerfect N) (hN1 : N ≠ ⊥) : N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have h1 : (N.map (QuotientGroup.mk' (Subgroup.center Q))).IsSubnormal :=
    hN.map (QuotientGroup.mk'_surjective _)
  rcases h1.eq_bot_or_top_of_isSimpleGroup hsimple with hbot | htop
  · exfalso
    have hle : N ≤ Subgroup.center Q := by
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    apply hN1
    have hcomm : ⁅N, N⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro n hn m hm
      exact (Subgroup.mem_center_iff.mp (hle hn) m)
    rw [← Subgroup.isPerfect_iff.mp hNp, hcomm]
  · have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
      exact h2.symm
    have hle : commutator Q ≤ N := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      have hx : x ∈ N ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top x
      have hy : y ∈ N ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top y
      obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      obtain ⟨n', hn', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      have e : ⁅n * z, n' * z'⁆ = ⁅n, n'⁆ := by
        rw [Subgroup.mem_center_iff.mp hz n, Subgroup.mem_center_iff.mp hz' n']
        exact commutatorElement_mul_central hz hz' n n'
      rw [e, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

variable {G : Type} [Group G] [Finite G]

theorem centralizes_of_commutators_mem_theta {p : ℕ} (hp : p.Prime) {E K₀ : Subgroup G}
    (hE : CFSG.IsQuasisimple ↥E) (hEK : E ≤ K₀) {D : G} (hDN : D ∈ normalizer (E : Set G))
    (hD : ∀ e ∈ E, D * e * D⁻¹ * e⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K₀) :
    ∀ e ∈ E, D * e * D⁻¹ = e := by
  set θ := inSubgroup (aschbacherSolvableCore p) K₀ with hθ
  obtain ⟨hθK, hθnormal⟩ := theta_le_and_normal p K₀
  have hKN : K₀ ≤ normalizer (θ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hθK).mp hθnormal
  have hN : (θ.subgroupOf E).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hKN (hEK g.2)) n).mp hn
    simpa using this
  have hcen : θ.subgroupOf E ≤ Subgroup.center ↥E := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hE hN with htop | hle
    · exfalso
      have hEθ : E ≤ θ := fun x hx => by
        have : (⟨x, hx⟩ : ↥E) ∈ θ.subgroupOf E := htop ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      have hsolv := (theta_solvable_and_not_dvd hp K₀).1
      have hEsolv : Group.IsSolvable ↥E :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hEθ)
          (Subgroup.inclusion_injective hEθ)
      have : Nontrivial ↥E := CFSG.LocalCores.isQuasisimple_nontrivial hE
      have : Group.IsPerfect ↥E := hE.1
      exact Group.IsPerfect.not_isSolvable ↥E hEsolv
    · exact hle
  let σ : MulAut ↥E := E.normalizerMonoidHom ⟨D, hDN⟩
  have hσ : ∀ x : ↥E, σ x * x⁻¹ ∈ Subgroup.center ↥E := by
    intro x
    apply hcen
    rw [Subgroup.mem_subgroupOf]
    have := hD x x.2
    simpa [σ] using this
  intro e he
  have := mulAut_eq_id_of_perfect_central hE.1 σ hσ ⟨e, he⟩
  simpa [σ] using congrArg Subtype.val this


omit [Finite G] in
theorem fixedRes_subnormal {p : ℕ} {J : Subgroup G} {c f : G} (hJ : J ∈ thetaComponentsAt p c) :
    ((inSubgroup perfectResidual (J ⊓ centralizer ({f} : Set G))).subgroupOf
      (centralizer ({c} : Set G) ⊓ centralizer ({f} : Set G))).IsSubnormal := by
  set X' := centralizer ({c} : Set G) ⊓ centralizer ({f} : Set G) with hX'
  set E := inSubgroup perfectResidual (J ⊓ centralizer ({f} : Set G)) with hE
  have hX'c : X' ≤ centralizer ({c} : Set G) := inf_le_left
  have hJsn := isSubnormal_of_mem_thetaComponentsAt hJ
  have h1 : (J.subgroupOf X').IsSubnormal := by
    have := hJsn.comap (Subgroup.inclusion hX'c)
    rwa [Subgroup.comap_inclusion_subgroupOf] at this
  have hEJ : E ≤ J := (inSubgroup_perfectResidual_le _).trans inf_le_left
  have hle : E.subgroupOf X' ≤ J.subgroupOf X' := Subgroup.subgroupOf_mono X' hEJ
  refine Subgroup.IsSubnormal.trans hle ?_ h1
  refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : (((n : ↥(J.subgroupOf X')) : ↥X') : G) ∈ E := hn
  have hg' : (((g : ↥(J.subgroupOf X')) : ↥X') : G) ∈ J ⊓ centralizer ({f} : Set G) :=
    ⟨Subgroup.mem_subgroupOf.mp g.2, ((g : ↥(J.subgroupOf X')) : ↥X').2.2⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact conj_mem_inSubgroup_perfectResidual hg' hn'

omit [Finite G] in
theorem le_of_isSubnormal_of_quasisimple {E E₂ X : Subgroup G} (hE₂ : CFSG.IsQuasisimple ↥E₂)
    (hEE₂ : E ≤ E₂) (hE₂X : E₂ ≤ X) (hsn : (E.subgroupOf X).IsSubnormal)
    (hEp : Group.IsPerfect ↥E) (hE1 : E ≠ ⊥) : E₂ ≤ E := by
  have hEX : E ≤ X := hEE₂.trans hE₂X
  set K1 : Subgroup ↥X := E₂.subgroupOf X with hK1
  set H1 : Subgroup ↥X := E.subgroupOf X with hH1
  have hHK : H1 ≤ K1 := Subgroup.subgroupOf_mono X hEE₂
  have eK : ↥K1 ≃* ↥E₂ := Subgroup.subgroupOfEquivOfLe hE₂X
  have hq1 : CFSG.IsQuasisimple ↥K1 := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hE₂
  have hsn1 : (H1.subgroupOf K1).IsSubnormal := hsn.subgroupOf
  have eN : ↥(H1.subgroupOf K1) ≃* ↥E :=
    (Subgroup.subgroupOfEquivOfLe hHK).trans (Subgroup.subgroupOfEquivOfLe hEX)
  have hNp : Group.IsPerfect ↥(H1.subgroupOf K1) :=
    Group.IsPerfect.ofSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  have hN1 : H1.subgroupOf K1 ≠ ⊥ := by
    intro h0
    apply hE1
    rw [Subgroup.eq_bot_iff_forall] at h0 ⊢
    intro x hx
    have hmem : (⟨⟨x, hEX hx⟩, hHK (Subgroup.mem_subgroupOf.mpr hx)⟩ : ↥K1) ∈
        H1.subgroupOf K1 := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hx)
    have h1 := h0 _ hmem
    have h2 := congrArg (fun y : ↥K1 => ((y : ↥X) : G)) h1
    simpa using h2
  have htop := eq_top_of_isSubnormal_perfect_of_quasisimple hq1 hsn1 hNp hN1
  intro x hx
  have : (⟨⟨x, hE₂X hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩ : ↥K1) ∈ H1.subgroupOf K1 :=
    htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp this)

namespace Sec11Indeed

namespace Sit

variable {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G}

theorem L_isQuasisimple (sit : Sit p A c L a d) : CFSG.IsQuasisimple ↥L :=
  S11d.isQuasisimple_of_evenLie (isPerfect_of_mem_thetaComponentsAt sit.L_mem.2) sit.even

theorem fieldAutSetting (sit : Sit p A c L a d) {f : G} (hfa : InducesFieldAut p f L) :
    FieldAutSetting p L f :=
  ⟨sit.prime, sit.five_le, sit.L_isQuasisimple, sit.even,
    (Sec9A.evenRank_subgroup_le (L ⊔ zpowers f)).trans (sectionTenSetup_evenRank_eq sit.setup).le,
    sit.p_ndvd, hfa⟩

theorem fieldAutRank (sit : Sit p A c L a d) {f : G} (hfA : f ∈ A) : FieldAutRank p L f :=
  ⟨(sectionTenSetup_evenRank_eq sit.setup).le, c, by simpa using sit.zpow_c_mem_centralizer 1,
    sit.c_ne_one, sit.pow_eq_one sit.c_mem, sit.A_comm hfA sit.c_mem⟩

theorem exists_zpow_coords_f (sit : Sit p A c L a d) {f : G} {i j : ℤ} (hij : f = a ^ i * c ^ j)
    (hi : ¬ (p : ℤ) ∣ i) {y : G} (hy : y ∈ A) :
    ∃ s t w : ℤ, y = f ^ s * c ^ t * d ^ w := by
  obtain ⟨x, z, w, hy'⟩ := sit.exists_zpow_coords hy
  have : Fact p.Prime := ⟨sit.prime⟩
  obtain ⟨m, hm⟩ := Sec11Indeed.exists_nat_mul_add_dvd (p := p) hi (-1)
  have hap : a ^ p = 1 := sit.pow_eq_one sit.a_mem
  have hzpow : ∀ n : ℤ, (p : ℤ) ∣ n → a ^ n = 1 := fun n hn => by
    obtain ⟨t', rfl⟩ := hn
    rw [zpow_mul, zpow_natCast, hap, one_zpow]
  have hac : Commute a c := sit.A_comm sit.a_mem sit.c_mem
  have hai : a ^ i = f * c ^ (-j) := by
    rw [hij, mul_assoc, ← zpow_add]
    simp
  have hfc : Commute f (c ^ (-j)) := by
    rw [hij]
    exact (hac.zpow_zpow i (-j)).mul_left ((Commute.refl c).zpow_zpow j (-j))
  set s : ℤ := (m : ℤ) * x with hs
  have hax : a ^ x = (a ^ i) ^ s := by
    rw [← zpow_mul]
    have h1 : a ^ ((i * (m : ℤ) + -1) * x) = 1 := hzpow _ (Dvd.dvd.mul_right hm x)
    calc a ^ x = a ^ ((i * (m : ℤ) + -1) * x) * a ^ x := by rw [h1, one_mul]
      _ = a ^ (i * s) := by
        rw [← zpow_add, hs]
        congr 1
        ring
  refine ⟨s, z - j * s, w, ?_⟩
  rw [hy', hax, hai, hfc.mul_zpow, ← zpow_mul]
  have hcz : c ^ (z - j * s) = c ^ (-j * s) * c ^ z := by
    rw [← zpow_add]
    congr 1
    ring
  rw [hcz]
  group


theorem kernel_le_zpowers (sit : Sit p A c L a d) (hCent : FieldFixedCentralizer) {f : G} {i j : ℤ}
    (hij : f = a ^ i * c ^ j) (hi : ¬ (p : ℤ) ∣ i) (hfa : InducesFieldAut p f L)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ thetaComponentsAt p f) (hAK₀ : A ≤ normalizer (K₀ : Set G))
    (hEK₀ : inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ≤ K₀)
    (hcact : ¬ ∀ k ∈ K₀, c * k * c⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K₀) :
    ∀ y ∈ A, (∀ k ∈ K₀, y * k * y⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K₀) →
      y ∈ zpowers f := by
  intro y hy htr
  have hp := sit.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcA := sit.c_mem
  have hdA := sit.d_mem
  have hfA : f ∈ A := by
    rw [hij]
    exact A.mul_mem (A.zpow_mem sit.a_mem i) (A.zpow_mem hcA j)
  obtain ⟨s, t, w, hy'⟩ := sit.exists_zpow_coords_f hij hi hy
  have hK₀C : K₀ ≤ centralizer ({f} : Set G) := (mem_thetaComponentsAt_iff.mp hK₀).1
  have hcp : c ^ p = 1 := sit.pow_eq_one hcA
  have hdp : d ^ p = 1 := sit.pow_eq_one hdA
  have hzp : ∀ (e : G) (n : ℤ), e ^ p = 1 → (p : ℤ) ∣ n → e ^ n = 1 := by
    intro e n he hn
    obtain ⟨u, rfl⟩ := hn
    rw [zpow_mul, zpow_natCast, he, one_zpow]
  set z' := c ^ t * d ^ w with hz'
  have hz'A : z' ∈ A := A.mul_mem (A.zpow_mem hcA t) (A.zpow_mem hdA w)
  have hfs : ∀ k ∈ K₀, f ^ s * k = k * f ^ s := fun k hk => by
    have h1 : k * f = f * k := Subgroup.mem_centralizer_singleton_iff.mp (hK₀C hk)
    exact (Commute.zpow_left (show Commute f k from h1.symm) s).eq
  have htr' : ∀ k ∈ K₀, z' * k * z'⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K₀ := by
    intro k hk
    have hz'k : z' * k * z'⁻¹ ∈ K₀ := (Subgroup.mem_normalizer_iff.mp (hAK₀ hz'A) k).mp hk
    have h1 := htr k hk
    have e : y * k * y⁻¹ = z' * k * z'⁻¹ := by
      have hy2 : y = f ^ s * z' := by rw [hy', hz', mul_assoc]
      rw [hy2]
      calc f ^ s * z' * k * (f ^ s * z')⁻¹ = f ^ s * (z' * k * z'⁻¹) * (f ^ s)⁻¹ := by group
        _ = z' * k * z'⁻¹ := by rw [hfs _ hz'k]; group
    rwa [e] at h1
  by_cases hw : (p : ℤ) ∣ w
  · have hdw : d ^ w = 1 := hzp d w hdp hw
    by_cases ht : (p : ℤ) ∣ t
    · have hct : c ^ t = 1 := hzp c t hcp ht
      rw [hy', hct, hdw]
      simp
    · exfalso
      have hz'eq : z' = c ^ t := by rw [hz', hdw, mul_one]
      have hct : ∀ k ∈ K₀, c ^ t * k * (c ^ t)⁻¹ * k⁻¹ ∈
          inSubgroup (aschbacherSolvableCore p) K₀ := by
        rw [← hz'eq]
        exact htr'
      obtain ⟨m, hm⟩ := Sec11Indeed.exists_nat_mul_add_dvd (p := p) ht (-1)
      have hc_eq : (c ^ t) ^ (m : ℤ) = c := by
        rw [← zpow_mul]
        have h1 : c ^ (t * (m : ℤ) + -1) = 1 := hzp c _ hcp hm
        calc c ^ (t * (m : ℤ)) = c ^ (t * (m : ℤ) + -1) * c := by
              rw [zpow_add, zpow_neg_one]
              group
          _ = c := by rw [h1, one_mul]
      apply hcact
      have := acts_trivially_zpow (hAK₀ (A.zpow_mem hcA t)) hct (m : ℤ)
      rwa [hc_eq] at this
  · exfalso
    set D := d ^ w with hD
    have hDL : D ∈ L := L.zpow_mem sit.d_mem_L w
    have hdf : d * f = f * d := sit.A_comm hdA hfA
    have hDf : D ∈ centralizer ({f} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Commute.zpow_left (show Commute d f from hdf) w).eq
    have hDX : D ∈ L ⊓ centralizer ({f} : Set G) := ⟨hDL, hDf⟩
    have hEq := fixedRes_isQuasisimple hfa
    have hDN : D ∈ normalizer (inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) :
        Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · intro he
        exact conj_mem_inSubgroup_perfectResidual hDX he
      · intro he
        have := conj_mem_inSubgroup_perfectResidual (inv_mem hDX) he
        have e3 : D⁻¹ * (D * e * D⁻¹) * D⁻¹⁻¹ = e := by group
        rwa [e3] at this
    have hDtheta : ∀ e ∈ inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)),
        D * e * D⁻¹ * e⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K₀ := by
      intro e he
      have h1 := htr' e (hEK₀ he)
      have heL : e ∈ L := (inSubgroup_perfectResidual_le _ he).1
      have hXL : D * e * D⁻¹ ∈ L := L.mul_mem (L.mul_mem hDL heL) (L.inv_mem hDL)
      have hct : (c ^ t) * (D * e * D⁻¹) = (D * e * D⁻¹) * c ^ t :=
        ((Subgroup.mem_centralizer_iff.mp (sit.zpow_c_mem_centralizer t)) _ hXL).symm
      have hcd : c ^ t * D = D * c ^ t :=
        (Commute.zpow_zpow (show Commute c d from sit.A_comm hcA hdA) t w).eq
      have e1 : z' * e * z'⁻¹ = D * e * D⁻¹ := by
        calc z' * e * z'⁻¹ = c ^ t * (D * e * D⁻¹) * (c ^ t)⁻¹ := by
              rw [hz']; group
          _ = D * e * D⁻¹ := by rw [hct]; group
      rwa [e1] at h1
    have hcentE := centralizes_of_commutators_mem_theta hp hEq hEK₀ hDN hDtheta
    have hDcomm : ∀ e ∈ inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)),
        (D : G) * e = e * D := by
      intro e he
      have := hcentE e he
      calc D * e = D * e * D⁻¹ * D := by group
        _ = e * D := by rw [this]
    have hDc : (⟨D, hDL⟩ : ↥L) ∈ Subgroup.center ↥L :=
      hCent G p L f (sit.fieldAutSetting hfa) (sit.pow_eq_one hfA) (sit.fieldAutRank hfA)
        ⟨D, hDL⟩ hDcomm
    obtain ⟨m, hm⟩ := Sec11Indeed.exists_nat_mul_add_dvd (p := p) hw (-1)
    have hd_eq : D ^ (m : ℤ) = d := by
      rw [hD, ← zpow_mul]
      have h1 : d ^ (w * (m : ℤ) + -1) = 1 := hzp d _ hdp hm
      calc d ^ (w * (m : ℤ)) = d ^ (w * (m : ℤ) + -1) * d := by
            rw [zpow_add, zpow_neg_one]
            group
        _ = d := by rw [h1, one_mul]
    have hdc : (⟨d, sit.d_mem_L⟩ : ↥L) ∈ Subgroup.center ↥L := by
      have := Subgroup.zpow_mem _ hDc (m : ℤ)
      have e2 : (⟨D, hDL⟩ : ↥L) ^ (m : ℤ) = ⟨d, sit.d_mem_L⟩ := Subtype.ext hd_eq
      rwa [e2] at this
    have h1 := orderOf_dvd_natCard (⟨⟨d, sit.d_mem_L⟩, hdc⟩ : Subgroup.center ↥L)
    have hordd : orderOf d = p := orderOf_eq_prime hdp sit.d_ne_one
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hordd] at h1
    exact sit.p_ndvd h1

end Sit

end Sec11Indeed

end CFSG.RankThree.PartOne
