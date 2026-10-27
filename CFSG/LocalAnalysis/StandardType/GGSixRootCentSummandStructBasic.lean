module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummand
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.CatalogueBPrimeJoin

section Finite

variable {A B : Type*} [Group A] [Group B]

theorem ggRCSS_not_isPGroup_two [Finite A] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpA : p ∣ Nat.card A) : ¬ IsPGroup 2 A := by
  intro h2
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpA
  obtain ⟨k, hk⟩ := h2 a
  have hdvd : p ∣ 2 ^ k := ha ▸ orderOf_dvd_of_pow_eq_one hk
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

theorem ggRCSS_isQuasisimple_of_surjective [Finite A] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : CFSG.IsQuasisimple A) (hpA : p ∣ Nat.card A) (f : A →* B)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) : CFSG.IsQuasisimple B := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hA (MonoidHom.normal_ker f) with h | h
  · exfalso
    refine ggRCSS_not_isPGroup_two hp hp2 hpA fun a => ?_
    obtain ⟨k, hk⟩ := hker ⟨a, h ▸ Subgroup.mem_top a⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · exact CFSG.LocalCores.isQuasisimple_of_surjective hA f hf h

theorem ggRCSS_primeResidual_quasisimple [Finite A] {p : ℕ} (hp : p.Prime)
    (hA : CFSG.IsQuasisimple A) (hpA : p ∣ Nat.card A) : primeResidual p A = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : (primeResidual p A).Normal := by
    have := primeResidual_characteristic p A
    infer_instance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hA hn with h | h
  · exact h
  · exfalso
    have : Group.IsPerfect A := hA.1
    let P : Sylow p A := Classical.choice inferInstance
    have hPc : (P : Subgroup A) ≤ Subgroup.center A :=
      (pSubgroup_le_residual p _ P.isPGroup').trans h
    have : IsMulCommutative (P : Subgroup A) := isMulCommutative_iff.mpr
      fun x y => Subtype.ext ((Subgroup.mem_center_iff.mp (hPc x.property)) y).symm
    have hnorm : Subgroup.normalizer (P : Set A) ≤ Subgroup.centralizer (P : Set A) := by
      intro x _
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      exact ((Subgroup.mem_center_iff.mp (hPc hy)) x).symm
    have hτ : MonoidHom.transferSylow P hnorm = 1 :=
      CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative _
    have hker : (MonoidHom.transferSylow P hnorm).ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr hτ
    have hnot := MonoidHom.not_dvd_card_ker_transferSylow P hnorm
    rw [hker, Subgroup.card_top] at hnot
    exact hnot hpA

theorem ggRCSS_primeResidual_eq_top [Finite A] [Group.IsPerfect A] {p : ℕ} (hp : p.Prime)
    (N : Subgroup A) [N.Normal] (hN : IsPGroup 2 N) (hq : CFSG.IsQuasisimple (A ⧸ N))
    (hpQ : p ∣ Nat.card (A ⧸ N)) : primeResidual p A = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hRQ : (primeResidual p A).map (QuotientGroup.mk' N) = ⊤ := by
    rw [primeResidual_map_surjective p _ (QuotientGroup.mk'_surjective N)]
    exact ggRCSS_primeResidual_quasisimple hp hq hpQ
  have hRn : (primeResidual p A).Normal := by
    have := primeResidual_characteristic p A
    infer_instance
  have h2 : IsPGroup 2 (A ⧸ primeResidual p A) := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have hy : QuotientGroup.mk' N y ∈ (primeResidual p A).map (QuotientGroup.mk' N) := by
      rw [hRQ]
      exact Subgroup.mem_top _
    obtain ⟨r, hr, hyr⟩ := Subgroup.mem_map.mp hy
    have hn : r⁻¹ * y ∈ N := (QuotientGroup.eq (s := N)).mp hyr
    obtain ⟨k, hk⟩ := hN ⟨r⁻¹ * y, hn⟩
    refine ⟨k, ?_⟩
    have h1 : (r⁻¹ * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : (QuotientGroup.mk' (primeResidual p A) y) =
        QuotientGroup.mk' (primeResidual p A) (r⁻¹ * y) := by
      rw [map_mul]
      have : QuotientGroup.mk' (primeResidual p A) r⁻¹ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ((primeResidual p A).inv_mem hr)
      rw [this, one_mul]
    change (QuotientGroup.mk' (primeResidual p A) y) ^ 2 ^ k = 1
    rw [h2, ← map_pow, h1, map_one]
  have hnil : Group.IsNilpotent (A ⧸ primeResidual p A) := h2.isNilpotent
  have hsub : Subsingleton (A ⧸ primeResidual p A) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (A ⧸ primeResidual p A) hnil
  rw [eq_top_iff]
  intro y _
  have : QuotientGroup.mk' (primeResidual p A) y = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff _).mp this

theorem ggRCSS_perm_three_key : ∀ x : Equiv.Perm (Fin 3), x * x = 1 → x ≠ 1 →
    x * (finRotate 3 * x * (finRotate 3)⁻¹) ≠ 1 ∧
      (x * (finRotate 3 * x * (finRotate 3)⁻¹)) ^ 3 = 1 := by
  decide +kernel

theorem ggRCSS_perm_three_normal_two (N : Subgroup (Equiv.Perm (Fin 3))) (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have hcop : ∀ y : Equiv.Perm (Fin 3), y ∈ N → Nat.Coprime (orderOf y) 3 := by
    intro y hy
    obtain ⟨k, hk⟩ := h2 ⟨y, hy⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk')
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hx2 : x * x = 1 := by
    have h6 : x ^ 6 = 1 := by
      have := pow_card_eq_one (G := Equiv.Perm (Fin 3)) (x := x)
      simpa [Fintype.card_perm, Nat.factorial] using this
    have h1 : orderOf x ∣ 2 * 3 := orderOf_dvd_of_pow_eq_one h6
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp ((hcop x hx).dvd_of_dvd_mul_right h1)
  obtain ⟨hg1, hg3⟩ := ggRCSS_perm_three_key x hx2 hx1
  have hy : x * (finRotate 3 * x * (finRotate 3)⁻¹) ∈ N := N.mul_mem hx (hN.conj_mem x hx _)
  have h1 : orderOf (x * (finRotate 3 * x * (finRotate 3)⁻¹)) ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  have h2' := Nat.Coprime.eq_one_of_dvd (hcop _ hy) h1
  exact hg1 (orderOf_eq_one_iff.mp h2')

theorem ggRCSS_card_eq_range_mul_ker [Finite A] (f : A →* B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem ggRCSS_dvd_card_of_surjective [Finite A] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (f : A →* B) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (hpA : p ∣ Nat.card A) : p ∣ Nat.card B := by
  have h1 := ggRCSS_card_eq_range_mul_ker f
  rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at h1
  have h3 : ¬ p ∣ Nat.card f.ker := ggNot_dvd_card_of_isPGroup_two hp hp2 hker
  rw [h1] at hpA
  exact ((Nat.Prime.dvd_mul hp).mp hpA).resolve_right h3

end Finite

section Layer

variable {G : Type} [Group G]

@[expose] def GGRCSStructConcl (p : ℕ) (G₀ M : Subgroup G) (r : G) : Prop :=
  ∃ 𝒮 : Set (Subgroup (GGRCSNbar r)),
    (∀ S ∈ 𝒮, GGRCSQuasiPiece p (ggRCSImg r M) S ∨
      (p = 3 ∧ GGRCSSThreePiece (ggRCSImg r M) S)) ∧
    ∀ y : ↥(Subgroup.centralizer ({r} : Set G)),
      (y : G) ∈ ggOTwoPrime (G₀ ⊓ Subgroup.centralizer {r}) → (y : G) ^ p = 1 →
        QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))) y ∈
          sSup 𝒮

@[expose] def GGRCSLayerQuasi (p : ℕ) (V Y Q : Subgroup G) : Prop :=
  Y ≤ V ∧ IsSubnormal Y V ∧ ⁅Y, Y⁆ = Y ∧ p ∣ Nat.card Y ∧ Q ≤ Y ∧ IsPGroup 2 Q ∧
    V ≤ Subgroup.normalizer (Q : Set G) ∧
    ∀ [(Q.subgroupOf Y).Normal], CFSG.IsQuasisimple (↥Y ⧸ Q.subgroupOf Y)

@[expose] def GGRCSLayerSThree (V S R₀ Q : Subgroup G) : Prop :=
  S ≤ R₀ ∧ R₀ ≤ V ∧ V ≤ Subgroup.normalizer (R₀ : Set G) ∧ Q ≤ S ∧ IsPGroup 2 Q ∧
    V ≤ Subgroup.normalizer (Q : Set G) ∧ Nat.card S = 3 * Nat.card Q ∧
    ∀ [(Q.subgroupOf R₀).Normal], Nonempty (↥R₀ ⧸ Q.subgroupOf R₀ ≃* Equiv.Perm (Fin 3))

@[expose] def GGRCSLayerPiece (p : ℕ) (V S : Subgroup G) : Prop :=
  (∃ Q, GGRCSLayerQuasi p V S Q) ∨ (p = 3 ∧ ∃ R₀ Q, GGRCSLayerSThree V S R₀ Q)

@[expose] def GGRCSLayer (p : ℕ) (G₀ M : Subgroup G) (r : G) : Prop :=
  ∃ 𝒮₀ : Set (Subgroup G),
    (∀ S ∈ 𝒮₀, GGRCSLayerPiece p (M ⊓ Subgroup.centralizer {r}) S) ∧
    ∀ y ∈ ggOTwoPrime (G₀ ⊓ Subgroup.centralizer {r}), y ^ p = 1 → y ∈ sSup 𝒮₀

noncomputable abbrev ggRCSHom (r : G) {A : Subgroup G}
    (hA : A ≤ Subgroup.centralizer ({r} : Set G)) : ↥A →* GGRCSNbar r :=
  (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))).comp
    (Subgroup.inclusion hA)

theorem ggRCSHom_range (r : G) {A : Subgroup G} (hA : A ≤ Subgroup.centralizer ({r} : Set G)) :
    (ggRCSHom r hA).range = ggRCSImg r A := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem ggRCSHom_ker_isPGroup (r : G) {A : Subgroup G}
    (hA : A ≤ Subgroup.centralizer ({r} : Set G)) : IsPGroup 2 (ggRCSHom r hA).ker := by
  have hP : IsPGroup 2 (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))) :=
    Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 _
  intro a
  have h1 : (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))
      (Subgroup.inclusion hA (a : ↥A)) : GGRCSNbar r) = 1 := MonoidHom.mem_ker.mp a.2
  obtain ⟨k, hk⟩ := hP ⟨Subgroup.inclusion hA (a : ↥A), (QuotientGroup.eq_one_iff _).mp h1⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h2 := congrArg (fun z : ↥(CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))) =>
    ((z : ↥(Subgroup.centralizer ({r} : Set G))) : G)) hk
  simpa using h2

theorem ggRCSImg_mono (r : G) {A B : Subgroup G} (h : A ≤ B) : ggRCSImg r A ≤ ggRCSImg r B :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem mem_ggRCSImg (r : G) {A : Subgroup G} {y : ↥(Subgroup.centralizer ({r} : Set G))}
    (hy : (y : G) ∈ A) :
    QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))) y ∈
      ggRCSImg r A :=
  ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem ggRCSImg_isPGroup (r : G) {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    IsPGroup 2 (ggRCSImg r Q) :=
  (hQ.comap_of_injective _ (Subgroup.subtype_injective _)).map _

theorem ggRCSImg_normal (r : G) {M B : Subgroup G} (hBM : B ≤ M)
    (hN : M ⊓ Subgroup.centralizer {r} ≤ Subgroup.normalizer (B : Set G)) :
    ((ggRCSImg r B).subgroupOf (ggRCSImg r M)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (ggRCSImg_mono r hBM)]
  rintro _ _ ⟨b, hb, rfl⟩ ⟨m, hm, rfl⟩
  refine ⟨m * b * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hb hm
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  have hmV : (m : G) ∈ M ⊓ Subgroup.centralizer {r} := ⟨hm, m.2⟩
  simpa using (Subgroup.mem_normalizer_iff.mp (hN hmV) b).mp hb

theorem ggRCSImg_isSubnormal (r : G) {M Y : Subgroup G}
    (h : IsSubnormal Y (M ⊓ Subgroup.centralizer {r})) :
    IsSubnormal (ggRCSImg r Y) (ggRCSImg r M) := by
  have h1 := ggAssemblyIsSubnormal_subgroupOf h (Subgroup.centralizer {r})
  rw [Subgroup.inf_subgroupOf_right] at h1
  exact ggIsSubnormal_map _ h1

theorem ggRCSImg_perfect (r : G) {Y : Subgroup G} (hY : Y ≤ Subgroup.centralizer ({r} : Set G))
    (hperf : ⁅Y, Y⁆ = Y) : ⁅ggRCSImg r Y, ggRCSImg r Y⁆ = ggRCSImg r Y := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have : Group.IsPerfect ↥(ggRCSHom r hY).range := Group.IsPerfect.range _
  rw [← ggRCSHom_range r hY]
  exact Subgroup.isPerfect_iff.mp this

theorem ggRCS_exists_quot_surj (r : G) {Y Q : Subgroup G}
    (hY : Y ≤ Subgroup.centralizer ({r} : Set G)) (hQY : Q ≤ Y) [(Q.subgroupOf Y).Normal]
    [((ggRCSImg r Q).subgroupOf (ggRCSImg r Y)).Normal] :
    ∃ f : ↥Y ⧸ Q.subgroupOf Y →* ↥(ggRCSImg r Y) ⧸ (ggRCSImg r Q).subgroupOf (ggRCSImg r Y),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  set C := Subgroup.centralizer ({r} : Set G) with hC
  set Pc := CFSG.Assembly.pCore 2 ↥C with hPc
  have hP : IsPGroup 2 Pc := Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 _
  set φ := ggRCSHom r hY with hφ
  have hmem : ∀ y : ↥Y, φ y ∈ ggRCSImg r Y := fun y => by
    rw [← ggRCSHom_range r hY]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  let ψ' : ↥Y →* ↥(ggRCSImg r Y) := φ.codRestrict _ hmem
  let g := (QuotientGroup.mk' ((ggRCSImg r Q).subgroupOf (ggRCSImg r Y))).comp ψ'
  have hg : Q.subgroupOf Y ≤ g.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' ((ggRCSImg r Q).subgroupOf (ggRCSImg r Y))) (ψ' y) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact mem_ggRCSImg r (Subgroup.mem_subgroupOf.mp hy)
  refine ⟨QuotientGroup.lift (Q.subgroupOf Y) g hg, ?_, ?_⟩
  · intro z
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨y, hy⟩ : ∃ y : ↥Y, φ y = s := by
      have hs : (s : GGRCSNbar r) ∈ (ggRCSHom r hY).range := by
        rw [ggRCSHom_range r hY]
        exact s.2
      exact hs
    refine ⟨QuotientGroup.mk y, ?_⟩
    rw [QuotientGroup.lift_mk]
    change (QuotientGroup.mk' _) (ψ' y) = _
    congr 1
    exact Subtype.ext hy
  · intro z
    obtain ⟨z, hz⟩ := z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 : g y = 1 := by
      rw [MonoidHom.mem_ker, QuotientGroup.lift_mk] at hz
      exact hz
    have h2 : (ψ' y : GGRCSNbar r) ∈ ggRCSImg r Q := by
      change (QuotientGroup.mk' ((ggRCSImg r Q).subgroupOf (ggRCSImg r Y))) (ψ' y) = 1 at h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    obtain ⟨q, hq, hqy⟩ := h2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hq
    have hw : q⁻¹ * Subgroup.inclusion hY y ∈ Pc := by
      have h3 : (QuotientGroup.mk' Pc) q = (QuotientGroup.mk' Pc) (Subgroup.inclusion hY y) := hqy
      exact (QuotientGroup.eq (s := Pc)).mp h3
    obtain ⟨k, hk⟩ := hP ⟨_, hw⟩
    have hk' : ((q : G)⁻¹ * (y : G)) ^ 2 ^ k = 1 := by
      have := congrArg (fun z : ↥Pc => ((z : ↥C) : G)) hk
      simpa using this
    have hqY : (q : G) ∈ Y := hQY hq
    refine ⟨k, Subtype.ext ?_⟩
    change (QuotientGroup.mk y : ↥Y ⧸ Q.subgroupOf Y) ^ 2 ^ k = 1
    have h4 : (QuotientGroup.mk y : ↥Y ⧸ Q.subgroupOf Y) =
        QuotientGroup.mk (⟨q, hqY⟩⁻¹ * y) := by
      rw [QuotientGroup.mk_mul]
      have : (QuotientGroup.mk (⟨q, hqY⟩⁻¹ : ↥Y) : ↥Y ⧸ Q.subgroupOf Y) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact Q.inv_mem hq
      rw [this, one_mul]
    rw [h4, ← QuotientGroup.mk_pow]
    rw [QuotientGroup.eq_one_iff]
    have h5 : (⟨q, hqY⟩⁻¹ * y : ↥Y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [h5]
    exact one_mem _

end Layer

section Pieces

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem GGRCSLayerPiece.le {p : ℕ} {V S : Subgroup G} (h : GGRCSLayerPiece p V S) : S ≤ V := by
  rcases h with ⟨Q, hQ⟩ | ⟨-, R₀, Q, hT⟩
  · exact hQ.1
  · exact hT.1.trans hT.2.1

theorem ggRCSPiece_of_layer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {r : G} {M Y Q : Subgroup G}
    (h : GGRCSLayerQuasi p (M ⊓ Subgroup.centralizer {r}) Y Q) :
    GGRCSPiece p (ggRCSImg r M) (ggRCSImg r Y) (ggRCSImg r Q) := by
  obtain ⟨hYV, hsn, hperf, hpY, hQY, hQ2, hQN, hq⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have hYC : Y ≤ Subgroup.centralizer ({r} : Set G) := hYV.trans inf_le_right
  have hYM : Y ≤ M := hYV.trans inf_le_left
  have hQnY : (Q.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQY]
    intro a b ha hb
    exact (Subgroup.mem_normalizer_iff.mp (hQN (hYV hb)) a).mp ha
  have hq' := @hq hQnY
  set S := ggRCSImg r Y with hS
  set Qb := ggRCSImg r Q with hQb
  have hSV : S ≤ ggRCSImg r M := ggRCSImg_mono r hYM
  have hQbS : Qb ≤ S := ggRCSImg_mono r hQY
  have hQbn : (Qb.subgroupOf (ggRCSImg r M)).Normal := ggRCSImg_normal r (hQY.trans hYM) hQN
  have hQbnS : (Qb.subgroupOf S).Normal := ggRCS_normal_subgroupOf hSV hQbS hQbn
  have hQb2 : IsPGroup 2 Qb := ggRCSImg_isPGroup r hQ2
  have hQb2S : IsPGroup 2 (Qb.subgroupOf S) :=
    hQb2.comap_of_injective S.subtype (Subgroup.subtype_injective S)
  have hSperf : ⁅S, S⁆ = S := ggRCSImg_perfect r hYC hperf
  have hpYQ : p ∣ Nat.card (↥Y ⧸ Q.subgroupOf Y) := by
    refine ggRCSS_dvd_card_of_surjective hp hp2 (QuotientGroup.mk' (Q.subgroupOf Y))
      (QuotientGroup.mk'_surjective _) ?_ hpY
    rw [QuotientGroup.ker_mk']
    exact hQ2.comap_of_injective Y.subtype (Subgroup.subtype_injective Y)
  obtain ⟨f, hf, hfk⟩ := ggRCS_exists_quot_surj r hYC hQY
  have hSq : CFSG.IsQuasisimple (↥S ⧸ Qb.subgroupOf S) :=
    ggRCSS_isQuasisimple_of_surjective hp hp2 hq' hpYQ f hf hfk
  have hpSQ : p ∣ Nat.card (↥S ⧸ Qb.subgroupOf S) :=
    ggRCSS_dvd_card_of_surjective hp hp2 f hf hfk hpYQ
  have hpS : p ∣ Nat.card S := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Qb.subgroupOf S)]
    exact hpSQ.mul_right _
  have : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.mpr hSperf
  have hres := ggRCSS_primeResidual_eq_top hp (Qb.subgroupOf S) hQb2S hSq hpSQ
  rw [primeResidual_eq_closure] at hres
  have hgen : S ≤ Subgroup.closure {s : GGRCSNbar r | s ∈ S ∧ ∃ n : ℕ, s ^ p ^ n = 1} := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥S) ∈ Subgroup.closure {y : ↥S | ∃ k : ℕ, orderOf y = p ^ k} := by
      rw [hres]
      exact Subgroup.mem_top _
    have h2 := Subgroup.mem_map_of_mem S.subtype h1
    rw [MonoidHom.map_closure] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
    refine ⟨y.2, k, ?_⟩
    change ((y : GGRCSNbar r)) ^ p ^ k = 1
    rw [← Subgroup.coe_pow, ← hk, pow_orderOf_eq_one, Subgroup.coe_one]
  exact ⟨hSV, ggRCSImg_isSubnormal r hsn, hSperf, hpS, hgen, hQbS, hQb2, hQbn,
    by intro _; exact hSq⟩

theorem ggRCSSThreePiece_of_layer {r : G} {M S R₀ Q : Subgroup G}
    (h : GGRCSLayerSThree (M ⊓ Subgroup.centralizer {r}) S R₀ Q) :
    GGRCSSThreePiece (ggRCSImg r M) (ggRCSImg r S) := by
  obtain ⟨hSR, hRV, hRN, hQS, hQ2, hQN, hcard, he⟩ := h
  have hRM : R₀ ≤ M := hRV.trans inf_le_left
  have hRC : R₀ ≤ Subgroup.centralizer ({r} : Set G) := hRV.trans inf_le_right
  have hSC : S ≤ Subgroup.centralizer ({r} : Set G) := hSR.trans hRC
  have hQC : Q ≤ Subgroup.centralizer ({r} : Set G) := hQS.trans hSC
  have hQR : Q ≤ R₀ := hQS.trans hSR
  refine ⟨ggRCSImg r R₀, ggRCSImg r Q, ggRCSImg_mono r hSR, ggRCSImg_mono r hRM,
    ggRCSImg_normal r hRM hRN, ggRCSImg_mono r hQS, ggRCSImg_isPGroup r hQ2,
    ggRCSImg_normal r (hQR.trans hRM) hQN, ?_, ?_⟩
  ·
    have hQnS : (Q.subgroupOf S).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hQS]
      intro a b ha hb
      exact (Subgroup.mem_normalizer_iff.mp (hQN (hRV (hSR hb))) a).mp ha
    have hQcard : Nat.card (Q.subgroupOf S) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
    have hSQ3 : Nat.card (↥S ⧸ Q.subgroupOf S) = 3 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf S)
      rw [hQcard, hcard] at h1
      have hQpos : 0 < Nat.card Q := Nat.card_pos
      exact (Nat.eq_of_mul_eq_mul_right hQpos h1).symm
    have key : ∀ s : ↥S, ggRCSHom r hSC s = 1 → (s : G) ∈ Q := by
      intro s hs
      obtain ⟨k, hk⟩ := ggRCSHom_ker_isPGroup r hSC ⟨s, hs⟩
      have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      set z : ↥S ⧸ Q.subgroupOf S := QuotientGroup.mk s
      have hz1 : z ^ 2 ^ k = 1 := by rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
      have hz3 : z ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥S ⧸ Q.subgroupOf S) (x := z)
        rwa [hSQ3] at this
      have hzo : orderOf z ∣ Nat.gcd (2 ^ k) 3 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz1) (orderOf_dvd_of_pow_eq_one hz3)
      rw [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)), Nat.dvd_one,
        orderOf_eq_one_iff] at hzo
      have := (QuotientGroup.eq_one_iff s).mp hzo
      exact Subgroup.mem_subgroupOf.mp this
    let e : (ggRCSHom r hSC).ker ≃ (ggRCSHom r hQC).ker :=
      { toFun := fun s => ⟨⟨s.1, key s.1 s.2⟩, s.2⟩
        invFun := fun q => ⟨⟨q.1, hQS q.1.2⟩, q.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have h1 := ggRCSS_card_eq_range_mul_ker (ggRCSHom r hSC)
    have h2 := ggRCSS_card_eq_range_mul_ker (ggRCSHom r hQC)
    rw [ggRCSHom_range] at h1 h2
    rw [Nat.card_congr e, hcard, h2] at h1
    have hpos : 0 < Nat.card (ggRCSHom r hQC).ker := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← h1, mul_assoc])).symm
  ·
    intro _
    have hQnR : (Q.subgroupOf R₀).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hQR]
      intro a b ha hb
      exact (Subgroup.mem_normalizer_iff.mp (hQN (hRV hb)) a).mp ha
    obtain ⟨e⟩ := @he hQnR
    obtain ⟨f, hf, hfk⟩ := ggRCS_exists_quot_surj r hRC hQR
    have hker : f.ker = ⊥ := by
      have h1 : (f.ker.map e.toMonoidHom).Normal :=
        (MonoidHom.normal_ker f).map e.toMonoidHom e.surjective
      have h2 := ggRCSS_perm_three_normal_two _ h1 (hfk.map e.toMonoidHom)
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h2
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
    exact ⟨(MulEquiv.ofBijective f ⟨hinj, hf⟩).symm.trans e⟩

theorem ggRCSStructConcl_of_layer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ M : Subgroup G}
    {r : G} (h : GGRCSLayer p G₀ M r) : GGRCSStructConcl p G₀ M r := by
  obtain ⟨𝒮₀, h𝒮₀, hcov⟩ := h
  refine ⟨ggRCSImg r '' 𝒮₀, ?_, ?_⟩
  · rintro _ ⟨S₀, hS₀, rfl⟩
    rcases h𝒮₀ S₀ hS₀ with ⟨Q, hQ⟩ | ⟨hp3, R₀, Q, hT⟩
    · exact Or.inl ⟨_, ggRCSPiece_of_layer hp hp2 hQ⟩
    · exact Or.inr ⟨hp3, ggRCSSThreePiece_of_layer hT⟩
  · intro y hyX hyp
    have hle : sSup 𝒮₀ ≤ ((sSup (ggRCSImg r '' 𝒮₀)).comap (QuotientGroup.mk'
        (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))))).map
          (Subgroup.centralizer ({r} : Set G)).subtype := by
      refine sSup_le fun S₀ hS₀ s hs => ?_
      have hS₀C : S₀ ≤ Subgroup.centralizer ({r} : Set G) :=
        (h𝒮₀ S₀ hS₀).le.trans inf_le_right
      refine ⟨⟨s, hS₀C hs⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have hmemS : ggRCSImg r S₀ ∈ ggRCSImg r '' 𝒮₀ := ⟨S₀, hS₀, rfl⟩
      exact (le_sSup hmemS : ggRCSImg r S₀ ≤ sSup (ggRCSImg r '' 𝒮₀))
        (mem_ggRCSImg r (y := ⟨s, hS₀C hs⟩) hs)
    obtain ⟨c, hc, hcy⟩ := hle (hcov _ hyX hyp)
    have hcy' : c = y := Subtype.ext hcy
    rw [← hcy']
    exact hc

end Pieces

section Derived

variable {G : Type} [Group G]

noncomputable abbrev ggRCSX (G₀ : Subgroup G) (r : G) : Subgroup G :=
  ggOTwoPrime (G₀ ⊓ Subgroup.centralizer {r})

noncomputable abbrev ggRCSXd (G₀ : Subgroup G) (r : G) : Subgroup G :=
  CFSG.Quasithin.perfectCore (ggRCSX G₀ r)

@[expose] def GGRootCentDerivedAt (p : ℕ) (G₀ : Subgroup G) (r : G) : Prop :=
  (∀ y ∈ ggRCSX G₀ r, y ^ p = 1 → y = 1) ∨
  (p ∣ Nat.card (ggRCSXd G₀ r) ∧
    (∃ Q : Subgroup G, Q ≤ ggRCSXd G₀ r ∧ IsPGroup 2 Q ∧ (Q.subgroupOf (ggRCSXd G₀ r)).Normal ∧
      ∀ [(Q.subgroupOf (ggRCSXd G₀ r)).Normal],
        CFSG.IsQuasisimple (↥(ggRCSXd G₀ r) ⧸ Q.subgroupOf (ggRCSXd G₀ r))) ∧
    ∀ y ∈ ggRCSX G₀ r, y ^ p = 1 → y ∈ ggRCSXd G₀ r) ∨
  (∃ Q : Subgroup G, Q ≤ ggRCSX G₀ r ∧ IsPGroup 2 Q ∧
    (Q.subgroupOf (ggRCSX G₀ r)).Normal ∧
    ∀ [(Q.subgroupOf (ggRCSX G₀ r)).Normal],
      Nonempty (↥(ggRCSX G₀ r) ⧸ Q.subgroupOf (ggRCSX G₀ r) ≃* Equiv.Perm (Fin 3)))

theorem ggRCSS_card_comap_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f) (H : Subgroup B) :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  let g : ↥(H.comap f) →* ↥H := (f.comp (H.comap f).subtype).codRestrict H (fun a => a.2)
  have hg : Function.Surjective g := by
    intro h
    obtain ⟨a, ha⟩ := hf h
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    rw [Subgroup.mem_comap, ha]
    exact h.2
  have h1 := ggRCSS_card_eq_range_mul_ker g
  rw [MonoidHom.range_eq_top.mpr hg, Subgroup.card_top] at h1
  rw [h1]
  congr 1
  refine Nat.card_congr
    { toFun := fun a => ⟨a.1.1, ?_⟩
      invFun := fun b => ⟨⟨b.1, ?_⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · have h2 := congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
    exact MonoidHom.mem_ker.mpr h2
  · rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp b.2]
    exact one_mem _
  · rw [MonoidHom.mem_ker]
    exact Subtype.ext (MonoidHom.mem_ker.mp b.2)

theorem ggRCSS_sign_of_pow_three :
    ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → Equiv.Perm.sign σ = 1 := by
  decide +kernel

theorem ggRCSS_card_alternating_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 3)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h
  have h6 : Nat.factorial 3 = 6 := rfl
  omega

variable [Finite G]

theorem ggRCS_quasisimple_pCoreOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) [hQn : (Q.subgroupOf Y).Normal]
    (hq : CFSG.IsQuasisimple (↥Y ⧸ Q.subgroupOf Y)) (hpY : p ∣ Nat.card Y)
    [((CFSG.Assembly.pCoreOf 2 Y).subgroupOf Y).Normal] :
    CFSG.IsQuasisimple (↥Y ⧸ (CFSG.Assembly.pCoreOf 2 Y).subgroupOf Y) := by
  have hQ2Y : IsPGroup 2 (Q.subgroupOf Y) := hQ2.comap_of_injective Y.subtype Y.subtype_injective
  have hQP : Q.subgroupOf Y ≤ (CFSG.Assembly.pCoreOf 2 Y).subgroupOf Y := by
    have h1 := Dichotomy.CentralizerContainment.le_pCore_assembly hQn hQ2Y
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    exact ⟨y, h1 hy, rfl⟩
  have hker :
      Q.subgroupOf Y ≤ (QuotientGroup.mk' ((CFSG.Assembly.pCoreOf 2 Y).subgroupOf Y)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hQP
  have hpYQ : p ∣ Nat.card (↥Y ⧸ Q.subgroupOf Y) := by
    refine ggRCSS_dvd_card_of_surjective hp hp2 (QuotientGroup.mk' (Q.subgroupOf Y))
      (QuotientGroup.mk'_surjective _) ?_ hpY
    rw [QuotientGroup.ker_mk']
    exact hQ2Y
  refine ggRCSS_isQuasisimple_of_surjective hp hp2 hq hpYQ
    (QuotientGroup.lift (Q.subgroupOf Y) (QuotientGroup.mk' _) hker) ?_ ?_
  · intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ z
    exact ⟨QuotientGroup.mk y, QuotientGroup.lift_mk _ _ _⟩
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MonoidHom.mem_ker, QuotientGroup.lift_mk, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hz
    obtain ⟨k, hk⟩ := ggIsPGroup_pCoreOf 2 Y ⟨_, hz⟩
    have hk' : y ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    refine ⟨k, Subtype.ext ?_⟩
    change (QuotientGroup.mk y : ↥Y ⧸ Q.subgroupOf Y) ^ 2 ^ k = 1
    rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]

end Derived

end CFSG.StandardType
