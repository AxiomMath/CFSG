module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A4
open scoped Pointwise

variable {G : Type*} [Group G] {X M : Subgroup G}

namespace A4

theorem coe_sup_eq_mul_of_mul_comm {X R : Subgroup G} (h : (R : Set G) * X = X * R) :
    (↑(X ⊔ R) : Set G) = X * R := by
  rw [Subgroup.sup_eq_closure_mul]
  refine Set.Subset.antisymm (fun x hx => ?_) Subgroup.subset_closure
  induction hx using Subgroup.closure_induction'' with
  | one => exact ⟨1, X.one_mem, 1, R.one_mem, mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    have : y⁻¹ * x⁻¹ ∈ (R : Set G) * X := Set.mul_mem_mul (R.inv_mem hy) (X.inv_mem hx)
    rw [h] at this
    simpa using this
  | mul x' x'' _ _ hx hx' =>
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hx
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hx'
    have : y₁ * x₂ ∈ (R : Set G) * X := Set.mul_mem_mul hy₁ hx₂
    rw [h] at this
    obtain ⟨a, ha, b, hb, hab⟩ := this
    have hab' : a * b = y₁ * x₂ := hab
    refine ⟨x₁ * a, X.mul_mem hx₁ ha, b * y₂, R.mul_mem hb hy₂, ?_⟩
    calc x₁ * a * (b * y₂) = x₁ * (a * b) * y₂ := by group
      _ = x₁ * (y₁ * x₂) * y₂ := by rw [hab']
      _ = x₁ * y₁ * (x₂ * y₂) := by group

theorem exists_pow_mem_of_mul {H M R : Subgroup G} (hN : M ≤ Subgroup.normalizer (H : Set G))
    (hR : IsPGroup 2 R) {m x r : G} (hm : m ∈ M) (hx : x ∈ H) (hr : r ∈ R)
    (hmxr : m = x * r) (hHM : H ≤ M) : ∃ k : ℕ, m ^ 2 ^ k ∈ H := by
  have hrM : r ∈ M := by
    have : r = x⁻¹ * m := by rw [hmxr]; group
    rw [this]; exact M.mul_mem (M.inv_mem (hHM hx)) hm
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  have hk' : r ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨x', hx', h⟩ := exists_pow_mul_eq hx (hN hrM) (2 ^ k)
  refine ⟨k, ?_⟩
  rw [hmxr, h, hk', mul_one]
  exact hx'

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

end A4

theorem oTwoUpper_le_of_subnormal_mul {H K R : Subgroup G} (h : IsSubnormal H K)
    (hR : IsPGroup 2 R) :
    (∀ k ∈ K, ∃ x ∈ H, ∃ r ∈ R, k = x * r) → oTwoUpper K ≤ H := by
  induction h with
  | refl K => intro _; exact oTwoUpper_le K
  | @step H M K hle hN hMK ih =>
    intro hKR
    have hM : oTwoUpper K ≤ M := ih fun k hk => by
      obtain ⟨x, hx, r, hr, h⟩ := hKR k hk
      exact ⟨x, hle hx, r, hr, h⟩
    have hHM : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    have hMK' : M ≤ K := subnormal_le hMK
    have h1 : oTwoUpper K ≤ oTwoUpper M := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      exact mem_oTwoUpper_of_odd (hM (Subgroup.subset_closure hx)) hx.2
    refine h1.trans (oTwoUpper_le_of_pow_mem fun m hm => ?_)
    obtain ⟨x, hx, r, hr, hmxr⟩ := hKR m (hMK' hm)
    exact exists_pow_mem_of_mul hHM hR hm hx hr hmxr hle

theorem a4_2_1 {R : Subgroup G} (hRM : R ≤ M) (hR : IsPGroup 2 R) :
    IsSignalizer M X R ↔ ⁅X, R⁆ ≤ R :=
  isSignalizer_iff_commutator_le hRM hR

theorem a4_2_2 (hX : X = oTwoUpper X) (hXM : IsSubnormal X M) {R : Subgroup G} (hRM : R ≤ M)
    (hR : IsPGroup 2 R) (hRX : (R : Set G) * X = X * R) :
    X = oTwoUpper (X ⊔ R) ∧ (X.subgroupOf (X ⊔ R)).Normal := by
  have hKM : X ⊔ R ≤ M := sup_le (subnormal_le hXM) hRM
  have hXK : IsSubnormal X (X ⊔ R) := subnormal_of_le_of_le hXM le_sup_left hKM
  have hmul := coe_sup_eq_mul_of_mul_comm hRX
  have hle : oTwoUpper (X ⊔ R) ≤ X := by
    refine oTwoUpper_le_of_subnormal_mul hXK hR fun k hk => ?_
    have hk' : k ∈ (↑(X ⊔ R) : Set G) := hk
    rw [hmul] at hk'
    obtain ⟨x, hx, r, hr, rfl⟩ := hk'
    exact ⟨x, hx, r, hr, rfl⟩
  have h1 : oTwoUpper X ≤ oTwoUpper (X ⊔ R) := oTwoUpper_mono le_sup_left
  have heq : X = oTwoUpper (X ⊔ R) := le_antisymm (hX.le.trans h1) hle
  refine ⟨heq, Subgroup.normal_subgroupOf_of_le_normalizer ?_⟩
  have h2 := le_normalizer_oTwoUpper (X ⊔ R)
  rw [← heq] at h2
  exact h2

theorem a4_2_3 (hX : X = oTwoUpper X) (hXM : IsSubnormal X M) {R : Subgroup G}
    (hR : IsSignalizer M X R) : ⁅X, R⁆ ≤ pCoreOf 2 X := by
  have hRN : X ≤ Subgroup.normalizer (R : Set G) := hR.2.2
  have h1 : (R : Set G) * X = X * R := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left R X hRN, sup_comm,
      Subgroup.coe_mul_of_left_le_normalizer_right X R hRN]
  obtain ⟨-, hnorm⟩ := a4_2_2 hX hXM hR.1 hR.2.1 h1
  have hXR : X ⊔ R ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hnorm
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := le_sup_right.trans hXR
  have hcX : ⁅X, R⁆ ≤ X := by
    refine Subgroup.commutator_le.mpr fun x hx r hr => ?_
    have : r * x⁻¹ * r⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hRX hr) x⁻¹).mp (X.inv_mem hx)
    have h2 : x * (r * x⁻¹ * r⁻¹) ∈ X := X.mul_mem hx this
    have h3 : x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹) := by group
    show x * r * x⁻¹ * r⁻¹ ∈ X
    rw [h3]
    exact h2
  have hcR : ⁅X, R⁆ ≤ R := (isSignalizer_iff_commutator_le hR.1 hR.2.1).mp hR
  exact le_pCoreOf_of_le_normalizer 2 hcX (Subgroup.normalizer_commutator_ge_left X R)
    (hR.2.1.to_le hcR)

section Finite

variable [Finite G]

theorem signalizer_le_centralizerSection (hX : X = oTwoUpper X) (hXM : IsSubnormal X M)
    {R : Subgroup G} (hR : IsSignalizer M X R) :
    R ≤ centralizerSection M X (pCoreOf 2 X) :=
  (le_centralizerSection_iff (pCoreOf_le 2 X)).mpr ⟨hR.1, a4_2_3 hX hXM hR⟩

theorem pCoreOf_le_centralizerSection (hXM : X ≤ M) :
    pCoreOf 2 X ≤ centralizerSection M X (pCoreOf 2 X) := by
  refine (le_centralizerSection_iff (pCoreOf_le 2 X)).mpr ⟨(pCoreOf_le 2 X).trans hXM, ?_⟩
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp (le_normalizer_pCoreOf 2 X)

omit [Finite G] in
theorem le_normalizer_centralizerSection (M X : Subgroup G) :
    M ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (centralizerSection M X (pCoreOf 2 X) : Set G) := by
  intro g hg
  have hgM : g ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hg.1
  have hgX : g ∈ Subgroup.normalizer (X : Set G) := hg.2
  have hgZ : g ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 X hgX
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_centralizerSection hgM hgX hgZ hx, fun hx => ?_⟩
  have := conj_mem_centralizerSection (Subgroup.inv_mem _ hgM) (Subgroup.inv_mem _ hgX)
    (Subgroup.inv_mem _ hgZ) hx
  simpa [mul_assoc] using this

theorem pCoreOf_le_of_isSylowTwoOf_centralizerSection (hXM : X ≤ M) {S : Subgroup G}
    (hS : IsSylowTwoOf S (centralizerSection M X (pCoreOf 2 X))) : pCoreOf 2 X ≤ S :=
  le_of_normal_of_isSylowTwoOf hS (pCoreOf_le_centralizerSection hXM)
    (Subgroup.normal_subgroupOf_of_le_normalizer
      (centralizerSection_le_normalizer_right M X _)) (pCoreOf_isPGroup 2 X)

theorem isSylowTwoOf_inf_centralizerSection {T : Subgroup G}
    (hT : IsSylowTwoOf T (M ⊓ Subgroup.normalizer (X : Set G))) :
    IsSylowTwoOf (T ⊓ centralizerSection M X (pCoreOf 2 X))
      (centralizerSection M X (pCoreOf 2 X)) :=
  isSylowTwoOf_inf_normal hT
    (le_inf (centralizerSection_le_left M X _) (centralizerSection_le_normalizer_left M X _))
    (le_normalizer_centralizerSection M X)

theorem isSignalizer_of_isSylowTwoOf_centralizerSection (hXM : X ≤ M) {S : Subgroup G}
    (hS : IsSylowTwoOf S (centralizerSection M X (pCoreOf 2 X))) : IsSignalizer M X S := by
  have hO2S : pCoreOf 2 X ≤ S := pCoreOf_le_of_isSylowTwoOf_centralizerSection hXM hS
  have hcomm : ⁅X, S⁆ ≤ pCoreOf 2 X := ((le_centralizerSection_iff (pCoreOf_le 2 X)).mp hS.1).2
  refine ⟨hS.1.trans (centralizerSection_le_left M X _), hS.2.1, ?_⟩
  rw [Subgroup.le_normalizer_iff_commutator_le_right]
  exact hcomm.trans hO2S

theorem a4_2_4 (hX : X = oTwoUpper X) (hXM : IsSubnormal X M) (R : Subgroup G) :
    IsMaxSignalizer M X R ↔ IsSylowTwoOf R (centralizerSection M X (pCoreOf 2 X)) := by
  have key := fun S (hS : IsSylowTwoOf S (centralizerSection M X (pCoreOf 2 X))) =>
    isSignalizer_of_isSylowTwoOf_centralizerSection (subnormal_le hXM) hS
  constructor
  · intro hR
    have hRM₀ : R ≤ centralizerSection M X (pCoreOf 2 X) :=
      signalizer_le_centralizerSection hX hXM hR.1
    obtain ⟨S, hS, hRS⟩ := exists_isSylowTwoOf_ge hRM₀ hR.1.2.1
    have := hR.eq_of_le (key S hS) hRS
    rw [← this]
    exact hS
  · intro hR
    obtain ⟨R', hR', hRR'⟩ := exists_isMaxSignalizer_ge (key R hR)
    have hR'M₀ : R' ≤ centralizerSection M X (pCoreOf 2 X) :=
      signalizer_le_centralizerSection hX hXM hR'.1
    have h1 := (isSylowTwoOf_iff_maximal.mp hR).2.2 R' hR'M₀ hR'.1.2.1 hRR'
    rw [← le_antisymm h1 hRR']
    exact hR'

theorem pCoreOf_le_of_isMaxSignalizer_of_subnormal (hX : X = oTwoUpper X)
    (hXM : IsSubnormal X M) {S : Subgroup G} (hS : IsMaxSignalizer M X S) : pCoreOf 2 X ≤ S :=
  pCoreOf_le_of_isSylowTwoOf_centralizerSection (subnormal_le hXM) ((a4_2_4 hX hXM S).mp hS)

namespace A4

theorem exists_mem_normalizer_not_mem {R S : Subgroup G} (hS : IsPGroup 2 S) (hRS : R < S) :
    ∃ s ∈ S, s ∈ Subgroup.normalizer (R : Set G) ∧ s ∉ R := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hle : R ≤ S := hRS.le
  have hlt : R.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hRS.not_ge h
  have hlt' := Group.normalizerCondition_of_isNilpotent (G := S) (R.subgroupOf S) hlt
  obtain ⟨s, hs, hsn⟩ := IsConcreteLE.exists_of_lt hlt'
  refine ⟨s, s.2, ?_, fun h => hsn h⟩
  have : s ∈ (Subgroup.normalizer (R : Set G)).subgroupOf S := by
    rw [Subgroup.subgroupOf_normalizer_eq hle]
    exact hs
  exact this

end A4

theorem a4_2_5 (hX : X = oTwoUpper X) (hXM : IsSubnormal X M) {T : Subgroup G}
    (hT : IsSylowTwoOf T (M ⊓ Subgroup.normalizer (X : Set G))) :
    IsMaxSignalizer M X (pCoreOf 2 (X ⊔ T)) := by
  set M₀ := centralizerSection M X (pCoreOf 2 X) with hM₀
  set N := M ⊓ Subgroup.normalizer (X : Set G) with hN
  have hNnorm : N ≤ Subgroup.normalizer (M₀ : Set G) := le_normalizer_centralizerSection M X
  have hmax : IsMaxSignalizer M X (T ⊓ M₀) :=
    (a4_2_4 hX hXM _).mpr (isSylowTwoOf_inf_centralizerSection hT)
  have hTN : T ≤ N := hT.1
  have hXM' : X ≤ M := subnormal_le hXM
  have hle : T ⊓ M₀ ≤ pCoreOf 2 (X ⊔ T) := by
    refine le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) ?_ hmax.1.2.1
    refine sup_le hmax.1.2.2 ?_
    intro t ht
    exact mem_normalizer_inf (Subgroup.le_normalizer ht) (hNnorm (hTN ht))
  have hsig : IsSignalizer M X (pCoreOf 2 (X ⊔ T)) :=
    ⟨(pCoreOf_le 2 _).trans (sup_le hXM' (hTN.trans inf_le_left)), pCoreOf_isPGroup 2 _,
      le_sup_left.trans (le_normalizer_pCoreOf 2 _)⟩
  rw [hmax.eq_of_le hsig hle]
  exact hmax

theorem a4_2_6_1 {R : Subgroup G} (hR : IsMaxSignalizer M X R)
    (hodd : Odd ((M ⊓ Subgroup.normalizer (R : Set G)).relIndex (Subgroup.normalizer (R : Set G)))) :
    R = pCoreOf 2 (Subgroup.normalizer (R : Set G)) := by
  set N := Subgroup.normalizer (R : Set G) with hN
  obtain ⟨S, hS, hSle⟩ := exists_isSylowTwoOf_le_of_odd (inf_le_right : M ⊓ N ≤ N) hodd
  have hO2S : pCoreOf 2 N ≤ S :=
    le_of_normal_of_isSylowTwoOf hS (pCoreOf_le 2 N)
      (Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_pCoreOf 2 N))
      (pCoreOf_isPGroup 2 N)
  have hsig : IsSignalizer M X (pCoreOf 2 N) :=
    ⟨(hO2S.trans hSle).trans inf_le_left, pCoreOf_isPGroup 2 N,
      hR.1.2.2.trans (le_normalizer_pCoreOf 2 N)⟩
  have hRP : R ≤ pCoreOf 2 N :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hR.1.2.1
  exact (hR.eq_of_le hsig hRP).symm

theorem a4_2_6_2 {R : Subgroup G} (hR : IsMaxSignalizer M X R)
    (hN : Subgroup.normalizer (R : Set G) ≤ M) : IsMaxSignalizer ⊤ X R := by
  refine ⟨⟨le_top, hR.1.2.1, hR.1.2.2⟩, fun S hS hRS => ?_⟩
  have hsig : IsSignalizer M X (S ⊓ Subgroup.normalizer (R : Set G)) := by
    refine ⟨inf_le_right.trans hN, hS.2.1.to_inf_left, ?_⟩
    intro x hx
    exact mem_normalizer_inf (hS.2.2 hx) (Subgroup.le_normalizer.trans (le_refl _) (hR.1.2.2 hx))
  have hRle : R ≤ S ⊓ Subgroup.normalizer (R : Set G) := le_inf hRS Subgroup.le_normalizer
  have heq := hR.eq_of_le hsig hRle
  by_contra hSR
  have hlt : R < S := lt_of_le_of_ne hRS (fun h => hSR (h ▸ le_rfl))
  obtain ⟨s, hsS, hsN, hsR⟩ := exists_mem_normalizer_not_mem hS.2.1 hlt
  exact hsR (heq ▸ (⟨hsS, hsN⟩ : s ∈ S ⊓ Subgroup.normalizer (R : Set G)))

omit [Finite G] in
theorem centralizerSection_normalizer_eq (X Z : Subgroup G) :
    centralizerSection (Subgroup.normalizer (X : Set G)) X Z = centralizerSection ⊤ X Z := by
  ext m
  simp only [mem_centralizerSection, Subgroup.mem_top, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem a4_2_7 (hX : X = oTwoUpper X) (hXM : X ≤ M) (hXN : (X.subgroupOf M).Normal)
    {T R : Subgroup G} (hT : IsSylowTwoOf T M) (hR : R = pCoreOf 2 (X ⊔ T))
    (hNR : Subgroup.normalizer (R : Set G) ≤ M) :
    IsSylowTwoOf R (centralizerSection ⊤ X (pCoreOf 2 X)) ∧
    (∀ S, IsSylowTwoOf S (centralizerSection ⊤ X (pCoreOf 2 X)) → IsMaxSignalizer ⊤ X S) ∧
    IsMaxSignalizer M X R ∧
    (∀ S, IsMaxSignalizer M X S ↔ IsSylowTwoOf S (centralizerSection M X (pCoreOf 2 X))) ∧
    R = pCoreOf 2 (Subgroup.normalizer (R : Set G)) ∧
    IsSylowTwoOf R (conjClosure R M) := by
  have hMN : M ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp hXN
  have hsub : IsSubnormal X M := subnormal_of_normal hXM hXN
  have hsubN : IsSubnormal X (Subgroup.normalizer (X : Set G)) :=
    subnormal_of_normal Subgroup.le_normalizer (Subgroup.normal_subgroupOf_of_le_normalizer le_rfl)
  have hT' : IsSylowTwoOf T (M ⊓ Subgroup.normalizer (X : Set G)) := by
    rwa [inf_eq_left.mpr hMN]
  have hRmax : IsMaxSignalizer M X R := hR ▸ a4_2_5 hX hsub hT'
  have h4 := a4_2_4 hX hsub
  have hRsylM : IsSylowTwoOf R (centralizerSection M X (pCoreOf 2 X)) := (h4 R).mp hRmax
  have hodd : Odd ((M ⊓ Subgroup.normalizer (R : Set G)).relIndex (Subgroup.normalizer (R : Set G))) := by
    rw [inf_eq_right.mpr hNR, Subgroup.relIndex_self]
    exact odd_one
  have hRtop : IsMaxSignalizer ⊤ X R := a4_2_6_2 hRmax hNR
  have hRmaxN : IsMaxSignalizer (Subgroup.normalizer (X : Set G)) X R := by
    refine ⟨⟨hRmax.1.1.trans hMN, hRmax.1.2.1, hRmax.1.2.2⟩, fun S hS hRS => ?_⟩
    exact hRtop.2 ⟨le_top, hS.2.1, hS.2.2⟩ hRS
  have hRsylG : IsSylowTwoOf R (centralizerSection ⊤ X (pCoreOf 2 X)) := by
    have := (a4_2_4 hX hsubN R).mp hRmaxN
    rwa [centralizerSection_normalizer_eq] at this
  refine ⟨hRsylG, ?_, hRmax, h4, (a4_2_6_1 hRmax hodd).trans (by rw [hR]), ?_⟩
  ·
    intro S hS
    obtain ⟨h, hh, hconj⟩ := exists_conj_of_isSylowTwoOf hRsylG hS
    have hhX : h ∈ Subgroup.normalizer (X : Set G) :=
      centralizerSection_le_normalizer_left ⊤ X _ hh
    have hS' : IsMaxSignalizer (Subgroup.normalizer (X : Set G)) X S := by
      have : IsSylowTwoOf S (centralizerSection (Subgroup.normalizer (X : Set G)) X (pCoreOf 2 X)) := by
        rwa [centralizerSection_normalizer_eq]
      exact (a4_2_4 hX hsubN S).mpr this
    refine a4_2_6_2 hS' ?_
    intro g hg
    have hgR : h⁻¹ * g * h ∈ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have h1 := Subgroup.mem_normalizer_iff.mp hg (h * z * h⁻¹)
      have e1 : h⁻¹ * (h * z * h⁻¹) * h = z := by group
      have e2 : h⁻¹ * (g * (h * z * h⁻¹) * g⁻¹) * h = h⁻¹ * g * h * z * (h⁻¹ * g * h)⁻¹ := by group
      have h2 := hconj (h * z * h⁻¹)
      have h3 := hconj (g * (h * z * h⁻¹) * g⁻¹)
      rw [e1] at h2
      rw [e2] at h3
      rw [← h2, ← h3]
      exact h1
    have : h⁻¹ * g * h ∈ Subgroup.normalizer (X : Set G) := hMN (hNR hgR)
    have e3 : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
    rw [e3]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhX this) (Subgroup.inv_mem _ hhX)
  ·
    have hle : conjClosure R M ≤ centralizerSection M X (pCoreOf 2 X) := by
      refine conjClosure_le fun m hm r hr => ?_
      have hmX := hMN hm
      exact conj_mem_centralizerSection (Subgroup.le_normalizer hm) hmX
        (normalizer_le_normalizer_pCoreOf 2 X hmX) (hRsylM.1 hr)
    exact isSylowTwoOf_mono hRsylM (le_conjClosure R M) hle

theorem pCoreOf_le_of_isMaxSignalizer {Y B : Subgroup G} (hYM : Y ≤ M)
    (hB : IsMaxSignalizer M Y B) : pCoreOf 2 Y ≤ B := by
  have hP : IsSignalizer M Y (pCoreOf 2 Y ⊔ B) :=
    ⟨sup_le ((pCoreOf_le 2 Y).trans hYM) hB.1.1,
      IsPGroup.to_sup_of_normal_right' (pCoreOf_isPGroup 2 Y) hB.1.2.1
        ((pCoreOf_le 2 Y).trans hB.1.2.2),
      fun y hy => Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨le_normalizer_pCoreOf 2 Y hy, hB.1.2.2 hy⟩⟩
  have := hB.eq_of_le hP le_sup_right
  rw [← this]
  exact le_sup_left

theorem a4_3_1 (hX : X = oTwoUpper X) (hXM : IsSubnormal X M) {Y : Subgroup G} (hYM : Y ≤ M)
    (hY : (Y : Set G) = ((X ⊓ Y : Subgroup G) : Set G) * (pCoreOf 2 Y : Set G))
    (hX' : (X : Set G) = ((Y ⊓ X : Subgroup G) : Set G) * (pCoreOf 2 X : Set G)) :
    (∀ B : Subgroup G, IsSignalizer M Y B → B ≤ centralizerSection M X (pCoreOf 2 X)) ∧
      Y ≤ M ⊓ Subgroup.normalizer (X : Set G) := by
  have hO2 : pCoreOf 2 X ≤ pCoreOf 2 M := pCoreOf_le_of_subnormal 2 hXM
  have key : ∀ B : Subgroup G, IsSignalizer M Y B →
      B ≤ centralizerSection M X (pCoreOf 2 X) := by
    intro B hB
    have hBP : B ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      hB.1.trans (le_normalizer_pCoreOf 2 M)
    have hC2 : IsPGroup 2 (pCoreOf 2 X ⊔ B : Subgroup G) := by
      have h1 : IsPGroup 2 (pCoreOf 2 M ⊔ B : Subgroup G) :=
        IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 M) hB.2.1 hBP
      exact h1.to_le (sup_le_sup_right hO2 B)
    have hCM : pCoreOf 2 X ⊔ B ≤ M :=
      sup_le ((pCoreOf_le 2 X).trans (subnormal_le hXM)) hB.1
    have hCX : X ≤ Subgroup.normalizer ((pCoreOf 2 X ⊔ B : Subgroup G) : Set G) := by
      intro x hx
      have hx' : x ∈ (↑(Y ⊓ X) : Set G) * (pCoreOf 2 X : Set G) := hX' ▸ hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx'
      refine Subgroup.mul_mem _ ?_ (Subgroup.le_normalizer (Subgroup.mem_sup_left hz))
      exact Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨le_normalizer_pCoreOf 2 X hy.2, hB.2.2 hy.1⟩
    exact le_sup_right.trans (signalizer_le_centralizerSection hX hXM ⟨hCM, hC2, hCX⟩)
  refine ⟨key, ?_⟩
  have hO2Y : IsSignalizer M Y (pCoreOf 2 Y) :=
    ⟨(pCoreOf_le 2 Y).trans hYM, pCoreOf_isPGroup 2 Y, le_normalizer_pCoreOf 2 Y⟩
  have hnorm : pCoreOf 2 Y ≤ Subgroup.normalizer (X : Set G) :=
    fun w hw => centralizerSection_le_normalizer_left M X _ (key _ hO2Y hw)
  refine le_inf hYM fun y hy => ?_
  have hy' : y ∈ (↑(X ⊓ Y) : Set G) * (pCoreOf 2 Y : Set G) := hY ▸ hy
  obtain ⟨a, ha, w, hw, rfl⟩ := hy'
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer ha.1) (hnorm hw)

theorem a4_3_2 (hX : X = oTwoUpper X) (hXM : IsSubnormal X M) {Y : Subgroup G} (hYM : Y ≤ M)
    (hY : (Y : Set G) = ((X ⊓ Y : Subgroup G) : Set G) * (pCoreOf 2 Y : Set G))
    (hX' : (X : Set G) = ((Y ⊓ X : Subgroup G) : Set G) * (pCoreOf 2 X : Set G))
    {B : Subgroup G} (hB : IsMaxSignalizer M Y B) : IsMaxSignalizer M X B := by
  obtain ⟨h1, h1Y⟩ := a4_3_1 hX hXM hYM hY hX'
  have hBM₀ := h1 B hB.1
  obtain ⟨S, hS, hBS⟩ := exists_isSylowTwoOf_ge hBM₀ hB.1.2.1
  have hSM₀ : S ≤ centralizerSection M X (pCoreOf 2 X) := hS.1
  have hO2XB : pCoreOf 2 X ≤ B := by
    have hbnorm : B ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      hBM₀.trans (centralizerSection_le_normalizer_right M X _)
    have hYnorm : Y ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      fun y hy => normalizer_le_normalizer_pCoreOf 2 X (h1Y hy).2
    have hsig : IsSignalizer M Y (pCoreOf 2 X ⊔ B) :=
      ⟨sup_le ((pCoreOf_le 2 X).trans (subnormal_le hXM)) hB.1.1,
        IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 X) hB.1.2.1 hbnorm,
        fun y hy => Subgroup.inf_normalizer_le_normalizer_sup _ _
          ⟨hYnorm hy, hB.1.2.2 hy⟩⟩
    have := hB.eq_of_le hsig le_sup_right
    rw [← this]
    exact le_sup_left
  have hO2XS : pCoreOf 2 X ≤ S := hO2XB.trans hBS
  have hXS : X ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (((le_centralizerSection_iff (pCoreOf_le 2 X)).mp hSM₀).2).trans hO2XS
  have hO2Y : pCoreOf 2 Y ≤ S := (pCoreOf_le_of_isMaxSignalizer hYM hB).trans hBS
  have hSY : IsSignalizer M Y S := by
    refine ⟨hSM₀.trans (centralizerSection_le_left M X _), hS.2.1, fun y hy => ?_⟩
    have hy' : y ∈ (↑(X ⊓ Y) : Set G) * (pCoreOf 2 Y : Set G) := hY ▸ hy
    obtain ⟨a, ha, w, hw, rfl⟩ := hy'
    exact Subgroup.mul_mem _ (hXS ha.1) (Subgroup.le_normalizer (hO2Y hw))
  have hSB : S = B := hB.eq_of_le hSY hBS
  rw [← hSB]
  exact (a4_2_4 hX hXM S).mpr hS

end Finite

end CFSG.Quasithin
