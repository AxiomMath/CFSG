module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Quasithin.SteinbergCDOddResidualTools
public import CFSG.Quasithin.SteinbergCDSwappedFactorsCoreSupports
public import CFSG.RankThree.PGroups.SolvableTrivialComplementCore
import CFSG.Walter.ReeOrder.JT.Section7ZA

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.ABGLocalTools CFSG.SectionRank.Ccomm
open scoped commutatorElement Pointwise

variable {E : Type*} [Group E] {X : Subgroup E}

theorem inSubgroup_pCore_normal [X.Normal] (r : ℕ) : (inSubgroup (pCore r) X).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro g _
  exact mem_normalizer_inSubgroup_pCore r (by rw [normalizer_eq_top]; exact mem_top g)

theorem inSubgroup_pCore_le_pCore [X.Normal] (r : ℕ) : inSubgroup (pCore r) X ≤ pCore r E :=
  haveI := inSubgroup_pCore_normal (X := X) r
  le_sSup ⟨inferInstance, pCore_isPGroup.map X.subtype⟩

theorem inf_pCore_le_inSubgroup_pCore (r : ℕ) : X ⊓ pCore r E ≤ inSubgroup (pCore r) X := by
  have h : (pCore r E).subgroupOf X ≤ pCore r X :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  intro x hx
  exact ⟨⟨x, (Subgroup.mem_inf.mp hx).1⟩, h (Subgroup.mem_inf.mp hx).2, rfl⟩

theorem exists_pow_mem_pCore_of_isPGroup {p : ℕ} (hP : IsPGroup p (X ⧸ pCore 2 X)) (x : X) :
    ∃ m : ℕ, x ^ p ^ m ∈ pCore 2 X := by
  obtain ⟨m, hm⟩ := hP (x : X ⧸ pCore 2 X)
  exact ⟨m, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hm⟩

theorem le_inSubgroup_pCore_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p (X ⧸ pCore 2 X)) {T : Subgroup E} (hT : IsPGroup 2 T) :
    T ⊓ X ≤ inSubgroup (pCore 2) X := by
  intro y hy
  obtain ⟨hyT, hyX⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨k, hk⟩ := hT ⟨y, hyT⟩
  obtain ⟨m, hm⟩ := exists_pow_mem_pCore_of_isPGroup hP ⟨y, hyX⟩
  have hk' : (⟨y, hyX⟩ : X) ^ 2 ^ k ∈ pCore 2 X := by
    have h1 : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : (⟨y, hyX⟩ : X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using h1)
    rw [h2]
    exact one_mem _
  have hcop : Nat.Coprime (p ^ m) (2 ^ k) :=
    Nat.Coprime.pow m k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact ⟨_, CFSG.Walter.JT.mem_of_pow_mem_of_coprime hm hk' hcop, rfl⟩

theorem exists_pow_mem_pCore_of_mem_sup [X.Normal] {p : ℕ} (hP : IsPGroup p (X ⧸ pCore 2 X)) {d : E}
    (hd : d ∈ X ⊔ pCore 2 E) : ∃ m : ℕ, d ^ p ^ m ∈ pCore 2 E := by
  have hd' : d ∈ ((pCore 2 E ⊔ X : Subgroup E) : Set E) := by rw [sup_comm]; exact hd
  rw [normal_mul] at hd'
  obtain ⟨r, hr, x, hx, rfl⟩ := hd'
  obtain ⟨m, hm⟩ := exists_pow_mem_pCore_of_isPGroup hP ⟨x, hx⟩
  have hxm : x ^ p ^ m ∈ pCore 2 E :=
    inSubgroup_pCore_le_pCore (X := X) 2 ⟨_, hm, by simp⟩
  refine ⟨m, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff r).mpr hr, one_mul, ← QuotientGroup.mk_pow,
    (QuotientGroup.eq_one_iff _).mpr hxm]

theorem mem_sup_pCore_of_conj_eq [Finite E] [X.Normal] (T : Sylow 2 E)
    (hXT : X ⊔ (T : Subgroup E) = ⊤) {g : E}
    (hg : ∀ x : X, ((MulAut.conjNormal g x : X) : X ⧸ pCore 2 X) = (x : X ⧸ pCore 2 X)) :
    g ∈ X ⊔ pCore 2 E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (inSubgroup (pCore 2) X).Normal := inSubgroup_pCore_normal 2
  set κ : E →* MulAut (X ⧸ pCore 2 X) := (autQuotient (pCore 2 X)).comp MulAut.conjNormal
    with hκ
  have hκx : ∀ (y : E) (x : X), κ y (x : X ⧸ pCore 2 X) =
      ((MulAut.conjNormal y x : X) : X ⧸ pCore 2 X) := fun _ _ => rfl
  set K := κ.ker with hK
  have hmemK : ∀ y : E, y ∈ K ↔ ∀ x : X,
      ((MulAut.conjNormal y x : X) : X ⧸ pCore 2 X) = (x : X ⧸ pCore 2 X) := by
    intro y
    rw [MonoidHom.mem_ker]
    constructor
    · intro h x
      rw [← hκx, h]
      rfl
    · intro h
      ext z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
      rw [hκx, h x]
      rfl
  have hmemQ : ∀ x : X, x ∈ pCore 2 X ↔ (x : E) ∈ inSubgroup (pCore 2) X := fun x =>
    (Subgroup.mem_map_iff_mem X.subtype_injective).symm
  have hmemK' : ∀ y : E, y ∈ K → ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ inSubgroup (pCore 2) X := by
    intro y hy x hx
    have h := (hmemK y).mp hy ⟨x, hx⟩⁻¹
    rw [QuotientGroup.eq, hmemQ] at h
    have e : y * x * y⁻¹ * x⁻¹ = ((MulAut.conjNormal y (⟨x, hx⟩⁻¹ : X) : X) : E)⁻¹ *
        ((⟨x, hx⟩⁻¹ : X) : E) := by
      rw [MulAut.conjNormal_apply]
      simp only [Subgroup.coe_inv]
      group
    rw [e]
    simpa using h
  have hqR : inSubgroup (pCore 2) X ≤ pCore 2 E := inSubgroup_pCore_le_pCore 2
  have hXR : X ⊓ pCore 2 E ≤ inSubgroup (pCore 2) X := inf_pCore_le_inSubgroup_pCore 2
  have hRK : pCore 2 E ≤ K := by
    intro r hr
    rw [hmemK]
    intro x
    symm
    rw [QuotientGroup.eq, hmemQ]
    refine hXR (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact Subtype.mem _
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
      have h1 : (x : E)⁻¹ * r * (x : E) ∈ pCore 2 E := by
        simpa using (inferInstance : (pCore 2 E).Normal).conj_mem _ hr (x : E)⁻¹
      have e : (x : E)⁻¹ * (r * x * r⁻¹) = ((x : E)⁻¹ * r * x) * r⁻¹ := by group
      rw [e]
      exact mul_mem h1 (inv_mem hr)
  have hRT : pCore 2 E ≤ (T : Subgroup E) := IsPGroup.le_sylow_of_normal pCore_isPGroup T
  have hTsyl : IsSylowOf 2 (T : Subgroup E) ⊤ :=
    isSylowOf_iff.mpr ⟨le_top, T.isPGroup', by rw [relIndex_top_right]; exact T.not_dvd_index⟩
  have hS : ¬ 2 ∣ ((T : Subgroup E) ⊓ K).relIndex K :=
    (isSylowOf_iff.mp (hTsyl.inf_of_le_normalizer le_top (by rw [normalizer_eq_top]))).2.2
  obtain ⟨a, ha⟩ := exists_index_eq_two_pow_of_sup_eq_top T.isPGroup' hXT
  have hconj : ∀ y ∈ X ⊓ K, ∀ s ∈ (T : Subgroup E) ⊓ K, y * s * y⁻¹ ∈ (T : Subgroup E) ⊓ K := by
    intro y hy s hs
    obtain ⟨hyX, hyK⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hsT, hsK⟩ := Subgroup.mem_inf.mp hs
    refine Subgroup.mem_inf.mpr ⟨?_, (inferInstance : K.Normal).conj_mem s hsK y⟩
    have h1 := hmemK' s hsK y hyX
    have h2 : y * s * y⁻¹ * s⁻¹ ∈ (T : Subgroup E) := by
      have h3 := hRT (hqR (inv_mem h1))
      have e : (s * y * s⁻¹ * y⁻¹)⁻¹ = y * s * y⁻¹ * s⁻¹ := by group
      rwa [e] at h3
    have e : y * s * y⁻¹ = (y * s * y⁻¹ * s⁻¹) * s := by group
    rw [e]
    exact mul_mem h2 hsT
  have hXKn : X ⊓ K ≤ normalizer (((T : Subgroup E) ⊓ K : Subgroup E) : Set E) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro s
    refine ⟨hconj y hy s, fun h => ?_⟩
    have h1 := hconj y⁻¹ (inv_mem hy) _ h
    simpa [mul_assoc] using h1
  have hKn : K ≤ normalizer (((T : Subgroup E) ⊓ K : Subgroup E) : Set E) :=
    le_of_inf_le_of_le_of_index_eq_two_pow ha hS hXKn le_normalizer
  have hSR : (T : Subgroup E) ⊓ K ≤ pCore 2 E := by
    have hSn : (((T : Subgroup E) ⊓ K).subgroupOf K).Normal :=
      (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hKn
    have hSp : IsPGroup 2 (((T : Subgroup E) ⊓ K).subgroupOf K) :=
      (T.isPGroup'.to_inf_left (K := K)).comap_subtype
    have h1 : ((T : Subgroup E) ⊓ K).subgroupOf K ≤ pCore 2 K := le_sSup ⟨hSn, hSp⟩
    intro s hs
    exact inSubgroup_pCore_le_pCore (X := K) 2
      ⟨⟨s, (Subgroup.mem_inf.mp hs).2⟩, h1 hs, rfl⟩
  have hKXR : K ≤ X ⊔ pCore 2 E :=
    le_of_inf_le_of_le_of_index_eq_two_pow ha hS (inf_le_left.trans le_sup_left)
      (hSR.trans le_sup_right)
  exact hKXR ((hmemK g).mpr hg)

theorem mem_sup_pCore_of_conj_eq_frattini [Finite E] [X.Normal] (T : Sylow 2 E)
    (hXT : X ⊔ (T : Subgroup E) = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p (X ⧸ pCore 2 X)) {g : E}
    (hg : ∀ x : X, (((MulAut.conjNormal g x : X) : X ⧸ pCore 2 X) :
        (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)) =
      ((x : X ⧸ pCore 2 X) : (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X))) :
    g ∈ X ⊔ pCore 2 E := by
  have : Fact p.Prime := ⟨hp⟩
  set κ : E →* MulAut (X ⧸ pCore 2 X) := (autQuotient (pCore 2 X)).comp MulAut.conjNormal
    with hκ
  have hker : κ g ∈ (autQuotient (frattini (X ⧸ pCore 2 X))).ker := by
    rw [mem_ker_autQuotient]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have h := (hg x).symm
    rw [QuotientGroup.eq] at h
    exact h
  obtain ⟨m, hm⟩ := isPGroup_ker_autQuotient_frattini hP ⟨κ g, hker⟩
  have hm' : κ (g ^ p ^ m) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hm
  have h1 : g ^ p ^ m ∈ X ⊔ pCore 2 E := by
    refine mem_sup_pCore_of_conj_eq T hXT fun x => ?_
    have h := congrArg (fun σ : MulAut (X ⧸ pCore 2 X) => σ (x : X ⧸ pCore 2 X)) hm'
    exact h
  obtain ⟨k, hk⟩ := exists_two_pow_mem_of_sup_eq_top T.isPGroup' hXT g
  exact CFSG.Walter.JT.mem_of_pow_mem_of_coprime h1 (mem_sup_left hk)
    (Nat.Coprime.pow m k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))

theorem le_of_forall_two_pow_mem [Finite E] [X.Normal] (T : Sylow 2 E)
    (hXT : X ⊔ (T : Subgroup E) = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p (X ⧸ pCore 2 X)) {N : Subgroup E} (hRN : pCore 2 E ≤ N)
    (hNX : (N.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) ≤ frattini (X ⧸ pCore 2 X))
    {D : Subgroup E} [D.Normal] (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ N) : D ≤ N := by
  have hcop : ∀ m k : ℕ, Nat.Coprime (p ^ m) (2 ^ k) := fun m k =>
    Nat.Coprime.pow m k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hDX : ∀ y : X, (y : E) ∈ D → (y : X ⧸ pCore 2 X) ∈ frattini (X ⧸ pCore 2 X) := by
    intro y hy
    obtain ⟨k, hk⟩ := hD y hy
    obtain ⟨m, hm⟩ := hP (y : X ⧸ pCore 2 X)
    have h1 : (y : X ⧸ pCore 2 X) ^ 2 ^ k ∈ frattini (X ⧸ pCore 2 X) := by
      rw [← QuotientGroup.mk_pow]
      exact hNX ⟨y ^ 2 ^ k, by simpa [mem_subgroupOf] using hk, rfl⟩
    have h2 : (y : X ⧸ pCore 2 X) ^ p ^ m ∈ frattini (X ⧸ pCore 2 X) := by
      rw [hm]
      exact one_mem _
    exact CFSG.Walter.JT.mem_of_pow_mem_of_coprime h2 h1 (hcop m k)
  intro d hdD
  have hdX : d ∈ X ⊔ pCore 2 E := by
    refine mem_sup_pCore_of_conj_eq_frattini T hXT hp hp2 hP fun x => ?_
    symm
    rw [QuotientGroup.eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    apply hDX
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    have h1 : (x : E)⁻¹ * d * (x : E) ∈ D := by
      simpa using (inferInstance : D.Normal).conj_mem d hdD (x : E)⁻¹
    have e : (x : E)⁻¹ * (d * x * d⁻¹) = ((x : E)⁻¹ * d * x) * d⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem hdD)
  obtain ⟨m, hm⟩ := exists_pow_mem_pCore_of_mem_sup hP hdX
  obtain ⟨k, hk⟩ := hD d hdD
  exact CFSG.Walter.JT.mem_of_pow_mem_of_coprime (hRN hm) hk (hcop m k)

theorem coprime_residual_module_decomposition [Finite E] [X.Normal] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hP : IsPGroup p (X ⧸ pCore 2 X)) {U : Subgroup E} [U.Normal]
    (hUab : ∀ x y : U, x * y = y * x) (hU2 : IsPGroup 2 U)
    (hqU : inSubgroup (pCore 2) X ≤ centralizer (U : Set E)) :
    (U ⊓ centralizer (X : Set E)) ⊔ ⁅U, X⁆ = U ∧
      Disjoint (U ⊓ centralizer (X : Set E)) ⁅U, X⁆ ∧ ⁅⁅U, X⁆, X⁆ = ⁅U, X⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (inSubgroup (pCore 2) X).Normal := inSubgroup_pCore_normal 2
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p X))
  set Xp := (S : Subgroup X).map X.subtype with hXp
  have hXpX : Xp ≤ X := map_subtype_le _
  have hXpp : IsPGroup p Xp := S.isPGroup'.map X.subtype
  have hSθ : (S : Subgroup X).map (QuotientGroup.mk' (pCore 2 X)) = ⊤ := by
    have h := (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))).is_maximal'
      (IsPGroup.to_subgroup hP ⊤) le_top
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))]
    exact h.symm
  have hXqXp : inSubgroup (pCore 2) X ⊔ Xp = X := by
    have h1 : (S : Subgroup X) ⊔ pCore 2 X = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 X))) hSθ
      rwa [comap_map_eq, QuotientGroup.ker_mk', comap_top] at this
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at h2
    rw [sup_comm]
    exact h2
  have hUq : U ≤ centralizer (inSubgroup (pCore 2) X : Set E) := le_centralizer_iff.mp hqU
  have hCU : U ⊓ centralizer (X : Set E) = U ⊓ centralizer (Xp : Set E) := by
    refine le_antisymm (inf_le_inf_left _ (centralizer_le hXpX)) ?_
    intro u hu
    obtain ⟨huU, huXp⟩ := Subgroup.mem_inf.mp hu
    refine Subgroup.mem_inf.mpr ⟨huU, ?_⟩
    rw [← zpowers_le, le_centralizer_iff, ← hXqXp]
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff, zpowers_le]
      exact hUq huU
    · rw [← le_centralizer_iff, zpowers_le]
      exact huXp
  have hVeq : ⁅U, X⁆ = ⁅U, Xp⁆ := by
    refine le_antisymm ?_ (commutator_mono le_rfl hXpX)
    rw [commutator_le]
    intro u hu x hx
    have hx' : x ∈ ((inSubgroup (pCore 2) X ⊔ Xp : Subgroup E) : Set E) := by
      rw [hXqXp]
      exact hx
    rw [normal_mul] at hx'
    obtain ⟨c, hc, y, hy, rfl⟩ := hx'
    have hcu : u * c = c * u := mem_centralizer_iff.mp (hqU hc) u hu
    have huy : ⁅u, y⁆ ∈ U := by
      rw [commutatorElement_def]
      have h1 : y * u⁻¹ * y⁻¹ ∈ U := (inferInstance : U.Normal).conj_mem _ (inv_mem hu) y
      have e : u * y * u⁻¹ * y⁻¹ = u * (y * u⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hu h1
    have hcuy : ⁅u, y⁆ * c = c * ⁅u, y⁆ := mem_centralizer_iff.mp (hqU hc) _ huy
    have e : ⁅u, c * y⁆ = ⁅u, y⁆ := by
      have h2 : c * ⁅u, y⁆ * c⁻¹ = ⁅u, y⁆ := by rw [← hcuy, mul_inv_cancel_right]
      rw [← h2]
      simp only [commutatorElement_def]
      calc u * (c * y) * u⁻¹ * (c * y)⁻¹ = (u * c) * y * u⁻¹ * y⁻¹ * c⁻¹ := by group
        _ = (c * u) * y * u⁻¹ * y⁻¹ * c⁻¹ := by rw [hcu]
        _ = c * (u * y * u⁻¹ * y⁻¹) * c⁻¹ := by group
    rw [e]
    exact commutator_mem_commutator hu hy
  have hcop : Nat.Coprime (Nat.card Xp) (Nat.card U) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hXpp
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hU2
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hXpU : Xp ≤ normalizer (U : Set E) := by
    rw [normalizer_eq_top]
    exact le_top
  obtain ⟨h1, h2⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp U Xp hXpU hUab hcop
  have h3 := CFSG.QuasithinUnique.Setup.Layer.commutator_commutator_eq U Xp hXpU hUab hcop
  refine ⟨by rw [hCU, hVeq]; exact h1, by rw [hCU, hVeq]; exact h2, ?_⟩
  refine le_antisymm (commutator_le_left _ _) ?_
  calc ⁅U, X⁆ = ⁅⁅U, Xp⁆, Xp⁆ := by rw [h3, hVeq]
    _ ≤ ⁅⁅U, X⁆, X⁆ := commutator_mono (le_of_eq hVeq.symm) hXpX

theorem map_subgroupOf_le_frattini_of_irreducible [Finite E] [X.Normal] {T : Subgroup E}
    (hirr : ∀ M : Subgroup ((X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)),
      (∀ t ∈ T, ∀ x : X, ((x : X ⧸ pCore 2 X) : (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)) ∈ M →
        (((MulAut.conjNormal t x : X) : X ⧸ pCore 2 X) :
          (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)) ∈ M) → M = ⊥ ∨ M = ⊤)
    {N : Subgroup E} [N.Normal] (hqN : inSubgroup (pCore 2) X ≤ N) (hXN : ¬ X ≤ N) :
    (N.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) ≤ frattini (X ⧸ pCore 2 X) := by
  set θ := QuotientGroup.mk' (pCore 2 X) with hθ
  set Φ := frattini (X ⧸ pCore 2 X) with hΦ
  set M := ((N.subgroupOf X).map θ).map (QuotientGroup.mk' Φ) with hM
  set β : E →* MulAut ((X ⧸ pCore 2 X) ⧸ Φ) :=
    (autQuotient Φ).comp ((autQuotient (pCore 2 X)).comp MulAut.conjNormal) with hβ
  have hinv : ∀ t ∈ T, ∀ x : X, ((x : X ⧸ pCore 2 X) : (X ⧸ pCore 2 X) ⧸ Φ) ∈ M →
      (((MulAut.conjNormal t x : X) : X ⧸ pCore 2 X) : (X ⧸ pCore 2 X) ⧸ Φ) ∈ M := by
    intro t _ x hx
    obtain ⟨y, ⟨b, hb, rfl⟩, hby⟩ := hx
    refine ⟨θ (MulAut.conjNormal t b), ⟨MulAut.conjNormal t b, ?_, rfl⟩, ?_⟩
    · change ((MulAut.conjNormal t b : X) : E) ∈ N
      rw [MulAut.conjNormal_apply]
      exact (inferInstance : N.Normal).conj_mem (b : E) hb t
    · have h := congrArg (β t) hby
      exact h
  rcases hirr M hinv with hMb | hMt
  · rw [hM, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hMb
    exact hMb
  · exfalso
    apply hXN
    have h1 : (N.subgroupOf X).map θ ⊔ Φ = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' Φ)) hMt
      rwa [hM, comap_map_eq, QuotientGroup.ker_mk', comap_top] at this
    have h2 : (N.subgroupOf X).map θ = ⊤ := frattini_nongenerating h1
    have h3 : N.subgroupOf X ⊔ pCore 2 X = ⊤ := by
      have := congrArg (Subgroup.comap θ) h2
      rwa [comap_map_eq, hθ, QuotientGroup.ker_mk', comap_top] at this
    have h4 : pCore 2 X ≤ N.subgroupOf X := fun x hx => hqN ⟨x, hx, rfl⟩
    rw [sup_eq_left.mpr h4] at h3
    intro x hx
    have : (⟨x, hx⟩ : X) ∈ N.subgroupOf X := by
      rw [h3]
      exact mem_top _
    exact this

theorem irreducible_odd_residual_full_central_core_module_exact_kernel [Finite E] [X.Normal]
    (T : Sylow 2 E) (hXT : X ⊔ (T : Subgroup E) = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p (X ⧸ pCore 2 X))
    (hirr : ∀ M : Subgroup ((X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)),
      (∀ t ∈ (T : Subgroup E), ∀ x : X,
        ((x : X ⧸ pCore 2 X) : (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)) ∈ M →
          (((MulAut.conjNormal t x : X) : X ⧸ pCore 2 X) :
            (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)) ∈ M) → M = ⊥ ∨ M = ⊤)
    {q R U V B C FX : Subgroup E} (hq : q = inSubgroup (pCore 2) X) (hR : R = pCore 2 E)
    (hU : U = primeReducedAggregate E 2) (hVdef : V = ⁅U, X⁆)
    (hB : B = X ⊓ centralizer (V : Set E)) (hC : C = centralizer (V : Set E))
    (hFX : FX = ((frattini (X ⧸ pCore 2 X)).comap (QuotientGroup.mk' (pCore 2 X))).map X.subtype)
    (hV : V ≠ ⊥) :
    U = BlueprintB2.centerTorsion 2 R ∧
      ((U ⊓ centralizer (X : Set E)) ⊔ V = U ∧ (U ⊓ centralizer (X : Set E)) ⊓ V = ⊥ ∧
        IsElementaryAbelian 2 ↥(U ⊓ centralizer (X : Set E)) ∧ IsElementaryAbelian 2 V) ∧
      IsPrimeReduced 2 V ∧ ⁅V, X⁆ = V ∧ q ≤ B ∧ B ≤ FX ∧
      centralizer (U : Set E) = C ∧ C = R ⊔ B ∧ (C : Set E) = (R : Set E) * (B : Set E) ∧
      (T : Subgroup E) ⊓ C = R ∧ X ⊓ R = q ∧ (∃ _ : C.Normal, pCore 2 (E ⧸ C) = ⊥) ∧
      (∃ ρ : E →* MulAut V, ∀ (g : E) (v : V), ((ρ g v : V) : E) = g * v * g⁻¹) ∧
      (B.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) ≤ frattini (X ⧸ pCore 2 X) ∧
      ∃ _ : (B.subgroupOf X).Normal,
        (∀ ρ : E →* MulAut V, (∀ (g : E) (v : V), ((ρ g v : V) : E) = g * v * g⁻¹) →
          Group.IsSolvable ρ.range ∧ ((X.map ρ).subgroupOf ρ.range).Normal ∧
            IsSylowOf p (X.map ρ) ρ.range ∧
            generalizedFitting ρ.range = (X.map ρ).subgroupOf ρ.range ∧
            ∃ e : X ⧸ B.subgroupOf X ≃* X.map ρ, ∀ x : X, (e x : MulAut V) = ρ x) ∧
        (∃ e : X ⧸ B.subgroupOf X ≃*
            (X ⧸ pCore 2 X) ⧸ (B.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)),
          ∀ x : X, e x = ((x : X ⧸ pCore 2 X) :
            (X ⧸ pCore 2 X) ⧸ (B.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))) ∧
        ∃ μ : (X ⧸ B.subgroupOf X) ⧸ frattini (X ⧸ B.subgroupOf X) ≃*
            (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X),
          (∀ x : X, μ ((x : X ⧸ B.subgroupOf X) : (X ⧸ B.subgroupOf X) ⧸
              frattini (X ⧸ B.subgroupOf X)) =
            ((x : X ⧸ pCore 2 X) : (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X))) ∧
          ∃ (α : E →* MulAut ((X ⧸ B.subgroupOf X) ⧸ frattini (X ⧸ B.subgroupOf X)))
            (β : E →* MulAut ((X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X))),
            (∀ (g : E) (x : X), α g ((x : X ⧸ B.subgroupOf X) :
                (X ⧸ B.subgroupOf X) ⧸ frattini (X ⧸ B.subgroupOf X)) =
              (((MulAut.conjNormal g x : X) : X ⧸ B.subgroupOf X) :
                (X ⧸ B.subgroupOf X) ⧸ frattini (X ⧸ B.subgroupOf X))) ∧
            (∀ (g : E) (x : X), β g ((x : X ⧸ pCore 2 X) :
                (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)) =
              (((MulAut.conjNormal g x : X) : X ⧸ pCore 2 X) :
                (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X))) ∧
            ∀ (g : E) (w : (X ⧸ B.subgroupOf X) ⧸ frattini (X ⧸ B.subgroupOf X)),
              μ (α g w) = β g (μ w) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : ∀ m k : ℕ, Nat.Coprime (p ^ m) (2 ^ k) := fun m k =>
    Nat.Coprime.pow m k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hRn : R.Normal := hR ▸ pCore_normal
  have hqn : q.Normal := hq ▸ inSubgroup_pCore_normal 2
  have hqR : q ≤ R := by rw [hq, hR]; exact inSubgroup_pCore_le_pCore 2
  have hqX : q ≤ X := by rw [hq]; exact map_subtype_le _
  have hXRq : X ⊓ R = q := by
    refine le_antisymm ?_ (le_inf hqX hqR)
    rw [hq, hR]
    exact inf_pCore_le_inSubgroup_pCore 2
  have hRT : R ≤ (T : Subgroup E) := hR ▸ IsPGroup.le_sylow_of_normal pCore_isPGroup T
  obtain ⟨hUn, hUel, hUZ⟩ := primeReducedAggregate_normal_elementaryAbelian (E := E) 2
  have hUred := isPrimeReduced_primeReducedAggregate (E := E) 2
  rw [← hU] at hUn hUel hUZ hUred
  rw [← hR] at hUZ
  have hRU : R ≤ centralizer (U : Set E) := hR ▸ pCore_le_centralizer_of_isPrimeReduced hUred
  have hUab : ∀ x y : U, x * y = y * x := fun x y =>
    Subtype.ext ((BlueprintB2.isElementaryAbelian_iff.mp hUel).1 x x.2 y y.2)
  have hU2 : IsPGroup 2 U := IsElementaryAbelian.isPGroup 2 U
  have hqU : q ≤ centralizer (U : Set E) := hqR.trans hRU
  obtain ⟨hdec, hdisj, hVX⟩ :=
    coprime_residual_module_decomposition hp hp2 hP hUab hU2 (hq ▸ hqU)
  rw [← hVdef] at hdec hdisj hVX
  have hVn : V.Normal := hVdef ▸ inferInstance
  have hVU : V ≤ U := hVdef ▸ commutator_le_left U X
  have hVel : IsElementaryAbelian 2 V := BlueprintB2.isElementaryAbelian_of_le hVU hUel
  have hCn : C.Normal := hC ▸ inferInstance
  have hBXC : B = X ⊓ C := by rw [hB, hC]
  have hBn : B.Normal := hBXC ▸ inferInstance
  have hRC : R ≤ C := hC ▸ hRU.trans (centralizer_le hVU)
  have hqB : q ≤ B := hBXC ▸ le_inf hqX (hqR.trans hRC)
  have hXC : ¬ X ≤ C := by
    intro h
    apply hV
    rw [← hVX]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp (hC ▸ h))
  have hCΦ : (C.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) ≤
      frattini (X ⧸ pCore 2 X) :=
    map_subgroupOf_le_frattini_of_irreducible hirr (hq ▸ hqR.trans hRC) hXC
  have hBsub : B.subgroupOf X = C.subgroupOf X := by rw [hBXC, inf_subgroupOf_left]
  have hBΦ : (B.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) ≤
      frattini (X ⧸ pCore 2 X) := hBsub ▸ hCΦ
  have hBFX : B ≤ FX := by
    intro b hb
    have hbX : b ∈ X := (Subgroup.mem_inf.mp (hBXC ▸ hb : b ∈ X ⊓ C)).1
    rw [hFX]
    exact ⟨⟨b, hbX⟩, hBΦ ⟨⟨b, hbX⟩, hb, rfl⟩, rfl⟩
  have hCXR : C ≤ X ⊔ R := by
    intro c hc
    rw [hR]
    refine mem_sup_pCore_of_conj_eq_frattini T hXT hp hp2 hP fun x => ?_
    symm
    rw [QuotientGroup.eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    apply hCΦ
    refine ⟨x⁻¹ * MulAut.conjNormal c x, ?_, rfl⟩
    change ((x⁻¹ * MulAut.conjNormal c x : X) : E) ∈ C
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    have h1 : (x : E)⁻¹ * c * x ∈ C := by simpa using hCn.conj_mem c hc (x : E)⁻¹
    have e : (x : E)⁻¹ * (c * x * c⁻¹) = ((x : E)⁻¹ * c * x) * c⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem hc)
  have hCRB : C = R ⊔ B := by
    refine le_antisymm (fun c hc => ?_) (sup_le hRC (hBXC ▸ inf_le_right))
    have hc' : c ∈ ((R ⊔ X : Subgroup E) : Set E) := by
      rw [sup_comm]
      exact hCXR hc
    rw [normal_mul] at hc'
    obtain ⟨r, hr, x, hx, rfl⟩ := hc'
    have hxC : x ∈ C := by
      have e : x = r⁻¹ * (r * x) := by group
      rw [e]
      exact mul_mem (inv_mem (hRC hr)) hc
    exact mul_mem_sup hr (hBXC ▸ Subgroup.mem_inf.mpr ⟨hx, hxC⟩)
  have hCset : (C : Set E) = (R : Set E) * (B : Set E) := by rw [hCRB, normal_mul]
  have hCU : centralizer (U : Set E) = C := by
    refine le_antisymm (hC ▸ centralizer_le hVU) ?_
    rw [hCRB]
    refine sup_le hRU fun b hb => ?_
    obtain ⟨hbX, hbC⟩ := Subgroup.mem_inf.mp (hBXC ▸ hb : b ∈ X ⊓ C)
    rw [← zpowers_le, le_centralizer_iff, ← hdec]
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff, zpowers_le, mem_centralizer_iff]
      intro u hu
      exact (mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 b hbX).symm
    · rw [← le_centralizer_iff, zpowers_le]
      exact hC ▸ hbC
  have hTX : (T : Subgroup E) ⊓ X ≤ q :=
    hq ▸ le_inSubgroup_pCore_of_isPGroup hp hp2 hP T.isPGroup'
  have hTC : (T : Subgroup E) ⊓ C = R := by
    refine le_antisymm (fun t ht => ?_) (le_inf hRT hRC)
    obtain ⟨htT, htC⟩ := Subgroup.mem_inf.mp ht
    have ht' : t ∈ ((R ⊔ B : Subgroup E) : Set E) := by
      rw [← hCRB]
      exact htC
    rw [normal_mul] at ht'
    obtain ⟨r, hr, b, hb, rfl⟩ := ht'
    have hbT : b ∈ (T : Subgroup E) := by
      have e : b = r⁻¹ * (r * b) := by group
      rw [e]
      exact mul_mem (inv_mem (hRT hr)) htT
    have hbX : b ∈ X := (Subgroup.mem_inf.mp (hBXC ▸ hb : b ∈ X ⊓ C)).1
    exact mul_mem hr (hqR (hTX (Subgroup.mem_inf.mpr ⟨hbT, hbX⟩)))
  have hRC' : pCore 2 E ≤ C := hR ▸ hRC
  have hred : ∀ D : Subgroup E, D.Normal → (∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ C) → D ≤ C :=
    fun D hD hDk => le_of_forall_two_pow_mem (D := D) T hXT hp hp2 hP hRC' hCΦ hDk
  have hO2 : pCore 2 (E ⧸ C) = ⊥ := by
    subst hC
    exact (BlueprintB2.pCore_quotient_centralizer_eq_bot_iff 2).mpr hred
  have hVred : IsPrimeReduced 2 V := (isPrimeReduced_iff_forall 2).mpr ⟨hVn, hVel, hC ▸ hred⟩
  have hUeq : U = BlueprintB2.centerTorsion 2 R := by
    refine le_antisymm hUZ ?_
    set Z := BlueprintB2.centerTorsion 2 R with hZ
    have hZn : Z.Normal := by
      refine ⟨fun z hz g => ?_⟩
      obtain ⟨hzR, hzc, hz2⟩ := BlueprintB2.mem_centerTorsion_iff.mp hz
      refine BlueprintB2.mem_centerTorsion_iff.mpr ⟨hRn.conj_mem z hzR g, fun k hk => ?_, ?_⟩
      · have hk' : g⁻¹ * k * g ∈ R := by simpa using hRn.conj_mem k hk g⁻¹
        have h1 := hzc _ hk'
        calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
          _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
          _ = g * z * g⁻¹ * k := by group
      · rw [conj_pow, hz2, mul_one, mul_inv_cancel]
    have hZel : IsElementaryAbelian 2 Z := by
      refine BlueprintB2.isElementaryAbelian_iff.mpr ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
      · exact ((BlueprintB2.mem_centerTorsion_iff.mp ha).2.1 b
          (BlueprintB2.mem_centerTorsion_iff.mp hb).1).symm
      · exact (BlueprintB2.mem_centerTorsion_iff.mp ha).2.2
    have hZred : IsPrimeReduced 2 Z := by
      refine (isPrimeReduced_iff_forall 2).mpr ⟨hZn, hZel, fun D hD hDk => ?_⟩
      have hRN : pCore 2 E ≤ centralizer (Z : Set E) := by
        rw [← hR]
        intro r hr
        rw [mem_centralizer_iff]
        intro z hz
        exact ((BlueprintB2.mem_centerTorsion_iff.mp hz).2.1 r hr).symm
      have hNC : centralizer (Z : Set E) ≤ C := (centralizer_le hUZ).trans hCU.le
      have hNX : ((centralizer (Z : Set E)).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) ≤
          frattini (X ⧸ pCore 2 X) :=
        (map_mono (show (centralizer (Z : Set E)).subgroupOf X ≤ C.subgroupOf X from
          fun x hx => hNC hx)).trans hCΦ
      exact le_of_forall_two_pow_mem (D := D) T hXT hp hp2 hP hRN hNX hDk
    exact hU ▸ le_primeReducedAggregate hZred
  have hρex : ∃ ρ : E →* MulAut V, ∀ (g : E) (v : V), ((ρ g v : V) : E) = g * v * g⁻¹ :=
    ⟨MulAut.conjNormal, fun g v => MulAut.conjNormal_apply g v⟩
  have hqB' : pCore 2 X ≤ B.subgroupOf X := fun x hx => hqB (hq ▸ ⟨x, hx, rfl⟩)
  refine ⟨hUeq, ⟨hdec, disjoint_iff.mp hdisj,
    BlueprintB2.isElementaryAbelian_of_le inf_le_left hUel, hVel⟩, hVred, hVX, hqB, hBFX, hCU,
    hCRB, hCset, hTC, hXRq, ⟨hCn, hO2⟩, hρex, hBΦ, inferInstance, ?_, ?_, ?_⟩
  ·
    intro ρ hρ
    have hρker : ρ.ker = C := by
      ext g
      rw [MonoidHom.mem_ker, hC, mem_centralizer_iff]
      constructor
      · intro h v hv
        have h1 := hρ g ⟨v, hv⟩
        rw [h, MulAut.one_apply] at h1
        calc v * g = (g * v * g⁻¹) * g := by rw [← h1]
          _ = g * v := by group
      · intro h
        refine MulEquiv.ext fun v => Subtype.ext ?_
        rw [hρ, MulAut.one_apply]
        calc g * v * g⁻¹ = v * g * g⁻¹ := by rw [h v v.2]
          _ = v := by group
    have hPVΓ : X.map ρ ≤ ρ.range := map_le_range ρ X
    have hmapR : X.map ρ.rangeRestrict = (X.map ρ).subgroupOf ρ.range := by
      ext γ
      rw [mem_subgroupOf]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, hxγ⟩
        exact ⟨x, hx, Subtype.ext hxγ⟩
    have hPVn : ((X.map ρ).subgroupOf ρ.range).Normal :=
      hmapR ▸ (inferInstance : X.Normal).map ρ.rangeRestrict ρ.rangeRestrict_surjective
    have hPVp : IsPGroup p (X.map ρ) := by
      rintro ⟨_, x, hx, rfl⟩
      obtain ⟨m, hm⟩ := exists_pow_mem_pCore_of_isPGroup hP ⟨x, hx⟩
      have hxq : x ^ p ^ m ∈ q := by
        rw [hq]
        exact ⟨_, hm, by simp⟩
      have hxm : x ^ p ^ m ∈ C := (Subgroup.mem_inf.mp (hBXC ▸ hqB hxq : x ^ p ^ m ∈ X ⊓ C)).2
      refine ⟨m, Subtype.ext ?_⟩
      rw [← hρker, MonoidHom.mem_ker] at hxm
      simpa [map_pow] using hxm
    have hPVp' : IsPGroup p ((X.map ρ).subgroupOf ρ.range) := hPVp.comap_subtype
    have hΓ2 : ∀ γ : ρ.range, ∃ k : ℕ, γ ^ 2 ^ k ∈ (X.map ρ).subgroupOf ρ.range := by
      rintro ⟨_, g, rfl⟩
      obtain ⟨k, hk⟩ := exists_two_pow_mem_of_sup_eq_top T.isPGroup' hXT g
      refine ⟨k, ?_⟩
      rw [mem_subgroupOf]
      exact ⟨g ^ 2 ^ k, hk, by simp [map_pow]⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, ((X.map ρ).subgroupOf ρ.range).index = 2 ^ j := by
      obtain ⟨a, ha⟩ := exists_index_eq_two_pow_of_sup_eq_top T.isPGroup' hXT
      have h1 := index_map_dvd X ρ.rangeRestrict_surjective
      rw [hmapR, ha] at h1
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      exact ⟨j, hj⟩
    have hsolv : Group.IsSolvable ρ.range := by
      have : Group.IsNilpotent ((X.map ρ).subgroupOf ρ.range) := hPVp'.isNilpotent
      have hQ2 : IsPGroup 2 (ρ.range ⧸ (X.map ρ).subgroupOf ρ.range) := by
        intro y
        obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨k, hk⟩ := hΓ2 γ
        exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
      have : Group.IsNilpotent (ρ.range ⧸ (X.map ρ).subgroupOf ρ.range) := hQ2.isNilpotent
      exact Group.isSolvable_of_ker_le_range ((X.map ρ).subgroupOf ρ.range).subtype
        (QuotientGroup.mk' ((X.map ρ).subgroupOf ρ.range))
        (by rw [QuotientGroup.ker_mk', range_subtype])
    have hSyl : IsSylowOf p (X.map ρ) ρ.range := by
      refine isSylowOf_iff.mpr ⟨hPVΓ, hPVp, ?_⟩
      rw [relIndex, hj]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    have hO2Γ : pCore 2 ρ.range = ⊥ := by
      have hDn : ((pCore 2 ρ.range).comap ρ.rangeRestrict).Normal :=
        (pCore_normal (p := 2) (G := ρ.range)).comap _
      have hDC : (pCore 2 ρ.range).comap ρ.rangeRestrict ≤ C := by
        refine hred _ hDn fun d hd => ?_
        obtain ⟨k, hk⟩ := pCore_isPGroup (p := 2) (G := ρ.range) ⟨_, hd⟩
        refine ⟨k, ?_⟩
        rw [← hρker, MonoidHom.mem_ker]
        have h1 : (ρ.rangeRestrict d) ^ 2 ^ k = 1 := congrArg Subtype.val hk
        have h2 := congrArg Subtype.val h1
        simpa [map_pow] using h2
      rw [eq_bot_iff]
      intro γ hγ
      obtain ⟨g, rfl⟩ := ρ.rangeRestrict_surjective γ
      have hgC : g ∈ C := hDC hγ
      rw [← hρker, MonoidHom.mem_ker] at hgC
      rw [mem_bot]
      exact Subtype.ext hgC
    have hFit : fittingSubgroup ρ.range = (X.map ρ).subgroupOf ρ.range := by
      refine le_antisymm ?_ (le_sSup ⟨hPVn, hPVp'.isNilpotent⟩)
      rw [fitting_eq_sup_pCore ρ.range]
      refine iSup_le fun r => ?_
      by_cases hr2 : r.1.1 = 2
      · have h0 : pCore r.1.1 ρ.range = ⊥ := by rw [hr2]; exact hO2Γ
        rw [h0]
        exact bot_le
      · intro γ hγ
        have hr : r.1.1.Prime := Nat.prime_of_mem_primeFactors r.1.2
        obtain ⟨m, hm⟩ := pCore_isPGroup (p := r.1.1) (G := ρ.range) ⟨γ, hγ⟩
        obtain ⟨k, hk⟩ := hΓ2 γ
        have h1 : γ ^ r.1.1 ^ m ∈ (X.map ρ).subgroupOf ρ.range := by
          have h2 : γ ^ r.1.1 ^ m = 1 := congrArg Subtype.val hm
          rw [h2]
          exact one_mem _
        exact CFSG.Walter.JT.mem_of_pow_mem_of_coprime h1 hk
          (Nat.Coprime.pow m k ((Nat.coprime_primes hr Nat.prime_two).mpr hr2))
    have hgen : generalizedFitting ρ.range = (X.map ρ).subgroupOf ρ.range := by
      rw [CFSG.RankThree.PGroups.generalizedFitting_eq_fittingSubgroup_of_isSolvable, hFit]
    have hf : ∀ x : X, (ρ.comp X.subtype) x ∈ X.map ρ := fun x => mem_map_of_mem ρ x.2
    set f : X →* X.map ρ := (ρ.comp X.subtype).codRestrict (X.map ρ) hf with hfdef
    have hfs : Function.Surjective f := by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfk : f.ker = B.subgroupOf X := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, hBXC]
      constructor
      · intro h
        refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
        rw [← hρker, MonoidHom.mem_ker]
        exact congrArg Subtype.val h
      · intro h
        apply Subtype.ext
        have h1 := (Subgroup.mem_inf.mp h).2
        rw [← hρker, MonoidHom.mem_ker] at h1
        exact h1
    exact ⟨hsolv, hPVn, hSyl, hgen,
      (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun x => rfl⟩
  ·
    refine ⟨(QuotientGroup.quotientQuotientEquivQuotient (pCore 2 X) (B.subgroupOf X) hqB').symm,
      fun x => ?_⟩
    rw [MulEquiv.symm_apply_eq]
    rfl
  ·
    obtain ⟨μ, hμ⟩ := exists_frattini_quotient_equiv hqB' hBΦ
    set β : E →* MulAut ((X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)) :=
      (autQuotient (frattini (X ⧸ pCore 2 X))).comp
        ((autQuotient (pCore 2 X)).comp MulAut.conjNormal) with hβ
    set α : E →* MulAut ((X ⧸ B.subgroupOf X) ⧸ frattini (X ⧸ B.subgroupOf X)) :=
      (MulAut.congr μ).symm.toMonoidHom.comp β with hα
    have hβx : ∀ (g : E) (x : X), β g ((x : X ⧸ pCore 2 X) :
        (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)) =
      (((MulAut.conjNormal g x : X) : X ⧸ pCore 2 X) :
        (X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)) := fun _ _ => rfl
    have hαμ : ∀ (g : E) (w : (X ⧸ B.subgroupOf X) ⧸ frattini (X ⧸ B.subgroupOf X)),
        μ (α g w) = β g (μ w) := by
      intro g w
      exact μ.apply_symm_apply _
    refine ⟨μ, hμ, α, β, fun g x => ?_, hβx, hαμ⟩
    apply μ.injective
    rw [hαμ, hμ, hβx, hμ]

end CFSG.Quasithin.SteinbergCD
