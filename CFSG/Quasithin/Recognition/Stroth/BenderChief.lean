module

public import CFSG.Quasithin.Recognition.Stroth.BenderOmega
public import CFSG.Quasithin.EmptyFaithful.S152He3Chief
public import CFSG.Quasithin.Recognition.Stroth.BenderDisplacement

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizerMod_zpowers_iff_of_normalizer {N L : Subgroup G} {t x : G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (htL : t ∈ Subgroup.normalizer (L : Set G)) (hxN : x ∈ N) :
    x ∈ centralizerMod L N (Subgroup.zpowers t) ↔ x * t * x⁻¹ * t⁻¹ ∈ L := by
  constructor
  · intro hx
    exact hx.2.2 t (Subgroup.mem_zpowers t)
  · intro ht
    have hxL : x ∈ Subgroup.normalizer (L : Set G) := hNL hxN
    have hpos : ∀ n : ℕ, x * t ^ n * x⁻¹ * (t ^ n)⁻¹ ∈ L := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hconj : t ^ n * (x * t * x⁻¹ * t⁻¹) * (t ^ n)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htL n) _).mp ht
        have e : x * t ^ (n + 1) * x⁻¹ * (t ^ (n + 1))⁻¹ =
            (x * t ^ n * x⁻¹ * (t ^ n)⁻¹) *
              (t ^ n * (x * t * x⁻¹ * t⁻¹) * (t ^ n)⁻¹) := by
          rw [pow_succ]
          group
        rw [e]
        exact L.mul_mem ih hconj
    have hneg : ∀ n : ℕ, x * (t ^ n)⁻¹ * x⁻¹ * ((t ^ n)⁻¹)⁻¹ ∈ L := by
      intro n
      have hA : (x * t ^ n * x⁻¹ * (t ^ n)⁻¹)⁻¹ ∈ L := L.inv_mem (hpos n)
      have hconj : (t ^ n)⁻¹ * (x * t ^ n * x⁻¹ * (t ^ n)⁻¹)⁻¹ * t ^ n ∈ L := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ (Subgroup.pow_mem _ htL n)) _).mp hA
        simpa using h
      have e : (t ^ n)⁻¹ * (x * t ^ n * x⁻¹ * (t ^ n)⁻¹)⁻¹ * t ^ n =
          x * (t ^ n)⁻¹ * x⁻¹ * ((t ^ n)⁻¹)⁻¹ := by group
      rwa [e] at hconj
    refine ⟨hxN, hxL, fun a ha => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · simpa [zpow_natCast] using hpos n
    · simpa [zpow_neg, zpow_natCast] using hneg n

theorem relIndex_centralizerMod_eq_index_of_fixedSection
    {H N L : Subgroup G} {t : G} [(L.subgroupOf N).Normal]
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (htH : t ∈ H) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (tL : MulAut (SectionW N L)) (K : Subgroup (SectionW N L))
    (hKmem : ∀ u : ↥N, QuotientGroup.mk u ∈ K ↔
      tL (QuotientGroup.mk u) = QuotientGroup.mk u)
    (hact : ∀ u : ↥N, tL (QuotientGroup.mk u) =
      QuotientGroup.mk (conjAct N ⟨t, hHN htH⟩ u)) :
    (centralizerMod L N (Subgroup.zpowers t)).relIndex N = K.index := by
  classical
  let X : Subgroup ↥N := K.comap (QuotientGroup.mk' (L.subgroupOf N))
  have hXK : X.index = K.index :=
    Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective _)
  let X' : Subgroup G := X.map N.subtype
  have hX'sub : X'.subgroupOf N = X := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      simpa [hyx'] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hX'idx : X'.relIndex N = X.index := by
    change (X'.subgroupOf N).index = X.index
    rw [hX'sub]
  have hX'eq : X' = centralizerMod L N (Subgroup.zpowers t) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, huX, rfl⟩
      have huK : (QuotientGroup.mk u : SectionW N L) ∈ K := by
        simpa [X] using huX
      have hfix : tL (QuotientGroup.mk u) = QuotientGroup.mk u :=
        (hKmem u).mp huK
      rw [hact] at hfix
      have hq : ((conjAct N ⟨t, hHN htH⟩ u)⁻¹ * u : ↥N) ∈ L.subgroupOf N :=
        (QuotientGroup.eq).mp hfix
      have h1 : (t * (u : G) * t⁻¹)⁻¹ * (u : G) ∈ L := by
        simpa [conjAct_coe_apply] using Subgroup.mem_subgroupOf.mp hq
      have h2 : (u : G) * ((t * (u : G) * t⁻¹)⁻¹ * (u : G)) * (u : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hNL u.2) _).mp h1
      have e : (u : G) * ((t * (u : G) * t⁻¹)⁻¹ * (u : G)) * (u : G)⁻¹ =
          (u : G) * t * (u : G)⁻¹ * t⁻¹ := by group
      rw [e] at h2
      exact (mem_centralizerMod_zpowers_iff_of_normalizer hNL (hHL htH) u.2).2 h2
    · rintro hx
      obtain ⟨hxN, -, hxcomm⟩ := hx
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      have hxK : (QuotientGroup.mk (⟨x, hxN⟩ : ↥N) : SectionW N L) ∈ K := by
        rw [hKmem ⟨x, hxN⟩, hact]
        apply (QuotientGroup.eq).mpr
        rw [Subgroup.mem_subgroupOf]
        have hx1 : x * t * x⁻¹ * t⁻¹ ∈ L := hxcomm t (Subgroup.mem_zpowers t)
        have hx2 : t * x⁻¹ * t⁻¹ * x ∈ L := by
          have h := (Subgroup.mem_normalizer_iff.mp
            (Subgroup.inv_mem _ (hNL hxN)) _).mp hx1
          have e : (x : G)⁻¹ * (x * t * x⁻¹ * t⁻¹) * ((x : G)⁻¹)⁻¹ =
              t * (x : G)⁻¹ * t⁻¹ * x := by group
          rwa [e] at h
        simpa [conjAct_coe_apply, mul_assoc] using hx2
      simpa [X] using hxK
  calc (centralizerMod L N (Subgroup.zpowers t)).relIndex N
      = X'.relIndex N := by rw [hX'eq]
    _ = X.index := hX'idx
    _ = K.index := hXK

theorem chiefStep_section_sq_mem {H U L N : Subgroup G}
    (hU : IsPGroup 2 U) (hUH : U ≤ H) (hstep : IsChiefStep H U L N) :
    ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ L ∧ a * a ∈ L := by
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) := isElemAbelian_chiefMod hstep hUH hU
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hιsq : ∀ x : ↥N, Ch3z.chiefIota hNL x * Ch3z.chiefIota hNL x = 1 := by
    intro x
    have h := hE.2 (Ch3z.chiefIota hNL x).1 (Ch3z.chiefIota hNL x).2
    refine Subtype.ext ?_
    simpa [pow_two] using h
  intro a ha b hb
  have habN : a * b * a⁻¹ * b⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem ha hb) (N.inv_mem ha)) (N.inv_mem hb)
  have haaN : a * a ∈ N := N.mul_mem ha ha
  constructor
  · rw [← Ch3z.chiefIota_eq_one_iff hNL ⟨_, habN⟩]
    have harg : (⟨a * b * a⁻¹ * b⁻¹, habN⟩ : ↥N) =
        ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ :=
      Subtype.ext (by simp [mul_assoc])
    rw [harg, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h := hιsq ⟨a * b, N.mul_mem ha hb⟩
    rw [show (⟨a * b, N.mul_mem ha hb⟩ : ↥N) = ⟨a, ha⟩ * ⟨b, hb⟩ from
      Subtype.ext rfl, map_mul] at h
    rw [inv_eq_of_mul_eq_one_right (hιsq ⟨a, ha⟩),
      inv_eq_of_mul_eq_one_right (hιsq ⟨b, hb⟩)]
    simpa [mul_assoc] using h
  · rw [← Ch3z.chiefIota_eq_one_iff hNL ⟨_, haaN⟩]
    have harg : (⟨a * a, haaN⟩ : ↥N) = ⟨a, ha⟩ * ⟨a, ha⟩ := Subtype.ext rfl
    rw [harg, map_mul]
    exact hιsq ⟨a, ha⟩

theorem sq_le_relIndex_centralizerMod
    {H U L N : Subgroup G} {q : ℕ}
    (hX : IsSzU3Quot (oTwoQuot ↥H) q) (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    {t : G} (htH : t ∈ H) (ht : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H) :
    q ^ 2 ≤ (centralizerMod L N (Subgroup.zpowers t)).relIndex N := by
  classical
  obtain ⟨hQ, hZinv, hbound⟩ := bender_actor_facts (X := oTwoQuot ↥H) (q := q) hX
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr hNL
  have hnotriv : ∃ h ∈ H, ∃ u ∈ N, h * u * h⁻¹ * u⁻¹ ∉ L := by
    by_contra hcon
    apply hnc
    intro h hh u hu
    by_contra hnu
    exact hcon ⟨h, hh, u, hu, hnu⟩
  have hmax : ∀ X : Subgroup G, L ≤ X → X ≤ N →
      H ≤ Subgroup.normalizer (X : Set G) → X = L ∨ X = N := by
    intro X hLX hXN hHX
    exact hstep.2.2.2 X
      ⟨hXN.trans hstep.1.1, fun g hg x hx =>
        (Subgroup.mem_normalizer_iff.mp (hHX hg) x).mp hx⟩ hLX hXN
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) := isElemAbelian_chiefMod hstep hUH hU
  have hQK : pCoreOf 2 H ≤ centralizerMod L H N :=
    Ch3z.pCoreOf_le_centralizerMod hUH hstep hE
  have hO2triv : ∀ r ∈ pCoreOf 2 H, ∀ u ∈ N, r * u * r⁻¹ * u⁻¹ ∈ L :=
    fun r hr u hu => (hQK hr).2.2 u hu
  obtain ⟨hnt, La, tL, hperf, hirr, htL, htL2, htL1, hact, ⟨eCQ⟩, hsq⟩ :=
    section_actor (U := N) (U' := L) (chiefStep_section_sq_mem hU hUH hstep)
      hHN hHL hstep.2.2.1 hmax hnotriv hO2triv hQ hZinv htH ht htO
  have hWcomm : ∀ x y : SectionW N L, x * y = y * x := by
    intro x y
    calc x * y = (x * y)⁻¹ :=
          (inv_eq_of_mul_eq_one_right (hsq (x * y))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
          rw [inv_eq_of_mul_eq_one_right (hsq x), inv_eq_of_mul_eq_one_right (hsq y)]
  letI : CommGroup (SectionW N L) :=
    { (inferInstance : Group (SectionW N L)) with mul_comm := hWcomm }
  haveI : Nontrivial (SectionW N L) := hnt
  let K : Subgroup (SectionW N L) := fixV (Subgroup.zpowers tL)
  have hKmem : ∀ u : ↥N, QuotientGroup.mk u ∈ K ↔
      tL (QuotientGroup.mk u) = QuotientGroup.mk u :=
    fun u => mem_fixV_zpowers_iff_apply
  have hactor : q ^ 2 ≤ (fixV (Subgroup.zpowers tL)).index :=
    hbound (SectionW N L) hsq La hperf hirr ⟨eCQ⟩ tL htL htL2 htL1
  rw [relIndex_centralizerMod_eq_index_of_fixedSection hHN hHL htH hNL tL K hKmem hact]
  exact hactor

theorem sq_le_relIndex_centralizerMod_of_not_le
    {H U L N A : Subgroup G} {q : ℕ}
    (hX : IsSzU3Quot (oTwoQuot ↥H) q) (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) (hAH : A ≤ H)
    (hA : ∀ a ∈ A, a * a ∈ pCoreOf 2 H) (hAO : ¬ A ≤ pCoreOf 2 H) :
    q ^ 2 ≤ (centralizerMod L N A).relIndex N := by
  have hex : ∃ t ∈ A, t ∉ pCoreOf 2 H := by
    by_contra hcon
    apply hAO
    intro a ha
    by_contra haO
    exact hcon ⟨a, ha, haO⟩
  obtain ⟨t, htA, htO⟩ := hex
  have htH : t ∈ H := hAH htA
  refine (sq_le_relIndex_centralizerMod hX hU hUH hstep hnc htH
    (hA t htA) htO).trans ?_
  exact Subgroup.relIndex_le_of_le_left
    (centralizerMod_anti_right (X := N) (U := Subgroup.zpowers t) (U' := A)
      (Subgroup.zpowers_le.mpr htA))
    (Subgroup.index_ne_zero_of_finite)

private theorem mul_self_mem_of_mul_self_mem_zpowers {P : Subgroup G} {t a : G}
    (ht : t * t ∈ P) (ha : a ∈ Subgroup.zpowers t) : a * a ∈ P := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have h2 : (t * t) ^ k ∈ P := Subgroup.zpow_mem _ ht k
  convert h2 using 2
  have hbase : t * t = t ^ (2 : ℤ) :=
    ((zpow_natCast t 2).trans (pow_two t)).symm
  rw [← zpow_add, hbase, ← zpow_mul]
  congr 1
  ring

theorem pow_sq_le_relIndex_centralizer
    {H U : Subgroup G} {q c : ℕ}
    (hX : IsSzU3Quot (oTwoQuot ↥H) q) (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hser : IsChiefSeriesFrom H U U c) {t : G} (htH : t ∈ H)
    (ht : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H) :
    (q ^ 2) ^ c ≤
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex U := by
  have hk : ∀ L' N' : Subgroup G, IsChiefStep H U L' N' → ¬ IsCentralStep H L' N' →
      q ^ 2 ≤ (centralizerMod L' N' (Subgroup.zpowers t)).relIndex N' := by
    intro L' N' hstep' hnc'
    refine sq_le_relIndex_centralizerMod_of_not_le hX hU hUH hstep' hnc'
      (Subgroup.zpowers_le.mpr htH) (fun a ha => ?_)
      (fun hle => htO (hle (Subgroup.mem_zpowers t)))
    exact mul_self_mem_of_mul_self_mem_zpowers ht ha
  exact D15Proof.pow_le_relIndex hUH (Subgroup.zpowers_le.mpr htH) hk hser

end CFSG.Quasithin.Stroth
