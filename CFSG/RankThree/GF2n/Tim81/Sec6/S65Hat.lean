module

public import CFSG.RankThree.GF2n.Tim81.Sec6.S65MinBar
import CFSG.RankThree.GF2n.Tim81.Sec5.I6Conic
import CFSG.Timmesfeld.Bridge.OddTranspMain
import CFSG.GroupTheory.ConjFixedParity
import CFSG.RankThree.GF2n.Tim78S410Core
import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld
open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}
variable {U B : Subgroup G} {α β : G}
variable {H : Subgroup G} {h₀ y₀ z₀ : G}

abbrev UHat (U : Subgroup G) : Type := UBar U ⧸ CFSG.solvableRadical (UBar U)

@[expose] def piU (U : Subgroup G) : ↥U →* UHat U :=
  (QuotientGroup.mk' (CFSG.solvableRadical (UBar U))).comp
    (QuotientGroup.mk' (Subgroup.center ↥U))

abbrev ptsIn (V S : Subgroup G) : Set (Subgroup G) := {C | C ∈ omegaSet V ∧ C ≤ S}

abbrev sylowImage (U : Subgroup G) (S : Sylow 2 ↥U) : Subgroup G :=
  (S : Subgroup ↥U).map U.subtype

theorem MinBad.conj_alpha (hS : Sec6Hyp M V) (hm : MinBad V U B α β)
    (ht : Twin M V U α H h₀ y₀ z₀) {k : G} (hk : k ∈ U) (hkV : conjSubgroup k V = V) :
    k * α * k⁻¹ = α := by
  have hroot := hS.sec5.toRootHyp
  have hVpts : V ∈ Tim79a.omegaOf V H := by
    have h := Tim79a.conjSubgroup_mem_omegaOf (V := V) (H := H) H.one_mem
    rwa [CGT.Timmesfeld75.conjSubgroup_one] at h
  have hA'pts : conjSubgroup y₀ V ∈ Tim79a.omegaOf V H :=
    Tim79a.conjSubgroup_mem_omegaOf ht.mem_H
  have hA'omega : conjSubgroup y₀ V ∈ omegaSet V :=
    Tim79a.conjSubgroup_mem_omegaOf (H := ⊤) (Subgroup.mem_top y₀)
  have hα2 : α * α = 1 := hroot.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hkz : k * z₀ * k⁻¹ = z₀ := by
    have h := Subgroup.mem_centralizer_iff.mp ht.mem_ZU.2 k hk
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  set α₁ : G := k * α * k⁻¹ with hα₁def
  have hα₁V : α₁ ∈ V := by
    have h : α₁ ∈ conjSubgroup k V := Subgroup.mem_map.mpr ⟨α, hm.memα, rfl⟩
    rwa [hkV] at h
  have hkey : α₁ * z₀ = (α₁ * α) * (α * z₀) := by
    calc α₁ * z₀ = α₁ * (α * α) * z₀ := by rw [hα2]; group
      _ = (α₁ * α) * (α * z₀) := by group
  have hαz1 : α * z₀ ≠ 1 := by
    intro h
    apply ht.not_mem
    have hz : z₀ = α := by
      calc z₀ = α * (α * z₀) := by rw [← mul_assoc, hα2, one_mul]
        _ = α * 1 := by rw [h]
        _ = α := mul_one α
    rw [hz]
    exact hm.memα
  have hαzD : α * z₀ ∈ Tim78.classD V := mem_classD_of_mem hA'omega ht.mem hαz1
  have hdD : α₁ * z₀ ∈ Tim78.classD V := by
    have h := Tim78.mem_classD_conj hαzD k
    have hk' : k * (α * z₀) * k⁻¹ = α₁ * z₀ := by
      rw [hα₁def]
      calc k * (α * z₀) * k⁻¹ = (k * α * k⁻¹) * (k * z₀ * k⁻¹) := by group
        _ = (k * α * k⁻¹) * z₀ := by rw [hkz]
    rwa [hk'] at h
  have hmem : α₁ * z₀ ∈ V ⊔ conjSubgroup y₀ V := by
    rw [hkey]
    exact Subgroup.mul_mem_sup (V.mul_mem hα₁V hm.memα) ht.mem
  have hmem2 := Sec45Shape.mem_or_mem_of_points hroot ht.shape hVpts hA'pts ht.ne.symm
    hmem hdD
  rcases hmem2 with h | h
  · exfalso
    apply ht.not_mem
    have hz : z₀ = α₁⁻¹ * (α₁ * z₀) := by group
    rw [hz]
    exact V.mul_mem (V.inv_mem hα₁V) h
  · have hmemA' : α₁ * α ∈ conjSubgroup y₀ V := by
      have hEq : α₁ * α = (α₁ * z₀) * (α * z₀)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hα2]
        group
      rw [hEq]
      exact (conjSubgroup y₀ V).mul_mem h ((conjSubgroup y₀ V).inv_mem ht.mem)
    have hmemV : α₁ * α ∈ V := V.mul_mem hα₁V hm.memα
    have hbot : α₁ * α ∈ (⊥ : Subgroup G) := by
      rw [← inf_conjSubgroup_eq_bot_of_isTI hroot.toHyp.ti ht.ne]
      exact Subgroup.mem_inf.mpr ⟨hmemV, hmemA'⟩
    have h1 : α₁ * α = 1 := Subgroup.mem_bot.mp hbot
    calc k * α * k⁻¹ = α₁ := rfl
      _ = α₁ * (α * α) := by rw [hα2, mul_one]
      _ = (α₁ * α) * α := by group
      _ = α := by rw [h1, one_mul]

theorem MinBad.isBender (hB : OddTranspBender) (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) : CFSG.BenderSuzuki.IsBenderGroup (UHat U) :=
  CFSG.Timmesfeld.Bridge.OddTransp.isBenderGroup_quotient_of_le
    (hm.setup hS h64) (hm.meetsSq hS h64) (hm.disconnected hS h64)
    (fun H _ _ F _ hS' hrad hF hdisc => hB H F hS' hrad hF hdisc)

theorem MinBad.piU_ne_one (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β)
    {x : ↥U} (hx : (x : G) ∈ EU V U) : piU U x ≠ 1 := by
  have hxbar : (x : UBar U) ∈ EBar V U := ⟨x, hx, rfl⟩
  have hsol : Group.IsSolvable (CFSG.solvableRadical (UBar U)) :=
    CFSG.Timmesfeld.Bridge.OddTransp.isSolvable_solvableRadical
  have hnot := CFSG.Timmesfeld.Bridge.OddTransp.not_mem_of_isSolvable
    (hm.setup hS h64) (hm.meetsSq hS h64) hsol hxbar
  intro h1
  apply hnot
  have h1' : (QuotientGroup.mk' (CFSG.solvableRadical (UBar U))) (x : UBar U) = 1 := h1
  exact (QuotientGroup.eq_one_iff (x : UBar U)).mp h1'

private theorem commute_of_mem_isPGroup_two (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) {d e : G} (hd : d ∈ S) (he : e ∈ S)
    (hdD : d ∈ Tim78.classD V) (heD : e ∈ Tim78.classD V) : Commute d e := by
  obtain ⟨k, hk⟩ := hS2 ⟨d * e, S.mul_mem hd he⟩
  have hk' : (d * e) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact hS.commute_of_pow_two_pow h64 hdD heD hk'

theorem MinBad.mem_pts (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hnc : NoCommPair M V)
    (hm : MinBad V U B α β) (ht : Twin M V U α H h₀ y₀ z₀)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hVS : V ⊔ conjSubgroup y₀ V ≤ S)
    {C : Subgroup G} (hC : C ∈ ptsIn V S) : C ∈ Tim79a.omegaOf V H := by
  classical
  have hroot := hS.sec5.toRootHyp
  have hVpts : V ∈ Tim79a.omegaOf V H := by
    have h := Tim79a.conjSubgroup_mem_omegaOf (V := V) (H := H) H.one_mem
    rwa [CGT.Timmesfeld75.conjSubgroup_one] at h
  have hA'pts : conjSubgroup y₀ V ∈ Tim79a.omegaOf V H :=
    Tim79a.conjSubgroup_mem_omegaOf ht.mem_H
  have hA'omega : conjSubgroup y₀ V ∈ omegaSet V :=
    Tim79a.conjSubgroup_mem_omegaOf (H := ⊤) (Subgroup.mem_top y₀)
  have hα1 : α ≠ 1 := hm.alpha_ne_one hS
  have hα2 : α * α = 1 := hroot.mul_self_of_mem (mem_omegaSet_self V) hm.memα
  have hαD : α ∈ Tim78.classD V := mem_classD_of_mem (mem_omegaSet_self V) hm.memα hα1
  have hαS : α ∈ S := hVS (Subgroup.mem_sup_left hm.memα)
  have hαz1 : α * z₀ ≠ 1 := by
    intro h
    apply ht.not_mem
    have hz : z₀ = α := by
      calc z₀ = α * (α * z₀) := by rw [← mul_assoc, hα2, one_mul]
        _ = α * 1 := by rw [h]
        _ = α := mul_one α
    rw [hz]
    exact hm.memα
  have hαzD : α * z₀ ∈ Tim78.classD V := mem_classD_of_mem hA'omega ht.mem hαz1
  have hαzS : α * z₀ ∈ S := hVS (Subgroup.mem_sup_right ht.mem)
  have hCcenV : C ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, one_mul]
    · have hxD : x ∈ Tim78.classD V := mem_classD_of_mem hC.1 hx hx1
      have hcx : Commute x α :=
        commute_of_mem_isPGroup_two hS h64 hS2 (hC.2 hx) hαS hxD hαD
      exact (hroot.commute_of_commute_mem hC.1 (mem_omegaSet_self V) hx hm.memα hx1 hα1
        hcx x hx y hy).eq.symm
  have hCcenA' : C ≤ Subgroup.centralizer (conjSubgroup y₀ V : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, one_mul]
    · have hxD : x ∈ Tim78.classD V := mem_classD_of_mem hC.1 hx hx1
      have hcx : Commute x (α * z₀) :=
        commute_of_mem_isPGroup_two hS h64 hS2 (hC.2 hx) hαzS hxD hαzD
      exact (hroot.commute_of_commute_mem hC.1 hA'omega hx ht.mem hx1 hαz1
        hcx x hx y hy).eq.symm
  have hCM : C ≤ M := hCcenV.trans (by
    rw [← hroot.toHyp.normalizer_eq]
    exact Subgroup.centralizer_le_normalizer (V : Set G))
  rcases h64 C hC.1 hCM with hCV | hCsig
  · rw [hCV]
    exact hVpts
  · have hcomm : ⁅conjSubgroup y₀ V, C⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hCcenA'
    obtain ⟨p, hp, hpC⟩ := hnc (conjSubgroup y₀ V) ht.sigma C hCsig hcomm
    refine Tim79a.mem_omegaOf.mpr ⟨p * y₀, H.mul_mem (ht.shape.Pc_le hp) ht.mem_H, ?_⟩
    rw [hpC, CGT.Timmesfeld75.conjSubgroup_conjSubgroup]

private theorem exists_least_period {g : ↥U} :
    ∃ k₀ : ℕ, 0 < k₀ ∧ conjSubgroup ((g : G) ^ k₀) V = V ∧
      ∀ d, 0 < d → d < k₀ → conjSubgroup ((g : G) ^ d) V ≠ V := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ conjSubgroup ((g : G) ^ k) V = V := by
    refine ⟨orderOf g, orderOf_pos g, ?_⟩
    have h1 : (g : ↥U) ^ orderOf g = 1 := pow_orderOf_eq_one g
    have h2 : (g : G) ^ orderOf g = 1 := by
      rw [← Subgroup.coe_pow, h1]
      rfl
    rw [h2, conjSubgroup_one]
  obtain ⟨hk1, hk2⟩ := Nat.find_spec hex
  exact ⟨Nat.find hex, hk1, hk2, fun d hd hdk h => Nat.find_min hex hdk ⟨hd, h⟩⟩

private theorem orbit_bound_card (hS : Sec6Hyp M V)
    (hm : MinBad V U B α β) (ht : Twin M V U α H h₀ y₀ z₀) {K : Type*} [Group K]
    (π : ↥U →* K) (g : ↥U) {Z : Subgroup K}
    (htr : ∀ z ∈ Z, z ≠ 1 → ∃ k : ℕ,
      π g ^ k * π ⟨α, hm.le.2.2.1⟩ * (π g ^ k)⁻¹ = z)
    {k₀ : ℕ} (hk₀pos : 0 < k₀) (hk₀V : conjSubgroup ((g : G) ^ k₀) V = V) :
    Nat.card Z ≤ k₀ + 1 := by
  classical
  let αU : ↥U := ⟨α, hm.le.2.2.1⟩
  let f : ℕ → K := fun k => π g ^ k * π αU * (π g ^ k)⁻¹
  have hcomm₀ : π g ^ k₀ * π αU * (π g ^ k₀)⁻¹ = π αU := by
    have hV : conjSubgroup (((g : ↥U) ^ k₀ : ↥U) : G) V = V := by
      rw [Subgroup.coe_pow]
      exact hk₀V
    have h := hm.conj_alpha hS ht (k := (((g : ↥U) ^ k₀ : ↥U) : G)) (g ^ k₀).2 hV
    have hU : (g : ↥U) ^ k₀ * αU * ((g : ↥U) ^ k₀)⁻¹ = αU := by
      apply Subtype.ext
      simpa [αU, Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hπ := congrArg π hU
    simpa only [map_mul, map_inv, map_pow] using hπ
  have hper : ∀ k : ℕ, f (k + k₀) = f k := by
    intro k
    have hpow : π g ^ (k + k₀) = π g ^ k * π g ^ k₀ := pow_add _ _ _
    simp only [f, hpow, mul_inv_rev]
    calc (π g ^ k * π g ^ k₀) * π αU * ((π g ^ k₀)⁻¹ * (π g ^ k)⁻¹)
        = π g ^ k * (π g ^ k₀ * π αU * (π g ^ k₀)⁻¹) * (π g ^ k)⁻¹ := by group
      _ = π g ^ k * π αU * (π g ^ k)⁻¹ := by rw [hcomm₀]
  have hiter : ∀ q r : ℕ, f (r + k₀ * q) = f r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have hq : r + k₀ * (q + 1) = (r + k₀ * q) + k₀ := by ring
      rw [hq, hper, ih]
  have hfmod : ∀ k : ℕ, f k = f (k % k₀) := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k k₀]
    exact hiter (k / k₀) (k % k₀)
  have hsub : (Z : Set K) ⊆ insert 1 (f '' {r : ℕ | r < k₀}) := by
    intro z hz
    by_cases hz1 : z = 1
    · exact Set.mem_insert_iff.mpr (Or.inl hz1)
    · obtain ⟨k, hk⟩ := htr z hz hz1
      have hfk : f k = z := hk
      refine Set.mem_insert_iff.mpr (Or.inr ⟨k % k₀, ?_, ?_⟩)
      · exact Nat.mod_lt k hk₀pos
      · rw [← hfmod]
        exact hfk
  have hZcard : Nat.card Z = (Z : Set K).ncard := Nat.card_coe_set_eq _
  rw [hZcard]
  calc (Z : Set K).ncard ≤ (insert 1 (f '' {r : ℕ | r < k₀})).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (f '' {r : ℕ | r < k₀}).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ {r : ℕ | r < k₀}.ncard + 1 := Nat.add_le_add_right Set.ncard_image_le _
    _ = k₀ + 1 := by
        have hset : {r : ℕ | r < k₀} = (Finset.range k₀ : Set ℕ) := by
          ext r
          simp
        rw [hset, Set.ncard_coe_finset, Finset.card_range]

private theorem orbit_bound_distinct {g : ↥U} {k₀ : ℕ}
    (hmin : ∀ d, 0 < d → d < k₀ → conjSubgroup ((g : G) ^ d) V ≠ V) :
    ∀ i < k₀, ∀ j < k₀,
      conjSubgroup ((g : G) ^ i) V = conjSubgroup ((g : G) ^ j) V → i = j := by
  have hdist : ∀ a b : ℕ, a < b →
      conjSubgroup ((g : G) ^ a) V = conjSubgroup ((g : G) ^ b) V →
      conjSubgroup ((g : G) ^ (b - a)) V = V := by
    intro a b hab heq
    have h1 : conjSubgroup (((g : G) ^ a)⁻¹) (conjSubgroup ((g : G) ^ a) V) =
        conjSubgroup (((g : G) ^ a)⁻¹) (conjSubgroup ((g : G) ^ b) V) := by rw [heq]
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
    have h2 : ((g : G) ^ a)⁻¹ * (g : G) ^ b = (g : G) ^ (b - a) := by
      have hb : (g : G) ^ b = (g : G) ^ a * (g : G) ^ (b - a) := by
        rw [← pow_add, Nat.add_sub_of_le (le_of_lt hab)]
      rw [hb, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h2] at h1
    exact h1.symm
  intro i hi j hj heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hd : 0 < j - i := by omega
    have hdk : j - i < k₀ := by omega
    exact (hmin (j - i) hd hdk) (hdist i j hlt heq)
  · have hd : 0 < i - j := by omega
    have hdk : i - j < k₀ := by omega
    exact (hmin (i - j) hd hdk) (hdist j i hgt heq.symm)

theorem MinBad.orbit_bound (hS : Sec6Hyp M V) (hm : MinBad V U B α β)
    (ht : Twin M V U α H h₀ y₀ z₀) {K : Type*} [Group K] (π : ↥U →* K) (g : ↥U)
    {Z : Subgroup K} (htr : ∀ z ∈ Z, z ≠ 1 → ∃ k : ℕ,
      π g ^ k * π ⟨α, hm.le.2.2.1⟩ * (π g ^ k)⁻¹ = z) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ Nat.card Z ≤ k₀ + 1 ∧
      ∀ i < k₀, ∀ j < k₀,
        conjSubgroup ((g : G) ^ i) V = conjSubgroup ((g : G) ^ j) V → i = j := by
  obtain ⟨k₀, hk₀pos, hk₀V, hmin⟩ := exists_least_period (V := V) (g := g)
  exact ⟨k₀, hk₀pos, orbit_bound_card hS hm ht π g htr hk₀pos hk₀V,
    orbit_bound_distinct hmin⟩

private theorem comap_eq_inf_sup_center {S₁ : Sylow 2 ↥U} {N : Subgroup (UBar U)} [N.Normal]
    (hNle : N ≤ (S₁ : Subgroup ↥U).map (QuotientGroup.mk' (Subgroup.center ↥U))) :
    N.comap (QuotientGroup.mk' (Subgroup.center ↥U)) =
      ((S₁ : Subgroup ↥U) ⊓ N.comap (QuotientGroup.mk' (Subgroup.center ↥U))) ⊔
        Subgroup.center ↥U := by
  classical
  set πc : ↥U →* UBar U := QuotientGroup.mk' (Subgroup.center ↥U) with hπc
  let Nhat : Subgroup ↥U := N.comap πc
  have hcenter_le : Subgroup.center ↥U ≤ Nhat := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hz1 : πc z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [hz1]
    exact N.one_mem
  refine le_antisymm ?_ (sup_le inf_le_right hcenter_le)
  intro x hx
  have hxN : πc x ∈ N := hx
  have hxS : πc x ∈ (S₁ : Subgroup ↥U).map πc := hNle hxN
  obtain ⟨s, hs, hsc⟩ := Subgroup.mem_map.mp hxS
  have hmem_center : s⁻¹ * x ∈ Subgroup.center ↥U := by
    rw [← QuotientGroup.eq_one_iff]
    show πc (s⁻¹ * x) = 1
    rw [map_mul, map_inv, hsc]
    exact inv_mul_cancel (πc x)
  have hsN : s ∈ Nhat := by
    have h2 : s = x * (s⁻¹ * x)⁻¹ := by group
    rw [h2]
    exact Nhat.mul_mem hx (Nhat.inv_mem (hcenter_le hmem_center))
  have hxsup : x = s * (s⁻¹ * x) := by group
  rw [hxsup]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hs, hsN⟩)
    (Subgroup.mem_sup_right hmem_center)

private theorem preimage_eq_sylow_sup_center {S₁ : Sylow 2 ↥U} (N : Subgroup (UBar U)) [N.Normal]
    (hN : IsPGroup 2 N) :
    ∃ (Nhat T : Subgroup ↥U),
      Nhat = N.comap (QuotientGroup.mk' (Subgroup.center ↥U)) ∧
      Nhat = T ⊔ Subgroup.center ↥U ∧ IsPGroup 2 T ∧ T ≤ (S₁ : Subgroup ↥U) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥U)) :=
    QuotientGroup.mk'_surjective _
  let Sbar : Sylow 2 (UBar U) := Sylow.mapSurjective hsurj S₁
  have hNle : N ≤ (Sbar : Subgroup (UBar U)) := IsPGroup.le_sylow_of_normal hN Sbar
  have hNle' : N ≤ (S₁ : Subgroup ↥U).map (QuotientGroup.mk' (Subgroup.center ↥U)) := by
    rw [← Sylow.coe_mapSurjective hsurj S₁]
    exact hNle
  exact ⟨N.comap (QuotientGroup.mk' (Subgroup.center ↥U)),
    (S₁ : Subgroup ↥U) ⊓ N.comap (QuotientGroup.mk' (Subgroup.center ↥U)), rfl,
    comap_eq_inf_sup_center hNle', S₁.isPGroup'.to_le inf_le_left, inf_le_left⟩

private theorem exists_fixed_point {S₁ : Sylow 2 ↥U}
    (hodd : Odd (ptsIn V (sylowImage U S₁)).ncard)
    {T : Subgroup ↥U} (hT2 : IsPGroup 2 T)
    (hTS : T ≤ (S₁ : Subgroup ↥U)) :
    ∃ C : Subgroup G, C ∈ ptsIn V (sylowImage U S₁) ∧ C ≤ U ∧
      (∀ t ∈ T, conjSubgroup (t : G) C = C) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h𝒜 : ∀ x ∈ T.map U.subtype, ∀ C ∈ ptsIn V (sylowImage U S₁),
      C.map (MulAut.conj x).toMonoidHom ∈ ptsIn V (sylowImage U S₁) := by
    intro x hx C hC
    obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp hx
    have htS : (t : G) ∈ sylowImage U S₁ :=
      Subgroup.mem_map.mpr ⟨t, hTS htT, rfl⟩
    have hnorm : conjSubgroup (t : G) (sylowImage U S₁) = sylowImage U S₁ :=
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer htS)
    refine ⟨?_, ?_⟩
    · change conjSubgroup (t : G) C ∈ omegaSet V
      obtain ⟨k, -, hk⟩ := Tim79a.mem_omegaOf.mp hC.1
      rw [hk, CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      exact Tim79a.conjSubgroup_mem_omegaOf (H := ⊤) (Subgroup.mem_top ((t : G) * k))
    · change conjSubgroup (t : G) C ≤ sylowImage U S₁
      rw [← hnorm]
      exact Subgroup.map_mono hC.2
  have hpar := CFSG.GroupTheory.ncard_modEq_ncard_fixed (T := T.map U.subtype)
    (hT2.map U.subtype) h𝒜
  have hfixodd : Odd {C ∈ ptsIn V (sylowImage U S₁) | ∀ x ∈ T.map U.subtype,
      C.map (MulAut.conj x).toMonoidHom = C}.ncard := by
    rw [Nat.odd_iff] at hodd ⊢
    rw [← hpar]
    exact hodd
  have hfixne : {C ∈ ptsIn V (sylowImage U S₁) | ∀ x ∈ T.map U.subtype,
      C.map (MulAut.conj x).toMonoidHom = C}.Nonempty := by
    have hpos : 0 < {C ∈ ptsIn V (sylowImage U S₁) | ∀ x ∈ T.map U.subtype,
        C.map (MulAut.conj x).toMonoidHom = C}.ncard := hfixodd.pos
    rwa [Set.ncard_pos] at hpos
  obtain ⟨C, hCmem, hCfix⟩ := hfixne
  refine ⟨C, hCmem, ?_, ?_⟩
  · exact hCmem.2.trans (Subgroup.map_subtype_le (H := U) (K := (S₁ : Subgroup ↥U)))
  · intro t ht
    have h := hCfix (t : G) (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
    simpa [conjSubgroup] using h

private theorem fixed_point_inter_bot (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) {S₁ : Sylow 2 ↥U} {N : Subgroup (UBar U)} [N.Normal]
    (hN : IsPGroup 2 N) {Nhat : Subgroup ↥U}
    (hNhatdef : Nhat = N.comap (QuotientGroup.mk' (Subgroup.center ↥U)))
    {C : Subgroup G} (hCmem : C ∈ ptsIn V (sylowImage U S₁)) (hCU : C ≤ U) :
    C ⊓ Nhat.map U.subtype = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxC, hxN⟩
  by_contra hx1
  obtain ⟨n, hnN, rfl⟩ := Subgroup.mem_map.mp hxN
  have hxD : (n : G) ∈ Tim78.classD V := mem_classD_of_mem hCmem.1 hxC hx1
  have hnEU : (n : G) ∈ EU V U := ⟨hxD, C, hCmem.1, hCU, hxC⟩
  have hnbar : (n : UBar U) ∈ EBar V U := ⟨n, hnEU, rfl⟩
  have hNsol : Group.IsSolvable N := by
    have := hN.isNilpotent
    infer_instance
  rw [hNhatdef, Subgroup.mem_comap] at hnN
  exact (CFSG.Timmesfeld.Bridge.OddTransp.not_mem_of_isSolvable
    (hm.setup hS h64) (hm.meetsSq hS h64) hNsol hnbar) hnN

private theorem sylow_part_centralizes {N : Subgroup (UBar U)} [N.Normal]
    {Nhat T : Subgroup ↥U} [Nhat.Normal] (hNhat : Nhat = T ⊔ Subgroup.center ↥U)
    {C : Subgroup G} (hCfixT : ∀ t ∈ T, conjSubgroup (t : G) C = C)
    (hCN : C ⊓ Nhat.map U.subtype = ⊥) :
    ∀ t ∈ T, ∀ c : ↥U, (c : G) ∈ C → Commute (t : G) (c : G) := by
  have hTN : T ≤ Nhat := hNhat ▸ le_sup_left
  intro t htT c hcC
  have hcU : (c : G) ∈ U := c.2
  have hnorm : conjSubgroup ((t : G)⁻¹) C = C := by
    have h := congrArg (conjSubgroup ((t : G)⁻¹)) (hCfixT t htT)
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h
    exact h.symm
  have hctC : (t : G)⁻¹ * (c : G)⁻¹ * (t : G) * (c : G) ∈ C := by
    have h1 : (t : G)⁻¹ * (c : G)⁻¹ * (t : G) ∈ C := by
      have h : (MulAut.conj ((t : G)⁻¹)) ((c : G)⁻¹) ∈
          C.map (MulAut.conj ((t : G)⁻¹)).toMonoidHom :=
        Subgroup.mem_map_of_mem _ (C.inv_mem hcC)
      rw [show C.map (MulAut.conj ((t : G)⁻¹)).toMonoidHom = C from hnorm] at h
      simpa [MulAut.conj_apply] using h
    exact C.mul_mem h1 hcC
  have hctN : (t : G)⁻¹ * (c : G)⁻¹ * (t : G) * (c : G) ∈ Nhat.map U.subtype := by
    have hmemU : (c : G)⁻¹ * (t : G) * (c : G) ∈ U :=
      U.mul_mem (U.mul_mem (U.inv_mem hcU) t.2) hcU
    have hconjU : (⟨(c : G), hcU⟩ : ↥U)⁻¹ * t * (⟨(c : G), hcU⟩ : ↥U) ∈ Nhat := by
      have h := (inferInstance : Nhat.Normal).conj_mem t (hTN htT) (⟨(c : G), hcU⟩ : ↥U)⁻¹
      simpa only [inv_inv] using h
    have h2 : t⁻¹ * ((⟨(c : G), hcU⟩ : ↥U)⁻¹ * t * (⟨(c : G), hcU⟩ : ↥U)) ∈ Nhat :=
      Nhat.mul_mem (Nhat.inv_mem (hTN htT)) hconjU
    have hmemU2 : (t : G)⁻¹ * (c : G)⁻¹ * (t : G) * (c : G) ∈ U :=
      U.mul_mem (U.mul_mem (U.mul_mem (U.inv_mem t.2) (U.inv_mem hcU)) t.2) hcU
    have hX : (⟨(t : G)⁻¹ * (c : G)⁻¹ * (t : G) * (c : G), hmemU2⟩ : ↥U) =
        t⁻¹ * ((⟨(c : G), hcU⟩ : ↥U)⁻¹ * t * (⟨(c : G), hcU⟩ : ↥U)) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    exact Subgroup.mem_map.mpr
      ⟨⟨(t : G)⁻¹ * (c : G)⁻¹ * (t : G) * (c : G), hmemU2⟩, hX ▸ h2, rfl⟩
  have h1 : (t : G)⁻¹ * (c : G)⁻¹ * (t : G) * (c : G) = 1 := by
    have hbot : (t : G)⁻¹ * (c : G)⁻¹ * (t : G) * (c : G) ∈
        C ⊓ Nhat.map U.subtype := ⟨hctC, hctN⟩
    rw [hCN] at hbot
    exact Subgroup.mem_bot.mp hbot
  have h3 : (c : G)⁻¹ * (t : G) * (c : G) = (t : G) := by
    have h4 := congrArg (fun x => (t : G) * x) h1
    simpa [mul_assoc] using h4
  calc (t : G) * (c : G) = (c : G) * ((c : G)⁻¹ * (t : G) * (c : G)) := by group
    _ = (c : G) * (t : G) := by rw [h3]

private theorem preimage_centralizes_point {N : Subgroup (UBar U)} [N.Normal]
    {Nhat T : Subgroup ↥U} [Nhat.Normal] (hNhat : Nhat = T ⊔ Subgroup.center ↥U)
    {C : Subgroup G} (hCfixT : ∀ t ∈ T, conjSubgroup (t : G) C = C)
    (hCN : C ⊓ Nhat.map U.subtype = ⊥) :
    ∀ n ∈ Nhat, ∀ c : ↥U, (c : G) ∈ C → Commute (n : G) (c : G) := by
  have hTC := sylow_part_centralizes (N := N) (Nhat := Nhat) (T := T) hNhat hCfixT hCN
  intro n hn c hcC
  have hn' : n ∈ T ⊔ Subgroup.center ↥U := by rw [← hNhat]; exact hn
  obtain ⟨t, htT, z, hz, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := T) (t := Subgroup.center ↥U)).mp hn'
  have hzc : Commute (z : G) (c : G) :=
    (Subgroup.commute_subtype_iff z c).mpr (Subgroup.mem_center_iff.mp hz c).symm
  exact (hTC t htT c hcC).mul_left hzc

private theorem preimage_centralizes_EU (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) {S₁ : Sylow 2 ↥U} {N : Subgroup (UBar U)} [N.Normal]
    {Nhat T : Subgroup ↥U} [Nhat.Normal] (hNhat : Nhat = T ⊔ Subgroup.center ↥U)
    {C : Subgroup G}
    (hCmem : C ∈ ptsIn V (sylowImage U S₁)) (hCU : C ≤ U)
    (hCfixT : ∀ t ∈ T, conjSubgroup (t : G) C = C)
    (hCN : C ⊓ Nhat.map U.subtype = ⊥) :
    ∀ n ∈ Nhat, ∀ y ∈ EU V U, Commute (n : G) y := by
  have hNhatC := preimage_centralizes_point (N := N) (Nhat := Nhat) (T := T)
    hNhat hCfixT hCN
  intro n hn y hy
  have hCne : C ≠ ⊥ := by
    intro h
    have hc : Nat.card C = 1 := by rw [h, Subgroup.card_bot]
    have hq : 4 ≤ Nat.card V := hS.sec5.toRootHyp.four_le_card
    have hCV : Nat.card C = Nat.card V := by
      obtain ⟨k, -, hk⟩ := Tim79a.mem_omegaOf.mp hCmem.1
      rw [hk]
      exact card_conjSubgroup k V
    omega
  obtain ⟨c, hcne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
  let cU : ↥U := ⟨(c : G), hCU c.2⟩
  have hcC : (cU : G) ∈ C := c.2
  have hc1 : (cU : G) ≠ 1 := fun h => hcne (Subtype.ext h)
  have hcD : (cU : G) ∈ Tim78.classD V := mem_classD_of_mem hCmem.1 hcC hc1
  have hcEU : (cU : G) ∈ EU V U := ⟨hcD, C, hCmem.1, hCU, hcC⟩
  obtain ⟨u, huU, ζ, hζ, hyeq⟩ := hm.exists_conj hS h64 hcEU hy
  have hnζ : Commute (n : G) ζ :=
    Subgroup.mem_centralizer_iff.mp hζ.2 (n : G) n.2
  have hnu : Commute (n : G) ((u : G) * (cU : G) * (u : G)⁻¹) := by
    have hmemU : (u : G)⁻¹ * (n : G) * (u : G) ∈ U :=
      U.mul_mem (U.mul_mem (U.inv_mem huU) n.2) huU
    have hconjU : (⟨(u : G), huU⟩ : ↥U)⁻¹ * n * (⟨(u : G), huU⟩ : ↥U) ∈ Nhat := by
      have h := (inferInstance : Nhat.Normal).conj_mem n hn (⟨(u : G), huU⟩ : ↥U)⁻¹
      simpa only [inv_inv] using h
    have h1 : Commute ((u : G)⁻¹ * (n : G) * (u : G)) (cU : G) :=
      hNhatC _ hconjU cU hcC
    have h2 := (Commute.conj_iff (u : G)).mpr h1
    simpa [mul_assoc] using h2
  rw [hyeq]
  exact hnu.mul_right hnζ

theorem MinBad.eq_bot_of_normal (hS : Sec6Hyp M V) (h64 : OmegaM M V) (hm : MinBad V U B α β)
    {S₁ : Sylow 2 ↥U} (hodd : Odd (ptsIn V (sylowImage U S₁)).ncard)
    (N : Subgroup (UBar U)) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  classical
  obtain ⟨Nhat, T, hNhatdef, hNhat, hT2, hTS⟩ :=
    preimage_eq_sylow_sup_center N hN
  have hNhatN : Nhat.Normal := by
    rw [hNhatdef]
    infer_instance
  haveI := hNhatN
  obtain ⟨C, hCmem, hCU, hCfixT⟩ :=
    exists_fixed_point hodd hT2 hTS
  have hCN : C ⊓ Nhat.map U.subtype = ⊥ :=
    fixed_point_inter_bot hS h64 hm hN hNhatdef hCmem hCU
  have hNhat_central : ∀ n ∈ Nhat, ∀ y ∈ EU V U, Commute (n : G) y :=
    preimage_centralizes_EU (N := N) (Nhat := Nhat) (T := T) hS h64 hm hNhat hCmem hCU
      hCfixT hCN
  have hNhat_le_center : Nhat ≤ Subgroup.center ↥U := by
    intro n hn
    rw [mem_center_iff_mem_ZU]
    refine Subgroup.mem_inf.mpr ⟨n.2, ?_⟩
    change (n : G) ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hEU : EU V U ⊆ Subgroup.centralizer ({(n : G)} : Set G) := by
      intro x hx
      change x ∈ Subgroup.centralizer ({(n : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact (hNhat_central n hn x hx).eq
    have hU : U ≤ Subgroup.centralizer ({(n : G)} : Set G) := by
      intro z hz
      have hz' : z ∈ Subgroup.closure (EU V U) := by rwa [hm.closure_EU]
      exact (Subgroup.closure_le (K := Subgroup.centralizer ({(n : G)} : Set G))).mpr hEU hz'
    exact (Subgroup.mem_centralizer_iff.mp (hU hy) (n : G) (Set.mem_singleton _)).symm
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥U) y
  refine (QuotientGroup.eq_one_iff x).mpr (hNhat_le_center ?_)
  rw [hNhatdef, Subgroup.mem_comap]
  exact hy

theorem MinBad.solvableRadical_eq_bot (hS : Sec6Hyp M V) (h64 : OmegaM M V)
    (hm : MinBad V U B α β) {S₁ : Sylow 2 ↥U}
    (hodd : Odd (ptsIn V (sylowImage U S₁)).ncard) :
    CFSG.solvableRadical (UBar U) = ⊥ := by
  have hO2 : CFSG.pCore 2 (UBar U) = ⊥ :=
    hm.eq_bot_of_normal hS h64 hodd (CFSG.pCore 2 (UBar U)) CFSG.pCore_isPGroup
  have hR := CFSG.Timmesfeld.Bridge.OddTransp.solvableRadical_eq_zStar
    (hm.setup hS h64) (hm.meetsSq hS h64)
  rw [hR, Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [CFSG.Timmesfeld.Bridge.OddTransp.mem_zStar_iff] at hx
  have hcen : x ∈ Subgroup.center (UBar U) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := hx y
    rw [hO2] at h
    rw [Subgroup.mem_bot] at h
    exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  rw [hm.center_eq_bot hS h64] at hcen
  exact hcen

end CFSG.RankThree.GF2n.Tim81
