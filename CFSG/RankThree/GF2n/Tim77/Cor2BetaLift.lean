module

public import CFSG.RankThree.GF2n.Tim77.Cor2BetaPack
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaShult
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaCentral
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaStmts
public import CFSG.RankThree.GF2n.Tim77.Sec32d
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.Timmesfeld.Bridge.Asc72NoPolar

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem cor2Beta_wcl_le_normalClosure (t : G) :
    CFSG.LargeExtraspecial.S11.wcl t ≤ normalClosure ({t} : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨m, hm, -⟩
  rw [hm]
  exact (inferInstance : (normalClosure ({t} : Set G)).Normal).conj_mem t
    (subset_normalClosure (Set.mem_singleton t)) m

theorem cor2Beta_wcl_action {S : Sylow 2 G} {t : G} (hs : ShultSetup S t)
    {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) {w : G}
    (hw : w ∈ CFSG.LargeExtraspecial.S11.wcl t) :
    (∀ n ∈ N, w * n * w⁻¹ = n) ∨ (∀ n ∈ N, w * n * w⁻¹ = t * n * t⁻¹) := by
  have hNn : ∀ (g n : G), n ∈ N → g * n * g⁻¹ ∈ N := fun g n hn =>
    (inferInstance : N.Normal).conj_mem n hn g
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.sq
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    right
    intro n hn
    have h := cor2Beta_commute_mul_wclSet hs hN hy n hn
    calc y * n * y⁻¹ = t⁻¹ * ((t * y) * n * (t * y)⁻¹) * t := by group
      _ = t⁻¹ * n * t := by rw [h]; group
      _ = t * n * t⁻¹ := by rw [htinv]
  | one => left; intro n hn; simp
  | mul a b _ _ ha hb =>
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · left; intro n hn
      calc a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = n := by rw [hb n hn, ha n hn]
    · right; intro n hn
      calc a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = a * (t * n * t⁻¹) * a⁻¹ := by rw [hb n hn]
        _ = t * n * t⁻¹ := ha _ (hNn t n hn)
    · right; intro n hn
      calc a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = a * n * a⁻¹ := by rw [hb n hn]
        _ = t * n * t⁻¹ := ha n hn
    · left; intro n hn
      calc a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = a * (t * n * t⁻¹) * a⁻¹ := by rw [hb n hn]
        _ = t * (t * n * t⁻¹) * t⁻¹ := ha _ (hNn t n hn)
        _ = (t * t) * n * (t * t)⁻¹ := by group
        _ = n := by rw [hs.sq]; group
  | inv a _ ha =>
    have hmem : ∀ n ∈ N, a⁻¹ * n * a ∈ N := fun n hn => by
      simpa using hNn a⁻¹ n hn
    rcases ha with ha | ha
    · left; intro n hn
      have h1 := ha (a⁻¹ * n * a) (hmem n hn)
      have h2 : a * (a⁻¹ * n * a) * a⁻¹ = n := by group
      rw [h2] at h1
      rw [inv_inv, ← h1]
    · right; intro n hn
      have h1 := ha (a⁻¹ * n * a) (hmem n hn)
      have h2 : a * (a⁻¹ * n * a) * a⁻¹ = n := by group
      rw [h2] at h1
      calc a⁻¹ * n * a⁻¹⁻¹ = t⁻¹ * (t * (a⁻¹ * n * a) * t⁻¹) * t := by group
        _ = t⁻¹ * n * t := by rw [← h1]
        _ = t * n * t⁻¹ := by rw [htinv]

theorem cor2Beta_kleinFour_two {X : Type} [Group X] [IsKleinFour X] :
    ∃ a b : X, a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 := by
  have h4 : Nat.card X = 4 := IsKleinFour.card_four
  obtain ⟨a, ha⟩ : ∃ a : X, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton X := ⟨fun x y => by rw [hcon x, hcon y]⟩
    have := Nat.card_of_subsingleton (1 : X)
    omega
  have hord : orderOf a ∣ 2 := by
    have := Monoid.order_dvd_exponent a
    rwa [IsKleinFour.exponent_two] at this
  have hzp : Nat.card (Subgroup.zpowers a) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd two_pos hord
  obtain ⟨b, hb⟩ : ∃ b : X, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.zpowers a = ⊤ := eq_top_iff.mpr fun x _ => hcon x
    rw [htop, Subgroup.card_top] at hzp
    omega
  refine ⟨a, b, ha, fun h => hb (h ▸ Subgroup.one_mem _), fun h => hb ?_⟩
  have : b = a⁻¹ := by
    calc b = a⁻¹ * (a * b) := by group
      _ = a⁻¹ := by rw [h, mul_one]
  rw [this]
  exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)

theorem cor2Beta_component_lift {S : Sylow 2 G} {t : G} (hs : ShultSetup S t) {N : Subgroup G}
    [N.Normal] (hN : N = CFSG.Goldschmidt.oddCoreOf (normalClosure ({t} : Set G)))
    {Kb : Subgroup (G ⧸ N)}
    (hK : IsComponentOf Kb ((normalClosure ({t} : Set G)).map (QuotientGroup.mk' N)))
    (hV : ∃ V : Subgroup (G ⧸ N), V ≤ Kb ∧
        V ≤ (CFSG.LargeExtraspecial.S11.wcl t).map (QuotientGroup.mk' N) ∧ IsKleinFour ↥V ∧
        ∀ v ∈ V, v ≠ 1 → ∃ k ∈ Kb, k * v ≠ v * k) :
    ∃ K : Subgroup G, IsComponentOf K (normalClosure ({t} : Set G)) ∧
      K.map (QuotientGroup.mk' N) = Kb ∧ ∀ k ∈ K, ∀ n ∈ N, k * n = n * k := by
  classical
  set H : Subgroup G := normalClosure ({t} : Set G) with hH
  have hHn : H.Normal := inferInstance
  have hNH : N ≤ H := by rw [hN]; exact Subgroup.map_subtype_le _
  have hNodd : Odd (Nat.card N) := by
    rw [hN]; exact CFSG.CGT.Timmesfeld75.odd_card_oddCoreOf H
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hNn : ∀ (g n : G), n ∈ N → g * n * g⁻¹ ∈ N := fun g n hn =>
    (inferInstance : N.Normal).conj_mem n hn g
  obtain ⟨V, hVK, hVW, hV4, hVnc⟩ := hV
  haveI := hV4
  obtain ⟨a, b, ha1, hb1, hab1⟩ := cor2Beta_kleinFour_two (X := ↥V)
  have hVW' : ∀ v ∈ V, ∃ w ∈ CFSG.LargeExtraspecial.S11.wcl t, π w = v := fun v hv => by
    obtain ⟨w, hw, rfl⟩ := hVW hv
    exact ⟨w, hw, rfl⟩
  obtain ⟨w₁, hw₁, hπ₁⟩ := hVW' a.1 a.2
  obtain ⟨w₂, hw₂, hπ₂⟩ := hVW' b.1 b.2
  have ha1' : (a : G ⧸ N) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b : G ⧸ N) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hab1' : (a : G ⧸ N) * b ≠ 1 := fun h => hab1 (Subtype.ext h)
  obtain ⟨w, hwW, hwc, hwV, hw1⟩ : ∃ w ∈ CFSG.LargeExtraspecial.S11.wcl t,
      (∀ n ∈ N, w * n = n * w) ∧ π w ∈ V ∧ π w ≠ 1 := by
    have hcent : ∀ w' : G, (∀ n ∈ N, w' * n * w'⁻¹ = n) → ∀ n ∈ N, w' * n = n * w' :=
      fun w' h n hn => by
        calc w' * n = (w' * n * w'⁻¹) * w' := by group
          _ = n * w' := by rw [h n hn]
    rcases cor2Beta_wcl_action hs hNodd hw₁ with h1 | h1
    · exact ⟨w₁, hw₁, hcent w₁ h1, by rw [hπ₁]; exact a.2, by rw [hπ₁]; exact ha1'⟩
    rcases cor2Beta_wcl_action hs hNodd hw₂ with h2 | h2
    · exact ⟨w₂, hw₂, hcent w₂ h2, by rw [hπ₂]; exact b.2, by rw [hπ₂]; exact hb1'⟩
    refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, hcent _ fun n hn => ?_, ?_, ?_⟩
    · calc w₁ * w₂ * n * (w₁ * w₂)⁻¹ = w₁ * (w₂ * n * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * (t * n * t⁻¹) * w₁⁻¹ := by rw [h2 n hn]
        _ = t * (t * n * t⁻¹) * t⁻¹ := h1 _ (hNn t n hn)
        _ = (t * t) * n * (t * t)⁻¹ := by group
        _ = n := by rw [hs.sq]; group
    · rw [map_mul, hπ₁, hπ₂]; exact V.mul_mem a.2 b.2
    · rw [map_mul, hπ₁, hπ₂]; exact hab1'
  set Kt : Subgroup G := Kb.comap π with hKt
  set C : Subgroup G := Kt ⊓ Subgroup.centralizer (N : Set G) with hC
  have hwC : w ∈ C :=
    ⟨hVK hwV, Subgroup.mem_centralizer_iff.mpr fun n hn => (hwc n hn).symm⟩
  have hCconj : ∀ k ∈ Kt, ∀ c ∈ C, k * c * k⁻¹ ∈ C := by
    intro k hk c hc
    obtain ⟨hcK, hcc⟩ := hc
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
    · show π (k * c * k⁻¹) ∈ Kb
      rw [map_mul, map_mul, map_inv]
      exact Kb.mul_mem (Kb.mul_mem hk hcK) (Kb.inv_mem hk)
    · have h1 := Subgroup.mem_centralizer_iff.mp hcc (k⁻¹ * n * k)
        (by simpa using hNn k⁻¹ n hn)
      calc n * (k * c * k⁻¹) = k * ((k⁻¹ * n * k) * c) * k⁻¹ := by group
        _ = k * (c * (k⁻¹ * n * k)) * k⁻¹ := by rw [h1]
        _ = (k * c * k⁻¹) * n := by group
  have hπC : C.map π ≤ Kb := by
    rintro _ ⟨c, hc, rfl⟩
    exact hc.1
  have hCnorm : ((C.map π).subgroupOf Kb).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (g : G ⧸ N)
    have hπk : π k = (g : G ⧸ N) := hk
    have hkKt : k ∈ Kt := by
      show π k ∈ Kb
      rw [hπk]; exact g.2
    refine ⟨k * c * k⁻¹, hCconj k hkKt c hc, ?_⟩
    rw [map_mul, map_mul, map_inv, hπk, hcx]
    rfl
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups_assembly hK.2.2
      hCnorm with htop | hcen
  swap
  · exfalso
    obtain ⟨k, hkK, hk⟩ := hVnc (π w) hwV hw1
    have hw' : (⟨π w, hVK hwV⟩ : ↥Kb) ∈ (C.map π).subgroupOf Kb := ⟨w, hwC, rfl⟩
    have := Subgroup.mem_center_iff.mp (hcen hw') ⟨k, hkK⟩
    exact hk (congrArg Subtype.val this)
  have hCπ : C.map π = Kb := le_antisymm hπC (Subgroup.subgroupOf_eq_top.mp htop)
  have hKbperf : Group.IsPerfect ↥Kb := ⟨hK.2.2.1⟩
  have hKbq : CFSG.IsQuasisimple ↥Kb :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hK.2.2
  set K : Subgroup G := (CFSG.perfectResidual C).map C.subtype with hKdef
  have hKperf : Group.IsPerfect ↥K :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map C
  have hKC : K ≤ C := Subgroup.map_subtype_le _
  have hKmap : K.map π = Kb := by
    have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map π C
    rw [hCπ] at h
    rw [h]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.perfectResidual_map_eq_of_isPerfect hKbperf
  have hcm : (H.map π).comap π = H := by
    rw [Subgroup.comap_map_eq, hker]
    exact sup_eq_left.mpr hNH
  have hKtH : Kt ≤ H := (Subgroup.comap_mono hK.1).trans hcm.le
  have hKtsub : IsSubnormal Kt H := by
    have := CFSG.Open.IsSubnormal.comap π hK.2.1
    rwa [hcm] at this
  have hCKt : C ≤ Kt := inf_le_left
  have hCnormKt : (C.subgroupOf Kt).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hCconj g.1 g.2 x hx
  have hKnormC : (K.subgroupOf C).Normal := by
    have hchar : (CFSG.perfectResidual C).Characteristic :=
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
    have : K.subgroupOf C = CFSG.perfectResidual C :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    rw [this]
    infer_instance
  have hKsub : IsSubnormal K H :=
    IsSubnormal.step hKC hKnormC (IsSubnormal.step hCKt hCnormKt hKtsub)
  have hKcen : N.subgroupOf K ≤ Subgroup.center ↥K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hxN : (x : G) ∈ N := hx
    have hgc : (g : G) ∈ Subgroup.centralizer (N : Set G) := (hKC g.2).2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc x hxN).symm
  let f : ↥K →* ↥Kb := (π.comp K.subtype).codRestrict Kb
    (fun k => by rw [← hKmap]; exact ⟨k.1, k.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : G ⧸ N) ∈ K.map π := by rw [hKmap]; exact y.2
    obtain ⟨k, hk, hky⟩ := hy
    exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  have hfker : f.ker = N.subgroupOf K := by
    ext k
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have : π k.1 = 1 := congrArg Subtype.val h
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    · intro h
      apply Subtype.ext
      show π k.1 = 1
      rw [hπ, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr h
  let e : ↥K ⧸ N.subgroupOf K ≃* ↥Kb :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hQ : CFSG.IsQuasisimple (↥K ⧸ N.subgroupOf K) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mpr hKbq
  have hKq : CFSG.IsQuasisimple ↥K := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_extension_derived
      hKcen hQ
    have h2 : commutator ↥K = ⊤ := hKperf.commutator_eq_top
    rw [h2] at h1
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).mp h1
  refine ⟨K, ⟨hKC.trans (hCKt.trans hKtH), hKsub,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hKq⟩,
    hKmap, ?_⟩
  intro k hk n hn
  exact (Subgroup.mem_centralizer_iff.mp (hKC hk).2 n hn).symm

theorem cor2Beta_componentLift_of :
    ∀ (G : Type) [Group G] [Finite G] {S : Sylow 2 G} {t : G} (hs : ShultSetup S t)
      {N : Subgroup G} [N.Normal]
      (hN : N = CFSG.Goldschmidt.oddCoreOf (normalClosure ({t} : Set G)))
      {Kb : Subgroup (G ⧸ N)}
      (hK : IsComponentOf Kb ((normalClosure ({t} : Set G)).map (QuotientGroup.mk' N)))
      (hV : ∃ V : Subgroup (G ⧸ N), V ≤ Kb ∧
          V ≤ (CFSG.LargeExtraspecial.S11.wcl t).map (QuotientGroup.mk' N) ∧ IsKleinFour ↥V ∧
          ∀ v ∈ V, v ≠ 1 → ∃ k ∈ Kb, k * v ≠ v * k),
      ∃ K : Subgroup G, IsComponentOf K (normalClosure ({t} : Set G)) ∧
        K.map (QuotientGroup.mk' N) = Kb ∧ ∀ k ∈ K, ∀ n ∈ N, k * n = n * k :=
  fun _ _ _ _ _ hs _ _ hN _ hK hV => cor2Beta_component_lift hs hN hK hV

section LayerData

variable {X : Type} [Group X] [Finite X]

theorem cor2Beta_component_not_le_odd {N' : Subgroup X} (hodd : Odd (Nat.card N'))
    {K : Subgroup X} (hK : CFSG.IsComponent K) : ¬ K ≤ N' := by
  intro hKN
  haveI : Group.IsSolvable N' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  haveI : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hKN)
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  haveI : Group.IsPerfect K := hK.1.1
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem cor2Beta_component_commute_odd {N' : Subgroup X} [N'.Normal]
    (hodd : Odd (Nat.card N')) {K : Subgroup X} (hK : CFSG.IsComponent K) : ⁅K, N'⁆ = ⊥ := by
  haveI : Group.IsSolvable N' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact (CFSG.LocalCores.component_solvable_centralizer inferInstance
    (inferInstance : N'.Normal).isSubnormal).1 K hK

theorem cor2Beta_layer_data {N' : Subgroup X} [N'.Normal] (hodd : Odd (Nat.card N'))
    (hA : CFSG.pCore 2 (X ⧸ N') ⊔ CFSG.layer (X ⧸ N') = ⊤)
    (hL : ∀ Kq : Subgroup (X ⧸ N'), CFSG.IsComponent Kq →
      ∃ K : Subgroup X, CFSG.IsComponent K ∧ K.map (QuotientGroup.mk' N') = Kq) :
    ∃ P : Subgroup X, P.Normal ∧ (∀ x : X, ∃ p ∈ P, ∃ e ∈ CFSG.layer X, p * e = x) ∧
      (∀ e ∈ CFSG.layer X, ∀ p ∈ P, e * p = p * e) ∧ (∀ p ∈ P, ∃ a : ℕ, p ^ 2 ^ a ∈ N') := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : X →* X ⧸ N' := QuotientGroup.mk' N' with hρ
  haveI hsolv : Group.IsSolvable N' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hEN : ⁅CFSG.layer X, N'⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hsolv
      (inferInstance : N'.Normal).isSubnormal).2
  have hmapcomp : ∀ K : Subgroup X, CFSG.IsComponent K → CFSG.IsComponent (K.map ρ) :=
    fun K hK => CFSG.LocalAnalysis.ComponentInitial.component_quotient_image hK
      (cor2Beta_component_not_le_odd hodd hK)
  have hlayermap : (CFSG.layer X).map ρ ≤ CFSG.layer (X ⧸ N') := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact CFSG.LocalCores.component_le_layer (hmapcomp K hK)
  have hlayerQ : CFSG.layer (X ⧸ N') ≤ (CFSG.layer X).map ρ := by
    refine sSup_le fun Kq hKq => ?_
    obtain ⟨K, hK, rfl⟩ := hL Kq hKq
    exact Subgroup.map_mono (CFSG.LocalCores.component_le_layer hK)
  set P : Subgroup X := (CFSG.pCore 2 (X ⧸ N')).comap ρ with hP
  have hPn : P.Normal := Subgroup.Normal.comap CFSG.pCore_normal ρ
  have hFle : CFSG.pCore 2 (X ⧸ N') ≤ CFSG.fittingSubgroup (X ⧸ N') :=
    (CFSG.LocalCores.fitting_characteristic).2.2 _ CFSG.pCore_normal
      (CFSG.pCore_isPGroup.isNilpotent)
  have hcomm : ⁅CFSG.layer (X ⧸ N'), CFSG.fittingSubgroup (X ⧸ N')⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact CFSG.LocalCores.fitting_layer_commute
  have h1 : ⁅CFSG.layer X, P⁆ ≤ N' := by
    refine Subgroup.commutator_le.mpr fun e he p hp => ?_
    rw [← QuotientGroup.ker_mk' N', MonoidHom.mem_ker, map_commutatorElement]
    have hm := Subgroup.commutator_mem_commutator (hlayermap (Subgroup.mem_map_of_mem ρ he))
      (hFle hp)
    rw [hcomm, Subgroup.mem_bot] at hm
    exact hm
  have h2 : ⁅CFSG.layer X, P⁆ = ⊥ := by
    refine CFSG.LocalCores.perfect_double_commutator CFSG.LocalCores.layer_isPerfect
      (le_bot_iff.mp ?_)
    calc ⁅⁅CFSG.layer X, P⁆, CFSG.layer X⁆ ≤ ⁅N', CFSG.layer X⁆ :=
          Subgroup.commutator_mono h1 le_rfl
      _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hEN
  refine ⟨P, hPn, ?_, ?_, ?_⟩
  · intro x
    have hx : ρ x ∈ CFSG.pCore 2 (X ⧸ N') ⊔ CFSG.layer (X ⧸ N') := hA ▸ Subgroup.mem_top _
    obtain ⟨p, hp, l, hl, hpl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨e, he, rfl⟩ := hlayerQ hl
    refine ⟨x * e⁻¹, ?_, e, he, by group⟩
    show ρ (x * e⁻¹) ∈ CFSG.pCore 2 (X ⧸ N')
    rw [map_mul, map_inv, ← hpl, mul_inv_cancel_right]
    exact hp
  · intro e he p hp
    have := Subgroup.commutator_mem_commutator he hp
    rw [h2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · intro p hp
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X ⧸ N')) ⟨ρ p, hp⟩
    refine ⟨a, ?_⟩
    have : (ρ p) ^ 2 ^ a = 1 := congrArg Subtype.val ha
    rw [← map_pow] at this
    rwa [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this

end LayerData

omit [Finite G] in
theorem cor2Beta_isComponentOf_iff {H K : Subgroup G} (hKH : K ≤ H) :
    IsComponentOf K H ↔ CFSG.IsComponent (K.subgroupOf H) :=
  CFSG.Assembly.isComponentOf_iff_open.symm.trans
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKH)

omit [Finite G] in
theorem cor2Beta_layer_map_subtype (H : Subgroup G) :
    (CFSG.layer ↥H).map H.subtype = sSup {K : Subgroup G | IsComponentOf K H} := by
  have hset : Subgroup.map H.subtype '' {K' : Subgroup ↥H | CFSG.IsComponent K'} =
      {K : Subgroup G | IsComponentOf K H} := by
    ext K
    constructor
    · rintro ⟨K', hK', rfl⟩
      have hle : K'.map H.subtype ≤ H := Subgroup.map_subtype_le K'
      refine (cor2Beta_isComponentOf_iff hle).mpr ?_
      have : (K'.map H.subtype).subgroupOf H = K' :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective K'
      rwa [this]
    · intro hK
      exact ⟨K.subgroupOf H, (cor2Beta_isComponentOf_iff hK.1).mp hK,
        Subgroup.map_subgroupOf_eq_of_le hK.1⟩
  rw [← hset, sSup_image]
  exact (Subgroup.gc_map_comap H.subtype).l_sSup

omit [Finite G] in
theorem cor2Beta_layer_normal (H : Subgroup G) [H.Normal] :
    (sSup {K : Subgroup G | IsComponentOf K H}).Normal := by
  rw [← cor2Beta_layer_map_subtype H]
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨e, he, rfl⟩ := hx
  let φ : MulAut ↥H := MulAut.conjNormal g
  have hchar : (CFSG.layer ↥H).Characteristic := CFSG.LocalCores.layer_characteristic
  have hmem : e ∈ (CFSG.layer ↥H).comap φ.toMonoidHom := by
    rw [hchar.fixed φ]
    exact he
  refine ⟨φ e, Subgroup.mem_comap.1 hmem, ?_⟩
  simp [φ]

omit [Finite G] in
theorem cor2Beta_isComponentOf_map_injective {Q Q' : Type} [Group Q] [Group Q'] (ψ : Q →* Q')
    (hψ : Function.Injective ψ) {Kq : Subgroup Q} (hK : CFSG.IsComponent Kq) :
    IsComponentOf (Kq.map ψ) ψ.range := by
  have hle : Kq.map ψ ≤ ψ.range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  refine (cor2Beta_isComponentOf_iff hle).mpr ?_
  let e : Q ≃* ψ.range := MonoidHom.ofInjective hψ
  have h := CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent e hK
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem cor2Beta_exists_psi (H N : Subgroup G) [N.Normal]
    (hN : N = CFSG.Goldschmidt.oddCoreOf H) :
    ∃ ψ : (↥H ⧸ CFSG.Open.goldschmidtOddCore ↥H) →* (G ⧸ N), Function.Injective ψ ∧
      ψ.range = H.map (QuotientGroup.mk' N) ∧
      ψ.comp (QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore ↥H)) =
        (QuotientGroup.mk' N).comp H.subtype := by
  have hNH : ∀ x : ↥H, x ∈ CFSG.Open.goldschmidtOddCore ↥H ↔ (x : G) ∈ N := by
    intro x
    rw [hN]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
  have hle : CFSG.Open.goldschmidtOddCore ↥H ≤
      ((QuotientGroup.mk' N).comp H.subtype).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr ((hNH x).mp hx)
  let ψ := QuotientGroup.lift (CFSG.Open.goldschmidtOddCore ↥H)
    ((QuotientGroup.mk' N).comp H.subtype) hle
  have hψ : ∀ x : ↥H, ψ (x : ↥H ⧸ CFSG.Open.goldschmidtOddCore ↥H) = (x : G ⧸ N) :=
    fun x => rfl
  refine ⟨ψ, ?_, ?_, rfl⟩
  · rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hψ, QuotientGroup.eq_one_iff] at hq
    exact (QuotientGroup.eq_one_iff _).mpr ((hNH x).mpr hq)
  · ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨((⟨x, hx⟩ : ↥H) : ↥H ⧸ CFSG.Open.goldschmidtOddCore ↥H), rfl⟩

theorem cor2Beta_hasNormalTwoComplement_of_split {Y N Z : Subgroup G} [N.Normal]
    [IsMulCommutative ↥Z] (hNodd : Odd (Nat.card N)) (hNY : N ≤ Y) (hZY : Z ≤ Y)
    (hZc : ∀ z ∈ Z, ∀ y ∈ Y, z * y = y * z) (hZN : ∀ z ∈ Z, ∀ n ∈ N, z * n = n * z)
    (hsplit : ∀ y ∈ Y, ∃ o ∈ Y, ∃ z ∈ Z, (∃ a : ℕ, o ^ 2 ^ a ∈ N) ∧ y = o * z) :
    HasNormalTwoComplement ↥Y := by
  classical
  obtain ⟨Oz, hOz, hOzodd, hOzn, hOzp⟩ := cor2Beta_hasNormalTwoComplement_of_comm (Q := Z)
  set Zo : Subgroup G := Oz.map Z.subtype with hZo
  have hZoZ : Zo ≤ Z := Subgroup.map_subtype_le _
  have hZoodd : Odd (Nat.card Zo) := by
    rw [hZo, Subgroup.card_map_of_injective Z.subtype_injective]
    exact hOzodd
  have hZopow : ∀ z ∈ Z, ∃ b : ℕ, z ^ 2 ^ b ∈ Zo := by
    intro z hz
    obtain ⟨b, hb⟩ := hOzp (QuotientGroup.mk (⟨z, hz⟩ : ↥Z))
    refine ⟨b, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hb
    exact ⟨(⟨z, hz⟩ : ↥Z) ^ 2 ^ b, hb, by simp⟩
  set O' : Subgroup G := N ⊔ Zo with hO'
  have hO'Y : O' ≤ Y := sup_le hNY (hZoZ.trans hZY)
  have hO'mem : ∀ x ∈ O', ∃ n ∈ N, ∃ z ∈ Zo, n * z = x := fun x hx =>
    Subgroup.mem_sup_of_normal_left.mp hx
  have hodd : Odd (Nat.card O') := by
    by_contra hnodd
    have h2 : 2 ∣ Nat.card O' := by
      rw [Nat.not_odd_iff_even] at hnodd
      exact even_iff_two_dvd.mp hnodd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥O') 2 h2
    obtain ⟨n, hn, z, hz, hnz⟩ := hO'mem (u : G) u.2
    have hno : Odd (orderOf n) :=
      Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hn)
    have hzo : Odd (orderOf z) :=
      Odd.of_dvd_nat hZoodd (Subgroup.orderOf_dvd_natCard Zo hz)
    have hc : Commute n z := (hZN z (hZoZ hz) n hn).symm
    have hdvd : orderOf (n * z) ∣ Nat.lcm (orderOf n) (orderOf z) := hc.orderOf_mul_dvd_lcm
    have hu2 : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    rw [← hnz] at hu2
    rw [hu2] at hdvd
    have h3 : 2 ∣ orderOf n * orderOf z := hdvd.trans (Nat.lcm_dvd_mul _ _)
    have h4 := Nat.odd_iff.mp (hno.mul hzo)
    generalize orderOf n * orderOf z = m at h3 h4
    omega
  have hnormal : (O'.subgroupOf Y).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨n, hn, z, hz, hnz⟩ := hO'mem _ hx
    have hzg : z * (g : G) = (g : G) * z := hZc z (hZoZ hz) g g.2
    have e : (g : G) * (x : G) * (g : G)⁻¹ = ((g : G) * n * (g : G)⁻¹) * z := by
      rw [← hnz]
      calc (g : G) * (n * z) * (g : G)⁻¹
          = ((g : G) * n * (g : G)⁻¹) * ((g : G) * z * (g : G)⁻¹) := by group
        _ = ((g : G) * n * (g : G)⁻¹) * z := by
            rw [show (g : G) * z * (g : G)⁻¹ = z from by rw [← hzg]; group]
    show (g : G) * (x : G) * (g : G)⁻¹ ∈ O'
    rw [e]
    exact Subgroup.mul_mem_sup ((inferInstance : N.Normal).conj_mem n hn g) hz
  have hpgroup : IsPGroup 2 (↥Y ⧸ O'.subgroupOf Y) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨o, hoY, z, hzZ, ⟨a, ha⟩, hyoz⟩ := hsplit y y.2
    obtain ⟨b, hb⟩ := hZopow z hzZ
    refine ⟨a + b, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hcomm : Commute o z := (hZc z hzZ o hoY).symm
    have hy' : ((y ^ 2 ^ (a + b) : ↥Y) : G) = o ^ 2 ^ (a + b) * z ^ 2 ^ (a + b) := by
      rw [Subgroup.coe_pow, hyoz, hcomm.mul_pow]
    rw [hy']
    refine Subgroup.mul_mem_sup ?_ ?_
    · rw [pow_add, pow_mul]
      exact N.pow_mem ha _
    · have : 2 ^ (a + b) = 2 ^ b * 2 ^ a := by rw [add_comm, pow_add]
      rw [this, pow_mul]
      exact Zo.pow_mem hb _
  refine ⟨O'.subgroupOf Y, hnormal, ?_, hnormal, hpgroup⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO'Y).toEquiv]
  exact hodd

theorem cor2Beta_quotient_center_equiv {A B : Type} [Group A] [Group B] [Group.IsPerfect A]
    (f : A →* B) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center A) :
    Nonempty (A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B) := by
  let g : A →* B ⧸ Subgroup.center B := (QuotientGroup.mk' (Subgroup.center B)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgker : g.ker = Subgroup.center A := by
    rw [← CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel f hf hker]
    ext x
    simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

omit [Finite G] in
theorem cor2Beta_isCoveringOf_component {H N K : Subgroup G} [N.Normal]
    (hK : IsComponentOf K H) (hKN : ∀ k ∈ K, ∀ n ∈ N, k * n = n * k)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (↥(K.map (QuotientGroup.mk' N)) ⧸ Subgroup.center ↥(K.map (QuotientGroup.mk' N)))) :
    IsCoveringOf Tim77Cor2BetaList ↥K := by
  haveI : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  refine ⟨hK.2.2.1, Subgroup.center ↥K, le_rfl, inferInstance, ?_⟩
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hker : (π.subgroupMap K).ker ≤ Subgroup.center ↥K := by
    rw [Subgroup.ker_subgroupMap, hπ, QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hKN g.1 g.2 x.1 hx)
  obtain ⟨e⟩ := cor2Beta_quotient_center_equiv (π.subgroupMap K) (π.subgroupMap_surjective K)
    hker
  exact sec32d_beta_of_bender (CFSG.Timmesfeld.Bridge.Asc72.isBenderGroup_of_mulEquiv e hB)

theorem cor2Beta_E_shape_of_components {H : Subgroup G}
    (hnormal : ∀ K : Subgroup G, IsComponentOf K H → (K.subgroupOf H).Normal)
    (hcov : ∀ K : Subgroup G, IsComponentOf K H → IsCoveringOf Tim77Cor2BetaList ↥K) :
    ∃ (r : ℕ) (K : Fin r → Subgroup G),
      (∀ i, K i ≤ sSup {K : Subgroup G | IsComponentOf K H}) ∧
      (∀ i, ((K i).subgroupOf H).Normal) ∧
      (∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) ∧
      (⨆ i, K i) = sSup {K : Subgroup G | IsComponentOf K H} ∧
      ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(K i) := by
  classical
  obtain ⟨r, ⟨e⟩⟩ : ∃ r : ℕ, Nonempty (Fin r ≃ {K : Subgroup G // IsComponentOf K H}) := by
    haveI : Finite {K : Subgroup G // IsComponentOf K H} := inferInstance
    obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin {K : Subgroup G // IsComponentOf K H}
    exact ⟨r, ⟨e.symm⟩⟩
  refine ⟨r, fun i => (e i).1, fun i => le_sSup (e i).2, fun i => hnormal _ (e i).2, ?_, ?_,
    fun i => hcov _ (e i).2⟩
  · intro i j hij x hx y hy
    exact cor2Beta_components_commute (e i).2 (e j).2
      (fun h => hij (e.injective (Subtype.ext h))) x hx y hy
  · refine le_antisymm (iSup_le fun i => le_sSup (e i).2) (sSup_le fun K hK => ?_)
    calc K = (e (e.symm ⟨K, hK⟩)).1 := by simp
      _ ≤ ⨆ i, (e i).1 := le_iSup (fun i => (e i).1) _

theorem cor2Beta_decomp_of_layer_data {H N : Subgroup G} [hHn : H.Normal] [N.Normal]
    (hNH : N ≤ H) (hNodd : Odd (Nat.card N))
    (hF1 : ∀ K : Subgroup G, IsComponentOf K H → ∀ k ∈ K, ∀ n ∈ N, k * n = n * k)
    (hBender : ∀ K : Subgroup G, IsComponentOf K H → CFSG.BenderSuzuki.IsBenderGroup
      (↥(K.map (QuotientGroup.mk' N)) ⧸ Subgroup.center ↥(K.map (QuotientGroup.mk' N))))
    (hEn : (sSup {K : Subgroup G | IsComponentOf K H}).Normal)
    (P : Subgroup G) (hPH : P ≤ H)
    (hP1 : ∀ h ∈ H, ∃ p ∈ P, ∃ e ∈ sSup {K : Subgroup G | IsComponentOf K H}, p * e = h)
    (hP2 : ∀ e ∈ sSup {K : Subgroup G | IsComponentOf K H}, ∀ p ∈ P, e * p = p * e)
    (hP3 : ∀ p ∈ P, ∃ a : ℕ, p ^ 2 ^ a ∈ N) :
    ∃ E Y : Subgroup G, Cor2BetaDecomp H E Y := by
  classical
  set E : Subgroup G := sSup {K : Subgroup G | IsComponentOf K H} with hE
  set Y : Subgroup G := Subgroup.centralizer (E : Set G) ⊓ H with hY
  have hEH : E ≤ H := sSup_le fun K hK => hK.1
  have hKE : ∀ K, IsComponentOf K H → K ≤ E := fun K hK => le_sSup hK
  have hEN : ∀ e ∈ E, ∀ n ∈ N, e * n = n * e := by
    have : E ≤ Subgroup.centralizer (N : Set G) := sSup_le fun K hK k hk =>
      Subgroup.mem_centralizer_iff.mpr fun n hn => (hF1 K hK k hk n hn).symm
    intro e he n hn
    exact (Subgroup.mem_centralizer_iff.mp (this he) n hn).symm
  have hYc : ∀ y ∈ Y, ∀ e ∈ E, e * y = y * e := fun y hy e he =>
    Subgroup.mem_centralizer_iff.mp hy.1 e he
  have hPY : P ≤ Y := fun p hp =>
    ⟨Subgroup.mem_centralizer_iff.mpr fun e he => hP2 e he p hp, hPH hp⟩
  have hNY : N ≤ Y := fun n hn =>
    ⟨Subgroup.mem_centralizer_iff.mpr fun e he => hEN e he n hn, hNH hn⟩
  have hYn : Y.Normal := by
    refine ⟨fun y hy g =>
      ⟨Subgroup.mem_centralizer_iff.mpr fun e he => ?_, hHn.conj_mem y hy.2 g⟩⟩
    have he' : g⁻¹ * e * g ∈ E := by simpa using hEn.conj_mem e he g⁻¹
    have h1 := hYc y hy _ he'
    calc e * (g * y * g⁻¹) = g * ((g⁻¹ * e * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
      _ = (g * y * g⁻¹) * e := by group
  have hsup : E ⊔ Y = H := by
    refine le_antisymm (sup_le hEH inf_le_right) fun h hh => ?_
    obtain ⟨p, hp, e, he, rfl⟩ := hP1 h hh
    rw [← hP2 e he p hp]
    exact Subgroup.mul_mem_sup he (hPY hp)
  haveI : IsMulCommutative ↥(E ⊓ Y) :=
    ⟨⟨fun a b => Subtype.ext (hYc b.1 b.2.2 a.1 a.2.1)⟩⟩
  have hcompl : HasNormalTwoComplement ↥Y := by
    refine cor2Beta_hasNormalTwoComplement_of_split (Z := E ⊓ Y) hNodd hNY inf_le_right
      (fun z hz y hy => hYc y hy z hz.1) (fun z hz n hn => hEN z hz.1 n hn) ?_
    intro y hy
    obtain ⟨p, hp, e, he, hpe⟩ := hP1 y hy.2
    refine ⟨p, hPY hp, e, ⟨he, ?_⟩, hP3 p hp, hpe.symm⟩
    have : e = p⁻¹ * y := by rw [← hpe]; group
    rw [this]
    exact Y.mul_mem (Y.inv_mem (hPY hp)) hy
  have hEnorm : ∀ K, IsComponentOf K H → E ≤ normalizer (K : Set G) := by
    intro K hK
    refine sSup_le fun L hL => ?_
    by_cases hLK : L = K
    · rw [hLK]
      exact Subgroup.le_normalizer
    · exact cor2Beta_le_normalizer_of_commute fun a ha b hb =>
        cor2Beta_components_commute hK hL (fun h => hLK h.symm) a ha b hb
  have hHnorm : ∀ K, IsComponentOf K H → H ≤ normalizer (K : Set G) := by
    intro K hK h hh
    obtain ⟨p, hp, e, he, rfl⟩ := hP1 h hh
    have hPK : P ≤ normalizer (K : Set G) :=
      cor2Beta_le_normalizer_of_commute fun a ha b hb => hP2 a (hKE K hK ha) b hb
    exact Subgroup.mul_mem _ (hPK hp) (hEnorm K hK he)
  refine ⟨E, Y, ⟨hEH, rfl, inf_le_right, hsup, fun e he y hy => hYc y hy e he, hEn, hYn, hcompl,
    ?_⟩⟩
  obtain ⟨r, K, h1, h2, h3, h4, h5⟩ := cor2Beta_E_shape_of_components
    (fun K hK => (Subgroup.normal_subgroupOf_iff_le_normalizer hK.1).mpr (hHnorm K hK))
    (fun K hK => cor2Beta_isCoveringOf_component hK (hF1 K hK) (hBender K hK))
  exact ⟨r, K, h1, h2, h3, h4, h5⟩

theorem cor2Beta_goldschmidt_A (hGold : Goldschmidt1974) {S : Sylow 2 G} {t : G}
    (hs : ShultSetup S t) :
    CFSG.pCore 2 (↥(normalClosure ({t} : Set G)) ⧸
        CFSG.Open.goldschmidtOddCore ↥(normalClosure ({t} : Set G))) ⊔
      CFSG.layer (↥(normalClosure ({t} : Set G)) ⧸
        CFSG.Open.goldschmidtOddCore ↥(normalClosure ({t} : Set G))) = ⊤ := by
  obtain ⟨hWS, hcl⟩ :=
    CFSG.LargeExtraspecial.S11.wcl_stronglyClosed S hs.mem hs.central hs.abelian
  obtain ⟨ha, -, -⟩ := hGold G S (CFSG.LargeExtraspecial.S11.wcl t) hWS hs.abelian hcl
  have hMH : Subgroup.normalClosure ((CFSG.LargeExtraspecial.S11.wcl t : Subgroup G) : Set G) =
      normalClosure ({t} : Set G) := by
    refine le_antisymm (Subgroup.normalClosure_le_normal ?_)
      (Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr
        (CFSG.LargeExtraspecial.S11.self_mem_wcl t)))
    exact fun x hx => cor2Beta_wcl_le_normalClosure t hx
  have hlayer : ∀ (Q : Type) [Group Q], CFSG.layer Q = CFSG.Open.goldschmidtLayer Q :=
    fun Q _ => CFSG.WholeGroup.layerOf_congr CFSG.isComponent_iff_open
  have key : ∀ M : Subgroup G, M = normalClosure ({t} : Set G) →
      CFSG.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ⊔
        CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) = ⊤ →
      CFSG.pCore 2 (↥(normalClosure ({t} : Set G)) ⧸
          CFSG.Open.goldschmidtOddCore ↥(normalClosure ({t} : Set G))) ⊔
        CFSG.layer (↥(normalClosure ({t} : Set G)) ⧸
          CFSG.Open.goldschmidtOddCore ↥(normalClosure ({t} : Set G))) = ⊤ := by
    intro M hM h
    subst hM
    rw [hlayer]
    exact h
  exact key _ hMH ha

theorem cor2Beta_shultDecomp_of (hGold : Goldschmidt1974) (hB4 : Cor2BetaComponentDataStatement)
    : Cor2BetaShultDecompStatement := by
  have hB6 := cor2Beta_componentLift_of
  intro G _ _ S t hs
  classical
  set H : Subgroup G := normalClosure ({t} : Set G) with hH
  haveI hHn : H.Normal := inferInstance
  set N : Subgroup G := CFSG.Goldschmidt.oddCoreOf H with hNdef
  haveI hNn : N.Normal := oddCoreOf_normal hHn
  have hNH : N ≤ H := Subgroup.map_subtype_le _
  have hNodd : Odd (Nat.card N) := odd_card_oddCoreOf H
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  set N' : Subgroup ↥H := CFSG.Open.goldschmidtOddCore ↥H with hN'
  have hN'odd : Odd (Nat.card N') := odd_card_goldschmidtOddCore ↥H
  set ρ : ↥H →* ↥H ⧸ N' := QuotientGroup.mk' N' with hρ
  have hA := cor2Beta_goldschmidt_A hGold hs
  obtain ⟨ψ, hψinj, hrange, hψcomp⟩ := cor2Beta_exists_psi H N rfl
  have hmapψ : ∀ K : Subgroup G, K ≤ H → ((K.subgroupOf H).map ρ).map ψ = K.map π := by
    intro K hK
    rw [Subgroup.map_map, hψcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hK]
  have hKbar : ∀ K : Subgroup G, IsComponentOf K H → IsComponentOf (K.map π) (H.map π) := by
    intro K hK
    have h1 : CFSG.IsComponent ((K.subgroupOf H).map ρ) :=
      CFSG.LocalAnalysis.ComponentInitial.component_quotient_image
        ((cor2Beta_isComponentOf_iff hK.1).mp hK)
        (cor2Beta_component_not_le_odd hN'odd ((cor2Beta_isComponentOf_iff hK.1).mp hK))
    have h2 := cor2Beta_isComponentOf_map_injective ψ hψinj h1
    rwa [hmapψ K hK.1, hrange] at h2
  have hL : ∀ Kq : Subgroup (↥H ⧸ N'), CFSG.IsComponent Kq →
      ∃ K : Subgroup ↥H, CFSG.IsComponent K ∧ K.map ρ = Kq := by
    intro Kq hKq
    have hKb : IsComponentOf (Kq.map ψ) (H.map π) := by
      have := cor2Beta_isComponentOf_map_injective ψ hψinj hKq
      rwa [hrange] at this
    obtain ⟨-, hV⟩ := @hB4 G _ _ S t hs N hNn rfl (Kq.map ψ) hKb
    obtain ⟨K, hK, hKmap, -⟩ := @hB6 G _ _ S t hs N hNn rfl (Kq.map ψ) hKb hV
    refine ⟨K.subgroupOf H, (cor2Beta_isComponentOf_iff hK.1).mp hK, ?_⟩
    apply Subgroup.map_injective hψinj
    rw [hmapψ K hK.1, hKmap]
  obtain ⟨P, -, hP1, hP2, hP3⟩ := cor2Beta_layer_data hN'odd hA hL
  have hEmap := cor2Beta_layer_map_subtype H
  refine cor2Beta_decomp_of_layer_data (N := N) hNH hNodd ?_ ?_ (cor2Beta_layer_normal H)
    (P.map H.subtype) (Subgroup.map_subtype_le P) ?_ ?_ ?_
  ·
    intro K hK k hk n hn
    obtain ⟨n', hn', rfl⟩ := hn
    have h := cor2Beta_component_commute_odd hN'odd ((cor2Beta_isComponentOf_iff hK.1).mp hK)
    have hmem := Subgroup.commutator_mem_commutator
      (show (⟨k, hK.1 hk⟩ : ↥H) ∈ K.subgroupOf H from hk) hn'
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact congrArg Subtype.val hmem
  · intro K hK
    exact (@hB4 G _ _ S t hs N hNn rfl (K.map π) (hKbar K hK)).1
  · intro h hh
    obtain ⟨p, hp, e, he, hpe⟩ := hP1 ⟨h, hh⟩
    refine ⟨p, ⟨p, hp, rfl⟩, e, ?_, congrArg Subtype.val hpe⟩
    rw [← hEmap]
    exact ⟨e, he, rfl⟩
  · intro e he p hp
    rw [← hEmap] at he
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨p', hp', rfl⟩ := hp
    exact congrArg Subtype.val (hP2 e' he' p' hp')
  · intro p hp
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨a, ha⟩ := hP3 p' hp'
    exact ⟨a, ⟨_, ha, rfl⟩⟩

end CFSG.RankThree.GF2n.Tim77
