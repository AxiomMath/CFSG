module

public import CFSG.RankThree.GF2n.Tim79aSpBraidModel
public import CFSG.RankThree.GF2n.Tim79aSec34Summand

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic

structure OppFacts (K : Type) [Group K] (A : Subgroup K) : Prop where
  braid : ∀ g : K, ¬ (∀ a ∈ A, ∀ b ∈ conjSub A g, a * b = b * a) →
    ∀ a ∈ A, a ≠ 1 → ∃ b ∈ conjSub A g, orderOf (a * b) = 3
  meet : ∀ g : K, ¬ (∀ a ∈ A, ∀ b ∈ conjSub A g, a * b = b * a) →
    conjSub A g ⊓ Subgroup.normalizer (A : Set K) = ⊥

theorem spOppStatement_of_models : ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSp K A → OppFacts K A := by
  have hB := spBraidModel_holds
  have hM := spOppMeetModel_holds
  rintro K _ _ A ⟨f, Δ, hf, hΔ, hA⟩
  obtain ⟨n, Φ, a, T, hΦ, -, hT, rfl⟩ := exists_isTransGroup_of_transvConclusionSp hf hΔ hA
  have hnc : ∀ g' : StatedSp n (GaloisField 2 f), ¬ (∀ x ∈ T.map Φ, ∀ y ∈ conjSub (T.map Φ) (Φ g'),
      x * y = y * x) → spForm a (SpExtras.mat n (GaloisField 2 f) g' *ᵥ a) ≠ 0 := by
    intro g' h h0
    apply h
    rw [conjSub_map]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := (hT.commuting (hT.conjSub g') h0) x hx y hy
    rw [← map_mul, ← map_mul, this.eq]
  refine ⟨fun g hg x hx hx1 => ?_, fun g hg => ?_⟩
  · obtain ⟨g', rfl⟩ := hΦ.2 g
    obtain ⟨t, ht, rfl⟩ := hx
    have h0 := hnc g' hg
    have ht1 : t ≠ 1 := fun h => hx1 (by rw [h, map_one])
    obtain ⟨t', ht', hord⟩ := hB n (GaloisField 2 f) a _ T _ hT (hT.conjSub g') h0 t ht ht1
    refine ⟨Φ t', ?_, ?_⟩
    · rw [conjSub_map]; exact Subgroup.mem_map_of_mem Φ ht'
    · rw [← map_mul, orderOf_injective Φ hΦ.1, hord]
  · obtain ⟨g', rfl⟩ := hΦ.2 g
    have h0 := hnc g' hg
    rw [conjSub_map, ← Subgroup.map_normalizer_eq_of_bijective T hΦ,
      ← Subgroup.map_inf_eq _ _ Φ hΦ.1,
      hM n (GaloisField 2 f) a _ _ _ hT (hT.conjSub g') h0, Subgroup.map_bot]

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Sec3Setup

variable {M V Q P H : Subgroup G} [Finite G]

theorem not_commuting_tilde (hs : Sec3Setup M V Q P H) {y : ↥(xOf V H)}
    (hyc : (y : G) ∉ Ycomm V H) :
    ¬ ∀ a ∈ VZ V H, ∀ b ∈ conjSub (VZ V H) (xToZ hs.setup.mc.toMinCex.V_le_H y),
      a * b = b * a := by
  intro hall
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  apply hyc
  have hcomm := hc.commute_conj_of_commute_tilde (x₁ := 1) (x₂ := y) (by
    intro a ha b hb
    rw [map_one, conjSubgroup_one] at ha
    exact hall a ha b hb)
  refine ⟨y.2, fun u hu w hw => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr
    (hcomm u (by rw [OneMemClass.coe_one, conjSubgroup_one]; exact hu) w hw)]
  exact (wOf V H).one_mem

theorem classicalRootSp_tilde (h3 : Sec23Three V H) : ClassicalRootSp (XbarZ V H) (VZ V H) := by
  obtain ⟨f, hf, -, hT⟩ := h3
  exact ⟨f, rootClassZ V H, hf, hT, VZ_mem_rootClassZ V H⟩

end Sec3Setup

theorem sec34OppMeetStatement_of_sp : Sec34OppMeetStatement := by
  have hS := spOppStatement_of_models
  intro G _ _ M V Q P H hs h3 y hy hyc v hv hvN
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hyH : y ∈ H := xOf_le_H hVH hy
  have hF := hS _ _ (Sec3Setup.classicalRootSp_tilde h3)
  set yy : ↥(xOf V H) := ⟨y, hy⟩ with hyy
  have hmeet := hF.meet (xToZ hVH yy) (hs.not_commuting_tilde (y := yy) hyc)
  have hvX : v ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hyH) hv
  set vv : ↥(xOf V H) := ⟨v, hvX⟩ with hvv
  have h1 : xToZ hVH vv ∈ conjSub (VZ V H) (xToZ hVH yy) := by
    have : xToZ hVH vv ∈ imgZ V H (conjSubgroup y V) := by
      exact ⟨xToXbar hVH vv, Subgroup.mem_subgroupOf.mpr
        (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) vv, hv, rfl⟩), rfl⟩
    rw [imgZ_conj hVH yy] at this
    exact this
  have h2 : xToZ hVH vv ∈ Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := by
    apply mem_normalizer_of_conjSubgroup_eq
    have := imgZ_conj hVH vv
    rw [mem_normalizer_iff_conjSubgroup_eq.mp hvN, ← VZ_eq_imgZ] at this
    exact this.symm
  have h3' : xToZ hVH vv ∈ conjSub (VZ V H) (xToZ hVH yy) ⊓
      Subgroup.normalizer (VZ V H : Set (XbarZ V H)) := ⟨h1, h2⟩
  rw [hmeet, Subgroup.mem_bot] at h3'
  have hcen : xToXbar hVH vv ∈ Subgroup.center (Xbar V H) := (QuotientGroup.eq_one_iff _).mp h3'
  by_contra hvW
  have hv1 : v ≠ 1 := fun h => hvW (h ▸ (wOf V H).one_mem)
  have hD : xToXbar hVH vv ∈ Dy V H :=
    mem_dbarOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) vv,
      ⟨hv1, conjSubgroup y V, conjSubgroup_mem_omegaOf hyH, hv⟩, hvW, rfl⟩
  exact hs.setup.data.noncentral _ hD hcen

namespace Sec3Setup

variable {M V Q P H : Subgroup G} [Finite G]

theorem exists_lift_VZ (hs : Sec3Setup M V Q P H) {t : XbarZ V H} (ht : t ∈ VZ V H) :
    ∃ aa : ↥(xOf V H), (aa : G) ∈ V ∧ xToZ hs.setup.mc.toMinCex.V_le_H aa = t := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  obtain ⟨bc, hbc, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨x, hx, hxb⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hbc)
  have hxX : (x : G) ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hx
  refine ⟨⟨(x : G), hxX⟩, hx, ?_⟩
  show projZ V H (xToXbar hc.V_le_H ⟨(x : G), hxX⟩) = projZ V H bc
  congr 1
  apply Subtype.ext
  rw [coe_xToXbar]
  exact hxb

theorem exists_lift_conj_VZ (hs : Sec3Setup M V Q P H) {y : G} (hy : y ∈ xOf V H)
    {t : XbarZ V H}
    (ht : t ∈ conjSub (VZ V H) (xToZ hs.setup.mc.toMinCex.V_le_H ⟨y, hy⟩)) :
    ∃ bb : ↥(xOf V H), (bb : G) ∈ conjSubgroup y V ∧
      xToZ hs.setup.mc.toMinCex.V_le_H bb = t := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hyH : y ∈ H := xOf_le_H hVH hy
  have ht' : t ∈ imgZ V H (conjSubgroup y V) := by rw [imgZ_conj hVH ⟨y, hy⟩]; exact ht
  obtain ⟨bc, hbc, rfl⟩ := Subgroup.mem_map.mp ht'
  obtain ⟨x, hx, hxb⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hbc)
  have hxX : (x : G) ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hyH) hx
  refine ⟨⟨(x : G), hxX⟩, hx, ?_⟩
  show projZ V H (xToXbar hVH ⟨(x : G), hxX⟩) = projZ V H bc
  congr 1
  apply Subtype.ext
  rw [coe_xToXbar]
  exact hxb

theorem mem_Dy_of_mem_conj (hs : Sec3Setup M V Q P H) {y : G} (hy : y ∈ H) (bb : ↥(xOf V H))
    (hb : (bb : G) ∈ conjSubgroup y V) (hbW : (bb : G) ∉ wOf V H) :
    xToXbar hs.setup.mc.toMinCex.V_le_H bb ∈ Dy V H :=
  mem_dbarOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hs.setup.mc.toMinCex.V_le_H) bb,
    ⟨fun h => hbW (h ▸ (wOf V H).one_mem), conjSubgroup y V, conjSubgroup_mem_omegaOf hy, hb⟩,
    hbW, rfl⟩

theorem pow_three_mem_wOf (hs : Sec3Setup M V Q P H) {y : G} (hy : y ∈ xOf V H)
    (aa bb : ↥(xOf V H)) (ha : (aa : G) ∈ V) (haW : (aa : G) ∉ wOf V H)
    (hb : (bb : G) ∈ conjSubgroup y V) (hbW : (bb : G) ∉ wOf V H)
    (hord : orderOf (xToZ hs.setup.mc.toMinCex.V_le_H aa *
      xToZ hs.setup.mc.toMinCex.V_le_H bb) = 3) :
    ((aa : G) * (bb : G)) ^ 3 ∈ wOf V H := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hyH : y ∈ H := xOf_le_H hVH hy
  have ha1 : (aa : G) ≠ 1 := fun h => haW (h ▸ (wOf V H).one_mem)
  have haD : xToXbar hVH aa ∈ Dy V H :=
    mem_dbarOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) aa,
      ⟨ha1, V, V_mem_omegaOf V H, ha⟩, haW, rfl⟩
  have hbD := hs.mem_Dy_of_mem_conj hyH bb hb hbW
  have haa1 : xToXbar hVH aa * xToXbar hVH aa = 1 := by
    rw [← map_mul]
    have : aa * aa = 1 := Subtype.ext (hc.elemAb.mul_self_eq_one ha)
    rw [this, map_one]
  have hbsq : bb * bb = 1 := by
    apply Subtype.ext
    have h1 := hc.elemAb.mul_self_eq_one (mem_conjSubgroup.mp hb)
    show (bb : G) * (bb : G) = 1
    calc (bb : G) * (bb : G) = y * ((y⁻¹ * (bb : G) * y) * (y⁻¹ * (bb : G) * y)) * y⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hbb1 : xToXbar hVH bb * xToXbar hVH bb = 1 := by
    rw [← map_mul, hbsq, map_one]
  set g : Xbar V H := xToXbar hVH aa * xToXbar hVH bb with hg
  have hpg : projZ V H g = xToZ hVH aa * xToZ hVH bb := by
    rw [hg, map_mul]; rfl
  have hdvd : 3 ∣ orderOf g := by
    have := orderOf_map_dvd (projZ V H) g
    rwa [hpg, hord] at this
  have hcen3 : g ^ 3 ∈ Subgroup.center (Xbar V H) := by
    apply (QuotientGroup.eq_one_iff _).mp
    show projZ V H (g ^ 3) = 1
    rw [map_pow, hpg, ← hord]
    exact pow_orderOf_eq_one _
  have hg6 : g ^ 6 = 1 := by
    set ā := xToXbar hVH aa with hā
    set b' := xToXbar hVH bb with hb'
    have hāinv : ā⁻¹ = ā := inv_eq_of_mul_eq_one_right haa1
    have hb'inv : b'⁻¹ = b' := inv_eq_of_mul_eq_one_right hbb1
    have h1 : ā * g * ā⁻¹ = g⁻¹ := by
      rw [hg, mul_inv_rev, hb'inv, hāinv]
      calc ā * (ā * b') * ā = (ā * ā) * b' * ā := by group
        _ = b' * ā := by rw [haa1, one_mul]
    have h2 : ā * g ^ 3 * ā⁻¹ = g ^ 3 := by
      rw [Subgroup.mem_center_iff.mp hcen3 ā]
      group
    have h3' : ā * g ^ 3 * ā⁻¹ = (g⁻¹) ^ 3 := by
      rw [← h1, conj_pow]
    rw [h2, inv_pow] at h3'
    calc g ^ 6 = g ^ 3 * g ^ 3 := by rw [← pow_add]
      _ = 1 := by
        nth_rewrite 1 [h3']
        exact inv_mul_cancel _
  have hk6 : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one hg6
  have hk : orderOf g = 3 := by
    have hroot : orderOf g = 2 ∨ orderOf g = 4 ∨ Odd (orderOf g) :=
      hs.setup.data.root.2.1 _ haD _ hbD
    obtain ⟨m, hm⟩ := hdvd
    have hm2 : m ∣ 2 := by
      have : 3 * m ∣ 3 * 2 := by rw [← hm]; exact hk6
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h1 | h2
    · rw [hm, h1]
    · exfalso
      have h6 : orderOf g = 6 := by rw [hm, h2]
      rcases hroot with h | h | h
      · rw [h6] at h; exact absurd h (by norm_num)
      · rw [h6] at h; exact absurd h (by norm_num)
      · rw [h6, Nat.odd_iff] at h; exact absurd h (by norm_num)
  have hg3 : g ^ 3 = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
  have hs3 : xToXbar hVH ((aa * bb) ^ 3) = 1 := by
    rw [map_pow, map_mul]; exact hg3
  have := (piBar_eq_one_iff (V := V) (H := H)
    (Subgroup.inclusion (xOf_le_H hVH) ((aa * bb) ^ 3))).1 (by
    have h := congrArg Subtype.val hs3
    rw [coe_xToXbar] at h
    exact h)
  simpa using this

end Sec3Setup

theorem sec34BraidStatement_of_sp : Sec34BraidStatement := by
  have hS := spOppStatement_of_models
  intro G _ _ M V Q P H hs h3 y hy hyc a ha haW
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hF := hS _ _ (Sec3Setup.classicalRootSp_tilde h3)
  have hnc := hs.not_commuting_tilde (y := ⟨y, hy⟩) hyc
  have haX : a ∈ xOf V H := le_xOf (V_mem_omegaOf V H) ha
  set aa : ↥(xOf V H) := ⟨a, haX⟩ with haa
  have ha1 : a ≠ 1 := fun h => haW (h ▸ (wOf V H).one_mem)
  have haD : xToXbar hVH aa ∈ Dy V H :=
    mem_dbarOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) aa,
      ⟨ha1, V, V_mem_omegaOf V H, ha⟩, haW, rfl⟩
  have hãV : xToZ hVH aa ∈ VZ V H :=
    ⟨xToXbar hVH aa, Subgroup.mem_subgroupOf.mpr
      (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) aa, ha, rfl⟩), rfl⟩
  have hã1 : xToZ hVH aa ≠ 1 := fun h =>
    hs.setup.data.noncentral _ haD ((QuotientGroup.eq_one_iff _).mp h)
  obtain ⟨_, hbt, hord⟩ := hF.braid (xToZ hVH ⟨y, hy⟩) hnc _ hãV hã1
  obtain ⟨bb, hbb, rfl⟩ := hs.exists_lift_conj_VZ hy hbt
  have hbW : (bb : G) ∉ wOf V H := by
    intro hbW'
    have h1 : piBar V H (Subgroup.inclusion (xOf_le_H hVH) bb) = 1 := (piBar_eq_one_iff _).2 hbW'
    have h2 : xToXbar hVH bb = 1 := Subtype.ext h1
    have h6 : xToZ hVH bb = 1 := by rw [xToZ_apply, h2, map_one]
    rw [h6, mul_one] at hord
    have haa1 : xToZ hVH aa * xToZ hVH aa = 1 := by
      rw [← map_mul]
      have : aa * aa = 1 := Subtype.ext (hc.elemAb.mul_self_eq_one ha)
      rw [this, map_one]
    have h5 : orderOf (xToZ hVH aa) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact haa1)
    rw [hord] at h5
    omega
  exact ⟨(bb : G), hbb, hbW, hs.pow_three_mem_wOf hy aa bb ha haW hbb hbW hord⟩

theorem sec34SummandStatement_of_line (hLine : Sec34LineStatement) : Sec34SummandStatement :=
  sec34SummandStatement_of_parts hLine
    sec34BraidStatement_of_sp
    (sec34OppMeetStatement_of_sp
      )

end CFSG.RankThree.GF2n.Tim79a
