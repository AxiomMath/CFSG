module

public import CFSG.RankThree.PartTwo.Sec11.Item116
public import CFSG.RankThree.PartTwo.Sec10.Item10Std

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem Sec11Std.normalizer_le_normalizer_L (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set Ln := L.map (MulAut.conj n).toMonoidHom with hLn
  have hcn : Subgroup.centralizer ({(MulAut.conj n) c} : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    have hz : Subgroup.zpowers ((MulAut.conj n) c) = Subgroup.zpowers c := by
      have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
      rw [MonoidHom.map_zpowers] at h1
      exact h1
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
      GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, hz]
  have hLnc : Ln ∈ thetaComponentsAt 3 c := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt
    rw [thetaComponentsAt_eq_thetaComponentsIn, hcn] at h1
    exact h1
  have hLnList : Sec9.IsList1016 (Ln ⧸ aschbacherSolvableCore 3 Ln) :=
    isList1016_of_mulEquiv (Sec13.thetaQuotEquiv (MulAut.conj n) L).symm h.isList1016
  have hZ := center_eq_bot_of_isList1016 hLnList
  have h3 : 3 ∣ Nat.card Ln := by
    rw [hLn, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    have hd3 := three_dvd_card_of_isList1016 h.isList1016
    exact hd3.trans (Subgroup.card_quotient_dvd_card _)
  exact not_three_dvd_of_mem_thetaComponentsAt_ne h45 h.toHyp91 hLnc hne hZ h3

@[expose] def OutAbelian1016 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec9.IsList1016 X →
    ∀ σ τ : MulAut X, KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹)

theorem commutator_mem_innerPreimage (hOA : OutAbelian1016) {L : Subgroup G}
    (hl : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)) {n y : G}
    (hn : n ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G)) :
    n * y * n⁻¹ * y⁻¹ ∈ innerPreimage L := by
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  have hm : n * y * n⁻¹ * y⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hy)
      (Subgroup.inv_mem _ hn)) (Subgroup.inv_mem _ hy)
  refine mem_innerPreimage_iff.mpr ⟨hm, ?_⟩
  have e : (⟨n * y * n⁻¹ * y⁻¹, _⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨n, hn⟩ * ⟨y, hy⟩ * (⟨n, hn⟩ : Subgroup.normalizer (L : Set G))⁻¹ *
        (⟨y, hy⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
  change ρ _ ∈ _
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hOA _ hl _ _

theorem Sec11Std.isSylowOf_inf_L {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) : IsSylowOf 3 (R ⊓ L) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one
  have hRc := le_centralizer_of_le_normalizer_zpowers hc3 h.isSylowOf.isPGroup h.isSylowOf.le
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hCH : C ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [hC, GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.centralizer_le_normalizer _
  have hRC : IsSylowOf 3 R C := h.isSylowOf.of_le hRc hCH
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsAt
  have hR' : IsSylowOf 3 (R.subgroupOf C) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hRc, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hRC
  have h1 := Sec10.IsSylowOf.inf_of_isSubnormal hR' hL'.2.1
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C,
    Subgroup.map_inf _ _ _ C.subtype_injective, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hRc, inf_of_le_left hLC] at h1
  exact h1

theorem eq_one_of_mem_R_of_mem_theta {R L : Subgroup G} (hR : IsPGroup 3 R) {w : G}
    (hwR : w ∈ R) (hwθ : w ∈ inSubgroup (aschbacherSolvableCore 3) L) : w = 1 := by
  obtain ⟨⟨w', hw'L⟩, hw'θ, rfl⟩ := hwθ
  obtain ⟨k, hk⟩ := hR ⟨w', hwR⟩
  have hk' : (⟨w', hw'L⟩ : L) ^ 3 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  have := eq_one_of_mem_theta_of_pow_eq_one hw'θ hk'
  exact congrArg Subtype.val this

theorem Sec11Data.commute_s_x {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) :
    s * x = x * s := by
  have hx : x ∈ R ⊓ L := by
    rw [h.inf_L_eq]
    exact Subgroup.mem_zpowers x
  have hs : s ∈ R ⊓ Sec4.thetaQuotCentralizer L := by
    rw [h.inf_centralizer_eq]
    exact Subgroup.mem_zpowers s
  obtain ⟨hsN, hsθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hs.2
  have h1 := hsθ x hx.2
  have h2 : s * x * s⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have e : s * x * s⁻¹ * x⁻¹ = x * (x⁻¹ * (s * x * s⁻¹)) * x⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hx.2) _).mp h1
  have h3 : s * x * s⁻¹ * x⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hs.1 hx.1) (R.inv_mem hs.1)) (R.inv_mem hx.1)
  have h4 := eq_one_of_mem_R_of_mem_theta h.isSylowOf.isPGroup h3 h2
  calc s * x = (s * x * s⁻¹ * x⁻¹) * (x * s) := by group
    _ = x * s := by rw [h4, one_mul]

theorem Sec11Data.inf_innerPreimage_eq {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) :
    R ⊓ innerPreimage L = Subgroup.closure {s, x} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx : x ∈ R ⊓ L := by
    rw [h.inf_L_eq]
    exact Subgroup.mem_zpowers x
  have hs : s ∈ R ⊓ Sec4.thetaQuotCentralizer L := by
    rw [h.inf_centralizer_eq]
    exact Subgroup.mem_zpowers s
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  apply le_antisymm
  swap
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · refine ⟨hs.1, mem_innerPreimage_iff.mpr ⟨(Sec6.mem_thetaQuotCentralizer_iff.mp hs.2).1, ?_⟩⟩
      obtain ⟨⟨s', hs'N⟩, hs'1, hs's⟩ := hs.2
      have : (⟨s', hs'N⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨y, (Sec6.mem_thetaQuotCentralizer_iff.mp hs.2).1⟩ := Subtype.ext hs's
      rw [this] at hs'1
      exact ⟨1, by rw [map_one]; exact (MonoidHom.mem_ker.mp hs'1).symm⟩
    · exact ⟨hx.1, mem_innerPreimage_iff.mpr ⟨Subgroup.le_normalizer hx.2,
        ⟨_, (thetaQuotMulAut_compAction_of_mem L hx.2).symm⟩⟩⟩
  rintro y ⟨hyR, hyI⟩
  obtain ⟨hyN, ⟨l, hl0⟩⟩ := mem_innerPreimage_iff.mp hyI
  have hl : MulAut.conj l = ρ ⟨y, hyN⟩ := hl0
  obtain ⟨Q, hQ⟩ := h.toSec11Std.isSylowOf_inf_L
  set Q' := Q.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L)) with hQ'
  have hZ := center_eq_bot_of_isList1016 h.isList1016
  have hτQ : ∀ q ∈ (Q' : Subgroup (L ⧸ aschbacherSolvableCore 3 L)),
      ρ ⟨y, hyN⟩ q ∈ (Q' : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) := by
    intro q hq
    rw [hQ', Sylow.coe_mapSurjective] at hq ⊢
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have hq₀R : (q₀ : G) ∈ R ⊓ L := by
      rw [← hQ]
      exact ⟨q₀, hq₀, rfl⟩
    have hyq : y * (q₀ : G) * y⁻¹ ∈ R ⊓ L :=
      ⟨R.mul_mem (R.mul_mem hyR hq₀R.1) (R.inv_mem hyR),
        (Subgroup.mem_normalizer_iff.mp hyN _).mp q₀.2⟩
    rw [← hQ] at hyq
    obtain ⟨q₁, hq₁, hq₁eq⟩ := hyq
    refine ⟨q₁, hq₁, ?_⟩
    rw [QuotientGroup.mk'_apply, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    exact hq₁eq
  have hlN : l ∈ Subgroup.normalizer
      ((Q' : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Set _) := by
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    have := hτQ q hq
    rw [← hl, MulAut.conj_apply] at this
    exact this
  obtain ⟨k, hk⟩ := h.isSylowOf.isPGroup ⟨y, hyR⟩
  have hyk : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hlk : l ^ 3 ^ k = 1 := by
    have h1 : MulAut.conj (l ^ 3 ^ k) = 1 := by
      rw [map_pow, hl, ← map_pow, hyk, map_one]
    have h2 : l ^ 3 ^ k ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      have := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => φ q) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hl3 : IsPGroup 3 (Subgroup.zpowers l) := by
    rintro ⟨w, hw⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hlk, one_zpow]
  have hsup := hl3.to_sup_of_normal_right' Q'.isPGroup' (Subgroup.zpowers_le.mpr hlN)
  have heq := Q'.is_maximal' hsup le_sup_right
  have hlQ : l ∈ (Q' : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) := by
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers l)
  rw [hQ', Sylow.coe_mapSurjective] at hlQ
  obtain ⟨q₀, hq₀, rfl⟩ := hlQ
  have hq₀x : (q₀ : G) ∈ Subgroup.zpowers x := by
    rw [← h.inf_L_eq, ← hQ]
    exact ⟨q₀, hq₀, rfl⟩
  have hq₀N : (q₀ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer q₀.2
  have hu : y * (q₀ : G)⁻¹ ∈ R ⊓ Sec4.thetaQuotCentralizer L := by
    refine ⟨R.mul_mem hyR (R.inv_mem (by rw [← h.inf_L_eq] at hq₀x; exact hq₀x.1)), ?_⟩
    refine ⟨⟨y, hyN⟩ * (⟨(q₀ : G), hq₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹,
      MonoidHom.mem_ker.mpr ?_, rfl⟩
    change ρ (⟨y, hyN⟩ * (⟨(q₀ : G), hq₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹) = 1
    have hq : ρ ⟨(q₀ : G), hq₀N⟩ = MulAut.conj ((q₀ : L) : L ⧸ aschbacherSolvableCore 3 L) :=
      thetaQuotMulAut_compAction_of_mem L q₀.2
    rw [map_mul, map_inv, hq, ← hl, QuotientGroup.mk'_apply, mul_inv_cancel]
  rw [h.inf_centralizer_eq] at hu
  have e : y = (y * (q₀ : G)⁻¹) * (q₀ : G) := by group
  rw [e]
  exact Subgroup.mul_mem _
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hu)
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hq₀x)

end CFSG.RankThree.PartTwo.Sec11
