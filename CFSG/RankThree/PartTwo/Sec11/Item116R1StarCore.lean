module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1StarSec
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionRep
public import CFSG.RankThree.PartOne.S9.QD32.RigidityMain
public import CFSG.RankThree.PartTwo.Sec5.Bender.Core
public import CFSG.RankThree.OddKernel.SimpleQuotient

public section

section

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OddCore37
  CFSG.RankThree.PartTwo.Sec3 Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem mem_inSubgroup_center_iff {G : Type*} [Group G] (U : Subgroup G) (g : G) :
    g ∈ inSubgroup Subgroup.center U ↔ ∃ h : U, h ∈ Subgroup.center U ∧ (h : G) = g := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

theorem five_star_core {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D R : Subgroup G} [D.Normal] {w : G} (hw5 : IsPGroup 5 (zpowers w)) (hD : IsPGroup p D)
    (hDexp : ∀ d ∈ D, d ^ p = 1) (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hR2 : IsPGroup 2 R)
    (hwR : zpowers w ≤ normalizer (R : Set G)) (hRw : ⁅R, zpowers w⁆ = R) (hR1 : R ≠ ⊥)
    (hfaith : R ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hfix : ∀ r ∈ R, r ≠ 1 → CFSG.pRank p ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) :
    Nonempty (↥R ≃* QD32) ∧
      (∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ inSubgroup Subgroup.center R →
        r ∈ inSubgroup Subgroup.center R) ∧
      (inSubgroup frattini D).relIndex D = p ^ 4 ∧ 3 ≤ CFSG.pRank p ↥D := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have h5pr : (5 : ℕ).Prime := Nat.prime_five
  have hnD : ∀ g : G, g ∈ normalizer (D : Set G) := fun g =>
    (Subgroup.le_normalizer_of_normal : (⊤ : Subgroup G) ≤ normalizer (D : Set G)) (Subgroup.mem_top g)
  have hRD : R ≤ normalizer (D : Set G) := fun g _ => hnD g
  have hwD : w ∈ normalizer (D : Set G) := hnD w
  have hwA : zpowers w ≤ normalizer (D : Set G) := fun g _ => hnD g
  obtain ⟨T, hTR, hTcrit, hAT, hTA, hidem, hAnorm, hle⟩ :=
    exists_critical_commutator_pow hw5 hR2 hwR hRw hR1
  have hWR : ⁅T, zpowers w⁆ ≤ R := hle.trans hTR
  have hWfaith : ⁅T, zpowers w⁆ ⊓ centralizer (D : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hWR).trans hfaith.le)
  have hfix' : ∀ u ∈ ⁅T, zpowers w⁆, u ≠ 1 →
      CFSG.Assembly.pRank p (D ⊓ centralizer ({u} : Set G)) ≤ 2 := fun u hu hu1 => by
    rw [r116_assembly_pRank_eq]
    exact hfix u (hWR hu) hu1
  obtain ⟨U₀, hU₀W, hxU₀, hU₀X, hU₀1, hU₀ext, hU₀card, hU₀fpf⟩ :=
    exists_extraspecial_below hp hp2 (q := 5) h5pr (by norm_num) rfl (P := D) (U := ⁅T, zpowers w⁆)
      (X := zpowers w) (x := w) hD (hR2.to_le hWR) rfl hw5 hidem hTA (hWR.trans hRD) hwA hWfaith hfix'
  have hU₀R : U₀ ≤ R := hU₀W.trans hWR
  have hU₀D : U₀ ≤ normalizer (D : Set G) := hU₀R.trans hRD
  obtain ⟨k, hk⟩ := hw5 ⟨w, Subgroup.mem_zpowers w⟩
  have hwk : w ^ (5 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  let γ : MulAut ↥U₀ := U₀.normalizerMonoidHom ⟨w, hxU₀⟩
  have hγapp : ∀ s : U₀, ((γ s : U₀) : G) = w * s * w⁻¹ := fun s =>
    normalizerMonoidHom_apply_apply_coe _ _ _
  have hγq : γ ^ (5 ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨w, hxU₀⟩ : normalizer (U₀ : Set G)) ^ (5 ^ k) = 1 := Subtype.ext (by simpa using hwk)
    rw [this, map_one]
  have hγfpf : ∀ s : U₀, γ s * s⁻¹ ∈ Subgroup.center U₀ → s ∈ Subgroup.center U₀ := by
    intro s hs
    have h1 : w * (s : G) * w⁻¹ * (s : G)⁻¹ ∈ inSubgroup Subgroup.center U₀ := by
      refine (mem_inSubgroup_center_iff U₀ _).2 ⟨γ s * s⁻¹, hs, ?_⟩
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hγapp]
    have h2 := hU₀fpf (s : G) s.2 h1
    obtain ⟨h, hh, hhs⟩ := (mem_inSubgroup_center_iff U₀ _).1 h2
    have : h = s := Subtype.ext hhs
    rwa [this] at hh
  have hU₀qd : Nonempty (↥U₀ ≃* QD32) := qd32_of_fpf hU₀ext hU₀card γ hγq hγfpf
  have hγ5 : γ ^ 5 = 1 := pow_five_eq_one_of_fpf hU₀ext hU₀card γ hγq hγfpf
  have hDp : IsPGroup p ↥D := hD
  have hDexp' : ∀ d : ↥D, d ^ p = 1 := fun d =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp d d.2, Subgroup.coe_one])
  have hclassD : commutator ↥D ≤ Subgroup.center ↥D := commutator_le_center_of_forall hDcl
  let ρ : ↥U₀ →* MulAut ↥D := conjAction D U₀ hU₀D
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (u : G) ∈ centralizer (D : Set G) := mem_ker_conjAction.mp hu
    have h2 : (u : G) ∈ R ⊓ centralizer (D : Set G) := ⟨hU₀R u.2, h1⟩
    rw [hfaith, mem_bot] at h2
    exact Subtype.ext h2
  have hfixρ : ∀ s : ↥U₀, s ≠ 1 →
      CFSG.pRank p ↥(CFSG.RankThree.PartOne.FixedRank36.fixedSub (ρ s)) ≤ 2 := by
    intro s hs
    have hs1 : (s : G) ≠ 1 := fun h => hs (Subtype.ext h)
    exact (pRank_fixedSubgroupOf_le hp.one_lt (le_refl D) s).trans
      (hfix' (s : G) (hU₀W s.2) hs1)
  obtain ⟨hcardfrat, hrank3⟩ := ext32_module_data hp2 hDp hDexp' hclassD hU₀ext hU₀card γ hγ5
    hγfpf ρ hρ hfixρ
  have hrel : (inSubgroup frattini D).relIndex D = p ^ 4 := by
    rw [CFSG.RankThree.PartOne.Torsion37.relIndex_inSubgroup_frattini_eq_card]
    exact hcardfrat
  have hcyc := isCyclic_inf_centralizer_of_qd32 hp hp2 hD hrel hR2 hfaith hU₀R hU₀qd
  have hodd : Odd (Nat.card ↥(zpowers w)) := by
    obtain ⟨n, hn⟩ := hw5.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  have hRU : R = U₀ :=
    criticalQuaternionDihedralOvergroupRigidity G R (zpowers w) T U₀ hR2 hodd hwR hRw hTR hTcrit
      (hU₀W.trans hle) (Subgroup.zpowers_le.mpr hxU₀) hU₀qd hcyc
  subst hRU
  exact ⟨hU₀qd, hU₀fpf, hrel, hrank3⟩

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OddCore37
  CFSG.RankThree.PartTwo.Sec3 Subgroup
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec16.Proof166Res2 (eq_one_of_inr_mem_centralizer)

namespace CFSG.RankThree.PartTwo.Sec11

theorem h16_mem_inSubgroup_center_iff {G : Type} [Group G] (U : Subgroup G) (g : G) :
    g ∈ inSubgroup Subgroup.center U ↔ g ∈ U ∧ ∀ h ∈ U, h * g = g * h := by
  unfold inSubgroup
  constructor
  · intro hg
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hg
    subst hzg
    refine ⟨z.2, fun k hk => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
  · rintro ⟨hg, hcomm⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩,
      Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hcomm k.1 k.2), rfl⟩

theorem h16_range_inl_isPGroup {G : Type} [Group G] (p : ℕ) (D : Subgroup G)
    (hD : IsPGroup p D) :
    IsPGroup p ((SemidirectProduct.inl :
      ↥D →* (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D)).range) := by
  rw [MonoidHom.range_eq_map]
  exact (hD.to_subgroup ⊤).map _

theorem h16_range_inl_normal {G : Type} [Group G] (D : Subgroup G) :
    ((SemidirectProduct.inl :
      ↥D →* (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D)).range).Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

theorem five_star_core_hom {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D R : Subgroup G} {w : G} (hw5 : IsPGroup 5 (zpowers w)) (hD : IsPGroup p D)
    (hDexp : ∀ d ∈ D, d ^ p = 1) (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hR2 : IsPGroup 2 R) (hRD : R ≤ normalizer (D : Set G)) (hwD : w ∈ normalizer (D : Set G))
    (hwR : zpowers w ≤ normalizer (R : Set G)) (hRw : ⁅R, zpowers w⁆ = R)
    (hR1 : ¬ R ≤ Subgroup.centralizer (D : Set G))
    (hfix : ∀ r ∈ R, r ≠ 1 → CFSG.pRank p ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) :
    R ⊓ Subgroup.centralizer (D : Set G) = ⊥ ∧ Nonempty (↥R ≃* QD32) ∧
      (∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ inSubgroup Subgroup.center R →
        r ∈ inSubgroup Subgroup.center R) ∧
      (inSubgroup frattini D).relIndex D = p ^ 4 ∧ 3 ≤ CFSG.pRank p ↥D := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hDexp' : ∀ d : ↥D, d ^ p = 1 := fun d =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp d d.2, Subgroup.coe_one])
  have hDcl' : ∀ a b c : ↥D, ⁅a, b⁆ * c = c * ⁅a, b⁆ := fun a b c =>
    Subtype.ext (hDcl a a.2 b b.2 c c.2)
  let φ : normalizer (D : Set G) →* MulAut ↥D := D.normalizerMonoidHom
  let f : normalizer (D : Set G) →* (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D) :=
    SemidirectProduct.inr.comp φ
  have hfm : ∀ m : normalizer (D : Set G), f m = SemidirectProduct.inr (φ m) := fun m => rfl
  have hfφ : ∀ m : normalizer (D : Set G), f m = 1 → φ m = 1 := fun m h =>
    SemidirectProduct.inr_injective (h.trans (map_one _).symm)
  have hcent : ∀ m : normalizer (D : Set G), φ m = 1 →
      (m : G) ∈ Subgroup.centralizer (D : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : φ m ⟨d, hd⟩ = ⟨d, hd⟩ := by simp [hm]
    have h2 : (m : G) * d * (m : G)⁻¹ = d :=
      (e1c_phi_apply D m ⟨d, hd⟩).symm.trans (congrArg Subtype.val h1)
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  obtain ⟨Rh, hRh⟩ : ∃ Rh : Subgroup (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D),
      Rh = (R.subgroupOf (normalizer (D : Set G))).map f := ⟨_, rfl⟩
  obtain ⟨Dh, hDh⟩ : ∃ Dh : Subgroup (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D),
      Dh = (SemidirectProduct.inl :
        ↥D →* (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D)).range := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ↥R →* (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D),
      F = f.comp (Subgroup.inclusion hRD) := ⟨_, rfl⟩
  have hFapp : ∀ r : ↥R, F r = f ⟨r.1, hRD r.2⟩ := fun r => by
    subst hF
    rfl
  let xN : normalizer (D : Set G) := ⟨w, hwD⟩
  have hZ : (zpowers w).comap (normalizer (D : Set G)).subtype = zpowers xN := by
    ext n
    rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, Subtype.ext hj⟩
    · rintro ⟨j, hj⟩
      subst hj
      exact ⟨j, rfl⟩
  have hX5 : IsPGroup 5 (zpowers xN) := by
    rw [← hZ]
    exact hw5.comap_of_injective (normalizer (D : Set G)).subtype
      (normalizer (D : Set G)).subtype_injective
  have hŴ5 : IsPGroup 5 (zpowers (f xN)) := by
    rw [← MonoidHom.map_zpowers]
    exact hX5.map f
  have hU2 : IsPGroup 2 (R.subgroupOf (normalizer (D : Set G))) :=
    hR2.comap_of_injective (normalizer (D : Set G)).subtype
      (normalizer (D : Set G)).subtype_injective
  have hRh2 : IsPGroup 2 Rh := by
    rw [hRh]
    exact hU2.map f
  have hDhp : IsPGroup p Dh := by
    rw [hDh]
    exact h16_range_inl_isPGroup p D hD
  haveI hDhn : Dh.Normal := by
    rw [hDh]
    exact h16_range_inl_normal D
  have hDexpĜ : ∀ d ∈ Dh, d ^ p = 1 := by
    intro d hd
    rw [hDh] at hd
    obtain ⟨d', rfl⟩ := MonoidHom.mem_range.mp hd
    rw [← map_pow, hDexp' d', map_one]
  have hDclĜ : ∀ a ∈ Dh, ∀ b ∈ Dh, ∀ c ∈ Dh, ⁅a, b⁆ * c = c * ⁅a, b⁆ := by
    intro a ha b hb c hc
    rw [hDh] at ha hb hc
    obtain ⟨a', rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨b', rfl⟩ := MonoidHom.mem_range.mp hb
    obtain ⟨c', rfl⟩ := MonoidHom.mem_range.mp hc
    rw [← map_commutatorElement, ← map_mul, ← map_mul, hDcl' a' b' c']
  have hRDn : R ⊓ normalizer (D : Set G) = R := inf_eq_left.mpr hRD
  have hUx : ⁅R.subgroupOf (normalizer (D : Set G)), zpowers xN⁆ =
      R.subgroupOf (normalizer (D : Set G)) := by
    apply Subgroup.map_injective (f := (normalizer (D : Set G)).subtype)
      (normalizer (D : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, hRDn, MonoidHom.map_zpowers]
    exact hRw
  have hRw' : ⁅Rh, zpowers (f xN)⁆ = Rh := by
    rw [hRh, ← MonoidHom.map_zpowers, ← Subgroup.map_commutator, hUx]
  have hwn : w ∈ normalizer (R : Set G) := hwR (Subgroup.mem_zpowers w)
  have hxN : xN ∈ normalizer ((R.subgroupOf (normalizer (D : Set G)) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hwn (h : G)
  have hRwN : zpowers (f xN) ≤ normalizer ((Rh : Subgroup _) : Set _) := by
    rw [hRh, Subgroup.zpowers_le]
    exact Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f hxN)
  have hRhne : Rh ≠ ⊥ := by
    obtain ⟨r, hr, hrC⟩ := SetLike.not_le_iff_exists.mp hR1
    intro h0
    have hfr : f ⟨r, hRD hr⟩ ≠ 1 := fun h1 => hrC (hcent ⟨r, hRD hr⟩ (hfφ _ h1))
    apply hfr
    have hmem : f ⟨r, hRD hr⟩ ∈ Rh := by
      rw [hRh]
      exact Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hr)
    rw [h0, Subgroup.mem_bot] at hmem
    exact hmem
  have hfaithĜ : Rh ⊓ Subgroup.centralizer ((Dh : Subgroup _) : Set _) = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg, hgC⟩
    rw [hRh] at hg
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hg
    rw [hDh] at hgC
    have hnC : (SemidirectProduct.inr (φ m) : ↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D) ∈
        Subgroup.centralizer (((SemidirectProduct.inl :
          ↥D →* (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D)).range : Subgroup _) : Set _) := hgC
    rw [Subgroup.mem_bot, hfm, eq_one_of_inr_mem_centralizer hnC, map_one]
  have hfixĜ : ∀ r ∈ Rh, r ≠ 1 →
      CFSG.pRank p ↥(Dh ⊓ Subgroup.centralizer
        ({r} : Set (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D))) ≤ 2 := by
    intro r hr hr1
    rw [hRh] at hr
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hr
    have hm1 : φ m ≠ 1 := fun h1 => hr1 (by rw [hfm, h1, map_one])
    have hmR : (m : G) ∈ R := Subgroup.mem_subgroupOf.mp hm
    have hm1G : (m : G) ≠ 1 := fun h1 => hm1 (by rw [show m = 1 from Subtype.ext h1, map_one])
    have hloc := hfix (m : G) hmR hm1G
    rw [SectionRank.pRank_coe_eq_openPRank] at hloc
    have hmapD : (MonoidHom.eqLocus (φ m).toMonoidHom (MonoidHom.id ↥D)).map D.subtype ≤
        D ⊓ Subgroup.centralizer ({(m : G)} : Set G) := by
      rintro g hg
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
      have he' : (φ m).toMonoidHom e = (MonoidHom.id ↥D) e := he
      have h3 : (m : G) * (e : G) * (m : G)⁻¹ = (e : G) := congrArg Subtype.val he'
      refine Subgroup.mem_inf.mpr ⟨e.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    have hle1 := SectionRank.pRank_le_map hp.one_lt D.subtype D.subtype_injective
      (MonoidHom.eqLocus (φ m).toMonoidHom (MonoidHom.id ↥D))
    have hle2 := SectionRank.pRank_mono hp.one_lt hmapD
    have hE : CFSG.Assembly.pRank p (MonoidHom.eqLocus (φ m).toMonoidHom (MonoidHom.id ↥D)) ≤ 2 :=
      (hle1.trans hle2).trans hloc
    rw [hDh, ← r116_assembly_pRank_eq]
    exact (r116_pRank_le p hp.one_lt (φ m)).trans hE
  obtain ⟨hNe, hfpfĜ, hrelĜ, hrankĜ⟩ := five_star_core hp hp2 (D := Dh) (R := Rh) (w := f xN)
    hŴ5 hDhp hDexpĜ hDclĜ hRh2 hRwN hRw' hRhne hfaithĜ hfixĜ
  obtain ⟨eĜ⟩ := hNe
  have hinl : Function.Injective
      (SemidirectProduct.inl : ↥D →* (↥D ⋊[MonoidHom.id (MulAut ↥D)] MulAut ↥D)) :=
    SemidirectProduct.inl_injective
  let eD : ↥D ≃* ↥Dh := (MonoidHom.ofInjective hinl).trans (MulEquiv.subgroupCongr hDh.symm)
  have hrankD : 3 ≤ CFSG.pRank p ↥D :=
    hrankĜ.trans (CFSG.RankThree.OddKernel.pRank_le_of_injective hp.one_lt eD.symm.toMonoidHom
      eD.symm.injective)
  have hrelD : (inSubgroup frattini D).relIndex D = p ^ 4 := by
    rw [CFSG.RankThree.PartOne.Torsion37.relIndex_inSubgroup_frattini_eq_card] at hrelĜ ⊢
    rw [← hrelĜ]
    exact Nat.card_congr (QuotientGroup.congr (frattini ↥D) (frattini ↥Dh) eD
      (CFSG.RankThree.PartOne.Torsion37.frattini_map_mulEquiv eD)).toEquiv
  have hfaithR : R ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgR, hgC⟩
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hloc := hfix g hgR hg1
    have hDC : D ⊓ Subgroup.centralizer ({g} : Set G) = D := by
      apply inf_eq_left.mpr
      intro d hd
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hgC) d hd
    rw [hDC] at hloc
    have h32 : 3 ≤ 2 := hrankD.trans hloc
    omega
  have hFrange : F.range = Rh := by
    rw [hRh, hF]
    ext g
    constructor
    · rintro ⟨r, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨r.1, hRD r.2⟩, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
    · intro hg
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hg
      exact MonoidHom.mem_range.mpr ⟨⟨m.1, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hFapp] at ha
    have hcen := hcent ⟨a.1, hRD a.2⟩ (hfφ _ ha)
    have hmem : (a : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) :=
      Subgroup.mem_inf.mpr ⟨a.2, hcen⟩
    rw [hfaithR, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have eR : ↥R ≃* ↥Rh := (MonoidHom.ofInjective hFinj).trans (MulEquiv.subgroupCongr hFrange)
  have hfpf : ∀ r ∈ R, w * r * w⁻¹ * r⁻¹ ∈ inSubgroup Subgroup.center R →
      r ∈ inSubgroup Subgroup.center R := by
    intro r hr hcr
    rw [h16_mem_inSubgroup_center_iff] at hcr ⊢
    obtain ⟨hcR, hcc⟩ := hcr
    refine ⟨hr, ?_⟩
    let rN : normalizer (D : Set G) := ⟨r, hRD hr⟩
    have hrU : rN ∈ R.subgroupOf (normalizer (D : Set G)) := Subgroup.mem_subgroupOf.mpr hr
    have hcU : xN * rN * xN⁻¹ * rN⁻¹ ∈ R.subgroupOf (normalizer (D : Set G)) :=
      Subgroup.mem_subgroupOf.mpr hcR
    have hcomm_hyp : f xN * f rN * (f xN)⁻¹ * (f rN)⁻¹ ∈ inSubgroup Subgroup.center Rh := by
      rw [h16_mem_inSubgroup_center_iff]
      have hfc : f xN * f rN * (f xN)⁻¹ * (f rN)⁻¹ = f (xN * rN * xN⁻¹ * rN⁻¹) := by
        simp only [map_mul, map_inv]
      rw [hfc, hRh]
      refine ⟨Subgroup.mem_map_of_mem f hcU, ?_⟩
      intro k hk
      obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hcc k'.1 (Subgroup.mem_subgroupOf.mp hk')
    have hfr := hfpfĜ (f rN) (by rw [hRh]; exact Subgroup.mem_map_of_mem f hrU) hcomm_hyp
    rw [h16_mem_inSubgroup_center_iff] at hfr
    obtain ⟨-, hcomm⟩ := hfr
    intro h hh
    let hN : normalizer (D : Set G) := ⟨h, hRD hh⟩
    have key := hcomm (f hN)
      (by rw [hRh]; exact Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hh))
    have key2 : F ⟨h * r, R.mul_mem hh hr⟩ = F ⟨r * h, R.mul_mem hr hh⟩ := by
      rw [hFapp, hFapp]
      show f (hN * rN) = f (rN * hN)
      rw [map_mul, map_mul]
      exact key
    exact congrArg Subtype.val (hFinj key2)
  exact ⟨hfaithR, ⟨eR.trans eĜ⟩, hfpf, hrelD, hrankD⟩

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem isExtraspecial_of_qd32 {R : Type*} [Group R] (e : R ≃* QD32) :
    IsExtraspecialPGroup 2 R ∧ Nat.card R = 32 := by
  refine ⟨CFSG.RankThree.PartOne.Lifting36.isExtraspecialPGroup_of_mulEquiv e.symm
    (CFSG.RankThree.GroupTheory.SteinbergBY.quaternion_dihedral_extraspecial_involution_generation
      |>.2.1), ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.GroupTheory.card_QD32

theorem five_star_prop :
    ∀ (G : Type) [Group G] [Finite G], FiveLocalRankHyp G →
      ∀ (θ S : Subgroup G), Group.IsSolvable θ → ¬ 3 ∣ Nat.card θ →
        inSubgroup (CFSG.pCore 2) θ = ⊥ → S ≤ θ → IsPGroup 2 S → FiveStarAt θ S := by
  intro G _ _ hloc θ S hθs hθ3 hO2 hSθ hS2 w hw5 hwθ hwS hnt
  classical
  have hXS : zpowers w ≤ normalizer (S : Set G) := Subgroup.zpowers_le.mpr hwS
  have hRS : fiveStarR S w ≤ S := fiveStarR_le hwS
  have hRθ : fiveStarR S w ≤ θ := hRS.trans hSθ
  have hR2 : IsPGroup 2 (fiveStarR S w) := hS2.to_le hRS
  have hR1 : fiveStarR S w ≠ ⊥ := by
    obtain ⟨s, hs, hne⟩ := hnt
    intro hbot
    apply hne
    have h1 : ⁅s⁻¹, w⁆ ∈ fiveStarR S w :=
      Subgroup.commutator_mem_commutator (inv_mem hs) (Subgroup.mem_zpowers w)
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h1
    simp only [inv_inv] at h1
    calc w * s * w⁻¹ = s * (s⁻¹ * w * s * w⁻¹) := by group
      _ = s := by rw [h1, mul_one]
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers w)) (Nat.card S) := by
    obtain ⟨k, hk⟩ := hw5.exists_card_eq
    obtain ⟨m, hm⟩ := hS2.exists_card_eq
    rw [hk, hm]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have hRX : ⁅fiveStarR S w, Subgroup.zpowers w⁆ = fiveStarR S w := by
    apply le_antisymm
    · apply (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers w)
        (K := fiveStarR S w)).mp
      exact Subgroup.normalizer_commutator_ge_right S (Subgroup.zpowers w)
    · exact CFSG.RankThree.PartTwo.Sec5.Bender.commutator_le_commutator_commutator S
        (Subgroup.zpowers w) hXS hcop
  have hwR : zpowers w ≤ normalizer (fiveStarR S w : Set G) := by
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact Subgroup.zpow_mem _ (mem_normalizer_fiveStarR_self S w) n
  obtain ⟨r, hr, hr3, u0, hu0R, p0, hp0P, hcomm⟩ :=
    e1c_exists_prime hθs hθ3 hO2 hRθ hR2 hR1
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G, P = CFSG.inSubgroup (CFSG.pCore r) θ := ⟨_, rfl⟩
  have hP2 : IsPGroup r P := by
    rw [hPdef]
    exact (CFSG.pCore_isPGroup (p := r) (G := ↥θ)).map θ.subtype
  have hθN : θ ≤ Subgroup.normalizer (P : Set G) := by
    rw [hPdef]
    exact fun g hg => e1c_normalizer_le_inSubgroup r θ (Subgroup.le_normalizer hg)
  have hNθP : normalizer (θ : Set G) ≤ normalizer (P : Set G) := by
    rw [hPdef]
    exact e1c_normalizer_le_inSubgroup r θ
  have hp0P' : p0 ∈ P := by
    rw [hPdef]
    exact hp0P
  have hp01 : p0 ≠ 1 := by
    intro h
    exact hcomm (by rw [h, mul_one, one_mul])
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hp0P'
    exact hp01 hp0P'
  obtain ⟨D, hDP, hND, hDexp, hDcl, hDfix⟩ := exists_critical_subgroup_fix hr2 hP2 hPne
  have hDp : IsPGroup r D := hP2.to_le hDP
  have hRD : fiveStarR S w ≤ normalizer (D : Set G) := fun g hg =>
    hND (hNθP (Subgroup.le_normalizer (hRθ hg)))
  have hwD : w ∈ normalizer (D : Set G) := hND (hNθP hwθ)
  have hSD : S ≤ normalizer (D : Set G) := fun g hg =>
    hND (hNθP (Subgroup.le_normalizer (hSθ hg)))
  have hRnc : ¬ fiveStarR S w ≤ centralizer (D : Set G) := by
    intro hle
    apply hcomm
    have hu0 : u0 ∈ centralizer (D : Set G) := hle hu0R
    have h2 : IsPGroup 2 (zpowers u0) := hR2.to_le (Subgroup.zpowers_le.mpr hu0R)
    have hu0P : u0 ∈ normalizer (P : Set G) := hNθP (Subgroup.le_normalizer (hRθ hu0R))
    have := hDfix u0 hu0P h2 hu0
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this p0 hp0P').symm
  have hfix : ∀ x ∈ fiveStarR S w, x ≠ 1 →
      CFSG.pRank r ↥(D ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 2 := by
    intro x hx hx1
    exact hloc r hr hr3 D hDp x hx1 (hR2.to_le (Subgroup.zpowers_le.mpr hx))
  obtain ⟨hfaith, hQ, hfpf, hrel, hrank3⟩ := five_star_core_hom hr hr2 hw5 hDp hDexp hDcl hR2 hRD hwD
    hwR hRX hRnc hfix
  obtain ⟨hRext, hR32⟩ := isExtraspecial_of_qd32 (hQ.some)
  have hirr : IsFrattiniIrreducibleFor (fiveStarR S w) D :=
    frattini_irreducible_of_normalizer hr hr2 hRD hDp hrel hRext hR32 hfaith
  exact ⟨hQ, hfpf, r, D, hr, hr3, hDp, hDexp, hSD, hfaith, hrank3, hirr⟩

end CFSG.RankThree.PartTwo.Sec11

end
