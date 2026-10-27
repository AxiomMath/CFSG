module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralCoreReduction
public import CFSG.Quasithin.Background.RonanE42Defs
public import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.Quasithin.RonanE42.Gen

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42

variable {G : Type} [Group G] [Finite G]

abbrev xt (T H : Subgroup G) : Subgroup G := fStarPre H ⊔ T

noncomputable abbrev iRank (H : Subgroup G) : ℕ := CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))

theorem eq_bot_of_normalized {Q : Type} [Group Q] [Finite Q] (hO2 : CFSG.pCore 2 Q = ⊥)
    (hF : CFSG.IsQuasisimple ↥(CFSG.generalizedFitting Q) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(CFSG.generalizedFitting Q) = p)
    {R : Subgroup Q} (hR : IsPGroup 2 R)
    (hRn : ∀ f ∈ CFSG.generalizedFitting Q, ∀ r ∈ R, f * r * f⁻¹ ∈ R) : R = ⊥ := by
  classical
  set F := CFSG.generalizedFitting Q with hFdef
  haveI hFchar : F.Characteristic := by
    rw [hFdef, CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.characteristic Q
  haveI hFn : F.Normal := inferInstance
  have hnorm2 : ∀ P : Subgroup Q, P.Normal → IsPGroup 2 P → P = ⊥ := fun P hPn hP2 =>
    le_bot_iff.mp (hO2 ▸ (le_sSup ⟨hPn, hP2⟩ : P ≤ CFSG.pCore 2 Q))
  have hFne : F ≠ ⊥ := by
    intro hF0
    rcases hF with hQ | ⟨p, hp, hcard⟩
    · obtain ⟨a, b, hab⟩ := hQ.2.2
      apply hab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      have ha : a = 1 := Subtype.ext (by simpa [hF0] using a.2)
      have hb : b = 1 := Subtype.ext (by simpa [hF0] using b.2)
      simp [ha, hb]
    · rw [hF0, Subgroup.card_bot] at hcard
      exact hp.one_lt.ne hcard
  have hS2 : IsPGroup 2 ↥(R ⊓ F) := hR.to_le inf_le_left
  have hRF : R ⊓ F = ⊥ := by
    rcases hF with hQ | ⟨p, hp, hcard⟩
    · haveI : Group.IsPerfect ↥F := hQ.1
      have hQ' : CFSG.Open.IsQuasisimple ↥F := ⟨Group.IsPerfect.commutator_eq_top, hQ.2.1⟩
      haveI hSn : ((R ⊓ F).subgroupOf F).Normal := by
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        refine ⟨?_, ?_⟩
        · simpa using hRn g g.2 n hn.1
        · simpa using F.mul_mem (F.mul_mem g.2 hn.2) (F.inv_mem g.2)
      rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ'
        ((R ⊓ F).subgroupOf F) with hc | ht
      ·
        set n := Nat.card Q
        let P : Subgroup Q :=
          { carrier := {z | z ∈ F ∧ (∀ f ∈ F, z * f = f * z) ∧ z ^ (2 ^ n) = 1}
            mul_mem' := fun {a b} ha hb => by
              refine ⟨F.mul_mem ha.1 hb.1, fun f hf => ?_, ?_⟩
              · rw [mul_assoc, hb.2.1 f hf, ← mul_assoc, ha.2.1 f hf, mul_assoc]
              · have hc : Commute a b := ha.2.1 b hb.1
                rw [hc.mul_pow, ha.2.2, hb.2.2, one_mul]
            one_mem' := ⟨F.one_mem, fun f _ => by simp, by simp⟩
            inv_mem' := fun {a} ha => by
              refine ⟨F.inv_mem ha.1, fun f hf => ?_, by rw [inv_pow, ha.2.2, inv_one]⟩
              have := ha.2.1 f hf
              calc a⁻¹ * f = a⁻¹ * (f * a) * a⁻¹ := by group
                _ = a⁻¹ * (a * f) * a⁻¹ := by rw [this]
                _ = f * a⁻¹ := by group }
        have hPn : P.Normal := by
          refine ⟨fun z hz g => ⟨hFn.conj_mem z hz.1 g, fun f hf => ?_, ?_⟩⟩
          · have h1 : g⁻¹ * f * g ∈ F := by simpa using hFn.conj_mem f hf g⁻¹
            have h2 := hz.2.1 _ h1
            calc g * z * g⁻¹ * f = g * (z * (g⁻¹ * f * g)) * g⁻¹ := by group
              _ = g * ((g⁻¹ * f * g) * z) * g⁻¹ := by rw [h2]
              _ = f * (g * z * g⁻¹) := by group
          · rw [conj_pow, hz.2.2, mul_one, mul_inv_cancel]
        have hPp : IsPGroup 2 P := fun g => ⟨n, Subtype.ext (by simpa using g.2.2.2)⟩
        have hP : P = ⊥ := hnorm2 P hPn hPp
        refine le_bot_iff.mp fun x hx => ?_
        rw [← hP]
        refine ⟨hx.2, fun f hf => ?_, ?_⟩
        · have hmem : (⟨x, hx.2⟩ : ↥F) ∈ (R ⊓ F).subgroupOf F := Subgroup.mem_subgroupOf.mpr hx
          have := Subgroup.mem_center_iff.mp (hc hmem) ⟨f, hf⟩
          exact (congrArg Subtype.val this).symm
        · obtain ⟨k, hk⟩ := hS2 ⟨x, hx⟩
          have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
          obtain ⟨j, -, hjx⟩ :=
            (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
          have hjn : j ≤ n := by
            have h1 : 2 ^ j ≤ n := hjx ▸ Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard x)
            exact (Nat.lt_two_pow_self).le.trans h1
          exact orderOf_dvd_iff_pow_eq_one.mp (hjx ▸ Nat.pow_dvd_pow 2 hjn)
      · exfalso
        have hFR : F ≤ R := fun f hf => by
          have : (⟨f, hf⟩ : ↥F) ∈ (R ⊓ F).subgroupOf F := by rw [ht]; trivial
          exact (Subgroup.mem_subgroupOf.mp this).1
        exact hFne (hnorm2 F hFn (hR.to_le hFR))
    · haveI : Fact (Nat.card ↥F).Prime := ⟨by rw [hcard]; exact hp⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((R ⊓ F).subgroupOf F) with hb | ht
      · have h := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hb)
        rwa [inf_eq_left.mpr (inf_le_right : R ⊓ F ≤ F)] at h
      · exfalso
        have hFR : F ≤ R := fun f hf => by
          have : (⟨f, hf⟩ : ↥F) ∈ (R ⊓ F).subgroupOf F := by rw [ht]; trivial
          exact (Subgroup.mem_subgroupOf.mp this).1
        exact hFne (hnorm2 F hFn (hR.to_le hFR))
  have hRc : R ≤ Subgroup.centralizer (F : Set Q) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hcomm : f * r * f⁻¹ * r⁻¹ ∈ R ⊓ F :=
      ⟨R.mul_mem (hRn f hf r hr) (R.inv_mem hr),
        by simpa [mul_assoc] using F.mul_mem hf (hFn.conj_mem f⁻¹ (F.inv_mem hf) r)⟩
    rw [hRF, Subgroup.mem_bot] at hcomm
    have : f * r * f⁻¹ = r := by rw [mul_inv_eq_one] at hcomm; exact hcomm
    calc f * r = f * r * f⁻¹ * f := by group
      _ = r * f := by rw [this]
  have hRle : R ≤ F := hRc.trans (CFSG.centralizer_generalizedFitting_le Q)
  exact le_bot_iff.mp (le_inf le_rfl hRle |>.trans hRF.le)

theorem fstar_le_of_normalized {Q : Type} [Group Q] [Finite Q] (hO2 : CFSG.pCore 2 Q = ⊥)
    (hF : CFSG.IsQuasisimple ↥(CFSG.generalizedFitting Q) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(CFSG.generalizedFitting Q) = p)
    {Y : Subgroup Q} (hYn : ∀ f ∈ CFSG.generalizedFitting Q, ∀ z ∈ Y, f * z * f⁻¹ ∈ Y)
    {y : Q} (hyY : y ∈ Y) (hy1 : y ≠ 1) {n : ℕ} (hyn : y ^ (2 ^ n) = 1) :
    CFSG.generalizedFitting Q ≤ Y := by
  classical
  set F := CFSG.generalizedFitting Q with hFdef
  haveI hFchar : F.Characteristic := by
    rw [hFdef, CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.characteristic Q
  haveI hFn : F.Normal := inferInstance
  have hcen : Y ≤ Subgroup.centralizer (F : Set Q) → False := by
    intro hYc
    have hyc := Subgroup.mem_centralizer_iff.mp (hYc hyY)
    have hz : Subgroup.zpowers y = ⊥ := by
      refine eq_bot_of_normalized hO2 hF ?_ ?_
      · intro g
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
        refine ⟨n, Subtype.ext ?_⟩
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyn, one_zpow]
      · intro f hf r hr
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
        have hc : Commute f (y ^ k) := (Commute.zpow_right (hyc f hf) k)
        rw [hc.eq, mul_inv_cancel_right]
        exact Subgroup.zpow_mem_zpowers y k
    exact hy1 (Subgroup.mem_bot.mp (hz ▸ Subgroup.mem_zpowers y))
  have hcomm_le : ⁅F, Y⁆ ≤ Y ⊓ F := by
    rw [Subgroup.commutator_le]
    intro f hf z hz
    rw [commutatorElement_def]
    exact ⟨Y.mul_mem (hYn f hf z hz) (Y.inv_mem hz),
      by simpa [mul_assoc] using F.mul_mem hf (hFn.conj_mem f⁻¹ (F.inv_mem hf) z)⟩
  have hYcen_of : ⁅F, Y⁆ = ⊥ → Y ≤ Subgroup.centralizer (F : Set Q) := fun h =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact h)
  haveI hSn : ((Y ⊓ F).subgroupOf F).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    refine ⟨?_, ?_⟩
    · simpa using hYn g g.2 m hm.1
    · simpa using F.mul_mem (F.mul_mem g.2 hm.2) (F.inv_mem g.2)
  rcases hF with hQ | ⟨p, hp, hcard⟩
  · haveI : Group.IsPerfect ↥F := hQ.1
    have hQ' : CFSG.Open.IsQuasisimple ↥F := ⟨Group.IsPerfect.commutator_eq_top, hQ.2.1⟩
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ'
      ((Y ⊓ F).subgroupOf F) with hc | ht
    · exfalso
      apply hcen
      set Zq : Subgroup Q := (Subgroup.center ↥F).map F.subtype
      have hYF : Y ⊓ F ≤ Zq := by
        intro x hx
        have hmem : (⟨x, hx.2⟩ : ↥F) ∈ (Y ⊓ F).subgroupOf F := Subgroup.mem_subgroupOf.mpr hx
        exact Subgroup.mem_map_of_mem _ (hc hmem)
      have hZcent : Zq ≤ Subgroup.centralizer (F : Set Q) := by
        intro z hz
        obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hz
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hf ⟨h, hh⟩)
      have hZF : ⁅Zq, F⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZcent
      have h3 : ⁅⁅F, Y⁆, F⁆ = ⊥ :=
        le_antisymm ((Subgroup.commutator_mono (hcomm_le.trans hYF) le_rfl).trans hZF.le) bot_le
      exact hYcen_of (CFSG.ComponentClassification.Quasisimple.perfect_double_commutator _ _ h3)
    · exact (Subgroup.subgroupOf_eq_top.mp ht).trans inf_le_left
  · haveI : Fact (Nat.card ↥F).Prime := ⟨by rw [hcard]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Y ⊓ F).subgroupOf F) with hb | ht
    · exfalso
      apply hcen
      have hYF0 : Y ⊓ F = ⊥ := by
        have h := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hb)
        rwa [inf_eq_left.mpr (inf_le_right : Y ⊓ F ≤ F)] at h
      exact hYcen_of (le_bot_iff.mp (hcomm_le.trans hYF0.le))
    · exact (Subgroup.subgroupOf_eq_top.mp ht).trans inf_le_left

theorem xt_good {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hF : CFSG.IsQuasisimple ↥(fStarMod H) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p)
    {Y : Subgroup G} (hY : Y ≤ xt T H) (hYn : ∀ h ∈ xt T H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 (xt T H))) :
    xt T H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) := by
  classical
  have hXH : xt T H ≤ H := sup_le (Subgroup.map_subtype_le _) hTH
  haveI : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal (p := 2)
  set ι : ↥(xt T H) →* ↥H := Subgroup.inclusion hXH
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  set φ : ↥(xt T H) →* ↥H ⧸ CFSG.pCore 2 ↥H := π.comp ι with hφ
  have hO2 : CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCore_quotient_eq_bot (G := ↥H) 2
  have h2 : φ.ker ≤ CFSG.pCore 2 ↥(xt T H) := by
    have hk : φ.ker = (CFSG.pCore 2 ↥H).comap ι := by
      rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    have hp : IsPGroup 2 φ.ker := by
      rw [hk]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).comap_of_injective ι
        (Subgroup.inclusion_injective hXH)
    exact (le_sSup ⟨φ.normal_ker, hp⟩ : φ.ker ≤ CFSG.pCore 2 ↥(xt T H))
  obtain ⟨b, hbYT, hb⟩ := SetLike.not_le_iff_exists.mp hYT
  obtain ⟨hbY, hbT⟩ := Subgroup.mem_inf.mp hbYT
  let b' : ↥(xt T H) := ⟨b, hY hbY⟩
  have hb'ne : φ b' ≠ 1 := by
    intro h1
    exact hb (Subgroup.mem_map.mpr ⟨b', h2 (MonoidHom.mem_ker.mpr h1), rfl⟩)
  obtain ⟨k, hk⟩ := hT.isPGroup (⟨b, hbT⟩ : T)
  have hb'k : φ b' ^ 2 ^ k = 1 := by
    have : b' ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [← map_pow, this, map_one]
  have hYbn : ∀ f ∈ CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H),
      ∀ z ∈ (Y.subgroupOf (xt T H)).map φ, f * z * f⁻¹ ∈ (Y.subgroupOf (xt T H)).map φ := by
    intro f hf z hz
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) f
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hhX : (h : G) ∈ xt T H :=
      le_sup_left (a := fStarPre H) (Subgroup.mem_map.mpr ⟨h, Subgroup.mem_comap.mpr hf, rfl⟩)
    let x : ↥(xt T H) := ⟨h, hhX⟩
    have hx : ι x = h := Subtype.ext rfl
    refine Subgroup.mem_map.mpr ⟨x * y * x⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hYn h hhX y hy
    · rw [map_mul, map_mul, map_inv]
      simp only [hφ, MonoidHom.comp_apply, hx]
      rfl
  have hsub := fstar_le_of_normalized hO2 hF hYbn
    (Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hbY : b' ∈ Y.subgroupOf (xt T H)))
    hb'ne hb'k
  have hX : fStarPre H ≤ Y ⊔ pCoreOf 2 H := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy'Y, hy'eq⟩ := Subgroup.mem_map.mp (hsub (Subgroup.mem_comap.mp hx'))
    have hπ : (QuotientGroup.mk (ι y') : ↥H ⧸ CFSG.pCore 2 ↥H) = QuotientGroup.mk x' := hy'eq
    have hr : (ι y')⁻¹ * x' ∈ CFSG.pCore 2 ↥H := QuotientGroup.eq.mp hπ
    have hrmem : H.subtype ((ι y')⁻¹ * x') ∈ pCoreOf 2 H :=
      Subgroup.mem_map.mpr ⟨_, hr, rfl⟩
    have hx_eq : H.subtype x' = (y' : G) * H.subtype ((ι y')⁻¹ * x') := by
      simp [ι]
    rw [hx_eq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hy'Y) hrmem
  have hRT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow hT hTH
  exact le_sup_of_le_right
    (sup_le (hX.trans (sup_le le_sup_right (hRT.trans le_sup_left))) le_sup_left)

theorem xt_rank {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hF : CFSG.IsQuasisimple ↥(fStarMod H) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p) :
    iRank (xt T H) ≤ iRank H := by
  classical
  have hXH : xt T H ≤ H := sup_le (Subgroup.map_subtype_le _) hTH
  haveI : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal (p := 2)
  haveI : (CFSG.pCore 2 ↥(xt T H)).Normal := CFSG.pCore_normal (p := 2)
  set ι : ↥(xt T H) →* ↥H := Subgroup.inclusion hXH
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  set φ : ↥(xt T H) →* ↥H ⧸ CFSG.pCore 2 ↥H := π.comp ι with hφ
  have hO2 : CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCore_quotient_eq_bot (G := ↥H) 2
  have h1 : CFSG.pCore 2 ↥(xt T H) ≤ φ.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    refine eq_bot_of_normalized hO2 hF ((CFSG.pCore_isPGroup (p := 2) (G := _)).map φ) ?_
    intro f hf r hr
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) f
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hr
    have hhX : (h : G) ∈ xt T H :=
      le_sup_left (a := fStarPre H) (Subgroup.mem_map.mpr ⟨h, Subgroup.mem_comap.mpr hf, rfl⟩)
    let x : ↥(xt T H) := ⟨h, hhX⟩
    have hx : ι x = h := Subtype.ext rfl
    refine Subgroup.mem_map.mpr ⟨x * y * x⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥(xt T H))).conj_mem y hy x, ?_⟩
    rw [map_mul, map_mul, map_inv]
    simp only [hφ, MonoidHom.comp_apply, hx]
    rfl
  have h2 : φ.ker ≤ CFSG.pCore 2 ↥(xt T H) := by
    have hk : φ.ker = (CFSG.pCore 2 ↥H).comap ι := by
      rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    have hp : IsPGroup 2 φ.ker := by
      rw [hk]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).comap_of_injective ι
        (Subgroup.inclusion_injective hXH)
    exact (le_sSup ⟨φ.normal_ker, hp⟩ : φ.ker ≤ CFSG.pCore 2 ↥(xt T H))
  have heq : CFSG.pCore 2 ↥(xt T H) = φ.ker := le_antisymm h1 h2
  let e := QuotientGroup.quotientMulEquivOfEq heq
  have hinj : Function.Injective ((QuotientGroup.kerLift φ).comp e.toMonoidHom) :=
    (QuotientGroup.kerLift_injective φ).comp e.injective
  exact CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) _ hinj

theorem xt_le {T H : Subgroup G} (hTH : T ≤ H) : xt T H ≤ H :=
  sup_le (Subgroup.map_subtype_le _) hTH

end CFSG.Quasithin.RonanE42.Gen
