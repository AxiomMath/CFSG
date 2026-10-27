module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Config

variable {G : Type} [Group G]

theorem center_eq_bot_of_marking {L : Subgroup G} (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) : Subgroup.center R = ⊥ := by
  have : Group.IsPerfect L := ⟨hL⟩
  have hZ := Group.IsPerfect.center_quotient_center_eq_bot L
  rw [eq_bot_iff]
  intro r hr
  have h1 : θ.symm r ∈ Subgroup.center (L ⧸ Subgroup.center L) := by
    rw [Subgroup.mem_center_iff] at hr ⊢
    intro q
    apply θ.injective
    rw [map_mul, map_mul, θ.apply_symm_apply]
    exact hr (θ q)
  rw [hZ, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  simpa using congrArg θ h1

theorem mulAut_conj_apply_eq {R : Type} [Group R] (φ : MulAut R) (r : R) :
    MulAut.conj (φ r) = φ * MulAut.conj r * φ⁻¹ := by
  ext s
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

variable [Finite G]

theorem card_zpowers_sup_zpowers {p : ℕ} (hp : p.Prime) {B : Subgroup G}
    (hB : IsElemAbelian p B) {x d : G} (hxB : x ∈ B) (hdB : d ∈ B) (hx1 : x ≠ 1)
    (hdx : d ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers d : Subgroup G) = p ^ 2 := by
  have := Fact.mk hp
  have hdp : d ^ p = 1 := hB.2 d hdB
  have hxp : x ^ p = 1 := hB.2 x hxB
  have hd1 : d ≠ 1 := fun h => hdx (h ▸ one_mem _)
  have hN : Subgroup.zpowers d ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact IsElemAbelian.comm hB (Subgroup.zpowers_le.mpr hxB hz) (Subgroup.zpowers_le.mpr hdB hy)
  have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers d) := by
    rw [Subgroup.disjoint_def]
    intro g hgx hgd
    by_contra hg1
    exact hdx (mem_of_mem_zpowers_of_ne_one hp hdp hd1 hgd hgx hg1)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj,
    Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hxp hx1, orderOf_eq_prime hdp hd1, sq]

theorem ggNormTwoR_or_delta {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I)
    (h4 : ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥) :
    GGNormTwoR (ggQuotHom θ) (ggGamma L hBN).range ∨
      ∃ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer (L : Set G) ∧
        T₀ ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T₀ ∧
        B ≤ Subgroup.normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥ := by
  obtain ⟨D, hDn, hID, hodd⟩ := hOD
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := h4
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := fun t ht =>
    mem_normalizer_of_sstar hS hnc (hTx ht)
  set lamT := ((ggLAut L θ).comp (Subgroup.inclusion hTN)).range with hlamT
  have hlamT2 : IsPGroup 2 lamT :=
    hT2.of_surjective ((ggLAut L θ).comp (Subgroup.inclusion hTN)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  by_cases hΘ1 : lamT ⊓ (MulAut.conj : R →* MulAut R).range = ⊥
  · right
    refine ⟨T ⊓ Subgroup.centralizer (L : Set G), inf_le_right, inf_le_left.trans hTx,
      hT2.to_le inf_le_left, ?_,
      commutator_inf_centralizer_ne_bot hp hp2 hL θ (fun b hb => hS.1.1.2 b hb) hBN h3 hDn hID
        hodd hT2 hTN hBT hTB hΘ1⟩
    rw [Subgroup.le_normalizer_iff]
    intro b hb t ht
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : b⁻¹ * l * b ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hBN (Subgroup.inv_mem _ hb)) l).mp hl
      rwa [inv_inv] at h1
    have hc := Subgroup.mem_centralizer_iff.mp ht.2 _ hl'
    calc l * (b * t * b⁻¹) = b * ((b⁻¹ * l * b) * t) * b⁻¹ := by group
      _ = b * (t * (b⁻¹ * l * b)) * b⁻¹ := by rw [hc]
      _ = b * t * b⁻¹ * l := by group
  · left
    set Θ := lamT ⊓ (MulAut.conj : R →* MulAut R).range with hΘ
    have hZ := center_eq_bot_of_marking hL θ
    have hΘB : ∀ b (hb : b ∈ B), ∀ φ ∈ Θ,
        ggLAut L θ ⟨b, hBN hb⟩ * φ * (ggLAut L θ ⟨b, hBN hb⟩)⁻¹ ∈ Θ := by
      intro b hb φ hφ
      obtain ⟨⟨t, rfl⟩, hφi⟩ := hφ
      have hbtb : b * (t : G) * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp t.2
      refine ⟨⟨⟨b * t * b⁻¹, hbtb⟩, ?_⟩, (ggInnNormal R).conj_mem _ hφi _⟩
      have h1 : Subgroup.inclusion hTN ⟨b * t * b⁻¹, hbtb⟩ =
          (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set G)) * Subgroup.inclusion hTN t *
            (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set G))⁻¹ :=
        Subtype.ext rfl
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_mul, map_mul, map_inv]
    refine ⟨Θ.comap (MulAut.conj : R →* MulAut R), ?_, ?_, ?_⟩
    · intro hbot
      apply hΘ1
      rw [eq_bot_iff]
      intro φ hφ
      obtain ⟨r, hr⟩ := hφ.2
      have hrU : r ∈ Θ.comap (MulAut.conj : R →* MulAut R) := by
        show MulAut.conj r ∈ Θ
        rw [hr]
        exact hφ
      rw [hbot, Subgroup.mem_bot] at hrU
      rw [Subgroup.mem_bot, ← hr, hrU, map_one]
    · rintro ⟨r, hr⟩
      obtain ⟨k, hk⟩ := hlamT2 ⟨MulAut.conj r, hr.1⟩
      have h1 : MulAut.conj (r ^ 2 ^ k) = 1 := by
        have h2 := congrArg Subtype.val hk
        rw [Subgroup.coe_pow] at h2
        rw [map_pow]
        exact h2
      have hc : r ^ 2 ^ k ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h2 := congrArg (fun φ : MulAut R => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        calc g * r ^ 2 ^ k = r ^ 2 ^ k * g * (r ^ 2 ^ k)⁻¹ * r ^ 2 ^ k := by rw [h2]
          _ = r ^ 2 ^ k * g := by group
      rw [hZ, Subgroup.mem_bot] at hc
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hc)⟩
    · rintro _ ⟨b, rfl⟩ l hl
      show MulAut.conj (ggQuotHom θ (ggGamma L hBN b l)) ∈ Θ
      rw [← ggBeta_ggQuotHom L hBN θ b l, mulAut_conj_apply_eq, ggBeta_eq]
      exact hΘB b b.2 _ hl

theorem ggStdSubPre_of_endNode {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {d : B} (hend : GGIsEndNode (ggGamma L hBN).range (ggGamma L hBN d)) :
    LargeEvenStdSubPre p B x L (Subgroup.zpowers x ⊔ Subgroup.zpowers (d : G))
      ((LargeEvenLayer (ggFix (ggGamma L hBN d))).map L.subtype) := by
  have := Fact.mk hp
  obtain ⟨-, ha1, hcomp, hcent⟩ := hend
  set γ := ggGamma L hBN with hγ
  have hxB : x ∈ B := hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hdx : (d : G) ∉ Subgroup.zpowers x := by
    intro hd
    apply ha1
    rw [ggGamma_eq_one_iff]
    rw [← inf_centralizer_eq_zpowers_of_sstar hp hS] at hd
    exact hd.2
  set D : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers (d : G) with hD
  set J' := LargeEvenLayer (ggFix (γ d)) with hJ'
  have hJ'fix : J' ≤ ggFix (γ d) := sSup_le fun K hK => hK.1
  have hfix : (ggFix (γ d)).map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBN d
  have hDB : D ≤ B := sup_le (Subgroup.zpowers_le.mpr hxB) (Subgroup.zpowers_le.mpr d.2)
  refine ⟨hDB, isElemAbelian_mono hS.1.1 hDB,
    card_zpowers_sup_zpowers hp hS.1.1 hxB d.2 hS.2.2.1 hdx,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x), ?_, ?_, ?_⟩
  · rw [← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  · rw [← hfix]
    exact isComponentOf_map_of_injective _ L.subtype_injective hcomp
  · apply le_antisymm
    · refine le_inf hDB (sup_le ?_ ?_)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro _ ⟨j, -, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLx j.2)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro _ ⟨j, hj, rfl⟩
        have h1 := congrArg Subtype.val (mem_ggFix.mp (hJ'fix hj))
        rw [ggGamma_coe] at h1
        calc (j : G) * d = d * j * (d : G)⁻¹ * d := by rw [h1]
          _ = d * j := by group
    · rintro b ⟨hbB, hbJ⟩
      have hγb : ∀ j ∈ J', γ ⟨b, hbB⟩ j = j := by
        intro j hj
        apply Subtype.ext
        rw [ggGamma_coe]
        have := Subgroup.mem_centralizer_iff.mp hbJ j ⟨j, hj, rfl⟩
        calc b * j * b⁻¹ = j * b * b⁻¹ := by rw [this]
          _ = j := by group
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hcent _ ⟨⟨b, hbB⟩, rfl⟩).mp hγb)
      have hker : ((⟨b, hbB⟩ : B) * d ^ (-k)) ∈ γ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_zpow, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
      rw [ker_ggGamma L hBN hp hS, Subgroup.mem_subgroupOf] at hker
      have hb : b = (((⟨b, hbB⟩ : B) * d ^ (-k) : B) : G) * (d : G) ^ k := by
        rw [Subgroup.coe_mul, Subgroup.coe_zpow, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
          mul_one]
      rw [hb]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hker)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

theorem inf_centralizer_le_of_centEnd {p : ℕ} (hp : p.Prime) {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (hBs : GGBstar p B Bs)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {d : B} (hcent : GGCentEnd (ggGamma L hBsN).range (ggGamma L hBN d)) :
    Bs ⊓ Subgroup.centralizer
        (((LargeEvenLayer (ggFix (ggGamma L hBN d))).map L.subtype : Subgroup G) : Set G) ≤
      Subgroup.zpowers x ⊔ Subgroup.zpowers (d : G) := by
  rintro e ⟨heBs, heJ⟩
  have hfix : ∀ j ∈ LargeEvenLayer (ggFix (ggGamma L hBN d)),
      ggGamma L hBsN ⟨e, heBs⟩ j = j := by
    intro j hj
    apply Subtype.ext
    rw [ggGamma_coe]
    have := Subgroup.mem_centralizer_iff.mp heJ j ⟨j, hj, rfl⟩
    calc e * j * e⁻¹ = j * e * e⁻¹ := by rw [this]
      _ = j := by group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hcent _ ⟨⟨e, heBs⟩, rfl⟩).mp hfix)
  have hdd : ggGamma L hBN d = ggGamma L hBsN ⟨d, hBs.1 d.2⟩ :=
    MulEquiv.ext fun l => Subtype.ext (by rw [ggGamma_coe, ggGamma_coe])
  have hker : ggGamma L hBsN ((⟨e, heBs⟩ : Bs) * ⟨d, hBs.1 d.2⟩ ^ (-k)) = 1 := by
    rw [map_mul, map_zpow, ← hdd, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
  rw [ggGamma_eq_one_iff] at hker
  have hmem : (((⟨e, heBs⟩ : Bs) * ⟨d, hBs.1 d.2⟩ ^ (-k) : Bs) : G) ∈ Subgroup.zpowers x := by
    rw [← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1
      hS.2.2.2.1.1 hS.2.2.2.2]
    exact ⟨Subtype.prop _, hker⟩
  have he : e = (((⟨e, heBs⟩ : Bs) * ⟨d, hBs.1 d.2⟩ ^ (-k) : Bs) : G) * (d : G) ^ k := by
    rw [Subgroup.coe_mul, Subgroup.coe_zpow, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
      mul_one]
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

theorem zpow_apply_eq_self_of_apply_eq {H : Type*} [Group H] {φ : MulAut H} {j : H}
    (h : φ j = j) (k : ℤ) : (φ ^ k) j = j := by
  have hφ : φ ∈ MulAction.stabilizer (MulAut H) j := MulAction.mem_stabilizer_iff.mpr h
  exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpow_mem _ hφ k)

theorem ggIsEndNode_of_stdSubPre {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {D₁ K₁ : Subgroup G} (hT : LargeEvenStdSubPre p B x L D₁ K₁) :
    ∃ a₁, GGIsEndNode (ggGamma L hBN).range a₁ ∧
      Nonempty (↥(LargeEvenLayer (ggFix a₁)) ≃* ↥K₁) := by
  have := Fact.mk hp
  obtain ⟨hDB, -, hDc, hxD, hK, hKc, hDeq⟩ := hT
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  obtain ⟨d₁, hd₁D, hd₁x⟩ : ∃ d₁ ∈ D₁, d₁ ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show D₁ ≤ Subgroup.zpowers x from fun g hg => hcon g hg)
    rw [hDc, Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 x hxB) hx1] at h1
    have h2 := hp.two_le
    nlinarith
  have hd₁B : d₁ ∈ B := hDB hd₁D
  set d : B := ⟨d₁, hd₁B⟩ with hd
  have hDeq' : D₁ = Subgroup.zpowers x ⊔ Subgroup.zpowers d₁ := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hxD)
      (Subgroup.zpowers_le.mpr hd₁D)) ?_).symm
    rw [hDc, card_zpowers_sup_zpowers hp hS.1.1 hxB hd₁B hx1 hd₁x]
  have hfix : (ggFix (ggGamma L hBN d)).map L.subtype =
      L ⊓ Subgroup.centralizer (D₁ : Set G) := by
    rw [hDeq', inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBN d
  have hK₁ : K₁ = (LargeEvenLayer (ggFix (ggGamma L hBN d))).map L.subtype := by
    rw [hK, ← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  refine ⟨ggGamma L hBN d, ⟨⟨d, rfl⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro h1
    apply hd₁x
    rw [ggGamma_eq_one_iff] at h1
    rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
    exact ⟨hd₁B, h1⟩
  · have hc := hKc
    rw [hK₁, ← hfix] at hc
    have h1 := (isComponentOf_comap_of_injective _ L.subtype_injective hc).1
    rwa [Subgroup.comap_map_eq_self_of_injective L.subtype_injective] at h1
  · rintro _ ⟨b, rfl⟩
    constructor
    · intro hfixb
      have hbK : (b : G) ∈ B ⊓ Subgroup.centralizer (K₁ : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨b.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff, hK₁]
        rintro _ ⟨j, hj, rfl⟩
        have h1 := congrArg Subtype.val (hfixb j hj)
        rw [ggGamma_coe] at h1
        calc (j : G) * b = b * j * (b : G)⁻¹ * b := by rw [h1]
          _ = b * j := by group
      rw [← hDeq, hDeq'] at hbK
      have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers d₁ ≤
          ((Subgroup.zpowers (ggGamma L hBN d)).comap (ggGamma L hBN)).map B.subtype := by
        have hx' : (⟨x, hxB⟩ : B) ∈
            (Subgroup.zpowers (ggGamma L hBN d)).comap (ggGamma L hBN) := by
          rw [Subgroup.mem_comap,
            (ggGamma_eq_one_iff L hBN ⟨x, hxB⟩).mpr (mem_centralizer_of_le_centralizer hLx)]
          exact one_mem _
        have hd' : d ∈ (Subgroup.zpowers (ggGamma L hBN d)).comap (ggGamma L hBN) :=
          Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
        exact sup_le (Subgroup.zpowers_le.mpr ⟨⟨x, hxB⟩, hx', rfl⟩)
          (Subgroup.zpowers_le.mpr ⟨d, hd', rfl⟩)
      obtain ⟨b', hb', hbb'⟩ := hle hbK
      have hb'b : b' = b := Subtype.ext hbb'
      rw [← hb'b]
      exact hb'
    · intro hmem j hj
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hk]
      have hjfix : ggGamma L hBN d j = j :=
        mem_ggFix.mp ((sSup_le fun K hK => hK.1 :
          LargeEvenLayer (ggFix (ggGamma L hBN d)) ≤ ggFix (ggGamma L hBN d)) hj)
      exact zpow_apply_eq_self_of_apply_eq hjfix k
  · rw [hK₁]
    exact ⟨(LargeEvenLayer (ggFix (ggGamma L hBN d))).equivMapOfInjective _ L.subtype_injective⟩

theorem ggGamma_endNode_hyps {p r : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hBs : GGBstar p B Bs) (hne : B ≠ Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I) (hlift : GGTorusLift p r R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    IsElemAbelian p (ggGamma L hBN).range ∧
      (∀ a ∈ (ggGamma L hBN).range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      p ^ r ≤ Nat.card (ggGamma L hBN).range ∧
      p ^ 3 ≤ Nat.card (ggGamma L hBN).range ∧
      (ggGamma L hBN).range < (ggGamma L hBsN).range ∧
      IsElemAbelian p (ggGamma L hBsN).range ∧
      Nat.card (ggGamma L hBsN).range ≤ p * Nat.card (ggGamma L hBN).range ∧
      GGNoTwoBetween (ggGamma L hBN).range (ggGamma L hBsN).range ∧
      (GGNormTwoR (ggQuotHom θ) (ggGamma L hBN).range ∨
        GGDeltaAdm p L (ggGamma L hBN).range) := by
  have hT' := hT
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT'
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  obtain ⟨hA, hAI, hr, h3'⟩ := ggGamma_range_props hp hS hβ.2.2.2 hL θ hBN h3 hlift
  have hγγs : ∀ b : B, ggGamma L hBN b = ggGamma L hBsN ⟨b, hBs.1 b.2⟩ := fun b =>
    MulEquiv.ext fun l => Subtype.ext (by rw [ggGamma_coe, ggGamma_coe])
  have hAAs : (ggGamma L hBN).range ≤ (ggGamma L hBsN).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBs.1 b.2⟩, (hγγs b).symm⟩
  have hAlt : (ggGamma L hBN).range < (ggGamma L hBsN).range := by
    refine lt_of_le_of_ne hAAs fun heq => hne ?_
    refine le_antisymm hBs.1 fun e he => ?_
    obtain ⟨b, hb⟩ := (heq ▸ (⟨⟨e, he⟩, rfl⟩ : ggGamma L hBsN ⟨e, he⟩ ∈ (ggGamma L hBsN).range) :
      ggGamma L hBsN ⟨e, he⟩ ∈ (ggGamma L hBN).range)
    have hker : ggGamma L hBsN ((⟨e, he⟩ : Bs) * (⟨b, hBs.1 b.2⟩ : Bs)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hγγs, hb, mul_inv_cancel]
    rw [ggGamma_eq_one_iff] at hker
    have hmem : (((⟨e, he⟩ : Bs) * (⟨b, hBs.1 b.2⟩ : Bs)⁻¹ : Bs) : G) ∈ Subgroup.zpowers x := by
      rw [← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1
        hS.2.2.2.1.1 hS.2.2.2.2]
      exact ⟨Subtype.prop _, hker⟩
    have he' : e = (((⟨e, he⟩ : Bs) * (⟨b, hBs.1 b.2⟩ : Bs)⁻¹ : Bs) : G) * (b : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [he']
    exact B.mul_mem (Subgroup.zpowers_le.mpr hS.2.1 hmem) b.2
  have hAs : IsElemAbelian p (ggGamma L hBsN).range := isElemAbelian_range
    (fun a b => Subtype.ext (IsElemAbelian.comm hBs.2.1 a.2 b.2))
    (fun a => Subtype.ext (by simpa using hBs.2.1.2 a a.2)) _
  have hcard : Nat.card (ggGamma L hBsN).range ≤ p * Nat.card (ggGamma L hBN).range := by
    have hcB := card_range_ggGamma_mul L hBN hp hS
    have hcBs := card_range_ggGamma_mul_of hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1 hS.2.2.2.1.1
      hS.2.2.2.2 hBsN
    have h1 : Nat.card (ggGamma L hBsN).range * p ≤
        p * Nat.card (ggGamma L hBN).range * p := by
      rw [hcBs, mul_assoc, hcB]
      exact hBs.2.2.1
    exact Nat.le_of_mul_le_mul_right h1 hp.pos
  have hnone : GGNoTwoBetween (ggGamma L hBN).range (ggGamma L hBsN).range := by
    intro E hAE hEAs U hU2 hEU
    by_contra hU1
    set E₂ : Subgroup G := (E.comap (ggGamma L hBsN)).map Bs.subtype with hE₂
    have hE₂Bs : E₂ ≤ Bs := Subgroup.map_subtype_le _
    have hBE₂ : B ≤ E₂ := fun b hb =>
      ⟨⟨b, hBs.1 hb⟩, hAE.le ⟨⟨b, hb⟩, hγγs ⟨b, hb⟩⟩, rfl⟩
    have hBne : B ≠ E₂ := by
      intro heq
      obtain ⟨φ, hφE, hφA⟩ := IsConcreteLE.exists_of_lt hAE
      obtain ⟨e₀, rfl⟩ := hEAs hφE
      have he₀ : (e₀ : G) ∈ E₂ := ⟨e₀, hφE, rfl⟩
      rw [← heq] at he₀
      exact hφA ⟨⟨e₀, he₀⟩, hγγs ⟨e₀, he₀⟩⟩
    have hE₂A : IsElemAbelian p E₂ := isElemAbelian_mono hBs.2.1 hE₂Bs
    have hE₂N : E₂ ≤ Subgroup.normalizer ((U.map L.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      rintro _ ⟨e, he, rfl⟩ _ ⟨u, hu, rfl⟩
      exact ⟨_, hEU _ he u hu, ggGamma_coe L hBsN e u⟩
    have hU1' : U.map L.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
      exact hU1
    have hc := card_le_of_twoLocal hp ⟨U.map L.subtype, hU1', hU2.map _, rfl⟩ hE₂N hE₂A
    rw [← hS.1.2.1] at hc
    exact hBne (Subgroup.eq_of_le_of_card_ge hBE₂ hc)
  have hcase : GGNormTwoR (ggQuotHom θ) (ggGamma L hBN).range ∨
      GGDeltaAdm p L (ggGamma L hBN).range := by
    rcases ggNormTwoR_or_delta hp hβ.2.1 hS hnc hL θ hBN h3 hOD hst.2.1 with hα | hδ
    · exact Or.inl hα
    · exact Or.inr (ggDeltaAdm_of_delta hp hS hBN hδ)
  exact ⟨hA, hAI, hr, h3', hAlt, hAs, hcard, hnone, hcase⟩

theorem exists_stdSubIOne_of_data {p r : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hBs : GGBstar p B Bs) (hne : B ≠ Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I) (hlift : GGTorusLift p r R) (hend : GGEndNodeIOne p r R I) :
    ∃ D J : Subgroup G, LargeEvenStdSub p B x L D J ∧
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  have hT' := hT
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT'
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := fun e he =>
    mem_normalizer_of_sstar hS hnc (Subgroup.mem_centralizer_singleton_iff.mpr
      (IsElemAbelian.comm hBs.2.1 he (hBs.1 hS.2.1)))
  obtain ⟨hA, hAI, hr, h3', hAlt, hAs, hcard, hnone, hcase⟩ :=
    ggGamma_endNode_hyps hT hBs hne hnc hL θ hBN h3 hOD hlift hBsN
  obtain ⟨a, ⟨haA, ha1, hcomp, hcentA⟩, hcentAs, hrule⟩ := hend L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL _ _ hA hAlt hAs hcard hAI hr h3' hcase
    hnone
  obtain ⟨d, rfl⟩ := haA
  have hendd : GGIsEndNode (ggGamma L hBN).range (ggGamma L hBN d) :=
    ⟨⟨d, rfl⟩, ha1, hcomp, hcentA⟩
  refine ⟨_, _, ⟨ggStdSubPre_of_endNode hp hS hBN hendd, ?_⟩,
    inf_centralizer_le_of_centEnd hp hS hBs hBN hBsN hcentAs⟩
  rintro ⟨hp3, D₁, K₁, hT₁, hns⟩ hsm
  obtain ⟨a₁, hend₁, ⟨e₁⟩⟩ := ggIsEndNode_of_stdSubPre hp hS hBN hT₁
  have hns₁ : ¬ LargeEvenSmall (LargeEvenLayer (ggFix a₁)) := fun h =>
    hns ((largeEvenSmall_congr e₁).mp h)
  exact hrule hp3 ⟨a₁, hend₁, hns₁⟩ ((largeEvenSmall_congr
    ((LargeEvenLayer (ggFix (ggGamma L hBN d))).equivMapOfInjective _ L.subtype_injective)).mpr
      hsm)

theorem exists_stdSubPre_nonSmall_of_data {p r : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hBs : GGBstar p B Bs) (hne : B ≠ Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I) (hlift : GGTorusLift p r R)
    (hend : GGEndNodeIOneNonSmall p r R I) :
    ∃ D J : Subgroup G, LargeEvenStdSubPre p B x L D J ∧ (p = 3 → ¬ LargeEvenSmall J) := by
  have hT' := hT
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT'
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := fun e he =>
    mem_normalizer_of_sstar hS hnc (Subgroup.mem_centralizer_singleton_iff.mpr
      (IsElemAbelian.comm hBs.2.1 he (hBs.1 hS.2.1)))
  obtain ⟨hA, hAI, hr, h3', hAlt, hAs, hcard, hnone, hcase⟩ :=
    ggGamma_endNode_hyps hT hBs hne hnc hL θ hBN h3 hOD hlift hBsN
  obtain ⟨a, ⟨haA, ha1, hcomp, hcentA⟩, hcentAs, hns⟩ := hend L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL _ _ hA hAlt hAs hcard hAI hr h3' hcase
    hnone
  obtain ⟨d, rfl⟩ := haA
  have hendd : GGIsEndNode (ggGamma L hBN).range (ggGamma L hBN d) :=
    ⟨⟨d, rfl⟩, ha1, hcomp, hcentA⟩
  refine ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers (d : G),
    (LargeEvenLayer (ggFix (ggGamma L hBN d))).map L.subtype,
    ggStdSubPre_of_endNode hp hS hBN hendd, ?_⟩
  intro hp3 hsm
  exact hns hp3 ((largeEvenSmall_congr
    ((LargeEvenLayer (ggFix (ggGamma L hBN d))).equivMapOfInjective _ L.subtype_injective)).mpr hsm)

end Config

theorem ggStdSubIOneProperInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
        ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I) :
    GGStdSubIOneProperInputOn S := by
  intro G _ _ p B Bs x L hT hBs hne hM
  have hnc := ha₀ G p B x L hT
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, hOD, r, hlift, hend⟩ :=
    largeEvenRawDatum_exists hraw
  exact exists_stdSubIOne_of_data hT hBs hne hnc hL θ hBN h3 hOD hlift hend

theorem ggStdSubIOneProperInput_of_labels (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
        ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I) :
    GGStdSubIOneProperInput :=
  ggStdSubIOneProperInput_of_cover (S := fun _ _ => True)
    (ggStdSubIOneProperInputOn_of_labels ha₀ fun p lab hp hlab _ hs => h p lab hp hlab hs)
    fun _ _ _ _ => trivial

end CFSG.StandardType
