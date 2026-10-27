module

public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Fix

variable {H : Type*} [Group H]

@[expose] def ggFix (a : MulAut H) : Subgroup H where
  carrier := {h | a h = h}
  mul_mem' {x y} hx hy := by
    change a x = x at hx
    change a y = y at hy
    change a (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := map_one a
  inv_mem' {x} hx := by
    change a x = x at hx
    change a x⁻¹ = x⁻¹
    rw [map_inv, hx]

theorem mem_ggFix {a : MulAut H} {h : H} : h ∈ ggFix a ↔ a h = h :=
  Iff.rfl

end Fix

section Inj

variable {H H' : Type*} [Group H] [Group H']

theorem isSubnormal_comap_hom (f : H →* H') {A B : Subgroup H'} (h : IsSubnormal A B) :
    IsSubnormal (A.comap f) (B.comap f) :=
  h.comap f

theorem isComponentOf_map_of_injective (f : H →* H') (hf : Function.Injective f)
    {K C : Subgroup H} (h : IsComponentOf K C) : IsComponentOf (K.map f) (C.map f) := by
  obtain ⟨hKC, hs, hq⟩ := h
  refine ⟨Subgroup.map_mono hKC, isSubnormal_map_hom f hs, ?_⟩
  rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (K.equivMapOfInjective f hf)).1 hq

theorem isComponentOf_comap_of_injective (f : H →* H') (hf : Function.Injective f)
    {K' : Subgroup H'} {C : Subgroup H} (h : IsComponentOf K' (C.map f)) :
    IsComponentOf (K'.comap f) C ∧ (K'.comap f).map f = K' := by
  obtain ⟨hKC, hs, hq⟩ := h
  have hmap : (K'.comap f).map f = K' :=
    Subgroup.map_comap_eq_self (hKC.trans (Subgroup.map_le_range f C))
  refine ⟨⟨?_, ?_, ?_⟩, hmap⟩
  · intro g hg
    obtain ⟨g', hg', hgg'⟩ := hKC hg
    rw [← hf hgg']
    exact hg'
  · have := isSubnormal_comap_hom f hs
    rwa [Subgroup.comap_map_eq_self_of_injective hf] at this
  · rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
    have e : ↥(K'.comap f) ≃* ↥K' :=
      ((K'.comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hmap)
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq

theorem largeEvenLayer_map_of_injective (f : H →* H') (hf : Function.Injective f)
    (C : Subgroup H) : LargeEvenLayer (C.map f) = (LargeEvenLayer C).map f := by
  apply le_antisymm
  · refine sSup_le fun K' hK' => ?_
    obtain ⟨hK, hmap⟩ := isComponentOf_comap_of_injective f hf hK'
    rw [← hmap]
    exact Subgroup.map_mono (le_sSup hK)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (isComponentOf_map_of_injective f hf hK)

end Inj

section Gamma

variable {G : Type} [Group G] (L : Subgroup G) {B : Subgroup G}
  (hBN : B ≤ Subgroup.normalizer (L : Set G))

@[expose] noncomputable def ggGamma : B →* MulAut L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion hBN)

theorem ggGamma_coe (b : B) (l : L) : ((ggGamma L hBN b l : L) : G) = b * l * (b : G)⁻¹ :=
  rfl

theorem ggGamma_eq_one_iff (b : B) :
    ggGamma L hBN b = 1 ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    have h1 := congrArg Subtype.val (congrArg (fun a : MulAut L => a ⟨l, hl⟩) h)
    simp only [MulAut.one_apply] at h1
    rw [ggGamma_coe] at h1
    calc l * b = b * l * (b : G)⁻¹ * b := by rw [h1]
      _ = b * l := by group
  · intro h
    ext l
    rw [MulAut.one_apply, ggGamma_coe, ← h l l.2]
    group

theorem ggBeta_ggQuotHom {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) (b : B) (l : L) :
    ggBeta L θ hBN b (ggQuotHom θ l) = ggQuotHom θ (ggGamma L hBN b l) := by
  rw [ggQuotHom_apply, ggQuotHom_apply, ggBeta_eq, ggLAut_apply]
  rfl

theorem map_ggFix_ggGamma (d : B) :
    (ggFix (ggGamma L hBN d)).map L.subtype =
      L ⊓ Subgroup.centralizer ({(d : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := congrArg Subtype.val (mem_ggFix.mp hl)
    rw [ggGamma_coe] at h1
    calc (l : G) * d = d * l * (d : G)⁻¹ * d := by rw [h1]
      _ = d * l := by group
  · rintro ⟨hgL, hgd⟩
    refine ⟨⟨g, hgL⟩, ?_, rfl⟩
    apply Subtype.ext
    rw [ggGamma_coe]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hgd
    calc (d : G) * g * (d : G)⁻¹ = g * d * (d : G)⁻¹ := by rw [h1]
      _ = g := by group

variable [Finite G]

theorem ker_ggGamma {p : ℕ} (hp : p.Prime) {x : G} (hS : LargeEvenSStar p B x L) :
    (ggGamma L hBN).ker = (Subgroup.zpowers x).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff,
    ← inf_centralizer_eq_zpowers_of_sstar hp hS]
  exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩

theorem card_range_ggGamma_mul {p : ℕ} (hp : p.Prime) {x : G} (hS : LargeEvenSStar p B x L) :
    Nat.card (ggGamma L hBN).range * p = Nat.card B := by
  have := Fact.mk hp
  have h1 := card_range_mul_card_ker (ggGamma L hBN)
  rw [ker_ggGamma L hBN hp hS] at h1
  have hxB : x ∈ B := hS.2.1
  have h2 : Nat.card ((Subgroup.zpowers x).subgroupOf B) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 x hxB) hS.2.2.1]
  rwa [h2] at h1

end Gamma

@[expose] def GGEndNode (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
        ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

section Reduction

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_sup_zpowers {L : Subgroup G} {x d : G}
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers d : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer ({d} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hg⟩
    refine ⟨hgL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hg d
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))).symm
  · rintro ⟨hgL, hgd⟩
    refine ⟨hgL, ?_⟩
    have h1 : Subgroup.zpowers x ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)).symm
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hgd).symm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hh)

theorem ggStdSubPreInput_of_labels
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGEndNode p r R I) :
    GGStdSubPreInput := by
  intro G _ _ p B x L hT
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hM := largeEvenMarking_and_labelAll (S := fun lab => LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hst.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, r, hlift, hend⟩ := largeEvenRawDatum_exists hraw
  set γ := ggGamma L hBN with hγ
  have hBp : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hS.1.1.2 b b.2)
  have hBc : ∀ a b : B, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hS.1.1 a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBN b, ggBeta_mem L θ hBN h3 b, fun l => ggBeta_ggQuotHom L hBN θ b l⟩
  have hcA := card_range_ggGamma_mul L hBN hp hS
  have hcβ := card_range_ggBeta_mul L θ hp hS hL hBN
  have hAβ : Nat.card γ.range = Nat.card (ggBeta L θ hBN).range :=
    Nat.eq_of_mul_eq_mul_right hp.pos (hcA.trans hcβ.symm)
  have hr : p ^ r ≤ Nat.card γ.range := by
    rw [hAβ]
    exact pow_le_card_range_ggBeta hp hS hL θ hBN hlift
  have h3' : p ^ 3 ≤ Nat.card γ.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
    rw [← hcA, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  obtain ⟨a, haA, ha1, hcomp, hcent⟩ := hend L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hL γ.range hA hAI hr h3'
  obtain ⟨d, rfl⟩ := haA
  have hxB : x ∈ B := hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hdx : (d : G) ∉ Subgroup.zpowers x := by
    intro hd
    apply ha1
    rw [ggGamma_eq_one_iff]
    rw [← inf_centralizer_eq_zpowers_of_sstar hp hS] at hd
    exact hd.2
  have hdp : (d : G) ^ p = 1 := hS.1.1.2 d d.2
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hd1 : (d : G) ≠ 1 := fun h => hdx (h ▸ one_mem _)
  set D : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers (d : G) with hD
  set J' := LargeEvenLayer (ggFix (γ d)) with hJ'
  have hJ'fix : J' ≤ ggFix (γ d) := sSup_le fun K hK => hK.1
  have hfix : (ggFix (γ d)).map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBN d
  have hDB : D ≤ B := sup_le (Subgroup.zpowers_le.mpr hxB) (Subgroup.zpowers_le.mpr d.2)
  refine ⟨D, J'.map L.subtype, hDB, isElemAbelian_mono hS.1.1 hDB, ?_,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x), ?_, ?_, ?_⟩
  ·
    have hN : Subgroup.zpowers (d : G) ≤
        Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      intro y hy
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact IsElemAbelian.comm hS.1.1 (Subgroup.zpowers_le.mpr hxB hz)
        (Subgroup.zpowers_le.mpr d.2 hy)
    have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers (d : G)) := by
      have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers (d : G) : Subgroup G) ∣ p := by
        have := Subgroup.card_dvd_of_le
          (inf_le_right : Subgroup.zpowers x ⊓ Subgroup.zpowers (d : G) ≤ _)
        rwa [Nat.card_zpowers, orderOf_eq_prime hdp hd1] at this
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · rw [disjoint_iff]
        exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hdx
        have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers (d : G) = Subgroup.zpowers (d : G) :=
          Subgroup.eq_of_le_of_card_ge inf_le_right
            (by rw [h1, Nat.card_zpowers, orderOf_eq_prime hdp hd1])
        have hmem : (d : G) ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers (d : G) := by
          rw [heq]
          exact Subgroup.mem_zpowers _
        exact hmem.1
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj,
      Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hxp hS.2.2.1,
      orderOf_eq_prime hdp hd1, sq]
  ·
    rw [← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  ·
    rw [← hfix]
    exact isComponentOf_map_of_injective _ L.subtype_injective hcomp
  ·
    apply le_antisymm
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

end Reduction

end CFSG.StandardType
