module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Facts
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.RankThree.PartOne.S12.Sec15Frattini
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Quasithin.H13.L32A.C.SkPf (mem_centMod map_eq_of_forall_mem isSylowTwoOf_sylow)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def piInf (L : Subgroup G) : ↥L →* BarInf L := QuotientGroup.mk' (CFSG.solvableRadical ↥L)

@[expose] noncomputable def barAutInf (L : Subgroup G) : MulAut ↥L →* MulAut (BarInf L) where
  toFun φ := QuotientGroup.congr (CFSG.solvableRadical ↥L) (CFSG.solvableRadical ↥L) φ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

@[expose] noncomputable def rhoInf (L : Subgroup G) :
    ↥(normalizer (L : Set G)) →* MulAut (BarInf L) :=
  (barAutInf L).comp (Subgroup.normalizerMonoidHom L)

omit [Finite G] in
theorem rhoInf_mk (L : Subgroup G) (m : ↥(normalizer (L : Set G))) (x : ↥L) :
    rhoInf L m (piInf L x) = piInf L (Subgroup.normalizerMonoidHom L m x) := rfl

omit [Finite G] in
theorem rhoInf_mk_coe (L : Subgroup G) (m : ↥(normalizer (L : Set G))) (x : ↥L) :
    ((Subgroup.normalizerMonoidHom L m x : ↥L) : G) = (m : G) * (x : G) * (m : G)⁻¹ := by
  simp

omit [Finite G] in
theorem OInf_le (L : Subgroup G) : OInf L ≤ L := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

omit [Finite G] in
theorem OInf_subgroupOf (L : Subgroup G) : (OInf L).subgroupOf L = CFSG.solvableRadical ↥L :=
  Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

omit [Finite G] in
theorem mem_OInf_iff {L : Subgroup G} {x : ↥L} :
    (x : G) ∈ OInf L ↔ x ∈ CFSG.solvableRadical ↥L := by
  rw [← Subgroup.mem_subgroupOf, OInf_subgroupOf]

omit [Finite G] in
theorem le_normalizer_OInf (L : Subgroup G) : L ≤ normalizer (OInf L : Set G) := by
  have h : ((OInf L).subgroupOf L).Normal := by
    rw [OInf_subgroupOf]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (OInf_le L)).1 h

omit [Finite G] in
theorem normalizer_le_normalizer_OInf (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (OInf L : Set G) := by
  have key : ∀ t ∈ normalizer (L : Set G), ∀ x ∈ OInf L, t * x * t⁻¹ ∈ OInf L := by
    intro t ht x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Subgroup.normalizerMonoidHom L ⟨t, ht⟩ y, ?_, by simp⟩
    have hfix : (CFSG.solvableRadical ↥L).map (Subgroup.normalizerMonoidHom L ⟨t, ht⟩).toMonoidHom =
        CFSG.solvableRadical ↥L :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance _
    rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  intro t ht
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have h1 := key t⁻¹ (inv_mem ht) _ hx
  rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h1

omit [Finite G] in
theorem mem_sup_OInf_iff (L : Subgroup G) (Q : Subgroup ↥L) {x : ↥L} :
    (x : G) ∈ Q.map L.subtype ⊔ OInf L ↔ piInf L x ∈ Q.map (piInf L) := by
  have hQK : Q.map L.subtype ≤ normalizer (OInf L : Set G) :=
    (Subgroup.map_subtype_le Q).trans (le_normalizer_OInf L)
  constructor
  · intro hx
    have hx' : (x : G) ∈ ((Q.map L.subtype : Subgroup G) : Set G) * (OInf L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hQK]
      exact hx
    obtain ⟨s, ⟨q, hq, rfl⟩, k, hk, hsk⟩ := Set.mem_mul.mp hx'
    obtain ⟨r, hr, rfl⟩ := hk
    have : x = q * r := Subtype.ext hsk.symm
    refine ⟨q, hq, ?_⟩
    rw [this, map_mul]
    have : piInf L r = 1 := (QuotientGroup.eq_one_iff r).2 hr
    rw [this, mul_one]
  · rintro ⟨q, hq, hqx⟩
    have h1 : x * q⁻¹ ∈ CFSG.solvableRadical ↥L := by
      have : piInf L (x * q⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hqx, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    have h2 : ((x * q⁻¹ : ↥L) : G) ∈ OInf L := mem_OInf_iff.2 h1
    have h3 : (x : G) = ((x * q⁻¹ : ↥L) : G) * (q : G) := by simp
    rw [h3]
    exact mul_mem (mem_sup_right h2) (mem_sup_left ⟨q, hq, rfl⟩)

theorem isSylowTwoOf_map_piInf (L : Subgroup G) (Q : Sylow 2 ↥L) :
    IsSylowTwoOf ((Q : Subgroup ↥L).map (piInf L)) ⊤ :=
  isSylowTwoOf_sylow (Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L)))

theorem rhoInf_map_eq (L : Subgroup G) (Q : Subgroup ↥L) {t : G} (htL : t ∈ normalizer (L : Set G))
    (htS : t ∈ normalizer ((Q.map L.subtype ⊔ OInf L : Subgroup G) : Set G)) :
    (Q.map (piInf L)).map (rhoInf L ⟨t, htL⟩).toMonoidHom = Q.map (piInf L) := by
  refine map_eq_of_forall_mem fun u hu => ?_
  obtain ⟨q, hq, rfl⟩ := mem_map.1 hu
  show rhoInf L ⟨t, htL⟩ (piInf L q) ∈ _
  rw [rhoInf_mk]
  refine (mem_sup_OInf_iff L Q).1 ?_
  rw [rhoInf_mk_coe]
  exact (mem_normalizer_iff.1 htS (q : G)).1 (mem_sup_left (mem_map_of_mem L.subtype hq))

omit [Finite G] in
theorem rhoInf_pow_eq_one (L : Subgroup G) {t : G} (htL : t ∈ normalizer (L : Set G)) {a : ℕ}
    (ha : t ^ a = 1) : rhoInf L ⟨t, htL⟩ ^ a = 1 := by
  have h1 : (⟨t, htL⟩ : ↥(normalizer (L : Set G))) ^ a = 1 := Subtype.ext (by simpa using ha)
  rw [← map_pow, h1, map_one]

omit [Finite G] in
theorem conj_mul_inv_mem_of_mem_centMod (L : Subgroup G) (Q : Subgroup ↥L) {t : G}
    (htL : t ∈ normalizer (L : Set G)) {x : ↥L}
    (hx : piInf L x ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod (Q.map (piInf L))
      (rhoInf L ⟨t, htL⟩)) :
    t * (x : G) * t⁻¹ * (x : G)⁻¹ ∈ Q.map L.subtype ⊔ OInf L := by
  obtain ⟨-, hx2⟩ := mem_centMod.1 hx
  have h1 : piInf L (Subgroup.normalizerMonoidHom L ⟨t, htL⟩ x * x⁻¹) ∈ Q.map (piInf L) := by
    rw [map_mul, map_inv]
    exact hx2
  have h2 := (mem_sup_OInf_iff L Q (x := Subgroup.normalizerMonoidHom L ⟨t, htL⟩ x * x⁻¹)).2 h1
  have e : (((Subgroup.normalizerMonoidHom L ⟨t, htL⟩ x * x⁻¹ : ↥L)) : G) =
      t * (x : G) * t⁻¹ * (x : G)⁻¹ := by
    rw [Subgroup.coe_mul, rhoInf_mk_coe, Subgroup.coe_inv]
  rwa [e] at h2


omit [Finite G] in
theorem piInf_mem_normalizer (L : Subgroup G) (Q : Subgroup ↥L) {h : ↥L}
    (hh : (h : G) ∈ normalizer ((Q.map L.subtype ⊔ OInf L : Subgroup G) : Set G)) :
    piInf L h ∈ normalizer ((Q.map (piInf L) : Subgroup (BarInf L)) : Set (BarInf L)) := by
  rw [mem_normalizer_iff]
  intro u
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L) u
  change piInf L z ∈ _ ↔ piInf L h * piInf L z * (piInf L h)⁻¹ ∈ _
  rw [← map_inv, ← map_mul, ← map_mul, ← mem_sup_OInf_iff, ← mem_sup_OInf_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.1 hh z

theorem exists_conj_mul_inv_mem {Tor Out : ℕ → Prop} {L S : Subgroup G} {n s : ℕ}
    (hS : IsSylowOf 2 S L) (hF : TorusFacts218 (BarInf L) n Tor Out) (hs : Odd s) (hsn : s ∣ n) :
    ∃ d : ↥L, orderOf (piInf L d) = 2 ^ s - 1 ∧ ∀ x ∈ zpowers (d : G), ∀ t ∈ normalizer (L : Set G),
      t ∈ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) → (∃ a : ℕ, t ^ 2 ^ a = 1) →
        t * x * t⁻¹ * x⁻¹ ∈ S ⊔ OInf L := by
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨db, hdb, hcent⟩ := hF.exists_mem_centMod (isSylowTwoOf_map_piInf L Q) hs hsn
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L) db
  refine ⟨d, hdb, ?_⟩
  intro x hx t htL htS ⟨a, ha⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
  have h1 : piInf L (d ^ m) ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod
      ((Q : Subgroup ↥L).map (piInf L)) (rhoInf L ⟨t, htL⟩) := by
    rw [map_zpow]
    exact zpow_mem (hcent _ ⟨a, rhoInf_pow_eq_one L htL ha⟩
      (rhoInf_map_eq L (Q : Subgroup ↥L) htL htS)) m
  have h2 := conj_mul_inv_mem_of_mem_centMod L (Q : Subgroup ↥L) htL h1
  rwa [Subgroup.coe_zpow] at h2

theorem exists_pow_conj_mem {Tor Out : ℕ → Prop} {L S : Subgroup G} {n : ℕ}
    (hS : IsSylowOf 2 S L) (hF : TorusFacts218 (BarInf L) n Tor Out) {x : G}
    (hxL : x ∈ normalizer (L : Set G))
    (hxS : x ∈ normalizer ((S ⊔ OInf L : Subgroup G) : Set G)) {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1) :
    ∃ k : ℕ, ∀ h ∈ L, h ∈ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) →
      x * h * x⁻¹ * (h ^ k)⁻¹ ∈ S ⊔ OInf L := by
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨k, hk⟩ := hF.pow_action (isSylowTwoOf_map_piInf L Q)
    (rhoInf_map_eq L (Q : Subgroup ↥L) hxL hxS) hm (rhoInf_pow_eq_one L hxL hxm)
  refine ⟨k, fun h hhL hhN => ?_⟩
  have h1 := hk _ (piInf_mem_normalizer L (Q : Subgroup ↥L) (h := ⟨h, hhL⟩) hhN)
  rw [rhoInf_mk, ← map_pow, ← map_inv, ← map_mul] at h1
  have h2 := (mem_sup_OInf_iff L (Q : Subgroup ↥L)).2 h1
  rwa [Subgroup.coe_mul, rhoInf_mk_coe, Subgroup.coe_inv, Subgroup.coe_pow] at h2

theorem eq_one_of_pow_eq_one_of_facts {Tor Out : ℕ → Prop} {L S : Subgroup G} {n : ℕ}
    (hS : IsSylowOf 2 S L) (hF : TorusFacts218 (BarInf L) n Tor Out) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hOut : Out p) (hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L)) {h : G}
    (hhL : h ∈ L) (hhS : h ∈ normalizer ((S ⊔ OInf L : Subgroup G) : Set G)) (hhp : h ^ p = 1) :
    h = 1 := by
  obtain ⟨Q, rfl⟩ := hS
  have hbp : (piInf L ⟨h, hhL⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨h, hhL⟩ : ↥L) ^ p = 1 := Subtype.ext (by simpa using hhp)
    rw [this, map_one]
  have hb : piInf L ⟨h, hhL⟩ = 1 :=
    hF.eq_one_of_pow_eq_one hp hp2 hOut (isSylowTwoOf_map_piInf L Q)
      (piInf_mem_normalizer L (Q : Subgroup ↥L) (h := ⟨h, hhL⟩) hhS) hbp
  have hR : (⟨h, hhL⟩ : ↥L) ∈ CFSG.solvableRadical ↥L := (QuotientGroup.eq_one_iff _).1 hb
  have hg : (⟨⟨h, hhL⟩, hR⟩ : ↥(CFSG.solvableRadical ↥L)) ^ p = 1 :=
    Subtype.ext (Subtype.ext (by simpa using hhp))
  have h1 : orderOf (⟨⟨h, hhL⟩, hR⟩ : ↥(CFSG.solvableRadical ↥L)) ∣ p :=
    orderOf_dvd_of_pow_eq_one hg
  have h2 := orderOf_dvd_natCard (⟨⟨h, hhL⟩, hR⟩ : ↥(CFSG.solvableRadical ↥L))
  rcases (Nat.dvd_prime hp).1 h1 with h3 | h3
  · have := orderOf_eq_one_iff.1 h3
    exact congrArg (fun z : ↥(CFSG.solvableRadical ↥L) => ((z : ↥L) : G)) this
  · exact absurd (h3 ▸ h2) hpK


theorem not_dvd_card_sup_OInf {L S : Subgroup G} (hS : IsSylowOf 2 S L) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) :
    ¬ r ∣ Nat.card ↥(S ⊔ OInf L) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q, rfl⟩ := hS
  intro hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hyL : ((y : ↥(((Q : Subgroup ↥L).map L.subtype) ⊔ OInf L)) : G) ∈ L :=
    sup_le (Subgroup.map_subtype_le _) (OInf_le L) y.2
  set z : ↥L := ⟨(y : G), hyL⟩ with hz
  have hordz : orderOf z = r := by
    rw [← hy, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  have hzU : piInf L z ∈ (Q : Subgroup ↥L).map (piInf L) :=
    (mem_sup_OInf_iff L (Q : Subgroup ↥L)).1 y.2
  have hd : orderOf (piInf L z) ∣ r := hordz ▸ orderOf_map_dvd _ _
  rcases (Nat.dvd_prime hr).1 hd with h1 | h1
  ·
    have h2 : z ∈ CFSG.solvableRadical ↥L :=
      (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
    have h3 := orderOf_dvd_natCard (⟨z, h2⟩ : ↥(CFSG.solvableRadical ↥L))
    have h4 : orderOf (⟨z, h2⟩ : ↥(CFSG.solvableRadical ↥L)) = r := by
      rw [← hordz, Subgroup.orderOf_mk]
    rw [h4] at h3
    exact hrK h3
  ·
    obtain ⟨u, hu, hue⟩ := hzU
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨u, hu⟩
    have h2 : orderOf (piInf L z) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← hue, ← map_pow]
      have : u ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [this, map_one]
    rw [h1] at h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))

theorem pRank_eq_pRank_barInf {L : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) :
    CFSG.Open.pRank r L = CFSG.Open.pRank r (⊤ : Subgroup (BarInf L)) := by
  have : Fact r.Prime := ⟨hr⟩
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    ← CFSG.SectionRank.pRank_quotient_eq (CFSG.solvableRadical ↥L) hrK]

omit [Finite G] in
theorem mem_normalizer_sup_of_mem {S K : Subgroup G} {g : G} (hS : g ∈ normalizer (S : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((S ⊔ K : Subgroup G) : Set G) := by
  have hle : zpowers g ≤ normalizer ((S ⊔ K : Subgroup G) : Set G) := by
    have hW : S ⊔ K = Subgroup.closure ((S : Set G) ∪ K) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [hW, Subgroup.le_normalizer_closure_iff]
    intro x hx y hy
    rw [← hW]
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
    have hxS : g ^ m ∈ normalizer (S : Set G) := zpow_mem hS m
    have hxK : g ^ m ∈ normalizer (K : Set G) := zpow_mem hK m
    rcases hy with hy | hy
    · exact mem_sup_left ((mem_normalizer_iff.1 hxS y).1 hy)
    · exact mem_sup_right ((mem_normalizer_iff.1 hxK y).1 hy)
  exact hle (mem_zpowers g)

theorem relIndex_sup_eq_relIndex {T K : Subgroup G} (hTK : T ≤ normalizer (K : Set G)) :
    T.relIndex (T ⊔ K) = T.relIndex K := by
  have hKA : K ≤ T ⊔ K := le_sup_right
  have hN : (K.subgroupOf (T ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).mpr (sup_le hTK Subgroup.le_normalizer)
  have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (K.subgroupOf (T ⊔ K))
    (T.subgroupOf (T ⊔ K))
  have h2 : K.subgroupOf (T ⊔ K) ⊔ T.subgroupOf (T ⊔ K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKA le_sup_left, sup_comm]
    exact Subgroup.subgroupOf_self _
  rw [h2, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hKA] at h1
  exact h1

theorem isSylowOf_sup_of_inf {T K : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (h : IsSylowOf 2 (T ⊓ K) K) : IsSylowOf 2 T (T ⊔ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨-, -, hdvd⟩ := h
  refine ⟨le_sup_left, hT, ?_⟩
  rw [relIndex_sup_eq_relIndex hTK, ← Subgroup.inf_relIndex_right]
  exact hdvd

theorem exists_orderOf_eq_mem_normalizer {Tor Out : ℕ → Prop} {L T : Subgroup G} {n s r : ℕ}
    (hF : TorusFacts218 (BarInf L) n Tor Out) (hT : IsPGroup 2 T) (hTL : T ≤ normalizer (L : Set G))
    (hS : IsSylowOf 2 (T ⊓ L) L) (hs : Odd s) (hsn : s ∣ n) (hr : r ∣ 2 ^ s - 1) :
    ∃ y ∈ L, orderOf y = r ∧ zpowers y ≤ normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hdo, hcomm⟩ := exists_conj_mul_inv_mem hS hF hs hsn
  have hTK : T ≤ normalizer (OInf L : Set G) := hTL.trans (normalizer_le_normalizer_OInf L)
  have hdL : (d : G) ∈ L := d.2
  have key : ∀ x ∈ zpowers (d : G), ∀ h ∈ T, x * h * x⁻¹ ∈ T ⊔ OInf L := by
    intro x hx h hh
    have hhL : h⁻¹ ∈ normalizer (L : Set G) := hTL (inv_mem hh)
    have hhS₀ : h⁻¹ ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, ← mem_normalizer_iff.1 (le_normalizer (inv_mem hh)) y,
        ← mem_normalizer_iff.1 hhL y]
    have hhS : h⁻¹ ∈ normalizer (((T ⊓ L : Subgroup G) ⊔ OInf L : Subgroup G) : Set G) :=
      mem_normalizer_sup_of_mem hhS₀ (hTK (inv_mem hh))
    obtain ⟨a, ha⟩ := hT ⟨h⁻¹, inv_mem hh⟩
    have h1 := hcomm x hx h⁻¹ hhL hhS ⟨a, congrArg Subtype.val ha⟩
    have e : x * h * x⁻¹ = h * (h⁻¹ * x * h⁻¹⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left hh)
      ((sup_le_sup_right (inf_le_left : T ⊓ L ≤ T) (OInf L) : (T ⊓ L) ⊔ OInf L ≤ T ⊔ OInf L) h1)
  have hdN : (d : G) ∈ normalizer ((T ⊔ OInf L : Subgroup G) : Set G) := by
    have hW : T ⊔ OInf L = Subgroup.closure ((T : Set G) ∪ OInf L) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    have hle : zpowers (d : G) ≤ normalizer ((T ⊔ OInf L : Subgroup G) : Set G) := by
      rw [hW, Subgroup.le_normalizer_closure_iff]
      intro x hx y hy
      rw [← hW]
      rcases hy with hy | hy
      · exact key x hx y hy
      · have hxL : x ∈ L := by
          obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
          exact zpow_mem hdL m
        exact mem_sup_right ((mem_normalizer_iff.1 (le_normalizer_OInf L hxL) y).1 hy)
    exact hle (mem_zpowers _)
  have hK : IsSylowOf 2 ((T ⊓ L) ⊓ OInf L) (OInf L) :=
    hS.inf_of_le_normalizer (OInf_le L) (le_normalizer_OInf L)
  rw [inf_assoc, inf_eq_right.2 (OInf_le L)] at hK
  have hTsyl : IsSylowOf 2 T (T ⊔ OInf L) := isSylowOf_sup_of_inf hT hTK hK
  obtain ⟨a, ha, hn⟩ := CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf
    hTsyl hdN
  have ha' : a ∈ (OInf L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (OInf L) T hTK]
    exact (sup_comm T (OInf L)) ▸ ha
  obtain ⟨k, hk, h, hh, rfl⟩ := Set.mem_mul.mp ha'
  have hy1N : (k⁻¹ * (d : G)) ∈ normalizer (T : Set G) := by
    have h1 : (h⁻¹ : G) * (k⁻¹ * (d : G)) ∈ normalizer (T : Set G) := by
      simpa [mul_assoc] using hn
    have h2 := mul_mem (le_normalizer hh) h1
    simpa [mul_assoc] using h2
  have hkL : k ∈ L := OInf_le L hk
  have hy1L : k⁻¹ * (d : G) ∈ L := mul_mem (inv_mem hkL) hdL
  set y₁ : ↥L := ⟨k⁻¹ * (d : G), hy1L⟩ with hy₁
  have hpi : piInf L y₁ = piInf L d := by
    have : y₁ = (⟨k, hkL⟩ : ↥L)⁻¹ * d := rfl
    rw [this, map_mul, map_inv]
    have hk1 : piInf L ⟨k, hkL⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (mem_OInf_iff.1 hk)
    rw [hk1, inv_one, one_mul]
  have hrd : r ∣ orderOf y₁ := by
    have h1 : orderOf (piInf L y₁) ∣ orderOf y₁ := orderOf_map_dvd _ _
    rw [hpi, hdo] at h1
    exact hr.trans h1
  have hord1 : orderOf (k⁻¹ * (d : G)) = orderOf y₁ := by
    rw [hy₁, Subgroup.orderOf_mk]
  refine ⟨(k⁻¹ * (d : G)) ^ (orderOf (k⁻¹ * (d : G)) / r), pow_mem hy1L _, ?_,
    (zpowers_le.2 (pow_mem hy1N _))⟩
  have h0 : orderOf (k⁻¹ * (d : G)) ≠ 0 := (orderOf_pos _).ne'
  exact orderOf_pow_orderOf_div h0 (by rw [hord1]; exact hrd)

end CFSG.LocalAnalysis.UniquenessCase.UC22
