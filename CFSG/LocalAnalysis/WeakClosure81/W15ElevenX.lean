module

public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteen
public import CFSG.LocalAnalysis.WeakClosure81.SevenInH
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenShape
public import CFSG.LocalAnalysis.WeakClosure81.W15TenSeven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure XData15 (V₀ U H Q₀ : Subgroup G) (p : ℕ) (X : Subgroup G) (v : G) : Prop where
  sylow : IsSylowIn p X (kHull15 V₀ H)
  le : X ≤ Q₀
  inf_eq : X ⊓ iHull15 V₀ U H = ⊥
  sup_eq : X ⊔ iHull15 V₀ U H = Q₀
  mem : v ∈ V₀
  not_mem : v ∉ iHull15 V₀ U H
  normalizes : v ∈ normalizer (X : Set G)
  comm_eq : ⁅X, zpowers v⁆ = X
  cent : iHull15 V₀ U H ⊓ centralizer (X : Set G) = ⊥
  commutator_eq : ⁅iHull15 V₀ U H, zpowers v⁆ = v1Sub15 V₀ U
  heis : Nat.card ↥X = p ^ 3 → ∃ x z g : G, HeisConfig p X v x z g ∧
    iHull15 V₀ U H ⊓ centralizer ({z} : Set G) = ⊥ ∧
    iHull15 V₀ U H ⊓ centralizer ({x} : Set G) ≤ centralizer ({v} : Set G)

private theorem b15_relIndex_sup_eq_relIndex_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B h) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

private theorem b15_heisConfig_map {K : Type} [Group K] (f : K →* G)
    (hf : Function.Injective f) {p : ℕ} {P : Subgroup K} {v x z g : K}
    (h : HeisConfig p P v x z g) :
    HeisConfig p (P.map f) (f v) (f x) (f z) (f g) where
  x_mem := Subgroup.mem_map_of_mem f h.x_mem
  z_mem := Subgroup.mem_map_of_mem f h.z_mem
  g_mem := Subgroup.mem_map_of_mem f h.g_mem
  x_pow := by rw [← map_pow, h.x_pow, map_one]
  g_pow := by rw [← map_pow, h.g_pow, map_one]
  z_pow := by rw [← map_pow, h.z_pow, map_one]
  z_ne_one := fun h1 => h.z_ne_one (hf (by rw [h1, map_one]))
  z_central := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [map_mul] using congrArg f (h.z_central y hy)
  g_conj_x := by simpa [map_mul, map_inv] using congrArg f h.g_conj_x
  v_conj_x := by simpa [map_mul, map_inv] using congrArg f h.v_conj_x
  v_comm_z := by simpa [map_mul] using congrArg f h.v_comm_z
  le_closure := by
    have h1 := Subgroup.map_mono (f := f) h.le_closure
    rwa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton] at h1
  centralizer_le := by
    rintro _ ⟨y, hy, rfl⟩ hcomm
    have hvy : v * y = y * v := hf (by rw [map_mul, map_mul]; exact hcomm)
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem f (h.centralizer_le y hy hvy)
  v_conj_mem := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, hc, hvy⟩ := h.v_conj_mem y hy
    refine ⟨f c, ?_, ?_⟩
    · rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem f hc
    · simpa [map_mul, map_inv] using congrArg f hvy

section Certified


private theorem b15_W15ElevenX_pair {V H E Q : Subgroup G} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hVΩ : V ∈ omegaSet V H E)
    (hQK : Q ≤ kSub V H E) (hIQ : iSub V H E ≤ Q)
    (hQnorm : (Q.subgroupOf (kSub V H E)).Normal) (hKQV : kSub V H E = Q ⊔ V)
    [((iSub V H E).subgroupOf Q).Normal]
    (hnil : Group.IsNilpotent (↥Q ⧸ (iSub V H E).subgroupOf Q))
    (hQp : IsPGroup p (↥Q ⧸ (iSub V H E).subgroupOf Q))
    (hodd : Odd ((iSub V H E).relIndex Q)) (hQI : ¬ Q ≤ iSub V H E) :
    ∃ P : Subgroup G, ∃ v : G,
      P ≤ Q ∧ P ⊓ iSub V H E = ⊥ ∧ P ⊔ iSub V H E = Q ∧
      v ∈ V ∧ v ∉ iSub V H E ∧ v ∈ normalizer (P : Set G) ∧
      ⁅P, zpowers v⁆ = P ∧ iSub V H E ⊓ centralizer (P : Set G) = ⊥ ∧
      ⁅iSub V H E, zpowers v⁆ = V ⊓ iSub V H E ∧
      (Nat.card ↥P = p ^ 3 → CFSG.IsExtraspecial p ↥P → Monoid.exponent ↥P = p →
        ∃ x z g : G, HeisConfig p P v x z g ∧
          iSub V H E ⊓ centralizer ({z} : Set G) = ⊥ ∧
          iSub V H E ⊓ centralizer ({x} : Set G) ≤ centralizer ({v} : Set G)) := by
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  have hQH : Q ≤ H := hQK.trans hKH
  have hIO : iSub V H E ≤ pCoreOf 2 H := iSup₂_le fun U _ => inf_le_right
  have hIH : iSub V H E ≤ H := hIO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHI : H ≤ normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal hEH hEnorm)
  have hVK : V ≤ kSub V H E := le_kSub hVΩ
  have hIe : IsElemAbelian 2 (iSub V H E) := seven_two_iSub_isElemAbelian_uncond hV hTI hE hOmH
  have hindex : (V ⊓ iSub V H E).relIndex V = 2 :=
    relIndex_inf_iSub_eq_two hV hTI hE hEH hEnorm hOmH hVΩ hQK hIQ hQnorm hKQV hodd hQI
  have hU2 : ∀ U ∈ omegaSet V H E, (U ⊓ iSub V H E).relIndex U = 2 := fun U hU =>
    relIndex_inf_iSub_eq_two_of_mem_omegaSet hV hEH hEnorm hOmH hQK hIQ hQnorm hKQV hodd hindex hU
  have hgenQ : Q ≤ iSub V H E ⊔ ⁅Q, V⁆ :=
    le_iSub_sup_commutator hV hEH hEnorm hOmH hQK hIQ hQnorm hKQV hodd
  have hIK : iSub V H E ≤ ⁅iSub V H E, kSub V H E⁆ :=
    iSub_le_commutator_kSub hV hTI hE hEH hEnorm hOmH hU2
  have hVnI : ¬ V ≤ iSub V H E := by
    intro h
    obtain ⟨g, -, -, hnot⟩ := mem_omegaSet.mp hVΩ
    exact hnot (h.trans hIO)
  obtain ⟨v, hvV, hvI⟩ := Set.not_subset.mp hVnI
  have hv : v * v = 1 := elemAbelian_mul_self hV hvV
  have hVv : V ≤ zpowers v ⊔ iSub V H E :=
    (le_zpowers_sup_of_relIndex_eq_two inf_le_left hindex hvV (fun h => hvI h.2)).trans
      (sup_le_sup_left inf_le_right _)
  obtain ⟨P, hPQ, hPI, hPIQ, hvP⟩ := exists_complement_normalized_by_involution hV hTI hE hEH
    hEnorm hOmH hVΩ hQK hIQ hQnorm hindex hodd hnil hvV hvI
  obtain ⟨e⟩ := exists_mulEquiv_quotient_of_complement hPQ hPI hPIQ
  have hP : IsPGroup p ↥P := hQp.of_equiv e.symm
  have hvN : v ∈ normalizer (iSub V H E : Set G) := hHI (hKH (hVK hvV))
  have hPv : ⁅P, zpowers v⁆ = P :=
    commutator_zpowers_eq_of_complement (hQH.trans hHI) hvN hPI hPIQ hvP hVv hgenQ
  have hPH : P ≤ H := hPQ.trans hQH
  have hPN : P ≤ normalizer (iSub V H E : Set G) := hPH.trans hHI
  have hKle : kSub V H E ≤ iSub V H E ⊔ P ⊔ zpowers v := by
    rw [hKQV, ← hPIQ]
    exact sup_le (sup_le (le_sup_of_le_left le_sup_right) (le_sup_of_le_left le_sup_left))
      (hVv.trans (sup_le le_sup_right (le_sup_of_le_left le_sup_left)))
  have hIgen : iSub V H E ≤ ⁅iSub V H E, iSub V H E ⊔ P ⊔ zpowers v⁆ :=
    hIK.trans (Subgroup.commutator_mono le_rfl hKle)
  have hcent : iSub V H E ⊓ centralizer (P : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_commutator_generation hp hIe hP hPN hvN hv hvP hIgen
  have hcommI : ⁅iSub V H E, zpowers v⁆ = V ⊓ iSub V H E := by
    have hN := nVSub_eq_inf_iSub_of_relIndex_eq_two hV hTI hE hEH hEnorm hOmH hindex
    exact commutator_iSub_eq_inf_iSub hV hTI hE hEH hEnorm hOmH hVΩ hN hvV hvI
  refine ⟨P, v, hPQ, hPI, hPIQ, hvV, hvI, hvP, hPv, hcent, hcommI, ?_⟩
  intro hcard hextP hexpP
  haveI : CFSG.IsExtraspecial p ↥P := hextP
  obtain ⟨x, z, g, cfg⟩ := exists_heisConfig hp hcard hexpP hv hvP hPv
  have hT : ∀ y ∈ normalizer (iSub V H E : Set G),
      ∀ w ∈ ⁅iSub V H E, zpowers v⁆, w ≠ 1 →
      y ∈ centralizer ({w} : Set G) → ⁅v, y⁆ ∈ iSub V H E := fun y hy w hw hw1 hyw =>
    commutator_mem_iSub_of_mem_centralizer hV hTI hE hEH hEnorm hOmH hVΩ hindex hvV hvI hy hw hw1
      hyw
  have hCz : iSub V H E ⊓ centralizer ({z} : Set G) = ⊥ :=
    inf_centralizer_eq_bot hp hIe hP hPN hvN hv hvP cfg hPI hPv hIgen hT
  have hCx : iSub V H E ⊓ centralizer ({x} : Set G) ≤ centralizer ({v} : Set G) :=
    inf_centralizer_le_centralizer_involution hPN hvN hvP cfg hPI hT
  exact ⟨x, z, g, cfg, hCz, hCx⟩

private theorem b15_W15ElevenX_pair_in {V H E Q I : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hVH : V ≤ H)
    (hE : IsMulCommutative E) (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hVΩ : V ∈ omegaSet V H E) (hI : I = conjClosure (V ⊓ pCoreOf 2 H) H)
    (hQK : Q ≤ conjClosure V H) (hIQ : I ≤ Q) (hQnorm : H ≤ normalizer (Q : Set G))
    (hKQV : conjClosure V H = Q ⊔ V) [(I.subgroupOf Q).Normal]
    (hQp : IsPGroup p (↥Q ⧸ I.subgroupOf Q)) (hodd : Odd (I.relIndex Q)) (hQI : ¬ Q ≤ I) :
    ∃ P : Subgroup G, ∃ v : G,
      P ≤ Q ∧ P ⊓ I = ⊥ ∧ P ⊔ I = Q ∧ v ∈ V ∧ v ∉ I ∧ v ∈ normalizer (P : Set G) ∧
      ⁅P, zpowers v⁆ = P ∧ I ⊓ centralizer (P : Set G) = ⊥ ∧ ⁅I, zpowers v⁆ = V ⊓ I ∧
      (Nat.card ↥P = p ^ 3 → CFSG.IsExtraspecial p ↥P → Monoid.exponent ↥P = p →
        ∃ x z g : G, HeisConfig p P v x z g ∧ I ⊓ centralizer ({z} : Set G) = ⊥ ∧
          I ⊓ centralizer ({x} : Set G) ≤ centralizer ({v} : Set G)) := by
  have hQH : Q ≤ H := hQK.trans (conjClosure_le fun k hk z hz =>
    H.mul_mem (H.mul_mem hk (hVH hz)) (H.inv_mem hk))
  have hIH : I ≤ H := hIQ.trans hQH
  have hf : Function.Injective H.subtype := Subgroup.subtype_injective H
  have hKeq := kSub_subgroupOf_top hVH hEnorm hVΩ
  have hIeq : iSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) = I.subgroupOf H := by
    rw [iSub_subgroupOf_top hVH hEnorm hVΩ, hI]
  haveI hQhat : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2 hQnorm
  haveI hIhat : (I.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).2
      (by rw [hI]; exact le_normalizer_conjClosure _ _)
  haveI : ((iSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H)).subgroupOf
      (Q.subgroupOf H)).Normal := by
    rw [hIeq]
    infer_instance
  have he : ((iSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H)).subgroupOf
      (Q.subgroupOf H)).map (Subgroup.subgroupOfEquivOfLe hQH : ↥(Q.subgroupOf H) →* ↥Q) =
      I.subgroupOf Q := by
    rw [hIeq]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hz))
    · intro hy
      exact ⟨⟨⟨y, hQH y.2⟩, y.2⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy)), rfl⟩
  have hQp' : IsPGroup p (↥(Q.subgroupOf H) ⧸
      (iSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H)).subgroupOf (Q.subgroupOf H)) :=
    hQp.of_equiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hQH) he).symm
  obtain ⟨P, v, hPQ, hPI, hPIQ, hvV, hvI, hvN, hPv, hcent, hcomm, hheis⟩ :=
    b15_W15ElevenX_pair (G := ↥H) (V := V.subgroupOf H) (H := ⊤) (E := E.subgroupOf H)
      (Q := Q.subgroupOf H) hp (isElemAbelian_subgroupOf hV) (isTI_subgroupOf hVH hTI)
      (isMulCommutative_subgroupOf hE) le_top (hEnorm.subgroupOf ⊤) (fun _ _ => le_top)
      (subgroupOf_mem_omegaSet hVΩ hVH)
      (by rw [hKeq]; exact fun x hx => hQK hx) (by rw [hIeq]; exact fun x hx => hIQ hx)
      (by haveI := hQhat; infer_instance)
      (by rw [hKeq, hKQV, Subgroup.subgroupOf_sup hQH hVH]) hQp'.isNilpotent hQp'
      (by rw [hIeq, Subgroup.relIndex_subgroupOf hQH]; exact hodd)
      (by
        rw [hIeq]
        exact fun hle => hQI fun x hx => hle (show (⟨x, hQH hx⟩ : ↥H) ∈ Q.subgroupOf H from hx))
  rw [hIeq] at hPI hPIQ hvI hcent hcomm hheis
  have hmapI : (I.subgroupOf H).map H.subtype = I := Subgroup.map_subgroupOf_eq_of_le hIH
  have hmapV : (V.subgroupOf H).map H.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVH
  have hmapQ : (Q.subgroupOf H).map H.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQH
  refine ⟨P.map H.subtype, H.subtype v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono hPQ).trans hmapQ.le
  · rw [← hmapI, ← Subgroup.map_inf _ _ _ hf, hPI, Subgroup.map_bot]
  · rw [← hmapI, ← Subgroup.map_sup, hPIQ, hmapQ]
  · exact Subgroup.mem_subgroupOf.mp hvV
  · exact fun h => hvI (Subgroup.mem_subgroupOf.mpr h)
  · exact Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map.mpr ⟨v, hvN, rfl⟩)
  · rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, hPv]
  · rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hyH : y ∈ H := hIH (Subgroup.mem_inf.mp hy).1
    have hyc : (⟨y, hyH⟩ : ↥H) ∈ I.subgroupOf H ⊓ Subgroup.centralizer (P : Set ↥H) := by
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 (s : G)
        ⟨s, hs, rfl⟩
      exact Subtype.ext h1
    rw [hcent] at hyc
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hyc)
  · have h1 := congrArg (Subgroup.map H.subtype) hcomm
    rw [Subgroup.map_commutator, hmapI, MonoidHom.map_zpowers,
      Subgroup.map_inf _ _ _ hf, hmapV, hmapI] at h1
    exact h1
  · intro hcard hext hexp
    have e := Subgroup.equivMapOfInjective P H.subtype hf
    haveI := hext
    obtain ⟨x, z, g, cfg, hz, hx⟩ := hheis ((Nat.card_congr e.toEquiv).trans hcard)
      (isExtraspecial_of_mulEquiv e) ((Monoid.exponent_eq_of_mulEquiv e).trans hexp)
    refine ⟨H.subtype x, H.subtype z, H.subtype g, b15_heisConfig_map H.subtype hf cfg, ?_, ?_⟩
    · rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have hyH : y ∈ H := hIH (Subgroup.mem_inf.mp hy).1
      have hyc : (⟨y, hyH⟩ : ↥H) ∈ I.subgroupOf H ⊓ Subgroup.centralizer ({z} : Set ↥H) := by
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).1, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 (s : G)
          (Set.mem_singleton _))
      rw [hz] at hyc
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hyc)
    · intro y hy
      have hyH : y ∈ H := hIH (Subgroup.mem_inf.mp hy).1
      have hyc : (⟨y, hyH⟩ : ↥H) ∈ I.subgroupOf H ⊓ Subgroup.centralizer ({x} : Set ↥H) := by
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).1, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 (s : G)
          (Set.mem_singleton _))
      have hv := Subgroup.mem_centralizer_iff.mp (hx hyc) v (Set.mem_singleton _)
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact congrArg Subtype.val hv

theorem Cfg1511.exists_xData {M V₀ V U S H P Q₀ : Subgroup G} {p : ℕ}
    (c : Cfg1511 M V₀ V U S H P Q₀ p) : ∃ (X : Subgroup G) (v : G), XData15 V₀ U H Q₀ p X v := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  haveI hNormI : ((iHull15 V₀ U H).subgroupOf Q₀).Normal := c.normal_subgroupOf
  have hIeq : iHull15 V₀ U H = conjClosure (V₀ ⊓ pCoreOf 2 H) H := by
    rw [iHull15, Hyp1510.inf_pCoreOf_eq c.w81 c.std c.cex c.hyp]
  obtain ⟨X, v, hXle, hXinf, hXsup, hvV, hvI, hvN, hXv, hXcent, hXcomm, hXheis⟩ :=
    b15_W15ElevenX_pair_in c.p_ne_two c.cex.hyp.elemAbelian₀ c.cex.hyp.isTI c.hyp.V₀_le_H
      (c.hyp.isMulCommutative_eSub15 c.std c.cex) c.hyp.eSub15_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer c.hyp.eSub15_le).2
        (Hyp1510.le_normalizer_eSub15 V₀ P H))
      (c.hyp.mem_omegaSet_self c.inputs c.std c.cex) hIeq c.odd.le_kHull c.odd.iHull_le
      c.odd.normal c.odd.sup_eq.symm c.isPGroup_quot c.odd.odd c.not_le_iHull15
  have hQnormI : Q₀ ≤ normalizer (iHull15 V₀ U H : Set G) :=
    (OddCore15.le_H c.hyp c.odd).trans (Hyp1510.le_normalizer_iHull15 V₀ U H)
  have hXnormN : X ≤ normalizer (iHull15 V₀ U H : Set G) := hXle.trans hQnormI
  have hXrelQ : X.relIndex Q₀ = Nat.card (iHull15 V₀ U H) := by
    have h1 : X.relIndex Q₀ = X.relIndex (iHull15 V₀ U H ⊔ X) := by
      rw [← hXsup, sup_comm]
    rw [h1, b15_relIndex_sup_eq_relIndex_of_le_normalizer hXnormN,
      ← Subgroup.inf_relIndex_right X (iHull15 V₀ U H), hXinf, Subgroup.relIndex_bot_left]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI2 : IsPGroup 2 (iHull15 V₀ U H) :=
    c.hyp.sylow.isPGroup.to_le (c.hyp.iHull15_le_P c.cex)
  obtain ⟨k, hk⟩ := hI2.exists_card_eq
  have hXrelK : X.relIndex (kHull15 V₀ H) = 2 ^ k * 2 := by
    rw [← Subgroup.relIndex_mul_relIndex X Q₀ (kHull15 V₀ H) hXle c.odd.le_kHull,
      c.relIndex_Q₀_kHull15, hXrelQ, hk]
  have hnotdvd : ¬ p ∣ X.relIndex (kHull15 V₀ H) := by
    rw [hXrelK]
    intro hdiv
    have hdiv' : p ∣ 2 ^ (k + 1) := by rw [pow_succ]; exact hdiv
    exact c.p_ne_two ((Nat.prime_dvd_prime_iff_eq c.prime Nat.prime_two).mp
      (c.prime.dvd_of_dvd_pow hdiv'))
  have hXK : X ≤ kHull15 V₀ H := hXle.trans c.odd.le_kHull
  obtain ⟨e⟩ := exists_mulEquiv_quotient_of_complement hXle hXinf hXsup
  have hXp : IsPGroup p ↥X := c.isPGroup_quot.of_equiv e.symm
  have hcommEq : ⁅iHull15 V₀ U H, zpowers v⁆ = v1Sub15 V₀ U := by
    rwa [Hyp1510.inf_iHull15_eq c.w81 c.std c.cex c.hyp] at hXcomm
  refine ⟨X, v, ⟨hXK, hXp, hnotdvd⟩, hXle, hXinf, hXsup, hvV, hvI, hvN, hXv, hXcent, hcommEq, ?_⟩
  intro hcardX
  have hcardN : Nat.card (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) = p ^ 3 :=
    (nat_card_eq_of_complement hXle hXinf hXsup).symm.trans hcardX
  have hshape := c.shape
  simp only [OddCoreShape15] at hshape
  rcases hshape with h1 | ⟨-, hextI, hexpI⟩
  · exfalso
    rw [h1] at hcardN
    have hp2 : p ^ 2 = 1 := by
      have hp3 : p * p ^ 2 = p * 1 := by
        calc p * p ^ 2 = p ^ 3 := by ring
          _ = p := hcardN.symm
          _ = p * 1 := by ring
      exact mul_left_cancel₀ c.prime.ne_zero hp3
    exact c.prime.ne_one (Nat.dvd_one.mp (hp2 ▸ dvd_pow_self p (by norm_num : 2 ≠ 0)))
  · haveI := hextI
    haveI hExtX : CFSG.IsExtraspecial p ↥X := isExtraspecial_of_complement hXle hXinf hXsup
    have hXexp : Monoid.exponent ↥X = p :=
      (exponent_eq_of_complement hXle hXinf hXsup).trans hexpI
    exact hXheis hcardX hExtX hXexp

end Certified

namespace XData15

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem isPGroup (hX : XData15 V₀ U H Q₀ p X v) : IsPGroup p ↥X := hX.sylow.isPGroup

theorem le_kHull15 (hX : XData15 V₀ U H Q₀ p X v) : X ≤ kHull15 V₀ H := hX.sylow.le

theorem le_H (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) : X ≤ H :=
  hX.le_kHull15.trans c.hyp.kHull15_le

theorem mul_self (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) : v * v = 1 :=
  CFSG.Open.IsElemAbelian.mul_self_eq_one c.cex.hyp.elemAbelian₀ hX.mem

theorem le_zpowers_sup (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    V₀ ≤ zpowers v ⊔ v1Sub15 V₀ U := by
  refine le_zpowers_sup_of_relIndex_eq_two (A := v1Sub15 V₀ U) (V := V₀)
    (v1Sub15_le_left V₀ U) (c.w81.relIndex_eq_two c.std c.cex) hX.mem ?_
  intro hv1
  exact hX.not_mem (Hyp1510.v1Sub15_le_iHull15 V₀ U H hv1)

theorem conjClosure_eq (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) : conjClosure (v1Sub15 V₀ U) X = iHull15 V₀ U H := by
  refine le_antisymm ?_ ?_
  · rw [iHull15]
    exact conjClosure_mono le_rfl (hX.le_H c)
  · rw [iHull15]
    refine conjClosure_le fun g hg z hz => ?_
    obtain ⟨k, hk, m, hm, hgkm⟩ :=
      Hyp1510.exists_mul_mem_inf (M := M) (V₀ := V₀) (V := V) (U := U) (S := S) (H := H) (P := P)
        c.inputs c.std c.cex c.hyp g hg
    have hmM : m ∈ M := (Subgroup.mem_inf.mp hm).2
    have hz'n : m * z * m⁻¹ ∈ v1Sub15 V₀ U :=
      (Subgroup.mem_normalizer_iff.1
        (Cex15.normal_v1Sub15 (M := M) (V₀ := V₀) (V := V) (U := U) (S := S)
          c.inputs c.std c.cex hmM) z).1 hz
    obtain ⟨x, hx, i, hi, w, hw, hkiw⟩ := c.exists_mul_mul_of_mem_kHull15 hX.sylow hk
    have hi1 : i ∈ iHull15 V₀ U H ⊔ U := Subgroup.mem_sup_left hi
    have hz'1 : m * z * m⁻¹ ∈ iHull15 V₀ U H ⊔ U :=
      Subgroup.mem_sup_left (Hyp1510.v1Sub15_le_iHull15 V₀ U H hz'n)
    have hwz' : w * (m * z * m⁻¹) * w⁻¹ = m * z * m⁻¹ := by
      have hcomm : w * (m * z * m⁻¹) = (m * z * m⁻¹) * w :=
        B2F.isElemAbelian_comm c.cex.hyp.elemAbelian₀ hw (v1Sub15_le_left V₀ U hz'n)
      rw [hcomm]; group
    have hiz' : i * (m * z * m⁻¹) * i⁻¹ = m * z * m⁻¹ := by
      have hcomm : i * (m * z * m⁻¹) = (m * z * m⁻¹) * i :=
        c.hyp.comm_iHull15_sup i hi1 (m * z * m⁻¹) hz'1
      rw [hcomm]; group
    have hmain : g * z * g⁻¹ = x * (m * z * m⁻¹) * x⁻¹ := by
      have h1 : g * z * g⁻¹ = k * (m * z * m⁻¹) * k⁻¹ := by
        rw [hgkm]; group
      have h2 : k * (m * z * m⁻¹) * k⁻¹ = x * (m * z * m⁻¹) * x⁻¹ := by
        rw [hkiw]
        calc (x * i * w) * (m * z * m⁻¹) * (x * i * w)⁻¹
            = x * (i * (w * (m * z * m⁻¹) * w⁻¹) * i⁻¹) * x⁻¹ := by group
          _ = x * (m * z * m⁻¹) * x⁻¹ := by rw [hwz', hiz']
      rw [h1, h2]
    rw [hmain]
    exact mem_conjClosure hx hz'n

end XData15

end CFSG.LocalAnalysis.WeakClosure81
