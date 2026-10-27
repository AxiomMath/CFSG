module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreSym
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreQ
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def barPre (H : Subgroup G) {Q : Type} [Group Q] (φ : ↥H →* Q) (Xb : Subgroup Q) :
    Subgroup G :=
  (Xb.comap φ).map H.subtype

theorem barPre_le (H : Subgroup G) {Q : Type} [Group Q] (φ : ↥H →* Q) (Xb : Subgroup Q) :
    barPre H φ Xb ≤ H :=
  Subgroup.map_subtype_le (Xb.comap φ)

theorem mem_barPre {H : Subgroup G} {Q : Type} [Group Q] {φ : ↥H →* Q} {Xb : Subgroup Q}
    {g : G} : g ∈ barPre H φ Xb ↔ ∃ hg : g ∈ H, φ ⟨g, hg⟩ ∈ Xb := by
  rw [barPre, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hg⟩
    rw [Subgroup.mem_comap] at hh
    subst hg
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, hgX⟩
    exact ⟨⟨g, hg⟩, by rwa [Subgroup.mem_comap], rfl⟩

theorem le_barPre {H J : Subgroup G} (hJH : J ≤ H) {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H J φ) (Xb : Subgroup Q) : J ≤ barPre H φ Xb := by
  intro j hj
  refine mem_barPre.mpr ⟨hJH hj, ?_⟩
  rw [show φ ⟨j, hJH hj⟩ = 1 from (hφ.ker_iff ⟨j, hJH hj⟩).mpr hj]
  exact Xb.one_mem

theorem barSub_barPre {H J : Subgroup G} {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H J φ) (Xb : Subgroup Q) : barSub H φ (barPre H φ Xb) = Xb := by
  have hsub : (barPre H φ Xb).subgroupOf H = Xb.comap φ := by
    change (((Xb.comap φ).map H.subtype).subgroupOf H) = Xb.comap φ
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  change ((barPre H φ Xb).subgroupOf H).map φ = Xb
  rw [hsub]
  exact Subgroup.map_comap_eq_self_of_surjective hφ.surjective Xb

theorem relIndex_barPre {H J : Subgroup G} (hJH : J ≤ H) {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H J φ) (Xb : Subgroup Q) : J.relIndex (barPre H φ Xb) = Nat.card Xb := by
  rw [← card_barSub_eq_relIndex_of_isBarMap (K := H) (N := J) (A := barPre H φ Xb)
    (barPre_le H φ Xb) hJH hφ, barSub_barPre hφ Xb]

theorem le_normalizer_barPre {H J : Subgroup G} {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H J φ) {Xb : Subgroup Q} {A : Subgroup G} (hAH : A ≤ H)
    (hA : barSub H φ A ≤ Subgroup.normalizer (Xb : Set Q)) :
    A ≤ Subgroup.normalizer ((barPre H φ Xb : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨hgH, hgX⟩ := mem_barPre.mp hg
    have haH : a ∈ H := hAH ha
    have haBar : φ ⟨a, haH⟩ ∈ barSub H φ A := mem_barSub.mpr ⟨⟨a, haH⟩, ha, rfl⟩
    have hnorm := hA haBar
    rw [Subgroup.mem_normalizer_iff] at hnorm
    refine mem_barPre.mpr ⟨H.mul_mem (H.mul_mem haH hgH) (H.inv_mem haH), ?_⟩
    have hphi : φ ⟨a * g * a⁻¹, H.mul_mem (H.mul_mem haH hgH) (H.inv_mem haH)⟩ =
        φ ⟨a, haH⟩ * φ ⟨g, hgH⟩ * (φ ⟨a, haH⟩)⁻¹ := by
      rw [show (⟨a * g * a⁻¹,
          H.mul_mem (H.mul_mem haH hgH) (H.inv_mem haH)⟩ : ↥H) =
          ⟨a, haH⟩ * ⟨g, hgH⟩ * ⟨a, haH⟩⁻¹ from Subtype.ext rfl,
        map_mul, map_mul, map_inv]
    rw [hphi]
    exact (hnorm (φ ⟨g, hgH⟩)).mp hgX
  · intro hg
    obtain ⟨hgH, hgX⟩ := mem_barPre.mp hg
    have haH : a ∈ H := hAH ha
    have hgH' : g ∈ H := by
      rw [show g = a⁻¹ * (a * g * a⁻¹) * a by group]
      exact H.mul_mem (H.mul_mem (H.inv_mem haH) hgH) haH
    have hnorm := hA (mem_barSub.mpr ⟨⟨a, haH⟩, ha, rfl⟩)
    have hnorm_inv : (φ ⟨a, haH⟩)⁻¹ ∈ Subgroup.normalizer (Xb : Set Q) :=
      (Subgroup.normalizer (Xb : Set Q)).inv_mem hnorm
    have hiff := (Subgroup.mem_normalizer_iff.mp hnorm_inv) (φ ⟨a * g * a⁻¹, hgH⟩)
    have hmem : (φ ⟨a, haH⟩)⁻¹ * φ ⟨a * g * a⁻¹, hgH⟩ * ((φ ⟨a, haH⟩)⁻¹)⁻¹ ∈ Xb :=
      hiff.mp hgX
    rw [inv_inv] at hmem
    refine mem_barPre.mpr ⟨hgH', ?_⟩
    have hEq : (⟨g, hgH'⟩ : ↥H) = ⟨a, haH⟩⁻¹ * ⟨a * g * a⁻¹, hgH⟩ * ⟨a, haH⟩ := by
      apply Subtype.ext
      show g = a⁻¹ * (a * g * a⁻¹) * a
      group
    rw [hEq, map_mul, map_mul, map_inv]
    exact hmem

theorem barSub_le_normalizer_barSub {H : Subgroup G} {Q : Type} [Group Q] (φ : ↥H →* Q)
    {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    barSub H φ A ≤ Subgroup.normalizer ((barSub H φ B : Subgroup Q) : Set Q) := by
  intro x hx
  obtain ⟨a, haA, rfl⟩ := mem_barSub.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨b, hbB, rfl⟩ := mem_barSub.mp hy
    refine mem_barSub.mpr ⟨a * b * a⁻¹, ?_, ?_⟩
    · have hnorm := hAB haA
      rw [Subgroup.mem_normalizer_iff] at hnorm
      exact (hnorm (b : G)).mp hbB
    · rw [map_mul, map_mul, map_inv]
  · intro hy
    obtain ⟨b, hbB, hbφ⟩ := mem_barSub.mp hy
    refine mem_barSub.mpr ⟨a⁻¹ * b * a, ?_, ?_⟩
    · have hnorm_inv : ((a : G))⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
        (Subgroup.normalizer (B : Set G)).inv_mem (hAB haA)
      rw [Subgroup.mem_normalizer_iff] at hnorm_inv
      have hmemB := (hnorm_inv (b : G)).mp hbB
      rw [inv_inv] at hmemB
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmemB
    · rw [map_mul, map_mul, map_inv, hbφ]
      group

theorem forall_commutator_mem_of_commutator_eq_bot {H J : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) {N : Subgroup G} (hNH : N ≤ H) {v : G} (hv : v ∈ H)
    (hN : ⁅barSub H φ N, Subgroup.zpowers (φ ⟨v, hv⟩)⁆ = ⊥) : ∀ n ∈ N, ⁅v, n⁆ ∈ J := by
  intro n hn
  have hnH : n ∈ H := hNH hn
  set k : ↥H := ⁅(⟨n, hnH⟩ : ↥H), (⟨v, hv⟩ : ↥H)⁆ with hk
  have hmemk : φ k ∈ ⁅barSub H φ N, Subgroup.zpowers (φ ⟨v, hv⟩)⁆ := by
    have hkφ : φ k = ⁅φ ⟨n, hnH⟩, φ ⟨v, hv⟩⁆ := by rw [hk, map_commutatorElement]
    rw [hkφ]
    exact Subgroup.commutator_mem_commutator
      (mem_barSub.mpr ⟨⟨n, hnH⟩, hn, rfl⟩) (Subgroup.mem_zpowers _)
  rw [hN, Subgroup.mem_bot] at hmemk
  have hJ : (k : G) ∈ J := (hφ.ker_iff k).mp hmemk
  have hcoe : (k : G) = ⁅n, v⁆ := by
    rw [hk]
    exact map_commutatorElement H.subtype ⟨n, hnH⟩ ⟨v, hv⟩
  rw [hcoe] at hJ
  rw [← commutatorElement_inv]
  exact J.inv_mem hJ

theorem Hyp78.odd_card_barSub {V H E J L N : Subgroup G} (h : Hyp78 V H E J L) {Q : Type}
    [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H J φ) (hNK : N ≤ kSub V H E)
    (hJN : kSub V H E ⊓ J ≤ N) (hNodd : Odd ((kSub V H E ⊓ J).relIndex N)) :
    Odd (Nat.card (barSub H φ N)) := by
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hcard : Nat.card (barSub H φ N) = J.relIndex N :=
    card_barSub_eq_relIndex_of_isBarMap (K := H) (N := J) (A := N)
      (hNK.trans hKH) hJH hφ
  have h5 : J.relIndex N = (kSub V H E ⊓ J).relIndex N := by
    have hEq : J ⊓ N = (kSub V H E ⊓ J) ⊓ N := by
      rw [inf_assoc]
      exact (inf_eq_right.mpr (inf_le_right.trans hNK)).symm
    rw [← Subgroup.inf_relIndex_right J N,
      ← Subgroup.inf_relIndex_right (kSub V H E ⊓ J) N, hEq]
  rw [hcard, h5]
  exact hNodd

private theorem seven_eight_core_bar_relIndex_conjSubgroup (A B : Subgroup G) (k : G) :
    (conjSubgroup A k).relIndex (conjSubgroup B k) = A.relIndex B := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.relIndex_map_map_of_injective A B (MulAut.conj k⁻¹).injective

private theorem seven_eight_core_bar_relIndex_sup_right {H J K : Subgroup G}
    (hKH : K ≤ H) (hJH : J ≤ H) [hJn : (J.subgroupOf H).Normal] :
    J.relIndex (K ⊔ J) = J.relIndex K := by
  have hsup : K ⊔ J ≤ H := sup_le hKH hJH
  have h1 := Subgroup.relIndex_sup_right (K.subgroupOf H) (J.subgroupOf H)
  have h2 := Subgroup.relIndex_subgroupOf (H := J) (K := K ⊔ J) (L := H) hsup
  have h3 := Subgroup.relIndex_subgroupOf (H := J) (K := K) (L := H) hKH
  rw [← h2, Subgroup.subgroupOf_sup hKH hJH, h1, h3]

private theorem seven_eight_core_bar_deltaSet_iff {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    {Q : Type} [Group Q] {φ : ↥H →* Q} {v : G} (hvH : v ∈ H) {a : Q} :
    a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hvH⟩) ↔
      ∃ x ∈ pCoreOf 2 L, ∃ hx : x ∈ H,
        a = φ ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hx hvH) (H.inv_mem hx)⟩ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨xk, hxkc, hxkφ⟩ := mem_barSub.mp hx
    refine ⟨(xk : G), hxkc, xk.2, ?_⟩
    rw [← hxkφ]
    rw [show (⟨(xk : G) * v * (xk : G)⁻¹,
        H.mul_mem (H.mul_mem xk.2 hvH) (H.inv_mem xk.2)⟩ : ↥H) =
        xk * ⟨v, hvH⟩ * xk⁻¹ from Subtype.ext rfl,
      map_mul, map_mul, map_inv]
  · rintro ⟨x, hxcore, hxH, rfl⟩
    refine ⟨φ ⟨x, hxH⟩, mem_barSub.mpr ⟨⟨x, hxH⟩, hxcore, rfl⟩, ?_⟩
    rw [show (⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hvH) (H.inv_mem hxH)⟩ : ↥H) =
        ⟨x, hxH⟩ * ⟨v, hvH⟩ * ⟨x, hxH⟩⁻¹ from Subtype.ext rfl,
      map_mul, map_mul, map_inv]

theorem Hyp78.sevenEightFrame {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] [Finite Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H J φ) {v : G} (hv : v ∈ V) (hvJ : v ∉ J) :
    SevenEightFrame (barSub H φ L) (barSub H φ (pCoreOf 2 L))
      (barSet H φ {u | ∃ U ∈ omegaWithin V H E L, u ∈ U ∧ u ∉ J})
      (φ ⟨v, h.omega_le V h.mem hv⟩) := by
  have hVH : v ∈ H := h.omega_le V h.mem hv
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLH : L ≤ H := h.le_kSub.trans hKH
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.jnormal
  haveI hJn : (J.subgroupOf H).Normal := h.jnormal
  have hgen : (⨆ U ∈ omegaWithin V H E L, U) = L := h.generated
  set S : Set G := {u | ∃ U ∈ omegaWithin V H E L, u ∈ U ∧ u ∉ J} with hSdef
  have hSH : S ⊆ H := by
    rintro u ⟨U, hU, huU, -⟩
    exact h.omega_le U hU.1 huU
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
  ·
    exact barSub_le_normalizer_barSub φ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  ·
    intro d hd
    obtain ⟨k, hkS, rfl⟩ := mem_barSet.mp hd
    obtain ⟨U, hU, hkU, -⟩ := hkS
    have hUe : IsElemAbelian 2 U := isElemAbelian_of_mem_omegaSet h.elemAbelian hU.1
    have h2 : (k : G) * (k : G) = 1 := elemAbelian_mul_self hUe hkU
    rw [← map_mul, show k * k = 1 from Subtype.ext h2, map_one]
  ·
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      intro d hd
      obtain ⟨k, hkS, rfl⟩ := mem_barSet.mp hd
      obtain ⟨U, hU, hkU, -⟩ := hkS
      exact mem_barSub.mpr ⟨k, hU.2 hkU, rfl⟩
    · have hLclosure : L ≤ Subgroup.closure S := by
        rw [← hgen]
        refine iSup_le fun U => iSup_le fun hU => ?_
        intro u hu
        by_cases huJ : u ∈ J
        · have hUrel : J.relIndex U = 2 := by
            obtain ⟨k, hkK, rfl⟩ := h.transitive U hU.1
            have hkH : k ∈ H := hKH hkK
            have hJk : conjSubgroup J k = J :=
              conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormH hkH)
            have hstep : (conjSubgroup J k).relIndex (conjSubgroup V k) = J.relIndex V :=
              seven_eight_core_bar_relIndex_conjSubgroup J V k
            rw [hJk, hV2] at hstep
            exact hstep
          have hUnotJ : ¬ U ≤ J := by
            intro hUJ
            have h1 : J.relIndex U = 1 := Subgroup.relIndex_eq_one.mpr hUJ
            rw [hUrel] at h1
            norm_num at h1
          obtain ⟨u₀, hu₀U, hu₀J⟩ := Set.not_subset.mp hUnotJ
          have h1J : u * u₀ ∉ J := by
            intro hmem
            exact hu₀J (by
              rw [show u₀ = u⁻¹ * (u * u₀) by group]
              exact J.mul_mem (J.inv_mem huJ) hmem)
          have hm1 : u * u₀ ∈ Subgroup.closure S :=
            Subgroup.subset_closure ⟨U, hU, U.mul_mem hu hu₀U, h1J⟩
          have hm2 : u₀ ∈ Subgroup.closure S :=
            Subgroup.subset_closure ⟨U, hU, hu₀U, hu₀J⟩
          rw [show u = (u * u₀) * u₀⁻¹ by group]
          exact (Subgroup.closure S).mul_mem hm1 ((Subgroup.closure S).inv_mem hm2)
        · exact Subgroup.subset_closure ⟨U, hU, hu, huJ⟩
      have hTmap : (Subgroup.closure (H.subtype ⁻¹' S)).map H.subtype =
          Subgroup.closure S := by
        rw [MonoidHom.map_closure]
        congr 1
        ext x
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact hk
        · intro hx
          exact ⟨⟨x, hSH hx⟩, hx, rfl⟩
      have hLle : L.subgroupOf H ≤ Subgroup.closure (H.subtype ⁻¹' S) := by
        intro l hl
        have hlS : (l : G) ∈ Subgroup.closure S := hLclosure hl
        rw [← hTmap] at hlS
        obtain ⟨k, hk, hkG⟩ := Subgroup.mem_map.mp hlS
        have hkl : k = l := Subtype.ext hkG
        rwa [← hkl]
      calc barSub H φ L = (L.subgroupOf H).map φ := rfl
        _ ≤ (Subgroup.closure (H.subtype ⁻¹' S)).map φ := Subgroup.map_mono hLle
        _ = Subgroup.closure (φ '' (H.subtype ⁻¹' S)) := MonoidHom.map_closure φ _
        _ = Subgroup.closure (barSet H φ S) := rfl
  ·
    exact mem_barSet.mpr ⟨⟨v, hVH⟩, ⟨V, ⟨h.mem, h.left_le⟩, hv, hvJ⟩, rfl⟩
  ·
    intro a ha a' ha'
    rw [seven_eight_core_bar_deltaSet_iff h hVH] at ha ha'
    obtain ⟨x, hxcore, hxH, rfl⟩ := ha
    obtain ⟨y, hycore, hyH, rfl⟩ := ha'
    have hxinv : x⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem hxcore
    have hyinv : y⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem hycore
    have hxmem : x * v * x⁻¹ ∈ conjSubgroup V x⁻¹ := by
      rw [mem_conjSubgroup_iff]
      rwa [show x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v by group]
    have hymem : y * v * y⁻¹ ∈ conjSubgroup V y⁻¹ := by
      rw [mem_conjSubgroup_iff]
      rwa [show y⁻¹ * (y * v * y⁻¹) * (y⁻¹)⁻¹ = v by group]
    have hbot : ⁅conjSubgroup V x⁻¹, conjSubgroup V y⁻¹⁆ = ⊥ :=
      seven_eight_commutator_conj_eq_bot h hxinv hyinv
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hcomm : (x * v * x⁻¹) * (y * v * y⁻¹) = (y * v * y⁻¹) * (x * v * x⁻¹) :=
      ((Subgroup.mem_centralizer_iff.mp (hle hxmem)) (y * v * y⁻¹) hymem).symm
    have hAB : (⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ : ↥H) *
        ⟨y * v * y⁻¹, H.mul_mem (H.mul_mem hyH hVH) (H.inv_mem hyH)⟩ =
        ⟨y * v * y⁻¹, H.mul_mem (H.mul_mem hyH hVH) (H.inv_mem hyH)⟩ *
        ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ :=
      Subtype.ext hcomm
    calc φ ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ *
          φ ⟨y * v * y⁻¹, H.mul_mem (H.mul_mem hyH hVH) (H.inv_mem hyH)⟩
        = φ (⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ *
            ⟨y * v * y⁻¹, H.mul_mem (H.mul_mem hyH hVH) (H.inv_mem hyH)⟩) :=
          (map_mul φ _ _).symm
      _ = φ (⟨y * v * y⁻¹, H.mul_mem (H.mul_mem hyH hVH) (H.inv_mem hyH)⟩ *
            ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩) := by rw [hAB]
      _ = φ ⟨y * v * y⁻¹, H.mul_mem (H.mul_mem hyH hVH) (H.inv_mem hyH)⟩ *
          φ ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ :=
          map_mul φ _ _
  ·
    have hsubset : {W : Subgroup G | ∃ g ∈ pCoreOf 2 L, W = conjSubgroup V g ⊔ J} ⊆
        (fun a => barPre H φ (Subgroup.zpowers a)) ''
          deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hVH⟩) := by
      rintro W ⟨g, hgcore, rfl⟩
      have hgL : g ∈ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hgcore
      have hgH : g ∈ H := hLH hgL
      have hcgmem : conjSubgroup V g ∈ omegaSet V H E :=
        conjSubgroup_mem_omegaSet h.le h.normal h.mem hgH
      have hcgH : conjSubgroup V g ≤ H := h.omega_le _ hcgmem
      have hsup_le : conjSubgroup V g ⊔ J ≤ H := sup_le hcgH hJH
      let hgvH : g⁻¹ * v * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hgH) hVH) hgH
      let a : Q := φ ⟨g⁻¹ * v * g, hgvH⟩
      have hgvmem : g⁻¹ * v * g ∈ conjSubgroup V g := by
        rw [mem_conjSubgroup_iff]
        rwa [show g * (g⁻¹ * v * g) * g⁻¹ = v by group]
      have hVg_e : IsElemAbelian 2 (conjSubgroup V g) :=
        isElemAbelian_of_mem_omegaSet h.elemAbelian hcgmem
      have hgv2 : (g⁻¹ * v * g) * (g⁻¹ * v * g) = 1 := elemAbelian_mul_self hVg_e hgvmem
      have hgvJ : g⁻¹ * v * g ∉ J := by
        intro hmem
        apply hvJ
        have hJg : conjSubgroup J g = J :=
          conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormH hgH)
        have hconj : g⁻¹ * v * g ∈ conjSubgroup J g := by rw [hJg]; exact hmem
        have h2 : g * (g⁻¹ * v * g) * g⁻¹ ∈ J := mem_conjSubgroup_iff.mp hconj
        rwa [show g * (g⁻¹ * v * g) * g⁻¹ = v by group] at h2
      have haΔ : a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hVH⟩) := by
        refine ⟨(φ ⟨g, hgH⟩)⁻¹, (barSub H φ (pCoreOf 2 L)).inv_mem ?_, ?_⟩
        · exact mem_barSub.mpr ⟨⟨g, hgH⟩, hgcore, rfl⟩
        · show φ ⟨g⁻¹ * v * g, hgvH⟩ =
              (φ ⟨g, hgH⟩)⁻¹ * φ ⟨v, hVH⟩ * ((φ ⟨g, hgH⟩)⁻¹)⁻¹
          rw [show (⟨g⁻¹ * v * g, hgvH⟩ : ↥H) =
              ⟨g, hgH⟩⁻¹ * ⟨v, hVH⟩ * ⟨g, hgH⟩ from Subtype.ext rfl,
            map_mul, map_mul, map_inv, inv_inv]
      refine ⟨a, haΔ, ?_⟩
      haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
      have hVe : IsElemAbelian 2 V := isElemAbelian_of_mem_omegaSet h.elemAbelian h.mem
      have hVleH : V ≤ H := h.omega_le V h.mem
      have hbarV : barSub H φ V = Subgroup.zpowers (φ ⟨v, hVH⟩) := by
        have hcardV : Nat.card (barSub H φ V) = 2 := by
          rw [card_barSub_eq_relIndex_of_isBarMap (K := H) (N := J) (A := V)
            hVleH hJH hφ, hV2]
        have hvb_mem : φ ⟨v, hVH⟩ ∈ barSub H φ V :=
          mem_barSub.mpr ⟨⟨v, hVH⟩, hv, rfl⟩
        have hle : Subgroup.zpowers (φ ⟨v, hVH⟩) ≤ barSub H φ V :=
          Subgroup.zpowers_le.mpr hvb_mem
        have hvv : v * v = 1 := elemAbelian_mul_self hVe hv
        have hvb2 : (φ ⟨v, hVH⟩) ^ 2 = 1 := by
          rw [pow_two, ← map_mul,
            show (⟨v, hVH⟩ : ↥H) * ⟨v, hVH⟩ = 1 from Subtype.ext hvv, map_one]
        have hvbne : φ ⟨v, hVH⟩ ≠ 1 := by
          intro h1
          exact hvJ ((hφ.ker_iff ⟨v, hVH⟩).mp h1)
        have hcardz : Nat.card (Subgroup.zpowers (φ ⟨v, hVH⟩)) = 2 := by
          rw [Nat.card_zpowers, orderOf_eq_prime hvb2 hvbne]
        exact (Subgroup.eq_of_le_of_card_ge hle (by simp [hcardz, hcardV])).symm
      have hbarCg : barSub H φ (conjSubgroup V g) = Subgroup.zpowers a := by
        rw [show barSub H φ (conjSubgroup V g) =
            conjSubgroup (barSub H φ V) (φ ⟨g, hgH⟩) from
          barSub_conjSubgroup φ V ⟨g, hgH⟩, hbarV]
        show conjSubgroup (Subgroup.zpowers (φ ⟨v, hVH⟩)) (φ ⟨g, hgH⟩) = Subgroup.zpowers a
        rw [CFSG.Quasithin.conjSubgroup, MonoidHom.map_zpowers]
        congr 1
        change MulAut.conj (φ ⟨g, hgH⟩)⁻¹ (φ ⟨v, hVH⟩) = a
        rw [MulAut.conj_apply]
        show (φ ⟨g, hgH⟩)⁻¹ * φ ⟨v, hVH⟩ * ((φ ⟨g, hgH⟩)⁻¹)⁻¹ =
          φ ⟨g⁻¹ * v * g, hgvH⟩
        rw [show (⟨g⁻¹ * v * g, hgvH⟩ : ↥H) =
            ⟨g, hgH⟩⁻¹ * ⟨v, hVH⟩ * ⟨g, hgH⟩ from Subtype.ext rfl,
          map_mul, map_mul, map_inv, inv_inv]
      have hbarJ : barSub H φ J = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨k, hkJ, rfl⟩ := mem_barSub.mp hy
        rw [Subgroup.mem_bot, (hφ.ker_iff k).mpr hkJ]
      have hbarW : barSub H φ (conjSubgroup V g ⊔ J) = Subgroup.zpowers a := by
        rw [barSub_sup hcgH hJH, hbarCg, hbarJ, sup_bot_eq]
      have hXY : conjSubgroup V g ⊔ J ≤ barPre H φ (Subgroup.zpowers a) := by
        intro w hw
        have hwH : w ∈ H := hsup_le hw
        have hwbar : φ ⟨w, hwH⟩ ∈ barSub H φ (conjSubgroup V g ⊔ J) :=
          mem_barSub.mpr ⟨⟨w, hwH⟩, hw, rfl⟩
        rw [hbarW] at hwbar
        exact mem_barPre.mpr ⟨hwH, hwbar⟩
      have ha2 : a ^ 2 = 1 := by
        show (φ ⟨g⁻¹ * v * g, hgvH⟩) ^ 2 = 1
        rw [pow_two, ← map_mul,
          show (⟨g⁻¹ * v * g, hgvH⟩ : ↥H) * ⟨g⁻¹ * v * g, hgvH⟩ = 1
            from Subtype.ext hgv2, map_one]
      have hane : a ≠ 1 := by
        intro h1
        exact hgvJ ((hφ.ker_iff ⟨g⁻¹ * v * g, hgvH⟩).mp h1)
      have hYrel : J.relIndex (barPre H φ (Subgroup.zpowers a)) = 2 := by
        rw [relIndex_barPre hJH hφ (Subgroup.zpowers a), Nat.card_zpowers,
          orderOf_eq_prime ha2 hane]
      have hXrel : J.relIndex (conjSubgroup V g ⊔ J) = 2 := by
        rw [seven_eight_core_bar_relIndex_sup_right hcgH hJH,
          seven_eight_relIndex_conjSubgroup_eq_two h hV2 hgcore]
      have hJX : J ≤ conjSubgroup V g ⊔ J := le_sup_right
      have hmul := Subgroup.relIndex_mul_relIndex (H := J)
        (K := conjSubgroup V g ⊔ J) (L := barPre H φ (Subgroup.zpowers a)) hJX hXY
      have hone : (conjSubgroup V g ⊔ J).relIndex (barPre H φ (Subgroup.zpowers a)) = 1 := by
        rw [hXrel, hYrel] at hmul
        omega
      exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hXY
    have h1 : ({W : Subgroup G | ∃ g ∈ pCoreOf 2 L, W = conjSubgroup V g ⊔ J} : Set _).ncard ≤
        ((fun a => barPre H φ (Subgroup.zpowers a)) ''
          deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hVH⟩)).ncard :=
      Set.ncard_le_ncard hsubset
    have h2 : ((fun a => barPre H φ (Subgroup.zpowers a)) ''
        deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hVH⟩)).ncard ≤
        (deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hVH⟩)).ncard :=
      Set.ncard_image_le
    exact le_trans h.four_le (le_trans h1 h2)
  ·
    intro d hd
    obtain ⟨k, hkS, rfl⟩ := mem_barSet.mp hd
    obtain ⟨U, hU, hkU, hkJ⟩ := hkS
    rcases Hyp78.forall_commute_or_forall_pow_three h hV2 hU with hcom | hpow
    · left
      intro a ha
      rw [seven_eight_core_bar_deltaSet_iff h hVH] at ha
      obtain ⟨x, hxcore, hxH, rfl⟩ := ha
      have hxinv : x⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem hxcore
      have hxmem : x * v * x⁻¹ ∈ conjSubgroup V x⁻¹ := by
        rw [mem_conjSubgroup_iff]
        rwa [show x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v by group]
      have hcomm : (k : G) * (x * v * x⁻¹) = (x * v * x⁻¹) * (k : G) :=
        hcom x⁻¹ hxinv (k : G) hkU (x * v * x⁻¹) hxmem
      calc φ k * φ ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩
          = φ (k * ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩) :=
            (map_mul φ k _).symm
        _ = φ (⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ * k) := by
              rw [show k * ⟨x * v * x⁻¹,
                    H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ =
                  ⟨x * v * x⁻¹,
                    H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ * k
                from Subtype.ext hcomm]
        _ = φ ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ * φ k :=
              map_mul φ _ k
    · right
      intro a ha
      rw [seven_eight_core_bar_deltaSet_iff h hVH] at ha
      obtain ⟨x, hxcore, hxH, rfl⟩ := ha
      have hxinv : x⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem hxcore
      have hxmem : x * v * x⁻¹ ∈ conjSubgroup V x⁻¹ := by
        rw [mem_conjSubgroup_iff]
        rwa [show x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v by group]
      have hxJ : x * v * x⁻¹ ∉ J := by
        intro hxJmem
        apply hvJ
        have hJxinv : conjSubgroup J x⁻¹ = J :=
          conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormH (H.inv_mem hxH))
        have hconj : x * v * x⁻¹ ∈ conjSubgroup J x⁻¹ := by rw [hJxinv]; exact hxJmem
        have h2 := mem_conjSubgroup_iff.mp hconj
        rw [inv_inv] at h2
        rwa [show x⁻¹ * (x * v * x⁻¹) * x = v by group] at h2
      have hwu : ((x * v * x⁻¹) * (k : G)) ^ 3 = 1 :=
        hpow x⁻¹ hxinv (k : G) hkU hkJ (x * v * x⁻¹) hxmem hxJ
      have hEq : (⟨x * v * x⁻¹,
          H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ * k) ^ 3 = 1 :=
        Subtype.ext hwu
      calc (φ ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ * φ k) ^ 3
          = (φ (⟨x * v * x⁻¹,
                H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ * k)) ^ 3 := by
            rw [map_mul]
        _ = φ ((⟨x * v * x⁻¹,
                H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩ * k) ^ 3) :=
            (map_pow φ _ 3).symm
        _ = φ 1 := by rw [hEq]
        _ = 1 := map_one φ
  ·
    obtain ⟨U, hU, u, huU, huJ, hpow⟩ := Hyp78.exists_pow_three_eq_one h hV2
    have huH : u ∈ H := h.omega_le U hU.1 huU
    refine ⟨φ ⟨u, huH⟩, mem_barSet.mpr ⟨⟨u, huH⟩, ⟨U, hU, huU, huJ⟩, rfl⟩, ?_⟩
    intro a ha
    rw [seven_eight_core_bar_deltaSet_iff h hVH] at ha
    obtain ⟨x, hxcore, hxH, rfl⟩ := ha
    have hxinv : x⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem hxcore
    have hxmem : x * v * x⁻¹ ∈ conjSubgroup V x⁻¹ := by
      rw [mem_conjSubgroup_iff]
      rwa [show x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v by group]
    have hxJ : x * v * x⁻¹ ∉ J := by
      intro hxJmem
      apply hvJ
      have hJxinv : conjSubgroup J x⁻¹ = J :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormH (H.inv_mem hxH))
      have hconj : x * v * x⁻¹ ∈ conjSubgroup J x⁻¹ := by rw [hJxinv]; exact hxJmem
      have h2 := mem_conjSubgroup_iff.mp hconj
      rw [inv_inv] at h2
      rwa [show x⁻¹ * (x * v * x⁻¹) * x = v by group] at h2
    have hwu : ((x * v * x⁻¹) * u) ^ 3 = 1 :=
      hpow x⁻¹ hxinv (x * v * x⁻¹) hxmem hxJ
    let w : ↥H := ⟨x * v * x⁻¹, H.mul_mem (H.mul_mem hxH hVH) (H.inv_mem hxH)⟩
    let uH : ↥H := ⟨u, huH⟩
    have hEq : (w * uH) ^ 3 = 1 := Subtype.ext hwu
    calc (φ w * φ uH) ^ 3
        = (φ (w * uH)) ^ 3 := by rw [map_mul]
      _ = φ ((w * uH) ^ 3) := (map_pow φ _ 3).symm
      _ = φ 1 := by rw [hEq]
      _ = 1 := map_one φ

end CFSG.LocalAnalysis.WeakClosure81
