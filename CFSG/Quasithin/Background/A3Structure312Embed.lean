
module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A4Defs
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace A312

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_inf_of_subnormal {T H L : Subgroup G} (h : IsSubnormal L H) :
    IsSylowTwoOf T H → IsSylowTwoOf (T ⊓ L) L := by
  induction h with
  | refl K =>
    intro hT
    rwa [inf_eq_left.mpr hT.1]
  | @step L M K hLM hN _ ih =>
    intro hT
    have h1 := ih hT
    have hnorm : M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN
    have h2 := A4.isSylowTwoOf_inf_normal h1 hLM hnorm
    rwa [inf_assoc, inf_eq_right.mpr hLM] at h2

theorem inf_sup_le_of_sylow {T L N : Subgroup G} (hTL : IsSylowTwoOf (T ⊓ L) L)
    (hT2 : IsPGroup 2 T) (hLN : L ≤ Subgroup.normalizer (N : Set G)) :
    T ⊓ (L ⊔ N) ≤ (T ⊓ L) ⊔ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := L ⊔ N with hY
  have hNY : N ≤ Y := le_sup_right
  have hLY : L ≤ Y := le_sup_left
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) := sup_le hLN Subgroup.le_normalizer
  have hNn : (N.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYN
  let φ : ↥Y →* ↥Y ⧸ N.subgroupOf Y := QuotientGroup.mk' (N.subgroupOf Y)
  let ψ : ↥L →* ↥Y ⧸ N.subgroupOf Y := φ.comp (Subgroup.inclusion hLY)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Y) y
    have hx' : x ∈ (↑(L ⊔ N) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L N hLN] at hx'
    obtain ⟨l, hl, n, hn, rfl⟩ := hx'
    refine ⟨⟨l, hl⟩, ?_⟩
    show φ (Subgroup.inclusion hLY ⟨l, hl⟩) = φ ⟨l * n, hx⟩
    simp only [φ, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hn
  let P : Sylow 2 ↥L := A4.toSylow hTL
  let P' : Sylow 2 (↥Y ⧸ N.subgroupOf Y) := P.mapSurjective hψ
  have hP' : (P' : Subgroup (↥Y ⧸ N.subgroupOf Y)) = ((T ⊓ L).subgroupOf L).map ψ :=
    Sylow.coe_mapSurjective hψ P
  set Q' : Subgroup (↥Y ⧸ N.subgroupOf Y) := ((T ⊓ Y).subgroupOf Y).map φ with hQ'
  have hQ'p : IsPGroup 2 Q' :=
    (A4.isPGroup_subgroupOf_of_le inf_le_right (hT2.to_inf_left)).map φ
  have hPQ : (P' : Subgroup (↥Y ⧸ N.subgroupOf Y)) ≤ Q' := by
    rw [hP']
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ T ⊓ L := hx
    exact ⟨Subgroup.inclusion hLY x, ⟨hx'.1, hLY x.2⟩, rfl⟩
  have hQP : Q' ≤ (P' : Subgroup (↥Y ⧸ N.subgroupOf Y)) := by
    obtain ⟨R, hR⟩ := hQ'p.exists_le_sylow
    have h1 : (P' : Subgroup (↥Y ⧸ N.subgroupOf Y)) = R := by
      refine Subgroup.eq_of_le_of_card_ge (hPQ.trans hR) ?_
      rw [R.card_eq_multiplicity, P'.card_eq_multiplicity]
    exact hR.trans h1.ge
  intro q hq
  have hqY : q ∈ Y := hq.2
  have hφq : φ ⟨q, hqY⟩ ∈ Q' := ⟨⟨q, hqY⟩, hq, rfl⟩
  have h2 := hQP hφq
  rw [hP'] at h2
  obtain ⟨x, hx, hxq⟩ := h2
  have hxq' : (QuotientGroup.mk (Subgroup.inclusion hLY x) : ↥Y ⧸ N.subgroupOf Y) =
      QuotientGroup.mk ⟨q, hqY⟩ := hxq
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxq'
  have hn : (x : G)⁻¹ * q ∈ N := by simpa using hxq'
  have hxTL : (x : G) ∈ T ⊓ L := hx
  have hq' : q = (x : G) * ((x : G)⁻¹ * q) := by group
  rw [hq']
  exact Subgroup.mul_mem_sup hxTL hn

omit [Finite G] in
theorem commutator_le_of_le_normalizer {B L X : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (L : Set G)) (hXL : X ≤ L) : ⁅B, X⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro b hb x hx
  have h1 : b * x * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hB hb) x).mp (hXL hx)
  have : ⁅b, x⁆ = (b * x * b⁻¹) * x⁻¹ := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact L.mul_mem h1 (L.inv_mem (hXL hx))

omit [Finite G] in
theorem commutatorElement_mem {B : Subgroup G} {b t : G} (hb : b ∈ B) (ht : t ∈ B) :
    ⁅b, t⁆ ∈ B := by
  have : ⁅b, t⁆ = (b * t * b⁻¹) * t⁻¹ := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact B.mul_mem (B.mul_mem (B.mul_mem hb ht) (B.inv_mem hb)) (B.inv_mem ht)

theorem commutator_inf_eq_self {T M B : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M)
    (hB : B ∈ cComp M) : ⁅B, T ⊓ B⁆ = B := by
  have hBM : B ≤ M := le_of_mem_cComp hB
  have hTM' : IsSylowTwoOf T M := A4.isSylowTwoOf_mono hT hTM le_top
  have hTB : IsSylowTwoOf (T ⊓ B) B :=
    isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hB) hTM'
  rcases cComp_commutator_dichotomy_of_le hB (inf_le_left.trans hTM : T ⊓ B ≤ M) with
    ⟨hle, -⟩ | heq
  · exfalso
    set R : Subgroup G := solvRad B with hR
    have hBnorm : B ≤ Subgroup.normalizer (solvRad M : Set G) :=
      hBM.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad M))
    have hNnorm : B ≤ Subgroup.normalizer ((B ⊓ solvRad M : Subgroup G) : Set G) :=
      fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hb, hBnorm hb⟩
    have hNsolv : Group.IsSolvable ↥(B ⊓ solvRad M) := by
      have := solvRad_isSolvable M
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_right : B ⊓ solvRad M ≤ solvRad M))
        (Subgroup.inclusion_injective _)
    have hNR : B ⊓ solvRad M ≤ R :=
      le_solvRad inf_le_left ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hNnorm)
        hNsolv
    have hcommR : ∀ b ∈ B, ∀ t ∈ T ⊓ B, ⁅b, t⁆ ∈ R := fun b hb t ht =>
      hNR ⟨commutatorElement_mem hb ht.2, hle (Subgroup.commutator_mem_commutator hb ht)⟩
    obtain ⟨-, ⟨hsimple, hnonab⟩, -⟩ := cComp_structure hB
    have hTR : T ⊓ B ≤ R := by
      intro t ht
      have hcenter : (QuotientGroup.mk' (R.subgroupOf B) ⟨t, ht.2⟩ : ↥B ⧸ R.subgroupOf B) ∈
          Subgroup.center (↥B ⧸ R.subgroupOf B) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf B) y
        have hcomm : ⁅(⟨b, hb⟩ : ↥B), (⟨t, ht.2⟩ : ↥B)⁆ ∈ R.subgroupOf B := by
          rw [Subgroup.mem_subgroupOf]
          exact hcommR b hb t ht
        have h1 := (QuotientGroup.eq_one_iff _).mpr hcomm
        have h2 : QuotientGroup.mk' (R.subgroupOf B) ⁅(⟨b, hb⟩ : ↥B), (⟨t, ht.2⟩ : ↥B)⁆ = 1 := h1
        rw [map_commutatorElement] at h2
        exact commutatorElement_eq_one_iff_mul_comm.mp h2
      have hcbot : Subgroup.center (↥B ⧸ R.subgroupOf B) = ⊥ := by
        rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (↥B ⧸ R.subgroupOf B)) with
          h | h
        · exact h
        · exfalso
          obtain ⟨a, b, hab⟩ := hnonab
          have ha : a ∈ Subgroup.center (↥B ⧸ R.subgroupOf B) := by rw [h]; trivial
          exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
      rw [hcbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at hcenter
      exact hcenter
    have hodd : Odd (Nat.card (↥B ⧸ R.subgroupOf B)) := by
      have h1 : (R.subgroupOf B).index ∣ ((T ⊓ B).subgroupOf B).index :=
        Subgroup.index_dvd_of_le (fun x hx => hTR hx)
      have h2 : ¬ 2 ∣ (R.subgroupOf B).index := fun h => hTB.2.2 (h.trans h1)
      rw [Nat.odd_iff]
      have : (R.subgroupOf B).index = Nat.card (↥B ⧸ R.subgroupOf B) := rfl
      omega
    have hs1 : Group.IsSolvable (↥B ⧸ R.subgroupOf B) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hRs : Group.IsSolvable ↥R := solvRad_isSolvable B
    have hs2 : Group.IsSolvable ↥(R.subgroupOf B) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le B)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (solvRad_le B)).injective
    exact not_isSolvable_of_mem_cComp hB (Group.isSolvable_of_subgroup_quotient (R.subgroupOf B))
  · rw [heq]
    exact le_antisymm
      (conjClosure_le fun h hh z hz => B.mul_mem (B.mul_mem hh.2 hz) (B.inv_mem hh.2))
      (le_conjClosure B (T ⊓ B))

theorem eq_bot_of_le_sSup {T B : Subgroup G} (hT : IsSylowTwoOf T ⊤) (h37 : A37Statement G)
    (hBT : ⁅B, T ⊓ B⁆ = B) (hperf : ⁅B, B⁆ = B)
    (hnorm : ∀ L ∈ cComp (⊤ : Subgroup G), B ≤ Subgroup.normalizer (L : Set G))
    (hsolv : ∀ L ∈ cComp (⊤ : Subgroup G), Group.IsSolvable ↥⁅B, T ⊓ L⁆)
    (S : Set (Subgroup G)) (hS : S ⊆ cComp (⊤ : Subgroup G)) (hBS : B ≤ sSup S) : B = ⊥ := by
  have hfin : S.Finite := Set.toFinite S
  revert hS hBS
  refine Set.Finite.induction_on (motive := fun S _ => S ⊆ cComp (⊤ : Subgroup G) →
    B ≤ sSup S → B = ⊥) S hfin ?_ ?_
  · intro _ hBS
    rw [sSup_empty] at hBS
    exact le_bot_iff.mp hBS
  · intro L S' hLS' _ ih hsub hBS
    have hL : L ∈ cComp (⊤ : Subgroup G) := hsub (Set.mem_insert _ _)
    have hS'sub : S' ⊆ cComp (⊤ : Subgroup G) := fun K hK => hsub (Set.mem_insert_of_mem _ hK)
    rw [sSup_insert] at hBS
    set N : Subgroup G := sSup S' with hN
    have hLN : L ≤ Subgroup.normalizer (N : Set G) := by
      have h1 : N ≤ Subgroup.centralizer (L : Set G) := by
        refine sSup_le fun K hK => ?_
        have hKL : L ≠ K := fun h => hLS' (h ▸ hK)
        have := h37 L hL K (hS'sub hK) hKL
        exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp this)
      exact (Subgroup.le_centralizer_iff.mpr h1).trans (Subgroup.centralizer_le_normalizer _)
    have hTL : IsSylowTwoOf (T ⊓ L) L :=
      isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hL) hT
    have hT2 : IsPGroup 2 T := hT.2.1
    have hTY := inf_sup_le_of_sylow hTL hT2 hLN
    have hYN : L ⊔ N ≤ Subgroup.normalizer (N : Set G) := sup_le hLN Subgroup.le_normalizer
    have hTLN : T ⊓ L ≤ Subgroup.normalizer (N : Set G) := inf_le_right.trans hLN
    set D : Subgroup G := ⁅B, T ⊓ L⁆ ⊔ N with hD
    have hBD : B ≤ D := by
      refine hBT.symm.le.trans ?_
      rw [Subgroup.commutator_le]
      intro b hb t ht
      have htY : t ∈ T ⊓ (L ⊔ N) := ⟨ht.1, hBS ht.2⟩
      have hts := hTY htY
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTLN] at hts
      obtain ⟨s, hs, n, hn, rfl⟩ := hts
      have hbY : b ∈ L ⊔ N := hBS hb
      have h1 : ⁅b, s * n⁆ = ⁅b, s⁆ * (s * ⁅b, n⁆ * s⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h1]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hb hs))
        (Subgroup.mem_sup_right ?_)
      have hbn : b * n * b⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hYN hbY) n).mp hn
      have hbn' : ⁅b, n⁆ ∈ N := by
        have : ⁅b, n⁆ = (b * n * b⁻¹) * n⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact N.mul_mem hbn (N.inv_mem hn)
      have hsN : s ∈ Subgroup.normalizer (N : Set G) := hTLN hs
      exact (Subgroup.mem_normalizer_iff.mp hsN _).mp hbn'
    have hDnorm : D ≤ Subgroup.normalizer (N : Set G) := by
      refine sup_le ?_ Subgroup.le_normalizer
      exact (commutator_le_of_le_normalizer (hnorm L hL) inf_le_right).trans hLN
    have hsolvD : Group.IsSolvable ↥⁅B, T ⊓ L⁆ := hsolv L hL
    have hcore : perfectCore D ≤ N :=
      perfectCore_le_of_sup_solvable le_sup_right
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hDnorm) (by
          rw [hD, sup_comm]) hsolvD
    exact ih hS'sub ((le_perfectCore_of_perfect hBD hperf).trans hcore)

theorem exists_le_cComp {T B : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T)
    (h37 : A37Statement G) (h39 : A39Statement G) :
    ∃ L ∈ cComp (⊤ : Subgroup G), B ≤ L := by
  have hB' : B ∈ cComp (B ⊔ T) := hB
  have hperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB'
  have hBT : ⁅B, T ⊓ B⁆ = B := commutator_inf_eq_self hT le_sup_right hB'
  have hBspan : B ≤ cCompSpan (⊤ : Subgroup G) := by
    rw [h39.1]
    exact le_perfectCore_of_perfect le_top hperf
  have hnorm : ∀ L ∈ cComp (⊤ : Subgroup G), B ≤ Subgroup.normalizer (L : Set G) := fun L hL =>
    hBspan.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (cComp_normal_span hL).1).mp
      (cComp_normal_span hL).2)
  by_contra hcon
  push Not at hcon
  have hsolv : ∀ L ∈ cComp (⊤ : Subgroup G), Group.IsSolvable ↥⁅B, T ⊓ L⁆ := by
    intro L hL
    rcases cComp_commutator_dichotomy_of_le hB'
      (inf_le_left.trans le_sup_right : T ⊓ L ≤ B ⊔ T) with ⟨-, hs⟩ | heq
    · exact hs
    · exfalso
      apply hcon L hL
      calc B ≤ conjClosure B (T ⊓ L) := le_conjClosure _ _
        _ = ⁅B, T ⊓ L⁆ := heq.symm
        _ ≤ L := commutator_le_of_le_normalizer (hnorm L hL) inf_le_right
  exact ne_bot_of_mem_cComp hB' (eq_bot_of_le_sSup hT h37 hBT hperf hnorm hsolv (cComp ⊤)
    subset_rfl hBspan)

omit [Finite G] in
theorem eq_of_le_of_le {B L L' : Subgroup G} (h37 : A37Statement G) (hB : B ≠ ⊥)
    (hperf : ⁅B, B⁆ = B) (hL : L ∈ cComp (⊤ : Subgroup G)) (hL' : L' ∈ cComp (⊤ : Subgroup G))
    (hBL : B ≤ L) (hBL' : B ≤ L') : L' = L := by
  by_contra hne
  have h1 := h37 L hL L' hL' (Ne.symm hne)
  apply hB
  refine le_bot_iff.mp ?_
  calc B = ⁅B, B⁆ := hperf.symm
    _ ≤ ⁅L, L'⁆ := Subgroup.commutator_mono hBL hBL'
    _ = ⊥ := h1

end A312

end CFSG.Quasithin
