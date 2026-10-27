module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def cComp (X : Subgroup G) : Set (Subgroup G) :=
  {L | quasithinIsCComponent L X}

@[expose] def cCompInter (X H : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ cComp X ∧ L ≤ H}

theorem mem_cComp_iff {L X : Subgroup G} : L ∈ cComp X ↔ quasithinIsCComponent L X := Iff.rfl

theorem mem_cCompInter_iff {L X H : Subgroup G} : L ∈ cCompInter X H ↔ L ∈ cComp X ∧ L ≤ H :=
  Iff.rfl

theorem ne_bot_of_mem_cComp {L X : Subgroup G} (hL : L ∈ cComp X) : L ≠ ⊥ := hL.1

theorem perfect_of_mem_cComp {L X : Subgroup G} (hL : L ∈ cComp X) : ⁅L, L⁆ = L := hL.2.1

theorem subnormal_of_mem_cComp {L X : Subgroup G} (hL : L ∈ cComp X) : IsSubnormal L X :=
  hL.2.2.1

theorem le_of_mem_cComp {L X : Subgroup G} (hL : L ∈ cComp X) : L ≤ X :=
  A3.subnormal_le hL.2.2.1

theorem not_subnormal_of_mem_cComp {L X K : Subgroup G} (hL : L ∈ cComp X) (hKL : K < L)
    (hK : K ≠ ⊥) (hKp : ⁅K, K⁆ = K) : ¬ IsSubnormal K X :=
  hL.2.2.2 K hKL hK hKp

theorem mem_cComp_iff_minimal [Finite G] {L X : Subgroup G} :
    L ∈ cComp X ↔
      Minimal (fun K : Subgroup G => K ≠ ⊥ ∧ perfectCore K = K ∧ IsSubnormal K X) L := by
  constructor
  · intro hL
    refine ⟨⟨hL.1, (perfectCore_eq_self_iff L).mpr hL.2.1, hL.2.2.1⟩, ?_⟩
    rintro K ⟨hKne, hKperf, hKsub⟩ hKL
    by_contra hLK
    exact hL.2.2.2 K (lt_of_le_not_ge hKL hLK) hKne ((perfectCore_eq_self_iff K).mp hKperf) hKsub
  · intro h
    obtain ⟨⟨hne, hperf, hsub⟩, hmin⟩ := h
    refine ⟨hne, (perfectCore_eq_self_iff L).mp hperf, hsub, fun K hKL hKne hKperf hKsub => ?_⟩
    exact hKL.not_ge (hmin ⟨hKne, (perfectCore_eq_self_iff K).mpr hKperf, hKsub⟩ hKL.le)

theorem perfectCore_eq_bot_of_subnormal_lt [Finite G] {L X N : Subgroup G} (hL : L ∈ cComp X)
    (hN : IsSubnormal N L) (hlt : N < L) : perfectCore N = ⊥ := by
  by_contra hne
  exact not_subnormal_of_mem_cComp hL ((perfectCore_le N).trans_lt hlt) hne
    (perfectCore_perfect N) (A3.subnormal_trans (A3.subnormal_perfectCore hN)
      (subnormal_of_mem_cComp hL))

theorem le_solvRad_of_subnormal_lt [Finite G] {L X M : Subgroup G} (hL : L ∈ cComp X)
    (hM : IsSubnormal M L) (hlt : M < L) : M ≤ solvRad L :=
  le_solvRad_of_subnormal hM
    ((isSolvable_iff_perfectCore_eq_bot M).mpr (perfectCore_eq_bot_of_subnormal_lt hL hM hlt))

theorem not_isSolvable_of_mem_cComp [Finite G] {L X : Subgroup G} (hL : L ∈ cComp X) :
    ¬ Group.IsSolvable L := by
  intro hs
  have h1 := (isSolvable_iff_perfectCore_eq_bot L).mp hs
  rw [perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hL)] at h1
  exact ne_bot_of_mem_cComp hL h1

theorem cComp_self_eq_singleton [Finite G] {L X : Subgroup G} (hL : L ∈ cComp X) :
    cComp L = {L} := by
  have hLL : L ∈ cComp L := by
    refine ⟨ne_bot_of_mem_cComp hL, perfect_of_mem_cComp hL, IsSubnormal.refl L,
      fun K hKL hKne hKperf hKsub => ?_⟩
    have := perfectCore_eq_bot_of_subnormal_lt hL hKsub hKL
    rw [perfectCore_eq_self_of_perfect hKperf] at this
    exact hKne this
  ext K
  constructor
  · intro hK
    by_contra hKL
    have hlt : K < L := lt_of_le_of_ne (le_of_mem_cComp hK) hKL
    exact not_subnormal_of_mem_cComp hL hlt (ne_bot_of_mem_cComp hK) (perfect_of_mem_cComp hK)
      (A3.subnormal_trans (subnormal_of_mem_cComp hK) (subnormal_of_mem_cComp hL))
  · intro hK
    rw [Set.mem_singleton_iff] at hK
    rw [hK]
    exact hLL

theorem normal_eq_top_or_map_le_solvRad [Finite G] {L X : Subgroup G} (hL : L ∈ cComp X)
    (P : Subgroup ↥L) [hP : P.Normal] : P = ⊤ ∨ P.map L.subtype ≤ solvRad L := by
  have hP'L : P.map L.subtype ≤ L := fun x ⟨y, _, hy⟩ => hy ▸ y.2
  have hPP' : (P.map L.subtype).subgroupOf L = P :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective P
  have hP'normal : ((P.map L.subtype).subgroupOf L).Normal := by
    rw [hPP']
    exact hP
  have hP'sub : IsSubnormal (P.map L.subtype) L := A3.subnormal_of_normal hP'L hP'normal
  by_cases hP'eq : P.map L.subtype = L
  · left
    rw [← hPP', hP'eq, Subgroup.subgroupOf_self]
  · right
    exact le_solvRad_of_subnormal_lt hL hP'sub (lt_of_le_of_ne hP'L hP'eq)

theorem cComp_structure [Finite G] {L X : Subgroup G} (hL : L ∈ cComp X) :
    (Maximal (fun K : Subgroup G => IsSubnormal K L ∧ K ≠ L) (solvRad L) ∧
        ∀ M : Subgroup G, Maximal (fun K : Subgroup G => IsSubnormal K L ∧ K ≠ L) M →
          M = solvRad L) ∧
      (IsSimpleGroup (↥L ⧸ (solvRad L).subgroupOf L) ∧
        ∃ a b : ↥L ⧸ (solvRad L).subgroupOf L, a * b ≠ b * a) ∧
      cComp L = {L} := by
  have hsolv : Group.IsSolvable ↥(solvRad L) := solvRad_isSolvable L
  have hne : solvRad L ≠ L := fun h =>
    not_isSolvable_of_mem_cComp hL ((solvRad_eq_self_iff L).mp h)
  have hsubn : IsSubnormal (solvRad L) L :=
    A3.subnormal_of_normal (solvRad_le L) (solvRad_normal L)
  have hmax : ∀ M : Subgroup G, IsSubnormal M L → M ≠ L → M ≤ solvRad L := fun M hM hML =>
    le_solvRad_of_subnormal_lt hL hM (lt_of_le_of_ne (A3.subnormal_le hM) hML)
  have hnonab : ∃ a b : ↥L ⧸ (solvRad L).subgroupOf L, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have h1 : Group.IsSolvable (↥L ⧸ (solvRad L).subgroupOf L) := Group.isSolvable_of_comm hcomm
    have h2 : Group.IsSolvable ↥((solvRad L).subgroupOf L) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).injective
    exact not_isSolvable_of_mem_cComp hL
      (Group.isSolvable_of_subgroup_quotient ((solvRad L).subgroupOf L))
  have hsimple : IsSimpleGroup (↥L ⧸ (solvRad L).subgroupOf L) := by
    obtain ⟨a, b, hab⟩ := hnonab
    have hnt : Nontrivial (↥L ⧸ (solvRad L).subgroupOf L) :=
      ⟨⟨a, 1, fun h => hab (by rw [h, one_mul, mul_one])⟩⟩
    refine ⟨fun T hT => ?_⟩
    let M' : Subgroup ↥L := (solvRad L).subgroupOf L
    let P : Subgroup ↥L := T.comap (QuotientGroup.mk' M')
    have hPnormal : P.Normal := hT.comap _
    have hMP : M' ≤ P := fun x hx => by
      have h1 : (x : ↥L ⧸ M') = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      show (x : ↥L ⧸ M') ∈ T
      rw [h1]
      exact T.one_mem
    rcases normal_eq_top_or_map_le_solvRad hL P with hPtop | hle
    · right
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have : x ∈ P := hPtop ▸ Subgroup.mem_top x
      exact this
    · left
      have hPM : P ≤ M' := fun x hx => hle (Subgroup.mem_map_of_mem L.subtype hx)
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hxP : x ∈ P := hy
      exact (QuotientGroup.eq_one_iff x).mpr (hPM hxP)
  have hmaximal : Maximal (fun K : Subgroup G => IsSubnormal K L ∧ K ≠ L) (solvRad L) :=
    ⟨⟨hsubn, hne⟩, fun _ hy _ => hmax _ hy.1 hy.2⟩
  have hunique : ∀ M : Subgroup G,
      Maximal (fun K : Subgroup G => IsSubnormal K L ∧ K ≠ L) M → M = solvRad L := fun M hM =>
    le_antisymm (hmax M hM.1.1 hM.1.2) (hM.2 ⟨hsubn, hne⟩ (hmax M hM.1.1 hM.1.2))
  exact ⟨⟨hmaximal, hunique⟩, ⟨hsimple, hnonab⟩, cComp_self_eq_singleton hL⟩

theorem cComp_mem_of_le [Finite G] {X H L : Subgroup G} (hL : L ∈ cComp X) (hLH : L ≤ H)
    (hHX : H ≤ X) : L ∈ cComp H := by
  refine ⟨ne_bot_of_mem_cComp hL, perfect_of_mem_cComp hL,
    A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hL) hLH hHX, fun K hKL hKne hKperf hKsub => ?_⟩
  have hKL' : IsSubnormal K L := A3.subnormal_of_le_of_le hKsub hKL.le hLH
  have := perfectCore_eq_bot_of_subnormal_lt hL hKL' hKL
  rw [perfectCore_eq_self_of_perfect hKperf] at this
  exact hKne this

theorem cComp_mem_of_subnormal {X H K : Subgroup G} (hH : IsSubnormal H X) (hK : K ∈ cComp H) :
    K ∈ cComp X := by
  refine ⟨ne_bot_of_mem_cComp hK, perfect_of_mem_cComp hK,
    A3.subnormal_trans (subnormal_of_mem_cComp hK) hH, fun K' hK'K hK'ne hK'perf hK'sub => ?_⟩
  have hK'H : IsSubnormal K' H :=
    A3.subnormal_of_le_of_le hK'sub (hK'K.le.trans (le_of_mem_cComp hK)) (A3.subnormal_le hH)
  exact not_subnormal_of_mem_cComp hK hK'K hK'ne hK'perf hK'H

theorem cCompInter_subset_and_eq [Finite G] (X H : Subgroup G) :
    (H ≤ X → cCompInter X H ⊆ cComp H) ∧ (IsSubnormal H X → cCompInter X H = cComp H) := by
  refine ⟨fun hHX L hL => cComp_mem_of_le hL.1 hL.2 hHX, fun hHX => ?_⟩
  ext L
  constructor
  · intro hL
    exact cComp_mem_of_le hL.1 hL.2 (A3.subnormal_le hHX)
  · intro hL
    exact ⟨cComp_mem_of_subnormal hHX hL, le_of_mem_cComp hL⟩

theorem cComp_commutator_perfectCore [Finite G] {X L N : Subgroup G} (hL : L ∈ cComp X)
    (hNX : N ≤ X) (hNs : Group.IsSolvable N) (hLN : L ≤ Subgroup.normalizer (N : Set G)) :
    ⁅L, N⁆ ≤ L ∧ perfectCore (L ⊔ N) = L := by
  induction X using WellFoundedLT.induction generalizing L N with
  | _ X ih =>
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hL
  have hYX : L ⊔ N ≤ X := sup_le hLX hNX
  rcases eq_or_lt_of_le hYX with hYeq | hYlt
  · by_cases hLXeq : L = X
    · have hNL : N ≤ L := by rw [hLXeq]; exact hNX
      refine ⟨(Subgroup.commutator_mono le_rfl hNL).trans (A3.commutator_self_le L), ?_⟩
      rw [sup_eq_left.mpr hNL]
      exact perfectCore_eq_self_of_perfect hLperf
    · have hlt : L < X := lt_of_le_of_ne hLX hLXeq
      obtain ⟨P, hPX, hPn, hLP⟩ :=
        A3.subnormal_exists_normal_of_lt (subnormal_of_mem_cComp hL) hlt
      have hLPc : L ∈ cComp P := cComp_mem_of_le hL hLP hPX.le
      have hPXnorm : X ≤ Subgroup.normalizer (P : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hPX.le).mp hPn
      have hLnormP : L ≤ Subgroup.normalizer ((P ⊓ N : Subgroup G) : Set G) := fun l hl =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hPXnorm (hLX hl), hLN hl⟩
      have hPNs : Group.IsSolvable ↥(P ⊓ N) :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion (inf_le_right : P ⊓ N ≤ N)) (Subgroup.inclusion_injective _)
      obtain ⟨-, hperfP⟩ := ih P hPX hLPc inf_le_left hPNs hLnormP
      have hPeq : P = L ⊔ (P ⊓ N) := A3.eq_sup_inf_of_le_sup hLN hLP (hPX.le.trans hYeq.symm.le)
      rw [← hPeq] at hperfP
      have hXnormL : X ≤ Subgroup.normalizer (L : Set G) := by
        have := hPXnorm.trans (normalizer_le_normalizer_perfectCore P)
        rwa [hperfP] at this
      have hLnormX : (L.subgroupOf X).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hXnormL
      refine ⟨Subgroup.commutator_le.mpr fun l hl n hn => ?_, ?_⟩
      · have hn' : n ∈ Subgroup.normalizer (L : Set G) := hXnormL (hNX hn)
        have : n * l⁻¹ * n⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hn' l⁻¹).mp (L.inv_mem hl)
        simpa [commutatorElement_def, mul_assoc] using L.mul_mem hl this
      · rw [hYeq]
        exact le_antisymm (perfectCore_le_of_sup_solvable hLX hLnormX hYeq.symm hNs)
          (le_perfectCore_of_perfect hLX hLperf)
  · exact ih (L ⊔ N) hYlt (cComp_mem_of_le hL le_sup_left hYX) le_sup_right hNs hLN

@[expose] def lFamily (T : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ cComp (B ⊔ T)}

theorem cComp_subset_lFamily [Finite G] {T H : Subgroup G} (hTH : T ≤ H) :
    cComp H ⊆ lFamily T := fun _ hL =>
  cComp_mem_of_le hL le_sup_left (sup_le (le_of_mem_cComp hL) hTH)

end CFSG.Quasithin
