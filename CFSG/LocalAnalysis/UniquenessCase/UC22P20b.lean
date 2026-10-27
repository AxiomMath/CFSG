module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p20b_pCoreOf_le_T (D : Data G) {H : Subgroup G} (hTH : D.T ≤ H) :
    pCoreOf 2 H ≤ D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowG.of_le hTH le_top
  have hn : D.T ≤ normalizer (pCoreOf 2 H : Set G) :=
    hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hle : D.T ⊔ pCoreOf 2 H ≤ H := sup_le hTH (Subgroup.map_subtype_le _)
  have h := hsyl.eq_of_le le_sup_left hle (D.sylowM.isPGroup.to_sup_of_normal_right' hP2 hn)
  exact le_of_le_of_eq le_sup_right h

theorem uc22p20b_mem_hSet (D : Data G) {H Y : Subgroup G} (hH : H ∈ hSet D.T D.M)
    (hTY : D.T ≤ Y) (hYH : Y ≤ H) (hY : ¬ Y ≤ D.M) : Y ∈ hSet D.T D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hTY, hY, ?_⟩
  have hPT := uc22p20b_pCoreOf_le_T D hH.1
  have hP : pCoreOf 2 H ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPT.trans hTY)
      (hYH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  intro x hx
  have hx1 : x ∈ H := hYH hx.1
  have hx2 : x ∈ centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hP) hx.2
  exact hP (hH.2.2 ⟨hx1, hx2⟩)

theorem uc22p20b_le_M_of_solvable (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {H Y : Subgroup G} (hH : H ∈ hSet D.T D.M) (hTY : D.T ≤ Y) (hYH : Y ≤ H)
    (hs : Group.IsSolvable ↥Y) : Y ≤ D.M := by
  by_contra hY
  have hmem := uc22p20b_mem_hSet D hH hTY hYH hY
  obtain ⟨L, _, hL, hLB⟩ := (h1930 _ hmem).1
  obtain ⟨a, b, hab⟩ := hB L hLB
  exact hab (uc22p20a_abelian_of_compositionFactor hs hL a b)

theorem uc22p20b_isSylowOf_inf {X : Type} [Group X] [Finite X] (T₀ W : Subgroup X) [W.Normal]
    (hT : IsPGroup 2 T₀) (hT' : ¬ 2 ∣ T₀.index) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T₀ ⊓ W) W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTop : CFSG.ABGLocalTools.IsSylowOf 2 T₀ (⊤ : Subgroup X) :=
    (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨le_top, hT, by rwa [Subgroup.relIndex_top_right]⟩
  exact hTop.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge

theorem uc22p20b_normalizer_sup_eq_top {X : Type} [Group X] [Finite X] (T₀ W : Subgroup X)
    [W.Normal] (hT : IsPGroup 2 T₀) (hT' : ¬ 2 ∣ T₀.index) :
    normalizer ((T₀ ⊓ W : Subgroup X) : Set X) ⊔ W = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := uc22p20b_isSylowOf_inf T₀ W hT hT'
  have := Sylow.normalizer_sup_eq_top Q
  rwa [hQ] at this

theorem uc22p20b_solvable_normalizer {X : Type} [Group X] [Finite X] (T₀ W : Subgroup X)
    [W.Normal] (hT : IsPGroup 2 T₀) (hT' : ¬ 2 ∣ T₀.index) (hs : Group.IsSolvable (X ⧸ W)) :
    Group.IsSolvable ↥(normalizer ((T₀ ⊓ W : Subgroup X) : Set X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup X := T₀ ⊓ W with hSdef
  set N : Subgroup X := normalizer (S : Set X) with hNdef
  have hSyl := uc22p20b_isSylowOf_inf T₀ W hT hT'
  have hSW : S ≤ W := inf_le_right
  have hSN : S ≤ N := Subgroup.le_normalizer
  have hSN₁ : S ≤ N ⊓ W := le_inf hSN hSW
  have hS2 : IsPGroup 2 S := hT.to_inf_left
  haveI hSs : Group.IsSolvable ↥S := by
    haveI : Group.IsNilpotent ↥S := hS2.isNilpotent
    infer_instance
  have hN₁ : Group.IsSolvable ↥(N ⊓ W) := by
    have hnorm : (S.subgroupOf (N ⊓ W)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSN₁).2 inf_le_left
    haveI := hnorm
    haveI hSs' : Group.IsSolvable ↥(S.subgroupOf (N ⊓ W)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hSN₁).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hSN₁).injective
    have hodd : Odd (Nat.card (↥(N ⊓ W) ⧸ S.subgroupOf (N ⊓ W))) := by
      have h1 := (CFSG.ABGLocalTools.isSylowOf_iff.1 hSyl).2.2
      have h2 : S.relIndex (N ⊓ W) ∣ S.relIndex W := by
        rw [← Subgroup.relIndex_mul_relIndex S (N ⊓ W) W hSN₁ inf_le_right]
        exact dvd_mul_right _ _
      have h3 : ¬ 2 ∣ (S.subgroupOf (N ⊓ W)).index := fun h => h1 (h.trans h2)
      rw [← Subgroup.index_eq_card]
      exact Nat.odd_iff.2 (by omega)
    haveI : Group.IsSolvable (↥(N ⊓ W) ⧸ S.subgroupOf (N ⊓ W)) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact Group.isSolvable_of_ker_le_range (S.subgroupOf (N ⊓ W)).subtype
      (QuotientGroup.mk' (S.subgroupOf (N ⊓ W)))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  haveI := hN₁
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (inf_le_left : N ⊓ W ≤ N))
    ((QuotientGroup.mk' W).comp N.subtype) ?_
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  exact ⟨⟨x, x.2, hx⟩, rfl⟩

theorem uc22p20b_isSolvable_quotient {X : Type} [Group X] [Finite X] (W : Subgroup X) [W.Normal]
    (h : CFSG.perfectResidual X ≤ W) : Group.IsSolvable (X ⧸ W) := by
  haveI : Finite (Subgroup X) := Finite.of_injective _ SetLike.coe_injective
  haveI : WellFoundedLT (Subgroup X) := Finite.to_wellFoundedLT
  obtain ⟨y, ⟨N, rfl⟩, hy⟩ := (wellFounded_lt (α := Subgroup X)).has_min
    (Set.range fun n => derivedSeries X n) ⟨derivedSeries X 0, 0, rfl⟩
  have hN : derivedSeries X N ≤ W := by
    refine le_trans ?_ h
    refine le_iInf fun m => ?_
    have h1 : derivedSeries X (max m N) ≤ derivedSeries X N :=
      derivedSeries_antitone X (le_max_right m N)
    have h2 : derivedSeries X (max m N) ≤ derivedSeries X m :=
      derivedSeries_antitone X (le_max_left m N)
    have h3 : ¬ derivedSeries X (max m N) < derivedSeries X N :=
      hy _ ⟨max m N, rfl⟩
    exact (eq_of_le_of_not_lt h1 h3).symm.le.trans h2
  refine ⟨⟨N, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective W) N]
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  simpa using (QuotientGroup.eq_one_iff x).2 (hN hx)

theorem uc22p20b_exists_cCompSpan_mul (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    (h20_1 : S20_1_124 D) (h20_3 : S20_3 D) {H : Subgroup G} (hH : H ∈ hSet D.T D.M) :
    ∀ h ∈ H, ∃ c ∈ CFSG.Quasithin.cCompSpan H, ∃ m ∈ H ⊓ D.M, h = c * m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h hh
  have hR : OInf H ≤ D.M := (h20_1 h1930 H hH).2.2
  obtain ⟨W', hW'⟩ : ∃ W' : Subgroup ↥H, W' = CFSG.Quasithin.oInftyE ↥H := ⟨_, rfl⟩
  haveI hW'n : W'.Normal := hW' ▸ inferInstance
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subgroup ↥H, T₀ = D.T.subgroupOf H := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ := (D.sylowG.of_le hH.1 le_top).exists_sylow_eq_subgroupOf
  have hT₀p : IsPGroup 2 T₀ := by rw [hT₀, ← hQ]; exact Q.isPGroup'
  have hT₀i : ¬ 2 ∣ T₀.index := by rw [hT₀, ← hQ]; exact Q.not_dvd_index
  have hperf : CFSG.perfectResidual ↥H ≤ W' := by
    have h3 := h20_3 h1930 H hH
    unfold Hinf CFSG.inSubgroup at h3
    rw [hW']
    exact (Subgroup.map_le_map_iff_of_injective H.subtype_injective).1 h3
  have hsolv : Group.IsSolvable (↥H ⧸ W') := uc22p20b_isSolvable_quotient W' hperf
  have hfr := uc22p20b_normalizer_sup_eq_top T₀ W' hT₀p hT₀i
  have hNs := uc22p20b_solvable_normalizer T₀ W' hT₀p hT₀i hsolv
  obtain ⟨N, hN⟩ : ∃ N : Subgroup ↥H, N = normalizer ((T₀ ⊓ W' : Subgroup ↥H) : Set ↥H) :=
    ⟨_, rfl⟩
  rw [← hN] at hfr hNs
  have hT₀N : T₀ ≤ N := fun t ht => by
    rw [hN]
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, ?_⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr hW'n]
    trivial
  have hTY : D.T ≤ N.map H.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hH.1, ← hT₀]
    exact Subgroup.map_mono hT₀N
  have hYs : Group.IsSolvable ↥(N.map H.subtype) :=
    Group.isSolvable_of_surjective
      (f := (N.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
      (N.equivMapOfInjective H.subtype H.subtype_injective).surjective
  have hYM : N.map H.subtype ≤ D.M :=
    uc22p20b_le_M_of_solvable D hB h1930 hH hTY (Subgroup.map_subtype_le _) hYs
  have hmem : (⟨h, hh⟩ : ↥H) ∈ N ⊔ W' := hfr ▸ Subgroup.mem_top _
  obtain ⟨n, hn, w, hw, hnw⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hw' := hw
  rw [hW', CFSG.Quasithin.E1.oInftyE_eq_cCompSpan_sup] at hw'
  obtain ⟨c, hc, r, hr, hcr⟩ := Subgroup.mem_sup_of_normal_right.1 hw'
  have hnM : (n : G) ∈ D.M := hYM ⟨n, hn, rfl⟩
  have hrM : (r : G) ∈ D.M := hR ⟨r, hr, rfl⟩
  refine ⟨((n * c * n⁻¹ : ↥H) : G), ?_, ((n * r : ↥H) : G),
    ⟨(n * r).2, D.M.mul_mem hnM hrM⟩, ?_⟩
  · rw [CFSG.Quasithin.cCompSpan_eq_map_subtype]
    exact ⟨n * c * n⁻¹, (CFSG.Quasithin.cCompSpan_normal (G := ↥H)).conj_mem c hc n, rfl⟩
  · have : (⟨h, hh⟩ : ↥H) = (n * c * n⁻¹) * (n * r) := by
      rw [← hnw, ← hcr]
      group
    exact congrArg Subtype.val this

@[expose] def CompInCalL (D : Data G) : Prop :=
  ∀ H ∈ hSet D.T D.M, ∀ K ∈ CFSG.Quasithin.cComp H, ¬ K ≤ D.M → ∃ L ∈ calLOf D.T D.M H, K ≤ L

theorem uc22p20b_le_normalizer_iSup {ι : Sort*} (K : ι → Subgroup G) (A : Subgroup G)
    (hA : ∀ i, A ≤ normalizer (K i : Set G)) :
    A ≤ normalizer ((⨆ i, K i : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun i => Subgroup.mem_normalizer_iff_map_conj_eq.1 (hA i hg)

theorem uc22p20b_cCompSpan_le_mul (D : Data G) (h5 : CompInCalL D) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) :
    ∀ c ∈ CFSG.Quasithin.cCompSpan H, ∃ x ∈ (⨆ L ∈ calLOf D.T D.M H, L : Subgroup G),
      ∃ m ∈ H ⊓ D.M, c = x * m := by
  intro c hc
  let Zo : Subgroup G :=
    ⨆ K : {K : Subgroup G // K ∈ CFSG.Quasithin.cComp H ∧ ¬ K ≤ D.M}, (K : Subgroup G)
  let Zm : Subgroup G :=
    ⨆ K : {K : Subgroup G // K ∈ CFSG.Quasithin.cComp H ∧ K ≤ D.M}, (K : Subgroup G)
  have hZo : Zo ≤ ⨆ L ∈ calLOf D.T D.M H, L := by
    refine iSup_le fun K => ?_
    obtain ⟨L, hL, hKL⟩ := h5 H hH K.1 K.2.1 K.2.2
    exact hKL.trans (le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ calLOf D.T D.M H) => L) L hL)
  have hZm : Zm ≤ H ⊓ D.M :=
    iSup_le fun K => le_inf (CFSG.Quasithin.le_of_mem_cComp K.2.1) K.2.2
  have hnorm : ∀ K ∈ CFSG.Quasithin.cComp H,
      CFSG.Quasithin.cCompSpan H ≤ normalizer (K : Set G) := fun K hK =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.Quasithin.cComp_normal_span_of_le hK).1).1
      (CFSG.Quasithin.cComp_normal_span_of_le hK).2
  have hZmC : Zm ≤ CFSG.Quasithin.cCompSpan H :=
    iSup_le fun K => CFSG.Quasithin.le_cCompSpan K.2.1
  have hCo : CFSG.Quasithin.cCompSpan H ≤ normalizer (Zo : Set G) :=
    uc22p20b_le_normalizer_iSup _ _ fun K => hnorm K.1 K.2.1
  have hcZ : c ∈ Zo ⊔ Zm := by
    have : CFSG.Quasithin.cCompSpan H ≤ Zo ⊔ Zm := by
      refine sSup_le fun K hK => ?_
      by_cases hKM : K ≤ D.M
      · exact le_sup_of_le_right (le_iSup (fun K : {K : Subgroup G //
          K ∈ CFSG.Quasithin.cComp H ∧ K ≤ D.M} => (K : Subgroup G)) ⟨K, hK, hKM⟩)
      · exact le_sup_of_le_left (le_iSup (fun K : {K : Subgroup G //
          K ∈ CFSG.Quasithin.cComp H ∧ ¬ K ≤ D.M} => (K : Subgroup G)) ⟨K, hK, hKM⟩)
    exact this hc
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Zo Zm (hZmC.trans hCo)]
    at hcZ
  obtain ⟨x, hx, m, hm, rfl⟩ := hcZ
  exact ⟨x, hZo hx, m, hZm hm, rfl⟩

theorem uc22p20b_s20_4_of_comp (D : Data G) (hB : ListBNonabelian) (h20_1 : S20_1_124 D)
    (h20_3 : S20_3 D) (h5 : CompInCalL D) : S20_4 D := by
  intro h1930 H hH
  have hXH : (⨆ L ∈ calLOf D.T D.M H, L : Subgroup G) ≤ H :=
    iSup₂_le fun L hL => CFSG.Open.IsSubnormal.le hL.2
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, m, hm, rfl⟩
    exact H.mul_mem (hXH hx) hm.1
  · intro h hh
    obtain ⟨c, hc, m, hm, rfl⟩ := uc22p20b_exists_cCompSpan_mul D hB h1930 h20_1 h20_3 hH h hh
    obtain ⟨x, hx, m', hm', rfl⟩ := uc22p20b_cCompSpan_le_mul D h5 hH c hc
    exact ⟨x, hx, m' * m, (H ⊓ D.M).mul_mem hm' hm, by rw [mul_assoc]⟩

@[expose] def uc22p20bCj (t : G) (K : Subgroup G) : Subgroup G :=
  K.map (MulAut.conj t).toMonoidHom

@[expose] def uc22p20bOrb (T K : Subgroup G) : Subgroup G :=
  ⨆ t : T, uc22p20bCj (t : G) K

theorem uc22p20b_mem_cj {t : G} {K : Subgroup G} {x : G} :
    x ∈ uc22p20bCj t K ↔ ∃ y ∈ K, t * y * t⁻¹ = x := by
  simp [uc22p20bCj, Subgroup.mem_map]

theorem uc22p20b_cj_cj (a b : G) (K : Subgroup G) :
    uc22p20bCj a (uc22p20bCj b K) = uc22p20bCj (a * b) K := by
  ext x
  simp only [uc22p20b_mem_cj]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by group⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, by group⟩

theorem uc22p20b_cj_one (K : Subgroup G) : uc22p20bCj 1 K = K := by
  ext x
  simp [uc22p20b_mem_cj]

theorem uc22p20b_cj_le_orb {T K : Subgroup G} {t : G} (ht : t ∈ T) :
    uc22p20bCj t K ≤ uc22p20bOrb T K :=
  le_iSup (fun t : T => uc22p20bCj (t : G) K) ⟨t, ht⟩

theorem uc22p20b_le_orb (T K : Subgroup G) : K ≤ uc22p20bOrb T K := by
  have := uc22p20b_cj_le_orb (T := T) (K := K) T.one_mem
  rwa [uc22p20b_cj_one] at this

theorem uc22p20b_orb_le {T K H : Subgroup G} (hTH : T ≤ H) (hKH : K ≤ H) :
    uc22p20bOrb T K ≤ H := by
  refine iSup_le fun t x hx => ?_
  obtain ⟨y, hy, rfl⟩ := uc22p20b_mem_cj.1 hx
  exact H.mul_mem (H.mul_mem (hTH t.2) (hKH hy)) (H.inv_mem (hTH t.2))

theorem uc22p20b_le_normalizer_orb (T K : Subgroup G) : T ≤ normalizer (uc22p20bOrb T K : Set G) := by
  have key : ∀ g ∈ T, ∀ x ∈ uc22p20bOrb T K, g * x * g⁻¹ ∈ uc22p20bOrb T K := by
    intro g hg x hx
    have hmap : (uc22p20bOrb T K).map (MulAut.conj g).toMonoidHom ≤ uc22p20bOrb T K := by
      rw [uc22p20bOrb, Subgroup.map_iSup]
      refine iSup_le fun t => ?_
      have : (uc22p20bCj (t : G) K).map (MulAut.conj g).toMonoidHom = uc22p20bCj (g * t) K :=
        uc22p20b_cj_cj g t K
      rw [this]
      exact uc22p20b_cj_le_orb (T.mul_mem hg t.2)
    exact hmap ⟨x, hx, by simp [MulAut.conj_apply]⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ (T.inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem uc22p20b_orb_perfect {T K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    ⁅uc22p20bOrb T K, uc22p20bOrb T K⁆ = uc22p20bOrb T K := by
  refine CFSG.Quasithin.A3.commutator_iSup_eq_of_perfect (fun t : T => uc22p20bCj (t : G) K)
    fun t => ?_
  show ⁅K.map (MulAut.conj (t : G)).toMonoidHom, K.map (MulAut.conj (t : G)).toMonoidHom⁆ =
    K.map (MulAut.conj (t : G)).toMonoidHom
  rw [← Subgroup.map_commutator, hK]

theorem uc22p20b_cj_mem_cComp {H K : Subgroup G} (hK : K ∈ CFSG.Quasithin.cComp H) {t : G}
    (ht : t ∈ H) : uc22p20bCj t K ∈ CFSG.Quasithin.cComp H := by
  have h := CFSG.Quasithin.cComp_map_mulEquiv (MulAut.conj t) hK
  have hH : H.map (MulAut.conj t).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer ht)
  rw [hH] at h
  exact h

theorem uc22p20b_normal_cCompSpan (H : Subgroup G) :
    ((CFSG.Quasithin.cCompSpan H).subgroupOf H).Normal := by
  rw [CFSG.Quasithin.cCompSpan_eq_map_subtype, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact CFSG.Quasithin.cCompSpan_normal

theorem uc22p20b_orb_subnormal {T H K : Subgroup G} (hK : K ∈ CFSG.Quasithin.cComp H)
    (hTH : T ≤ H) : CFSG.Open.IsSubnormal (uc22p20bOrb T K) H := by
  have hmem : ∀ t : T, uc22p20bCj (t : G) K ∈ CFSG.Quasithin.cComp H := fun t =>
    uc22p20b_cj_mem_cComp hK (hTH t.2)
  have hnorm : ∀ t : T, CFSG.Quasithin.cCompSpan H ≤ normalizer (uc22p20bCj (t : G) K : Set G) :=
    fun t => (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.Quasithin.cComp_normal_span_of_le (hmem t)).1).1
      (CFSG.Quasithin.cComp_normal_span_of_le (hmem t)).2
  have hLC : uc22p20bOrb T K ≤ CFSG.Quasithin.cCompSpan H :=
    iSup_le fun t => CFSG.Quasithin.le_cCompSpan (hmem t)
  have hCn : CFSG.Quasithin.cCompSpan H ≤ normalizer (uc22p20bOrb T K : Set G) :=
    uc22p20b_le_normalizer_iSup _ _ hnorm
  have hCH : CFSG.Quasithin.cCompSpan H ≤ H := by
    rw [CFSG.Quasithin.cCompSpan_eq_map_subtype]
    exact Subgroup.map_subtype_le _
  exact CFSG.Open.IsSubnormal.step hLC ((Subgroup.normal_subgroupOf_iff_le_normalizer hLC).2 hCn)
    (CFSG.Open.IsSubnormal.step hCH (uc22p20b_normal_cCompSpan H) (CFSG.Open.IsSubnormal.refl H))

theorem uc22p20b_mem_of_le_sSup {X : Subgroup G} (𝒪 : Set (Subgroup G))
    (h𝒪 : 𝒪 ⊆ CFSG.Quasithin.cComp X) {C : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp X)
    (hCle : C ≤ sSup 𝒪) : C ∈ 𝒪 := by
  by_contra hCnot
  set R : Subgroup G := CFSG.Quasithin.solvRad X with hR
  have hcomm : ∀ K' ∈ 𝒪, ∀ c ∈ C, ∀ k ∈ K', ⁅c, k⁆ ∈ R := by
    intro K' hK' c hc k hk
    have hne : C ≠ K' := fun h => hCnot (h ▸ hK')
    have hK'X : K' ∈ CFSG.Quasithin.cComp X := h𝒪 hK'
    have hnormK' : CFSG.Quasithin.cCompSpan X ≤ normalizer (K' : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.Quasithin.cComp_normal_span_of_le hK'X).1).1
        (CFSG.Quasithin.cComp_normal_span_of_le hK'X).2
    have hCK' : ⁅C, K'⁆ ≤ R := by
      rcases CFSG.Quasithin.cComp_commutator_dichotomy_of_le hC
          (CFSG.Quasithin.le_of_mem_cComp hK'X) with ⟨h1, -⟩ | h2
      · exact h1
      · exfalso
        have hle : ⁅C, K'⁆ ≤ K' := by
          refine Subgroup.commutator_le.mpr fun c' hc' k' hk' => ?_
          have hc'N := hnormK' (CFSG.Quasithin.le_cCompSpan hC hc')
          have : c' * k' * c'⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.1 hc'N k').1 hk'
          exact K'.mul_mem this (K'.inv_mem hk')
        have hCle' : C ≤ K' :=
          (CFSG.Quasithin.le_conjClosure C K').trans (h2 ▸ hle)
        rcases eq_or_lt_of_le hCle' with heq | hlt
        · exact hne heq
        · exact CFSG.Quasithin.not_subnormal_of_mem_cComp hK'X hlt
            (CFSG.Quasithin.ne_bot_of_mem_cComp hC) (CFSG.Quasithin.perfect_of_mem_cComp hC)
            (CFSG.Quasithin.subnormal_of_mem_cComp hC)
    exact hCK' (Subgroup.commutator_mem_commutator hc hk)
  let Zg : Subgroup G :=
    { carrier := {g | g ∈ X ∧ ∀ c ∈ C, ⁅c, g⁆ ∈ R}
      one_mem' := ⟨X.one_mem, fun c _ => by simp [R]⟩
      mul_mem' := by
        rintro g h ⟨hgX, hg⟩ ⟨hhX, hh⟩
        refine ⟨X.mul_mem hgX hhX, fun c hc => ?_⟩
        have e : ⁅c, g * h⁆ = ⁅c, g⁆ * (g * ⁅c, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact R.mul_mem (hg c hc)
          (CFSG.Quasithin.conj_mem_solvRad (Subgroup.le_normalizer hgX) (hh c hc))
      inv_mem' := by
        rintro g ⟨hgX, hg⟩
        refine ⟨X.inv_mem hgX, fun c hc => ?_⟩
        have e : ⁅c, g⁻¹⁆ = g⁻¹ * ⁅c, g⁆⁻¹ * g := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := CFSG.Quasithin.conj_mem_solvRad (Subgroup.le_normalizer (X.inv_mem hgX))
          (R.inv_mem (hg c hc))
        simpa [mul_assoc] using this }
  have h𝒪Z : sSup 𝒪 ≤ Zg := by
    refine sSup_le fun K' hK' k hk => ?_
    exact ⟨CFSG.Quasithin.le_of_mem_cComp (h𝒪 hK') hk, fun c hc => hcomm K' hK' c hc k hk⟩
  have hCC : ⁅C, C⁆ ≤ R := by
    refine Subgroup.commutator_le.mpr fun c hc c' hc' => ?_
    exact (h𝒪Z (hCle hc')).2 c hc
  have hCR : C ≤ R := by
    rw [← CFSG.Quasithin.perfect_of_mem_cComp hC]
    exact hCC
  haveI : Group.IsSolvable ↥R := CFSG.Quasithin.solvRad_isSolvable X
  exact CFSG.Quasithin.not_isSolvable_of_mem_cComp hC
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hCR)
      (Subgroup.inclusion_injective hCR))

theorem uc22p20b_isQuasisimple_cComp_of_layer {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.layer Y = ⊤) {C : Subgroup Y} (hC : C ∈ CFSG.Quasithin.cComp (⊤ : Subgroup Y)) :
    CFSG.IsQuasisimple ↥C := by
  set R := CFSG.solvableRadical Y with hRdef
  haveI hRn : R.Normal := inferInstance
  have hRs : Group.IsSolvable ↥R := CFSG.Quasithin.A3.solvableRadical_isSolvable
  have hcent : ⁅CFSG.layer Y, R⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hRs hRn.isSubnormal).2
  rw [hY] at hcent
  have hRc : R ≤ Subgroup.center Y := Subgroup.commutator_top_left_eq_bot_iff_le_center.1 hcent
  have hker : Group.IsSolvable (QuotientGroup.mk' R).ker := by
    rw [QuotientGroup.ker_mk']; exact hRs
  have hCbar := CFSG.Quasithin.map_mem_cComp_top (QuotientGroup.mk' R)
    (QuotientGroup.mk'_surjective R) hker hC
  have hcomp : CFSG.IsComponent (C.map (QuotientGroup.mk' R)) :=
    CFSG.Quasithin.isComponent_of_mem_cComp_top
      (CFSG.Quasithin.A3.solvableRadical_quotient_eq_bot Y) hCbar
  have hperf : Group.IsPerfect ↥C :=
    Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfect_of_mem_cComp hC)
  refine (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf
    ((QuotientGroup.mk' R).subgroupMap C) ((QuotientGroup.mk' R).subgroupMap_surjective C)
    ?_).2 hcomp.1
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxR : ((x : ↥C) : Y) ∈ R := by
    have h1 : (QuotientGroup.mk' R) ((x : ↥C) : Y) = 1 := congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff _).1 h1
  rw [Subgroup.mem_center_iff]
  intro z
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hRc hxR) (z : Y))

theorem uc22p20b_cComp_orb {T H K : Subgroup G} (hK : K ∈ CFSG.Quasithin.cComp H) (hTH : T ≤ H) :
    CFSG.Quasithin.cComp (uc22p20bOrb T K) = Set.range (fun t : T => uc22p20bCj (t : G) K) := by
  have hsub := uc22p20b_orb_subnormal hK hTH
  have hLH : uc22p20bOrb T K ≤ H :=
    uc22p20b_orb_le hTH (CFSG.Quasithin.le_of_mem_cComp hK)
  ext C
  constructor
  · intro hC
    have hCH : C ∈ CFSG.Quasithin.cComp H := CFSG.Quasithin.cComp_mem_of_subnormal hsub hC
    refine uc22p20b_mem_of_le_sSup (X := H) (Set.range fun t : T => uc22p20bCj (t : G) K) ?_ hCH ?_
    · rintro _ ⟨t, rfl⟩
      exact uc22p20b_cj_mem_cComp hK (hTH t.2)
    · rw [sSup_range]
      exact CFSG.Quasithin.le_of_mem_cComp hC
  · rintro ⟨t, rfl⟩
    exact CFSG.Quasithin.cComp_mem_of_le (uc22p20b_cj_mem_cComp hK (hTH t.2))
      (uc22p20b_cj_le_orb t.2) hLH

theorem uc22p20b_sSup_cComp_orb {T H K : Subgroup G} (hK : K ∈ CFSG.Quasithin.cComp H)
    (hTH : T ≤ H) : sSup (CFSG.Quasithin.cComp (uc22p20bOrb T K)) = uc22p20bOrb T K := by
  set L := uc22p20bOrb T K with hLdef
  refine le_antisymm (sSup_le fun C hC => CFSG.Quasithin.le_of_mem_cComp hC) ?_
  refine iSup_le fun t => le_sSup ?_
  rw [hLdef, uc22p20b_cComp_orb hK hTH]
  exact ⟨t, rfl⟩

theorem uc22p20b_oInftyE_orb {T H K : Subgroup G} (hK : K ∈ CFSG.Quasithin.cComp H)
    (hTH : T ≤ H) : CFSG.Quasithin.oInftyE ↥(uc22p20bOrb T K) = ⊤ := by
  set L := uc22p20bOrb T K with hLdef
  have hspan : CFSG.Quasithin.cCompSpan L = L := uc22p20b_sSup_cComp_orb hK hTH
  have h5 := (CFSG.Quasithin.cComp_part_five_of_le L).2
  rw [hspan] at h5
  have hL : L ≤ (CFSG.Quasithin.oInftyE ↥L).map L.subtype :=
    h5.le.trans (CFSG.Quasithin.perfectCore_le _)
  rw [eq_top_iff]
  intro x _
  obtain ⟨w, hw, hwx⟩ := hL x.2
  have : w = x := Subtype.ext hwx
  exact this ▸ hw

theorem uc22p20b_conjTransitive_orb {T H K : Subgroup G} (hK : K ∈ CFSG.Quasithin.cComp H)
    (hTH : T ≤ H) :
    ConjTransitive (uc22p20bOrb T K ⊔ T) (CFSG.Quasithin.cComp (uc22p20bOrb T K)) := by
  intro C₁ h₁ C₂ h₂
  rw [uc22p20b_cComp_orb hK hTH] at h₁ h₂
  obtain ⟨t₁, rfl⟩ := h₁
  obtain ⟨t₂, rfl⟩ := h₂
  refine ⟨(t₂ : G) * (t₁ : G)⁻¹, le_sup_right (a := uc22p20bOrb T K) (T.mul_mem t₂.2 (T.inv_mem t₁.2)),
    ?_⟩
  show uc22p20bCj (t₂ : G) K = uc22p20bCj ((t₂ : G) * (t₁ : G)⁻¹) (uc22p20bCj (t₁ : G) K)
  rw [uc22p20b_cj_cj]
  congr 2
  group

theorem uc22p20b_isPGroup_pCoreOf (K : Subgroup G) : IsPGroup 2 (pCoreOf 2 K) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype

theorem uc22p20b_pCoreOf_le (K : Subgroup G) : pCoreOf 2 K ≤ K :=
  Subgroup.map_subtype_le _

theorem uc22p20b_le_pCoreOf {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 P)
    (hn : ∀ k ∈ K, ∀ x ∈ P, k * x * k⁻¹ ∈ P) : P ≤ pCoreOf 2 K := by
  have hN : (P.subgroupOf K).Normal := ⟨fun x hx k => hn (k : G) k.2 x hx⟩
  have hQ : IsPGroup 2 (P.subgroupOf K) := hP.comap_subtype
  have hle : P.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hN, hQ⟩
  intro x hx
  exact ⟨⟨x, hPK hx⟩, hle hx, rfl⟩

theorem uc22p20b_conj_mem_pCoreOf_self {K : Subgroup G} {k x : G} (hk : k ∈ K)
    (hx : x ∈ pCoreOf 2 K) : k * x * k⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem y hy ⟨k, hk⟩, rfl⟩

theorem uc22p20b_pCoreOf_le_of_subnormal {K L : Subgroup G} (h : CFSG.Open.IsSubnormal K L) :
    pCoreOf 2 K ≤ pCoreOf 2 L := by
  induction h with
  | refl => exact le_rfl
  | @step K M L hKM hN _ ih =>
    refine le_trans ?_ ih
    have hnorm : ∀ n ∈ M, ∀ k ∈ K, n * k * n⁻¹ ∈ K := fun n hn k hk =>
      (Subgroup.normal_subgroupOf_iff hKM).1 hN k n hk hn
    refine uc22p20b_le_pCoreOf ((uc22p20b_pCoreOf_le K).trans hKM) (uc22p20b_isPGroup_pCoreOf K) ?_
    intro m hm x hx
    have hPK : (pCoreOf 2 K).map (MulAut.conj m).toMonoidHom ≤ K := by
      rintro _ ⟨y, hy, rfl⟩
      exact hnorm m hm y (uc22p20b_pCoreOf_le K hy)
    have hP2 : IsPGroup 2 ((pCoreOf 2 K).map (MulAut.conj m).toMonoidHom) :=
      (uc22p20b_isPGroup_pCoreOf K).map _
    have hPn : ∀ k ∈ K, ∀ y ∈ (pCoreOf 2 K).map (MulAut.conj m).toMonoidHom,
        k * y * k⁻¹ ∈ (pCoreOf 2 K).map (MulAut.conj m).toMonoidHom := by
      rintro k hk _ ⟨y, hy, rfl⟩
      have hk' : m⁻¹ * k * m ∈ K := by simpa using hnorm m⁻¹ (M.inv_mem hm) k hk
      refine ⟨(m⁻¹ * k * m) * y * (m⁻¹ * k * m)⁻¹,
        uc22p20b_conj_mem_pCoreOf_self hk' hy, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      group
    exact uc22p20b_le_pCoreOf hPK hP2 hPn ⟨x, hx, rfl⟩

theorem uc22p20b_isQuasisimple_bar2 {L K : Subgroup G} (hL : OTwoE ↥L = ⊤)
    (hK : K ∈ CFSG.Quasithin.cComp L) : CFSG.Open.IsQuasisimple (Bar2 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKL : K ≤ L := CFSG.Quasithin.le_of_mem_cComp hK
  have hsub : CFSG.Open.IsSubnormal K L := CFSG.Quasithin.subnormal_of_mem_cComp hK
  haveI hPn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hlayer : CFSG.layer (↥L ⧸ CFSG.pCore 2 ↥L) = ⊤ := by
    have h1 : (CFSG.layer (↥L ⧸ CFSG.pCore 2 ↥L)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
        ⊤ := hL
    have h2 := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)) (CFSG.layer (↥L ⧸ CFSG.pCore 2 ↥L))
    rw [h1, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    exact h2.symm
  haveI hPs : Group.IsSolvable ↥(CFSG.pCore 2 ↥L) := by
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥L) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
    infer_instance
  have hK' : K.subgroupOf L ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥L) :=
    CFSG.Quasithin.subgroupOf_mem_cComp hK
  have hKbar := CFSG.Quasithin.map_mem_cComp_top (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hPs) hK'
  have hqs : CFSG.IsQuasisimple ↥((K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
    uc22p20b_isQuasisimple_cComp_of_layer hlayer hKbar
  let φ : ↥K →* ↥L ⧸ CFSG.pCore 2 ↥L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hKL)
  have hrange : φ.range = (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hKL x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ.ker = CFSG.pCore 2 ↥K := by
    have key : ∀ x : ↥K, x ∈ φ.ker ↔ ((x : ↥K) : G) ∈ pCoreOf 2 L := by
      intro x
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (Subgroup.inclusion hKL x) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      constructor
      · intro h
        exact ⟨Subgroup.inclusion hKL x, h, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = Subgroup.inclusion hKL x := Subtype.ext hyx
        exact this ▸ hy
    ext x
    rw [key]
    have key2 : x ∈ CFSG.pCore 2 ↥K ↔ ((x : ↥K) : G) ∈ pCoreOf 2 K := by
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        exact this ▸ hy
    rw [key2]
    constructor
    · intro h
      refine uc22p20b_le_pCoreOf (K := K) (P := K ⊓ pCoreOf 2 L) inf_le_left
        ((uc22p20b_isPGroup_pCoreOf L).to_inf_right) ?_ ⟨x.2, h⟩
      intro k hk y hy
      exact ⟨K.mul_mem (K.mul_mem hk hy.1) (K.inv_mem hk),
        uc22p20b_conj_mem_pCoreOf_self (hKL hk) hy.2⟩
    · intro h
      exact uc22p20b_pCoreOf_le_of_subnormal hsub h
  let e : Bar2 K ≃* ↥((K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)
  exact (CFSG.Open.IsQuasisimple.of_mulEquiv e (CFSG.Quasithin.A3.isQuasisimple_iff_open.1 hqs))

def uc22p20bSimpSec (X : Type) [Group X] (Λ : Type) [Group Λ] : Prop :=
  IsSimpleGroup Λ ∧ ∃ (M : Subgroup X) (φ : ↥M →* Λ), M.IsSubnormal ∧ Function.Surjective φ ∧
    (φ.ker.map M.subtype).IsSubnormal

theorem uc22p20b_simpSec_of_cf {X : Type} [Group X] {Λ : Type} [Group Λ]
    (h : CFSG.Quasithin.E1.IsCompositionFactor X Λ) : uc22p20bSimpSec X Λ := by
  obtain ⟨N, M, hNM, hle, hN, hM, hs, ⟨e⟩⟩ := h
  haveI := hs
  refine ⟨e.symm.isSimpleGroup, M, e.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf M)), hM, ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · have : (e.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf M))).ker = N.subgroupOf M := by
      ext x
      simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [this, Subgroup.map_subgroupOf_eq_of_le hle]
    exact hN

theorem uc22p20b_simpSec_of_surjective {A Q : Type} [Group A] [Group Q] {Λ : Type} [Group Λ]
    (ψ : A →* Q) (hψ : Function.Surjective ψ) (h : uc22p20bSimpSec Q Λ) : uc22p20bSimpSec A Λ := by
  obtain ⟨hΛ, M, φ, hM, hφ, hk⟩ := h
  refine ⟨hΛ, M.comap ψ, φ.comp (ψ.subgroupComap M), hM.comap ψ, ?_, ?_⟩
  · exact hφ.comp (ψ.subgroupComap_surjective_of_surjective M hψ)
  · have : ((φ.comp (ψ.subgroupComap M)).ker).map (M.comap ψ).subtype =
        (φ.ker.map M.subtype).comap ψ := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨ψ.subgroupComap M y, hy, rfl⟩
      · rintro ⟨m, hm, hmx⟩
        have hxM : ψ x ∈ M := by rw [← hmx]; exact m.2
        refine ⟨⟨x, hxM⟩, ?_, rfl⟩
        have : ψ.subgroupComap M ⟨x, hxM⟩ = m := Subtype.ext hmx.symm
        rw [this]; exact hm
    rw [this]
    exact hk.comap ψ

theorem uc22p20b_simpSec_comm {X : Type} [Group X] [Group.IsSolvable X] {Λ : Type} [Group Λ]
    (h : uc22p20bSimpSec X Λ) : ∀ a b : Λ, a * b = b * a := by
  obtain ⟨hΛ, M, φ, -, hφ, -⟩ := h
  haveI : Group.IsSolvable ↥M := inferInstance
  haveI : Group.IsSolvable Λ := Group.isSolvable_of_surjective hφ
  exact IsSimpleGroup.comm_iff_isSolvable.2 inferInstance

theorem uc22p20b_simpSec_simple {S : Type} [Group S] [IsSimpleGroup S] {Λ : Type} [Group Λ]
    (hnc : ∃ a b : Λ, a * b ≠ b * a) (h : uc22p20bSimpSec S Λ) : Nonempty (S ≃* Λ) := by
  obtain ⟨hΛ, M, φ, hM, hφ, hk⟩ := h
  obtain ⟨a, b, hab⟩ := hnc
  have hMtop : M = ⊤ := by
    rcases CFSG.Open.IsSubnormal.eq_bot_or_top (CFSG.Open.IsSubnormal.top_iff.2 hM) with h | h
    · exfalso
      subst h
      obtain ⟨x, rfl⟩ := hφ a
      obtain ⟨y, rfl⟩ := hφ b
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      have hy : y = 1 := Subtype.ext (Subgroup.mem_bot.1 y.2)
      exact hab (by rw [hx, hy])
    · exact h
  subst hMtop
  rcases CFSG.Open.IsSubnormal.eq_bot_or_top (CFSG.Open.IsSubnormal.top_iff.2 hk) with h | h
  ·
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have : (x : S) ∈ φ.ker.map (⊤ : Subgroup S).subtype := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subtype.ext (Subgroup.mem_bot.1 this)
    exact ⟨(Subgroup.topEquiv (G := S)).symm.trans (MulEquiv.ofBijective φ ⟨hinj, hφ⟩)⟩
  · exfalso
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    have hx : x ∈ φ.ker := by
      have : (x : S) ∈ φ.ker.map (⊤ : Subgroup S).subtype := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨z, hz, hzx⟩ := this
      have : z = x := Subtype.ext hzx
      exact this ▸ hz
    have hy : y ∈ φ.ker := by
      have : (y : S) ∈ φ.ker.map (⊤ : Subgroup S).subtype := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
    rw [MonoidHom.mem_ker] at hx hy
    exact hab (by rw [hx, hy])

theorem uc22p20b_simpSec_restrict {X : Type} [Group X] (N : Subgroup X) [N.Normal] {Λ : Type} [Group Λ]
    (h : uc22p20bSimpSec X Λ) : uc22p20bSimpSec ↥N Λ ∨ uc22p20bSimpSec (X ⧸ N) Λ := by
  obtain ⟨hΛ, M, φ, hM, hφ, hk⟩ := h
  have hNM : (N.subgroupOf M).Normal := Subgroup.normal_subgroupOf
  haveI := hNM
  haveI : ((N.subgroupOf M).map φ).Normal := Subgroup.Normal.map hNM φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf M).map φ) with hbot | htop
  ·
    right
    have hle : N.subgroupOf M ≤ φ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      have : φ x ∈ (N.subgroupOf M).map φ := ⟨x, hx, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    let ρ : ↥M →* ↥(M.map (QuotientGroup.mk' N)) := (QuotientGroup.mk' N).subgroupMap M
    have hρ : Function.Surjective ρ := (QuotientGroup.mk' N).subgroupMap_surjective M
    have hker : ρ.ker ≤ φ.ker := by
      intro x hx
      apply hle
      rw [MonoidHom.mem_ker] at hx
      have h1 : (((x : ↥M) : X) : X ⧸ N) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff ((x : ↥M) : X)).1 h1
    let φ₂ : ↥(M.map (QuotientGroup.mk' N)) →* Λ := ρ.liftOfSurjective hρ ⟨φ, hker⟩
    have hφ₂ : ∀ m, φ₂ (ρ m) = φ m := fun m =>
      MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨φ, hker⟩ m
    refine ⟨hΛ, M.map (QuotientGroup.mk' N), φ₂, hM.map (QuotientGroup.mk'_surjective N), ?_, ?_⟩
    · intro l
      obtain ⟨m, rfl⟩ := hφ l
      exact ⟨ρ m, hφ₂ m⟩
    · have : (φ₂.ker).map (M.map (QuotientGroup.mk' N)).subtype =
          (φ.ker.map M.subtype).map (QuotientGroup.mk' N) := by
        ext y
        simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype]
        constructor
        · rintro ⟨z, hz, rfl⟩
          obtain ⟨m, rfl⟩ := hρ z
          rw [hφ₂] at hz
          exact ⟨(m : X), ⟨m, hz, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
          refine ⟨ρ m, ?_, rfl⟩
          rw [hφ₂]; exact hm
      rw [this]
      exact hk.map (QuotientGroup.mk'_surjective N)
  ·
    left
    let M₁ : Subgroup ↥N := M.subgroupOf N
    let ι : ↥M₁ →* ↥M := (N.subtype.comp M₁.subtype).codRestrict M (fun y => y.2)
    have hι : ∀ y : ↥M₁, ((ι y : ↥M) : X) = (((y : ↥N)) : X) := fun y => rfl
    refine ⟨hΛ, M₁, φ.comp ι, hM.comap N.subtype, ?_, ?_⟩
    · intro l
      have hl : l ∈ (N.subgroupOf M).map φ := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨m, hm, rfl⟩ := hl
      have hmN : (m : X) ∈ N := hm
      refine ⟨⟨⟨(m : X), hmN⟩, show ((m : X)) ∈ M from m.2⟩, ?_⟩
      show φ (ι _) = φ m
      congr 1
    · have : ((φ.comp ι).ker).map M₁.subtype = (φ.ker.map M.subtype).comap N.subtype := by
        ext z
        simp only [Subgroup.mem_map, Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply,
          Subgroup.coe_subtype]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨ι y, hy, rfl⟩
        · rintro ⟨m, hm, hmz⟩
          have hzM : (z : X) ∈ M := by rw [← hmz]; exact m.2
          refine ⟨⟨z, hzM⟩, ?_, rfl⟩
          have : ι ⟨z, hzM⟩ = m := Subtype.ext hmz.symm
          show φ (ι ⟨z, hzM⟩) = 1
          rw [this]; exact hm
      rw [this]
      exact hk.comap N.subtype

theorem uc22p20b_simpSec_cComp {X C : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp X) {Λ : Type} [Group Λ]
    (hnc : ∃ a b : Λ, a * b ≠ b * a) (h : uc22p20bSimpSec ↥C Λ) :
    Nonempty (BarInf C ≃* Λ) := by
  haveI hNn : (CFSG.solvableRadical ↥C).Normal := inferInstance
  haveI hsolv : Group.IsSolvable ↥(CFSG.solvableRadical ↥C) :=
    CFSG.Quasithin.A3.solvableRadical_isSolvable
  rcases uc22p20b_simpSec_restrict (CFSG.solvableRadical ↥C) h with h1 | h2
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (uc22p20b_simpSec_comm h1 a b)
  · have hsimple : IsSimpleGroup (BarInf C) := by
      have hstruct := (CFSG.Quasithin.cComp_structure hC).2.1.1
      have heq : (CFSG.Quasithin.solvRad C).subgroupOf C = CFSG.solvableRadical ↥C := by
        rw [CFSG.Quasithin.solvRad_eq_map_solvableRadical, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      haveI := hstruct
      exact (QuotientGroup.quotientMulEquivOfEq heq).symm.isSimpleGroup
    haveI := hsimple
    exact uc22p20b_simpSec_simple hnc h2

theorem uc22p20b_simpSec_sSup_cComp {L : Subgroup G} {Λ : Type} [Group Λ]
    (hnc : ∃ a b : Λ, a * b ≠ b * a) (F : Set (Subgroup G)) (hF : F.Finite)
    (hFL : F ⊆ CFSG.Quasithin.cComp L) (h : uc22p20bSimpSec ↥(sSup F) Λ) :
    ∃ C ∈ F, Nonempty (BarInf C ≃* Λ) := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    exfalso
    rw [sSup_empty] at h
    haveI : Group.IsSolvable ↥(⊥ : Subgroup G) :=
      Group.isSolvable_of_comm (fun a b => Subsingleton.elim _ _)
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (uc22p20b_simpSec_comm h a b)
  | @insert C₀ F' hC₀ hF' ih =>
    have hC₀L : C₀ ∈ CFSG.Quasithin.cComp L := hFL (Set.mem_insert _ _)
    have hF'L : F' ⊆ CFSG.Quasithin.cComp L := fun C hC => hFL (Set.mem_insert_of_mem _ hC)
    rw [sSup_insert] at h
    set P : Subgroup G := sSup F' with hP
    have hnorm : ∀ C ∈ CFSG.Quasithin.cComp L,
        CFSG.Quasithin.cCompSpan L ≤ normalizer (C : Set G) := fun C hC =>
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.Quasithin.cComp_normal_span_of_le hC).1).1
        (CFSG.Quasithin.cComp_normal_span_of_le hC).2
    have hC₀C : C₀ ≤ CFSG.Quasithin.cCompSpan L := CFSG.Quasithin.le_cCompSpan hC₀L
    have hPC : P ≤ CFSG.Quasithin.cCompSpan L :=
      sSup_le fun C hC => CFSG.Quasithin.le_cCompSpan (hF'L hC)
    have hPn : CFSG.Quasithin.cCompSpan L ≤ normalizer (P : Set G) := by
      rw [hP, sSup_eq_iSup']
      exact uc22p20b_le_normalizer_iSup _ _ fun C => hnorm C.1 (hF'L C.2)
    have hXP : P ≤ C₀ ⊔ P := le_sup_right
    have hNnorm : (P.subgroupOf (C₀ ⊔ P)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXP).2
        (sup_le (hC₀C.trans hPn) Subgroup.le_normalizer)
    haveI := hNnorm
    rcases uc22p20b_simpSec_restrict (P.subgroupOf (C₀ ⊔ P)) h with h1 | h2
    ·
      have h1' : uc22p20bSimpSec ↥P Λ :=
        uc22p20b_simpSec_of_surjective (Subgroup.subgroupOfEquivOfLe hXP).symm.toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hXP).symm.surjective h1
      obtain ⟨C, hC, hCΛ⟩ := ih hF'L h1'
      exact ⟨C, Set.mem_insert_of_mem _ hC, hCΛ⟩
    ·
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' (P.subgroupOf (C₀ ⊔ P))).comp
            (Subgroup.inclusion (le_sup_left : C₀ ≤ C₀ ⊔ P))) := by
        intro q
        obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf (C₀ ⊔ P)) q
        have hx' : x ∈ ((C₀ ⊔ P : Subgroup G) : Set G) := hx
        rw [Subgroup.coe_mul_of_left_le_normalizer_right C₀ P (hC₀C.trans hPn)] at hx'
        obtain ⟨c, hc, p, hp, rfl⟩ := hx'
        refine ⟨⟨c, hc⟩, ?_⟩
        simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using P.inv_mem hp
      have h2' := uc22p20b_simpSec_of_surjective _ hsurj h2
      obtain ⟨e⟩ := uc22p20b_simpSec_cComp hC₀L hnc h2'
      exact ⟨C₀, Set.mem_insert _ _, ⟨e⟩⟩

@[expose] def ListBNotSmall : Prop :=
  ∀ (L : Type) [Group L], Asc1930ListB L →
    (∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsL2Odd L p ∧ ¬ IsL3Odd L p) ∧ ¬ IsAlt L 6 ∧ ¬ IsAlt L 7

theorem uc22p20b_compFactorsOfCComp :
    ∀ (L B : Subgroup G), B ≤ normalizer (L : Set G) → Group.IsSolvable ↥B →
      sSup (CFSG.Quasithin.cComp L) = L →
      ∀ (Λ : Type) [Group Λ], CFSG.Quasithin.E1.IsCompositionFactor ↥(L ⊔ B) Λ →
        (∃ a b : Λ, a * b ≠ b * a) → ∃ C ∈ CFSG.Quasithin.cComp L, Nonempty (BarInf C ≃* Λ) := by
  intro L B hB hBs hsSup Λ _ hcf hnc
  have h := uc22p20b_simpSec_of_cf hcf
  have hLX : L ≤ L ⊔ B := le_sup_left
  have hNn : (L.subgroupOf (L ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 (sup_le Subgroup.le_normalizer hB)
  haveI := hNn
  rcases uc22p20b_simpSec_restrict (L.subgroupOf (L ⊔ B)) h with h1 | h2
  · have h1' : uc22p20bSimpSec ↥L Λ :=
      uc22p20b_simpSec_of_surjective (Subgroup.subgroupOfEquivOfLe hLX).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hLX).symm.surjective h1
    haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
    have h1'' : uc22p20bSimpSec ↥(sSup (CFSG.Quasithin.cComp L)) Λ := by
      rw [hsSup]; exact h1'
    exact uc22p20b_simpSec_sSup_cComp hnc (CFSG.Quasithin.cComp L) (Set.toFinite _) subset_rfl h1''
  · exfalso
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' (L.subgroupOf (L ⊔ B))).comp
          (Subgroup.inclusion (le_sup_right : B ≤ L ⊔ B))) := by
      intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (L ⊔ B)) q
      have hx' : x ∈ ((L ⊔ B : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L B hB] at hx'
      obtain ⟨l, hl, b, hb, rfl⟩ := hx'
      refine ⟨⟨b, hb⟩, ?_⟩
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using (Subgroup.mem_normalizer_iff''.1 (hB hb) l).1 hl
    haveI : Group.IsSolvable ↥B := hBs
    haveI : Group.IsSolvable (↥(L ⊔ B) ⧸ L.subgroupOf (L ⊔ B)) :=
      Group.isSolvable_of_surjective hsurj
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (uc22p20b_simpSec_comm h2 a b)

theorem uc22p20b_compInCalL (D : Data G) (h1930 : H1930 D) (h20_2 : S20_2 D)
    (hB : ListBNonabelian) (hS : ListBNotSmall) : CompInCalL D := by
  intro H hH K hK hKM
  have hTH : D.T ≤ H := hH.1
  have hKH : K ≤ H := CFSG.Quasithin.le_of_mem_cComp hK
  set L : Subgroup G := uc22p20bOrb D.T K with hLdef
  have hLH : L ≤ H := uc22p20b_orb_le hTH hKH
  have hsub : CFSG.Open.IsSubnormal L H := uc22p20b_orb_subnormal hK hTH
  have hKL : K ≤ L := uc22p20b_le_orb D.T K
  have hperfK : ⁅K, K⁆ = K := CFSG.Quasithin.perfect_of_mem_cComp hK
  have hperfL : ⁅L, L⁆ = L := uc22p20b_orb_perfect hperfK
  have hYH : L ⊔ D.T ≤ H := sup_le hLH hTH
  have hYnot : ¬ L ⊔ D.T ≤ D.M := fun h => hKM (hKL.trans (le_sup_left.trans h))
  have hY : L ⊔ D.T ∈ hSet D.T D.M := uc22p20b_mem_hSet D hH le_sup_right hYH hYnot
  have hLn : (L.subgroupOf (L ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer (uc22p20b_le_normalizer_orb D.T K))
  have hoE : CFSG.Quasithin.oInftyE ↥L = ⊤ := uc22p20b_oInftyE_orb hK hTH
  have h2 := h20_2 h1930 (L ⊔ D.T) hY L le_sup_left hLn hperfL hoE
    (uc22p20b_conjTransitive_orb hK hTH)
  have hTsolv : Group.IsSolvable ↥D.T := by
    haveI : Group.IsNilpotent ↥D.T := D.sylowM.isPGroup.isNilpotent
    infer_instance
  have hOTwo : OTwoE ↥L = ⊤ := by
    rcases h2 with h | hbad
    · exact h
    · exfalso
      obtain ⟨Λ, _, hΛ, hΛB⟩ := (h1930 _ hY).1
      obtain ⟨a, b, hab⟩ := hB Λ hΛB
      obtain ⟨C, hC, ⟨e⟩⟩ := uc22p20b_compFactorsOfCComp L D.T (uc22p20b_le_normalizer_orb D.T K) hTsolv
        (uc22p20b_sSup_cComp_orb hK hTH) Λ hΛ ⟨a, b, hab⟩
      obtain ⟨hl, h6, h7⟩ := hS Λ hΛB
      rcases hbad with ⟨⟨p, hp, hp2, hCp⟩ | hAlt, -⟩
      · rcases hCp C hC with h | h
        · exact (hl p hp hp2).1 (CFSG.Blueprint.LieModel.of_mulEquiv e h)
        · exact (hl p hp hp2).2 (CFSG.Blueprint.LieModel.of_mulEquiv e h)
      · rcases hAlt C hC with h | h
        · exact h6 ⟨e.symm.trans h.some⟩
        · exact h7 ⟨e.symm.trans h.some⟩
  have hKc : K ∈ CFSG.Quasithin.cComp L := by
    rw [hLdef, uc22p20b_cComp_orb hK hTH]
    exact ⟨⟨1, D.T.one_mem⟩, by simp [uc22p20b_cj_one]⟩
  have hquasi : CFSG.Open.IsQuasisimple (Bar2 K) := uc22p20b_isQuasisimple_bar2 hOTwo hKc
  refine ⟨L, ⟨⟨uc22p20b_le_normalizer_orb D.T K, hperfL, hY, K,
    ⟨CFSG.Quasithin.A3.subnormal_of_le_of_le (CFSG.Quasithin.subnormal_of_mem_cComp hK) hKL hLH,
      hperfK, hquasi⟩, rfl⟩, hsub⟩, hKL⟩

theorem s20_4_of (D : Data G) (h20_1 : S20_1_124 D) (h20_2 : S20_2 D) (h20_3 : S20_3 D)
    (hB : ListBNonabelian) (hS : ListBNotSmall) : S20_4 D :=
  fun h1930 => uc22p20b_s20_4_of_comp D hB h20_1 h20_3
    (uc22p20b_compInCalL D h1930 h20_2 hB hS) h1930

end CFSG.LocalAnalysis.UniquenessCase.UC22
