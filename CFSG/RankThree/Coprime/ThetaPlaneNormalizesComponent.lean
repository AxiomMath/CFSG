module

public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
public import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThreeEvenClassification.Helpers
open scoped commutatorElement

section Components

variable {G : Type*} [Group G]

theorem mem_map_center_iff {L : Subgroup G} {x : G} :
    x ∈ (center L).map L.subtype ↔ x ∈ L ∧ ∀ l ∈ L, l * x = x * l := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun l hl => ?_⟩
    have := (mem_center_iff.mp hy) ⟨l, hl⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxL, hx⟩
    refine ⟨⟨x, hxL⟩, mem_center_iff.mpr fun l => Subtype.ext (hx l l.2), rfl⟩

theorem mem_normalizer_of_mem_component [Finite G] {L K : Subgroup G} (hL : IsComponent L)
    (hK : IsComponent K) {x : G} (hx : x ∈ L) : x ∈ normalizer (K : Set G) := by
  rcases CFSG.LocalCores.distinct_components_commute hL hK with rfl | h
  · exact le_normalizer hx
  · exact centralizer_le_normalizer _ (commutator_eq_bot_iff_le_centralizer.mp h hx)

theorem commutator_mem_normalizer_of_mem_component [Finite G] {L : Subgroup G}
    (hL : IsComponent L) {x : G} (hx : x ∈ L) (d : G) : ⁅d, x⁆ ∈ normalizer (L : Set G) := by
  have hK := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj d⁻¹) hL
  have hxK := mem_normalizer_of_mem_component hL hK hx
  have hconj : d * x * d⁻¹ ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff] at hxK ⊢
    intro h
    have hmem : ∀ y : G, y ∈ L.map (MulAut.conj d⁻¹).toMonoidHom ↔ d * y * d⁻¹ ∈ L := by
      intro y
      rw [mem_map_equiv]
      simp
    have h1 := hxK (d⁻¹ * h * d)
    rw [hmem, hmem] at h1
    have e1 : d * (d⁻¹ * h * d) * d⁻¹ = h := by group
    have e2 : d * (x * (d⁻¹ * h * d) * x⁻¹) * d⁻¹ = d * x * d⁻¹ * h * (d * x * d⁻¹)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  rw [commutatorElement_def]
  exact mul_mem hconj (inv_mem (le_normalizer hx))

theorem mem_normalizer_of_le_centralizer [Finite G] {L P : Subgroup G} (hL : IsComponent L)
    (hPL : P ≤ L) (hPZ : ¬ P ≤ (center L).map L.subtype) {d : G}
    (hd : d ∈ centralizer (P : Set G)) : d ∈ normalizer (L : Set G) := by
  by_contra hdL
  have hK := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj d) hL
  have hne : L ≠ L.map (MulAut.conj d).toMonoidHom := by
    intro h
    apply hdL
    rw [mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    exact h.symm
  have hcomm := (CFSG.LocalCores.distinct_components_commute hL hK).resolve_left hne
  apply hPZ
  intro x hx
  rw [mem_map_center_iff]
  refine ⟨hPL hx, fun l hl => ?_⟩
  have hxK : x ∈ L.map (MulAut.conj d).toMonoidHom := by
    refine ⟨x, hPL hx, ?_⟩
    have hdx : x * d = d * x := (mem_centralizer_iff.mp hd) x hx
    change d * x * d⁻¹ = x
    rw [← hdx, mul_inv_cancel_right]
  have hKc : L.map (MulAut.conj d).toMonoidHom ≤ centralizer (L : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  exact (mem_centralizer_iff.mp (hKc hxK)) l hl

end Components

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_normalized {p : ℕ} [Fact p.Prime] (L B : Subgroup G) (hBp : IsPGroup p B)
    (hBL : B ≤ normalizer (L : Set G)) :
    ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup p Q ∧ (∀ n : ℕ, p ^ n ∣ Nat.card L → p ^ n ∣ Nat.card Q) ∧
      B ≤ normalizer (Q : Set G) ∧
      ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal → IsPGroup p N → N ≤ Q := by
  classical
  let φ : B →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBL)
  let _ : MulDistribMulAction B L := MulDistribMulAction.compHom L φ
  let _ : MulAction B (Sylow p L) := Sylow.pointwiseMulAction
  have hcard : ¬ p ∣ Nat.card (Sylow p L) := by
    intro h
    have h1 := card_sylow_modEq_one p L
    have h2 : Nat.card (Sylow p L) % p = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.ModEq, h2, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at h1
    exact zero_ne_one h1
  obtain ⟨Q₀, hQ₀⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p L) hcard
  refine ⟨(Q₀ : Subgroup L).map L.subtype, map_subtype_le _, Q₀.isPGroup'.map _,
    fun n hn => ?_, ?_, fun N hNL hN hNp => ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L)]
    exact Q₀.pow_dvd_card_of_pow_dvd_card hn
  · rw [le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : B) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : B) • y ∈ (Q₀ : Subgroup L) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : B) (Q₀ : Subgroup L) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((L.normalizerMonoidHom) (Subgroup.inclusion hBL ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  · have hNp' : IsPGroup p (N.subgroupOf L) := hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNL).symm
    have hle := hNp'.le_sylow_of_normal Q₀
    have h := Subgroup.map_mono (f := L.subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNL] at h

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_subgroupOf {T W : Subgroup G} (hWT : W ≤ T) {n : T}
    (hn : n ∈ normalizer (W.subgroupOf T : Set T)) : (n : G) ∈ normalizer (W : Set G) := by
  rw [mem_normalizer_iff] at hn ⊢
  intro h
  by_cases hh : h ∈ T
  · have := hn ⟨h, hh⟩
    simpa [mem_subgroupOf] using this
  · have h1 : h ∉ W := fun h' => hh (hWT h')
    have h2 : (n : G) * h * (n : G)⁻¹ ∉ W := by
      intro h'
      apply hh
      have := T.mul_mem (T.mul_mem (T.inv_mem n.2) (hWT h')) n.2
      simpa [mul_assoc] using this
    exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩

theorem exists_pgroup_le_normalizer {p : ℕ} [Fact p.Prime] {L Q B Z : Subgroup G}
    (hQL : Q ≤ L) (hQp : IsPGroup p Q) (hBp : IsPGroup p B) (hBQ : B ≤ normalizer (Q : Set G))
    (hZQ : Z ≤ Q) (hQZ : ¬ Q ≤ Z) :
    ∃ P : Subgroup G, P ≤ L ∧ IsPGroup p P ∧ P ≤ normalizer ((Z ⊔ B : Subgroup G) : Set G) ∧
      ¬ P ≤ Z := by
  set W := Z ⊔ B with hW
  set T := Q ⊔ B with hT
  have hTp : IsPGroup p T := IsPGroup.to_sup_of_normal_left' hQp hBp hBQ
  have hWT : W ≤ T := sup_le_sup_right hZQ B
  rcases eq_or_lt_of_le hWT with hWeq | hWlt
  · refine ⟨Q, hQL, hQp, ?_, hQZ⟩
    rw [hWeq]
    exact le_sup_left.trans le_normalizer
  · have : Group.IsNilpotent T := hTp.isNilpotent
    have hlt : W.subgroupOf T < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply hWlt.ne
      apply le_antisymm hWT
      intro x hx
      have : (⟨x, hx⟩ : T) ∈ W.subgroupOf T := h ▸ mem_top _
      exact this
    obtain ⟨n, hnN, hnW⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hnG := mem_normalizer_of_mem_normalizer_subgroupOf hWT hnN
    have hnW' : (n : G) ∉ W := fun h => hnW (mem_subgroupOf.mpr h)
    obtain ⟨q, hq, b, hb, hqb⟩ := normalized_sup_factorization Q B hBQ (n : G) n.2
    have hbW : b ∈ W := mem_sup_right hb
    have hqN : q ∈ normalizer (W : Set G) := by
      have : q = (n : G) * b⁻¹ := by rw [← hqb, mul_inv_cancel_right]
      rw [this]
      exact mul_mem hnG (inv_mem (le_normalizer hbW))
    have hqZ : q ∉ Z := by
      intro h
      apply hnW'
      rw [← hqb]
      exact mul_mem (mem_sup_left h) hbW
    refine ⟨zpowers q, zpowers_le.mpr (hQL hq), hQp.to_le (zpowers_le.mpr hq),
      zpowers_le.mpr hqN, fun h => hqZ (h (mem_zpowers q))⟩

end Sylow

theorem theta_plane_intersection_normalizes_prime_component {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {L : Subgroup G} (hL : IsComponent L)
    (hZ : (center L).map L.subtype ≤ pCore p G) (hpL : p ∣ Nat.card (L ⧸ center L))
    {B : Subgroup G} (hBL : B ≤ normalizer (L : Set G)) (_hB : IsElementaryAbelian p B)
    (hBcard : Nat.card B = p ^ 2) : thetaT p B ≤ normalizer (L : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup G := (center L).map L.subtype with hZdef
  set I := thetaT p B with hIdef
  have hBp : IsPGroup p B := IsPGroup.of_card hBcard
  obtain ⟨hIsolv, hIp, hIB, hInormal, -, -, -, -, -⟩ :=
    theta_plane_alpha_product_equivariance hp B hBcard
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hBcard
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hcentb : centralizer ((zpowers b : Subgroup G) : Set G) = centralizer ({b} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hIOp : ⁅I, pCore p G⁆ = ⊥ := by
    have hle : I ≤ inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set G)) :=
      iInf_le_of_le b (iInf_le_of_le hb (iInf_le_of_le hb1' le_rfl))
    have hR := local_prime_complement_centralizes_normal_prime_group hp (P := pCore p G)
      (A := zpowers b) (S := inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set G)))
      (hP := pCore_isPGroup) (hBp.to_le (zpowers_le.mpr hb))
      (by rw [hcentb]; exact map_subtype_le _)
      (by
        rw [hcentb, inSubgroup, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]
        infer_instance)
      (by
        rw [inSubgroup, card_map_of_injective (subtype_injective _)]
        exact (solvable_prime_complement_core_characterization
          (H := centralizer ({b} : Set G)) hp).2.2.1)
    exact le_bot_iff.mp (hR ▸ commutator_mono hle le_rfl)
  have hIZ : I ≤ centralizer (Z : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hIOp).trans (centralizer_le hZ)
  set W := Z ⊔ B with hWdef
  have hZL : Z ≤ L := map_subtype_le _
  have hBZ : B ≤ normalizer (Z : Set G) := by
    rw [le_normalizer_iff]
    intro g hg z hz
    rw [mem_map_center_iff] at hz ⊢
    refine ⟨le_normalizer_iff.mp hBL g hg z hz.1, fun l hl => ?_⟩
    have hl' : g⁻¹ * l * g ∈ L := by
      have := le_normalizer_iff.mp hBL g⁻¹ (inv_mem hg) l hl
      simpa using this
    have h := hz.2 _ hl'
    calc l * (g * z * g⁻¹) = g * (g⁻¹ * l * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * l * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * l := by group
  have hZp : IsPGroup p Z := (pCore_isPGroup (p := p) (G := G)).to_le hZ
  have hWp : IsPGroup p W := IsPGroup.to_sup_of_normal_left' hZp hBp hBZ
  have hIW : I ≤ centralizer (W : Set G) := by
    rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.mp hIZ) (le_centralizer_iff.mp hIB)
  have hCBI : centralizer (B : Set G) ≤ normalizer (I : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hIB).mp hInormal
  have hInW : (I.subgroupOf (centralizer (W : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hIW).mpr
      ((centralizer_le (le_sup_right : B ≤ W)).trans hCBI)
  have hI1 : I ≤ thetaCoreOf p (centralizer (W : Set G)) :=
    normal_solvable_primeComplement_le_thetaCoreOf p I _ hIW hInW hIsolv hIp
  have hCWnormal : ((centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mpr
      (normalizes_centralizer_of_normalizes _ W le_rfl)
  have hI2 := thetaCoreOf_mono_of_normal p hp _ _ (centralizer_le_normalizer _) hCWnormal
  set D := thetaCoreOf p (normalizer (W : Set G)) with hDdef
  have hID : I ≤ D := hI1.trans hI2
  have hDnormal : normalizer (W : Set G) ≤ normalizer (D : Set G) := by
    have h : (D.subgroupOf (normalizer (W : Set G))).Normal := by
      have heq : D.subgroupOf (normalizer (W : Set G)) =
          solvablePrimeComplementCore (normalizer (W : Set G)) p :=
        comap_map_eq_self_of_injective (subtype_injective _) _
      rw [heq]
      exact (solvablePrimeComplementCore_properties _ p hp).1
    exact (normal_subgroupOf_iff_le_normalizer (thetaCoreOf_le p _)).mp h
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp hZp
  have hpc : p ^ (c + 1) ∣ Nat.card L := by
    rw [card_eq_card_quotient_mul_card_subgroup (center L), pow_succ, mul_comm]
    have hcard : Nat.card (center L) = p ^ c := by
      rw [← hc, hZdef, card_map_of_injective (subtype_injective _)]
    rw [hcard]
    exact mul_dvd_mul_right hpL _
  obtain ⟨Q, hQL, hQp, hQcard, hBQ, hQnormal⟩ := exists_sylow_normalized L B hBp hBL
  have hZQ : Z ≤ Q := hQnormal Z hZL (by
    rw [hZdef, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]
    infer_instance) hZp
  have hQZ : ¬ Q ≤ Z := by
    intro h
    have heq := le_antisymm h hZQ
    have h1 := hQcard _ hpc
    rw [heq, hc] at h1
    have h2 := Nat.le_of_dvd (pow_pos hp.pos c) h1
    have h3 : p ^ c < p ^ (c + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self c)
    omega
  obtain ⟨P, hPL, hPp, hPW, hPZ⟩ := exists_pgroup_le_normalizer hQL hQp hBp hBQ hZQ hQZ
  have hfac := coprime_commutator_centralizer_factorization p hp P D hPp
    (thetaCoreOf_prime_complement p hp _) (hPW.trans hDnormal)
  refine hID.trans ?_
  rw [hfac]
  refine sup_le ?_ ?_
  · refine commutator_le.mpr fun d _ x hx => ?_
    exact commutator_mem_normalizer_of_mem_component hL (hPL hx) d
  · exact fun d hd => mem_normalizer_of_le_centralizer hL hPL hPZ hd.2

end CFSG.RankThree.Coprime
