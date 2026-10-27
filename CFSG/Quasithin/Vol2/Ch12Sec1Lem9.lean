module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem5
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise

@[expose] def Lem1219Cartan : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
      ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H → 2 < E1.nParam H →
        ∃ (p : ℕ) (X : Subgroup G), p.Prime ∧ 3 < p ∧ IsPGroup p ↥X ∧ X ≠ ⊥ ∧
          X ≤ H ⊓ Subgroup.normalizer (L : Set G) ∧
          (X : Set G) * (T : Set G) = (T : Set G) * (X : Set G) ∧
          ¬ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lem1219Perm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
      ∀ (p : ℕ) (X : Subgroup G), p.Prime → 3 < p → IsPGroup p ↥X →
        X ≤ Subgroup.normalizer (L : Set G) →
        (X : Set G) * (T : Set G) = (T : Set G) * (X : Set G) →
          X ≤ Subgroup.centralizer (V : Set G)

@[expose] def Lem1219OddLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
      ∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
        ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) →
          ∃ X : Subgroup G,
            X ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ∧ X ≠ ⊥ ∧
              Odd (Nat.card X) ∧ ¬ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lem1219Geom : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2),
    Hyp121 G T L V V₁ V₂ n → IsDualPairing121 L V₁ V₂ β →
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (L : Set G) → Odd (Nat.card X) →
        ¬ X ≤ Subgroup.centralizer (V : Set G) →
        ∀ U : Subgroup G, U ≤ V → X ≤ Subgroup.centralizer (U : Set G) →
          (∀ u ∈ U, IsSingular121 V₁ V₂ β u) → n + 2 ≤ mQuot V U

namespace Sec1219

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

omit [Finite G] in
theorem exists_abelian_of_solvable {X : Subgroup G} (hX : X ≠ ⊥) (hs : Group.IsSolvable ↥X) :
    ∃ B : Subgroup G, B ≤ X ∧ B ≠ ⊥ ∧ IsMulCommutative ↥B ∧
      Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (B : Set G) := by
  classical
  set D : ℕ → Subgroup G := fun i => (derivedSeries ↥X i).map X.subtype with hD
  have hD0 : D 0 = X := by
    simp only [hD, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hDs : ∀ i, D (i + 1) = ⁅D i, D i⁆ := fun i => by
    simp only [hD, derivedSeries_succ, Subgroup.map_commutator]
  have hN : ∀ i, Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (D i : Set G) := by
    intro i
    induction i with
    | zero => rw [hD0]
    | succ i ih =>
      intro g hg
      rw [hDs]
      exact mem_normalizer_commutator (ih hg) (ih hg)
  obtain ⟨k, hk⟩ := hs.solvable
  have hex : ∃ i, D i = ⊥ := ⟨k, by simp only [hD, hk, Subgroup.map_bot]⟩
  have hk₀ : D (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hk₀0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, hD0] at hk₀
    exact hX hk₀
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hDj : D j ≠ ⊥ := Nat.find_min hex (by omega)
  have hc : ⁅D j, D j⁆ = ⊥ := by
    rw [← hDs, ← hj]
    exact hk₀
  refine ⟨D j, Subgroup.map_subtype_le _, hDj, ⟨⟨fun a b => Subtype.ext ?_⟩⟩, hN j⟩
  have h1 := Subgroup.commutator_mem_commutator a.2 b.2
  rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem psl_two_card_ne_20160 (k : ℕ) : 2 ^ k * (4 ^ k - 1) ≠ 20160 := by
  intro h
  by_cases hk : 9 ≤ k
  · have h1 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h2 : 4 ^ 9 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h3 : 2 ^ 9 * (4 ^ 9 - 1) ≤ 2 ^ k * (4 ^ k - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
    omega
  · interval_cases k <;> omega

theorem card_of_hyp121 {T L V V₁ V₂ : Subgroup G} {n : ℕ} (hyp : Hyp121 G T L V V₁ V₂ n) :
    (n = 4 ∧ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 20160) ∨
      (n = 5 ∧ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 9999360) := by
  obtain ⟨e⟩ := hyp.iso
  rw [Nat.card_congr e.toEquiv]
  rcases hyp.rank with rfl | rfl
  · exact Or.inl ⟨rfl, by rw [card_sl_zmod_two]; decide⟩
  · exact Or.inr ⟨rfl, by rw [card_sl_zmod_two]; decide⟩

theorem lieModel_four_of_hyp121 {T L V V₁ V₂ : Subgroup G} (hyp : Hyp121 G T L V V₁ V₂ 4) :
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 := by
  obtain ⟨e⟩ := hyp.iso
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
    inferInstance, inferInstance, by simp, ⟨e.trans ?_⟩⟩
  exact (QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 4 (ZMod 2) (by simp)).symm

variable {T L V V₁ V₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem card_extSq_sec {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(FFModel.extSq K 4).sec = 2 ^ 6 := by
  refine (Nat.card_congr (Subgroup.topEquiv (G := (FFModel.extSq K 4).Amb)).toEquiv).trans ?_
  refine (Nat.card_congr (Multiplicative.toAdd (α := ⋀[K]^2 (Fin 4 → K)))).trans ?_
  rw [Module.natCard_eq_pow_finrank (K := K), exteriorPower.finrank_eq, Module.finrank_fin_fun, hK]
  rfl

open CFSG.Quasithin.H in
theorem notSum121_holds :
    ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
      Hyp121 G T L V V₁ V₂ n → n = 4 →
        ¬ IsNaturalSumUnder 4 L V ∧
          ¬ ∃ _ : IsMulCommutative ↥V, SLExteriorTwo (V := ↥V) (autOn L V) ⊤ ⊥ 4 := by
  intro G _ _ T L V V₁ V₂ n hyp hn
  subst hn
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hcV : IsMulCommutative ↥V := hVe.1
  have hcard := (Sec1212.card_eq_of_hyp121 hyp).2.2
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hLV : L ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer.trans (Sec121Q.normalizer_le_of_hyp121 hyp)
  refine ⟨?_, ?_⟩
  · rintro ⟨k, W, hk, hW, hiso, hind, hsup⟩
    set Λ := autOn L V with hΛ
    have hinf' : V₁.subgroupOf V ⊓ V₂.subgroupOf V = ⊥ := InternalSec.inf_subgroupOf_eq_bot hyp.inf
    have hsup' : V₁.subgroupOf V ⊔ V₂.subgroupOf V = ⊤ :=
      InternalSec.sup_subgroupOf_eq_top hV₁V hV₂V hyp.sup
    have hne : ∀ {X : Subgroup G}, X ≤ V → X ≠ ⊥ → X.subgroupOf V ≠ ⊥ := fun hX hX0 h =>
      hX0 (by
        have h1 := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
        rwa [inf_eq_left.mpr hX] at h1)
    have hirr : ∀ {X : Subgroup G}, X ≤ V → L ≤ Subgroup.normalizer (X : Set G) →
        (∃ _ : IsMulCommutative ↥X, BinaryNaturalSL (V := ↥X) (autOn L X) ⊤ ⊥ 4 1) →
          Pair.IsIrr Λ (X.subgroupOf V) := by
      intro X hXV hLX ⟨hcX, hnatX⟩
      exact ⟨hne hXV (Sec121Q.ne_bot_of_natural (by norm_num) hnatX), fun U hU hUi =>
        InternalSec.irr_subgroupOf hLV
          (fun J hJ hLJ => Sec121Q.eq_bot_or_eq_of_natural hLX hnatX J hJ hLJ) U hU hUi⟩
    have hniso : ¬ Pair.IsoMod Λ (V₁.subgroupOf V) (V₂.subgroupOf V) := fun h =>
      hyp.dual (Sec121.isXSectionIso₂_of_isoMod hV₁V hV₂V hLV h)
    have hWV : ∀ i, W i = V₁ ∨ W i = V₂ := by
      intro i
      obtain ⟨hWiV, hLWi, hnatWi⟩ := hW i
      rcases Pair.eq_or_eq_of_isIrr hinf' hsup' (InternalSec.autOn_inv_subgroupOf hyp.norm₁)
          (InternalSec.autOn_inv_subgroupOf hyp.norm₂) (hirr hV₁V hyp.norm₁ hyp.nat₁)
          (hirr hV₂V hyp.norm₂ hyp.nat₂) hniso (InternalSec.autOn_inv_subgroupOf hLWi)
          (hirr hWiV hLWi hnatWi) with h | h
      · left
        rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hWiV, inf_eq_left.mpr hV₁V] at h
        exact h
      · right
        rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hWiV, inf_eq_left.mpr hV₂V] at h
        exact h
    obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
    obtain ⟨hc₂, hnat₂⟩ := hyp.nat₂
    have hV₁0 : V₁ ≠ ⊥ := Sec121Q.ne_bot_of_natural (by norm_num) hnat₁
    have hV₂0 : V₂ ≠ ⊥ := Sec121Q.ne_bot_of_natural (by norm_num) hnat₂
    by_cases hk2 : 2 ≤ k
    · set i₀ : Fin k := ⟨0, by omega⟩
      set i₁ : Fin k := ⟨1, by omega⟩
      have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
      have hdisj : W i₀ ⊓ W i₁ = ⊥ := disjoint_iff.mp (hind.pairwiseDisjoint hi)
      rcases hWV i₀ with h0 | h0 <;> rcases hWV i₁ with h1 | h1
      · rw [h0, h1, inf_idem] at hdisj
        exact hV₁0 hdisj
      · exact hyp.dual (h0 ▸ h1 ▸ hiso i₀ i₁)
      · exact hyp.dual (h1 ▸ h0 ▸ hiso i₁ i₀)
      · rw [h0, h1, inf_idem] at hdisj
        exact hV₂0 hdisj
    ·
      have hk1 : k = 1 := by omega
      subst hk1
      have hW0 : W 0 = V := by
        rw [← hsup]
        exact le_antisymm (le_iSup W 0) (iSup_le fun i => by rw [Subsingleton.elim i 0])
      rcases hWV 0 with h0 | h0
      · apply hV₂0
        rw [eq_bot_iff, ← hyp.inf]
        exact le_inf (h0 ▸ hW0 ▸ hV₂V) le_rfl
      · apply hV₁0
        rw [eq_bot_iff, ← hyp.inf]
        exact le_inf le_rfl (h0 ▸ hW0 ▸ hV₁V)
  · rintro ⟨hc, π, hπ⟩
    obtain ⟨E, -⟩ := G64.RealizesVia.exists_secEquiv (D := FFModel.extSq (ZMod 2) 4) rfl hπ
    have h6 : Nat.card ↥V = 2 ^ 6 := by
      rw [Nat.card_congr E.toEquiv]
      exact card_extSq_sec (by simp)
    rw [hcard] at h6
    norm_num at h6

theorem eq_commutator_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) : V = ⁅V, L⁆ := by
  have hn2 : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
  have hMV := Sec121Q.normalizer_le_of_hyp121 hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hMV
  have key : ∀ X : Subgroup G, L ≤ Subgroup.normalizer (X : Set G) →
      (∃ _ : IsMulCommutative ↥X, BinaryNaturalSL (V := ↥X) (autOn L X) ⊤ ⊥ n 1) →
        X = ⁅X, L⁆ := by
    intro X hLX ⟨hc, hnat⟩
    have hle : ⁅X, L⁆ ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.1 hLX
    have hN : L ≤ Subgroup.normalizer ((⁅X, L⁆ : Subgroup G) : Set G) := fun l hl =>
      mem_normalizer_commutator (hLX hl) (Subgroup.le_normalizer hl)
    rcases Sec121Q.eq_bot_or_eq_of_natural hLX hnat _ hle hN with h0 | h1
    · exfalso
      apply Sec121Q.ne_bot_of_binaryNaturalSL hnat hn2
      have hLC : L ≤ Subgroup.centralizer (X : Set G) :=
        Subgroup.le_centralizer_iff.1 ((Subgroup.commutator_eq_bot_iff_le_centralizer).1 h0)
      refine eq_bot_iff.mpr fun a ha => ?_
      obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLX).mp ha
      rw [Subgroup.mem_bot]
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [A4.actionOn_apply_coe, MulAut.one_apply]
      have := Subgroup.mem_centralizer_iff.mp (hLC hl) w w.2
      rw [← this, mul_inv_cancel_right]
    · exact h1.symm
  refine le_antisymm ?_ (Subgroup.le_normalizer_iff_commutator_le_left.1 hLV)
  rw [← hyp.sup]
  have h1 := key V₁ hyp.norm₁ hyp.nat₁
  have h2 := key V₂ hyp.norm₂ hyp.nat₂
  refine sup_le ?_ ?_
  · exact h1.le.trans (Subgroup.commutator_mono le_sup_left le_rfl)
  · exact h2.le.trans (Subgroup.commutator_mono le_sup_right le_rfl)

theorem lem1219_one_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h443 : Stmt4_4_3Orbit')
    (hyp : Hyp121 G T L V V₁ V₂ n) (X : Subgroup G)
    (hXM : X ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G))
    (hX1 : X ≠ ⊥) (hXo : Odd (Nat.card X)) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, -⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have hqs := Sec121Thm.isQuasisimple_of_hyp121 hyp
  have hLT : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun t ht l hl => (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl)
      (le_conjClosure L T)
  obtain ⟨⟨hMmax, -, -⟩, -⟩ :=
    (h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).2 L hyp.maximal hqs
  rw [hLT] at hMmax
  obtain ⟨B, hBX, hB1, hBc, hNB⟩ :=
    exists_abelian_of_solvable hX1 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hXo)
  have hBo : Odd (Nat.card B) := Odd.of_dvd_nat hXo (Subgroup.card_dvd_of_le hBX)
  have hBM : B ≤ Subgroup.normalizer (L : Set G) := hBX.trans (hXM.trans inf_le_left)
  have hBV : B ≤ Subgroup.centralizer (V : Set G) := hBX.trans (hXM.trans inf_le_right)
  have hMV := Sec121Q.normalizer_le_of_hyp121 hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hMV
  have hVT := Sec1215.le_of_hyp121 hyp hTL
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  have hVn : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV (hTL.trans hMV)
  have hQ := setup121Q_holds G T L V V₁ V₂ n hyp hTL
  have hVQ : V ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right) hVn hV2
  have hVZ : V ≤ quasithinOmegaOneCenter (pCoreOf 2 (L ⊔ T)) := by
    intro v hv
    refine Subgroup.subset_closure ⟨⟨hVQ hv, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩,
      hVe.2 v hv⟩
    rw [hQ] at hr
    exact (Subgroup.mem_centralizer_iff.mp hr.2 v hv).symm
  have hLB : ⁅L, B⁆ ≤ L ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1 hBM) ?_
    rw [Subgroup.commutator_le]
    intro l hl b hb
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : l⁻¹ * v * l ∈ V := (Subgroup.mem_normalizer_iff''.1 (hLV hl) v).1 hv
    have hbv : (l⁻¹ * v * l) * b = b * (l⁻¹ * v * l) :=
      Subgroup.mem_centralizer_iff.1 (hBV hb) _ hv'
    have hbv' : v * b⁻¹ = b⁻¹ * v := Subgroup.mem_centralizer_iff.1 (hBV (B.inv_mem hb)) v hv
    rw [commutatorElement_def]
    calc v * (l * b * l⁻¹ * b⁻¹) = l * ((l⁻¹ * v * l) * b) * l⁻¹ * b⁻¹ := by group
      _ = l * (b * (l⁻¹ * v * l)) * l⁻¹ * b⁻¹ := by rw [hbv]
      _ = l * b * l⁻¹ * (v * b⁻¹) := by group
      _ = l * b * l⁻¹ * (b⁻¹ * v) := by rw [hbv']
      _ = l * b * l⁻¹ * b⁻¹ * v := by group
  have hCL : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
    obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
    have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
    exact (inf_le_inf_left L (Subgroup.centralizer_le hV₁V)).trans
      (Sec121Q.inf_centralizer_le_pCoreOf_of_hyp121 hyp hV₁V hyp.norm₁ hnat₁)
  have hBT : (B : Set G) * ((⊥ : Subgroup G) : Set G) =
      ((⊥ : Subgroup G) : Set G) * (B : Set G) := by
    rw [Subgroup.coe_bot, Set.mul_singleton, Set.singleton_mul]
    simp
  have horb : ∀ t ∈ T, ∃ s ∈ (⊥ : Subgroup G), CFSG.conjugate L t = CFSG.conjugate L s :=
    fun t ht => ⟨1, Subgroup.one_mem _, by
      rw [conjugate_eq_self_of_normalizes (hTL ht), conjugate_eq_self_of_mem L.one_mem]⟩
  rcases h443 G T (Subgroup.normalizer (L : Set G)) L B ⊥ V hyp.simple hyp.nonabelian hyp.qtke
      hyp.sylow hMmax hTL hyp.maximal hyp.faithful Subgroup.le_normalizer hqs hBM hB1 hBc hBo
      (by rw [hLT]; exact hLB.trans hCL) bot_le hBT horb (by rw [hLT]; exact hVZ)
      (by rw [hLT]; exact hVn) (by rw [hLT]; exact eq_commutator_of_hyp121 hyp)
      (Sec121Thm.ne_bot_of_hyp121 hyp)
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).2 (Subgroup.le_centralizer_iff.1 hBV)) with
    hN | ⟨-, hlist, hcases⟩
  · exact hNB.trans hN
  · exfalso
    rcases card_of_hyp121 hyp with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · rcases hcases with ⟨-, -, h4, -, -⟩ | ⟨m, -, hm, -⟩ | ⟨h3, -⟩
      · rcases h4 (lieModel_four_of_hyp121 hyp) with hs | hs
        · exact (notSum121_holds G T L V V₁ V₂ 4 hyp rfl).1 hs
        · exact (notSum121_holds G T L V V₁ V₂ 4 hyp rfl).2 hs
      · rw [Lem11.card_of_lieModel_psl_two hm] at hc
        exact psl_two_card_ne_20160 _ hc
      · obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_of_lieModel h3
        rw [Nat.card_congr e.toEquiv, card_sl_zmod_two] at hc
        exact absurd hc (by decide)
    · rcases Lem11.card_of_list443 hlist with ⟨k, hk⟩ | hk | hk | hk | hk | hk | hk
      · rw [hc] at hk
        exact Lem11.psl_two_card_ne 9999360 (Or.inl rfl) hk.symm
      all_goals omega

theorem two_le_nParam_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1211 : Lem1211)
    (hH91 : LemH91) (h1217 : Lem1217) (h1218 : Lem1218) (hyp : Hyp121 G T L V V₁ V₂ n)
    (H : Subgroup G) (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    2 ≤ E1.nParam H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hNV⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have hT := hyp.sylow
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hVT := Sec1215.le_of_hyp121 hyp hTL
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hTL.trans hNV.ge
  have h322 : HypE322 T V :=
    ⟨⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩, hVT, hTV⟩
  have huniqQ := Sec1215.isUniqueM_of_hyp121 h331 hyp hTL
  obtain ⟨β, hβ, -⟩ := (hH91 G T L V V₁ V₂ n hyp hTL).2
  have hs : sParam hVe = 2 :=
    ((lem1212_of h1001 h331 h1211) G T L V V₁ V₂ n β hyp hβ).2 hVe |>.2.1
  have hw : (2 : ℕ∞) ≤ wParam T V := by
    refine le_wParam_of_wClos_le fun j hj => ?_
    interval_cases j
    · exact h1217 G T L V V₁ V₂ n hyp
    · exact h1218 G T L V V₁ V₂ n hyp
  have hS : IsSylowIn 2 T H :=
    ⟨hH.1.1, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hH.1.1))⟩
  have hrk : 2 ≤ rk ↥V := hs ▸ sParam_le_rk hVe
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj⟩ : ∃ j : ℕ, E1.nParam H = j :=
    ⟨(E1.nParam H).toNat, (ENat.natCast_toNat (ne_top_of_lt hlt)).symm⟩
  have hj2 : j < 2 := by
    rw [hj] at hlt
    exact_mod_cast hlt
  have hgen := e3_19 hVe hS (i := 0) hj (by omega)
  have hW := (e3_34_two hVe h322 huniqQ (i := 0) (by omega)
    (lt_of_lt_of_le (by norm_num) hw)).1
  have hC := (e3_34_two hVe h322 huniqQ (i := j) (by omega)
    (lt_of_lt_of_le (by exact_mod_cast hj2) hw)).2
  apply hH.2.1
  rw [← hgen, zero_add]
  exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hW)

theorem nParam_eq_two_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h443 : Stmt4_4_3Orbit')
    (h1211 : Lem1211) (hH91 : LemH91) (h1217 : Lem1217) (h1218 : Lem1218)
    (hCartan : Lem1219Cartan) (hPerm : Lem1219Perm) (hyp : Hyp121 G T L V V₁ V₂ n)
    (H : Subgroup G) (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    E1.nParam H = 2 := by
  obtain ⟨hTL, -⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  refine le_antisymm ?_ (two_le_nParam_of h1001 h331 h1211 hH91 h1217 h1218 hyp H hH)
  by_contra hlt
  push Not at hlt
  obtain ⟨p, X, hp, hp3, hXp, hX1, hXHM, hXT, hXN⟩ :=
    hCartan G T L V V₁ V₂ n hyp hTL H hH hlt
  have hXM : X ≤ Subgroup.normalizer (L : Set G) := hXHM.trans inf_le_right
  have hXV := hPerm G T L V V₁ V₂ n hyp hTL p X hp hp3 hXp hXM hXT
  have hXo : Odd (Nat.card X) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hXp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two (by omega)).pow
  exact hXN (lem1219_one_of h1001 h331 h443 hyp X (le_inf hXM hXV) hX1 hXo)

theorem rParam_ge_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h443 : Stmt4_4_3Orbit')
    (h1211 : Lem1211) (hH91 : LemH91) (hOdd : Lem1219OddLocal)
    (hGeom : Lem1219Geom) (hyp : Hyp121 G T L V V₁ V₂ n) :
    ((n + 2 : ℕ) : ℕ∞) ≤ rParam V := by
  obtain ⟨hTL, hNV⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  obtain ⟨β, hβ, -⟩ := (hH91 G T L V V₁ V₂ n hyp hTL).2
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hUN⟩ := hU
  rw [hNV] at hUN
  by_cases hU1 : U = ⊥
  ·
    have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
    have := hVe.1
    obtain ⟨-, -, hcard⟩ := Sec1212.card_eq_of_hyp121 hyp
    rw [hU1, mQuot_bot_eq_rk, rk, hcard, ← pow_add, padicValNat.prime_pow]
    have : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
    exact_mod_cast (by omega : n + 2 ≤ n + n)
  obtain ⟨X, hXMU, hX1, hXo, hXN⟩ := hOdd G T L V V₁ V₂ n hyp hTL U hUV hU1 hUN
  have hXV : ¬ X ≤ Subgroup.centralizer (V : Set G) := fun hXV =>
    hXN (lem1219_one_of h1001 h331 h443 hyp X (le_inf (hXMU.trans inf_le_left) hXV) hX1 hXo)
  have hsing := ((lem1212_of h1001 h331 h1211) G T L V V₁ V₂ n β hyp hβ).1 U hUV hUN
  exact_mod_cast hGeom G T L V V₁ V₂ n β hyp hβ X (hXMU.trans inf_le_left) hXo hXV U hUV
    (hXMU.trans inf_le_right) hsing

end Sec1219

open Sec1219 in
theorem lem1219_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h443 : Stmt4_4_3Orbit')
    (h1211 : Lem1211) (hH91 : LemH91) (h1217 : Lem1217) (h1218 : Lem1218)
    (hCartan : Lem1219Cartan) (hPerm : Lem1219Perm) (hOdd : Lem1219OddLocal)
    (hGeom : Lem1219Geom) : Lem1219 := by
  intro G _ _ T L V V₁ V₂ n hyp
  exact ⟨fun X hXM hX1 hXo => lem1219_one_of h1001 h331 h443 hyp X hXM hX1 hXo,
    fun H hH => nParam_eq_two_of h1001 h331 h443 h1211 hH91 h1217 h1218 hCartan hPerm hyp H hH,
    rParam_ge_of h1001 h331 h443 h1211 hH91 hOdd hGeom hyp⟩

end CFSG.Quasithin.H13
