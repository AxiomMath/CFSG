module

public import CFSG.Quasithin.H13.L32A768a
public import CFSG.Quasithin.H13.L32A768b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow
public import CFSG.Quasithin.Background.C1GNBlocks

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

abbrev tU (T : Subgroup G) (u : G) : Subgroup G := T ⊓ Subgroup.centralizer ({u} : Set G)

abbrev yU (T V : Subgroup G) (u : G) : Subgroup G := kz T V ⊔ tU T u

omit [Finite G] in
theorem quasithinOmegaOneCenter_le_centralizer (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.2

omit [Finite G] in
theorem T_le_normalizer_tU {u : G} (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    T ≤ Subgroup.normalizer (tU T u : Set G) := by
  have hZ : ∀ c ∈ fsuV1 T V, ∀ s ∈ T, c * s = s * c := fun c hc s hs =>
    (Subgroup.mem_centralizer_iff.mp
      (quasithinOmegaOneCenter_le_centralizer T (Subgroup.mem_inf.mp hc).2) s hs).symm
  have key : ∀ t ∈ T, ∀ s ∈ tU T u, t * s * t⁻¹ ∈ tU T u := by
    intro t ht s hs
    obtain ⟨hsT, hsu⟩ := Subgroup.mem_inf.mp hs
    have hsu' := Subgroup.mem_centralizer_singleton_iff.mp hsu
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem ht hsT) (inv_mem ht), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨c, hc, hcu⟩ : ∃ c ∈ fsuV1 T V, t⁻¹ * u * t = c * u :=
      ⟨t⁻¹ * u * t * u⁻¹, by simpa using hT t⁻¹ (inv_mem ht), by group⟩
    have hsc := hZ c hc s hsT
    calc t * s * t⁻¹ * u = t * (s * (t⁻¹ * u * t)) * t⁻¹ := by group
      _ = t * (s * (c * u)) * t⁻¹ := by rw [hcu]
      _ = t * ((c * u) * s) * t⁻¹ := by
        rw [show s * (c * u) = c * u * s by rw [← mul_assoc, ← hsc, mul_assoc, hsu', ← mul_assoc]]
      _ = t * (t⁻¹ * u * t * s) * t⁻¹ := by rw [hcu]
      _ = u * (t * s * t⁻¹) := by group
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key t ht s, fun hs => ?_⟩
  have := key t⁻¹ (inv_mem ht) _ hs
  rwa [show t⁻¹ * (t * s * t⁻¹) * t⁻¹⁻¹ = s by group] at this

theorem yU_le_centralizer (h : Hyp147 G T L V) (hMod : StmtL32NModule) {u : G}
    (hu : u ∈ u0 T V) : yU T V u ≤ Subgroup.centralizer ({u} : Set G) :=
  sup_le (kz_le_centralizer_of_mem_u0 h hMod hu) inf_le_right

theorem T_le_normalizer_yU (h : Hyp147 G T L V) (h63 : Thm14_7_63) {u : G}
    (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    T ≤ Subgroup.normalizer (yU T V u : Set G) := by
  intro t ht
  rw [← conjSub_eq_self_iff, conjSub_sup,
    conjSub_eq_self_iff.mpr ((T_le_hz h h63).trans (le_normalizer_oTwoUpper _) ht),
    conjSub_eq_self_iff.mpr (T_le_normalizer_tU hT ht)]

theorem hz_le_normalizer_yU (h : Hyp147 G T L V) (h63 : Thm14_7_63) {u : G}
    (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    hz T V ≤ Subgroup.normalizer (yU T V u : Set G) := by
  rw [(h63 G T L V h).2.2.1]
  exact sup_le (le_sup_left.trans (Subgroup.le_normalizer)) (T_le_normalizer_yU h h63 hT)

theorem inf_yU (h : Hyp147 G T L V) (hMod : StmtL32NModule) {u : G} (hu : u ∈ u0 T V) :
    T ⊓ yU T V u = tU T u :=
  le_antisymm (le_inf inf_le_left (inf_le_right.trans (yU_le_centralizer h hMod hu)))
    (le_inf inf_le_left le_sup_right)

theorem card_hz_mul (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) {u : G}
    (hu : u ∈ u0 T V) (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    Nat.card (hz T V) * Nat.card (tU T u) = Nat.card (yU T V u) * Nat.card T := by
  have h1 := L32NSet14.card_sup_mul_card_inf (T_le_normalizer_yU h h63 hT)
  have hsup : T ⊔ yU T V u = hz T V := by
    rw [(h63 G T L V h).2.2.1]
    exact le_antisymm (sup_le le_sup_right (sup_le le_sup_left
      (inf_le_left.trans le_sup_right))) (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
  rw [hsup, inf_yU h hMod hu] at h1
  rw [h1, mul_comm]

omit [Finite G] in
theorem relIndex_eq_of_card_mul {A B X Y : Subgroup G} [Finite ↥A] [Finite ↥B] (hA : A ≤ Y)
    (hB : B ≤ X) (hc : Nat.card X * Nat.card A = Nat.card Y * Nat.card B) :
    B.relIndex X = A.relIndex Y := by
  have e1 := Subgroup.relIndex_mul_card A Y
  have e2 := Subgroup.relIndex_mul_card B X
  rw [inf_eq_left.mpr hA] at e1
  rw [inf_eq_left.mpr hB] at e2
  have hpos : 0 < Nat.card A * Nat.card B := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc B.relIndex X * (Nat.card A * Nat.card B) = Nat.card X * Nat.card A := by
        rw [← e2]; ring
    _ = Nat.card Y * Nat.card B := hc
    _ = A.relIndex Y * (Nat.card A * Nat.card B) := by rw [← e1]; ring

theorem isSylowTwoOf_tU (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) {u : G}
    (hu : u ∈ u0 T V) (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    QuasithinUnique.IsSylowTwoOf (tU T u) (yU T V u) := by
  have hTH := T_le_hz h h63
  refine ⟨le_sup_right, h.fsu.sylow.1.to_le inf_le_left, fun h2 => ?_⟩
  have e := relIndex_eq_of_card_mul (le_sup_right : tU T u ≤ yU T V u) hTH
    (card_hz_mul h hMod h63 hu hT)
  exact (isSylowTwoOf_of_le h hTH).2.2 (by rw [← Subgroup.relIndex, e]; exact h2)

theorem inf_centralizer_le_yU (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {u : G} (hu : u ∈ u0 T V) :
    hz T V ⊓ Subgroup.centralizer ({u} : Set G) ≤ yU T V u := by
  intro x hx
  obtain ⟨hxH, hxu⟩ := Subgroup.mem_inf.mp hx
  have hTK : T ≤ Subgroup.normalizer (kz T V : Set G) :=
    (T_le_hz h h63).trans (le_normalizer_oTwoUpper _)
  have hKC := kz_le_centralizer_of_mem_u0 h hMod hu
  rw [(h63 G T L V h).2.2.1, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTK] at hxH
  obtain ⟨t, ht, k, hk, rfl⟩ := hxH
  have htu : t ∈ Subgroup.centralizer ({u} : Set G) := by
    have := mul_mem hxu (inv_mem (hKC hk))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨ht, htu⟩))
    (Subgroup.mem_sup_left hk)

omit [Finite G] in
theorem mem_normalizer_inf_of_mem {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  exact fun x => ⟨fun hx => ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩,
    fun hx => ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩⟩

theorem pCoreOf_kz_le_T (h : Hyp147 G T L V) (h63 : Thm14_7_63) : pCoreOf 2 (kz T V) ≤ T := by
  have hTH := T_le_hz h h63
  have h1 : pCoreOf 2 (kz T V) ≤ pCoreOf 2 (hz T V) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (oTwoUpper_le _))
      ((le_normalizer_oTwoUpper _).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  exact h1.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h hTH))

theorem isMinParabolicOf_yU (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {u : G} (hu : u ∈ u0 T V) (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    IsMinParabolicOf (yU T V u) (yU T V u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, π, -, hπs, hπk, -⟩ := isL24Section_u0 h hMod h63
  have hTH := T_le_hz h h63
  have hKC := kz_le_centralizer_of_mem_u0 h hMod hu
  have hTK : T ≤ Subgroup.normalizer (kz T V : Set G) := hTH.trans (le_normalizer_oTwoUpper _)
  set D := T ⊓ kz T V with hD
  have hO2D : pCoreOf 2 (kz T V) ≤ D := le_inf (pCoreOf_kz_le_T h h63) (pCoreOf_le 2 _)
  have hDtU : D ≤ tU T u := le_inf inf_le_left (inf_le_right.trans hKC)
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := fun t ht =>
    mem_normalizer_inf_of_mem (Subgroup.le_normalizer ht) (hTK ht)
  set P : Subgroup SL(2, F4) := (D.subgroupOf (kz T V)).map π with hP
  have hker : π.ker ≤ D.subgroupOf (kz T V) := by
    rw [hπk]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hO2D hx
  have hcomap : P.comap π = D.subgroupOf (kz T V) := by
    rw [hP, Subgroup.comap_map_eq, sup_eq_left.mpr hker]
  have hPodd : ¬ 2 ∣ P.index := by
    rw [hP, Subgroup.index_map_eq _ hπs hker]
    have hc := L32NSet14.card_sup_mul_card_inf hTK
    rw [show T ⊔ kz T V = hz T V by rw [(h63 G T L V h).2.2.1, sup_comm]] at hc
    have e := relIndex_eq_of_card_mul (inf_le_right : D ≤ kz T V) hTH
      (by rw [hc, mul_comm])
    rw [← Subgroup.relIndex, ← e]
    exact (isSylowTwoOf_of_le h hTH).2.2
  have hP2 : IsPGroup 2 P := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨n, hn⟩ := h.fsu.sylow.1
      ⟨(k : G), (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hk)).1⟩
    have hk2 : k ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    exact ⟨n, Subtype.ext (by simp [← map_pow, hk2])⟩
  have hNP : ∀ k : ↥(kz T V), (k : G) ∈ Subgroup.normalizer (D : Set G) →
      π k ∈ Subgroup.normalizer (P : Set SL(2, F4)) := by
    have key : ∀ k : ↥(kz T V), (k : G) ∈ Subgroup.normalizer (D : Set G) →
        ∀ A ∈ P, π k * A * (π k)⁻¹ ∈ P := by
      intro k hk A hA
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hA
      refine Subgroup.mem_map.mpr ⟨k * d * k⁻¹, ?_, by simp⟩
      rw [Subgroup.mem_subgroupOf] at hd ⊢
      exact (Subgroup.mem_normalizer_iff.mp hk d).mp hd
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro A
    refine ⟨key k hk A, fun hA => ?_⟩
    have := key k⁻¹ (inv_mem hk) _ hA
    rwa [map_inv, inv_inv, show (π k)⁻¹ * (π k * A * (π k)⁻¹) * π k = A by group] at this
  have hPN : ∀ k : ↥(kz T V), π k ∈ Subgroup.normalizer (P : Set SL(2, F4)) →
      (k : G) ∈ Subgroup.normalizer (D : Set G) := by
    have key : ∀ k : ↥(kz T V), π k ∈ Subgroup.normalizer (P : Set SL(2, F4)) →
        ∀ d ∈ D, (k : G) * d * (k : G)⁻¹ ∈ D := by
      intro k hk d hd
      have hdK : d ∈ kz T V := (Subgroup.mem_inf.mp hd).2
      have hmem : (⟨d, hdK⟩ : ↥(kz T V)) ∈ D.subgroupOf (kz T V) := hd
      have h1 : π (k * ⟨d, hdK⟩ * k⁻¹) ∈ P := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hk _).mp (Subgroup.mem_map_of_mem π hmem)
      have h2 : k * ⟨d, hdK⟩ * k⁻¹ ∈ D.subgroupOf (kz T V) := by
        rw [← hcomap]
        exact h1
      exact h2
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨key k hk d, fun hd => ?_⟩
    have hk' : π k⁻¹ ∈ Subgroup.normalizer (P : Set SL(2, F4)) := by
      rw [map_inv]
      exact inv_mem hk
    have := key k⁻¹ hk' _ hd
    simp only [Subgroup.coe_inv, inv_inv] at this
    rwa [show (k : G)⁻¹ * ((k : G) * d * (k : G)⁻¹) * (k : G) = d by group] at this
  have hKD : ¬ kz T V ≤ Subgroup.normalizer (D : Set G) := by
    intro hle
    apply not_top_le_normalizer_of_isPGroup hP2 hPodd
    intro A _
    obtain ⟨k, rfl⟩ := hπs A
    exact hNP k (hle k.2)
  have hTn : ¬ yU T V u ≤ Subgroup.normalizer (tU T u : Set G) := by
    intro hle
    apply hKD
    intro k hk
    have h1 : k ∈ Subgroup.normalizer ((tU T u ⊓ kz T V : Subgroup G) : Set G) :=
      mem_normalizer_inf_of_mem (hle (Subgroup.mem_sup_left hk)) (Subgroup.le_normalizer hk)
    have e : tU T u ⊓ kz T V = D :=
      le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf hDtU inf_le_right)
    rwa [e] at h1
  have hXY : yU T V u ⊓ Subgroup.normalizer (D : Set G) < yU T V u := by
    refine lt_of_le_of_ne inf_le_left fun e => hKD ?_
    intro k hk
    have : k ∈ yU T V u ⊓ Subgroup.normalizer (D : Set G) := by
      rw [e]
      exact Subgroup.mem_sup_left hk
    exact this.2
  have hTX : tU T u ≤ yU T V u ⊓ Subgroup.normalizer (D : Set G) :=
    le_inf le_sup_right (inf_le_left.trans hTD)
  have hmax : ∀ Y' : Subgroup G, tU T u ≤ Y' → Y' < yU T V u →
      Y' ≤ yU T V u ⊓ Subgroup.normalizer (D : Set G) := by
    intro Y' hY'1 hY'2
    set M : Subgroup SL(2, F4) := ((Y' ⊓ kz T V).subgroupOf (kz T V)).map π with hM
    have hPM : P ≤ M := by
      rw [hP, hM]
      refine Subgroup.map_mono fun x hx => ?_
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨hY'1 (hDtU hx), (Subgroup.mem_inf.mp hx).2⟩
    rcases eq_top_or_le_normalizer_of_isPGroup hP2 hPodd hPM with hMt | hMN
    · exfalso
      have hKY : kz T V ≤ Y' := by
        intro k hk
        have hπk' : π ⟨k, hk⟩ ∈ M := hMt ▸ Subgroup.mem_top _
        obtain ⟨k', hk', e⟩ := Subgroup.mem_map.mp hπk'
        have hker' : k'⁻¹ * ⟨k, hk⟩ ∈ π.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
        have hkD := hker hker'
        rw [Subgroup.mem_subgroupOf] at hkD hk'
        have h1 := mul_mem hk'.1 (hY'1 (hDtU hkD))
        simpa using h1
      exact absurd (sup_le hKY hY'1) (not_le_of_gt hY'2)
    · intro y hy
      refine ⟨hY'2.le hy, ?_⟩
      have hyY := hY'2.le hy
      have htK : tU T u ≤ Subgroup.normalizer (kz T V : Set G) := inf_le_left.trans hTK
      rw [show yU T V u = tU T u ⊔ kz T V from sup_comm _ _, ← SetLike.mem_coe,
        Subgroup.coe_mul_of_left_le_normalizer_right _ _ htK] at hyY
      obtain ⟨t, ht, k, hk, rfl⟩ := hyY
      have hkY : k ∈ Y' := by
        have := mul_mem (inv_mem (hY'1 ht)) hy
        rwa [inv_mul_cancel_left] at this
      have hkN : π ⟨k, hk⟩ ∈ Subgroup.normalizer (P : Set SL(2, F4)) :=
        hMN (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨hkY, hk⟩))
      exact mul_mem (hTD (Subgroup.mem_inf.mp ht).1) (hPN ⟨k, hk⟩ hkN)
  exact (minParabolic_iff.mp (Setup.minParabolic_of_uniqueMax
    (isSylowTwoOf_tU h hMod h63 hu hT) hTn hTX hXY hmax)).1

theorem yU_le_hz (h : Hyp147 G T L V) (h63 : Thm14_7_63) {u : G} : yU T V u ≤ hz T V :=
  sup_le (oTwoUpper_le _) (inf_le_left.trans (T_le_hz h h63))

theorem pCoreOf_yU_ne_bot (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {u : G} (hu : u ∈ u0 T V) : pCoreOf 2 (yU T V u) ≠ ⊥ := by
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)
  have huU : u ∈ fsuU T V := centralizerMod_le_left _ _ _ hu
  have hV1T : fsuV1 T V ≤ T :=
    inf_le_right.trans ((Subgroup.closure_le T).mpr fun _ hx => hx.1.1)
  have hV1Y : fsuV1 T V ≤ yU T V u := fun z hz => Subgroup.mem_sup_right
    (Subgroup.mem_inf.mpr ⟨hV1T hz, Subgroup.mem_centralizer_singleton_iff.mpr
      (fsuU_comm h (hV1U hz) huU)⟩)
  have hN : yU T V u ≤ Subgroup.normalizer (fsuV1 T V : Set G) := by
    rw [normalizer_eq_centralizer_of_card_two hV1]
    exact yU_le_hz h h63
  have hp : IsPGroup 2 (fsuV1 T V) := IsPGroup.of_card (n := 1) (by rw [hV1, pow_one])
  have hle := le_pCoreOf_of_le_normalizer 2 hV1Y hN hp
  intro hb
  rw [hb, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hV1
  omega

theorem charTwo_yU (h : Hyp147 G T L V) (h63 : Thm14_7_63) {u : G}
    (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) : CharTwo (yU T V u) := by
  obtain ⟨hHz, -⟩ := h63 G T L V h
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hInH : InH (S : Subgroup G) (hz T V) := ⟨by rw [hS]; exact T_le_hz h h63, hHz.1.2⟩
  exact A4.charTwo_of_normal (yU_le_hz h h63) (hz_le_normalizer_yU h h63 hT)
    (charTwo_of_inH h.fsu.qtke.2.1 S hInH)

theorem isSQTKTC_yU (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) {u : G}
    (hu : u ∈ u0 T V) : IsSQTKTC (yU T V u) :=
  ⟨kGroup_of_pCoreOf_ne_bot h.fsu.qtke h.fsu.simple h.fsu.nonabelian
      (pCoreOf_yU_ne_bot h hMod h63 hu),
    stronglyQuasithin_of_pCoreOf_ne_bot h.fsu.qtke (pCoreOf_yU_ne_bot h hMod h63 hu)⟩

omit [Finite G] in
theorem pow_mul_mem_of_le_normalizer {K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) (m : ℕ) :
    ∃ k' ∈ K, (t * k) ^ m = t ^ m * k' := by
  induction m with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ m ih =>
    obtain ⟨k', hk', e⟩ := ih
    refine ⟨t⁻¹ * k' * t * k, mul_mem ?_ hk, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem ht) k').mp hk'
      simpa using this
    · rw [pow_succ, e, pow_succ]
      group

omit [Finite G] in
theorem mem_of_pow_two_pow_mem {N : Subgroup G} {g : G} (hg : Odd (orderOf g)) {k : ℕ}
    (hk : g ^ 2 ^ k ∈ N) : g ∈ N := by
  have hcop : Nat.Coprime (2 ^ k) (orderOf g) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hg)
  by_cases h1 : orderOf g = 1
  · rw [orderOf_eq_one_iff.mp h1]
    exact one_mem _
  have hpos : 1 < orderOf g := by
    obtain ⟨m, hm⟩ := hg
    omega
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hpos
  have e : (g ^ 2 ^ k) ^ m = g := by
    rw [← pow_mul, ← pow_mod_orderOf g (2 ^ k * m), hm, pow_one]
  rw [← e]
  exact pow_mem hk m

theorem twoResidual_yU (h : Hyp147 G T L V) (h63 : Thm14_7_63) {u : G} :
    twoResidual (yU T V u) = kz T V := by
  have hTK : T ≤ Subgroup.normalizer (kz T V : Set G) :=
    (T_le_hz h h63).trans (le_normalizer_oTwoUpper _)
  refine le_antisymm (iInf_le_of_le (kz T V) (iInf_le_of_le ⟨le_sup_left, ?_, ?_⟩ le_rfl)) ?_
  · exact sup_le Subgroup.le_normalizer (inf_le_left.trans hTK)
  · intro x hx
    have htK : tU T u ≤ Subgroup.normalizer (kz T V : Set G) := inf_le_left.trans hTK
    rw [show yU T V u = tU T u ⊔ kz T V from sup_comm _ _, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ htK] at hx
    obtain ⟨t, ht, k, hk, rfl⟩ := hx
    obtain ⟨n, hn⟩ := h.fsu.sylow.1 ⟨t, (Subgroup.mem_inf.mp ht).1⟩
    have ht2 : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨k', hk', e⟩ := pow_mul_mem_of_le_normalizer (htK ht) hk (2 ^ n)
    exact ⟨n, by rw [e, ht2, one_mul]; exact hk'⟩
  · refine le_iInf fun N => le_iInf fun hN => ?_
    refine (Subgroup.closure_le _).mpr fun g hg => ?_
    obtain ⟨k, hk⟩ := hN.2.2 g (Subgroup.mem_sup_left (Subgroup.subset_closure hg))
    exact mem_of_pow_two_pow_mem hg.2 hk

end CFSG.Quasithin.H13.L32A
