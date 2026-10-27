module

public import CFSG.Quasithin.EmptyFaithful.S146Six2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace S146T

section Algebra

variable {G : Type} [Group G]

theorem comm_mul_left (q q' w : G) : ⁅q * q', w⁆ = q * ⁅q', w⁆ * q⁻¹ * ⁅q, w⁆ := by
  simp only [commutatorElement_def]; group

theorem comm_mul_right (q w w' : G) : ⁅q, w * w'⁆ = ⁅q, w⁆ * (w * ⁅q, w'⁆ * w⁻¹) := by
  simp only [commutatorElement_def]; group

theorem comm_eq_one_iff {q w : G} : ⁅q, w⁆ = 1 ↔ w * q = q * w := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem conj_comm (t q w : G) : ⁅t⁻¹ * q * t, w⁆ = t⁻¹ * ⁅q, t * w * t⁻¹⁆ * t := by
  simp only [commutatorElement_def]; group

end Algebra

end S146T

section Setting

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem S146T.Z_sq {x : G} (hx : x ∈ quasithinOmegaOneCenter T) : x ^ 2 = 1 :=
  (mem_quasithinOmegaOneCenter_iff.mp hx).2.2

omit [Finite G] in
theorem S146T.Z_le {x : G} (hx : x ∈ quasithinOmegaOneCenter T) : x ∈ T :=
  (mem_quasithinOmegaOneCenter_iff.mp hx).1

omit [Finite G] in
theorem S146T.comm_Z {y x : G} (hy : y ∈ mcOf T) (hx : x ∈ quasithinOmegaOneCenter T) :
    y * x = x * y :=
  (Subgroup.mem_centralizer_iff.mp hy x hx).symm

omit [Finite G] in
theorem S146T.comm_Z_T {y x : G} (hy : y ∈ T) (hx : x ∈ quasithinOmegaOneCenter T) :
    y * x = x * y :=
  S146T.comm_Z (le_centralizer_quasithinOmegaOneCenter T hy) hx

theorem Setting146.Z_eq_of_iff (S : Setting146 G T M) {a b : G} (ha : a ∈ quasithinOmegaOneCenter T)
    (hb : b ∈ quasithinOmegaOneCenter T) (h : a = 1 ↔ b = 1) : a = b := by
  by_cases ha1 : a = 1
  · rw [ha1, eq_comm]; exact h.mp ha1
  · have hb1 : b ≠ 1 := fun e => ha1 (h.mpr e)
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))).mp S.card_Z
    have h1 : (⟨a, ha⟩ : ↥(quasithinOmegaOneCenter T)) = y :=
      huniq _ (fun e => ha1 (congrArg Subtype.val e))
    have h2 : (⟨b, hb⟩ : ↥(quasithinOmegaOneCenter T)) = y :=
      huniq _ (fun e => hb1 (congrArg Subtype.val e))
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem Setting146.comm_mem_Z (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) {u q : G}
    (hu : u ∈ conjClosure (VZ T M) H) (hq : q ∈ pCoreOf 2 H) :
    ⁅q, u⁆ ∈ quasithinOmegaOneCenter T := by
  have h := (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91.commutator_conjClosure_le u hu q hq
  have h1 := (quasithinOmegaOneCenter T).inv_mem h
  have e : (u * q * u⁻¹ * q⁻¹)⁻¹ = ⁅q, u⁆ := by simp only [commutatorElement_def]; group
  rwa [e] at h1

theorem Setting146.mem_mcOf_of_mem_conjClosure (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : u ∈ conjClosure (VZ T M) H) : u ∈ mcOf T :=
  S.le_mcOf hH (pCoreOf_le 2 H
    ((S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91.conjClosure_Vp_le_pCoreOf hu))

theorem Setting146.pCoreOf_mcOf_le_pCoreOf (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 (S.pCoreOf_mcOf_le.trans hH.1.1)
    ((S.le_mcOf hH).trans (le_normalizer_pCoreOf 2 (mcOf T))) (pCoreOf_isPGroup 2 _)

omit [Finite G] in
theorem S146T.mem_tZero_iff {u : G} (hu : u ∈ mcOf T) {t : G} :
    t ∈ tZero T u ↔ t ∈ T ∧ ⁅t, u⁆ ∈ quasithinOmegaOneCenter T := by
  constructor
  · rintro ⟨ht, -, h⟩
    exact ⟨ht, h u (Subgroup.mem_zpowers u)⟩
  · rintro ⟨ht, hc⟩
    refine ⟨ht, Subgroup.centralizer_le_normalizer _
      (le_centralizer_quasithinOmegaOneCenter T ht), fun w hw => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcomm : Commute ⁅t, u⁆ u := (S146T.comm_Z hu hc).symm
    have e1 : t * u * t⁻¹ = ⁅t, u⁆ * u := by simp only [commutatorElement_def]; group
    have e2 : t * u ^ k * t⁻¹ * (u ^ k)⁻¹ = ⁅t, u⁆ ^ k := by
      calc t * u ^ k * t⁻¹ * (u ^ k)⁻¹ = (t * u * t⁻¹) ^ k * (u ^ k)⁻¹ := by rw [conj_zpow]
        _ = (⁅t, u⁆ * u) ^ k * (u ^ k)⁻¹ := by rw [e1]
        _ = ⁅t, u⁆ ^ k := by rw [hcomm.mul_zpow]; group
    rw [e2]
    exact Subgroup.zpow_mem _ hc k

omit [Finite G] in
theorem S146T.mem_tU_iff {u t : G} : t ∈ tU T u ↔ t ∈ T ∧ ⁅t, u⁆ = 1 := by
  rw [S146T.comm_eq_one_iff]
  constructor
  · rintro ⟨ht, hc⟩
    exact ⟨ht, (Subgroup.mem_centralizer_iff.mp hc u rfl)⟩
  · rintro ⟨ht, hc⟩
    exact ⟨ht, Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact hc⟩

omit [Finite G] in
theorem S146T.tZero_le (T : Subgroup G) (u : G) : tZero T u ≤ T :=
  centralizerMod_le_left _ _ _

omit [Finite G] in
theorem Setting146.exists_comm_ne_one {H : Subgroup G} {u : G} (hu : IsInvU T M H u) :
    ∃ q ∈ pCoreOf 2 (mcOf T), ⁅q, u⁆ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hu.not_central
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact (S146T.comm_eq_one_iff.mp (hcon q hq)).symm

theorem Setting146.pCoreOf_mcOf_le_tZero (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) : pCoreOf 2 (mcOf T) ≤ tZero T u :=
  fun _ hq => (S146T.mem_tZero_iff (S.mem_mcOf_of_mem_conjClosure hH hu.mem)).mpr
    ⟨S.pCoreOf_mcOf_le hq, S.comm_mem_Z hH hu.mem (S.pCoreOf_mcOf_le_pCoreOf hH hq)⟩

theorem Setting146.pCoreOf_le_tZero (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) : pCoreOf 2 H ≤ tZero T u :=
  fun _ hq => (S146T.mem_tZero_iff (S.mem_mcOf_of_mem_conjClosure hH hu.mem)).mpr
    ⟨pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hH.1.1) hq,
      S.comm_mem_Z hH hu.mem hq⟩

theorem Setting146.relIndex_tU_tZero (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {u : G} (hu : IsInvU T M H u) : (tU T u).relIndex (tZero T u) = 2 := by
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hu.mem
  obtain ⟨q₀, hq₀, hq₀u⟩ := Setting146.exists_comm_ne_one hu
  have hq₀Z : ⁅q₀, u⁆ ∈ quasithinOmegaOneCenter T :=
    S.comm_mem_Z hH hu.mem (S.pCoreOf_mcOf_le_pCoreOf hH hq₀)
  have hq₀T0 : q₀ ∈ tZero T u := S.pCoreOf_mcOf_le_tZero hH hu hq₀
  have hq₀T : q₀ ∈ T := S.pCoreOf_mcOf_le hq₀
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨q₀, hq₀T0⟩, fun b => ?_⟩
  obtain ⟨hbT, hbZ⟩ := (S146T.mem_tZero_iff huG).mp b.2
  have hmul : ⁅(b : G) * q₀, u⁆ = ⁅q₀, u⁆ * ⁅(b : G), u⁆ := by
    rw [S146T.comm_mul_left]
    have : (b : G) * ⁅q₀, u⁆ * (b : G)⁻¹ = ⁅q₀, u⁆ := by
      rw [S146T.comm_Z_T hbT hq₀Z]; group
    rw [this]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  show Xor ((b : G) * q₀ ∈ tU T u) ((b : G) ∈ tU T u)
  by_cases hβ : ⁅(b : G), u⁆ = 1
  · refine Or.inr ⟨S146T.mem_tU_iff.mpr ⟨hbT, hβ⟩, fun h => hq₀u ?_⟩
    have := (S146T.mem_tU_iff.mp h).2
    rwa [hmul, hβ, mul_one] at this
  · have hβγ : ⁅(b : G), u⁆ = ⁅q₀, u⁆ :=
      S.Z_eq_of_iff hbZ hq₀Z ⟨fun h => absurd h hβ, fun h => absurd h hq₀u⟩
    refine Or.inl ⟨S146T.mem_tU_iff.mpr ⟨T.mul_mem hbT hq₀T, ?_⟩,
      fun h => hβ ((S146T.mem_tU_iff.mp h).2)⟩
    rw [hmul, ← hβγ]
    have := S146T.Z_sq hbZ
    rwa [sq] at this

theorem Setting146.relIndex_tU_T (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {u : G} (hu : IsInvU T M H u) : (tU T u).relIndex T = 4 := by
  have h := Subgroup.relIndex_mul_relIndex (tU T u) (tZero T u) T (tU_le_tZero T u)
    (S146T.tZero_le T u)
  rw [S.relIndex_tU_tZero hH hu, hu.index_two] at h
  omega

theorem Setting146.tZero_eq_sup_mcOf (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {u : G} (hu : IsInvU T M H u) : tZero T u = pCoreOf 2 (mcOf T) ⊔ tU T u := by
  obtain ⟨q₀, hq₀, hq₀u⟩ := Setting146.exists_comm_ne_one hu
  have hsub : pCoreOf 2 (mcOf T) ⊔ tU T u ≤ tZero T u :=
    sup_le (S.pCoreOf_mcOf_le_tZero hH hu) (tU_le_tZero T u)
  rcases eq_or_eq_of_relIndex_eq_two (le_sup_right : tU T u ≤ pCoreOf 2 (mcOf T) ⊔ tU T u) hsub
    (S.relIndex_tU_tZero hH hu) with h | h
  · exact absurd (S146T.mem_tU_iff.mp (h ▸ Subgroup.mem_sup_left hq₀)).2 hq₀u
  · exact h.symm

theorem Setting146.tZero_eq_sup_pCoreOf (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) : tZero T u = pCoreOf 2 H ⊔ tU T u := by
  apply le_antisymm
  · rw [S.tZero_eq_sup_mcOf hH hu]
    exact sup_le_sup_right (S.pCoreOf_mcOf_le_pCoreOf hH) _
  · exact sup_le (S.pCoreOf_le_tZero hH hu) (tU_le_tZero T u)

theorem Setting146.tZero_le_normalizer_tU (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) :
    tZero T u ≤ Subgroup.normalizer (tU T u : Set G) := by
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hu.mem
  have key : ∀ t ∈ tZero T u, ∀ c ∈ tU T u, t * c * t⁻¹ ∈ tU T u := by
    intro t ht c hc
    obtain ⟨hcT, hcu⟩ := S146T.mem_tU_iff.mp hc
    have htT : t ∈ T := ((S146T.mem_tZero_iff huG).mp ht).1
    have hγ : ⁅t⁻¹, u⁆ ∈ quasithinOmegaOneCenter T :=
      ((S146T.mem_tZero_iff huG).mp ((tZero T u).inv_mem ht)).2
    refine S146T.mem_tU_iff.mpr ⟨T.mul_mem (T.mul_mem htT hcT) (T.inv_mem htT), ?_⟩
    have e1 : ⁅t * c * t⁻¹, u⁆ = t * ⁅c, t⁻¹ * u * t⁆ * t⁻¹ := by
      simp only [commutatorElement_def]; group
    have e2 : t⁻¹ * u * t = ⁅t⁻¹, u⁆ * u := by simp only [commutatorElement_def]; group
    have e3 : ⁅c, ⁅t⁻¹, u⁆⁆ = 1 := S146T.comm_eq_one_iff.mpr (S146T.comm_Z_T hcT hγ).symm
    rw [e1, e2, S146T.comm_mul_right, e3, hcu, one_mul, mul_one]
    group
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨key t ht n, fun h => ?_⟩
  have h1 := key t⁻¹ ((tZero T u).inv_mem ht) _ h
  have e : t⁻¹ * (t * n * t⁻¹) * t⁻¹⁻¹ = n := by group
  rwa [e] at h1

theorem Setting146.mem_tZero_of_mem_normalizer (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) {t : G} (htT : t ∈ T)
    (htN : t ∈ Subgroup.normalizer (tU T u : Set G)) : t ∈ tZero T u := by
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hu.mem
  by_contra htT0
  apply hu.not_central_mul t htT htT0
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqH : q ∈ pCoreOf 2 H := S.pCoreOf_mcOf_le_pCoreOf hH hq
  have hqT : q ∈ T := S.pCoreOf_mcOf_le hq
  have hutU : t * u * t⁻¹ ∈ conjClosure (VZ T M) H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (VZ T M) H (hH.1.1 htT)) u).mp hu.mem
  have ha : ⁅q, u⁆ ∈ quasithinOmegaOneCenter T := S.comm_mem_Z hH hu.mem hqH
  have hb : ⁅q, t * u * t⁻¹⁆ ∈ quasithinOmegaOneCenter T := S.comm_mem_Z hH hutU hqH
  have hab : ⁅q, u⁆ = ⁅q, t * u * t⁻¹⁆ := by
    refine S.Z_eq_of_iff ha hb ?_
    have h1 : ⁅q, u⁆ = 1 ↔ q ∈ tU T u :=
      ⟨fun h => S146T.mem_tU_iff.mpr ⟨hqT, h⟩, fun h => (S146T.mem_tU_iff.mp h).2⟩
    have h2 : ⁅q, t * u * t⁻¹⁆ = 1 ↔ t⁻¹ * q * t ∈ tU T u := by
      constructor
      · intro h
        refine S146T.mem_tU_iff.mpr ⟨T.mul_mem (T.mul_mem (T.inv_mem htT) hqT) htT, ?_⟩
        rw [S146T.conj_comm, h]; group
      · intro h
        have h' := (S146T.mem_tU_iff.mp h).2
        rw [S146T.conj_comm] at h'
        have e : ⁅q, t * u * t⁻¹⁆ = t * (t⁻¹ * ⁅q, t * u * t⁻¹⁆ * t) * t⁻¹ := by group
        rw [e, h']; group
    have h3 : t⁻¹ * q * t ∈ tU T u ↔ q ∈ tU T u := by
      have h4 := Subgroup.mem_normalizer_iff.mp htN (t⁻¹ * q * t)
      have e : t * (t⁻¹ * q * t) * t⁻¹ = q := by group
      rwa [e] at h4
    rw [h1, h2, h3]
  have hu_b : u * ⁅q, t * u * t⁻¹⁆ * u⁻¹ = ⁅q, t * u * t⁻¹⁆ := by
    rw [S146T.comm_Z huG hb]; group
  have hfin : ⁅q, u * (t * u * t⁻¹)⁆ = 1 := by
    rw [S146T.comm_mul_right, hu_b, ← hab]
    have := S146T.Z_sq ha
    rwa [sq] at this
  exact (S146T.comm_eq_one_iff.mp hfin).symm

theorem Setting146.stage1463_one (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {u : G} (hu : IsInvU T M H u) :
    (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2 ∧
      tZero T u = T ⊓ Subgroup.normalizer (tU T u : Set G) ∧
      tZero T u = pCoreOf 2 (mcOf T) ⊔ tU T u ∧ tZero T u = pCoreOf 2 H ⊔ tU T u := by
  refine ⟨S.relIndex_tU_T hH hu, S.relIndex_tU_tZero hH hu, ?_, S.tZero_eq_sup_mcOf hH hu,
    S.tZero_eq_sup_pCoreOf hH hu⟩
  apply le_antisymm
  · exact le_inf (S146T.tZero_le T u) (S.tZero_le_normalizer_tU hH hu)
  · exact fun t ht => S.mem_tZero_of_mem_normalizer hH hu ht.1 ht.2

theorem stage1463_one_proof : Stage1463One :=
  fun _ _ _ _ _ S _ hH _ hu => S.stage1463_one hH hu

theorem stage1463_two_of (h : Stage1461Six) : Stage1463Two := by
  intro G _ _ T M S H hH u hu
  have hnorm : ((tZero T u).subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hu.index_two
  have h6 := h G T M S H hH (tZero T u) (S.pCoreOf_le_tZero hH hu) (S146T.tZero_le T u) hnorm
  have hle : Subgroup.normalizer (tZero T u : Set G) ≤ mcOf T := h6.1.trans h6.2
  calc Subgroup.normalizer (tZero T u : Set G)
      = Subgroup.normalizer (tZero T u : Set G) ⊓ mcOf T := (inf_eq_left.mpr hle).symm
    _ = T := hu.normalizer_eq

end Setting

end CFSG.Quasithin
