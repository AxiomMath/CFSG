module

public import CFSG.Quasithin.H13.AS91Sec7Geom
public import CFSG.Quasithin.H13.AS91Sec7Plane

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

theorem ncard_doubleCount {α β : Type*} [Finite α] [Finite β] (r : α → β → Prop) (P : α → Prop)
    (Q : β → Prop) {m n : ℕ} (hP : ∀ a, P a → {b | Q b ∧ r a b}.ncard = m)
    (hQ : ∀ b, Q b → {a | P a ∧ r a b}.ncard = n) :
    {a | P a}.ncard * m = {b | Q b}.ncard * n := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    (s := Finset.univ.filter P) (t := Finset.univ.filter Q)
  have h1 : ∀ a ∈ Finset.univ.filter P,
      ((Finset.univ.filter Q).bipartiteAbove r a).card = m := fun a ha => by
    rw [← hP a (Finset.mem_filter.1 ha).2, ← Set.ncard_coe_finset]
    congr 1
    ext b
    simp [Finset.bipartiteAbove]
  have h2 : ∀ b ∈ Finset.univ.filter Q,
      ((Finset.univ.filter P).bipartiteBelow r b).card = n := fun b hb => by
    rw [← hQ b (Finset.mem_filter.1 hb).2, ← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [Finset.bipartiteBelow]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul] at key
  have hPc : {a | P a}.ncard = (Finset.univ.filter P).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp
  have hQc : {b | Q b}.ncard = (Finset.univ.filter Q).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext b
    simp
  rw [hPc, hQc]
  exact key

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem card_Q : Nat.card c.S.Q = 2 ^ 13 := by
  haveI : Finite c.S.Qt := Finite.of_equiv _ c.ψ.symm.toEquiv
  have h1 : Nat.card c.S.Qt = 2 ^ 12 := by
    rw [Nat.card_congr c.ψ.toEquiv, Nat.card_fun,
      CFSG.CharacterTheory.SteinbergBY.FieldFour.natCard_eq]
    simp
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := c.S.Qt)
  rw [h1, Nat.card_zmod] at h2
  have h3 : Module.finrank (ZMod 2) c.S.Qt = 12 := (Nat.pow_right_injective (le_refl 2) h2).symm
  have h4 : c.S.width = 6 := by
    have := c.S.finrank_Qt_eq_two_mul_width
    omega
  rw [c.S.card_Q_eq, h4]

theorem card_G3 : Nat.card c.G3 = 2 ^ 13 * 2661120 := by
  have hM : c.S.M = c.G3 := by
    show centralizer ({c.S.z} : Set G) = centralizer ({z} : Set G)
    rw [c.S_z]
  rw [← hM, card_eq_card_quotient_mul_card_subgroup c.S.ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange c.S.ρ).toEquiv, c.S.ker_ρ, c.card_Q,
    mul_comm]
  congr 1
  exact c.card_Mbar

theorem smul_x0_eq_mk (g : G) : g • c.x0 = (g : G ⧸ c.G1) := by
  simp [Loc49.x0, basePt, MulAction.Quotient.smul_mk]

theorem ptsP_eq_orbit : {a | c.OnP a c.pi0} = MulAction.orbit ↥c.G3 c.x0 := by
  ext a
  change a ∈ c.ptsP ↔ _
  rw [c.mem_ptsP_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, c.smul_x0_eq_mk h⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.2, (c.smul_x0_eq_mk h).symm⟩

theorem ncard_ptsP_eq_relIndex : {a | c.OnP a c.pi0}.ncard = c.G1.relIndex c.G3 := by
  rw [c.ptsP_eq_orbit, ← MulAction.index_stabilizer ↥c.G3 c.x0]
  have h : MulAction.stabilizer ↥c.G3 c.x0 = c.G1.subgroupOf c.G3 := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change (g : G) • c.x0 = c.x0 ↔ _
    rw [← MulAction.mem_stabilizer_iff (G := G), c.stab_x0]
  rw [h]
  rfl

theorem relIndex_G13 : c.G13.relIndex c.G3 = 77 := by
  have h := Subgroup.relIndex_mul_card (H := c.G13) (K := c.G3)
  rw [inf_eq_left.mpr c.G13_le, c.card_G13, c.card_G3] at h
  norm_num at h
  omega

theorem relIndex_G1_dvd : c.G1.relIndex c.G3 ∣ 77 :=
  c.relIndex_G13 ▸ Subgroup.relIndex_dvd_of_le_left c.G3 (c.G13_le_inf.trans inf_le_left)

end Loc49

namespace M24G

open CFSG.ASVolI.ChH

section Count

variable
  {U : Finset (Finset (Fin 24))}

theorem not_disjoint_self_of_isTrio {t : Finset (Finset (Fin 24))} (ht : IsTrio t) :
    ¬ Disjoint t t := by
  rw [Finset.disjoint_self_iff_empty]
  rintro rfl
  simpa using ht.1

theorem ncard_disjoint_triosOf (hU : IsSextet U) {t : Finset (Finset (Fin 24))}
    (ht : t ∈ triosOf U) : {k | k ∈ triosOf U ∧ Disjoint k t}.ncard = 8 := by
  classical
  obtain ⟨h2, h3⟩ := stmt2_1_1_triosOf hU
  obtain ⟨D₁, D₂, hD12, hDD⟩ := Finset.card_eq_two.1 (h2 t ht)
  have hD₁ : D₁ ∈ spreadsOf U ∧ t ∈ D₁ :=
    Finset.mem_filter.1 (hDD ▸ Finset.mem_insert_self _ _)
  have hD₂ : D₂ ∈ spreadsOf U ∧ t ∈ D₂ :=
    Finset.mem_filter.1 (hDD ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hmem : ∀ D ∈ spreadsOf U, t ∈ D → D = D₁ ∨ D = D₂ := fun D hD htD => by
    have : D ∈ (spreadsOf U).filter (t ∈ ·) := Finset.mem_filter.2 ⟨hD, htD⟩
    rw [hDD] at this
    simpa using this
  have hset : {k | k ∈ triosOf U ∧ Disjoint k t} = ↑((D₁.erase t) ∪ (D₂.erase t)) := by
    ext k
    simp only [Set.mem_setOf_eq, Finset.coe_union, Set.mem_union, Finset.mem_coe,
      Finset.mem_erase]
    constructor
    · rintro ⟨hk, hkd⟩
      have hkt : k ≠ t := by
        rintro rfl
        exact not_disjoint_self_of_isTrio (mem_triosOf.1 ht).1 hkd
      have h4 : ∃ D ∈ spreadsOf U, k ∈ D ∧ t ∈ D := by
        by_contra hcon
        push Not at hcon
        exact (not_disjoint_iff_spreadsOf hU hk ht hkt).2 (fun D hD h => hcon D hD h.1 h.2) hkd
      obtain ⟨D, hD, hkD, htD⟩ := h4
      rcases hmem D hD htD with rfl | rfl
      · exact Or.inl ⟨hkt, hkD⟩
      · exact Or.inr ⟨hkt, hkD⟩
    · rintro (⟨hkt, hkD⟩ | ⟨hkt, hkD⟩)
      · obtain ⟨h1, h5, h6⟩ := (mem_spreadsOf.1 hD₁.1).2 k hkD
        exact ⟨mem_triosOf.2 ⟨h1, h5⟩, h6 t hD₁.2 hkt⟩
      · obtain ⟨h1, h5, h6⟩ := (mem_spreadsOf.1 hD₂.1).2 k hkD
        exact ⟨mem_triosOf.2 ⟨h1, h5⟩, h6 t hD₂.2 hkt⟩
  have hdisj : Disjoint (D₁.erase t) (D₂.erase t) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    obtain ⟨hkt, hk1⟩ := Finset.mem_erase.1 hk1
    obtain ⟨-, hk2⟩ := Finset.mem_erase.1 hk2
    have h5 := Finset.card_le_one.1 (h3 D₁ hD₁.1 D₂ hD₂.1 hD12).le
      k (Finset.mem_inter.2 ⟨hk1, hk2⟩) t (Finset.mem_inter.2 ⟨hD₁.2, hD₂.2⟩)
    exact hkt h5
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj,
    Finset.card_erase_of_mem hD₁.2, Finset.card_erase_of_mem hD₂.2,
    (mem_spreadsOf.1 hD₁.1).1, (mem_spreadsOf.1 hD₂.1).1]

theorem ncard_meet_triosOf (hU : IsSextet U) {t : Finset (Finset (Fin 24))}
    (ht : t ∈ triosOf U) : {k | k ∈ triosOf U ∧ k ≠ t ∧ ¬ Disjoint k t}.ncard = 6 := by
  have h8 := ncard_disjoint_triosOf hU ht
  have h15 := card_triosOf hU
  have htt : t ∉ {k | k ∈ triosOf U ∧ Disjoint k t} ∪
      {k | k ∈ triosOf U ∧ k ≠ t ∧ ¬ Disjoint k t} := by
    rintro (⟨-, h⟩ | ⟨-, h, -⟩)
    · exact not_disjoint_self_of_isTrio (mem_triosOf.1 ht).1 h
    · exact h rfl
  have hdisj : Disjoint {k | k ∈ triosOf U ∧ Disjoint k t}
      {k | k ∈ triosOf U ∧ k ≠ t ∧ ¬ Disjoint k t} := by
    rw [Set.disjoint_left]
    rintro k ⟨-, h1⟩ ⟨-, -, h2⟩
    exact h2 h1
  have hT : (↑(triosOf U) : Set (Finset (Finset (Fin 24)))) =
      insert t ({k | k ∈ triosOf U ∧ Disjoint k t} ∪
        {k | k ∈ triosOf U ∧ k ≠ t ∧ ¬ Disjoint k t}) := by
    ext k
    simp only [Finset.mem_coe, Set.mem_insert_iff, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro hk
      by_cases hkt : k = t
      · exact Or.inl hkt
      · by_cases hd : Disjoint k t
        · exact Or.inr (Or.inl ⟨hk, hd⟩)
        · exact Or.inr (Or.inr ⟨hk, hkt, hd⟩)
    · rintro (rfl | ⟨hk, -⟩ | ⟨hk, -⟩)
      · exact ht
      · exact hk
      · exact hk
  have h := congrArg Set.ncard hT
  rw [Set.ncard_coe_finset, h15, Set.ncard_insert_of_notMem htt, Set.ncard_union_eq hdisj, h8]
    at h
  omega

end Count

end M24G

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

section Cert13


include ρ in
theorem ncard_lnP_onL_trio {g : G} {a : G ⧸ c.G1} {σ : G ⧸ c.G3} (hg : g • c.x0 = a)
    (ha : c.OnP a σ) (P : Finset (Finset (Fin 24)) → Prop) :
    {n | c.OnL a n ∧ c.LnP n σ ∧ P (ρ.trio (g⁻¹ • n))}.ncard =
      {k | k ∈ M24G.triosOf (ρ.sext (g⁻¹ • σ)) ∧ P k}.ncard := by
  have hinj : Set.InjOn (fun n => ρ.trio (g⁻¹ • n))
      {n | c.OnL a n ∧ c.LnP n σ ∧ P (ρ.trio (g⁻¹ • n))} :=
    fun n hn n' hn' h => ρ.eq_of_trio_at hg hn.1 hn'.1 h
  rw [← hinj.ncard_image]
  congr 1
  ext k
  constructor
  · rintro ⟨n, ⟨han, hnσ, hP⟩, rfl⟩
    exact ⟨ρ.trio_mem_triosOf hg ha han hnσ, hP⟩
  · rintro ⟨hk, hP⟩
    obtain ⟨n, han, hnσ, rfl⟩ := ρ.exists_line_of_mem_triosOf hg ha hk
    exact ⟨n, ⟨han, hnσ, hP⟩, rfl⟩

section Cert17


include ρ in
theorem ncard_lnP_onL {a : G ⧸ c.G1} {σ : G ⧸ c.G3} (ha : c.OnP a σ) :
    {m | c.OnL a m ∧ c.LnP m σ}.ncard = 15 := by
  obtain ⟨g, hg, -⟩ := c.exists_frameP ha
  have h := ρ.ncard_lnP_onL_trio hg ha (fun _ => True)
  simp only [and_true] at h
  rw [h, Finset.setOf_mem, Set.ncard_coe_finset]
  exact M24G.card_triosOf (ρ.isSextet_sext_at hg ha)

include ρ in
theorem ncard_adj_onP (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z)
    {a : G ⧸ c.G1} {σ : G ⧸ c.G3} (ha : c.OnP a σ) :
    {b | c.OnP b σ ∧ c.Delta.Adj a b}.ncard = 60 := by
  have h := ncard_doubleCount (fun (m : G ⧸ c.G2) (b : G ⧸ c.G1) => c.OnL b m)
    (fun m => c.OnL a m ∧ c.LnP m σ) (fun b => c.OnP b σ ∧ c.Delta.Adj a b) (m := 4) (n := 1)
    ?_ ?_
  · rw [ρ.ncard_lnP_onL ha] at h
    omega
  · rintro m ⟨ham, hm⟩
    have hset : {b | (c.OnP b σ ∧ c.Delta.Adj a b) ∧ c.OnL b m} = {b | c.OnL b m} \ {a} := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨-, hab⟩, hbm⟩
        exact ⟨hbm, fun h => hab.ne h.symm⟩
      · rintro ⟨hbm, hba⟩
        exact ⟨⟨c.inc_pt_plane hbm hm, c.adj_of_onL (Ne.symm hba) ham hbm⟩, hbm⟩
    rw [hset, Set.ncard_sdiff_singleton_of_mem (show a ∈ {b | c.OnL b m} from ham), c.ncard_onL m]
  · rintro b ⟨hb, hab⟩
    rw [Set.ncard_eq_one]
    obtain ⟨hne, l, hal, hbl⟩ := id hab
    refine ⟨l, ?_⟩
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨han, -⟩, hbn⟩
      exact (c.eq_of_onL hLU hJ hne hal hbl han hbn).symm
    · rintro rfl
      exact ⟨⟨hal, c.lnP_of_adj hG2 hJ ha hb hab hal hbl⟩, hbl⟩

include ρ in
theorem ncard_onP (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z)
    (σ : G ⧸ c.G3) : {a | c.OnP a σ}.ncard = 77 := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G c.pi0 σ
  have himg : {a | c.OnP a (g • c.pi0)} = (g • ·) '' {a | c.OnP a c.pi0} :=
    objOf_smul c.G1 c.G3 g c.pi0
  rw [himg, Set.ncard_image_of_injective _ (MulAction.injective g), c.ncard_ptsP_eq_relIndex]
  have h61 : 61 ≤ {a | c.OnP a c.pi0}.ncard := by
    have h60 := ρ.ncard_adj_onP hLU hG2 hJ c.x0_mem_ptsP
    have hx : c.x0 ∉ {b | c.OnP b c.pi0 ∧ c.Delta.Adj c.x0 b} := fun h => h.2.ne rfl
    have hsub : insert c.x0 {b | c.OnP b c.pi0 ∧ c.Delta.Adj c.x0 b} ⊆ {a | c.OnP a c.pi0} := by
      rintro a (rfl | ⟨ha, -⟩)
      · exact c.x0_mem_ptsP
      · exact ha
    have := Set.ncard_le_ncard hsub
    rwa [Set.ncard_insert_of_notMem hx, h60] at this
  rw [c.ncard_ptsP_eq_relIndex] at h61
  have hdvd := c.relIndex_G1_dvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  generalize c.G1.relIndex c.G3 = n at h61 hdvd hle ⊢
  interval_cases n <;> omega

include ρ in
theorem ncard_far_onP (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z)
    {a : G ⧸ c.G1} {σ : G ⧸ c.G3} (ha : c.OnP a σ) :
    {b | c.OnP b σ ∧ b ≠ a ∧ ¬ c.Delta.Adj a b}.ncard = 16 := by
  have h77 := ρ.ncard_onP hLU hG2 hJ σ
  have h60 := ρ.ncard_adj_onP hLU hG2 hJ ha
  have haN : a ∉ {b | c.OnP b σ ∧ c.Delta.Adj a b} ∪
      {b | c.OnP b σ ∧ b ≠ a ∧ ¬ c.Delta.Adj a b} := by
    rintro (⟨-, h⟩ | ⟨-, h, -⟩)
    · exact h.ne rfl
    · exact h rfl
  have hdisj : Disjoint {b | c.OnP b σ ∧ c.Delta.Adj a b}
      {b | c.OnP b σ ∧ b ≠ a ∧ ¬ c.Delta.Adj a b} := by
    rw [Set.disjoint_left]
    rintro b ⟨-, h1⟩ ⟨-, -, h2⟩
    exact h2 h1
  have hsplit : {b | c.OnP b σ} = insert a ({b | c.OnP b σ ∧ c.Delta.Adj a b} ∪
      {b | c.OnP b σ ∧ b ≠ a ∧ ¬ c.Delta.Adj a b}) := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_union]
    constructor
    · intro hb
      by_cases hba : b = a
      · exact Or.inl hba
      · by_cases hab : c.Delta.Adj a b
        · exact Or.inr (Or.inl ⟨hb, hab⟩)
        · exact Or.inr (Or.inr ⟨hb, hba, hab⟩)
    · rintro (rfl | ⟨hb, -⟩ | ⟨hb, -, -⟩)
      · exact ha
      · exact hb
      · exact hb
  have h := congrArg Set.ncard hsplit
  rw [h77, Set.ncard_insert_of_notMem haN, Set.ncard_union_eq hdisj, h60] at h
  omega

include ρ in
theorem ncard_lnP (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z)
    (σ : G ⧸ c.G3) : {m | c.LnP m σ}.ncard = 231 := by
  have h := ncard_doubleCount (fun (a : G ⧸ c.G1) (m : G ⧸ c.G2) => c.OnL a m)
    (fun a => c.OnP a σ) (fun m => c.LnP m σ) (m := 15) (n := 5) ?_ ?_
  · rw [ρ.ncard_onP hLU hG2 hJ σ] at h
    omega
  · intro a ha
    have h15 := ρ.ncard_lnP_onL ha
    simpa only [and_comm] using h15
  · intro m hm
    have hset : {a | c.OnP a σ ∧ c.OnL a m} = {a | c.OnL a m} := by
      ext a
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨c.inc_pt_plane h hm, h⟩⟩
    rw [hset]
    exact c.ncard_onL m

end Cert17

section Cert12


include ρ in
theorem mem_deltaAt_one_or_two {a : G ⧸ c.G1} {m n : G ⧸ c.G2} {σ : G ⧸ c.G3}
    (ham : c.OnL a m) (han : c.OnL a n) (hm : c.LnP m σ) (hn : c.LnP n σ) (hnm : n ≠ m) :
    n ∈ c.deltaAt 1 a m ∨ n ∈ c.deltaAt 2 a m := by
  obtain ⟨g, hg, -⟩ := c.exists_frame ham
  by_cases hd : Disjoint (ρ.trio (g⁻¹ • n)) (ρ.trio (g⁻¹ • m))
  · exact Or.inr ((ρ.mem_deltaAt_two_iff_at hg ham han).2 ⟨hd, σ, hm, hn⟩)
  · exact Or.inl ((ρ.mem_deltaAt_one_iff_at hg ham han).2 ⟨hnm, hd⟩)

include ρ in
theorem lnP_three_eq_deltaAt_one (hLU : Stmt5_LineU) (h54 : Stmt5_4) (hJ : HypJ4 G z)
    {a w : G ⧸ c.G1} {l : G ⧸ c.G2} {σ : G ⧸ c.G3} (hal : c.OnL a l) (hwl : c.OnL w l)
    (hl : c.LnP l σ) (haw : a ≠ w) :
    {m | (c.LnP m σ ∧ ¬ c.OnL a m ∧ {b | c.OnL b m ∧ c.Delta.Adj a b}.ncard = 3) ∧
        c.OnL w m} = {n | n ∈ c.deltaAt 1 w l ∧ c.LnP n σ} := by
  ext m
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hm, hna, h3⟩, hwm⟩
    have hml : m ≠ l := fun h => hna (h ▸ hal)
    refine ⟨?_, hm⟩
    rcases ρ.mem_deltaAt_one_or_two hwl hwm hl hm hml with h1 | h2
    · exact h1
    · exfalso
      have hall : {b | c.OnL b m ∧ c.Delta.Adj a b} = {b | c.OnL b m} := by
        ext b
        simp only [Set.mem_setOf_eq]
        exact ⟨fun h => h.1, fun h => ⟨h, c.stmt7_1_two h54 hJ hwl hal haw h2 h⟩⟩
      rw [hall, c.ncard_onL m] at h3
      omega
  · rintro ⟨hδ, hm⟩
    have hwm := c.onL_of_mem_deltaAt hδ
    obtain ⟨g, hg, -⟩ := c.exists_frame hwl
    obtain ⟨hml, -⟩ := (ρ.mem_deltaAt_one_iff_at hg hwl hwm).1 hδ
    exact ⟨⟨hm, fun ham => hml (c.eq_of_onL hLU hJ haw hal hwl ham hwm).symm,
      c.stmt7_1_one h54 hJ hwl hal haw hδ⟩, hwm⟩

include ρ in
theorem lnP_all_eq_deltaAt_two (hLU : Stmt5_LineU) (h54 : Stmt5_4) (hJ : HypJ4 G z)
    {a w : G ⧸ c.G1} {l : G ⧸ c.G2} {σ : G ⧸ c.G3} (hal : c.OnL a l) (hwl : c.OnL w l)
    (hl : c.LnP l σ) (haw : a ≠ w) :
    {m | (c.LnP m σ ∧ ¬ c.OnL a m ∧ ∀ b, c.OnL b m → c.Delta.Adj a b) ∧ c.OnL w m} =
      {n | n ∈ c.deltaAt 2 w l ∧ c.LnP n σ} := by
  ext m
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hm, hna, hall⟩, hwm⟩
    have hml : m ≠ l := fun h => hna (h ▸ hal)
    refine ⟨?_, hm⟩
    rcases ρ.mem_deltaAt_one_or_two hwl hwm hl hm hml with h1 | h2
    · exfalso
      have h3 := c.stmt7_1_one h54 hJ hwl hal haw h1
      have hall' : {b | c.OnL b m ∧ c.Delta.Adj a b} = {b | c.OnL b m} := by
        ext b
        simp only [Set.mem_setOf_eq]
        exact ⟨fun h => h.1, fun h => ⟨h, hall b h⟩⟩
      rw [hall', c.ncard_onL m] at h3
      omega
    · exact h2
  · rintro ⟨hδ, hm⟩
    have hwm := c.onL_of_mem_deltaAt hδ
    refine ⟨⟨hm, fun ham => ?_, fun b hb => c.stmt7_1_two h54 hJ hwl hal haw hδ hb⟩, hwm⟩
    have hml : l = m := c.eq_of_onL hLU hJ haw hal hwl ham hwm
    subst hml
    obtain ⟨i, -, hu⟩ := ρ.deltaAt_existsUnique hwl hwl
    have h0 : (0 : Fin 5) = i := hu 0 ((ρ.mem_deltaAt_zero_iff hwl hwl).2 rfl)
    have h2 : (2 : Fin 5) = i := hu 2 hδ
    exact absurd (h0.trans h2.symm) (by decide)

section Cert17


include ρ in
theorem ncard_deltaAt_one_lnP {a : G ⧸ c.G1} {m : G ⧸ c.G2} {σ : G ⧸ c.G3} (ham : c.OnL a m)
    (hm : c.LnP m σ) : {n | n ∈ c.deltaAt 1 a m ∧ c.LnP n σ}.ncard = 6 := by
  have ha : c.OnP a σ := c.inc_pt_plane ham hm
  obtain ⟨g, hg, -⟩ := c.exists_frameP ha
  have h := ρ.ncard_lnP_onL_trio hg ha
    (fun k => k ≠ ρ.trio (g⁻¹ • m) ∧ ¬ Disjoint k (ρ.trio (g⁻¹ • m)))
  have hset : {n | n ∈ c.deltaAt 1 a m ∧ c.LnP n σ} = {n | c.OnL a n ∧ c.LnP n σ ∧
      (ρ.trio (g⁻¹ • n) ≠ ρ.trio (g⁻¹ • m) ∧
        ¬ Disjoint (ρ.trio (g⁻¹ • n)) (ρ.trio (g⁻¹ • m)))} := by
    ext n
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hn, hnσ⟩
      have han := c.onL_of_mem_deltaAt hn
      obtain ⟨hne, hnd⟩ := (ρ.mem_deltaAt_one_iff_at hg ham han).1 hn
      exact ⟨han, hnσ, fun h => hne (ρ.eq_of_trio_at hg han ham h), hnd⟩
    · rintro ⟨han, hnσ, hne, hnd⟩
      exact ⟨(ρ.mem_deltaAt_one_iff_at hg ham han).2 ⟨fun h => hne (by rw [h]), hnd⟩, hnσ⟩
  rw [hset, h]
  exact M24G.ncard_meet_triosOf (ρ.isSextet_sext_at hg ha) (ρ.trio_mem_triosOf hg ha ham hm)

include ρ in
theorem ncard_deltaAt_two_lnP {a : G ⧸ c.G1} {m : G ⧸ c.G2} {σ : G ⧸ c.G3} (ham : c.OnL a m)
    (hm : c.LnP m σ) : {n | n ∈ c.deltaAt 2 a m ∧ c.LnP n σ}.ncard = 8 := by
  have ha : c.OnP a σ := c.inc_pt_plane ham hm
  obtain ⟨g, hg, -⟩ := c.exists_frameP ha
  have h := ρ.ncard_lnP_onL_trio hg ha (fun k => Disjoint k (ρ.trio (g⁻¹ • m)))
  have hset : {n | n ∈ c.deltaAt 2 a m ∧ c.LnP n σ} = {n | c.OnL a n ∧ c.LnP n σ ∧
      Disjoint (ρ.trio (g⁻¹ • n)) (ρ.trio (g⁻¹ • m))} := by
    ext n
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hn, hnσ⟩
      have han := c.onL_of_mem_deltaAt hn
      exact ⟨han, hnσ, ((ρ.mem_deltaAt_two_iff_at hg ham han).1 hn).1⟩
    · rintro ⟨han, hnσ, hd⟩
      exact ⟨(ρ.mem_deltaAt_two_iff_at hg ham han).2 ⟨hd, σ, hm, hnσ⟩, hnσ⟩
  rw [hset, h]
  exact M24G.ncard_disjoint_triosOf (ρ.isSextet_sext_at hg ha) (ρ.trio_mem_triosOf hg ha ham hm)

include ρ in
theorem all_or_three_of_lnP (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (h54 : Stmt5_4)
    (hJ : HypJ4 G z) {a : G ⧸ c.G1} {σ : G ⧸ c.G3} {m : G ⧸ c.G2} (ha : c.OnP a σ)
    (hm : c.LnP m σ) (ham : ¬ c.OnL a m) :
    (∀ b, c.OnL b m → c.Delta.Adj a b) ∨ {b | c.OnL b m ∧ c.Delta.Adj a b}.ncard = 3 := by
  have hN := ρ.ncard_adj_onP hLU hG2 hJ ha
  have h3 := ncard_doubleCount (fun (w : G ⧸ c.G1) (n : G ⧸ c.G2) => c.OnL w n)
    (fun w => c.OnP w σ ∧ c.Delta.Adj a w)
    (fun n => c.LnP n σ ∧ ¬ c.OnL a n ∧ {b | c.OnL b n ∧ c.Delta.Adj a b}.ncard = 3)
    (m := 6) (n := 3) ?_ ?_
  swap
  · rintro w ⟨hw, haw⟩
    obtain ⟨hne, l, hal, hwl⟩ := id haw
    have hl : c.LnP l σ := c.lnP_of_adj hG2 hJ ha hw haw hal hwl
    rw [ρ.lnP_three_eq_deltaAt_one hLU h54 hJ hal hwl hl hne]
    exact ρ.ncard_deltaAt_one_lnP hwl hl
  swap
  · rintro n ⟨hn, -, h3⟩
    have hset : {w | (c.OnP w σ ∧ c.Delta.Adj a w) ∧ c.OnL w n} =
        {b | c.OnL b n ∧ c.Delta.Adj a b} := by
      ext w
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨c.inc_pt_plane h.1 hn, h.2⟩, h.1⟩⟩
    rw [hset]
    exact h3
  have h5 := ncard_doubleCount (fun (w : G ⧸ c.G1) (n : G ⧸ c.G2) => c.OnL w n)
    (fun w => c.OnP w σ ∧ c.Delta.Adj a w)
    (fun n => c.LnP n σ ∧ ¬ c.OnL a n ∧ ∀ b, c.OnL b n → c.Delta.Adj a b)
    (m := 8) (n := 5) ?_ ?_
  swap
  · rintro w ⟨hw, haw⟩
    obtain ⟨hne, l, hal, hwl⟩ := id haw
    have hl : c.LnP l σ := c.lnP_of_adj hG2 hJ ha hw haw hal hwl
    rw [ρ.lnP_all_eq_deltaAt_two hLU h54 hJ hal hwl hl hne]
    exact ρ.ncard_deltaAt_two_lnP hwl hl
  swap
  · rintro n ⟨hn, -, hall⟩
    have hset : {w | (c.OnP w σ ∧ c.Delta.Adj a w) ∧ c.OnL w n} = {b | c.OnL b n} := by
      ext w
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨⟨c.inc_pt_plane h hn, hall w h⟩, h⟩⟩
    rw [hset]
    exact c.ncard_onL n
  rw [hN] at h3 h5
  have hΛ : {n | c.LnP n σ ∧ ¬ c.OnL a n}.ncard = 216 := by
    have hsub : {n | c.OnL a n ∧ c.LnP n σ} ⊆ {n | c.LnP n σ} := fun n hn => hn.2
    have h := Set.ncard_sdiff hsub
    rw [ρ.ncard_lnP hLU hG2 hJ σ, ρ.ncard_lnP_onL ha] at h
    have hset : {n | c.LnP n σ} \ {n | c.OnL a n ∧ c.LnP n σ} =
        {n | c.LnP n σ ∧ ¬ c.OnL a n} := by
      ext n
      simp only [Set.mem_diff, Set.mem_setOf_eq]
      tauto
    rw [← hset, h]
  have hdisj : Disjoint {n | c.LnP n σ ∧ ¬ c.OnL a n ∧ {b | c.OnL b n ∧ c.Delta.Adj a b}.ncard = 3}
      {n | c.LnP n σ ∧ ¬ c.OnL a n ∧ ∀ b, c.OnL b n → c.Delta.Adj a b} := by
    rw [Set.disjoint_left]
    rintro n ⟨-, -, h3⟩ ⟨-, -, hall⟩
    have hset : {b | c.OnL b n ∧ c.Delta.Adj a b} = {b | c.OnL b n} := by
      ext b
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, hall b h⟩⟩
    rw [hset, c.ncard_onL n] at h3
    omega
  have hsub : {n | c.LnP n σ ∧ ¬ c.OnL a n ∧ {b | c.OnL b n ∧ c.Delta.Adj a b}.ncard = 3} ∪
      {n | c.LnP n σ ∧ ¬ c.OnL a n ∧ ∀ b, c.OnL b n → c.Delta.Adj a b} ⊆
        {n | c.LnP n σ ∧ ¬ c.OnL a n} := by
    rintro n (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
  have hcard : ({n | c.LnP n σ ∧ ¬ c.OnL a n ∧ {b | c.OnL b n ∧ c.Delta.Adj a b}.ncard = 3} ∪
      {n | c.LnP n σ ∧ ¬ c.OnL a n ∧ ∀ b, c.OnL b n → c.Delta.Adj a b}).ncard = 216 := by
    rw [Set.ncard_union_eq hdisj]
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hΛ])
  have hmem : m ∈ {n | c.LnP n σ ∧ ¬ c.OnL a n} := ⟨hm, ham⟩
  rw [← heq] at hmem
  rcases hmem with ⟨-, -, h3'⟩ | ⟨-, -, hall⟩
  · exact Or.inr h3'
  · exact Or.inl hall

end Cert17

end Cert12

end Cert13

end ResM24

end CFSG.Quasithin.H13.AS91
