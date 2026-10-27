module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamNVertex
public import CFSG.Quasithin.Background.GoldschmidtAmalgamVBase
public import CFSG.Quasithin.Recognition.GoldschmidtPushingUp
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

namespace GoldAmN

variable {D : Type*} [Group D]

@[expose] def coreIn (G N : Subgroup D) : Subgroup D where
  carrier := {n | ∀ g ∈ G, g * n * g⁻¹ ∈ N}
  mul_mem' := by
    intro a b ha hb g hg
    have := N.mul_mem (ha g hg) (hb g hg)
    simpa [mul_assoc] using this
  one_mem' := by intro g hg; simp
  inv_mem' := by
    intro a ha g hg
    have := N.inv_mem (ha g hg)
    simpa [mul_assoc] using this

theorem coreIn_le (G N : Subgroup D) : coreIn G N ≤ N := fun n hn => by
  simpa using hn 1 G.one_mem

theorem le_normalizer_coreIn (G N : Subgroup D) :
    G ≤ Subgroup.normalizer (coreIn G N : Set D) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn g' hg'
    have := hn (g' * g) (G.mul_mem hg' hg)
    simpa [mul_assoc] using this
  · intro hn g' hg'
    have := hn (g' * g⁻¹) (G.mul_mem hg' (G.inv_mem hg))
    simpa [mul_assoc] using this

theorem sq_mem_of_relIndex_two {H T : Subgroup D} (hHT : H ≤ T)
    (hnorm : T ≤ Subgroup.normalizer (H : Set D)) (h2 : H.relIndex T = 2) {t : D} (ht : t ∈ T) :
    t ^ 2 ∈ H := by
  have hN : (H.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHT).mpr hnorm
  have := Subgroup.pow_index_mem (H.subgroupOf T) (⟨t, ht⟩ : T)
  have hidx : (H.subgroupOf T).index = 2 := h2
  rw [hidx] at this
  exact this

variable [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem amalgam_symm (h : IsGoldschmidtAmalgam G₁ G₂) : IsGoldschmidtAmalgam G₂ G₁ :=
  { h.toIsGoldschmidtTriple.symm with pCore_eq_bot := h.pCore_eq_bot }

theorem le_normalizer_of_mem_vTriple (h : IsGoldschmidtVTriple G₁ G₂) {x : D} (hx : x ∈ G₂)
    (hx3 : orderOf x = 3) {N : Subgroup D} (hT : G₁ ⊓ G₂ ≤ Subgroup.normalizer (N : Set D))
    (hxN : x ∈ Subgroup.normalizer (N : Set D)) : G₂ ≤ Subgroup.normalizer (N : Set D) := by
  have hxT : (⟨x, hx⟩ : G₂) ∉ (G₁ ⊓ G₂).subgroupOf G₂ := fun hmem =>
    not_mem_of_isPGroup_two h.isPGroup_inf hx3 hmem
  have hsup := gold_sup_zpowers_eq_top (H := (G₁ ⊓ G₂).subgroupOf G₂) h.relIndex_inf_right hxT
  have hle : (G₁ ⊓ G₂).subgroupOf G₂ ⊔ Subgroup.zpowers (⟨x, hx⟩ : G₂) ≤
      (Subgroup.normalizer (N : Set D)).subgroupOf G₂ := by
    refine sup_le ?_ ?_
    · intro t ht
      exact hT ht
    · rw [Subgroup.zpowers_le]
      exact hxN
  intro g hg
  have : (⟨g, hg⟩ : G₂) ∈ (Subgroup.normalizer (N : Set D)).subgroupOf G₂ :=
    hle (by rw [hsup]; exact Subgroup.mem_top _)
  exact this

theorem le_normalizer_of_mem (h : IsGoldschmidtTriple G₁ G₂) {x : D} (hx : x ∈ G₂)
    (hx3 : orderOf x = 3) {N : Subgroup D} (hT : G₁ ⊓ G₂ ≤ Subgroup.normalizer (N : Set D))
    (hxN : x ∈ Subgroup.normalizer (N : Set D)) : G₂ ≤ Subgroup.normalizer (N : Set D) :=
  le_normalizer_of_mem_vTriple h.toVTriple hx hx3 hT hxN

theorem inf_sup_zpowers_eq_right_vTriple (h : IsGoldschmidtVTriple G₁ G₂) {x : D} (hx : x ∈ G₂)
    (hx3 : orderOf x = 3) : G₁ ⊓ G₂ ⊔ Subgroup.zpowers x = G₂ := by
  apply le_antisymm
  · exact sup_le inf_le_right ((Subgroup.zpowers_le).mpr hx)
  · have hxT : (⟨x, hx⟩ : G₂) ∉ (G₁ ⊓ G₂).subgroupOf G₂ := fun hmem =>
      not_mem_of_isPGroup_two h.isPGroup_inf hx3 hmem
    have hsup := gold_sup_zpowers_eq_top (H := (G₁ ⊓ G₂).subgroupOf G₂) h.relIndex_inf_right hxT
    intro g hg
    have hmem : (⟨g, hg⟩ : G₂) ∈
        (G₁ ⊓ G₂).subgroupOf G₂ ⊔ Subgroup.zpowers (⟨x, hx⟩ : G₂) := by
      rw [hsup]; exact Subgroup.mem_top _
    have := Subgroup.mem_map_of_mem G₂.subtype hmem
    rw [Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le inf_le_right] at this
    exact this

theorem inf_sup_zpowers_eq_right (h : IsGoldschmidtTriple G₁ G₂) {x : D} (hx : x ∈ G₂)
    (hx3 : orderOf x = 3) : G₁ ⊓ G₂ ⊔ Subgroup.zpowers x = G₂ :=
  inf_sup_zpowers_eq_right_vTriple h.toVTriple hx hx3

omit [Finite D] in
theorem eq_bot_of_normalizes_vAmalgam (h : IsGoldschmidtVAmalgam G₁ G₂) {N : Subgroup D}
    (hN : N ≤ G₁ ⊓ G₂) (h₁ : G₁ ≤ Subgroup.normalizer (N : Set D))
    (h₂ : G₂ ≤ Subgroup.normalizer (N : Set D)) : N = ⊥ := by
  have htop : Subgroup.normalizer (N : Set D) = ⊤ := by
    rw [eq_top_iff, ← h.gen]
    exact sup_le h₁ h₂
  have : N.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have := h.toIsGoldschmidtVTriple.le_pCore_of_normal_le_inf hN
  rw [h.pCore_eq_bot] at this
  exact le_bot_iff.mp this

omit [Finite D] in
theorem eq_bot_of_normalizes (h : IsGoldschmidtAmalgam G₁ G₂) {N : Subgroup D}
    (hN : N ≤ G₁ ⊓ G₂) (h₁ : G₁ ≤ Subgroup.normalizer (N : Set D))
    (h₂ : G₂ ≤ Subgroup.normalizer (N : Set D)) : N = ⊥ := by
  have htop : Subgroup.normalizer (N : Set D) = ⊤ := by
    rw [eq_top_iff, ← h.gen]
    exact sup_le h₁ h₂
  have : N.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have := h.toIsGoldschmidtTriple.le_pCore_of_normal_le_inf hN
  rw [h.pCore_eq_bot] at this
  exact le_bot_iff.mp this

omit [Finite D] in
theorem mem_normalizer_inf {A B : Subgroup D} {g : D} (hA : g ∈ Subgroup.normalizer (A : Set D))
    (hB : g ∈ Subgroup.normalizer (B : Set D)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

structure CentThree (G : Subgroup D) (x : D) : Prop where
  mem : x ∈ G
  order : orderOf x = 3
  centralizes : ∀ q ∈ pCoreOf 2 G, x * q = q * x
  inverts : ∀ t ∈ G, t ∉ pCoreOf 2 G → t ^ 2 ∈ pCoreOf 2 G → t * x * t⁻¹ = x⁻¹

theorem exists_centThree (G : Subgroup D)
    (hq : Nonempty (↥G ⧸ Open.pCore 2 ↥G ≃* Equiv.Perm (Fin 3))) (hnc : ¬ CharTwo G) :
    ∃ x, CentThree G x := by
  obtain ⟨x, hxG, hx3, hxc, hxinv⟩ := exists_order_three_centralizing G hq hnc
  exact ⟨x, ⟨hxG, hx3, hxc, hxinv⟩⟩

omit [Finite D] in
theorem CentThree.mem_normalizer {G : Subgroup D} {x : D} (hx : CentThree G x) {N : Subgroup D}
    (hN : N ≤ pCoreOf 2 G) : x ∈ Subgroup.normalizer (N : Set D) := by
  have hfix : ∀ m ∈ N, x * m * x⁻¹ = m := fun m hm => by
    rw [hx.centralizes m (hN hm)]; group
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [hfix n hn]; exact hn
  · intro hn
    have hm := hfix _ hn
    have hn' : n = x * n * x⁻¹ := by
      calc n = x⁻¹ * (x * n * x⁻¹) * x := by group
        _ = x⁻¹ * (x * (x * n * x⁻¹) * x⁻¹) * x := by rw [hm]
        _ = x * n * x⁻¹ := by group
    rw [hn']; exact hn

theorem eq_bot_of_le_pCoreOf_right (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) {N : Subgroup D} (hN : N ≤ pCoreOf 2 G₂)
    (hnorm : G₁ ≤ Subgroup.normalizer (N : Set D)) : N = ⊥ := by
  have hT := h.toIsGoldschmidtTriple
  have hNT : N ≤ G₁ ⊓ G₂ := hN.trans (pCoreOf_le_inf_right hT)
  have hG₂ : G₂ ≤ Subgroup.normalizer (N : Set D) :=
    le_normalizer_of_mem hT hx.mem hx.order (inf_le_left.trans hnorm) (hx.mem_normalizer hN)
  exact eq_bot_of_normalizes h hNT hnorm hG₂

theorem card_inf_eq_two_mul_left (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card ↥(G₁ ⊓ G₂) = 2 * Nat.card ↥(pCoreOf 2 G₁) := by
  have h1 := card_left h
  have h2 := card_left_eq_six_mul h
  omega

theorem card_inf_eq_two_mul_right (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card ↥(G₁ ⊓ G₂) = 2 * Nat.card ↥(pCoreOf 2 G₂) := by
  have := card_inf_eq_two_mul_left h.symm
  rwa [inf_comm] at this

omit [Finite D] in
theorem inf_le_normalizer_left : G₁ ⊓ G₂ ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set D) :=
  inf_le_left.trans (le_normalizer_pCoreOf 2 G₁)

omit [Finite D] in
theorem inf_le_normalizer_right : G₁ ⊓ G₂ ≤ Subgroup.normalizer (pCoreOf 2 G₂ : Set D) :=
  inf_le_right.trans (le_normalizer_pCoreOf 2 G₂)

theorem sq_eq_one_of_mem_pCoreOf_left (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) {q : D} (hq : q ∈ pCoreOf 2 G₁) : q ^ 2 = 1 := by
  have hT := h.toIsGoldschmidtTriple
  have hcore : coreIn G₁ (pCoreOf 2 G₂) = ⊥ :=
    eq_bot_of_le_pCoreOf_right h hx (coreIn_le _ _) (le_normalizer_coreIn _ _)
  have hmem : q ^ 2 ∈ coreIn G₁ (pCoreOf 2 G₂) := by
    intro g hg
    have hgq : g * q * g⁻¹ ∈ pCoreOf 2 G₁ :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₁ hg) q).mp hq
    have hgT : g * q * g⁻¹ ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_left hT hgq
    have hsq := sq_mem_of_relIndex_two (pCoreOf_le_inf_right hT) inf_le_normalizer_right
      (relIndex_pCoreOf_right hT) hgT
    simpa [conj_pow] using hsq
  rw [hcore] at hmem
  exact hmem

theorem card_pCoreOf_left_le_eight (h : IsGoldschmidtAmalgam G₁ G₂) {x : D}
    (hx : CentThree G₂ x) : Nat.card ↥(pCoreOf 2 G₁) ≤ 8 := by
  have hT := h.toIsGoldschmidtTriple
  have hTG : G₁ ⊓ G₂ ≤ G₁ := inf_le_left
  have hQ₂T := pCoreOf_le_inf_right hT
  have hQ₁T := pCoreOf_le_inf_left hT
  have hQn : ((pCoreOf 2 G₁).subgroupOf G₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 G₁)).mpr
      (le_normalizer_pCoreOf 2 G₁)
  have hP2 : ((pCoreOf 2 G₂).subgroupOf G₁).relIndex ((G₁ ⊓ G₂).subgroupOf G₁) ∣ 2 := by
    rw [Subgroup.relIndex_subgroupOf hTG, relIndex_pCoreOf_right hT]
  have h8 := gold_relIndex_inf_normalCore_le_eight (A := ↥G₁)
    (E := (G₁ ⊓ G₂).subgroupOf G₁) (P := (pCoreOf 2 G₂).subgroupOf G₁)
    (Q := (pCoreOf 2 G₁).subgroupOf G₁) hT.relIndex_inf_left (fun g hg => hQ₂T hg) hP2
    (fun g hg => hQ₁T hg)
  have hconj : ∀ g ∈ G₁, ∀ n ∈ (((pCoreOf 2 G₂).subgroupOf G₁).normalCore).map G₁.subtype,
      g * n * g⁻¹ ∈ (((pCoreOf 2 G₂).subgroupOf G₁).normalCore).map G₁.subtype := by
    rintro g hg _ ⟨y, hy, rfl⟩
    exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
      (Subgroup.normalCore_normal _).conj_mem y hy ⟨g, hg⟩, rfl⟩
  have hPcore : ((pCoreOf 2 G₂).subgroupOf G₁).normalCore = ⊥ := by
    have hNQ : (((pCoreOf 2 G₂).subgroupOf G₁).normalCore).map G₁.subtype ≤ pCoreOf 2 G₂ := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.normalCore_le ((pCoreOf 2 G₂).subgroupOf G₁) hy
    have hNn : G₁ ≤ Subgroup.normalizer
        ((((pCoreOf 2 G₂).subgroupOf G₁).normalCore).map G₁.subtype : Set D) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro n
      exact ⟨hconj g hg n, fun hn => by
        have := hconj g⁻¹ (G₁.inv_mem hg) _ hn
        simpa [mul_assoc] using this⟩
    have hbot := eq_bot_of_le_pCoreOf_right h hx hNQ hNn
    exact (Subgroup.map_eq_bot_iff_of_injective _ G₁.subtype_injective).mp hbot
  rw [hPcore, inf_bot_eq, Subgroup.relIndex_bot_left] at h8
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 G₁)).toEquiv] at h8

theorem pCoreOf_ne_of_card_ne (h : IsGoldschmidtAmalgam G₁ G₂)
    (hT : Nat.card ↥(G₁ ⊓ G₂) ≠ 2) : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂ := by
  intro heq
  have hbot : pCoreOf 2 G₁ = ⊥ := by
    refine eq_bot_of_normalizes h (pCoreOf_le_inf_left h.toIsGoldschmidtTriple)
      (le_normalizer_pCoreOf 2 G₁) ?_
    rw [heq]
    exact le_normalizer_pCoreOf 2 G₂
  have h1 := card_inf_eq_two_mul_left h.toIsGoldschmidtTriple
  rw [hbot, Subgroup.card_bot] at h1
  exact hT (by omega)

theorem relIndex_pCoreOf_right_pCoreOf_left (h : IsGoldschmidtTriple G₁ G₂)
    (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) :
    (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2 := by
  have hQ₁T := pCoreOf_le_inf_left h
  have hle : (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) ≤ (pCoreOf 2 G₂).relIndex (G₁ ⊓ G₂) :=
    Subgroup.relIndex_le_of_le_right hQ₁T (by rw [relIndex_pCoreOf_right h]; norm_num)
  rw [relIndex_pCoreOf_right h] at hle
  have hne1 : (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) ≠ 1 := by
    intro h1
    have hle1 : pCoreOf 2 G₁ ≤ pCoreOf 2 G₂ := Subgroup.relIndex_eq_one.mp h1
    apply hne
    refine Subgroup.eq_of_le_of_card_ge hle1 ?_
    have := card_inf_eq_two_mul_left h
    have := card_inf_eq_two_mul_right h
    omega
  have hpos : (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_dvd_card (H := pCoreOf 2 G₂) (K := pCoreOf 2 G₁)
    rw [h0] at this
    exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd this)
  omega

theorem relIndex_inf_pCoreOf_left (h : IsGoldschmidtTriple G₁ G₂)
    (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) :
    (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2 := by
  rw [inf_comm, Subgroup.inf_relIndex_right]
  exact relIndex_pCoreOf_right_pCoreOf_left h hne

theorem card_inf_pCoreOf_left (h : IsGoldschmidtTriple G₁ G₂)
    (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) :
    Nat.card ↥(pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) * 2 = Nat.card ↥(pCoreOf 2 G₁) := by
  have := Subgroup.relIndex_mul_card (H := pCoreOf 2 G₂) (K := pCoreOf 2 G₁)
  rw [relIndex_pCoreOf_right_pCoreOf_left h hne, inf_comm] at this
  linarith

theorem charTwo_left_of_four_le (h : IsGoldschmidtAmalgam G₁ G₂) {x : D} (hx : CentThree G₂ x)
    (hcard : 4 ≤ Nat.card ↥(pCoreOf 2 G₁)) : CharTwo G₁ := by
  by_contra hnc
  obtain ⟨x₁, hx₁G, hx₁3, hx₁c, -⟩ := exists_order_three_centralizing G₁ h.quotient₁ hnc
  have hT := h.toIsGoldschmidtTriple
  have hTne : Nat.card ↥(G₁ ⊓ G₂) ≠ 2 := by
    have := card_inf_eq_two_mul_left hT
    omega
  have hne := pCoreOf_ne_of_card_ne h hTne
  have hRcard := card_inf_pCoreOf_left hT hne
  have hRT : G₁ ⊓ G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup D) : Set D) :=
    fun t ht => mem_normalizer_inf (inf_le_normalizer_left ht) (inf_le_normalizer_right ht)
  have hx₁R : x₁ ∈ Subgroup.normalizer
      ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup D) : Set D) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hfix : ∀ m ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂, x₁ * m * x₁⁻¹ = m := fun m hm => by
      rw [hx₁c m hm.1]; group
    constructor
    · intro hn
      rw [hfix n hn]; exact hn
    · intro hn
      have hm := hfix _ hn
      have hn' : n = x₁ * n * x₁⁻¹ := by
        calc n = x₁⁻¹ * (x₁ * n * x₁⁻¹) * x₁ := by group
          _ = x₁⁻¹ * (x₁ * (x₁ * n * x₁⁻¹) * x₁⁻¹) * x₁ := by rw [hm]
          _ = x₁ * n * x₁⁻¹ := by group
      rw [hn']; exact hn
  have hG₁ : G₁ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup D) : Set D) :=
    le_normalizer_of_mem (amalgam_symm h).toIsGoldschmidtTriple hx₁G hx₁3
      (by rw [inf_comm]; exact hRT) hx₁R
  have hbot := eq_bot_of_le_pCoreOf_right h hx inf_le_right hG₁
  rw [hbot, Subgroup.card_bot] at hRcard
  omega

end GoldAmN

end F6

end CFSG.Quasithin
