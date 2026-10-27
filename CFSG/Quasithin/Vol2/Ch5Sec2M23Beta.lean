module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Match

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Blueprint CFSG.Quasithin.Asc94 CFSG.Open CFSG.QuasithinUnique
  CFSG.M23Norm3
open scoped Pointwise

theorem exists_m23_apply4
    (a b : Fin 4 → Fin 23) (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ g : ↥NativeSporadic.M23, ∀ i, (g : Equiv.Perm (Fin 23)) (a i) = b i := by
  have h4 := m23_four_transitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M23 (⟨a, ha⟩ : Fin 4 ↪ Fin 23)
    ⟨b, hb⟩
  refine ⟨g, fun i => ?_⟩
  have := congrArg (fun f : Fin 4 ↪ Fin 23 => f i) hg
  simp only [Function.Embedding.smul_apply] at this
  exact this

theorem le_sup_Lbar_IxBar :
    Gbar ≤ Lbar ⊔ IxBar := by
  classical
  set J := Lbar ⊔ IxBar with hJ
  obtain ⟨u, hu⟩ := exists_m23_apply4 ![16, 19, 21, 22] ![19, 16, 21, 22] (by decide) (by decide)
  obtain ⟨v, hv⟩ := exists_m23_apply4 ![16, 19, 21, 22] ![16, 19, 22, 21] (by decide) (by decide)
  have hquad : ∀ w : ↥NativeSporadic.M23,
      (∀ x ∈ ({16, 19, 21, 22} : Set (Fin 23)), (w : Equiv.Perm (Fin 23)) x ∈
        ({16, 19, 21, 22} : Set (Fin 23))) →
        w ∈ quadStab ↥NativeSporadic.M23 (16 : Fin 23) 19 21 22 := by
    intro w hw
    rw [mem_stabilizer_iff]
    have hsub : w • ({16, 19, 21, 22} : Set (Fin 23)) ⊆ {16, 19, 21, 22} := by
      rintro _ ⟨x, hx, rfl⟩
      exact hw x hx
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_smul_set]
  have hu21 : (u : Equiv.Perm (Fin 23)) 21 = 21 := hu 2
  have hu22 : (u : Equiv.Perm (Fin 23)) 22 = 22 := hu 3
  have hv21 : (v : Equiv.Perm (Fin 23)) 21 = 22 := hv 2
  have hv22 : (v : Equiv.Perm (Fin 23)) 22 = 21 := hv 3
  have huG : u ∈ Gbar := mem_Gbar_iff.mpr (Or.inl ⟨hu21, hu22⟩)
  have hvG : v ∈ Gbar := mem_Gbar_iff.mpr (Or.inr ⟨hv21, hv22⟩)
  have huI : u ∈ IxBar := by
    refine Subgroup.mem_inf.mpr ⟨hquad u ?_, huG⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · right; left; exact hu 0
    · left; exact hu 1
    · right; right; left; exact hu 2
    · right; right; right; exact hu 3
  have hvI : v ∈ IxBar := by
    refine Subgroup.mem_inf.mpr ⟨hquad v ?_, hvG⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · left; exact hv 0
    · right; left; exact hv 1
    · right; right; right; exact hv 2
    · right; right; left; exact hv 3
  have hLfix : Lbar ≤ fix21 := fun x hx =>
    mem_fix21_iff.mpr ⟨(mem_Lbar_iff.mp hx).2.1, (mem_Lbar_iff.mp hx).2.2⟩
  have hfixS : IsSimpleGroup ↥fix21 := by
    have e : ↥fix21 ≃* ↥P0 := (Subgroup.subgroupOfEquivOfLe fix21_le_Gbar).symm.trans
      ((Subgroup.equivMapOfInjective _ psiBar psiBar_injective).trans
        (MulEquiv.subgroupCongr map_fix21_eq_P0))
    have := isSimpleGroup_P0
    have : Nontrivial ↥fix21 := by
      rw [← Finite.one_lt_card_iff_nontrivial, card_fix21]
      norm_num
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcL : Nat.card ↥(Lbar.subgroupOf fix21) = 960 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLfix).toEquiv, card_fix3 _ (by decide)]
  have hle : Lbar.subgroupOf fix21 ≤ J.subgroupOf fix21 := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
  have hfixJ : fix21 ≤ J := by
    rcases eq_or_eq_top_of_card_eq_960 card_fix21 hcL hle with h | h
    · exfalso
      have hmem : (⟨u, mem_fix21_iff.mpr ⟨hu21, hu22⟩⟩ : ↥fix21) ∈ J.subgroupOf fix21 :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right huI)
      rw [h] at hmem
      have h19 := (mem_Lbar_iff.mp (Subgroup.mem_subgroupOf.mp hmem)).1
      have hu19 : (u : Equiv.Perm (Fin 23)) 19 = 16 := hu 1
      exact absurd (h19.symm.trans hu19) (by decide)
    · intro x hx
      have : (⟨x, hx⟩ : ↥fix21) ∈ J.subgroupOf fix21 := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  intro x hx
  rcases mem_Gbar_iff.mp hx with h | ⟨h21, h22⟩
  · exact hfixJ (mem_fix21_iff.mpr h)
  · have hxv : x * v⁻¹ ∈ fix21 := by
      rw [mem_fix21_iff]
      have e1 : ((v⁻¹ : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) 21 = 22 := by
        rw [Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq]; exact hv22.symm
      have e2 : ((v⁻¹ : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) 22 = 21 := by
        rw [Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq]; exact hv21.symm
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, e1, e2]
      exact ⟨h22, h21⟩
    have := J.mul_mem (hfixJ hxv) (Subgroup.mem_sup_right hvI)
    rwa [inv_mul_cancel_right] at this

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_stabilizer_coset_iff {Gx : Subgroup G} {t g : G} :
    g ∈ stabilizer G ((t : G) : G ⧸ Gx) ↔ t⁻¹ * g * t ∈ Gx := by
  rw [mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  constructor
  · intro h
    have := Gx.inv_mem h
    simpa [mul_assoc] using this
  · intro h
    have := Gx.inv_mem h
    simpa [mul_assoc] using this

theorem inf_stabilizer_eq_L
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q) (h516 : Stmt5_2_16)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) (hsimple : IsSimpleGroup ↥(m23G0 M L H B D))
    (hcardG0 : Nat.card ↥(m23G0 M L H B D) = 20160) {t : G} (hsw : IsM23Swap M2 π t) :
    m23Gx T M L H B D ⊓ stabilizer G ((t : G) : G ⧸ m23Gx T M L H B D) = L := by
  classical
  set Gx := m23Gx T M L H B D with hGxdef
  set G0 := m23G0 M L H B D with hG0def
  set K := oTwoUpper H with hKdef
  set J := Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx) with hJdef
  have hLG0 : L ≤ G0 := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hKG0 : K ≤ G0 := le_sup_right.trans le_sup_right
  have hG0Gx : G0 ≤ Gx := le_sup_left
  have hTGx : T ≤ Gx := le_sup_right
  obtain ⟨htM2, ht56, ht45⟩ := hsw
  have hH := eq_setStabIn_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hGxM2 : Gx ⊓ M2 = H :=
    (stmt5_2_19_of hQ h516 h526 h1284 hSz hU4 hsp G T M L V H B D L₂ n M2 π hyp hM23 hS).1
  obtain ⟨-, -, -, -, hcardL⟩ := setting_L_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hidx : G0.relIndex Gx = 2 := (h516 G T M L V H B D L₂ n hyp hM23).2.2.1
  have hM2stab : ∀ (m : G) (hm : m ∈ M2), m ∈ stabilizer G ((t : G) : G ⧸ Gx) ↔
      π ⟨m, hm⟩ • ({4, 5} : Set (Fin 7)) = {4, 5} := by
    intro m hm
    rw [mem_stabilizer_coset_iff]
    have hc : t⁻¹ * m * t ∈ M2 := M2.mul_mem (M2.mul_mem (M2.inv_mem htM2) hm) htM2
    have e1 : t⁻¹ * m * t ∈ Gx ↔ t⁻¹ * m * t ∈ H := by
      rw [← hGxM2, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h, hc⟩, fun h => h.1⟩
    rw [e1, hH, mem_setStabIn]
    have e2 : π ⟨t⁻¹ * m * t, hc⟩ = (π ⟨t, htM2⟩)⁻¹ * π ⟨m, hm⟩ * π ⟨t, htM2⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    constructor
    · rintro ⟨_, h⟩
      rw [e2, mul_smul, mul_smul, ht56, inv_smul_eq_iff, ht56] at h
      exact h
    · intro h
      refine ⟨hc, ?_⟩
      rw [e2, mul_smul, mul_smul, ht56, h, inv_smul_eq_iff, ht56]
  set σ₀ : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 4 6 with hσ₀
  have hσ₀A : Equiv.Perm.sign σ₀ = 1 := by
    rw [hσ₀, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  obtain ⟨t₀, ht₀⟩ : σ₀ ∈ π.range := hS.range_eq ▸ Equiv.Perm.mem_alternatingGroup.mpr hσ₀A
  have hσ₀N := conj_mem_k4List h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS hσ₀A (by
    intro i hi
    rcases (show i = 4 ∨ i = 5 ∨ i = 6 by omega) with rfl | rfl | rfl <;> decide)
  have ht₀M : (t₀ : G) ∈ M := mem_M_of_mem_normalizer_k4Sub h526 h527 h1284 hSz hU4 hsp hQ hyp
    hM23 hS t₀ (ht₀ ▸ hσ₀N)
  have ht₀N : (t₀ : G) ∈ Subgroup.normalizer (L : Set G) := hyp.normal ht₀M
  have ht₀t : (t₀ : G)⁻¹ * t ∈ Gx := by
    have hc : (t₀ : G)⁻¹ * t ∈ M2 := M2.mul_mem (M2.inv_mem t₀.2) htM2
    have hmem : (t₀ : G)⁻¹ * t ∈ H := by
      rw [hH, mem_setStabIn]
      refine ⟨hc, ?_⟩
      have e : π ⟨(t₀ : G)⁻¹ * t, hc⟩ = (π t₀)⁻¹ * π ⟨t, htM2⟩ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [e, mul_smul, ht56, ht₀, inv_smul_eq_iff, eq_comm, smul_pair_set_eq_iff]
      decide
    exact (Subgroup.mem_inf.mp (hGxM2 ▸ hmem)).1
  have hLJ : L ≤ J := by
    intro l hl
    refine Subgroup.mem_inf.mpr ⟨hG0Gx (hLG0 hl), ?_⟩
    rw [mem_stabilizer_coset_iff]
    have h1 : (t₀ : G)⁻¹ * l * t₀ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht₀N) l).mp hl
      simpa using this
    have e : t⁻¹ * l * t = ((t₀ : G)⁻¹ * t)⁻¹ * ((t₀ : G)⁻¹ * l * t₀) * ((t₀ : G)⁻¹ * t) := by
      group
    rw [e]
    exact Gx.mul_mem (Gx.mul_mem (Gx.inv_mem ht₀t) (hG0Gx (hLG0 h1))) ht₀t
  have hTJ : ¬ T ≤ J := by
    intro hTJ
    obtain ⟨g, hgT, hg56⟩ := (hS.orbits 5 6).mpr rfl
    have hgS : (g : G) ∈ stabilizer G ((t : G) : G ⧸ Gx) := (Subgroup.mem_inf.mp (hTJ hgT)).2
    rw [hM2stab _ g.2, smul_pair_set_eq_iff, hg56] at hgS
    rcases hgS with ⟨-, h⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)
  have hKJ : ¬ K ≤ J := by
    intro hKJ
    set σ₁ : Equiv.Perm (Fin 7) := Equiv.swap 0 4 * Equiv.swap 1 2 with hσ₁
    have hσ₁A : Equiv.Perm.sign σ₁ = 1 := by
      rw [hσ₁, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      decide
    obtain ⟨k, hk⟩ : σ₁ ∈ π.range := hS.range_eq ▸ Equiv.Perm.mem_alternatingGroup.mpr hσ₁A
    have hkK := mem_K_of_fix56 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS k.2
      (by rw [show (⟨(k : G), k.2⟩ : ↥M2) = k from rfl, hk]; decide)
      (by rw [show (⟨(k : G), k.2⟩ : ↥M2) = k from rfl, hk]; decide)
    have hkS : (k : G) ∈ stabilizer G ((t : G) : G ⧸ Gx) := (Subgroup.mem_inf.mp (hKJ hkK)).2
    rw [hM2stab _ k.2, show (⟨(k : G), k.2⟩ : ↥M2) = k from rfl, hk, smul_pair_set_eq_iff] at hkS
    rcases hkS with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  have hJG0 : ∀ g ∈ G0, g ∈ J → g ∈ L := by
    have hPc : Nat.card ↥(L.subgroupOf G0) = 960 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLG0).toEquiv, hcardL]
    have hPX : L.subgroupOf G0 ≤ J.subgroupOf G0 := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hLJ (Subgroup.mem_subgroupOf.mp hx))
    rcases eq_or_eq_top_of_card_eq_960 hcardG0 hPc hPX with h | h
    · intro g hg hgJ
      have : (⟨g, hg⟩ : ↥G0) ∈ J.subgroupOf G0 := Subgroup.mem_subgroupOf.mpr hgJ
      rw [h] at this
      exact Subgroup.mem_subgroupOf.mp this
    · exfalso
      apply hKJ
      intro k hk
      have : (⟨k, hKG0 hk⟩ : ↥G0) ∈ J.subgroupOf G0 := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have hG0n : ∀ x ∈ Gx, ∀ g ∈ G0, x * g * x⁻¹ ∈ G0 := by
    intro x hx g hg
    have hn : (G0.subgroupOf Gx).Normal := Subgroup.normal_of_index_eq_two hidx
    have := hn.conj_mem ⟨g, hG0Gx hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hcard_of : ∀ X : Subgroup G, X ≤ Gx → (∀ g ∈ G0, g ∈ X → g ∈ L) → L ≤ X →
      Nat.card X ≤ 1920 ∧ (Nat.card X = 1920 → X ≤ Subgroup.normalizer (L : Set G)) := by
    intro X hXGx hXL hLX
    have hinf : G0 ⊓ X = L := le_antisymm (fun g hg => hXL g hg.1 hg.2)
      (le_inf hLG0 hLX)
    have hr : G0.relIndex X ≤ 2 := by
      rw [← hidx]
      exact Subgroup.relIndex_le_of_le_right hXGx (by rw [hidx]; norm_num)
    have hc := Subgroup.relIndex_mul_card (H := G0) (K := X)
    rw [hinf, hcardL] at hc
    refine ⟨by nlinarith, fun h1920 => ?_⟩
    intro x hxX
    rw [Subgroup.mem_normalizer_iff]
    intro l
    have hr2 : G0.relIndex X = 2 := by
      rw [h1920] at hc
      omega
    constructor
    · intro hl
      refine hXL _ (hG0n x (hXGx hxX) l (hLG0 hl)) ?_
      exact X.mul_mem (X.mul_mem hxX (hLX hl)) (X.inv_mem hxX)
    · intro hl
      have hl' : l = x⁻¹ * (x * l * x⁻¹) * x := by group
      rw [hl']
      have h1 : x⁻¹ * (x * l * x⁻¹) * x⁻¹⁻¹ ∈ G0 :=
        hG0n x⁻¹ (Gx.inv_mem (hXGx hxX)) _ (hLG0 hl)
      rw [inv_inv] at h1
      refine hXL _ h1 ?_
      exact X.mul_mem (X.mul_mem (X.inv_mem hxX) (hLX hl)) hxX
  obtain ⟨hJc, hJN⟩ := hcard_of J inf_le_left hJG0 hLJ
  set NL := Gx ⊓ Subgroup.normalizer (L : Set G) with hNL
  have hNLG0 : ∀ g ∈ G0, g ∈ NL → g ∈ L := fun g hg hgN =>
    mem_L_of_mem_G0_of_normalizes h526 h1284 hSz hU4 hsp hQ hyp hM23 hS hsimple hcardG0 hg hgN.2
  obtain ⟨hNLc, -⟩ := hcard_of NL inf_le_left hNLG0
    (le_inf (hLG0.trans hG0Gx) Subgroup.le_normalizer)
  have hTNL : T ≤ NL := le_inf hTGx (hyp.T_le.trans hyp.normal)
  have hJ960 : Nat.card J ≤ 960 := by
    by_contra hlt
    push Not at hlt
    have hr : G0.relIndex J * 960 = Nat.card J := by
      have hinf : G0 ⊓ J = L := le_antisymm (fun g hg => hJG0 g hg.1 hg.2) (le_inf hLG0 hLJ)
      have := Subgroup.relIndex_mul_card (H := G0) (K := J)
      rwa [hinf, hcardL] at this
    have h1920 : Nat.card J = 1920 := by
      have hr2 : G0.relIndex J ≤ 2 := by
        rw [← hidx]
        exact Subgroup.relIndex_le_of_le_right inf_le_left (by rw [hidx]; norm_num)
      have key : G0.relIndex J = 2 := by
        rcases Nat.lt_or_ge (G0.relIndex J) 2 with h | h
        · exfalso
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp h) with h0 | h0
          · rw [h0, zero_mul] at hr
            rw [← hr] at hlt
            exact Nat.not_lt_zero _ hlt
          · rw [h0, one_mul] at hr
            rw [← hr] at hlt
            exact lt_irrefl _ hlt
        · exact le_antisymm hr2 h
      rw [← hr, key]
    have hJNL : J ≤ NL := le_inf inf_le_left (hJN h1920)
    have heq : J = NL := Subgroup.eq_of_le_of_card_ge hJNL (by rw [h1920]; exact hNLc)
    exact hTJ (heq ▸ hTNL)
  exact (Subgroup.eq_of_le_of_card_ge hLJ (by rw [hcardL]; exact hJ960)).symm

theorem mem_Lbar_iff_of_mem_Gbar {z : ↥NativeSporadic.M23} (hz : z ∈ Gbar)
    (h : (19 : Fin 23) ≠ 21) :
    z ∈ stabilizer ↥NativeSporadic.M23 (pair (19 : Fin 23) 21 h) ↔ z ∈ Lbar := by
  rw [mem_stabilizer_iff, smul_pair, pair_eq_iff, m23_smul_eq, m23_smul_eq, mem_Lbar_iff]
  rcases mem_Gbar_iff.mp hz with ⟨h21, h22⟩ | ⟨h21, h22⟩
  · rw [h21]
    constructor
    · rintro (⟨h19, -⟩ | ⟨-, h⟩)
      · exact ⟨h19, rfl, h22⟩
      · exact absurd h (by decide)
    · rintro ⟨h19, -, -⟩
      exact Or.inl ⟨h19, rfl⟩
  · rw [h21]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact absurd h (by decide)
    · rintro ⟨-, h, -⟩
      exact absurd h (by decide)

theorem mem_I_of_zeta {G : Type} [Group G] {M2 : Subgroup G} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    {ι : Fin 7 → Fin 23} {ζ : ↥M2 ≃* ↥(stabilizer ↥NativeSporadic.M23 heptad₀)}
    (hinj : Function.Injective ι) (hζ : IsPermEquiv M2 π ι ζ) (hι3 : ι 3 = 16) (hι4 : ι 4 = 19)
    (hι5 : ι 5 = 21) (hι6 : ι 6 = 22) {m : ↥M2}
    (hq : (ζ m : ↥NativeSporadic.M23) ∈ quadStab ↥NativeSporadic.M23 (16 : Fin 23) 19 21 22) :
    (m : G) ∈ m23I M2 π := by
  have e : ({16, 19, 21, 22} : Set (Fin 23)) = ι '' {3, 4, 5, 6} := by
    simp only [Set.image_insert_eq, Set.image_singleton, hι3, hι4, hι5, hι6]
  rw [mem_stabilizer_iff, e, hζ.smul_image_eq_iff hinj] at hq
  exact mem_setStabIn.mpr ⟨m.2, hq⟩

theorem stmt5_2_17_20_of
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    (hset : Stmt5_2_10_setting) (hfus : M23Fusion3) (h515 : Stmt5_2_15) (h516 : Stmt5_2_16) :
    Stmt5_2_17_20 := by
  intro G _ _ T M L V H B D L₂ n M2 π hyp hM23 hS
  obtain ⟨ι, ζ, hinj, hιH, hζ, hι3, hι4, hι5, hι6, β, hβζ, hβL, hβG0⟩ :=
    exists_beta_of_setting h526 h527 h1284 hSz hU4 hsp hQ hset hfus h515 h516 hyp hM23 hS
  refine ⟨ι, ζ, hinj, hιH, hζ, fun t habcd htI hsw => ?_⟩
  have hG0Gx : m23G0 M L H B D ≤ m23Gx T M L H B D := le_sup_left
  obtain ⟨hsimple, hcardG0⟩ := simple_card_G0_of_beta hG0Gx β hβG0
  have h1 := inf_stabilizer_eq_L h526 h527 h1284 hSz hU4 hsp hQ h516 hyp hM23 hS hsimple hcardG0
    hsw
  have hGxM2 : m23Gx T M L H B D ⊓ M2 = H :=
    (stmt5_2_19_of hQ h516 h526 h1284 hSz hU4 hsp G T M L V H B D L₂ n M2 π hyp hM23 hS).1
  have hpreI : ∀ z : ↥Gbar, (z : ↥NativeSporadic.M23) ∈ IxBar →
      ((β.symm z : ↥(m23Gx T M L H B D)) : G) ∈ m23I M2 π ⊓ m23Gx T M L H B D := by
    intro z hz
    have hzM2 : (z : ↥NativeSporadic.M23) ∈ M2bar := IxBar_le_Hbar hz |>.2
    set m := ζ.symm ⟨z, hzM2⟩ with hm
    have hζm : (ζ m : ↥NativeSporadic.M23) = z := by rw [hm, MulEquiv.apply_symm_apply]
    have hmI : (m : G) ∈ m23I M2 π := by
      refine mem_I_of_zeta hinj hζ hι3 hι4 hι5 hι6 ?_
      rw [hζm]
      exact (Subgroup.mem_inf.mp hz).1
    have h56 : ι 5 ≠ ι 6 := hinj.ne (by decide)
    have hmH : (m : G) ∈ H := by
      have hH := eq_setStabIn_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
      rw [hH, mem_setStabIn]
      refine ⟨m.2, ?_⟩
      rw [← hζ.smul_pair_eq_iff hinj m h56 h56, hζm, ← xbar0_eq_pair hι5 hι6 h56]
      exact (Subgroup.mem_inf.mp hz).2
    have hmGx : (m : G) ∈ m23Gx T M L H B D := (Subgroup.mem_inf.mp (hGxM2 ▸ hmH)).1
    have hβm : β ⟨m, hmGx⟩ = z := by
      apply Subtype.ext
      rw [hβζ ⟨m, hmGx⟩ m.2 hmI]
      exact hζm
    rw [← hβm, MulEquiv.symm_apply_apply]
    exact Subgroup.mem_inf.mpr ⟨hmI, hmGx⟩
  have hpreL : ∀ z : ↥Gbar, (z : ↥NativeSporadic.M23) ∈ Lbar →
      ((β.symm z : ↥(m23Gx T M L H B D)) : G) ∈ L := by
    intro z hz
    rw [hβL, MulEquiv.apply_symm_apply]
    exact hz
  have hxbar : xbar0 = xbar habcd := xbar0_eq_pair hι5 hι6 _
  set β' : ↥(m23Gx T M L H B D) ≃* stabilizer ↥NativeSporadic.M23 (xbar habcd) :=
    β.trans (MulEquiv.subgroupCongr (by rw [← hxbar])) with hβ'
  have hβ'v : ∀ g, (β' g : ↥NativeSporadic.M23) = β g := fun g => rfl
  refine ⟨h1, ?_, β', fun g hgM hgI => ?_, fun g => ?_⟩
  ·
    rw [h1]
    intro g hg
    have hz : (β ⟨g, hg⟩ : ↥NativeSporadic.M23) ∈ Lbar ⊔ IxBar :=
      le_sup_Lbar_IxBar (β ⟨g, hg⟩).2
    have hLG : Lbar ≤ Gbar := fun x hx => fix21_le_Gbar
      (mem_fix21_iff.mpr ⟨(mem_Lbar_iff.mp hx).2.1, (mem_Lbar_iff.mp hx).2.2⟩)
    have hIG : IxBar ≤ Gbar := fun x hx => (Subgroup.mem_inf.mp hx).2
    have hclG : Subgroup.closure ((Lbar : Set ↥NativeSporadic.M23) ∪ IxBar) ≤ Gbar :=
      (Subgroup.closure_le _).mpr (Set.union_subset hLG hIG)
    have hcl : ∀ z ∈ Lbar ⊔ IxBar, ∀ hzG : z ∈ Gbar,
        ((β.symm ⟨z, hzG⟩ : ↥(m23Gx T M L H B D)) : G) ∈ L ⊔ m23I M2 π ⊓ m23Gx T M L H B D := by
      intro z hz
      rw [Subgroup.sup_eq_closure] at hz
      induction hz using Subgroup.closure_induction with
      | mem x hx =>
        intro hxG
        rcases hx with hx | hx
        · exact Subgroup.mem_sup_left (hpreL ⟨x, hxG⟩ hx)
        · exact Subgroup.mem_sup_right (hpreI ⟨x, hxG⟩ hx)
      | one =>
        intro h1G
        rw [show (⟨1, h1G⟩ : ↥Gbar) = 1 from rfl, map_one]
        exact Subgroup.one_mem _
      | mul x y hx hy ihx ihy =>
        intro hxyG
        rw [show (⟨x * y, hxyG⟩ : ↥Gbar) = ⟨x, hclG hx⟩ * ⟨y, hclG hy⟩ from rfl, map_mul,
          Subgroup.coe_mul]
        exact Subgroup.mul_mem _ (ihx (hclG hx)) (ihy (hclG hy))
      | inv x hx ih =>
        intro hxG
        rw [show (⟨x⁻¹, hxG⟩ : ↥Gbar) = (⟨x, hclG hx⟩)⁻¹ from rfl, map_inv, Subgroup.coe_inv]
        exact Subgroup.inv_mem _ (ih (hclG hx))
    have := hcl _ hz (β ⟨g, hg⟩).2
    rwa [show (⟨(β ⟨g, hg⟩ : ↥NativeSporadic.M23), (β ⟨g, hg⟩).2⟩ : ↥Gbar) = β ⟨g, hg⟩ from rfl,
      MulEquiv.symm_apply_apply] at this
  ·
    rw [hβ'v]
    exact hβζ g hgM hgI
  ·
    have hy : ybar habcd = pair (19 : Fin 23) 21 (by decide) :=
      Subtype.ext (by simp [ybar, hι4, hι5])
    rw [hy, hβ'v, mem_Lbar_iff_of_mem_Gbar (β g).2, ← hβL]
    constructor
    · intro hgS
      have : (g : G) ∈ m23Gx T M L H B D ⊓ stabilizer G ((t : G) : G ⧸ m23Gx T M L H B D) :=
        Subgroup.mem_inf.mpr ⟨g.2, hgS⟩
      rw [h1] at this
      exact this
    · intro hgL
      have : (g : G) ∈ m23Gx T M L H B D ⊓ stabilizer G ((t : G) : G ⧸ m23Gx T M L H B D) := by
        rw [h1]; exact hgL
      exact (Subgroup.mem_inf.mp this).2

theorem stmt5_2_10_aut_of
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    (hset : Stmt5_2_10_setting) (hfus : M23Fusion3) (h515 : Stmt5_2_15) (h516 : Stmt5_2_16) :
    Stmt5_2_10_aut := by
  intro G _ _ T M L V H B D L₂ n M2 π hyp hM23 hS α hα
  obtain ⟨ι, ζ, hinj, hιH, hζ, hι3, hι4, hι5, hι6, β, hβζ, hβL, hβG0⟩ :=
    exists_beta_of_setting h526 h527 h1284 hSz hU4 hsp hQ hset hfus h515 h516 hyp hM23 hS
  have hLGx : L ≤ m23Gx T M L H B D :=
    le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hLG : Lbar ≤ Gbar := fun x hx => fix21_le_Gbar
    (mem_fix21_iff.mpr ⟨(mem_Lbar_iff.mp hx).2.1, (mem_Lbar_iff.mp hx).2.2⟩)
  set βL : ↥L ≃* ↥Lbar :=
    { toFun := fun l => ⟨β ⟨l, hLGx l.2⟩, (hβL _).mp l.2⟩
      invFun := fun z => ⟨β.symm ⟨z, hLG z.2⟩,
        (hβL _).mpr (by rw [MulEquiv.apply_symm_apply]; exact z.2)⟩
      left_inv := fun l => by simp
      right_inv := fun z => by simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have key : (⟨((x * y : ↥L) : G), hLGx (x * y).2⟩ : ↥(m23Gx T M L H B D)) =
            ⟨x, hLGx x.2⟩ * ⟨y, hLGx y.2⟩ := rfl
        show ((β ⟨_, hLGx (x * y).2⟩ : ↥Gbar) : ↥NativeSporadic.M23) =
          ((β ⟨x, hLGx x.2⟩ : ↥Gbar) : ↥NativeSporadic.M23) *
            ((β ⟨y, hLGx y.2⟩ : ↥Gbar) : ↥NativeSporadic.M23)
        rw [key, map_mul]
        rfl } with hβL'
  set αbar : ↥Lbar ≃* ↥Lbar := (βL.symm.trans α).trans βL with hαbar
  have hfix : ∀ f : ↥Lbar, (f : ↥NativeSporadic.M23) ∈ F4bar → αbar f = f := by
    intro f hf
    have hfq : (f : ↥NativeSporadic.M23) ∈ quadStab ↥NativeSporadic.M23 (16 : Fin 23) 19 21 22 := by
      rw [mem_stabilizer_iff]
      have hfix4 := (mem_fixingSubgroup_iff _).mp hf
      ext x
      simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_insert_iff, Set.mem_singleton_iff]
      have h16 := hfix4 16 (by simp)
      have h19 := hfix4 19 (by simp)
      have h21 := hfix4 21 (by simp)
      have h22 := hfix4 22 (by simp)
      constructor
      · rintro (h | h | h | h) <;>
        · have := congrArg (fun y => (f : ↥NativeSporadic.M23) • y) h
          simp only [smul_inv_smul] at this
          rw [this]
          simp [h16, h19, h21, h22]
      · rintro (rfl | rfl | rfl | rfl)
        · left; rw [inv_smul_eq_iff, h16]
        · right; left; rw [inv_smul_eq_iff, h19]
        · right; right; left; rw [inv_smul_eq_iff, h21]
        · right; right; right; rw [inv_smul_eq_iff, h22]
    have hfM2 : (f : ↥NativeSporadic.M23) ∈ M2bar :=
      mem_stabilizer_heptad₀_of_mem_quadStab (by decide) (by decide) hfq
    set m := ζ.symm ⟨f, hfM2⟩ with hm
    have hζm : (ζ m : ↥NativeSporadic.M23) = f := by rw [hm, MulEquiv.apply_symm_apply]
    have hmI : (m : G) ∈ m23I M2 π := by
      refine mem_I_of_zeta hinj hζ hι3 hι4 hι5 hι6 ?_
      rw [hζm]
      exact hfq
    have h56 : ι 5 ≠ ι 6 := hinj.ne (by decide)
    have hmH : (m : G) ∈ H := by
      have hH := eq_setStabIn_of_setting h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
      rw [hH, mem_setStabIn]
      refine ⟨m.2, ?_⟩
      rw [← hζ.smul_pair_eq_iff hinj m h56 h56, hζm, ← xbar0_eq_pair hι5 hι6 h56]
      exact hLG f.2
    have hGxM2 : m23Gx T M L H B D ⊓ M2 = H :=
      (stmt5_2_19_of hQ h516 h526 h1284 hSz hU4 hsp G T M L V H B D L₂ n M2 π hyp hM23 hS).1
    have hmGx : (m : G) ∈ m23Gx T M L H B D := (Subgroup.mem_inf.mp (hGxM2 ▸ hmH)).1
    have hβm : (β ⟨m, hmGx⟩ : ↥NativeSporadic.M23) = f := by
      rw [hβζ ⟨m, hmGx⟩ m.2 hmI]
      exact hζm
    have hmL : (m : G) ∈ L := (hβL ⟨m, hmGx⟩).mpr (by rw [hβm]; exact f.2)
    have hk : βL.symm f = ⟨m, hmL⟩ := by
      apply βL.injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hβm.symm
    rw [hαbar, MulEquiv.trans_apply, MulEquiv.trans_apply, hk, hα ⟨m, hmL⟩ hmI, ← hk,
      MulEquiv.apply_symm_apply]
  have hαbar1 := eq_refl_of_fix_F4bar αbar hfix
  refine MulEquiv.ext fun l => ?_
  have := congrArg (fun φ : ↥Lbar ≃* ↥Lbar => φ (βL l)) hαbar1
  simp only [hαbar, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.refl_apply] at this
  exact βL.injective this

end CFSG.Quasithin.H13
