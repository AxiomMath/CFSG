module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxMc
public import CFSG.Quasithin.EmptyFaithful.S14110AuxBlocks
public import CFSG.Quasithin.EmptyFaithful.S14110AuxS4
public import CFSG.Quasithin.EmptyFaithful.S14110AuxDihedral
public import CFSG.Quasithin.EmptyFaithful.S14110D8

public section

namespace CFSG.Quasithin.S14110

open CFSG.Open CFSG.LieType.BorelTits Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_commutator_eq {X J : Subgroup G} (hJ : ⁅X, J⁆ = X) :
    J ≤ normalizer (X : Set G) := by
  have key : ∀ j ∈ J, ∀ x ∈ X, j * x * j⁻¹ ∈ X := by
    intro j hj x hx
    have h1 : ⁅x, j⁆ ∈ ⁅X, J⁆ := Subgroup.commutator_mem_commutator hx hj
    rw [hJ] at h1
    have h2 : (⁅x, j⁆)⁻¹ ∈ X := X.inv_mem h1
    have : j * x * j⁻¹ = (⁅x, j⁆)⁻¹ * x := by rw [commutatorElement_def]; group
    rw [this]
    exact X.mul_mem h2 hx
  intro j hj
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key j hj x, fun hx => ?_⟩
  have := key j⁻¹ (J.inv_mem hj) _ hx
  rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this

omit [Finite G] in
theorem thompsonJ_le_self (R : Subgroup G) : thompsonJ R ≤ R :=
  iSup₂_le fun _ hA => hA.1

omit [Finite G] in
theorem not_two_dvd_index_subgroupOf {T M : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTM : T ≤ M) : ¬ 2 ∣ (T.subgroupOf M).index := by
  intro hd
  apply hT.2
  refine hd.trans ?_
  have := Subgroup.relIndex_dvd_index_of_le hTM
  simpa [Subgroup.relIndex] using this

omit [Finite G] in
theorem mem_normalizer_iff_cj {g : G} {X : Subgroup G} :
    g ∈ normalizer (X : Set G) ↔ cj g X = X := by
  rw [mem_normalizer_iff]
  constructor
  · intro h
    ext x
    rw [mem_cj]
    have := h (g⁻¹ * x * g)
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    exact this
  · intro h y
    have h1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    constructor
    · intro hy
      rw [← h, mem_cj, h1]
      exact hy
    · intro hy
      rw [← h, mem_cj, h1] at hy
      exact hy

omit [Finite G] in
theorem le_normalizer_inf_centralizer {M X₀ : Subgroup G}
    (hn : M ≤ normalizer (X₀ : Set G)) :
    M ≤ normalizer ((M ⊓ centralizer (X₀ : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ M, ∀ k ∈ M ⊓ centralizer (X₀ : Set G),
      m * k * m⁻¹ ∈ M ⊓ centralizer (X₀ : Set G) := fun m hm k hk =>
    ⟨M.mul_mem (M.mul_mem hm hk.1) (M.inv_mem hm), conj_mem_centralizer hn hm hk.2⟩
  intro m hm
  rw [mem_normalizer_iff]
  intro k
  exact ⟨key m hm k, fun hk => by simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ hk⟩

theorem case_normal {T Mc M X W R : Subgroup G} {c : G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hX : A4Data X W c) (hXM : X ≤ M) (hXn : M ≤ normalizer (X : Set G))
    (hRT : R ≤ T) (hJ : ⁅X, thompsonJ R⁆ = X) :
    M = Mc ∧ 2 < Nat.card (quasithinOmegaOneCenter T) := by
  classical
  have hTM : T ≤ M := hM.2
  set K : Subgroup G := M ⊓ centralizer (X : Set G) with hK
  have hWn : M ≤ normalizer (W : Set G) := hXn.trans hX.normalizer_le_normalizer_W
  have hKn : M ≤ normalizer (K : Set G) := le_normalizer_inf_centralizer hXn
  have hXnK : X ≤ normalizer (K : Set G) := hXM.trans hKn
  have hNM : K ⊔ X ≤ M := sup_le inf_le_left hXM
  have hMN : M ≤ normalizer ((K ⊔ X : Subgroup G) : Set G) := fun m hm =>
    Subgroup.inf_normalizer_le_normalizer_sup K X ⟨hKn hm, hXn hm⟩
  have hodd : ∀ g ∈ M, Odd (orderOf g) → g ∈ K ⊔ X := by
    intro g hg hord
    have hgm : g ^ orderOf g = 1 := pow_orderOf_eq_one g
    obtain ⟨x, hx, hxc⟩ := hX.exists_mem_mul_centralizer_of_odd (hXn hg) hord
      (by rw [hgm]; exact one_mem _)
    have hk : x⁻¹ * g ∈ K := ⟨M.mul_mem (M.inv_mem (hXM hx)) hg, hxc⟩
    have : g = x * (x⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left hk)
  have hfact : ∀ m ∈ M, ∃ k ∈ K, ∃ x ∈ X, ∃ t ∈ T, m = k * x * t := by
    intro m hm
    obtain ⟨n, hn, t, ht, rfl⟩ := exists_mul_of_odd_mem hNM hMN hTM
      (not_two_dvd_index_subgroupOf h.sylow hTM) hodd m hm
    have hn' : n ∈ ((K ⊔ X : Subgroup G) : Set G) := hn
    rw [coe_mul_of_right_le_normalizer_left K X hXnK] at hn'
    obtain ⟨k, hk, x, hx, rfl⟩ := hn'
    exact ⟨k, hk, x, hx, t, ht, by group⟩
  have hW1 : W ≠ ⊥ := by
    intro hb
    have := hX.card_W
    rw [hb, Subgroup.card_bot] at this
    omega
  by_cases hCT : T ⊓ centralizer (X : Set G) = ⊥
  ·
    exfalso
    have hK1 : K = ⊥ := centralizer_eq_bot_of_centralizer_inf_eq_bot h hM hXn hCT
    have hne : ∃ m ∈ M, m ∉ X := by
      by_contra hcon0
      have hcon : ∀ m ∈ M, m ∈ X := fun m hm => by_contra fun hmX => hcon0 ⟨m, hm, hmX⟩
      have hTX : T ≤ X := fun t ht => hcon t (hTM ht)
      have hJW : thompsonJ R ≤ W := by
        intro j hj
        have hjT : j ∈ T := hRT (thompsonJ_le_self R hj)
        obtain ⟨n, hn⟩ := h.sylow.1 (⟨j, hjT⟩ : T)
        exact hX.mem_W_of_two_pow (hTX hjT) (by simpa using congrArg Subtype.val hn)
      have hXW : X ≤ W := by
        calc X = ⁅X, thompsonJ R⁆ := hJ.symm
          _ ≤ W := by
            rw [Subgroup.commutator_le]
            intro x hx j hj
            have hxj : x * j * x⁻¹ ∈ W := (mem_normalizer_iff.1 (hX.le_normalizer hx) j).1 (hJW hj)
            rw [commutatorElement_def]
            exact W.mul_mem hxj (W.inv_mem (hJW hj))
      have := Subgroup.card_le_of_le hXW
      rw [hX.card_X, hX.card_W] at this
      omega
    obtain ⟨e⟩ := nonempty_mulEquiv_perm_four hX hXM (fun m hm => hXn hm)
      (fun m hm hcom => by
        have hmK : m ∈ K := ⟨hm, mem_centralizer_iff.2 (fun x hx => (hcom x hx).symm)⟩
        rw [hK1] at hmK
        exact Subgroup.mem_bot.1 hmK) hne
    obtain ⟨φ⟩ := nonempty_mulEquiv_dihedralFour_of_sylow hTM h.sylow.1
      (not_two_dvd_index_subgroupOf h.sylow hTM) e
    exact not_nonempty_mulEquiv_dihedralFour h ⟨φ⟩
  · exact eq_mc_of_centralizer_ne_bot h hM hXM hXn hX.center hX.le hW1 hX.sq_eq_one hWn hfact hCT

end CFSG.Quasithin.S14110
