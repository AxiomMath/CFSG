module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.SBc17InnB

public section

namespace CFSG.Quasithin.H13.KGBlk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem eq_one_of_commute_swap_small {n : ℕ} (hn : n ≤ 6) {c : Equiv.Perm (Fin n)}
    (hc5 : c ^ 5 = 1) {x y : Fin n} (hxy : x ≠ y)
    (hcomm : c * Equiv.swap x y = Equiv.swap x y * c) : c = 1 := by
  classical
  obtain ⟨hcx, hcy⟩ := SBc17.fix_of_commute_swap hxy hcomm hc5
  have hinv : ∀ z, c z ∈ ({x, y} : Finset (Fin n))ᶜ ↔ z ∈ ({x, y} : Finset (Fin n))ᶜ := by
    intro z
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (h ▸ hcx), fun h => h2 (h ▸ hcy)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (c.injective (h.trans hcx.symm)),
        fun h => h2 (c.injective (h.trans hcy.symm))⟩
  have hcard : (({x, y} : Finset (Fin n))ᶜ).card ≤ 4 := by
    rw [Finset.card_compl, Finset.card_pair hxy, Fintype.card_fin]
    omega
  have hfix := SBc17.perm_fix_of_invariant_small c hc5 _ hinv hcard
  ext z
  by_cases hz : z ∈ ({x, y} : Finset (Fin n))ᶜ
  · rw [hfix z hz, Equiv.Perm.one_apply]
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, not_and,
      not_not] at hz
    by_cases hzx : z = x
    · rw [hzx, hcx, Equiv.Perm.one_apply]
    · rw [hz hzx, hcy, Equiv.Perm.one_apply]

theorem eq_one_of_two_group_seven {N : Subgroup (Equiv.Perm (Fin 7))} (hN : IsPGroup 2 N)
    {x y : Fin 7} (hxy : x ≠ y) (hNσ : ∀ ν ∈ N, ν * Equiv.swap x y = Equiv.swap x y * ν)
    (hNs : ∀ ν ∈ N, Equiv.Perm.sign ν = 1) {c : Equiv.Perm (Fin 7)} (hc5 : c ^ 5 = 1)
    (hc1 : c ≠ 1) (hcσ : c * Equiv.swap x y = Equiv.swap x y * c)
    (hcN : c ∈ Subgroup.normalizer (N : Set (Equiv.Perm (Fin 7)))) : ∀ ν ∈ N, ν = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcx, hcy⟩ := SBc17.fix_of_commute_swap hxy hcσ hc5
  have hct : c.cycleType = {5} := SBc17.cycleType_eq_five (by norm_num) hc5 hc1
  have hcyc : c.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp (by rw [hct]; rfl)
  have hsupp : c.support.card = 5 := by rw [← Equiv.Perm.sum_cycleType, hct]; rfl
  have hxs : x ∉ c.support := Equiv.Perm.notMem_support.mpr hcx
  have hys : y ∉ c.support := Equiv.Perm.notMem_support.mpr hcy
  have hpts : ∀ w, w ∈ c.support ∨ w = x ∨ w = y := by
    intro w
    by_contra h
    push Not at h
    have hc := Finset.card_le_card (Finset.subset_univ (insert w (insert x (insert y c.support))))
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      hsupp, Finset.card_univ, Fintype.card_fin] at hc
    · omega
    · exact hys
    · simp [hxy, hxs]
    · simp [h.1, h.2.1, h.2.2]
  have hswap : ∀ ν ∈ N, ∀ w, ν (Equiv.swap x y w) = Equiv.swap x y (ν w) := by
    intro ν hν w
    have := congrArg (fun f : Equiv.Perm (Fin 7) => f w) (hNσ ν hν)
    simpa using this
  set F := MulAction.fixedPoints ↥N (Fin 7) with hF
  have hmem : ∀ w, w ∈ F ↔ ∀ ν ∈ N, ν w = w := by
    intro w
    rw [hF, MulAction.mem_fixedPoints]
    exact ⟨fun h ν hν => h ⟨ν, hν⟩, fun h ν => h ν ν.2⟩
  have hmod := hN.card_modEq_card_fixedPoints (Fin 7)
  have hxy' : x ∈ F ↔ y ∈ F := by
    rw [hmem, hmem]
    constructor
    · intro h ν hν
      have := hswap ν hν x
      rwa [Equiv.swap_apply_left, h ν hν, Equiv.swap_apply_left] at this
    · intro h ν hν
      have := hswap ν hν y
      rwa [Equiv.swap_apply_right, h ν hν, Equiv.swap_apply_right] at this
  obtain ⟨z, hzF, hzs⟩ : ∃ z ∈ F, z ∈ c.support := by
    by_contra hno
    push Not at hno
    have hsub : F ⊆ {x, y} := fun w hw => by
      rcases hpts w with h | h | h
      · exact absurd h (hno w hw)
      · simp [h]
      · simp [h]
    have hcard : Nat.card F = 0 ∨ Nat.card F = 2 := by
      by_cases hx : x ∈ F
      · right
        have hFe : F = {x, y} :=
          Set.Subset.antisymm hsub (Set.insert_subset_iff.mpr ⟨hx, by simpa using hxy'.mp hx⟩)
        rw [hFe, Nat.card_coe_set_eq, Set.ncard_pair hxy]
      · left
        have hFe : F = ∅ := by
          refine Set.eq_empty_of_forall_notMem fun w hw => ?_
          rcases Set.mem_insert_iff.mp (hsub hw) with h | h
          · exact hx (h ▸ hw)
          · exact hx (hxy'.mpr ((Set.mem_singleton_iff.mp h) ▸ hw))
        rw [hFe, Nat.card_coe_set_eq, Set.ncard_empty]
    rw [Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin] at hmod
    unfold Nat.ModEq at hmod
    rcases hcard with h | h <;> rw [h] at hmod <;> norm_num at hmod
  have hcF : ∀ w ∈ F, c w ∈ F := by
    intro w hw
    rw [hmem] at hw ⊢
    intro ν hν
    have hν' : c⁻¹ * ν * c ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) ν).mp hν
      simpa using this
    have h1 := hw _ hν'
    simp only [Equiv.Perm.mul_apply] at h1
    calc ν (c w) = c (c⁻¹ (ν (c w))) := by simp
      _ = c w := by rw [h1]
  have hpowF : ∀ k : ℕ, (c ^ k) z ∈ F := by
    intro k
    induction k with
    | zero => simpa using hzF
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hcF _ ih
  have hsF : ∀ w ∈ c.support, w ∈ F := by
    intro w hw
    obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (Equiv.Perm.mem_support.mp hzs)
      (Equiv.Perm.mem_support.mp hw)
    rw [← hi]
    exact hpowF i
  intro ν hν
  have hfixs : ∀ w ∈ c.support, ν w = w := fun w hw => (hmem w).mp (hsF w hw) ν hν
  have hνx : ν x = x ∨ ν x = y := by
    rcases hpts (ν x) with h | h | h
    · exfalso
      have hx' : ν x = x := ν.injective (hfixs _ h)
      rw [hx'] at h
      exact hxs h
    · exact Or.inl h
    · exact Or.inr h
  rcases hνx with h | h
  · have hy' : ν y = y := by
      have := hswap ν hν x
      rwa [Equiv.swap_apply_left, h, Equiv.swap_apply_left] at this
    ext w
    rcases hpts w with hw | rfl | rfl
    · rw [hfixs w hw, Equiv.Perm.one_apply]
    · rw [h, Equiv.Perm.one_apply]
    · rw [hy', Equiv.Perm.one_apply]
  · exfalso
    have hy' : ν y = x := by
      have := hswap ν hν x
      rwa [Equiv.swap_apply_left, h, Equiv.swap_apply_right] at this
    have hνs : ν = Equiv.swap x y := by
      ext w
      rcases hpts w with hw | rfl | rfl
      · rw [hfixs w hw, Equiv.swap_apply_of_ne_of_ne (fun h' : w = x => hxs (h' ▸ hw))
          (fun h' : w = y => hys (h' ▸ hw))]
      · rw [h, Equiv.swap_apply_left]
      · rw [hy', Equiv.swap_apply_right]
    have hs := hNs ν hν
    rw [hνs, Equiv.Perm.sign_swap hxy] at hs
    exact absurd hs (by decide)

variable {G : Type} [Group G]

theorem alt_commute_of_mem {J R M V : Subgroup G} (hR : R ≤ Subgroup.normalizer (J : Set G))
    (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 J) {n : ℕ}
    {α : ↥J →* alternatingGroup (Fin n)} (hker : α.ker = CFSG.pCore 2 ↥J) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (V : Set G)) {σ : Equiv.Perm (Fin n)}
    (hrel : ∀ (k : G) (hk : k ∈ J) (hk' : t * k * t⁻¹ ∈ J),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ J) V = autOn J V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V)))
    {a : G} (haM : a ∈ M ⊓ J) :
    ((α ⟨a, haM.2⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ =
      σ * ((α ⟨a, haM.2⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
  have haJ : a ∈ J := haM.2
  have haV : a ∈ Subgroup.normalizer (V : Set G) := hJV haJ
  have hmem : conjAct V ⟨a, haV⟩ ∈ autOn (M ⊓ J) V := SBc17.mem_autOn_iff.mpr ⟨a, haV, haM, rfl⟩
  rw [hMK] at hmem
  have hcomm : conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩ = conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩ :=
    Subgroup.mem_centralizer_iff.mp hmem.2 _ (SBc17.mem_autOn_iff.mpr ⟨t, htV, htR, rfl⟩)
  have hta : t * a⁻¹ * t⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hR htR) a⁻¹).mp (J.inv_mem haJ)
  have hw : a * (t * a⁻¹ * t⁻¹) ∈ J := J.mul_mem haJ hta
  have hw1 : SBc17.actOn hJV ⟨a * (t * a⁻¹ * t⁻¹), hw⟩ = 1 := by
    apply Subtype.ext
    show conjAct V ⟨a * (t * a⁻¹ * t⁻¹), hJV hw⟩ = 1
    have e : (⟨a * (t * a⁻¹ * t⁻¹), hJV hw⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨a, haV⟩ * (⟨t, htV⟩ * ⟨a, haV⟩⁻¹ * ⟨t, htV⟩⁻¹) := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc conjAct V ⟨a, haV⟩ * (conjAct V ⟨t, htV⟩ * (conjAct V ⟨a, haV⟩)⁻¹ *
          (conjAct V ⟨t, htV⟩)⁻¹) = (conjAct V ⟨a, haV⟩ * conjAct V ⟨t, htV⟩) *
            (conjAct V ⟨a, haV⟩)⁻¹ * (conjAct V ⟨t, htV⟩)⁻¹ := by group
      _ = (conjAct V ⟨t, htV⟩ * conjAct V ⟨a, haV⟩) * (conjAct V ⟨a, haV⟩)⁻¹ *
            (conjAct V ⟨t, htV⟩)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  have hwC := (SBc17.actOn_eq_one_iff hJV _).mp hw1
  have hwO : a * (t * a⁻¹ * t⁻¹) ∈ pCoreOf 2 J := hD ⟨hw, hwC⟩
  have hα1 : α ⟨a * (t * a⁻¹ * t⁻¹), hw⟩ = 1 :=
    (SBc17.map_eq_one_iff_mem_pCoreOf hker _).mpr hwO
  have hsplit : (⟨a * (t * a⁻¹ * t⁻¹), hw⟩ : ↥J) = ⟨a, haJ⟩ * ⟨t * a⁻¹ * t⁻¹, hta⟩ := rfl
  rw [hsplit, map_mul] at hα1
  have hrel' := hrel a⁻¹ (J.inv_mem haJ) hta
  have hinvα : (α ⟨a⁻¹, J.inv_mem haJ⟩ : alternatingGroup (Fin n)) = (α ⟨a, haJ⟩)⁻¹ := by
    have : (⟨a⁻¹, J.inv_mem haJ⟩ : ↥J) = (⟨a, haJ⟩ : ↥J)⁻¹ := rfl
    rw [this, map_inv]
  rw [hinvα] at hrel'
  set c : Equiv.Perm (Fin n) := (α ⟨a, haJ⟩ : Equiv.Perm (Fin n)) with hc
  have h1 : c * (σ * c⁻¹ * σ⁻¹) = 1 := by
    have := congrArg (fun z : alternatingGroup (Fin n) => (z : Equiv.Perm (Fin n))) hα1
    simpa [hc, hrel'] using this
  have : c * σ * c⁻¹ * σ⁻¹ = 1 := by
    calc c * σ * c⁻¹ * σ⁻¹ = c * (σ * c⁻¹ * σ⁻¹) := by group
      _ = 1 := h1
  exact commutatorElement_eq_one_iff_mul_comm.mp this

end CFSG.Quasithin.H13.KGBlk
