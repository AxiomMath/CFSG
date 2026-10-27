module

public import CFSG.Quasithin.Background.C1GNBlockLemmas

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace C1GN

theorem mem_evenWeight_three {x : Fin 3 → ZMod 2} : x ∈ evenWeight 3 ↔ x 0 + x 1 + x 2 = 0 := by
  simp [evenWeight, AddMonoidHom.mem_ker, Fin.sum_univ_three]

theorem alt3_four_cases (w0 w1 w2 y0 y1 y2 : ZMod 2) (hw : w0 + w1 + w2 = 0) (hy : y0 + y1 + y2 = 0)
    (hy0 : ¬ (y0 = 0 ∧ y1 = 0 ∧ y2 = 0)) :
    (w0 = 0 ∧ w1 = 0 ∧ w2 = 0) ∨ (w0 = y0 ∧ w1 = y1 ∧ w2 = y2) ∨
      (w0 = y2 ∧ w1 = y0 ∧ w2 = y1) ∨ (w0 = y1 ∧ w1 = y2 ∧ w2 = y0) := by
  revert w0 w1 w2 y0 y1 y2
  decide


theorem exists_alt3_hom {V : Type*} [Group V] (hcomm : ∀ a b : V, a * b = b * a)
    (hV2 : ∀ x : V, x ^ 2 = 1) (Z : Subgroup V)
    (σ : V ≃* V) (hσ3 : ∀ x : V, σ (σ (σ x)) = x) (hfix : ∀ x : V, σ x = x → x ∈ Z)
    (hZfix : ∀ z ∈ Z, σ z = z)
    (hZtop : Z < ⊤) (hirr : ∀ W : Subgroup V, Z ≤ W → (∀ w ∈ W, σ w ∈ W) → W = Z ∨ W = ⊤) :
    ∃ β : V →* Multiplicative (evenWeight 3), Function.Surjective β ∧ β.ker = Z ∧
      ∀ u : V, ∀ i : Fin 3, ((Multiplicative.toAdd (β (σ u)) : evenWeight 3) : Fin 3 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 3) : Fin 3 → ZMod 2) (i - 1) := by
  classical
  let _ : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  have h2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    show Additive.ofMul ((Additive.toMul x) ^ 2) = 0
    rw [hV2]
    rfl
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  let p : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup Z)
  have hp : ∀ a : Additive V, a ∈ p ↔ Additive.toMul a ∈ Z := fun a => Iff.rfl
  obtain ⟨x, hx⟩ : ∃ x : V, x ∉ Z := by
    by_contra h
    push Not at h
    exact hZtop.ne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨f, hfx, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := p)
    (x := Additive.ofMul x) (fun h => hx ((hp _).1 h)) inferInstance
  set F : V → ZMod 2 := fun v => f (Additive.ofMul v) with hF
  have hFmul : ∀ a b : V, F (a * b) = F a + F b := fun a b => by
    simp only [hF]; rw [ofMul_mul, map_add]
  have hFZ : ∀ z ∈ Z, F z = 0 := by
    intro z hz
    have : f (Additive.ofMul z) ∈ p.map f := Submodule.mem_map_of_mem ((hp _).2 hz)
    rw [hfp] at this
    exact (Submodule.mem_bot _).1 this
  have hFx : F x ≠ 0 := hfx
  have hF1 : F 1 = 0 := hFZ 1 Z.one_mem
  have hsymm : ∀ v, σ.symm v = σ (σ v) := fun v => by
    apply σ.injective
    rw [MulEquiv.apply_symm_apply, hσ3]
  have hsymm2 : ∀ v, σ.symm (σ.symm v) = σ v := fun v => by
    rw [hsymm v, MulEquiv.symm_apply_apply]
  have hc_mem : ∀ v : V, (![F v, F (σ.symm v), F (σ.symm (σ.symm v))] : Fin 3 → ZMod 2) ∈
      evenWeight 3 := by
    intro v
    rw [mem_evenWeight_three]
    show F v + F (σ.symm v) + F (σ.symm (σ.symm v)) = 0
    have hσn : σ (v * σ.symm v * σ.symm (σ.symm v)) = v * σ.symm v * σ.symm (σ.symm v) := by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hsymm2]
      ac_rfl
    have := hFZ _ (hfix _ hσn)
    rw [hFmul, hFmul] at this
    exact this
  let β : V →* Multiplicative (evenWeight 3) :=
    MonoidHom.mk' (fun v => Multiplicative.ofAdd
      (⟨![F v, F (σ.symm v), F (σ.symm (σ.symm v))], hc_mem v⟩ : evenWeight 3)) (by
        intro u v
        show Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
        congr 1
        apply Subtype.ext
        funext i
        fin_cases i <;> simp [hFmul, map_mul])
  have hβ : ∀ v : V, ∀ i : Fin 3,
      ((Multiplicative.toAdd (β v) : evenWeight 3) : Fin 3 → ZMod 2) i =
        ![F v, F (σ.symm v), F (σ.symm (σ.symm v))] i := fun v i => rfl
  have hequi : ∀ u : V, ∀ i : Fin 3,
      ((Multiplicative.toAdd (β (σ u)) : evenWeight 3) : Fin 3 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 3) : Fin 3 → ZMod 2) (i - 1) := by
    intro u i
    rw [hβ, hβ]
    fin_cases i
    · show F (σ u) = F (σ.symm (σ.symm u))
      rw [hsymm2]
    · show F (σ.symm (σ u)) = F u
      rw [MulEquiv.symm_apply_apply]
    · show F (σ.symm (σ.symm (σ u))) = F (σ.symm u)
      rw [MulEquiv.symm_apply_apply]
  have hker : β.ker = Z := by
    have hZK : Z ≤ β.ker := by
      intro z hz
      rw [MonoidHom.mem_ker]
      have h1 : σ.symm z = z := by
        rw [MulEquiv.symm_apply_eq]; exact (hZfix z hz).symm
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      rw [hβ]
      fin_cases i <;> simp [h1, hFZ z hz]
    have hinv : ∀ w ∈ β.ker, σ w ∈ β.ker := by
      intro w hw
      rw [MonoidHom.mem_ker] at hw ⊢
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      rw [hequi]
      have : (Multiplicative.toAdd (β w) : evenWeight 3) = 0 := by
        rw [hw]; rfl
      rw [this]
      rfl
    rcases hirr β.ker hZK hinv with h | h
    · exact h
    · exfalso
      have hxk : x ∈ β.ker := h ▸ Subgroup.mem_top x
      rw [MonoidHom.mem_ker] at hxk
      apply hFx
      have := congrArg (fun w : Multiplicative (evenWeight 3) =>
        ((Multiplicative.toAdd w : evenWeight 3) : Fin 3 → ZMod 2) 0) hxk
      simpa [hβ] using this
  refine ⟨β, ?_, hker, hequi⟩
  intro w
  set w' : Fin 3 → ZMod 2 := ((Multiplicative.toAdd w : evenWeight 3) : Fin 3 → ZMod 2) with hw'
  have hwmem : w' ∈ evenWeight 3 := (Multiplicative.toAdd w).2
  rw [mem_evenWeight_three] at hwmem
  have hymem := hc_mem x
  rw [mem_evenWeight_three] at hymem
  have hy0 : ¬ (F x = 0 ∧ F (σ.symm x) = 0 ∧ F (σ.symm (σ.symm x)) = 0) := fun h => hFx h.1
  have key := alt3_four_cases (w' 0) (w' 1) (w' 2) (F x) (F (σ.symm x)) (F (σ.symm (σ.symm x)))
    hwmem hymem hy0
  have hext : ∀ u : V, (∀ i : Fin 3, w' i = ((Multiplicative.toAdd (β u) : evenWeight 3) :
      Fin 3 → ZMod 2) i) → β u = w := by
    intro u hu
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact (hu i).symm
  rcases key with ⟨h0, h1, h2'⟩ | ⟨h0, h1, h2'⟩ | ⟨h0, h1, h2'⟩ | ⟨h0, h1, h2'⟩
  · refine ⟨1, hext 1 ?_⟩
    intro i
    rw [hβ]
    fin_cases i
    · simpa [hF1] using h0
    · simpa [hF1] using h1
    · simpa [hF1] using h2'
  · refine ⟨x, hext x ?_⟩
    intro i
    rw [hβ]
    fin_cases i
    · exact h0
    · exact h1
    · exact h2'
  · refine ⟨σ x, hext (σ x) ?_⟩
    intro i
    rw [hequi]
    fin_cases i
    · show w' 0 = F (σ.symm (σ.symm x)); exact h0
    · show w' 1 = F x; exact h1
    · show w' 2 = F (σ.symm x); exact h2'
  · refine ⟨σ (σ x), hext (σ (σ x)) ?_⟩
    intro i
    rw [hequi, hequi]
    fin_cases i
    · show w' 0 = F (σ.symm x); exact h0
    · show w' 1 = F (σ.symm (σ.symm x)); exact h1
    · show w' 2 = F x; exact h2'

variable {G : Type} [Group G]

theorem alt3_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem finRotate_three_mem : finRotate 3 ∈ alternatingGroup (Fin 3) := by
  rw [Equiv.Perm.mem_alternatingGroup, sign_finRotate]
  norm_num

theorem finRotate_three_inv_apply (i : Fin 3) : (finRotate 3)⁻¹ i = i - 1 := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, finRotate_apply]
  simp

theorem le_normalizer_blockU' (L : Subgroup G) :
    L ≤ Subgroup.normalizer (blockU L : Set G) := by
  unfold blockU blockQ
  rw [Subgroup.commutator_comm]
  exact A3.le_normalizer_commutator_left L (pCoreOf 2 L)

theorem commute_of_mem_pCore {L : Subgroup G} (hL : IsShort2 L) {q : ↥L}
    (hq : q ∈ CFSG.pCore 2 ↥L) {u : G} (hu : u ∈ blockU L) : (q : G) * u = u * (q : G) := by
  have hqQ : (q : G) ∈ blockQ L := ⟨q, by assumption, rfl⟩
  exact (Subgroup.mem_centralizer_iff.1 (hL.2.2.1.1 hu).2) (q : G) hqQ


theorem isAltType_three_of_isAltQuotient {L C : Subgroup G} (hL : IsShort2 L)
    (hq : IsAltQuotient L C 3) : IsAltType L 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnotLC : ¬ L ≤ C := not_le_of_isAltQuotient hq (le_refl 3)
  obtain ⟨φ, hφs, hφk⟩ := hq
  have hcard3 := alt3_card
  have hpc : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x, hx⟩
    have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [MonoidHom.mem_ker]
    have h1 : (φ x) ^ 2 ^ k = 1 := by rw [← map_pow, hxk, map_one]
    have h2 : (φ x) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := alternatingGroup (Fin 3)) (x := φ x)
      rwa [hcard3] at this
    have h3 : orderOf (φ x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have h4 : orderOf (φ x) ∣ 3 := orderOf_dvd_of_pow_eq_one h2
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have : orderOf (φ x) = 1 := Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h4)
    exact orderOf_eq_one_iff.1 this
  have hkle : φ.ker ≤ CFSG.pCore 2 ↥L := by
    rcases hL.2.2.2.1 with hQ | h3
    · exfalso
      have hperf : ⁅L, L⁆ = L := isShort2_perfect_of_perfect_quotient hL hQ.1.commutator_eq_top
      have hL' : commutator ↥L = ⊤ := (Subgroup.isPerfect_iff.2 hperf).commutator_eq_top
      have hcomm3 : ∀ a b : alternatingGroup (Fin 3), a * b = b * a := by decide
      have hle : commutator ↥L ≤ φ.ker := by
        rw [_root_.commutator_def]
        refine Subgroup.commutator_le.2 fun a _ b _ => ?_
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm3 _ _)
      rw [hL', top_le_iff] at hle
      apply hnotLC
      rw [hφk] at hle
      exact Subgroup.subgroupOf_eq_top.1 hle
    · have hidx : φ.ker.index = 3 := by
        rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top, hcard3]
      have h1 := Subgroup.relIndex_mul_index hpc
      have h3' : (CFSG.pCore 2 ↥L).index = 3 := h3
      rw [hidx, h3'] at h1
      have h4 : (CFSG.pCore 2 ↥L).relIndex φ.ker = 1 := by omega
      exact Subgroup.relIndex_eq_one.1 h4
  have hker : φ.ker = CFSG.pCore 2 ↥L := le_antisymm hkle hpc
  have hUQ := hL.2.2.1
  have hcentU : ∀ q ∈ CFSG.pCore 2 ↥L, ∀ u ∈ blockU L, (q : G) * u = u * (q : G) :=
    fun q hq u hu => commute_of_mem_pCore hL hq hu
  have hLU := le_normalizer_blockU' L
  let c : alternatingGroup (Fin 3) := ⟨finRotate 3, finRotate_three_mem⟩
  have hc1 : c ≠ 1 := by
    intro h
    have h' : (finRotate 3 : Equiv.Perm (Fin 3)) = 1 := congrArg Subtype.val h
    have := congrArg (fun p : Equiv.Perm (Fin 3) => p 0) h'
    simp only [finRotate_apply, Equiv.Perm.coe_one, id_eq] at this
    exact absurd this (by decide)
  obtain ⟨ℓ₀, hℓ₀⟩ := hφs c
  have hℓ₀N : (ℓ₀ : G) ∈ Subgroup.normalizer (blockU L : Set G) := hLU ℓ₀.2
  let σ : ↥(blockU L) ≃* ↥(blockU L) := (blockU L).normalizerMonoidHom ⟨ℓ₀, hℓ₀N⟩
  have hσ : ∀ u : ↥(blockU L), ((σ u : ↥(blockU L)) : G) = (ℓ₀ : G) * u * (ℓ₀ : G)⁻¹ := fun u =>
    (blockU L).normalizerMonoidHom_apply_apply_coe ⟨ℓ₀, hℓ₀N⟩ u
  have hgen : ∀ ℓ : ↥L, ℓ ∈ Subgroup.closure ((φ.ker : Set ↥L) ∪ {ℓ₀}) := by
    intro ℓ
    have hzp : Subgroup.zpowers c = ⊤ := zpowers_eq_top_of_prime_card hcard3 hc1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
      (show φ ℓ ∈ Subgroup.zpowers c by rw [hzp]; exact Subgroup.mem_top _)
    have h1 : ℓ = ℓ₀ ^ k * (ℓ₀ ^ (-k) * ℓ) := by group
    have h2 : ℓ₀ ^ (-k) * ℓ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hℓ₀, zpow_neg, hk, inv_mul_cancel]
    have hg0 : ℓ₀ ∈ Subgroup.closure ((φ.ker : Set ↥L) ∪ {ℓ₀}) :=
      Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton ℓ₀))
    have hg1 : ℓ₀ ^ (-k) * ℓ ∈ Subgroup.closure ((φ.ker : Set ↥L) ∪ {ℓ₀}) :=
      Subgroup.subset_closure (Set.mem_union_left _ h2)
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hg0 k) hg1
  have hLle : ∀ K' : Subgroup G, (∀ q ∈ CFSG.pCore 2 ↥L, (q : G) ∈ K') → (ℓ₀ : G) ∈ K' →
      L ≤ K' := by
    intro K' hq h0 ℓ hℓ
    have hle : Subgroup.closure ((φ.ker : Set ↥L) ∪ {ℓ₀}) ≤ K'.comap L.subtype := by
      rw [Subgroup.closure_le]
      rintro y (hy | hy)
      · have hy' : y ∈ φ.ker := hy
        rw [hker] at hy'
        exact hq y hy'
      · rw [Set.mem_singleton_iff.1 hy]; exact h0
    exact hle (hgen ⟨ℓ, hℓ⟩)
  have hcommU : ∀ a b : ↥(blockU L), a * b = b * a := by
    intro a b
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 (hUQ.1 b.2).2) (a : G) (hUQ.1 a.2).1
  have hV2 : ∀ x : ↥(blockU L), x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hUQ.2 x x.2)
  have hσ3 : ∀ x : ↥(blockU L), σ (σ (σ x)) = x := by
    intro x
    apply Subtype.ext
    have hℓ3 : ℓ₀ * ℓ₀ * ℓ₀ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, hℓ₀]
      have := pow_card_eq_one' (G := alternatingGroup (Fin 3)) (x := c)
      rw [hcard3, pow_three'] at this
      exact this
    have hp3 : ((ℓ₀ * ℓ₀ * ℓ₀ : ↥L) : G) * x = x * ((ℓ₀ * ℓ₀ * ℓ₀ : ↥L) : G) :=
      hcentU _ (hker ▸ hℓ3) x x.2
    simp only [Subgroup.coe_mul] at hp3
    rw [hσ, hσ, hσ]
    calc (ℓ₀ : G) * ((ℓ₀ : G) * ((ℓ₀ : G) * x * (ℓ₀ : G)⁻¹) * (ℓ₀ : G)⁻¹) * (ℓ₀ : G)⁻¹
        = ((ℓ₀ : G) * (ℓ₀ : G) * (ℓ₀ : G)) * x * ((ℓ₀ : G)⁻¹ * (ℓ₀ : G)⁻¹ * (ℓ₀ : G)⁻¹) := by
          simp only [mul_assoc]
      _ = x * ((ℓ₀ : G) * (ℓ₀ : G) * (ℓ₀ : G)) * ((ℓ₀ : G)⁻¹ * (ℓ₀ : G)⁻¹ * (ℓ₀ : G)⁻¹) := by
          rw [hp3]
      _ = x := by group
  have hfix : ∀ x : ↥(blockU L), σ x = x → x ∈ (blockZ L).subgroupOf (blockU L) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    have hxc : (ℓ₀ : G) * x = x * (ℓ₀ : G) := by
      have := congrArg (fun y : ↥(blockU L) => (y : G)) hx
      simp only [hσ] at this
      calc (ℓ₀ : G) * x = ((ℓ₀ : G) * x * (ℓ₀ : G)⁻¹) * (ℓ₀ : G) := by group
        _ = x * (ℓ₀ : G) := by rw [this]
    have hLc : L ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
      apply hLle
      · intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hcentU q hq x x.2).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hxc.symm
    intro ℓ hℓ
    exact (Subgroup.mem_centralizer_iff.1 (hLc hℓ) (x : G) rfl).symm
  have hZfix : ∀ z ∈ (blockZ L).subgroupOf (blockU L), σ z = z := by
    intro z hz
    apply Subtype.ext
    rw [hσ]
    have hzc : (z : G) ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_subgroupOf.1 hz).2
    have := Subgroup.mem_centralizer_iff.1 hzc (ℓ₀ : G) ℓ₀.2
    calc (ℓ₀ : G) * z * (ℓ₀ : G)⁻¹ = z * (ℓ₀ : G) * (ℓ₀ : G)⁻¹ := by rw [this]
      _ = z := by group
  have hZtop : (blockZ L).subgroupOf (blockU L) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact not_le_of_gt hL.2.2.2.2.1
  have hirr : ∀ W : Subgroup ↥(blockU L), (blockZ L).subgroupOf (blockU L) ≤ W →
      (∀ w ∈ W, σ w ∈ W) → W = (blockZ L).subgroupOf (blockU L) ∨ W = ⊤ := by
    intro W hZW hWσ
    set W' : Subgroup G := W.map (blockU L).subtype
    have hW'U : W' ≤ blockU L := Subgroup.map_subtype_le W
    have hZW' : blockZ L ≤ W' := by
      intro z hz
      exact ⟨⟨z, hz.1⟩, hZW (Subgroup.mem_subgroupOf.2 hz), rfl⟩
    have hmemW' : ∀ g : G, g ∈ W' ↔ ∃ w : ↥(blockU L), w ∈ W ∧ (w : G) = g :=
      fun g => Subgroup.mem_map
    have hnorm : L ≤ Subgroup.normalizer (W' : Set G) := by
      apply hLle
      · intro q hq
        rw [Subgroup.mem_normalizer_iff]
        intro h
        have hc' : ∀ w ∈ blockU L, (q : G) * w * (q : G)⁻¹ = w := fun w hw => by
          rw [hcentU q hq w hw]; group
        have hc : ∀ w ∈ W', (q : G) * w * (q : G)⁻¹ = w := fun w hw => hc' w (hW'U hw)
        constructor
        · intro hh
          rw [hc h hh]; exact hh
        · intro hh
          have hhU : h ∈ blockU L :=
            (Subgroup.mem_normalizer_iff.1 (hLU q.2) h).2 (hW'U hh)
          rw [hc' h hhU] at hh
          exact hh
      · rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · intro hh
          obtain ⟨w, hw, rfl⟩ := (hmemW' h).1 hh
          exact (hmemW' _).2 ⟨σ w, hWσ w hw, hσ w⟩
        · intro hh
          have hhU : h ∈ blockU L := (Subgroup.mem_normalizer_iff.1 hℓ₀N h).2 (hW'U hh)
          let w₁ : ↥(blockU L) := ⟨h, hhU⟩
          obtain ⟨w, hw, hwe⟩ := (hmemW' _).1 hh
          have hσw : σ w₁ = w := Subtype.ext (by rw [hσ]; exact hwe.symm)
          have hw₁ : w₁ ∈ W := by
            have := hWσ (σ w₁) (hσw ▸ hw)
            have := hWσ _ this
            rwa [hσ3] at this
          exact (hmemW' h).2 ⟨w₁, hw₁, rfl⟩
    rcases hL.2.2.2.2.2 W' hZW' hW'U hnorm with h | h
    · left
      calc W = W'.comap (blockU L).subtype :=
            (Subgroup.comap_map_eq_self_of_injective (blockU L).subtype_injective W).symm
        _ = (blockZ L).subgroupOf (blockU L) :=
            congrArg (fun K : Subgroup G => K.comap (blockU L).subtype) h
    · right
      calc W = W'.comap (blockU L).subtype :=
            (Subgroup.comap_map_eq_self_of_injective (blockU L).subtype_injective W).symm
        _ = (blockU L).subgroupOf (blockU L) :=
            congrArg (fun K : Subgroup G => K.comap (blockU L).subtype) h
        _ = ⊤ := Subgroup.subgroupOf_self _
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_alt3_hom hcommU hV2 ((blockZ L).subgroupOf (blockU L)) σ
    hσ3 hfix hZfix hZtop hirr
  have hc_val : ((c : alternatingGroup (Fin 3)) : Equiv.Perm (Fin 3)) = finRotate 3 := rfl
  have hP : ∀ ℓ : ↥L, ∀ u v : ↥(blockU L), (v : G) = (ℓ : G) * u * (ℓ : G)⁻¹ → ∀ i : Fin 3,
      ((Multiplicative.toAdd (β v) : evenWeight 3) : Fin 3 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 3) : Fin 3 → ZMod 2)
          ((((φ ℓ : alternatingGroup (Fin 3)) : Equiv.Perm (Fin 3)))⁻¹ i) := by
    intro ℓ
    have hmem := hgen ℓ
    induction hmem using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · intro u v huv i
        have hxk : x ∈ φ.ker := hx
        have hφx : φ x = 1 := hxk
        have hxp : x ∈ CFSG.pCore 2 ↥L := hker ▸ hxk
        have hvu : v = u := by
          apply Subtype.ext
          rw [huv, hcentU x hxp u u.2]
          group
        rw [hvu, hφx]
        simp
      · intro u v huv i
        have hx' : x = ℓ₀ := hx
        rw [hx'] at huv ⊢
        have hvu : v = σ u := Subtype.ext (by rw [huv, hσ])
        rw [hvu, hβe, hℓ₀, hc_val, finRotate_three_inv_apply]
    | one =>
      intro u v huv i
      have hvu : v = u := Subtype.ext (by simpa using huv)
      rw [hvu]
      simp
    | mul x y _ _ ihx ihy =>
      intro u v huv i
      have hu' : (y : G) * u * (y : G)⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.1 (hLU y.2) (u : G)).1 u.2
      let u' : ↥(blockU L) := ⟨(y : G) * u * (y : G)⁻¹, hu'⟩
      have hu'e : (u' : G) = (y : G) * u * (y : G)⁻¹ := rfl
      have hv : (v : G) = (x : G) * u' * (x : G)⁻¹ := by
        rw [huv, hu'e]
        simp only [Subgroup.coe_mul]
        group
      have h1 := ihx u' v hv i
      have h2 := ihy u u' hu'e ((φ x : Equiv.Perm (Fin 3))⁻¹ i)
      rw [h1, h2]
      simp [map_mul, mul_inv_rev, Equiv.Perm.mul_apply]
    | inv x _ ih =>
      intro u v huv i
      have hv' : (u : G) = (x : G) * v * (x : G)⁻¹ := by
        rw [huv]
        simp only [InvMemClass.coe_inv, inv_inv]
        group
      have := ih v u hv' ((φ x : Equiv.Perm (Fin 3)) i)
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
      rw [← this]
      simp
  exact ⟨φ, hφs, hker, β, hβs, hβk, hP⟩

end C1GN

end CFSG.Quasithin
