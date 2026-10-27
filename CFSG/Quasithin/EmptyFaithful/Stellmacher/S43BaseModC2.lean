module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecOrthNat
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.IrredClassification
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseDict

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

private theorem S5SylF_fix : ∀ σ ∈ S5SylF, σ 4 = 4 := by decide +kernel

private theorem S5SylF_trans : ∀ q : Fin 5, q ≠ 4 → ∀ j : Fin 5, j ≠ 4 →
    ∃ d ∈ S5SylF, d q = j := by decide +kernel

theorem S5Syl_le_stab_four : S5Syl ≤ MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5) :=
  fun σ hσ => (MulAction.mem_stabilizer_iff).mpr (S5SylF_fix σ ((mem_S5Syl_iff σ).mp hσ))

theorem le_stab_four_or_eq_top {K : Subgroup (Perm (Fin 5))} (hK : S5Syl ≤ K) :
    K ≤ MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5) ∨ K = ⊤ := by
  by_cases h : K ≤ MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)
  · exact Or.inl h
  · refine Or.inr (F53.F5b_core S5Syl K card_S5Syl 4 (fun q j hq hj => ?_) hK h)
    obtain ⟨d, hd, hdq⟩ := S5SylF_trans q hq j hj
    exact ⟨d, (mem_S5Syl_iff d).mpr hd, hdq⟩

section Rank

variable {G : Type} [Group G]

theorem secIdx_eq_one_iff {L N : Subgroup G} {x : G} (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    secIdx (Subgroup.zpowers x) L N = 1 ↔ ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ L := by
  unfold secIdx
  rw [Subgroup.relIndex_eq_one]
  constructor
  · intro h y hy
    exact ((mem_fixSecIn_zpowers_iff hNL hx).mp (h hy)).2
  · intro h y hy
    exact (mem_fixSecIn_zpowers_iff hNL hx).mpr ⟨hy, h y hy⟩

theorem secIdx_pos [Finite G] (A L N : Subgroup G) : 0 < secIdx A L N :=
  Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)

theorem secIdx_bot (W : Subgroup G) (x : G) :
    secIdx (Subgroup.zpowers x) ⊥ W = (W ⊓ Subgroup.centralizer ({x} : Set G)).relIndex W := by
  have hn : ∀ g : G, g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  have e : fixSecIn (Subgroup.zpowers x) ⊥ W = W ⊓ Subgroup.centralizer ({x} : Set G) := by
    ext y
    rw [mem_fixSecIn_zpowers_iff (fun g _ => hn g) (hn x), Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    refine and_congr_right fun _ => ?_
    simp only [Subgroup.mem_bot, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have : x * y = y * x := by
        have h1 : x * y * x⁻¹ = y := by
          have := mul_inv_eq_one.mp h
          simpa [mul_assoc] using this
        calc x * y = x * y * x⁻¹ * x := by group
          _ = y * x := by rw [h1]
      exact this
    · intro h
      rw [h]
      group
  unfold secIdx
  rw [e]

theorem secIdx_mul_le [Finite G] {L N₁ N : Subgroup G} {x : G} (hL : L ≤ N₁) (h1 : N₁ ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hNN : N ≤ Subgroup.normalizer (N₁ : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxN : x ∈ Subgroup.normalizer (N₁ : Set G)) :
    secIdx (Subgroup.zpowers x) L N₁ * secIdx (Subgroup.zpowers x) N₁ N ≤
      secIdx (Subgroup.zpowers x) L N := by
  have hN₁L : N₁ ≤ Subgroup.normalizer (L : Set G) := h1.trans hNL
  have hF : ∀ y, y ∈ fixSecIn (Subgroup.zpowers x) L N ↔ y ∈ N ∧ x * y * x⁻¹ * y⁻¹ ∈ L :=
    fun y => mem_fixSecIn_zpowers_iff hNL hxL
  have hF₂ : ∀ y, y ∈ fixSecIn (Subgroup.zpowers x) N₁ N ↔ y ∈ N ∧ x * y * x⁻¹ * y⁻¹ ∈ N₁ :=
    fun y => mem_fixSecIn_zpowers_iff hNN hxN
  have hF₁ : ∀ y, y ∈ fixSecIn (Subgroup.zpowers x) L N₁ ↔ y ∈ N₁ ∧ x * y * x⁻¹ * y⁻¹ ∈ L :=
    fun y => mem_fixSecIn_zpowers_iff hN₁L hxL
  have hFF₂ : fixSecIn (Subgroup.zpowers x) L N ≤ fixSecIn (Subgroup.zpowers x) N₁ N := fun y hy =>
    (hF₂ y).mpr ⟨((hF y).mp hy).1, hL ((hF y).mp hy).2⟩
  have hN₁F₂ : N₁ ≤ fixSecIn (Subgroup.zpowers x) N₁ N := fun y hy => by
    refine (hF₂ y).mpr ⟨h1 hy, ?_⟩
    exact N₁.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN y).mp hy) (N₁.inv_mem hy)
  have hF₂N : fixSecIn (Subgroup.zpowers x) N₁ N ≤ N := fun y hy => ((hF₂ y).mp hy).1
  have hinf : fixSecIn (Subgroup.zpowers x) L N ⊓ N₁ = fixSecIn (Subgroup.zpowers x) L N₁ := by
    ext y
    rw [Subgroup.mem_inf, hF, hF₁]
    exact ⟨fun ⟨⟨_, h⟩, h'⟩ => ⟨h', h⟩, fun ⟨h', h⟩ => ⟨⟨h1 h', h⟩, h'⟩⟩
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hFF₂ hF₂N
  have hle : (fixSecIn (Subgroup.zpowers x) L N).relIndex N₁ ≤
      (fixSecIn (Subgroup.zpowers x) L N).relIndex (fixSecIn (Subgroup.zpowers x) N₁ N) :=
    Subgroup.relIndex_le_of_le_right hN₁F₂ Subgroup.index_ne_zero_of_finite
  have e1 : secIdx (Subgroup.zpowers x) L N₁ =
      (fixSecIn (Subgroup.zpowers x) L N).relIndex N₁ := by
    unfold secIdx
    rw [← hinf, Subgroup.inf_relIndex_right]
  unfold secIdx at e1 ⊢
  rw [e1, ← hmul]
  exact Nat.mul_le_mul_right _ hle

theorem prod_le_two {f : ℕ → ℕ} {r : ℕ} (hpos : ∀ i, 0 < f i)
    (hprod : ∏ i ∈ Finset.range r, f i ≤ 2) :
    (∀ i, i < r → f i = 1 ∨ f i = 2) ∧ ∀ i j, i < r → j < r → i ≠ j → f i = 1 ∨ f j = 1 := by
  have hone : ∀ s : Finset ℕ, s ⊆ Finset.range r → ∏ i ∈ s, f i ≤ 2 := fun s hs =>
    (Finset.prod_le_prod_of_subset_of_one_le hs fun i _ _ => hpos i).trans hprod
  refine ⟨fun i hi => ?_, fun i j hi hj hij => ?_⟩
  · have h1 := hone {i} (by simpa using hi)
    rw [Finset.prod_singleton] at h1
    have := hpos i
    omega
  · have h1 := hone {i, j} (by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simpa)
    rw [Finset.prod_pair hij] at h1
    have := hpos i
    have := hpos j
    by_contra hcon
    push Not at hcon
    have h3 : 2 ≤ f i := by omega
    have h4 : 2 ≤ f j := by omega
    nlinarith

theorem secIdx_prod_le [Finite G] {W : ℕ → Subgroup G} {x : G} {r : ℕ}
    (hchain : ∀ i j, i ≤ j → j ≤ r → W i ≤ W j)
    (hnorm : ∀ i j, i ≤ r → j ≤ r → W j ≤ Subgroup.normalizer (W i : Set G))
    (hx : ∀ i, i ≤ r → x ∈ Subgroup.normalizer (W i : Set G)) :
    ∏ i ∈ Finset.range r, secIdx (Subgroup.zpowers x) (W i) (W (i + 1)) ≤
      secIdx (Subgroup.zpowers x) (W 0) (W r) := by
  suffices h : ∀ k, k ≤ r → ∏ i ∈ Finset.range k, secIdx (Subgroup.zpowers x) (W i) (W (i + 1)) ≤
      secIdx (Subgroup.zpowers x) (W 0) (W k) from h r le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    rw [Finset.range_zero, Finset.prod_empty]
    exact secIdx_pos (Subgroup.zpowers x) (W 0) (W 0)
  | succ k ih =>
    intro hk
    rw [Finset.prod_range_succ]
    calc _ ≤ secIdx (Subgroup.zpowers x) (W 0) (W k) *
          secIdx (Subgroup.zpowers x) (W k) (W (k + 1)) :=
          Nat.mul_le_mul_right _ (ih (by omega))
      _ ≤ _ := secIdx_mul_le (hchain 0 k (by omega) (by omega)) (hchain k (k + 1) (by omega) hk)
          (hnorm 0 (k + 1) (by omega) hk) (hnorm k (k + 1) (by omega) hk)
          (hx 0 (by omega)) (hx k (by omega))

theorem secIdx_chain_of_le_two [Finite G] {W : ℕ → Subgroup G} {x : G} {r : ℕ}
    (hchain : ∀ i j, i ≤ j → j ≤ r → W i ≤ W j)
    (hnorm : ∀ i j, i ≤ r → j ≤ r → W j ≤ Subgroup.normalizer (W i : Set G))
    (hx : ∀ i, i ≤ r → x ∈ Subgroup.normalizer (W i : Set G))
    (h2 : secIdx (Subgroup.zpowers x) (W 0) (W r) ≤ 2) :
    (∀ i, i < r → secIdx (Subgroup.zpowers x) (W i) (W (i + 1)) = 1 ∨
      secIdx (Subgroup.zpowers x) (W i) (W (i + 1)) = 2) ∧
    ∀ i j, i < r → j < r → i ≠ j →
      secIdx (Subgroup.zpowers x) (W i) (W (i + 1)) = 1 ∨
        secIdx (Subgroup.zpowers x) (W j) (W (j + 1)) = 1 := by
  have hprod := (secIdx_prod_le hchain hnorm hx).trans h2
  exact prod_le_two (f := fun i => secIdx (Subgroup.zpowers x) (W i) (W (i + 1)))
    (fun i => secIdx_pos _ _ _) hprod

end Rank

section Comm

variable {G : Type} [Group G]

theorem commutator_zpowers_le {N R : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (R : Set G))
    (h : ∀ n ∈ N, ⁅n, x⁆ ∈ R) : ⁅N, Subgroup.zpowers x⁆ ≤ R := by
  let T : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (R : Set G) ∧ ∀ n ∈ N, ⁅n, g⁆ ∈ R}
      one_mem' := ⟨Subgroup.one_mem _, fun n _ => by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro g k ⟨hg, hg'⟩ ⟨hk, hk'⟩
        refine ⟨Subgroup.mul_mem _ hg hk, fun n hn => ?_⟩
        have e : ⁅n, g * k⁆ = ⁅n, g⁆ * (g * ⁅n, k⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact R.mul_mem (hg' n hn) ((Subgroup.mem_normalizer_iff.mp hg _).mp (hk' n hn))
      inv_mem' := by
        rintro g ⟨hg, hg'⟩
        refine ⟨Subgroup.inv_mem _ hg, fun n hn => ?_⟩
        have e : ⁅n, g⁻¹⁆ = g⁻¹ * ⁅n, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp (R.inv_mem (hg' n hn)) }
  have hz : Subgroup.zpowers x ≤ T := Subgroup.zpowers_le.mpr ⟨hx, h⟩
  rw [Subgroup.commutator_le]
  intro n hn g hg
  exact (hz hg).2 n hn

theorem commutator_zpowers_le_self {W : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) : ⁅W, Subgroup.zpowers x⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro w hw g hg
  have hg' : g ∈ Subgroup.normalizer (W : Set G) := (Subgroup.zpowers_le.mpr hx) hg
  have h1 : g * w⁻¹ * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hg' _).mp (W.inv_mem hw)
  have : ⁅w, g⁆ = w * (g * w⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact W.mul_mem hw h1

theorem card_commutator_zpowers {W : Subgroup G} {x : G}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hx : x ∈ Subgroup.normalizer (W : Set G)) :
    Nat.card (⁅W, Subgroup.zpowers x⁆ : Subgroup G) =
      (W ⊓ Subgroup.centralizer ({x} : Set G)).relIndex W := by
  have hc : ∀ w ∈ W, x * w * x⁻¹ ∈ W := fun w hw => (Subgroup.mem_normalizer_iff.mp hx w).mp hw
  have hc' : ∀ w ∈ W, x⁻¹ * w * x ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * w * x)).mpr (by simpa [mul_assoc] using hw)
  have hmem : ∀ w : ↥W, ⁅(w : G), x⁆ ∈ W := fun w => by
    have : ⁅(w : G), x⁆ = w * (x * (w : G)⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact W.mul_mem w.2 (hc _ (W.inv_mem w.2))
  let f : ↥W →* ↥W := MonoidHom.mk' (fun w => ⟨⁅(w : G), x⁆, hmem w⟩) (fun a b => by
    apply Subtype.ext
    have hA' : x * (a : G)⁻¹ * x⁻¹ ∈ W := hc _ (W.inv_mem a.2)
    have hB' : x * (b : G)⁻¹ * x⁻¹ ∈ W := hc _ (W.inv_mem b.2)
    have e1 : ⁅((a * b : ↥W) : G), x⁆ = (a : G) * (b : G) * (x * (b : G)⁻¹ * x⁻¹) *
        (x * (a : G)⁻¹ * x⁻¹) := by
      simp only [Subgroup.coe_mul, commutatorElement_def]; group
    have e2 : ⁅(a : G), x⁆ * ⁅(b : G), x⁆ = (a : G) * (x * (a : G)⁻¹ * x⁻¹) *
        ((b : G) * (x * (b : G)⁻¹ * x⁻¹)) := by
      simp only [commutatorElement_def]; group
    show ⁅((a * b : ↥W) : G), x⁆ = ⁅(a : G), x⁆ * ⁅(b : G), x⁆
    rw [e1, e2]
    have h3 := hW _ (W.mul_mem b.2 hB') _ hA'
    calc (a : G) * b * (x * (b : G)⁻¹ * x⁻¹) * (x * (a : G)⁻¹ * x⁻¹)
        = a * ((b * (x * (b : G)⁻¹ * x⁻¹)) * (x * (a : G)⁻¹ * x⁻¹)) := by group
      _ = a * ((x * (a : G)⁻¹ * x⁻¹) * (b * (x * (b : G)⁻¹ * x⁻¹))) := by rw [h3]
      _ = _ := by group)
  have hker : f.ker = (W ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      have h1 : ⁅(w : G), x⁆ = 1 := congrArg Subtype.val h
      have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
      exact ⟨w.2, fun h hh => by rw [Set.mem_singleton_iff] at hh; subst hh; exact h2.symm⟩
    · rintro ⟨-, h⟩
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr (h x rfl).symm
  have hrange : (⁅W, Subgroup.zpowers x⁆ : Subgroup G) = f.range.map W.subtype := by
    apply le_antisymm
    · refine commutator_zpowers_le ?_ fun n hn => ⟨f ⟨n, hn⟩, ⟨_, rfl⟩, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        refine ⟨f ⟨x * (w : G) * x⁻¹, hc _ w.2⟩, ⟨_, rfl⟩, ?_⟩
        show ⁅x * (w : G) * x⁻¹, x⁆ = x * ⁅(w : G), x⁆ * x⁻¹
        simp only [commutatorElement_def]; group
      · rintro ⟨_, ⟨w, rfl⟩, hw⟩
        refine ⟨f ⟨x⁻¹ * (w : G) * x, hc' _ w.2⟩, ⟨_, rfl⟩, ?_⟩
        have hw' : ⁅(w : G), x⁆ = x * r * x⁻¹ := hw
        show ⁅x⁻¹ * (w : G) * x, x⁆ = r
        have : ⁅x⁻¹ * (w : G) * x, x⁆ = x⁻¹ * ⁅(w : G), x⁆ * x := by
          simp only [commutatorElement_def]; group
        rw [this, hw']
        group
    · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact Subgroup.commutator_mem_commutator w.2 (Subgroup.mem_zpowers x)
  rw [hrange, Subgroup.card_map_of_injective W.subtype_injective, ← Subgroup.index_ker, hker]
  rfl

theorem relIndex_sup_eq_of_le_normalizer {A N : Subgroup G}
    (h : A ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (A ⊔ N) = N.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A N h).toEquiv.symm

end Comm

namespace Dict5

variable {G : Type} [Group G] {X S Z : Subgroup G} (D : Dict5 X S Z)

theorem relIndex_centralizer_eq_two_iff (s : ↥X) :
    (Z ⊓ Subgroup.centralizer ({(s : G)} : Set G)).relIndex Z = 2 ↔ (D.ψ s).IsSwap := by
  rw [D.relIndex_centralizer_eq s]
  by_cases h1 : D.ψ s = 1
  · rw [h1, idx_orth]
    simp only [↓reduceIte]
    constructor
    · intro h; omega
    · rintro ⟨x, y, hxy, h⟩
      have := congrArg (fun f => f x) h
      simp at this
      exact absurd this hxy
  · exact (transvections _ h1).2

end Dict5

section Chief

variable {G : Type} [Group G] [Finite G]

theorem commutator_pCoreOf_mem {X U L N : Subgroup G} (hU : U ≤ pCoreOf 2 X)
    (hstep : IsChiefStep X U L N) :
    ∀ q ∈ pCoreOf 2 X, ∀ y ∈ N, q * y * q⁻¹ * y⁻¹ ∈ L := by
  intro q hq y hy
  have h := pCoreOf_le_cSecIn_of_chiefStep (hU.trans (pCoreOf_le 2 X)) hU hstep hq
  exact ((mem_cSecIn_iff (normalizer_left hstep)).mp h).2 y hy

omit [Finite G] in
theorem IsModelSec.exists_secIdx {n : ℕ} {M : Model n} {F L N : Subgroup G}
    (h : IsModelSec M F L N) (hLN : L ≤ N) :
    ∃ θ : ↥F →* Perm (Fin n), Function.Surjective θ ∧ θ.ker = (cSecIn F L N).subgroupOf F ∧
      ∀ (a : G) (ha : a ∈ F), secIdx (Subgroup.zpowers a) L N = idx M (θ ⟨a, ha⟩) := by
  obtain ⟨hn, θ, β, hs, hk, hsd⟩ := h
  exact ⟨θ, hs, hk, fun a ha => hsd.secIdx_eq_idx hLN ha⟩

omit [Finite G] in
theorem IsNatSec.four_le_secIdx {F L N : Subgroup G} (h : IsNatSec F L N) (hLN : L ≤ N) {a : G}
    (ha : a ∈ F) (hac : a ∉ cSecIn F L N) : 4 ≤ secIdx (Subgroup.zpowers a) L N := by
  obtain ⟨θ, -, hk, hidx⟩ := IsModelSec.exists_secIdx h hLN
  rw [hidx a ha]
  refine (transvections _ fun h1 => hac ?_).1
  exact (mem_cSecIn_iff_of_ker hk ha).mp h1

omit [Finite G] in
theorem IsOrthSec.exists_swap_iff {F L N : Subgroup G} (h : IsOrthSec F L N) (hLN : L ≤ N) :
    ∃ θ : ↥F →* Perm (Fin 5), Function.Surjective θ ∧ θ.ker = (cSecIn F L N).subgroupOf F ∧
      ∀ (a : G) (ha : a ∈ F), a ∉ cSecIn F L N →
        (secIdx (Subgroup.zpowers a) L N = 2 ↔ (θ ⟨a, ha⟩).IsSwap) := by
  obtain ⟨θ, hs, hk, hidx⟩ := IsModelSec.exists_secIdx h hLN
  refine ⟨θ, hs, hk, fun a ha hac => ?_⟩
  rw [hidx a ha]
  exact (transvections _ fun h1 => hac ((mem_cSecIn_iff_of_ker hk ha).mp h1)).2

theorem chief_central_or_nat_or_orth {X U L N : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5))) (hU : U ≤ pCoreOf 2 X)
    (hstep : IsChiefStep X U L N) :
    IsCentralStep X L N ∨
      (cSecIn X L N = pCoreOf 2 X ∧ (IsNatSec X L N ∨ IsOrthSec X L N)) := by
  by_cases hc : IsCentralStep X L N
  · exact Or.inl hc
  · refine Or.inr ?_
    obtain ⟨h1, h2⟩ := chiefStep_orth_or_nat_of_classification
      (fun M hM hnt => model5_irred_classification M hM hnt) hq hU hstep hc
    exact ⟨h1, h2.symm⟩

theorem chief_chain_of_le_two {X : Subgroup G} (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    {W : ℕ → Subgroup G} {x : G} {r : ℕ} (hx : x ∈ X) (hxQ : x ∉ pCoreOf 2 X)
    (hWQ : ∀ i, i ≤ r → W i ≤ pCoreOf 2 X)
    (hXW : ∀ i, i ≤ r → X ≤ Subgroup.normalizer (W i : Set G))
    (hstep : ∀ i, i < r → IsChiefStep X (pCoreOf 2 X) (W i) (W (i + 1)))
    (h2 : secIdx (Subgroup.zpowers x) (W 0) (W r) ≤ 2) :
    (∀ i, i < r → ¬ IsCentralStep X (W i) (W (i + 1)) →
      IsOrthSec X (W i) (W (i + 1)) ∧ secIdx (Subgroup.zpowers x) (W i) (W (i + 1)) = 2) ∧
    ∀ i j, i < r → j < r → i ≠ j →
      IsCentralStep X (W i) (W (i + 1)) ∨ IsCentralStep X (W j) (W (j + 1)) := by
  have hmono : ∀ i j, i ≤ j → j ≤ r → W i ≤ W j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hj
      exact (ih (by omega)).trans (hstep j (by omega)).2.2.1.le
  have hnorm : ∀ i j, i ≤ r → j ≤ r → W j ≤ Subgroup.normalizer (W i : Set G) :=
    fun i j hi hj => ((hWQ j hj).trans (pCoreOf_le 2 X)).trans (hXW i hi)
  have hxn : ∀ i, i ≤ r → x ∈ Subgroup.normalizer (W i : Set G) := fun i hi => hXW i hi hx
  obtain ⟨hle2, hone⟩ := secIdx_chain_of_le_two hmono hnorm hxn h2
  have hnc : ∀ i, i < r → ¬ IsCentralStep X (W i) (W (i + 1)) →
      secIdx (Subgroup.zpowers x) (W i) (W (i + 1)) ≠ 1 ∧
        x ∉ cSecIn X (W i) (W (i + 1)) := by
    intro i hi hnci
    have hxc : x ∉ cSecIn X (W i) (W (i + 1)) := by
      rcases chief_central_or_nat_or_orth hq le_rfl (hstep i hi) with h | ⟨h, -⟩
      · exact absurd h hnci
      · rw [h]; exact hxQ
    refine ⟨fun h1 => hxc ?_, hxc⟩
    have := (secIdx_eq_one_iff (hnorm i (i + 1) (by omega) hi) (hxn i (by omega))).mp h1
    exact (mem_cSecIn_iff (hXW i (by omega))).mpr ⟨hx, this⟩
  refine ⟨fun i hi hnci => ?_, fun i j hi hj hij => ?_⟩
  · obtain ⟨h1, hxc⟩ := hnc i hi hnci
    have h2' : secIdx (Subgroup.zpowers x) (W i) (W (i + 1)) = 2 := by
      rcases hle2 i hi with h | h
      · exact absurd h h1
      · exact h
    refine ⟨?_, h2'⟩
    rcases chief_central_or_nat_or_orth hq le_rfl (hstep i hi) with h | ⟨-, h | h⟩
    · exact absurd h hnci
    · have := IsNatSec.four_le_secIdx h (hstep i hi).2.2.1.le hx hxc
      omega
    · exact h
  · by_contra hcon
    push Not at hcon
    rcases hone i j hi hj hij with h | h
    · exact (hnc i hi hcon.1).1 h
    · exact (hnc j hj hcon.2).1 h

end Chief

end CFSG.Quasithin.F53.Stellmacher.S43
