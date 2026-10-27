module

public import CFSG.Quasithin.Recognition.Kleidman.F204.GeoBase1

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

theorem sum_eq_zero_of_pairs {ι : Type*} [DecidableEq ι] {s : Finset ι} (hs : s.card = 4)
    {σ : ι → ι} (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hσne : ∀ i ∈ s, σ i ≠ i) {f : ι → ZMod 2} {c : ZMod 2} (hc : ∀ i ∈ s, f i + f (σ i) = c) :
    ∑ i ∈ s, f i = 0 := by
  obtain ⟨i, hi⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hj := hσs i hi
  have hji := hσne i hi
  have h1 : ((s.erase i).erase (σ i)).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hji, hj⟩), Finset.card_erase_of_mem hi, hs]
  obtain ⟨k, hk⟩ : ((s.erase i).erase (σ i)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hkj, hk'⟩ := Finset.mem_erase.mp hk
  obtain ⟨hki, hks⟩ := Finset.mem_erase.mp hk'
  have hl := hσs k hks
  have hlk := hσne k hks
  have hli : σ k ≠ i := by
    intro h
    apply hkj
    rw [← h, hσσ k hks]
  have hlj : σ k ≠ σ i := by
    intro h
    apply hki
    rw [← hσσ k hks, h, hσσ i hi]
  have hsub : ({i, σ i, k, σ k} : Finset ι) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({i, σ i, k, σ k} : Finset ι).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hlk.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hkj.symm, hlj.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hji.symm, hki.symm, hli.symm⟩
  have heq : ({i, σ i, k, σ k} : Finset ι) = s :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hs, hcard])
  rw [← heq, Finset.sum_insert, Finset.sum_insert, Finset.sum_pair hlk.symm]
  · have e1 := hc i hi
    have e2 := hc k hks
    calc f i + (f (σ i) + (f k + f (σ k))) = (f i + f (σ i)) + (f k + f (σ k)) := by ring
      _ = c + c := by rw [e1, e2]
      _ = 0 := by
        have : ∀ x : ZMod 2, x + x = 0 := by decide
        exact this c
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hkj.symm, hlj.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hji.symm, hki.symm, hli.symm⟩

variable {G : Type} [Group G] [Finite G]

variable {H M B S : Subgroup G}

namespace Amal

variable (hA : Amal H M B S)
include hA

open Classical in
theorem false_of_quadratic_hyperplane {α β : Geo H M} (hβ : β ∈ nbrs α) {V W : Subgroup G}
    (hVn : stab α ≤ Subgroup.normalizer (V : Set G)) (hW2 : W.relIndex V = 2)
    (hWn : stab α ⊓ stab β ≤ Subgroup.normalizer (W : Set G))
    (hCW : V ⊓ Subgroup.centralizer (Qv β : Set G) ≤ W)
    (hQ : ∀ ν ∈ nbrs α, Qv ν ≤ stab α)
    (htr : ∀ ν ∈ nbrs α, ∀ μ ∈ nbrs α, ∀ μ' ∈ nbrs α, μ ≠ ν → μ' ≠ ν →
      ∃ q : ↥(H ⊔ M), (q : G) ∈ Qv ν ∧ q • μ = μ')
    (hfree : ∀ t : ↥(H ⊔ M), (t : G) ∈ Qv β → ∀ μ ∈ nbrs α, μ ≠ β → t • μ = μ →
      ∀ μ' ∈ nbrs α, t • μ' = μ')
    (hsq : ∀ t : ↥(H ⊔ M), (t : G) ∈ Qv β → ∀ μ ∈ nbrs α, t • (t • μ) = μ)
    (hgen : V ≤ ⨆ (ν : Geo H M) (_ : ν ∈ nbrs α), V ⊓ Subgroup.centralizer (Qv ν : Set G))
    (hquad : ∀ v ∈ V, ∀ t ∈ Qv β, v * t * v⁻¹ * t⁻¹ ∈ Subgroup.centralizer (Qv β : Set G)) :
    False := by
  have hconjV : ∀ g : G, g ∈ stab α → ∀ x ∈ V, g⁻¹ * x * g ∈ V := by
    intro g hg x hx
    have hg' : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := inv_mem (hVn hg)
    have := (Subgroup.mem_normalizer_iff.mp hg' x).mp hx
    simpa using this
  have hnbr : ∀ g : ↥(H ⊔ M), (g : G) ∈ stab α → ∀ μ ∈ nbrs α, g • μ ∈ nbrs α := by
    intro g hg μ hμ
    have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj α μ from hμ)
    rwa [smul_eq_of_mem_stab hg] at this
  have hrep : ∀ μ, μ ∈ nbrs α → ∃ g : ↥(H ⊔ M), (g : G) ∈ stab α ∧ g • β = μ :=
    fun μ hμ => stab_transitive_on_nbrs hβ hμ
  choose! rep hrep1 hrep2 using hrep
  have hWconj : ∀ h : ↥(H ⊔ M), (h : G) ∈ stab α → h • β = β → ∀ y : G,
      ((h : G)⁻¹ * y * h ∈ W ↔ y ∈ W) := by
    intro h hh hhβ y
    have hn : (h : G)⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
      inv_mem (hWn ⟨hh, mem_stab_of_smul_eq hhβ⟩)
    have := (Subgroup.mem_normalizer_iff.mp hn y)
    simp only [inv_inv] at this
    exact this.symm
  have hindep : ∀ μ ∈ nbrs α, ∀ g : ↥(H ⊔ M), (g : G) ∈ stab α → g • β = μ → ∀ x : G,
      ((g : G)⁻¹ * x * g ∈ W ↔ ((rep μ : G)⁻¹ * x * rep μ) ∈ W) := by
    intro μ hμ g hg hgβ x
    set h : ↥(H ⊔ M) := g⁻¹ * rep μ with hh
    have hhα : (h : G) ∈ stab α := by
      rw [hh, Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (inv_mem hg) (hrep1 μ hμ)
    have hhβ : h • β = β := by
      rw [hh, mul_smul, hrep2 μ hμ, ← hgβ, inv_smul_smul]
    have e : (rep μ : G)⁻¹ * x * rep μ = (h : G)⁻¹ * ((g : G)⁻¹ * x * g) * h := by
      rw [hh]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e, hWconj h hhα hhβ]
  set f : Geo H M → G → ZMod 2 := fun μ x =>
    if (rep μ : G)⁻¹ * x * rep μ ∈ W then 0 else 1 with hf
  have hW2' : (W.subgroupOf V).index = 2 := hW2
  have hmulW : ∀ a ∈ V, ∀ b ∈ V, (a * b ∈ W ↔ (a ∈ W ↔ b ∈ W)) := by
    intro a ha b hb
    have := Subgroup.mul_mem_iff_of_index_two hW2' (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa [Subgroup.mem_subgroupOf] using this
  have f_add : ∀ μ ∈ nbrs α, ∀ x ∈ V, ∀ y ∈ V, f μ (x * y) = f μ x + f μ y := by
    intro μ hμ x hx y hy
    have hx' := hconjV _ (hrep1 μ hμ) x hx
    have hy' := hconjV _ (hrep1 μ hμ) y hy
    have e : (rep μ : G)⁻¹ * (x * y) * rep μ =
        ((rep μ : G)⁻¹ * x * rep μ) * ((rep μ : G)⁻¹ * y * rep μ) := by group
    simp only [hf, e]
    have key := hmulW _ hx' _ hy'
    by_cases h1 : (rep μ : G)⁻¹ * x * rep μ ∈ W <;> by_cases h2 : (rep μ : G)⁻¹ * y * rep μ ∈ W
    · simp only [h1, h2, iff_true] at key
      simp [key, h1, h2]
    · simp only [h1, h2, iff_false] at key
      simp [key, h1, h2]
    · simp only [h1, h2, iff_true] at key
      simp [key, h1, h2]
    · simp only [h1, h2, iff_self] at key
      simp only [key, h1, h2, ite_true, ite_false]
      decide
  have f_inv : ∀ μ, ∀ x : G, f μ x⁻¹ = f μ x := by
    intro μ x
    have e : (rep μ : G)⁻¹ * x⁻¹ * rep μ = ((rep μ : G)⁻¹ * x * rep μ)⁻¹ := by group
    simp only [hf, e, inv_mem_iff]
  have f_one : ∀ μ, f μ 1 = 0 := by
    intro μ
    simp only [hf, mul_one, inv_mul_cancel, one_mem, ite_true]
  have f_conj : ∀ μ ∈ nbrs α, ∀ q : ↥(H ⊔ M), (q : G) ∈ stab α → ∀ x : G,
      f (q • μ) x = f μ ((q : G)⁻¹ * x * q) := by
    intro μ hμ q hq x
    have hqμ := hnbr q hq μ hμ
    have hg : ((q * rep μ : ↥(H ⊔ M)) : G) ∈ stab α := by
      rw [Subgroup.coe_mul]; exact mul_mem hq (hrep1 μ hμ)
    have hgβ : (q * rep μ) • β = q • μ := by rw [mul_smul, hrep2 μ hμ]
    have := hindep (q • μ) hqμ (q * rep μ) hg hgβ x
    have e : (((q * rep μ : ↥(H ⊔ M)) : G))⁻¹ * x * ((q * rep μ : ↥(H ⊔ M)) : G) =
        (rep μ : G)⁻¹ * ((q : G)⁻¹ * x * q) * rep μ := by
      simp only [Subgroup.coe_mul]; group
    rw [e] at this
    simp only [hf]
    by_cases h1 : (rep μ : G)⁻¹ * ((q : G)⁻¹ * x * q) * rep μ ∈ W
    · simp only [this.mp h1, h1, ite_true]
    · have h2 : ¬ (rep (q • μ) : G)⁻¹ * x * rep (q • μ) ∈ W := fun h => h1 (this.mpr h)
      simp only [h2, h1, ite_false]
  have f_cent_zero : ∀ ν ∈ nbrs α, ∀ c ∈ V ⊓ Subgroup.centralizer (Qv ν : Set G), f ν c = 0 := by
    intro ν hν c hc
    have hcV := hconjV _ (hrep1 ν hν) c hc.1
    have hcC : (rep ν : G)⁻¹ * c * rep ν ∈ Subgroup.centralizer (Qv β : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyν : (rep ν : G) * y * (rep ν : G)⁻¹ ∈ Qv ν := by
        have e := Qv_smul (rep ν) β
        rw [hrep2 ν hν] at e
        rw [e, mem_conjSub]
        simpa [mul_assoc] using hy
      have hcomm := (Subgroup.mem_centralizer_iff.mp hc.2) _ hyν
      calc y * ((rep ν : G)⁻¹ * c * rep ν)
          = (rep ν : G)⁻¹ * (((rep ν : G) * y * (rep ν : G)⁻¹) * c) * rep ν := by group
        _ = (rep ν : G)⁻¹ * (c * ((rep ν : G) * y * (rep ν : G)⁻¹)) * rep ν := by rw [hcomm]
        _ = (rep ν : G)⁻¹ * c * rep ν * y := by group
    simp only [hf, hCW ⟨hcV, hcC⟩, ite_true]
  have f_cent_const : ∀ ν ∈ nbrs α, ∀ c ∈ V ⊓ Subgroup.centralizer (Qv ν : Set G),
      ∀ μ ∈ nbrs α, ∀ μ' ∈ nbrs α, μ ≠ ν → μ' ≠ ν → f μ c = f μ' c := by
    intro ν hν c hc μ hμ μ' hμ' hμν hμ'ν
    obtain ⟨q, hq, hqμ⟩ := htr ν hν μ hμ μ' hμ' hμν hμ'ν
    have hqc : (q : G)⁻¹ * c * q = c := by
      have := (Subgroup.mem_centralizer_iff.mp hc.2) _ hq
      rw [mul_assoc, ← this]; group
    rw [← hqμ, f_conj μ hμ q (hQ ν hν hq) c, hqc]
  have : Finite ↑(nbrs α) := Nat.finite_of_card_ne_zero (by rw [hA.card_nbrs α]; norm_num)
  set s : Finset (Geo H M) := (Set.toFinite (nbrs α)).toFinset with hs
  have hmem : ∀ μ, μ ∈ s ↔ μ ∈ nbrs α := fun μ => Set.Finite.mem_toFinset _
  have hscard : s.card = 5 := by
    rw [hs, ← Set.ncard_eq_toFinset_card, ← Nat.card_coe_set_eq, hA.card_nbrs α]
  have four : ∀ x : ZMod 2, (4 : ℕ) • x = 0 := by decide
  set F : G → ZMod 2 := fun x => ∑ μ ∈ s, f μ x with hF
  have F_cent : ∀ ν ∈ nbrs α, ∀ c ∈ V ⊓ Subgroup.centralizer (Qv ν : Set G), F c = 0 := by
    intro ν hν c hc
    have hνs := (hmem ν).mpr hν
    have hcard : (s.erase ν).card = 4 := by rw [Finset.card_erase_of_mem hνs, hscard]
    obtain ⟨μ0, hμ0⟩ : (s.erase ν).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hμ0ν, hμ0s⟩ := Finset.mem_erase.mp hμ0
    have hsum : ∑ μ ∈ s.erase ν, f μ c = (s.erase ν).card • f μ0 c := by
      apply Finset.sum_eq_card_nsmul
      intro μ hμ
      obtain ⟨hμν, hμs⟩ := Finset.mem_erase.mp hμ
      exact f_cent_const ν hν c hc μ ((hmem μ).mp hμs) μ0 ((hmem μ0).mp hμ0s) hμν hμ0ν
    simp only [hF]
    rw [← Finset.add_sum_erase s _ hνs, hsum, hcard, four, f_cent_zero ν hν c hc, add_zero]
  have F_add : ∀ x ∈ V, ∀ y ∈ V, F (x * y) = F x + F y := by
    intro x hx y hy
    simp only [hF, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ hμ => f_add μ ((hmem μ).mp hμ) x hx y hy
  let E : Subgroup G :=
    { carrier := {x | x ∈ V ∧ F x = 0}
      one_mem' := ⟨one_mem V, by simp only [hF, f_one, Finset.sum_const_zero]⟩
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by rw [F_add x hx.1 y hy.1, hx.2, hy.2,
        add_zero]⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by simp only [hF, f_inv]; exact hx.2⟩ }
  have hVE : V ≤ E := by
    refine hgen.trans (iSup₂_le fun ν hν => ?_)
    intro c hc
    exact ⟨hc.1, F_cent ν hν c hc⟩
  have hβs := (hmem β).mpr hβ
  have hcard4 : (s.erase β).card = 4 := by rw [Finset.card_erase_of_mem hβs, hscard]
  obtain ⟨μ1, hμ1⟩ : (s.erase β).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hμ1β, hμ1s⟩ := Finset.mem_erase.mp hμ1
  have hcard3 : ((s.erase β).erase μ1).card = 3 := by rw [Finset.card_erase_of_mem hμ1, hcard4]
  obtain ⟨μ2, hμ2⟩ : ((s.erase β).erase μ1).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hμ21, hμ2'⟩ := Finset.mem_erase.mp hμ2
  obtain ⟨hμ2β, hμ2s⟩ := Finset.mem_erase.mp hμ2'
  obtain ⟨t, ht, htμ⟩ := htr β hβ μ1 ((hmem μ1).mp hμ1s) μ2 ((hmem μ2).mp hμ2s) hμ1β hμ2β
  have htα : (t : G) ∈ stab α := hQ β hβ ht
  have htβ : t • β = β := smul_eq_of_mem_stab ((pCoreOf_le 2 (stab β)) ht)
  have hσs : ∀ μ ∈ s.erase β, t • μ ∈ s.erase β := by
    intro μ hμ
    obtain ⟨hμβ, hμs⟩ := Finset.mem_erase.mp hμ
    refine Finset.mem_erase.mpr ⟨?_, (hmem _).mpr (hnbr t htα μ ((hmem μ).mp hμs))⟩
    intro h
    apply hμβ
    rw [← htβ] at h
    exact smul_left_cancel t h
  have hσσ : ∀ μ ∈ s.erase β, t • (t • μ) = μ := fun μ hμ =>
    hsq t ht μ ((hmem μ).mp (Finset.mem_of_mem_erase hμ))
  have hσne : ∀ μ ∈ s.erase β, t • μ ≠ μ := by
    intro μ hμ h
    obtain ⟨hμβ, hμs⟩ := Finset.mem_erase.mp hμ
    have := hfree t ht μ ((hmem μ).mp hμs) hμβ h μ1 ((hmem μ1).mp hμ1s)
    rw [htμ] at this
    exact hμ21 this
  have hVW : V ≤ W := by
    intro m hm
    have htm := hconjV _ htα m hm
    have hcV : m⁻¹ * ((t : G)⁻¹ * m * t) ∈ V := mul_mem (inv_mem hm) htm
    have hcC : m⁻¹ * ((t : G)⁻¹ * m * t) ∈ Subgroup.centralizer (Qv β : Set G) := by
      have := hquad m⁻¹ (inv_mem hm) (t : G)⁻¹ (inv_mem ht)
      simpa [mul_assoc] using this
    have hpair : ∀ μ ∈ s.erase β, f μ m + f (t • μ) m = f μ1 (m⁻¹ * ((t : G)⁻¹ * m * t)) := by
      intro μ hμ
      obtain ⟨hμβ, hμs⟩ := Finset.mem_erase.mp hμ
      have hμα := (hmem μ).mp hμs
      rw [f_conj μ hμα t htα m, ← f_inv μ m, ← f_add μ hμα _ (inv_mem hm) _ htm]
      exact f_cent_const β hβ _ ⟨hcV, hcC⟩ μ hμα μ1 ((hmem μ1).mp hμ1s) hμβ hμ1β
    have hsum0 : ∑ μ ∈ s.erase β, f μ m = 0 :=
      sum_eq_zero_of_pairs hcard4 hσs hσσ hσne hpair
    have hF0 : F m = 0 := (hVE hm).2
    have hfβ : f β m = 0 := by
      have := Finset.add_sum_erase s (fun μ => f μ m) hβs
      simp only [hF] at hF0
      rw [← this, hsum0, add_zero] at hF0
      exact hF0
    have hrepW : (rep β : G)⁻¹ * m * rep β ∈ W := by
      by_contra hn
      simp only [hf, hn, ite_false] at hfβ
      exact absurd hfβ (by decide)
    have := (hindep β hβ 1 (one_mem _) (one_smul _ β) m).mpr hrepW
    simpa using this
  have hidx : W.relIndex V = 1 := Subgroup.relIndex_eq_one.mpr hVW
  omega

end Amal

end CFSG.Quasithin.Kleidman.F204
