module

public import CFSG.Quasithin.SteinbergBNA7ReversalDiagonal

public section

namespace CFSG.Quasithin.SteinbergBN

open Subgroup CFSG CFSG.QuasithinUnique CFSG.LocalAnalysis.SteinbergBV.ConstantRank
open scoped commutatorElement Pointwise

section Structure

variable {G : Type*} [Group G]

theorem mul_ne_mul_of_notMem {U A E : Subgroup G} (hUab : U ≤ centralizer (U : Set G))
    (hEU : E ≤ U) (hEA : E ≤ A) (hEC : E = U ⊓ centralizer (A : Set G))
    (hEidx : (E.relIndex A).Prime) {u a : G} (hu : u ∈ U) (huE : u ∉ E) (ha : a ∈ A)
    (haE : a ∉ E) : u * a ≠ a * u := by
  intro h
  have hEle : E ≤ A ⊓ centralizer ({u} : Set G) := le_inf hEA fun z hz => by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 (hUab (hEU hz)) u hu).symm
  have hW := SteinbergBS.ReversalPair.eq_of_le_of_prime_relIndex hEle inf_le_left hEidx
    fun hWE => haE (hWE (mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 h.symm⟩))
  apply huE
  rw [hEC]
  refine mem_inf.2 ⟨hu, mem_centralizer_iff.2 fun b hb => ?_⟩
  exact mem_centralizer_singleton_iff.1 (mem_inf.1 (hW.ge hb)).2

theorem mem_or_mem_of_mul_self_mem {S U A D E F : Subgroup G} (hS : U ⊔ A ⊔ D = S)
    (hbot : (U ⊔ A) ⊓ D = ⊥) (hDUA : D ≤ centralizer ((U ⊔ A : Subgroup G) : Set G))
    (hUA : U ≤ normalizer (A : Set G)) (hFD : F ≤ D)
    (hUexp : ∀ u ∈ U, u * u = 1) (hAexp : ∀ a ∈ A, a * a = 1)
    (hUab : U ≤ centralizer (U : Set G)) (hEU : E ≤ U) (hEA : E ≤ A)
    (hEC : E = U ⊓ centralizer (A : Set G)) (hEidx : (E.relIndex A).Prime) {z : G}
    (hz : z ∈ S) (hzz : z * z ∈ F) : z ∈ U ⊔ D ∨ z ∈ A ⊔ D := by
  have hUAD : U ⊔ A ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp hDUA).trans (centralizer_le_normalizer _)
  have hSmul : (S : Set G) = ((U ⊔ A : Subgroup G) : Set G) * (D : Set G) := by
    rw [← hS]
    exact coe_mul_of_left_le_normalizer_right (U ⊔ A) D hUAD
  obtain ⟨w, hw, d, hd, rfl⟩ : z ∈ ((U ⊔ A : Subgroup G) : Set G) * (D : Set G) := hSmul ▸ hz
  have hwd : w * d = d * w := mem_centralizer_iff.1 (hDUA hd) w hw
  have hww : w * w = 1 := by
    have h1 : w * w ∈ D := by
      have e : w * d * (w * d) * (d * d)⁻¹ = w * w := by
        calc w * d * (w * d) * (d * d)⁻¹ = w * (d * w) * d * (d * d)⁻¹ := by group
          _ = w * (w * d) * d * (d * d)⁻¹ := by rw [hwd]
          _ = w * w := by group
      rw [← e]
      exact mul_mem (hFD hzz) (inv_mem (mul_mem hd hd))
    have h2 : w * w ∈ (U ⊔ A) ⊓ D := mem_inf.2 ⟨mul_mem hw hw, h1⟩
    rwa [hbot, mem_bot] at h2
  have hUAmul : ((U ⊔ A : Subgroup G) : Set G) = (U : Set G) * (A : Set G) :=
    coe_mul_of_left_le_normalizer_right U A hUA
  obtain ⟨u, hu, a, ha, rfl⟩ : w ∈ (U : Set G) * (A : Set G) := hUAmul ▸ hw
  by_cases haE : a ∈ E
  · left
    exact mul_mem ((le_sup_left : U ≤ U ⊔ D) (mul_mem hu (hEU haE)))
      ((le_sup_right : D ≤ U ⊔ D) hd)
  · by_cases huE : u ∈ E
    · right
      exact mul_mem ((le_sup_left : A ≤ A ⊔ D) (mul_mem (hEA huE) ha))
        ((le_sup_right : D ≤ A ⊔ D) hd)
    · exfalso
      have hww' : u * a * (u * a) = 1 := hww
      have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hUexp u hu)
      have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hAexp a ha)
      apply mul_ne_mul_of_notMem hUab hEU hEA hEC hEidx hu huE ha haE
      rw [eq_inv_of_mul_eq_one_left hww', mul_inv_rev, huinv, hainv]

theorem mem_sup_of_commutator_mem {S U A D E F : Subgroup G} (hS : U ⊔ A ⊔ D = S)
    (hbot : (U ⊔ A) ⊓ D = ⊥) (hDUA : D ≤ centralizer ((U ⊔ A : Subgroup G) : Set G))
    (hUA : U ≤ normalizer (A : Set G)) (hFD : F ≤ D) (hUab : U ≤ centralizer (U : Set G))
    (hEU : E ≤ U) (hEC : E = A ⊓ centralizer (U : Set G)) {w : G} (hw : w ∈ S)
    (hwc : ∀ u ∈ U, ⁅w, u⁆ ∈ F) : w ∈ U ⊔ D := by
  have hUAD : U ⊔ A ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp hDUA).trans (centralizer_le_normalizer _)
  have hSmul : (S : Set G) = ((U ⊔ A : Subgroup G) : Set G) * (D : Set G) := by
    rw [← hS]
    exact coe_mul_of_left_le_normalizer_right (U ⊔ A) D hUAD
  obtain ⟨y, hy, d, hd, rfl⟩ : w ∈ ((U ⊔ A : Subgroup G) : Set G) * (D : Set G) := hSmul ▸ hw
  have hUAmul : ((U ⊔ A : Subgroup G) : Set G) = (U : Set G) * (A : Set G) :=
    coe_mul_of_left_le_normalizer_right U A hUA
  obtain ⟨u, hu, a, ha, rfl⟩ : y ∈ (U : Set G) * (A : Set G) := hUAmul ▸ hy
  have haU : a ∈ centralizer (U : Set G) := by
    rw [mem_centralizer_iff]
    intro v hv
    have hvUA : v ∈ U ⊔ A := (le_sup_left : U ≤ U ⊔ A) hv
    have hdv : d * v = v * d := (mem_centralizer_iff.1 (hDUA hd) v hvUA).symm
    have hc : ⁅u * a * d, v⁆ = ⁅u * a, v⁆ := by
      simp only [commutatorElement_def]
      calc u * a * d * v * (u * a * d)⁻¹ * v⁻¹ = u * a * (d * v) * d⁻¹ * a⁻¹ * u⁻¹ * v⁻¹ := by
            group
        _ = u * a * (v * d) * d⁻¹ * a⁻¹ * u⁻¹ * v⁻¹ := by rw [hdv]
        _ = u * a * v * (u * a)⁻¹ * v⁻¹ := by group
    have h1 : ⁅u * a, v⁆ ∈ (U ⊔ A) ⊓ D := by
      refine mem_inf.2 ⟨?_, hFD (hc ▸ hwc v hv)⟩
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hy hvUA) (inv_mem hy)) (inv_mem hvUA)
    rw [hbot, mem_bot, commutatorElement_def] at h1
    have h2 : u * a * v = v * (u * a) := by
      have := mul_inv_eq_one.1 h1
      rwa [mul_inv_eq_iff_eq_mul] at this
    have huv : u * v = v * u := mem_centralizer_iff.1 (hUab hu) v hv |>.symm
    calc v * a = u⁻¹ * (u * v) * a := by group
      _ = u⁻¹ * (v * u) * a := by rw [huv]
      _ = u⁻¹ * (v * (u * a)) := by group
      _ = u⁻¹ * (u * a * v) := by rw [h2]
      _ = a * v := by group
  have haE : a ∈ E := by
    rw [hEC]
    exact mem_inf.2 ⟨ha, haU⟩
  exact mul_mem ((le_sup_left : U ≤ U ⊔ D) (mul_mem hu (hEU haE)))
    ((le_sup_right : D ≤ U ⊔ D) hd)

theorem commutator_mem_of_mem_left {S Y D F : Subgroup G} (hS : Y ⊔ D = S)
    (hDY : D ≤ centralizer (Y : Set G)) (hFcomm : ∀ d ∈ D, ∀ e ∈ D, ⁅d, e⁆ ∈ F)
    (hFY : F ≤ D) {d s : G} (hd : d ∈ D) (hs : s ∈ S) : ⁅d, s⁆ ∈ F := by
  have hYD : Y ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp hDY).trans (centralizer_le_normalizer _)
  have hSmul : (S : Set G) = (Y : Set G) * (D : Set G) := by
    rw [← hS]
    exact coe_mul_of_left_le_normalizer_right Y D hYD
  obtain ⟨y, hy, e, he, rfl⟩ : s ∈ (Y : Set G) * (D : Set G) := hSmul ▸ hs
  have hdy : d * y = y * d := (mem_centralizer_iff.1 (hDY hd) y hy).symm
  have hc := hFcomm d hd e he
  have hcy : y * ⁅d, e⁆ = ⁅d, e⁆ * y :=
    mem_centralizer_iff.1 (hDY (hFY hc)) y hy
  have : ⁅d, y * e⁆ = ⁅d, e⁆ := by
    simp only [commutatorElement_def] at hcy ⊢
    calc d * (y * e) * d⁻¹ * (y * e)⁻¹ = (d * y) * e * d⁻¹ * e⁻¹ * y⁻¹ := by group
      _ = (y * d) * e * d⁻¹ * e⁻¹ * y⁻¹ := by rw [hdy]
      _ = (y * (d * e * d⁻¹ * e⁻¹)) * y⁻¹ := by group
      _ = (d * e * d⁻¹ * e⁻¹ * y) * y⁻¹ := by rw [hcy]
      _ = d * e * d⁻¹ * e⁻¹ := by group
  rw [this]
  exact hc

end Structure

section Main

variable {G : Type} [Group G] [Finite G]

theorem A3_small_family_index_two_normalizer_reversal {M T S : Subgroup G}
    (hT : IsSylowTwoOf T M) (hSn : M ≤ normalizer (S : Set G))
    (hS2 : IsPGroup 2 S) {r : ℕ} (hr : r = 1 ∨ r = 2) (Kf : Fin r → Subgroup G)
    (hK : ∀ i, IsShort2 (Kf i)) (h3 : ∀ i, Nat.card (Kf i ⧸ CFSG.pCore 2 (Kf i)) = 3)
    (hcomm : ∀ i j, i ≠ j → ⁅Kf i, Kf j⁆ = ⊥) (hSK : ∀ i, S ≤ normalizer (Kf i : Set G))
    (hUS : ∀ i, blockQ (Kf i) ≤ S)
    (hperm : ∀ t ∈ T, ∀ i, ∃ j, CFSG.conjugate (Kf i) t = Kf j)
    (htrans : ∀ i j, ∃ t ∈ T, CFSG.conjugate (Kf i) t = Kf j) :
    let K₁ := Kf ⟨0, by omega⟩
    let U₁ := blockQ K₁
    let T₁ := T ⊓ normalizer (K₁ : Set G)
    ∀ x ∈ M, ⁅U₁, CFSG.conjugate U₁ x⁆ ≠ ⊥ →
      ∃ _hr2 : r = 2, T₁ = T ⊓ normalizer (U₁ : Set G) ∧ T₁.relIndex T = 2 ∧
        (∃ x₀ ∈ M, x₀ ∈ normalizer (T₁ : Set G) ∧ x₀ * x₀ ∈ T₁ ∧
          ⁅U₁, CFSG.conjugate U₁ x₀⁆ ≠ ⊥) ∧
        ∀ t ∈ T, t ∉ T₁ → CFSG.conjugate K₁ t = Kf ⟨1, by omega⟩ ∧
          ⁅K₁, CFSG.conjugate K₁ t⁆ = ⊥ := by
  intro K₁ U₁ T₁ x hxM hx
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hT.1
  have hTS : T ≤ normalizer (S : Set G) := hTM.trans hSn
  obtain ⟨-, hUK', hUcard', hUexp', hUab', -, hUKC', -, -⟩ :=
    SteinbergBS.ReversalPair.a3_data (hK ⟨0, by omega⟩) (h3 ⟨0, by omega⟩)
  have hUK : U₁ ≤ K₁ := hUK'
  have hUcard : Nat.card U₁ = 4 := hUcard'
  have hUexp : ∀ u ∈ U₁, u * u = 1 := hUexp'
  have hUab : U₁ ≤ centralizer (U₁ : Set G) := hUab'
  have hUKC : U₁ ⊓ centralizer (K₁ : Set G) = ⊥ := hUKC'
  have hUS1 : U₁ ≤ S := hUS _
  have hSK1 : S ≤ normalizer (K₁ : Set G) := hSK _
  have hKU : normalizer (K₁ : Set G) ≤ normalizer (U₁ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁
  set Q : Subgroup G := S ⊓ centralizer (U₁ : Set G) with hQ
  set D : Subgroup G := S ⊓ centralizer (K₁ : Set G) with hD
  set A : Subgroup G := CFSG.conjugate U₁ x with hA
  set E : Subgroup G := ⁅U₁, A⁆ with hE
  have hxS : x ∈ normalizer (S : Set G) := hSn hxM
  obtain ⟨⟨-, -, hKU', -, -, -, hUDQ, -, hDU⟩, hrev, -⟩ :=
    SteinbergBS.actual_A3_reversal_pair_identities_and_odd_commutation (hK ⟨0, by omega⟩)
      (h3 ⟨0, by omega⟩) hS2 hSK1 rfl hUS1 hQ hD
  obtain ⟨hAS, hSA, hEUA, hUAC, hUCA, hEcard, -, -, -, -, -, -, -, hDA, hUAD, hUADbot, hDUA, -,
    hFx, -⟩ := hrev x hxS A E hA hE hx
  have hQS : Q ≤ S := inf_le_left
  have hDS : D ≤ S := inf_le_left
  have hEU : E ≤ U₁ := hEUA ▸ inf_le_left
  have hEA : E ≤ A := hEUA ▸ inf_le_right
  have hEC : E = U₁ ⊓ centralizer (A : Set G) := hEUA.trans hUAC
  have hEC' : E = A ⊓ centralizer (U₁ : Set G) := hEC.trans hUCA
  have hcard_conj : ∀ (H : Subgroup G) (g : G), Nat.card (CFSG.conjugate H g) = Nat.card H :=
    fun H g => card_map_of_injective (MulAut.conj g⁻¹).injective
  have hAcard : Nat.card A = 4 := by rw [hA, hcard_conj, hUcard]
  have hEidx : (E.relIndex A).Prime := by
    have h := relIndex_mul_card E A
    rw [inf_of_le_left hEA, hEcard, hAcard] at h
    have h2 : E.relIndex A = 2 := by omega
    rw [h2]
    exact Nat.prime_two
  have hAexp : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    rw [hA, mem_conjugate_iff_conj] at ha
    have h1 := hUexp _ ha
    have h2 : x * (a * a) * x⁻¹ = 1 := by
      calc x * (a * a) * x⁻¹ = x * a * x⁻¹ * (x * a * x⁻¹) := by group
        _ = 1 := h1
    simpa using h2
  have hAab : A ≤ centralizer (A : Set G) := by
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hUab
    rwa [show (centralizer (U₁ : Set G)).map (MulAut.conj x⁻¹).toMonoidHom =
      CFSG.conjugate (centralizer (U₁ : Set G)) x from rfl, conjugate_centralizer] at h
  have hUA : U₁ ≤ normalizer (A : Set G) := hUS1.trans hSA
  set F : Subgroup G := (frattini D).map D.subtype with hF
  have hD2 : IsPGroup 2 D := hS2.to_le hDS
  have hFD : F ≤ D := map_subtype_le _
  have hFcl : F = closure (commPowSet 2 D) := frattini_map_eq_closure hD2
  have hFsq : ∀ d ∈ D, d * d ∈ F := fun d hd => by
    rw [hFcl]
    exact subset_closure (Or.inr ⟨d, hd, (sq d).symm⟩)
  have hFcomm : ∀ d ∈ D, ∀ e ∈ D, ⁅d, e⁆ ∈ F := fun d hd e he => by
    rw [hFcl]
    exact subset_closure (Or.inl ⟨d, hd, e, he, rfl⟩)
  have hNF : normalizer (D : Set G) ≤ normalizer (F : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (frattini D)
  have hUDmul : ((U₁ ⊔ D : Subgroup G) : Set G) = (U₁ : Set G) * (D : Set G) :=
    coe_mul_of_left_le_normalizer_right U₁ D
      ((le_centralizer_iff.mp hDU).trans (centralizer_le_normalizer _))
  have hQsq : ∀ q ∈ Q, q * q ∈ F := by
    intro q hq
    rw [← hUDQ] at hq
    obtain ⟨u, hu, d, hd, rfl⟩ : q ∈ (U₁ : Set G) * (D : Set G) := hUDmul ▸ hq
    have hud : u * d = d * u := mem_centralizer_iff.1 (hDU hd) u hu
    have : u * d * (u * d) = (u * u) * (d * d) := by
      calc u * d * (u * d) = u * (d * u) * d := by group
        _ = u * (u * d) * d := by rw [hud]
        _ = (u * u) * (d * d) := by group
    rw [this, hUexp u hu, one_mul]
    exact hFsq d hd
  have hQx : CFSG.conjugate Q x = S ⊓ centralizer (A : Set G) := by
    rw [hQ, conjugate_inf, conjugate_centralizer, conjugate_eq_self_of_mem_normalizer hxS]
  have hADle : A ⊔ D ≤ S ⊓ centralizer (A : Set G) :=
    sup_le (le_inf hAS hAab) (le_inf hDS hDA)
  have hkey : ∀ z ∈ S, z * z ∈ F → z ∈ Q ∨ z ∈ S ⊓ centralizer (A : Set G) := by
    intro z hz hzz
    rcases mem_or_mem_of_mul_self_mem hUAD hUADbot hDUA hUA hFD hUexp hAexp hUab hEU hEA hEC
      hEidx hz hzz with h | h
    · exact Or.inl (hUDQ ▸ h)
    · exact Or.inr (hADle h)
  set M₁ : Subgroup G := M ⊓ normalizer (F : Set G) with hM₁
  have hdich : ∀ g ∈ M₁, CFSG.conjugate Q g = Q ∨ CFSG.conjugate Q g = CFSG.conjugate Q x := by
    intro g hg
    obtain ⟨hgM, hgF⟩ := mem_inf.1 hg
    have hgS := hSn hgM
    rcases SteinbergBS.ReversalPair.le_or_le_of_forall_mem_or (H := CFSG.conjugate Q g)
        (K₁ := Q) (K₂ := S ⊓ centralizer (A : Set G)) (fun z hz => by
      rw [mem_conjugate_iff_conj] at hz
      refine hkey z ?_ ?_
      · have := (mem_normalizer_iff.1 (inv_mem hgS) _).1 (hQS hz)
        rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this
      · have := (mem_normalizer_iff.1 (inv_mem hgF) _).1 (hQsq _ hz)
        rwa [show g⁻¹ * (g * z * g⁻¹ * (g * z * g⁻¹)) * g⁻¹⁻¹ = z * z by group] at this)
      with h | h
    · exact Or.inl (eq_of_le_of_card_ge h (by rw [hcard_conj]))
    · exact Or.inr (eq_of_le_of_card_ge (h.trans hQx.ge) (by rw [hcard_conj, hcard_conj]))
  have hcomm_ne : ∀ {H : Subgroup G}, A ≤ H → H ≤ centralizer (U₁ : Set G) → False := by
    intro H hAH hHC
    apply hx
    rw [hE, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hAH.trans hHC
  have hQxne : CFSG.conjugate Q x ≠ Q := by
    intro h
    refine hcomm_ne (H := Q) ?_ inf_le_right
    rw [← h, hQx]
    exact le_inf hAS hAab
  have hxF : x ∈ normalizer (F : Set G) := mem_normalizer_of_conjugate_eq hFx
  have hxM₁ : x ∈ M₁ := mem_inf.2 ⟨hxM, hxF⟩
  set C : Subgroup G := M₁ ⊓ normalizer (Q : Set G) with hC
  have hCM₁ : C ≤ M₁ := inf_le_left
  have hxC : x ∉ C := fun h => hQxne (conjugate_eq_self_of_mem_normalizer (mem_inf.1 h).2)
  have hconj_inj : ∀ (H H' : Subgroup G) (g : G), CFSG.conjugate H g = CFSG.conjugate H' g →
      H = H' := fun H H' g h => map_injective (MulAut.conj g⁻¹).injective h
  have hCidx : C.relIndex M₁ = 2 := by
    show (C.subgroupOf M₁).index = 2
    rw [Subgroup.index_eq_two_iff_exists_notMem_and']
    refine ⟨⟨x, hxM₁⟩, by rwa [mem_subgroupOf], fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    by_cases hb : (b : G) ∈ C
    · exact Or.inr hb
    · left
      have hbQ : CFSG.conjugate Q b = CFSG.conjugate Q x := by
        rcases hdich b b.2 with h | h
        · exact absurd (mem_inf.2 ⟨b.2, mem_normalizer_of_conjugate_eq h⟩) hb
        · exact h
      have hxb : ((⟨x, hxM₁⟩ * b : M₁) : G) = x * b := rfl
      rw [hxb]
      refine mem_inf.2 ⟨mul_mem hxM₁ b.2, mem_normalizer_of_conjugate_eq ?_⟩
      rcases hdich (x * b) (mul_mem hxM₁ b.2) with h | h
      · exact h
      · exfalso
        rw [← conjugate_conjugate', ← hbQ] at h
        exact hQxne (hbQ.symm.trans (hconj_inj _ _ _ h))
  have hNC : ∀ t ∈ M, t ∈ normalizer (K₁ : Set G) → t ∈ C := by
    intro t htM htK
    have htS := hSn htM
    have htD : t ∈ normalizer (D : Set G) := by
      have h1 : t ∈ normalizer (centralizer (K₁ : Set G) : Set G) := by
        rw [mem_normalizer_iff]
        intro y
        constructor
        · exact fun hy => SteinbergBS.ReversalPair.conj_mem_centralizer htK hy
        · intro hy
          have := SteinbergBS.ReversalPair.conj_mem_centralizer (inv_mem htK) hy
          rwa [show t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y by group] at this
      exact (le_normalizer_inf (S := zpowers t) (zpowers_le.2 htS) (zpowers_le.2 h1))
        (mem_zpowers t)
    have htU := hKU htK
    have htQ : t ∈ normalizer (Q : Set G) := by
      have h1 : t ∈ normalizer (centralizer (U₁ : Set G) : Set G) := by
        rw [mem_normalizer_iff]
        intro y
        constructor
        · exact fun hy => SteinbergBS.ReversalPair.conj_mem_centralizer htU hy
        · intro hy
          have := SteinbergBS.ReversalPair.conj_mem_centralizer (inv_mem htU) hy
          rwa [show t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y by group] at this
      exact (le_normalizer_inf (S := zpowers t) (zpowers_le.2 htS) (zpowers_le.2 h1))
        (mem_zpowers t)
    exact mem_inf.2 ⟨mem_inf.2 ⟨htM, hNF htD⟩, htQ⟩
  have hr2 : r = 2 := by
    rcases hr with hr1 | hr2
    · exfalso
      have hTC : T ≤ C := by
        intro t ht
        refine hNC t (hTM ht) ?_
        obtain ⟨j, hj⟩ := hperm t ht ⟨0, by omega⟩
        have hj0 : j = ⟨0, by omega⟩ := Fin.ext (by have := j.2; omega)
        rw [hj0] at hj
        exact mem_normalizer_of_conjugate_eq hj
      have h1 := relIndex_mul_relIndex T C M₁ hTC hCM₁
      have h2 := relIndex_mul_relIndex T M₁ M (hTC.trans hCM₁) inf_le_left
      rw [hCidx] at h1
      apply hT.2.2
      show 2 ∣ T.relIndex M
      rw [← h2, ← h1]
      exact (dvd_mul_left 2 _).mul_right _
    · exact hr2
  refine ⟨hr2, ?_⟩
  set K₂ : Subgroup G := Kf ⟨1, by omega⟩ with hK₂
  have hK12 : ⁅K₁, K₂⁆ = ⊥ := hcomm _ _ (by simp [Fin.ext_iff])
  have hK2C : K₂ ≤ centralizer (K₁ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 ((Subgroup.commutator_comm _ _).trans hK12)
  have hKUc : K₁ ⊓ centralizer (U₁ : Set G) = U₁ := hKU'
  have hKK : K₁ ⊓ K₂ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyK, hyK2⟩ := mem_inf.1 hy
    have hyC := hK2C hyK2
    have hyU : y ∈ U₁ := by
      rw [← hKUc]
      exact mem_inf.2 ⟨hyK, centralizer_le hUK hyC⟩
    rw [← hUKC]
    exact mem_inf.2 ⟨hyU, hyC⟩
  have hUne : U₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hUcard
    omega
  have hKne : K₁ ≠ K₂ := by
    intro h
    apply hUne
    rw [eq_bot_iff, ← hKK]
    exact le_inf hUK (h ▸ hUK)
  have hfin2 : ∀ j : Fin r, j = ⟨0, by omega⟩ ∨ j = ⟨1, by omega⟩ := by
    intro j
    rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 by have := j.2; omega) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hT01 : ∀ t ∈ T, ∀ i : Fin r, CFSG.conjugate (Kf i) t = K₁ ∨
      CFSG.conjugate (Kf i) t = K₂ := by
    intro t ht i
    obtain ⟨j, hj⟩ := hperm t ht i
    rcases hfin2 j with h | h
    · rw [h] at hj
      exact Or.inl hj
    · rw [h] at hj
      exact Or.inr hj
  have hout : ∀ t ∈ T, t ∉ T₁ → CFSG.conjugate K₁ t = K₂ := by
    intro t ht htT₁
    rcases hT01 t ht ⟨0, by omega⟩ with h | h
    · exact absurd (mem_inf.2 ⟨ht, mem_normalizer_of_conjugate_eq h⟩) htT₁
    · exact h
  have hT₁U : T₁ = T ⊓ normalizer (U₁ : Set G) := by
    refine le_antisymm (inf_le_inf_left _ hKU) fun t ht => ?_
    obtain ⟨htT, htU⟩ := mem_inf.1 ht
    refine mem_inf.2 ⟨htT, ?_⟩
    rcases hT01 t htT ⟨0, by omega⟩ with h | h
    · exact mem_normalizer_of_conjugate_eq h
    · exfalso
      apply hUne
      rw [eq_bot_iff, ← hKK]
      refine le_inf hUK ?_
      have h1 : CFSG.conjugate U₁ t ≤ CFSG.conjugate K₁ t := Subgroup.map_mono hUK
      rw [conjugate_eq_self_of_mem_normalizer htU, h] at h1
      exact h1
  have hT₁T : T₁ ≤ T := inf_le_left
  have hT₁idx : T₁.relIndex T = 2 := by
    obtain ⟨t₀, ht₀T, ht₀'⟩ := htrans ⟨0, by omega⟩ ⟨1, by omega⟩
    have ht₀ : CFSG.conjugate K₁ t₀ = K₂ := ht₀'
    have ht₀T₁ : t₀ ∉ T₁ := fun h => hKne (by
      rw [← ht₀]
      exact (conjugate_eq_self_of_mem_normalizer (mem_inf.1 h).2).symm)
    show (T₁.subgroupOf T).index = 2
    rw [Subgroup.index_eq_two_iff_exists_notMem_and']
    refine ⟨⟨t₀, ht₀T⟩, by rwa [mem_subgroupOf], fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    by_cases hb : (b : G) ∈ T₁
    · exact Or.inr hb
    · left
      have hbK := hout b b.2 hb
      have htb : ((⟨t₀, ht₀T⟩ * b : T) : G) = t₀ * b := rfl
      rw [htb]
      refine mem_inf.2 ⟨mul_mem ht₀T b.2, mem_normalizer_of_conjugate_eq ?_⟩
      rw [← conjugate_conjugate', ht₀]
      rcases hT01 b b.2 ⟨1, by omega⟩ with h | h
      · exact h
      · exfalso
        rw [← hbK] at h
        exact hKne (hconj_inj _ _ _ h).symm
  have hT₁C : T₁ ≤ C := fun t ht => hNC t (hTM (mem_inf.1 ht).1) (mem_inf.1 ht).2
  have hTM₁ : ∀ t ∈ T, t ∉ T₁ → t ∉ M₁ := by
    intro t ht htT₁ htM₁
    have htS := hTS ht
    have hU2K : CFSG.conjugate U₁ t ≤ K₂ := by
      rw [← hout t ht htT₁]
      exact Subgroup.map_mono hUK
    have hU2S : CFSG.conjugate U₁ t ≤ S := by
      rw [← conjugate_eq_self_of_mem_normalizer htS]
      exact Subgroup.map_mono hUS1
    have hU2D : CFSG.conjugate U₁ t ≤ D := le_inf hU2S (hU2K.trans hK2C)
    have hUAc : U₁ ⊔ A ≤ centralizer (CFSG.conjugate U₁ t : Set G) :=
      le_centralizer_iff.mp (hU2D.trans hDUA)
    have hQt : CFSG.conjugate Q t = S ⊓ centralizer (CFSG.conjugate U₁ t : Set G) := by
      rw [hQ, conjugate_inf, conjugate_centralizer, conjugate_eq_self_of_mem_normalizer htS]
    have hUAQt : U₁ ⊔ A ≤ CFSG.conjugate Q t := hQt ▸ le_inf (sup_le hUS1 hAS) hUAc
    rcases hdich t htM₁ with h | h
    · exact hcomm_ne (H := Q) ((le_sup_right.trans hUAQt).trans h.le) inf_le_right
    · rw [hQx] at h
      have hUCA' : U₁ ≤ centralizer (A : Set G) :=
        ((le_sup_left.trans hUAQt).trans h.le).trans inf_le_right
      exact hcomm_ne (H := A) le_rfl (le_centralizer_iff.mp hUCA')
  have hT₁2 : IsPGroup 2 T₁ := hT.2.1.to_le hT₁T
  obtain ⟨T₀, hT₁T₀, hT₀⟩ := exists_isSylowTwoOf_of_le (hT₁C.trans hCM₁) hT₁2
  have hT₀M₁ : T₀ ≤ M₁ := hT₀.1
  have hT₀C : ¬ T₀ ≤ C := by
    intro h
    apply hT₀.2.2
    show 2 ∣ T₀.relIndex M₁
    rw [← relIndex_mul_relIndex T₀ C M₁ h hCM₁, hCidx]
    exact dvd_mul_left 2 _
  obtain ⟨x₀, hx₀T₀, hx₀C⟩ := Set.not_subset.1 hT₀C
  have hCT₀ : C.relIndex T₀ = 2 := by
    have h1 : C.relIndex T₀ ≤ C.relIndex M₁ :=
      relIndex_le_of_le_right hT₀M₁ (by rw [hCidx]; norm_num)
    have h2 : C.relIndex T₀ ≠ 1 := fun h => hT₀C (relIndex_eq_one.1 h)
    have h3' : C.relIndex T₀ ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hT₀T : Nat.card T₀ ≤ Nat.card T := by
    obtain ⟨S', hT₀S', hS'⟩ := exists_isSylowTwoOf_of_le (hT₀M₁.trans inf_le_left) hT₀.2.1
    calc Nat.card T₀ ≤ Nat.card S' := Subgroup.card_le_of_le hT₀S'
      _ = Nat.card T := by
        rw [(isSylowTwoOf_iff.1 hS').2.2, (isSylowTwoOf_iff.1 hT).2.2]
  have hTcard : Nat.card T = 2 * Nat.card T₁ := by
    have h := relIndex_mul_card T₁ T
    rw [hT₁idx, inf_of_le_left hT₁T] at h
    exact h.symm
  have hCT₀card := relIndex_mul_card C T₀
  rw [hCT₀] at hCT₀card
  have hT₁eq : T₁ = C ⊓ T₀ := by
    refine eq_of_le_of_card_ge (le_inf hT₁C hT₁T₀) ?_
    omega
  have hT₁T₀idx : T₁.relIndex T₀ = 2 := by
    rw [hT₁eq, inf_relIndex_right, hCT₀]
  have hT₀N : T₀ ≤ normalizer (T₁ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hT₁T₀).1 (normal_of_index_eq_two hT₁T₀idx)
  have hx₀2 : x₀ * x₀ ∈ T₁ := by
    have h := Subgroup.sq_mem_of_index_two (show (T₁.subgroupOf T₀).index = 2 from hT₁T₀idx)
      ⟨x₀, hx₀T₀⟩
    rw [sq] at h
    exact h
  have hx₀M₁ : x₀ ∈ M₁ := hT₀M₁ hx₀T₀
  obtain ⟨hx₀M, hx₀F⟩ := mem_inf.1 hx₀M₁
  have hx₀S := hSn hx₀M
  have hnc : ⁅U₁, CFSG.conjugate U₁ x₀⁆ ≠ ⊥ := by
    intro h
    have hUx₀Q : CFSG.conjugate U₁ x₀ ≤ Q := by
      refine le_inf ?_ ?_
      · rw [← conjugate_eq_self_of_mem_normalizer hx₀S]
        exact Subgroup.map_mono hUS1
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          ((Subgroup.commutator_comm _ _).trans h)
    have hDx₀Q : CFSG.conjugate D x₀ ≤ Q := by
      intro z hz
      rw [mem_conjugate_iff_conj] at hz
      have hzS : z ∈ S := by
        have := (mem_normalizer_iff.1 (inv_mem hx₀S) _).1 (hDS hz)
        rwa [show x₀⁻¹ * (x₀ * z * x₀⁻¹) * x₀⁻¹⁻¹ = z by group] at this
      rw [← hUDQ]
      refine mem_sup_of_commutator_mem hUAD hUADbot hDUA hUA hFD hUab hEU hEC' hzS
        fun u hu => ?_
      have hus : x₀ * u * x₀⁻¹ ∈ S := (mem_normalizer_iff.1 hx₀S _).1 (hUS1 hu)
      have h1 := commutator_mem_of_mem_left hUAD hDUA hFcomm hFD hz hus
      have h2 := (mem_normalizer_iff.1 (inv_mem hx₀F) _).1 h1
      have e : x₀⁻¹ * ⁅x₀ * z * x₀⁻¹, x₀ * u * x₀⁻¹⁆ * x₀⁻¹⁻¹ = ⁅z, u⁆ := by
        simp only [commutatorElement_def]
        group
      rwa [e] at h2
    have hQx₀ : CFSG.conjugate Q x₀ = Q := by
      refine eq_of_le_of_card_ge ?_ (by rw [hcard_conj])
      rw [← hUDQ, CFSG.conjugate, Subgroup.map_sup]
      exact sup_le (hUDQ ▸ hUx₀Q) (hUDQ ▸ hDx₀Q)
    exact hx₀C (mem_inf.2 ⟨hx₀M₁, mem_normalizer_of_conjugate_eq hQx₀⟩)
  refine ⟨hT₁U, hT₁idx, ⟨x₀, hx₀M, hT₀N hx₀T₀, hx₀2, hnc⟩, fun t ht htT₁ => ⟨hout t ht htT₁,
    ?_⟩⟩
  rw [hout t ht htT₁]
  exact hK12

end Main

end CFSG.Quasithin.SteinbergBN
