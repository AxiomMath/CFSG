module

public import CFSG.Quasithin.H13.A6S13833g

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

theorem fpf3_sum_const : ∀ σ : Perm (Fin 6), σ ^ 3 = 1 → (∀ i, σ i ≠ i) →
    ∀ y : Fin 6 → ZMod 2, ∑ i, y i = 0 →
      y + vp σ y + vp σ (vp σ y) = 0 ∨ y + vp σ y + vp σ (vp σ y) = onesV := by
  decide +kernel

theorem wtv_add_ones_four : ∀ a : Fin 6 → ZMod 2, wtv a = 4 → wtv (a + onesV) = 2 := by
  decide +kernel

theorem dotv_syn : ∀ a b : Fin 6 → ZMod 2, wtv a = 4 → wtv b = 4 → wtv (a + b) = 4 →
    dotv a a = 0 ∧ dotv b a = 0 := by
  decide +kernel

theorem exists_dotv_one : ∀ a : Fin 6 → ZMod 2, wtv a = 4 →
    ∃ y : Fin 6 → ZMod 2, ∑ i, y i = 0 ∧ dotv y a = 1 := by
  decide +kernel

@[expose] def tri15 : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 1 2, swap 0 1 * swap 1 3, swap 0 1 * swap 1 4, swap 0 2 * swap 2 3,
    swap 0 2 * swap 2 4, swap 0 3 * swap 3 4, swap 1 2 * swap 2 3, swap 1 2 * swap 2 4,
    swap 1 3 * swap 3 4, swap 2 3 * swap 3 4]

theorem tri15_facts : ∀ σ ∈ tri15, Perm.sign σ = 1 ∧ σ ^ 3 = 1 := by decide +kernel

theorem tri15_moves : ∀ a b : Fin 6 → ZMod 2, wtv a = 4 → wtv b = 4 → wtv (a + b) = 4 →
    ∃ σ ∈ tri15, vp σ a = a ∧ ¬ InL a b (vp σ b) ∧ ¬ InL a b (vp σ (vp σ b)) := by
  decide +kernel

theorem trivModW2_of_fix : ∀ σ : Perm (Fin 6), (∀ y : P6, InW2 y → act4f σ y = y) →
    TrivModW2 σ := by
  decide +kernel

@[expose] def CubeW2 (σ : Perm (Fin 6)) : Prop :=
  StabW2 σ → σ ^ 45 = 1 → ¬ (∀ y : P6, InW4 y → InW3 y → InW3 (act4f σ y)) →
    ∀ w : P6, InW4 w → InW2 (w * act4f σ w * act4f σ (act4f σ w))

instance (σ : Perm (Fin 6)) : Decidable (CubeW2 σ) := by unfold CubeW2; infer_instance

theorem cube_W2 : ∀ σ : Perm (Fin 6), CubeW2 σ := by
  decide +kernel

theorem false_of_relIndex_two_cube {G : Type} [Group G] {X Y : Subgroup G} {x : G}
    (hxX : x ∈ Subgroup.normalizer (X : Set G)) (hxY : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y)
    (hsq : ∀ y ∈ Y, y * y ∈ X)
    (hcube : ∀ y ∈ Y, y * (x * y * x⁻¹) * (x * (x * y * x⁻¹) * x⁻¹) ∈ X)
    (h2 : X.relIndex Y = 2) : False := by
  obtain ⟨y, hyY, hyX⟩ : ∃ y ∈ Y, y ∉ X := by
    by_contra h
    push Not at h
    rw [Subgroup.relIndex_eq_one.2 h] at h2
    norm_num at h2
  have hnX : ∀ w, w ∉ X → x * w * x⁻¹ ∉ X := fun w hw h =>
    hw ((Subgroup.mem_normalizer_iff.mp hxX w).mpr h)
  have hy₁Y := hxY y hyY
  have hy₁X := hnX y hyX
  have hy₂X := hnX _ hy₁X
  have h01 := inv_mul_mem_of_relIndex_two h2 hyY hy₁Y hyX hy₁X
  have hyy : y * (x * y * x⁻¹) ∈ X := by
    have e : y * (x * y * x⁻¹) = (y * y) * (y⁻¹ * (x * y * x⁻¹)) := by group
    rw [e]
    exact X.mul_mem (hsq y hyY) h01
  have h := X.mul_mem (X.inv_mem hyy) (hcube y hyY)
  have e : (y * (x * y * x⁻¹))⁻¹ * (y * (x * y * x⁻¹) * (x * (x * y * x⁻¹) * x⁻¹)) =
      x * (x * y * x⁻¹) * x⁻¹ := by group
  rw [e] at h
  exact hy₂X h

theorem card_sup_mul_le {G : Type} [Group G] [Finite G] {A B W : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hWA : W ≤ A) (hWB : W ≤ B) :
    Nat.card ↥(A ⊔ B) * Nat.card W ≤ Nat.card A * Nat.card B := by
  have h := card_sup_mul_card_inf' hAB
  have hle : Nat.card W ≤ Nat.card ↥(A ⊓ B) := Subgroup.card_le_of_le (le_inf hWA hWB)
  calc Nat.card ↥(A ⊔ B) * Nat.card W ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) :=
        Nat.mul_le_mul_left _ hle
    _ = Nat.card A * Nat.card B := h

theorem mul_rearrange6 {G : Type} [Group G] {A : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {a b c d e f : G} (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (he : e ∈ A) :
    a * b * (c * d) * (e * f) = (a * c * e) * (b * d * f) := by
  have hbc := hA b hb c hc
  have hde := hA d hd e he
  have hbe := hA b hb e he
  calc a * b * (c * d) * (e * f) = a * (b * c) * (d * e) * f := by group
    _ = a * (c * b) * (e * d) * f := by rw [hbc, hde]
    _ = a * c * (b * e) * d * f := by group
    _ = a * c * (e * b) * d * f := by rw [hbe]
    _ = (a * c * e) * (b * d * f) := by group

theorem mem_normalizer_inf_two {G : Type} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (hA y) (hB y)

@[expose] def dotHom (a : Fin 6 → ZMod 2) : ↥(evenWeight 6) →+ ZMod 2 where
  toFun y := dotv (y : Fin 6 → ZMod 2) a
  map_zero' := dotv_zero a
  map_add' x y := dotv_add (x : Fin 6 → ZMod 2) (y : Fin 6 → ZMod 2) a

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_K2_of_odd {k₁ : G} (hk₁H : k₁ ∈ S.G1)
    (hk₁N : k₁ ∈ Subgroup.normalizer (S.V2 : Set G)) {m : ℕ} (hm : Odd m) (hk₁m : k₁ ^ m = 1) :
    k₁ ∈ S.K2 := by
  have hk₁C : k₁ ∈ Subgroup.centralizer (S.V2 : Set G) := by
    have hkz : k₁ * S.z * k₁⁻¹ = S.z := by
      have h : k₁ * S.z = S.z * k₁ := Subgroup.mem_centralizer_singleton_iff.mp hk₁H
      rw [h, mul_inv_cancel_right]
    have hz2 : S.z * S.z = 1 := by
      have := isElemAbelian_pow_eq_one S.elemAbelian_V S.z_mem_V
      rwa [pow_two] at this
    have hV1 : ∀ y ∈ fsuV1 T V, k₁ * y * k₁⁻¹ = y := by
      intro y hy
      rcases (S.mem_V1_iff).1 hy with rfl | rfl
      · group
      · exact hkz
    have h12 : (fsuV1 T V).relIndex S.V2 = 2 := by
      have h1 := Subgroup.relIndex_mul_card (fsuV1 T V) S.V2
      rw [inf_eq_left.2 S.V1_le_V2, S.card_V2, S.card_V1] at h1
      omega
    have hku : S.u1⁻¹ * (k₁ * S.u1 * k₁⁻¹) ∈ fsuV1 T V := by
      have hmem : k₁ * S.u1 * k₁⁻¹ ∈ S.V2 :=
        (Subgroup.mem_normalizer_iff.mp hk₁N S.u1).mp S.u1_mem_V2
      by_contra hne
      have hnot : k₁ * S.u1 * k₁⁻¹ ∉ fsuV1 T V := by
        intro h
        apply S.u1_not_V1
        have := (Subgroup.mem_normalizer_iff.mp
          (S.normalizer_V1 ▸ (hk₁H : k₁ ∈ Subgroup.centralizer ({S.z} : Set G)) :
            k₁ ∈ Subgroup.normalizer (fsuV1 T V : Set G)) _).mpr h
        exact this
      exact hne (inv_mul_mem_of_relIndex_two h12 S.u1_mem_V2 hmem S.u1_not_V1 hnot)
    have hu : k₁ * S.u1 * k₁⁻¹ = S.u1 := by
      rcases (S.mem_V1_iff).1 hku with h | h
      · calc k₁ * S.u1 * k₁⁻¹ = S.u1 * (S.u1⁻¹ * (k₁ * S.u1 * k₁⁻¹)) := by group
          _ = S.u1 := by rw [h, mul_one]
      · exfalso
        have hs : k₁ * S.u1 * k₁⁻¹ = S.u1 * S.z := by
          calc k₁ * S.u1 * k₁⁻¹ = S.u1 * (S.u1⁻¹ * (k₁ * S.u1 * k₁⁻¹)) := by group
            _ = S.u1 * S.z := by rw [h]
        have hj : ∀ j : ℕ, k₁ ^ j * S.u1 * (k₁ ^ j)⁻¹ = S.u1 * S.z ^ j := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
            calc k₁ ^ (j + 1) * S.u1 * (k₁ ^ (j + 1))⁻¹ =
                k₁ * (k₁ ^ j * S.u1 * (k₁ ^ j)⁻¹) * k₁⁻¹ := by group
              _ = (k₁ * S.u1 * k₁⁻¹) * (k₁ * S.z ^ j * k₁⁻¹) := by rw [ih]; group
              _ = S.u1 * S.z * S.z ^ j := by rw [hs, ← conj_pow, hkz]
              _ = S.u1 * S.z ^ (j + 1) := by rw [pow_succ']; group
        have hm2 := hj m
        rw [hk₁m, one_mul, inv_one, mul_one] at hm2
        obtain ⟨j, rfl⟩ := hm
        rw [pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul] at hm2
        exact S.z_ne_one (by
          have := congrArg (S.u1⁻¹ * ·) hm2
          simpa using this.symm)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    by_cases hy1 : y ∈ fsuV1 T V
    · have := hV1 y hy1
      calc y * k₁ = (k₁ * y * k₁⁻¹) * k₁ := by rw [this]
        _ = k₁ * y := by group
    · have h1 := inv_mul_mem_of_relIndex_two h12 S.u1_mem_V2 hy S.u1_not_V1 hy1
      have hw := hV1 _ h1
      have e : k₁ * y * k₁⁻¹ = y := by
        calc k₁ * y * k₁⁻¹ = (k₁ * S.u1 * k₁⁻¹) * (k₁ * (S.u1⁻¹ * y) * k₁⁻¹) := by group
          _ = y := by rw [hu, hw]; group
      calc y * k₁ = (k₁ * y * k₁⁻¹) * k₁ := by rw [e]
        _ = k₁ * y := by group
  exact Subgroup.subset_closure ⟨hk₁C, m, hm, hk₁m⟩


section CoverLt

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
  {τ : Perm (Fin 6)} {ρ' : ↥S.G1 →* Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  {K : Subgroup G}
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)

include hβk hβe hρ' hN' honto' in
theorem cover_weights :
    wtv ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) :
      Fin 6 → ZMod 2) = 4 ∧
    wtv ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
      Fin 6 → ZMod 2) = 4 ∧
    wtv (((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) :
      Fin 6 → ZMod 2) +
      ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
      Fin 6 → ZMod 2)) = 4 := by
  have h12 : S.u1 * S.u2 ∈ S.V3 := S.V3.mul_mem S.u1_mem_V3 S.u2_mem_V3
  refine ⟨S.cover_V3_weight hβk hβe hρ' hN' honto' S.u1_mem_V3 S.u1_not_V1,
    S.cover_V3_weight hβk hβe hρ' hN' honto' S.u2_mem_V3 S.u2_not_V1, ?_⟩
  rw [← S.cover_mul _ _ S.u1_mem_V3 S.u2_mem_V3]
  exact S.cover_V3_weight hβk hβe hρ' hN' honto' h12 S.u12_not_V1

include hβk hβe hρ' hN' honto' in
theorem V3_inf_U1c_le : S.V3 ⊓ S.U1c β ≤ fsuV1 T V := by
  rintro v ⟨hv3, hv1⟩
  by_contra hn
  have hw := S.cover_V3_weight hβk hβe hρ' hN' honto' hv3 hn
  obtain ⟨huU, hc⟩ := (S.mem_U1c).1 hv1
  rcases (mem_constWeight_iff _).1 hc with h | h
  · have h' : ((Multiplicative.toAdd (β ⟨v, S.V3_le_UH hv3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2) = 0 := congrArg Subtype.val h
    rw [h'] at hw
    exact absurd hw (by decide)
  · have h' : ((Multiplicative.toAdd (β ⟨v, S.V3_le_UH hv3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2) = onesV := congrArg Subtype.val h
    rw [h', wtv_ones] at hw
    exact absurd hw (by decide)

include hβs hβk hβe hρ' hN' honto' in
theorem card_V3_sup_U1c : Nat.card ↥(S.V3 ⊔ S.U1c β) = 16 := by
  have hN : S.V3 ≤ Subgroup.normalizer (S.U1c β : Set G) :=
    (S.V3_le_UH.trans S.UH_le_G1).trans (S.G1_le_normalizer_U1c hβe hβk)
  have h := card_sup_mul_card_inf' hN
  have hinf : S.V3 ⊓ S.U1c β = fsuV1 T V :=
    le_antisymm (S.V3_inf_U1c_le hβk hβe hρ' hN' honto') (le_inf S.V1_le_V3 (S.V1_le_U1c hβk))
  rw [hinf, S.card_V3, S.card_U1c hβs hβk, S.card_V1] at h
  omega

@[expose] noncomputable def UHperp
    (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)) : Subgroup G :=
  ((AddMonoidHom.toMultiplicative (dotHom ((Multiplicative.toAdd
    (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2))).comp β).ker.map
    (conjClosure S.V3 S.G1).subtype

theorem mem_UHperp {u : G} : u ∈ S.UHperp β ↔ ∃ hu : u ∈ conjClosure S.V3 S.G1,
    dotv ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2)
      ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2) = 0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, MonoidHom.mem_ker.1 hw⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, MonoidHom.mem_ker.2 h, rfl⟩

theorem UHperp_le_UH : S.UHperp β ≤ conjClosure S.V3 S.G1 := Subgroup.map_subtype_le _

include hβk hβe hρ' hN' honto' in
theorem V3_le_UHperp : S.V3 ≤ S.UHperp β := by
  intro v hv
  refine (S.mem_UHperp).2 ⟨S.V3_le_UH hv, ?_⟩
  obtain ⟨wa, wb, wab⟩ := S.cover_weights hβk hβe hρ' hN' honto'
  obtain ⟨haa, hba⟩ := dotv_syn _ _ wa wb wab
  rcases S.cover_inL_of_V3 hβk hv with h | h | h | h <;> rw [h]
  · exact dotv_zero _
  · exact haa
  · exact hba
  · rw [dotv_add, haa, hba, add_zero]

theorem U1c_le_UHperp : S.U1c β ≤ S.UHperp β := by
  intro u hu
  obtain ⟨huU, hc⟩ := (S.mem_U1c).1 hu
  refine (S.mem_UHperp).2 ⟨huU, ?_⟩
  rcases (mem_constWeight_iff _).1 hc with h | h
  · rw [show ((Multiplicative.toAdd (β ⟨u, huU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = 0 from
      congrArg Subtype.val h]
    exact dotv_zero _
  · rw [show ((Multiplicative.toAdd (β ⟨u, huU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = onesV
      from congrArg Subtype.val h, dotv_ones]
    exact sum_eq_zero _

include hβe in
theorem conj_mem_UHperp {k : G} (hk : k ∈ S.K2) {d : G} (hd : d ∈ S.UHperp β) :
    k * d * k⁻¹ ∈ S.UHperp β := by
  obtain ⟨hdU, h0⟩ := (S.mem_UHperp).1 hd
  have hkH := S.K2_le_G1 hk
  have hkd : k * d * k⁻¹ ∈ conjClosure S.V3 S.G1 :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hkH) d).mp hdU
  refine (S.mem_UHperp).2 ⟨hkd, ?_⟩
  have hku : k * S.u1 * k⁻¹ = S.u1 := by
    have h1 := Subgroup.mem_centralizer_iff.mp (S.K2_le_centralizer hk) S.u1 S.u1_mem_V2
    calc k * S.u1 * k⁻¹ = S.u1 * k * k⁻¹ := by rw [h1]
      _ = S.u1 := by group
  have ha := hβe ⟨k, hkH⟩ ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ hku.symm
  have hd' := hβe ⟨k, hkH⟩ ⟨d, hdU⟩ ⟨_, hkd⟩ rfl
  rw [hd']
  have ha' := congrArg Subtype.val ha
  rw [ha']
  exact (dotv_vp _ _ _).trans h0

include hβe hβk hρ' hN' honto' in
theorem U21_le_UHperp : S.U21 ≤ S.UHperp β :=
  conjClosure_le fun _ hk _ hv =>
    S.conj_mem_UHperp hβe hk (S.V3_le_UHperp hβk hβe hρ' hN' honto' hv)

include hβs hβk hβe hρ' hN' honto' in
theorem card_UHperp_le : Nat.card (S.UHperp β) ≤ 32 := by
  obtain ⟨wa, -, -⟩ := S.cover_weights hβk hβe hρ' hN' honto'
  obtain ⟨y, hy, hy1⟩ := exists_dotv_one _ wa
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd ⟨y, mem_ev_of_sum_zero hy⟩)
  have hlt : S.UHperp β < conjClosure S.V3 S.G1 := by
    refine lt_of_le_of_ne S.UHperp_le_UH fun h => ?_
    have huD : (u : G) ∈ S.UHperp β := by rw [h]; exact u.2
    obtain ⟨hu', h0⟩ := (S.mem_UHperp).1 huD
    have e : ((Multiplicative.toAdd (β ⟨(u : G), hu'⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) =
        y := by
      rw [show (⟨(u : G), hu'⟩ : ↥(conjClosure S.V3 S.G1)) = u from rfl, hu]
      rfl
    rw [e, hy1] at h0
    exact one_ne_zero h0
  have h64 := S.card_UH_cover hβs hβk
  have hd : Nat.card (S.UHperp β) ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← h64]
    exact Subgroup.card_dvd_of_le hlt.le
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have hne : Nat.card (S.UHperp β) ≠ 64 := fun h =>
    hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le (by rw [h, h64]))
  have hj5 : j ≤ 5 := by
    by_contra h
    have h6 : j = 6 := by omega
    rw [hjc, h6] at hne
    exact hne (by norm_num)
  rw [hjc]
  calc 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hj5
    _ = 32 := by norm_num

@[expose] def LnSub (a b : Fin 6 → ZMod 2) : AddSubgroup ↥(evenWeight 6) where
  carrier := {y | InLn a b (y : Fin 6 → ZMod 2)}
  add_mem' := fun hx hy => inLn_add hx hy
  zero_mem' := Or.inl (Or.inl rfl)
  neg_mem' := fun {y} hy => by
    have e : ((-y : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = (y : Fin 6 → ZMod 2) := by
      funext i
      exact ZMod.neg_eq_self_mod_two _
    show InLn a b _
    rw [e]
    exact hy

@[expose] noncomputable def UHline
    (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)) : Subgroup G :=
  ((AddSubgroup.toSubgroup (LnSub
    ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2)
    ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
      Fin 6 → ZMod 2))).comap β).map (conjClosure S.V3 S.G1).subtype

theorem mem_UHline {u : G} : u ∈ S.UHline β ↔ ∃ hu : u ∈ conjClosure S.V3 S.G1,
    InLn ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2)
      ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
        Fin 6 → ZMod 2)
      ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, h, rfl⟩

include hβk in
theorem V3_sup_U1c_le_UHline : S.V3 ⊔ S.U1c β ≤ S.UHline β := by
  refine sup_le (fun v hv => (S.mem_UHline).2 ⟨S.V3_le_UH hv, Or.inl (S.cover_inL_of_V3 hβk hv)⟩)
    fun u hu => ?_
  obtain ⟨huU, hc⟩ := (S.mem_U1c).1 hu
  refine (S.mem_UHline).2 ⟨huU, ?_⟩
  rcases (mem_constWeight_iff _).1 hc with h | h
  · left
    rw [show ((Multiplicative.toAdd (β ⟨u, huU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = 0 from
      congrArg Subtype.val h]
    exact Or.inl rfl
  · right
    rw [show ((Multiplicative.toAdd (β ⟨u, huU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = onesV
      from congrArg Subtype.val h]
    exact Or.inl (vadd_self _)

end CoverLt

end Setting4

theorem inL_of_inLn_four {a b y : Fin 6 → ZMod 2} (wa : wtv a = 4) (wb : wtv b = 4)
    (wab : wtv (a + b) = 4) (h : InLn a b y) (hy : wtv y = 4) : InL a b y := by
  rcases h with h | h
  · exact h
  exfalso
  have key : ∀ c, y + (fun _ => 1) = c → y = c + onesV := fun c hc => by
    rw [← hc, add_assoc]
    exact (add_zero y).symm.trans (congrArg (y + ·) (vadd_self _).symm)
  rcases h with h | h | h | h
  · have := key _ h
    rw [this, zero_add, wtv_ones] at hy
    exact absurd hy (by decide)
  · rw [key _ h, wtv_add_ones_four _ wa] at hy
    exact absurd hy (by decide)
  · rw [key _ h, wtv_add_ones_four _ wb] at hy
    exact absurd hy (by decide)
  · rw [key _ h, wtv_add_ones_four _ wab] at hy
    exact absurd hy (by decide)


namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section CoverLt2

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
  {τ : Perm (Fin 6)} {ρ' : ↥S.G1 →* Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  {K : Subgroup G}
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)

include hβk hβe hρ' hN' honto' in
theorem exists_K2_moves_cover (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, ρ k = σ) :
    ∃ k ∈ S.K2, ∃ hw : k * S.u2 * k⁻¹ ∈ conjClosure S.V3 S.G1,
      ¬ InL ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) : ↥(evenWeight 6)) :
          Fin 6 → ZMod 2)
        ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) : ↥(evenWeight 6)) :
          Fin 6 → ZMod 2)
        ((Multiplicative.toAdd (β ⟨_, hw⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) ∧
      wtv ((Multiplicative.toAdd (β ⟨_, hw⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = 4 := by
  obtain ⟨wa, wb, wab⟩ := S.cover_weights hβk hβe hρ' hN' honto'
  obtain ⟨σ, hσ, hσa, hσb, hσb2⟩ := tri15_moves _ _ wa wb wab
  obtain ⟨hs, h3⟩ := tri15_facts σ hσ
  obtain ⟨k₀, hk₀⟩ := honto σ (Perm.mem_alternatingGroup.mpr hs)
  have hUN : ∀ h ∈ S.G1, ∀ x ∈ conjClosure S.V3 S.G1, h * x * h⁻¹ ∈ conjClosure S.V3 S.G1 :=
    fun h hh x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hh) x).mp hx
  have hk₀U := hUN _ k₀.2 _ (S.V3_le_UH S.u1_mem_V3)
  have he := hβe k₀ ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ ⟨_, hk₀U⟩ rfl
  have hb : β ⟨_, hk₀U⟩ = β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ := by
    refine S.cover_coe_eq ?_
    rw [he]
    show vp (ρ k₀) _ = _
    rw [hk₀]
    exact hσa
  have h1 := S.mem_V1_of_beta_eq hβk hb
  have hku : S.u1⁻¹ * ((k₀ : G) * S.u1 * (k₀ : G)⁻¹) ∈ fsuV1 T V := by
    have hc : S.u1⁻¹ * (((k₀ : G) * S.u1 * (k₀ : G)⁻¹) * S.u1⁻¹) * S.u1 =
        ((k₀ : G) * S.u1 * (k₀ : G)⁻¹) * S.u1⁻¹ := by
      rcases (S.mem_V1_iff).1 h1 with h | h
      · rw [h]; group
      · rw [h]
        have hz : S.u1⁻¹ * S.z * S.u1 = S.z := by
          have := isElemAbelian_comm S.elemAbelian_V S.u1_mem_V S.z_mem_V
          calc S.u1⁻¹ * S.z * S.u1 = S.u1⁻¹ * (S.z * S.u1) := by group
            _ = S.u1⁻¹ * (S.u1 * S.z) := by rw [this]
            _ = S.z := by group
        exact hz
    have e : S.u1⁻¹ * ((k₀ : G) * S.u1 * (k₀ : G)⁻¹) =
        S.u1⁻¹ * (((k₀ : G) * S.u1 * (k₀ : G)⁻¹) * S.u1⁻¹) * S.u1 := by group
    rw [e, hc]
    exact h1
  have hk₀N := S.normalizes_V2_of k₀.2 hku
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (k₀ : G)).ne'
  have hk₁m : ((k₀ : G) ^ (2 ^ e)) ^ m = 1 := by
    rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hk₁H : (k₀ : G) ^ (2 ^ e) ∈ S.G1 := S.G1.pow_mem k₀.2 _
  have hk₁N : (k₀ : G) ^ (2 ^ e) ∈ Subgroup.normalizer (S.V2 : Set G) := Subgroup.pow_mem _ hk₀N _
  have hk₁K := S.mem_K2_of_odd hk₁H hk₁N hm hk₁m
  have hρk₁ : ρ ⟨(k₀ : G) ^ (2 ^ e), hk₁H⟩ = σ ^ (2 ^ e) := by
    rw [← hk₀, ← map_pow]
    rfl
  have hσe : σ ^ (2 ^ e) = σ ∨ σ ^ (2 ^ e) = σ * σ := by
    rw [pow_eq_pow_mod (2 ^ e) h3]
    have h0 : 2 ^ e % 3 ≠ 0 := by
      intro h0
      have h3d : 3 ∣ 2 ^ e := Nat.dvd_of_mod_eq_zero h0
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
      omega
    have hlt := Nat.mod_lt (2 ^ e) (show 3 > 0 by norm_num)
    rcases (show 2 ^ e % 3 = 1 ∨ 2 ^ e % 3 = 2 by omega) with h | h <;> rw [h]
    · left; exact pow_one σ
    · right; exact pow_two σ
  have hwU := hUN _ hk₁H _ (S.V3_le_UH S.u2_mem_V3)
  refine ⟨_, hk₁K, hwU, ?_, ?_⟩
  · have hw := hβe ⟨_, hk₁H⟩ ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩ ⟨_, hwU⟩ rfl
    rw [hw]
    show ¬ InL _ _ (vp (ρ ⟨_, hk₁H⟩) _)
    rw [hρk₁]
    rcases hσe with h | h <;> rw [h]
    · exact hσb
    · rw [vp_mul]
      exact hσb2
  · have hw := hβe ⟨_, hk₁H⟩ ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩ ⟨_, hwU⟩ rfl
    rw [hw]
    show wtv (vp (ρ ⟨_, hk₁H⟩) _) = 4
    rw [wtv_vp]
    exact wb

include hβs hβk hβe hρ' hN' honto' in
theorem card_UH_inf_W {W : Subgroup G} (hUW : S.U0c β ≤ W)
    (hWU : W < conjClosure (conjClosure S.V3 S.G1) L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    {c : G} (hcH : c ∈ S.G1) (hcL : c ∈ L) (hc3 : c ^ 3 = 1) (hfp : ∀ i, ρ ⟨c, hcH⟩ i ≠ i) :
    Nat.card ↥(conjClosure S.V3 S.G1 ⊓ W) = 16 := by
  have hU64 := S.card_UH_cover hβs hβk
  have hU1W : S.U1c β ≤ W := (le_conjClosure (S.U1c β) L).trans hUW
  have hVW : V ≤ W := (S.V_le_U0c hβk).trans hUW
  have hle : S.V3 ⊔ S.U1c β ≤ conjClosure S.V3 S.G1 ⊓ W :=
    sup_le (le_inf S.V3_le_UH (S.V3_le_V.trans hVW)) (le_inf S.U1c_le_UH hU1W)
  have h16 : 16 ∣ Nat.card ↥(conjClosure S.V3 S.G1 ⊓ W) := by
    rw [← S.card_V3_sup_U1c hβs hβk hβe hρ' hN' honto']
    exact Subgroup.card_dvd_of_le hle
  have h64 : Nat.card ↥(conjClosure S.V3 S.G1 ⊓ W) ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← hU64]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h64
  rw [hjc] at h16 ⊢
  interval_cases j
  · norm_num at h16
  · norm_num at h16
  · norm_num at h16
  · norm_num at h16
  · norm_num
  ·
    exfalso
    have h2 : (conjClosure S.V3 S.G1 ⊓ W).relIndex (conjClosure S.V3 S.G1) = 2 := by
      have h1 := Subgroup.relIndex_mul_card (conjClosure S.V3 S.G1 ⊓ W) (conjClosure S.V3 S.G1)
      rw [inf_eq_left.2 (inf_le_left : conjClosure S.V3 S.G1 ⊓ W ≤ _), hjc, hU64] at h1
      omega
    have hUN : ∀ h ∈ S.G1, ∀ x ∈ conjClosure S.V3 S.G1, h * x * h⁻¹ ∈ conjClosure S.V3 S.G1 :=
      fun h hh x hx =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hh) x).mp hx
    refine false_of_relIndex_two_cube (x := c)
      (mem_normalizer_inf_two (le_normalizer_conjClosure S.V3 S.G1 hcH) (hLW hcL))
      (fun y hy => hUN c hcH y hy) (fun y hy => ?_) (fun y hy => ?_) h2
    ·
      have hyy : y * y ∈ fsuV1 T V := by
        refine (hβk ⟨y * y, (conjClosure S.V3 S.G1).mul_mem hy hy⟩).1 ?_
        have e : (⟨y * y, (conjClosure S.V3 S.G1).mul_mem hy hy⟩ : ↥(conjClosure S.V3 S.G1)) =
            ⟨y, hy⟩ * ⟨y, hy⟩ := rfl
        rw [e, map_mul]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_one, ew_add_self]
      have hV1 : fsuV1 T V ≤ conjClosure S.V3 S.G1 ⊓ W :=
        S.V1_le_V3.trans (le_sup_left.trans hle)
      exact hV1 hyy
    ·
      have hy1 := hUN c hcH y hy
      have hy2 := hUN c hcH _ hy1
      have hm : y * (c * y * c⁻¹) * (c * (c * y * c⁻¹) * c⁻¹) ∈ conjClosure S.V3 S.G1 :=
        (conjClosure S.V3 S.G1).mul_mem ((conjClosure S.V3 S.G1).mul_mem hy hy1) hy2
      refine (le_sup_right.trans hle) ((S.mem_U1c).2 ⟨hm, ?_⟩)
      have e : (⟨_, hm⟩ : ↥(conjClosure S.V3 S.G1)) = ⟨y, hy⟩ * ⟨_, hy1⟩ * ⟨_, hy2⟩ := rfl
      rw [e, map_mul β, map_mul β, toAdd_mul, toAdd_mul]
      have he1 := hβe ⟨c, hcH⟩ ⟨y, hy⟩ ⟨_, hy1⟩ rfl
      have he2 := hβe ⟨c, hcH⟩ ⟨_, hy1⟩ ⟨_, hy2⟩ rfl
      rw [he2, he1]
      have hρ3 : ρ ⟨c, hcH⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨c, hcH⟩ : ↥S.G1) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
        rw [this, map_one]
      rcases fpf3_sum_const _ hρ3 hfp _ (sum_eq_zero (Multiplicative.toAdd (β ⟨y, hy⟩))) with
        h | h
      · exact (mem_constWeight_iff _).2 (Or.inl (Subtype.ext h))
      · exact (mem_constWeight_iff _).2 (Or.inr (Subtype.ext h))
  ·
    exfalso
    have e : conjClosure S.V3 S.G1 ⊓ W = conjClosure S.V3 S.G1 :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hjc, hU64]; norm_num)
    have hUW' : conjClosure S.V3 S.G1 ≤ W := by rw [← e]; exact inf_le_right
    have : conjClosure (conjClosure S.V3 S.G1) L ≤ W := conjClosure_le fun l hl u hu =>
      (Subgroup.mem_normalizer_iff.mp (hLW hl) u).mp (hUW' hu)
    exact hWU.not_ge this

end CoverLt2

end Setting4

end CFSG.Quasithin.H13.A6
