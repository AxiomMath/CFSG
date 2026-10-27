module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26a
public import CFSG.Quasithin.Background.F9FiveStruct

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom

namespace S126L26

variable {G : Type*} [Group G]

theorem hI_inv {V Q : Subgroup G} {g : G} (hQ : g ∈ Subgroup.normalizer (Q : Set G))
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ Q) :
    ¬ ∀ x ∈ V ⊔ conjSub g⁻¹⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ Q := by
  intro hall
  apply hI
  intro x hx
  have hK : V ⊔ conjSub g⁻¹ V ≤ conjSub g⁻¹ (V ⊔ conjSub g⁻¹⁻¹ V) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [mem_conjSub]
      refine Subgroup.mem_sup_right ?_
      rw [mem_conjSub]
      have e : g⁻¹⁻¹⁻¹ * (g⁻¹⁻¹ * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rw [e]
      exact hy
    · rw [mem_conjSub] at hy ⊢
      exact Subgroup.mem_sup_left hy
  obtain ⟨n, hn⟩ := hall _ (mem_conjSub.mp (hK hx))
  rw [inv_inv, conj_pow] at hn
  refine ⟨n, ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hQ) _).mp hn
  have e : g⁻¹ * (g * x ^ 2 ^ n * g⁻¹) * g⁻¹⁻¹ = x ^ 2 ^ n := by group
  rwa [e] at this

theorem mem_or_inv_mul_mem {Vp V : Subgroup G} (hidx : Vp.relIndex V = 2) {v w : G}
    (hv : v ∈ V) (hvp : v ∉ Vp) (hw : w ∈ V) : w ∈ Vp ∨ v⁻¹ * w ∈ Vp := by
  by_cases hwp : w ∈ Vp
  · exact Or.inl hwp
  right
  have key := Subgroup.mul_mem_iff_of_index_two (H := Vp.subgroupOf V) hidx
    (a := (⟨v, hv⟩ : ↥V)⁻¹) (b := ⟨w, hw⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at key
  refine key.2 (iff_of_false (fun h => hvp ?_) hwp)
  have := Vp.inv_mem h
  rwa [inv_inv] at this

theorem comm_mul_mem {V₁ : Subgroup G} {b v p : G} (hvN : v ∈ Subgroup.normalizer (V₁ : Set G))
    (h1 : b * v * b⁻¹ * v⁻¹ ∈ V₁) (h2 : b * p * b⁻¹ * p⁻¹ ∈ V₁) :
    b * (v * p) * b⁻¹ * (v * p)⁻¹ ∈ V₁ := by
  have h3 : v * (b * p * b⁻¹ * p⁻¹) * v⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hvN _).mp h2
  have e : b * (v * p) * b⁻¹ * (v * p)⁻¹ =
      (b * v * b⁻¹ * v⁻¹) * (v * (b * p * b⁻¹ * p⁻¹) * v⁻¹) := by group
  rw [e]
  exact V₁.mul_mem h1 h3

theorem conj_comm {X : Subgroup G} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (k : G) :
    ∀ a ∈ conjSub k X, ∀ b ∈ conjSub k X, a * b = b * a := by
  intro a ha b hb
  have e := hX _ (mem_conjSub.mp ha) _ (mem_conjSub.mp hb)
  have e2 : k⁻¹ * (a * b) * k = k⁻¹ * (b * a) * k := by
    calc k⁻¹ * (a * b) * k = k⁻¹ * a * k * (k⁻¹ * b * k) := by group
      _ = k⁻¹ * b * k * (k⁻¹ * a * k) := e
      _ = k⁻¹ * (b * a) * k := by group
  simpa using e2

theorem conj_sq {X : Subgroup G} (hX : ∀ a ∈ X, a * a = 1) (k : G) :
    ∀ a ∈ conjSub k X, a * a = 1 := by
  intro a ha
  have e := hX _ (mem_conjSub.mp ha)
  have e2 : a * a = k * (k⁻¹ * a * k * (k⁻¹ * a * k)) * k⁻¹ := by group
  rw [e2, e]
  group

section Hyp

variable [Finite G] {T V L V₁ Vp H : Subgroup G} (h : HypF91 T V L V₁ Vp H)
include h

theorem comm_V (hidx : Vp.relIndex V = 2) (hV : ¬ V ≤ pCoreOf 2 H) {v b : G} (hv : v ∈ V)
    (hb : b ∈ pCoreOf 2 H) : v * b * v⁻¹ * b⁻¹ ∈ Vp := by
  rw [(h.F95_1 hidx hV).1]
  have hQn := le_normalizer_pCoreOf 2 H
  have hvH : v ∈ H := h.V_le_H hv
  have hbT : b ∈ T := isSylowTwoOf_pCoreOf_le h.sylow_H hb
  refine ⟨?_, ?_⟩
  · have h1 : b * v⁻¹ * b⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (h.T_normalizes_V hbT) _).mp (V.inv_mem hv)
    have := V.mul_mem hv h1
    simpa [mul_assoc] using this
  · have h1 : v * b * v⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_normalizer_iff.mp (hQn hvH) b).mp hb
    exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hb)

theorem comm_Vp_Vpg {g : G} (hg : g ∈ H) {a b : G} (ha : a ∈ Vp) (hb : b ∈ conjSub g⁻¹ Vp) :
    a * b * a⁻¹ * b⁻¹ ∈ V₁ := by
  have hbU : b ∈ conjClosure Vp H := HypF91.conjSub_inv_le_U hg (le_conjClosure Vp H) hb
  have haQ : a ∈ pCoreOf 2 H := h.Vp_le_pCoreOf_and_commutator_le.1 ha
  have := V₁.inv_mem (h.commutator_conjClosure_le b hbU a haQ)
  convert this using 1
  group

theorem setup (hidx : Vp.relIndex V = 2) (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    (hcard : Nat.card Vp = 32)
    (hC : Subgroup.centralizer (Vp : Set G) ≤ Subgroup.centralizer (V : Set G))
    {g : G} (hg : g ∈ H) (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H)
    {v : G} (hv : v ∈ V) (hvp : v ∉ Vp) :
    S126Crd.Setup V₁ Vp (conjSub g⁻¹ Vp) v (g⁻¹ * v * g) := by
  have hH := h.H_normalizes_V₁
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hVpQ : Vp ≤ pCoreOf 2 H := (le_conjClosure Vp H).trans hUQ
  have hBU : conjSub g⁻¹ Vp ≤ conjClosure Vp H :=
    HypF91.conjSub_inv_le_U hg (le_conjClosure Vp H)
  have hBQ : conjSub g⁻¹ Vp ≤ pCoreOf 2 H := hBU.trans hUQ
  have hgV₁ : conjSub g⁻¹ V₁ = V₁ := F7.conjSub_eq_of_mem_normalizer (hH (H.inv_mem hg))
  have hZB : V₁ ≤ conjSub g⁻¹ Vp := by
    rw [← hgV₁]
    exact conjSub_mono _ h.V₁_le_Vp
  have hcommA : ∀ a ∈ Vp, ∀ a' ∈ Vp, a * a' = a' * a := fun a ha a' ha' =>
    isElemAbelian_comm h.elemAbelian_Vp ha ha'
  have hsqA : ∀ a ∈ Vp, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact isElemAbelian_pow_eq_one h.elemAbelian_Vp ha
  have hvH : v ∈ H := h.V_le_H hv
  have hiH : g⁻¹ * v * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) hvH) hg
  have hD' := h.F95_D_eq hyp5 (H.inv_mem hg) (hI_inv (le_normalizer_pCoreOf 2 H hg) hI)
  have hD := h.F95_D_eq hyp5 hg hI
  have vinj : ∀ b ∈ conjSub g⁻¹ Vp, v * b * v⁻¹ * b⁻¹ ∈ V₁ → b ∈ V₁ := by
    intro b hb hvb
    have hc : g * b * g⁻¹ ∈ Vp := by
      have := mem_conjSub.mp hb
      rwa [inv_inv] at this
    have hVcomm : ∀ u ∈ V, b * u * b⁻¹ * u⁻¹ ∈ V₁ := by
      intro u hu
      rcases mem_or_inv_mul_mem hidx hv hvp hu with hup | hup
      · exact h.commutator_conjClosure_le b (hBU hb) _ (hVpQ hup)
      · have e : u = v * (v⁻¹ * u) := by group
        rw [e]
        refine comm_mul_mem (hH hvH) ?_ (h.commutator_conjClosure_le b (hBU hb) _ (hVpQ hup))
        have := V₁.inv_mem hvb
        convert this using 1
        group
    have hcD : g * b * g⁻¹ ∈ centralizerMod V₁ Vp (conjSub g⁻¹⁻¹ V) := by
      refine ⟨hc, hH (h.Vp_le_H hc), fun w hw => ?_⟩
      have hu : g⁻¹ * w * g ∈ V := by
        have := mem_conjSub.mp hw
        simp only [inv_inv] at this
        exact this
      have := (Subgroup.mem_normalizer_iff.mp (hH hg) _).mp (hVcomm _ hu)
      convert this using 1
      group
    rw [hD'] at hcD
    have := (Subgroup.mem_normalizer_iff.mp (hH (H.inv_mem hg)) _).mp hcD
    convert this using 1
    group
  have iinj : ∀ a ∈ Vp, g⁻¹ * v * g * a * (g⁻¹ * v * g)⁻¹ * a⁻¹ ∈ V₁ → a ∈ V₁ := by
    intro a ha hia
    have haD : a ∈ centralizerMod V₁ Vp (conjSub g⁻¹ V) := by
      refine ⟨ha, hH (h.Vp_le_H ha), fun w hw => ?_⟩
      have hu : g * w * g⁻¹ ∈ V := by
        have := mem_conjSub.mp hw
        rwa [inv_inv] at this
      rcases mem_or_inv_mul_mem hidx hv hvp hu with hup | hup
      · refine comm_Vp_Vpg h hg ha ?_
        rw [mem_conjSub, inv_inv]
        exact hup
      · have hp' : g⁻¹ * (v⁻¹ * (g * w * g⁻¹)) * g ∈ conjSub g⁻¹ Vp := by
          rw [mem_conjSub, inv_inv]
          have e : g * (g⁻¹ * (v⁻¹ * (g * w * g⁻¹)) * g) * g⁻¹ = v⁻¹ * (g * w * g⁻¹) := by
            group
          rw [e]
          exact hup
        have e : w = g⁻¹ * v * g * (g⁻¹ * (v⁻¹ * (g * w * g⁻¹)) * g) := by group
        rw [e]
        refine comm_mul_mem (hH hiH) ?_ (comm_Vp_Vpg h hg ha hp')
        have := V₁.inv_mem hia
        convert this using 1
        group
    rw [hD] at haD
    exact haD
  exact
    { card_Z := h.card_V₁
      Z_le_A := h.V₁_le_Vp
      Z_le_B := hZB
      comm_A := hcommA
      comm_B := conj_comm hcommA g⁻¹
      sq_A := hsqA
      sq_B := conj_sq hsqA g⁻¹
      card_A := hcard
      card_B := by rw [card_conjSub]; exact hcard
      comm_AB := fun a ha b hb => comm_Vp_Vpg h hg ha hb
      nondeg := fun b hb hcomm => by
        have hbC : b ∈ Subgroup.centralizer (Vp : Set G) :=
          Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha
        have hbV := Subgroup.mem_centralizer_iff.mp (hC hbC) v hv
        refine vinj b hb ?_
        rw [hbV, mul_inv_cancel_right, mul_inv_cancel]
        exact V₁.one_mem
      v_A := fun a ha => isElemAbelian_comm h.elemAbelian hv (h.Vp_le_V ha)
      v_B := fun b hb => comm_V h hidx hV hv (hBQ hb)
      v_inj := vinj
      i_B := fun b hb => by
        have hc : g * b * g⁻¹ ∈ V := by
          have := mem_conjSub.mp hb
          rw [inv_inv] at this
          exact h.Vp_le_V this
        have e := isElemAbelian_comm h.elemAbelian hv hc
        calc g⁻¹ * v * g * b = g⁻¹ * (v * (g * b * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * b * g⁻¹ * v) * g := by rw [e]
          _ = b * (g⁻¹ * v * g) := by group
      i_A := fun a ha => by
        rw [mem_conjSub, inv_inv]
        have haQ : g * a * g⁻¹ ∈ pCoreOf 2 H :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) a).mp (hVpQ ha)
        have := comm_V h hidx hV hv haQ
        convert this using 1
        group
      i_inj := iinj }

theorem pow_mem (hidx : Vp.relIndex V = 2) (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    (hcard : Nat.card Vp = 32)
    (hC : Subgroup.centralizer (Vp : Set G) ≤ Subgroup.centralizer (V : Set G))
    {g : G} (hg : g ∈ H) (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H)
    {v : G} (hv : v ∈ V) (hvp : v ∉ Vp) :
    (v * (g⁻¹ * v * g)) ^ 5 ∈ pCoreOf 2 H ∨ (v * (g⁻¹ * v * g)) ^ 6 ∈ pCoreOf 2 H := by
  have hS := setup h hidx hV hyp5 hcard hC hg hI hv hvp
  have hF := h.F95_5 hidx hV hyp5 hg hI
  have hH := h.H_normalizes_V₁
  have hVgH := h.conjSub_inv_le_H hg
  have hiI : g⁻¹ * v * g ∈ V ⊔ conjSub g⁻¹ V := by
    refine Subgroup.mem_sup_right ?_
    rw [mem_conjSub]
    have e : g⁻¹⁻¹ * (g⁻¹ * v * g) * g⁻¹ = v := by group
    rw [e]
    exact hv
  have hxI : v * (g⁻¹ * v * g) ∈ V ⊔ conjSub g⁻¹ V :=
    (V ⊔ conjSub g⁻¹ V).mul_mem (Subgroup.mem_sup_left hv) hiI
  have hIH : V ⊔ conjSub g⁻¹ V ≤ H := sup_le h.V_le_H hVgH
  have hVpN : Vp ≤ Subgroup.normalizer (V₁ : Set G) := h.Vp_le_H.trans hH
  have hVpgN : conjSub g⁻¹ Vp ≤ Subgroup.normalizer (V₁ : Set G) :=
    (conjSub_mono _ h.Vp_le_V).trans (hVgH.trans hH)
  have key : ∀ k : ℕ,
      (∀ a ∈ Vp, (v * (g⁻¹ * v * g)) ^ k * a * ((v * (g⁻¹ * v * g)) ^ k)⁻¹ * a⁻¹ ∈ V₁) →
      (∀ b ∈ conjSub g⁻¹ Vp,
        (v * (g⁻¹ * v * g)) ^ k * b * ((v * (g⁻¹ * v * g)) ^ k)⁻¹ * b⁻¹ ∈ V₁) →
      (v * (g⁻¹ * v * g)) ^ k ∈ pCoreOf 2 H := by
    intro k hA hB
    have hk : (v * (g⁻¹ * v * g)) ^ k ∈ V ⊔ conjSub g⁻¹ V := Subgroup.pow_mem _ hxI k
    have hmem : (v * (g⁻¹ * v * g)) ^ k ∈
        centralizerMod V₁ (V ⊔ conjSub g⁻¹ V) (Vp ⊔ conjSub g⁻¹ Vp) := by
      rw [centralizerMod_sup_right hVpN hVpgN]
      exact ⟨⟨hk, hH (hIH hk), hA⟩, ⟨hk, hH (hIH hk), hB⟩⟩
    rw [hF.faithful] at hmem
    exact hmem.2
  rcases hS.pow_five_or_six with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (key 5 h1 h2)
  · exact Or.inr (key 6 h1 h2)

theorem inverted_pow_mem (hidx : Vp.relIndex V = 2)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    (hcard : Nat.card Vp = 32)
    (hC : Subgroup.centralizer (Vp : Set G) ≤ Subgroup.centralizer (V : Set G))
    {v x : G} (hv : v ∈ V) (hvQ : v ∉ pCoreOf 2 H) (hx : x ∈ H)
    (hinv : v * x * v⁻¹ * x ∈ pCoreOf 2 H) {m : ℕ} (hodd : x ^ (2 * m + 1) ∈ pCoreOf 2 H) :
    x ^ 3 ∈ pCoreOf 2 H ∨ x ^ 5 ∈ pCoreOf 2 H := by
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hvQ (hle hv)
  have hVpQ : Vp ≤ pCoreOf 2 H := (le_conjClosure Vp H).trans h.conjClosure_Vp_le_pCoreOf
  have hvp : v ∉ Vp := fun hvp => hvQ (hVpQ hvp)
  have hvH : v ∈ H := h.V_le_H hv
  let N : Subgroup ↥H := (pCoreOf 2 H).subgroupOf H
  have : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr (le_normalizer_pCoreOf 2 H)
  have hmem : ∀ y : ↥H, ((y : ↥H ⧸ N) = 1) ↔ (y : G) ∈ pCoreOf 2 H := fun y =>
    (QuotientGroup.eq_one_iff y).trans Subgroup.mem_subgroupOf
  let a : ↥H := ⟨v, hvH⟩
  let b : ↥H := ⟨x, hx⟩
  set A : ↥H ⧸ N := (a : ↥H ⧸ N) with hA
  set B : ↥H ⧸ N := (b : ↥H ⧸ N) with hB
  have hA2 : A * A = 1 := by
    rw [hA, ← QuotientGroup.mk_mul, hmem]
    show v * v ∈ pCoreOf 2 H
    rw [← pow_two, isElemAbelian_pow_eq_one h.elemAbelian hv]
    exact (pCoreOf 2 H).one_mem
  have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA2
  have hAB : A * B * A⁻¹ = B⁻¹ := by
    have h1 : A * B * A⁻¹ * B = 1 := by
      rw [hA, hB, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, hmem]
      exact hinv
    exact eq_inv_of_mul_eq_one_left h1
  have hBodd : B ^ (2 * m + 1) = 1 := by
    rw [hB, ← QuotientGroup.mk_pow, hmem]
    exact hodd
  have hY : ((a * ((b ^ m)⁻¹ * a * b ^ m) : ↥H) : ↥H ⧸ N) = B⁻¹ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, ← hA, ← hB]
    have h0 : A * B⁻¹ * A⁻¹ = B := by
      calc A * B⁻¹ * A⁻¹ = (A * B * A⁻¹)⁻¹ := by group
        _ = B := by rw [hAB, inv_inv]
    have h1 : A * (B ^ m)⁻¹ * A⁻¹ = B ^ m := by
      rw [← inv_pow, ← conj_pow, h0]
    have h2 : B ^ m * B ^ m = B⁻¹ := by
      rw [← pow_add, eq_inv_iff_mul_eq_one, ← pow_succ, ← two_mul]
      exact hBodd
    calc A * ((B ^ m)⁻¹ * A * B ^ m) = A * (B ^ m)⁻¹ * A⁻¹ * B ^ m := by
          rw [hAinv]; simp only [mul_assoc]
      _ = B⁻¹ := by rw [h1, h2]
  have hyG : ((a * ((b ^ m)⁻¹ * a * b ^ m) : ↥H) : G) = v * ((x ^ m)⁻¹ * v * x ^ m) := rfl
  by_cases hxQ : x ∈ pCoreOf 2 H
  · left
    exact Subgroup.pow_mem _ hxQ 3
  have hI : ¬ ∀ z ∈ V ⊔ conjSub (x ^ m)⁻¹ V, ∃ n : ℕ, z ^ 2 ^ n ∈ pCoreOf 2 H := by
    intro hall
    have hiI : (x ^ m)⁻¹ * v * x ^ m ∈ V ⊔ conjSub (x ^ m)⁻¹ V := by
      refine Subgroup.mem_sup_right ?_
      rw [mem_conjSub]
      have e : (x ^ m)⁻¹⁻¹ * ((x ^ m)⁻¹ * v * x ^ m) * (x ^ m)⁻¹ = v := by group
      rw [e]
      exact hv
    obtain ⟨n, hn⟩ := hall _ ((V ⊔ conjSub (x ^ m)⁻¹ V).mul_mem (Subgroup.mem_sup_left hv) hiI)
    rw [← hyG, ← SubgroupClass.coe_pow, ← hmem, QuotientGroup.mk_pow, hY, inv_pow,
      inv_eq_one] at hn
    have hcop : Nat.Coprime (2 ^ n) (2 * m + 1) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (odd_two_mul_add_one m))
    have ho : orderOf B = 1 :=
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hn) hcop).eq_one_of_dvd
        (orderOf_dvd_of_pow_eq_one hBodd)
    rw [orderOf_eq_one_iff, hB, hmem] at ho
    exact hxQ ho
  rcases pow_mem h hidx hV hyp5 hcard hC (H.pow_mem hx m) hI hv hvp with h5 | h6
  · right
    rw [← hyG, ← SubgroupClass.coe_pow, ← hmem, QuotientGroup.mk_pow, hY, inv_pow,
      inv_eq_one] at h5
    have := (hmem (b ^ 5)).mp (by rw [QuotientGroup.mk_pow]; exact h5)
    rwa [SubgroupClass.coe_pow] at this
  · left
    rw [← hyG, ← SubgroupClass.coe_pow, ← hmem, QuotientGroup.mk_pow, hY, inv_pow,
      inv_eq_one] at h6
    have ho6 : orderOf B ∣ 6 := orderOf_dvd_of_pow_eq_one h6
    have hoo : orderOf B ∣ 2 * m + 1 := orderOf_dvd_of_pow_eq_one hBodd
    have ho3 : orderOf B ∣ 3 := by
      obtain ⟨o, ho⟩ : ∃ o, orderOf B = o := ⟨_, rfl⟩
      rw [ho] at ho6 hoo ⊢
      have hle : o ≤ 6 := Nat.le_of_dvd (by norm_num) ho6
      interval_cases o <;> omega
    have h3 : B ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp ho3
    have := (hmem (b ^ 3)).mp (by rw [QuotientGroup.mk_pow]; exact h3)
    rwa [SubgroupClass.coe_pow] at this

end Hyp

end S126L26

end CFSG.Quasithin.H13
