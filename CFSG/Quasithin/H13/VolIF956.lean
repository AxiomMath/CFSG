module

public import CFSG.Quasithin.H13.A5Inputs2
public import CFSG.Quasithin.H13.VolIF956Core
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.G118S3
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open Subgroup

theorem card_le_ncard_of_forall_mem {Q : Type*} [Finite Q] {S : Set Q} (h : ∀ q, q ∈ S) :
    Nat.card Q ≤ S.ncard := by
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard fun q _ => h q

theorem nonempty_mulEquiv_perm_three_of_involutions {Q : Type*} [Group Q] [Finite Q] {a b : Q}
    (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 3 = 1) (ha1 : a ≠ 1)
    (hgen : closure ({a, b} : Set Q) = ⊤) (hnot : ¬ ∀ q : Q, ∃ n : ℕ, q ^ 2 ^ n = 1) :
    Nonempty (Q ≃* Equiv.Perm (Fin 3)) := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hx2 : a * b * (a * b) = b * a := by
    have h3 : a * b * (a * b) * (a * b) = 1 := by rw [← pow_three']; exact hab
    calc a * b * (a * b) = a * b * (a * b) * (a * b) * (a * b)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [h3, one_mul]
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  have hbab : b * a * b = a * b * a := by
    calc b * a * b = a * b * (a * b) * b := by rw [hx2]
      _ = a * b * a * (b * b) := by simp only [mul_assoc]
      _ = a * b * a := by rw [hb, mul_one]
  have r4 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have r6 : a * (a * b * a) = b * a := by rw [← mul_assoc, ← mul_assoc, ha, one_mul]
  have r10 : b * (a * b) = a * b * a := by rw [← mul_assoc, hbab]
  have r11 : b * (b * a) = a := by rw [← mul_assoc, hb, one_mul]
  have r12 : b * (a * b * a) = a * b := by
    calc b * (a * b * a) = b * a * b * a := by simp only [mul_assoc]
      _ = a * b * a * a := by rw [hbab]
      _ = a * b := by rw [mul_assoc (a * b) a a, ha, mul_one]
  have hstep : ∀ x ∈ ({a, b} : Set Q), ∀ y ∈ ({1, a, b, a * b, b * a, a * b * a} : Set Q),
      x * y ∈ ({1, a, b, a * b, b * a, a * b * a} : Set Q) := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy | hy | hy | hy | hy <;> subst x <;> subst y
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl r4))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mul_assoc _ _ _).symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl r6))))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inl hb
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr r10))))
    · exact Or.inr (Or.inl r11)
    · exact Or.inr (Or.inr (Or.inr (Or.inl r12)))
  have hall : ∀ q : Q, q ∈ ({1, a, b, a * b, b * a, a * b * a} : Set Q) := by
    intro q
    have hq : q ∈ closure ({a, b} : Set Q) := by rw [hgen]; exact mem_top q
    induction hq using closure_induction_left with
    | one => exact Or.inl rfl
    | mul_left x hx y _ ih => exact hstep x hx y ih
    | inv_mul_cancel x hx y _ ih =>
      have hxinv : x⁻¹ = x := by
        rcases hx with hx | hx
        · rw [hx, ha']
        · rw [Set.mem_singleton_iff.1 hx, hb']
      rw [hxinv]
      exact hstep x hx y ih
  have h6 : Nat.card Q ≤ 6 := by
    refine (card_le_ncard_of_forall_mem hall).trans ?_
    have h1 := Set.ncard_insert_le (1 : Q) ({a, b, a * b, b * a, a * b * a} : Set Q)
    have h2 := Set.ncard_insert_le a ({b, a * b, b * a, a * b * a} : Set Q)
    have h3 := Set.ncard_insert_le b ({a * b, b * a, a * b * a} : Set Q)
    have h4 := Set.ncard_insert_le (a * b) ({b * a, a * b * a} : Set Q)
    have h5 := Set.ncard_insert_le (b * a) ({a * b * a} : Set Q)
    have h6 := Set.ncard_singleton (a * b * a)
    omega
  have h2dvd : 2 ∣ Nat.card Q := by
    have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
    rw [← hord]
    exact orderOf_dvd_natCard a
  have hne : ∀ n : ℕ, Nat.card Q ≠ 2 ^ n := by
    intro n hn
    exact hnot fun q => ⟨n, by rw [← hn]; exact pow_card_eq_one'⟩
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hc6 : Nat.card Q = 6 := by
    have h2 : Nat.card Q ≠ 2 := by simpa using hne 1
    have h4 : Nat.card Q ≠ 4 := by simpa using hne 2
    obtain ⟨m, hm⟩ := h2dvd
    omega
  have hc1 : a * b ≠ 1 := by
    intro h1
    have hba : b = a := by rw [eq_inv_of_mul_eq_one_right h1, ha']
    have hall2 : ∀ q : Q, q ∈ ({1, a} : Set Q) := by
      intro q
      rcases hall q with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr (h.trans hba)
      · exact Or.inl (h.trans h1)
      · exact Or.inl (h.trans (by rw [hba, ha]))
      · exact Or.inr (h.trans (by rw [h1, one_mul]))
    have h2 := card_le_ncard_of_forall_mem hall2
    have h3 := Set.ncard_insert_le (1 : Q) ({a} : Set Q)
    have h4 := Set.ncard_singleton a
    omega
  exact G11.G118.g118_mulEquiv_perm_three hc6 ha ha1 hab hc1
    (by rw [mul_inv_rev, ha', hb', ← mul_assoc, ha, one_mul])

variable {G : Type*} [Group G]

theorem nonempty_sup_quotient_perm_three [Finite G] {A B P : Subgroup G}
    [(P.subgroupOf (A ⊔ B)).Normal] {a b : G} (haA : a ∈ A) (hbB : b ∈ B) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (haP : a ∉ P) (hab3 : (a * b) ^ 3 ∈ P)
    (hAcos : ∀ w ∈ A, w ∈ P ∨ w * a ∈ P) (hBcos : ∀ y ∈ B, y ∈ P ∨ y * b ∈ P)
    (hnot : ¬ ∀ x ∈ A ⊔ B, ∃ n : ℕ, x ^ 2 ^ n ∈ P) :
    Nonempty (↥(A ⊔ B) ⧸ P.subgroupOf (A ⊔ B) ≃* Equiv.Perm (Fin 3)) := by
  let N := P.subgroupOf (A ⊔ B)
  let π : ↥(A ⊔ B) →* ↥(A ⊔ B) ⧸ N := QuotientGroup.mk' N
  have hπ1 : ∀ x : ↥(A ⊔ B), π x = 1 ↔ (x : G) ∈ P := fun x => QuotientGroup.eq_one_iff x
  let a' : ↥(A ⊔ B) := ⟨a, mem_sup_left haA⟩
  let b' : ↥(A ⊔ B) := ⟨b, mem_sup_right hbB⟩
  refine nonempty_mulEquiv_perm_three_of_involutions (a := π a') (b := π b') ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul]
    refine (hπ1 _).2 ?_
    show a * a ∈ P
    rw [ha2]
    exact P.one_mem
  · rw [← map_mul]
    refine (hπ1 _).2 ?_
    show b * b ∈ P
    rw [hb2]
    exact P.one_mem
  · rw [← map_mul, ← map_pow]
    exact (hπ1 _).2 hab3
  · exact fun e => haP ((hπ1 a').1 e)
  · rw [eq_top_iff]
    rintro q -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    let C := closure ({π a', π b'} : Set (↥(A ⊔ B) ⧸ N))
    have hK : A ⊔ B ≤ (C.comap π).map (A ⊔ B).subtype := by
      refine sup_le (fun w hw => ⟨⟨w, mem_sup_left hw⟩, ?_, rfl⟩)
        (fun y hy => ⟨⟨y, mem_sup_right hy⟩, ?_, rfl⟩)
      · change π ⟨w, mem_sup_left hw⟩ ∈ C
        rcases hAcos w hw with hwP | hwP
        · rw [(hπ1 ⟨w, mem_sup_left hw⟩).2 hwP]
          exact C.one_mem
        · have h1 : π (⟨w, mem_sup_left hw⟩ * a') = 1 := (hπ1 _).2 hwP
          rw [map_mul] at h1
          rw [eq_inv_of_mul_eq_one_left h1]
          exact C.inv_mem (subset_closure (Set.mem_insert _ _))
      · change π ⟨y, mem_sup_right hy⟩ ∈ C
        rcases hBcos y hy with hyP | hyP
        · rw [(hπ1 ⟨y, mem_sup_right hy⟩).2 hyP]
          exact C.one_mem
        · have h1 : π (⟨y, mem_sup_right hy⟩ * b') = 1 := (hπ1 _).2 hyP
          rw [map_mul] at h1
          rw [eq_inv_of_mul_eq_one_left h1]
          exact C.inv_mem (subset_closure (Set.mem_insert_of_mem _ rfl))
    obtain ⟨y, hy, hyx⟩ := hK x.2
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hy
    exact hy
  · intro hall
    apply hnot
    intro x hx
    obtain ⟨n, hn⟩ := hall (π ⟨x, hx⟩)
    refine ⟨n, ?_⟩
    rw [← map_pow] at hn
    exact (hπ1 _).1 hn

section Data

variable {T V L V₁ Vp H : Subgroup G}

omit [Group G] in
theorem mem_conjSub_inv_iff [Group G] {K : Subgroup G} {k x : G} :
    x ∈ conjSub k⁻¹ K ↔ k * x * k⁻¹ ∈ K := by
  rw [mem_conjSub, inv_inv]

variable [Finite G]

theorem f956_comm_mem (h : HypF91 T V L V₁ Vp H) {a c y : G} (ha : a ∈ conjClosure Vp H)
    (hc : c * c = 1) (hca : c * a * c⁻¹ * a⁻¹ ∈ V₁)
    (hy : y ∈ pCoreOf 2 H ∨ y * c ∈ pCoreOf 2 H) : a * y * a⁻¹ * y⁻¹ ∈ V₁ := by
  rcases hy with hy | hy
  · exact h.commutator_conjClosure_le a ha y hy
  · obtain ⟨p, hp⟩ : ∃ p, p = y * c := ⟨_, rfl⟩
    rw [← hp] at hy
    have hyp : y = p * c := by rw [hp, mul_assoc, hc, mul_one]
    have h1 := h.commutator_conjClosure_le a ha p hy
    have h2 : a * c * a⁻¹ * c⁻¹ ∈ V₁ := by
      have := V₁.inv_mem hca
      have e : (c * a * c⁻¹ * a⁻¹)⁻¹ = a * c * a⁻¹ * c⁻¹ := by group
      rwa [e] at this
    have h3 : p * (a * c * a⁻¹ * c⁻¹) * p⁻¹ ∈ V₁ :=
      (mem_normalizer_iff.mp (h.H_normalizes_V₁ (pCoreOf_le 2 H hy)) _).mp h2
    have e : a * y * a⁻¹ * y⁻¹ = (a * p * a⁻¹ * p⁻¹) * (p * (a * c * a⁻¹ * c⁻¹) * p⁻¹) := by
      rw [hyp]
      group
    rw [e]
    exact V₁.mul_mem h1 h3

theorem f956Data (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    (hcomm : ⁅V, H ⊓ centralizer (Vp : Set G)⁆ ≤ V₁) (hcard : Nat.card V = 2 ^ 4)
    {k : G} (hk : k ∈ H) (hI : ¬ ∀ x ∈ V ⊔ conjSub k⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H)
    {a₀ : G} (ha₀V : a₀ ∈ V) (ha₀2 : a₀ * a₀ = 1)
    (ha₀cos : ∀ w ∈ V, w ∈ pCoreOf 2 H ∨ w * a₀ ∈ pCoreOf 2 H)
    {i : G} (hiV : i ∈ conjSub k⁻¹ V) (hi2 : i * i = 1)
    (hicos : ∀ y ∈ conjSub k⁻¹ V, y ∈ pCoreOf 2 H ∨ y * i ∈ pCoreOf 2 H)
    {z : G} (hzV₁ : ∀ t, t ∈ V₁ ↔ t = 1 ∨ t = z) (hz1 : z ≠ 1) :
    F956Data H V₁ Vp (conjSub k⁻¹ Vp) z a₀ i := by
  have hHN := h.H_normalizes_V₁
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hVpU : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
  have hYU : conjSub k⁻¹ Vp ≤ conjClosure Vp H := HypF91.conjSub_inv_le_U hk hVpU
  have hVkH : conjSub k⁻¹ V ≤ H := h.conjSub_inv_le_H hk
  have hYV : conjSub k⁻¹ Vp ≤ conjSub k⁻¹ V := conjSub_mono _ h.Vp_le_V
  have hYH : conjSub k⁻¹ Vp ≤ H := hYV.trans hVkH
  have hcentral : ∀ {g t : G}, g ∈ H → t ∈ V₁ → g * t * g⁻¹ = t := by
    intro g t hg ht
    have := mem_centralizer_iff.mp (h.H_le_centralizer hg) t ht
    rw [← this]
    group
  have hVkcomm : ∀ x ∈ conjSub k⁻¹ V, ∀ u ∈ conjSub k⁻¹ V, x * u = u * x := by
    intro x hx u hu
    have hc := isElemAbelian_comm h.elemAbelian (mem_conjSub_inv_iff.1 hx)
      (mem_conjSub_inv_iff.1 hu)
    calc x * u = k⁻¹ * ((k * x * k⁻¹) * (k * u * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * u * k⁻¹) * (k * x * k⁻¹)) * k := by rw [hc]
      _ = u * x := by group
  have hVp8 : Nat.card Vp = 8 := by
    have h1 := (Vp.subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe h.Vp_le_V).toEquiv] at h1
    have h2 : (Vp.subgroupOf V).index = 2 := hidx
    rw [h2, hcard] at h1
    omega
  have hY8 : Nat.card (conjSub k⁻¹ Vp) = 8 := by rw [CosetGeom.card_conjSub]; exact hVp8
  have hI' : ¬ ∀ x ∈ V ⊔ conjSub k⁻¹⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H := by
    intro hall
    apply hI
    intro x hx
    have hx' : k * x * k⁻¹ ∈ V ⊔ conjSub k⁻¹⁻¹ V := by
      have := mul_mem_conjSub (g := k) hx
      rw [conjSub_sup, conjSub_inv_conjSub, sup_comm] at this
      rw [inv_inv]
      exact this
    obtain ⟨n, hn⟩ := hall _ hx'
    refine ⟨n, ?_⟩
    rw [conj_pow] at hn
    have := (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hk)) _).mp hn
    have e : k⁻¹ * (k * x ^ 2 ^ n * k⁻¹) * k⁻¹⁻¹ = x ^ 2 ^ n := by group
    rwa [e] at this
  have hvfix : ∀ b ∈ conjSub k⁻¹ Vp, a₀ * b * a₀⁻¹ * b⁻¹ ∈ V₁ → b ∈ V₁ := by
    intro b hb hab
    have hb' : k * b * k⁻¹ ∈ Vp := mem_conjSub_inv_iff.1 hb
    have hmem : k * b * k⁻¹ ∈ centralizerMod V₁ Vp (conjSub k⁻¹⁻¹ V) := by
      refine ⟨hb', hHN (h.Vp_le_H hb'), fun y hy => ?_⟩
      simp only [mem_conjSub, inv_inv] at hy
      have h1 := f956_comm_mem h (hYU hb) ha₀2 hab (ha₀cos _ hy)
      have h2 := hcentral hk h1
      have e : k * b * k⁻¹ * y * (k * b * k⁻¹)⁻¹ * y⁻¹ =
          k * (b * (k⁻¹ * y * k) * b⁻¹ * (k⁻¹ * y * k)⁻¹) * k⁻¹ := by group
      rw [e, h2]
      exact h1
    rw [h.F95_D_eq hyp5 (H.inv_mem hk) hI'] at hmem
    have h3 := hcentral (H.inv_mem hk) hmem
    have e : k⁻¹ * (k * b * k⁻¹) * k⁻¹⁻¹ = b := by group
    rw [e] at h3
    rw [h3]
    exact hmem
  exact
    { mem_V₁ := hzV₁
      z_ne := hz1
      z_comm := fun g hg => mem_centralizer_iff.mp (h.H_le_centralizer hg) z
        ((hzV₁ z).2 (Or.inr rfl))
      X_le := h.Vp_le_H
      Y_le := hYH
      v_mem := h.V_le_H ha₀V
      i_mem := hVkH hiV
      V₁_le_X := h.V₁_le_Vp
      V₁_le_Y := fun t ht => mem_conjSub_inv_iff.2 (by rw [hcentral hk ht]; exact h.V₁_le_Vp ht)
      inf_le := by
        rintro x ⟨hx, hxY⟩
        have hmem : x ∈ centralizerMod V₁ Vp (conjSub k⁻¹ V) := by
          refine ⟨hx, hHN (h.Vp_le_H hx), fun u hu => ?_⟩
          rw [hVkcomm x (hYV hxY) u hu, mul_inv_cancel_right, mul_inv_cancel]
          exact V₁.one_mem
        rwa [h.F95_D_eq hyp5 hk hI] at hmem
      card_X := hVp8
      card_Y := hY8
      card_V₁ := h.card_V₁
      sq_X := fun a ha => by
        have := isElemAbelian_pow_eq_one h.elemAbelian_Vp ha
        rwa [pow_two] at this
      sq_Y := fun b hb => by
        have h1 := isElemAbelian_pow_eq_one h.elemAbelian_Vp (mem_conjSub_inv_iff.1 hb)
        rw [pow_two] at h1
        calc b * b = k⁻¹ * ((k * b * k⁻¹) * (k * b * k⁻¹)) * k := by group
          _ = 1 := by rw [h1]; group
      comm_X := fun a ha a' ha' => isElemAbelian_comm h.elemAbelian_Vp ha ha'
      comm_Y := fun b hb b' hb' => hVkcomm b (hYV hb) b' (hYV hb')
      comm_XY := fun a ha b hb => h.commutator_conjClosure_le a (hVpU ha) b (hUQ (hYU hb))
      v_X := fun a ha => isElemAbelian_comm h.elemAbelian ha₀V (h.Vp_le_V ha)
      i_Y := fun b hb => hVkcomm i hiV b (hYV hb)
      v_Y := fun b hb => by
        have hc : b * a₀ * b⁻¹ * a₀⁻¹ ∈ Vp :=
          (h.F95_2_aux hidx hV).2.1 (commutator_mem_commutator (hYU hb) ha₀V)
        have := Vp.inv_mem hc
        have e : (b * a₀ * b⁻¹ * a₀⁻¹)⁻¹ = a₀ * b * a₀⁻¹ * b⁻¹ := by group
        rwa [e] at this
      i_X := fun a ha => by
        have hc : a * i * a⁻¹ * i⁻¹ ∈ conjSub k⁻¹ Vp :=
          (h.F95_conj_aux hidx hV hk).2 (commutator_mem_commutator (hVpU ha) hiV)
        have := (conjSub k⁻¹ Vp).inv_mem hc
        have e : (a * i * a⁻¹ * i⁻¹)⁻¹ = i * a * i⁻¹ * a⁻¹ := by group
        rwa [e] at this
      v_fix := hvfix
      i_fix := fun a ha hia => by
        have hmem : a ∈ centralizerMod V₁ Vp (conjSub k⁻¹ V) :=
          ⟨ha, hHN (h.Vp_le_H ha), fun y hy => f956_comm_mem h (hVpU ha) hi2 hia (hicos y hy)⟩
        rwa [h.F95_D_eq hyp5 hk hI] at hmem
      nonab := by
        by_contra hne
        push Not at hne
        have hle : conjSub k⁻¹ Vp ≤ V₁ := by
          intro b hb
          refine hvfix b hb (hcomm (commutator_mem_commutator ha₀V ?_))
          exact ⟨hYH hb, mem_centralizer_iff.2 fun a ha => hne a ha b hb⟩
        have := card_le_of_le hle
        rw [hY8, h.card_V₁] at this
        omega }

end Data

theorem stmtF956i : A5.StmtF956i := by
  intro G _ _ T V L V₁ Vp H h hidx hV hyp5 hcomm hcard k hk hI
  obtain ⟨a₀, ha₀V, ha₀2, ha₀cos, ha₀Q⟩ := h.exists_a₀ hidx hV
  obtain ⟨z', hz'1, hz'u⟩ := (Nat.card_eq_two_iff' (1 : ↥V₁)).1 h.card_V₁
  have hz1 : (z' : G) ≠ 1 := fun e => hz'1 (Subtype.ext e)
  have hzV₁ : ∀ t, t ∈ V₁ ↔ t = 1 ∨ t = (z' : G) := by
    intro t
    constructor
    · intro ht
      by_cases ht1 : t = 1
      · exact Or.inl ht1
      · exact Or.inr (congrArg Subtype.val
          (hz'u ⟨t, ht⟩ fun e => ht1 (congrArg Subtype.val e)))
    · rintro (rfl | rfl)
      · exact V₁.one_mem
      · exact z'.2
  have hQconj : ∀ {q : G}, q ∈ pCoreOf 2 H → k⁻¹ * q * k ∈ pCoreOf 2 H := by
    intro q hq
    have := (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hk)) q).mp hq
    rwa [inv_inv] at this
  have hiV : k⁻¹ * a₀ * k ∈ conjSub k⁻¹ V := by
    rw [mem_conjSub_inv_iff]
    have e : k * (k⁻¹ * a₀ * k) * k⁻¹ = a₀ := by group
    rw [e]
    exact ha₀V
  have hi2 : k⁻¹ * a₀ * k * (k⁻¹ * a₀ * k) = 1 := by
    calc k⁻¹ * a₀ * k * (k⁻¹ * a₀ * k) = k⁻¹ * (a₀ * a₀) * k := by group
      _ = 1 := by rw [ha₀2]; group
  have hicos : ∀ y ∈ conjSub k⁻¹ V,
      y ∈ pCoreOf 2 H ∨ y * (k⁻¹ * a₀ * k) ∈ pCoreOf 2 H := by
    intro y hy
    rcases ha₀cos _ (mem_conjSub_inv_iff.1 hy) with hw | hw
    · left
      have := hQconj hw
      have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      rwa [e] at this
    · right
      have := hQconj hw
      have e : k⁻¹ * (k * y * k⁻¹ * a₀) * k = y * (k⁻¹ * a₀ * k) := by group
      rwa [e] at this
  have D := f956Data h hidx hV hyp5 hcomm hcard hk hI ha₀V ha₀2 ha₀cos hiV hi2 hicos hzV₁ hz1
  have hIH : V ⊔ conjSub k⁻¹ V ≤ H := sup_le h.V_le_H (h.conjSub_inv_le_H hk)
  have hN : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub k⁻¹ V)).Normal :=
    normal_subgroupOf_of_le_normalizer (hIH.trans (le_normalizer_pCoreOf 2 H))
  have hcube : (a₀ * (k⁻¹ * a₀ * k)) ^ 3 ∈ pCoreOf 2 H := by
    have hmem : (a₀ * (k⁻¹ * a₀ * k)) ^ 3 ∈
        centralizerMod V₁ (V ⊔ conjSub k⁻¹ V) (Vp ⊔ conjSub k⁻¹ Vp) := by
      refine ⟨pow_mem (mul_mem (mem_sup_left ha₀V) (mem_sup_right hiV)) 3,
        h.H_normalizes_V₁ (hIH (pow_mem (mul_mem (mem_sup_left ha₀V) (mem_sup_right hiV)) 3)),
        fun u hu => ?_⟩
      rw [D.cube_comm hu, mul_inv_cancel_right, mul_inv_cancel]
      exact V₁.one_mem
    rw [(h.F95_5 hidx hV hyp5 hk hI).faithful] at hmem
    exact hmem.2
  exact ⟨D.isQ8Sq, hN, nonempty_sup_quotient_perm_three ha₀V hiV ha₀2 hi2 ha₀Q hcube ha₀cos
    hicos hI⟩

end CFSG.Quasithin.H13.VolI
