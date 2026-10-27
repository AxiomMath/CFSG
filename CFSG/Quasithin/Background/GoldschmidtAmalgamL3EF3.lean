module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EWord
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Ord

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

abbrev Ksub (A B : Subgroup D) : Subgroup D := coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B

@[expose] def Nsub (A B : Subgroup D) (V : Subgroup D) : Subgroup D :=
  conjClosure V B ⊔ ⁅Ksub A B, Ksub A B⁆

namespace Ctx

omit [Finite D] in
theorem K_le_B (_c : Ctx A B z V) : Ksub A B ≤ B := coreIn_le_left _ _

omit [Finite D] in
theorem K_le_Q (_c : Ctx A B z V) : Ksub A B ≤ pCoreOf 2 A := coreIn_right_le_pCoreOf_left

omit [Finite D] in
theorem K_normal (_c : Ctx A B z V) {x k : D} (hx : x ∈ B) (hk : k ∈ Ksub A B) :
    x * k * x⁻¹ ∈ Ksub A B :=
  coreIn_conj_mem hx hk

omit [Finite D] in
theorem N_normal (_c : Ctx A B z V) {x n : D} (hx : x ∈ B) (hn : n ∈ Nsub A B V) :
    x * n * x⁻¹ ∈ Nsub A B V := by
  have hK : conjSub x (Ksub A B) = Ksub A B :=
    conjSub_eq_of_mem_normalizer (le_normalizer_coreIn _ _ hx)
  have hU : conjSub x (conjClosure V B) = conjClosure V B :=
    conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V B hx)
  have hN : conjSub x (Nsub A B V) = Nsub A B V := by
    unfold Nsub conjSub
    rw [Subgroup.map_sup, Subgroup.map_commutator]
    unfold conjSub at hK hU
    rw [hK, hU]
  have hmem : x ∈ Subgroup.normalizer (Nsub A B V : Set D) := mem_normalizer_of_conjSub_eq hN
  exact (Subgroup.mem_normalizer_iff.mp hmem n).mp hn

omit [Finite D] in
theorem V_le_N (_c : Ctx A B z V) : V ≤ Nsub A B V :=
  (le_conjClosure V B).trans le_sup_left

omit [Finite D] in
theorem comm_K_K_N (_c : Ctx A B z V) {k k' : D} (hk : k ∈ Ksub A B) (hk' : k' ∈ Ksub A B) :
    ⁅k, k'⁆ ∈ Nsub A B V :=
  Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hk hk')

theorem comm_K_K_M (c : Ctx A B z V) {k k' : D} (hk : k ∈ Ksub A B) (hk' : k' ∈ Ksub A B) :
    ⁅k, k'⁆ ∈ Msub A B V :=
  c.comm_Q_Q_M (c.K_le_Q hk) (c.K_le_Q hk')

theorem N_le_WM (c : Ctx A B z V) : Nsub A B V ≤ Wsub A B V ⊔ Msub A B V := by
  refine sup_le (c.U_le_W.trans le_sup_left) ?_
  rw [Subgroup.commutator_le]
  exact fun k hk k' hk' => Subgroup.mem_sup_right (c.comm_K_K_M hk hk')

end Ctx

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

include g in
theorem Q_step {q k : D} (hq : q ∈ pCoreOf 2 A) (hk : k ∈ Ksub A B) :
    q * k * q⁻¹ * k⁻¹ ∈ Nsub A B V := by
  obtain ⟨w, hw, k₁, hk₁, rfl⟩ := g.exists_mul_of_mem_Q hq
  have hwQ := c.W_le_Q hw
  have hk₁B : k₁ ∈ B := c.K_le_B hk₁
  have hk' : k₁ * k * k₁⁻¹ ∈ Ksub A B := c.K_normal hk₁B hk
  have e : w * k₁ * k * (w * k₁)⁻¹ * k⁻¹ =
      ⁅w, k₁ * k * k₁⁻¹⁆ * ⁅k₁, k⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  refine (Nsub A B V).mul_mem ?_ (c.comm_K_K_N hk₁ hk)
  exact c.V_le_N (c.comm_W_Q hw (c.K_le_Q hk'))

end Gen

namespace Ctx

@[expose] def Trivk (c : Ctx A B z V) (X : Subgroup D) (hX : X ≤ B) : Subgroup D where
  carrier := {x | x ∈ X ∧ ∀ k ∈ Ksub A B, x * k * x⁻¹ * k⁻¹ ∈ Nsub A B V}
  one_mem' := ⟨X.one_mem, fun k _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
    refine ⟨X.mul_mem haX hbX, fun k hk => ?_⟩
    have e : a * b * k * (a * b)⁻¹ * k⁻¹ =
        (a * (b * k * b⁻¹ * k⁻¹) * a⁻¹) * (a * k * a⁻¹ * k⁻¹) := by group
    rw [e]
    exact (Nsub A B V).mul_mem (c.N_normal (hX haX) (hb k hk)) (ha k hk)
  inv_mem' := by
    rintro a ⟨haX, ha⟩
    refine ⟨X.inv_mem haX, fun k hk => ?_⟩
    have hk' : a⁻¹ * k * a⁻¹⁻¹ ∈ Ksub A B := c.K_normal (B.inv_mem (hX haX)) hk
    have h1 := ha _ hk'
    have e : a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ =
        (a * (a⁻¹ * k * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * k * a⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact (Nsub A B V).inv_mem h1

omit [Finite D] in
theorem Trivk_conj (c : Ctx A B z V) {X : Subgroup D} {hX : X ≤ B}
    (hXn : ∀ x ∈ B, ∀ y ∈ X, x * y * x⁻¹ ∈ X) {x p : D} (hx : x ∈ B) (hp : p ∈ c.Trivk X hX) :
    x * p * x⁻¹ ∈ c.Trivk X hX := by
  obtain ⟨hpX, hp⟩ := hp
  refine ⟨hXn x hx p hpX, fun k hk => ?_⟩
  have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ Ksub A B := c.K_normal (B.inv_mem hx) hk
  have e : x * p * x⁻¹ * k * (x * p * x⁻¹)⁻¹ * k⁻¹ =
      x * (p * (x⁻¹ * k * x⁻¹⁻¹) * p⁻¹ * (x⁻¹ * k * x⁻¹⁻¹)⁻¹) * x⁻¹ := by group
  rw [e]
  exact c.N_normal hx (hp _ hk')

omit [Finite D] in
theorem Trivk_normal (c : Ctx A B z V) {X : Subgroup D} {hX : X ≤ B}
    (hXn : ∀ x ∈ B, ∀ y ∈ X, x * y * x⁻¹ ∈ X) : B ≤ Subgroup.normalizer (c.Trivk X hX : Set D) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => c.Trivk_conj hXn hx hn, fun hn => ?_⟩
  have := c.Trivk_conj hXn (B.inv_mem hx) hn
  simpa [mul_assoc] using this

end Ctx

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

include g in
theorem P_eq_Trivk : c.Trivk (pCoreOf 2 B) (c.P_le_T.trans inf_le_right) = pCoreOf 2 B := by
  set SB := c.Trivk (pCoreOf 2 B) (c.P_le_T.trans inf_le_right) with hSBdef
  have hSBP : SB ≤ pCoreOf 2 B := fun x hx => hx.1
  have hR : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ SB := fun r hr =>
    ⟨hr.2, fun k hk => g.Q_step hr.1 hk⟩
  have hnorm : B ≤ Subgroup.normalizer (SB : Set D) :=
    c.Trivk_normal fun x hx y hy => pCoreOf_conj_mem (A := B) hx hy
  by_contra hne
  have hKpos : 0 < Nat.card ↥(Ksub A B) := Nat.card_pos
  have hcardR : Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) = 2 * Nat.card ↥(Ksub A B) :=
    c.hyp.card_inf_pCoreOf_eq c.card_eq
  have hcardP : Nat.card ↥(pCoreOf 2 B) = 4 * Nat.card ↥(Ksub A B) :=
    c.hyp.card_pCoreOf_right_eq c.card_eq
  have hRP : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ pCoreOf 2 B := inf_le_right
  have hidx : (pCoreOf 2 A ⊓ pCoreOf 2 B).relIndex (pCoreOf 2 B) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 A ⊓ pCoreOf 2 B) (pCoreOf 2 B)
    rw [inf_eq_left.mpr hRP, hcardR, hcardP] at h1
    have : (pCoreOf 2 A ⊓ pCoreOf 2 B).relIndex (pCoreOf 2 B) * (2 * Nat.card ↥(Ksub A B)) =
        2 * (2 * Nat.card ↥(Ksub A B)) := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 A ⊓ pCoreOf 2 B) SB (pCoreOf 2 B) hR hSBP
  rw [hidx] at hmul
  have hdvd : (pCoreOf 2 A ⊓ pCoreOf 2 B).relIndex SB ∣ 2 := Dvd.intro _ hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · have hSBR : SB = pCoreOf 2 A ⊓ pCoreOf 2 B := le_antisymm (Subgroup.relIndex_eq_one.mp h1) hR
    have hBN : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
      rw [← hSBR]; exact hnorm
    have hRK : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ Ksub A B :=
      le_coreIn (inf_le_left.trans (c.Q_le_T.trans inf_le_right)) hBN le_rfl
    have := Subgroup.card_le_of_le hRK
    omega
  · rw [h2] at hmul
    have h3 : SB.relIndex (pCoreOf 2 B) = 1 := by omega
    exact hne (le_antisymm hSBP (Subgroup.relIndex_eq_one.mp h3))

include g in
theorem P_step {p k : D} (hp : p ∈ pCoreOf 2 B) (hk : k ∈ Ksub A B) :
    p * k * p⁻¹ * k⁻¹ ∈ Nsub A B V := by
  have : p ∈ c.Trivk (pCoreOf 2 B) (c.P_le_T.trans inf_le_right) := by
    rw [g.P_eq_Trivk]; exact hp
  exact this.2 k hk

include g in
theorem T_step {t k : D} (ht : t ∈ A ⊓ B) (hk : k ∈ Ksub A B) :
    t * k * t⁻¹ * k⁻¹ ∈ Nsub A B V := by
  have hne : pCoreOf 2 A ≠ pCoreOf 2 B := c.hyp.gold.pCoreOf_ne c.hyp.card_inf_ne_two
  have hsup := c.hyp.gold.pCoreOf_sup_eq hne
  have hle : pCoreOf 2 A ⊔ pCoreOf 2 B ≤ c.Trivk (A ⊓ B) inf_le_right := by
    refine sup_le (fun q hq => ⟨c.Q_le_T hq, fun k hk => g.Q_step hq hk⟩)
      (fun p hp => ⟨c.P_le_T hp, fun k hk => g.P_step hp hk⟩)
  have : t ∈ c.Trivk (A ⊓ B) inf_le_right := hle (by rw [hsup]; exact ht)
  exact this.2 k hk

end Gen

omit [Finite D] in
theorem le_normalizer_of_conj {X H : Subgroup D} (h : ∀ x ∈ X, ∀ n ∈ H, x * n * x⁻¹ ∈ H) :
    X ≤ Subgroup.normalizer (H : Set D) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => h x hx n hn, fun hn => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hn
  simpa [mul_assoc] using this

omit [Finite D] in
theorem conj_mem_sup {X H₁ H₂ : Subgroup D} (h₁ : X ≤ Subgroup.normalizer (H₁ : Set D))
    (h₂ : X ≤ Subgroup.normalizer (H₂ : Set D)) {x n : D} (hx : x ∈ X) (hn : n ∈ H₁ ⊔ H₂) :
    x * n * x⁻¹ ∈ H₁ ⊔ H₂ := by
  have e : conjSub x (H₁ ⊔ H₂) = H₁ ⊔ H₂ := by
    have e1 : conjSub x H₁ = H₁ := conjSub_eq_of_mem_normalizer (h₁ hx)
    have e2 : conjSub x H₂ = H₂ := conjSub_eq_of_mem_normalizer (h₂ hx)
    unfold conjSub at e1 e2 ⊢
    rw [Subgroup.map_sup, e1, e2]
  have hmem : x ∈ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup D) : Set D) :=
    mem_normalizer_of_conjSub_eq e
  exact (Subgroup.mem_normalizer_iff.mp hmem n).mp hn

namespace Ctx

omit [Finite D] in
theorem W_le_normalizer (c : Ctx A B z V) : A ≤ Subgroup.normalizer (Wsub A B V : Set D) :=
  le_normalizer_of_conj fun _ hx _ hn => c.W_normal hx hn

omit [Finite D] in
theorem M_le_normalizer (c : Ctx A B z V) : A ≤ Subgroup.normalizer (Msub A B V : Set D) :=
  le_normalizer_of_conj fun _ hx _ hn => c.M_normal hx hn

omit [Finite D] in
theorem WM_normal (c : Ctx A B z V) {x n : D} (hx : x ∈ A) (hn : n ∈ Wsub A B V ⊔ Msub A B V) :
    x * n * x⁻¹ ∈ Wsub A B V ⊔ Msub A B V :=
  conj_mem_sup c.W_le_normalizer c.M_le_normalizer hx hn

@[expose] def Triva (c : Ctx A B z V) : Subgroup D where
  carrier := {x | x ∈ A ∧ ∀ q ∈ pCoreOf 2 A, x * q * x⁻¹ * q⁻¹ ∈ Wsub A B V ⊔ Msub A B V}
  one_mem' := ⟨A.one_mem, fun q _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
    refine ⟨A.mul_mem haA hbA, fun q hq => ?_⟩
    have e : a * b * q * (a * b)⁻¹ * q⁻¹ =
        (a * (b * q * b⁻¹ * q⁻¹) * a⁻¹) * (a * q * a⁻¹ * q⁻¹) := by group
    rw [e]
    exact (Wsub A B V ⊔ Msub A B V).mul_mem (c.WM_normal haA (hb q hq)) (ha q hq)
  inv_mem' := by
    rintro a ⟨haA, ha⟩
    refine ⟨A.inv_mem haA, fun q hq => ?_⟩
    have hq' : a⁻¹ * q * a⁻¹⁻¹ ∈ pCoreOf 2 A := pCoreOf_conj_mem (A.inv_mem haA) hq
    have h1 := ha _ hq'
    have e : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ =
        (a * (a⁻¹ * q * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * q * a⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact (Wsub A B V ⊔ Msub A B V).inv_mem h1

omit [Finite D] in
theorem Triva_normal (c : Ctx A B z V) : A ≤ Subgroup.normalizer (c.Triva : Set D) := by
  refine le_normalizer_of_conj fun x hx s hs => ?_
  obtain ⟨hsA, hs⟩ := hs
  refine ⟨A.mul_mem (A.mul_mem hx hsA) (A.inv_mem hx), fun q hq => ?_⟩
  have hq' : x⁻¹ * q * x⁻¹⁻¹ ∈ pCoreOf 2 A := pCoreOf_conj_mem (A.inv_mem hx) hq
  have e : x * s * x⁻¹ * q * (x * s * x⁻¹)⁻¹ * q⁻¹ =
      x * (s * (x⁻¹ * q * x⁻¹⁻¹) * s⁻¹ * (x⁻¹ * q * x⁻¹⁻¹)⁻¹) * x⁻¹ := by group
  rw [e]
  exact c.WM_normal hx (hs _ hq')

end Ctx

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

include g in
theorem A_step {x q : D} (hx : x ∈ A) (hq : q ∈ pCoreOf 2 A) :
    x * q * x⁻¹ * q⁻¹ ∈ Wsub A B V ⊔ Msub A B V := by
  have hT : A ⊓ B ≤ c.Triva := by
    intro t ht
    refine ⟨ht.1, fun q hq => ?_⟩
    obtain ⟨w, hw, k, hk, rfl⟩ := g.exists_mul_of_mem_Q hq
    have e : t * (w * k) * t⁻¹ * (w * k)⁻¹ = (t * w * t⁻¹) * (t * k * t⁻¹ * k⁻¹) * w⁻¹ := by
      group
    rw [e]
    have h1 : t * w * t⁻¹ ∈ Wsub A B V ⊔ Msub A B V := Subgroup.mem_sup_left (c.W_normal ht.1 hw)
    have h2 : t * k * t⁻¹ * k⁻¹ ∈ Wsub A B V ⊔ Msub A B V := c.N_le_WM (g.T_step ht hk)
    have h3 : w⁻¹ ∈ Wsub A B V ⊔ Msub A B V := Subgroup.mem_sup_left ((Wsub A B V).inv_mem hw)
    exact (Wsub A B V ⊔ Msub A B V).mul_mem ((Wsub A B V ⊔ Msub A B V).mul_mem h1 h2) h3
  have hA : c.Triva = A := c.eq_left_of_normal hT (fun x hx => hx.1) c.Triva_normal
  have : x ∈ c.Triva := by rw [hA]; exact hx
  exact this.2 q hq

end Gen

omit [Finite D] in
theorem Ctx.exists_mul_of_mem_sup (c : Ctx A B z V) {x : D}
    (hx : x ∈ Wsub A B V ⊔ Msub A B V) :
    ∃ w ∈ Wsub A B V, ∃ m ∈ Msub A B V, x = w * m := by
  let S : Subgroup D :=
    { carrier := {x | ∃ w ∈ Wsub A B V, ∃ m ∈ Msub A B V, x = w * m}
      one_mem' := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨w, hw, m, hm, rfl⟩ ⟨w', hw', m', hm', rfl⟩
        refine ⟨w * w', Subgroup.mul_mem _ hw hw', m * m', Subgroup.mul_mem _ hm hm', ?_⟩
        have h : m * w' = w' * m := ((c.mem_M_iff.mp hm).2 w' hw').symm
        calc w * m * (w' * m') = w * (m * w') * m' := by group
          _ = w * (w' * m) * m' := by rw [h]
          _ = w * w' * (m * m') := by group
      inv_mem' := by
        rintro _ ⟨w, hw, m, hm, rfl⟩
        refine ⟨w⁻¹, Subgroup.inv_mem _ hw, m⁻¹, Subgroup.inv_mem _ hm, ?_⟩
        have h : m * w = w * m := ((c.mem_M_iff.mp hm).2 w hw).symm
        calc (w * m)⁻¹ = (m * w)⁻¹ := by rw [h]
          _ = w⁻¹ * m⁻¹ := mul_inv_rev m w }
  have hle : Wsub A B V ⊔ Msub A B V ≤ S :=
    sup_le (fun w hw => ⟨w, hw, 1, Subgroup.one_mem _, by simp⟩)
      (fun m hm => ⟨1, Subgroup.one_mem _, m, hm, by simp⟩)
  exact hle hx

end GoldAmL3E

end F6

end CFSG.Quasithin
