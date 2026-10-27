module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.Lem1227Lt

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.Seven

namespace A7

structure V7 where
  a : Fin 7
  b : Fin 7
  c : Fin 7
  d : Fin 7
  e : Fin 7
  f : Fin 7
  g : Fin 7
  deriving DecidableEq

namespace V7

@[expose] def get (x : V7) : Fin 7 → Fin 7
  | 0 => x.a
  | 1 => x.b
  | 2 => x.c
  | 3 => x.d
  | 4 => x.e
  | 5 => x.f
  | 6 => x.g

@[expose] def mul (x y : V7) : V7 :=
  ⟨x.get y.a, x.get y.b, x.get y.c, x.get y.d, x.get y.e, x.get y.f, x.get y.g⟩

@[expose] def one : V7 := ⟨0, 1, 2, 3, 4, 5, 6⟩

instance : Mul V7 := ⟨mul⟩

instance : One V7 := ⟨one⟩

@[expose] def enc (σ : P7) : V7 := ⟨σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6⟩

theorem get_enc (σ : P7) (i : Fin 7) : (enc σ).get i = σ i := by
  fin_cases i <;> rfl

theorem enc_mul (σ τ : P7) : enc (σ * τ) = enc σ * enc τ := by
  show enc (σ * τ) = ⟨(enc σ).get (τ 0), (enc σ).get (τ 1), (enc σ).get (τ 2),
    (enc σ).get (τ 3), (enc σ).get (τ 4), (enc σ).get (τ 5), (enc σ).get (τ 6)⟩
  simp only [get_enc]
  rfl

theorem enc_inj : Function.Injective enc := by
  intro σ τ h
  refine Equiv.ext fun i => ?_
  have := congrArg (fun r => r.get i) h
  simpa only [get_enc] using this

theorem enc_one : enc 1 = 1 := by decide +kernel

end V7

theorem mem_of_closure {G : Type*} [Group G] [Finite G] {S : Set G} {p : G → Prop} (h1 : p 1)
    (hS : ∀ s ∈ S, p s) (hmul : ∀ x y, p x → p y → p (x * y)) {x : G}
    (hx : x ∈ Subgroup.closure S) : p x := by
  refine Subgroup.closure_induction (p := fun x _ => p x) (fun s hs => hS s hs) h1
    (fun x y _ _ hx hy => hmul x y hx hy) (fun x _ hx => ?_) hx
  have hpow : ∀ k : ℕ, p (x ^ k) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hx
  have hn : 0 < orderOf x := orderOf_pos x
  have : x⁻¹ = x ^ (orderOf x - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [this]
  exact hpow _

@[expose] def aR : V7 := ⟨1, 2, 3, 0, 5, 4, 6⟩

@[expose] def bR : V7 := ⟨2, 1, 0, 3, 5, 4, 6⟩

@[expose] def tR : V7 := ⟨0, 1, 2, 3, 5, 4, 6⟩

@[expose] def D7R : List V7 :=
  [1, aR, aR * aR, aR * aR * aR, bR, aR * bR, aR * aR * bR, aR * aR * aR * bR]

theorem enc_aD : V7.enc (perm7 [[0, 1, 2, 3], [4, 5]]) = aR := by decide +kernel

theorem enc_bD : V7.enc (perm7 [[0, 2], [4, 5]]) = bR := by decide +kernel

theorem enc_tD : V7.enc (perm7 [[4, 5]]) = tR := by decide +kernel

theorem dGens_eq : dGens = [perm7 [[0, 1, 2, 3], [4, 5]], perm7 [[0, 2], [4, 5]]] := rfl

theorem D7R_mul : ∀ u ∈ D7R, ∀ v ∈ D7R, u * v ∈ D7R := by decide +kernel

theorem exists_of_mem_D7R {u : V7} (hu : u ∈ D7R) : ∃ x ∈ D7, V7.enc x = u := by
  have ha : perm7 [[0, 1, 2, 3], [4, 5]] ∈ D7 := Subgroup.subset_closure (by simp [dGens])
  have hb : perm7 [[0, 2], [4, 5]] ∈ D7 := Subgroup.subset_closure (by simp [dGens])
  simp only [D7R, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, V7.enc_one⟩
  · exact ⟨_, ha, enc_aD⟩
  · exact ⟨_, mul_mem ha ha, by rw [V7.enc_mul, enc_aD]⟩
  · exact ⟨_, mul_mem (mul_mem ha ha) ha, by rw [V7.enc_mul, V7.enc_mul, enc_aD]⟩
  · exact ⟨_, hb, enc_bD⟩
  · exact ⟨_, mul_mem ha hb, by rw [V7.enc_mul, enc_aD, enc_bD]⟩
  · exact ⟨_, mul_mem (mul_mem ha ha) hb, by rw [V7.enc_mul, V7.enc_mul, enc_aD, enc_bD]⟩
  · exact ⟨_, mul_mem (mul_mem (mul_mem ha ha) ha) hb,
      by rw [V7.enc_mul, V7.enc_mul, V7.enc_mul, enc_aD, enc_bD]⟩

theorem mem_D7_iff {x : P7} : x ∈ D7 ↔ V7.enc x ∈ D7R := by
  constructor
  · intro hx
    refine mem_of_closure (p := fun x => V7.enc x ∈ D7R) ?_ ?_ ?_ hx
    · rw [V7.enc_one]; decide +kernel
    · intro s hs
      simp only [dGens, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · rw [enc_aD]; decide +kernel
      · rw [enc_bD]; decide +kernel
    · intro x y hx hy
      rw [V7.enc_mul]
      exact D7R_mul _ hx _ hy
  · intro h
    obtain ⟨y, hy, hyx⟩ := exists_of_mem_D7R h
    rwa [← V7.enc_inj hyx]

set_option maxRecDepth 100000 in
theorem norm7R : ∀ σ : P7, (∃ d ∈ D7R, V7.enc σ * aR = d * V7.enc σ) →
    (∃ d ∈ D7R, V7.enc σ * bR = d * V7.enc σ) →
    V7.enc σ ∈ D7R ∨ ∃ d ∈ D7R, V7.enc σ = tR * d := by decide +kernel

theorem D7R_fix : ∀ u ∈ D7R, u.g = 6 ∧ (u.e = 4 ∨ u.e = 5) ∧ (u.f = 4 ∨ u.f = 5) := by
  decide +kernel

@[expose] def Qfix (σ : P7) : Prop := σ 6 = 6 ∧ (σ 4 = 4 ∨ σ 4 = 5) ∧ (σ 5 = 4 ∨ σ 5 = 5)

theorem Qfix_of_mem_D7 {σ : P7} (h : σ ∈ D7) : Qfix σ := by
  have := D7R_fix _ (mem_D7_iff.1 h)
  simpa [Qfix, V7.enc] using this

theorem Qfix_mul {σ τ : P7} (hσ : Qfix σ) (hτ : Qfix τ) : Qfix (σ * τ) := by
  obtain ⟨a6, a4, a5⟩ := hσ
  obtain ⟨b6, b4, b5⟩ := hτ
  refine ⟨by simp [Perm.mul_apply, b6, a6], ?_, ?_⟩
  · rcases b4 with h | h <;> simp [Perm.mul_apply, h] <;> tauto
  · rcases b5 with h | h <;> simp [Perm.mul_apply, h] <;> tauto

theorem Qfix_tD : Qfix (perm7 [[4, 5]]) := by
  unfold Qfix
  decide +kernel

theorem norm_D7_aux {σ : P7} (h : ∀ x, x ∈ D7 → σ * x * σ⁻¹ ∈ D7) :
    (σ ∈ D7 ∨ ∃ d ∈ D7, σ = perm7 [[4, 5]] * d) := by
  have ha : perm7 [[0, 1, 2, 3], [4, 5]] ∈ D7 := Subgroup.subset_closure (by simp [dGens])
  have hb : perm7 [[0, 2], [4, 5]] ∈ D7 := Subgroup.subset_closure (by simp [dGens])
  have key : ∀ x ∈ D7, ∃ d ∈ D7R, V7.enc σ * V7.enc x = d * V7.enc σ := by
    intro x hx
    refine ⟨V7.enc (σ * x * σ⁻¹), mem_D7_iff.1 (h x hx), ?_⟩
    rw [← V7.enc_mul, ← V7.enc_mul]
    congr 1
    group
  have hk1 := key _ ha
  have hk2 := key _ hb
  rw [enc_aD] at hk1
  rw [enc_bD] at hk2
  rcases norm7R σ hk1 hk2 with h1 | ⟨d, hd, h2⟩
  · exact Or.inl (mem_D7_iff.2 h1)
  · obtain ⟨y, hy, rfl⟩ := exists_of_mem_D7R hd
    refine Or.inr ⟨y, hy, V7.enc_inj ?_⟩
    rw [V7.enc_mul, enc_tD, h2]

theorem Qfix_of_norm {σ : P7} (h : ∀ x, x ∈ D7 → σ * x * σ⁻¹ ∈ D7) : Qfix σ := by
  rcases norm_D7_aux h with h1 | ⟨d, hd, rfl⟩
  · exact Qfix_of_mem_D7 h1
  · exact Qfix_mul Qfix_tD (Qfix_of_mem_D7 hd)

theorem norm_inv {σ : P7} (h : ∀ x, x ∈ D7 ↔ σ * x * σ⁻¹ ∈ D7) :
    ∀ x, x ∈ D7 → σ⁻¹ * x * σ⁻¹⁻¹ ∈ D7 := by
  intro x hx
  rw [inv_inv]
  refine (h _).2 ?_
  have : σ * (σ⁻¹ * x * σ) * σ⁻¹ = x := by group
  rw [this]
  exact hx

theorem norm_D7 {σ : P7} (h : ∀ x, x ∈ D7 ↔ σ * x * σ⁻¹ ∈ D7) :
    (σ ∈ D7 ∨ ∃ d ∈ D7, σ = perm7 [[4, 5]] * d) ∧ Qfix σ ∧ Qfix σ⁻¹ :=
  ⟨norm_D7_aux fun x hx => (h x).1 hx, Qfix_of_norm fun x hx => (h x).1 hx,
    Qfix_of_norm (norm_inv h)⟩

@[expose] def PresF (vec : Fin 7 → V3) (x : P7) : Prop :=
  ∀ a b c : Fin 7, vec a + vec b + vec c = 0 → vec (x a) + vec (x b) + vec (x c) = 0

theorem PresF_mul (vec : Fin 7 → V3) {x y : P7} (hx : PresF vec x) (hy : PresF vec y) :
    PresF vec (x * y) := fun a b c h => hx _ _ _ (hy a b c h)

theorem PresF_one (vec : Fin 7 → V3) : PresF vec 1 := fun _ _ _ h => h

theorem PresF_of_gens (vec : Fin 7 → V3) {G : List P7} (hG : ∀ g ∈ G, PresF vec g) {x : P7}
    (hx : x ∈ Subgroup.closure {g | g ∈ G}) : PresF vec x :=
  mem_of_closure (p := PresF vec) (PresF_one vec) (fun s hs => hG s hs)
    (fun _ _ hx hy => PresF_mul vec hx hy) hx

theorem Z8_pres {x : P7} (hx : x ∈ Z 8) : PresF vec8 x := by
  refine PresF_of_gens vec8 (G := dGens ++ [perm7 [[2, 5], [3, 6]]]) ?_ hx
  intro g hg
  simp only [dGens, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  unfold PresF
  rcases hg with (rfl | rfl) | rfl <;> decide +kernel

theorem Z9_pres {x : P7} (hx : x ∈ Z 9) : PresF vec9 x := by
  refine PresF_of_gens vec9 (G := dGens ++ [perm7 [[2, 4], [3, 6]]]) ?_ hx
  intro g hg
  simp only [dGens, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  unfold PresF
  rcases hg with (rfl | rfl) | rfl <;> decide +kernel

theorem not_pres8 :
    ¬ PresF vec8 (perm7 [[4, 5]] * perm7 [[2, 5], [3, 6]] * (perm7 [[4, 5]])⁻¹) := by
  unfold PresF
  decide +kernel

theorem not_pres9 :
    ¬ PresF vec9 (perm7 [[4, 5]] * perm7 [[2, 4], [3, 6]] * (perm7 [[4, 5]])⁻¹) := by
  unfold PresF
  decide +kernel

theorem D7_le_Z8 : D7 ≤ Z 8 := by
  refine Subgroup.closure_mono ?_
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg ⊢
  change g ∈ dGens ++ [perm7 [[2, 5], [3, 6]]]
  exact List.mem_append_left _ hg

theorem D7_le_Z9 : D7 ≤ Z 9 := by
  refine Subgroup.closure_mono ?_
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg ⊢
  change g ∈ dGens ++ [perm7 [[2, 4], [3, 6]]]
  exact List.mem_append_left _ hg

theorem gen8_mem : perm7 [[2, 5], [3, 6]] ∈ Z 8 :=
  Subgroup.subset_closure (by
    simp only [Set.mem_ofPred_eq]
    change _ ∈ dGens ++ [perm7 [[2, 5], [3, 6]]]
    exact List.mem_append_right _ (List.mem_singleton_self _))

theorem gen9_mem : perm7 [[2, 4], [3, 6]] ∈ Z 9 :=
  Subgroup.subset_closure (by
    simp only [Set.mem_ofPred_eq]
    change _ ∈ dGens ++ [perm7 [[2, 4], [3, 6]]]
    exact List.mem_append_right _ (List.mem_singleton_self _))

theorem not_normalizes_Z8 {d : P7} (hd : d ∈ D7)
    (h : ∀ z, z ∈ Z 8 → perm7 [[4, 5]] * d * z * (perm7 [[4, 5]] * d)⁻¹ ∈ Z 8) : False := by
  have hdZ : d ∈ Z 8 := D7_le_Z8 hd
  have hz : d⁻¹ * perm7 [[2, 5], [3, 6]] * d ∈ Z 8 :=
    mul_mem (mul_mem (inv_mem hdZ) gen8_mem) hdZ
  have h1 := Z8_pres (h _ hz)
  apply not_pres8
  have : perm7 [[4, 5]] * d * (d⁻¹ * perm7 [[2, 5], [3, 6]] * d) * (perm7 [[4, 5]] * d)⁻¹ =
      perm7 [[4, 5]] * perm7 [[2, 5], [3, 6]] * (perm7 [[4, 5]])⁻¹ := by group
  rwa [this] at h1

theorem not_normalizes_Z9 {d : P7} (hd : d ∈ D7)
    (h : ∀ z, z ∈ Z 9 → perm7 [[4, 5]] * d * z * (perm7 [[4, 5]] * d)⁻¹ ∈ Z 9) : False := by
  have hdZ : d ∈ Z 9 := D7_le_Z9 hd
  have hz : d⁻¹ * perm7 [[2, 4], [3, 6]] * d ∈ Z 9 :=
    mul_mem (mul_mem (inv_mem hdZ) gen9_mem) hdZ
  have h1 := Z9_pres (h _ hz)
  apply not_pres9
  have : perm7 [[4, 5]] * d * (d⁻¹ * perm7 [[2, 4], [3, 6]] * d) * (perm7 [[4, 5]] * d)⁻¹ =
      perm7 [[4, 5]] * perm7 [[2, 4], [3, 6]] * (perm7 [[4, 5]])⁻¹ := by group
  rwa [this] at h1

end A7

end CFSG.Quasithin.H13.Lem1227Lt
