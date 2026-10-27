module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutLie

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13.F431

universe u

section Lie

variable {Mb : Type u} [Group Mb]

structure F431UnOut (T S : Subgroup Mb) (f : Mb) (N N' : Subgroup Mb) (z t : Mb)
    (V : Subgroup Mb) : Prop where
  sylow : IsSylowTwoOf T ⊤
  T_le : T ≤ N
  T_le' : T ≤ N'
  S_le : S ≤ T
  S_norm : T ≤ Subgroup.normalizer (S : Set Mb)
  cyc : ∃ t₀ : Mb, T = S ⊔ Subgroup.zpowers t₀
  z_mem : z ∈ S
  z_two : orderOf z = 2
  t_mem : t ∈ S
  t_two : orderOf t = 2
  zt_not_conj : ¬ IsConj z t
  z_ZN : z ∈ centerOf (perfectCore N)
  Z_sq : ∀ x ∈ centerOf (perfectCore N), x ^ 2 = 1
  ZN_trans : ∀ x ∈ centerOf (perfectCore N), x ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = x
  center_T : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w
  fusion : ∀ x ∈ S, orderOf x = 2 → ∃ i, (i = z ∨ i = t) ∧
    Relation.ReflTransGen (fun a b : Mb => a ∈ T ∧ b ∈ T ∧
      ((∃ m ∈ N, m * a * m⁻¹ = b) ∨ (∃ m ∈ N', m * a * m⁻¹ = b))) x i
  V_le : V ≤ S
  V_ab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  V_sq : ∀ a ∈ V, a ^ 2 = 1
  V_zt : z ∈ V ∧ t ∈ V
  V_eq : V = centerOf (pCoreOf 2 N')
  V_unique : ∀ E : Subgroup Mb, E ≤ T → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
    Nat.card E = Nat.card V → E = V
  f_mem : f ∈ T
  f_not : f ∉ S
  f_sq : f ^ 2 = 1
  Tf_lt_z : Nat.card (spTf T f) < Nat.card ↥(T ⊓ Subgroup.centralizer ({z} : Set Mb))
  Tf_lt_t : Nat.card (spTf T f) < Nat.card ↥(T ⊓ Subgroup.centralizer ({t} : Set Mb))
  Sylow_Tf : IsSylowTwoOf (spTf T f) (Subgroup.centralizer ({f} : Set Mb) ⊓ N)
  W_le : spWf T f ≤ S
  W_ne : ∃ x ∈ spWf T f, x ∈ centerOf (perfectCore N) ∧ x ≠ 1
  W_cls : ∀ y ∈ spWf T f, IsConj z y → y ∈ centerOf (perfectCore N)

end Lie

@[expose] def F431UnOutLieProp (m f : ℕ) : Prop :=
  ∀ (D : Type) [Group D], LieModel D .PSU m 2 f → ∀ A : LieAmalgamExt D,
    ¬ Odd (Nat.card ↥A.K / Nat.card D) →
    ∃ (T S : Subgroup ↥A.K) (g z t : ↥A.K) (V : Subgroup ↥A.K),
      F431UnOut T S g A.Mb1 A.Mb2 z t V ∨ F431UnOut T S g A.Mb2 A.Mb1 z t V

end CFSG.Quasithin.H13.F431.Un
