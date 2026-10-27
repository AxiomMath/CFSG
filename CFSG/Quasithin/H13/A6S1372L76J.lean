module

public import CFSG.Quasithin.H13.A6S1372L76I

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76J

theorem w3_comm : ∀ y : P6, InW4 y → InW3 y → ∃ y' : P6, InW4 y' ∧ InW3 y' ∧
    A6L76G.InV1 (y * (act4f (swap 0 1 * swap 1 2) y' * y'⁻¹)⁻¹) := by
  decide +kernel

theorem w2_cosets : ∀ x : P6, InW2 x → A6L76G.InV1 x ∨ A6L76G.InV1 (x * dv 0 1) := by
  decide +kernel

theorem c012_pow_four :
    ((swap (0 : Fin 6) 1 * swap 1 2) ^ 4 : Perm (Fin 6)) = swap 0 1 * swap 1 2 := by
  decide

theorem duads456 : ∀ a b : Fin 7, (a = 4 ∨ a = 5 ∨ a = 6) → (b = 4 ∨ b = 5 ∨ b = 6) → a ≠ b →
    A6L76.vecS 7 {a, b} = A6L76.vecS 7 {4, 5} ∨ A6L76.vecS 7 {a, b} = A6L76.vecS 7 {4, 6} ∨
      A6L76.vecS 7 {a, b} = A6L76.vecS 7 {5, 6} := by
  decide

theorem c465_facts : (∀ x : Fin 7, A6L76E.cyc3 4 6 5 x ≠ x → x = 4 ∨ x = 5 ∨ x = 6) ∧
    A6L76E.cyc3 (4 : Fin 7) 6 5 4 ≠ 4 ∧ A6L76E.cyc3 (4 : Fin 7) 6 5 5 ≠ 5 ∧
    A6L76E.cyc3 (4 : Fin 7) 6 5 6 ≠ 6 ∧ A6L76E.cyc3 (4 : Fin 7) 6 5 ≠ 1 ∧
    A6L76E.cyc3 (4 : Fin 7) 6 5 4 = 6 := by
  decide

theorem mem456_of_comm {t : Perm (Fin 7)}
    (ht : t * A6L76E.cyc3 4 6 5 = A6L76E.cyc3 4 6 5 * t) {i : Fin 7}
    (hi : A6L76E.cyc3 4 6 5 i ≠ i) : t i = 4 ∨ t i = 5 ∨ t i = 6 := by
  refine c465_facts.1 _ fun h => hi (t.injective ?_)
  have e := congrArg (fun f : Perm (Fin 7) => f i) ht
  simp only [Perm.mul_apply] at e
  rw [e, h]

theorem permAct_duad {t : Perm (Fin 7)} (ht : t * A6L76E.cyc3 4 6 5 = A6L76E.cyc3 4 6 5 * t)
    {i j : Fin 7} (hi : A6L76E.cyc3 4 6 5 i ≠ i) (hj : A6L76E.cyc3 4 6 5 j ≠ j) (hij : i ≠ j) :
    G6.permAct 7 t (A6L76.vecS 7 {i, j}) = A6L76.vecS 7 {4, 5} ∨
      G6.permAct 7 t (A6L76.vecS 7 {i, j}) = A6L76.vecS 7 {4, 6} ∨
      G6.permAct 7 t (A6L76.vecS 7 {i, j}) = A6L76.vecS 7 {5, 6} := by
  rw [A6L76E.permAct_vecS]
  simp only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding]
  exact duads456 _ _ (mem456_of_comm ht hi) (mem456_of_comm ht hj) fun e => hij (t.injective e)

@[expose] def InV3c (w : G6.PermMod 7) : Prop :=
  w = 1 ∨ w = A6L76.vecS 7 {4, 5} ∨ w = A6L76.vecS 7 {4, 6} ∨ w = A6L76.vecS 7 {5, 6}

theorem permAct_inV3c {t : Perm (Fin 7)} (ht : t * A6L76E.cyc3 4 6 5 = A6L76E.cyc3 4 6 5 * t)
    {w : G6.PermMod 7} (hw : InV3c w) : InV3c (G6.permAct 7 t w) := by
  obtain ⟨-, h4, h5, h6, -, -⟩ := c465_facts
  rcases hw with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (permAct_duad ht h4 h5 (by decide))
  · exact Or.inr (permAct_duad ht h4 h6 (by decide))
  · exact Or.inr (permAct_duad ht h5 h6 (by decide))

theorem e45_mem : A6L76.vecS 7 {4, 5} ∈ (FFModel.altDn 7).sec := A6L76I.e7_facts.2.1

theorem e46_mem : A6L76.vecS 7 {4, 6} ∈ (FFModel.altDn 7).sec := A6L76I.e7_facts.2.2.1

theorem e56_mem : A6L76.vecS 7 {5, 6} ∈ (FFModel.altDn 7).sec := A6L76I.e7_facts.2.2.2.1

theorem InV3c.mem {w : G6.PermMod 7} (h : InV3c w) : w ∈ (FFModel.altDn 7).sec := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact e45_mem
  · exact e46_mem
  · exact e56_mem

theorem InV3c.mem_list {w : G6.PermMod 7} (h : InV3c w) :
    (w : (FFModel.altDn 7).Amb) ∈ ([1, A6L76.vecS 7 {4, 5}, A6L76.vecS 7 {4, 6},
      A6L76.vecS 7 {5, 6}] : List (FFModel.altDn 7).Amb) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact List.mem_cons.2 (Or.inl rfl)
  · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
  · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
  · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2
      (Or.inr (List.mem_singleton.2 rfl))))))

theorem InV3c.of_mem_list {v : (FFModel.altDn 7).Amb}
    (h : v ∈ ([1, A6L76.vecS 7 {4, 5}, A6L76.vecS 7 {4, 6}, A6L76.vecS 7 {5, 6}] :
      List (FFModel.altDn 7).Amb)) : InV3c v := by
  rcases List.mem_cons.1 h with h | h
  · exact Or.inl h
  rcases List.mem_cons.1 h with h | h
  · exact Or.inr (Or.inl h)
  rcases List.mem_cons.1 h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (List.mem_singleton.1 h)))

@[expose] def permHom (n : ℕ) : (FFModel.altDn n).Gam →* Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype

theorem e9_of_three {γ : Perm (Fin 7)} (hs : Perm.sign γ = 1) (h4 : γ 4 = 6) (h5 : γ 5 = 4)
    (h6 : γ 6 = 5) : ∃ a b : Perm (Fin 7), Perm.sign a = 1 ∧ Perm.sign b = 1 ∧
      A6L76B.E9Pair a b ∧ a * γ ^ 4 = γ ^ 4 * a ∧ b * γ ^ 4 = γ ^ 4 * b ∧
      a * A6L76E.cyc3 4 6 5 = A6L76E.cyc3 4 6 5 * a ∧
      b * A6L76E.cyc3 4 6 5 = A6L76E.cyc3 4 6 5 * b := by
  obtain ⟨hE, -, -, -, hc3⟩ := A6L76E.e9_7
  obtain ⟨-, -, -, -, hi6, hi4, hi5⟩ := A6L76I.e7_facts
  obtain ⟨-, -, -, -, hc1, hc4⟩ := c465_facts
  have hcs : Perm.sign (A6L76E.cyc3 (4 : Fin 7) 6 5) = 1 :=
    A6L76E.sign_cyc3 (by decide) (by decide)
  set c := A6L76E.cyc3 (4 : Fin 7) 6 5 with hc
  set δ := c⁻¹ * γ with hδ
  have hδ4 : δ 4 = 4 := by rw [hδ, Perm.mul_apply, h4, hi6]
  have hδ5 : δ 5 = 5 := by rw [hδ, Perm.mul_apply, h5, hi4]
  have hδ6 : δ 6 = 6 := by rw [hδ, Perm.mul_apply, h6, hi5]
  have hδs : Perm.sign δ = 1 := by rw [hδ, map_mul, map_inv, hcs, hs, inv_one, one_mul]
  have hcδ : c * δ = δ * c := A6L76E.comm_c465 hδ4 hδ5 hδ6
  have hγ4 : γ ^ 4 = c * δ ^ 4 := by
    have hγ : γ = c * δ := by rw [hδ, mul_inv_cancel_left]
    rw [hγ, (show Commute c δ from hcδ).mul_pow 4, show c ^ 4 = c ^ 3 * c from pow_succ c 3, hc3,
      one_mul]
  set δ₁ := δ ^ 4 with hδ₁
  have h14 : δ₁ 4 = 4 := Perm.pow_apply_eq_self_of_apply_eq_self hδ4 4
  have h15 : δ₁ 5 = 5 := Perm.pow_apply_eq_self_of_apply_eq_self hδ5 4
  have h16 : δ₁ 6 = 6 := Perm.pow_apply_eq_self_of_apply_eq_self hδ6 4
  have h13 : δ₁ ^ 3 = 1 := by
    rw [hδ₁, ← pow_mul]
    rcases A6L76E.alt4_cases' hδs hδ4 hδ5 hδ6 with h | h
    · rw [show 4 * 3 = 3 * 4 from rfl, pow_mul, h, one_pow]
    · rw [show 4 * 3 = 2 * 6 from rfl, pow_mul, h, one_pow]
  have h1s : Perm.sign δ₁ = 1 := by rw [hδ₁, map_pow, hδs, one_pow]
  have hcδ₁ : c * δ₁ = δ₁ * c := A6L76E.comm_c465 h14 h15 h16
  by_cases hδ1 : δ₁ = 1
  · have hγ' : γ ^ 4 = c := by rw [hγ4, hδ1, mul_one]
    refine ⟨A6L76E.cyc3 0 1 2, c, A6L76E.sign_cyc3 (by decide) (by decide), hcs, hE, ?_, ?_,
      hE.1, rfl⟩
    · rw [hγ']; exact hE.1
    · rw [hγ']
  · have hne : ∀ y : Perm (Fin 7), y 4 = 4 → c ≠ y := fun y hy e => by
      have h64 : (6 : Fin 7) = 4 :=
        hc4.symm.trans ((congrArg (fun f : Perm (Fin 7) => f 4) e).trans hy)
      exact absurd h64 (by decide)
    refine ⟨δ₁, c, h1s, hcs, ⟨hcδ₁.symm, h13, hc3, hδ1, hc1, hne _ h14, hne _ ?_⟩, ?_, ?_,
      hcδ₁.symm, rfl⟩
    · rw [Perm.mul_apply, h14, h14]
    · rw [hγ4, ← mul_assoc, ← hcδ₁]
    · rw [hγ4, ← mul_assoc, mul_assoc c δ₁ c, ← hcδ₁, mul_assoc]

end A6L76J

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem fsuV1_le_V3 : fsuV1 T V ≤ S.V3 := S.V1_le_V2.trans S.V2_le_V3

theorem exists_comm_V3 {x : ↥(Subgroup.normalizer (V : Set G))}
    (hx : S.frame.ρ x = swap 0 1 * swap 1 2) {v : G} (hv : v ∈ S.V3) :
    ∃ u ∈ S.V3, v * ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ ∈ fsuV1 T V := by
  obtain ⟨hvV, hvW⟩ := S.mem_pre.1 hv
  obtain ⟨y', hy4, hy3, hy⟩ :=
    A6L76J.w3_comm ((S.frame.ψ ⟨v, hvV⟩ : ↥W4) : P6) (S.frame.ψ ⟨v, hvV⟩).2 hvW
  have huV : ((S.frame.ψ.symm ⟨y', hy4⟩ : ↥V) : G) ∈ V := (S.frame.ψ.symm _).2
  have hψu : S.frame.ψ ⟨_, huV⟩ = ⟨y', hy4⟩ := S.frame.ψ.apply_symm_apply _
  refine ⟨_, S.mem_pre.2 ⟨huV, by rw [hψu]; exact hy3⟩, ?_⟩
  set u : G := ((S.frame.ψ.symm ⟨y', hy4⟩ : ↥V) : G) with hu
  have hxu : (x : G) * u * (x : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp x.2 u).mp huV
  have hw : v * ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ ∈ V :=
    V.mul_mem hvV (V.inv_mem (V.mul_mem hxu (V.inv_mem huV)))
  rw [S.mem_V1_iff_inV1 hw]
  have e : (⟨v * ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹, hw⟩ : ↥V) =
      ⟨v, hvV⟩ * ((⟨_, hxu⟩ : ↥V) * (⟨u, huV⟩ : ↥V)⁻¹)⁻¹ := rfl
  rw [e, map_mul, map_inv, map_mul, map_inv, S.psi_conj x ⟨u, huV⟩, hψu]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, act4_coe]
  rw [hx]
  exact hy

theorem mem_V2_cosets {u : G} (hu : u ∈ S.V2) : u ∈ fsuV1 T V ∨ u * S.v2 ∈ fsuV1 T V := by
  obtain ⟨huV, huW⟩ := S.mem_pre.1 hu
  rcases A6L76J.w2_cosets ((S.frame.ψ ⟨u, huV⟩ : ↥W4) : P6) huW with h | h
  · exact Or.inl ((S.mem_V1_iff_inV1 huV).2 h)
  · right
    rw [S.mem_V1_iff_inV1 (V.mul_mem huV S.v2_mem_V)]
    have e : (⟨u * S.v2, V.mul_mem huV S.v2_mem_V⟩ : ↥V) = ⟨u, huV⟩ * ⟨S.v2, S.v2_mem_V⟩ := rfl
    rw [e, map_mul, Subgroup.coe_mul, S.psi_v2]
    exact h

theorem conj_v2_mul_self (k : G) : (k * S.v2 * k⁻¹) * (k * S.v2 * k⁻¹) = 1 := by
  rw [show k * S.v2 * k⁻¹ * (k * S.v2 * k⁻¹) = k * (S.v2 * S.v2) * k⁻¹ by group,
    S.v2_mul_self, mul_one, mul_inv_cancel]

variable {S}

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)] {D : FFModel}

theorem conj_mem_UH (C : S.Ctx76 H K D) {k u : G} (hk : k ∈ K)
    (hu : u ∈ conjClosure S.V3 H) : k * u * k⁻¹ ∈ conjClosure S.V3 H :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (C.hKH hk)) u).mp hu

theorem βU_eq_of_mul_mem (C : S.Ctx76 H K D) {u b : G} (huU : u ∈ conjClosure S.V3 H)
    (hbU : b ∈ conjClosure S.V3 H) (hb2 : b * b = 1) (h : u * b ∈ fsuV1 T V) :
    C.βU ⟨u, huU⟩ = C.βU ⟨b, hbU⟩ := by
  have hubU : u * b ∈ conjClosure S.V3 H := (conjClosure S.V3 H).mul_mem huU hbU
  have e : (⟨u, huU⟩ : ↥(conjClosure S.V3 H)) = ⟨u * b, hubU⟩ * ⟨b, hbU⟩ := by
    apply Subtype.ext
    show u = u * b * b
    rw [mul_assoc, hb2, mul_one]
  rw [e, map_mul, C.βU_V1 h hubU, one_mul]

theorem comm_mem_V3 (C : S.Ctx76 H K D) {x : G} (hxK : x ∈ K)
    (hxN : ∀ v ∈ S.V3, x * v * x⁻¹ ∈ S.V3) {u' v : G} (hu'U : u' ∈ conjClosure S.V3 H)
    (hv3 : v ∈ S.V3) (hvU : v ∈ conjClosure S.V3 H) (hβ : C.βU ⟨u', hu'U⟩ = C.βU ⟨v, hvU⟩) :
    x * u' * x⁻¹ * u'⁻¹ ∈ S.V3 := by
  have hzU : u' * v⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem hu'U ((conjClosure S.V3 H).inv_mem hvU)
  have hz1 : C.βU ⟨u' * v⁻¹, hzU⟩ = 1 := by
    have e : (⟨u' * v⁻¹, hzU⟩ : ↥(conjClosure S.V3 H)) = ⟨u', hu'U⟩ * (⟨v, hvU⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, hβ, mul_inv_cancel]
  have hzV1 := (C.βU_eq_one_iff _).1 hz1 x hxK
  have hcU : x * v * x⁻¹ * v⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem (C.conj_mem_UH hxK hvU) ((conjClosure S.V3 H).inv_mem hvU)
  have hcz : (x * v * x⁻¹ * v⁻¹) * (u' * v⁻¹)⁻¹ = (u' * v⁻¹)⁻¹ * (x * v * x⁻¹ * v⁻¹) :=
    congrArg Subtype.val (mul_comm (⟨_, hcU⟩ : ↥(conjClosure S.V3 H))
      ⟨_, (conjClosure S.V3 H).inv_mem hzU⟩)
  have e2 : x * u' * x⁻¹ * u'⁻¹ =
      (x * (u' * v⁻¹) * x⁻¹ * (u' * v⁻¹)⁻¹) * (x * v * x⁻¹ * v⁻¹) := by
    calc x * u' * x⁻¹ * u'⁻¹ =
        x * (u' * v⁻¹) * x⁻¹ * ((x * v * x⁻¹ * v⁻¹) * (u' * v⁻¹)⁻¹) := by group
      _ = x * (u' * v⁻¹) * x⁻¹ * ((u' * v⁻¹)⁻¹ * (x * v * x⁻¹ * v⁻¹)) := by rw [hcz]
      _ = _ := by group
  rw [e2]
  exact S.V3.mul_mem (S.fsuV1_le_V3 hzV1) (S.V3.mul_mem (hxN v hv3) (S.V3.inv_mem hv3))

theorem conj_comm_mem_V3 (C : S.Ctx76 H K D) {x d : G}
    (hxK : x ∈ K) (hxN : ∀ v ∈ S.V3, x * v * x⁻¹ ∈ S.V3) (hdK : d ∈ K)
    (hcomm : C.α ⟨d, hdK⟩ * C.α ⟨x, hxK⟩ = C.α ⟨x, hxK⟩ * C.α ⟨d, hdK⟩) {u v : G}
    (hduU : d * u * d⁻¹ ∈ conjClosure S.V3 H) (hv3 : v ∈ S.V3)
    (hvU : v ∈ conjClosure S.V3 H) (hβ : C.βU ⟨d * u * d⁻¹, hduU⟩ = C.βU ⟨v, hvU⟩) :
    d * (x * u * x⁻¹ * u⁻¹) * d⁻¹ ∈ S.V3 := by
  have hqK : x⁻¹ * d * x * d⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hxK) hdK) hxK) (K.inv_mem hdK)
  have hqα : C.α ⟨x⁻¹ * d * x * d⁻¹, hqK⟩ = 1 := by
    have e : (⟨x⁻¹ * d * x * d⁻¹, hqK⟩ : ↥K) =
        (⟨x, hxK⟩ : ↥K)⁻¹ * ⟨d, hdK⟩ * ⟨x, hxK⟩ * (⟨d, hdK⟩ : ↥K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ (C.α ⟨d, hdK⟩), hcomm]
    group
  have hqU := (S.mem_QH_iff_tilde C.hNS C.h13315 C.h1356two C.hH (C.hKH hqK)).1
    ((C.α_eq_one_iff ⟨_, hqK⟩).1 hqα) _ hduU
  have key : d * (x * u * x⁻¹ * u⁻¹) * d⁻¹ =
      (x * ((x⁻¹ * d * x * d⁻¹) * (d * u * d⁻¹) * (x⁻¹ * d * x * d⁻¹)⁻¹ * (d * u * d⁻¹)⁻¹) *
        x⁻¹) * (x * (d * u * d⁻¹) * x⁻¹ * (d * u * d⁻¹)⁻¹) := by group
  rw [key, S.conj_V1_of_mem C.hH (C.hKH hxK) hqU]
  exact S.V3.mul_mem (S.fsuV1_le_V3 hqU) (C.comm_mem_V3 hxK hxN hduU hv3 hvU hβ)

variable (C : S.Ctx76 H K (FFModel.altDn 7))
  {g : ↥(Subgroup.normalizer (V : Set G))} (hgL : (g : G) ∈ S.L1)
  (hg : S.frame.ρ g = swap 0 1 * swap 1 2)
  (h45 : C.βU ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨_, A6L76J.e45_mem⟩)
  (h46 : C.βU ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ =
    QuotientGroup.mk ⟨_, A6L76J.e46_mem⟩)
include h45 h46

theorem βU_prod : C.βU ⟨S.v2 * ((g : G) * S.v2 * (g : G)⁻¹), (conjClosure S.V3 H).mul_mem
    (S.v2_mem_UH H) (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H))⟩ =
      QuotientGroup.mk ⟨_, A6L76J.e56_mem⟩ := by
  rw [show (⟨S.v2 * ((g : G) * S.v2 * (g : G)⁻¹), (conjClosure S.V3 H).mul_mem
      (S.v2_mem_UH H) (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H))⟩ :
        ↥(conjClosure S.V3 H)) = ⟨S.v2, S.v2_mem_UH H⟩ *
      ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ from rfl, map_mul, h45, h46,
    ← QuotientGroup.mk_mul, show (⟨_, A6L76J.e45_mem⟩ * ⟨_, A6L76J.e46_mem⟩ :
      ↥(FFModel.altDn 7).sec) = ⟨_, A6L76J.e56_mem⟩ from Subtype.ext A6L76I.e7_facts.1]

include hg in
theorem classes_V3 {u : G} (hu3 : u ∈ S.V3) (huU : u ∈ conjClosure S.V3 H) :
    ∃ (w : G6.PermMod 7) (hw : w ∈ (FFModel.altDn 7).sec),
      C.βU ⟨u, huU⟩ = QuotientGroup.mk ⟨w, hw⟩ ∧ A6L76J.InV3c w := by
  rcases S.mem_V3_cases hg hu3 with h | h | h | h
  · refine ⟨1, Subgroup.one_mem _, ?_, Or.inl rfl⟩
    rw [C.βU_V1 h huU]
    exact (QuotientGroup.mk_one _).symm
  · exact ⟨_, A6L76J.e45_mem,
      (C.βU_eq_of_mul_mem huU (S.v2_mem_UH H) S.v2_mul_self h).trans h45, Or.inr (Or.inl rfl)⟩
  · exact ⟨_, A6L76J.e46_mem, (C.βU_eq_of_mul_mem huU _ (S.conj_v2_mul_self _) h).trans h46,
      Or.inr (Or.inr (Or.inl rfl))⟩
  · rw [← S.v2_mul_conj hg] at h
    have hb2 : (S.v2 * ((g : G) * S.v2 * (g : G)⁻¹)) * (S.v2 * ((g : G) * S.v2 * (g : G)⁻¹)) =
        1 := by
      rw [S.v2_mul_conj hg]
      exact S.conj_v2_mul_self _
    exact ⟨_, A6L76J.e56_mem, (C.βU_eq_of_mul_mem huU _ hb2 h).trans (C.βU_prod hgL h45 h46),
      Or.inr (Or.inr (Or.inr rfl))⟩

include hg in
theorem reps_V3 {w : G6.PermMod 7} (hw : w ∈ (FFModel.altDn 7).sec) (hc : A6L76J.InV3c w) :
    ∃ v ∈ S.V3, ∃ hvU : v ∈ conjClosure S.V3 H,
      C.βU ⟨v, hvU⟩ = QuotientGroup.mk ⟨w, hw⟩ := by
  rcases hc with rfl | rfl | rfl | rfl
  · refine ⟨1, S.V3.one_mem, (conjClosure S.V3 H).one_mem, ?_⟩
    rw [show (⟨1, (conjClosure S.V3 H).one_mem⟩ : ↥(conjClosure S.V3 H)) = 1 from rfl, map_one]
    exact (QuotientGroup.mk_one _).symm
  · exact ⟨S.v2, S.v2_mem_V3, S.v2_mem_UH H, h45⟩
  · exact ⟨_, S.conj_v2_mem_V3 hg, _, h46⟩
  · exact ⟨_, S.V3.mul_mem S.v2_mem_V3 (S.conj_v2_mem_V3 hg), _, C.βU_prod hgL h45 h46⟩

include hg in
theorem exists_V3_conj {d : G} (hdK : d ∈ K)
    (ht : A6L76C.permOf (C.α ⟨d, hdK⟩) * A6L76E.cyc3 4 6 5 =
      A6L76E.cyc3 4 6 5 * A6L76C.permOf (C.α ⟨d, hdK⟩))
    {u : G} (hu3 : u ∈ S.V3) (huU : u ∈ conjClosure S.V3 H) :
    ∃ v ∈ S.V3, ∃ hvU : v ∈ conjClosure S.V3 H,
      C.βU ⟨d * u * d⁻¹, C.conj_mem_UH hdK huU⟩ = C.βU ⟨v, hvU⟩ := by
  obtain ⟨w, hw, hβ, hc⟩ := C.classes_V3 hgL hg h45 h46 hu3 huU
  have h1 := C.βU_equiv ⟨d, hdK⟩ ⟨u, huU⟩ (C.conj_mem_UH hdK huU) hw hβ
  obtain ⟨v, hv3, hvU, hv⟩ := C.reps_V3 hgL hg h45 h46 (G6.permAct_mem_coreMod _ hw)
    (A6L76J.permAct_inV3c ht hc)
  exact ⟨v, hv3, hvU, h1.trans hv.symm⟩

include hg in
theorem conj_mem_V3_of_comm {x : ↥(Subgroup.normalizer (V : Set G))}
    (hxL : (x : G) ∈ S.L1)
    (hx : S.frame.ρ x = swap 0 1 * swap 1 2) {d : G} (hdK : d ∈ K)
    (hcx : A6L76C.permOf (C.α ⟨d, hdK⟩) * A6L76C.permOf (C.α ⟨x, C.hL1K hxL⟩) =
      A6L76C.permOf (C.α ⟨x, C.hL1K hxL⟩) * A6L76C.permOf (C.α ⟨d, hdK⟩))
    (ht : A6L76C.permOf (C.α ⟨d, hdK⟩) * A6L76E.cyc3 4 6 5 =
      A6L76E.cyc3 4 6 5 * A6L76C.permOf (C.α ⟨d, hdK⟩)) {v : G} (hv : v ∈ S.V3) :
    d * v * d⁻¹ ∈ S.V3 := by
  obtain ⟨u, hu3, hw⟩ := S.exists_comm_V3 hx hv
  have huU : u ∈ conjClosure S.V3 H := le_conjClosure _ _ hu3
  obtain ⟨v', hv'3, hv'U, hβ⟩ := C.exists_V3_conj hgL hg h45 h46 hdK ht hu3 huU
  have h1 := C.conj_comm_mem_V3 (C.hL1K hxL) (fun _ hw' => conj_V3_of_L1 hxL hw') hdK
    (A6L76C.permOf_injective hcx) (C.conj_mem_UH hdK huU) hv'3 hv'U hβ
  have e : d * v * d⁻¹ = (d * (v * ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹) * d⁻¹) *
      (d * ((x : G) * u * (x : G)⁻¹ * u⁻¹) * d⁻¹) := by group
  rw [e, S.conj_V1_of_mem C.hH (C.hKH hdK) hw]
  exact S.V3.mul_mem (S.fsuV1_le_V3 hw) h1

include hg in
theorem points_seven : A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) 4 = 6 ∧
    A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) 5 = 4 ∧ A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) 6 = 5 := by
  have h1 := C.βU_equiv ⟨g, C.hL1K hgL⟩ ⟨S.v2, S.v2_mem_UH H⟩
    (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)) A6L76J.e45_mem h45
  have h2 := A6L76H.eq_of_mk_eq A6L76H.sum_one_seven (h46.symm.trans h1)
  have hγ1 : G6.permAct 7 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) (A6L76.vecS 7 {4, 5}) =
      A6L76.vecS 7 {4, 6} := (A6L76C.act_eq _ _).symm.trans (congrArg Subtype.val h2).symm
  obtain ⟨-, hmz⟩ := C.classes_odd A6L76H.sum_one_seven hgL hg A6L76J.e45_mem h45
  have hγ2 : G6.permAct 7 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) (A6L76.vecS 7 {4, 6}) =
      A6L76.vecS 7 {5, 6} := by
    rw [← hγ1, ← MulAut.mul_apply, ← map_mul, ← pow_two, ← hmz, hγ1, A6L76I.e7_facts.1]
  exact A6L76E.eps7_points hγ1 hγ2

include hg in
theorem hat_of_seven (h1337 : Stmt13_3_7) : IsHatA6 L := by
  by_contra hhat
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := S.pRank_three_NV3_le_one C.h13315 h1337 hhat C.hH
  obtain ⟨h4, h5, h6⟩ := C.points_seven hgL hg h45 h46
  have hxL : ((g ^ 4 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.L1 := by
    rw [Subgroup.coe_pow]
    exact S.L1.pow_mem hgL 4
  have hx : S.frame.ρ (g ^ 4) = swap 0 1 * swap 1 2 := by
    rw [map_pow, hg]
    exact A6L76J.c012_pow_four
  have hxα : A6L76C.permOf (C.α ⟨_, C.hL1K hxL⟩) =
      A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) ^ 4 := by
    rw [show A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) ^ 4 =
      A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩ ^ 4) from rfl, ← map_pow]
    congr 2
  obtain ⟨a, b, has, hbs, hE, hag, hbg, hac, hbc⟩ :=
    A6L76J.e9_of_three (A6L76C.permOf_sign _) h4 h5 h6
  set Y : Subgroup (FFModel.altDn 7).Gam :=
    (Subgroup.centralizer ({A6L76C.permOf (C.α ⟨_, C.hL1K hxL⟩), A6L76E.cyc3 4 6 5} :
      Set (Perm (Fin 7)))).comap (A6L76J.permHom 7) with hY
  have hmemY : ∀ t : Perm (Fin 7), t * A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) ^ 4 =
      A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) ^ 4 * t →
      t * A6L76E.cyc3 4 6 5 = A6L76E.cyc3 4 6 5 * t → ∀ ht : t ∈ alternatingGroup (Fin 7),
      (⟨t, ht⟩ : (FFModel.altDn 7).Gam) ∈ Y := by
    intro t h1 h2 ht
    show t ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · rw [hxα]
      exact h1.symm
    · exact h2.symm
  have h2 : 2 ≤ CFSG.Open.pRank 3 Y :=
    A6L76B.two_le_pRank_of_e9 (hmemY a hag hac (Perm.mem_alternatingGroup.2 has))
      (hmemY b hbg hbc (Perm.mem_alternatingGroup.2 hbs)) (A6L76H.e9_of_perm hE)
  have h3 := A6L76B.pRank_map_le C.α C.not_three_dvd_ker (Y.comap C.α)
  rw [Subgroup.map_comap_eq_self_of_surjective C.α_surj] at h3
  have h4' := A6L76F.pRank_le_map_of_not_dvd (p := 3) K.subtype
    (by rw [Subgroup.ker_subtype, Subgroup.card_bot]; norm_num) (Y.comap C.α)
  have hfwd : ∀ d : ↥K, d ∈ Y.comap C.α → ∀ v ∈ S.V3, (d : G) * v * (d : G)⁻¹ ∈ S.V3 := by
    intro d hd v hv
    have hc : A6L76J.permHom 7 (C.α d) ∈ Subgroup.centralizer
        ({A6L76C.permOf (C.α ⟨_, C.hL1K hxL⟩), A6L76E.cyc3 4 6 5} : Set (Perm (Fin 7))) := hd
    rw [Subgroup.mem_centralizer_iff] at hc
    exact C.conj_mem_V3_of_comm hgL hg h45 h46 hxL hx d.2 (hc _ (Set.mem_insert _ _)).symm
      (hc _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))).symm hv
  have hXN : (Y.comap C.α).map K.subtype ≤ H ⊓ Subgroup.normalizer (S.V3 : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨C.hKH d.2, Subgroup.mem_normalizer_iff.2 fun v => ⟨hfwd d hd v, fun h => ?_⟩⟩
    have h1 : ((d⁻¹ : ↥K) : G) * ((d : G) * v * (d : G)⁻¹) * ((d⁻¹ : ↥K) : G)⁻¹ ∈ S.V3 :=
      hfwd d⁻¹ ((Y.comap C.α).inv_mem hd) _ h
    have e : ((d⁻¹ : ↥K) : G) * ((d : G) * v * (d : G)⁻¹) * ((d⁻¹ : ↥K) : G)⁻¹ = v := by
      rw [Subgroup.coe_inv]
      group
    rwa [e] at h1
  have h5' := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hXN
  omega

omit h46 in
theorem mapsOnto_V2 : A6L76.MapsOnto C.β ((S.V2.subgroupOf (conjClosure S.V3 H)).map
    (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      ([1, A6L76.vecS 7 {4, 5}] : List (FFModel.altDn 7).Amb) := by
  refine ⟨fun x hx => ?_, fun v hv => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hx
    have e : x = C.ι y := Subtype.ext hxy.symm
    have hy2 : (y : G) ∈ S.V2 := Subgroup.mem_subgroupOf.1 hy
    rw [e]
    rcases S.mem_V2_cosets hy2 with h | h
    · refine ⟨1, ?_, List.mem_cons.2 (Or.inl rfl)⟩
      rw [show C.β (C.ι y) = C.βU ⟨y, y.2⟩ from rfl, C.βU_V1 h y.2]
      exact (QuotientGroup.mk_one _).symm
    · exact ⟨⟨_, A6L76J.e45_mem⟩,
        (C.βU_eq_of_mul_mem y.2 (S.v2_mem_UH H) S.v2_mul_self h).trans h45,
        List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl))⟩
  · rcases List.mem_cons.1 hv with rfl | hv
    · exact ⟨1, Subgroup.one_mem _, 1, by rw [map_one]; exact (QuotientGroup.mk_one _).symm, rfl⟩
    · rw [List.mem_singleton.1 hv]
      exact ⟨C.ι ⟨S.v2, S.v2_mem_UH H⟩, Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.2 S.v2_mem_V2 : (⟨S.v2, S.v2_mem_UH H⟩ : ↥(conjClosure S.V3 H)) ∈
          S.V2.subgroupOf (conjClosure S.V3 H)), ⟨_, A6L76J.e45_mem⟩, h45, rfl⟩

include hg in
theorem mapsOnto_V3 : A6L76.MapsOnto C.β ((S.V3.subgroupOf (conjClosure S.V3 H)).map
    (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      ([1, A6L76.vecS 7 {4, 5}, A6L76.vecS 7 {4, 6}, A6L76.vecS 7 {5, 6}] :
        List (FFModel.altDn 7).Amb) := by
  refine ⟨fun x hx => ?_, fun v hv => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hx
    have e : x = C.ι y := Subtype.ext hxy.symm
    rw [e]
    obtain ⟨w, hw, hβ, hc⟩ := C.classes_V3 hgL hg h45 h46 (Subgroup.mem_subgroupOf.1 hy) y.2
    exact ⟨⟨w, hw⟩, hβ, hc.mem_list⟩
  · have hc := A6L76J.InV3c.of_mem_list hv
    obtain ⟨u, hu3, huU, hβ⟩ := C.reps_V3 hgL hg h45 h46 hc.mem hc
    exact ⟨C.ι ⟨u, huU⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hu3 :
      (⟨u, huU⟩ : ↥(conjClosure S.V3 H)) ∈ S.V3.subgroupOf (conjClosure S.V3 H)),
      ⟨v, hc.mem⟩, hβ, rfl⟩

end Ctx76

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem exists_normal7 (h13314 : Stmt13_3_14)
    (C : S.Ctx76 H K (FFModel.altDn 7)) {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) (hg : S.frame.ρ g = swap 0 1 * swap 1 2) :
    ∃ C' : S.Ctx76 H K (FFModel.altDn 7),
      C'.βU ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨_, A6L76J.e45_mem⟩ ∧
      C'.βU ⟨_, C'.conj_mem_UH (C'.hL1K hgL) (S.v2_mem_UH H)⟩ =
        QuotientGroup.mk ⟨_, A6L76J.e46_mem⟩ := by
  obtain ⟨m, hm, hxm⟩ := C.exists_rep
  obtain ⟨hwm, hwy, hwz, hne, -⟩ := C.classes7 h13314 hgL hg hm hxm
  obtain ⟨h1, h2⟩ := A6L76E.tri7 _ _ hwm hwy hwz hne
  refine ⟨C.twist (A6L76E.tau7 m (G6.permAct 7 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) m)),
    ?_, ?_⟩
  · rw [C.twist_βU, hxm, A6L76C.twistQ_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext h1)
  · rw [C.twist_βU, C.βU_equiv ⟨g, C.hL1K hgL⟩ ⟨S.v2, S.v2_mem_UH H⟩
      (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)) hm hxm, A6L76C.twistQ_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext h2)

theorem seven (h13314 : Stmt13_3_14) (h1337 : Stmt13_3_7)
    (C : S.Ctx76 H K (FFModel.altDn 7)) :
    IsHatA6 L ∧
      ∃ (π : (FFModel.altDn 7).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
          ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec),
        CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 7)
          (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
          (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
          (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
            commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β ∧
        A6L76.MapsOnto β ((S.V2.subgroupOf (conjClosure S.V3 H)).map
            (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
          ([1, A6L76.vecS 7 {4, 5}] : List (FFModel.altDn 7).Amb) ∧
        A6L76.MapsOnto β ((S.V3.subgroupOf (conjClosure S.V3 H)).map
            (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
          ([1, A6L76.vecS 7 {4, 5}, A6L76.vecS 7 {4, 6}, A6L76.vecS 7 {5, 6}] :
            List (FFModel.altDn 7).Amb) := by
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  obtain ⟨C', h45, h46⟩ := C.exists_normal7 h13314 hgL hg
  exact ⟨C'.hat_of_seven hgL hg h45 h46 h1337, C'.π, C'.β, C'.hR, C'.mapsOnto_V2 h45,
    C'.mapsOnto_V3 hgL hg h45 h46⟩

end Ctx76

end Setting4

end CFSG.Quasithin.H13.A6
