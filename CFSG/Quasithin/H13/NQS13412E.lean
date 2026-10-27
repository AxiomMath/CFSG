module

public import CFSG.Quasithin.H13.NQS134108E

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

@[expose] def l3p : L3.Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

theorem l3p_mem : L3.act l3p l3e1 = l3e1 := by decide +kernel

theorem l3_selfnorm : ∀ γ : L3.Γ, L3.act (γ * l3p * γ⁻¹) l3e1 = l3e1 →
    L3.act γ l3e1 = l3e1 := by
  decide +kernel

@[expose] def a6p : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

theorem a6p_mem : a6p ∈ stab45List := by decide +kernel

theorem a6_selfnorm : ∀ γ : Perm (Fin 6), γ * a6p * γ⁻¹ ∈ stab45List → γ ^ 45 = 1 →
    γ ∈ stab45List := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem ParData.exists_of_odd {K T U L1T : Subgroup G} {Γ : Type} [Group Γ]
    {ρ : ↥(normalizer (U : Set G)) →* Γ} {Q P : Subgroup Γ} (DP : ParData K T U L1T ρ Q P)
    (hPQ : P ≤ Q)
    (hρker : ∀ g : ↥(normalizer (U : Set G)), ρ g = 1 → (g : G) ∈ centralizer (U : Set G))
    {p : Γ} (hp : p ∈ P)
    (hfin : ∀ γ : Γ, γ * p * γ⁻¹ ∈ P → (∃ m : ℕ, Odd m ∧ γ ^ m = 1) → γ ∈ P)
    {y : G} (hyU : y ∈ normalizer (U : Set G)) (hyK : y ∈ normalizer (K : Set G))
    (hyL : ∀ k ∈ K, k ∈ L1T → y * k * y⁻¹ ∈ L1T) (hy : ∃ m : ℕ, Odd m ∧ y ^ m = 1) :
    ∃ k ∈ K, k ∈ L1T ∧ y * k⁻¹ ∈ centralizer (U : Set G) := by
  obtain ⟨g₁, hg₁K, hg₁⟩ := DP.img p (hPQ hp)
  have hg₁L : (g₁ : G) ∈ L1T := (DP.P_iff g₁ hg₁K).1 (hg₁ ▸ hp)
  set ny : ↥(normalizer (U : Set G)) := ⟨y, hyU⟩ with hny
  have hc : ρ ny * p * (ρ ny)⁻¹ ∈ P := by
    have hK' : ((ny * g₁ * ny⁻¹ : ↥(normalizer (U : Set G))) : G) ∈ K :=
      (mem_normalizer_iff.mp hyK _).mp hg₁K
    have hL' : ((ny * g₁ * ny⁻¹ : ↥(normalizer (U : Set G))) : G) ∈ L1T :=
      hyL _ hg₁K hg₁L
    have := (DP.P_iff _ hK').2 hL'
    rwa [map_mul, map_mul, map_inv, hg₁] at this
  have hodd : ∃ m : ℕ, Odd m ∧ ρ ny ^ m = 1 := by
    obtain ⟨m, hm, hym⟩ := hy
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, show ny ^ m = 1 from Subtype.ext (by simpa using hym), map_one]
  have hP : ρ ny ∈ P := hfin _ hc hodd
  obtain ⟨g, hgK, hgρ⟩ := DP.img (ρ ny) (hPQ hP)
  have hgL : (g : G) ∈ L1T := (DP.P_iff g hgK).1 (hgρ ▸ hP)
  refine ⟨g, hgK, hgL, ?_⟩
  have h1 : ρ (ny * g⁻¹) = 1 := by rw [map_mul, map_inv, hgρ, mul_inv_cancel]
  exact hρker _ h1

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem zV_eq_mul (hV1 : Nat.card ↥(fsuV1 T V) = 4) {zb : G} (hzb : zb ∈ fsuV1 T V)
    (hzbL : zb ∉ centralizer (L : Set G)) (hzbz : zb ≠ z) : S.zV = z * zb := by
  have h2 : ∀ u ∈ fsuV1 T V, u * u = 1 := fun u hu => by
    rw [← pow_two]
    exact (mem_quasithinOmegaOneCenter_iff.1 hu.2).2.2
  have hvV1 : S.zV ∈ fsuV1 T V := ⟨S.zV_mem_V, U3.s134_zV_mem_Z S⟩
  have hvL : S.zV ∈ centralizer (L : Set G) := (S.mem_ZV_iff.2 (Or.inr rfl)).2
  have hzb1 : zb ≠ 1 := fun h => hzbL (h ▸ one_mem _)
  have h := mul_mul_eq_one_of_card_four hV1 h2 D.zV1 hzb hvV1 D.z_ne_one hzb1 S.zV_ne_one
    hzbz.symm (fun h => D.zL (h ▸ hvL)) (fun h => hzbL (h ▸ hvL))
  rw [eq_inv_of_mul_eq_one_right h]
  exact inv_eq_of_mul_eq_one_right (h2 _ (mul_mem D.zV1 hzb))

theorem conj_mem_W (hV1 : Nat.card ↥(fsuV1 T V) = 4) (hZVW : V ⊓ centralizer (L : Set G) ≤ W)
    {zb : G} (hzb : zb ∈ fsuV1 T V) (hzbL : zb ∉ centralizer (L : Set G)) (hzbz : zb ≠ z)
    {h : G} (hhK : h ∈ normalizer (K : Set G)) (hhzb : h * zb = zb * h) {w : G} (hw : w ∈ W) :
    h⁻¹ * w * h ∈ W := by
  set v := S.zV with hv
  have hvW : v ∈ W := hZVW (S.mem_ZV_iff.2 (Or.inr rfl))
  have hvz : v = z * zb := D.zV_eq_mul hV1 hzb hzbL hzbz
  have hKW : K ≤ normalizer (W : Set G) := D.Wirr.2.2.1
  have hzK : ∀ k ∈ K, z⁻¹ * k * z = k := fun k hk => by
    have h1 : k * z = z * k := mem_centralizer_singleton_iff.1 (D.Kz hk)
    rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
  have hfW : ∀ k ∈ K, v⁻¹ * k * v * k⁻¹ ∈ W := fun k hk => by
    have h1 : k * v * k⁻¹ ∈ W := (mem_normalizer_iff.mp (hKW hk) v).mp hvW
    rw [mul_assoc (v⁻¹ * k), mul_assoc v⁻¹]
    exact mul_mem (inv_mem hvW) (by simpa [mul_assoc] using h1)
  have hconj : ∀ k ∈ K, h⁻¹ * (v⁻¹ * k * v * k⁻¹) * h =
      v⁻¹ * (h⁻¹ * k * h) * v * (h⁻¹ * k * h)⁻¹ := by
    intro k hk
    have hk' : h⁻¹ * k * h ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hhK) k).mp hk
      simpa using this
    have e3 : h⁻¹ * zb⁻¹ = zb⁻¹ * h⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hhzb]
    have e4 : h * zb * h⁻¹ = zb := by rw [hhzb, mul_inv_cancel_right]
    calc h⁻¹ * (v⁻¹ * k * v * k⁻¹) * h = h⁻¹ * zb⁻¹ * (z⁻¹ * k * z) * zb * k⁻¹ * h := by
          rw [hvz]; group
      _ = zb⁻¹ * h⁻¹ * k * zb * k⁻¹ * h := by rw [hzK k hk, e3]
      _ = zb⁻¹ * h⁻¹ * k * (h * zb * h⁻¹) * k⁻¹ * h := by rw [e4]
      _ = zb⁻¹ * (z⁻¹ * (h⁻¹ * k * h) * z) * zb * (h⁻¹ * k * h)⁻¹ := by
          rw [hzK _ hk']; group
      _ = v⁻¹ * (h⁻¹ * k * h) * v * (h⁻¹ * k * h)⁻¹ := by rw [hvz]; group
  set W₁ := closure {x : G | ∃ k ∈ K, x = v⁻¹ * k * v * k⁻¹} with hW₁
  have hW₁W : W₁ ≤ W := (closure_le _).2 fun x ⟨k, hk, hx⟩ => hx ▸ hfW k hk
  have hW₁h : ∀ x ∈ W₁, h⁻¹ * x * h ∈ W := by
    intro x hx
    have hle : W₁ ≤ W.comap (MulAut.conj h⁻¹).toMonoidHom := by
      refine (closure_le _).2 fun x ⟨k, hk, hx⟩ => ?_
      show (MulAut.conj h⁻¹) x ∈ W
      rw [MulAut.conj_apply, inv_inv, hx, hconj k hk]
      have hk' : h⁻¹ * k * h ∈ K := by
        have := (mem_normalizer_iff.mp (inv_mem hhK) k).mp hk
        simpa using this
      exact hfW _ hk'
    have := hle hx
    simpa [MulAut.conj_apply] using this
  have hKW₁ : K ≤ normalizer (W₁ : Set G) := by
    rw [hW₁, le_normalizer_closure_iff]
    rintro k' hk' x ⟨k, hk, rfl⟩
    have e : k' * (v⁻¹ * k * v * k⁻¹) * k'⁻¹ =
        (v⁻¹ * k' * v * k'⁻¹)⁻¹ * (v⁻¹ * (k' * k) * v * (k' * k)⁻¹) := by group
    rw [e]
    exact mul_mem (inv_mem (subset_closure ⟨k', hk', rfl⟩))
      (subset_closure ⟨k' * k, mul_mem hk' hk, rfl⟩)
  have hcommW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥W) ⟨b, hb⟩)
  set C := W ⊓ centralizer (K : Set G) with hC
  have hCK : K ≤ normalizer (C : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hKW hg, le_normalizer_centralizer_of le_normalizer hg⟩
  have hJK : K ≤ normalizer ((W₁ ⊔ C : Subgroup G) : Set G) := by
    rw [← closure_eq W₁, ← closure_eq C, ← Subgroup.closure_union, le_normalizer_closure_iff]
    rintro k hk x (hx | hx)
    · exact subset_closure (Or.inl ((mem_normalizer_iff.mp (hKW₁ hk) x).mp hx))
    · exact subset_closure (Or.inr ((mem_normalizer_iff.mp (hCK hk) x).mp hx))
  have hWW₁ : W ≤ W₁ := by
    rcases D.Wirr.2.2.2.2.2.1 (W₁ ⊔ C) le_sup_right (sup_le hW₁W inf_le_left) hJK with
      hJ | hJ
    ·
      exfalso
      have hfC : ∀ k ∈ K, v⁻¹ * k * v * k⁻¹ ∈ centralizer (K : Set G) := fun k hk =>
        (mem_inf.1 (hJ ▸ (le_sup_left : W₁ ≤ W₁ ⊔ C) (subset_closure ⟨k, hk, rfl⟩))).2
      have hkv : ∀ k ∈ K, k * v * k⁻¹ = v * (v⁻¹ * k * v * k⁻¹) := fun k hk => by group
      set N := K ⊓ centralizer ({v} : Set G) with hN
      have hNnorm : (N.subgroupOf K).Normal := by
        rw [normal_subgroupOf_iff inf_le_left]
        intro n k hn hk
        refine mem_inf.2 ⟨mul_mem (mul_mem hk (mem_inf.1 hn).1) (inv_mem hk),
          mem_centralizer_singleton_iff.2 ?_⟩
        have hnv : n * v = v * n := mem_centralizer_singleton_iff.1 (mem_inf.1 hn).2
        set c := v⁻¹ * k * v * k⁻¹ with hc
        have hcK := hfC k hk
        have hcn : n * c = c * n := mem_centralizer_iff.1 hcK n (mem_inf.1 hn).1
        have hck : k * c = c * k := mem_centralizer_iff.1 hcK k hk
        have e1 : k⁻¹ * v * k = v * c⁻¹ := by
          have h1 : k * v * k⁻¹ = v * c := hkv k hk
          have h2 : v = k⁻¹ * (v * c) * k := by rw [← h1]; group
          calc k⁻¹ * v * k = k⁻¹ * v * k * c * c⁻¹ := by group
            _ = k⁻¹ * v * (k * c) * c⁻¹ := by group
            _ = k⁻¹ * v * (c * k) * c⁻¹ := by rw [hck]
            _ = k⁻¹ * (v * c) * k * c⁻¹ := by group
            _ = v * c⁻¹ := by rw [← h2]
        calc k * n * k⁻¹ * v = k * n * (k⁻¹ * v * k) * k⁻¹ := by group
          _ = k * n * (v * c⁻¹) * k⁻¹ := by rw [e1]
          _ = k * (n * v) * c⁻¹ * k⁻¹ := by group
          _ = k * (v * n) * c⁻¹ * k⁻¹ := by rw [hnv]
          _ = k * v * (n * c⁻¹) * k⁻¹ := by group
          _ = k * v * (c⁻¹ * n) * k⁻¹ := by
              have e2 : n * c⁻¹ = c⁻¹ * n := by
                calc n * c⁻¹ = c⁻¹ * (c * n) * c⁻¹ := by group
                  _ = c⁻¹ * (n * c) * c⁻¹ := by rw [hcn]
                  _ = c⁻¹ * n := by group
              rw [e2]
          _ = k * (v * c⁻¹) * n * k⁻¹ := by group
          _ = k * (k⁻¹ * v * k) * n * k⁻¹ := by rw [e1]
          _ = v * (k * n * k⁻¹) := by group
      have hN2 : ∀ x ∈ K, ∃ j : ℕ, x ^ 2 ^ j ∈ N := by
        intro x hx
        refine ⟨1, mem_inf.2 ⟨pow_mem hx _, mem_centralizer_singleton_iff.2 ?_⟩⟩
        set c := v⁻¹ * x * v * x⁻¹ with hc
        have hcW : c ∈ W := hfW x hx
        have hcx : x * c = c * x := mem_centralizer_iff.1 (hfC x hx) x hx
        have hcc : c * c = 1 := by rw [← pow_two]; exact D.sq_eq_one hcW
        have h1 : x * v * x⁻¹ = v * c := hkv x hx
        have h2 : x ^ 2 ^ 1 * v * (x ^ 2 ^ 1)⁻¹ = v := by
          calc x ^ 2 ^ 1 * v * (x ^ 2 ^ 1)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by
                rw [pow_one, pow_two]; group
            _ = x * (v * c) * x⁻¹ := by rw [h1]
            _ = (x * v * x⁻¹) * (x * c * x⁻¹) := by group
            _ = v * c * c := by rw [h1, hcx, mul_inv_cancel_right]
            _ = v := by rw [mul_assoc, hcc, mul_one]
        calc x ^ 2 ^ 1 * v = x ^ 2 ^ 1 * v * (x ^ 2 ^ 1)⁻¹ * x ^ 2 ^ 1 := by group
          _ = v * x ^ 2 ^ 1 := by rw [h2]
      have hNK : N = K := D.Kf.2.1 N inf_le_left hNnorm hN2
      apply D.KZV
      intro k hk
      rw [mem_centralizer_iff]
      intro x hx
      rcases S.mem_ZV_iff.1 hx with rfl | rfl
      · rw [one_mul, mul_one]
      · have : k ∈ N := hNK ▸ hk
        exact (mem_centralizer_singleton_iff.1 (mem_inf.1 this).2).symm
    ·
      rw [← D.Wirr.2.2.2.1, commutator_le]
      intro w hw k hk
      have hCW₁ : C ≤ normalizer (W₁ : Set G) := fun c hc => mem_normalizer_iff.2 fun x => by
        constructor
        · intro hx
          rw [hcommW c (mem_inf.1 hc).1 x (hW₁W hx), mul_inv_cancel_right]
          exact hx
        · intro hx
          have e : x = c * x * c⁻¹ := by
            rw [hcommW c (mem_inf.1 hc).1 x ?_, mul_inv_cancel_right]
            have h1 := hW₁W hx
            have h2 : c⁻¹ * (c * x * c⁻¹) * c ∈ W := mul_mem (mul_mem (inv_mem (mem_inf.1 hc).1)
              h1) (mem_inf.1 hc).1
            simpa [mul_assoc] using h2
          rw [e]
          exact hx
      have hw' : w ∈ W₁ ⊔ C := hJ ▸ hw
      obtain ⟨w₁, hw₁, c, hc, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hCW₁ hw'
      have hck : c * k = k * c := (mem_centralizer_iff.1 (mem_inf.1 hc).2 k hk).symm
      have e : ⁅w₁ * c, k⁆ = w₁ * (k * w₁⁻¹ * k⁻¹) := by
        rw [commutatorElement_def]
        calc w₁ * c * k * (w₁ * c)⁻¹ * k⁻¹ = w₁ * (c * k) * c⁻¹ * w₁⁻¹ * k⁻¹ := by group
          _ = w₁ * (k * c) * c⁻¹ * w₁⁻¹ * k⁻¹ := by rw [hck]
          _ = w₁ * (k * w₁⁻¹ * k⁻¹) := by group
      rw [e]
      exact mul_mem hw₁ ((mem_normalizer_iff.mp (hKW₁ hk) _).mp (inv_mem hw₁))
  exact hW₁h w (hWW₁ hw)

theorem le_normalizer_W (hV1 : Nat.card ↥(fsuV1 T V) = 4)
    (hZVW : V ⊓ centralizer (L : Set G) ≤ W) {zb : G} (hzb : zb ∈ fsuV1 T V)
    (hzbL : zb ∉ centralizer (L : Set G)) (hzbz : zb ≠ z) {Y : Subgroup G}
    (hYK : Y ≤ normalizer (K : Set G)) (hYzb : Y ≤ centralizer ({zb} : Set G)) :
    Y ≤ normalizer (W : Set G) := by
  intro y hy
  have hc : ∀ h ∈ Y, ∀ w ∈ W, h⁻¹ * w * h ∈ W := fun h hh w hw =>
    D.conj_mem_W hV1 hZVW hzb hzbL hzbz (hYK hh) (mem_centralizer_singleton_iff.1 (hYzb hh)) hw
  refine mem_normalizer_iff.2 fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · have := hc y⁻¹ (inv_mem hy) w hw
    simpa using this
  · have := hc y hy _ hw
    simpa [mul_assoc] using this

end Data13410

end CFSG.Quasithin.H13.NQS134
