module

public import CFSG.Quasithin.H13.A6S13824p
public import CFSG.Quasithin.Background.IndQuad

public section

namespace CFSG.Quasithin.H13.A6.S7C

open Equiv

section Fix

variable {M : Type*} [CommGroup M] {Φ : Perm (Fin 7) →* MulAut M} {m₀ : M}

theorem apply_dec_mul {a b : ℕ} (ha : valid a = true) (hb : valid b = true) :
    dec (cm a b) = dec a * dec b := by
  apply cd_injective
  rw [cd_mul, cd_dec ha, cd_dec hb, cd_dec]
  rw [← cd_dec ha, ← cd_dec hb, ← cd_mul]
  exact valid_cd _

theorem fix_of_cover {base p : ℕ → Bool}
    (hB : ∀ t : Perm (Fin 7), base (cd t) = true → Φ t m₀ = m₀) {W : List ℕ}
    (hW : ∀ w ∈ W, valid w = true ∧ Φ (dec w) m₀ = m₀)
    (hcov : ∀ σ : Perm (Fin 7), p (cd σ) = true →
      (W.any fun w => base (cm (cinv w) (cd σ))) = true)
    (σ : Perm (Fin 7)) (hσ : p (cd σ) = true) : Φ σ m₀ = m₀ := by
  obtain ⟨w, hw, hb⟩ := List.any_eq_true.mp (hcov σ hσ)
  obtain ⟨hv, hfix⟩ := hW w hw
  have h1 : Φ ((dec w)⁻¹ * σ) m₀ = m₀ := by
    refine hB _ ?_
    rw [cd_mul, cd_inv, cd_dec hv]
    exact hb
  calc Φ σ m₀ = Φ (dec w) (Φ ((dec w)⁻¹ * σ) m₀) := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = m₀ := by rw [h1, hfix]

noncomputable def val (Φ : Perm (Fin 7) →* MulAut M) (m₀ : M) (key : ℕ → ℕ) (k : ℕ) : M :=
  if h : ∃ σ : Perm (Fin 7), key (cd σ) = k then Φ h.choose m₀ else 1

theorem mu_eq_val {X : Subgroup (Perm (Fin 7))} (hX : ∀ t ∈ X, Φ t m₀ = m₀) {key : ℕ → ℕ}
    (hkey : ∀ σ τ : Perm (Fin 7), key (cd σ) = key (cd τ) → σ⁻¹ * τ ∈ X) (σ : Perm (Fin 7)) :
    Φ σ m₀ = val Φ m₀ key (key (cd σ)) := by
  have h : ∃ τ : Perm (Fin 7), key (cd τ) = key (cd σ) := ⟨σ, rfl⟩
  simp only [val, h, ↓reduceDIte]
  have h1 := hX _ (hkey σ _ h.choose_spec.symm)
  calc Φ σ m₀ = Φ σ (Φ (σ⁻¹ * h.choose) m₀) := by rw [h1]
    _ = Φ h.choose m₀ := by rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]

end Fix

theorem dg_enc_ofFn (f : Fin 7 → ℕ) (hf : ∀ i, f i < 8) (j : Fin 7) :
    dg (enc (List.ofFn f)) j = f j := by
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3; have h4 := hf 4
  have h5 := hf 5; have h6 := hf 6
  simp only [enc, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil]
  fin_cases j <;> simp only [dg] <;> norm_num <;> omega

theorem eq_of_enc_ofFn {f g : Fin 7 → ℕ} (hf : ∀ i, f i < 8) (hg : ∀ i, g i < 8)
    (h : enc (List.ofFn f) = enc (List.ofFn g)) (j : Fin 7) : f j = g j := by
  rw [← dg_enc_ofFn f hf, ← dg_enc_ofFn g hg, h]

@[expose] def kfD (x j : ℕ) : ℕ :=
  if j = dg x 6 then 2 else if j = dg x 4 ∨ j = dg x 5 then 1 else 0

@[expose] def keyD (x : ℕ) : ℕ := enc (List.ofFn fun j : Fin 7 => kfD x j)

@[expose] def kf4 (x j : ℕ) : ℕ :=
  if j = dg x 0 ∨ j = dg x 1 ∨ j = dg x 2 ∨ j = dg x 3 then 1 else 0

@[expose] def key4 (x : ℕ) : ℕ := enc (List.ofFn fun j : Fin 7 => kf4 x j)

@[expose] def kfC (x j : ℕ) : ℕ :=
  if j = dg x 0 then dg x 1 else if j = dg x 1 then dg x 0 else if j = dg x 2 then dg x 3 else
    if j = dg x 3 then dg x 2 else 7

@[expose] def keyC (x : ℕ) : ℕ := enc (List.ofFn fun j : Fin 7 => kfC x j)

theorem dg_lt (x i : ℕ) : dg x i < 8 := Nat.mod_lt _ (by norm_num)

theorem val_ne_of_ne {τ : Perm (Fin 7)} {i j : Fin 7} (h : i ≠ j) : (τ i).val ≠ (τ j).val :=
  fun e => h (τ.injective (Fin.ext e))

theorem inv_mul_apply_val (σ τ : Perm (Fin 7)) (i : Fin 7) (k : Fin 7)
    (h : (τ i).val = (σ k).val) : ((σ⁻¹ * τ) i) = k := by
  rw [Perm.mul_apply, show τ i = σ k from Fin.ext h]
  simp

theorem dg_cd0 (σ : Perm (Fin 7)) : dg (cd σ) 0 = (σ 0).val := dg_cd σ 0
theorem dg_cd1 (σ : Perm (Fin 7)) : dg (cd σ) 1 = (σ 1).val := dg_cd σ 1
theorem dg_cd2 (σ : Perm (Fin 7)) : dg (cd σ) 2 = (σ 2).val := dg_cd σ 2
theorem dg_cd3 (σ : Perm (Fin 7)) : dg (cd σ) 3 = (σ 3).val := dg_cd σ 3
theorem dg_cd4 (σ : Perm (Fin 7)) : dg (cd σ) 4 = (σ 4).val := dg_cd σ 4
theorem dg_cd5 (σ : Perm (Fin 7)) : dg (cd σ) 5 = (σ 5).val := dg_cd σ 5
theorem dg_cd6 (σ : Perm (Fin 7)) : dg (cd σ) 6 = (σ 6).val := dg_cd σ 6

theorem keyD_sound {σ τ : Perm (Fin 7)} (h : keyD (cd σ) = keyD (cd τ)) : σ⁻¹ * τ ∈ D7 := by
  have hf := eq_of_enc_ofFn (fun j => by unfold kfD; split_ifs <;> omega)
    (fun j => by unfold kfD; split_ifs <;> omega) h
  have key : ∀ i : Fin 7, kfD (cd σ) (τ i) = kfD (cd τ) (τ i) := fun i => hf (τ i)
  simp only [kfD, dg_cd4, dg_cd5, dg_cd6] at key
  set ρ := σ⁻¹ * τ with hρ
  have e : ∀ i, σ (ρ i) = τ i := fun i => by rw [hρ, Perm.mul_apply]; simp
  have hlt : ∀ i : Fin 7, i.val < 4 → (ρ i).val < 4 := by
    intro i hi
    have k := key i
    have n6 := val_ne_of_ne (τ := τ) (show i ≠ 6 by intro e; rw [e] at hi; simp at hi)
    have n4 := val_ne_of_ne (τ := τ) (show i ≠ 4 by intro e; rw [e] at hi; simp at hi)
    have n5 := val_ne_of_ne (τ := τ) (show i ≠ 5 by intro e; rw [e] at hi; simp at hi)
    have m : (τ i).val ≠ (σ 6).val ∧ (τ i).val ≠ (σ 4).val ∧ (τ i).val ≠ (σ 5).val := by
      split_ifs at k <;> omega
    have h4 : (ρ i).val ≠ 4 := fun e4 => m.2.1 (by rw [← e i, show ρ i = 4 from Fin.ext e4])
    have h5 : (ρ i).val ≠ 5 := fun e5 => m.2.2 (by rw [← e i, show ρ i = 5 from Fin.ext e5])
    have h6 : (ρ i).val ≠ 6 := fun e6 => m.1 (by rw [← e i, show ρ i = 6 from Fin.ext e6])
    have := (ρ i).isLt
    omega
  have h6 : ρ 6 = 6 := by
    have k := key 6
    refine inv_mul_apply_val σ τ 6 6 ?_
    split_ifs at k <;> omega
  rw [mem_D7_iff]
  simp only [inD, Df, S4f, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, dg_cd]
  exact ⟨⟨⟨⟨hlt 0 (by norm_num), hlt 1 (by norm_num)⟩, hlt 2 (by norm_num)⟩,
    hlt 3 (by norm_num)⟩, by rw [h6]; rfl⟩

theorem key4_sound {σ τ : Perm (Fin 7)} (h : key4 (cd σ) = key4 (cd τ)) : σ⁻¹ * τ ∈ S43 := by
  have hf := eq_of_enc_ofFn (fun j => by unfold kf4; split_ifs <;> omega)
    (fun j => by unfold kf4; split_ifs <;> omega) h
  have key : ∀ i : Fin 7, kf4 (cd σ) (τ i) = kf4 (cd τ) (τ i) := fun i => hf (τ i)
  simp only [kf4, dg_cd0, dg_cd1, dg_cd2, dg_cd3] at key
  set ρ := σ⁻¹ * τ with hρ
  have e : ∀ i, σ (ρ i) = τ i := fun i => by rw [hρ, Perm.mul_apply]; simp
  have hlt : ∀ i : Fin 7, i.val < 4 → (ρ i).val < 4 := by
    intro i hi
    have k := key i
    have hin : (τ i).val = (τ 0).val ∨ (τ i).val = (τ 1).val ∨ (τ i).val = (τ 2).val ∨
        (τ i).val = (τ 3).val := by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp
    rw [ite_eq_left hin] at k
    have m : (τ i).val = (σ 0).val ∨ (τ i).val = (σ 1).val ∨ (τ i).val = (σ 2).val ∨
        (τ i).val = (σ 3).val := by
      by_contra hn
      rw [ite_eq_right hn] at k
      exact absurd k (by norm_num)
    rcases m with m | m | m | m <;> rw [inv_mul_apply_val σ τ i _ m] <;> norm_num
  rw [mem_S43_iff]
  simp only [inS4, S4f, Bool.and_eq_true, decide_eq_true_eq, dg_cd]
  exact ⟨⟨⟨hlt 0 (by norm_num), hlt 1 (by norm_num)⟩, hlt 2 (by norm_num)⟩, hlt 3 (by norm_num)⟩

theorem keyC_sound {σ τ : Perm (Fin 7)} (h : keyC (cd σ) = keyC (cd τ)) : σ⁻¹ * τ ∈ C7 := by
  have hb : ∀ x j, kfC x j < 8 := fun x j => by
    unfold kfC; split_ifs <;> first | omega | exact dg_lt _ _
  have hf := eq_of_enc_ofFn (fun j => hb _ _) (fun j => hb _ _) h
  have key : ∀ i : Fin 7, kfC (cd σ) (τ i) = kfC (cd τ) (τ i) := fun i => hf (τ i)
  simp only [kfC, dg_cd0, dg_cd1, dg_cd2, dg_cd3] at key
  set ρ := σ⁻¹ * τ with hρ
  have n01 := val_ne_of_ne (τ := τ) (show (0 : Fin 7) ≠ 1 by decide)
  have n02 := val_ne_of_ne (τ := τ) (show (0 : Fin 7) ≠ 2 by decide)
  have n03 := val_ne_of_ne (τ := τ) (show (0 : Fin 7) ≠ 3 by decide)
  have n12 := val_ne_of_ne (τ := τ) (show (1 : Fin 7) ≠ 2 by decide)
  have n13 := val_ne_of_ne (τ := τ) (show (1 : Fin 7) ≠ 3 by decide)
  have n23 := val_ne_of_ne (τ := τ) (show (2 : Fin 7) ≠ 3 by decide)
  have k0 := key 0
  have k2 := key 2
  rw [ite_eq_left rfl] at k0
  rw [ite_eq_right (Ne.symm n02), ite_eq_right (Ne.symm n12), ite_eq_left rfl] at k2
  have hpair : ∀ a b : Fin 7, (if (τ a).val = (σ 0).val then (σ 1).val else
      if (τ a).val = (σ 1).val then (σ 0).val else if (τ a).val = (σ 2).val then (σ 3).val else
      if (τ a).val = (σ 3).val then (σ 2).val else 7) = (τ b).val →
      (ρ a).val < 4 ∧ (ρ b).val < 4 ∧ (ρ a).val / 2 = (ρ b).val / 2 := by
    intro a b hab
    have hτb := (τ b).isLt
    split_ifs at hab with c0 c1 c2 c3
    · rw [inv_mul_apply_val σ τ a 0 c0, inv_mul_apply_val σ τ b 1 hab.symm]; norm_num
    · rw [inv_mul_apply_val σ τ a 1 c1, inv_mul_apply_val σ τ b 0 hab.symm]; norm_num
    · rw [inv_mul_apply_val σ τ a 2 c2, inv_mul_apply_val σ τ b 3 hab.symm]; norm_num
    · rw [inv_mul_apply_val σ τ a 3 c3, inv_mul_apply_val σ τ b 2 hab.symm]; norm_num
    · omega
  obtain ⟨h0, h1, h01⟩ := hpair 0 1 k0
  obtain ⟨h2, h3, -⟩ := hpair 2 3 k2
  rw [mem_C7_iff]
  simp only [inC, Cf, S4f, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, dg_cd]
  exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h01⟩

@[expose] def tog (s : List ℕ) (k : ℕ) : List ℕ := if k ∈ s then s.erase k else k :: s

@[expose] def xorL (L : List (List ℕ)) : List ℕ :=
  L.foldr (fun r s => r.foldr (fun k s => tog s k) s) []

section Xor

variable {M : Type*} [CommGroup M] (hsq : ∀ x : M, x * x = 1)
include hsq

theorem prod_tog (v : ℕ → M) (s : List ℕ) (k : ℕ) :
    ((tog s k).map v).prod = v k * (s.map v).prod := by
  unfold tog
  split_ifs with h
  · have hp := (List.perm_cons_erase h).map v
    rw [hp.prod_eq, List.map_cons, List.prod_cons, ← mul_assoc, hsq, one_mul]
  · rw [List.map_cons, List.prod_cons]

theorem prod_foldr_tog (v : ℕ → M) (r s : List ℕ) :
    ((r.foldr (fun k s => tog s k) s).map v).prod = (r.map v).prod * (s.map v).prod := by
  induction r with
  | nil => simp
  | cons a r ih =>
    rw [List.foldr_cons, prod_tog hsq, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem prod_xorL (v : ℕ → M) (L : List (List ℕ)) (h : ∀ r ∈ L, (r.map v).prod = 1) :
    ((xorL L).map v).prod = 1 := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    rw [xorL, List.foldr_cons, ← xorL, prod_foldr_tog hsq, h r List.mem_cons_self,
      ih fun r' hr' => h r' (List.mem_cons_of_mem r hr'), one_mul]

end Xor

@[expose] def lamKeys (key : ℕ → ℕ) (r1 r2 n : ℕ) : List ℕ := [key n, key (cm n r1), key (cm n r2)]

@[expose] def conjC (k e : ℕ) : ℕ := cm (cm k e) (cinv k)

@[expose] def quadKeys (key : ℕ → ℕ) (e1 e2 k n : ℕ) : List ℕ :=
  [key n, key (cm (conjC k e1) n), key (cm (conjC k e2) n),
    key (cm (cm (conjC k e1) (conjC k e2)) n)]

@[expose] def entryKeys (key : ℕ → ℕ) (r1 r2 e1 e2 : ℕ) (e : ℕ × ℕ × ℕ) : List ℕ :=
  if e.1 = 0 then lamKeys key r1 r2 e.2.2 else quadKeys key e1 e2 e.2.1 e.2.2

section Rel

variable {M : Type*} [CommGroup M] {Φ : Perm (Fin 7) →* MulAut M} {m₀ : M}

theorem lam_inst {key : ℕ → ℕ} {v : ℕ → M} (hμ : ∀ σ, Φ σ m₀ = v (key (cd σ))) {r1 r2 : ℕ}
    (hv1 : valid r1 = true) (hv2 : valid r2 = true)
    (hrel : m₀ * Φ (dec r1) m₀ * Φ (dec r2) m₀ = 1) {n : ℕ} (hn : valid n = true) :
    ((lamKeys key r1 r2 n).map v).prod = 1 := by
  have hw : ∀ σ : Perm (Fin 7), Φ (dec n) (Φ σ m₀) = v (key (cm n (cd σ))) := fun σ => by
    rw [← MulAut.mul_apply, ← map_mul, hμ, cd_mul, cd_dec hn]
  have h := congrArg (Φ (dec n)) hrel
  rw [map_one, map_mul, map_mul, hw, hw, cd_dec hv1, cd_dec hv2, hμ, cd_dec hn] at h
  simp only [lamKeys, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc]
  exact h

theorem quad_inst (hsq : ∀ x : M, x * x = 1) {key : ℕ → ℕ} {v : ℕ → M}
    (hμ : ∀ σ, Φ σ m₀ = v (key (cd σ))) {E : Set (Perm (Fin 7))} (hq : IndQuad.QuadOn Φ E)
    {e1 e2 : ℕ} (he1 : dec e1 ∈ E) (he2 : dec e2 ∈ E) (hv1 : valid e1 = true)
    (hv2 : valid e2 = true) {k n : ℕ} (hk : valid k = true) (hn : valid n = true) :
    ((quadKeys key e1 e2 k n).map v).prod = 1 := by
  have hinv : ∀ x : M, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  set y := dec k * dec e1 * (dec k)⁻¹ with hy
  set y' := dec k * dec e2 * (dec k)⁻¹ with hy'
  set w := Φ (dec n) m₀ with hwdef
  have hw : ∀ σ : Perm (Fin 7), Φ σ w = v (key (cm (cd σ) n)) := fun σ => by
    rw [hwdef, ← MulAut.mul_apply, ← map_mul, hμ, cd_mul, cd_dec hn]
  have hcy : cd y = conjC k e1 := by
    rw [hy, cd_mul, cd_mul, cd_inv, cd_dec hk, cd_dec hv1]
    rfl
  have hcy' : cd y' = conjC k e2 := by
    rw [hy', cd_mul, cd_mul, cd_inv, cd_dec hk, cd_dec hv2]
    rfl
  have h := hq (dec k) (dec e1) he1 (dec e2) he2 w
  rw [← hy, ← hy', map_mul, map_inv, ← MulAut.mul_apply, ← map_mul, hw, hw, hw, cd_mul, hcy,
    hcy', hinv, hinv] at h
  have hw0 : w = v (key n) := by rw [hwdef, hμ, cd_dec hn]
  rw [hw0] at h
  simp only [quadKeys, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  calc v (key n) * (v (key (cm (conjC k e1) n)) * (v (key (cm (conjC k e2) n)) *
        v (key (cm (cm (conjC k e1) (conjC k e2)) n))))
      = (v (key (cm (cm (conjC k e1) (conjC k e2)) n)) * v (key (cm (conjC k e1) n))) *
          (v (key (cm (conjC k e2) n)) * v (key n)) := by ac_rfl
    _ = 1 := by rw [h, hsq]

theorem cert_sound (hsq : ∀ x : M, x * x = 1) {key : ℕ → ℕ} {v : ℕ → M}
    (hμ : ∀ σ, Φ σ m₀ = v (key (cd σ))) {r1 r2 : ℕ} (hr1 : valid r1 = true)
    (hr2 : valid r2 = true) (hrel : m₀ * Φ (dec r1) m₀ * Φ (dec r2) m₀ = 1)
    {E : Set (Perm (Fin 7))} (hq : IndQuad.QuadOn Φ E) {e1 e2 : ℕ} (he1 : dec e1 ∈ E)
    (he2 : dec e2 ∈ E) (hv1 : valid e1 = true) (hv2 : valid e2 = true)
    (cert : List (ℕ × ℕ × ℕ)) (hcert : (cert.all fun e => valid e.2.1 && valid e.2.2) = true) :
    ((xorL (cert.map (entryKeys key r1 r2 e1 e2))).map v).prod = 1 := by
  refine prod_xorL hsq v _ fun r hr => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  have hv := List.all_eq_true.mp hcert e he
  simp only [Bool.and_eq_true] at hv
  unfold entryKeys
  split_ifs
  · exact lam_inst hμ hr1 hr2 hrel hv.2
  · exact quad_inst hsq hμ hq he1 he2 hv1 hv2 hv.1 hv.2

end Rel

@[expose] def bfsK (key : ℕ → ℕ) (r1 r2 : ℕ) : List ℕ → List (ℕ × ℕ) → Option (List ℕ)
  | K, [] => some K
  | K, (n, i) :: rest =>
    let ks := lamKeys key r1 r2 n
    if valid n && ((List.range 3).all fun j => j == i || K.contains (ks.getD j 0)) && i < 3 then
      bfsK key r1 r2 (ks.getD i 0 :: K) rest
    else none

section Bfs

variable {M : Type*} [CommGroup M] {Φ : Perm (Fin 7) →* MulAut M} {m₀ : M}

theorem eq_mul_of_prod (hsq : ∀ x : M, x * x = 1) {x y z : M} (h : x * (y * z) = 1) :
    x = y * z ∧ y = x * z ∧ z = x * y := by
  have h1 : x = y * z := by
    calc x = x * (y * z) * (y * z) := by rw [mul_assoc, hsq, mul_one]
      _ = y * z := by rw [h, one_mul]
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, mul_assoc, hsq, mul_one]
  · rw [h1, mul_comm y z, mul_assoc, hsq, mul_one]

theorem bfs_sound (hsq : ∀ x : M, x * x = 1) {key : ℕ → ℕ} {v : ℕ → M} {r1 r2 : ℕ}
    (hlam : ∀ n, valid n = true → ((lamKeys key r1 r2 n).map v).prod = 1) {B : Subgroup M} :
    ∀ (steps : List (ℕ × ℕ)) (K K' : List ℕ), bfsK key r1 r2 K steps = some K' →
      (∀ k ∈ K, v k ∈ B) → ∀ k ∈ K', v k ∈ B
  | [], K, K', h, hK => by
    simp only [bfsK, Option.some.injEq] at h
    subst h
    exact hK
  | (n, i) :: rest, K, K', h, hK => by
    simp only [bfsK] at h
    split_ifs at h with hc
    refine bfs_sound hsq hlam rest _ K' h fun k hk => ?_
    rcases List.mem_cons.mp hk with rfl | hk
    · simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
        beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at hc
      obtain ⟨⟨hv, hK3⟩, hi⟩ := hc
      have hp := hlam n hv
      simp only [lamKeys, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one] at hp
      obtain ⟨e0, e1, e2⟩ := eq_mul_of_prod hsq hp
      have hm : ∀ j < 3, j ≠ i → v ((lamKeys key r1 r2 n).getD j 0) ∈ B := fun j hj hji =>
        hK _ ((hK3 j hj).resolve_left hji)
      interval_cases i
      · show v (key n) ∈ B
        rw [e0]
        exact B.mul_mem (hm 1 (by norm_num) (by norm_num)) (hm 2 (by norm_num) (by norm_num))
      · show v (key (cm n r1)) ∈ B
        rw [e1]
        exact B.mul_mem (hm 0 (by norm_num) (by norm_num)) (hm 2 (by norm_num) (by norm_num))
      · show v (key (cm n r2)) ∈ B
        rw [e2]
        exact B.mul_mem (hm 0 (by norm_num) (by norm_num)) (hm 1 (by norm_num) (by norm_num))
    · exact hK k hk

theorem card_closure_le (hsq : ∀ x : M, x * x = 1) {n : ℕ} (b : Fin n → M) :
    Nat.card (Subgroup.closure (Set.range b)) ≤ 2 ^ n := by
  classical
  let φ : (Fin n → Bool) → M := fun f => ∏ i, if f i then b i else 1
  have hφmul : ∀ f g, φ f * φ g = φ (fun i => xor (f i) (g i)) := by
    intro f g
    simp only [φ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hf : f i <;> by_cases hg : g i <;> simp [hf, hg, hsq]
  let S : Subgroup M :=
    { carrier := Set.range φ
      mul_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨_, (hφmul f g).symm⟩
      one_mem' := ⟨fun _ => false, by simp [φ]⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        exact ⟨f, (inv_eq_of_mul_eq_one_right (hsq _)).symm⟩ }
  have hle : Subgroup.closure (Set.range b) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨fun j => decide (j = i), ?_⟩
    simp [φ]
  have : Finite S := Finite.of_surjective (fun f => (⟨φ f, f, rfl⟩ : S))
    (by rintro ⟨_, f, rfl⟩; exact ⟨f, rfl⟩)
  calc Nat.card (Subgroup.closure (Set.range b)) ≤ Nat.card S := Subgroup.card_le_of_le hle
    _ = Nat.card (Set.range φ) := rfl
    _ ≤ Nat.card (Fin n → Bool) := Finite.card_range_le φ
    _ = 2 ^ n := by simp

end Bfs

@[expose] def q1c : ℕ := 1607340
@[expose] def q2c : ℕ := 1682184
@[expose] def c456 : ℕ := 1267336
@[expose] def c465 : ℕ := 1468040

@[expose] def v1c : ℕ := 1754305
@[expose] def v2c : ℕ := 1753626
@[expose] def c012 : ℕ := 1754641
@[expose] def c021 : ℕ := 1754690

@[expose] def t1c : ℕ := 1754753
@[expose] def t2c : ℕ := 1753626
@[expose] def t3c : ℕ := 1726088

@[expose] def ctct (c t i : ℕ) : ℕ := dg c (dg t (dg c (dg t i)))

@[expose] def cubeConds (c : ℕ) : Bool :=
  (T0f fun i => dg c (dg c (dg c i))) && [t1c, t2c, t3c].all fun t =>
    (T0f fun i => ctct c t (ctct c t (ctct c t i))) &&
      T0f fun i => dg c (ctct c t (dg c (ctct c t (dg c (ctct c t i)))))

theorem shape_all (σ : Perm (Fin 7)) : (!cubeConds (cd σ) || inS4 (cd σ) || inPA (cd σ)) = true :=
  forall_cd (P := fun x => !cubeConds x || inS4 x || inPA x) (by decide +kernel) σ

@[expose] def cosetsOK (x : ℕ) : Bool :=
  (!inPA x || inT0 x || (T0f fun i => pos q1c (dg x i)) || T0f fun i => pos q2c (dg x i)) &&
    (!inS4 x || inC x || (Cf fun i => pos c012 (dg x i)) || Cf fun i => pos c021 (dg x i)) &&
    (!inS4 x || inD x || (Df fun i => pos c456 (dg x i)) || Df fun i => pos c465 (dg x i))

theorem cosetsOK_all (σ : Perm (Fin 7)) : cosetsOK (cd σ) = true :=
  forall_cd (P := cosetsOK) (by decide +kernel) σ

@[expose] def coreA (c : ℕ) : Bool :=
  !inPA c || inT0 c || T0L.all fun x => !(T0f fun i => dg c (dg x (pos c i))) ||
    !(T0f fun i => pos c (dg x (dg c i))) || inE8 x

theorem coreA_ok : PAL.all coreA = true := by decide +kernel

@[expose] def tnormC (c : ℕ) : Bool :=
  [t1c, t2c, t3c].all fun t => (T0f fun i => dg c (ctct c t i)) || T0f fun i => ctct c t i

@[expose] def L18 : List ℕ :=
  [1267336, 1468040, 1579354, 1579795, 1608019, 1608474, 1650796, 1651237, 1679461,
    1679916, 1753241, 1753290, 1753731, 1753808, 1754123, 1754200, 1754641, 1754690]

@[expose] def ord3 (x : ℕ) : Bool := (List.range 7).all fun i => dg x (dg x (dg x i)) == i

theorem L18_complete (σ : Perm (Fin 7)) :
    (!ord3 (cd σ) || cd σ == idc || !tnormC (cd σ) || L18.contains (cd σ)) = true :=
  forall_cd (P := fun x => !ord3 x || x == idc || !tnormC x || L18.contains x)
    (by decide +kernel) σ

@[expose] def hatConds (c0 c1 : ℕ) : Bool :=
  (T0f fun i => dg c0 (dg c1 (pos c0 (pos c1 i)))) && !inT0 c1 && !(T0f fun i => dg c0 (dg c1 i)) &&
    !(T0f fun i => dg c0 (dg c0 (dg c1 i))) &&
    (T0f fun i => dg c0 (dg c1 (dg c0 (dg c1 (dg c0 (dg c1 i)))))) &&
    (T0f fun i => dg c0 (dg c1 (dg c1 (dg c0 (dg c1 (dg c1 (dg c0 (dg c1 (dg c1 i))))))))) &&
    cubeConds c1

@[expose] def hatOK (c0 c1 : ℕ) : Bool :=
  !hatConds c0 c1 || ((inC c0 || inD c0) && T0L.all fun x =>
    !((T0f fun i => dg c0 (dg x (pos c0 i))) && (T0f fun i => pos c0 (dg x (dg c0 i))) &&
      (T0f fun i => dg c1 (dg x (pos c1 i))) && (T0f fun i => pos c1 (dg x (dg c1 i)))) ||
      inV4 x)

theorem hat_ok : (L18.all fun c0 => S43L.all fun c1 => hatOK c0 c1) = true := by decide +kernel

@[expose] def covCD (c0 : ℕ) : Bool :=
  (!inC c0 || CL.all fun g => inT0 g || (T0f fun i => pos c0 (dg g i)) ||
    T0f fun i => pos c0 (pos c0 (dg g i))) &&
  (!inD c0 || DL.all fun g => inT0 g || (T0f fun i => pos c0 (dg g i)) ||
    T0f fun i => pos c0 (pos c0 (dg g i)))

theorem covCD_ok : L18.all covCD = true := by decide +kernel

theorem T0f_cd_iff {σ : Perm (Fin 7)} : (T0f fun i => dg (cd σ) i) = true ↔ σ ∈ T0 :=
  mem_T0_iff.symm

theorem valid_of_mem_gens {t : ℕ} (ht : t ∈ [t1c, t2c, t3c]) : valid t = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> decide

theorem cubeConds_of {c : Perm (Fin 7)} (h0 : c ^ 3 ∈ T0)
    (ht : ∀ t ∈ [t1c, t2c, t3c], (c * (dec t * c * dec t)) ^ 3 ∈ T0 ∧
      (c * c * (dec t * c * dec t)) ^ 3 ∈ T0) : cubeConds (cd c) = true := by
  unfold cubeConds
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, fun t htm => ?_⟩
  · rw [pow_three] at h0
    have e : (T0f fun i => dg (cd c) (dg (cd c) (dg (cd c) i))) = inT0 (cd (c * (c * c))) := by
      unfold inT0
      congr 1
      funext i
      simp only [dg_cd, Perm.mul_apply]
    rw [e]
    exact mem_T0_iff.mp h0
  · obtain ⟨h1, h2⟩ := ht t htm
    obtain ⟨τ, rfl⟩ : ∃ τ : Perm (Fin 7), cd τ = t := ⟨dec t, cd_dec (valid_of_mem_gens htm)⟩
    rw [dec_cd τ (valid_cd τ), pow_three] at h1 h2
    rw [Bool.and_eq_true]
    constructor
    · have e : (T0f fun i => ctct (cd c) (cd τ) (ctct (cd c) (cd τ) (ctct (cd c) (cd τ) i))) =
          inT0 (cd (c * (τ * c * τ) * (c * (τ * c * τ) * (c * (τ * c * τ))))) := by
        unfold inT0
        congr 1
        funext i
        simp only [ctct, dg_cd, Perm.mul_apply]
      rw [e]
      exact mem_T0_iff.mp h1
    · have e : (T0f fun i => dg (cd c) (ctct (cd c) (cd τ) (dg (cd c) (ctct (cd c) (cd τ)
          (dg (cd c) (ctct (cd c) (cd τ) i)))))) =
          inT0 (cd (c * c * (τ * c * τ) * (c * c * (τ * c * τ) * (c * c * (τ * c * τ))))) := by
        unfold inT0
        congr 1
        funext i
        simp only [ctct, dg_cd, Perm.mul_apply]
      rw [e]
      exact mem_T0_iff.mp h2

theorem shape {c : Perm (Fin 7)} (h : cubeConds (cd c) = true) : c ∈ S43 ∨ c ∈ PA := by
  have h1 := shape_all c
  rw [h] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact Or.inl (mem_S43_iff.mpr h1)
  · exact Or.inr (mem_PA_iff.mpr h1)

theorem inv_mul_mem_T0 {q g : Perm (Fin 7)} (h : (T0f fun i => pos (cd q) (dg (cd g) i)) = true) :
    q⁻¹ * g ∈ T0 := by
  rw [← T0f_cd_iff, ← h]
  congr 1
  funext i
  simp only [dg_cd, pos_cd, Perm.mul_apply]

theorem inv_mul_mem_C7 {q g : Perm (Fin 7)} (h : (Cf fun i => pos (cd q) (dg (cd g) i)) = true) :
    q⁻¹ * g ∈ C7 := by
  rw [mem_C7_iff, inC, ← h]
  congr 1
  funext i
  simp only [dg_cd, pos_cd, Perm.mul_apply]

theorem inv_mul_mem_D7 {q g : Perm (Fin 7)} (h : (Df fun i => pos (cd q) (dg (cd g) i)) = true) :
    q⁻¹ * g ∈ D7 := by
  rw [mem_D7_iff, inD, ← h]
  congr 1
  funext i
  simp only [dg_cd, pos_cd, Perm.mul_apply]

theorem cosets_PA {g : Perm (Fin 7)} (hg : g ∈ PA) :
    g ∈ T0 ∨ (dec q1c)⁻¹ * g ∈ T0 ∨ (dec q2c)⁻¹ * g ∈ T0 := by
  have h := cosetsOK_all g
  simp only [cosetsOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h.1.1 with ((h | h) | h) | h
  · exact absurd (mem_PA_iff.mp hg) (by rw [h]; simp)
  · exact Or.inl (mem_T0_iff.mpr h)
  · exact Or.inr (Or.inl (inv_mul_mem_T0 (by rw [cd_dec (by decide)]; exact h)))
  · exact Or.inr (Or.inr (inv_mul_mem_T0 (by rw [cd_dec (by decide)]; exact h)))

theorem cosets_S43_C {g : Perm (Fin 7)} (hg : g ∈ S43) :
    g ∈ C7 ∨ (dec c012)⁻¹ * g ∈ C7 ∨ (dec c021)⁻¹ * g ∈ C7 := by
  have h := cosetsOK_all g
  simp only [cosetsOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h.1.2 with ((h | h) | h) | h
  · exact absurd (mem_S43_iff.mp hg) (by rw [h]; simp)
  · exact Or.inl (mem_C7_iff.mpr h)
  · exact Or.inr (Or.inl (inv_mul_mem_C7 (by rw [cd_dec (by decide)]; exact h)))
  · exact Or.inr (Or.inr (inv_mul_mem_C7 (by rw [cd_dec (by decide)]; exact h)))

theorem cosets_S43_D {g : Perm (Fin 7)} (hg : g ∈ S43) :
    g ∈ D7 ∨ (dec c456)⁻¹ * g ∈ D7 ∨ (dec c465)⁻¹ * g ∈ D7 := by
  have h := cosetsOK_all g
  simp only [cosetsOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h.2 with ((h | h) | h) | h
  · exact absurd (mem_S43_iff.mp hg) (by rw [h]; simp)
  · exact Or.inl (mem_D7_iff.mpr h)
  · exact Or.inr (Or.inl (inv_mul_mem_D7 (by rw [cd_dec (by decide)]; exact h)))
  · exact Or.inr (Or.inr (inv_mul_mem_D7 (by rw [cd_dec (by decide)]; exact h)))

theorem conj_mem_T0_iff {c x : Perm (Fin 7)} :
    c * x * c⁻¹ ∈ T0 ↔ (T0f fun i => dg (cd c) (dg (cd x) (pos (cd c) i))) = true := by
  rw [← T0f_cd_iff]
  constructor <;> intro h <;> rw [← h] <;> congr 1 <;> funext i <;>
    simp only [dg_cd, pos_cd, Perm.mul_apply]

theorem conj_inv_mem_T0_iff {c x : Perm (Fin 7)} :
    c⁻¹ * x * c ∈ T0 ↔ (T0f fun i => pos (cd c) (dg (cd x) (dg (cd c) i))) = true := by
  rw [← T0f_cd_iff]
  constructor <;> intro h <;> rw [← h] <;> congr 1 <;> funext i <;>
    simp only [dg_cd, pos_cd, Perm.mul_apply]

theorem mem_list_of {σ : Perm (Fin 7)} :
    (inT0 (cd σ) = true → cd σ ∈ T0L) ∧ (inPA (cd σ) = true → cd σ ∈ PAL) ∧
      (inS4 (cd σ) = true → cd σ ∈ S43L) ∧ (inD (cd σ) = true → cd σ ∈ DL) ∧
      (inC (cd σ) = true → cd σ ∈ CL) := by
  have h := listsOK_all σ
  simp only [listsOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at h
  refine ⟨fun hx => h.1.1.1.1.1.1.resolve_left (by rw [hx]; simp),
    fun hx => h.1.1.1.1.1.2.resolve_left (by rw [hx]; simp),
    fun hx => h.1.1.1.1.2.resolve_left (by rw [hx]; simp),
    fun hx => h.1.1.1.2.resolve_left (by rw [hx]; simp),
    fun hx => h.1.1.2.resolve_left (by rw [hx]; simp)⟩

theorem mem_E8_of_core {c x : Perm (Fin 7)} (hc : c ∈ PA) (hc' : c ∉ T0) (hx : x ∈ T0)
    (h1 : c * x * c⁻¹ ∈ T0) (h2 : c⁻¹ * x * c ∈ T0) : x ∈ E8 := by
  have hcL := mem_list_of.2.1 (mem_PA_iff.mp hc)
  have hxL := mem_list_of.1 (mem_T0_iff.mp hx)
  have h := List.all_eq_true.mp coreA_ok _ hcL
  simp only [coreA, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  rcases h with (h | h) | h
  · exact absurd (mem_PA_iff.mp hc) (by rw [h]; simp)
  · exact absurd (mem_T0_iff.mpr h) hc'
  · have h3 := h _ hxL
    rw [conj_mem_T0_iff.mp h1, conj_inv_mem_T0_iff.mp h2] at h3
    simp only [Bool.true_eq_false, or_self, false_or] at h3
    exact mem_E8_iff.mpr h3

theorem mem_L18 {c : Perm (Fin 7)} (h3 : c ^ 3 = 1) (h1 : c ≠ 1)
    (ht : ∀ t ∈ [t1c, t2c, t3c], c * c * (dec t * c * dec t) ∈ T0 ∨
      c * (dec t * c * dec t) ∈ T0) : cd c ∈ L18 := by
  have h := L18_complete c
  have ho : ord3 (cd c) = true := by
    simp only [ord3, List.all_eq_true, List.mem_range, beq_iff_eq]
    intro i hi
    have e : dg (cd c) (dg (cd c) (dg (cd c) i)) = ((c ^ 3) ⟨i, hi⟩).val := by
      have := dg_cd c ⟨i, hi⟩
      simp only at this
      rw [this, dg_cd, dg_cd, pow_succ, pow_succ, pow_one, Perm.mul_apply, Perm.mul_apply]
    rw [e, h3]
    rfl
  have hc1 : cd c ≠ idc := fun e => h1 (cd_injective (e.trans cd_one.symm))
  have htn : tnormC (cd c) = true := by
    unfold tnormC
    rw [List.all_eq_true]
    intro t htm
    have h' := ht t htm
    obtain ⟨τ, rfl⟩ : ∃ τ : Perm (Fin 7), cd τ = t := ⟨dec t, cd_dec (valid_of_mem_gens htm)⟩
    rw [dec_cd τ (valid_cd τ)] at h'
    have e1 : (T0f fun i => dg (cd c) (ctct (cd c) (cd τ) i)) =
        inT0 (cd (c * c * (τ * c * τ))) := by
      unfold inT0
      congr 1
      funext i
      simp only [ctct, dg_cd, Perm.mul_apply]
    have e2 : (T0f fun i => ctct (cd c) (cd τ) i) = inT0 (cd (c * (τ * c * τ))) := by
      unfold inT0
      congr 1
      funext i
      simp only [ctct, dg_cd, Perm.mul_apply]
    rw [Bool.or_eq_true, e1, e2]
    exact h'.imp mem_T0_iff.mp mem_T0_iff.mp
  rw [ho, htn] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, hc1, false_or,
    List.contains_iff_mem, Bool.false_eq_true] at h
  exact h

theorem hat_shape {c0 c1 : Perm (Fin 7)} (hL : cd c0 ∈ L18) (hc1 : c1 ∈ S43)
    (hcube1 : cubeConds (cd c1) = true) (hcomm : c0 * c1 * c0⁻¹ * c1⁻¹ ∈ T0) (h1 : c1 ∉ T0)
    (h2 : c0 * c1 ∉ T0) (h3 : c0 * c0 * c1 ∉ T0) (h4 : (c0 * c1) ^ 3 ∈ T0)
    (h5 : (c0 * (c1 * c1)) ^ 3 ∈ T0) :
    (c0 ∈ C7 ∨ c0 ∈ D7) ∧ ∀ x ∈ T0, c0 * x * c0⁻¹ ∈ T0 → c0⁻¹ * x * c0 ∈ T0 →
      c1 * x * c1⁻¹ ∈ T0 → c1⁻¹ * x * c1 ∈ T0 → x ∈ V4 := by
  have hc1L := mem_list_of.2.2.1 (mem_S43_iff.mp hc1)
  have h := List.all_eq_true.mp (List.all_eq_true.mp hat_ok _ hL) _ hc1L
  have e1 : (T0f fun i => dg (cd c0) (dg (cd c1) (pos (cd c0) (pos (cd c1) i)))) =
      inT0 (cd (c0 * c1 * c0⁻¹ * c1⁻¹)) := by
    unfold inT0
    congr 1
    funext i
    simp only [dg_cd, pos_cd, Perm.mul_apply]
  have e2 : (T0f fun i => dg (cd c0) (dg (cd c1) i)) = inT0 (cd (c0 * c1)) := by
    unfold inT0
    congr 1
    funext i
    simp only [dg_cd, Perm.mul_apply]
  have e3 : (T0f fun i => dg (cd c0) (dg (cd c0) (dg (cd c1) i))) = inT0 (cd (c0 * c0 * c1)) := by
    unfold inT0
    congr 1
    funext i
    simp only [dg_cd, Perm.mul_apply]
  have e4 : (T0f fun i => dg (cd c0) (dg (cd c1) (dg (cd c0) (dg (cd c1) (dg (cd c0)
      (dg (cd c1) i)))))) = inT0 (cd ((c0 * c1) ^ 3)) := by
    unfold inT0
    congr 1
    funext i
    simp only [dg_cd, pow_succ, pow_zero, one_mul, Perm.mul_apply]
  have e5 : (T0f fun i => dg (cd c0) (dg (cd c1) (dg (cd c1) (dg (cd c0) (dg (cd c1) (dg (cd c1)
      (dg (cd c0) (dg (cd c1) (dg (cd c1) i))))))))) = inT0 (cd ((c0 * (c1 * c1)) ^ 3)) := by
    unfold inT0
    congr 1
    funext i
    simp only [dg_cd, pow_succ, pow_zero, one_mul, Perm.mul_apply]
  have hconds : hatConds (cd c0) (cd c1) = true := by
    simp only [hatConds, Bool.and_eq_true, Bool.not_eq_true', e1, e2, e3, e4, e5]
    refine ⟨⟨⟨⟨⟨⟨mem_T0_iff.mp hcomm, ?_⟩, ?_⟩, ?_⟩, mem_T0_iff.mp h4⟩, mem_T0_iff.mp h5⟩,
      hcube1⟩
    · exact Bool.eq_false_iff.mpr fun h' => h1 (mem_T0_iff.mpr h')
    · exact Bool.eq_false_iff.mpr fun h' => h2 (mem_T0_iff.mpr h')
    · exact Bool.eq_false_iff.mpr fun h' => h3 (mem_T0_iff.mpr h')
  simp only [hatOK, hconds, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    List.all_eq_true] at h
  obtain ⟨hCD, hcore⟩ := h
  refine ⟨hCD.imp mem_C7_iff.mpr mem_D7_iff.mpr, fun x hx hx1 hx2 hx3 hx4 => ?_⟩
  have hxL := mem_list_of.1 (mem_T0_iff.mp hx)
  rcases hcore _ hxL with h' | h'
  · rw [conj_mem_T0_iff.mp hx1, conj_inv_mem_T0_iff.mp hx2, conj_mem_T0_iff.mp hx3,
      conj_inv_mem_T0_iff.mp hx4] at h'
    exact absurd h' (by decide)
  · exact mem_V4_iff.mpr h'

theorem cover_C {c0 g : Perm (Fin 7)} (hL : cd c0 ∈ L18) (hc0 : c0 ∈ C7) (hg : g ∈ C7) :
    g ∈ T0 ∨ c0⁻¹ * g ∈ T0 ∨ c0⁻¹ * (c0⁻¹ * g) ∈ T0 := by
  have h := List.all_eq_true.mp covCD_ok _ hL
  simp only [covCD, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_true] at h
  rcases h.1 with h | h
  · exact absurd (mem_C7_iff.mp hc0) (by rw [h]; simp)
  rcases h _ (mem_list_of.2.2.2.2 (mem_C7_iff.mp hg)) with (h | h) | h
  · exact Or.inl (mem_T0_iff.mpr h)
  · exact Or.inr (Or.inl (inv_mul_mem_T0 h))
  · refine Or.inr (Or.inr ?_)
    rw [← T0f_cd_iff, ← h]
    congr 1
    funext i
    simp only [dg_cd, pos_cd, Perm.mul_apply]

theorem cover_D {c0 g : Perm (Fin 7)} (hL : cd c0 ∈ L18) (hc0 : c0 ∈ D7) (hg : g ∈ D7) :
    g ∈ T0 ∨ c0⁻¹ * g ∈ T0 ∨ c0⁻¹ * (c0⁻¹ * g) ∈ T0 := by
  have h := List.all_eq_true.mp covCD_ok _ hL
  simp only [covCD, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_true] at h
  rcases h.2 with h | h
  · exact absurd (mem_D7_iff.mp hc0) (by rw [h]; simp)
  rcases h _ (mem_list_of.2.2.2.1 (mem_D7_iff.mp hg)) with (h | h) | h
  · exact Or.inl (mem_T0_iff.mpr h)
  · exact Or.inr (Or.inl (inv_mul_mem_T0 h))
  · refine Or.inr (Or.inr ?_)
    rw [← T0f_cd_iff, ← h]
    congr 1
    funext i
    simp only [dg_cd, pos_cd, Perm.mul_apply]

section Rel

variable {M : Type*} [CommGroup M] {Φ : Perm (Fin 7) →* MulAut M} {m₀ : M}

theorem rel_of_cos (hsq : ∀ x : M, x * x = 1) {X : Subgroup (Perm (Fin 7))}
    (hX : ∀ t ∈ X, Φ t m₀ = m₀) {r1 r2 c : Perm (Fin 7)}
    (hc : c ∈ X ∨ r1⁻¹ * c ∈ X ∨ r2⁻¹ * c ∈ X)
    (hcc : c * c ∈ X ∨ r1⁻¹ * (c * c) ∈ X ∨ r2⁻¹ * (c * c) ∈ X) (h1 : Φ c m₀ ≠ m₀)
    (h2 : Φ (c * c) m₀ ≠ m₀) (h12 : Φ c m₀ ≠ Φ (c * c) m₀)
    (hrel : m₀ * Φ c m₀ = Φ (c * c) m₀) :
    m₀ * Φ r1 m₀ * Φ r2 m₀ = 1 ∧ Φ r1 m₀ ≠ m₀ := by
  have hmu : ∀ {r g : Perm (Fin 7)}, r⁻¹ * g ∈ X → Φ g m₀ = Φ r m₀ := fun {r g} h => by
    calc Φ g m₀ = Φ r (Φ (r⁻¹ * g) m₀) := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = Φ r m₀ := by rw [hX _ h]
  have h3 : m₀ * Φ c m₀ * Φ (c * c) m₀ = 1 := by rw [hrel, hsq]
  rcases hc with ha | ha | ha
  · exact absurd (hX _ ha) h1
  · rw [hmu ha] at h1 h12 h3
    rcases hcc with hb | hb | hb
    · exact absurd (hX _ hb) h2
    · exact absurd (hmu hb).symm h12
    · rw [hmu hb] at h3
      exact ⟨h3, h1⟩
  · rw [hmu ha] at h1 h12 h3
    rcases hcc with hb | hb | hb
    · exact absurd (hX _ hb) h2
    · rw [hmu hb] at h3 h2
      refine ⟨?_, h2⟩
      rw [mul_assoc, mul_comm (Φ r1 m₀), ← mul_assoc]
      exact h3
    · exact absurd (hmu hb).symm h12

end Rel

theorem exists_mem_ne_ne {G : Type*} [Group G] {E : Subgroup G} (h4 : 4 ≤ Nat.card E) (x y : G) :
    ∃ z ∈ E, z ≠ x ∧ z ≠ y := by
  by_contra hcon
  push Not at hcon
  have hsub : (E : Set G) ⊆ {x, y} := fun z hz => by
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr (hcon z hz hzx)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, y} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le x {y}).trans (by rw [Set.ncard_singleton])
  have h3 : (E : Set G).ncard = Nat.card E := (Nat.card_coe_set_eq _).symm
  omega

end CFSG.Quasithin.H13.A6.S7C
