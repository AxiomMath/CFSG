module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fin5_shift_const {f : Fin 5 → V} {g : G} (hf : ∀ i, g • f i = f (i + 1))
    {i j : Fin 5} (hij : i ≠ j) (h : f i = f j) : ∀ k, f k = f 0 := by
  open Fin.CommRing Fin.NatCast in
  have hpow : ∀ (n : ℕ) (k : Fin 5), g ^ n • f k = f (k + n) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [pow_succ', mul_smul, ih, hf]
      congr 1
      push_cast
      ring
  open Fin.CommRing Fin.NatCast in
  have hshift : ∀ k, f k = f (k + (j - i)) := by
    intro k
    have h1 := hpow (k - i).val i
    have h2 := hpow (k - i).val j
    rw [h] at h1
    have h3 := h1.symm.trans h2
    rw [Fin.cast_val_eq_self] at h3
    have e1 : i + (k - i) = k := by ring
    have e2 : j + (k - i) = k + (j - i) := by ring
    rwa [e1, e2] at h3
  open Fin.CommRing Fin.NatCast in
  have hmul : ∀ (n : ℕ) (k : Fin 5), f k = f (k + n * (j - i)) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [ih k, hshift (k + n * (j - i))]
      congr 1
      push_cast
      ring
  open Fin.CommRing Fin.NatCast in
  have hex : ∀ d k : Fin 5, d ≠ 0 → ∃ n : Fin 5, n * d = k := by decide
  open Fin.CommRing Fin.NatCast in
  intro k
  have hd : j - i ≠ 0 := fun h0 => hij (by
    have : j = i := by simpa [sub_eq_zero] using h0
    exact this.symm)
  obtain ⟨n, hn⟩ := hex (j - i) k hd
  rw [hmul n.val 0, Fin.cast_val_eq_self, zero_add, hn]

theorem not_injective_of_ncard_lt {S : Set V} (hfin : S.Finite) (hlt : S.ncard < 5)
    {f : Fin 5 → V} (hf : ∀ k, f k ∈ S) : ¬ Function.Injective f := by
  intro hinj
  have := Set.ncard_le_ncard_of_injOn f (s := Set.univ) (t := S) (fun a _ => hf a)
    hinj.injOn hfin
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem neighborSet_ncard {v : V} {k : ℕ} (hv : valence Γ v = k) :
    (Γ.neighborSet v).ncard = k := by
  rw [← Nat.card_coe_set_eq]
  exact hv

theorem neighborSet_finite {v : V} {k : ℕ} (hk : 0 < k) (hv : valence Γ v = k) :
    (Γ.neighborSet v).Finite :=
  Set.finite_of_ncard_pos (by rw [neighborSet_ncard hv]; exact hk)

theorem neighborSet_diff_ncard {v a : V} {k : ℕ} (hv : valence Γ v = k)
    (ha : Γ.Adj v a) : (Γ.neighborSet v \ {a}).ncard = k - 1 := by
  have ha' : a ∈ Γ.neighborSet v := ha
  rw [Set.ncard_sdiff_singleton_of_mem ha', neighborSet_ncard hv]

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem dist_vert (F : FanTree Γ G) (i : Fin 5) {m : ℕ} (hm : m ≤ 4) :
    Γ.dist α ((D.P i).vert m) = m := by
  have := Arc.dist_eq F.isTree (D.P i) m hm
  rwa [D.start i] at this

theorem valence_vert_even (F : FanTree Γ G) (i : Fin 5) {m : ℕ} (hm : m ≤ 4) (he : m % 2 = 0) :
    valence Γ ((D.P i).vert m) = 5 :=
  valence_of_dist_even F D.val (by rw [D.dist_vert F i hm]; exact he)

theorem valence_vert_odd (F : FanTree Γ G) (i : Fin 5) {m : ℕ} (hm : m ≤ 4) (ho : m % 2 = 1) :
    valence Γ ((D.P i).vert m) = 3 :=
  valence_of_dist_odd F D.val (by rw [D.dist_vert F i hm]; exact ho)

theorem valence_alpha (F : FanTree Γ G) (i : Fin 5) : valence Γ (D.alpha i) = 5 :=
  D.valence_vert_even F i (by norm_num) (by norm_num)

theorem valence_beta (F : FanTree Γ G) (i : Fin 5) : valence Γ (D.beta i) = 3 :=
  D.valence_vert_odd F i (by norm_num) (by norm_num)

theorem valence_xi (F : FanTree Γ G) (i : Fin 5) : valence Γ (D.xi i) = 3 :=
  D.valence_vert_odd F i (by norm_num) (by norm_num)

theorem valence_delta (F : FanTree Γ G) (i : Fin 5) : valence Γ (D.delta i) = 5 :=
  D.valence_vert_even F i (by norm_num) (by norm_num)

theorem dist_delta (F : FanTree Γ G) (i : Fin 5) : Γ.dist α (D.delta i) = 4 :=
  D.dist_vert F i le_rfl

theorem z_delta_mem_stabilizer (F : FanTree Γ G) (h : Fan71c F L) (i : Fin 5) :
    L.z (D.delta i) ∈ MulAction.stabilizer G α :=
  (h.z_mem_stabilizer_iff (D.valence_delta F i) α).2
    (by rw [dist_comm, D.dist_delta F i])

theorem x_mem_stabilizer (F : FanTree Γ G) (h : Fan71c F L) : D.x ∈ MulAction.stabilizer G α :=
  Subgroup.mul_mem _ (D.z_delta_mem_stabilizer F h 2) (D.z_delta_mem_stabilizer F h 0)

theorem delta_injective : Function.Injective D.delta := by
  intro i j hij
  apply D.inj
  show L.z (D.delta i) = L.z (D.delta j)
  rw [hij]

theorem x_inv_smul_delta (F : FanTree Γ G) (h : Fan71c F L) (i : Fin 5) :
    D.x⁻¹ • D.delta i = D.delta (i + 1) := by
  apply h.z_injective (by rw [valence_smul F]; exact D.valence_delta F i) (D.valence_delta F _)
  rw [L.z_inv_smul D.x (D.valence_delta F i)]
  exact D.conj i

theorem adj_start_beta (k : Fin 5) : Γ.Adj α (D.beta k) := by
  have := (D.P k).adj 0 (by norm_num)
  rwa [D.start k] at this

theorem adj_beta_alpha (k : Fin 5) : Γ.Adj (D.beta k) (D.alpha k) :=
  (D.P k).adj 1 (by norm_num)

theorem adj_alpha_xi (k : Fin 5) : Γ.Adj (D.alpha k) (D.xi k) := (D.P k).adj 2 (by norm_num)

theorem adj_xi_delta (k : Fin 5) : Γ.Adj (D.xi k) (D.delta k) := (D.P k).adj 3 (by norm_num)

theorem alpha_ne_start (k : Fin 5) : D.alpha k ≠ α := fun h =>
  (D.P k).nb 0 (by norm_num) ((D.start k).trans h.symm)

theorem xi_ne_beta (k : Fin 5) : D.xi k ≠ D.beta k := fun h =>
  (D.P k).nb 1 (by norm_num) h.symm

theorem delta_ne_alpha (k : Fin 5) : D.delta k ≠ D.alpha k := fun h =>
  (D.P k).nb 2 (by norm_num) h.symm

theorem x_inv_smul_vert (F : FanTree Γ G) (h : Fan71c F L) (i : Fin 5) {m : ℕ} (hm : m ≤ 4) :
    D.x⁻¹ • (D.P i).vert m = (D.P (i + 1)).vert m := by
  have hx : D.x⁻¹ • α = α := MulAction.mem_stabilizer_iff.1 (inv_mem (D.x_mem_stabilizer F h))
  refine smul_vert_eq_of_ends F (D.P i) (D.P (i + 1)) D.x⁻¹ ?_ ?_ m hm
  · rw [D.start, D.start, hx]
  · exact D.x_inv_smul_delta F h i

end D10Set

end CFSG.Quasithin.Fan86
