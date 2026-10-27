module

public import CFSG.RankThree.PartOne.SEITZ6.G2MSwap
public import CFSG.LieType.Steinberg.Collection
public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.RankThree.PartOne.SEITZ6.G2Close

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def posList : List ℕ := [0, 1, 4, 8, 3, 7]

@[expose] def hh : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 4 => 2
  | 8 => 3
  | 3 => 4
  | 7 => 5
  | _ => 0

@[expose] noncomputable def ordProd (c : ℕ → K) : adjointGroup .G2 K :=
  xp 0 (c 0) * xp 1 (c 1) * xp 4 (c 4) * xp 8 (c 8) * xp 3 (c 3) * xp 7 (c 7)

@[expose] noncomputable def Ug (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  ⨆ p ∈ posList, Xp K p


theorem comm_of_swap {G : Type*} [Group G] (g h z : G) (hz : g * h = z * (h * g)) :
    ⁅g, h⁆ = z := by
  rw [commutatorElement_def]
  calc g * h * g⁻¹ * h⁻¹ = z * (h * g) * g⁻¹ * h⁻¹ := by rw [hz]
    _ = z := by group

theorem mem_posList {p : ℕ} (hp : p ∈ posList) : p = 0 ∨ p = 1 ∨ p = 4 ∨ p = 8 ∨ p = 3 ∨ p = 7 := by
  simpa [posList] using hp

theorem xp_mem_Xp (p : ℕ) (hp : p < 12) (c : K) : xp p c ∈ Xp K p :=
  (mem_Xp_iff hp _).2 ⟨c, rfl⟩

theorem mem_TT {a b c : ℕ} (hc : c ∈ posList) (h : min (hh a) (hh b) < hh c)
    {z : adjointGroup .G2 K} (hz : z ∈ Xp K c) :
    z ∈ ⨆ c ∈ posList, ⨆ (_ : min (hh a) (hh b) < hh c), Xp K c := by
  have : Xp K c ≤ ⨆ c ∈ posList, ⨆ (_ : min (hh a) (hh b) < hh c), Xp K c :=
    le_iSup₂_of_le c hc (le_iSup (fun _ : min (hh a) (hh b) < hh c => Xp K c) h)
  exact this hz

macro "g2coll" : tactic => `(tactic| simp only [mul_assoc, tail_40, tail_80, tail_70, tail_31,
    tail_71, tail_34, tail_74, tail_38, tail_78, tail_73, end_40, end_80, end_70, end_31, end_71,
    end_34, end_74, end_38, end_78, end_73, tail_10, tail_41, tail_81, tail_30, tail_84, end_10,
    end_41, end_81, end_30, end_84, xp_merge, xp_merge', xp_cancel, xp_cancel',
    CharTwo.add_self_eq_zero, xp_zero, one_mul, mul_one])

macro "memTT" : tactic => `(tactic| repeat' first
    | exact Subgroup.one_mem _
    | apply Subgroup.mul_mem
    | exact mem_TT (c := 0) (by simp [posList]) (by decide) (xp_mem_Xp 0 (by norm_num) _)
    | exact mem_TT (c := 1) (by simp [posList]) (by decide) (xp_mem_Xp 1 (by norm_num) _)
    | exact mem_TT (c := 4) (by simp [posList]) (by decide) (xp_mem_Xp 4 (by norm_num) _)
    | exact mem_TT (c := 8) (by simp [posList]) (by decide) (xp_mem_Xp 8 (by norm_num) _)
    | exact mem_TT (c := 3) (by simp [posList]) (by decide) (xp_mem_Xp 3 (by norm_num) _)
    | exact mem_TT (c := 7) (by simp [posList]) (by decide) (xp_mem_Xp 7 (by norm_num) _))

theorem comm_cond [CharP K 2] : ∀ a ∈ posList, ∀ b ∈ posList, a ≠ b → ∀ x ∈ Xp K a,
    ∀ y ∈ Xp K b, ⁅x, y⁆ ∈ ⨆ c ∈ posList, ⨆ (_ : min (hh a) (hh b) < hh c), Xp K c := by
  intro a ha b hb hab x hx y hy
  have ha' := mem_posList ha
  have hb' := mem_posList hb
  obtain ⟨s, rfl⟩ := (mem_Xp_iff
    (by rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num) x).1 hx
  obtain ⟨t, rfl⟩ := (mem_Xp_iff
    (by rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num) y).1 hy
  rw [commutatorElement_def, xp_inv, xp_inv]
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | (g2coll; memTT)

theorem posList_nodup : posList.Nodup := by decide

theorem posList_sorted : posList.Pairwise fun a b => hh a ≤ hh b := by decide

theorem lt_twelve_of_mem_posList {p : ℕ} (hp : p ∈ posList) : p < 12 := by
  rcases mem_posList hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem exists_ordProd [CharP K 2] {u : adjointGroup .G2 K} (hu : u ∈ Ug K) :
    ∃ c : ℕ → K, u = ordProd c := by
  classical
  obtain ⟨f, hf, rfl⟩ := exists_prod_eq_of_commutator_mem (fun p => Xp K p) hh posList_nodup
    posList_sorted comm_cond u hu
  have hc : ∀ p ∈ posList, ∃ c : K, xp p c = f p := fun p hp =>
    (mem_Xp_iff (lt_twelve_of_mem_posList hp) _).1 (hf p hp)
  choose! c hc using hc
  refine ⟨c, ?_⟩
  simp only [posList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [ordProd]
  have h0 := hc 0 (by simp [posList])
  have h1 := hc 1 (by simp [posList])
  have h4 := hc 4 (by simp [posList])
  have h8 := hc 8 (by simp [posList])
  have h3 := hc 3 (by simp [posList])
  have h7 := hc 7 (by simp [posList])
  rw [h0, h1, h4, h8, h3, h7]
  simp only [mul_assoc]

@[expose] def htG2 : (Fin (Tag.rank .G2) → ℤ) →+ ℤ :=
  Pi.evalAddMonoidHom (fun _ => ℤ) (0 : Fin 2) + Pi.evalAddMonoidHom (fun _ => ℤ) (1 : Fin 2)

theorem ordProd_injective [CharP K 2] {c d : ℕ → K} (h : ordProd c = ordProd d) :
    ∀ p ∈ posList, c p = d p := by
  set L : List (Fin (Tag.rank .G2) → ℤ) := posList.map rt with hLdef
  have hroots : ∀ γ ∈ L, IsRoot .G2 γ ∧ 0 < htG2 γ := by
    intro γ hγ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hγ
    refine ⟨isRoot_rt (lt_twelve_of_mem_posList hp), ?_⟩
    rcases mem_posList hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hnd : L.Nodup := by decide
  have hsort : L.Pairwise fun γ δ => htG2 γ ≤ htG2 δ := by decide
  have hinj := prodInjective (F := rootOperatorFamily .G2) (K := K) htG2 L hnd hroots hsort
  set pos : (Fin (Tag.rank .G2) → ℤ) → ℕ := fun v =>
    if v e0 = 1 ∧ v e1 = 0 then 0 else if v e0 = 0 ∧ v e1 = 1 then 1 else
    if v e0 = 1 ∧ v e1 = 1 then 4 else if v e0 = 1 ∧ v e1 = 2 then 8 else
    if v e0 = 1 ∧ v e1 = 3 then 3 else 7 with hpos
  have hpos_rt : ∀ p ∈ posList, pos (rt p) = p := by
    intro p hp
    rcases mem_posList hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hprodc : ∀ e : ℕ → K,
      (L.map fun v => xPar (rootOperatorFamily .G2) v (e (pos v))).prod = ordProd e := by
    intro e
    simp only [hLdef, List.map_map]
    rw [List.map_congr_left (g := fun p => xp p (e p)) (fun p hp => by
      simp only [Function.comp_apply, hpos_rt p hp])]
    simp [posList, ordProd, mul_assoc]
  have key := hinj (fun v => xPar (rootOperatorFamily .G2) v (c (pos v)))
    (fun v => xPar (rootOperatorFamily .G2) v (d (pos v)))
    (fun γ hγ => xPar_mem (hroots _ hγ).1 _) (fun γ hγ => xPar_mem (hroots _ hγ).1 _)
    (by rw [hprodc c, hprodc d]; exact h)
  intro p hp
  have hmem : rt p ∈ L := List.mem_map.2 ⟨p, hp, rfl⟩
  have := key (rt p) hmem
  simp only [hpos_rt p hp] at this
  exact xPar_injective (F := rootOperatorFamily .G2) (K := K) (hroots _ hmem).1 this

theorem ofNat_eq_char2 [CharP K 2] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : K) = ((n % 2 : ℕ) : K) := by
  rw [← Nat.cast_ofNat]
  exact (CharP.natCast_eq_natCast K 2).2 (Nat.mod_modEq n 2).symm

macro "char2" : tactic => `(tactic| (ring_nf; simp [ofNat_eq_char2]; try ring_nf))

theorem ordProd_inv [CharP K 2] (c : ℕ → K) :
    (ordProd c)⁻¹ =
      xp 7 (c 7) * xp 3 (c 3) * xp 8 (c 8) * xp 4 (c 4) * xp 1 (c 1) * xp 0 (c 0) := by
  simp only [ordProd, mul_inv_rev, xp_inv, mul_assoc]

theorem conj_x1 [CharP K 2] (c : ℕ → K) (a : K) :
    ordProd c * xp 1 a * (ordProd c)⁻¹ =
      xp 1 a * (xp 4 (a * c 0) * (xp 8 (a ^ 2 * c 0) * (xp 3 (a ^ 3 * c 0 + a ^ 2 * c 4 + a * c 8) *
        xp 7 (a ^ 2 * c 0 * c 4 + a * c 0 * c 8 + a * c 4 ^ 2)))) := by
  rw [ordProd_inv]
  unfold ordProd
  g2coll
  congr 1
  · congr 1; char2
  · congr 1
    · congr 1; char2
    · congr 1
      · congr 1; char2
      · congr 1
        · congr 1; char2
        · congr 1; char2

theorem conj_x0 [CharP K 2] (c : ℕ → K) (d : K) :
    ordProd c * xp 0 d * (ordProd c)⁻¹ =
      xp 0 d * (xp 4 (c 1 * d) * (xp 8 (c 1 ^ 2 * d) * (xp 3 (c 1 ^ 3 * d) *
        xp 7 (c 0 * c 1 ^ 3 * d + c 1 ^ 3 * d ^ 2 + c 3 * d)))) := by
  rw [ordProd_inv]
  unfold ordProd
  g2coll
  congr 1
  · congr 1; char2
  · congr 1
    · congr 1; char2
    · congr 1
      · congr 1; char2
      · congr 1
        · congr 1; char2
        · congr 1; char2

theorem conj_x3 [CharP K 2] (c : ℕ → K) (d : K) :
    ordProd c * xp 3 d * (ordProd c)⁻¹ = xp 3 d * xp 7 (c 0 * d) := by
  rw [ordProd_inv]
  unfold ordProd
  g2coll
  have e4 : c 1 * c 0 + (c 4 + (c 1 * c 0 + c 4)) = 0 := by char2
  have e8 : c 1 ^ 2 * c 0 + (c 8 + (c 1 ^ 2 * c 0 + c 8)) = 0 := by char2
  rw [e4, e8, xp_zero, xp_zero, one_mul, one_mul]
  congr 1
  · congr 1; char2
  · congr 1; char2

@[expose] def mk6 (a0 a1 a4 a8 a3 a7 : K) : ℕ → K := fun p =>
  if p = 0 then a0 else if p = 1 then a1 else if p = 4 then a4 else if p = 8 then a8
  else if p = 3 then a3 else if p = 7 then a7 else 0

theorem ordProd_mk6 (a0 a1 a4 a8 a3 a7 : K) :
    ordProd (mk6 a0 a1 a4 a8 a3 a7) =
      xp 0 a0 * xp 1 a1 * xp 4 a4 * xp 8 a8 * xp 3 a3 * xp 7 a7 := by
  simp [ordProd, mk6]

theorem six_inj [CharP K 2] {a0 a1 a4 a8 a3 a7 b0 b1 b4 b8 b3 b7 : K}
    (h : xp 0 a0 * xp 1 a1 * xp 4 a4 * xp 8 a8 * xp 3 a3 * xp 7 a7 =
      xp 0 b0 * xp 1 b1 * xp 4 b4 * xp 8 b8 * xp 3 b3 * xp 7 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a4 = b4 ∧ a8 = b8 ∧ a3 = b3 ∧ a7 = b7 := by
  have h' := ordProd_injective (c := mk6 a0 a1 a4 a8 a3 a7) (d := mk6 b0 b1 b4 b8 b3 b7)
    (by rw [ordProd_mk6, ordProd_mk6]; exact h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [mk6] using h' 0 (by simp [posList])
  · simpa [mk6] using h' 1 (by simp [posList])
  · simpa [mk6] using h' 4 (by simp [posList])
  · simpa [mk6] using h' 8 (by simp [posList])
  · simpa [mk6] using h' 3 (by simp [posList])
  · simpa [mk6] using h' 7 (by simp [posList])

@[expose] noncomputable def Up (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  Xp K 7 ⊔ Xp K 1

theorem commute_Xp [CharP K 2] {p q : ℕ} (hp : p < 12) (hq : q < 12)
    (h : ∀ x y : K, Commute (xp p x) (xp q y)) :
    ∀ g ∈ Xp K p, ∀ g' ∈ Xp K q, g * g' = g' * g := by
  intro g hg g' hg'
  obtain ⟨x, rfl⟩ := (mem_Xp_iff hp g).1 hg
  obtain ⟨y, rfl⟩ := (mem_Xp_iff hq g').1 hg'
  exact (h x y).eq

theorem le_normalizer_of_commute {G : Type*} [Group G] {H N : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ N, x * y = y * x) : H ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h x hx y hy]
    simpa using hy
  · intro hy
    have h1 := h x⁻¹ (H.inv_mem hx) _ hy
    have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [this, h1]
    simpa using hy

theorem mem_Up_iff [CharP K 2] {g : adjointGroup .G2 K} :
    g ∈ Up K ↔ ∃ a b : K, g = xp 7 a * xp 1 b := by
  have hle : Xp K 7 ≤ Subgroup.normalizer ((Xp K 1 : Subgroup (adjointGroup .G2 K)) : Set _) :=
    le_normalizer_of_commute (commute_Xp (by norm_num) (by norm_num)
      (fun x y => (commute_17 y x).symm))
  have h := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle
  rw [← SetLike.mem_coe]
  unfold Up
  rw [h, Set.mem_mul]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_Xp_iff (by norm_num) x).1 hx
    obtain ⟨b, rfl⟩ := (mem_Xp_iff (by norm_num) y).1 hy
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨xp 7 a, xp_mem_Xp 7 (by norm_num) a, xp 1 b, xp_mem_Xp 1 (by norm_num) b, rfl⟩

theorem Up_coords [CharP K 2] {a0 a1 a4 a8 a3 a7 : K}
    (h : xp 0 a0 * xp 1 a1 * xp 4 a4 * xp 8 a8 * xp 3 a3 * xp 7 a7 ∈ Up K) :
    a0 = 0 ∧ a4 = 0 ∧ a8 = 0 ∧ a3 = 0 := by
  obtain ⟨a, b, hab⟩ := mem_Up_iff.1 h
  have e : xp 7 a * xp 1 b = xp 0 0 * xp 1 b * xp 4 0 * xp 8 0 * xp 3 0 * xp 7 a := by
    simp only [xp_zero, one_mul, mul_one]
    exact (commute_17 b a).eq.symm
  rw [e] at hab
  obtain ⟨h0, -, h4, h8, h3, -⟩ := six_inj hab
  exact ⟨h0, h4, h8, h3⟩

theorem conj_x1_coords [CharP K 2] (c : ℕ → K) (a : K)
    (h : ordProd c * xp 1 a * (ordProd c)⁻¹ ∈ Up K) :
    a * c 0 = 0 ∧ a ^ 3 * c 0 + a ^ 2 * c 4 + a * c 8 = 0 := by
  rw [conj_x1] at h
  have e := Up_coords (a0 := 0) (a1 := a) (a4 := a * c 0) (a8 := a ^ 2 * c 0)
    (a3 := a ^ 3 * c 0 + a ^ 2 * c 4 + a * c 8)
    (a7 := a ^ 2 * c 0 * c 4 + a * c 0 * c 8 + a * c 4 ^ 2)
    (by simpa only [xp_zero, one_mul, mul_assoc] using h)
  exact ⟨e.2.1, e.2.2.2⟩

theorem coords_of_conj_x1 [CharP K 2] (c : ℕ → K) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h1 : ordProd c * xp 1 1 * (ordProd c)⁻¹ ∈ Up K)
    (ht : ordProd c * xp 1 t * (ordProd c)⁻¹ ∈ Up K) :
    c 0 = 0 ∧ c 4 = 0 ∧ c 8 = 0 := by
  obtain ⟨a1, b1⟩ := conj_x1_coords c 1 h1
  obtain ⟨a2, b2⟩ := conj_x1_coords c t ht
  have hc0 : c 0 = 0 := by simpa using a1
  rw [hc0] at b1 b2
  have h48 : c 4 + c 8 = 0 := by simpa using b1
  have h8 : c 8 = c 4 := (CharTwo.add_eq_zero.1 h48).symm
  rw [h8] at b2
  have h2 : t * ((t + 1) * c 4) = 0 := by
    have : t ^ 2 * c 4 + t * c 4 = 0 := by simpa using b2
    linear_combination this
  have ht' : t + 1 ≠ 0 := fun h => ht1 (CharTwo.add_eq_zero.1 h)
  have hc4 : c 4 = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h ht0
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h ht'
      · exact h
  exact ⟨hc0, hc4, by rw [h8, hc4]⟩

theorem eq_zero_of_conj_x0 [CharP K 2] (c : ℕ → K) (d : K)
    (h : ordProd c * xp 0 d * (ordProd c)⁻¹ ∈ Up K) : d = 0 := by
  rw [conj_x0] at h
  exact (Up_coords (a0 := d) (a1 := 0) (a4 := c 1 * d) (a8 := c 1 ^ 2 * d) (a3 := c 1 ^ 3 * d)
    (a7 := c 0 * c 1 ^ 3 * d + c 1 ^ 3 * d ^ 2 + c 3 * d)
    (by simpa only [xp_zero, mul_one, mul_assoc] using h)).1

theorem eq_zero_of_conj_x3 [CharP K 2] (c : ℕ → K) (d : K)
    (h : ordProd c * xp 3 d * (ordProd c)⁻¹ ∈ Up K) : d = 0 := by
  rw [conj_x3] at h
  exact (Up_coords (a0 := 0) (a1 := 0) (a4 := 0) (a8 := 0) (a3 := d) (a7 := c 0 * d)
    (by simpa only [xp_zero, one_mul, mul_assoc] using h)).2.2.2

end CFSG.RankThree.PartOne.SEITZ6
