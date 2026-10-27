module

public import CFSG.Quasithin.Vol2.Ch12Sec4G2SylData
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Background.P3G2Zorn

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Open

@[expose] def sGenE (j : ℕ) : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2) :=
  if j = 0 then zT01 else if j = 1 then zX else zT10 * zT01 * zX * zT01 * zT10

theorem matCode_sGenE {j : ℕ} (hj : j < 3) : matCode (sGenE j) = sGens.getD j [] := by
  interval_cases j
  · simp only [sGenE, ↓reduceIte]
    exact matCode_zT01
  · simp only [sGenE, one_ne_zero, ↓reduceIte]
    exact matCode_zX
  · simp only [sGenE, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte]
    rw [matCode_mul, matCode_mul, matCode_mul, matCode_mul, matCode_zT01, matCode_zT10, matCode_zX,
      matW_eq]
    rfl

theorem sGenE_mem (j : ℕ) : sGenE j ∈ quasithinG2 (ZMod 2) := by
  have h1 : zT01 ∈ quasithinG2 (ZMod 2) := mem_quasithinG2 zT01_mul
  have h2 : zT10 ∈ quasithinG2 (ZMod 2) := mem_quasithinG2 zT10_mul
  have h3 : zX ∈ quasithinG2 (ZMod 2) := mem_quasithinG2 zX_mul
  unfold sGenE
  split_ifs
  · exact h1
  · exact h3
  · exact mul_mem (mul_mem (mul_mem (mul_mem h2 h1) h3) h1) h2

@[expose] def sWordE (w : List ℕ) : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2) :=
  w.foldl (fun g j => g * sGenE j) 1

theorem matCode_foldl (w : List ℕ) (hw : ∀ j ∈ w, j < 3)
    (g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) :
    matCode ⇑(w.foldl (fun g j => g * sGenE j) g) =
      w.foldl (fun m j => mmul m (sGens.getD j [])) (matCode g) := by
  induction w generalizing g with
  | nil => rfl
  | cons j w ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (fun k hk => hw k (List.mem_cons_of_mem _ hk)),
      matCode_mul, matCode_sGenE (hw j List.mem_cons_self)]

theorem foldl_mem (w : List ℕ) {g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)}
    (hg : g ∈ quasithinG2 (ZMod 2)) :
    w.foldl (fun g j => g * sGenE j) g ∈ quasithinG2 (ZMod 2) := by
  induction w generalizing g with
  | nil => exact hg
  | cons j w ih => exact ih (mul_mem hg (sGenE_mem j))

@[expose] def sElt (i : ℕ) : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2) :=
  sWordE (sWords.getD i [])

theorem matCode_sElt {i : ℕ} (hi : i < 64) : matCode (sElt i) = sM i := by
  obtain ⟨h1, h2⟩ := sWords_spec i hi
  rw [sElt, sWordE, matCode_foldl _ h2, matCode_one]
  exact h1

theorem sElt_mem_G (i : ℕ) : sElt i ∈ quasithinG2 (ZMod 2) :=
  foldl_mem _ (one_mem _)

theorem sElt_zero : sElt 0 = 1 := by
  apply linearEquiv_eq_of_matCode
  rw [matCode_sElt (by norm_num), sM_zero]
  exact matCode_one.symm

theorem sElt_injective {i k : ℕ} (hi : i < 64) (hk : k < 64) (h : sElt i = sElt k) : i = k :=
  sMats_inj i hi k hk (by rw [← matCode_sElt hi, ← matCode_sElt hk, h])

theorem sElt_mul_gen {i j : ℕ} (hi : i < 64) (hj : j < 3) :
    ∃ k < 64, sElt i * sGenE j = sElt k := by
  obtain ⟨k, hk, hk'⟩ := sMats_closed i hi j hj
  refine ⟨k, hk, linearEquiv_eq_of_matCode ?_⟩
  rw [matCode_mul, matCode_sElt hi, matCode_sGenE hj, matCode_sElt hk, hk']

theorem sElt_mul_foldl (w : List ℕ) (hw : ∀ j ∈ w, j < 3) {i : ℕ} (hi : i < 64) :
    ∃ k < 64, w.foldl (fun g j => g * sGenE j) (sElt i) = sElt k := by
  induction w generalizing i with
  | nil => exact ⟨i, hi, rfl⟩
  | cons j w ih =>
    obtain ⟨k, hk, hk'⟩ := sElt_mul_gen hi (hw j List.mem_cons_self)
    rw [List.foldl_cons, hk']
    exact ih (fun l hl => hw l (List.mem_cons_of_mem _ hl)) hk

theorem foldl_mul (w : List ℕ) (g h : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) :
    w.foldl (fun g j => g * sGenE j) (g * h) = g * w.foldl (fun g j => g * sGenE j) h := by
  induction w generalizing h with
  | nil => rfl
  | cons j w ih => rw [List.foldl_cons, List.foldl_cons, mul_assoc, ih]

theorem foldl_eq_mul (w : List ℕ) (g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) :
    w.foldl (fun g j => g * sGenE j) g = g * w.foldl (fun g j => g * sGenE j) 1 := by
  rw [← foldl_mul, mul_one]

theorem sElt_mul {i k : ℕ} (hi : i < 64) (hk : k < 64) : ∃ l < 64, sElt i * sElt k = sElt l := by
  obtain ⟨-, h2⟩ := sWords_spec k hk
  obtain ⟨l, hl, e⟩ := sElt_mul_foldl (sWords.getD k []) h2 hi
  refine ⟨l, hl, ?_⟩
  rw [← e, foldl_eq_mul]
  rfl

theorem sElt_inv {i : ℕ} (hi : i < 64) : ∃ k < 64, (sElt i)⁻¹ = sElt k := by
  choose f hf hf' using fun k : Fin 64 => sElt_mul hi k.2
  let F : Fin 64 → Fin 64 := fun k => ⟨f k, hf k⟩
  have hF : Function.Injective F := by
    intro a b hab
    have h1 : sElt (f a) = sElt (f b) := congrArg (fun x : Fin 64 => sElt x) hab
    rw [← hf' a, ← hf' b] at h1
    exact Fin.ext (sElt_injective a.2 b.2 (mul_left_cancel h1))
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hF) ⟨0, by norm_num⟩
  refine ⟨k, k.2, ?_⟩
  have h1 : sElt i * sElt k = 1 := by
    rw [hf' k, ← sElt_zero]
    exact congrArg (fun x : Fin 64 => sElt x) hk
  exact inv_eq_of_mul_eq_one_right h1

@[expose] def sSub : Subgroup (quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) where
  carrier := {g | ∃ i < 64, sElt i = g}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨k, hk, rfl⟩
    obtain ⟨l, hl, e⟩ := sElt_mul hi hk
    exact ⟨l, hl, e.symm⟩
  one_mem' := ⟨0, by norm_num, sElt_zero⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨k, hk, e⟩ := sElt_inv hi
    exact ⟨k, hk, e.symm⟩

theorem mem_sSub {g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)} :
    g ∈ sSub ↔ ∃ i < 64, sElt i = g := Iff.rfl

theorem sSub_le : sSub ≤ quasithinG2 (ZMod 2) := by
  rintro _ ⟨i, -, rfl⟩
  exact sElt_mem_G i

theorem card_sSub : Nat.card sSub = 64 := by
  have hbij : Function.Bijective fun i : Fin 64 => (⟨sElt i, i, i.2, rfl⟩ : sSub) := by
    constructor
    · intro a b hab
      exact Fin.ext (sElt_injective a.2 b.2 (congrArg Subtype.val hab))
    · rintro ⟨_, i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_fin]

theorem card_g2Two : Nat.card ↥(quasithinG2 (ZMod 2)) = 12096 := by
  norm_num [G11.P3G2.quasithinG2_eq_cayleyGroup, Vol2.KGNat.card_cayleyGroup, Nat.card_zmod]

instance finite_g2Two : Finite ↥(quasithinG2 (ZMod 2)) :=
  Nat.finite_of_card_ne_zero (by rw [card_g2Two]; norm_num)

@[expose] def sSubG : Subgroup ↥(quasithinG2 (ZMod 2)) := sSub.subgroupOf (quasithinG2 (ZMod 2))

theorem card_sSubG : Nat.card sSubG = 64 := by
  rw [sSubG, ← card_sSub]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe sSub_le).toEquiv

theorem factorization_g2Two : (Nat.card ↥(quasithinG2 (ZMod 2))).factorization 2 = 6 := by
  rw [card_g2Two, show (12096 : ℕ) = 2 ^ 6 * 189 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

@[expose] noncomputable def sylowSub : Sylow 2 ↥(quasithinG2 (ZMod 2)) :=
  Sylow.ofCard sSubG (by rw [card_sSubG, factorization_g2Two]; norm_num)

theorem coe_sylowSub : (sylowSub : Subgroup ↥(quasithinG2 (ZMod 2))) = sSubG := rfl

end CFSG.Quasithin.H13.Orbit
