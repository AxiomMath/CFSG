module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCBase

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

variable {G : Type} [Group G] [Finite G]

theorem qTwoLMPrimeC_elemAbelian_T {B Bs L : Subgroup G} (hBs : GGBstar 3 B Bs) :
    IsElemAbelian 3 (Bs ⊓ L) :=
  CFSG.Open.IsElemAbelian.mono hBs.2.1 inf_le_left

private lemma qTwoLMPrimeC_tor_center_eq_bot {B L : Subgroup G} {x : G} {m : ℕ}
    (hG : GGThmIHyp 3 B x L) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hMul : PSUTrivialMultiplier m) {u : G} (hu : u ∈ L)
    (h : ∀ l ∈ L, u * l * u⁻¹ = l) : u = 1 := by
  have hmem : (⟨u, hu⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hl := h l l.2
    have hl' : u * (l : G) = (l : G) * u := by
      calc
        u * (l : G) = (u * (l : G) * u⁻¹) * u := by group
        _ = (l : G) * u := by rw [hl]
    exact hl'.symm
  rw [qTwoLMFrameC_center_bot hG hL hMul, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

private lemma qTwoLMPrimeC_tor_conj_eq {B L : Subgroup G} {x : G} {m : ℕ}
    (hG : GGThmIHyp 3 B x L) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hMul : PSUTrivialMultiplier m) {u v : G} (hu : u ∈ L) (hv : v ∈ L)
    (h : ∀ l ∈ L, u * l * u⁻¹ = v * l * v⁻¹) : u = v := by
  have hvu : v⁻¹ * u ∈ L := L.mul_mem (L.inv_mem hv) hu
  have h1 : ∀ l ∈ L, (v⁻¹ * u) * l * (v⁻¹ * u)⁻¹ = l := by
    intro l hl
    have h2 := h l hl
    calc
      (v⁻¹ * u) * l * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * l * u⁻¹) * v := by group
      _ = v⁻¹ * (v * l * v⁻¹) * v := by rw [h2]
      _ = l := by group
  have h3 := qTwoLMPrimeC_tor_center_eq_bot hG hL hMul hvu h1
  calc
    u = v * (v⁻¹ * u) := by group
    _ = v * 1 := by rw [h3]
    _ = v := by group

theorem qTwoLMPrimeC_rep_mem {B Bs L : Subgroup G} {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m)
    {b e : G} (hb : b ∈ Bs) (he : e ∈ L) (hbe : ∀ l ∈ L, b * l * b⁻¹ = e * l * e⁻¹) :
    e ∈ Bs ⊓ L := by
  refine Subgroup.mem_inf.mpr ⟨?_, he⟩
  have hb3 : b ^ 3 = 1 := hBs.2.1.2 b hb
  have he3 : e ^ 3 = 1 := by
    have hpow : ∀ k : ℕ, ∀ l ∈ L,
        b ^ k * l * (b ^ k)⁻¹ = e ^ k * l * (e ^ k)⁻¹ := by
      intro k
      induction k with
      | zero =>
        intro l hl
        simp
      | succ k ih =>
        intro l hl
        have hmem_e : e * l * e⁻¹ ∈ L := L.mul_mem (L.mul_mem he hl) (L.inv_mem he)
        have h1 := ih (e * l * e⁻¹) hmem_e
        calc
          b ^ (k + 1) * l * (b ^ (k + 1))⁻¹ =
              b ^ k * (b * l * b⁻¹) * (b ^ k)⁻¹ := by
            rw [pow_succ]
            group
          _ = b ^ k * (e * l * e⁻¹) * (b ^ k)⁻¹ := by rw [hbe l hl]
          _ = e ^ k * (e * l * e⁻¹) * (e ^ k)⁻¹ := h1
          _ = e ^ (k + 1) * l * (e ^ (k + 1))⁻¹ := by
            rw [pow_succ]
            group
    have h3 := hpow 3
    apply qTwoLMPrimeC_tor_center_eq_bot hG hL hMul (L.pow_mem he 3)
    intro l hl
    have h3l := h3 l hl
    rw [hb3, one_mul, inv_one, mul_one] at h3l
    exact h3l.symm
  have hcent : e ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    rcases qTwoLMPrimeC_inner hG hBs hN h3 hL b' hb' with ⟨e', he', hbe'⟩
    have hbb' : b * b' = b' * b := CFSG.Open.IsElemAbelian.comm hBs.2.1 hb hb'
    have hconj : ∀ l ∈ L, (e * e') * l * (e * e')⁻¹ = (e' * e) * l * (e' * e)⁻¹ := by
      intro l hl
      have h1 : b * b' * l * (b * b')⁻¹ = e * (e' * l * e'⁻¹) * e⁻¹ := by
        calc
          b * b' * l * (b * b')⁻¹ = b * (b' * l * b'⁻¹) * b⁻¹ := by group
          _ = b * (e' * l * e'⁻¹) * b⁻¹ := by rw [hbe' l hl]
          _ = e * (e' * l * e'⁻¹) * e⁻¹ := by
            rw [hbe (e' * l * e'⁻¹) (L.mul_mem (L.mul_mem he' hl) (L.inv_mem he'))]
      have h2 : b' * b * l * (b' * b)⁻¹ = e' * (e * l * e⁻¹) * e'⁻¹ := by
        calc
          b' * b * l * (b' * b)⁻¹ = b' * (b * l * b⁻¹) * b'⁻¹ := by group
          _ = b' * (e * l * e⁻¹) * b'⁻¹ := by rw [hbe l hl]
          _ = e' * (e * l * e⁻¹) * e'⁻¹ := by
            rw [hbe' (e * l * e⁻¹) (L.mul_mem (L.mul_mem he hl) (L.inv_mem he))]
      rw [hbb'] at h1
      rw [h2] at h1
      calc
        (e * e') * l * (e * e')⁻¹ = e * (e' * l * e'⁻¹) * e⁻¹ := by group
        _ = e' * (e * l * e⁻¹) * e'⁻¹ := h1.symm
        _ = (e' * e) * l * (e' * e)⁻¹ := by group
    have hee' : e * e' = e' * e :=
      qTwoLMPrimeC_tor_conj_eq hG hL hMul (L.mul_mem he he') (L.mul_mem he' he) hconj
    have hbe'_e : b' * e * b'⁻¹ = e' * e * e'⁻¹ := hbe' e he
    have hbe'_e' : b' * e * b'⁻¹ = e := by
      calc
        b' * e * b'⁻¹ = e' * e * e'⁻¹ := hbe'_e
        _ = e * e' * e'⁻¹ := by rw [← hee']
        _ = e := by group
    calc
      b' * e = (b' * e * b'⁻¹) * b' := by group
      _ = e * b' := by rw [hbe'_e']
  exact hBs.2.2.2 e hcent he3

theorem qTwoLMPrimeC_split {B Bs L : Subgroup G} {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m) :
    ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ L, ∃ k : ℕ, b = t * x ^ k := by
  intro b hb
  rcases qTwoLMPrimeC_inner hG hBs hN h3 hL b hb with ⟨e, he, hbe⟩
  have heT : e ∈ Bs ⊓ L := qTwoLMPrimeC_rep_mem hG hBs hN h3 hL hMul hb he hbe
  have hcBs : e⁻¹ * b ∈ Bs := Bs.mul_mem (Bs.inv_mem heT.1) hb
  have hcCent : e⁻¹ * b ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := hbe l hl
    have h1 : e⁻¹ * b * l = l * e⁻¹ * b := by
      calc
        e⁻¹ * b * l = e⁻¹ * (b * l * b⁻¹) * b := by group
        _ = e⁻¹ * (e * l * e⁻¹) * b := by rw [h]
        _ = l * e⁻¹ * b := by group
    rw [← mul_assoc]
    exact h1.symm
  have hcKer : e⁻¹ * b ∈ Bs ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_inf.mpr ⟨hcBs, hcCent⟩
  rw [qTwoLMPrimeC_ker hG hBs] at hcKer
  rcases Subgroup.mem_zpowers_iff.mp hcKer with ⟨k', hk'⟩
  have hxBs : x ∈ Bs := hBs.1 hG.2.2.2.2.2.2.1.2.1
  have hx3 : x ^ 3 = 1 := hBs.2.1.2 x hxBs
  have hxne : x ≠ 1 := hG.2.2.2.2.2.2.1.2.2.1
  have horder : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  let k : ℕ := (k' % 3).toNat
  have hk_eq : x ^ k' = x ^ k := by
    rw [← zpow_mod_orderOf, horder]
    have hnonneg : 0 ≤ k' % 3 := Int.emod_nonneg k' (by norm_num)
    change x ^ (k' % 3) = x ^ k
    rw [← Int.toNat_of_nonneg hnonneg, zpow_natCast]
  refine ⟨e, heT, k, ?_⟩
  calc
    b = e * (e⁻¹ * b) := by group
    _ = e * x ^ k' := by rw [← hk']
    _ = e * x ^ k := by rw [hk_eq]

theorem qTwoLMPrimeC_card_T_ge {B Bs L : Subgroup G} {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m) :
    3 ^ 3 ≤ Nat.card ↥(Bs ⊓ L) := by
  have hxBs : x ∈ Bs := hBs.1 hG.2.2.2.2.2.2.1.2.1
  let f : ↥(Bs ⊓ L) × Fin 3 → ↥Bs := fun p =>
    ⟨(p.1 : G) * x ^ (p.2 : ℕ), Bs.mul_mem p.1.2.1 (Bs.pow_mem hxBs (p.2 : ℕ))⟩
  have hsurj : Function.Surjective f := by
    intro b
    rcases qTwoLMPrimeC_split hG hBs hN h3 hL hMul b.1 b.2 with ⟨t, ht, k, hk⟩
    have hx3 : x ^ 3 = 1 := hBs.2.1.2 x hxBs
    have hkmod : x ^ k = x ^ (k % 3) := by
      rw [pow_eq_pow_iff_modEq]
      have horder : orderOf x = 3 := orderOf_eq_prime hx3 hG.2.2.2.2.2.2.1.2.2.1
      rw [horder]
      exact (Nat.mod_modEq k 3).symm
    refine ⟨(⟨t, ht⟩, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [f, Fin.val_mk]
    apply Subtype.ext
    rw [hkmod] at hk
    exact hk.symm
  have hcard : Nat.card ↥Bs ≤ Nat.card (↥(Bs ⊓ L) × Fin 3) :=
    Nat.card_le_card_of_surjective f hsurj
  rw [Nat.card_prod, Nat.card_fin] at hcard
  have hcardBs : 3 ^ 4 ≤ Nat.card ↥Bs := qTwoLMPrimeC_card_ge hG hBs
  have hle : 3 ^ 3 * 3 ≤ Nat.card ↥(Bs ⊓ L) * 3 := by
    calc
      3 ^ 3 * 3 = 3 ^ 4 := by norm_num
      _ ≤ Nat.card ↥Bs := hcardBs
      _ ≤ Nat.card ↥(Bs ⊓ L) * 3 := hcard
  exact Nat.le_of_mul_le_mul_right hle (by norm_num)

theorem qTwoLMPrimeC_selfcent {B Bs L : Subgroup G} {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m) :
    ∀ n ∈ L, (∀ t ∈ Bs ⊓ L, n * t = t * n) → n ^ 3 = 1 → n ∈ Bs ⊓ L := by
  intro n hnL hnT hn3
  have hcent : n ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rcases qTwoLMPrimeC_split hG hBs hN h3 hL hMul b hb with ⟨t, ht, k, hk⟩
    have hnt : n * t = t * n := hnT t ht
    have hnx : n * x = x * n := by
      have hmem : x * n = n * x := by
        have hx : x ∈ ({x} : Set G) := Set.mem_singleton x
        have hle : n ∈ Subgroup.centralizer ({x} : Set G) :=
          qTwoLMFrameC_le_centralizer hG hnL
        exact Subgroup.mem_centralizer_iff.mp hle x hx
      exact hmem.symm
    have hnxk : n * x ^ k = x ^ k * n := by
      have hcomm : Commute n x := hnx
      exact Commute.pow_right hcomm k
    calc
      b * n = (t * x ^ k) * n := by rw [← hk]
      _ = t * (x ^ k * n) := by rw [mul_assoc]
      _ = t * (n * x ^ k) := by rw [← hnxk]
      _ = (t * n) * x ^ k := by rw [← mul_assoc]
      _ = (n * t) * x ^ k := by rw [← hnt]
      _ = n * (t * x ^ k) := by rw [mul_assoc]
      _ = n * b := by rw [← hk]
  exact Subgroup.mem_inf.mpr ⟨hBs.2.2.2 n hcent hn3, hnL⟩

end CFSG.StandardType.QTwo

end
