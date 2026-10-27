module

public import CFSG.RankThree.Native.ONTripleSig
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.NormalizesFive

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.ThreePrime

attribute [local irreducible] dotProduct

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup Equiv CFSG.RankThree.Native.ONTriple
open CFSG.RankThree.PartTwo

theorem no_five_sY : ∀ j < 2, ∀ x : Perm (Fin 6), x ^ 5 = 1 → x ≠ 1 → sY j * x ≠ x * sY j := by
  decide +kernel

theorem sY_cube : ∀ j < 2, sY j ^ 3 = 1 := by decide +kernel

theorem threePrime_card_dvd_eight {j : ℕ} (hj : j < 2) (B : Subgroup (Perm (Fin 6)))
    (hBA : B ≤ alternatingGroup (Fin 6)) (h3 : ¬ 3 ∣ Nat.card B)
    (hinv : ∀ t ∈ B, cj (sY j) t ∈ B) : Nat.card B ∣ 8 := by
  have h40 : Nat.card B ∣ 40 := by
    have h360 : Nat.card B ∣ 360 := by
      have := Subgroup.card_dvd_of_le hBA
      rwa [card_alt_six] at this
    have hc : Nat.Coprime (Nat.card B) 9 := by
      have : Nat.Coprime (Nat.card B) 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
      simpa using Nat.Coprime.pow_right 2 this
    exact hc.dvd_of_dvd_mul_left (by simpa using h360)
  set κ := sY j with hκ
  have hmap : B.map (MulAut.conj κ⁻¹).toMonoidHom ≤ B := by
    rintro _ ⟨t, ht, rfl⟩
    simpa [cj, MulAut.conj_apply] using hinv t ht
  have hcard : Nat.card (B.map (MulAut.conj κ⁻¹).toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj κ⁻¹).injective
  have heq : B.map (MulAut.conj κ⁻¹).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hmap hcard.ge
  have hnorm : κ⁻¹ ∈ Subgroup.normalizer (B : Set (Perm (Fin 6))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : κ⁻¹ * h * κ⁻¹⁻¹ ∈ B.map (MulAut.conj κ⁻¹).toMonoidHom := ⟨h, hh, by simp⟩
      rwa [heq] at this
    · intro hh
      rw [← heq] at hh
      obtain ⟨b, hb, hbh⟩ := hh
      have : b = h := by simpa [MulAut.conj_apply] using hbh
      exact this ▸ hb
  refine Proving.card_dvd_eight_of_pow_three_normalizes (t := κ⁻¹) ?_ hnorm h40 ?_
  · rw [inv_pow, sY_cube j hj, inv_one]
  · intro x hx hox hcomm
    apply no_five_sY j hj x
    · rw [← hox]; exact pow_orderOf_eq_one x
    · intro h1; rw [h1] at hox; simp at hox
    · have h : x * κ = κ * x := by
        have := congrArg (fun u => κ * u * κ) hcomm
        simpa [mul_assoc] using this
      exact h.symm

section K0

set_option linter.unusedSectionVars false


theorem mem_K0_of_coprime {g : GM} (hg : g ∈ centralizer {xG 0}) {n : ℕ} (hn : g ^ n = 1)
    (hcop : Nat.Coprime 3 n) : g ∈ K0G := by
  obtain ⟨a, k, hk, rfl⟩ := mem_centralizer_x0_iff.1 hg
  have hk0 : Commute k (xG 0) := K0_comm hk
  have hc : Commute (xG 0 ^ a) k := hk0.symm.pow_left a
  rw [hc.mul_pow, ← pow_mul] at hn
  have h1 : xG 0 ^ (a * n) ∈ K0G := by
    rw [eq_inv_of_mul_eq_one_left hn]
    exact inv_mem (pow_mem hk _)
  have h3 := three_dvd_of_pow_x0 (pow_x0_mem_K0 h1)
  obtain ⟨b, rfl⟩ := hcop.dvd_of_dvd_mul_right h3
  rw [pow_mul, xG0_cube, one_pow, one_mul]
  exact hk

theorem zG_pow_three : zG ^ 3 = 1 := by
  rw [← relG.orderOf_x]; exact pow_orderOf_eq_one _

theorem eq_one_of_cube_of_not_dvd {W : Subgroup GM} (h3 : ¬ 3 ∣ Nat.card W) {g : GM} (hg : g ∈ W)
    (hg3 : g ^ 3 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  have h2 : orderOf g ∣ Nat.card W := by
    have := orderOf_dvd_natCard (⟨g, hg⟩ : W)
    rwa [Subgroup.orderOf_mk] at this
  have hc : Nat.Coprime (orderOf g) 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · rw [h]; exact Nat.coprime_one_left _
    · exfalso; apply h3; rw [← h]; exact h2
  have : orderOf g = 1 := by
    have := Nat.dvd_gcd (dvd_refl (orderOf g)) h1
    rwa [hc, Nat.dvd_one] at this
  exact orderOf_eq_one_iff.1 this

theorem K0_threePrime_subgroups {j : ℕ} (hj : j < 2) (W : Subgroup GM) (hWK : W ≤ K0G)
    (h3 : ¬ 3 ∣ Nat.card W) (hy : ∀ g ∈ W, (yG j)⁻¹ * g * yG j ∈ W) :
    W = ⊥ ∨ ∃ (m : ℕ) (hm : m < 3), W = VG j m hj hm := by
  have hA : ∀ t ∈ blockImage W, Perm.sign t = 1 := by
    intro t ht
    obtain ⟨k, -, rfl⟩ := mem_blockImage.1 ht
    exact actK_mem_alt k
  have hinv : ∀ t ∈ blockImage W, cj (sY j) t ∈ blockImage W := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := mem_blockImage.1 ht
    have hmem : ((⟨yG j, yG_mem_K0 hj⟩⁻¹ * k * ⟨yG j, yG_mem_K0 hj⟩ : K0G) : GM) ∈ W := by
      have e : ((⟨yG j, yG_mem_K0 hj⟩⁻¹ * k * ⟨yG j, yG_mem_K0 hj⟩ : K0G) : GM) =
          (yG j)⁻¹ * k * yG j := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      exact hy _ hk
    refine mem_blockImage.2 ⟨_, hmem, ?_⟩
    unfold cj
    rw [map_mul, map_mul, map_inv, actK_yG hj]
  have hBA : blockImage W ≤ alternatingGroup (Fin 6) := fun t ht =>
    Equiv.Perm.mem_alternatingGroup.2 (hA t ht)
  have hB3 : ¬ 3 ∣ Nat.card (blockImage W) := by
    intro h
    apply h3
    refine h.trans ?_
    have h1 : Nat.card (blockImage W) ∣ Nat.card (W.subgroupOf K0G) := Subgroup.card_map_dvd (W.subgroupOf K0G) actK
    have h2 : Nat.card (W.subgroupOf K0G) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv
    rw [h2] at h1
    exact h1
  have h8 : Nat.card (blockImage W) ∣ 8 := threePrime_card_dvd_eight hj _ hBA hB3 hinv
  have h2W : ∀ g ∈ W, ∃ n, g ^ (2 ^ n) = 1 := by
    intro g hg
    refine ⟨3, ?_⟩
    set k : K0G := ⟨g, hWK hg⟩
    have hkB : actK k ∈ blockImage W := mem_blockImage.2 ⟨k, hg, rfl⟩
    have hB8 : actK k ^ 8 = 1 := by
      have := pow_card_eq_one' (G := blockImage W) (x := ⟨actK k, hkB⟩)
      have h' : actK k ^ Nat.card (blockImage W) = 1 := congrArg Subtype.val this
      obtain ⟨c, hc⟩ := h8
      rw [hc, pow_mul, h', one_pow]
    have hk8 : actK (k ^ 8) = 1 := by rw [map_pow, hB8]
    obtain ⟨c, hc⟩ := zG_mem_ker (k ^ 8) hk8
    have hg8 : g ^ 8 ∈ W := pow_mem hg 8
    have hg83 : (g ^ 8) ^ 3 = 1 := by
      have : (g ^ 8 : GM) = zG ^ c := by
        have := hc
        simpa [k] using this
      rw [this, ← pow_mul, mul_comm, pow_mul, zG_pow_three, one_pow]
    have := eq_one_of_cube_of_not_dvd h3 hg8 hg83
    simpa using this
  exact K0_two_subgroups hj W hWK h2W hy

end K0

section Piece

set_option linter.unusedSectionVars false


theorem piece_threePrime {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) (S : Subgroup GM)
    (hS : ¬ 3 ∣ Nat.card S) (hA : AG j ≤ normalizer (S : Set GM)) :
    S ⊓ centralizer {mL j l} = ⊥ ∨ ∃ (m : ℕ) (hm : m < 3), S ⊓ centralizer {mL j l} =
      XG j l m hj hm := by
  set N := nL j l
  set W : Subgroup GM := (S ⊓ centralizer {mL j l}).map (MulAut.conj N).toMonoidHom with hW
  have hWc : W ≤ centralizer {xG 0} := by
    rw [hW]
    refine (map_mono inf_le_right).trans ?_
    rw [map_conj_centralizer, mL]
    intro k hk
    have e : N * (N⁻¹ * xG 0 * N) * N⁻¹ = xG 0 := by group
    rwa [e] at hk
  have hSc : Nat.Coprime 3 (Nat.card S) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hS
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h
    apply hS
    refine h.trans ?_
    rw [hW, Subgroup.card_map_of_injective (MulAut.conj N).injective]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hWK : W ≤ K0G := fun g hg => by
    obtain ⟨s, hs, rfl⟩ := hg
    refine mem_K0_of_coprime (hWc ⟨s, hs, rfl⟩) (n := Nat.card S) ?_ hSc
    have := pow_card_eq_one' (G := S) (x := ⟨s, hs.1⟩)
    have h' : s ^ Nat.card S = 1 := congrArg Subtype.val this
    show (N * s * N⁻¹) ^ Nat.card S = 1
    rw [conj_pow, h']; simp
  have hyW : ∀ g ∈ W, (yG j)⁻¹ * g * yG j ∈ W := by
    rintro _ ⟨s, hs, rfl⟩
    set y' := N⁻¹ * yG j * N with hy'
    have hy'A : y' ∈ AG j := conj_mem_AG hj hl (yG_mem_AG hj)
    have hy'n := hA hy'A
    have hs' : y'⁻¹ * s * y' ∈ S := by
      have := (mem_normalizer_iff.1 (hA (inv_mem hy'A)) s).1 hs.1
      simpa using this
    have hc : y'⁻¹ * s * y' ∈ centralizer {mL j l} := by
      have hm : Commute s (mL j l) := mem_centralizer_singleton_iff.1 hs.2
      have hyc : Commute y' (mL j l) := AG_comm hj hy'A (mL_mem_AG hj hl)
      rw [mem_centralizer_singleton_iff]
      exact ((hyc.inv_left.mul_left hm).mul_left hyc).eq
    refine ⟨y'⁻¹ * s * y', ⟨hs', hc⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hy']
    group
  have hback : S ⊓ centralizer {mL j l} = W.map (MulAut.conj N⁻¹).toMonoidHom := by
    rw [hW, map_map]
    conv_lhs => rw [← map_id (S ⊓ centralizer {mL j l})]
    congr 1
    refine MonoidHom.ext fun g => ?_
    simp [MulAut.conj_apply]
    group
  rcases K0_threePrime_subgroups hj W hWK hW3 hyW with hbot | ⟨m, hm, hV⟩
  · left
    rw [hback, hbot, Subgroup.map_bot]
  · right
    refine ⟨m, hm, ?_⟩
    rw [hback, hV]
    rfl

end Piece

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.ThreePrime
