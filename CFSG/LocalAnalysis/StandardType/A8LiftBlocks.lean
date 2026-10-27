module

public import CFSG.LocalAnalysis.StandardType.SpBlockMatrices

public section

namespace CFSG.StandardType

open Matrix

@[expose] def HasOrderSevenData (Γ : Type*) [Group Γ] : Prop :=
  ∃ x y : Γ, orderOf x = 7 ∧ y * x * y⁻¹ = x ^ 2 ∧ Subgroup.normalClosure ({x} : Set Γ) = ⊤

@[expose] def HasOrderFiveData (Γ : Type*) [Group Γ] : Prop :=
  ∃ x y : Γ, orderOf x = 5 ∧ y * x * y⁻¹ = x ^ 2 ∧ Subgroup.normalClosure ({x} : Set Γ) = ⊤

section Data

variable {J : Type*} [Group J] [Finite J]

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_orderOf_prime_conj_sq_normalClosure_of_central_ext (hJ : IsAlternatingEightCover J)
    (π : Γ →* J) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Γ)
    (hperf : commutator Γ = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hkill : ∀ z ∈ π.ker, z ^ p = 1 → z = 1) {x y : J} (hx : orderOf x = p)
    (hxy : y * x * y⁻¹ = x ^ 2) :
    ∃ x' y' : Γ, orderOf x' = p ∧ y' * x' * y'⁻¹ = x' ^ 2 ∧
      Subgroup.normalClosure ({x'} : Set Γ) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  let K := π.ker
  let m := Nat.card K
  have hp_notdvd : ¬ p ∣ m := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := K) p hdvd
    have hord : orderOf (z : Γ) = p := (Subgroup.orderOf_mk (z : Γ) z.2).symm.trans hz
    have hzpow : (z : Γ) ^ p = 1 := by rw [← hord, pow_orderOf_eq_one]
    have hz1 : (z : Γ) = 1 := hkill (z : Γ) z.2 hzpow
    have hzone : z = 1 := Subtype.ext hz1
    have h1 : orderOf z = 1 := orderOf_eq_one_iff.mpr hzone
    exact hp.ne_one (hz.symm.trans h1)
  have hcop : Nat.Coprime p m := (hp.coprime_iff_not_dvd).mpr hp_notdvd
  obtain ⟨t, ht1, ht2⟩ := Nat.chineseRemainder hcop 1 0
  have htmod : t % p = 1 := by
    have h := ht1
    rw [Nat.ModEq] at h
    rwa [Nat.mod_eq_of_lt hp.one_lt] at h
  have htdvd : m ∣ t := Nat.modEq_zero_iff_dvd.mp ht2
  obtain ⟨x₀, hx₀⟩ := hπ x
  obtain ⟨y₀, hy₀⟩ := hπ y
  have hat : x ^ t = x := by rw [← pow_mod_orderOf x t, hx, htmod, pow_one]
  have hπx : π (x₀ ^ t) = x := by rw [map_pow, hx₀, hat]
  have hx_ne : x ≠ 1 := by
    intro h
    exact hp.ne_one (hx.symm.trans (orderOf_eq_one_iff.mpr h))
  have hx₀_ne : x₀ ^ t ≠ 1 := by
    intro h
    exact hx_ne (by rw [← hπx, h, map_one])
  have hz0 : x₀ ^ p ∈ K := by
    rw [MonoidHom.mem_ker]
    show π (x₀ ^ p) = 1
    rw [map_pow, hx₀, ← hx]
    exact pow_orderOf_eq_one x
  have hz0pow : (x₀ ^ p) ^ m = 1 := by
    have h : (⟨x₀ ^ p, hz0⟩ : K) ^ m = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  have hx_pow : (x₀ ^ t) ^ p = 1 := by
    obtain ⟨s, hs⟩ := htdvd
    rw [← pow_mul, mul_comm t p, pow_mul, hs, pow_mul, hz0pow, one_pow]
  let w := ((x₀ ^ t) ^ 2)⁻¹ * (y₀ * (x₀ ^ t) * y₀⁻¹)
  have hwK : w ∈ K := by
    rw [MonoidHom.mem_ker]
    show π (((x₀ ^ t) ^ 2)⁻¹ * (y₀ * (x₀ ^ t) * y₀⁻¹)) = 1
    simp only [map_mul, map_pow, map_inv, hπx, hy₀, hxy]
    group
  have hyx : y₀ * (x₀ ^ t) * y₀⁻¹ = (x₀ ^ t) ^ 2 * w := by
    dsimp only [w]
    group
  have hcomm : Commute ((x₀ ^ t) ^ 2) w :=
    Subgroup.mem_center_iff.mp (hker hwK) ((x₀ ^ t) ^ 2)
  have hwp : w ^ p = 1 := by
    have hconj : (y₀ * (x₀ ^ t) * y₀⁻¹) ^ p = 1 := by
      rw [conj_pow, hx_pow]
      simp
    have h1 : ((x₀ ^ t) ^ 2 * w) ^ p = 1 := by rw [← hyx]; exact hconj
    rw [hcomm.mul_pow] at h1
    have hx2 : ((x₀ ^ t) ^ 2) ^ p = 1 := by
      rw [← pow_mul, mul_comm 2 p, pow_mul, hx_pow, one_pow]
    rwa [hx2, one_mul] at h1
  have hw1 : w = 1 := hkill w hwK hwp
  have hconj : y₀ * (x₀ ^ t) * y₀⁻¹ = (x₀ ^ t) ^ 2 := by
    rw [hyx, hw1, mul_one]
  let N := Subgroup.normalClosure ({x₀ ^ t} : Set Γ)
  have hxmem : x ∈ N.map π := by
    rw [Subgroup.mem_map]
    exact ⟨x₀ ^ t, Subgroup.subset_normalClosure (Set.mem_singleton _), hπx⟩
  have hNnotle : ¬ N.map π ≤ Subgroup.center J := by
    intro hle
    have hxc : x ∈ Subgroup.center J := hle hxmem
    have h2 : ∃ k, orderOf x = 2 ^ k := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hJ.2.2) (⟨x, hxc⟩ : Subgroup.center J)
      exact ⟨k, (Subgroup.orderOf_mk x hxc).symm.trans hk⟩
    obtain ⟨k, hk⟩ := h2
    have hdvd : p ∣ 2 ^ k := by
      rw [← hx, hk]
    have hp_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
    exact hp2 hp_eq
  have hNnormal : (N.map π).Normal :=
    (Subgroup.normalClosure_normal (s := ({x₀ ^ t} : Set Γ))).map π hπ
  have hNtop : N.map π = ⊤ :=
    IsAlternatingEightCover.eq_top_of_normal hJ (N := N.map π) hNnormal hNnotle
  have hsup : N ⊔ π.ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hgm : π g ∈ N.map π := by rw [hNtop]; trivial
    obtain ⟨n, hnN, hn⟩ := Subgroup.mem_map.mp hgm
    have hz : n⁻¹ * g ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      show π (n⁻¹ * g) = 1
      rw [map_mul, map_inv, hn, inv_mul_cancel]
    have hg : g = n * (n⁻¹ * g) := by group
    rw [hg]
    exact Subgroup.mul_mem_sup hnN hz
  haveI : IsMulCommutative ↥π.ker :=
    { is_comm :=
        { comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hker b.2) (a : Γ)) } }
  have hle : commutator Γ ≤ N :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := N) hsup inferInstance
  have hNtop' : N = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact hle (by rw [hperf]; trivial)
  exact ⟨x₀ ^ t, y₀, orderOf_eq_prime hx_pow hx₀_ne, hconj, hNtop'⟩

theorem hasOrderSevenData_of_central_ext (hJ : IsAlternatingEightCover J) (π : Γ →* J)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Γ) (hperf : commutator Γ = ⊤)
    (h7 : ∀ z ∈ π.ker, z ^ 7 = 1 → z = 1) : HasOrderSevenData Γ := by
  obtain ⟨x, y, hx, hxy⟩ := hJ.exists_orderOf_seven_conj_sq
  obtain ⟨x', y', h1, h2, h3⟩ :=
    exists_orderOf_prime_conj_sq_normalClosure_of_central_ext (p := 7) hJ π hπ hker hperf
      (by decide) (by decide) h7 hx hxy
  exact ⟨x', y', h1, h2, h3⟩

theorem hasOrderFiveData_of_central_ext (hJ : IsAlternatingEightCover J) (π : Γ →* J)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Γ) (hperf : commutator Γ = ⊤)
    (h5 : ∀ z ∈ π.ker, z ^ 5 = 1 → z = 1) : HasOrderFiveData Γ := by
  obtain ⟨x, y, hx, hxy⟩ := hJ.exists_orderOf_five_conj_sq
  obtain ⟨x', y', h1, h2, h3⟩ :=
    exists_orderOf_prime_conj_sq_normalClosure_of_central_ext (p := 5) hJ π hπ hker hperf
      (by decide) (by decide) h5 hx hxy
  exact ⟨x', y', h1, h2, h3⟩

end Data

section Small

variable {Γ : Type*} [Group Γ] [Finite Γ] {E : Type*} [Field E] [IsAlgClosed E] [CharP E 2]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem HasOrderFiveData.map_eq_one_of_card_le_three (h : HasOrderFiveData Γ)
    (hι : Fintype.card ι ≤ 3) (ρ : Γ →* Matrix ι ι E) (g : Γ) : ρ g = 1 := by
  obtain ⟨x, y, hx, hxy, htop⟩ := h
  have hX : ρ x ^ 5 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hY : IsUnit (ρ y) := (Group.isUnit y).map ρ
  have h1 : ρ x = 1 :=
    OrderFiveSeven.eq_one_of_pow_five_of_card_le_three hι hY (map_conj_sq_aux ρ hxy) hX
  let K := (ρ.toHomUnits).ker
  have hKx : x ∈ K := by
    rw [MonoidHom.mem_ker]
    exact Units.ext (by rw [MonoidHom.coe_toHomUnits, h1, Units.val_one])
  have hle : Subgroup.normalClosure ({x} : Set Γ) ≤ K :=
    Subgroup.normalClosure_le_normal (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      simpa [hz] using hKx)
  have hKtop : K = ⊤ := by
    rw [htop] at hle
    exact le_antisymm le_top hle
  have hKg : g ∈ K := by rw [hKtop]; trivial
  have h1' : ρ.toHomUnits g = 1 := hKg
  have : (ρ.toHomUnits g : Matrix ι ι E) = ((1 : (Matrix ι ι E)ˣ) : Matrix ι ι E) :=
    congrArg Units.val h1'
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this

theorem HasOrderSevenData.map_eq_one_of_card_le_five_of_form (h : HasOrderSevenData Γ)
    (σ : E ≃+* E) (hσ : ∀ η : E, η ^ 7 = 1 → ∃ k : ℕ, σ η = η ^ 2 ^ k) {G : Matrix ι ι E}
    (hG : IsUnit G) (hι : Fintype.card ι ≤ 5) (ρ : Γ →* Matrix ι ι E)
    (hρ : ∀ g, (ρ g)ᵀ * G * (ρ g).map σ = G) (g : Γ) : ρ g = 1 := by
  obtain ⟨x, y, hx, hxy, htop⟩ := h
  have hX : ρ x ^ 7 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hY : IsUnit (ρ y) := (Group.isUnit y).map ρ
  have h1 : ρ x = 1 :=
    OrderFiveSeven.eq_one_of_pow_seven_of_form σ hσ hG hι hY (map_conj_sq_aux ρ hxy) hX (hρ x)
  let K := (ρ.toHomUnits).ker
  have hKx : x ∈ K := by
    rw [MonoidHom.mem_ker]
    exact Units.ext (by rw [MonoidHom.coe_toHomUnits, h1, Units.val_one])
  have hle : Subgroup.normalClosure ({x} : Set Γ) ≤ K :=
    Subgroup.normalClosure_le_normal (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      simpa [hz] using hKx)
  have hKtop : K = ⊤ := by
    rw [htop] at hle
    exact le_antisymm le_top hle
  have hKg : g ∈ K := by rw [hKtop]; trivial
  have h1' : ρ.toHomUnits g = 1 := hKg
  have : (ρ.toHomUnits g : Matrix ι ι E) = ((1 : (Matrix ι ι E)ˣ) : Matrix ι ι E) :=
    congrArg Units.val h1'
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this

end Small

namespace SpBlocks

variable {Γ : Type*} [Group Γ] [Finite Γ] {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem HasOrderFiveData.blk_eq_one_of_card_le_three (h : HasOrderFiveData Γ) (I : Finset ι)
    (Q : Γ →* Matrix ι ι Ω) (hQ : ∀ g, Splits I (Q g)) (hI : I.card ≤ 3) (g : Γ) :
    blk I (Q g) = 1 := by
  have hcard : Fintype.card ↥I ≤ 3 := by
    rw [Fintype.card_coe]
    exact hI
  have hh := HasOrderFiveData.map_eq_one_of_card_le_three h hcard (blkHom I Q hQ) g
  rw [blkHom_apply] at hh
  exact hh

theorem HasOrderSevenData.blk_eq_one_of_card_le_five (h : HasOrderSevenData Γ) (I : Finset ι)
    (Q : Γ →* Matrix ι ι Ω) (hQ : ∀ g, Splits I (Q g)) (σ : Ω ≃+* Ω)
    (hσ : ∀ η : Ω, η ^ 7 = 1 → ∃ k : ℕ, σ η = η ^ 2 ^ k) {H : Matrix ι ι Ω} (hH : Splits I H)
    (hHu : IsUnit H) (hform : ∀ g, (Q g)ᵀ * H * (Q g).map σ = H) (hI : I.card ≤ 5) (g : Γ) :
    blk I (Q g) = 1 := by
  have hcard : Fintype.card ↥I ≤ 5 := by
    rw [Fintype.card_coe]
    exact hI
  have hρ : ∀ g, ((blkHom I Q hQ) g)ᵀ * blk I H * ((blkHom I Q hQ) g).map σ = blk I H := by
    intro g
    have h1 : blk I ((Q g)ᵀ * H * (Q g).map σ) = blk I H := congrArg (blk I) (hform g)
    have h2 : blk I ((Q g)ᵀ) * blk I H * blk I ((Q g).map σ) = blk I H := by
      rw [← (hQ g).transpose.blk_mul H, ← ((hQ g).transpose.mul hH).blk_mul ((Q g).map σ)]
      exact h1
    change (blk I (Q g))ᵀ * blk I H * (blk I (Q g)).map (σ : Ω →+* Ω) = blk I H
    rw [← blk_transpose (Q g), ← blk_map (Q g) (σ : Ω →+* Ω)]
    exact h2
  have hh := HasOrderSevenData.map_eq_one_of_card_le_five_of_form h σ hσ
      (G := blk I H) (hH.isUnit_blk hHu) hcard (blkHom I Q hQ) hρ g
  rw [blkHom_apply] at hh
  exact hh

theorem eq_one_of_forall_blk_eq_one {κ : Type*} [DecidableEq κ] {K : Type*} [Field K]
    (c : ι → κ) (M : Matrix ι ι K) (hs : ∀ k, Splits (Finset.univ.filter fun a => c a = k) M)
    (h1 : ∀ k, blk (Finset.univ.filter fun a => c a = k) M = 1) : M = 1 := by
  ext a b
  by_cases hc : c a = c b
  · let F := Finset.univ.filter (fun x => c x = c a)
    have ha : a ∈ F := by simp [F]
    have hb : b ∈ F := by simp [F, hc.symm]
    have h := congr_fun (congr_fun (h1 (c a)) ⟨a, ha⟩) ⟨b, hb⟩
    simp only [blk, Matrix.submatrix_apply] at h
    rw [h, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · have hsub : (⟨a, ha⟩ : F) = ⟨b, hb⟩ := Subtype.ext hab
      rw [if_pos hsub, if_pos hab]
    · have hne : ¬ (⟨a, ha⟩ : F) = ⟨b, hb⟩ := fun hh => hab (Subtype.ext_iff.mp hh)
      rw [if_neg hne, if_neg hab]
  · let F := Finset.univ.filter (fun x => c x = c a)
    have ha : a ∈ F := by simp [F]
    have hb : b ∉ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hc h.symm
    have hzero : M a b = 0 := hs (c a) a b ⟨fun _ => hb, fun _ => ha⟩
    rw [hzero, Matrix.one_apply, if_neg (fun hab => hc (by rw [hab]))]

end SpBlocks

end CFSG.StandardType
