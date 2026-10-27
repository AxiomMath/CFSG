module

public import CFSG.Quasithin.EmptyFaithful.Insp7RedB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Insp7

theorem card_of_extQ8SqS3S3 {P : Type*} [Group P] [Finite P] (h : S143.ExtQ8SqS3S3 P) :
    Nat.card P = 1152 := by
  obtain ⟨ψ, hψs, hq, -⟩ := h
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [hq.1, MonoidHom.range_eq_top.mpr hψs, Subgroup.card_top] at h1
  have h2 : Nat.card (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = 36 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [h2] at h1
  omega

theorem two_pow_mul_odd_eq {k m s : ℕ} (hs : ¬ 2 ∣ s) (h : 2 ^ k * s = 2 ^ m * 9) :
    k = m ∧ s = 9 := by
  have hk : k = m := by
    have h1 := congrArg (padicValNat 2) h
    rw [padicValNat.mul (by positivity) (by rintro rfl; simp at hs),
      padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hs,
      padicValNat.eq_zero_of_not_dvd (by norm_num)] at h1
    simpa using h1
  subst hk
  refine ⟨rfl, ?_⟩
  have h2 : 2 ^ k * s = 2 ^ k * 9 := h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h2


@[expose] def InspAt (F : ∀ (L : Type) [Group L], Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
    ∀ z : L, z * z = 1 → z ∉ Subgroup.center L →
      ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L), Function.Injective ρ →
        (∀ l : L, MulAut.conj l ∈ ρ.range) →
        ∀ ž : Gc, ρ ž = MulAut.conj z →
          ∀ Ŝ : Subgroup Gc, IsPGroup 2 Ŝ → ¬ 2 ∣ Ŝ.index →
            Ŝ ≤ Subgroup.centralizer ({ž} : Set Gc) →
            ∀ P : Subgroup Gc, P ≤ Subgroup.centralizer ({ž} : Set Gc) →
              P.relIndex (Subgroup.centralizer ({ž} : Set Gc)) ≤ 2 → ¬ S143.ExtQ8SqS3S3 ↥P

theorem inspNum_iff : InspNum ↔ InspAt ListCases := Iff.rfl

@[expose] def NumFactAt (F : ∀ (L : Type) [Group L], Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
    ∀ z : L, z * z = 1 → z ∉ Subgroup.center L →
      ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L), Function.Injective ρ →
        (∀ l : L, MulAut.conj l ∈ ρ.range) →
        ∀ ž : Gc, ρ ž = MulAut.conj z →
          ∀ Ŝ : Subgroup Gc, IsPGroup 2 Ŝ → ¬ 2 ∣ Ŝ.index →
            Ŝ ≤ Subgroup.centralizer ({ž} : Set Gc) →
            (Nat.card Ŝ = 2 ^ 7 ∨ Nat.card Ŝ = 2 ^ 8) →
              Nat.card (Subgroup.centralizer ({ž} : Set Gc)) ≠ 9 * Nat.card Ŝ

theorem inspAt_of_numFactAt {F : ∀ (L : Type) [Group L], Prop} (h : NumFactAt F) : InspAt F := by
  intro L _ _ hq hF z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC P hPC hrel hext
  have hP1152 : Nat.card P = 1152 := card_of_extQ8SqS3S3 hext
  have hCP : Nat.card (Subgroup.centralizer ({ž} : Set Gc)) =
      Nat.card P * P.relIndex (Subgroup.centralizer ({ž} : Set Gc)) := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf (Subgroup.centralizer ({ž} : Set Gc)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv] at h1
    exact h1.symm
  have hCS : Nat.card (Subgroup.centralizer ({ž} : Set Gc)) =
      Nat.card Ŝ * Ŝ.relIndex (Subgroup.centralizer ({ž} : Set Gc)) := by
    have h1 := Subgroup.card_mul_index (Ŝ.subgroupOf (Subgroup.centralizer ({ž} : Set Gc)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hŜC).toEquiv] at h1
    exact h1.symm
  have hSodd : ¬ 2 ∣ Ŝ.relIndex (Subgroup.centralizer ({ž} : Set Gc)) := fun h2 =>
    hŜodd (h2.trans (Subgroup.relIndex_dvd_index_of_le hŜC))
  have hCpos : 0 < Nat.card (Subgroup.centralizer ({ž} : Set Gc)) := Nat.card_pos
  have hrpos : 0 < P.relIndex (Subgroup.centralizer ({ž} : Set Gc)) := by
    rcases Nat.eq_zero_or_pos (P.relIndex (Subgroup.centralizer ({ž} : Set Gc))) with h0 | h0
    · rw [h0, mul_zero] at hCP; omega
    · exact h0
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hŜ2
  set r := P.relIndex (Subgroup.centralizer ({ž} : Set Gc)) with hr
  set s := Ŝ.relIndex (Subgroup.centralizer ({ž} : Set Gc)) with hs
  have hcase : (r = 1 ∧ Nat.card (Subgroup.centralizer ({ž} : Set Gc)) = 2 ^ 7 * 9) ∨
      (r = 2 ∧ Nat.card (Subgroup.centralizer ({ž} : Set Gc)) = 2 ^ 8 * 9) := by
    rcases (by omega : r = 1 ∨ r = 2) with h1 | h1
    · left; refine ⟨h1, ?_⟩; rw [hCP, hP1152, h1]; norm_num
    · right; refine ⟨h1, ?_⟩; rw [hCP, hP1152, h1]; norm_num
  rcases hcase with ⟨-, hC⟩ | ⟨-, hC⟩
  · have h1 : 2 ^ k * s = 2 ^ 7 * 9 := by rw [← hk, ← hC, hCS]
    obtain ⟨hk7, hs9⟩ := two_pow_mul_odd_eq hSodd h1
    refine h L hq hF z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC (Or.inl (by rw [hk, hk7])) ?_
    rw [hCS, hs9, mul_comm]
  · have h1 : 2 ^ k * s = 2 ^ 8 * 9 := by rw [← hk, ← hC, hCS]
    obtain ⟨hk8, hs9⟩ := two_pow_mul_odd_eq hSodd h1
    refine h L hq hF z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC (Or.inr (by rw [hk, hk8])) ?_
    rw [hCS, hs9, mul_comm]


theorem ker_conj_eq_center (L : Type) [Group L] :
    (MulAut.conj : L →* MulAut L).ker = Subgroup.center L := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h y
    have := congrArg (fun m : MulAut L => m y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * x = (x * y * x⁻¹) * x := by rw [this]
      _ = x * y := by group
  · intro h
    ext y
    simp only [MulAut.conj_apply, MulAut.one_apply]
    calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [h y]
      _ = y := by group

theorem numFactAt_of_big {F : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      2 ^ 9 ∣ Nat.card (L ⧸ Subgroup.center L)) : NumFactAt F := by
  intro L _ _ hq hFL z _ _ Gc _ _ ρ hρ hinn ž _ Ŝ _ hŜodd _ hcard
  exfalso
  have h9 := hF L hq hFL
  have hInn : (MulAut.conj : L →* MulAut L).range ≤ ρ.range := by
    rintro _ ⟨l, rfl⟩
    exact hinn l
  have h1 : Nat.card (MulAut.conj : L →* MulAut L).range ∣ Nat.card ρ.range :=
    Subgroup.card_dvd_of_le hInn
  have h2 : Nat.card (MulAut.conj : L →* MulAut L).range = Nat.card (L ⧸ Subgroup.center L) := by
    rw [← ker_conj_eq_center]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L)).toEquiv).symm
  have h3 : Nat.card ρ.range = Nat.card Gc := Nat.card_range_of_injective hρ
  rw [h2, h3] at h1
  have h4 := h9.trans h1
  have h5 := Subgroup.card_mul_index Ŝ
  rcases hcard with hc | hc
  · rw [← h5, hc] at h4
    have : 2 ^ 2 ∣ Ŝ.index := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ 7)).mp
      (by simpa [← pow_add] using h4)
    exact hŜodd (dvd_trans (dvd_pow_self 2 (by norm_num)) this)
  · rw [← h5, hc] at h4
    have : 2 ∣ Ŝ.index := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ 8)).mp
      (by simpa [← pow_add] using h4)
    exact hŜodd this

end Insp7

end CFSG.Quasithin
