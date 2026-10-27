module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7RM
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D}

omit [Finite D] in
theorem eq_one_of_pow_two_of_odd {x : D} {o j : ℕ} (hodd : Odd o) (h2 : x ^ (2 ^ j) = 1)
    (ho : x ^ o = 1) : x = 1 := by
  have h3 : orderOf x ∣ Nat.gcd (2 ^ j) o :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one ho)
  have hc : Nat.Coprime (2 ^ j) o := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  rw [hc.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

section CB

variable (h : GoldHyp A B) (hne : pCoreOf 2 A ≠ pCoreOf 2 B)
  (hN : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))

include h hne hN

theorem eq_one_of_odd_centralizer {x : D} (hxB : x ∈ B)
    (hxC : x ∈ Subgroup.centralizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D)) {o : ℕ}
    (hodd : Odd o) (ho : x ^ o = 1) : x = 1 := by
  set R : Subgroup D := pCoreOf 2 A ⊓ pCoreOf 2 B with hR
  have hR2 : IsPGroup 2 R := (pCoreOf_isPGroup 2 A : IsPGroup 2 (pCoreOf 2 A)).to_le inf_le_left
  have hidx := relIndex_inf_pCoreOf_right' h hne
  have hxR : ∀ w ∈ R, x * w * x⁻¹ = w := fun w hw => by
    have := Subgroup.mem_centralizer_iff.mp hxC w hw
    rw [← this]
    group
  have hcent : ∀ q ∈ pCoreOf 2 B, x * q * x⁻¹ = q := by
    intro q hq
    set r : D := x * q * x⁻¹ * q⁻¹ with hr
    have hrR : r ∈ R := conj_mul_inv_mem_of_relIndex_two hidx (hN hxB)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B hxB) y).mp hy) hq
    have hpow : ∀ k : ℕ, x ^ k * q * (x ^ k)⁻¹ = r ^ k * q := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e1 : x ^ (k + 1) * q * (x ^ (k + 1))⁻¹ = x * (x ^ k * q * (x ^ k)⁻¹) * x⁻¹ := by
          rw [pow_succ']; group
        rw [e1, ih]
        have e2 : x * (r ^ k * q) * x⁻¹ = (x * r ^ k * x⁻¹) * (x * q * x⁻¹) := by group
        have e3 : x * q * x⁻¹ = r * q := by rw [hr]; group
        rw [e2, hxR _ (R.pow_mem hrR k), e3, pow_succ]
        group
    have hr1 : r = 1 := by
      have h1 := hpow o
      rw [ho] at h1
      simp only [one_mul, inv_one, mul_one] at h1
      have h2 : r ^ o = 1 := by
        have := mul_right_cancel (h1.symm.trans (one_mul q).symm)
        exact this
      obtain ⟨j, hj⟩ := hR2 ⟨r, hrR⟩
      exact eq_one_of_pow_two_of_odd hodd (congrArg Subtype.val hj) h2
    have : x * q * x⁻¹ * q⁻¹ = 1 := hr1
    exact (mul_inv_eq_one.mp this)
  have hxQ : x ∈ pCoreOf 2 B := h.vertex_right.charTwo ⟨hxB, Subgroup.mem_centralizer_iff.mpr
    fun q hq => (mul_eq_of_conj_eq (hcent q hq)).symm⟩
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 B : IsPGroup 2 (pCoreOf 2 B)) ⟨x, hxQ⟩
  exact eq_one_of_pow_two_of_odd hodd (congrArg Subtype.val hj) ho

theorem inf_centralizer_le_pCoreOf_right :
    B ⊓ Subgroup.centralizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) ≤ pCoreOf 2 B := by
  set R : Subgroup D := pCoreOf 2 A ⊓ pCoreOf 2 B with hR
  set K : Subgroup D := B ⊓ Subgroup.centralizer (R : Set D) with hK
  have hK2 : IsPGroup 2 K := by
    rintro ⟨g, hg⟩
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    refine ⟨a, Subtype.ext ?_⟩
    have hg' : g ^ 2 ^ a ∈ K := K.pow_mem hg _
    have hb1 : (g ^ 2 ^ a) ^ b = 1 := by
      rw [← pow_mul, ← hab]
      exact pow_orderOf_eq_one g
    have := eq_one_of_odd_centralizer h hne hN hg'.1 hg'.2 hb hb1
    simpa using this
  have hKn : B ≤ Subgroup.normalizer (K : Set D) := by
    refine le_normalizer_of_forall fun b hb x hx => ⟨B.mul_mem (B.mul_mem hb hx.1) (B.inv_mem hb),
      Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have hr' : b⁻¹ * r * b ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hN (B.inv_mem hb)) r).mp hr
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hr'
    calc r * (b * x * b⁻¹) = b * ((b⁻¹ * r * b) * x) * b⁻¹ := by group
      _ = b * (x * (b⁻¹ * r * b)) * b⁻¹ := by rw [hc]
      _ = (b * x * b⁻¹) * r := by group
  exact le_pCoreOf_of_normalizes inf_le_left hKn hK2

end CB

section RH

variable (h : GoldHyp A B) (hne : pCoreOf 2 A ≠ pCoreOf 2 B)
  (hN : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))
  {y : D} (hy : y ∈ B) (hy3 : orderOf y = 3)

include h hne hN hy hy3

theorem pCoreOf_rH :
    pCoreOf 2 (((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y) ⊔ pCoreOf 2 A) =
      pCoreOf 2 A ⊓ pCoreOf 2 B := by
  set R : Subgroup D := pCoreOf 2 A ⊓ pCoreOf 2 B with hR
  set M : Subgroup D := R ⊔ Subgroup.zpowers y with hM
  set H : Subgroup D := M ⊔ pCoreOf 2 A with hH
  have hR2 : IsPGroup 2 R := (pCoreOf_isPGroup 2 A : IsPGroup 2 (pCoreOf 2 A)).to_le inf_le_left
  have hRH : R ≤ H := le_sup_left.trans le_sup_left
  have hHN : H ≤ Subgroup.normalizer (R : Set D) := (sup_zpowers_sup_le h hy).trans hN
  have hRP : R ≤ pCoreOf 2 H := le_pCoreOf_of_normalizes hRH hHN hR2
  have hidx : ((pCoreOf 2 A).subgroupOf H).index = 3 := relIndex_pCoreOf_sup h hne hN hy hy3
  have hsyl : IsSylowTwoOf (pCoreOf 2 A) H :=
    ⟨le_sup_right, pCoreOf_isPGroup 2 A, by rw [hidx]; norm_num⟩
  have hPQ : pCoreOf 2 H ≤ pCoreOf 2 A := isSylowTwoOf_pCoreOf_le hsyl
  have h1 := Subgroup.relIndex_mul_relIndex R (pCoreOf 2 H) (pCoreOf 2 A) hRP hPQ
  rw [relIndex_inf_pCoreOf_left' h hne] at h1
  have hd : R.relIndex (pCoreOf 2 H) ∣ 2 := Dvd.intro _ h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h2 | h2
  · exact (Subgroup.relIndex_eq_one.mp h2).antisymm hRP
  · exfalso
    have h3 : (pCoreOf 2 H).relIndex (pCoreOf 2 A) = 1 := by
      rw [h2] at h1
      omega
    have h4 : pCoreOf 2 A ≤ pCoreOf 2 H := Subgroup.relIndex_eq_one.mp h3
    apply not_le_normalizer_sup h hne hy hy3
    have h5 : pCoreOf 2 H = pCoreOf 2 A := le_antisymm hPQ h4
    have h6 := le_normalizer_pCoreOf 2 H
    rw [h5] at h6
    exact h6

theorem charTwo_rH :
    CharTwo (((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y) ⊔ pCoreOf 2 A) := by
  set R : Subgroup D := pCoreOf 2 A ⊓ pCoreOf 2 B with hR
  set M : Subgroup D := R ⊔ Subgroup.zpowers y with hM
  set H : Subgroup D := M ⊔ pCoreOf 2 A with hH
  have hHB : H ≤ B := sup_zpowers_sup_le h hy
  have hK2 : IsPGroup 2 (H ⊓ pCoreOf 2 B : Subgroup D) :=
    (pCoreOf_isPGroup 2 B : IsPGroup 2 (pCoreOf 2 B)).to_le inf_le_right
  have hKn : H ≤ Subgroup.normalizer ((H ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
    refine le_normalizer_of_forall fun t ht m hm => ⟨H.mul_mem (H.mul_mem ht hm.1)
      (H.inv_mem ht), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B (hHB ht)) m).mp hm.2
  have hle : H ⊓ pCoreOf 2 B ≤ pCoreOf 2 H := le_pCoreOf_of_normalizes inf_le_left hKn hK2
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (R : Set D) := by
    have := hx.2
    rwa [pCoreOf_rH h hne hN hy hy3] at this
  exact hle ⟨hx.1, inf_centralizer_le_pCoreOf_right h hne hN ⟨hHB hx.1, hxC⟩⟩

omit hne hN in
theorem noCharNormal_rH (C : Subgroup D) (hCS : C ≤ pCoreOf 2 A) (hC0 : C ≠ ⊥)
    (hchar : (C.subgroupOf (pCoreOf 2 A)).Characteristic) :
    ¬ ((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ Subgroup.zpowers y) ⊔ pCoreOf 2 A ≤
      Subgroup.normalizer (C : Set D) := by
  intro hHC
  have hAC : A ≤ Subgroup.normalizer (C : Set D) := fun a ha =>
    normalizer_le_normalizer_of_characteristic hCS hchar (le_normalizer_pCoreOf 2 A ha)
  have hyC : y ∈ Subgroup.normalizer (C : Set D) :=
    hHC (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
  have hBC : B ≤ Subgroup.normalizer (C : Set D) := by
    have := GoldAmN.inf_sup_zpowers_eq_right_vTriple h.amalgam.toIsGoldschmidtVTriple hy hy3
    rw [← this]
    exact sup_le (inf_le_left.trans hAC) (Subgroup.zpowers_le.mpr hyC)
  exact hC0 (h.eq_bot_of_normalizes hAC hBC (hCS.trans h.pCoreOf_left_le))

end RH

end GoldAmLab7

end F6

end CFSG.Quasithin
