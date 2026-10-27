module

public import CFSG.RankThree.GF2n.Smith81.Sec220Defs
public import CFSG.RankThree.GF2n.Smith81.Sec220TvLemmas
public import CFSG.RankThree.GF2n.Stroth80.Sec12MixedRoot
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_comm_eq_of_mem_Qv [Finite G] {M Q Z : Subgroup G}
    {v : G} (Hs : StrothHyp M Q Z) (hvH : v ∈ H0 M Z) (hk_odd : Odd (orderOf v)) {t : G}
    (htQv : t ∈ Qv Q v) (htZ : t ∉ Z) {z₀ : G} (hz₀ : z₀ ∈ Z) :
    ∃ x ∈ Qv Q v, ⁅x, t⁆ = z₀ := by
  have htQ : t ∈ Q := htQv.1
  have htv : t * v = v * t := mem_Cv.mp htQv.2
  have hvN : v ∈ Subgroup.normalizer (Q : Set G) := Hs.Q_normal.2 hvH.1
  have hQ2 : IsPGroup 2 Q := isPGroup_Q' Hs
  obtain ⟨m, γ, M₀, -, hD⟩ := stroth_globalModelDataGF Hs
  have hvZ : ∀ a ∈ Z, v * a * v⁻¹ = a := by
    intro a ha
    have hav : a * v = v * a := Subgroup.mem_centralizer_iff.mp hvH.2 a ha
    rw [← hav]
    group
  obtain ⟨T, hTπ, -, hTB⟩ := hD.linear_of_centralizes hvH.1 hvZ
  have R := hD.reg
  have hvQ : ∀ j : ℕ, ∀ x ∈ Q, v ^ j * x * (v ^ j)⁻¹ ∈ Q := by
    intro j x hx
    have hvj : v ^ j ∈ Subgroup.normalizer (Q : Set G) := Subgroup.pow_mem _ hvN j
    exact (Subgroup.mem_normalizer_iff.mp hvj x).mp hx
  set et := M₀.π t with het
  have het0 : et ≠ 0 := fun h0 => htZ ((M₀.π_ker t htQ).mp h0)
  have hTt : T et = et := by
    rw [het, ← hTπ t htQ]
    congr 1
    rw [← htv]
    group
  set k := orderOf v with hk
  have hk1 : (k : GaloisField 2 m) = 1 := by
    rw [CharTwo.natCast_eq_ite, if_neg (Nat.not_even_iff_odd.mpr hk_odd)]
  have hiter : ∀ j : ℕ, ∀ x ∈ Q, (⇑T)^[j] (M₀.π x) = M₀.π (v ^ j * x * (v ^ j)⁻¹) := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply', ih x hx, ← hTπ _ (hvQ j x hx)]
      congr 1
      rw [pow_succ']
      group
  have hTk : ∀ e, (⇑T)^[k] e = e := by
    intro e
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    rw [hiter k x hx, hk, pow_orderOf_eq_one]
    congr 1
    group
  obtain ⟨f, hf⟩ : ∃ f, M₀.B f et ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact het0 (M₀.nondeg et fun f => by rw [Tim79.QuadModel.B_comm, hcon f, neg_zero])
  set e₁ := ∑ j ∈ Finset.range k, (⇑T)^[j] f with he₁
  have hTe₁ : T e₁ = e₁ := by
    have hsum : ∑ j ∈ Finset.range k, T ((⇑T)^[j] f) =
        ∑ j ∈ Finset.range k, (⇑T)^[j + 1] f :=
      Finset.sum_congr rfl fun j _ => (Function.iterate_succ_apply' (⇑T) j f).symm
    have h1 := Finset.sum_range_succ' (fun j => (⇑T)^[j] f) k
    have h2 := Finset.sum_range_succ (fun j => (⇑T)^[j] f) k
    rw [hTk f] at h2
    simp only [Function.iterate_zero_apply] at h1
    rw [he₁, map_sum, hsum]
    exact add_right_cancel (h1.symm.trans h2)
  have hB : ∀ j : ℕ, M₀.B ((⇑T)^[j] f) et = M₀.B f et := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      calc M₀.B ((⇑T)^[j + 1] f) et = M₀.B (T ((⇑T)^[j] f)) (T et) := by
            rw [Function.iterate_succ_apply', hTt]
        _ = M₀.B ((⇑T)^[j] f) et := hTB _ _
        _ = M₀.B f et := ih
  have hBe₁ : M₀.B e₁ et = M₀.B f et := by
    rw [he₁, map_sum, LinearMap.sum_apply]
    simp only [hB, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul (GaloisField 2 m), hk1, one_smul]
  set e₂ := (γ z₀ / M₀.B e₁ et) • e₁ with he₂
  have hTe₂ : T e₂ = e₂ := by rw [he₂, map_smul, hTe₁]
  have hBe₂ : M₀.B e₂ et = γ z₀ := by
    rw [he₂, map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ (hBe₁ ▸ hf)]
  obtain ⟨x, hxQ, hx⟩ := M₀.π_surj e₂
  have hvxQ : v * x * v⁻¹ ∈ Q := by simpa using hvQ 1 x hxQ
  have hπx : M₀.π (v * x * v⁻¹) = M₀.π x := by rw [hTπ x hxQ, hx, hTe₂]
  have hd : (v * x * v⁻¹)⁻¹ * x ∈ Z := (M₀.pi_eq_iff hvxQ hxQ).mp hπx
  set d := x⁻¹ * (v * x * v⁻¹) with hd_def
  have hdZ : d ∈ Z := by
    have : d = ((v * x * v⁻¹)⁻¹ * x)⁻¹ := by rw [hd_def]; group
    rw [this]
    exact Z.inv_mem hd
  have hvd : v * d * v⁻¹ = d := hvZ d hdZ
  have hvd' : Commute v d := by
    show v * d = d * v
    calc v * d = (v * d * v⁻¹) * v := by group
      _ = d * v := by rw [hvd]
  have hxd : x * d = v * x * v⁻¹ := by rw [hd_def]; group
  have hpowd : ∀ j : ℕ, v ^ j * x * (v ^ j)⁻¹ = x * d ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : v * d ^ j = d ^ j * v := (hvd'.pow_right j).eq
      calc v ^ (j + 1) * x * (v ^ (j + 1))⁻¹ = v * (v ^ j * x * (v ^ j)⁻¹) * v⁻¹ := by
            rw [pow_succ']
            group
        _ = v * (x * d ^ j) * v⁻¹ := by rw [ih]
        _ = (v * x * v⁻¹) * (v * d ^ j) * v⁻¹ := by group
        _ = (v * x * v⁻¹) * d ^ j := by rw [hc]; group
        _ = x * d ^ (j + 1) := by rw [pow_succ', ← mul_assoc, hxd]
  have hdk : d ^ k = 1 := by
    have := hpowd k
    rw [hk, pow_orderOf_eq_one] at this
    have e : x = x * d ^ orderOf v := by simpa using this
    exact (mul_eq_left.mp e.symm)
  have hd1 : d = 1 := by
    refine eq_one_of_odd_mem_isPGroup_two hQ2 (Hs.Z_normal.1 hdZ) ?_
    exact Odd.of_dvd_nat hk_odd (orderOf_dvd_of_pow_eq_one hdk)
  have hxv : x * v = v * x := by
    have e : v * x * v⁻¹ = x := by
      have : x⁻¹ * (v * x * v⁻¹) = 1 := by rw [← hd_def, hd1]
      calc v * x * v⁻¹ = x * (x⁻¹ * (v * x * v⁻¹)) := by group
        _ = x := by rw [this, mul_one]
    calc x * v = (v * x * v⁻¹) * v := by rw [e]
      _ = v * x := by group
  refine ⟨x, ⟨hxQ, mem_Cv.mpr hxv⟩, ?_⟩
  have hcZ : ⁅x, t⁆ ∈ Z := M₀.comm_mem x hxQ t htQ
  have hγ : γ ⁅x, t⁆ = γ z₀ := by rw [M₀.comm_eq x hxQ t htQ, hx, hBe₂]
  have hγinv : γ z₀⁻¹ = - γ z₀ := by
    have := R.add z₀ hz₀ z₀⁻¹ (Z.inv_mem hz₀)
    rw [mul_inv_cancel, R.one] at this
    linear_combination -this
  have h0 : γ (⁅x, t⁆ * z₀⁻¹) = 0 := by
    rw [R.add _ hcZ _ (Z.inv_mem hz₀), hγinv, hγ, add_neg_cancel]
  exact mul_inv_eq_one.mp (R.inj _ (Z.mul_mem hcZ (Z.inv_mem hz₀)) h0)

theorem le_Cv_of_fixed_mem [Finite G] {M Q Z B₀ : Subgroup G}
    {v : G} (hc : Ctx M Q Z B₀) (hvM : v ∈ M)
    (hvZ : ∀ z ∈ Z, v * z * v⁻¹ = z) (hvN : v ∈ Subgroup.normalizer (B₀ : Set G)) {b : G}
    (hb : b ∈ B₀) (hbZ : b ∉ Z) (hvb : v * b * v⁻¹ = b) : B₀ ≤ Cv v := by
  obtain ⟨K, _, _, _, γ, M₀, hM⟩ := stroth_globalModelData hc.hyp
  obtain ⟨T, hT, -, -⟩ := hM.linear_of_centralizes hvM hvZ
  have hbQ : b ∈ Q := hc.le hb
  have hπb : M₀.π b ≠ 0 := fun h0 => hbZ ((M₀.π_ker b hbQ).mp h0)
  have hline := hc.img_eq_line_of_ne hM hb hπb
  intro b' hb'
  have hb'Q : b' ∈ Q := hc.le hb'
  obtain ⟨s, hs⟩ := (hline _).mp (M₀.pi_mem_img hb' hb'Q)
  have hw : v * b' * v⁻¹ ∈ B₀ := (Subgroup.mem_normalizer_iff.mp hvN b').mp hb'
  have hwQ : v * b' * v⁻¹ ∈ Q := hc.le hw
  have hπ : M₀.π (v * b' * v⁻¹) = M₀.π b' := by
    rw [hT b' hb'Q, hs, map_smul, ← hT b hbQ, hvb]
  have hmem : (v * b' * v⁻¹)⁻¹ * b' ∈ Z := (M₀.pi_eq_iff hwQ hb'Q).mp hπ
  have hmem' : (v * b' * v⁻¹)⁻¹ * b' ∈ B₀ := B₀.mul_mem (B₀.inv_mem hw) hb'
  have h1 : (v * b' * v⁻¹)⁻¹ * b' = 1 := by
    have := Subgroup.mem_inf.mpr ⟨hmem, hmem'⟩
    rwa [hc.inf_eq_bot, Subgroup.mem_bot] at this
  have h2 : v * b' * v⁻¹ = b' := inv_mul_eq_one.mp h1
  rw [mem_Cv]
  calc b' * v = (v * b' * v⁻¹) * v := by rw [h2]
    _ = v * b' := by group

end CFSG.RankThree.GF2n.Smith81
