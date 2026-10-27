module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusPackageP123

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Helpers

private lemma ggL45_zpow_eq_zpow_of_modEq {G : Type*} [Group G] (x : G) {n : ℕ}
    (hn : x ^ n = 1) {a b : ℤ} (h : a ≡ b [ZMOD (n : ℤ)]) : x ^ a = x ^ b := by
  have hord : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hn
  have hdvd : (orderOf x : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hord
  have hba : (n : ℤ) ∣ b - a := Int.ModEq.dvd h
  have hsub : (orderOf x : ℤ) ∣ b - a := hdvd.trans hba
  exact zpow_eq_zpow_iff_modEq.mpr (Int.modEq_iff_dvd.mpr hsub)

private lemma ggL45_c_pow_modEq {p : ℕ} {s : ℕ} (hs : 2 ≤ s) {c : ℤ} {k : ℕ}
    (hc : c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s]) (j : ℕ) :
    c ^ j ≡ 1 + (p : ℤ) ^ (s - 1) * (j : ℤ) * (k : ℤ) [ZMOD (p : ℤ) ^ s] := by
  have hPsq : (p : ℤ) ^ s ∣ ((p : ℤ) ^ (s - 1)) ^ 2 := by
    have hle : s ≤ (s - 1) * 2 := by omega
    simpa [pow_mul] using pow_dvd_pow (p : ℤ) hle
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ]
    refine (ih.mul hc).trans ?_
    apply Int.modEq_of_dvd
    have hdiff : (1 + (p : ℤ) ^ (s - 1) * (((j + 1 : ℕ) : ℤ)) * (k : ℤ)) -
        ((1 + (p : ℤ) ^ (s - 1) * (j : ℤ) * (k : ℤ)) *
          (1 + (p : ℤ) ^ (s - 1) * (k : ℤ))) =
        -(((p : ℤ) ^ (s - 1)) ^ 2 * (j : ℤ) * (k : ℤ) ^ 2) := by
      push_cast
      ring
    rw [hdiff]
    exact dvd_neg.mpr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hPsq (j : ℤ)) ((k : ℤ) ^ 2))

private lemma ggL45_inS_zpow {p : ℕ} {K : Type*} [Group K] {E : Subgroup (MulAut K)} {h : K}
    (hh : GGL45InS p E h) (m : ℤ) : GGL45InS p E (h ^ m) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ := hh.1
    refine ⟨t, ?_⟩
    rw [← zpow_natCast (h ^ m) (p ^ t), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht,
      one_zpow]
  · intro e he
    rw [map_zpow, hh.2 e he]

private lemma ggL45_psi_pow_zpow {p : ℕ} {K : Type*} [Group K] {R : Type} [Group R]
    {I : Set (MulAut R)} {θ : K ⧸ Subgroup.center K ≃* R} {ψ : MulAut K}
    {E : Subgroup (MulAut K)} {s : ℕ} {c : ℤ}
    (H2 : GGL45HTwo p I θ ψ E s c) {h : K} (hh : GGL45InS p E h) (j : ℕ) :
    (ψ ^ j) h = h ^ (c ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_zpow, (H2.2.1 h hh).2, ← zpow_mul, pow_succ]
    congr 1
    ring

end Helpers

section SetI

variable {p : ℕ} {K : Type*} [Group K] {R : Type} [Group R] {I : Set (MulAut R)}
  {θ : K ⧸ Subgroup.center K ≃* R} {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem ggL45TorusP4_of_H (hp : p.Prime) (hEψ : ∀ e ∈ E, e * ψ = ψ * e) {s : ℕ} (hs : 2 ≤ s)
    {c : ℤ} {k : ℕ} (hk : ¬ p ∣ k) (hc : c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s])
    (H2 : GGL45HTwo p I θ ψ E s c) (H4 : GGL45HFourMod p I θ E (ggInducedAut θ ψ)) :
    ∀ γ : MulAut K, GGL45IsPElt p γ → (∀ e ∈ E, γ * e = e * γ) → ¬ GGL45InducesIn θ I γ →
      GGL45InducesIn θ I (γ ^ p) →
      ∃ k' : ℕ, ¬ p ∣ k' ∧ ∀ h : K, GGL45InS p E h → γ h = h ^ (1 + p ^ (s - 1) * k') := by
  intro γ hγp hγE hγnot hγpI
  have hγbarp : GGL45IsPElt p (ggInducedAut θ γ) := by
    obtain ⟨m, hm⟩ := hγp
    exact ⟨m, by rw [← map_pow, hm, map_one]⟩
  have hγbarcomm : ∀ e ∈ E,
      ggInducedAut θ γ * ggInducedAut θ e = ggInducedAut θ e * ggInducedAut θ γ := by
    intro e he
    rw [← map_mul, ← map_mul, hγE e he]
  have hγbarnot : ggInducedAut θ γ ∉ I := by
    intro hmem
    exact hγnot ((ggL45_inducesIn_iff θ I γ).2 hmem)
  have hγbarpI : (ggInducedAut θ γ) ^ p ∈ I := by
    have h := (ggL45_inducesIn_iff θ I (γ ^ p)).mp hγpI
    rwa [map_pow] at h
  obtain ⟨j, hjp, hj⟩ := H4 (ggInducedAut θ γ) hγbarp hγbarcomm hγbarnot hγbarpI
  let a : MulAut K := γ * (ψ ^ j)⁻¹
  have haind : GGL45InducesIn θ I a := by
    rw [ggL45_inducesIn_iff]
    have hmap : ggInducedAut θ a = ggInducedAut θ γ * ((ggInducedAut θ ψ) ^ j)⁻¹ := by
      dsimp [a]
      rw [map_mul, map_inv, map_pow]
    rw [hmap]
    exact hj
  have haE : ∀ e ∈ E, a * e = e * a := by
    intro e he
    have hγe : Commute γ e := hγE e he
    have hψe : Commute (ψ ^ j) e :=
      (Commute.symm (show Commute e ψ from hEψ e he)).pow_left j
    have hinv : Commute ((ψ ^ j)⁻¹) e := hψe.inv_left
    have h : Commute (γ * (ψ ^ j)⁻¹) e := hγe.mul_left hinv
    simpa [a] using h.eq
  have hafix : ∀ h : K, GGL45InS p E h → a h = h :=
    fun h hh => H2.2.2 a haind haE h hh
  have hγeq : γ = a * ψ ^ j := by
    dsimp [a]
    group
  refine ⟨j * k, ?_, ?_⟩
  · intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact hjp h
    · exact hk h
  · intro h hh
    have hpsi : (ψ ^ j) h = h ^ (c ^ j) := ggL45_psi_pow_zpow H2 hh j
    have hfixh : a (h ^ (c ^ j)) = h ^ (c ^ j) := hafix _ (ggL45_inS_zpow hh (c ^ j))
    have hps : h ^ p ^ s = 1 := (H2.2.1 h hh).1
    have hmod := ggL45_c_pow_modEq hs hc j
    have hcong : c ^ j ≡ 1 + (p : ℤ) ^ (s - 1) * ((j * k : ℕ) : ℤ) [ZMOD (p : ℤ) ^ s] := by
      convert hmod using 1
      push_cast
      ring
    have hpow : h ^ (c ^ j) = h ^ (1 + (p : ℤ) ^ (s - 1) * ((j * k : ℕ) : ℤ)) :=
      ggL45_zpow_eq_zpow_of_modEq h hps hcong
    have hnat : ((1 + p ^ (s - 1) * (j * k) : ℕ) : ℤ) =
        1 + (p : ℤ) ^ (s - 1) * ((j * k : ℕ) : ℤ) := by
      push_cast
      ring
    calc γ h = (a * ψ ^ j) h := by rw [hγeq]
      _ = a ((ψ ^ j) h) := rfl
      _ = a (h ^ (c ^ j)) := by rw [hpsi]
      _ = h ^ (c ^ j) := hfixh
      _ = h ^ (1 + (p : ℤ) ^ (s - 1) * ((j * k : ℕ) : ℤ)) := hpow
      _ = h ^ (1 + p ^ (s - 1) * (j * k)) := by rw [← hnat, zpow_natCast]

theorem ggL45TorusPackage_of_HMod (hp : p.Prime) (hK : commutator K = ⊤)
    (hEψ : ∀ e ∈ E, e * ψ = ψ * e) (H : GGL45TorusH p I θ ψ E) :
    GGL45TorusPackage p I θ ψ E := by
  obtain ⟨s, hs, c, k, hk, hc, H1, H2, H3, H4⟩ := H
  obtain ⟨hP1a, hP1b⟩ := ggL45TorusP1_of_H hK hc H1
  obtain ⟨hP2a, hP2b, hP2c, hP2d⟩ := ggL45TorusP2_of_H H2 H3
  exact ⟨s, hs, k, hk, hP1a, hP1b, hP2a, hP2b, hP2c, hP2d, ggL45TorusP3_of_H hp hs hk hc H2 H3,
    ggL45TorusP4_of_H hp hEψ hs hk hc H2 H4⟩

end SetI

section Normal

variable {p : ℕ} {K : Type*} [Group K] {R : Type} [Group R] {θ : K ⧸ Subgroup.center K ≃* R}
  {E : Subgroup (MulAut K)}

theorem ggL45HFourMod_of_HFour (hp : p.Prime) (I : Subgroup (MulAut R)) [I.Normal] {f : MulAut R}
    (hf : f ^ p = 1) (hfI : f ∉ I)
    (hfE : ∀ e ∈ E, f * ggInducedAut θ e = ggInducedAut θ e * f)
    (H4 : GGL45HFour p (I : Set (MulAut R)) θ E) :
    GGL45HFourMod p (I : Set (MulAut R)) θ E f := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hIT, ⟨g, hgT, hg⟩, hT⟩ := H4
  intro α hαp hαE hαI hαpI
  let π : MulAut R →* MulAut R ⧸ I := QuotientGroup.mk' I
  have hfT : f ∈ T := by
    refine hT f ?_ hfE
    exact ⟨1, by simpa using hf⟩
  have hαT : α ∈ T := hT α hαp hαE
  have hπf_ne : π f ≠ 1 := by
    intro h
    exact hfI ((QuotientGroup.eq_one_iff f).mp (by rwa [QuotientGroup.mk'_apply] at h))
  have hπf_pow : (π f) ^ p = 1 := by
    rw [← map_pow, hf, map_one]
  have hπf_ord : orderOf (π f) = p := orderOf_eq_prime hπf_pow hπf_ne
  have hπα_ne : π α ≠ 1 := by
    intro h
    exact hαI ((QuotientGroup.eq_one_iff α).mp (by rwa [QuotientGroup.mk'_apply] at h))
  have hπα_pow : (π α) ^ p = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (α ^ p)).mpr hαpI
  have hπα_ord : orderOf (π α) = p := orderOf_eq_prime hπα_pow hπα_ne
  have hmemf : π f ∈ Subgroup.zpowers (π g) := by
    obtain ⟨m, hm⟩ := hg f hfT
    have hm1 : (π g) ^ m * π f = 1 := by
      have h : (QuotientGroup.mk' I) (g ^ m * f) = 1 :=
        (QuotientGroup.eq_one_iff (g ^ m * f)).mpr hm
      rw [map_mul, map_zpow] at h
      simpa [π] using h
    refine Subgroup.mem_zpowers_iff.mpr ⟨-m, ?_⟩
    rw [eq_inv_of_mul_eq_one_right hm1, ← zpow_neg]
  have hmemα : π α ∈ Subgroup.zpowers (π g) := by
    obtain ⟨n, hn⟩ := hg α hαT
    have hn1 : (π g) ^ n * π α = 1 := by
      have h : (QuotientGroup.mk' I) (g ^ n * α) = 1 :=
        (QuotientGroup.eq_one_iff (g ^ n * α)).mpr hn
      rw [map_mul, map_zpow] at h
      simpa [π] using h
    refine Subgroup.mem_zpowers_iff.mpr ⟨-n, ?_⟩
    rw [eq_inv_of_mul_eq_one_right hn1, ← zpow_neg]
  let C := Subgroup.zpowers (π g)
  let x : C := ⟨π f, hmemf⟩
  let y : C := ⟨π α, hmemα⟩
  have hxord : orderOf x = p := by
    change orderOf (⟨π f, hmemf⟩ : C) = p
    rw [Subgroup.orderOf_mk, hπf_ord]
  have hyord : orderOf y = p := by
    change orderOf (⟨π α, hmemα⟩ : C) = p
    rw [Subgroup.orderOf_mk, hπα_ord]
  haveI hFx : Finite ↥(Subgroup.zpowers x) :=
    IsOfFinOrder.finite_zpowers (by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨p, hp.pos, by rw [← hxord, pow_orderOf_eq_one]⟩)
  haveI hFy : Finite ↥(Subgroup.zpowers y) :=
    IsOfFinOrder.finite_zpowers (by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨p, hp.pos, by rw [← hyord, pow_orderOf_eq_one]⟩)
  haveI hCyc : IsCyclic C := Subgroup.isCyclic_zpowers (π g)
  have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hyord])
  have hyx : y ∈ Subgroup.zpowers x := by
    have h := Subgroup.mem_zpowers y
    rwa [← heq] at h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyx
  have hkval : (π f) ^ k = π α := by
    have h := congrArg (Subtype.val) hk
    simpa [Subgroup.coe_pow] using h
  have hmem : π α ∈ Subgroup.zpowers (π f) :=
    Subgroup.mem_zpowers_iff.mpr ⟨k, hkval⟩
  have hπf_fin : IsOfFinOrder (π f) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨p, hp.pos, hπf_pow⟩
  rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hπf_fin] at hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨j, hjrange, hj⟩ := hmem
  rw [Finset.mem_range] at hjrange
  have hjlt : j < p := by rw [← hπf_ord]; exact hjrange
  refine ⟨j, ?_, ?_⟩
  · intro hdvd
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hjlt
    rw [hj0, pow_zero] at hj
    exact hπα_ne hj.symm
  · have h1 : (QuotientGroup.mk' I) (α * (f ^ j)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hj, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (α * (f ^ j)⁻¹)).mp
      (by rwa [QuotientGroup.mk'_apply] at h1)

end Normal

end CFSG.StandardType
