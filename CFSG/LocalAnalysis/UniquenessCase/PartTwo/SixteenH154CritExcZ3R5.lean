module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_zp_eq_of_mem_zp_of_prime {G : Type} [Group G] [Finite G]
    {g x : G} {p : ℕ} (hp : p.Prime) (hg : orderOf g = p)
    (hx : x ∈ Subgroup.zpowers g) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = Subgroup.zpowers g := by
  have hdvd : orderOf x ∣ p := hg ▸ orderOf_dvd_of_mem_zpowers hx
  have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have hxp : orderOf x = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hxle : Subgroup.zpowers x ≤ Subgroup.zpowers g := Subgroup.zpowers_le.mpr hx
  refine Subgroup.eq_of_le_of_card_ge hxle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hxp, hg]

private lemma s16h_commute_of_mem_zpowers {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    {y : G} (hy : y ∈ Subgroup.zpowers b) : a * y = y * a := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hn]
  exact (show Commute a b from hab).zpow_right n |>.eq

private lemma s16h_card_fixedPoints_eq_card_fixV {W : Type} [CommGroup W] (x : MulAut W) :
    Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) W) =
      Nat.card ↥(fixV (Subgroup.zpowers x)) := by
  refine Nat.card_congr (Set.equivOfEq ?_)
  ext w
  simp only [SetLike.mem_coe, mem_fixV, MulAction.mem_fixedPoints]
  constructor
  · intro h y hy
    exact h ⟨y, hy⟩
  · intro h g
    exact h g.1 g.2

private lemma s16h_card_fixV_zpowers_of_five {W : Type} [CommGroup W] [Finite W]
    (hcard : Nat.card W = 64) {l : MulAut W} (hl : orderOf l = 3)
    (hfpf : ∀ w : W, l w = w → w = 1)
    {R : Subgroup (MulAut W)} (hRl : R ≤ centralizer ({l} : Set (MulAut W)))
    (hR5 : IsPGroup 5 R) {x : MulAut W} (hxR : x ∈ R) (hx1 : x ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers x)) = 4 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set U : Subgroup W := fixV (Subgroup.zpowers x) with hU_eq
  have hmod5 : Nat.card W ≡ Nat.card ↥U [MOD 5] := by
    have hle : Subgroup.zpowers x ≤ R := Subgroup.zpowers_le.mpr hxR
    have hzp : IsPGroup 5 ↥(Subgroup.zpowers x) := hR5.to_le hle
    have h := hzp.card_modEq_card_fixedPoints W
    rwa [s16h_card_fixedPoints_eq_card_fixV x] at h
  have hxl : x * l = l * x := Subgroup.mem_centralizer_singleton_iff.mp (hRl hxR)
  have hl_inv : ∀ y ∈ Subgroup.zpowers l, ∀ u ∈ U, y u ∈ U := by
    intro y hy u hu
    rw [hU_eq, mem_fixV] at hu ⊢
    intro z hz
    have hyh : y * x = x * y := (s16h_commute_of_mem_zpowers hxl hy).symm
    have hzy : z * y = y * z := (s16h_commute_of_mem_zpowers hyh hz).symm
    calc z (y u) = (z * y) u := by rw [MulAut.mul_apply]
      _ = (y * z) u := by rw [hzy]
      _ = y (z u) := by rw [MulAut.mul_apply]
      _ = y u := by rw [hu z hz]
  have hbot_l : fixV (Subgroup.zpowers l) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [mem_fixV] at hw
    rw [Subgroup.mem_bot]
    exact hfpf w (hw l (Subgroup.mem_zpowers l))
  have h3dvd : 3 ∣ Nat.card ↥U - 1 := by
    have hRval : ∀ y ∈ Subgroup.zpowers l, y ≠ 1 →
        Nat.card ↥(U ⊓ fixV (Subgroup.zpowers y)) = 1 := by
      intro y hy hy1
      have hyeq : Subgroup.zpowers y = Subgroup.zpowers l :=
        s16h_zp_eq_of_mem_zp_of_prime (p := 3) (by norm_num) hl hy hy1
      rw [hyeq, hbot_l, inf_bot_eq, Subgroup.card_bot]
    have h := s16h_card_dvd_sub_of_fix_card (W := W) (R := Subgroup.zpowers l)
      (U := U) (c := 1) hl_inv hRval
    simpa [Nat.card_zpowers, hl] using h
  have hU_dvd : Nat.card ↥U ∣ 64 := by
    simpa [hcard] using Subgroup.card_subgroup_dvd_card U
  have hU_ne64 : Nat.card ↥U ≠ 64 := by
    intro h64
    have hUt : U = ⊤ := by
      refine Subgroup.eq_of_le_of_card_ge le_top ?_
      rw [Subgroup.card_top, hcard, h64]
    have hxone : x = 1 := by
      ext w
      have hw : w ∈ U := by rw [hUt]; exact Subgroup.mem_top w
      rw [hU_eq, mem_fixV] at hw
      simpa using hw x (Subgroup.mem_zpowers x)
    exact hx1 hxone
  have h64pow : (64 : ℕ) = 2 ^ 6 := by norm_num
  obtain ⟨k, hk6, hUk⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp (h64pow ▸ hU_dvd)
  have hmod2 : (64 : ℕ) ≡ 2 ^ k [MOD 5] := by simpa [hUk, hcard] using hmod5
  have hk26 : k = 2 ∨ k = 6 := by
    interval_cases k <;> norm_num at hmod2
    · left; rfl
    · right; rfl
  rcases hk26 with h | h
  · rw [hUk, h]; norm_num
  · exact absurd (by rw [hUk, h]; norm_num) hU_ne64

private lemma s16h_card_mulAut_le_six {F : Type} [Group F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (MulAut F) ≤ 6 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let S := {x : F // x ≠ 1}
  have hScard : Nat.card S = 3 := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {x : F // x ≠ 1} = 3
    rw [Fintype.card_subtype_compl (fun x : F => x = 1), Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hF]
  let φ : MulAut F → Equiv.Perm S := fun σ =>
    { toFun := fun x => ⟨σ x.1, fun h => x.2 (σ.injective (by rw [h, map_one]))⟩
      invFun := fun x => ⟨σ.symm x.1, fun h => x.2 (by simpa using congrArg σ h)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hφinj : Function.Injective φ := by
    intro σ τ h
    ext x
    by_cases hx : x = 1
    · subst hx; simp
    · have := congrArg (fun f : Equiv.Perm S => (f ⟨x, hx⟩ : F)) h
      simpa [φ] using this
  have h1 : Nat.card (MulAut F) ≤ Nat.card (Equiv.Perm S) :=
    Nat.card_le_card_of_injective φ hφinj
  have h2 : Nat.card (Equiv.Perm S) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hScard]
    norm_num
  omega

theorem s16h_false_of_five_torus {W : Type} [CommGroup W] [Finite W] (hcard : Nat.card W = 64)
    {l : MulAut W} (hl : orderOf l = 3) (hfpf : ∀ w : W, l w = w → w = 1)
    {R D : Subgroup (MulAut W)} (hRl : R ≤ centralizer ({l} : Set (MulAut W)))
    (hR5 : IsPGroup 5 R) (hR1 : R ≠ ⊥) (hD : IsElemAbelian 3 D) (hD27 : 27 ≤ Nat.card ↥D)
    (hDR : D ≤ normalizer (R : Set (MulAut W))) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfix4 : ∀ x ∈ R, x ≠ 1 → Nat.card ↥(fixV (Subgroup.zpowers x)) = 4 :=
    fun x hx hx1 => s16h_card_fixV_zpowers_of_five hcard hl hfpf hRl hR5 hx hx1
  have hR_dvd : Nat.card ↥R ∣ 60 := by
    have hUt : ∀ x ∈ R, ∀ u ∈ (⊤ : Subgroup W), x u ∈ ⊤ := fun _ _ _ _ => Subgroup.mem_top _
    have hRval : ∀ x ∈ R, x ≠ 1 →
        Nat.card ↥((⊤ : Subgroup W) ⊓ fixV (Subgroup.zpowers x)) = 4 := by
      intro x hx hx1
      rw [top_inf_eq]
      exact hfix4 x hx hx1
    have h := s16h_card_dvd_sub_of_fix_card (W := W) (R := R) (U := ⊤) (c := 4) hUt hRval
    have h' : Nat.card ↥R ∣ 64 - 4 := by simpa [Subgroup.card_top, hcard] using h
    norm_num at h'
    exact h'
  have hRcard : Nat.card ↥R = 5 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 5) (G := R)).mp hR5
    have h5n_dvd : 5 ^ n ∣ 60 := hn ▸ hR_dvd
    have hn_le : n ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ n := by omega
      have h25 : 25 ∣ 5 ^ n := by
        calc (25 : ℕ) = 5 ^ 2 := by norm_num
          _ ∣ 5 ^ n := pow_dvd_pow 5 h2
      have h25' : 25 ∣ 60 := h25.trans h5n_dvd
      norm_num at h25'
    have hn_ne : n ≠ 0 := by
      intro h0
      have h1 : Nat.card ↥R = 1 := by rw [hn, h0]; norm_num
      exact hR1 (Subgroup.card_eq_one.mp h1)
    interval_cases n
    · exact absurd rfl hn_ne
    · simpa using hn
  obtain ⟨ρ, hρR, hρ1⟩ : ∃ x ∈ R, x ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one R with h | h
    · exact absurd h hR1
    · exact h
  have hρ5 : orderOf ρ = 5 := by
    have hdvd : orderOf ρ ∣ Nat.card ↥R := R.orderOf_dvd_natCard hρR
    rw [hRcard] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hρ1
    · exact h
  have hRzp : R = Subgroup.zpowers ρ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hρR) ?_).symm
    rw [Nat.card_zpowers, hρ5, hRcard]
  have hDcent : D ≤ Subgroup.centralizer ({ρ} : Set (MulAut W)) := by
    have hEn : D ≤ normalizer ((Subgroup.zpowers ρ : Subgroup (MulAut W)) : Set (MulAut W)) := by
      rwa [← hRzp]
    have hmain := s16h_card_le_mul_cent_of_normalizes (X := MulAut W) (e := ρ)
      (p := 5) (q := 3) (by norm_num) hρ5 (by norm_num) hEn (fun x hx => hD.2 x hx)
    rw [if_neg (by norm_num : ¬ (3 ∣ 5 - 1)), one_mul] at hmain
    have hcard' : Nat.card ↥D ≤ Nat.card ↥(D ⊓ Subgroup.centralizer ({ρ} : Set (MulAut W))) :=
      hmain
    have heq : D ⊓ Subgroup.centralizer ({ρ} : Set (MulAut W)) = D :=
      Subgroup.eq_of_le_of_card_ge inf_le_left hcard'
    exact heq ▸ inf_le_right
  set F : Subgroup W := fixV (Subgroup.zpowers ρ) with hF_eq
  have hFcard : Nat.card ↥F = 4 := by
    rw [hF_eq]
    exact hfix4 ρ hρR hρ1
  have hDstab : D ≤ stabSub F := by
    intro d hd
    rw [mem_stabSub]
    intro u
    have hcomm : d * ρ = ρ * d := by
      have h := hDcent hd
      rwa [Subgroup.mem_centralizer_singleton_iff] at h
    constructor
    · intro hu
      rw [hF_eq, mem_fixV] at hu ⊢
      intro z hz
      have hdz : z * d = d * z := (s16h_commute_of_mem_zpowers hcomm hz).symm
      have hdz1 : z (d u) = d (z u) := by
        calc z (d u) = (z * d) u := by rw [MulAut.mul_apply]
          _ = (d * z) u := by rw [hdz]
          _ = d (z u) := by rw [MulAut.mul_apply]
      exact d.injective (hdz1.symm.trans (hu z hz))
    · intro hu
      rw [hF_eq, mem_fixV] at hu ⊢
      intro z hz
      have hdz : z * d = d * z := (s16h_commute_of_mem_zpowers hcomm hz).symm
      calc z (d u) = (z * d) u := by rw [MulAut.mul_apply]
        _ = (d * z) u := by rw [hdz]
        _ = d (z u) := by rw [MulAut.mul_apply]
        _ = d u := by rw [hu z hz]
  set H : Subgroup (MulAut W) := D ⊓ centSub F with hH_eq
  have hH_card : 9 ≤ Nat.card ↥H := by
    have hexpD : Monoid.exponent ↥D ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun x : ↥D => Subtype.ext (hD.2 x.1 x.2))
    have hD3 : IsPGroup 3 ↥D :=
      IsPGroup.of_exponent_dvd_pow (p := 3) (n := 1) (by simpa using hexpD)
    have hD3sub : IsPGroup 3 (D.subgroupOf (stabSub F)) :=
      hD3.of_equiv (Subgroup.subgroupOfEquivOfLe hDstab).symm
    have haut3 : IsPGroup 3 (autSub D F) := by
      change IsPGroup 3 ((D.subgroupOf (stabSub F)).map (resHom F))
      exact hD3sub.map (resHom F)
    have haut_le6 : Nat.card (autSub D F) ≤ 6 :=
      le_trans (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)
        (s16h_card_mulAut_le_six hFcard)
    have hcardmul : Nat.card (autSub D F) * Nat.card ↥H = Nat.card ↥D := by
      rw [hH_eq]
      exact card_autSub_mul (A := D) (U := F) hDstab
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3) (G := autSub D F)).mp haut3
    have hk_le : k ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ k := by omega
      have h9 : 9 ≤ 3 ^ k := by
        calc (9 : ℕ) = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h2
      rw [← hk] at h9
      omega
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with h0 | h1
    · rw [hk, h0, pow_zero, one_mul] at hcardmul
      omega
    · rw [hk, h1, pow_one] at hcardmul
      omega
  have hHcard4 : ∀ h ∈ H, h ≠ 1 → fixV (Subgroup.zpowers h) = F := by
    intro h hhH hh1
    set U : Subgroup W := fixV (Subgroup.zpowers h) with hU_eq
    have hHD : H ≤ D := by rw [hH_eq]; exact inf_le_left
    have hHcent : H ≤ centSub F := by rw [hH_eq]; exact inf_le_right
    have hhD : h ∈ D := hHD hhH
    have hhcF : h ∈ centSub F := hHcent hhH
    have hcomm : h * ρ = ρ * h := by
      have h := hDcent hhD
      rwa [Subgroup.mem_centralizer_singleton_iff] at h
    have hFU : F ≤ U := by
      intro u hu
      rw [hU_eq, mem_fixV]
      intro z hz
      have hhu : h u = u := (mem_centSub.mp hhcF) u hu
      have hfix := smul_eq_self_of_mem_zpowers hz hhu
      simpa using hfix
    have hρU : ∀ y ∈ Subgroup.zpowers ρ, ∀ u ∈ U, y u ∈ U := by
      intro y hy u hu
      rw [hU_eq, mem_fixV] at hu ⊢
      intro z hz
      have hyh : y * h = h * y := (s16h_commute_of_mem_zpowers hcomm hy).symm
      have hzy : z * y = y * z := (s16h_commute_of_mem_zpowers hyh hz).symm
      calc z (y u) = (z * y) u := by rw [MulAut.mul_apply]
        _ = (y * z) u := by rw [hzy]
        _ = y (z u) := by rw [MulAut.mul_apply]
        _ = y u := by rw [hu z hz]
    have h5dvd : 5 ∣ Nat.card ↥U - 4 := by
      have hRval : ∀ y ∈ Subgroup.zpowers ρ, y ≠ 1 →
          Nat.card ↥(U ⊓ fixV (Subgroup.zpowers y)) = 4 := by
        intro y hy hy1
        have hyeq : Subgroup.zpowers y = Subgroup.zpowers ρ :=
          s16h_zp_eq_of_mem_zp_of_prime (p := 5) (by norm_num) hρ5 hy hy1
        rw [hyeq, ← hF_eq]
        have hinf : U ⊓ F = F := inf_eq_right.mpr hFU
        rw [hinf, hFcard]
      have h := s16h_card_dvd_sub_of_fix_card (W := W) (R := Subgroup.zpowers ρ)
        (U := U) (c := 4) hρU hRval
      simpa [Nat.card_zpowers, hρ5] using h
    have hU_dvd : Nat.card ↥U ∣ 64 := by
      simpa [hcard] using Subgroup.card_subgroup_dvd_card U
    have hU_ge : 4 ≤ Nat.card ↥U := by
      rw [← hFcard]
      exact Subgroup.card_le_of_le hFU
    have h64pow : (64 : ℕ) = 2 ^ 6 := by norm_num
    obtain ⟨k, hk6, hUk⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp (h64pow ▸ hU_dvd)
    have hU_ne64 : Nat.card ↥U ≠ 64 := by
      intro h64
      have hUt : U = ⊤ := by
        refine Subgroup.eq_of_le_of_card_ge le_top ?_
        rw [Subgroup.card_top, hcard, h64]
      have hcone : h = 1 := by
        ext w
        have hw : w ∈ U := by rw [hUt]; exact Subgroup.mem_top w
        rw [hU_eq, mem_fixV] at hw
        simpa using hw h (Subgroup.mem_zpowers h)
      exact hh1 hcone
    have hk26 : k = 2 ∨ k = 6 := by
      have hk2 : 2 ≤ k := by
        by_contra h
        have hk1 : k ≤ 1 := by omega
        rw [hUk] at hU_ge
        interval_cases k <;> norm_num at hU_ge
      rw [hUk] at h5dvd
      interval_cases k <;> norm_num at h5dvd
      · left; rfl
      · right; rfl
    have hUcard4 : Nat.card ↥U = 4 := by
      rcases hk26 with h | h
      · rw [hUk, h]; norm_num
      · exact absurd (by rw [hUk, h]; norm_num) hU_ne64
    have hUF : U = F := (Subgroup.eq_of_le_of_card_ge hFU (by omega)).symm
    simpa [hU_eq] using hUF
  have hFtop : F = ⊤ := by
    have hHD : H ≤ D := by rw [hH_eq]; exact inf_le_left
    haveI : IsMulCommutative ↥D := hD.1
    have hHab : IsElemAbelian 3 H :=
      ⟨IsMulCommutative.of_comm (fun a b =>
          Subtype.ext (congrArg (fun x : ↥D => (x : MulAut W))
            (mul_comm' (⟨a.1, hHD a.2⟩ : ↥D) (⟨b.1, hHD b.2⟩ : ↥D)))),
        fun x hx => hD.2 x (hHD hx)⟩
    have hW3 : ¬ 3 ∣ Nat.card W := by rw [hcard]; norm_num
    have hcardH : 3 ^ 2 ≤ Nat.card ↥H := by simpa using hH_card
    exact s16h_eq_top_of_fixV_le (p := 3) (by norm_num) hW3 hHab hcardH
      (fun x hx hx1 => le_of_eq (hHcard4 x hx hx1))
  have h64 : Nat.card ↥F = 64 := by rw [hFtop, Subgroup.card_top]; exact hcard
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
