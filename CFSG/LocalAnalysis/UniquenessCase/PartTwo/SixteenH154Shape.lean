module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Fpf
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_conj_mem_centerOf {X : Type*} [Group X] {L : Subgroup X} {x z : X}
    (hx : x ∈ Subgroup.normalizer (L : Set X)) (hz : z ∈ centerOf L) :
    x * z * x⁻¹ ∈ centerOf L := by
  obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hx z).mp hzL, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hzC ⊢
  intro l hl
  have hl' : x⁻¹ * l * x ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * l * x)).mpr (by
      have h : x * (x⁻¹ * l * x) * x⁻¹ = l := by group
      rwa [h])
  calc l * (x * z * x⁻¹) = x * ((x⁻¹ * l * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * l * x)) * x⁻¹ := by rw [hzC _ hl']
    _ = (x * z * x⁻¹) * l := by group

private theorem s16h_card_modEq_card_inf_centralizer {X : Type*} [Group X] [Finite X]
    {p : ℕ} [hp : Fact p.Prime] {x : X} (hx : x ^ p = 1)
    {Y : Subgroup X} (hxY : x ∈ Subgroup.normalizer (Y : Set X)) :
    Nat.card Y ≡ Nat.card (Y ⊓ Subgroup.centralizer ({x} : Set X) : Subgroup X) [MOD p] := by
  classical
  set R := Subgroup.zpowers x with hR
  have hRY : R ≤ Subgroup.normalizer (Y : Set X) := Subgroup.zpowers_le.mpr hxY
  let := Subgroup.conjMulDistribMulActionOfLeNormalizer R Y hRY
  have hRp : IsPGroup p R := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (p := p) hp.out (m := 1) (i := orderOf x)).mp
      (orderOf_dvd_of_pow_eq_one (show x ^ p ^ 1 = 1 by rw [pow_one]; exact hx))
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hmod := hRp.card_modEq_card_fixedPoints Y
  have hsmul : ∀ (r : R) (y : Y), ((r • y : Y) : X) = (r : X) * y * (r : X)⁻¹ := fun r y =>
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit R Y hRY r y
  let e : MulAction.fixedPoints R Y ≃
      (Y ⊓ Subgroup.centralizer ({x} : Set X) : Subgroup X) :=
    { toFun := fun y => ⟨((y : Y) : X), Subgroup.mem_inf.mpr ⟨(y : Y).2, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := congrArg Subtype.val (y.2 ⟨x, Subgroup.mem_zpowers x⟩)
        rw [hsmul] at h1
        calc ((y : Y) : X) * x = x * (y : Y) * x⁻¹ * x := by rw [h1]
          _ = x * (y : Y) := by group⟩⟩
      invFun := fun z => ⟨⟨z, (Subgroup.mem_inf.mp z.2).1⟩, fun r => by
        apply Subtype.ext
        rw [hsmul]
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp r.2
        have hc : Commute x (z : X) :=
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp z.2).2).symm
        have hcj : Commute (x ^ j) (z : X) := hc.zpow_left j
        rw [← hj]
        change x ^ j * (z : X) * (x ^ j)⁻¹ = z
        rw [hcj.eq, mul_inv_cancel_right]⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  rwa [Nat.card_congr e] at hmod

private theorem s16h_not_dvd_two_pow_mul_three_pow {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (a b : ℕ) : ¬ q ∣ 2 ^ a * 3 ^ b := by
  intro h
  rcases hq.dvd_mul.mp h with h2 | h3
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
  · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h3))

private theorem s16h_card_eq_of_dvd_modEq_nine {q c : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (hdiv : c ∣ 9) (hmod : 9 ≡ c [MOD q]) : c = 9 := by
  have hdiv' : c ∣ 3 ^ 2 := by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hdiv
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow (p := 3) (by norm_num : Nat.Prime 3)).mp hdiv'
  rw [hk] at hmod ⊢
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · exfalso
    have hle : 3 ^ 0 ≤ 9 := by norm_num
    have hdvd : q ∣ 9 - 3 ^ 0 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    norm_num at hdvd
    exact s16h_not_dvd_two_pow_mul_three_pow hq hq2 hq3 3 0 (by
      rw [show (2 : ℕ) ^ 3 * 3 ^ 0 = 8 by norm_num]; exact hdvd)
  · exfalso
    have hle : 3 ^ 1 ≤ 9 := by norm_num
    have hdvd : q ∣ 9 - 3 ^ 1 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    norm_num at hdvd
    exact s16h_not_dvd_two_pow_mul_three_pow hq hq2 hq3 1 1 (by
      rw [show (2 : ℕ) ^ 1 * 3 ^ 1 = 6 by norm_num]; exact hdvd)
  · norm_num

private theorem s16h_card_eq_of_dvd_modEq_twentyseven {q c : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (h3 : 3 ∣ c) (hdiv : c ∣ 27) (hmod : 27 ≡ c [MOD q]) : c = 27 := by
  have hdiv' : c ∣ 3 ^ 3 := by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact hdiv
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow (p := 3) (by norm_num : Nat.Prime 3)).mp hdiv'
  rw [hk] at hmod h3 ⊢
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by
    interval_cases k
    · norm_num at h3
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hk_cases with rfl | rfl | rfl
  · exfalso
    have hle : 3 ^ 1 ≤ 27 := by norm_num
    have hdvd : q ∣ 27 - 3 ^ 1 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    norm_num at hdvd
    exact s16h_not_dvd_two_pow_mul_three_pow hq hq2 hq3 3 1 (by
      rw [show (2 : ℕ) ^ 3 * 3 ^ 1 = 24 by norm_num]; exact hdvd)
  · exfalso
    have hle : 3 ^ 2 ≤ 27 := by norm_num
    have hdvd : q ∣ 27 - 3 ^ 2 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    norm_num at hdvd
    exact s16h_not_dvd_two_pow_mul_three_pow hq hq2 hq3 1 2 (by
      rw [show (2 : ℕ) ^ 1 * 3 ^ 2 = 18 by norm_num]; exact hdvd)
  · norm_num

private theorem s16h_card_of_isElemAbelianOfRank_two {G : Type*} [Group G]
    (h : IsElemAbelianOfRank 3 2 G) : Nat.card G = 9 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  simp [Fintype.card_fun, ZMod.card]

private theorem s16h_three_le_orderOf_two_zmod {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) : 3 ≤ orderOf (2 : ZMod q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h2ne0 : (2 : ZMod q) ≠ 0 := by
    intro h
    have : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this)
  have hpos : 0 < orderOf (2 : ZMod q) := by
    have h := orderOf_pos (Units.mk0 (2 : ZMod q) h2ne0)
    rw [← orderOf_units, Units.val_mk0] at h
    exact h
  have hle : 1 ≤ 2 ^ orderOf (2 : ZMod q) := Nat.one_le_pow _ 2 (by norm_num)
  have hdvd : q ∣ 2 ^ orderOf (2 : ZMod q) - 1 := by
    have h2 : ((2 ^ orderOf (2 : ZMod q) : ℕ) : ZMod q) = 1 := by
      rw [Nat.cast_pow]; exact pow_orderOf_eq_one (2 : ZMod q)
    have h3 : ((2 ^ orderOf (2 : ZMod q) - 1 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sub hle, h2]; simp
    exact (ZMod.natCast_eq_zero_iff (2 ^ orderOf (2 : ZMod q) - 1) q).mp h3
  by_contra h
  have hd : orderOf (2 : ZMod q) = 1 ∨ orderOf (2 : ZMod q) = 2 := by omega
  rcases hd with h1 | h2
  · rw [h1] at hdvd
    norm_num at hdvd
    exact hq.ne_one hdvd
  · rw [h2] at hdvd
    norm_num at hdvd
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdvd)

private theorem s16h_isElemAbelianOfRank_comm {G : Type*} [Group G] {p n : ℕ}
    (h : IsElemAbelianOfRank p n G) :
    (∀ a b : G, a * b = b * a) ∧ ∀ a : G, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

private theorem s16h_comm_pow_of_isElemAbelianOfRank_two {G : Type*} [Group G] {L : Subgroup G}
    (hL : IsElemAbelianOfRank 3 2 ↥L) :
    (∀ a ∈ L, ∀ b ∈ L, a * b = b * a) ∧ ∀ a ∈ L, a ^ 3 = 1 := by
  obtain ⟨hcomm, hpow⟩ := s16h_isElemAbelianOfRank_comm hL
  exact ⟨fun a ha b hb => congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩),
    fun a ha => congrArg Subtype.val (hpow ⟨a, ha⟩)⟩

section Helpers

variable {V : Type*} [CommGroup V]

private lemma s16h_commute_zpowers {x g : MulAut V} (hxg : g * x = x * g) {y : MulAut V}
    (hy : y ∈ Subgroup.zpowers x) : g * y = y * g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (show Commute g x from hxg).zpow_right n

private lemma s16h_commSub_zpowers_invariant {x g : MulAut V} {U : Subgroup V}
    (hxg : g * x = x * g) (hU : ∀ u ∈ U, g u ∈ U) {c : V}
    (hc : c ∈ commSub U (Subgroup.zpowers x)) :
    g c ∈ commSub U (Subgroup.zpowers x) := by
  refine Subgroup.closure_induction (p := fun c _ => g c ∈ commSub U (Subgroup.zpowers x))
    ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨y, hy, w, hw, rfl⟩
    have hyg : g * y = y * g := s16h_commute_zpowers hxg hy
    have h1 : g (y w) = y (g w) := by rw [← MulAut.mul_apply, hyg, MulAut.mul_apply]
    rw [map_mul, map_inv, h1]
    exact Subgroup.subset_closure ⟨y, hy, g w, hU w hw, rfl⟩
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]; exact Subgroup.inv_mem _ ha

private lemma s16h_inf_fixV_zpowers_invariant {x g : MulAut V} {U : Subgroup V}
    (hxg : g * x = x * g) (hU : ∀ u ∈ U, g u ∈ U) {c : V}
    (hc : c ∈ U ⊓ fixV (Subgroup.zpowers x)) :
    g c ∈ U ⊓ fixV (Subgroup.zpowers x) := by
  obtain ⟨hcU, hcfix⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨hU c hcU, ?_⟩
  rw [mem_fixV] at hcfix ⊢
  intro y hy
  have hyg : y * g = g * y := (s16h_commute_zpowers hxg hy).symm
  rw [← MulAut.mul_apply, hyg, MulAut.mul_apply, hcfix y hy]

private lemma s16h_centSub_sup (U₁ U₂ : Subgroup V) :
    centSub (U₁ ⊔ U₂) = centSub U₁ ⊓ centSub U₂ := by
  ext g
  rw [mem_centSub, Subgroup.mem_inf, mem_centSub, mem_centSub]
  exact ⟨fun h => ⟨fun u hu => h u (Subgroup.mem_sup_left hu),
      fun u hu => h u (Subgroup.mem_sup_right hu)⟩,
    fun h u hu => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul, h.1 a ha, h.2 b hb]⟩

end Helpers

theorem s16h_commute_of_normalizes_nine {X : Type*} [Group X] [Finite X] {L E : Subgroup X}
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hL : IsElemAbelianOfRank 3 2 ↥L ∨ IsPOnePlusTwo 3 ↥L)
    (hEn : E ≤ normalizer (L : Set X)) (hEq : ∀ x ∈ E, x ^ q = 1) :
    ∀ x ∈ E, ∀ l ∈ L, x * l = l * x := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro x hxE l hlL
  have hxL : x ∈ Subgroup.normalizer (L : Set X) := hEn hxE
  have hxq : x ^ q = 1 := hEq x hxE
  set C : Subgroup X := L ⊓ Subgroup.centralizer ({x} : Set X) with hC
  have hCdiv : Nat.card C ∣ Nat.card L := by
    rw [hC]; exact Subgroup.card_dvd_of_le inf_le_left
  have hmod : Nat.card L ≡ Nat.card C [MOD q] := by
    rw [hC]; exact s16h_card_modEq_card_inf_centralizer hxq hxL
  have hCL : C = L := by
    rcases hL with hE9 | h312
    · have hcardL : Nat.card ↥L = 9 := by
        obtain ⟨e⟩ := hE9
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
        simp [Fintype.card_fun, ZMod.card]
      have hc : Nat.card C = 9 :=
        s16h_card_eq_of_dvd_modEq_nine hq hq2 hq3
          (by rw [← hcardL]; exact hCdiv) (by rw [← hcardL]; exact hmod)
      exact Subgroup.eq_of_le_of_card_ge (show C ≤ L by rw [hC]; exact inf_le_left)
        (by simp [hc, hcardL])
    · haveI : CFSG.IsExtraspecial 3 ↥L := h312.1
      have hcardL : Nat.card ↥L = 27 := h312.2.1
      have hcenter_eq : centerOf L = (Subgroup.center ↥L).map L.subtype := by
        ext z
        constructor
        · intro hz
          obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
          refine ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
          intro g
          exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzC) g g.2)
        · rintro ⟨c, hc, hcz⟩
          rw [← hcz]
          refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l, hl⟩)
      have hZcard : Nat.card (centerOf L) = 3 := by
        rw [hcenter_eq, Subgroup.card_map_of_injective L.subtype_injective]
        exact CFSG.IsExtraspecial.center_order_p 3 ↥L
      have hxZ : x ∈ Subgroup.normalizer (centerOf L : Set X) := by
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · intro hz; exact s16h_conj_mem_centerOf hxL hz
        · intro hz
          have h := s16h_conj_mem_centerOf (Subgroup.inv_mem _ hxL) hz
          simpa [mul_assoc] using h
      have hZmod := s16h_card_modEq_card_inf_centralizer (Y := centerOf L) hxq hxZ
      have hCz_dvd : Nat.card ↥(centerOf L ⊓ Subgroup.centralizer ({x} : Set X)) ∣ 3 := by
        rw [← hZcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hCz_card : Nat.card ↥(centerOf L ⊓ Subgroup.centralizer ({x} : Set X)) = 3 := by
        have hdiv' : Nat.card ↥(centerOf L ⊓ Subgroup.centralizer ({x} : Set X)) ∣ 3 ^ 1 := by
          rw [pow_one]; exact hCz_dvd
        obtain ⟨k, hk1, hk⟩ := (Nat.dvd_prime_pow (p := 3) (by norm_num : Nat.Prime 3)).mp hdiv'
        have hk01 : k = 0 ∨ k = 1 := by omega
        rcases hk01 with rfl | rfl
        · exfalso
          rw [hZcard, hk] at hZmod
          have hle : 3 ^ 0 ≤ 3 := by norm_num
          have hdvd : q ∣ 3 - 3 ^ 0 := (Nat.modEq_iff_dvd' hle).mp hZmod.symm
          norm_num at hdvd
          exact s16h_not_dvd_two_pow_mul_three_pow hq hq2 hq3 1 0 (by
            rw [show (2 : ℕ) ^ 1 * 3 ^ 0 = 2 by norm_num]; exact hdvd)
        · rw [hk]; norm_num
      have hZleC : centerOf L ≤ C := by
        have hZleCx : centerOf L ≤ Subgroup.centralizer ({x} : Set X) := by
          have hCz_eq : centerOf L ⊓ Subgroup.centralizer ({x} : Set X) = centerOf L :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hCz_card, hZcard])
          intro z hz
          have hz' : z ∈ centerOf L ⊓ Subgroup.centralizer ({x} : Set X) := by
            rw [hCz_eq]; exact hz
          exact (Subgroup.mem_inf.mp hz').2
        intro z hz
        rw [hC, Subgroup.mem_inf]
        exact ⟨(Subgroup.mem_inf.mp hz).1, hZleCx hz⟩
      have h3dvd : 3 ∣ Nat.card C := by
        rw [← hZcard]
        exact Subgroup.card_dvd_of_le hZleC
      have hc : Nat.card C = 27 :=
        s16h_card_eq_of_dvd_modEq_twentyseven hq hq2 hq3 h3dvd
          (by rw [← hcardL]; exact hCdiv) (by rw [← hcardL]; exact hmod)
      exact Subgroup.eq_of_le_of_card_ge (show C ≤ L by rw [hC]; exact inf_le_left)
        (by simp [hc, hcardL])
  have hlC : l ∈ C := hCL.symm ▸ hlL
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hlC).2) x (Set.mem_singleton x)

theorem s16h_card_le_mul_cent_of_six {W : Type} [CommGroup W] [Finite W]
    (hV : ∀ v : W, v ^ 2 = 1) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    {L E : Subgroup (MulAut W)} (hL : IsElemAbelianOfRank 3 2 ↥L ∨ IsPOnePlusTwo 3 ↥L)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) ≤ 6)
    (hEn : E ≤ normalizer (L : Set (MulAut W))) (hE : IsElemAbelian q E) :
    Nat.card ↥E ≤ q * Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L)) := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hBE : ∀ b ∈ L, ∀ x ∈ E, b * x = x * b := fun b hb x hx =>
    (s16h_commute_of_normalizes_nine (X := MulAut W) hq hq2 hq3 hL hEn hE.2 x hx b hb).symm
  have hB : IsPGroup 3 ↥L := by
    rcases hL with hE9 | h312
    · exact IsPGroup.of_card (n := 2) (by
        rw [s16h_card_of_isElemAbelianOfRank_two hE9]; norm_num)
    · exact IsPGroup.of_card (n := 3) h312.2.1
  let U : Subgroup W := commSub (⊤ : Subgroup W) L
  have hUB : ∀ b ∈ L, ∀ u ∈ U, b u ∈ U := fun b hb u hu =>
    commSub_top_stable151b (X := L) (g := b)
      (fun x hx => L.mul_mem (L.mul_mem hb hx) (L.inv_mem hb)) u hu
  have hUE : ∀ x ∈ E, ∀ u ∈ U, x u ∈ U := fun x hx u hu =>
    commSub_top_stable151b (X := L) (g := x)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp (hEn hx) y).mp hy) u hu
  have h := s16h_card_le_pow_mul_cent (V := W) hV Nat.prime_three hq (by norm_num) hq2
    hB hE hBE hUB hUE hfix
  have hord3 : orderOf (2 : ZMod 3) = 2 :=
    orderOf_eq_prime (p := 2) (by decide) (by decide)
  have hd3 : 3 ≤ orderOf (2 : ZMod q) := s16h_three_le_orderOf_two_zmod hq hq2 hq3
  have hℓ4 : 4 ≤ Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q)) := by
    rw [hord3]
    have h2 : 2 ∣ Nat.lcm 2 (orderOf (2 : ZMod q)) := Nat.dvd_lcm_left _ _
    have hd : orderOf (2 : ZMod q) ∣ Nat.lcm 2 (orderOf (2 : ZMod q)) := Nat.dvd_lcm_right _ _
    have hdne : orderOf (2 : ZMod q) ≠ 0 := by omega
    have hlcmpos : 0 < Nat.lcm 2 (orderOf (2 : ZMod q)) :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by norm_num) hdne)
    have h3 : 3 ≤ Nat.lcm 2 (orderOf (2 : ZMod q)) :=
      hd3.trans (Nat.le_of_dvd hlcmpos hd)
    obtain ⟨k, hk⟩ := h2
    omega
  have hdiv1 : rk ↥U / Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q)) ≤ 1 := by
    have h6 : 6 / Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q)) ≤ 1 := by
      have : 6 / Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q)) < 2 :=
        (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega
    exact (Nat.div_le_div_right hrk).trans h6
  refine h.trans ?_
  have hq1 : q ^ (rk ↥U / Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q))) ≤ q := by
    simpa using Nat.pow_le_pow_right hq.pos hdiv1
  exact Nat.mul_le_mul_right _ hq1

theorem s16h_card_le_mul_cent_of_E9_eight {W : Type} [CommGroup W] [Finite W]
    (hV : ∀ v : W, v ^ 2 = 1) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    {L E : Subgroup (MulAut W)} (hL : IsElemAbelianOfRank 3 2 ↥L)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 8)
    (hx6 : ∀ x ∈ L, x ≠ 1 → rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers x)) = 6)
    (hEn : E ≤ normalizer (L : Set (MulAut W))) (hE : IsElemAbelian q E) :
    Nat.card ↥E ≤ q * Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L)) := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hBE : ∀ b ∈ L, ∀ x ∈ E, b * x = x * b := fun b hb x hx =>
    (s16h_commute_of_normalizes_nine (X := MulAut W) hq hq2 hq3 (Or.inl hL) hEn hE.2
      x hx b hb).symm
  have hcardL : Nat.card ↥L = 9 := s16h_card_of_isElemAbelianOfRank_two hL
  have hB : IsPGroup 3 ↥L :=
    IsPGroup.of_card (n := 2) (by rw [hcardL]; norm_num)
  obtain ⟨hcommL, hpowL⟩ := s16h_comm_pow_of_isElemAbelianOfRank_two hL
  haveI : Nontrivial ↥L := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hcardL]; norm_num)
  obtain ⟨x₀, hx₀ne⟩ := exists_ne (1 : ↥L)
  obtain ⟨x, hxL, hx1⟩ : ∃ x : MulAut W, x ∈ L ∧ x ≠ 1 :=
    ⟨x₀, x₀.2, fun h => hx₀ne (Subtype.ext h)⟩
  have hx3 : x ^ 3 = 1 := hpowL x hxL
  have hxorder : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h3
  have hPodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, hxorder]; norm_num
  let U : Subgroup W := commSub (⊤ : Subgroup W) L
  let U₁ : Subgroup W := commSub (⊤ : Subgroup W) (Subgroup.zpowers x)
  let U₂ : Subgroup W := U ⊓ fixV (Subgroup.zpowers x)
  have hUL : ∀ b ∈ L, ∀ u ∈ U, b u ∈ U := fun b hb u hu =>
    commSub_top_stable151b (X := L) (g := b)
      (fun y hy => L.mul_mem (L.mul_mem hb hy) (L.inv_mem hb)) u hu
  have hxU : ∀ y ∈ Subgroup.zpowers x, ∀ u ∈ U, y u ∈ U := fun y hy u hu =>
    hUL y (Subgroup.zpowers_le.2 hxL hy) u hu
  have hU₁leU : U₁ ≤ U := commSub_mono le_rfl (Subgroup.zpowers_le.2 hxL)
  have hrk1 : rk ↥U₁ = 6 := hx6 x hxL hx1
  have hsup : commSub U (Subgroup.zpowers x) ⊔ U₂ = U := (coprime_decomp hPodd hV hxU).1
  have hinf_top : U₁ ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
    have h := (coprime_decomp hPodd hV (W := ⊤)
      (fun g _ w _ => Subgroup.mem_top w)).2
    simpa [U₁] using h
  have hU₁U₂_sup : U₁ ⊔ U₂ = U := by
    apply le_antisymm
    · exact sup_le hU₁leU inf_le_left
    · rw [← hsup]
      exact sup_le_sup (commSub_mono le_top le_rfl) le_rfl
  have hU₁U₂ : U₁ ⊓ U₂ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc U₁ ⊓ U₂ ≤ U₁ ⊓ fixV (Subgroup.zpowers x) := inf_le_inf_left U₁ inf_le_right
      _ = ⊥ := hinf_top
  have hrkU₂ : rk ↥U₂ = 2 := by
    have h := rk_sup_add_rk_inf U₁ U₂
    rw [hU₁U₂_sup, hU₁U₂, rk_bot, hrk1, hrk] at h
    omega
  have hU₁L : ∀ b ∈ L, ∀ u ∈ U₁, b u ∈ U₁ := fun b hb u hu =>
    s16h_commSub_zpowers_invariant (U := ⊤) (hcommL b hb x hxL)
      (fun w _ => Subgroup.mem_top w) hu
  have hU₂L : ∀ b ∈ L, ∀ u ∈ U₂, b u ∈ U₂ := fun b hb u hu =>
    s16h_inf_fixV_zpowers_invariant (hcommL b hb x hxL) (hUL b hb) hu
  have hUE : ∀ y ∈ E, ∀ u ∈ U, y u ∈ U := fun y hy u hu =>
    commSub_top_stable151b (X := L) (g := y)
      (fun z hz => (Subgroup.mem_normalizer_iff.mp (hEn hy) z).mp hz) u hu
  have hEx : ∀ y ∈ E, y * x = x * y := fun y hy => (hBE x hxL y hy).symm
  have hU₁E : ∀ y ∈ E, ∀ u ∈ U₁, y u ∈ U₁ := fun y hy u hu =>
    s16h_commSub_zpowers_invariant (U := ⊤) (hEx y hy)
      (fun w _ => Subgroup.mem_top w) hu
  have hU₂E : ∀ y ∈ E, ∀ u ∈ U₂, y u ∈ U₂ := fun y hy u hu =>
    s16h_inf_fixV_zpowers_invariant (hEx y hy) (hUE y hy) hu
  have hfix1 : U₁ ⊓ fixV L = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right (fixV L) hU₁leU).trans hfix.le)
  have hfix2 : U₂ ⊓ fixV L = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right (fixV L) inf_le_left).trans hfix.le)
  have hord3 : orderOf (2 : ZMod 3) = 2 :=
    orderOf_eq_prime (p := 2) (by decide) (by decide)
  have hd3 : 3 ≤ orderOf (2 : ZMod q) := s16h_three_le_orderOf_two_zmod hq hq2 hq3
  have hℓ4 : 4 ≤ Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q)) := by
    rw [hord3]
    have h2 : 2 ∣ Nat.lcm 2 (orderOf (2 : ZMod q)) := Nat.dvd_lcm_left _ _
    have hd : orderOf (2 : ZMod q) ∣ Nat.lcm 2 (orderOf (2 : ZMod q)) := Nat.dvd_lcm_right _ _
    have hdne : orderOf (2 : ZMod q) ≠ 0 := by omega
    have hlcmpos : 0 < Nat.lcm 2 (orderOf (2 : ZMod q)) :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by norm_num) hdne)
    have h3 : 3 ≤ Nat.lcm 2 (orderOf (2 : ZMod q)) :=
      hd3.trans (Nat.le_of_dvd hlcmpos hd)
    obtain ⟨k, hk⟩ := h2
    omega
  have h6 : 6 / Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q)) ≤ 1 := by
    have : 6 / Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q)) < 2 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    omega
  have h2z : 2 / Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q)) = 0 :=
    Nat.div_eq_of_lt (by omega)
  have hstep1 : Nat.card ↥E ≤ q * Nat.card ↥(E ⊓ centSub U₁) := by
    have h := s16h_card_le_pow_mul_cent (V := W) hV Nat.prime_three hq (by norm_num) hq2
      hB hE hBE hU₁L hU₁E hfix1
    refine h.trans ?_
    have hq1 : q ^ (rk ↥U₁ / Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q))) ≤ q := by
      have hle : rk ↥U₁ / Nat.lcm (orderOf (2 : ZMod 3)) (orderOf (2 : ZMod q)) ≤ 1 := by
        rw [hrk1]; exact h6
      simpa using Nat.pow_le_pow_right hq.pos hle
    exact Nat.mul_le_mul_right _ hq1
  have hstep2 : Nat.card ↥(E ⊓ centSub U₁) ≤
      Nat.card ↥((E ⊓ centSub U₁) ⊓ centSub U₂) := by
    have h := s16h_card_le_pow_mul_cent (V := W) (B := L) (E := E ⊓ centSub U₁) (U := U₂)
      hV Nat.prime_three hq (by norm_num) hq2
      hB (hE.mono inf_le_left)
      (fun b hb y hy => hBE b hb y (Subgroup.mem_inf.mp hy).1)
      hU₂L (fun y hy u hu => hU₂E y (Subgroup.mem_inf.mp hy).1 u hu) hfix2
    rwa [hrkU₂, h2z, pow_zero, one_mul] at h
  have hle3 : (E ⊓ centSub U₁) ⊓ centSub U₂ ≤ E ⊓ centSub U := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨hgE, hgc1⟩ := Subgroup.mem_inf.mp hg1
    refine Subgroup.mem_inf.mpr ⟨hgE, ?_⟩
    have hgsup : g ∈ centSub (U₁ ⊔ U₂) := by
      rw [s16h_centSub_sup]
      exact Subgroup.mem_inf.mpr ⟨hgc1, hg2⟩
    rwa [hU₁U₂_sup] at hgsup
  have hcard3 : Nat.card ↥((E ⊓ centSub U₁) ⊓ centSub U₂) ≤
      Nat.card ↥(E ⊓ centSub U) :=
    Subgroup.card_le_of_le hle3
  calc Nat.card ↥E
      ≤ q * Nat.card ↥(E ⊓ centSub U₁) := hstep1
    _ ≤ q * Nat.card ↥((E ⊓ centSub U₁) ⊓ centSub U₂) := Nat.mul_le_mul_left _ hstep2
    _ ≤ q * Nat.card ↥(E ⊓ centSub U) := Nat.mul_le_mul_left _ hcard3

theorem s16h_card_le_mul_cent_of_shape {W : Type} [CommGroup W] [Finite W]
    (hV : ∀ v : W, v ^ 2 = 1) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    {L E : Subgroup (MulAut W)} (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    (hshape : (IsPOnePlusTwo 3 ↥L ∧ rk ↥(commSub (⊤ : Subgroup W) L) = 6) ∨
      (IsElemAbelianOfRank 3 2 ↥L ∧ rk ↥(commSub (⊤ : Subgroup W) L) = 6) ∨
      (IsElemAbelianOfRank 3 2 ↥L ∧ rk ↥(commSub (⊤ : Subgroup W) L) = 8 ∧
        ∀ x ∈ L, x ≠ 1 → rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers x)) = 6))
    (hEn : E ≤ normalizer (L : Set (MulAut W))) (hE : IsElemAbelian q E) :
    Nat.card ↥E ≤ q * Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L)) := by
  rcases hshape with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact s16h_card_le_mul_cent_of_six hV hq hq2 hq3 (Or.inr h1) hfix h2.le hEn hE
  · exact s16h_card_le_mul_cent_of_six hV hq hq2 hq3 (Or.inl h1) hfix h2.le hEn hE
  · exact s16h_card_le_mul_cent_of_E9_eight hV hq hq2 hq3 h1 hfix h2 h3 hEn hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
