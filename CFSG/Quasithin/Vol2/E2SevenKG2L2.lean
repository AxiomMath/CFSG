module

public import CFSG.Quasithin.Vol2.E2SevenBender
public import CFSG.Dihedral.Glauberman.DicksonMaxB
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open CFSG.BenderSuzuki.MatrixGroups

theorem two_dvd_of_five_dvd_two_pow_sub_one {n : ℕ} (h : 5 ∣ 2 ^ (2 * n) - 1) : 2 ∣ n := by
  by_contra hn
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨n / 2, by omega⟩
  have h16 : 2 ^ (2 * (2 * j + 1)) = 4 * 16 ^ j := by
    rw [show 2 * (2 * j + 1) = 2 + 2 * (2 * j) by ring, pow_add, pow_mul, pow_mul]
    norm_num
  have hmod : 16 ^ j % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [h16] at h
  omega

theorem odd_of_dvd_dickson {n z : ℕ} (hn : 1 ≤ n)
    (hz : z ∣ (2 ^ n - 1) / Nat.gcd (2 ^ n - 1) 2 ∨ z ∣ (2 ^ n + 1) / Nat.gcd (2 ^ n - 1) 2) :
    Odd z := by
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hodd : Odd (2 ^ n - 1) := Nat.odd_iff.mpr (by omega)
  have hodd' : Odd (2 ^ n + 1) := Nat.odd_iff.mpr (by omega)
  have hgcd : Nat.gcd (2 ^ n - 1) 2 = 1 := Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hodd)
  rw [hgcd, Nat.div_one, Nat.div_one] at hz
  rcases hz with hz | hz
  · exact hodd.of_dvd_nat hz
  · exact hodd'.of_dvd_nat hz

theorem le_of_isPGroup_of_odd_complement {Y : Type*} [Group Y] [Finite Y] {N C Q : Subgroup Y}
    [N.Normal] (hN : IsPGroup 2 N) (hC : Odd (Nat.card C)) (hdisj : Disjoint N C)
    (hsup : N ⊔ C = ⊤) (hQ : IsPGroup 2 Q) : Q ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp : Subgroup.IsComplement' N C :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj (by
      rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
  have hcard := hcomp.card_mul_card
  have h2 : IsPGroup 2 ↥(N ⊔ Q) := IsPGroup.to_sup_of_normal_left' hN hQ (by
    rw [Subgroup.normalizer_eq_top]
    exact le_top)
  obtain ⟨a, ha⟩ := h2.exists_card_eq
  obtain ⟨b, hb⟩ := hN.exists_card_eq
  have hdvd : 2 ^ a ∣ 2 ^ b * Nat.card C := by
    rw [← ha, ← hb, hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hab : 2 ^ a ∣ 2 ^ b :=
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hC)).dvd_of_dvd_mul_right hdvd
  have hle : Nat.card ↥(N ⊔ Q) ≤ Nat.card N := by
    rw [ha, hb]
    exact Nat.le_of_dvd (by positivity) hab
  exact le_sup_right.trans (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm.le

private theorem alternatingFour_sq_comm : ∀ a b : alternatingGroup (Fin 4), a ^ 2 = 1 →
    b ^ 2 = 1 → a * b = b * a := by
  decide

variable {G : Type} [Group G] [Finite G]

theorem isPSL_two_two_of_mulEquiv_psl2 {Q : Type} [Group Q] {m : ℕ} (hm : 2 ≤ m)
    (e : Q ≃* PSL2MatrixGroup (GaloisField 2 m)) : IsPSL 2 2 m Q := by
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩, GaloisField 2 m,
    inferInstance, inferInstance, hcard,
    ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL (GaloisField 2 m) 2 2 m
      (by omega) hcard).symm⟩⟩
  · have := congrArg Prod.snd h
    simp only at this
    omega
  · have := congrArg Prod.snd h
    simp only at this
    omega

omit [Finite G] in
theorem exists_isPSL_of_mulEquiv_psl2 {I : Subgroup G} {n m : ℕ} (hm : m ≠ 0) (hmn : m ∣ n)
    (e : ↥I ≃* PSL2MatrixGroup (GaloisField 2 m)) (h4 : 4 ∣ Nat.card I) :
    ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧ IsPSL 2 2 k ↥I := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · exfalso
    obtain rfl : m = 1 := by omega
    have hF : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by norm_num)
    have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center
      (K := GaloisField 2 1)
    rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1), hF] at hcard
    rw [Nat.card_congr e.toEquiv] at h4
    norm_num at hcard
    rw [hcard] at h4
    norm_num at h4
  · exact ⟨m, hm2, hmn, isPSL_two_two_of_mulEquiv_psl2 hm2 e⟩

omit [Finite G] in
theorem exists_isPSL_of_sup_of_injective {I V W : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n)
    (φ : ↥I →* PSL2MatrixGroup (GaloisField 2 n)) (hφ : Function.Injective φ)
    (hI : I = V ⊔ W) (hV : ∀ v ∈ V, v ^ 2 = 1) (hW : ∀ w ∈ W, w ^ 2 = 1)
    (h4 : 4 ∣ Nat.card I) (hI2 : ¬ IsPGroup 2 I) :
    ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧ IsPSL 2 2 k ↥I := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  set H := φ.range with hHdef
  let ψ : ↥I ≃* ↥H := MonoidHom.ofInjective hφ
  have hcardIH : Nat.card I = Nat.card H := Nat.card_congr ψ.toEquiv
  have hVI : V ≤ I := hI ▸ le_sup_left
  have hWI : W ≤ I := hI ▸ le_sup_right
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV x x.2)⟩
  have hW2 : IsPGroup 2 W := fun x => ⟨1, Subtype.ext (by simpa using hW x x.2)⟩
  set A := V.subgroupOf I with hA
  set B := W.subgroupOf I with hB
  have hAB : A ⊔ B = ⊤ := by
    rw [hA, hB, ← Subgroup.subgroupOf_sup hVI hWI, ← hI, Subgroup.subgroupOf_self]
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using hV _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  have hB2 : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using hW _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  have hABH : A.map ψ.toMonoidHom ⊔ B.map ψ.toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, hAB]
    exact Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective
  have hnot : ¬ IsPGroup 2 H := fun h => hI2 (h.of_equiv ψ.symm)
  have hodd : Odd (2 ^ n - 1) := by
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact Nat.odd_iff.mpr (by omega)
  have hgcd : Nat.gcd (2 ^ n - 1) 2 = 1 := Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hodd)
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 2) (f := n) hF H with
    hE | ⟨z, hz, hHz, -⟩ | ⟨z, hz, hHz, -⟩ | ⟨-, ⟨e4⟩⟩ | ⟨h16, -⟩ | ⟨h5, ⟨e5⟩⟩ |
      ⟨m, t, -, ht, N, C, hNn, hNe, -, -, hCt, hdisj, hsup⟩ | ⟨m, hm, hmn, ⟨eP⟩⟩ |
      ⟨m, hm, hmn, ⟨eG⟩⟩
  ·
    exact (hnot (CFSG.IsElementaryAbelian.isPGroup 2 ↥H)).elim
  ·
    rw [hF] at hz
    obtain ⟨j, hj⟩ := odd_of_dvd_dickson hn hz
    rw [hcardIH, hHz] at h4
    omega
  ·
    rw [hF] at hz
    obtain ⟨j, hj⟩ := odd_of_dvd_dickson hn hz
    rw [hcardIH, hHz] at h4
    omega
  ·
    exfalso
    let χ : ↥I ≃* alternatingGroup (Fin 4) := ψ.trans e4
    have hcomm : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := by
      intro v hv w hw
      have hv' : χ ⟨v, hVI hv⟩ ^ 2 = 1 := by
        rw [← map_pow, show (⟨v, hVI hv⟩ : ↥I) ^ 2 = 1 from Subtype.ext (by simpa using hV v hv),
          map_one]
      have hw' : χ ⟨w, hWI hw⟩ ^ 2 = 1 := by
        rw [← map_pow, show (⟨w, hWI hw⟩ : ↥I) ^ 2 = 1 from Subtype.ext (by simpa using hW w hw),
          map_one]
      have h := alternatingFour_sq_comm _ _ hv' hw'
      rw [← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (χ.injective h)
    have hWN : W ≤ Subgroup.normalizer (V : Set G) := by
      intro w hw
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [← hcomm x hx w hw, mul_assoc, mul_inv_cancel, mul_one]
        exact hx
      · intro hx
        have h1 := hcomm _ hx w hw
        have h2 : x = w * x * w⁻¹ := by
          have : w * x * w⁻¹ * w = w * (w * x * w⁻¹) := h1
          have h3 : w * x = w * (w * x * w⁻¹) := by simpa [mul_assoc] using this
          exact mul_left_cancel h3
        rw [h2]
        exact hx
    exact hI2 (hI ▸ IsPGroup.to_sup_of_normal_left' hV2 hW2 hWN)
  ·
    exfalso
    have h2 : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    omega
  ·
    have h2n : 2 ∣ n := by
      rcases h5 with h5 | h5
      · omega
      · exact two_dvd_of_five_dvd_two_pow_sub_one h5
    obtain ⟨e45⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
    exact ⟨2, le_rfl, h2n, isPSL_two_two_of_mulEquiv_psl2 le_rfl (ψ.trans (e5.trans e45.symm))⟩
  ·
    exfalso
    have hNp : IsPGroup 2 N := by
      have := hNe
      exact CFSG.IsElementaryAbelian.isPGroup 2 ↥N
    have htodd : Odd t := by
      rw [hgcd, Nat.div_one] at ht
      exact hodd.of_dvd_nat ht
    have hCodd : Odd (Nat.card C) := hCt ▸ htodd
    have hAN := le_of_isPGroup_of_odd_complement hNp hCodd hdisj hsup (hA2.map ψ.toMonoidHom)
    have hBN := le_of_isPGroup_of_odd_complement hNp hCodd hdisj hsup (hB2.map ψ.toMonoidHom)
    have htop : (⊤ : Subgroup ↥H) ≤ N := hABH ▸ sup_le hAN hBN
    exact hnot ((hNp.to_le htop).of_equiv Subgroup.topEquiv)
  ·
    exact exists_isPSL_of_mulEquiv_psl2 hm hmn (ψ.trans eP) h4
  ·
    let eQ : PSL2MatrixGroup (GaloisField 2 m) ≃*
        Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m) :=
      MulEquiv.ofBijective (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
        (R := GaloisField 2 m)) ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective, by
          intro x
          obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ x
          exact (CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare A).mpr
            (isSquare_of_charTwo' _)⟩
    exact exists_isPSL_of_mulEquiv_psl2 hm ((Dvd.intro_left 2 rfl).trans hmn)
      (ψ.trans (eG.trans eQ.symm)) h4

theorem kgBenderSubL2_holds : KGBenderSubL2 := by
  intro G _ _ K S V n g hn hK hS hVS hVC hV hV4 hgK hgN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k₀, hB⟩ := exists_fusionBenderBorel_of_isBenderOf (⟨hn, Or.inl hK⟩ : IsBenderOf n ↥K)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  let e' := e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 n (by omega) hF)
  have hVK : V ≤ K := hVS.trans hS.1
  have hWK : conjSub g V ≤ K := by
    intro x hx
    rw [mem_conjSub] at hx
    have := K.mul_mem (K.mul_mem hgK (hVK hx)) (K.inv_mem hgK)
    simpa [mul_assoc] using this
  set I := V ⊔ conjSub g V with hIdef
  have hIK : I ≤ K := sup_le hVK hWK
  have hW : ∀ w ∈ conjSub g V, w ^ 2 = 1 := by
    intro w hw
    rw [mem_conjSub] at hw
    have h1 := hV.2 _ hw
    have h2 : (g⁻¹ * w * g) ^ 2 = g⁻¹ * w ^ 2 * g := by
      simp only [pow_two, mul_assoc, mul_inv_cancel_left]
    rw [h2] at h1
    have h3 := congrArg (fun x => g * x * g⁻¹) h1
    simpa [mul_assoc] using h3
  obtain ⟨a, ha⟩ := (isPGroup_of_isElemAbelian hV).exists_card_eq
  have ha2 : 2 ≤ a := by
    by_contra h
    rw [ha] at hV4
    interval_cases a <;> norm_num at hV4
  have h4 : 4 ∣ Nat.card I := by
    have := Subgroup.card_dvd_of_le (le_sup_left : V ≤ I)
    rw [ha] at this
    exact (show 4 = 2 ^ 2 by norm_num) ▸ (Nat.pow_dvd_pow 2 ha2).trans this
  have hV1 : V ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hV4
    omega
  have hI2 : ¬ IsPGroup 2 I := by
    intro hI2
    obtain ⟨S', hS', hIS'⟩ := exists_isSylowTwoOf_ge hI2 hIK
    have h1 : S = S' := eq_of_isSylowTwoOf_of_inf_ne_bot hB hS hS'
      fun h0 => hV1 (le_bot_iff.mp (h0 ▸ le_inf hVS (le_sup_left.trans hIS')))
    have hSg : IsSylowTwoOf (conjSub g S) K := by
      have := isSylowTwoOf_conjSub hS g
      rwa [conjSub_eq_self (Subgroup.le_normalizer hgK)] at this
    have hVg1 : conjSub g V ≠ ⊥ := fun h0 => hV1 (by
      rw [eq_bot_iff] at h0 ⊢
      intro x hx
      have := h0 (show g * x * g⁻¹ ∈ conjSub g V by rw [mem_conjSub]; simpa [mul_assoc] using hx)
      rw [Subgroup.mem_bot] at this ⊢
      have := congrArg (fun w => g⁻¹ * w * g) this
      simpa [mul_assoc] using this)
    have hSS : S = conjSub g S := eq_of_isSylowTwoOf_of_inf_ne_bot hB hS hSg fun h0 => hVg1
      (le_bot_iff.mp (h0 ▸ le_inf (le_sup_right.trans (hIS'.trans h1.symm.le))
        ((conjSub g).monotone hVS)))
    apply hgN
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have : g * z * g⁻¹ ∈ conjSub g S := by rw [mem_conjSub]; simpa [mul_assoc] using hz
      rwa [← hSS] at this
    · intro hz
      rw [hSS, mem_conjSub] at hz
      simpa [mul_assoc] using hz
  obtain ⟨k, hk2, hkn, hk⟩ := exists_isPSL_of_sup_of_injective (by omega)
    (e'.toMonoidHom.comp (Subgroup.inclusion hIK))
    (e'.injective.comp (Subgroup.inclusion_injective hIK)) rfl hV.2 hW h4 hI2
  exact ⟨k, hk2, hkn, Or.inl hk⟩

end E2

end CFSG.Quasithin
