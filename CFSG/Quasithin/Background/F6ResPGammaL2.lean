module

public import CFSG.Quasithin.Background.F6ResPSigmaL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter

namespace F6

namespace PGammaRes

variable {p : ℕ} {K : Type} [Field K] [Finite K]

theorem z2d8_pow_four : ∀ x : Multiplicative (ZMod 2) × DihedralGroup 4, x ^ 4 = 1 := by
  decide

theorem z2d8_mul_involutions : ∀ x : Multiplicative (ZMod 2) × DihedralGroup 4,
    ∃ y z : Multiplicative (ZMod 2) × DihedralGroup 4, y * y = 1 ∧ z * z = 1 ∧ x = y * z := by
  decide

theorem d16_facts : (DihedralGroup.r 1 : DihedralGroup 8) ^ 4 ≠ 1 ∧
    DihedralGroup.sr 0 * (DihedralGroup.r 1 : DihedralGroup 8) ^ 2 ≠
      (DihedralGroup.r 1) ^ 2 * DihedralGroup.sr 0 := by
  decide

theorem wreath_sq_central : ∀ a b : Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2),
    a ^ 4 ≠ 1 → b * a ^ 2 = a ^ 2 * b := by
  decide

theorem not_dihedral_eight_equiv
    (φ : DihedralGroup 8 ≃* Multiplicative (ZMod 2) × DihedralGroup 4) : False :=
  d16_facts.1 (φ.injective (by rw [map_pow, z2d8_pow_four, map_one]))

theorem card_pgl2_psl2 (hp : p.Prime) (hK : Nat.card K = p ^ 2) (hp8 : p % 8 = 3 ∨ p % 8 = 5) :
    ∃ N : ℕ, Odd N ∧ Nat.card (PGL2 K) = 16 * N ∧ Nat.card (PSL2 K) = 8 * N := by
  have h9 := sq_mod_sixteen hp8
  obtain ⟨k, hk⟩ : ∃ k, p ^ 2 = 16 * k + 9 := ⟨p ^ 2 / 16, by omega⟩
  have hsq : (16 * k + 9) ^ 2 - 1 = 16 * (16 * k ^ 2 + 18 * k + 5) := by
    have : (16 * k + 9) ^ 2 = 16 * (16 * k ^ 2 + 18 * k + 5) + 1 := by ring
    omega
  have hp2 : p ≠ 2 := by omega
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp, hp.odd_of_ne_two hp2, by norm_num, hK⟩
  refine ⟨(16 * k + 9) * (16 * k ^ 2 + 18 * k + 5), Nat.odd_mul.mpr
    ⟨⟨8 * k + 4, by ring⟩, ⟨8 * k ^ 2 + 9 * k + 2, by ring⟩⟩, ?_, ?_⟩
  · rw [pgl2_card_formula, hK, hk, hsq]
    ring
  · rw [psl2_card_formula K hodd, hK, hk, hsq]
    have : (16 * k + 9) * (16 * (16 * k ^ 2 + 18 * k + 5)) =
        2 * (8 * ((16 * k + 9) * (16 * k ^ 2 + 18 * k + 5))) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]

theorem finite_pGammaL2 : Finite (PGammaL2 K) := by
  have : Finite (PGL2 K) := PGL2Res.finite_pgl2
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) fun e f hef => by
      ext x
      exact congrFun hef x
  exact Finite.of_injective (fun x : PGammaL2 K => (x.left, x.right)) fun x y hxy =>
    SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)

theorem sylow_pgl2_equiv (hp : p.Prime) (hK : Nat.card K = p ^ 2) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (S : Sylow 2 (PGL2 K)) : Nonempty (S ≃* DihedralGroup 8) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGL2 K) := PGL2Res.finite_pgl2
  have hp2 : p ≠ 2 := by omega
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp, hp.odd_of_ne_two hp2, by norm_num, hK⟩
  obtain ⟨N, hN, hPGL, -⟩ := card_pgl2_psl2 hp hK hp8
  obtain ⟨m, -, ⟨e⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hodd S
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hidx := S.not_dvd_index
  have hmul := (S : Subgroup (PGL2 K)).card_mul_index
  rw [hk, hPGL] at hmul
  have hk4 : k = 4 := by
    have h1 : 2 ^ k ∣ 16 * N := ⟨_, hmul.symm⟩
    have h2 : 16 ∣ 2 ^ k * (S : Subgroup (PGL2 K)).index := ⟨N, hmul⟩
    have hle : 2 ^ k ∣ 2 ^ 4 :=
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)).dvd_of_dvd_mul_right h1
    have hge : 2 ^ 4 ∣ 2 ^ k :=
      (Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr
        (Nat.two_dvd_ne_zero.mp hidx)))).dvd_of_dvd_mul_right h2
    exact le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hle)
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hge)
  have hm : 2 ^ m = 8 := by
    have h1 := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card, hk, hk4] at h1
    omega
  rw [hm] at e
  exact ⟨e⟩

theorem false_of_pgl2_z2d8 (hp : p.Prime) (hK : Nat.card K = p ^ 2)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) (χ : Multiplicative (ZMod 2) × DihedralGroup 4 →* PGL2 K)
    (hχ : Function.Injective χ) : False := by
  set Q := χ.range
  have e : Q ≃* Multiplicative (ZMod 2) × DihedralGroup 4 := (MonoidHom.ofInjective hχ).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGL2 K) := PGL2Res.finite_pgl2
  have hQ16 : Nat.card Q = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 4) (by rw [hQ16]; norm_num)
  obtain ⟨S, hQS⟩ := hQ2.exists_le_sylow
  obtain ⟨eS⟩ := sylow_pgl2_equiv hp hK hp8 S
  have hS16 : Nat.card S = 16 := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
  have hQS' : Q = S := Subgroup.eq_of_le_of_card_ge hQS (by rw [hQ16, hS16])
  exact not_dihedral_eight_equiv (eS.symm.trans ((MulEquiv.subgroupCongr hQS').symm.trans e))

theorem isSquare_det_of_mul_map (hp : p.Prime) (hK : Nat.card K = p ^ 2) (hp2 : p ≠ 2)
    {τ : K ≃+* K} (hττ : ∀ y, τ (τ y) = y) (hτ : ∀ y, τ y = y ^ p)
    (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det ≠ 0) (s : K)
    (e : A * A.map τ = Matrix.scalar (Fin 2) s) : IsSquare A.det := by
  have e00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) e
  have e01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) e
  have e10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) e
  have e11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) e
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hA ⊢
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h2 : (2 : K) ≠ 0 :=
    two_ne_zero_of_odd_card K (by rw [hK]; exact hodd.pow)
  have hts : τ s = s := by
    have htr : τ (A 0 0 * τ (A 0 0) + A 0 1 * τ (A 1 0) +
        (A 1 0 * τ (A 0 1) + A 1 1 * τ (A 1 1))) =
        A 0 0 * τ (A 0 0) + A 0 1 * τ (A 1 0) + (A 1 0 * τ (A 0 1) + A 1 1 * τ (A 1 1)) := by
      simp only [map_add, map_mul, hττ]
      ring
    rw [e00, e11, map_add] at htr
    have : (2 : K) * (τ s - s) = 0 := by linear_combination htr
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  set d := A 0 0 * A 1 1 - A 0 1 * A 1 0 with hd
  have hdet : d * τ d = s ^ 2 := by
    rw [hd, map_sub, map_mul, map_mul]
    linear_combination (A 1 0 * τ (A 0 1) + A 1 1 * τ (A 1 1)) * e00 + s * e11 -
      (A 1 0 * τ (A 0 0) + A 1 1 * τ (A 1 0)) * e01
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [hτ] at hdet
    have : d * d ^ p = 0 := by rw [hdet]; ring
    exact hA (by simpa [hp.ne_zero] using this)
  let _ : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    intro hc
    exact h2 (by rw [← Nat.cast_ofNat, ← hc]; exact ringChar.Nat.cast_ringChar)
  rw [FiniteField.isSquare_iff hchar hA, ← Nat.card_eq_fintype_card, hK]
  obtain ⟨m, rfl⟩ := hodd
  have hexp : (2 * m + 1) ^ 2 / 2 = (2 * m + 2) * m := by
    have : (2 * m + 1) ^ 2 = 2 * ((2 * m + 2) * m) + 1 := by ring
    omega
  rw [hexp, pow_mul, show 2 * m + 2 = (2 * m + 1) + 1 from rfl, pow_succ, ← hτ, mul_comm,
    hdet, ← pow_mul]
  have hsp : s ^ (2 * m) * s = s := by
    rw [← pow_succ, ← hτ, hts]
  calc s ^ (2 * m) = s ^ (2 * m) * s * s⁻¹ := by field_simp
    _ = 1 := by rw [hsp, mul_inv_cancel₀ hs0]

theorem left_mem_range_of_mul_self (hp : p.Prime) (hK : Nat.card K = p ^ 2) (hp2 : p ≠ 2)
    {x : PGammaL2 K} (hx : x * x = 1) (hxr : x.right ≠ 1) :
    x.left ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  set τ := x.right
  have hτ := PSigmaRes.ringAut_apply_eq_pow hp hK τ hxr
  have hττ : ∀ y, τ (τ y) = y := fun y => by
    have := congrArg (fun f : K ≃+* K => f y) (PSigmaRes.ringAut_mul_self hp hK τ)
    simpa using this
  have hleft : x.left * pgl2FieldAut K τ x.left = 1 := by
    have := congrArg SemidirectProduct.left hx
    rwa [SemidirectProduct.mul_left, SemidirectProduct.one_left] at this
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  rw [← hG] at hleft ⊢
  rw [pgl2FieldAut_apply] at hleft
  change Matrix.ProjGenLinGroup.mk G *
    pgl2RingEquiv τ (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K)) G) = 1 at hleft
  rw [pgl2RingEquiv_mk] at hleft
  change Matrix.ProjGenLinGroup.mk (G * Matrix.GeneralLinearGroup.map τ.toRingHom G) = 1
    at hleft
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hleft
  obtain ⟨s, hs⟩ := hleft
  rw [pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.val_det_apply]
  refine isSquare_det_of_mul_map hp hK hp2 hττ hτ (G : Matrix (Fin 2) (Fin 2) K) ?_ s ?_
  · rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  · rw [hs, Matrix.GeneralLinearGroup.coe_mul]
    congr 1

theorem eq_pSigmaL2 (hp : p.Prime) (hK : Nat.card K = p ^ 2) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    {H : Subgroup (PGammaL2 K)} (hL : pGammaL2PSLRange K ≤ H)
    (hrel : (pGammaL2PSLRange K).relIndex H = 2) {P : Subgroup H}
    (e : P ≃* Multiplicative (ZMod 2) × DihedralGroup 4) : H = PSigmaL2 K := by
  set L := pGammaL2PSLRange K
  set ψ : Multiplicative (ZMod 2) × DihedralGroup 4 →* PGammaL2 K :=
    H.subtype.comp (P.subtype.comp e.symm.toMonoidHom)
  have hψ : Function.Injective ψ :=
    H.subtype_injective.comp (P.subtype_injective.comp e.symm.injective)
  have hψH : ∀ z, ψ z ∈ H := fun z => (P.subtype (e.symm z)).2
  obtain ⟨N, hN, -, hPSL⟩ := card_pgl2_psl2 hp hK hp8
  have hLc : Nat.card L = 8 * N := by
    rw [← Nat.card_congr (pGammaL2PSLRangeEquiv K).toEquiv, hPSL]
  obtain ⟨z, hzz, hzL⟩ : ∃ z, z * z = 1 ∧ ψ z ∉ L := by
    by_contra hall
    push Not at hall
    have hle : ψ.range ≤ L := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, w, hy, hw, rfl⟩ := z2d8_mul_involutions x
      rw [map_mul]
      exact L.mul_mem (hall y hy) (hall w hw)
    have h16 := Subgroup.card_dvd_of_le hle
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψ, Subgroup.card_top,
      Nat.card_eq_fintype_card, hLc] at h16
    have h16' : 16 ∣ 8 * N := h16
    obtain ⟨t, ht⟩ := h16'
    obtain ⟨n, hn⟩ := hN
    omega
  set x := ψ z
  have hxH : x ∈ H := hψH z
  have hxx : x * x = 1 := by rw [← map_mul, hzz, map_one]
  have hidx : (L.subgroupOf H).index = 2 := hrel
  have hcoset : ∀ h ∈ H, h ∉ L → h * x⁻¹ ∈ L := by
    intro h hh hhL
    have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨h, hh⟩)
      (b := (⟨x, hxH⟩ : H)⁻¹)).mpr (iff_of_false (by simpa [Subgroup.mem_subgroupOf] using hhL)
        (by simpa [Subgroup.mem_subgroupOf] using hzL))
    simpa [Subgroup.mem_subgroupOf] using hmem
  have hLr : ∀ l ∈ L, l.right = 1 := fun l hl => by
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K l).mp hl
    rfl
  by_cases hxr : x.right = 1
  · exfalso
    have hHr : ∀ h ∈ H, h.right = 1 := fun h hh => by
      by_cases hhL : h ∈ L
      · exact hLr h hhL
      · have := hLr _ (hcoset h hh hhL)
        rwa [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hxr, inv_one,
          mul_one] at this
    have hψr : ∀ z, ψ z ∈ (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range := fun z =>
      ⟨(ψ z).left, PSigmaRes.inl_left_of_right_eq_one (hHr _ (hψH z))⟩
    have hinj : Function.Injective (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) :=
      SemidirectProduct.inl_injective
    refine false_of_pgl2_z2d8 hp hK hp8
      ((MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (ψ.codRestrict _ hψr)) ?_
    intro a b hab
    apply hψ
    have := congrArg Subtype.val ((MonoidHom.ofInjective hinj).symm.injective hab)
    exact this
  · have hxl := left_mem_range_of_mul_self hp hK (by omega) hxx hxr
    have hinlx : SemidirectProduct.inl x.left ∈ L := by
      obtain ⟨y, hy⟩ := hxl
      exact (mem_pGammaL2PSLRange_iff K _).mpr ⟨y, by rw [hy]⟩
    have hLS : L ≤ PSigmaL2 K := le_sup_left
    have hRS : (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K).range ≤ PSigmaL2 K :=
      le_sup_right
    have hxS : x ∈ PSigmaL2 K := by
      rw [← SemidirectProduct.inl_left_mul_inr_right x]
      exact (PSigmaL2 K).mul_mem (hLS hinlx) (hRS ⟨_, rfl⟩)
    apply le_antisymm
    · intro h hh
      by_cases hhL : h ∈ L
      · exact hLS hhL
      · have := (PSigmaL2 K).mul_mem (hLS (hcoset h hh hhL)) hxS
        rwa [inv_mul_cancel_right] at this
    · refine sup_le hL ?_
      rintro _ ⟨τ, rfl⟩
      by_cases hτ : τ = 1
      · rw [hτ, map_one]
        exact H.one_mem
      · have hτx : τ = x.right := RingEquiv.ext fun y => by
          rw [PSigmaRes.ringAut_apply_eq_pow hp hK τ hτ,
            PSigmaRes.ringAut_apply_eq_pow hp hK _ hxr]
        have hx' : SemidirectProduct.inr x.right = (SemidirectProduct.inl x.left)⁻¹ * x :=
          eq_inv_mul_of_mul_eq (SemidirectProduct.inl_left_mul_inr_right x)
        rw [hτx, hx']
        exact H.mul_mem (H.inv_mem (hL hinlx)) hxH

theorem not_sylow_wreath (hp : p.Prime) (hK : Nat.card K = p ^ 2) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (P : Sylow 2 (PGammaL2 K))
    (e : P ≃* Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGL2 K) := PGL2Res.finite_pgl2
  have : Finite (PGammaL2 K) := finite_pGammaL2
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 (PGL2 K)) := inferInstance
  obtain ⟨e₀⟩ := sylow_pgl2_equiv hp hK hp8 S₀
  set ι : PGL2 K →* PGammaL2 K := SemidirectProduct.inl
  have hι : Function.Injective ι := SemidirectProduct.inl_injective
  obtain ⟨P₁, hP₁⟩ := (S₀.isPGroup'.map ι : IsPGroup 2 ((S₀ : Subgroup (PGL2 K)).map ι))
    |>.exists_le_sylow
  set ψ : DihedralGroup 8 →* Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2) :=
    ((Sylow.equiv P₁ P).trans e).toMonoidHom.comp
      (((ι.comp (S₀ : Subgroup (PGL2 K)).subtype).codRestrict (P₁ : Subgroup (PGammaL2 K))
        fun s => hP₁ ⟨s, s.2, rfl⟩).comp e₀.symm.toMonoidHom)
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply e₀.symm.injective
    apply Subtype.ext
    apply hι
    have := congrArg Subtype.val (((Sylow.equiv P₁ P).trans e).injective hab)
    exact this
  have h4 : ψ (DihedralGroup.r 1) ^ 4 ≠ 1 := by
    rw [← map_pow]
    exact fun h => d16_facts.1 (hψ (h.trans (map_one ψ).symm))
  have hc := wreath_sq_central _ (ψ (DihedralGroup.sr 0)) h4
  rw [← map_pow, ← map_mul, ← map_mul] at hc
  exact d16_facts.2 (hψ hc)

end PGammaRes

theorem pGammaL2InspectionFact_holds : PGammaL2InspectionFact := by
  intro p K _ _ hp hK hp8
  exact ⟨fun H hL hrel ⟨P, ⟨e⟩⟩ => PGammaRes.eq_pSigmaL2 hp hK hp8 hL hrel e,
    fun P ⟨e⟩ => PGammaRes.not_sylow_wreath hp hK hp8 P e⟩

end F6

end CFSG.Quasithin
