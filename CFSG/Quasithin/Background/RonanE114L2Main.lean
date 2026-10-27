module

public import CFSG.Quasithin.Background.RonanE114L2Sig
public import CFSG.Quasithin.Background.RonanE114L2
public import CFSG.Quasithin.Background.RonanE114L2In
public import CFSG.Quasithin.Background.RonanE114L2Max
public import CFSG.Quasithin.Background.RonanE114L2Num
public import CFSG.Quasithin.Background.RonanE114L2Out

public section

namespace CFSG.Quasithin.RonanE114.L2

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open CFSG.Quasithin.Vol2.Ch11 CFSG.Quasithin.Vol2.Ch11.SecU1

theorem sigmaPGammaL2_pow {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h27 : 27 ≤ p ^ f)
    (v : PGammaL2 K) (hv : orderOf v = 2) (hvr : v.right ≠ 1) :
    SigmaFacts (pGammaL2PSLRange K) v := by
  have hσ : orderOf v.right = 2 := by
    have h2 : v ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hv])
    have h3 : v.right ^ 2 = 1 := by
      have h := map_pow (SemidirectProduct.rightHom (φ := pgl2FieldAut K)) v 2
      rw [h2, map_one, SemidirectProduct.rightHom_eq_right] at h
      exact h.symm
    exact orderOf_eq_prime h3 hvr
  obtain ⟨K₀, -, hcard, -⟩ := exists_fixed_subfield v.right hσ
  set q₀ := Nat.card K₀ with hq₀
  have hdvd : q₀ ∣ p ^ f := ⟨q₀, by rw [← hK, hcard]; ring⟩
  obtain ⟨j, -, hjq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hq5 : 5 ≤ q₀ := by
    by_contra hlt
    have : q₀ ≤ 4 := by omega
    have : q₀ ^ 2 ≤ 16 := by nlinarith
    rw [hK] at hcard
    omega
  have hj1 : 1 ≤ j := by
    by_contra hj
    obtain rfl : j = 0 := by omega
    rw [pow_zero] at hjq
    omega
  exact sigmaPGammaL2_gen ⟨p, j, hp, hp.odd_of_ne_two hp2, hj1, hjq⟩ hq5 hcard v hv hvr

variable {G : Type} [Group G] [Finite G]

theorem setting_of_psl2_pow
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hF : IsPSL 2 p f ↥(CFSG.generalizedFitting G)) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : Setting (CFSG.generalizedFitting G) := by
  have : Fact p.Prime := ⟨hp⟩
  set L := CFSG.generalizedFitting G with hLdef
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hF
  let e : L ≃* PSL2 K :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hf0 : 0 < f := by omega
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hpodd, hf0, hK⟩
  have h27 : 27 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hq2 : p ^ f % 2 = 1 := Nat.odd_iff.mp (hpodd.pow (n := f))
  have hq4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
  have hnab : ∃ a b : L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hZ := psl2_center_eq_bot K
    have hbig : Nat.card (PSL2 K) ≠ 1 := fun h1 => by
      have h2 := CFSG.Walter.Suzuki.two_dvd_card_psl2 K hodd
      rw [show Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = 1 from h1] at h2
      norm_num at h2
    apply hbig
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
    have ha : a ∈ Subgroup.center (PSL2 K) := Subgroup.mem_center_iff.mpr fun c => by
      have := hcon (e.symm c) (e.symm a)
      exact e.symm.injective (by rw [map_mul, map_mul, this])
    have hb : b ∈ Subgroup.center (PSL2 K) := Subgroup.mem_center_iff.mpr fun c => by
      have := hcon (e.symm c) (e.symm b)
      exact e.symm.injective (by rw [map_mul, map_mul, this])
    rw [hZ, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT hFT
  have hLn := hAS.normal
  obtain ⟨ι, hι⟩ := exists_adapted hK hodd (by omega) e hAS.centralizer_eq
  have hr : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      ((p ^ f % 4 = 1 → r ∣ p ^ f - 1) ∧ (p ^ f % 4 = 3 → r ∣ p ^ f + 1)) := by
    rcases hq4 with h4 | h4
    · obtain ⟨r, hrp, hr2, hrd⟩ := exists_odd_prime_dvd_half_pred hp hp2 (by omega)
        (by omega) h4
      exact ⟨r, hrp, hr2, fun _ => dvd_trans hrd (Nat.div_dvd_of_dvd (by omega)),
        fun h => absurd h (by omega)⟩
    · have hfodd : Odd f := by
        by_contra hfe
        obtain ⟨g, hg⟩ := Nat.not_odd_iff_even.mp hfe
        have h1 : p ^ f % 4 = 1 := by
          rw [hg, ← two_mul, pow_mul, Nat.pow_mod]
          have : p ^ 2 % 4 = 1 := by
            rcases hpodd with ⟨c, hc⟩
            rw [hc]
            ring_nf
            omega
          rw [this]
          simp
        omega
      obtain ⟨r, hrp, hr2, hrd⟩ := exists_odd_prime_dvd_half_succ hp hp2 hf hfodd
      exact ⟨r, hrp, hr2, fun h => absurd h (by omega),
        fun _ => dvd_trans hrd (Nat.div_dvd_of_dvd (by omega))⟩
  obtain ⟨r, hrp, hr2, hrq⟩ := hr
  refine ⟨hAS, ?_, fun x hx y hy h1 h2 => inner_conj_gen e hK hpodd hf0 hx hy h1 h2,
    fun x hx h1 => inner_solvable_gen e hK hpodd hf0 (by omega) hx h1,
    fun x hx h1 H hlt hHL => inner_max_gen e
      (fun t ht => psl2_centralizer_involution_isCoatom_gen hK hpodd (by omega) h27 ht) hx h1 H hlt
      hHL,
    fun x hx h1 y hy hcen => inner_center_gen e hK hpodd hf0 (by omega) hx h1 hy hcen,
    fun x hx h1 => inner_torus_gen e hLn hK hpodd hf0 (by omega) hrp hr2 hrq hx h1,
    fun b hbL hb2 => ?_,
    fun t₁ t₂ h₁ h₂ o₁ o₂ hc => outer_pair_gen hι hp hp2 hK h₁ h₂ o₁ o₂ hc⟩
  · rw [Nat.card_congr e.toEquiv]
    exact CFSG.Walter.Suzuki.two_dvd_card_psl2 K hodd
  · by_cases hr : (ι b).right = 1
    · rcases hq4 with h4 | h4
      · exact Or.inl (oddTorus_of_adapted hLn hι hodd (by rw [hK]; exact h4) (by omega) hbL hb2 hr)
      · exact Or.inl (oddTorus_of_adapted_three hLn hι hodd (by rw [hK]; exact h4) (by omega) hbL
          hb2 hr)
    · refine Or.inr (sigmaFacts_of_adapted hι (sigmaPGammaL2_pow hp hp2 hK h27 (ι b) ?_ hr))
      rw [orderOf_injective ι hι.1 b, hb2]

theorem nParam_le_one_of_psl2_pow
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hF : IsPSL 2 p f ↥(CFSG.generalizedFitting G)) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ 1 :=
  nParam_le_one_of_setting torusMember_holds componentMember_holds
    (setting_of_psl2_pow hp hp2 hf hs hF hT hFT)

end CFSG.Quasithin.RonanE114.L2

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11

variable {G : Type} [Group G] [Finite G]

theorem nParam_eq_one_of_isPSL2
    {T : Subgroup G} (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 < p ^ e) (hF : IsPSL 2 p e (ASInputs.FStar G)) :
    E1.nParam (⊤ : Subgroup G) = 1 := by
  by_cases he : e ≤ 2
  · exact nParam_eq_one_of_isPSL2_of_le_two hSQ hFs hT hFT hp hp2 h5 he hF
  · refine le_antisymm (L2.nParam_le_one_of_psl2_pow hp hp2 (by omega) hFs hF hT.1 hFT) ?_
    exact SecE3.one_le_nParam_of_not_odd (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G)
      (two_dvd_card_of_isPSL2 hp hp2 (by omega) hF))

end CFSG.Quasithin.RonanE114
