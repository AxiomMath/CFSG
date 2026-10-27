module

public import CFSG.Quasithin.Background.C41PfG
public import CFSG.Quasithin.Background.C41PfH
public import CFSG.Quasithin.Background.C41PfI

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

namespace C41Pf

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_not_le_normalizer (hA3 : A3Orbits G) {H K : Subgroup G}
    (hH : IsSQTKIn H) (hK : K ∈ cComp H) (hn : ¬ H ≤ Subgroup.normalizer (K : Set G)) :
    ∃ t ∈ H, ⁅K, conjByElt t K⁆ ≤ pCoreOf 2 H ∧
      (K ⊔ pCoreOf 2 H) ⊓ (conjByElt t K ⊔ pCoreOf 2 H) = pCoreOf 2 H := by
  obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (P := ⊥) (H := H) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  obtain ⟨hHT, hcase⟩ := hA3 H T K hH hT hK
  rcases hcase with hTN | ⟨t, htT, -, -, hcomm, hint, -⟩
  · exfalso
    apply hn
    intro x hx
    have hmem : conjByElt x K ∈ conjSubgroupsBy T K := by
      rw [← hHT]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hmem
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjByElt x K = K
    rw [he]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTN y hy)
  · exact ⟨t, hT.1 htT, hcomm, hint⟩

theorem c41KZero_of (hC27 : ASC27Statement G)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hG2 : CFSG.Quasithin.H13.Lem1211NNG2) : C41KZero G := by
  intro H R M L V K h hK hKc hKq hKM hRN ⟨P, hP1, hPp, hPMK, hPR⟩
  by_contra hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hW
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hPK : P ≤ K := hPMK.trans inf_le_right
  have hPM : P ≤ M := hPMK.trans inf_le_left
  have h23 := c2_10_four h
  have h1 := (hC27 H R M K W h23 hK hKq hKc hKM hRN rfl).1
  have hcases := SBc17.asc27_cases hC27 h23 hK hKq hKc hKM hRN rfl
  have hsolv : Group.IsSolvable ↥(autOn (M ⊓ K) W) → False := fun hs =>
    false_of_isSolvable_autOn h1 hPK hPM hPp hP1 hs
  obtain ⟨t, htH, hcomm, hint⟩ :=
    exists_conj_of_not_le_normalizer (a3Orbits_of_a37_a38 hA37 hA38) h.sqtk hK hn
  have hK'H : conjByElt t K ≤ H := by
    intro x hx
    rw [mem_conjByElt] at hx
    have := H.mul_mem (H.mul_mem htH (hKH hx)) (H.inv_mem htH)
    simpa [mul_assoc] using this
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G, E ≤ K → IsElemAbelian p E →
      Nat.card ↥E = p ^ 2 → False := by
    intro p hp hp2 E hEK hE hEc
    have : Fact p.Prime := ⟨hp⟩
    have hE1 : E ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hEc
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    obtain ⟨e, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hE1)
    have heo : orderOf (e : G) = p := orderOf_eq_prime (hE.2 _ e.2)
      (fun h => he1 (Subtype.ext h))
    have hyK' : t * (e : G) * t⁻¹ ∈ conjByElt t K := by
      rw [mem_conjByElt]
      simpa [mul_assoc] using hEK e.2
    have hyo : orderOf (t * (e : G) * t⁻¹) = p := by
      have h0 := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective (e : G)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h0
      rw [h0, heo]
    exact false_of_elemAbelian_pair h.sqtk hKH hK'H hcomm hint hp hp2 hEK hE hEc hyK' hyo
  have hsimple := isSimpleGroup_of_not_le_normalizer hA38 h.sqtk hK hn
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))
      with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hKq.2.2
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h0]
      exact Subgroup.mem_top _
  have hKN : K ≤ Subgroup.normalizer (W : Set G) := le_normalizer_omegaOneCenter K R
  have hliftstar : ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ E : Subgroup ↥(autOn K W), IsElemAbelian p E ∧ Nat.card ↥E = p ^ 2) → False := by
    rintro p hp hp2 ⟨E, hE, hEc⟩
    let φ : ↥K →* ↥(autOn K W) :=
      ((conjAct W).comp (Subgroup.inclusion hKN)).codRestrict (autOn K W) fun k =>
        ⟨Subgroup.inclusion hKN k, k.2, rfl⟩
    have hφ : Function.Surjective φ := by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hker : IsPGroup 2 ↥φ.ker := by
      intro x
      have hxC : ((x : ↥K) : G) ∈ Subgroup.centralizer (W : Set G) := by
        have h0 : conjAct W (Subgroup.inclusion hKN (x : ↥K)) = 1 :=
          congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
        exact (conjAct_eq_one_iff' _).mp h0
      have hxZ : ((x : ↥K) : G) ∈ oTwoZIn K := inf_centralizer_le_oTwoZIn h1 ⟨(x : ↥K).2, hxC⟩
      obtain ⟨w, hw, hwx⟩ := hxZ
      have hw1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) w = 1 := by
        have : QuotientGroup.mk' (CFSG.pCore 2 ↥K) w ∈ Subgroup.center _ := hw
        rw [hZ] at this
        exact Subgroup.mem_bot.mp this
      have hwO : w ∈ CFSG.pCore 2 ↥K := by
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw1
      have hwx' : w = (x : ↥K) := Subtype.ext hwx
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥K) (p := 2)) ⟨w, hwO⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      rw [hwx'] at this
      simpa using this
    obtain ⟨F, hFK, hF, hFc⟩ := exists_elemAbelian_lift φ hφ hker hp hp2 hE hEc
    exact hrank p hp hp2 F hFK hF hFc
  have hsub : autOn (M ⊓ K) W ≤ autOn (K ⊔ R) W := autOn_le_autOn (inf_le_right.trans le_sup_left)
  rcases hcases with ⟨-, -, -, hB⟩ | ⟨-, -, -, -, hB⟩ | ⟨-, -, -, e, Pt, hPt, he⟩ |
      ⟨-, -, -, e, Pt, hPt, he⟩ | ⟨⟨n, α, hn5, hn8, -, hαw, t', ht'R, ht'V, -, -, σ, hσ, hconj⟩,
        hMK⟩ | ⟨hHat, hidx, -⟩ | ⟨hExc, hidx⟩ | ⟨hA6 | hSp, hmax⟩ | ⟨-, hG2two, hmax⟩ |
      ⟨⟨n, F, _, _, hn1, hFc, ⟨e⟩⟩, hmax, -⟩ | ⟨he4 | he5, -, -⟩
  · exact hsolv (isSolvable_of_isBorelIn hB)
  · exact hsolv (isSolvable_of_isBorelIn hB)
  · exact hsolv (isSolvable_of_map_eq hsub e he (isSolvable_stabilizer_of_type_43 hPt))
  · exact hsolv (isSolvable_of_map_eq hsub e he (isSolvable_stabilizer_of_type_2221 hPt))
  ·
    obtain ⟨hα, hkerα, -⟩ := hαw
    by_cases hn6 : n ≤ 6
    · exact hP1 (eq_bot_of_alt_transposition hRN h1 hn5 hn6 α hα hkerα ht'R ht'V hσ hconj hMK
        hPK hPM hPp)
    · have hker2 : IsPGroup 2 ↥α.ker := hkerα ▸ CFSG.pCore_isPGroup
      have hn78 : n = 7 ∨ n = 8 := by omega
      rcases hn78 with rfl | rfl
      · obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_alt7
        obtain ⟨F', hFK, hF, hFc⟩ := exists_elemAbelian_lift α hα hker2 Nat.prime_three
          (by norm_num) hE hEc
        exact hrank 3 Nat.prime_three (by norm_num) F' hFK hF hFc
      · obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_alt8
        obtain ⟨F', hFK, hF, hFc⟩ := exists_elemAbelian_lift α hα hker2 Nat.prime_three
          (by norm_num) hE hEc
        exact hrank 3 Nat.prime_three (by norm_num) F' hFK hF hFc
  · exact hsolv (isSolvable_autOn (isSolvable_inf_of_relIndex (by norm_num) hidx
      (card_of_isHatA6Block hHat)))
  · exact hsolv (isSolvable_autOn (isSolvable_inf_of_relIndex (by norm_num) hidx
      (card_of_isExcA7Block hExc)))
  · exact hsolv (isSolvable_of_c27A6 hRN h1 hA6 hmax)
  ·
    obtain ⟨-, F, _, _, hF4, α, hα, hkerα, -⟩ := hSp
    have hker2 : IsPGroup 2 ↥α.ker := hkerα ▸ CFSG.pCore_isPGroup
    obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sp4 hF4
    obtain ⟨F', hFK, hF, hFc⟩ := exists_elemAbelian_lift α hα hker2 Nat.prime_three
      (by norm_num) hE hEc
    exact hrank 3 Nat.prime_three (by norm_num) F' hFK hF hFc
  · have := isSolvable_of_isMaxParabolic2_g2 hG2 hG2two hmax
    have hle : autOn (M ⊓ K) W ≤ autOn (M ⊓ K) W ⊔ autOn R W := le_sup_left
    exact hsolv (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle))
  ·
    by_cases hn1' : n = 1
    · subst hn1'
      exact hsolv (isSolvable_of_c27SL3_two (by rw [hFc]; norm_num) e hmax)
    · have hq : 3 ≤ Fintype.card F - 1 := by
        rw [hFc]
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (n := Fintype.card F - 1) (by omega)
      have hr2 : r ≠ 2 := by
        rintro rfl
        have hodd : Odd (Fintype.card F - 1) := by
          rw [hFc]
          have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          exact Nat.odd_iff.mpr (by
            have h2 : 2 ^ n % 2 = 0 := by
              rw [Nat.pow_mod]; simp [show n ≠ 0 by omega]
            omega)
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrd)
      exact hliftstar r hr hr2 (exists_elemAbelian_of_mulEquiv e (exists_elemAbelian_sl3 hr hrd))
  · obtain ⟨e⟩ := he4
    exact hliftstar 3 Nat.prime_three (by norm_num)
      (exists_elemAbelian_of_mulEquiv e exists_elemAbelian_sl4_two)
  · obtain ⟨e⟩ := he5
    exact hliftstar 3 Nat.prime_three (by norm_num)
      (exists_elemAbelian_of_mulEquiv e exists_elemAbelian_sl5_two)

end C41Pf

end CFSG.Quasithin
