module

public import CFSG.Quasithin.EmptyFaithful.Gap6R0D
public import CFSG.Quasithin.EmptyFaithful.Gap6R0F
public import CFSG.Quasithin.EmptyFaithful.Gap6R0E

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V] {X Tb : Subgroup (MulAut V)}

theorem exists_involution_gen {Y : Subgroup (MulAut V)} (hY : IsElemAbelian2 Y)
    (hcard : Nat.card Y = 2) :
    ∃ t : MulAut V, t ∈ Y ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ Subgroup.zpowers t = Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : Y ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hcard; omega
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Y)).mp hbot
  have htne : (t : MulAut V) ≠ 1 := fun h => ht1 (Subtype.ext h)
  exact ⟨t, t.2, htne, hY.2 t t.2, zpowers_eq_of_prime_card hcard t.2 htne⟩

theorem central_or_exc (hV : ∀ v : V, v ^ 2 = 1) (hsolv : Group.IsSolvable ↥X)
    (hO2 : pCoreOf 2 X = ⊥) (hsqtk : IsQuotientOfSQTKTC ↥X) (hsyl : Tb ∈ sylow2Of X)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) :
    fixV (fittingOf (Jhat X)) ≤ fixV A ∨
      (rk A = 2 ∧ rAV A = 2 ∧
        rk ↥(commV (fittingOf (Jhat X))) = rk ↥(commV (fittingOf (Jhat X)) ⊓ fixV A) + 3 ∧
        rk ↥(fixV (fittingOf (Jhat X))) = rk ↥(fixV (fittingOf (Jhat X)) ⊓ fixV A) + 1) := by
  by_cases hc : fixV (fittingOf (Jhat X)) ≤ fixV A
  · exact Or.inl hc
  right
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := QhatStar_spec hA
  have hAJ : A ≤ Jhat X := fun a ha => le_Jhat hA ha
  have hJX : Jhat X ≤ X := Jhat_le X
  have hAX : A ≤ X := hAJ.trans hJX
  have hAel := hA2.isElemAbelian2
  set F : Subgroup (MulAut V) := fittingOf (Jhat X) with hFdef
  obtain ⟨hsup, hinf⟩ := commV_sup_fixV hV hO2
  have hV₀ : ∀ g ∈ X, ∀ v ∈ commV F, g v ∈ commV F := fun g hg v hv => apply_mem_commV_F hg hv
  have hC : ∀ g ∈ X, ∀ v ∈ fixV F, g v ∈ fixV F := fun g hg v hv => apply_mem_fixV_F hg hv
  have hfaithA : ∀ a ∈ A, (∀ v ∈ commV F, a v = v) → a = 1 := fun a ha hfix =>
    eq_one_of_fix_commV hV hsolv hO2 (hAJ ha) hfix
  have E1 : rk V = rk ↥(commV F) + rk ↥(fixV F) := rk_split hsup hinf
  have E2 : rk ↥(fixV A) = rk ↥(commV F ⊓ fixV A) + rk ↥(fixV F ⊓ fixV A) :=
    rk_fixV_split hsup hinf (fun g hg => hV₀ g (hAX hg)) (fun g hg => hC g (hAX hg))
  have E3 : rk ↥(fixV A) + rkIdx (fixV A) = rk V := rk_add_rkIdx (fixV A)
  have hk : rk ↥(fixV F ⊓ fixV A) < rk ↥(fixV F) := by
    by_contra hge
    push Not at hge
    exact hc (inf_eq_left.mp (eq_of_le_of_rk_le hV inf_le_left hge))
  have hμ : rk ↥(commV F ⊓ fixV A) < rk ↥(commV F) := by
    by_contra hge
    push Not at hge
    have hV₀le : commV F ≤ fixV A := inf_eq_left.mp (eq_of_le_of_rk_le hV inf_le_left hge)
    exact hA2.ne_bot ((Subgroup.eq_bot_iff_forall _).mpr fun a ha =>
      hfaithA a ha (fun v hv => hV₀le hv a ha))
  have hn : (r : ℚ) * (rk A : ℚ) = (rkIdx (fixV A) : ℚ) := by rw [← hAr]; exact hA2.rAV_mul
  have hrk := rk_le_two_of_qhatStar hV hsolv hO2 hsqtk hA
  have hrkpos := hA2.rk_pos
  obtain ⟨p, hp, hp2, hD0⟩ := exists_odd_prime_comm_ne_bot hsolv hO2 hA2
  have : Fact p.Prime := ⟨hp⟩
  have h13 := D2_13 hV hr hA hp2 rfl hD0
  rcases (show rk A = 1 ∨ rk A = 2 by omega) with h1 | h2
  ·
    exfalso
    have hcardA : Nat.card A = 2 := by
      rw [card_eq_two_pow_of_isPGroup hAel.isPGroup, h1]
      norm_num
    obtain ⟨t, htA, ht1, ht2, htA'⟩ := exists_involution_gen hAel hcardA
    have hnr : (rkIdx (fixV A) : ℚ) = r := by
      rw [← hn, h1]
      simp
    have hD := h13.2.2.1 h1
    have hDF : ⁅pCoreOf p X, A⁆ ≤ F := comm_pCore_le_fitting hAJ le_rfl
    by_cases hp5 : p = 5
    · obtain ⟨-, -, hDcard, -, hdir, -⟩ := h13.2.1 hp5
      exact hc (trivial_on_C_of_direct_sum hV hDF (by rw [hDcard]; exact ⟨2, rfl⟩) hdir)
    · rcases hD.1 with hr1 | hr2'
      · obtain ⟨-, hDcard, -, hdir, -⟩ := hD.2 hr1
        exact hc (trivial_on_C_of_direct_sum hV hDF (by rw [hDcard]; exact ⟨1, rfl⟩) hdir)
      · have hn2 : rkIdx (fixV A) = 2 := by
          have : (rkIdx (fixV A) : ℚ) = 2 := by rw [hnr, hr2']
          exact_mod_cast this
        have hμ1 : rk ↥(commV F) = rk ↥(commV F ⊓ fixV (Subgroup.zpowers t)) + 1 := by
          rw [htA']
          omega
        have hcl := claimA2 hV hsolv hO2 hsyl hgen (hAJ htA) ht2 hμ1
        apply hc
        intro c hcC a ha
        rw [← htA'] at ha
        exact (mem_fixV_zpowers_iff.mpr (hcl c hcC)) a ha
  ·
    obtain ⟨hp3, hhyp⟩ := h13.2.2.2.2 (by omega)
    subst hp3
    have hPp : IsPGroup 3 (pCoreOf 3 X) := pCoreOf_isPGroup 3 X
    have hAP : A ≤ Subgroup.normalizer (pCoreOf 3 X : Set (MulAut V)) := fun a ha =>
      le_normalizer_pCoreOf 3 X (hAX ha)
    have hfaith3 := faithful_pCore_three_of_qhatStar hV hsolv hO2 hA (by omega)
    have hact : ∃ y ∈ pCoreOf 3 X, ∃ a ∈ A, a * y ≠ y * a := by
      by_contra hcon
      push Not at hcon
      obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A)).mp hA2.ne_bot
      exact ha1 (Subtype.ext (hfaith3 a a.2 fun y hy => hcon y hy a a.2))
    obtain ⟨B, hBA, hBcard, y, hy, a, haA, hne⟩ :=
      exists_hyperplane_commutator_ne_bot (by norm_num) hAel hA2.ne_bot hPp hAP hact
    set Q : Subgroup (MulAut V) := pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V)) with hQdef
    have hD' : ⁅Q, A⁆ ≠ ⊥ := commutator_ne_bot_iff.mpr ⟨y, hy, a, haA, hne⟩
    obtain ⟨hDcard, -, hdir, -⟩ := hhyp B hBA hBcard _ rfl hD'
    have hDF : ⁅Q, A⁆ ≤ F := comm_pCore_le_fitting hAJ inf_le_left
    have hα : fixV F ⊓ fixV B ≤ fixV A :=
      inf_fixV_le_of_direct_sum hV (by rw [hDcard]; exact ⟨1, rfl⟩) (fixV_anti hDF) hdir
    have hB2 : IsPGroup 2 B := hAel.isPGroup.to_le hBA
    have hQp : IsPGroup 3 Q := hPp.to_le inf_le_left
    have hQc : ∀ q ∈ Q, ∀ b ∈ B, q * b = b * q := fun q hq b hb =>
      ((Subgroup.mem_centralizer_iff.mp hq.2) b hb).symm
    have hPn : ∀ x ∈ X, ∀ g ∈ pCoreOf 3 X, x * g * x⁻¹ ∈ pCoreOf 3 X := fun x hx g hg =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hx) g).mp hg
    have hAQ : ∀ a ∈ A, ∀ z ∈ Q, a * z * a⁻¹ ∈ Q := by
      intro a ha z hz
      refine ⟨hPn a (hAX ha) z hz.1, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      have hab : Commute b a := hAel.1 b (hBA hb) a ha
      have hzb : b * z = z * b := (Subgroup.mem_centralizer_iff.mp hz.2) b hb
      calc b * (a * z * a⁻¹) = (b * a) * z * a⁻¹ := by group
        _ = a * b * z * a⁻¹ := by rw [hab.eq]
        _ = a * (b * z) * a⁻¹ := by group
        _ = a * (z * b) * a⁻¹ := by rw [hzb]
        _ = a * z * (b * a⁻¹) := by group
        _ = a * z * (a⁻¹ * b) := by rw [hab.inv_right.eq]
        _ = a * z * a⁻¹ * b := by group
    have hβ : commSub (fixV B) A ≠ ⊥ :=
      commSub_fixV_ne_bot hV (by norm_num) hQp hB2 hQc hAQ ⟨y, hy, a, haA, hne⟩
    have hfixAB : fixV A ≤ fixV B := fixV_anti hBA
    have hAnotB : ¬ fixV B ≤ fixV A := fun h => hβ (commSub_eq_bot_iff.mpr h)
    have hBX : B ≤ X := hBA.trans hAX
    have E2B : rk ↥(fixV B) = rk ↥(commV F ⊓ fixV B) + rk ↥(fixV F ⊓ fixV B) :=
      rk_fixV_split hsup hinf (fun g hg => hV₀ g (hBX hg)) (fun g hg => hC g (hBX hg))
    have hCeq : fixV F ⊓ fixV B = fixV F ⊓ fixV A :=
      le_antisymm (le_inf inf_le_left hα) (inf_le_inf_left _ hfixAB)
    have hlt : rk ↥(fixV A) < rk ↥(fixV B) := by
      by_contra hge
      push Not at hge
      exact hAnotB (eq_of_le_of_rk_le hV hfixAB hge).symm.le
    have hcardA : Nat.card A = 4 := by
      rw [card_eq_two_pow_of_isPGroup hAel.isPGroup, h2]
      norm_num
    have hBcard2 : Nat.card B = 2 := by omega
    have hB1 : B ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hBcard2; omega
    have hμB : rk ↥(commV F ⊓ fixV B) < rk ↥(commV F) := by
      by_contra hge
      push Not at hge
      have hV₀le : commV F ≤ fixV B := inf_eq_left.mp (eq_of_le_of_rk_le hV inf_le_left hge)
      exact hB1 ((Subgroup.eq_bot_iff_forall _).mpr fun b hb =>
        hfaithA b (hBA hb) fun v hv => hV₀le hv b hb)
    have hCrk : rk ↥(fixV F ⊓ fixV B) = rk ↥(fixV F ⊓ fixV A) := by rw [hCeq]
    have hn4 : rkIdx (fixV A) ≤ 4 := by
      have : (rkIdx (fixV A) : ℚ) ≤ 4 := by
        rw [← hn, h2]
        push_cast
        linarith
      exact_mod_cast this
    by_cases hmu2 : rk ↥(commV F) = rk ↥(commV F ⊓ fixV A) + 2
    · exfalso
      have hμ1B : rk ↥(commV F) = rk ↥(commV F ⊓ fixV B) + 1 := by omega
      have hBel : IsElemAbelian2 B :=
        ⟨fun a ha b hb => hAel.1 a (hBA ha) b (hBA hb), fun a ha => hAel.2 a (hBA ha)⟩
      obtain ⟨b, hbB, hb1, hb2, hBz⟩ := exists_involution_gen hBel hBcard2
      have hμ1B' : rk ↥(commV F) = rk ↥(commV F ⊓ fixV (Subgroup.zpowers b)) + 1 := by
        rw [hBz]
        exact hμ1B
      have hcl := claimA2 hV hsolv hO2 hsyl hgen (hAJ (hBA hbB)) hb2 hμ1B'
      apply hc
      intro c hcC
      refine hα ⟨hcC, ?_⟩
      intro g hg
      rw [← hBz] at hg
      exact (mem_fixV_zpowers_iff.mpr (hcl c hcC)) g hg
    · have hr2' : r = 2 := by
        have h4 : rkIdx (fixV A) = 4 := by omega
        have : (r : ℚ) * 2 = 4 := by
          have := hn
          rw [h2, h4] at this
          push_cast at this
          exact this
        have : (r : ℚ) = 2 := by linarith
        exact_mod_cast this
      refine ⟨h2, by rw [hAr, hr2'], by omega, by omega⟩

end Gap6

end CFSG.Quasithin
