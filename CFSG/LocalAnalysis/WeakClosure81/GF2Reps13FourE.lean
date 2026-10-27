module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Hyp
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Frobenius
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_three_dvd_component (hW : ∀ w : W, w * w = 1)
    {E : Subgroup (MulAut W)} {M : Subgroup W}
    (hEelem : CFSG.Open.IsElemAbelian 7 E) (hEcard : Nat.card ↥E = 49)
    (hMstab : StableUnder E M) (hMfix : M ⊓ fixV E = ⊥)
    {D : Subgroup (MulAut W)}
    (hD : D ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E) :
    3 ∣ rk ↥(M ⊓ fixV D) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEelem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hproper : D ≠ E := by
    intro hEq
    have hrel := hD.2
    rw [hEq] at hrel
    simp at hrel
  have h_exists : ∃ y ∈ E, y ∉ D := by
    by_contra h
    push Not at h
    exact hproper (le_antisymm hD.1 fun z hz => h z hz)
  obtain ⟨y, hyE, hyD⟩ := h_exists
  have hy1 : y ≠ 1 := by
    intro h
    exact hyD (h.symm ▸ D.one_mem)
  have hy7 : y ^ 7 = 1 := hEelem.2 y hyE
  have hyord : orderOf y = 7 := by
    have hdvd : orderOf y ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hy7
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h7
    · exact absurd (orderOf_eq_one_iff.mp h1) hy1
    · exact h7
  have hyhyp : Subgroup.zpowers y ∈
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E := by
    have hycard : Nat.card ↥(Subgroup.zpowers y) = 7 := by
      rw [Nat.card_zpowers, hyord]
    have hyle : Subgroup.zpowers y ≤ E := Subgroup.zpowers_le.mpr hyE
    refine ⟨hyle, ?_⟩
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers y) (K := E)
    rw [inf_of_le_left hyle, hycard, hEcard] at h
    omega
  have hne : D ≠ Subgroup.zpowers y := by
    intro h
    exact hyD (h ▸ Subgroup.mem_zpowers y)
  have hsup : D ⊔ Subgroup.zpowers y = E :=
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.sup_eq_of_hyperplanes hD hyhyp hne
  have hUy : StableUnder (Subgroup.zpowers y) (M ⊓ fixV D) := by
    intro z' hz' m hm
    rw [Subgroup.mem_inf] at hm ⊢
    refine ⟨hMstab z' (Subgroup.zpowers_le.mpr hyE hz') m hm.1, ?_⟩
    rw [mem_fixV] at hm ⊢
    intro d hd
    have hcomm : d * z' = z' * d :=
      hEcomm d (hD.1 hd) z' (Subgroup.zpowers_le.mpr hyE hz')
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hm.2 d hd]
  have hfix : (M ⊓ fixV D) ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
    rw [inf_assoc, ← w16g_fixV_sup D (Subgroup.zpowers y), hsup, hMfix]
  have hdvd := dParam_dvd_rk hW2 Nat.prime_seven (by norm_num) hyord
    (fun m hm => hUy y (Subgroup.mem_zpowers y) m hm) hfix
  have hdp : dParam 7 = 3 := by
    rw [dParam]
    exact orderOf_eq_prime (by decide) (by decide)
  rwa [hdp] at hdvd

private theorem w16g_component_le_commSub (hW : ∀ w : W, w * w = 1)
    {z : MulAut W} (hz : orderOf z = 7) {E : Subgroup (MulAut W)} {M : Subgroup W}
    (hMstab : StableUnder E M) (hMfix : M ⊓ fixV E = ⊥)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hzE : z ∈ E)
    {D : Subgroup (MulAut W)}
    (hD : D ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E)
    (hzhyp : Subgroup.zpowers z ∈
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E)
    (hDz : D ≠ Subgroup.zpowers z) :
    M ⊓ fixV D ≤ commSub ⊤ (Subgroup.zpowers z) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hZodd : Odd (Nat.card ↥(Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hz]
    norm_num
  have hsup : D ⊔ Subgroup.zpowers z = E :=
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.sup_eq_of_hyperplanes hD hzhyp hDz
  have hUstab : StableUnder (Subgroup.zpowers z) (M ⊓ fixV D) := by
    intro y hy m hm
    rw [Subgroup.mem_inf] at hm ⊢
    refine ⟨hMstab y (Subgroup.zpowers_le.mpr hzE hy) m hm.1, ?_⟩
    rw [mem_fixV] at hm ⊢
    intro d hd
    have hcomm : d * y = y * d :=
      hEcomm d (hD.1 hd) y (Subgroup.zpowers_le.mpr hzE hy)
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hm.2 d hd]
  have hfix : (M ⊓ fixV D) ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
    rw [inf_assoc, ← w16g_fixV_sup D (Subgroup.zpowers z), hsup, hMfix]
  have hdec := CFSG.Quasithin.B1.coprime_decomp hW2 hZodd hUstab
  have hEq : M ⊓ fixV D = commSub (M ⊓ fixV D) (Subgroup.zpowers z) := by
    have h := hdec.1
    rw [hfix, bot_sup_eq] at h
    exact h.symm
  calc M ⊓ fixV D = commSub (M ⊓ fixV D) (Subgroup.zpowers z) := hEq
    _ ≤ commSub ⊤ (Subgroup.zpowers z) := commSub_mono le_top le_rfl

private theorem w16g_mem_hyperplanes_of_card {E D : Subgroup (MulAut W)}
    (hEcard : Nat.card ↥E = 49) (hDE : D ≤ E) (hDcard : Nat.card ↥D = 7) :
    D ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine ⟨hDE, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := D) (K := E)
  rw [inf_of_le_left hDE, hDcard, hEcard] at h
  omega

theorem s134_E_components (hW : ∀ w : W, w * w = 1) {t x x' : MulAut W} (ht : orderOf t = 2)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) (hx : orderOf x = 7)
    (hx' : orderOf x' = 7) (hcomm : x * x' = x' * x) (htx : t * x * t⁻¹ = x')
    (htx' : t * x' * t⁻¹ = x) (hne : x' ∉ Subgroup.zpowers x) :
    rk ↥(commSub ⊤ (Subgroup.zpowers (x * x'⁻¹))) ≤ 6 ∧
      (∀ D ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7
          (Subgroup.zpowers x ⊔ Subgroup.zpowers x'),
        3 ∣ rk ↥(commSub ⊤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x') ⊓ fixV D)) ∧
      ((commSub ⊤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x') ⊓ fixV (Subgroup.zpowers x) = ⊥ ∧
          commSub ⊤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x') ⊓ fixV (Subgroup.zpowers x') =
            ⊥) ∨
        (rk ↥(commSub ⊤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x') ⊓
              fixV (Subgroup.zpowers x)) = 3 ∧
          rk ↥(commSub ⊤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x') ⊓
              fixV (Subgroup.zpowers x')) = 3 ∧
          rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 ∧
          ∀ D ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7
              (Subgroup.zpowers x ⊔ Subgroup.zpowers x'),
            D ≠ Subgroup.zpowers x → D ≠ Subgroup.zpowers x' →
              D ≠ Subgroup.zpowers (x * x'⁻¹) →
              commSub ⊤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x') ⊓ fixV D = ⊥)) := by
  classical
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hx7 : x ^ 7 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx'7 : x' ^ 7 = 1 := by rw [← hx']; exact pow_orderOf_eq_one x'
  have hx_notin_x' : x ∉ Subgroup.zpowers x' := by
    intro hxX'
    apply hne
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers x' := Subgroup.zpowers_le.mpr hxX'
    have heq : Subgroup.zpowers x = Subgroup.zpowers x' :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Nat.card_zpowers, hx', Nat.card_zpowers, hx])
    exact heq.symm ▸ Subgroup.mem_zpowers x'
  set X : Subgroup (MulAut W) := Subgroup.zpowers x with hX
  set X' : Subgroup (MulAut W) := Subgroup.zpowers x' with hX'
  set E : Subgroup (MulAut W) := X ⊔ X' with hE
  set M : Subgroup W := commSub ⊤ E with hM
  set z : MulAut W := x * x'⁻¹ with hz
  have hEelem : CFSG.Open.IsElemAbelian 7 E := by
    rw [hE, hX, hX']
    exact w16g_isElemAbelian_sup_zpowers hx7 hx'7 hcomm
  have hEcard : Nat.card ↥E = 49 := by
    rw [hE, hX, hX']
    have h := w16g_card_sup_zpowers Nat.prime_seven hx hx' hcomm hne
    norm_num at h ⊢
    exact h
  have hEodd : Odd (Nat.card ↥E) := by rw [hEcard]; norm_num
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEelem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hMstab : StableUnder E M := fun e he u hu => CFSG.Quasithin.Asc81c.commSub_stable' he hu
  have hME : commSub M E = M := by
    rw [hM]
    exact CFSG.Quasithin.Asc81c.commSub_commSub_eq' hW2 hEodd
  have hMfix : M ⊓ fixV E = ⊥ := by
    rw [hM, inf_comm]
    exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW2 hEodd
  have hdecomp :=
    inf_fixV_hyperplane_decomposition (W := W) hW2 Nat.prime_seven (by norm_num) E hEelem hMstab hME
  let U : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E → Subgroup W :=
    fun D => M ⊓ fixV (D : Subgroup (MulAut W))
  have hUind : iSupIndep U := hdecomp.1
  have hXhyp : X ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E := by
    refine w16g_mem_hyperplanes_of_card hEcard ?_ ?_
    · rw [hE, hX, hX']
      exact le_sup_left
    · rw [hX, Nat.card_zpowers, hx]
  have hX'hyp : X' ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E := by
    refine w16g_mem_hyperplanes_of_card hEcard ?_ ?_
    · rw [hE, hX, hX']
      exact le_sup_right
    · rw [hX', Nat.card_zpowers, hx']
  have hzE : z ∈ E := by
    rw [hE, hX, hX']
    have h1 : x ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers x' :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    have h2 : x'⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers x' :=
      Subgroup.mem_sup_right (Subgroup.inv_mem (Subgroup.zpowers x') (Subgroup.mem_zpowers x'))
    have h := Subgroup.mul_mem (Subgroup.zpowers x ⊔ Subgroup.zpowers x') h1 h2
    rw [hz]
    exact h
  have hzord : orderOf z = 7 := by
    have hz7 : z ^ 7 = 1 := hEelem.2 z hzE
    have hz1 : z ≠ 1 := by
      intro h
      apply hne
      have h' : x * x'⁻¹ = 1 := by rw [← hz]; exact h
      have hxeq : x = x' := by
        calc x = (x * x'⁻¹) * x' := by group
          _ = 1 * x' := by rw [h']
          _ = x' := one_mul x'
      rw [← hxeq]
      exact Subgroup.mem_zpowers x
    have hdvd : orderOf z ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hz7
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h7
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h7
  have hzhyp : Subgroup.zpowers z ∈
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E := by
    refine w16g_mem_hyperplanes_of_card hEcard (Subgroup.zpowers_le.mpr hzE) ?_
    rw [Nat.card_zpowers, hzord]
  have htz : t * z * t⁻¹ = z⁻¹ := by
    rw [hz]
    calc t * (x * x'⁻¹) * t⁻¹ = (t * x * t⁻¹) * (t * x'⁻¹ * t⁻¹) := by group
      _ = x' * (t * x' * t⁻¹)⁻¹ := by
            rw [htx, mul_inv_rev, mul_inv_rev, inv_inv]
            group
      _ = x' * x⁻¹ := by rw [htx']
      _ = (x * x'⁻¹)⁻¹ := by rw [mul_inv_rev]; group
  have hZrank : IsElemAbelianOfRank 7 1 ↥(Subgroup.zpowers z) :=
    w16g_isElemAbelianOfRank_one_of_card Nat.prime_seven (by rw [Nat.card_zpowers, hzord])
  have hinvZ : ∀ a ∈ Subgroup.zpowers z, t * a * t⁻¹ = a⁻¹ :=
    fun a ha => w16g_conj_inv_of_mem_zpowers htz ha
  have hbridge := rk_commSub_eq_two_mul_of_inverted hW2 ht Nat.prime_seven (by norm_num)
    (by norm_num) hZrank hinvZ
  have hcommZ_le : rk ↥(commSub ⊤ (Subgroup.zpowers z)) ≤ 6 := by
    calc rk ↥(commSub ⊤ (Subgroup.zpowers z))
        = 2 * rk ↥(commSub (commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t)) := hbridge
      _ ≤ 2 * rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
          gcongr
          exact rk_mono (commSub_mono le_top le_rfl)
      _ ≤ 2 * 3 := by gcongr
      _ = 6 := by norm_num
  have hthree : ∀ D ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E,
      3 ∣ rk ↥(M ⊓ fixV D) := fun D hD =>
    w16g_three_dvd_component hW hEelem hEcard hMstab hMfix hD
  have hX_ne_X' : X ≠ X' := by
    intro hEq
    have hxX' : x ∈ X' := by
      rw [← hEq]
      exact Subgroup.mem_zpowers x
    exact hx_notin_x' (hX' ▸ hxX')
  have hXmap : X.map (MulAut.conj t).toMonoidHom = X' := by
    rw [hX, hX', MonoidHom.map_zpowers]
    change Subgroup.zpowers (MulAut.conj t x) = Subgroup.zpowers x'
    rw [MulAut.conj_apply, htx]
  have hX'map : X'.map (MulAut.conj t).toMonoidHom = X := by
    rw [hX, hX', MonoidHom.map_zpowers]
    change Subgroup.zpowers (MulAut.conj t x') = Subgroup.zpowers x
    rw [MulAut.conj_apply, htx']
  have hEconj : E.map (MulAut.conj t).toMonoidHom = E := by
    rw [hE, Subgroup.map_sup, hXmap, hX'map]
    exact sup_comm X' X
  have hMmap : M.map t.toMonoidHom = M := by
    rw [hM]
    have h := CFSG.Quasithin.Asc81c.commSub_map_conj E t
    rw [hEconj] at h
    exact h.symm
  let DX : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E := ⟨X, hXhyp⟩
  let DX' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E := ⟨X', hX'hyp⟩
  have hDXX' : DX ≠ DX' := fun h => hX_ne_X' (congrArg Subtype.val h)
  have hdisj : Disjoint (U DX) (U DX') := hUind.pairwiseDisjoint hDXX'
  have hfixmap : (fixV X).map t.toMonoidHom = fixV X' := by
    have h := CFSG.Quasithin.Asc81c.fixV_map_conj X t
    rw [hXmap] at h
    exact h.symm
  have hGmap : (U DX).map t.toMonoidHom = U DX' := by
    change (M ⊓ fixV X).map t.toMonoidHom = M ⊓ fixV X'
    rw [Subgroup.map_inf _ _ _ t.injective, hMmap, hfixmap]
  have hrank_eq : rk ↥(U DX) = rk ↥(U DX') := by
    have hcard := Subgroup.card_map_of_injective (K := U DX) (f := t.toMonoidHom) t.injective
    rw [hGmap] at hcard
    unfold rk
    rw [hcard]
  have hXz : X ≠ Subgroup.zpowers z := by
    intro h
    have hzX : z ∈ X := h.symm ▸ Subgroup.mem_zpowers z
    have hx'_X : x' ∈ X := by
      have hx'eq : x' = x * z⁻¹ := by
        rw [hz]
        calc x' = x' * x * x⁻¹ := by group
          _ = x * x' * x⁻¹ := by rw [← hcomm]
          _ = x * (x * x'⁻¹)⁻¹ := by group
      rw [hx'eq]
      exact X.mul_mem (Subgroup.mem_zpowers x) (X.inv_mem hzX)
    exact hne hx'_X
  have hX'z : X' ≠ Subgroup.zpowers z := by
    intro h
    have hzX' : z ∈ X' := h.symm ▸ Subgroup.mem_zpowers z
    have hxX' : x ∈ X' := by
      have hxeq : x = z * x' := by rw [hz]; group
      rw [hxeq]
      exact X'.mul_mem hzX' (Subgroup.mem_zpowers x')
    have hx_notin_X' : x ∉ X' := by
      intro hxX'
      exact hx_notin_x' (hX' ▸ hxX')
    exact hx_notin_X' hxX'
  have hGX_le : U DX ≤ commSub ⊤ (Subgroup.zpowers z) :=
    w16g_component_le_commSub hW hzord hMstab hMfix hEcomm hzE hXhyp hzhyp hXz
  have hGX'_le : U DX' ≤ commSub ⊤ (Subgroup.zpowers z) :=
    w16g_component_le_commSub hW hzord hMstab hMfix hEcomm hzE hX'hyp hzhyp hX'z
  have hsum_two : rk ↥(U DX ⊔ U DX') = 2 * rk ↥(U DX) := by
    have h := rk_sup_add_rk_inf (U DX) (U DX')
    rw [hdisj.eq_bot, rk_bot, add_zero] at h
    rw [h, hrank_eq]
    ring
  have h2r_le : 2 * rk ↥(U DX) ≤ rk ↥(commSub ⊤ (Subgroup.zpowers z)) := by
    calc 2 * rk ↥(U DX) = rk ↥(U DX ⊔ U DX') := hsum_two.symm
      _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers z)) :=
          rk_mono (sup_le hGX_le hGX'_le)
  have hr3_le : rk ↥(U DX) ≤ 3 := by omega
  have h3dvd : 3 ∣ rk ↥(U DX) := hthree X hXhyp
  have hrcases : rk ↥(U DX) = 0 ∨ rk ↥(U DX) = 3 := by
    rcases h3dvd with ⟨k, hk⟩
    have hk1 : k ≤ 1 := by omega
    have hk0 : k = 0 ∨ k = 1 := by omega
    rcases hk0 with h0 | h1
    · left; rw [hk, h0]
    · right; rw [hk, h1]
  refine ⟨?_, ?_, ?_⟩
  · simpa [hz] using hcommZ_le
  · intro D hD
    have h := hthree D hD
    simpa [hM, hE, hX, hX'] using h
  · rcases hrcases with hr0 | hr3
    · left
      have hGX_bot : U DX = ⊥ := (rk_eq_zero_iff hW2).mp hr0
      have hGX'_bot : U DX' = ⊥ := by
        have h0' : rk ↥(U DX') = 0 := by rw [← hrank_eq, hGX_bot, rk_bot]
        exact (rk_eq_zero_iff hW2).mp h0'
      constructor
      · simpa [U, DX, hM, hE, hX, hX'] using hGX_bot
      · simpa [U, DX', hM, hE, hX, hX'] using hGX'_bot
    · right
      have hrank_sup : rk ↥(U DX ⊔ U DX') = 6 := by
        rw [hsum_two, hr3]
      have hleWz : U DX ⊔ U DX' ≤ commSub ⊤ (Subgroup.zpowers z) := sup_le hGX_le hGX'_le
      have hWz_eq' : U DX ⊔ U DX' = commSub ⊤ (Subgroup.zpowers z) :=
        eq_of_le_of_rk_le hW2 hleWz (by rw [hrank_sup]; exact hcommZ_le)
      have hWz_eq : commSub ⊤ (Subgroup.zpowers z) = U DX ⊔ U DX' := hWz_eq'.symm
      have hdich : U DX ⊓ U DX' = ⊥ := hdisj.eq_bot
      let f : ↥(U DX) → ↥(commSub ⊤ (Subgroup.zpowers t)) := fun u =>
        ⟨t (u : W) * (u : W)⁻¹,
          Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, (u : W),
            Subgroup.mem_top (u : W), rfl⟩⟩
      have hinj : Function.Injective f := by
        intro u v huv
        have hval : t (u : W) * (u : W)⁻¹ = t (v : W) * (v : W)⁻¹ :=
          congrArg Subtype.val huv
        have hkey : t ((v : W)⁻¹ * (u : W)) = (v : W)⁻¹ * (u : W) := by
          calc t ((v : W)⁻¹ * (u : W)) = (t (v : W))⁻¹ * t (u : W) := by
                rw [map_mul, map_inv]
            _ = (t (v : W))⁻¹ * (t (u : W) * (u : W)⁻¹) * (u : W) := by group
            _ = (t (v : W))⁻¹ * (t (v : W) * (v : W)⁻¹) * (u : W) := by rw [hval]
            _ = (v : W)⁻¹ * (u : W) := by group
        have hwU : ((v : W)⁻¹ * (u : W)) ∈ U DX :=
          (U DX).mul_mem ((U DX).inv_mem v.2) u.2
        have htwU' : t ((v : W)⁻¹ * (u : W)) ∈ U DX' := by
          have h := Subgroup.mem_map_of_mem t.toMonoidHom hwU
          rwa [hGmap] at h
        have hwU' : ((v : W)⁻¹ * (u : W)) ∈ U DX' := by
          rw [← hkey]
          exact htwU'
        have hwbot : ((v : W)⁻¹ * (u : W)) ∈ U DX ⊓ U DX' := ⟨hwU, hwU'⟩
        rw [hdich, Subgroup.mem_bot] at hwbot
        exact Subtype.ext (inv_mul_eq_one.mp hwbot).symm
      have hcard_le := Nat.card_le_card_of_injective f hinj
      have hrkT_ge : 3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
        have hcardU : Nat.card ↥(U DX) = 2 ^ rk ↥(U DX) := card_eq_two_pow hW2 (U DX)
        have hcardT : Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) =
            2 ^ rk ↥(commSub ⊤ (Subgroup.zpowers t)) :=
          card_eq_two_pow hW2 (commSub ⊤ (Subgroup.zpowers t))
        rw [hcardU, hcardT] at hcard_le
        have hle := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard_le
        omega
      have hrkT : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 := le_antisymm hrk hrkT_ge
      refine ⟨?_, ?_, hrkT, ?_⟩
      · simpa [U, DX, hM, hE, hX, hX'] using hr3
      · simpa [U, DX', hM, hE, hX, hX'] using (hrank_eq.symm.trans hr3)
      · intro D hD hDx hDx' hDz
        have hD_le : U ⟨D, hD⟩ ≤ commSub ⊤ (Subgroup.zpowers z) :=
          w16g_component_le_commSub hW hzord hMstab hMfix hEcomm hzE hD hzhyp hDz
        have hDXne : DX ≠ ⟨D, hD⟩ := by
          intro h
          exact hDx (hX ▸ (congrArg Subtype.val h).symm)
        have hDX'ne : DX' ≠ ⟨D, hD⟩ := by
          intro h
          exact hDx' (hX' ▸ (congrArg Subtype.val h).symm)
        have hdisjD : Disjoint (U ⟨D, hD⟩) (U DX ⊔ U DX') := by
          refine (hUind ⟨D, hD⟩).mono_right (sup_le ?_ ?_)
          · exact le_iSup₂ (f := fun j (_ : j ≠ ⟨D, hD⟩) => U j) DX hDXne
          · exact le_iSup₂ (f := fun j (_ : j ≠ ⟨D, hD⟩) => U j) DX' hDX'ne
        have hle : U ⟨D, hD⟩ ≤ U DX ⊔ U DX' := by
          rw [← hWz_eq]
          exact hD_le
        have hbot : U ⟨D, hD⟩ ⊓ (U DX ⊔ U DX') = ⊥ := hdisjD.eq_bot
        rw [inf_eq_left.mpr hle] at hbot
        simpa [U, hM, hE, hX, hX'] using hbot

end CFSG.LocalAnalysis.WeakClosure81
