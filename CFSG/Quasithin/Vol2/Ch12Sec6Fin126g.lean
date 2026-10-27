module

public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126b
public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126f

public section

namespace CFSG.Quasithin.H13

namespace F126

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom S126 Equiv
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_range_le {W : Type*} [Group W] [Finite W] (φ : W →* W) (D : Subgroup W) :
    Nat.card φ.range ≤ D.index * Nat.card (D.map φ) := by
  have h1 := (D.map φ.rangeRestrict).card_mul_index
  have h2 : (D.map φ.rangeRestrict).index ≤ D.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_map_dvd D φ.rangeRestrict_surjective)
  have h3 : Nat.card (D.map φ.rangeRestrict) = Nat.card (D.map φ) := by
    rw [← Subgroup.card_map_of_injective φ.range.subtype_injective, Subgroup.map_map,
      MonoidHom.subtype_comp_rangeRestrict]
  calc Nat.card φ.range = Nat.card (D.map φ.rangeRestrict) * (D.map φ.rangeRestrict).index :=
        h1.symm
    _ ≤ Nat.card (D.map φ) * D.index := Nat.mul_le_mul h3.le h2
    _ = D.index * Nat.card (D.map φ) := mul_comm _ _

theorem card_tilde_le (V₁ A : Subgroup G) (U : Subgroup (SecQuot (N1 V₁) V₁)) :
    Nat.card ((tildeOf V₁ A).subgroupOf U) ≤ Nat.card A := by
  calc Nat.card ((tildeOf V₁ A).subgroupOf U) ≤ Nat.card (tildeOf V₁ A) := by
        refine Nat.card_le_card_of_injective (fun s => (⟨((s : U) : SecQuot (N1 V₁) V₁), s.2⟩ :
          tildeOf V₁ A)) fun a b hab => ?_
        have := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext this)
    _ ≤ Nat.card ↥(A.subgroupOf (N1 V₁)) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    _ ≤ Nat.card A := by
        refine Nat.card_le_card_of_injective (fun a => (⟨((a : N1 V₁) : G), a.2⟩ : A))
          fun a b hab => ?_
        have := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext this)

omit [Finite G] in
theorem thetaH_mul_inv_mem {T V L V₁ Vp H : Subgroup G} (h : HypF91 T V L V₁ Vp H) {b : G}
    (hb : b ∈ H) {A : Subgroup G} {u : G} (huN : u ∈ N1 V₁) (hA : b * u * b⁻¹ * u⁻¹ ∈ A)
    (w : ↥(UT V₁ Vp H)) (hw : secMk (N1 V₁) V₁ ⟨u, huN⟩ = w) :
    thetaH h ⟨b, hb⟩ w * w⁻¹ ∈ (tildeOf V₁ A).subgroupOf (UT V₁ Vp H) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, thetaH_apply, ← hw,
    thetaH_apply_secMk, ← map_inv, ← map_mul]
  exact secMk_mem_secImg hA

omit [Finite G] in
theorem nine_dvd_card_star_MH {L H : Subgroup G} (e : S126.HStar H ≃* S53)
    (hidx : (Subgroup.normalizer (L : Set G) ⊓ H).relIndex H = 5) :
    9 ∣ Nat.card (S126.star H (Subgroup.normalizer (L : Set G) ⊓ H)) := by
  set M := Subgroup.normalizer (L : Set G) ⊓ H
  have hd : (S126.star H M).index ∣ 5 := by
    rw [← hidx]
    exact Subgroup.index_map_dvd (M.subgroupOf H) (QuotientGroup.mk'_surjective _)
  have hc := (S126.star H M).card_mul_index
  rw [card_Q e] at hc
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hd with h1 | h5
  · rw [h1, mul_one] at hc
    rw [hc]
    norm_num
  · rw [h5] at hc
    have h144 : Nat.card (S126.star H M) = 144 := by omega
    rw [h144]
    norm_num

theorem exists_conj_le_R1 {T V L V₁ Vp H : Subgroup G} (h : HypF98 T V L V₁ Vp H)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) :
    ∃ c ∈ H, conjSub c (F8.Uγ V H (g : G)) ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  have hV2 := (h.F913_2 s).2 γ₂ hγ₂nb hd
  obtain ⟨c, hc, hcγ⟩ := stab_transitive_on_nbrs hγ₂nb
    (show F8.γ₀ T L H ∈ nbrs (F8.γ₁ T L H) from (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H)).symm)
  have hcH : (c : G) ∈ H := by rwa [stab_γ₁ h.amalgamHypV.le₂] at hc
  have hc1 : c • F8.γ₁ T L H = F8.γ₁ T L H := smul_eq_of_mem_stab hc
  refine ⟨c, hcH, ?_⟩
  have h1 := conjSub_mono (c : G) hV2
  rw [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, hc1, hcγ,
    inf_comm, h.F913_1] at h1
  exact h1

variable {T L V H : Subgroup G} [IsMulCommutative ↥V]

theorem false_of_case3 (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (h98 : HypF98 T V L F.V1 F.V5 H) (h3 : Case3 T L F.V1 H) : False := by
  obtain ⟨⟨e⟩, hidx, hR1, hR1c, hR1sq⟩ := h3
  have h := h98.toHypF91
  let _ : CommGroup ↥(UT F.V1 F.V5 H) := commGroupOfElemAbelian h.isElemAbelian_tilde
  have hW : ∀ w : ↥(UT F.V1 F.V5 H), w ^ 2 = 1 := fun w =>
    Subtype.ext (h.isElemAbelian_tilde.2 w w.2)
  have hUN : conjClosure F.V5 H ≤ N1 F.V1 :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  set x := psiH h (xQ e) with hx
  set t := psiH h (tQ e) with ht
  have hx3 : x ^ 3 = 1 := by rw [hx, ← map_pow, xQ_pow_three, map_one]
  have hxfix : ∀ w, x w = w → w = 1 := fpf_xQ F hH h e
  have ht2 : t ^ 2 = 1 := by rw [ht, ← map_pow, tQ_sq, map_one]
  have htx : t * x * t⁻¹ = x ^ 2 := by
    rw [ht, hx, ← map_inv, ← map_mul, ← map_mul, tQ_conj, map_pow]
  set ρ := (psiH h).comp (ιA5 e) with hρdef
  have hρ : Function.Injective ρ := (psiH_injective h).comp (ιA5_injective e)
  have hρx : ∀ a, ρ a * x = x * ρ a := fun a => by
    rw [hρdef, hx, MonoidHom.comp_apply, ← map_mul, ← map_mul, ιA5_comm_xQ]
  have hρt : ∀ a, ρ a * t = t * ρ a := fun a => by
    rw [hρdef, ht, MonoidHom.comp_apply, ← map_mul, ← map_mul, ιA5_comm_tQ]
  obtain ⟨b₀, hb₀2, hb₀1⟩ : ∃ b : ↥(alternatingGroup (Fin 5)), b ^ 2 = 1 ∧ b ≠ 1 :=
    ⟨⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩, by decide, by decide⟩
  have hcard8 : 8 ≤ Nat.card ↥(UT F.V1 F.V5 H) := by
    have h16 := sixteen_le_card_cm_of_a5 hW hx3 hxfix ht2 htx ρ hρ hρx hρt hb₀2 hb₀1
    have := Subgroup.card_le_card_group (cm (ρ b₀))
    omega
  have hnt : ∀ q : S126.HStar H, Nat.card (cm (psiH h q)) ≠ 2 := fun q =>
    card_cm_ne_two hx3 hxfix hcard8 (psiH_conj h e q)
  have hne1 : ∀ b (hb : b ∈ H), b ∉ pCoreOf 2 H → Nat.card (cm (thetaH h ⟨b, hb⟩)) ≠ 1 := by
    intro b hb hbQ h1
    have hθ := eq_one_of_cm_eq_bot (Subgroup.card_eq_one.1 h1)
    rw [← psiH_mk] at hθ
    exact hbQ (mkH_eq_one_iff.1 (psiH_injective h (hθ.trans (map_one _).symm)))
  obtain ⟨γ, γ', g, s⟩ := h98.exists_F8Setup
  have hlt : F8.Dγ F.V5 F.V1 H (g : G) < F8.Uγ F.V5 H (g : G) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun heq => ?_
    obtain ⟨W', hW', hV₁W', hW'V, hcomm⟩ : ∃ W' : Subgroup G, IsElemAbelian 2 W' ∧ F.V1 ≤ W' ∧
        W' ≤ conjClosure V H ∧ ⁅W', F8.Uγ F.V5 H (g : G)⁆ = F.V1 := by
      rcases h98.F916_1 s heq.symm with ⟨-, -, -, htr⟩ | ⟨-, -, -, -, htr⟩
      · exact ⟨_, h98.F911_3, h.V₁_le_Vp.trans (le_conjClosure _ _),
          conjClosure_le fun _ hk _ hz => mem_conjClosure hk (h.Vp_le_V hz), htr⟩
      · exact ⟨V, h.elemAbelian, h.V₁_le_V, le_conjClosure V H, htr⟩
    obtain ⟨-, hBH, -, hBQ, -, -⟩ := h98.exists_qcrit_of_transvection s hW' hV₁W' hW'V hcomm
    have hBU : ⁅conjSub (g : G)⁻¹ W', conjClosure F.V5 H⁆ = conjSub (g : G)⁻¹ F.V1 := by
      have hU : conjSub (g : G)⁻¹ (F8.Uγ F.V5 H (g : G)) = conjClosure F.V5 H := by
        rw [F8.Uγ, conjSub_conjSub_inv]
      rw [← hU, conjSub_commutator, hcomm]
    obtain ⟨b, hbB, hbQ⟩ := IsConcreteLE.not_le_iff_exists.1 hBQ
    have hb := hBH hbB
    have hle : cm (thetaH h ⟨b, hb⟩) ≤
        (tildeOf F.V1 (conjSub (g : G)⁻¹ F.V1)).subgroupOf (UT F.V1 F.V5 H) := by
      rintro _ ⟨w, -, rfl⟩
      obtain ⟨⟨u, huN⟩, huU, hu⟩ := mem_secImg.1 w.2
      have hc := Subgroup.commutator_mem_commutator hbB huU
      rw [hBU, commutatorElement_def] at hc
      exact thetaH_mul_inv_mem h hb huN hc w hu
    have hcm2 : Nat.card (cm (thetaH h ⟨b, hb⟩)) ≤ 2 :=
      (Subgroup.card_le_of_le hle).trans ((card_tilde_le _ _ _).trans
        ((card_conjSub _ _).trans h.card_V₁).le)
    have h1 := hne1 b hb hbQ
    have h0 : Nat.card (cm (thetaH h ⟨b, hb⟩)) ≠ 0 := Nat.card_pos.ne'
    have h2 := hnt (QuotientGroup.mk ⟨b, hb⟩)
    rw [psiH_mk] at h2
    omega
  obtain ⟨δ, δ', k, sk, hpos, hle, -⟩ := h98.F916_4 s hlt
  obtain ⟨c, hcH, hcR⟩ := exists_conj_le_R1 h98 sk
  have hcU : conjSub c (F8.Uγ F.V5 H (k : G)) ≤ Ri T L F.V1 :=
    (conjSub_mono c h98.Uγ_le_Vγ).trans hcR
  have hDU : ¬ F8.Uγ F.V5 H (k : G) ≤ F8.Dγ F.V5 F.V1 H (k : G) := by
    intro hle'
    have h1 : (F8.Dγ F.V5 F.V1 H (k : G)).relIndex (F8.Uγ F.V5 H (k : G)) = 1 :=
      Subgroup.relIndex_eq_one.2 hle'
    unfold mIdx at hpos
    rw [h1, padicValNat_one_right] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨b, hbU, hbD⟩ := IsConcreteLE.not_le_iff_exists.1 hDU
  have hbH : b ∈ H := h98.Uγ_le_H sk hbU
  have hbQ : b ∉ pCoreOf 2 H := fun hq => hbD (by
    rw [h98.Dγ_eq_inf_pCoreOf sk]
    exact ⟨hbU, hq⟩)
  have hR1H : Ri T L F.V1 ≤ H := (pCoreOf_le 2 _).trans h.L₁T_le_H
  have hrelR1 : (pCoreOf 2 H).relIndex (Ri T L F.V1) = 4 := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 H) (Ri T L F.V1)
    have h2 := card_star hR1H
    rw [hR1c, inf_comm] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  have hQc : conjSub c (pCoreOf 2 H) = pCoreOf 2 H :=
    conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hcH)
  have hmU : (F8.Dγ F.V5 F.V1 H (k : G)).relIndex (F8.Uγ F.V5 H (k : G)) ≤ 4 := by
    rw [h98.Dγ_eq_inf_pCoreOf sk, Subgroup.inf_relIndex_left, ← F9.relIndex_conjSub c, hQc,
      ← hrelR1]
    exact Subgroup.relIndex_le_of_le_right hcU (by rw [hrelR1]; norm_num)
  have hm : mIdx (F8.Uγ F.V5 H (k : G)) (F8.Dγ F.V5 F.V1 H (k : G)) ≤ 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian h98.isElemAbelian_Uγ)] at hmU
    by_contra hc
    have : 2 ^ 3 ≤ 2 ^ mIdx (F8.Uγ F.V5 H (k : G)) (F8.Dγ F.V5 F.V1 H (k : G)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hmH : (F8.DH F.V5 F.V1 H (k : G)).relIndex (conjClosure F.V5 H) ≤ 4 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian h98.F911_3)]
    calc 2 ^ mIdx (conjClosure F.V5 H) (F8.DH F.V5 F.V1 H (k : G)) ≤ 2 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) (hle.trans hm)
      _ = 4 := by norm_num
  set f := thetaH h ⟨b, hbH⟩ with hf
  have hup : Nat.card (cm f) ≤ 8 := by
    let π : ↥(conjClosure F.V5 H) →* ↥(UT F.V1 F.V5 H) :=
      ((secMk (N1 F.V1) F.V1).comp (Subgroup.inclusion hUN)).codRestrict (UT F.V1 F.V5 H)
        fun u => secMk_mem_secImg u.2
    have hπ : Function.Surjective π := by
      rintro ⟨w, hw⟩
      obtain ⟨⟨u, huN⟩, huU, rfl⟩ := mem_secImg.1 hw
      exact ⟨⟨u, huU⟩, rfl⟩
    set D := ((F8.DH F.V5 F.V1 H (k : G)).subgroupOf (conjClosure F.V5 H)).map π with hD
    have hDi : D.index ≤ 4 :=
      (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_map_dvd _ hπ)).trans hmH
    have hDm : D.map (cmHom f) ≤
        (tildeOf F.V1 (F8.A₁ F.V1 (k : G))).subgroupOf (UT F.V1 F.V5 H) := by
      rintro _ ⟨_, ⟨d, hdD, rfl⟩, rfl⟩
      have hdD' : (d : G) ∈ F8.DH F.V5 F.V1 H (k : G) := hdD
      obtain ⟨-, -, hdc⟩ := hdD'
      have hc : b * d * b⁻¹ * (d : G)⁻¹ ∈ F8.A₁ F.V1 (k : G) := by
        have := (F8.A₁ F.V1 (k : G)).inv_mem (hdc b hbU)
        rwa [show ((d : G) * b * (d : G)⁻¹ * b⁻¹)⁻¹ = b * d * b⁻¹ * (d : G)⁻¹ by group] at this
      exact thetaH_mul_inv_mem h hbH (hUN d.2) hc (π d) rfl
    have hcmA : Nat.card (D.map (cmHom f)) ≤ 2 :=
      (Subgroup.card_le_of_le hDm).trans ((card_tilde_le _ _ _).trans h98.card_A₁.le)
    have hcm_eq : cm f = (cmHom f).range := by
      rw [MonoidHom.range_eq_map]
      rfl
    rw [hcm_eq]
    calc Nat.card (cmHom f).range ≤ D.index * Nat.card (D.map (cmHom f)) := card_range_le _ D
      _ ≤ 4 * 2 := Nat.mul_le_mul hDi hcmA
      _ = 8 := by norm_num
  set c' : ↥H := ⟨c, hcH⟩
  have hb'R : c * b * c⁻¹ ∈ Ri T L F.V1 := hcU (mul_mem_conjSub hbU)
  have hb'H : c * b * c⁻¹ ∈ H := hR1H hb'R
  have hR1A := le_range_ιA5 e (N := S126.star H (Subgroup.normalizer (L : Set G) ⊓ H))
    (P := S126.star H (Ri T L F.V1)) (by rw [hR1]; exact pCoreOf_le 2 _)
    (by rw [hR1]; exact le_normalizer_pCoreOf 2 _) hR1c hR1sq (nine_dvd_card_star_MH e hidx)
  have hmem : (QuotientGroup.mk ⟨c * b * c⁻¹, hb'H⟩ : S126.HStar H) ∈
      S126.star H (Ri T L F.V1) := ⟨⟨c * b * c⁻¹, hb'H⟩, hb'R, rfl⟩
  obtain ⟨a, ha⟩ := hR1A hmem
  have hmk : (QuotientGroup.mk ⟨c * b * c⁻¹, hb'H⟩ : S126.HStar H) =
      QuotientGroup.mk c' * QuotientGroup.mk ⟨b, hbH⟩ * (QuotientGroup.mk c')⁻¹ := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, eq_comm, mkH_eq_one_iff] at ha
    apply hbQ
    have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H (H.inv_mem hcH)) _).1 ha
    rwa [show c⁻¹ * (c * b * c⁻¹) * c⁻¹⁻¹ = b by group] at this
  have hb2 : b ^ 2 = 1 := (h98.isElemAbelian_Uγ (g := k)).2 b hbU
  have ha2 : a ^ 2 = 1 := by
    apply ιA5_injective e
    rw [map_pow, ha, map_one, ← QuotientGroup.mk_pow]
    apply mkH_eq_one_iff.2
    rw [Subgroup.coe_pow]
    show (c * b * c⁻¹) ^ 2 ∈ pCoreOf 2 H
    rw [show (c * b * c⁻¹) ^ 2 = c * b ^ 2 * c⁻¹ by rw [pow_two, pow_two]; group, hb2, mul_one,
      mul_inv_cancel]
    exact Subgroup.one_mem _
  have h16 := sixteen_le_card_cm_of_a5 hW hx3 hxfix ht2 htx ρ hρ hρx hρt ha2 ha1
  have hρa : ρ a = psiH h (QuotientGroup.mk c') * f * (psiH h (QuotientGroup.mk c'))⁻¹ := by
    rw [hρdef, MonoidHom.comp_apply, ha, hmk, map_mul, map_mul, map_inv, psiH_mk h ⟨b, hbH⟩]
  rw [hρa, card_cm_conj] at h16
  omega

end F126

open F126 in
theorem final126_of (h30 : Lemma12_6_30) : Final126 := by
  intro G _ _ T L V _ F hH hZ H K hIs h3 _
  exact false_of_case3 F hH ((h30 G T L V F hH hZ).2 H K hIs).2.2.toHypF98 h3

end CFSG.Quasithin.H13
