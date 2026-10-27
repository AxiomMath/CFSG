module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25Q

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative
open Matrix

namespace Lem25

@[expose] def M12t : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 0, 0; 0, 0, 1; 0, 1, 1]

@[expose] def m12t : GL (Fin 3) (ZMod 2) :=
  ⟨M12t, M12t ^ 2, by unfold M12t; decide +kernel, by unfold M12t; decide +kernel⟩

theorem coe_m12t : (m12t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = M12t := rfl

theorem m12t_cube : m12t ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_m12t, Units.val_one]
  unfold M12t
  decide +kernel

theorem m12t_ne_one : m12t ≠ 1 := fun h => by
  have := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1) h
  simp only [coe_m12t, Units.val_one] at this
  revert this
  unfold M12t
  decide

theorem M12t_mulVec_zero (x : Fin 3 → ZMod 2) : (M12t *ᵥ x) 0 = x 0 := by
  simp [M12t, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem M12t_single1 : M12t *ᵥ (Pi.single 1 1 : Fin 3 → ZMod 2) ≠ Pi.single 1 1 := by
  unfold M12t
  decide

theorem single1_zero : (Pi.single 1 1 : Fin 3 → ZMod 2) 0 = 0 := by decide

variable {G : Type} [Group G]

theorem exists_Y_three
    (h1222 : Stmt12_2_2) (h1220 : Stmt12_2_20) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn : n = 3) :
    ∃ y ∈ YY L U V, y ^ 3 = 1 ∧ y ≠ 1 ∧ ∃ a ∈ U ⊓ V, y * a * y⁻¹ ≠ a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨-, -, -, hVn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, ⟨hcommV, -⟩,
    -⟩ := hC
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, -, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have : IsMulCommutative ↥V := hcommV
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact Subtype.ext (hVe.2 v v.2)
  subst hn
  have hcard3 : Nat.card ↥V = 2 ^ (2 + 1) := hVn
  obtain ⟨e, he⟩ := exists_coords_index_two hV2' hcard3 (A := (U ⊓ V).subgroupOf V) hidx
  have he' : ∀ w : ↥V, (w : G) ∈ U ⊓ V ↔ Multiplicative.toAdd (e w) 0 = 0 := fun w => by
    rw [← he, Subgroup.mem_subgroupOf]
  have hodd : Odd (orderOf m12t) := by rw [orderOf_eq_three m12t_cube m12t_ne_one]; decide
  obtain ⟨x, hxo, hx⟩ := exists_odd_lift (actGL hLV e) (actGL_surjective hLV e htop) hodd
  have hxA : (x : G) ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    mem_normalizer_of_actGL hLV e 0 inf_le_right he' x fun y => by
      rw [hx, coe_m12t]; exact M12t_mulVec_zero y
  have hxY : (x : G) ∈ YY L U V := mem_oTwoUpper_of_odd ⟨x.2, hxA⟩ hxo
  have hx3 : (x : G) ^ 3 = 1 := by
    have h1 : actGL hLV e (x ^ 3) = 1 := by rw [map_pow, hx, m12t_cube]
    have h2 := (actGL_eq_one_iff hLV e (x ^ 3)).mp h1
    have h3 : ((x ^ 3 : ↥L) : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) := ⟨(x ^ 3).2, h2⟩
    obtain ⟨e3⟩ := Lem24.nonempty_coords (fun a ha b hb => congrArg Subtype.val
      (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hVe.2 hVn
    have h4 := Lem24.centralizer_le_pCoreOf hH hred (le_refl 3) e3 htop h3
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, h4⟩
    have hk' : ((x : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd3 : Odd (orderOf ((x : G) ^ 3)) :=
      Odd.of_dvd_nat hxo (orderOf_pow_dvd _)
    have hcop : Nat.Coprime (orderOf ((x : G) ^ 3)) (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd3)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk'))
  set a : ↥V := e.symm (Multiplicative.ofAdd (Pi.single 1 1)) with hadef
  have hea : Multiplicative.toAdd (e a) = Pi.single 1 1 := by
    rw [hadef, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have haA : (a : G) ∈ U ⊓ V := (he' a).mpr (by rw [hea]; exact single1_zero)
  have hmove : (x : G) * a * (x : G)⁻¹ ≠ a := by
    intro hfix
    have h1 := actGL_mulVec hLV e x a
    rw [hx, coe_m12t, hea] at h1
    have h2 : A4.actionOn V L hLV x a = a := Subtype.ext (by rw [A4.actionOn_apply_coe]; exact hfix)
    rw [h2, hea] at h1
    exact M12t_single1 h1
  refine ⟨x, hxY, hx3, fun h1 => hmove (by rw [h1]; group), a, haA, hmove⟩

theorem eq_inf_V_of_le_three [Finite G] {A B : Subgroup G} (hA : Nat.card A = 4) {y : G}
    (hy3 : y ^ 3 = 1) (hyA : y ∈ Subgroup.normalizer (A : Set G)) (hmove : ∃ a ∈ A, y * a * y⁻¹ ≠ a)
    (hBA : B ≤ A) (hB : B ≠ ⊥) (hyB : y ∈ Subgroup.normalizer (B : Set G)) : B = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCA : Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) = 1 := by
    have hmod := card_inf_centralizer_elem_modEq (S := A) hy3 hyA
    rw [hA] at hmod
    have hdvd : Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 4 :=
      hA ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) ≠ 4 := by
      intro h4
      have heq : A ⊓ Subgroup.centralizer ({y} : Set G) = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hA])
      obtain ⟨a, ha, hya⟩ := hmove
      rw [← heq] at ha
      apply hya
      rw [← Subgroup.mem_centralizer_singleton_iff.mp ha.2, mul_inv_cancel_right]
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases hc : Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) <;> simp_all
  have hCB : Nat.card ↥(B ⊓ Subgroup.centralizer ({y} : Set G)) = 1 := by
    have hle : Nat.card ↥(B ⊓ Subgroup.centralizer ({y} : Set G)) ≤ 1 :=
      hCA ▸ Subgroup.card_le_of_le (inf_le_inf_right _ hBA)
    have := Nat.card_pos (α := ↥(B ⊓ Subgroup.centralizer ({y} : Set G)))
    omega
  have hmod := card_inf_centralizer_elem_modEq (S := B) hy3 hyB
  rw [hCB] at hmod
  have hdvd : Nat.card B ∣ 4 := hA ▸ Subgroup.card_dvd_of_le hBA
  have hB1 : Nat.card B ≠ 1 := fun h1 => hB (Subgroup.eq_bot_of_card_eq B h1)
  have h4 : Nat.card B = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases hc : Nat.card B <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hBA (by rw [h4, hA])

theorem YY_le_NR
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) : YY L U V ≤ NR T U := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13⟩ := lem12225Star_of h331 h1222 h323 h1216
    h1220 G T L V H P U I h n p hH hNE hC
  exact le_sup_left.trans h13

theorem phi_surjective_three
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn : n = 3) {v₀ : G}
    (hD : PhiData (RR T U) V (U ⊓ V) v₀) : Function.Surjective hD.phi := by
  have hYN := YY_le_NR h331 h1222 h323 h1216 h1220 hH hNE hC
  have hYV : YY L U V ≤ Subgroup.normalizer (V : Set G) :=
    ((oTwoUpper_le _).trans inf_le_left).trans (le_normalizer_of_hyp1223 hH)
  obtain ⟨y, hyY, hy3, -, hmove⟩ := exists_Y_three h1222 h1220 hH hNE hC hn
  have hA : Nat.card ↥(U ⊓ V) = 4 := by rw [card_inf_V hC, hn]; norm_num
  set B : Subgroup G := hD.phi.range.map (U ⊓ V).subtype with hB
  have hBA : B ≤ U ⊓ V := Subgroup.map_subtype_le _
  have hBne : B ≠ ⊥ := by
    obtain ⟨u, huU, huV⟩ := exists_mem_U_not_mem_centralizer hH hC
    obtain ⟨hKR, -⟩ := CTL_facts h331 h1222 h323 h1216 h1220 hH hNE hC
    have huR : u ∈ RR T U := by
      obtain ⟨-, -, hc3, -⟩ := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h
        n p hH hNE hC
      show u ∈ T ⊓ Subgroup.centralizer (U : Set G)
      rw [hc3]
      exact Subgroup.mem_sup_left huU
    intro hbot
    have h1 : ((hD.phi ⟨u, huR⟩ : ↥(U ⊓ V)) : G) ∈ B := ⟨_, ⟨⟨u, huR⟩, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact huV ((hD.phi_eq_one_iff ⟨u, huR⟩).mp (Subtype.ext h1))
  have hyB : y ∈ Subgroup.normalizer (B : Set G) := by
    refine mem_normalizer_of_conj_mem fun b hb => ?_
    obtain ⟨_, ⟨r, rfl⟩, rfl⟩ := hb
    have hyr : y * (r : G) * y⁻¹ ∈ RR T U :=
      (Subgroup.mem_normalizer_iff.mp (hYN hyY) r).mp r.2
    refine ⟨_, ⟨⟨_, hyr⟩, rfl⟩, ?_⟩
    show ((hD.phi ⟨_, hyr⟩ : ↥(U ⊓ V)) : G) = y * ((hD.phi r : ↥(U ⊓ V)) : G) * y⁻¹
    rw [PhiData.phi_apply, PhiData.phi_apply]
    exact hD.comm_conj (hYN hyY) (hYV hyY) (YY_le_normalizer hyY) r.2
  have hBeq := eq_inf_V_of_le_three hA hy3 (YY_le_normalizer hyY) hmove hBA hBne hyB
  intro a
  have ha : (a : G) ∈ B := by rw [hBeq]; exact a.2
  obtain ⟨_, ⟨r, rfl⟩, hr⟩ := ha
  exact ⟨r, Subtype.ext hr⟩

theorem inf_centralizer_V_eq_three
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn : n = 3) {v₀ : G}
    (hD : PhiData (RR T U) V (U ⊓ V) v₀) :
    RR T U ⊓ Subgroup.centralizer (V : Set G) = (U ⊓ V) ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
      Nat.card (RR T U) = Nat.card ↥(RR T U ⊓ Subgroup.centralizer (V : Set G)) * 4 := by
  obtain ⟨hKR, hKV, hKA, hAK, hR⟩ := CTL_facts h331 h1222 h323 h1216 h1220 hH hNE hC
  have hA : Nat.card ↥(U ⊓ V) = 4 := by rw [card_inf_V hC, hn]; norm_num
  have hU : Nat.card U = 4 * 4 := by rw [card_U hC, hn]; norm_num
  have hsurj := phi_surjective_three h331 h1222 h323 h1216 h1220 hH hNE hC hn hD
  have hRc := card_eq_card_inf_mul (K := Subgroup.centralizer (V : Set G)) hD.phi
    hD.phi_eq_one_iff
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hA, inf_comm] at hRc
  refine ⟨?_, hRc⟩
  have hle : (U ⊓ V) ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ≤
      RR T U ⊓ Subgroup.centralizer (V : Set G) := by
    refine sup_le (le_inf (inf_V_le_RR hH hC) fun a ha => ?_) (le_inf hKR hKV)
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => hD.comm b hb a ha.2
  have hcard := card_sup_eq_mul hKA hAK
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, hA]
  have : Nat.card ↥(RR T U ⊓ Subgroup.centralizer (V : Set G)) * 4 =
      4 * Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) * 4 := by
    rw [← hRc, hR, hU]
    ring
  omega

theorem card_GL_three :
    Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Matrix.card_GL_field (𝔽 := ZMod 2) _).trans ?_
  rw [ZMod.card]
  simp [Fin.prod_univ_succ]

theorem card_T_le_three
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn : n = 3) : Nat.card T ≤ 2 ^ 7 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hc5, hc6, -, -, hc9, hc10, -⟩ := lem12225Star_of h331 h1222 h323 h1216
    h1220 G T L V H P U I h n p hH hNE hC
  have hVn : Nat.card V = 2 ^ 3 := by
    obtain ⟨-, -, -, hVn, -⟩ := hC
    rw [hVn, hn]
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨e3⟩ := Lem24.nonempty_coords hVab hVe.2 hVn
  have hTV := T_le_normalizer_V h1222 hH
  set α := A4.actionOn V T hTV with hα
  have hcard := card_eq_card_inf_mul (K := Subgroup.centralizer (V : Set G)) α
    (fun t => A4.actionOn_eq_one_iff hTV t)
  have hAut : Nat.card (MulAut ↥V) = 168 := by
    rw [Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e3).toEquiv, card_GL_three]
  have hrange : Nat.card α.range ≤ 8 := by
    have h2 : IsPGroup 2 α.range :=
      (hH.sylow.1 : IsPGroup 2 T).of_surjective α.rangeRestrict α.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have h3 : Nat.card α.range ∣ 168 := hAut ▸ Subgroup.card_subgroup_dvd_card α.range
    rw [hk] at h3 ⊢
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have h4 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h4.trans h3
      norm_num at this
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, -, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have hVL := V_le_L' hH
  have hO : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ (S : Subgroup G)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((LieType.BorelTits.pCoreOf_le 2 L).trans
      le_sup_left) (sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (hH.normalizes.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hKL : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    fun c hc => Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp hc.2 l hl.2)
  have hCV : Subgroup.centralizer (V : Set G) ⊓ (S : Subgroup G) ≤
      pCoreOf 2 (L ⊔ (S : Subgroup G)) := by
    rintro t ⟨htV, htS⟩
    have ht : t ∈ ((S : Subgroup G) ⊓ L) ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
      hc10 ▸ htS
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hKL ht
    have hcV : c ∈ Subgroup.centralizer (V : Set G) := Subgroup.centralizer_le hVL hc.2
    have hlV : l ∈ Subgroup.centralizer (V : Set G) := by
      have := Subgroup.mul_mem _ htV (Subgroup.inv_mem _ hcV)
      rwa [mul_inv_cancel_right] at this
    have hlO := Lem24.centralizer_le_pCoreOf hH hred (le_of_eq hn.symm) (hn ▸ e3) htop ⟨hl.2, hlV⟩
    refine Subgroup.mul_mem _ (hO hlO) ?_
    rw [hc5]
    exact Subgroup.mem_sup_right hc
  have hQ : Nat.card ↥(pCoreOf 2 (L ⊔ (S : Subgroup G))) ≤ 16 := by
    rw [hc5]
    have hKV : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
        Subgroup.centralizer (V : Set G) := inf_le_right.trans (Subgroup.centralizer_le hVL)
    have hVK : V ⊓ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxV, -, hxL⟩
      have : x ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hxV, hxL⟩
      rw [hc6] at this
      exact this
    rw [card_sup_eq_mul hKV hVK, hVn]
    have := hc9
    omega
  have hCTV := (Subgroup.card_le_of_le hCV).trans hQ
  rw [hcard]
  calc Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ (S : Subgroup G)) * Nat.card α.range ≤
      16 * 8 := Nat.mul_le_mul hCTV hrange
    _ = 2 ^ 7 := by norm_num

end Lem25

end CFSG.Quasithin.H13
