module

public import CFSG.Quasithin.Vol2.Ch8Sec3InputZ
public import CFSG.Quasithin.Vol2.Ch8Sec3Statements
public import CFSG.Quasithin.Background.HL3WrShat
public import CFSG.Quasithin.Background.E3Gen

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open

variable {G : Type*} [Group G] [Finite G] {V : Subgroup G}

theorem autI_mem_aSet_of_le (hV : IsElemAbelian 2 V) {g : G} {A X : Subgroup G}
    (hAg : A ≤ conjSubgroup V g) (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hAX : A ≤ X)
    {k : ℕ} (hk : 1 ≤ k) (hs : mQuot (conjSubgroup V g) A + k ≤ sParam hV)
    (hA : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    autI hV A ∈ aSet k (autI hV X) := by
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
  have hCA := e3_7 hV (le_inf hAg hAN) (by omega)
  refine ⟨autI_mono hV hAX, (autI_eq_bot_iff hV hAN).not.2 hA, isElemAbelian2_autI hV hAel hAN,
    ?_⟩
  intro B' hB' hm
  have hBA : preI hV A hAN B' ≤ A := preI_le hV
  have hpre : autI hV (preI hV A hAN B') = B' := autI_preI hV hB'
  have hm' : mQuot A (preI hV A hAN B') < k := by
    rw [← mQuot_autI_preI hV hAN hB']
    exact hm
  generalize preI hV A hAN B' = B at hBA hpre hm'
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hBA.trans hAN
  have hadd := mQuot_add (V := conjSubgroup V g) hBA hAg
  have hCB := e3_7 hV (le_inf (hBA.trans hAg) hBN) (by omega)
  ext v
  have e1 : v ∈ fixV B' ↔ v.val ∈ Subgroup.centralizer (B : Set G) := by
    rw [← hpre]
    exact mem_fixV_autI hV hBN v
  have e2 : v ∈ fixV (autI hV A) ↔ v.val ∈ Subgroup.centralizer (A : Set G) :=
    mem_fixV_autI hV hAN v
  rw [e1, e2]
  have hv : v.val ∈ V := v.val_mem
  constructor
  · intro hc
    have : v.val ∈ V ⊓ Subgroup.centralizer (B : Set G) := Subgroup.mem_inf.2 ⟨hv, hc⟩
    rw [hCB, ← hCA] at this
    exact (Subgroup.mem_inf.1 this).2
  · intro hc
    have : v.val ∈ V ⊓ Subgroup.centralizer (A : Set G) := Subgroup.mem_inf.2 ⟨hv, hc⟩
    rw [hCA, ← hCB] at this
    exact (Subgroup.mem_inf.1 this).2

end E3

namespace H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem convI_mem_normalizer_autI {V : Subgroup G} (hV : IsElemAbelian 2 V) {H : Subgroup G}
    {g : Subgroup.normalizer (V : Set G)} (hg : (g : G) ∈ Subgroup.normalizer (H : Set G)) :
    convI hV g ∈ Subgroup.normalizer (autI hV H : Set (MulAut (IntMod V hV))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    obtain ⟨h, hh, rfl⟩ := (mem_autI hV).1 hψ
    refine (mem_autI hV).2 ⟨g * h * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg h).mp hh, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · intro hψ
    obtain ⟨h, hh, hgh⟩ := (mem_autI hV).1 hψ
    refine (mem_autI hV).2 ⟨g⁻¹ * h * g, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) h).mp hh
      simpa using this
    · rw [map_mul, map_mul, map_inv, hgh]
      group

theorem eq_one_or_eq_eW00_of_mem_fixV {X : WMod} (hX : X ∈ fixV l3wrSylU) :
    X = 1 ∨ X = eW 0 0 := by
  have hfix : ∀ g : ↥SL32 × ↥SL32, g ∈ U3.prod U3 →
      mat g.1 * Multiplicative.toAdd X * (mat g.2)ᵀ = Multiplicative.toAdd X := fun g hg => by
    rw [← toAdd_rho]
    exact congrArg Multiplicative.toAdd (hX _ ⟨g, hg, rfl⟩)
  have h1 := hfix (tr 0 1 (by decide), 1) ⟨l3wr_tr01_mem_U3, U3.one_mem⟩
  have h2 := hfix (tr 0 2 (by decide), 1) ⟨l3wr_tr02_mem_U3, U3.one_mem⟩
  have h3 := hfix (1, tr 0 1 (by decide)) ⟨U3.one_mem, l3wr_tr01_mem_U3⟩
  have h4 := hfix (1, tr 0 2 (by decide)) ⟨U3.one_mem, l3wr_tr02_mem_U3⟩
  simp only [mat_tr, mat_one, Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul] at h1 h2 h3 h4
  have hY := eq_smul_E00 h1 h2 h3 h4
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd X 0 0) with hc | hc
  · left
    apply Multiplicative.toAdd.injective
    rw [hY, hc, Matrix.single_zero]
    rfl
  · right
    apply Multiplicative.toAdd.injective
    rw [hY, hc]
    rfl

omit [Finite G] in
theorem mem_of_two_pow_mem {M : Type*} [Group M] {H : Subgroup M} {x : M} (h3 : orderOf x = 3)
    {k : ℕ} (hk : x ^ 2 ^ k ∈ H) : x ∈ H := by
  have hr : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    have h : ¬ 3 ∣ 2 ^ k := fun h => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      (by norm_num)
    omega
  rw [← pow_mod_orderOf, h3] at hk
  rcases hr with h | h
  · rwa [h, pow_one] at hk
  · rw [h] at hk
    have hx : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul, ← pow_mod_orderOf, h3]
      norm_num
    rw [hx]
    exact H.pow_mem hk 2

theorem exists_conj_l3wrSylU_le {S : Subgroup (MulAut WMod)} (hSle : S ≤ img)
    (hScard : Nat.card ↥S = 2 ^ 6) : ∃ g ∈ img, B3.cj g l3wrSylU ≤ S := by
  have hidx : ¬ 2 ∣ (S.subgroupOf img).index := by
    have h1 := (S.subgroupOf img).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv, hScard, card_img] at h1
    have h2 : (S.subgroupOf img).index = 441 := by omega
    rw [h2]
    decide
  exact B3.exists_conj_le_sylow_sub hSle (IsPGroup.of_card hScard) hidx l3wrSylU_le_img
    (IsPGroup.of_card card_l3wrSylU)

theorem exists_inv_apply_eq_eW00 {S : Subgroup (MulAut WMod)} (hSle : S ≤ img)
    (hScard : Nat.card ↥S = 2 ^ 6) {w : WMod} (hw : ∀ y ∈ S, y w = w) (hw1 : w ≠ 1) :
    ∃ g ∈ img, g⁻¹ w = eW 0 0 := by
  obtain ⟨g, hg, hgS⟩ := exists_conj_l3wrSylU_le hSle hScard
  have hfix : g⁻¹ w ∈ fixV l3wrSylU := by
    rintro (x : MulAut WMod) hx
    have hx' : x ∈ l3wrSylU := hx
    have h1 := hw (g * x * g⁻¹) (hgS (B3.mem_cj.2 (by simpa [mul_assoc] using hx')))
    have h2 : g (x (g⁻¹ w)) = w := h1
    calc x (g⁻¹ w) = g⁻¹ (g (x (g⁻¹ w))) := (MulAut.inv_apply_self _ _ _).symm
      _ = g⁻¹ w := by rw [h2]
  rcases eq_one_or_eq_eW00_of_mem_fixV hfix with h | h
  · exfalso
    apply hw1
    have := congrArg g h
    rwa [MulAut.apply_inv_self, map_one] at this
  · exact ⟨g, hg, h⟩

theorem congrHom_trans_apply {W : Type*} [CommGroup W] (e : W ≃* WMod) (g : MulAut WMod)
    (x : MulAut W) : (congrHom (e.trans g) x : MulAut WMod) = MulAut.conj g (congrHom e x) :=
  MulEquiv.ext fun _ => rfl

theorem map_congrHom_trans_eq_img {W : Type*} [CommGroup W] (e : W ≃* WMod)
    {A : Subgroup (MulAut W)} (hA : A.map (congrHom e) = img) {g : MulAut WMod} (hg : g ∈ img) :
    (A.map (congrHom (e.trans g)) : Subgroup (MulAut WMod)) = img := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (congrHom e x : MulAut WMod) ∈ img := by
      rw [← hA]
      exact ⟨x, hx, rfl⟩
    have h := img.mul_mem (img.mul_mem hg hx') (img.inv_mem hg)
    have heq := (congrHom_trans_apply e g x).trans (MulAut.conj_apply g (congrHom e x))
    exact (congrArg (fun t : MulAut WMod => t ∈ img) heq).mpr h
  · intro y hy
    have hy' : g⁻¹ * y * g ∈ A.map (congrHom e) := by
      rw [hA]
      exact img.mul_mem (img.mul_mem (img.inv_mem hg) hy) hg
    obtain ⟨x, hx, hxe⟩ := hy'
    refine ⟨x, hx, ?_⟩
    have h1 : MulAut.conj g (g⁻¹ * y * g) = y := by
      rw [MulAut.conj_apply]
      group
    show (congrHom (e.trans g) x : MulAut WMod) = y
    rw [congrHom_trans_apply, hxe]
    exact h1

theorem congrHom_mem_norm {W : Type*} [CommGroup W] (e : W ≃* WMod) {A : Subgroup (MulAut W)}
    (hA : A.map (congrHom e) = img) {x : MulAut W}
    (hx : x ∈ Subgroup.normalizer (A : Set (MulAut W))) : (congrHom e x : MulAut WMod) ∈ norm := by
  have hmem : (congrHom e x : MulAut WMod) ∈
      (Subgroup.normalizer (A : Set (MulAut W))).map (congrHom e) := ⟨x, hx, rfl⟩
  have h := Subgroup.le_normalizer_map (congrHom e : MulAut W →* MulAut WMod) hmem
  rw [hA] at h
  exact h

theorem exists_model_eW00 {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (hV : IsElemAbelian 2 (fsuV T I)) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) {z : G} (hz1 : z ≠ 1)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) :
    ∃ e : IntMod (fsuV T I) hV ≃* WMod, (autI hV (fsuL0 T L)).map (congrHom e) = img ∧
      ∃ hz : z ∈ fsuV T I, e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := hyp.fsu
  have hL : (tensorPairModel SL32 SL32).RealizesMod (V := IntMod (fsuV T I) hV)
      (autI hV (fsuL0 T L)) := hrow.2
  obtain ⟨e, he⟩ := exists_model hL
  have hT := isSylowIn_top_of_fsu hfsu
  have hTL₀ : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) := le_normalizer_conjClosure L T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  have hB : Nat.card ↥(autI hV (fsuL0 T L)) = 2 ^ 6 * 441 := by
    have h1 := card_map_congrHom e (autI hV (fsuL0 T L))
    rw [he] at h1
    exact h1.symm.trans card_img
  have hfac : (2 ^ 6 * 441 : ℕ).factorization 2 = 6 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hS : Nat.card ↥(autI hV (T ⊓ fsuL0 T L)) = 2 ^ 6 := by
    have h : Nat.card ↥(autI hV (T ⊓ fsuL0 T L)) =
        2 ^ (Nat.card ↥(autI hV (fsuL0 T L))).factorization 2 :=
      card_autOn_inf_of_sylow hT hTL₀ hTV
    rw [h, hB, hfac]
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hz : z ∈ fsuV T I := hzmem.1
  have hzfix : ∀ y ∈ (autI hV (T ⊓ fsuL0 T L)).map (congrHom e),
      y (e (IntMod.mk hV ⟨z, hz⟩)) = e (IntMod.mk hV ⟨z, hz⟩) := by
    rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨t, htT, rfl⟩ := (mem_autI hV).1 hψ
    change e (convI hV t (e.symm (e (IntMod.mk hV ⟨z, hz⟩)))) = e (IntMod.mk hV ⟨z, hz⟩)
    rw [MulEquiv.symm_apply_apply]
    congr 1
    apply IntMod.val_injective
    rw [convI_apply_val]
    change (t : G) * z * (t : G)⁻¹ = z
    rw [Subgroup.mem_centralizer_iff.mp hzmem.2 t htT.1, mul_inv_cancel_right]
  have hne : e (IntMod.mk hV ⟨z, hz⟩) ≠ 1 := by
    intro h
    rw [← map_one e] at h
    exact hz1 (congrArg IntMod.val (e.injective h))
  obtain ⟨g, hg, hgz⟩ := exists_inv_apply_eq_eW00
    (S := (autI hV (T ⊓ fsuL0 T L)).map (congrHom e))
    (he ▸ Subgroup.map_mono (autI_mono hV inf_le_right)) ((card_map_congrHom e _).trans hS)
    hzfix hne
  exact ⟨e.trans g⁻¹, map_congrHom_trans_eq_img e he (img.inv_mem hg), hz, hgz⟩

theorem map_autI_ch83S_le_Shat {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G}
    (hzT : z ∈ Subgroup.centralizer (T : Set G))
    (e : IntMod (fsuV T I) hV ≃* WMod) (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) :
    (autI hV (ch83S T L z)).map (congrHom e) ≤ Shat := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    ⟨hTK, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hST : ch83S T L z ≤ T := pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)
  have hSN : ch83S T L z ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    hST.trans (le_sup_right.trans hN)
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzT t ht).symm
  have hezs : e.symm (eW 0 0) = IntMod.mk hV ⟨z, hz⟩ := by
    rw [← hez, MulEquiv.symm_apply_apply]
  have hfixz : ∀ t : Subgroup.normalizer (fsuV T I : Set G),
      (congrHom e (convI hV t) (eW 0 0) = eW 0 0 ↔
        (t : G) ∈ Subgroup.centralizer ({z} : Set G)) := by
    intro t
    have key : congrHom e (convI hV t) (eW 0 0) = eW 0 0 ↔ (t : G) * z * (t : G)⁻¹ = z := by
      change e (convI hV t (e.symm (eW 0 0))) = eW 0 0 ↔ _
      rw [hezs, ← hez, e.injective.eq_iff]
      constructor
      · intro h
        have h3 := congrArg IntMod.val h
        rw [convI_apply_val] at h3
        exact h3
      · intro h
        apply IntMod.val_injective
        rw [convI_apply_val]
        exact h
    rw [key, Subgroup.mem_centralizer_iff]
    constructor
    · intro h k hk
      rw [Set.mem_singleton_iff.1 hk]
      calc z * (t : G) = ((t : G) * z * (t : G)⁻¹) * t := by rw [h]
        _ = t * z := by group
    · intro h
      rw [← h z rfl, mul_inv_cancel_right]
  have hlift : ∀ c : MulAut WMod, c ∈ img → c (eW 0 0) = eW 0 0 → orderOf c = 3 →
      c ∈ (autI hV (ch83X T L z)).map (congrHom e) := by
    intro c hc hcE hc3
    have hc' : c ∈ (autI hV (fsuL0 T L)).map (congrHom e) := by
      rw [he]
      exact hc
    obtain ⟨ψ, hψ, rfl⟩ := hc'
    obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hψ
    have hlz : (l : G) ∈ Subgroup.centralizer ({z} : Set G) := (hfixz l).1 hcE
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient
      (fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G)) (l : G) ⟨hlL, hlz⟩
    have hpow : congrHom e (convI hV l) ^ 2 ^ k ∈
        (autI hV (ch83X T L z)).map (congrHom e) := by
      have hk' : ((l ^ 2 ^ k : Subgroup.normalizer (fsuV T I : Set G)) : G) ∈ ch83X T L z := by
        rw [Subgroup.coe_pow]
        exact hk
      refine ⟨convI hV (l ^ 2 ^ k), (mem_autI hV).2 ⟨l ^ 2 ^ k, hk', rfl⟩, ?_⟩
      rw [map_pow, map_pow]
    have hc3' : orderOf (congrHom e (convI hV l)) = 3 := hc3
    exact mem_of_two_pow_mem hc3' hpow
  have hconj : ∀ c ∈ (autI hV (ch83X T L z)).map (congrHom e),
      ∀ p ∈ (autI hV (ch83S T L z)).map (congrHom e),
        c * p * c⁻¹ ∈ (autI hV (ch83S T L z)).map (congrHom e) := by
    rintro _ ⟨ψ, hψ, rfl⟩ _ ⟨φ, hφ, rfl⟩
    obtain ⟨x, hxX, rfl⟩ := (mem_autI hV).1 hψ
    obtain ⟨s, hsS, rfl⟩ := (mem_autI hV).1 hφ
    have hxS : (x : G) ∈ Subgroup.normalizer (ch83S T L z : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (ch83X T L z ⊔ T)
        ((le_sup_left : ch83X T L z ≤ ch83X T L z ⊔ T) hxX)
    refine ⟨convI hV (x * s * x⁻¹), (mem_autI hV).2 ⟨x * s * x⁻¹, ?_, rfl⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hxS s).mp hsS
    · rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  refine le_Shat_of_normalized ?_ ?_ ?_
    (fun p hp => hconj _ (hlift _ (rho_mem_img _) (rho_fix_E00 c3_mem_P1 P1.one_mem)
      (by rw [orderOf_injective rho rho_injective]; exact orderOf_c3_one)) p hp)
    (fun p hp => hconj _ (hlift _ (rho_mem_img _) (rho_fix_E00 P1.one_mem c3_mem_P1)
      (by rw [orderOf_injective rho rho_injective]; exact orderOf_one_c3)) p hp)
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨s, hsS, rfl⟩ := (mem_autI hV).1 hψ
    have hsL : (s : G) ∈ Subgroup.normalizer (fsuL0 T L : Set G) :=
      le_normalizer_conjClosure L T (hST hsS)
    exact congrHom_mem_norm e he (convI_mem_normalizer_autI hV hsL)
  · exact (isPGroup_autI hV hSN (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).map _
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨s, hsS, rfl⟩ := (mem_autI hV).1 hψ
    exact (hfixz s).2 (hTz (hST hsS))

theorem stmt8_3_5_of (hmod : StmtFSUModule) (huniq : Input7_0_2_unique) (hQ : Input8_3_Q)
    (h832 : Stmt8_3_2) : Stmt8_3_5 := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hs := h832 G T L I hyp h731 hc hrow hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    ⟨hTK, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hST : ch83S T L z ≤ T := pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)
  have hXL : ch83X T L z ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have hQS : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ ch83S T L z := by
    rw [hQ G T L I hyp]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)).trans le_sup_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (sup_le_sup_right hXL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hQ2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    hyp.fsu.sylow.1.to_le inf_le_left
  have : IsMulCommutative ↥(fsuV T I) := hV.1
  have hVQ : fsuV T I ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    le_inf (fsuV_le_T hyp.fsu hV hN)
      (fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw => setLike_mul_comm hw hv)
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨e, he, hz, hez⟩ := exists_model_eW00 hyp hV hrow hz1 hzV
  have hzT : z ∈ Subgroup.centralizer (T : Set G) := by
    have : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
      rw [hzV]
      exact Subgroup.mem_zpowers z
    exact this.2
  have hSh := map_autI_ch83S_le_Shat hyp hV hN hzT e he hz hez
  have hW : ∀ i ≤ 1, wClos (fsuV T I) i (ch83S T L z) ≤
      T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    intro i hi
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAS, g, hAg, hAm⟩ := hA
    refine le_inf (hAS.trans hST) ?_
    by_contra hAC
    have hmem := autI_mem_aSet_of_le hV hAg ((hAS.trans hST).trans (le_sup_right.trans hN)) hAS
      (k := 2) (by norm_num) (by rw [hs, hAm]; omega) hAC
    have h1 := (map_mem_aSet_iff e).2 hmem
    have h2 : (autI hV A).map (congrHom e) ∈ E3.aSet 2 Shat := ⟨h1.1.trans hSh, h1.2⟩
    rw [aSet_two_Shat_eq_empty] at h2
    exact h2
  have hrk : 3 ≤ rk ↥(fsuV T I) := by
    have := sParam_le_rk hV
    rw [hs] at this
    exact this
  have hVS : fsuV T I ≤ ch83S T L z := hVQ.trans hQS
  have hS2 : IsSylowIn 2 (ch83S T L z) (ch83S T L z) :=
    ⟨le_rfl, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, by
      rw [Subgroup.relIndex_self]
      exact fun h => absurd (Nat.dvd_one.1 h) (by norm_num)⟩
  exact ⟨(e3_16_one hS2 hQS hQ2 (hW 0 (by norm_num)) (wClos_ne_bot hV hVS (by omega))
      (huniq G T L I hyp)).2,
    e3_16_three hS2 hQS hQ2 (hW 1 le_rfl) (wClos_ne_bot hV hVS (by omega)) (huniq G T L I hyp)⟩

end H13

end CFSG.Quasithin
