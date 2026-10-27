module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310B
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem835
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem836
public import CFSG.Quasithin.Vol2.Ch3Sec3Cor332
public import CFSG.Quasithin.Vol2.Ch7Lem734Wr
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootQuotientClassesBasic
public import CFSG.Quasithin.Vol2.Ch3T326H2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative Matrix Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ch8310

omit [Finite G] in
theorem le_of_inf_le {A B Y M : Subgroup G} (hBN : B ≤ Subgroup.normalizer (A : Set G))
    (hBY : B ≤ Y) (hYAB : Y ≤ A ⊔ B) (hYA : Y ⊓ A ≤ M) (hBM : B ≤ M) : Y ≤ M := by
  intro y hy
  have hy' : y ∈ ((A ⊔ B : Subgroup G) : Set G) := hYAB hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hBN] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  have haY : a ∈ Y := by
    have e : a = a * b * b⁻¹ := by group
    rw [e]
    exact Y.mul_mem hy (Y.inv_mem (hBY hb))
  exact M.mul_mem (hYA ⟨haY, ha⟩) (hBM hb)

omit [Finite G] in
theorem convI_fix_iff {T I : Subgroup G} (hV : IsElemAbelian 2 (fsuV T I))
    (e : IntMod (fsuV T I) hV ≃* WMod) {z : G} (hz : z ∈ fsuV T I)
    (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) (t : Subgroup.normalizer (fsuV T I : Set G)) :
    congrHom e (convI hV t) (eW 0 0) = eW 0 0 ↔
      (t : G) ∈ Subgroup.centralizer ({z} : Set G) := by
  have hezs : e.symm (eW 0 0) = IntMod.mk hV ⟨z, hz⟩ := by
    rw [← hez, MulEquiv.symm_apply_apply]
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

theorem mem_map_autI_ch83X {T L I : Subgroup G} (hV : IsElemAbelian 2 (fsuV T I))
    (e : IntMod (fsuV T I) hV ≃* WMod) (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    {z : G} (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0)
    {c : MulAut WMod} (hc : c ∈ img) (hcE : c (eW 0 0) = eW 0 0) (hc3 : orderOf c = 3) :
    c ∈ (autI hV (ch83X T L z)).map (congrHom e) := by
  have hc' : c ∈ (autI hV (fsuL0 T L)).map (congrHom e) := by
    rw [he]
    exact hc
  obtain ⟨ψ, hψ, rfl⟩ := hc'
  obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hψ
  have hlz : (l : G) ∈ Subgroup.centralizer ({z} : Set G) := (convI_fix_iff hV e hz hez l).1 hcE
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

theorem nine_dvd_card_autI_ch83X {T L I : Subgroup G} (hV : IsElemAbelian 2 (fsuV T I))
    (e : IntMod (fsuV T I) hV ≃* WMod) (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    {z : G} (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) :
    9 ∣ Nat.card (autI hV (ch83X T L z)) := by
  set a := rho ((c3, 1) : ↥SL32 × ↥SL32) with hadef
  set b := rho ((1, c3) : ↥SL32 × ↥SL32) with hbdef
  have ha3 : orderOf a = 3 := by
    rw [hadef, orderOf_injective rho rho_injective]
    exact orderOf_c3_one
  have hb3 : orderOf b = 3 := by
    rw [hbdef, orderOf_injective rho rho_injective]
    exact orderOf_one_c3
  have ha : a ∈ (autI hV (ch83X T L z)).map (congrHom e) :=
    mem_map_autI_ch83X hV e he hz hez (rho_mem_img _) (rho_fix_E00 c3_mem_P1 P1.one_mem) ha3
  have hb : b ∈ (autI hV (ch83X T L z)).map (congrHom e) :=
    mem_map_autI_ch83X hV e he hz hez (rho_mem_img _) (rho_fix_E00 P1.one_mem c3_mem_P1) hb3
  have hab : Commute a b := by
    change a * b = b * a
    rw [hadef, hbdef, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simp) (by simp)
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hab.zpow_zpow i j).eq
  have hdisj : Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx.1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx.2
    have h1 : ((c3, 1) : ↥SL32 × ↥SL32) ^ i = ((1, c3) : ↥SL32 × ↥SL32) ^ j := by
      apply rho_injective
      rw [map_zpow, map_zpow]
      exact hi.trans hj.symm
    have h2 : ((c3, 1) : ↥SL32 × ↥SL32) ^ i = 1 := by
      have h3 := congrArg Prod.fst h1
      simp only [Prod.pow_fst, one_zpow] at h3
      exact Prod.ext (by simpa using h3) (by simp)
    rw [Subgroup.mem_bot, ← hi, hadef, ← map_zpow, h2, map_one]
  have h9 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 9 := by
    rw [SBc15.card_sup_eq_mul_of_commute hcomm hdisj, Nat.card_zpowers, Nat.card_zpowers, ha3, hb3]
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ (autI hV (ch83X T L z)).map (congrHom e) :=
    sup_le ((Subgroup.zpowers_le).mpr ha) ((Subgroup.zpowers_le).mpr hb)
  have h1 : 9 ∣ Nat.card ↥((autI hV (ch83X T L z)).map (congrHom e)) :=
    h9 ▸ Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥((autI hV (ch83X T L z)).map (congrHom e)) =
      Nat.card ↥(autI hV (ch83X T L z)) := card_map_congrHom e _
  rw [h2] at h1
  exact h1

theorem nine_dvd_card_ch83X {T L I : Subgroup G} (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (e : IntMod (fsuV T I) hV ≃* WMod) (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    {z : G} (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) :
    9 ∣ Nat.card (ch83X T L z) := by
  have hXN : ch83X T L z ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    ((twoResidual_le _).trans inf_le_left).trans (le_sup_left.trans hN)
  exact (nine_dvd_card_autI_ch83X hV e he hz hez).trans
    (Dvd.intro _ (card_autI_mul_card_inf hV hXN))

omit [Finite G] in
theorem fsuM_le_sup {T L I : Subgroup G} (hV : IsElemAbelian 2 (fsuV T I))
    (hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (e : IntMod (fsuV T I) hV ≃* WMod) (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    {z : G} (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) :
    fsuM T L ≤ fsuL0 T L ⊔ (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  intro m hm
  set mm : Subgroup.normalizer (fsuV T I : Set G) := ⟨m, hMV hm⟩ with hmm
  have hc : congrHom e (convI hV mm) ∈ norm :=
    congrHom_mem_norm e he (convI_mem_normalizer_autI hV (g := mm) hm)
  obtain ⟨g, hg⟩ := mem_norm_iff.mp hc
  have hrho : rho g ∈ (autI hV (fsuL0 T L)).map (congrHom e) := by
    rw [he]
    exact rho_mem_img g
  obtain ⟨ψ, hψ, hψe⟩ := hrho
  obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hψ
  have htau : tau (eW 0 0) = eW 0 0 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_tau]
    exact Matrix.transpose_single 0 0 (1 : ZMod 2)
  have hsame : congrHom e (convI hV mm) (eW 0 0) = congrHom e (convI hV l) (eW 0 0) := by
    rw [hψe]
    rcases hg with h | h
    · rw [h]
    · rw [h]
      change rho g (tau (eW 0 0)) = rho g (eW 0 0)
      rw [htau]
  have hezs : e.symm (eW 0 0) = IntMod.mk hV ⟨z, hz⟩ := by
    rw [← hez, MulEquiv.symm_apply_apply]
  have hval : ∀ t : Subgroup.normalizer (fsuV T I : Set G),
      (e.symm (congrHom e (convI hV t) (eW 0 0))).val = (t : G) * z * (t : G)⁻¹ := by
    intro t
    change (e.symm (e (convI hV t (e.symm (eW 0 0))))).val = _
    rw [MulEquiv.symm_apply_apply, hezs, convI_apply_val]
    rfl
  have hml : m * z * m⁻¹ = (l : G) * z * (l : G)⁻¹ := by
    have h1 := congrArg (fun w => (e.symm w).val) hsame
    rw [hval mm, hval l] at h1
    exact h1
  have hn : (l : G)⁻¹ * m ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.1 hk]
    have h1 : (l : G)⁻¹ * m * z * ((l : G)⁻¹ * m)⁻¹ = z := by
      calc (l : G)⁻¹ * m * z * ((l : G)⁻¹ * m)⁻¹ = (l : G)⁻¹ * (m * z * m⁻¹) * l := by group
        _ = (l : G)⁻¹ * ((l : G) * z * (l : G)⁻¹) * l := by rw [hml]
        _ = z := by group
    calc z * ((l : G)⁻¹ * m)
        = ((l : G)⁻¹ * m * z * ((l : G)⁻¹ * m)⁻¹) * ((l : G)⁻¹ * m) := by rw [h1]
      _ = (l : G)⁻¹ * m * z := by group
  have hnM : (l : G)⁻¹ * m ∈ fsuM T L :=
    (fsuM T L).mul_mem ((fsuM T L).inv_mem (Subgroup.le_normalizer hlL)) hm
  have e1 : m = (l : G) * ((l : G)⁻¹ * m) := by group
  rw [e1]
  exact Subgroup.mul_mem_sup hlL ⟨hnM, hn⟩

end Ch8310

theorem stmt8_3_10_of
    (h3228 : Stmt3_2_2_eight) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h332 : Stmt3_3_2MTwo) (h326 : Stmt3_2_6C)
    (h832 : Stmt8_3_2) (h835 : Stmt8_3_5) (h837 : Stmt8_3_7) (h839 : Stmt8_3_9)
    (hExcl : Claim8310Excl) (hGzC : Claim8310Gz) (hNC : Claim8310N) : Stmt8_3_10 := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := stmtFSUModule_of_eight h3228
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzsq : z ^ 2 = 1 := by
    rw [← hz2]
    exact pow_orderOf_eq_one z
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    ⟨hTK, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hzn : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    Ch8310.le_normalizer_of_comm fun a ha b hb => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hb' : Commute z b := Subgroup.mem_centralizer_iff.1 hb z rfl
      exact (hb'.zpow_left k).eq
  have hz2grp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hL0M : fsuL0 T L ≤ fsuM T L := Subgroup.le_normalizer
  have hXL0 : ch83X T L z ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hXM : ch83X T L z ≤ fsuM T L := hXL0.trans hL0M
  have hXKz : ch83X T L z ≤ ch83Kz T L z := le_conjClosure _ _
  have hKzGz : ch83Kz T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    conjClosure_le fun h hh x hx =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hGzKz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (ch83Kz T L z : Set G) := le_normalizer_conjClosure _ _
  have hTKzN : T ≤ Subgroup.normalizer (ch83Kz T L z : Set G) := hTz.trans hGzKz
  have hTX : T ≤ Subgroup.normalizer (ch83X T L z : Set G) := fun t ht => by
    have h1 : t ∈ Subgroup.normalizer
        ((fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) :=
      E1.mem_normalizer_inf (hTM ht) (Subgroup.le_normalizer (hTz ht))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    rw [ch83X, E1.map_twoResidual, h1]
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
    hyp.fsu.sylow hyp.fsu.maximal
  obtain ⟨M₁, M₂, hne12, hM₁, hM₂, hTM₁, hTM₂⟩ := h332 G T hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow L hyp.fsu.maximal hyp.fsu.quasisimple
  obtain ⟨H₁, hH₁⟩ : ∃ H : Subgroup G, IsHStar T (fsuM T L) H := by
    by_cases h : M₁ = fsuM T L
    · exact exists_isHStar_of hU.1.1 hM₂ hTM₂ fun h' => hne12 (h.trans h'.symm)
    · exact exists_isHStar_of hU.1.1 hM₁ hTM₁ h
  have hzΩ : z ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hzT, hzmem.2⟩, hzsq⟩
  have hzH₁ := ((center_facts_fsu hC58 h317 h37 h38 h39 h3228 hyp hH₁).1 hzΩ).2
  have hH₁Gz : H₁ ≤ Subgroup.centralizer ({z} : Set G) := fun h hh =>
    Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact (Subgroup.mem_centralizer_iff.1 hzH₁ h hh).symm
  obtain ⟨hGz, halt⟩ := h837 G T L I hyp h731 hc hrow z hz2 hzV
  have hKzM : ¬ ch83Kz T L z ≤ fsuM T L := fun h =>
    hH₁.2.1 (hH₁Gz.trans (hGz.le.trans (sup_le h inf_le_left)))
  have hInH : InH T (ch83Kz T L z ⊔ T) := by
    refine ⟨le_sup_right, fun h => hz1 ?_⟩
    have hzO : Subgroup.zpowers z ≤ pCoreOf 2 (ch83Kz T L z ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((Subgroup.zpowers_le).mpr ((le_sup_right : T ≤ ch83Kz T L z ⊔ T) hzT))
        ((sup_le hKzGz hTz).trans hzn) hz2grp
    rw [h] at hzO
    exact Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO)
  have hKzTM : ¬ ch83Kz T L z ⊔ T ≤ fsuM T L := fun h => hKzM (le_sup_left.trans h)
  obtain ⟨H₀, hH₀le, hH₀min⟩ := exists_minimal_le_of_wellFoundedLT
    (fun Y : Subgroup G => InH T Y ∧ ¬ Y ≤ fsuM T L) (ch83Kz T L z ⊔ T) ⟨hInH, hKzTM⟩
  have hH₀ : IsHStar T (fsuM T L) H₀ :=
    ⟨hH₀min.1.1, hH₀min.1.2, fun Y hY hYH hYM => le_antisymm hYH (hH₀min.2 ⟨hY, hYM⟩ hYH)⟩
  have hn1 : E1.nParam H₀ ≠ 1 := by
    rw [h839 G T L I hyp h731 hc hrow H₀ hH₀]
    norm_num
  have hex := fun h => hExcl G T L I hyp h731 hc hrow z hz2 hzV h H₀ hH₀ hH₀le
  obtain ⟨K, s, hsT, hsN, hKC, hKz, hK5⟩ : ∃ (K : Subgroup G) (s : G), s ∈ T ∧
      s ∉ Subgroup.normalizer (K : Set G) ∧
      quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)) ∧
      ch83Kz T L z = K ⊔ CFSG.conjugate K s ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 5 1 := by
    rcases halt with ⟨K, s, hsT, hsN, hKC, hKz, p, hp, hKp⟩ | h4 | h5 | hHe
    · by_cases hp5 : p = 5
      · subst hp5
        exact ⟨K, s, hsT, hsN, hKC, hKz, hKp⟩
      · exact absurd (hex (Or.inl ⟨K, s, hsT, hsN, hKC, hKz, p, hp, hp5, hKp⟩)) hn1
    · exact absurd (hex (Or.inr (Or.inl h4))) hn1
    · exact absurd (hex (Or.inr (Or.inr (Or.inl h5)))) hn1
    · exact absurd (hex (Or.inr (Or.inr (Or.inr hHe)))) hn1
  have h1a : ∃ (K : Subgroup G) (s : G), s ∈ T ∧ s ∉ Subgroup.normalizer (K : Set G) ∧
      quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)) ∧
      ch83Kz T L z = K ⊔ CFSG.conjugate K s ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨K, s, hsT, hsN, hKC, hKz, Ch8310.sl24_of_psl25 hK5⟩
  obtain ⟨e, he, hz, hez⟩ := exists_model_eW00 hyp hV hrow hz1 hzV
  have hA5 : Nonempty (OTwoQuot K ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e₅⟩ := Ch8310.a5_of_psl25 hK5
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (BlueprintB2.pCore_eq_open_pCore 2 ↥K).symm).trans
      e₅⟩
  have hB : ch83X T L z ⊔ (T ⊓ ch83Kz T L z) ≤ fsuM T L :=
    sup_le hXM (inf_le_left.trans hTM)
  obtain ⟨hdich, hXN, -⟩ := Ch8310.borel_setting (mem_cComp_iff.mpr hKC) (hTsyl _ hTz) hsT hsN hKz
    hGzKz hA5 hXKz (hTX hsT) (Ch8310.nine_dvd_card_ch83X hV hN e he hz hez)
    fun h => hKzM (h.trans hB)
  have hsKz : s ∈ Subgroup.normalizer (ch83Kz T L z : Set G) := hTKzN hsT
  have h1b : IsHStar T (fsuM T L) (ch83Kz T L z ⊔ T) := by
    refine ⟨hInH, hKzTM, fun Y hY hYH hYM => ?_⟩
    have hsY : s ∈ Subgroup.normalizer ((Y ⊓ ch83Kz T L z : Subgroup G) : Set G) :=
      E1.mem_normalizer_inf (Subgroup.le_normalizer (hY.1 hsT)) hsKz
    rcases hdich (Y ⊓ ch83Kz T L z) (inf_le_inf_right _ hY.1) inf_le_right hsY with h | h
    · exact le_antisymm hYH (sup_le (h.trans inf_le_left) hY.1)
    · exact absurd (Ch8310.le_of_inf_le hTKzN hY.1 hYH (h.trans hB) hTM) hYM
  have h1c : ch83X T L z ⊔ (T ⊓ ch83Kz T L z) = ch83Kz T L z ⊓ fsuM T L := by
    have hsKM : s ∈ Subgroup.normalizer ((ch83Kz T L z ⊓ fsuM T L : Subgroup G) : Set G) :=
      E1.mem_normalizer_inf hsKz (Subgroup.le_normalizer (hTM hsT))
    rcases hdich (ch83Kz T L z ⊓ fsuM T L) (le_inf inf_le_right (inf_le_left.trans hTM))
        inf_le_left hsKM with h | h
    · exact absurd (h.trans inf_le_right) hKzM
    · exact le_antisymm (le_inf (sup_le hXKz inf_le_right) hB) h
  have h2a : Subgroup.centralizer ({z} : Set G) = ch83Kz T L z ⊔ T :=
    hGzC G T L I hyp h731 hc hrow z hz2 hzV h1a h1b h1c
  have hVVM : fsuV T I = fsuVM T L I := by
    rcases stmt3_2_6Lt_of_C h326 G T L I hyp.fsu hrow.1 with ⟨-, -, h, -⟩ | h
    · exact h
    · exact absurd ⟨hrow.1, h⟩ hyp.notThree
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hVVM]
    exact le_normalizer_conjClosure _ _
  have hMz : fsuM T L ⊓ Subgroup.centralizer ({z} : Set G) ≤ fsuL0 T L ⊔ T := by
    refine Ch8310.le_of_inf_le hTKzN (le_inf hTM hTz) (inf_le_right.trans h2a.le) ?_ le_sup_right
    intro y hy
    have hy1 : y ∈ ch83Kz T L z ⊓ fsuM T L := ⟨hy.2, hy.1.1⟩
    rw [← h1c] at hy1
    exact sup_le (hXL0.trans le_sup_left) (inf_le_left.trans le_sup_right) hy1
  have h2b : fsuM T L = fsuL0 T L ⊔ T :=
    le_antisymm ((Ch8310.fsuM_le_sup hV hMV e he hz hez).trans (sup_le le_sup_left hMz))
      (sup_le hL0M hTM)
  have hTKzS : T ⊓ ch83Kz T L z ≤ ch83S T L z :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
      (sup_le hXN fun t ht => E1.mem_normalizer_inf (Subgroup.le_normalizer ht) (hTKzN ht))
      (hyp.fsu.sylow.1.to_le inf_le_left)
  have hST : ch83S T L z ≤ T := pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)
  have hSKz : ch83S T L z ≤ Subgroup.normalizer (ch83Kz T L z : Set G) := hST.trans hTKzN
  have h3 : IsSylowIn 2 (ch83S T L z) (ch83Kz T L z ⊔ ch83S T L z) := by
    refine ⟨le_sup_right, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, ?_⟩
    rw [sup_comm,
      CFSG.ShultStronglyClosedTI.LinearChain.RootQuotientClasses.relIndex_sup_eq_relIndex hSKz,
      ← Subgroup.inf_relIndex_right]
    have heq : ch83S T L z ⊓ ch83Kz T L z = T ⊓ ch83Kz T L z :=
      le_antisymm (inf_le_inf_right _ hST) (le_inf hTKzS inf_le_right)
    rw [heq]
    exact ((hTsyl _ hTz).inf_normal hKzGz
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKzGz).mpr hGzKz)).not_dvd_relIndex
  have hzS : z ∈ ch83S T L z := by
    have h1 : Subgroup.zpowers z ≤ ch83S T L z :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((Subgroup.zpowers_le).mpr ((le_sup_right : T ≤ ch83X T L z ⊔ T) hzT))
        ((sup_le hXGz hTz).trans hzn) hz2grp
    exact h1 (Subgroup.mem_zpowers z)
  have hle2 := hNC G T L I hyp h731 hc hrow z hz2 hzV h1a h1c
  have hne1 : E1.nParam (ch83Kz T L z ⊔ ch83S T L z) ≠ 1 := fun h =>
    hKzM (le_sup_left.trans (stmt8_3_6_of hmod h832 h835 G T L I hyp h731 hc hrow z hz2 hzV _ h3 h))
  have hne0 : ¬ E1.nParam (ch83Kz T L z ⊔ ch83S T L z) ≤ 0 := fun h => by
    have hodd := E1.odd_of_nParam_le_zero h
    have h2 : 2 ∣ Nat.card ↥(ch83Kz T L z ⊔ ch83S T L z) := by
      rw [← hz2]
      exact Subgroup.orderOf_dvd_natCard _ ((le_sup_right : ch83S T L z ≤ _) hzS)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have h4 : E1.nParam (ch83Kz T L z ⊔ ch83S T L z) = 2 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, E1.nParam (ch83Kz T L z ⊔ ch83S T L z) = k :=
      ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (by simp) hle2)).symm⟩
    rw [hk] at hle2 hne1 hne0 ⊢
    have hk2 : k ≤ 2 := by exact_mod_cast hle2
    interval_cases k
    · simp at hne0
    · simp at hne1
    · rfl
  exact ⟨h1a, h1b, h1c, h2a, h2b, h3, h4⟩

end CFSG.Quasithin.H13
