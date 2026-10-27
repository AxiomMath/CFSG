module

public import CFSG.OddTranspositions.PartThree.Nine.SixGH

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm
  cosetNormalizerPerm_apply cosetNormalizerPerm_ker_eq_entire_centralizer)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace NineSixSetting

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem card_range (h : NineSixSetting hC T S U) :
    Nat.card (cosetNormalizerPerm ((S : Set G) ∩ D)).range = 168 := by
  have hneg : (-1 : ZMod 7) ≠ 1 := by decide
  obtain ⟨e⟩ := h.psl27
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpsl := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := ZMod 7)
  rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hneg,
    Nat.card_zmod] at hpsl
  rw [Nat.card_congr e.toEquiv]
  omega

theorem isSimpleGroup_range (h : NineSixSetting hC T S U) :
    IsSimpleGroup (cosetNormalizerPerm ((S : Set G) ∩ D)).range := by
  obtain ⟨e⟩ := h.psl27
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : IsSimpleGroup PSL(2, ZMod 7) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  have : Nontrivial (cosetNormalizerPerm ((S : Set G) ∩ D)).range := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom (MulEquiv.surjective _)

theorem card_sylow_map (h : NineSixSetting hC T S U) :
    Nat.card ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) = 16 := by
  obtain ⟨eH⟩ := h.psl28
  have h1 := card_sylow_map_le_of_psl2 h.three h.five h.delta (n := 3) (by norm_num) eH
  have h2 := two_mul_card_le_card_sylow_map h.three h.delta
  rw [h.card] at h2
  omega

theorem mem_or_mul_mem (h : NineSixSetting hC T S U) {t : G}
    (ht : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    t ∈ U ∨ hC.d * t ∈ U := by
  obtain ⟨eH⟩ := h.psl28
  exact h.delta.mem_or_mul_mem_of_psl2 h.three h.five (n := 3) (by norm_num) eH
    (by rw [h.card]; norm_num) t ht

theorem sylow_map_mul_self (h : NineSixSetting hC T S U) {t : G}
    (ht : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    t * t = 1 := by
  have hU := h.delta
  have := hU.isElementaryAbelian
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hdU : ∀ v ∈ U, hC.d * v = v * hC.d := fun v hv =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC
        (Subgroup.map_subtype_le _ (hU.le_pResidualOf hv)))).symm
  have hsq : ∀ v ∈ U, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian v hv
  rcases h.mem_or_mul_mem ht with htU | htU
  · exact hsq t htU
  · have ht' : t = hC.d * (hC.d * t) := by rw [← mul_assoc, hu2, one_mul]
    rw [ht']
    calc hC.d * (hC.d * t) * (hC.d * (hC.d * t)) =
        hC.d * ((hC.d * t) * hC.d) * (hC.d * t) := by group
      _ = hC.d * (hC.d * (hC.d * t)) * (hC.d * t) := by rw [← hdU _ htU]
      _ = hC.d * hC.d * ((hC.d * t) * (hC.d * t)) := by group
      _ = 1 := by rw [hu2, hsq _ htU, one_mul]

theorem sylow_map_commute (h : NineSixSetting hC T S U) {s t : G}
    (hs : s ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (ht : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    Commute s t := by
  have hU := h.delta
  have := hU.isElementaryAbelian
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hdU : ∀ v ∈ U, Commute hC.d v := fun v hv =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC
        (Subgroup.map_subtype_le _ (hU.le_pResidualOf hv)))).symm
  have hUc : ∀ v ∈ U, ∀ w ∈ U, Commute v w := fun v hv w hw =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hcen : ∀ x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      Commute x hC.d ∧ ∀ v ∈ U, Commute x v := by
    intro x hx
    rcases h.mem_or_mul_mem hx with hxU | hxU
    · exact ⟨(hdU x hxU).symm, fun v hv => hUc x hxU v hv⟩
    · have hx' : x = hC.d * (hC.d * x) := by rw [← mul_assoc, hu2, one_mul]
      rw [hx']
      exact ⟨(Commute.refl hC.d).mul_left (hdU _ hxU).symm,
        fun v hv => (hdU v hv).mul_left (hUc _ hxU v hv)⟩
  rcases h.mem_or_mul_mem hs with hsU | hsU
  · exact ((hcen t ht).2 s hsU).symm
  · have hs' : s = hC.d * (hC.d * s) := by rw [← mul_assoc, hu2, one_mul]
    rw [hs']
    exact (hcen t ht).1.symm.mul_left ((hcen t ht).2 _ hsU).symm

theorem le_commutator (h : NineSixSetting hC T S U) : U ≤ commutator G :=
  fun _ hz => mem_commutator_of_mem_omega h.delta hz

theorem mem_inter_iff_commute (h : NineSixSetting hC T S U) {w : G} (hw : w ∈ U) (hw1 : w ≠ 1)
    (x : G) : x ∈ (S : Set G) ∩ D ↔ x ∈ D ∧ Commute x w := by
  rw [h.delta.sylow_inter]
  exact h.delta.mem_delta_iff_commute h.hyp h.three h.five hw hw1 x

theorem card_sylow (h : NineSixSetting hC T S U) : Nat.card (S : Subgroup G) = 128 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eH⟩ := h.psl28
  have hT16 := h.card_sylow_map
  have hSN := h.four.2.1
  have hN : Nat.card (Subgroup.normalizer ((S : Set G) ∩ D)) = 2 ^ 7 * 21 := by
    have hker := Subgroup.card_ker_mul_card_range (cosetNormalizerPerm ((S : Set G) ∩ D))
    rw [cosetNormalizerPerm_ker_eq_entire_centralizer, h.five.1] at hker
    have hle : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
        Subgroup.normalizer ((S : Set G) ∩ D) := h.le.trans hSN
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hT16] at hker
    have hneg : (-1 : ZMod 7) ≠ 1 := by decide
    obtain ⟨e⟩ := h.psl27
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hpsl := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := ZMod 7)
    rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hneg,
      Nat.card_zmod] at hpsl
    rw [Nat.card_congr e.toEquiv] at hker
    omega
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have h1 : 2 ^ 7 ∣ Nat.card (S : Subgroup G) :=
    S.pow_dvd_card_of_pow_dvd_card
      ((hN ▸ Dvd.intro 21 rfl).trans (Subgroup.card_subgroup_dvd_card _))
  have h2 : 2 ^ k ∣ 2 ^ 7 * 21 := hk ▸ hN ▸ Subgroup.card_dvd_of_le hSN
  have h3 : 2 ^ k ∣ 2 ^ 7 :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left k (by norm_num)) h2)
  rw [hk] at h1 ⊢
  have h4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have h5 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3
  have : k = 7 := by omega
  rw [this]
  norm_num

theorem sylow_map_eq_sup (h : NineSixSetting hC T S U) :
    (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d ⊔ U := by
  obtain ⟨eH⟩ := h.psl28
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hor := h.delta.mem_or_mul_mem_of_psl2 h.three h.five (n := 3) (by norm_num) eH
    (by rw [h.card]; norm_num)
  refine le_antisymm (fun t ht => ?_)
    (sup_le (Subgroup.zpowers_le.mpr (d_mem_sylow_map hC h.three T)) h.delta.le_sylow_map)
  rcases hor t ht with htU | htU
  · exact Subgroup.mem_sup_right htU
  · have ht' : t = hC.d * (hC.d * t) := by rw [← mul_assoc, hu2, one_mul]
    rw [ht']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right htU)

theorem centralizer_eq_sylow_map (h : NineSixSetting hC T S U) :
    Subgroup.centralizer (U : Set G) =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  classical
  have hU := h.delta
  have := hU.isElementaryAbelian
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hUc : ∀ v ∈ U, ∀ w ∈ U, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hdU : ∀ v ∈ U, hC.d * v = v * hC.d := fun v hv =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC
        (Subgroup.map_subtype_le _ (hU.le_pResidualOf hv)))).symm
  have hTab : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      Subgroup.centralizer (U : Set G) := by
    rw [h.sylow_map_eq_sup]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hdU v hv).symm
    · intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hUc v hv w hw
  refine le_antisymm (fun x hx => ?_) hTab
  set Δ := (S : Set G) ∩ D with hΔ
  obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hCN : ∀ y ∈ Subgroup.centralizer (U : Set G), y ∈ Subgroup.normalizer Δ := by
    intro y hy
    have hys : y ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hy s hs).symm
    rw [hΔ, hU.sylow_inter]
    exact hU.centralizer_le_normalizer_delta h.hyp h.three h.five hs hs1' hys
  have hNU : ∀ n ∈ Subgroup.normalizer Δ, n ∈ Subgroup.normalizer (U : Set G) := by
    intro n hn
    rw [hΔ, hU.sylow_inter] at hn
    exact (hU.affine h.three).1 hn
  set M := (Subgroup.centralizer (U : Set G)).subgroupOf (Subgroup.normalizer Δ) with hM
  have hMn : M.Normal := by
    constructor
    intro m hm n
    rw [hM, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hm ⊢
    intro v hv
    have hnv : (n : G)⁻¹ * v * (n : G) ∈ U := by
      have h1 := (Subgroup.inv_mem _ (hNU n n.2) v).mp hv
      simpa using h1
    have h2 := hm _ hnv
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc v * ((n : G) * m * (n : G)⁻¹) = n * ((n : G)⁻¹ * v * n * m) * (n : G)⁻¹ := by group
      _ = n * (m * ((n : G)⁻¹ * v * n)) * (n : G)⁻¹ := by rw [h2]
      _ = (n : G) * m * (n : G)⁻¹ * v := by group
  have hact : ∀ m ∈ Subgroup.centralizer (U : Set G), ∀ (hm : m ∈ Subgroup.normalizer Δ),
      ∃ c ∈ U, ∀ δ ∈ Δ, m * δ * m⁻¹ = c * δ := by
    intro m hm hmN
    have huΔ : hC.d ∈ Δ := by
      rw [hΔ, hU.sylow_inter]
      exact ⟨1, U.one_mem, mul_one _⟩
    have h1 : m * hC.d * m⁻¹ ∈ Δ := (hmN hC.d).mp huΔ
    rw [hΔ, hU.sylow_inter] at h1
    obtain ⟨c, hc, hcu⟩ := h1
    refine ⟨c, hc, fun δ hδ => ?_⟩
    rw [hΔ, hU.sylow_inter] at hδ
    obtain ⟨w, hw, rfl⟩ := hδ
    have hmw : m * w * m⁻¹ = w := by
      rw [(Subgroup.mem_centralizer_iff.mp hm w hw).symm, mul_inv_cancel_right]
    calc m * (hC.d * w) * m⁻¹ = (m * hC.d * m⁻¹) * (m * w * m⁻¹) := by group
      _ = hC.d * c * w := by rw [← hcu, hmw]
      _ = c * (hC.d * w) := by rw [hdU c hc, mul_assoc]
  have hneg : (-1 : ZMod 7) ≠ 1 := by decide
  obtain ⟨e⟩ := h.psl27
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hsimp : IsSimpleGroup (cosetNormalizerPerm Δ).range := by
    have : IsSimpleGroup PSL(2, ZMod 7) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
    have : Nontrivial (cosetNormalizerPerm Δ).range := e.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom (MulEquiv.surjective _)
  set f := (cosetNormalizerPerm Δ).rangeRestrict with hf
  have hMn' : (M.map f).Normal := hMn.map f (cosetNormalizerPerm Δ).rangeRestrict_surjective
  have hxN := hCN x hx
  have hxM : (⟨x, hxN⟩ : Subgroup.normalizer Δ) ∈ M := by
    rw [hM, Subgroup.mem_subgroupOf]
    exact hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map f) with hbot | htop
  · have h1 : f ⟨x, hxN⟩ = 1 := by
      have := Subgroup.mem_map_of_mem f hxM
      rwa [hbot, Subgroup.mem_bot] at this
    have h2 : (⟨x, hxN⟩ : Subgroup.normalizer Δ) ∈ (cosetNormalizerPerm Δ).ker := by
      rw [MonoidHom.mem_ker]
      have := congrArg Subtype.val h1
      exact this
    rw [cosetNormalizerPerm_ker_eq_entire_centralizer, Subgroup.mem_subgroupOf] at h2
    rw [← h.five.1]
    exact h2
  · exfalso
    have hcomm : ∀ a b : (cosetNormalizerPerm Δ).range, a * b = b * a := by
      intro a b
      obtain ⟨ma, hma, rfl⟩ : a ∈ M.map f := htop ▸ Subgroup.mem_top a
      obtain ⟨mb, hmb, rfl⟩ : b ∈ M.map f := htop ▸ Subgroup.mem_top b
      obtain ⟨ca, hca, hta⟩ := hact _ (Subgroup.mem_subgroupOf.mp hma) ma.2
      obtain ⟨cb, hcb, htb⟩ := hact _ (Subgroup.mem_subgroupOf.mp hmb) mb.2
      apply Subtype.ext
      ext δ
      simp only [hf, MonoidHom.coe_rangeRestrict, Subgroup.coe_mul, Equiv.Perm.mul_apply,
        cosetNormalizerPerm_apply]
      have hb := htb δ δ.2
      have ha := hta δ δ.2
      have hbδ : (mb : G) * δ * (mb : G)⁻¹ ∈ Δ := (mb.2 δ).mp δ.2
      have haδ : (ma : G) * δ * (ma : G)⁻¹ ∈ Δ := (ma.2 δ).mp δ.2
      rw [hta _ hbδ, htb _ haδ, hb, ha, ← mul_assoc, ← mul_assoc, hUc ca hca cb hcb]
    obtain ⟨a, b, hab⟩ : ∃ a b : (cosetNormalizerPerm Δ).range, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      have hcard : Nat.card (cosetNormalizerPerm Δ).range = 168 := by
        have hpsl := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := ZMod 7)
        rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hneg,
          Nat.card_zmod] at hpsl
        rw [Nat.card_congr e.toEquiv]
        omega
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (cosetNormalizerPerm Δ).range) 2
        (by rw [hcard]; norm_num)
      have hyn : (Subgroup.zpowers y).Normal :=
        ⟨fun a ha g => by rw [mul_assoc, hc a g⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]; exact ha⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers y) with h1 | h1
      · have := Subgroup.mem_zpowers y
        rw [h1, Subgroup.mem_bot] at this
        rw [this, orderOf_one] at hy
        omega
      · have h2 := congrArg (fun H : Subgroup _ => Nat.card H) h1
        simp only [Nat.card_zpowers, hy, Subgroup.card_top, hcard] at h2
        omega
    exact hab (hcomm a b)

theorem sign_conj_eq_one (h : NineSixSetting hC T S U) {n : G}
    (hn : n ∈ Subgroup.normalizer ((S : Set G) ∩ D)) (σ : Equiv.Perm U)
    (hσ : ∀ x : U, (σ x : G) = n * x * n⁻¹) (ι : U ≃ Fin 8) :
    Equiv.Perm.sign (ι.permCongr σ) = 1 := by
  classical
  have hU := h.delta
  have := hU.isElementaryAbelian
  set Δ := (S : Set G) ∩ D with hΔ
  have hNU : ∀ m ∈ Subgroup.normalizer Δ, m ∈ Subgroup.normalizer (U : Set G) := by
    intro m hm
    rw [hΔ, hU.sylow_inter] at hm
    exact (hU.affine h.three).1 hm
  let φ : Subgroup.normalizer Δ →* Equiv.Perm U :=
    { toFun := fun m =>
        { toFun := fun x => ⟨m * x * (m : G)⁻¹, (hNU m m.2 x).mp x.2⟩
          invFun := fun x => ⟨(m : G)⁻¹ * x * m, (hNU m m.2 ((m : G)⁻¹ * x * m)).mpr
            (by simp [mul_assoc])⟩
          left_inv := fun x => Subtype.ext (by simp [mul_assoc])
          right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
      map_one' := by ext x; simp
      map_mul' := fun a b => by ext x; simp [mul_assoc] }
  let ψ : Subgroup.normalizer Δ →* ℤˣ :=
    Equiv.Perm.sign.comp ((ι.permCongrHom : Equiv.Perm U ≃* Equiv.Perm (Fin 8)).toMonoidHom.comp φ)
  set f := cosetNormalizerPerm Δ with hf
  have hker : f.ker ≤ ψ.ker := by
    intro m hm
    rw [hf, cosetNormalizerPerm_ker_eq_entire_centralizer, Subgroup.mem_subgroupOf, h.five.1,
      ← h.centralizer_eq_sylow_map] at hm
    have h1 : φ m = 1 := by
      ext x
      change (m : G) * x * (m : G)⁻¹ = x
      rw [← (Subgroup.mem_centralizer_iff.mp hm x x.2), mul_inv_cancel_right]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
  have hsimp := h.isSimpleGroup_range
  have hmapn : (ψ.ker.map f.rangeRestrict).Normal :=
    Subgroup.Normal.map inferInstance _ f.rangeRestrict_surjective
  have hσφ : σ = φ ⟨n, hn⟩ := by
    ext x
    rw [hσ x]
    rfl
  rw [hσφ]
  change ψ ⟨n, hn⟩ = 1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.ker.map f.rangeRestrict) with hbot | htop
  · exfalso
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := f.range) 3
      (by rw [hf, h.card_range]; norm_num)
    obtain ⟨n₀, hn₀⟩ := f.rangeRestrict_surjective y
    have h2 : n₀ ^ 2 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_two, Int.units_mul_self]
    have h3 : f.rangeRestrict (n₀ ^ 2) = 1 := by
      have := Subgroup.mem_map_of_mem f.rangeRestrict h2
      rwa [hbot, Subgroup.mem_bot] at this
    rw [map_pow, hn₀] at h3
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hy] at this
    norm_num at this
  · obtain ⟨k, hk, hkn⟩ : f.rangeRestrict ⟨n, hn⟩ ∈ ψ.ker.map f.rangeRestrict :=
      htop ▸ Subgroup.mem_top _
    have hk' : k⁻¹ * ⟨n, hn⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have := congrArg Subtype.val hkn
      simp only [MonoidHom.coe_rangeRestrict] at this
      rw [this, inv_mul_cancel]
    have := ψ.ker.mul_mem hk (hker hk')
    rw [mul_inv_cancel_left] at this
    exact this

theorem exists_mem_normalizer_conj_eq (h : NineSixSetting hC T S U) (φ : U ≃* U) :
    ∃ n ∈ Subgroup.normalizer ((S : Set G) ∩ D), ∀ x : U, n * (x : G) * n⁻¹ = φ x := by
  classical
  have hU := h.delta
  have := hU.isElementaryAbelian
  set Δ := (S : Set G) ∩ D with hΔ
  have hNU : ∀ m ∈ Subgroup.normalizer Δ, m ∈ Subgroup.normalizer (U : Set G) := by
    intro m hm
    rw [hΔ, hU.sylow_inter] at hm
    exact (hU.affine h.three).1 hm
  let c : Subgroup.normalizer Δ →* MulAut U :=
    { toFun := fun m =>
        { toFun := fun x => ⟨m * x * (m : G)⁻¹, (hNU m m.2 x).mp x.2⟩
          invFun := fun x => ⟨(m : G)⁻¹ * x * m, (hNU m m.2 ((m : G)⁻¹ * x * m)).mpr
            (by simp [mul_assoc])⟩
          left_inv := fun x => Subtype.ext (by simp [mul_assoc])
          right_inv := fun x => Subtype.ext (by simp [mul_assoc])
          map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
      map_one' := by ext x; simp
      map_mul' := fun a b => by ext x; simp [mul_assoc] }
  have hkerc : c.ker = (Subgroup.centralizer (U : Set G)).subgroupOf (Subgroup.normalizer Δ) := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hm x hx
      have hmx := congrArg Subtype.val (DFunLike.congr_fun hm ⟨x, hx⟩)
      change (m : G) * x * (m : G)⁻¹ = x at hmx
      calc x * (m : G) = (m : G) * x * (m : G)⁻¹ * m := by rw [hmx]
        _ = (m : G) * x := by group
    · intro hm
      ext x
      change (m : G) * x * (m : G)⁻¹ = x
      rw [← hm x x.2, mul_inv_cancel_right]
  have hTN : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      Subgroup.normalizer Δ := h.le.trans h.four.2.1
  have hTcard : Nat.card (((T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype).subgroupOf (Subgroup.normalizer Δ)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, h.card_sylow_map]
  have hN : Nat.card (Subgroup.normalizer Δ) = 16 * 168 := by
    have hk := Subgroup.card_ker_mul_card_range (cosetNormalizerPerm Δ)
    rw [cosetNormalizerPerm_ker_eq_entire_centralizer, h.five.1, hTcard, h.card_range] at hk
    omega
  have hc := Subgroup.card_ker_mul_card_range c
  rw [hkerc, h.centralizer_eq_sylow_map, hTcard, hN] at hc
  have htop : c.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [CFSG.ProperTwoGeneratedCore.ExceptionalEight.card_mulAut_eq_168 h.card]
    omega)
  obtain ⟨m, hm⟩ := (MonoidHom.range_eq_top.mp htop) φ
  exact ⟨m, m.2, fun x => congrArg Subtype.val (DFunLike.congr_fun hm x)⟩

end NineSixSetting

end CFSG.OddTranspositions.PartThree.Nine
