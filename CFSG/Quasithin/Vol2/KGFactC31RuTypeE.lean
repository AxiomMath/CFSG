module

public import CFSG.Quasithin.Vol2.KGFactC31RuHyp
public import CFSG.Quasithin.Vol2.KGFactC31RuConcl
public import CFSG.Quasithin.Vol2.KGFactC31RuBigZ
public import CFSG.Quasithin.Vol2.KGFactC31RuRefK
public import CFSG.Sporadic.Schreier.RuPair

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31

variable {A : Type} [Group A]

section Facts


theorem ruN_eq_normalizer_E :
    ruP ⊓ Subgroup.normalizer (ruESub : Set (Equiv.Perm (Fin 4060))) = ruN := by
  have h1 : ruN ≤ ruP ⊓ Subgroup.normalizer (ruESub : Set (Equiv.Perm (Fin 4060))) :=
    le_inf ruN_le (ruN_le_normalizer_K.trans normalizer_K_le_normalizer_E)
  exact (Subgroup.eq_of_le_of_card_ge h1 (card_normalizer_E_le.trans card_ruN.ge)).symm


theorem commut_memE {k v : Equiv.Perm (Fin 4060)} (hk : k ∈ ruK) (hv : v ∈ ruK) :
    k * v * k⁻¹ * v⁻¹ ∈ ruESub := by
  obtain ⟨-, hcomm, -⟩ := isSpecial2Group_ruK
  have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨k, hk⟩ : ↥ruK))
    (Subgroup.mem_top (⟨v, hv⟩ : ↥ruK))
  rw [← commutator_def, hcomm, mem_center_ruK_iff, commutatorElement_def] at h
  simpa using h

theorem uV32E_le_ruK : uV32E ≤ ruK := by
  rw [← ruP_centralizer_E, ← uE_eq]
  refine le_inf (refSub_le_ruP _) fun v hv => Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  exact eSub_comm hvV32E u v (by rw [← refSub_eq]; exact uE_le_uV32E hu)
    (by rw [← refSub_eq]; exact hv)

end Facts

section Config

variable [Finite A]

theorem config_E {M₀ R M V : Subgroup A} (h : RuHyp M₀ R M V) (e : G₀ ≃* A)
    (hEV : img e uE ≤ V) (hxE : e ⟨xE, ruN_le xE_memN⟩ ∈ M₀) :
    V = img e uE ∧ pCoreOf 2 M₀ = img e ruK ∧ M₀ = img e ruN ∧
      R = Subgroup.centralizer ((img e uE : Subgroup A) : Set A) := by
  obtain ⟨hVO, hOR, hRC, hNRM⟩ := h.facts
  set V' := pb e V with hV'
  set M₀' := pb e M₀ with hM₀'
  have hVP : V' ≤ ruP := pb_le e V
  have hEV' : uE ≤ V' := (le_iff_img_le e (refSub_le_ruP _)).mp hEV
  have hVab : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := by
    intro a ha b hb
    obtain ⟨haP, haV⟩ := (mem_pb e).mp ha
    obtain ⟨hbP, hbV⟩ := (mem_pb e).mp hb
    have := h.V_comm _ haV _ hbV
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (e.injective this)
  have hVsq : ∀ a ∈ V', a * a = 1 := by
    intro a ha
    obtain ⟨haP, haV⟩ := (mem_pb e).mp ha
    have := h.V_sq _ haV
    rw [← map_mul, ← map_one e] at this
    exact congrArg Subtype.val (e.injective this)
  have hM₀N : M₀' ≤ Subgroup.normalizer (V' : Set (Equiv.Perm (Fin 4060))) :=
    pb_le_normalizer e h.M₀V
  have hxM : xE ∈ M₀' := (apply_mem_iff_mem_pb e).mp hxE
  have hV32 : V' ≤ uV32E := by
    intro v hv
    refine mem_V32E_of (hVP hv) (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hVab u (hEV' hu) v hv) (hVsq v hv) fun j _ => ?_
    have hc : xE ^ (j + 1) * v * (xE ^ (j + 1))⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hM₀N hxM) _) v).mp hv
    exact hVab v hv _ hc
  have hM₀E : M₀' ≤ ruN := by
    intro m hm
    rw [← ruN_eq_normalizer_E, ← uE_eq]
    refine ⟨pb_le e M₀ hm, mem_normalizer_of_conj_le fun u hu => ?_⟩
    by_cases hu1 : u = 1
    · rw [hu1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    by_contra hn
    have h1 : m * u * m⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (hM₀N hm) u).mp (hEV' hu)
    have h2 := ncard_fixSet_of_mem_uV32E (hV32 h1) hn
    rw [ncard_fixSet_conj, ncard_fixSet_of_mem_uE hu hu1] at h2
    exact absurd h2 (by norm_num)
  have hCK : pb e (Subgroup.centralizer (V : Set A)) ≤ ruK := by
    rw [pb_centralizer, ← ruP_centralizer_E, ← uE_eq]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hEV')
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) :=
    isPGroup_of_pb e (isPGroup_ruK.to_le hCK)
  have hR : R = Subgroup.centralizer (V : Set A) := h.R_eq hC2
  have hNVR : Subgroup.normalizer (V : Set A) ≤ Subgroup.normalizer (R : Set A) := by
    rw [hR]
    exact normalizer_le_normalizer_centralizer V
  have hKV : img e ruK ≤ Subgroup.normalizer (V : Set A) := by
    rw [le_iff_img_le e ruK_le, pb_normalizer]
    refine le_inf ruK_le fun k hk => mem_normalizer_of_conj_le fun v hv => ?_
    have hvK : v ∈ ruK := uV32E_le_ruK (hV32 hv)
    have hc := commut_memE hk hvK
    rw [← uE_eq] at hc
    have : k * v * k⁻¹ = (k * v * k⁻¹ * v⁻¹) * v := by group
    rw [this]
    exact V'.mul_mem (hEV' hc) hv
  have hM₀E' : M₀ ≤ img e ruN := (img_le_iff_le_pb e).mpr hM₀E
  have hM₀K : M₀ ≤ Subgroup.normalizer ((img e ruK : Subgroup A) : Set A) := by
    refine hM₀E'.trans ?_
    rw [normalizer_img e ruK_le, img_le_img_iff e ruN_le]
    exact le_inf ruN_le ruN_le_normalizer_K
  have hK2 : IsPGroup 2 ↥(img e ruK) := by
    rw [img]
    exact (isPGroup_ruK.of_equiv (Subgroup.subgroupOfEquivOfLe ruK_le).symm).map _
  have hKO : M₀ ⊓ img e ruK ≤ pCoreOf 2 M₀ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm) (hM₀K hm))
      (hK2.to_le inf_le_right)
  have hKsec : img e ruK ≤ CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀) := by
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (M₀ : Set A) := hNRM (hNVR (hKV hk))
    refine ⟨h.NR (hNVR (hKV hk)), hkN, normalizer_le_normalizer_pCoreOf 2 M₀ hkN,
      fun x hx => hKO ⟨?_, ?_⟩⟩
    · have h1 : k * x⁻¹ * k⁻¹ ∈ M₀ :=
        (Subgroup.mem_normalizer_iff.mp hkN x⁻¹).mp (M₀.inv_mem hx)
      have : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
      rw [this]
      exact M₀.mul_mem hx h1
    · have h1 : x * k * x⁻¹ ∈ img e ruK := (Subgroup.mem_normalizer_iff.mp (hM₀K hx) k).mp hk
      exact (img e ruK).mul_mem h1 ((img e ruK).inv_mem hk)
  have hRK : R ≤ img e ruK := by
    rw [hR, ← img_pb e (Subgroup.centralizer (V : Set A))]
    exact img_mono e hCK
  have hRKe : img e ruK = R := eq_of_isSylowTwoOf_le h.syl hRK hKsec hK2
  have hVE : V' ≤ uE := by
    intro v hv
    rw [uE_eq, ruE_eq_center]
    have hvK : v ∈ ruK := uV32E_le_ruK (hV32 hv)
    refine ⟨⟨v, hvK⟩, Subgroup.mem_center_iff.mpr fun k => Subtype.ext ?_, rfl⟩
    have hkR : e ⟨k, ruK_le k.2⟩ ∈ R := by
      rw [← hRKe]
      exact (apply_mem_img e).mpr k.2
    rw [hR] at hkR
    obtain ⟨hvP, hvV⟩ := (mem_pb e).mp hv
    have := Subgroup.mem_centralizer_iff.mp hkR _ hvV
    rw [← map_mul, ← map_mul] at this
    exact (congrArg Subtype.val (e.injective this)).symm
  have hVeq : V = img e uE := by
    rw [pb_eq_iff e (refSub_le_ruP _)]
    exact le_antisymm hVE hEV'
  have hNM : img e ruN ≤ Subgroup.normalizer (M₀ : Set A) := by
    have hN : ruP ⊓ Subgroup.normalizer (uE : Set (Equiv.Perm (Fin 4060))) = ruN := by
      rw [uE_eq]
      exact ruN_eq_normalizer_E
    have : img e ruN = Subgroup.normalizer (V : Set A) := by
      rw [hVeq, normalizer_img e (refSub_le_ruP _)]
      exact (congrArg (img e) hN).symm
    rw [this]
    exact hNVR.trans hNRM
  have hNle : ruN ≤ M₀' := by
    refine ruN_le_closure.trans ?_
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hxM
    · have hn : e ⟨nE, ruN_le nE_memN⟩ ∈ Subgroup.normalizer (M₀ : Set A) :=
        hNM ((apply_mem_img e).mpr nE_memN)
      have := (Subgroup.mem_normalizer_iff.mp hn _).mp hxE
      rw [← map_inv, ← map_mul, ← map_mul] at this
      simpa using (apply_mem_iff_mem_pb e).mp this
  have hM₀eq : M₀ = img e ruN := by
    rw [pb_eq_iff e ruN_le]
    exact le_antisymm hM₀E hNle
  have hOK : pCoreOf 2 M₀ = img e ruK := by
    refine le_antisymm (hOR.trans hRKe.symm.le) ?_
    refine le_pCoreOf_of_le_normalizer 2 ?_ hM₀K hK2
    rw [hM₀eq]
    exact img_mono e ruK_leN
  exact ⟨hVeq, hOK, hM₀eq, by rw [hR, hVeq]⟩

theorem concl_E {S M₀ R M V : Subgroup A}
    (hSs : IsSporadic .Ru ↥S) (hcS : Subgroup.center ↥S = ⊥) (hM₀S : M₀ ≤ S)
    (h : RuHyp M₀ R M V) (e : G₀ ≃* A) (hEV : img e uE ≤ V) {y : G₀} (hyM : e y ∈ M₀)
    (hyN : (y : Equiv.Perm (Fin 4060)) ∈ Subgroup.normalizer (uE : Set (Equiv.Perm (Fin 4060))))
    (hy : ∃ k : ℕ, y ^ 7 ^ k = 1) (hy1 : y ≠ 1) : Concl S M₀ R M V := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hyN' : (y : Equiv.Perm (Fin 4060)) ∈ ruN := by
    rw [← ruN_eq_normalizer_E, ← uE_eq]
    exact ⟨y.2, hyN⟩
  obtain ⟨n, hnN, hxM⟩ := exists_conj_std e ruN_le xE_memN orderOf_xE
    (by rw [card_ruN]; norm_num) hyN' hy hy1 hyM
  set e' := conjE e n⁻¹ with he'
  have hnE : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈
      Subgroup.normalizer (uE : Set (Equiv.Perm (Fin 4060))) := by
    have h1 : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈ ruN := by
      simpa using ruN.inv_mem hnN
    rw [← ruN_eq_normalizer_E, ← uE_eq] at h1
    exact h1.2
  have hEV' : img e' uE ≤ V := by
    have e1 : uE.map (MulAut.conj ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060))).toMonoidHom = uE :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnE
    rw [img_conjE, e1]
    exact hEV
  obtain ⟨hV, hO, hM, hR⟩ := config_E h e' hEV' hxM
  have hvP : ∀ i, vE i ∈ ruP := fun i => vOf_mem _ _ i
  have hv := liftV_basis hvP hvE
  have hVe : V = (eSub hv).map e'.toMonoidHom := by rw [eSub_liftV_map e' hvP hvE]; exact hV
  have hKN : ruK.subgroupOf ruP ≤ ruN.subgroupOf ruP := fun x hx => ruK_leN hx
  have hcN : Nat.card (ruN.subgroupOf ruP) = 168 * Nat.card (ruK.subgroupOf ruP) := by
    rw [card_subgroupOf_of_le ruN_le, card_subgroupOf_of_le ruK_le, card_ruN, card_ruK]
  have hK : CFSG.Quasithin.IsSpecial2Group 3 8 ↥(ruK.subgroupOf ruP) :=
    C31Spor.isSpecial2Group_of_mulEquiv (Subgroup.subgroupOfEquivOfLe ruK_le).symm
      isSpecial2Group_ruK
  have hNC : ∀ x ∈ ruN.subgroupOf ruP,
      x ∈ Subgroup.centralizer (eSub hv : Set G₀) ↔ x ∈ ruK.subgroupOf ruP := by
    intro x _
    rw [eSub_liftV hvP hvE, mem_centralizer_subgroupOf_iff (refSub_le_ruP _),
      Subgroup.mem_subgroupOf,
      ← ruP_centralizer_E, ← uE_eq]
    exact ⟨fun hc => ⟨x.2, hc⟩, fun hc => hc.2⟩
  exact concl_L3 hSs hcS hM₀S h.MN h.comm e'.toMonoidHom e'.injective hv hKN hcN hK hNC hVe hO hM
    (by rw [hR, ← eSub_liftV_map e' hvP hvE])

end Config

end CFSG.Quasithin.KGC31.Ru

end
