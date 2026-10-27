module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210g
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxF
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxM
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxN

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

omit [Finite Γ] in
theorem SemisimpleAction.orbitClosure_le_group (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    orbitClosure J A ≤ G :=
  orbitClosure_le fun a ha => lcal_le (h.permutes_lcal a ha J hJ)

theorem SemisimpleAction.admits_sup_orbitClosure (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    Admits (cenIn G A ⊔ A) (orbitClosure J A) :=
  sup_le (fun _ hd => h.isDirectProduct_orbitClosure.le_normalizer ⟨J, hJ, rfl⟩
    (Subgroup.mem_inf.mp hd).1) (Thm210.admits_orbitClosure J)

omit [Finite Γ] in
theorem smear_map_conj (J : Subgroup Γ) {a : Γ} (ha : a ∈ A) :
    smear (J.map (MulAut.conj a).toMonoidHom) A = smear J A := by
  unfold smear
  rw [orbitClosure_map_conj J ha]

omit [Finite Γ] in
theorem SemisimpleAction.orbitClosure_le_sSup_diff (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {K : Subgroup Γ} (hK : ∀ a ∈ A, K ≠ J.map (MulAut.conj a).toMonoidHom) :
    orbitClosure J A ≤ sSup (lcal G \ {K}) :=
  orbitClosure_le fun a ha => le_sSup ⟨h.permutes_lcal a ha J hJ, fun he =>
    hK a ha (Set.mem_singleton_iff.mp he).symm⟩

theorem SemisimpleAction.projIn_eq_bot_of_not_orbit (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {K : Subgroup Γ} (hKG : K ∈ lcal G) (hK : ∀ a ∈ A, K ≠ J.map (MulAut.conj a).toMonoidHom)
    {Q : Subgroup Γ} (hQ : Q ≤ orbitClosure J A) : projIn (lcal G) K Q = ⊥ := by
  have hG := h.isDirectProduct_lcal
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hyQ, rfl⟩ := (hG.mem_projIn_iff hKG).mp hx
  have : hG.coord hKG y = 1 :=
    (hG.coord_eq_one_iff hKG y).mpr (h.orbitClosure_le_sSup_diff hJ hK (hQ hyQ))
  rw [this]
  exact Subgroup.one_mem _

theorem SemisimpleAction.mem_fProd_of_pow_eq_one
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {ℓ k : ℕ} (hℓ : ℓ.Prime) {v : Γ} (hv : v ∈ CFSG.fittingSubgroupOf (smear J A)) (hv1 : v ≠ 1)
    (hvℓ : v ^ ℓ = 1) {t : Γ} (htG₁ : t ∈ orbitClosure J A) (htM : t ∈ kProd A G)
    (htk : t ^ (ℓ ^ k) = 1) : t ∈ fProd A G := by
  have hG := h.isDirectProduct_lcal
  obtain ⟨htG, hkc⟩ := h.mem_kProd_iff.mp htM
  refine h.mem_fProd_iff.mpr ⟨htG, fun K hK => ?_⟩
  by_cases hKo : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
  · obtain ⟨a, ha, rfl⟩ := hKo
    set K := J.map (MulAut.conj a).toMonoidHom with hKdef
    have hsm : smear K A = smear J A := smear_map_conj J ha
    have hvG : v ∈ G := (Subgroup.mem_inf.mp (h.smear_le_cenIn hJ
      ((Subgroup.map_subtype_le _) hv))).1
    set c : ↥K := hG.coord hK ⟨v, hvG⟩ with hc
    have hcF : (c : Γ) ∈ CFSG.fittingSubgroupOf (cenIn K (norIn A K)) := by
      rw [← h.projIn_fittingSubgroupOf_smear hK, hsm]
      exact (hG.mem_projIn_iff hK).mpr ⟨⟨v, hvG⟩, hv, rfl⟩
    have hc1 : (c : Γ) ≠ 1 := by
      intro hc1
      have h1 : hG.coord hK ⟨v, hvG⟩ = 1 := Subtype.ext hc1
      have h2 : v ∈ smear J A ⊓ sSup (lcal G \ {K}) := by
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.map_subtype_le _) hv, ?_⟩
        exact (hG.coord_eq_one_iff hK _).mp h1
      rw [← hsm, h.smear_inf_sSup hK, Subgroup.mem_bot] at h2
      exact hv1 h2
    have hcℓ : (c : Γ) ^ ℓ = 1 := by
      have := congrArg (hG.coord hK) (show (⟨v, hvG⟩ : ↥G) ^ ℓ = 1 from Subtype.ext hvℓ)
      rw [map_pow, map_one] at this
      exact congrArg Subtype.val this
    have hyk : ((hG.coord hK ⟨t, htG⟩ : ↥K) : Γ) ^ (ℓ ^ k) = 1 := by
      have h1 : (hG.coord hK ⟨t, htG⟩) ^ (ℓ ^ k) = 1 := by
        rw [← map_pow]
        exact (congrArg (hG.coord hK) (show (⟨t, htG⟩ : ↥G) ^ (ℓ ^ k) = 1 from
          Subtype.ext htk)).trans (map_one _)
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    have := h.mem_fittingSubgroupOf_cenIn_of_pow_eq_one hK hℓ (hkc _ hK) hyk hcF hc1 hcℓ
    exact h.fittingSubgroupOf_cenIn_le_kJ hK this
  · have hK1 : hG.coord hK ⟨t, htG⟩ = 1 :=
      (hG.coord_eq_one_iff hK _).mpr
        (h.orbitClosure_le_sSup_diff hJ (fun a ha he => hKo ⟨a, ha, he⟩) htG₁)
    rw [hK1]
    exact Subgroup.one_mem _

theorem SemisimpleAction.le_fProd_of_le_orbitClosure
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {X : Subgroup Γ} (hXG₁ : X ≤ orbitClosure J A)
    (hX : Admits (cenIn G A ⊔ A) X) (hFX : ¬ CFSG.fittingSubgroupOf (smear J A) ≤ X) :
    X ≤ fProd A G := by
  have hG := h.isDirectProduct_lcal
  have hXG : X ≤ G := hXG₁.trans (h.orbitClosure_le_group hJ)
  have hnil : Group.IsNilpotent X := by
    refine isNilpotent_of_forall_projIn hG hXG fun K hK => ?_
    by_cases hKo : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
    · obtain ⟨a, ha, rfl⟩ := hKo
      by_contra hnn
      have := thm210h h hXG hX hK hnn
      rw [smear_map_conj J ha] at this
      exact hFX this
    · rw [h.projIn_eq_bot_of_not_orbit hJ hK (fun a ha he => hKo ⟨a, ha, he⟩) hXG₁]
      infer_instance
  have := thm210f h hXG hX hnil
  rwa [h.mOf_eq_kProd, h.fittingSubgroupOf_kProd] at this

theorem SemisimpleAction.le_fProd_of_fixed
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {T : Subgroup Γ} {u : Γ} (hTG₁ : T ≤ orbitClosure J A) (hTM : T ≤ kProd A G)
    (hTA : A ≤ Subgroup.normalizer (T : Set Γ)) (huR : u ∈ fProd A G)
    (huG₁ : u ∈ orbitClosure J A) (hu1 : u ≠ 1) (hu : ∀ t ∈ T, t * u * t⁻¹ = u) :
    T ≤ fProd A G := by
  have hG := h.isDirectProduct_lcal
  have huG : u ∈ G := h.orbitClosure_le_group hJ huG₁
  obtain ⟨K₀, hK₀, hK₀u⟩ : ∃ K₀ : Subgroup Γ, ∃ hK₀ : K₀ ∈ lcal G,
      hG.coord hK₀ ⟨u, huG⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hu1
    have : (⟨u, huG⟩ : ↥G) = 1 := hG.ext_coord fun K hK => by rw [map_one]; exact hcon K hK
    exact congrArg Subtype.val this
  obtain ⟨a₀, ha₀, rfl⟩ : ∃ a₀ ∈ A, K₀ = J.map (MulAut.conj a₀).toMonoidHom := by
    by_contra hno
    apply hK₀u
    exact (hG.coord_eq_one_iff hK₀ ⟨u, huG⟩).mpr (h.orbitClosure_le_sSup_diff hJ
      (fun a ha he => hno ⟨a, ha, he⟩) huG₁)
  intro t ht
  have htG₁ : t ∈ orbitClosure J A := hTG₁ ht
  have htG : t ∈ G := h.orbitClosure_le_group hJ htG₁
  obtain ⟨_, hkc⟩ := h.mem_kProd_iff.mp (hTM ht)
  refine h.mem_fProd_iff.mpr ⟨htG, fun K hK => ?_⟩
  by_cases hKo : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
  · obtain ⟨a, ha, rfl⟩ := hKo
    set b := a * a₀⁻¹ with hb
    have hbA : b ∈ A := mul_mem ha (inv_mem ha₀)
    have hKb : J.map (MulAut.conj a).toMonoidHom =
        (J.map (MulAut.conj a₀).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
      rw [map_conj_map_conj, hb, inv_mul_cancel_right]
    have hperm := h.permutes_lcal b hbA
    have hu'G : b * u * b⁻¹ ∈ G := hG.conj_mem hperm huG
    have hu'R : b * u * b⁻¹ ∈ fProd A G :=
      (Subgroup.mem_normalizer_iff.mp (h.admits_fProd hbA) u).mp huR
    have hu'T : ∀ t ∈ T, t * (b * u * b⁻¹) * t⁻¹ = b * u * b⁻¹ := by
      intro t ht
      have ht' : b⁻¹ * t * b ∈ T := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hTA (inv_mem hbA)) t).mp ht
      calc t * (b * u * b⁻¹) * t⁻¹
          = b * ((b⁻¹ * t * b) * u * (b⁻¹ * t * b)⁻¹) * b⁻¹ := by group
        _ = b * u * b⁻¹ := by rw [hu _ ht']
    set K₁ := J.map (MulAut.conj a).toMonoidHom with hK₁
    set K₂ := J.map (MulAut.conj a₀).toMonoidHom with hK₂
    have hcu : ((hG.coord hK ⟨b * u * b⁻¹, hu'G⟩ : ↥K₁) : Γ) ≠ 1 := by
      have h1 := hG.coord_conj hperm hK₀ huG
      have h2 := hG.coord_val_congr (hperm _ hK₀) hK hKb.symm ⟨b * u * b⁻¹, hu'G⟩
      intro hc1
      apply hK₀u
      have h3 := h1.symm.trans (h2.trans hc1)
      refine Subtype.ext ?_
      change ((hG.coord hK₀ ⟨u, huG⟩ : ↥K₂) : Γ) = 1
      calc ((hG.coord hK₀ ⟨u, huG⟩ : ↥K₂) : Γ)
          = b⁻¹ * (b * ((hG.coord hK₀ ⟨u, huG⟩ : ↥K₂) : Γ) * b⁻¹) * b := by group
        _ = 1 := by rw [h3]; group
    have hcomm : (⟨t, htG⟩ : ↥G) * ⟨b * u * b⁻¹, hu'G⟩ = ⟨b * u * b⁻¹, hu'G⟩ * ⟨t, htG⟩ :=
      Subtype.ext (mul_inv_eq_iff_eq_mul.mp (hu'T t ht))
    have h5 := congrArg (hG.coord hK) hcomm
    rw [map_mul, map_mul] at h5
    obtain ⟨_, hfc⟩ := h.mem_fProd_iff.mp hu'R
    exact h.mem_fittingSubgroupOf_kJ_of_commute hK (hkc _ hK) (hfc _ hK) hcu
      (congrArg Subtype.val h5)
  · have hK1 : hG.coord hK ⟨t, htG⟩ = 1 :=
      (hG.coord_eq_one_iff hK _).mpr
        (h.orbitClosure_le_sSup_diff hJ (fun a ha he => hKo ⟨a, ha, he⟩) htG₁)
    rw [hK1]
    exact Subgroup.one_mem _

theorem SemisimpleAction.sectionCentralizer_orbit_le_fProd
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {X : Subgroup Γ} (hXG₁ : X ≤ orbitClosure J A)
    (hX : Admits (cenIn G A ⊔ A) X) (hFX : ¬ CFSG.fittingSubgroupOf (smear J A) ≤ X) :
    orbitClosure J A ⊓ sectionCentralizer X (X ⊔ CFSG.fittingSubgroupOf (smear J A)) ≤
      fProd A G := by
  classical
  have hG := h.isDirectProduct_lcal
  set S := smear J A with hS
  set V := CFSG.fittingSubgroupOf S with hV
  set G₁ := orbitClosure J A with hG₁
  have hG₁G : G₁ ≤ G := h.orbitClosure_le_group hJ
  have hXG : X ≤ G := hXG₁.trans hG₁G
  have hSD : S ≤ cenIn G A := h.smear_le_cenIn hJ
  have hSG₁ : S ≤ G₁ := smear_le_orbitClosure J A
  have hVS : V ≤ S := Subgroup.map_subtype_le _
  have hVG₁ : V ≤ G₁ := hVS.trans hSG₁
  have hXS : X ⊓ S = ⊥ := h.inf_smear_eq_bot hX hJ hFX
  have hXR : X ≤ fProd A G := h.le_fProd_of_le_orbitClosure hJ hXG₁ hX hFX
  have hVR : V ≤ fProd A G :=
    h.le_fProd_of_nilpotent (hVS.trans (hSD.trans inf_le_left)) (isNilpotent_fittingSubgroupOf _)
      fun d hd y hy => fittingSubgroupOf_conj_mem_of_mem_normalizer
        (h.cenIn_le_normalizer_smear hJ hd) hy
  set W := X ⊔ V with hW
  have hWR : W ≤ fProd A G := sup_le hXR hVR
  have hWG₁ : W ≤ G₁ := sup_le hXG₁ hVG₁
  have hcommR := h.isMulCommutative_fProd
  have hWab : IsMulCommutative W := isMulCommutative_of_le hWR
  set T := G₁ ⊓ sectionCentralizer X W with hT
  have hTG₁ : T ≤ G₁ := inf_le_left
  have hTG : T ≤ G := hTG₁.trans hG₁G
  have hVadm : Admits (cenIn G A ⊔ A) V := by
    refine sup_le (le_normalizer_of_conj_mem fun d hd y hy => ?_)
      (le_normalizer_of_conj_mem fun a ha y hy => ?_)
    · exact fittingSubgroupOf_conj_mem_of_mem_normalizer (h.cenIn_le_normalizer_smear hJ hd) hy
    · have h1 := Subgroup.mem_centralizer_iff.mp (smear_le_centralizer J A (hVS hy)) a ha
      have h2 : a * y * a⁻¹ = y := by rw [h1]; group
      rw [h2]
      exact hy
  have hWadm : Admits (cenIn G A ⊔ A) W := fun q hq => mem_normalizer_sup (hX hq) (hVadm hq)
  have hG₁adm := h.admits_sup_orbitClosure hJ
  have hTadm : Admits (cenIn G A ⊔ A) T := by
    intro q hq
    refine mem_normalizer_of_conj_le fun g hg => ?_
    obtain ⟨hgG₁, hgs⟩ := Subgroup.mem_inf.mp hg
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hG₁adm hq) g).mp hgG₁,
        sectionCentralizer_conj_mem (hX hq) (hWadm hq) hgs⟩
  have hTD : T ⊓ cenIn G A ≤ V := by
    intro d hd
    obtain ⟨hdT, hdD⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨hdG₁, hds⟩ := Subgroup.mem_inf.mp hdT
    obtain ⟨-, hdc⟩ := mem_cenIn_iff.mp hdD
    have hdS : d ∈ S := Subgroup.mem_inf.mpr ⟨hdG₁, hdc⟩
    refine h.mem_fittingSubgroupOf_smear_of_commute hJ hdS fun v hv => ?_
    have h1 : ⁅d, v⁆ ∈ X := (mem_sectionCentralizer_iff.mp hds).2.2 v (Subgroup.mem_sup_right hv)
    have h2 : ⁅d, v⁆ ∈ V := by
      have := fittingSubgroupOf_conj_mem_of_mem_normalizer (h.cenIn_le_normalizer_smear hJ hdD) hv
      have h3 : ⁅d, v⁆ = (d * v * d⁻¹) * v⁻¹ := rfl
      rw [h3]
      exact mul_mem this (inv_mem hv)
    have h4 : ⁅d, v⁆ ∈ X ⊓ S := Subgroup.mem_inf.mpr ⟨h1, hVS h2⟩
    rw [hXS, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
    exact h4
  have hTsol : Group.IsSolvable T := by
    refine isSolvable_of_forall_projIn hG hTG fun K hK => ?_
    by_cases hKo : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
    · by_contra hns
      obtain ⟨-, hST⟩ := thm210g h hTG hTadm hK hns
      obtain ⟨a, ha, rfl⟩ := hKo
      rw [smear_map_conj J ha] at hST
      have hSV : S ≤ V := fun x hx => hTD (Subgroup.mem_inf.mpr ⟨hST hx, hSD hx⟩)
      exact h.fittingSubgroupOf_smear_ne hJ (le_antisymm hVS hSV)
    · rw [h.projIn_eq_bot_of_not_orbit hJ hK (fun a ha he => hKo ⟨a, ha, he⟩) hTG₁]
      infer_instance
  have hTM : T ≤ kProd A G := by
    have hDT : cenIn G A ≤ Subgroup.normalizer (T : Set Γ) := fun d hd =>
      hTadm (Subgroup.mem_sup_left hd)
    have hsol : Group.IsSolvable ↥(cenIn G A ⊔ T) :=
      isSolvable_sup_of_le_normalizer hDT hTsol h.solvable_cen
    have := (thm210b h).2 ⟨sup_le inf_le_left hTG, le_sup_left, hsol⟩
    rw [h.mOf_eq_kProd] at this
    exact le_sup_right.trans this
  have hVne : V ≠ ⊥ := h.fittingSubgroupOf_smear_ne_bot hJ
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card V ≠ 1 from fun h1 => hVne (Subgroup.card_eq_one.mp h1))
  have := Fact.mk hℓ
  obtain ⟨v₀, hv₀⟩ := exists_prime_orderOf_dvd_card' ℓ hℓd
  have hvV : (v₀ : Γ) ∈ V := v₀.2
  have hv₀1 : v₀ ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hv₀
    exact hℓ.one_lt.ne hv₀
  have hv1 : (v₀ : Γ) ≠ 1 := fun he => hv₀1 (Subtype.ext he)
  have hvℓ : (v₀ : Γ) ^ ℓ = 1 := by
    have := pow_orderOf_eq_one v₀
    rw [hv₀] at this
    exact congrArg Subtype.val this
  have hvX : (v₀ : Γ) ∉ X := fun hvx => hv1 (Subgroup.mem_bot.mp
    (hXS ▸ Subgroup.mem_inf.mpr ⟨hvx, hVS hvV⟩))
  obtain ⟨u, huW, hu1, hu⟩ := exists_fixed_ne_one (W := W) (X := X) (T := T)
    (R := fProd A G ⊓ G₁) hℓ (fun g hg => (mem_sectionCentralizer_iff.mp
      (Subgroup.mem_inf.mp hg).2).2.1)
    (fun t ht w hw => (mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp ht).2).2.2 w hw)
    (fun r hr => Subgroup.mem_centralizer_iff.mpr fun w hw => by
      have := mul_comm' (⟨w, hWR hw⟩ : fProd A G) ⟨r, (Subgroup.mem_inf.mp hr).1⟩
      exact congrArg Subtype.val this)
    (fun t ht ⟨k, hk⟩ => Subgroup.mem_inf.mpr
      ⟨h.mem_fProd_of_pow_eq_one hJ hℓ hvV hv1 hvℓ (hTG₁ ht) (hTM ht) hk, hTG₁ ht⟩)
    (Subgroup.mem_sup_right hvV) hvX hvℓ
  exact h.le_fProd_of_fixed hJ hTG₁ hTM (fun a ha => hTadm (Subgroup.mem_sup_right ha))
    (hWR huW) (hWG₁ huW) hu1 hu

end CFSG.SignalizerFunctorTheorem.McBride.Near
