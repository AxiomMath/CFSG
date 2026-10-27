module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FN

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

section Index

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem card_eq_mul_two_pow_ch615 {J L T₀ : Subgroup Γ} (hLJ : L ≤ J)
    (hJL : J ≤ Subgroup.normalizer (L : Set Γ)) (hT₀ : IsPGroup 2 ↥T₀) (hJ : J = L ⊔ T₀) :
    ∃ a : ℕ, Nat.card J = Nat.card L * 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (L.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLJ).mpr hJL
  have hT₀J : T₀ ≤ J := hJ ▸ le_sup_right
  have hT₀N : T₀ ≤ Subgroup.normalizer (L : Set Γ) := hT₀J.trans hJL
  have hQ : IsPGroup 2 (↥J ⧸ L.subgroupOf J) := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    have hj : (j : Γ) ∈ ((L ⊔ T₀ : Subgroup Γ) : Set Γ) := by rw [← hJ]; exact j.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T₀ hT₀N] at hj
    obtain ⟨l, hl, t, ht, hlt⟩ := Set.mem_mul.mp hj
    obtain ⟨e, he⟩ := hT₀ ⟨t, ht⟩
    have ht2 : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    refine ⟨e, ?_⟩
    have hjq : (QuotientGroup.mk j : ↥J ⧸ L.subgroupOf J) =
        QuotientGroup.mk (⟨t, hT₀J ht⟩ : ↥J) := by
      rw [QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have : ((j⁻¹ * ⟨t, hT₀J ht⟩ : ↥J) : Γ) = t⁻¹ * l⁻¹ * t := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hlt, mul_inv_rev]
      rw [this]
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hT₀N ht)) l⁻¹).mp
        (L.inv_mem hl)
      simpa [mul_assoc] using this
    rw [hjq, ← QuotientGroup.mk_pow]
    have : (⟨t, hT₀J ht⟩ : ↥J) ^ 2 ^ e = 1 := Subtype.ext (by simpa using ht2)
    rw [this, QuotientGroup.mk_one]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQ
  refine ⟨a, ?_⟩
  have h1 := (L.subgroupOf J).card_mul_index
  rw [Subgroup.index, ha, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLJ).toEquiv] at h1
  exact h1.symm

end Index

section S5

open Equiv

theorem d8_trans_ch615 : ∀ a b : Fin 5, a ≠ 4 → b ≠ 4 → ∃ i, d8_ch615 i a = b := by
  decide +kernel

theorem card_overgroup_perm_five_ch615 {S₀ R₀ : Subgroup (Perm (Fin 5))} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hSR : S₀ ≤ R₀) (hRS : R₀ ≠ S₀) (hR : Group.IsSolvable ↥R₀) : Nat.card R₀ = 24 := by
  have h8 := card_sylow_perm_five_ch615 hS₀
  have hdvd : Nat.card R₀ ∣ 120 := card_perm_five_ch615 ▸ Subgroup.card_subgroup_dvd_card R₀
  have hle : Nat.card R₀ ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨m, hm⟩ := hdvd
  obtain ⟨k, hk⟩ : 8 ∣ Nat.card R₀ := h8 ▸ Subgroup.card_dvd_of_le hSR
  have hR120 : Nat.card R₀ ≠ 120 := fun h => by
    have htop : R₀ = ⊤ := Subgroup.eq_top_of_card_eq R₀ (h.trans card_perm_five_ch615.symm)
    subst htop
    have := hR
    exact Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup (Perm (Fin 5))) ≃* _).toMonoidHom)
      (MulEquiv.surjective _))
  have hR8 : Nat.card R₀ ≠ 8 := fun h =>
    hRS (Subgroup.eq_of_le_of_card_ge hSR (by omega)).symm
  have hnA : ¬ alternatingGroup (Fin 5) ≤ R₀ := fun hA => by
    obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hA
    rw [card_alternating_five_ch615] at ha
    have h60 : 60 * a ≤ 120 := by
      rw [← ha]
      exact hle
    have ha2 : a ≤ 2 := by omega
    have hpos : 0 < Nat.card R₀ := Nat.card_pos
    interval_cases a
    · omega
    · omega
    · exact hR120 (by rw [ha])
  rw [hk] at hm hle hR120 hR8
  have hk15 : k ≤ 15 := by omega
  interval_cases k <;> try omega
  exfalso
  have hidx : R₀.index = 3 := by
    have h := R₀.card_mul_index
    rw [card_perm_five_ch615, hk] at h
    omega
  rcases eq_bot_or_le_of_normal_perm_five_ch615 (Subgroup.normalCore_normal R₀) with hb | hA
  · have hinj : Function.Injective (MulAction.toPermHom (Perm (Fin 5)) (Perm (Fin 5) ⧸ R₀)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hb]
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm (α := Perm (Fin 5) ⧸ R₀), ← Subgroup.index, hidx,
      card_perm_five_ch615] at this
    norm_num [Nat.factorial] at this
  · exact hnA (hA.trans (Subgroup.normalCore_le R₀))

theorem fix_four_of_overgroup_d8_ch615 {R : Subgroup (Perm (Fin 5))} (hSR : d8Sub_ch615 ≤ R)
    (h24 : Nat.card R = 24) : ∀ r ∈ R, r 4 = 4 := by
  intro r hr
  by_contra h4
  have htrans : ∀ b : Fin 5, ∃ x ∈ R, x 4 = b := by
    intro b
    by_cases hb : b = 4
    · exact ⟨1, R.one_mem, by rw [hb]; rfl⟩
    · obtain ⟨i, hi⟩ := d8_trans_ch615 (r 4) b h4 hb
      exact ⟨d8_ch615 i * r, R.mul_mem (hSR ⟨i, rfl⟩) hr, by rw [Equiv.Perm.mul_apply, hi]⟩
  have horb : MulAction.orbit ↥R (4 : Fin 5) = Set.univ := by
    refine Set.eq_univ_of_forall fun b => ?_
    obtain ⟨x, hx, hxb⟩ := htrans b
    exact ⟨⟨x, hx⟩, hxb⟩
  have hidx := MulAction.index_stabilizer ↥R (4 : Fin 5)
  rw [horb, Set.ncard_univ, Nat.card_fin] at hidx
  have hdvd := Subgroup.index_dvd_card (MulAction.stabilizer ↥R (4 : Fin 5))
  rw [hidx, h24] at hdvd
  norm_num at hdvd

theorem eq_of_overgroups_d8_ch615 {R₁ R₂ : Subgroup (Perm (Fin 5))} (h1 : d8Sub_ch615 ≤ R₁)
    (h1' : R₁ ≠ d8Sub_ch615) (h1s : Group.IsSolvable ↥R₁) (h2 : d8Sub_ch615 ≤ R₂)
    (h2' : R₂ ≠ d8Sub_ch615) (h2s : Group.IsSolvable ↥R₂) : R₁ = R₂ := by
  have hc1 := card_overgroup_perm_five_ch615 isSylowTwoOf_d8Sub_ch615 h1 h1' h1s
  have hc2 := card_overgroup_perm_five_ch615 isSylowTwoOf_d8Sub_ch615 h2 h2' h2s
  set P := MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5) with hP
  have hle : ∀ R : Subgroup (Perm (Fin 5)), (∀ r ∈ R, r 4 = 4) → R ≤ P := fun R hR r hr =>
    MulAction.mem_stabilizer_iff.mpr (hR r hr)
  have hJP : R₁ ⊔ R₂ ≤ P := sup_le (hle _ (fix_four_of_overgroup_d8_ch615 h1 hc1))
    (hle _ (fix_four_of_overgroup_d8_ch615 h2 hc2))
  have hPtop : P ≠ ⊤ := fun h => by
    have : swap (0 : Fin 5) 4 ∈ P := h ▸ Subgroup.mem_top _
    have h' := MulAction.mem_stabilizer_iff.mp this
    exact absurd h' (by decide)
  have hdvd : Nat.card ↥(R₁ ⊔ R₂) ∣ 120 :=
    card_perm_five_ch615 ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj⟩ : 24 ∣ Nat.card ↥(R₁ ⊔ R₂) := hc1 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hJ24 : Nat.card ↥(R₁ ⊔ R₂) = 24 := by
    obtain ⟨m, hm⟩ := hdvd
    rw [hj] at hm
    have hj5 : j ≤ 5 := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0] at hm; omega
      · nlinarith
    interval_cases j <;> try omega
    · exfalso
      apply hPtop
      have htop : R₁ ⊔ R₂ = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [hj, card_perm_five_ch615])
      exact top_le_iff.mp (htop ▸ hJP)
  have e1 : R₁ = R₁ ⊔ R₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hJ24, hc1])
  have e2 : R₂ = R₁ ⊔ R₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hJ24, hc2])
  rw [e1, ← e2]

theorem unique_overgroup_perm_five_ch615 : ∀ S₀ : Subgroup (Perm (Fin 5)), IsSylowTwoOf S₀ ⊤ →
    ∀ R₁ R₂ : Subgroup (Perm (Fin 5)), S₀ ≤ R₁ → R₁ ≠ S₀ → Group.IsSolvable ↥R₁ → S₀ ≤ R₂ →
      R₂ ≠ S₀ → Group.IsSolvable ↥R₂ → R₁ = R₂ := by
  intro S₀ hS₀ R₁ R₂ h1 h1' h1s h2 h2' h2s
  obtain ⟨x, -, rfl⟩ := isSylowTwoOf_d8Sub_ch615.exists_conj hS₀
  set f := MulAut.conj x⁻¹ with hf
  have hback : ∀ A : Subgroup (Perm (Fin 5)), (A.map (MulAut.conj x).toMonoidHom).map
      f.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext σ a
    simp [hf, MulAut.conj_apply, mul_assoc]
  have key : ∀ R : Subgroup (Perm (Fin 5)),
      d8Sub_ch615.map (MulAut.conj x).toMonoidHom ≤ R →
      R ≠ d8Sub_ch615.map (MulAut.conj x).toMonoidHom → Group.IsSolvable ↥R →
      d8Sub_ch615 ≤ R.map f.toMonoidHom ∧ R.map f.toMonoidHom ≠ d8Sub_ch615 ∧
        Group.IsSolvable ↥(R.map f.toMonoidHom) := by
    intro R hR hR' hRs
    refine ⟨?_, fun h => hR' ?_, ?_⟩
    · rw [← hback d8Sub_ch615]
      exact Subgroup.map_mono hR
    · have := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) h
      rw [Subgroup.map_map] at this
      rw [← this]
      convert (Subgroup.map_id R).symm
      ext σ a
      simp [hf, MulAut.conj_apply, mul_assoc]
    · have := hRs
      exact Group.isSolvable_of_surjective (f.toMonoidHom.subgroupMap_surjective R)
  obtain ⟨k1, k1', k1s⟩ := key R₁ h1 h1' h1s
  obtain ⟨k2, k2', k2s⟩ := key R₂ h2 h2' h2s
  exact Subgroup.map_injective f.injective (eq_of_overgroups_d8_ch615 k1 k1' k1s k2 k2' k2s)

end S5

section TransportU

variable {Γ : Type*} [Group Γ] {F : Subgroup Γ} {X : Type*} [Group X]

theorem unique_of_mulEquiv_ch615 (e : ↥F ≃* X)
    (hX : ∀ S₀ : Subgroup X, IsSylowTwoOf S₀ ⊤ → ∀ R₁ R₂ : Subgroup X, S₀ ≤ R₁ → R₁ ≠ S₀ →
      Group.IsSolvable ↥R₁ → S₀ ≤ R₂ → R₂ ≠ S₀ → Group.IsSolvable ↥R₂ → R₁ = R₂)
    {S : Subgroup Γ} (hS : IsSylowTwoOf S F) :
    ∀ R₁ R₂ : Subgroup Γ, S ≤ R₁ → R₁ ≤ F → R₁ ≠ S → Group.IsSolvable ↥R₁ → S ≤ R₂ → R₂ ≤ F →
      R₂ ≠ S → Group.IsSolvable ↥R₂ → R₁ = R₂ := by
  intro R₁ R₂ h1 h1F h1' h1s h2 h2F h2' h2s
  have hSF := hS.le
  have hinj : ∀ A B : Subgroup Γ, A ≤ F → B ≤ F →
      (A.subgroupOf F).map e.toMonoidHom = (B.subgroupOf F).map e.toMonoidHom → A = B := by
    intro A B hA hB h
    have h1 := Subgroup.map_injective e.injective h
    rwa [Subgroup.subgroupOf_inj, inf_eq_left.mpr hA, inf_eq_left.mpr hB] at h1
  have hne : ∀ R : Subgroup Γ, R ≤ F → R ≠ S →
      (R.subgroupOf F).map e.toMonoidHom ≠ (S.subgroupOf F).map e.toMonoidHom :=
    fun R hR hRS h => hRS (hinj _ _ hR hSF h)
  exact hinj _ _ h1F h2F (hX _ (isSylowTwoOf_map_ch615 e hS) _ _
    (Subgroup.map_mono fun x hx => h1 hx) (hne _ h1F h1') (isSolvable_map_ch615 e h1F h1s)
    (Subgroup.map_mono fun x hx => h2 hx) (hne _ h2F h2') (isSolvable_map_ch615 e h2F h2s))

end TransportU

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

omit [Finite G] in
theorem exists_fix_of_mem_omega_ch615 (hU : IsElemAbelian 2 (UX615 T L H)) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) :
    ∃ w : IntMod (UX615 T L H) hU, w.val = z ∧ ∀ t ∈ autI hU T, t w = w := by
  have hzU : z ∈ UX615 T L H := le_conjClosure _ _ hz
  obtain ⟨w, hw⟩ := IntMod.exists_eq_mk (hV := hU) ⟨z, hzU⟩
  refine ⟨w, hw, fun t ht => ?_⟩
  obtain ⟨⟨s, hsN⟩, hsT, rfl⟩ := (mem_autI hU).mp ht
  apply IntMod.val_injective
  rw [convI_apply_val, hw]
  have h1 := Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hz).2.1 s hsT
  show s * z * s⁻¹ = z
  rw [h1, mul_inv_cancel_right]

theorem not_fix_oTwoUpper_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H)) :
    ¬ ∀ w : IntMod (UX615 T L H) hU, (∀ t ∈ autI hU T, t w = w) →
      ∀ k ∈ autI hU (oTwoUpper H), k w = w := by
  intro hK
  apply c.notZ
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hsup : T ⊔ twoResidual H = H := sup_twoResidual_eq c.toCx615.isSylowTwoOf
  rw [twoResidual_eq_oTwoUpper'] at hsup
  rw [← hsup]
  refine sup_le (fun t ht => ?_) (fun k hk => ?_)
  · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hz).2.1 t ht).symm
  · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    obtain ⟨w, hwz, hwT⟩ := exists_fix_of_mem_omega_ch615 hU hz
    have hkN := hXN (Subgroup.mem_sup_right (oTwoUpper_le H hk))
    have h1 := congrArg IntMod.val (hK w hwT _ (convI_mem_autI hU hk hkN))
    rw [convI_apply_val, hwz] at h1
    calc z * k = k * z * k⁻¹ * k := by rw [h1]
      _ = k * z := by group

theorem not_fix_hall_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    {δ : MulAut (IntMod (UX615 T L H) hU)} (hδ : δ ∈ autI hU D) (hδ1 : δ ≠ 1) :
    ¬ ∀ w : IntMod (UX615 T L H) hU, (∀ t ∈ autI hU T, t w = w) → δ w = w := by
  intro hfix
  obtain ⟨⟨d, hdN⟩, hdD, rfl⟩ := (mem_autI hU).mp hδ
  have hd1 : d ≠ 1 := fun h => hδ1 (by
    have : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (UX615 T L H : Set G))) = 1 := Subtype.ext h
    rw [this, map_one])
  have hdodd : Odd (orderOf d) := Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hdD)
  apply c.ZL
  intro z hz
  refine c.CZd d (hD.1 hdD) hdodd hd1 (Subgroup.mem_inf.mpr ⟨hz.1, ?_⟩)
  obtain ⟨w, hwz, hwT⟩ := exists_fix_of_mem_omega_ch615 hU hz.1
  have h1 := congrArg IntMod.val (hfix w hwT)
  rw [convI_apply_val, hwz] at h1
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  calc d * z = d * z * d⁻¹ * d := by group
    _ = z * d := by rw [h1]

theorem isSylowTwoOf_inf_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hFX : F ≤ autI hU (borelL T L ⊔ H))
    (hXF : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (F : Set (MulAut _))) :
    IsSylowTwoOf (autI hU T ⊓ F) F := by
  have hn := (Subgroup.normal_subgroupOf_iff_le_normalizer hFX).mpr hXF
  exact RankOneRecog.isSylowTwoOf_inf_of_subnormal (c.isSylowTwoOf_autI_ch615 hU) hFX
    hn.isSubnormal

theorem autI_le_normalizer_oTwoUpper_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) :
    autI hU T ≤ Subgroup.normalizer (autI hU (oTwoUpper H) : Set (MulAut _)) := by
  have hTK' : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    c.hH.1.1.trans (le_normalizer_oTwoUpper H)
  intro y hy
  refine Subgroup.mem_normalizer_iff.mpr fun a =>
    ⟨fun ha => C124.autI_conj_mem hU hTK' y hy a ha, fun ha => ?_⟩
  have := C124.autI_conj_mem hU hTK' y⁻¹ ((autI hU T).inv_mem hy) _ ha
  simpa [mul_assoc] using this

theorem overgroup_oTwoUpper_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hKF : autI hU (oTwoUpper H) ≤ F)
    (hS : IsPGroup 2 ↥(autI hU T ⊓ F)) :
    autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F) ≤ F ∧
      autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F) ≠ autI hU T ⊓ F ∧
      Group.IsSolvable ↥(autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F)) := by
  refine ⟨sup_le hKF inf_le_right, fun h => ?_, ?_⟩
  · apply c.autI_oTwoUpper_ne_bot_ch615 hU
    rw [eq_bot_iff]
    refine autI_oTwoUpper_le_of_odd_ch615 hU fun y hy hyo => ?_
    have hyS : y ∈ autI hU T ⊓ F := h ▸ Subgroup.mem_sup_left hy
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_mem_l32_ch615 hS hyS hyo)
  · have hKs := c.isSolvable_autI_oTwoUpper_ch615 hU
    have hT2s : Group.IsSolvable ↥(autI hU T ⊓ F) := by
      have := hS.isNilpotent
      infer_instance
    exact A3.isSolvable_sup_of_le_normalizer
      (inf_le_left.trans (c.autI_le_normalizer_oTwoUpper_ch615 hU))

theorem exists_overgroups_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hFX : F ≤ autI hU (borelL T L ⊔ H))
    (hXF : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hdl : DLemmaFacts_ch615 F) (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hKF : autI hU (oTwoUpper H) ≤ F) :
    ∃ d ∈ autI hU D, d ≠ 1 ∧ d ∈ autI hU (borelL T L ⊔ T) ⊓ F ∧
      autI hU T ⊓ F ≤ autI hU (borelL T L ⊔ T) ⊓ F ∧
      autI hU (borelL T L ⊔ T) ⊓ F ≠ autI hU T ⊓ F ∧
      Group.IsSolvable ↥(autI hU (borelL T L ⊔ T) ⊓ F) ∧
      autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F) ≤ F ∧
      autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F) ≠ autI hU T ⊓ F ∧
      Group.IsSolvable ↥(autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F)) ∧
      autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F) ≠ autI hU (borelL T L ⊔ T) ⊓ F := by
  classical
  have hS := c.isSylowTwoOf_inf_ch615 hU hFX hXF
  obtain ⟨-, hout, hNS, hself⟩ := hdl
  have hDY : autI hU D ≤ autI hU (borelL T L ⊔ T) := autI_mono hU (hD.1.trans le_sup_left)
  have hTY : autI hU T ≤ autI hU (borelL T L ⊔ T) := autI_mono hU le_sup_right
  have hYX : autI hU (borelL T L ⊔ T) ≤ autI hU (borelL T L ⊔ H) :=
    autI_mono hU (sup_le le_sup_left (c.hH.1.1.trans le_sup_right))
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  have hDc : ¬ autI hU D ≤ Subgroup.centralizer (F : Set (MulAut _)) := fun hDc => by
    apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    rw [← Subgroup.mem_centralizer_iff.mp (hDc hy) k (hKF hk), mul_inv_cancel_right]
    exact hk
  obtain ⟨d, hdD, hdF, hd1, -⟩ := exists_mem_of_not_le_centralizer_ch615 hout hZ
    hS.isPGroup hS.le (hNS _ hS) (hself _ hS) (inf_le_left.trans hTY) hDY
    (c.isSolvable_autI_ch615 hU) (fun x hx => hXF (hYX (hDY hx))) hDsodd
    (fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho)
    (fun p hp hp2 x hx y hy hxp hyp hxy hx1 =>
      c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hx hy hxp hyp hxy hx1) hDc
  have hYs := c.isSolvable_autI_ch615 hU
  have hPDs : Group.IsSolvable ↥(autI hU (borelL T L ⊔ T) ⊓ F) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (inf_le_left : autI hU (borelL T L ⊔ T) ⊓ F ≤ _))
  have hdPD : d ∈ autI hU (borelL T L ⊔ T) ⊓ F := ⟨hDY hdD, hdF⟩
  have hdS : d ∉ autI hU T ⊓ F := fun h =>
    hd1 (eq_one_of_odd_of_mem_l32_ch615 hS.isPGroup h (hDsodd d hdD))
  have hTK := c.autI_le_normalizer_oTwoUpper_ch615 hU
  obtain ⟨hPKF, hPKS, hPKs⟩ := c.overgroup_oTwoUpper_ch615 hU hKF hS.isPGroup
  refine ⟨d, hdD, hd1, hdPD, le_inf (inf_le_left.trans hTY) inf_le_right,
    fun h => hdS (h ▸ hdPD), hPDs, hPKF, hPKS, hPKs, fun heq => ?_⟩
  apply c.not_hall_normalizes_ch615 hU hD hN
  intro δ hδ k hk
  have hδY := hDY hδ
  have hδF := hXF (hYX hδY)
  have key : autI hU (oTwoUpper H) ≤
      (autI hU (oTwoUpper H)).comap (MulAut.conj δ).toMonoidHom := by
    refine autI_oTwoUpper_le_of_odd_ch615 hU fun y hy hyo => ?_
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hyPD : y ∈ autI hU (borelL T L ⊔ T) ⊓ F := heq ▸ Subgroup.mem_sup_left hy
    have h1 : δ * y * δ⁻¹ ∈ autI hU (borelL T L ⊔ T) ⊓ F :=
      ⟨(autI hU _).mul_mem ((autI hU _).mul_mem hδY hyPD.1) ((autI hU _).inv_mem hδY),
        (Subgroup.mem_normalizer_iff.mp hδF y).mp hyPD.2⟩
    rw [← heq] at h1
    have hodd : Odd (orderOf (δ * y * δ⁻¹)) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hyo
    exact mem_of_odd_of_mem_sup_ch615 hS.isPGroup (inf_le_left.trans hTK) h1 hodd
  have := key hk
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem false_of_unique_overgroup_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hFX : F ≤ autI hU (borelL T L ⊔ H))
    (hXF : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hdl : DLemmaFacts_ch615 F) (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hKF : autI hU (oTwoUpper H) ≤ F)
    (huniq : ∀ R₁ R₂ : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      autI hU T ⊓ F ≤ R₁ → R₁ ≤ F → R₁ ≠ autI hU T ⊓ F → Group.IsSolvable ↥R₁ →
      autI hU T ⊓ F ≤ R₂ → R₂ ≤ F → R₂ ≠ autI hU T ⊓ F → Group.IsSolvable ↥R₂ → R₁ = R₂) :
    False := by
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  obtain ⟨-, -, -, -, hSD, hDS, hDs, hKF', hKS, hKs, hne⟩ :=
    c.exists_overgroups_ch615 hU hN hD hFX hXF hdl hZ hKF
  exact hne (huniq _ _ le_sup_right hKF' hKS hKs hSD inf_le_right hDS hDs)

theorem false_of_two_overgroups_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hFX : F ≤ autI hU (borelL T L ⊔ H))
    (hXF : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hdl : DLemmaFacts_ch615 F) (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hKF : autI hU (oTwoUpper H) ≤ F)
    (hpar : ∀ R₁ R₂ : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      autI hU T ⊓ F ≤ R₁ → R₁ ≤ F → R₁ ≠ autI hU T ⊓ F → Group.IsSolvable ↥R₁ →
      autI hU T ⊓ F ≤ R₂ → R₂ ≤ F → R₂ ≠ autI hU T ⊓ F → Group.IsSolvable ↥R₂ → R₁ ≠ R₂ →
      (∀ w, (∀ s ∈ autI hU T ⊓ F, s w = w) → ∀ x ∈ R₁, x w = w) ∨
      (∀ w, (∀ s ∈ autI hU T ⊓ F, s w = w) → ∀ x ∈ R₂, x w = w)) : False := by
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  obtain ⟨d, hdD, hd1, hdPD, hSD, hDS, hDs, hKF', hKS, hKs, hne⟩ :=
    c.exists_overgroups_ch615 hU hN hD hFX hXF hdl hZ hKF
  rcases hpar _ _ le_sup_right hKF' hKS hKs hSD inf_le_right hDS hDs hne with h | h
  · exact c.not_fix_oTwoUpper_ch615 hU fun w hw k hk =>
      h w (fun s hs => hw s hs.1) k (Subgroup.mem_sup_left hk)
  · exact c.not_fix_hall_ch615 hU hD hdD hd1 fun w hw => h w (fun s hs => hw s hs.1) d hdPD

end Cx615C

theorem genFitting_eq_or_iso_ch615 {W : Type} [CommGroup W] [Finite W] {J : Subgroup (MulAut W)}
    (h : B56Case1 J) :
    quasithinGenFitting J = J ∨ ((∀ T₀, IsSylowTwoOf T₀ J → J = quasithinGenFitting J ⊔ T₀) ∧
      ((∃ k, 5 ≤ k ∧ k ≤ 8 ∧ Nonempty (Equiv.Perm (Fin k) ≃* ↥J)) ∨
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
          Nonempty (↥(quasithinG2 K) ≃* ↥J))) := by
  obtain ⟨-, ⟨⟨-, hcase⟩, -⟩, -⟩ := h
  rcases hcase with h1 | h2 | ⟨k, h3⟩ | h4
  · obtain ⟨T, hT⟩ := exists_isSylowTwoOf J
    rcases h1.2.2 T hT with heq | ⟨-, hrest⟩
    · exact Or.inl heq.symm
    · refine Or.inr ⟨fun T₀ hT₀ => ?_, ?_⟩
      · rcases h1.2.2 T₀ hT₀ with heq' | ⟨hJ, -⟩
        · exact le_antisymm (heq'.le.trans le_sup_left) (sup_le (quasithinGenFitting_le J) hT₀.le)
        · exact hJ
      · rcases hrest with ⟨k, hk5, hk8, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
        · have hinj := FFC.injective_of_faithful_sec (FFC.symDn_faithful hk5) hπ
          exact Or.inl ⟨k, hk5, hk8, ⟨MulEquiv.ofBijective π ⟨hinj, hπ.1⟩⟩⟩
        · have hK2 : Nat.card K = 2 := by simpa using hK
          have : CharP K 2 := charTwo_facts_ch615 (n := 1) (by rw [hK2, pow_one])
          have hinj := FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ
          exact Or.inr ⟨K, inferInstance, inferInstance, hK2,
            ⟨MulEquiv.ofBijective π ⟨hinj, hπ.1⟩⟩⟩
  · exact Or.inl h2.1.symm
  · exact Or.inl h3.1.symm
  · exact Or.inl h4.1.symm

theorem genFitting_eq_or_card_ch615 {W : Type} [CommGroup W] [Finite W] {J : Subgroup (MulAut W)}
    (h : B56Case1 J) :
    quasithinGenFitting J = J ∨ ∃ a : ℕ, Nat.card J = Nat.card (quasithinGenFitting J) * 2 ^ a ∧
      ((∃ k, 5 ≤ k ∧ k ≤ 8 ∧ Nonempty (Equiv.Perm (Fin k) ≃* ↥J) ∧ Nat.card J = k.factorial) ∨
        Nat.card J = 12096) := by
  rcases genFitting_eq_or_iso_ch615 h with hJ | ⟨hJT, hiso⟩
  · exact Or.inl hJ
  · right
    obtain ⟨T₀, hT₀⟩ := exists_isSylowTwoOf J
    obtain ⟨a, ha⟩ := card_eq_mul_two_pow_ch615 (quasithinGenFitting_le J)
      (le_normalizer_quasithinGenFitting J) hT₀.isPGroup (hJT T₀ hT₀)
    refine ⟨a, ha, ?_⟩
    rcases hiso with ⟨k, hk5, hk8, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩
    · refine Or.inl ⟨k, hk5, hk8, ⟨e⟩, ?_⟩
      rw [← Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    · refine Or.inr ?_
      rw [← Nat.card_congr e.toEquiv, card_quasithinG2_1527d (n := 1) (by rw [hK, pow_one]), hK]
      norm_num

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_case1_sl2_eight_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H))))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) : False := by
  set e' := e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  have h4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hK4 := exists_finset_four_ch615 h4
  have hcard : Nat.card (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = 504 := by
    rw [Nat.card_congr e'.toEquiv, card_sl2_field_ch615, hK]
    norm_num
  have hJ : quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) =
      ffJ (autI hU (borelL T L ⊔ H)) := by
    rcases genFitting_eq_or_card_ch615 h1 with hJ | ⟨a, ha, hJc⟩
    · exact hJ
    · exfalso
      rw [hcard] at ha
      rcases hJc with ⟨k, hk5, hk8, -, hk⟩ | h12
      · rw [hk] at ha
        have hkf : k.factorial ≤ 40320 := (Nat.factorial_le hk8).trans (by decide)
        have ha7 : a < 7 := by
          by_contra hh
          have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hh)
          omega
        interval_cases k <;> interval_cases a <;> simp [Nat.factorial] at ha
      · rw [h12] at ha
        have ha7 : a < 7 := by
          by_contra hh
          have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hh)
          omega
        interval_cases a <;> omega
  have hB := borelFacts_of_mulEquiv_ch615 e' (not_isSolvable_sl2_ch615 hK4)
    (borel_of_sylow_ch615 (isSylowTwoOf_unipSub_ch615 hK)
      fun R hUR hR => borel_unipSub_ch615 hK4 hUR hR)
  exact c.false_of_case1_borel_ch615 hU hJ hB.2

theorem false_of_case1_sl2_four_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H)))) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) : False := by
  set e' := e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  have h4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hK4 := exists_finset_four_ch615 h4
  have hcard : Nat.card (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = 60 := by
    rw [Nat.card_congr e'.toEquiv, card_sl2_field_ch615, hK]
    norm_num
  rcases genFitting_eq_or_card_ch615 h1 with hJ | ⟨a, ha, hJc⟩
  · have hB := borelFacts_of_mulEquiv_ch615 e' (not_isSolvable_sl2_ch615 hK4)
      (borel_of_sylow_ch615 (isSylowTwoOf_unipSub_ch615 hK)
        fun R hUR hR => borel_unipSub_ch615 hK4 hUR hR)
    exact c.false_of_case1_borel_ch615 hU hJ hB.2
  rw [hcard] at ha
  rcases hJc with ⟨k, hk5, hk8, ⟨e₅⟩, hk⟩ | h12
  · rw [hk] at ha
    have hkf : k.factorial ≤ 40320 := (Nat.factorial_le hk8).trans (by decide)
    have ha10 : a < 10 := by
      by_contra hh
      have : 2 ^ 10 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hh)
      omega
    have hk5' : k = 5 := by
      interval_cases k
      · rfl
      all_goals exfalso; interval_cases a <;> simp [Nat.factorial] at ha
    subst hk5'
    have hdl : DLemmaFacts_ch615 (ffJ (autI hU (borelL T L ⊔ H))) :=
      dLemmaFacts_of_mulEquiv_ch615 e₅.symm Equiv.Perm.not_isSolvable_fin_5
        (fun α _ => exists_eq_conj_perm_five_ch615 α)
        (selfNormalizing_of_sylow_ch615 isSylowTwoOf_d8Sub_ch615 mem_d8Sub_of_conj_mem_ch615)
        (fun _ hS₀ _ hSR hRS hR g hg =>
          mem_of_conj_mem_overgroup_perm_five_ch615 hS₀ hSR hRS hR g hg)
    have hFX : ffJ (autI hU (borelL T L ⊔ H)) ≤ autI hU (borelL T L ⊔ H) := B6.ffJ_le _
    have hXF : autI hU (borelL T L ⊔ H) ≤
        Subgroup.normalizer (ffJ (autI hU (borelL T L ⊔ H)) : Set (MulAut _)) :=
      fun x hx => B6.le_normalizer_ffJ _ hx
    exact c.false_of_unique_overgroup_ch615 hU hN hFX hXF hdl
      (center_of_mulEquiv_ch615 e₅.symm eq_one_of_central_perm_five_ch615) (c.le_ffJ_ch615 hU).2
      (unique_of_mulEquiv_ch615 e₅.symm unique_overgroup_perm_five_ch615
        (c.isSylowTwoOf_inf_ch615 hU hFX hXF))
  · rw [h12] at ha
    have ha10 : a < 10 := by
      by_contra hh
      have : 2 ^ 10 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hh)
      omega
    interval_cases a <;> omega

end Cx615C

end CFSG.Quasithin.H13
