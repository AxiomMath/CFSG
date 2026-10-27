module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Normal
import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJTypes
import CFSG.RankThree.PartTwo.Sec14.Ronan148VDelta
import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

theorem commute_of_inf_eq_bot {U V : Subgroup Q} (hUV : U ≤ Subgroup.normalizer (V : Set Q))
    (hVU : V ≤ Subgroup.normalizer (U : Set Q)) (hint : U ⊓ V = ⊥) :
    ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := by
  intro u hu v hv
  have h1 : u * v * u⁻¹ * v⁻¹ ∈ V :=
    V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUV hu) v).mp hv) (V.inv_mem hv)
  have h2 : u * v * u⁻¹ * v⁻¹ ∈ U := by
    have h3 : v * u⁻¹ * v⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hVU hv) u⁻¹).mp (U.inv_mem hu)
    have h4 := U.mul_mem hu h3
    simpa [mul_assoc] using h4
  have h5 : u * v * u⁻¹ * v⁻¹ ∈ U ⊓ V := ⟨h2, h1⟩
  rw [hint, Subgroup.mem_bot] at h5
  calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
    _ = v * u := by rw [h5, one_mul]

theorem inf_centralizer_eq_of_a5_factor {Z U V : Subgroup Q} (hUZ : U ≤ Z) (hUV : U ⊔ V = Z)
    (hint : U ⊓ V = ⊥) (hZU : Z ≤ Subgroup.normalizer (U : Set Q))
    (hZV : Z ≤ Subgroup.normalizer (V : Set Q)) (hVZ : V ≤ Z)
    (hVc : ∀ v ∈ V, (∀ w ∈ V, v * w = w * v) → v = 1) :
    Z ⊓ Subgroup.centralizer (V : Set Q) = U := by
  have hcomm := commute_of_inf_eq_bot (hUZ.trans hZV) (hVZ.trans hZU) hint
  set H := Z ⊓ Subgroup.centralizer (V : Set Q) with hH
  have hUH : U ≤ H := le_inf hUZ fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hcomm u hu v hv).symm
  have hHV : H ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine hVc x hx.2 fun w hw => ?_
    exact (Subgroup.mem_centralizer_iff.mp hx.1.2 w hw).symm
  have h1 := Ronan148V.card_sup_mul_card_inf (inf_le_left.trans hZV : H ≤ _)
  rw [hHV, Subgroup.card_bot, mul_one] at h1
  have h2 := Ronan148V.card_sup_mul_card_inf (hUZ.trans hZV)
  rw [hint, Subgroup.card_bot, mul_one, hUV] at h2
  have h3 : Nat.card ↥(H ⊔ V) ≤ Nat.card Z := Subgroup.card_le_of_le (sup_le inf_le_left hVZ)
  have hV0 : 0 < Nat.card V := Nat.card_pos
  have h4 : Nat.card H ≤ Nat.card U := by
    have : Nat.card H * Nat.card V ≤ Nat.card U * Nat.card V := by rw [← h1, ← h2]; exact h3
    exact Nat.le_of_mul_le_mul_right this hV0
  exact (Subgroup.eq_of_le_of_card_ge hUH h4).symm

theorem mem_normalizer_of_a5_factor {Z U V : Subgroup Q} (hUZ : U ≤ Z) (hVZ : V ≤ Z)
    (hUV : U ⊔ V = Z) (hint : U ⊓ V = ⊥) (hZU : Z ≤ Subgroup.normalizer (U : Set Q))
    (hZV : Z ≤ Subgroup.normalizer (V : Set Q))
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (ψ : ↥V ≃* alternatingGroup (Fin 5)) {a : Q} (ha : a ∈ Subgroup.normalizer (Z : Set Q)) :
    a ∈ Subgroup.normalizer (V : Set Q) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  set V' := V.map (MulAut.conj a).toMonoidHom with hV'
  have hV'Z : V' ≤ Z := by
    rintro _ ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ha v).mp (hVZ hv)
  have hZV' : Z ≤ Subgroup.normalizer (V' : Set Q) := by
    intro z hz
    refine Item148HJ.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ := hx
    have hz' : a⁻¹ * z * a ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) z).mp hz
      simpa using this
    have hv' : (a⁻¹ * z * a) * v * (a⁻¹ * z * a)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hZV hz') v).mp hv
    refine ⟨_, hv', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcard : Nat.card V' = Nat.card V := Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hV60 : Nat.card V = 60 := by rw [Nat.card_congr ψ.toEquiv, h60]
  have eV' : ↥V' ≃* alternatingGroup (Fin 5) :=
    (V.equivMapOfInjective _ (MulAut.conj a).injective).symm.trans ψ
  have hV's : IsSimpleGroup ↥V' := MulEquiv.isSimpleGroup eV'
  have hnorm : ((V ⊓ V').subgroupOf V').Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hZV (hV'Z g.2)) _).mp hx.1,
      V'.mul_mem (V'.mul_mem g.2 hx.2) (V'.inv_mem g.2)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((V ⊓ V').subgroupOf V') with h0 | h0
  ·
    exfalso
    have hdisj : V ⊓ V' = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at h0
      have h1 := disjoint_iff.mp h0
      rwa [inf_assoc, inf_idem] at h1
    have hcomm := commute_of_inf_eq_bot (hV'Z.trans hZV) (hVZ.trans hZV')
      (by rw [inf_comm]; exact hdisj)
    have hV'U : V' ≤ U := by
      have hVc : ∀ v ∈ V, (∀ w ∈ V, v * w = w * v) → v = 1 := by
        intro v hv hvc
        have hZ : (⟨v, hv⟩ : ↥V) ∈ Subgroup.center ↥V := by
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (hvc g g.2).symm
        have hcen : Subgroup.center ↥V = ⊥ := by
          have hmap := Subgroup.map_center_eq ψ
          rw [Ronan148J.center_alternatingGroup_five_eq_bot] at hmap
          exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).mp hmap
        rw [hcen, Subgroup.mem_bot] at hZ
        exact congrArg Subtype.val hZ
      rw [← inf_centralizer_eq_of_a5_factor hUZ hUV hint hZU hZV hVZ hVc]
      exact le_inf hV'Z fun x hx =>
        Subgroup.mem_centralizer_iff.mpr fun v hv => (hcomm x hx v hv).symm
    have hN : (V'.subgroupOf U).Normal := by
      constructor
      intro x hx g
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hZV' (hUZ g.2)) _).mp hx
    have hNc : Nat.card (V'.subgroupOf U) = 60 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV'U).toEquiv, hcard, hV60]
    rcases card_normal_of_isTripleCover hU (V'.subgroupOf U) with h | h
    · rw [hNc] at h
      norm_num at h
    · rw [hNc, card_alternatingGroup_six] at h
      norm_num at h
  ·
    have hle : V' ≤ V := by
      rw [Subgroup.subgroupOf_eq_top] at h0
      exact h0.trans inf_le_left
    have heq : V' = V := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem exists_subgroups_of_isA6CoverTimesA5 {Z : Subgroup Q} (h : IsA6CoverTimesA5 ↥Z) :
    ∃ U V : Subgroup Q, U ≤ Z ∧ V ≤ Z ∧ U ⊔ V = Z ∧ U ⊓ V = ⊥ ∧
      Z ≤ Subgroup.normalizer (U : Set Q) ∧ Z ≤ Subgroup.normalizer (V : Set Q) ∧
      Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)) ∧
      Nonempty (↥V ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨U', V', hU'n, hV'n, hint', hsup', hU', ⟨ψ⟩⟩ := h
  have hnorm : ∀ {K : Subgroup ↥Z}, K.Normal →
      Z ≤ Subgroup.normalizer ((K.map Z.subtype : Subgroup Q) : Set Q) := by
    intro K hK z hz
    refine Item148HJ.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨⟨z, hz⟩ * k * ⟨z, hz⟩⁻¹, hK.conj_mem k hk ⟨z, hz⟩, ?_⟩
    simp
  refine ⟨U'.map Z.subtype, V'.map Z.subtype, Subgroup.map_subtype_le U',
    Subgroup.map_subtype_le V', ?_, ?_, hnorm hU'n, hnorm hV'n,
    KFacts.KS14.isTripleCover_congr (U'.equivMapOfInjective _ Z.subtype_injective) hU',
    ⟨(V'.equivMapOfInjective _ Z.subtype_injective).symm.trans ψ⟩⟩
  · rw [← Subgroup.map_sup, hsup', Subgroup.map_top, Subgroup.range_subtype]
  · rw [← Subgroup.map_inf_eq _ _ _ Z.subtype_injective, hint', Subgroup.map_bot]

theorem false_of_isA6CoverTimesA5_of_le {Aq Bq Z : Subgroup Q} {j : Q}
    (hAab : ∀ x ∈ Aq, ∀ y ∈ Aq, x * y = y * x) (hAp : IsPGroup 3 Aq)
    (hF3 : ∀ w : Q, w ∈ Subgroup.centralizer (Aq : Set Q) → w ^ 3 = 1 → w ∈ Aq)
    (hBA : Bq ≤ Aq) (hB9 : Nat.card Bq = 9) (hAeq : Bq ⊔ Subgroup.zpowers j = Aq)
    (hAZB : Aq ⊓ Z ≤ Bq) (hjZ : ∀ z ∈ Z, j * z = z * j)
    (hAN : Aq ≤ Subgroup.normalizer (Z : Set Q)) (h : IsA6CoverTimesA5 ↥Z) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U, V, hUZ, hVZ, hUV, hint, hZU, hZV, hU, ⟨ψ⟩⟩ := exists_subgroups_of_isA6CoverTimesA5 h
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have hcomm := commute_of_inf_eq_bot (hUZ.trans hZV) (hVZ.trans hZU) hint
  have hAV : Aq ≤ Subgroup.normalizer (V : Set Q) := fun a ha =>
    mem_normalizer_of_a5_factor hUZ hVZ hUV hint hZU hZV hU ψ (hAN ha)
  have h3V : 3 ∣ Nat.card V := by rw [Nat.card_congr ψ.toEquiv, h60]; norm_num
  obtain ⟨v₀, hv₀V, hv₀1, hv₀3, hv₀C⟩ := Ronan148J.exists_pow_eq_one_mem_centralizer hAp hAV h3V
  have hv₀A : v₀ ∈ Aq := hF3 v₀ hv₀C hv₀3
  have hv₀B : v₀ ∈ Bq := hAZB ⟨hv₀A, hVZ hv₀V⟩
  set Zc : Subgroup Q := (Subgroup.center ↥Z).map Z.subtype with hZc
  have hAZc : Aq ≤ Subgroup.normalizer (Zc : Set Q) := Ronan148J.le_normalizer_map_center hAN
  have hUc : (Subgroup.center ↥U).map U.subtype ≤ Zc := by
    rintro _ ⟨z, hz, rfl⟩
    have hzZ : (z : Q) ∈ Z := hUZ z.2
    refine ⟨⟨z, hzZ⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgZ : (g : Q) ∈ U ⊔ V := by rw [hUV]; exact g.2
    have hle : U ⊔ V ≤ Subgroup.centralizer ({(z : Q)} : Set Q) := by
      refine sup_le (fun u hu => ?_) (fun v hv => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨u, hu⟩)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm z z.2 v hv).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hgZ)
  have h3Zc : 3 ∣ Nat.card Zc := by
    have h1 := Subgroup.card_dvd_of_le hUc
    rw [Subgroup.card_map_of_injective U.subtype_injective, hU.1] at h1
    exact h1
  obtain ⟨k, hkZc, hk1, hk3, hkC⟩ := Ronan148J.exists_pow_eq_one_mem_centralizer hAp hAZc h3Zc
  obtain ⟨k', hk', rfl⟩ := hkZc
  have hkZ : (k' : Q) ∈ Z := k'.2
  have hkcen : ∀ z ∈ Z, (k' : Q) * z = z * k' := fun z hz =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp hk') ⟨z, hz⟩).symm
  have hkA : (k' : Q) ∈ Aq := hF3 _ hkC hk3
  have hkB : (k' : Q) ∈ Bq := hAZB ⟨hkA, hkZ⟩
  have hVc : ∀ v ∈ V, (∀ w ∈ V, v * w = w * v) → v = 1 := by
    intro v hv hvc
    have hZ : (⟨v, hv⟩ : ↥V) ∈ Subgroup.center ↥V := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hvc g g.2).symm
    have hcen : Subgroup.center ↥V = ⊥ := by
      have hmap := Subgroup.map_center_eq ψ
      rw [Ronan148J.center_alternatingGroup_five_eq_bot] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).mp hmap
    rw [hcen, Subgroup.mem_bot] at hZ
    exact congrArg Subtype.val hZ
  have hkU : (k' : Q) ∈ U := by
    rw [← inf_centralizer_eq_of_a5_factor hUZ hUV hint hZU hZV hVZ hVc]
    exact ⟨hkZ, Subgroup.mem_centralizer_iff.mpr fun v hv => (hkcen v (hVZ hv)).symm⟩
  have hv₀U : v₀ ∉ U := fun h => hv₀1 (by
    have : v₀ ∈ U ⊓ V := ⟨h, hv₀V⟩
    rwa [hint, Subgroup.mem_bot] at this)
  have hv₀k : v₀ ∉ Subgroup.zpowers (k' : Q) := fun h =>
    hv₀U ((Subgroup.zpowers_le.mpr hkU) h)
  have hkv : (k' : Q) * v₀ = v₀ * k' := hAab _ hkA _ hv₀A
  have hB : Subgroup.zpowers (k' : Q) ⊔ Subgroup.zpowers v₀ = Bq := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hkB)
      (Subgroup.zpowers_le.mpr hv₀B)) ?_
    rw [hB9, Ronan148J.card_zpowers_sup_zpowers_eq_nine hkv hk3 hk1 hv₀3 hv₀k]
  have hAeq' : Subgroup.zpowers (k' : Q) ⊔ (Subgroup.zpowers v₀ ⊔ Subgroup.zpowers j) = Aq := by
    rw [← sup_assoc, hB, hAeq]
  have hEU : Subgroup.zpowers v₀ ⊔ Subgroup.zpowers j ≤
      Subgroup.centralizer (U : Set Q) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun u hu => hcomm u hu v₀ hv₀V
    · exact Subgroup.mem_centralizer_iff.mpr fun u hu => (hjZ u (hUZ hu)).symm
  have hk3' : Nat.card (Subgroup.zpowers (k' : Q)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hk3 hk1
  have hAU : Aq ⊓ U ≤ Subgroup.zpowers (k' : Q) := by
    have hle : Subgroup.zpowers (k' : Q) ≤ Bq ⊓ U :=
      le_inf (Subgroup.zpowers_le.mpr hkB) (Subgroup.zpowers_le.mpr hkU)
    have hlt : Bq ⊓ U < Bq := lt_of_le_of_ne inf_le_left fun h' => hv₀U (by
      have : v₀ ∈ Bq ⊓ U := by rw [h']; exact hv₀B
      exact this.2)
    have h1 : Nat.card ↥(Bq ⊓ U) < 9 := hB9 ▸ Subgroup.card_lt_of_lt hlt
    have h2 : Nat.card ↥(Bq ⊓ U) ∣ 9 := hB9 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h3 : 3 ≤ Nat.card ↥(Bq ⊓ U) := hk3' ▸ Subgroup.card_le_of_le hle
    have h4 : Nat.card ↥(Bq ⊓ U) = 3 := by
      have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [h9] at h2
      obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
      interval_cases i
      · rw [hie] at h3
        norm_num at h3
      · rw [hie]
        norm_num
      · rw [hie] at h1
        norm_num at h1
    have heq : Subgroup.zpowers (k' : Q) = Bq ⊓ U :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hk3'])
    intro x hx
    rw [heq]
    exact ⟨hAZB ⟨hx.1, hUZ hx.2⟩, hx.2⟩
  have hAUN : Aq ≤ Subgroup.normalizer (U : Set Q) := by
    rw [← hAeq']
    refine sup_le ((Subgroup.zpowers_le.mpr hkU).trans Subgroup.le_normalizer) fun x hx =>
      Item148HJ.mem_normalizer_of_conj_mem fun u hu => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp (hEU hx) u hu
    rw [← h1]
    simpa using hu
  have hCN : Ronan148J.CentralNoncentral3 ↥U := by
    refine ⟨by rw [hU.1], ?_⟩
    obtain ⟨x, hx3, hxZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hU
    exact ⟨x, hx3, hxZ⟩
  exact Ronan148J.false_of_centralNoncentral_of_le hAp hF3 hk3' hAeq' hEU hAU hAUN hCN

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
