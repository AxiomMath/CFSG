module

public import CFSG.Quasithin.Vol2.Ch8Sec3L0Cent
public import CFSG.Quasithin.Background.HL3WrBlock
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8311

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative

namespace Ch838

section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem map_iSup_aSet (e : V ≃* W) (k : ℕ) (X : Subgroup (MulAut V)) :
    (⨆ A ∈ E3.aSet k X, A).map (congrHom e) = ⨆ B ∈ E3.aSet k (X.map (congrHom e)), B := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (f := fun B (_ : B ∈ E3.aSet k (X.map (congrHom e))) => B)
      (A.map (congrHom e)) ((map_mem_aSet_iff e).2 hA) le_rfl
  · refine iSup₂_le fun B hB => ?_
    obtain ⟨A, -, rfl⟩ := exists_eq_map_congrHom e hB.1
    exact Subgroup.map_mono (le_iSup₂_of_le (f := fun A (_ : A ∈ E3.aSet k X) => A) A
      ((map_mem_aSet_iff e).1 hB) le_rfl)

theorem map_congrHom_self {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) :
    X.map (congrHom x) = X := by
  have e : ∀ φ : MulAut V, congrHom x φ = x * φ * x⁻¹ := fun φ => MulEquiv.ext fun _ => rfl
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    rw [e]
    exact X.mul_mem (X.mul_mem hx hφ) (X.inv_mem hx)
  · intro hψ
    refine ⟨x⁻¹ * ψ * x, X.mul_mem (X.mul_mem (X.inv_mem hx) hψ) hx, ?_⟩
    rw [e]
    group

theorem map_iSup_aSet_self {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) (k : ℕ) :
    (⨆ A ∈ E3.aSet k X, A).map (congrHom x) = ⨆ A ∈ E3.aSet k X, A := by
  rw [map_iSup_aSet x k X, map_congrHom_self hx]

theorem apply_mem_fixV_iSup_aSet {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) (k : ℕ)
    {v : V} (hv : v ∈ fixV (⨆ A ∈ E3.aSet k X, A)) : x v ∈ fixV (⨆ A ∈ E3.aSet k X, A) := by
  have h := fixV_map_congrHom x (⨆ A ∈ E3.aSet k X, A)
  rw [map_iSup_aSet_self hx] at h
  rw [h]
  exact ⟨v, hv, rfl⟩

end Transport

theorem exists_lift_of_not_dvd_card_ker {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    {p : ℕ} [hp : Fact p.Prime] (φ : H →* K) {P : Subgroup K} (hP : IsPGroup p P)
    (hPφ : P ≤ φ.range) (hker : ¬ p ∣ Nat.card φ.ker) :
    ∃ Q : Subgroup H, Q ≤ P.comap φ ∧ Nat.card Q = Nat.card P ∧ ∀ x ∈ Q, φ x = 1 → x = 1 := by
  classical
  set N := P.comap φ with hN
  obtain ⟨S⟩ : Nonempty (Sylow p ↥N) := inferInstance
  refine ⟨(S : Subgroup ↥N).map N.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective N.subtype_injective, S.card_eq_multiplicity]
    set ψ : ↥N →* K := φ.comp N.subtype with hψ
    have hrange : ψ.range = P := by
      rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, hN, Subgroup.map_comap_eq,
        inf_eq_right.mpr hPφ]
    have hle : φ.ker ≤ N := fun x hx => by
      change φ x ∈ P
      rw [MonoidHom.mem_ker.mp hx]
      exact P.one_mem
    have hker' : Nat.card ψ.ker = Nat.card φ.ker := by
      have h1 : ψ.ker = φ.ker.subgroupOf N := by
        ext x
        simp [hψ, Subgroup.mem_subgroupOf]
      rw [h1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hcardN : Nat.card ↥N = Nat.card φ.ker * Nat.card P := by
      rw [← Subgroup.card_mul_index ψ.ker, Subgroup.index_ker, hrange, hker']
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
    rw [hcardN, hk, Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero _ hp.out.ne_zero),
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, Nat.Prime.factorization_pow hp.out,
      Finsupp.single_eq_same, zero_add]
  · rintro _ ⟨s, hs, rfl⟩ h1
    obtain ⟨n, hn⟩ := S.isPGroup' ⟨s, hs⟩
    have hx : ((s : ↥N) : H) ^ p ^ n = 1 := by
      have := congrArg (fun y : ↥(S : Subgroup ↥N) => ((y : ↥N) : H)) hn
      simpa using this
    have hxk : ((s : ↥N) : H) ∈ φ.ker := h1
    have h2 : orderOf ((s : ↥N) : H) ∣ p ^ n := orderOf_dvd_of_pow_eq_one hx
    have h3 : orderOf ((s : ↥N) : H) ∣ Nat.card φ.ker := by
      have := orderOf_dvd_natCard (⟨_, hxk⟩ : φ.ker)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (p ^ n) (Nat.card φ.ker) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hker)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3)

variable {G : Type} [Group G] [Finite G]

theorem exists_model_T {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (hV : IsElemAbelian 2 (fsuV T I)) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) :
    ∃ e : IntMod (fsuV T I) hV ≃* WMod, (autI hV (fsuL0 T L)).map (congrHom e) = img ∧
      (U3.prod U3).map rho ≤ (autI hV T).map (congrHom e) ∧
      (autI hV T).map (congrHom e) ≤ norm ∧ IsPGroup 2 ↥((autI hV T).map (congrHom e)) := by
  obtain ⟨e, he, hY⟩ := Ch8311.exists_model_sylU hyp hV hrow
  have hTL₀ : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) := le_normalizer_conjClosure L T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  refine ⟨e, he, hY, ?_, ?_⟩
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hψ
    exact congrHom_mem_norm e he (convI_mem_normalizer_autI hV (hTL₀ hg))
  · have h1 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (fsuV T I : Set G))) :=
      hyp.fsu.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm
    exact (h1.map (convI hV)).map _

omit [Finite G] in
theorem map_rbar_eq {T I : Subgroup G} {hV : IsElemAbelian 2 (fsuV T I)}
    {e : IntMod (fsuV T I) hV ≃* WMod} (hY : (U3.prod U3).map rho ≤ (autI hV T).map (congrHom e))
    (hYn : (autI hV T).map (congrHom e) ≤ norm)
    (hY2 : IsPGroup 2 ↥((autI hV T).map (congrHom e))) :
    (⨆ A ∈ E3.aSet 2 (autI hV T), A).map (congrHom e) = (R1.prod R1).map rho := by
  rw [map_iSup_aSet e 2, iSup_aSet_two_eq hYn hY2 hY]

omit [Finite G] in
theorem mem_ch83CR {T I : Subgroup G} (hV : IsElemAbelian 2 (fsuV T I)) {z : G}
    (hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G)) : z ∈ ch83CR hV := by
  refine ⟨IntMod.mk hV ⟨z, hz.1⟩, fun x hx => ?_, rfl⟩
  have hR : (⨆ A ∈ E3.aSet 2 (autI hV T), A) ≤ autI hV T := iSup₂_le fun A hA => hA.1
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 (hR hx)
  apply IntMod.val_injective
  rw [convI_apply_val]
  change (g : G) * z * (g : G)⁻¹ = z
  rw [Subgroup.mem_centralizer_iff.mp hz.2 g hg, mul_inv_cancel_right]

omit [Finite G] in
theorem le_normalizer_ch83CR {T I : Subgroup G} (hV : IsElemAbelian 2 (fsuV T I))
    (hTN : T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    T ≤ Subgroup.normalizer (ch83CR hV : Set G) := by
  have key : ∀ t ∈ T, ∀ u ∈ ch83CR hV, t * u * t⁻¹ ∈ ch83CR hV := by
    rintro t ht _ ⟨v, hv, rfl⟩
    have hx : convI hV ⟨t, hTN ht⟩ ∈ autI hV T := convI_mem_autI hV ht (hTN ht)
    exact ⟨convI hV ⟨t, hTN ht⟩ v, apply_mem_fixV_iSup_aSet hx 2 hv,
      convI_apply_val hV ⟨t, hTN ht⟩ v⟩
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key t ht u, fun h => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ h
  simpa [mul_assoc] using this

theorem exists_E9_ch83CR
    (h37 : CFSG.QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I)) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    ∃ P : Subgroup G, P ≤ Subgroup.normalizer (ch83CR hV : Set G) ∧ IsElemAbelian 3 P ∧
      Nat.card P = 3 ^ 2 ∧ P ⊓ Subgroup.centralizer (ch83CR hV : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  obtain ⟨e, he, hY, hYn, hY2⟩ := exists_model_T hyp hV hrow
  have hRe := map_rbar_eq hY hYn hY2
  set R := ⨆ A ∈ E3.aSet 2 (autI hV T), A with hRdef
  have hnn : ¬ T ≤ Subgroup.normalizer (L : Set G) := fun hT => hrow.1.ne
    (le_antisymm (Vol2.Ch10.SecA.le_fsuL0 T L) (conjClosure_le fun s hs l hl =>
      (Subgroup.mem_normalizer_iff.mp (hT hs) l).mp hl))
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hCL0 : fsuL0 T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
    rw [hVVM]
    exact Vol2.Ch10.SecA.fsuL0_inf_centralizer_le_of_fsu h37 h38 hyp.fsu hnn
  have hL0N : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
  set φ : ↥(fsuL0 T L) →* MulAut WMod :=
    (congrHom e).comp ((convI hV).comp (Subgroup.inclusion hL0N)) with hφ
  have hφapp : ∀ l : ↥(fsuL0 T L), φ l = congrHom e (convI hV ⟨l, hL0N l.2⟩) := fun l => rfl
  have hrange : φ.range = img := by
    rw [← he]
    ext ψ
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨convI hV ⟨l, hL0N l.2⟩, (mem_autI hV).2 ⟨⟨l, hL0N l.2⟩, l.2, rfl⟩, rfl⟩
    · rintro ⟨χ, hχ, rfl⟩
      obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hχ
      exact ⟨⟨g, hg⟩, rfl⟩
  have hfixR : ∀ v ∈ fixV R, e v ∈ fixV ((R1.prod R1).map rho) := by
    intro v hv x hx
    obtain ⟨r, hr, rfl⟩ := (Subgroup.ext_iff.mp hRe x).mpr hx
    change e (r (e.symm (e v))) = e v
    rw [MulEquiv.symm_apply_apply, hv r hr]
  have hfixR' : ∀ w ∈ fixV ((R1.prod R1).map rho), e.symm w ∈ fixV R := by
    intro w hw r hr
    have h1 := hw (congrHom e r) ((Subgroup.ext_iff.mp hRe _).mp ⟨r, hr, rfl⟩)
    change e (r (e.symm w)) = w at h1
    have h2 := congrArg e.symm h1
    rwa [MulEquiv.symm_apply_apply] at h2
  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    have h2 : IsPGroup 2 φ.ker := by
      intro x
      have hx1 : φ (x : ↥(fsuL0 T L)) = 1 := x.2
      have hxC : ((x : ↥(fsuL0 T L)) : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
        rw [hφapp] at hx1
        have h3 : convI hV ⟨_, hL0N (x : ↥(fsuL0 T L)).2⟩ = 1 :=
          congrHom_injective e (hx1.trans (map_one _).symm)
        exact (convI_eq_one_iff hV _).mp h3
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L)
        ⟨_, hCL0 ⟨(x : ↥(fsuL0 T L)).2, hxC⟩⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hn
      simpa using this
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
    rw [hk]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hP3 : IsPGroup 3 ↥PB := IsPGroup.of_card card_PB
  obtain ⟨Q, hQP, hQcard, hQinj⟩ := exists_lift_of_not_dvd_card_ker φ hP3
    (by rw [hrange]; exact PB_le_img) hker
  have hcommQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    have h1 : φ (a * b * (b * a)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul]
      have hab : φ a * φ b = φ b * φ a :=
        congrArg Subtype.val (isElemAbelian_PB.1.is_comm.comm ⟨_, hQP ha⟩ ⟨_, hQP hb⟩)
      rw [hab, mul_inv_cancel]
    have h2 := hQinj _ (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem (Q.mul_mem hb ha))) h1
    exact mul_inv_eq_one.mp h2
  have hpowQ : ∀ a ∈ Q, a ^ 3 = 1 := by
    intro a ha
    refine hQinj _ (Q.pow_mem ha 3) ?_
    rw [map_pow]
    exact isElemAbelian_PB.2 _ (hQP ha)
  refine ⟨Q.map (fsuL0 T L).subtype, ?_, ?_, ?_, ?_⟩
  ·
    have key : ∀ q ∈ Q, ∀ u ∈ ch83CR hV, (q : G) * u * (q : G)⁻¹ ∈ ch83CR hV := by
      rintro q hq _ ⟨v, hv, rfl⟩
      set y := convI hV ⟨(q : G), hL0N q.2⟩ with hy
      have hyPB : congrHom e y ∈ PB := hQP hq
      have h1 := hfixR' _ (apply_mem_fixV_of_mem_normalizer (PB_le_normalizer hyPB) (hfixR v hv))
      have h2 : e.symm (congrHom e y (e v)) = y v := by
        change e.symm (e (y (e.symm (e v)))) = y v
        rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      rw [h2] at h1
      exact ⟨y v, h1, convI_apply_val hV ⟨(q : G), hL0N q.2⟩ v⟩
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨key q hq u, fun h => ?_⟩
    have := key q⁻¹ (Q.inv_mem hq) _ h
    simpa [mul_assoc] using this
  ·
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨qa, hqa, hqa'⟩ := a.2
      obtain ⟨qb, hqb, hqb'⟩ := b.2
      change (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hqa', ← hqb']
      exact congrArg Subtype.val (hcommQ qa hqa qb hqb)
    · rintro _ ⟨q, hq, rfl⟩
      exact congrArg Subtype.val (hpowQ q hq)
  · rw [Subgroup.card_map_of_injective (fsuL0 T L).subtype_injective, hQcard, card_PB]
  ·
    rw [eq_bot_iff]
    rintro _ ⟨⟨q, hq, rfl⟩, hxC⟩
    rw [Subgroup.mem_bot]
    set y := convI hV ⟨(q : G), hL0N q.2⟩ with hy
    have hyv : ∀ v ∈ fixV R, y v = v := by
      intro v hv
      apply IntMod.val_injective
      rw [convI_apply_val]
      have h1 := Subgroup.mem_centralizer_iff.mp hxC (ch83Val hV v) ⟨v, hv, rfl⟩
      change (q : G) * v.val * (q : G)⁻¹ = v.val
      change v.val * (q : G) = (q : G) * v.val at h1
      rw [← h1, mul_inv_cancel_right]
    have hφ1 : φ q = 1 := by
      rw [hφapp]
      refine eq_one_of_mem_PB_of_fix (hQP hq) fun w hw => ?_
      change e (y (e.symm w)) = w
      rw [hyv _ (hfixR' w hw), MulEquiv.apply_symm_apply]
    rw [hQinj q hq hφ1]
    rfl

theorem not_three_dvd_card_centralizer_ch83CR
    (h37 : CFSG.QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) (hU1 : ch83CR hV ≠ ⊥) :
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (ch83CR hV : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPN, hP, hPcard, hPC⟩ := exists_E9_ch83CR h37 h38 h326 hyp hV hrow hN
  have hUV : ch83CR hV ≤ fsuV T I := by
    rintro _ ⟨v, -, rfl⟩
    exact v.val_mem
  have hU2 : IsElemAbelian 2 (ch83CR hV) := B2F.isElemAbelian_mono hUV hV
  have hloc : IsTwoLocal (Subgroup.normalizer (ch83CR hV : Set G)) :=
    ⟨ch83CR hV, hU1, B2F.isPGroup_of_isElemAbelian hU2, rfl⟩
  have h := CFSG.Quasithin.not_dvd_card_centralizer_of_faithful
    (fun q hq hq2 => CFSG.Quasithin.pRank_le_two_of_isTwoLocal hyp.fsu.qtke hloc hq hq2)
    (by norm_num : (3 : ℕ) ≠ 2) hPN hP hPcard Subgroup.le_normalizer hU2 hPN hPC
  rwa [inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)] at h

end Ch838

end CFSG.Quasithin.H13
