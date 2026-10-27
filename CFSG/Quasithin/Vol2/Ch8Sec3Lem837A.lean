module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem838A
public import CFSG.Quasithin.Background.HL3WrWreath

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative

namespace Ch837

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_le_normalizer_of_row {T L I : Subgroup G} [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) :
    ¬ T ≤ Subgroup.normalizer (L : Set G) := fun hT => hrow.1.ne
  (le_antisymm (Vol2.Ch10.SecA.le_fsuL0 T L) (conjClosure_le fun _ hs l hl =>
    (Subgroup.mem_normalizer_iff.mp (hT hs) l).mp hl))

theorem exists_model_eW00_T {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (hV : IsElemAbelian 2 (fsuV T I)) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) {z : G} (hz1 : z ≠ 1)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) :
    ∃ e : IntMod (fsuV T I) hV ≃* WMod, (autI hV (fsuL0 T L)).map (congrHom e) = img ∧
      (U3.prod U3).map rho ≤ (autI hV T).map (congrHom e) ∧
      (autI hV T).map (congrHom e) ≤ norm ∧
      ∃ hz : z ∈ fsuV T I, e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0 := by
  obtain ⟨e, he, hY, hYn, -⟩ := Ch838.exists_model_T hyp hV hrow
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hz : z ∈ fsuV T I := hzmem.1
  refine ⟨e, he, hY, hYn, hz, ?_⟩
  have hfix : e (IntMod.mk hV ⟨z, hz⟩) ∈ fixV l3wrSylU := by
    intro y hy
    obtain ⟨ψ, hψ, rfl⟩ := hY hy
    obtain ⟨t, htT, rfl⟩ := (mem_autI hV).1 hψ
    change e (convI hV t (e.symm (e (IntMod.mk hV ⟨z, hz⟩)))) = e (IntMod.mk hV ⟨z, hz⟩)
    rw [MulEquiv.symm_apply_apply]
    congr 1
    apply IntMod.val_injective
    rw [convI_apply_val]
    change (t : G) * z * (t : G)⁻¹ = z
    rw [Subgroup.mem_centralizer_iff.mp hzmem.2 t htT, mul_inv_cancel_right]
  rcases eq_one_or_eq_eW00_of_mem_fixV hfix with h | h
  · exfalso
    rw [← map_one e] at h
    exact hz1 (congrArg IntMod.val (e.injective h))
  · exact h

theorem exists_not_mem_img
    (h37 : CFSG.QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I)) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (e : IntMod (fsuV T I) hV ≃* WMod) (he : (autI hV (fsuL0 T L)).map (congrHom e) = img) :
    ∃ t ∈ T, ∃ ht : t ∈ Subgroup.normalizer (fsuV T I : Set G),
      congrHom e (convI hV ⟨t, ht⟩) ∉ img := by
  have hnn := not_le_normalizer_of_row hrow
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  have htN : t ∈ Subgroup.normalizer (fsuV T I : Set G) := hN (Subgroup.mem_sup_right ht)
  refine ⟨t, ht, htN, fun himg => ?_⟩
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hCL0 : fsuL0 T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
    rw [hVVM]
    exact Vol2.Ch10.SecA.fsuL0_inf_centralizer_le_of_fsu h37 h38 hyp.fsu hnn
  rw [← he] at himg
  obtain ⟨ψ, hψ, hψe⟩ := himg
  obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hψ
  have hlt : convI hV l = convI hV ⟨t, htN⟩ := congrHom_injective e hψe
  set c : G := (l : G)⁻¹ * t with hc
  have hcC : c ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    have h1 : convI hV (l⁻¹ * ⟨t, htN⟩) = 1 := by
      rw [map_mul, map_inv, hlt, inv_mul_cancel]
    exact (convI_eq_one_iff hV _).1 h1
  have hTL0 : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) := le_normalizer_conjClosure L T
  have hcN : c ∈ Subgroup.normalizer (fsuL0 T L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hlL)) (hTL0 ht)
  have hL0V : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
  have hcomm : ∀ y ∈ fsuL0 T L, y⁻¹ * c⁻¹ * y * c ∈ pCoreOf 2 (fsuL0 T L) := by
    intro y hy
    refine hCL0 ⟨?_, ?_⟩
    · have h1 : c⁻¹ * y * c ∈ fsuL0 T L := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hcN) y).mp hy
        simpa using this
      have := (fsuL0 T L).mul_mem ((fsuL0 T L).inv_mem hy) h1
      simpa [mul_assoc] using this
    · have hcC' : c⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := Subgroup.inv_mem _ hcC
      have h1 : y⁻¹ * c⁻¹ * y ∈ Subgroup.centralizer (fsuV T I : Set G) := by
        have := Vol2.Ch10.SecA.le_normalizer_centralizer hL0V ((fsuL0 T L).inv_mem hy)
        have := (Subgroup.mem_normalizer_iff.mp this c⁻¹).mp hcC'
        simpa using this
      exact Subgroup.mul_mem _ h1 hcC
  have hloc := hyp.fsu.maximal.1
  have hLn : fsuL0 T L ≤ Subgroup.normalizer (L : Set G) :=
    Vol2.Ch10.SecA.fsuL0_le_normalizer hloc
  have hle : CFSG.conjugate L t ≤ L ⊔ pCoreOf 2 (fsuL0 T L) := by
    intro y hy
    rw [Vol2.Ch10.SecA.mem_conjugate_iff] at hy
    set x := t * y * t⁻¹ with hx
    have hyx : y = t⁻¹ * x * t := by rw [hx]; group
    have hx' : (l : G)⁻¹ * x * l ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hLn ((fsuL0 T L).inv_mem hlL)) x).mp hy
      simpa using this
    set x' := (l : G)⁻¹ * x * l with hx'def
    have hx'L0 : x' ∈ fsuL0 T L := Vol2.Ch10.SecA.le_fsuL0 T L hx'
    have e1 : y = x' * (x'⁻¹ * c⁻¹ * x' * c) := by
      rw [hyx, hx'def, hc]
      group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx')
      (Subgroup.mem_sup_right (hcomm x' hx'L0))
  have heq : CFSG.conjugate L t = pCoreOf 2 (CFSG.conjugate L t) := by
    rw [← Vol2.Ch10.SecA.conjugate_inf_sup_pCoreOf_fsuL0_of_fsu h37 h38 hyp.fsu hnn ht htn]
    exact (inf_eq_left.mpr hle).symm
  have hs := Vol2.Ch10.SecA.isSimpleGroup_conjugate_of_fsu h37 h38 hyp.fsu hnn ht htn
  obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have ha : (a' : ↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) = 1 := by
    rw [Vol2.Ch10.SecA.mk_eq_one_iff, ← heq]
    exact a'.2
  have hb : (b' : ↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) = 1 := by
    rw [Vol2.Ch10.SecA.mk_eq_one_iff, ← heq]
    exact b'.2
  rw [ha, hb]

@[expose] noncomputable def actOn {V H : Subgroup G} (hV : IsElemAbelian 2 V)
    (e : IntMod V hV ≃* WMod) (hN : H ≤ Subgroup.normalizer (V : Set G)) : ↥H →* MulAut WMod :=
  (congrHom e).comp ((convI hV).comp (Subgroup.inclusion hN))

omit [Finite G] in
theorem actOn_apply {V H : Subgroup G} (hV : IsElemAbelian 2 V) (e : IntMod V hV ≃* WMod)
    (hN : H ≤ Subgroup.normalizer (V : Set G)) (x : ↥H) :
    actOn hV e hN x = congrHom e (convI hV ⟨x, hN x.2⟩) := rfl

theorem nonempty_oTwoQuot_equiv
    (h37 : CFSG.QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I)) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz1 : z ≠ 1)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) :
    Nonempty (OTwoQuot (ch83X T L z ⊔ T) ≃* S152N.W3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he, hY, -, hz, hez⟩ := exists_model_eW00_T hyp hV hrow hz1 hzV
  have hnn := not_le_normalizer_of_row hrow
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hCL0 : fsuL0 T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
    rw [hVVM]
    exact Vol2.Ch10.SecA.fsuL0_inf_centralizer_le_of_fsu h37 h38 hyp.fsu hnn
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  set X := ch83X T L z with hXdef
  have hXL : X ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) := (twoResidual_le _).trans inf_le_right
  have hXT : X ⊔ T ≤ fsuL0 T L ⊔ T := sup_le_sup_right hXL T
  have hNX : X ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) := hXT.trans hN
  have hL0n : X ⊔ T ≤ Subgroup.normalizer (fsuL0 T L : Set G) :=
    sup_le (hXL.trans Subgroup.le_normalizer) (le_normalizer_conjClosure L T)
  have hL0V : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
  have hezs : e.symm (eW 0 0) = IntMod.mk hV ⟨z, hz⟩ := by
    rw [← hez, MulEquiv.symm_apply_apply]
  have hfixz : ∀ g : Subgroup.normalizer (fsuV T I : Set G),
      (congrHom e (convI hV g) (eW 0 0) = eW 0 0 ↔
        (g : G) ∈ Subgroup.centralizer ({z} : Set G)) := by
    intro g
    have key : congrHom e (convI hV g) (eW 0 0) = eW 0 0 ↔ (g : G) * z * (g : G)⁻¹ = z := by
      change e (convI hV g (e.symm (eW 0 0))) = eW 0 0 ↔ _
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
      calc z * (g : G) = ((g : G) * z * (g : G)⁻¹) * g := by rw [h]
        _ = g * z := by group
    · intro h
      rw [← h z rfl, mul_inv_cancel_right]
  set act := actOn hV e hNX with hact
  have hstab : ∀ x : ↥(X ⊔ T), act x ∈ stabE := fun x => mem_stabE_iff.2
    ⟨congrHom_mem_norm e he (convI_mem_normalizer_autI hV (hL0n x.2)),
      (hfixz _).2 ((sup_le hXz hTz) x.2)⟩
  have hXimg : ∀ c : MulAut WMod, c ∈ img → c (eW 0 0) = eW 0 0 → orderOf c = 3 →
      c ∈ act.range := by
    intro c hc hcE hc3
    have hc' : c ∈ (autI hV (fsuL0 T L)).map (congrHom e) := by
      rw [he]
      exact hc
    obtain ⟨ψ, hψ, rfl⟩ := hc'
    obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hψ
    have hlz : (l : G) ∈ Subgroup.centralizer ({z} : Set G) := (hfixz l).1 hcE
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient
      (fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G)) (l : G) ⟨hlL, hlz⟩
    have hk' : (l : G) ^ 2 ^ k ∈ X ⊔ T := Subgroup.mem_sup_left hk
    have hpow : congrHom e (convI hV l) ^ 2 ^ k ∈ act.range := by
      refine ⟨⟨(l : G) ^ 2 ^ k, hk'⟩, ?_⟩
      rw [actOn_apply, ← map_pow, ← map_pow]
      try rfl
    exact mem_of_two_pow_mem hc3 hpow
  have hTimg : ∀ c : MulAut WMod, c ∈ (U3.prod U3).map rho → c ∈ act.range := by
    intro c hc
    obtain ⟨ψ, hψ, rfl⟩ := hY hc
    obtain ⟨t, htT, rfl⟩ := (mem_autI hV).1 hψ
    exact ⟨⟨t, Subgroup.mem_sup_right htT⟩, rfl⟩
  have hc1 := hXimg _ (rho_mem_img _) (rho_fix_E00 c3_mem_P1 P1.one_mem)
    (by rw [orderOf_injective rho rho_injective]; exact orderOf_c3_one)
  have hc2 := hXimg _ (rho_mem_img _) (rho_fix_E00 P1.one_mem c3_mem_P1)
    (by rw [orderOf_injective rho rho_injective]; exact orderOf_one_c3)
  have hu1 := hTimg _ ⟨(u0, 1), ⟨u0_mem_U3, U3.one_mem⟩, rfl⟩
  have hu2 := hTimg _ ⟨(1, u0), ⟨U3.one_mem, u0_mem_U3⟩, rfl⟩
  obtain ⟨t, ht, htN, htimg⟩ := exists_not_mem_img h37 h38 h326 hyp hV hrow hN e he
  have hty : congrHom e (convI hV ⟨t, htN⟩) ∈ act.range :=
    ⟨⟨t, Subgroup.mem_sup_right ht⟩, rfl⟩
  set ι : ↥(X ⊔ T) →* ↥stabE := act.codRestrict stabE hstab with hι
  set ω : ↥(X ⊔ T) →* S152N.W3 := omegaW.comp ι with hω
  have hrange : act.range ≤ stabE := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  have hsurj : Function.Surjective ω := by
    intro w
    obtain ⟨x, ⟨y, hy⟩, hxw⟩ := exists_omegaW_eq hrange hc1 hc2 hu1 hu2 hty htimg w
    refine ⟨y, ?_⟩
    have : ι y = x := Subtype.ext hy
    rw [hω, MonoidHom.comp_apply, this, hxw]
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hL0Tq := B6.isTwoQuotient_of_sup_eq hT2
    (sup_le Subgroup.le_normalizer (le_normalizer_conjClosure L T)) (sup_comm T (fsuL0 T L))
  have hC2 : ∀ y ∈ fsuL0 T L ⊔ T, y ∈ Subgroup.centralizer (fsuV T I : Set G) →
      ∃ n : ℕ, y ^ 2 ^ n = 1 := by
    intro y hy hyC
    obtain ⟨k, hk⟩ := hL0Tq y hy
    have hO : y ^ 2 ^ k ∈ pCoreOf 2 (fsuL0 T L) :=
      hCL0 ⟨hk, Subgroup.pow_mem _ hyC _⟩
    obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L) ⟨_, hO⟩
    refine ⟨k + m, ?_⟩
    have hm' : (y ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [pow_add, pow_mul, hm']
  have hker2 : IsPGroup 2 ω.ker := by
    rintro ⟨x, hx⟩
    have hS : act x ∈ Shat := (omegaW_eq_one_iff (ι x)).1 hx
    have hsq : act (x * x) = 1 := by
      rw [map_mul]
      exact mul_self_eq_one_of_mem_Shat hS
    have hC : ((x * x : ↥(X ⊔ T)) : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
      rw [actOn_apply] at hsq
      have h1 := congrHom_injective e (hsq.trans (map_one _).symm)
      exact (convI_eq_one_iff hV _).1 h1
    obtain ⟨n, hn⟩ := hC2 _ (hXT (x * x).2) hC
    refine ⟨n + 1, Subtype.ext (Subtype.ext ?_)⟩
    have e1 : ((x * x : ↥(X ⊔ T)) : G) = (x : G) ^ 2 := by rw [sq]; rfl
    rw [e1, ← pow_mul, ← pow_succ'] at hn
    simpa using hn
  have hker : ω.ker = CFSG.Open.pCore 2 ↥(X ⊔ T) := by
    apply le_antisymm
    · try with_reducible rfl
      exact le_sSup ⟨ω.normal_ker, hker2⟩
    · intro x hx
      have hn : ((CFSG.pCore 2 ↥(X ⊔ T)).map ω).Normal :=
        (CFSG.pCore_normal (p := 2) (G := ↥(X ⊔ T))).map ω hsurj
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥(X ⊔ T)).map ω) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥(X ⊔ T))).map ω
      have hbot := W3.eq_bot_of_normal_isPGroup_two hn h2
      have hmem : ω x ∈ (CFSG.pCore 2 ↥(X ⊔ T)).map ω := Subgroup.mem_map_of_mem ω hx
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ω hsurj)⟩

end Ch837

end CFSG.Quasithin.H13
