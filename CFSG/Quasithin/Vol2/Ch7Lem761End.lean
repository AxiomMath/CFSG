module

public import CFSG.Quasithin.Vol2.Ch7Lem761Pair
public import CFSG.Quasithin.Vol2.Ch7Inputs761
public import CFSG.Quasithin.Background.HSL3FixAbs
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.EmptyFaithful.S152L27A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem normalizer_zpowers_eq_centralizer {z : G} (hzz : z * z = 1) (hz1 : z ≠ 1) :
    Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have h1 := (Subgroup.mem_normalizer_iff.mp hg z).mp (Subgroup.mem_zpowers z)
    rcases SL3One.eq_one_or_eq_of_mem_zpowers hzz h1 with h | h
    · exfalso
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h]
  · intro hg
    have hgz : g * z * g⁻¹ = z := by rw [hg, mul_inv_cancel_right]
    have hk : ∀ k : ℤ, g * z ^ k * g⁻¹ = z ^ k := fun k => by rw [← conj_zpow, hgz]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hk k).symm⟩
    · rintro ⟨k, hk'⟩
      refine ⟨k, ?_⟩
      calc z ^ k = g⁻¹ * (g * z ^ k * g⁻¹) * g := by group
        _ = g⁻¹ * z ^ k * g := by rw [hk k]
        _ = g⁻¹ * (g * h * g⁻¹) * g := by rw [hk']
        _ = h := by group

omit [Finite G] in
theorem isPGroup_zpowers_of_mul_self {z : G} (hzz : z * z = 1) :
    IsPGroup 2 (Subgroup.zpowers z) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hzz))

omit [Finite G] in
theorem isSylowIn_of_odd {S K H : Subgroup G} (hS : IsSylowIn 2 S K) (hKH : K ≤ H)
    (hodd : ¬ 2 ∣ K.relIndex H) : IsSylowIn 2 S H := by
  refine ⟨hS.le.trans hKH, hS.isPGroup, fun h2 => ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex S K H hS.le hKH] at h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hS.not_dvd_relIndex h
  · exact hodd h

theorem fsuM_le_normalizer_of_pair (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5)
    (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] {n : ℕ}
    (hrow : Row711SL3Pair T L I n) :
    L = fsuL0 T L ∧ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
    refine h711n G T L I hyp inferInstance ?_
    right; right; right; right; right; right; right; right; right; right; right; left
    exact ⟨n, hrow⟩
  have hL : L = conjClosure L T := by
    refine le_antisymm (le_conjClosure L T) (conjClosure_le fun h hh z hz => ?_)
    exact (Subgroup.mem_normalizer_iff.mp (hTL hh) z).mp hz
  refine ⟨hL, ?_⟩
  obtain ⟨-, -, h3⟩ := h325 G T L I hyp.fsu hL
  have hVM : conjClosure (conjClosure I T) (Subgroup.normalizer (L : Set G)) =
      conjClosure I T := by
    rcases h3 with ⟨-, h⟩ | ⟨hI, -⟩ | ⟨-, -, ⟨t, htT, htN⟩, hall⟩
    · exact h.symm
    · exfalso
      obtain ⟨t, -, hsup, hinf, -⟩ := hrow.1
      have hle : CFSG.conjugate I t ≤ I := by
        calc CFSG.conjugate I t ≤ I ⊔ CFSG.conjugate I t := le_sup_right
          _ = fsuV T I := hsup
          _ = I := hI.symm
      have hbot : CFSG.conjugate I t = ⊥ := by
        rw [← inf_eq_right.mpr hle, hinf]
      apply hyp.fsu.irrPlus.2.1
      rw [eq_bot_iff]
      intro x hx
      have hx' : t⁻¹ * x * t ∈ CFSG.conjugate I t := by
        rw [mem_conjugate_iff']
        simpa [mul_assoc] using hx
      rw [hbot, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      calc x = t * (t⁻¹ * x * t) * t⁻¹ := by group
        _ = 1 := by rw [hx']; group
    · exact (hall t htT htN).1
  have h1 := le_normalizer_conjClosure (conjClosure I T) (Subgroup.normalizer (L : Set G))
  rw [hVM] at h1
  change Subgroup.normalizer (conjClosure L T : Set G) ≤ _
  rw [← hL]
  exact h1

theorem thompsonJ_le_centralizer_fsuV (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    thompsonJ T ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hnFF := not_isFFModule_of_hyp702 hyp hV hNM
  have hVT := fsuV_le_T hyp.fsu hV hN
  have hTN : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  unfold thompsonJ
  refine iSup₂_le fun A hA => ?_
  by_contra hA1
  apply hnFF
  obtain ⟨B, hBX, hB1, hB2, hBcard⟩ := isFFModule_autOn hV hVT hTN hA.1 hA hA1
  exact ⟨B, hBX.trans (autI_mono hV le_top), hB1, hB2, hBcard⟩

theorem not_isFFStarOffender_autOn (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ ∃ A : Subgroup (MulAut ↥(fsuV T I)),
      IsFFStarOffender (V := ↥(fsuV T I)) (autOn (fsuL0 T L ⊔ T) (fsuV T I)) A := by
  rintro _ ⟨A, hAX, hA1, hA2, hmax⟩
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hle : autOn (fsuL0 T L ⊔ T) (fsuV T I) ≤
      Subgroup.normalizer (autOn (fsuL0 T L) (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
    (autOn_le_autOn (fsuV T I) le_top).trans (autI_top_le_normalizer hV hNM)
  exact hyp.notFF inferInstance ⟨A, hAX.trans hle, hA1, hA2, hmax⟩

omit [Finite G] in
theorem exists_twist_eq (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) (htw : IsTwistedPair T L I) :
    ∃ t ∈ T, ∃ φ : MulAut (IntMod (fsuV T I) hV),
      φ ∈ Subgroup.normalizer (autI hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) hV))) ∧
      intSub hV I ⊓ (intSub hV I).map φ.toMonoidHom = ⊥ ∧
      intSub hV I ⊔ (intSub hV I).map φ.toMonoidHom = ⊤ ∧
      ¬ Pair.IsoMod (autI hV (fsuL0 T L)) (intSub hV I) ((intSub hV I).map φ.toMonoidHom) ∧
      (intSub hV I).map φ.toMonoidHom = intSub hV (CFSG.conjugate I t) := by
  obtain ⟨t, htT, hsup, hinf, hniso⟩ := htw
  have hIV : I ≤ fsuV T I := le_fsuV I T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hItV : CFSG.conjugate I t ≤ fsuV T I := by
    rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem htT)) y).mp (hIV hy)
    simpa [mul_assoc] using this
  have htN : t⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) := hTV (T.inv_mem htT)
  set φ := convI hV ⟨t⁻¹, htN⟩ with hφ
  set V₁ : Subgroup (IntMod (fsuV T I) hV) := intSub hV I with hV₁
  have hmap : V₁.map φ.toMonoidHom = intSub hV (CFSG.conjugate I t) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_intSub]
      change (φ v).val ∈ CFSG.conjugate I t
      rw [hφ, convI_apply_val, mem_conjugate_iff']
      have : t * (t⁻¹ * v.val * t⁻¹⁻¹) * t⁻¹ = v.val := by group
      rw [this]
      exact hv
    · intro hx
      rw [mem_intSub] at hx
      have hx' := mem_conjugate_iff'.mp hx
      refine ⟨IntMod.mk hV ⟨t * x.val * t⁻¹, hIV hx'⟩, hx', ?_⟩
      apply IntMod.val_injective
      change (φ (IntMod.mk hV ⟨t * x.val * t⁻¹, hIV hx'⟩)).val = x.val
      rw [hφ, convI_apply_val]
      change t⁻¹ * (t * x.val * t⁻¹) * t⁻¹⁻¹ = x.val
      group
  refine ⟨t, htT, φ, autI_top_le_normalizer hV hNM (convI_mem_autI hV (Subgroup.mem_top _) htN),
    ?_, ?_, ?_, hmap⟩
  · rw [hmap, eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have : x.val ∈ I ⊓ CFSG.conjugate I t := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact IntMod.val_injective this
  · rw [hmap]
    apply Subgroup.map_injective (valHom_injective hV)
    rw [Subgroup.map_sup, hV₁, map_valHom_intSub hV hIV, map_valHom_intSub hV hItV, hsup,
      map_valHom_top]
  · rw [hmap]
    intro h
    exact hniso (isXSectionIso_of_isoMod hV hIV hItV (le_fsuL0 T L)
      ((le_fsuL0 T L).trans (le_sup_left.trans hN)) h)

omit [Finite G] in
theorem mem_normalizer_map_valHom {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {U : Subgroup (IntMod V hV)} {n : G} (hn : n ∈ Subgroup.normalizer (V : Set G))
    (hU : ∀ u ∈ U, convI hV ⟨n, hn⟩ u ∈ U)
    (hU' : ∀ u ∈ U, convI hV ⟨n⁻¹, Subgroup.inv_mem _ hn⟩ u ∈ U) :
    n ∈ Subgroup.normalizer ((U.map (E3.valHom hV) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨convI hV ⟨n, hn⟩ u, hU u hu, by
      rw [E3.valHom_apply, E3.valHom_apply, convI_apply_val]⟩
  · rintro ⟨u, hu, hux⟩
    refine ⟨convI hV ⟨n⁻¹, Subgroup.inv_mem _ hn⟩ u, hU' u hu, ?_⟩
    rw [E3.valHom_apply, convI_apply_val]
    rw [E3.valHom_apply] at hux
    change n⁻¹ * u.val * n⁻¹⁻¹ = x
    rw [hux]
    group

theorem stmt7_6_1_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h734 : Stmt7_3_4)
    (h771 : Stmt7_7_1) (h772 : Stmt7_7_2) (h3104 : Stmt3_2_10_four)
    (h3106 : Stmt3_2_10_six) : Stmt7_6_1 := by
  intro G _ _ T L I hyp h731 _ hrow
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨hL, hVM⟩ := fsuM_le_normalizer_of_pair h711n h325 hyp hrow
  have hJ := thompsonJ_le_centralizer_fsuV h37 h38 h39 hyp hV hN
  have hVp : IsVplus T L I (fsuV T I) := Or.inr ⟨fun h => h.1 hL, rfl⟩
  obtain ⟨hw, hr, -, hoff⟩ :=
    offender_le_autL_761 h37 h38 h39 hmod h734 h771 hyp h731 hrow hV
  have hT := hypE322_of_fsu hyp.fsu hV hN
  have hpV : IsPGroup 2 (fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  obtain ⟨g, hg⟩ := exists_isWOffenderAt hV hT (by simp [hw])
  obtain ⟨hcardA, hAL⟩ := hoff g hg
  obtain ⟨hm1, -, -, hWeq⟩ :=
    offender_quad_761 h37 h38 h39 hmod h734 h771 hyp h731 hrow hV hg
  have hVg : IsElemAbelian 2 (conjSubgroup (fsuV T I) g) := isElemAbelian_conjSubgroup hV g
  have hAN : conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G) := inf_le_right
  have hA2 : IsElemAbelian2 (autI hV (conjSubgroup (fsuV T I) g ⊓
      Subgroup.normalizer (fsuV T I : Set G))) :=
    isElemAbelian2_autI hV (B2F.isElemAbelian_mono inf_le_left hVg) hAN
  have hrow' := hrow
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨t, htT, φ, hφN, hinf, hsup, hniso, hmapφ⟩ := exists_twist_eq hV hN hNM htw
  have hL3 : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥
      3 1 := hnat
  obtain ⟨z, hz1, hzV, -, hzcomm, Vi, Y, hzVi, hViz, hWle, hY0, hIrr1, hIrr2, hnorm⟩ :=
    SL3One.H4_SL3One_fix hL3 hφN hinf hsup hniso hAL hA2 hcardA
  have hfix8 := SL3One.card_fixV_le_eight_inner hL3 hφN hinf hsup hniso hAL hA2 hcardA
  obtain ⟨hcard, -, -, -, -, -⟩ := SL3One.H4_SL3One hL3 hφN hinf hsup hniso
    (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)
  have hzGV : z.val ∈ fsuV T I := IntMod.val_mem z
  have hzG1 : z.val ≠ 1 := fun h => hz1 (IntMod.val_injective h)
  have hzz : z.val * z.val = 1 := by
    rw [← sq]
    exact hV.2 _ hzGV
  have hcardA₁ : Nat.card ↥(fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G)) =
      32 := by
    have h1 := card_eq_two_pow_mul hpV (inf_le_left : fsuV T I ⊓
      Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) ≤ fsuV T I)
    rw [hm1, pow_one] at h1
    have h2 : Nat.card ↥(fsuV T I) = 64 := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
      exact hcard
    omega
  have hcardW : Nat.card ↥(E3.gammaCheck 1 (autI hV (conjSubgroup (fsuV T I) g ⊓
      Subgroup.normalizer (fsuV T I : Set G)))) = 32 := by
    rw [← hcardA₁, ← hWeq, Subgroup.card_map_of_injective (E3.valHom_injective hV)]
  obtain ⟨x, hx, w, hwW, hxw⟩ : ∃ x ∈ autI hV (conjSubgroup (fsuV T I) g ⊓
      Subgroup.normalizer (fsuV T I : Set G)), ∃ w ∈ E3.gammaCheck 1 (autI hV
        (conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G))),
      x w * w⁻¹ = z := by
    by_contra hcon
    push Not at hcon
    have hle : E3.gammaCheck 1 (autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G))) ≤ fixV (autI hV (conjSubgroup (fsuV T I) g ⊓
          Subgroup.normalizer (fsuV T I : Set G))) := by
      intro w hw
      rw [mem_fixV]
      intro x hx
      rcases hzcomm x hx w hw with h | h
      · exact mul_inv_eq_one.mp h
      · exact absurd h (hcon x hx w hw)
    have h1 := Subgroup.card_le_of_le hle
    rw [hcardW] at h1
    have h2 := h1.trans hfix8
    norm_num at h2
  obtain ⟨a, haA, rfl⟩ := (mem_autI hV).1 hx
  have hwA₁ : w.val ∈ fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
    rw [← hWeq]
    exact ⟨w, hwW, rfl⟩
  have hzval : z.val = (a : G) * w.val * (a : G)⁻¹ * w.val⁻¹ := by
    rw [← hxw, IntMod.val_mul, IntMod.val_inv, convI_apply_val]
  have hzVg : z.val ∈ conjSubgroup (fsuV T I) g := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hwA₁.2 (a : G)⁻¹).mp
      ((conjSubgroup (fsuV T I) g).inv_mem haA.1)
    have h2 := (conjSubgroup (fsuV T I) g).mul_mem haA.1 h1
    rw [hzval]
    convert h2 using 1
    group
  have hzI : ∃ x ∈ T, z.val ∈ CFSG.conjugate I x := by
    rcases hzV with h | h
    · refine ⟨1, T.one_mem, ?_⟩
      rw [mem_conjugate_iff']
      have h' : z.val ∈ I := mem_intSub.mp h
      simpa using h'
    · refine ⟨t, htT, ?_⟩
      rw [hmapφ] at h
      exact mem_intSub.mp h
  have hr2 : (2 : ℕ∞) < rParam (fsuV T I) := by
    rw [hr]
    exact_mod_cast (show (2 : ℕ) < 3 by norm_num)
  have hchar : QuasithinUnique.CharTwo (Subgroup.centralizer ({z.val} : Set G)) := by
    obtain ⟨x, hxT, hzx⟩ := hzI
    exact h772 G T L I hyp h731 inferInstance hrow' hr2 x hxT z.val hzx hzG1
  have hQG1 : pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) ≤
      Subgroup.centralizer ({z.val} : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hQp : IsPGroup 2 (pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hG1Q : Subgroup.centralizer ({z.val} : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hG1eq : Subgroup.normalizer ((Subgroup.zpowers z.val : Subgroup G) : Set G) =
      Subgroup.centralizer ({z.val} : Set G) :=
    normalizer_zpowers_eq_centralizer hzz hzG1
  have hUV : Subgroup.zpowers z.val ≤ fsuV T I := Subgroup.zpowers_le.mpr hzGV
  have hQN : pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) ≤
      Subgroup.normalizer (fsuV T I : Set G) := by
    have hodd := h3104 G T L I (fsuV T I) hyp.fsu hVp hJ (Subgroup.zpowers z.val) hUV
    rw [hG1eq] at hodd
    obtain ⟨S, hS, -⟩ := exists_isSylowIn_ge 2
      (bot_le : (⊥ : Subgroup G) ≤ fsuM T L ⊓ Subgroup.centralizer ({z.val} : Set G))
      IsPGroup.of_bot
    have hS' : IsSylowIn 2 S (Subgroup.centralizer ({z.val} : Set G)) :=
      isSylowIn_of_odd hS inf_le_right hodd
    exact (pCoreOf_le_of_isSylowIn hS').trans (hS.le.trans (inf_le_left.trans hVM))
  have hVG1 : fsuV T I ≤ Subgroup.centralizer ({z.val} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hV.1.is_comm.comm ⟨v, hv⟩ ⟨z.val, hzGV⟩))
  have hpres : ∀ n : G, ∀ hn : n ∈ Subgroup.normalizer (fsuV T I : Set G),
      n ∈ Subgroup.centralizer ({z.val} : Set G) →
      (∀ v ∈ Vi, convI hV ⟨n, hn⟩ v ∈ Vi) ∧ ∀ y ∈ Y, convI hV ⟨n, hn⟩ y ∈ Y := by
    intro n hn hnG1
    refine hnorm _ (autI_top_le_normalizer hV hNM (convI_mem_autI hV (Subgroup.mem_top _) hn)) ?_
    apply IntMod.val_injective
    rw [convI_apply_val]
    have h := Subgroup.mem_centralizer_singleton_iff.mp hnG1
    change n * z.val * n⁻¹ = z.val
    rw [h, mul_inv_cancel_right]
  have hnormG : ∀ n : G, n ∈ Subgroup.normalizer (fsuV T I : Set G) →
      n ∈ Subgroup.centralizer ({z.val} : Set G) →
      n ∈ Subgroup.normalizer ((Vi.map (E3.valHom hV) : Subgroup G) : Set G) ∧
        n ∈ Subgroup.normalizer ((Y.map (E3.valHom hV) : Subgroup G) : Set G) := by
    intro n hn hnG1
    have h1 := hpres n hn hnG1
    have h2 := hpres n⁻¹ (Subgroup.inv_mem _ hn) (Subgroup.inv_mem _ hnG1)
    exact ⟨mem_normalizer_map_valHom hV hn h1.1 h2.1, mem_normalizer_map_valHom hV hn h1.2 h2.2⟩
  have hT'p : IsPGroup 2 ↥(pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) ⊔ fsuV T I) :=
    IsPGroup.to_sup_of_normal_left' hQp hpV (hVG1.trans hG1Q)
  have hT'NG : pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) ⊔ fsuV T I ≤
      Subgroup.normalizer (fsuV T I : Set G) ⊓ Subgroup.centralizer ({z.val} : Set G) :=
    sup_le (le_inf hQN hQG1) (le_inf Subgroup.le_normalizer hVG1)
  have hzZ : ∀ g' ∈ Subgroup.centralizer ({z.val} : Set G), ∀ z' ∈ Subgroup.zpowers z.val,
      g' * z' * g'⁻¹ = z' := by
    intro g' hg' z' hz'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    have h := Subgroup.mem_centralizer_singleton_iff.mp hg'
    have hgz : g' * z.val * g'⁻¹ = z.val := by rw [h, mul_inv_cancel_right]
    rw [← conj_zpow, hgz]
  have hmemQ : ∀ x ∈ Subgroup.centralizer ({z.val} : Set G),
      (∀ q ∈ pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)),
        x * q * x⁻¹ * q⁻¹ ∈ Subgroup.zpowers z.val) →
      x ∈ pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) := fun x hx hxq =>
    mem_pCoreOf_of_comm_mod_central (isPGroup_zpowers_of_mul_self hzz) hzZ hchar hx hxq
  have hzQ : z.val ∈ pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) :=
    hmemQ z.val (Subgroup.mem_centralizer_singleton_iff.mpr rfl) fun q hq => by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hQG1 hq)
      rw [← h, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hinvQ : ∀ {U : Subgroup (IntMod (fsuV T I) hV)},
      (∀ n : G, ∀ hn : n ∈ Subgroup.normalizer (fsuV T I : Set G),
        n ∈ Subgroup.centralizer ({z.val} : Set G) → ∀ u ∈ U, convI hV ⟨n, hn⟩ u ∈ U) →
      ∀ h ∈ autI hV (fsuL0 T L), h z = z → ∀ u ∈ U ⊓ intSub hV
        (pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G))),
        h u ∈ U ⊓ intSub hV (pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G))) := by
    intro U hU h hh hhz u hu
    obtain ⟨ℓ, -, rfl⟩ := (mem_autI hV).1 hh
    have hℓG1 : (ℓ : G) ∈ Subgroup.centralizer ({z.val} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg IntMod.val hhz
      rw [convI_apply_val] at h1
      calc (ℓ : G) * z.val = (ℓ : G) * z.val * (ℓ : G)⁻¹ * ℓ := by group
        _ = z.val * ℓ := by rw [h1]
    refine Subgroup.mem_inf.mpr ⟨hU ℓ ℓ.2 hℓG1 u hu.1, ?_⟩
    rw [mem_intSub, convI_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (hG1Q hℓG1) u.val).mp (mem_intSub.mp hu.2)
  have hViG_le : Vi.map (E3.valHom hV) ≤ fsuV T I := E3.map_valHom_le hV Vi
  have hlt1 : Subgroup.zpowers z.val < Vi.map (E3.valHom hV) := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr ⟨z, hzVi, rfl⟩) fun h => hViz ?_
    intro v hv
    have h1 : E3.valHom hV v ∈ Subgroup.zpowers z.val := by
      rw [h]
      exact ⟨v, hv, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, E3.valHom_injective hV ?_⟩
    rw [map_zpow]
    exact hk
  obtain ⟨v, hvVi, hvz, hvfix⟩ := CFSG.Quasithin.exists_fixed_mod hT'p
    (hViG_le.trans le_sup_right) hlt1
    (fun n hn => (hnormG n (hT'NG hn).1 (hT'NG hn).2).1)
    (fun n hn => by rw [hG1eq]; exact (hT'NG hn).2)
  have hvQ : v ∈ pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) :=
    hmemQ v (hVG1 (hViG_le hvVi)) fun q hq => by
      have h := hvfix q (Subgroup.mem_sup_left hq)
      have e : v * q * v⁻¹ * q⁻¹ = (q * v * q⁻¹ * v⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ h
  have hViQ : Vi.map (E3.valHom hV) ≤ pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) := by
    have hJ1 : Vi ⊓ intSub hV (pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G))) = Vi := by
      refine hIrr1 _ inf_le_left ⟨hzVi, mem_intSub.mpr hzQ⟩ ?_
        (hinvQ fun n hn hnG1 => (hpres n hn hnG1).1)
      intro hle
      obtain ⟨u, hu, rfl⟩ := hvVi
      apply hvz
      have hu' : u ∈ Subgroup.zpowers z := hle ⟨hu, mem_intSub.mpr hvQ⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu'
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk, map_zpow, E3.valHom_apply]⟩
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ Vi ⊓ intSub hV (pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G))) := by
      rw [hJ1]
      exact hu
    exact mem_intSub.mp hu'.2
  have hYG_le : Y.map (E3.valHom hV) ≤ fsuV T I := E3.map_valHom_le hV Y
  have hYG0 : Y.map (E3.valHom hV) ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective Y (E3.valHom_injective hV)).not.mpr hY0
  obtain ⟨y, hyY, hy1, hyfix⟩ := CFSG.Quasithin.exists_fixed_mod hT'p
    (hYG_le.trans le_sup_right) (bot_lt_iff_ne_bot.mpr hYG0)
    (fun n hn => (hnormG n (hT'NG hn).1 (hT'NG hn).2).2)
    (fun n _ => QuadPair.mem_normalizer_bot n)
  have hyQ : y ∈ pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) :=
    hmemQ y (hVG1 (hYG_le hyY)) fun q hq => by
      have h := hyfix q (Subgroup.mem_sup_left hq)
      rw [Subgroup.mem_bot] at h
      have e : y * q * y⁻¹ * q⁻¹ = (q * y * q⁻¹ * y⁻¹)⁻¹ := by group
      rw [e, h, inv_one]
      exact Subgroup.one_mem _
  have hYQ : Y.map (E3.valHom hV) ≤ pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) := by
    have hJ2 : Y ⊓ intSub hV (pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G))) = Y := by
      refine hIrr2 _ inf_le_left ?_ (hinvQ fun n hn hnG1 => (hpres n hn hnG1).2)
      intro hbot
      obtain ⟨u, hu, rfl⟩ := hyY
      apply hy1
      have hu' : u ∈ Y ⊓ intSub hV (pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G))) :=
        ⟨hu, mem_intSub.mpr hyQ⟩
      rw [hbot, Subgroup.mem_bot] at hu'
      rw [hu', map_one]
      exact Subgroup.one_mem _
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ Y ⊓ intSub hV (pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G))) := by
      rw [hJ2]
      exact hu
    exact mem_intSub.mp hu'.2
  have hA₁Q : fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) := by
    rw [← hWeq]
    intro x hx
    have h1 := Subgroup.map_mono (f := E3.valHom hV) hWle hx
    rw [Subgroup.map_sup] at h1
    exact (sup_le hViQ hYQ) h1
  have hVQ : ¬ fsuV T I ≤ pCoreOf 2 (Subgroup.centralizer ({z.val} : Set G)) := by
    intro hle
    apply hg.1
    refine h3106 G T L I (fsuV T I) hyp.fsu hVp hJ (Subgroup.zpowers z.val) hUV
      (by rw [hG1eq]; exact hle) (not_isFFStarOffender_autOn h37 h38 h39 hyp hV hN) g
      (Subgroup.zpowers_le.mpr hzVg)
  have hpair : ∀ h : G, h ∈ Subgroup.centralizer ({z.val} : Set G) →
      IsPGroup 2 ↥(fsuV T I ⊔ conjSubgroup (fsuV T I) h) := by
    intro h hh
    have hpVh : IsPGroup 2 (conjSubgroup (fsuV T I) h) := isPGroup_conjSubgroup hpV h
    by_cases hN' : conjSubgroup (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G)
    · exact IsPGroup.to_sup_of_normal_left' hpV hpVh hN'
    · have hA₁h : conjSubgroup (fsuV T I ⊓ Subgroup.normalizer
          (conjSubgroup (fsuV T I) g : Set G)) h ≤
          conjSubgroup (fsuV T I) h ⊓ Subgroup.normalizer (fsuV T I : Set G) := by
        refine le_inf (conjSubgroup_mono_left h inf_le_left) fun x hx => hQN ?_
        rw [mem_conjSubgroup_iff] at hx
        have h2 := (Subgroup.mem_normalizer_iff.mp (hG1Q (Subgroup.inv_mem _ hh)) _).mp
          (hA₁Q hx)
        simpa [mul_assoc] using h2
      have hmh : mQuot (conjSubgroup (fsuV T I) h)
          (conjSubgroup (fsuV T I) h ⊓ Subgroup.normalizer (fsuV T I : Set G)) = 1 := by
        have h1 := mQuot_mono (V := conjSubgroup (fsuV T I) h) hA₁h
        rw [mQuot_conjSubgroup, hm1] at h1
        have h2 : mQuot (conjSubgroup (fsuV T I) h)
            (conjSubgroup (fsuV T I) h ⊓ Subgroup.normalizer (fsuV T I : Set G)) ≠ 0 := by
          intro h0
          apply hN'
          rw [← (mQuot_eq_zero_iff hpVh inf_le_left).mp h0]
          exact inf_le_right
        omega
      have hwoff : IsWOffenderAt T (fsuV T I) h := by
        refine ⟨fun hc => hN' ?_, by simp [hw, hmh]⟩
        exact (Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)).trans
            (Subgroup.centralizer_le_normalizer _)
      exact isPGroup_sup_conj_761 h37 h38 h39 hmod h734 h771 hyp h731 hrow' hV hwoff
  have hXp : IsPGroup 2 ↥((fsuV T I).subgroupOf (Subgroup.centralizer ({z.val} : Set G))) :=
    hpV.of_equiv (Subgroup.subgroupOfEquivOfLe hVG1).symm
  rcases baer_suzuki_subgroup hXp with hXO | ⟨h, hh⟩
  · exact hVQ fun v hv => ⟨⟨v, hVG1 hv⟩, hXO (show (⟨v, hVG1 hv⟩ :
      ↥(Subgroup.centralizer ({z.val} : Set G))) ∈
        (fsuV T I).subgroupOf (Subgroup.centralizer ({z.val} : Set G)) from hv), rfl⟩
  · apply hh
    have hK' : IsPGroup 2 ↥((fsuV T I ⊔ conjSubgroup (fsuV T I) (h : G)).subgroupOf
        (Subgroup.centralizer ({z.val} : Set G))) := (hpair h h.2).comap_subtype
    refine hK'.to_le (sup_le ?_ ?_)
    · intro x hx
      exact Subgroup.mem_sup_left (show (x : G) ∈ fsuV T I from hx)
    · intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have hy' : (h : G) * y * (h : G)⁻¹ ∈ fsuV T I := hy
      exact Subgroup.mem_sup_right (mem_conjSubgroup_iff.mpr hy')

end CFSG.Quasithin.H13
