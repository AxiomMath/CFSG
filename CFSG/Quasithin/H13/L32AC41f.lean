module

public import CFSG.Quasithin.H13.L32AC41e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem conj_map_eq {X : Type*} [Group X] (α : MulAut X) (k : X) :
    MulAut.conj (α k) = α * MulAut.conj k * α⁻¹ := by
  ext y
  simp [MulAut.mul_apply]

theorem mem_center_of_conj_eq_one {X : Type*} [Group X] {k : X} (h : MulAut.conj k = 1) :
    k ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro y
  have := congrArg (fun φ : MulAut X => φ y) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  exact (mul_inv_eq_iff_eq_mul.mp this).symm

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem exists_inv_pair_borel (hN1 : LieSylowOver3) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hq : CFSG.IsQuasisimple (cStar K))
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 1 < n)
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) (hl1K : ¬ l1 T L V ≤ K) :
    ∃ mx ∈ modO2Image H (l1 T L V), ∃ ms ∈ modO2Image H (l1 T L V ⊔ T),
      mx ^ 3 = 1 ∧ mx ≠ 1 ∧ (∃ k : ℕ, ms ^ 2 ^ k = 1) ∧ ms * mx * ms⁻¹ = mx⁻¹ ∧
      (∀ b ∈ szB1 T H K, mx * b * mx⁻¹ * b⁻¹ ∈ szS1 T H K) ∧
      (∀ b ∈ szB1 T H K, ms * b * ms⁻¹ * b⁻¹ ∈ szS1 T H K) ∧
      ∀ N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), N.Normal → mx ∈ N →
        modO2Image H (l1 T L V) ≤ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := Setting147.TH' S
  have hl1H : l1 T L V ≤ H := Setting147.l1H' S
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨ψ, hψ⟩ := S14.exists_rep
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf S.hyp hMod h1222 h1332 h1334
  obtain ⟨t, htT, htL, htn⟩ := exists_TL_not_triv S.hyp h1332 S14
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hx : x ∈ l1 T L V := hl1 ▸ hxL
  have hxH : x ∈ H := hl1H hx
  have htH : t ∈ H := hTH htT
  have hxX := S14.L1_le_X hxL
  have htX := S14.T_le_X htT
  have hxLL : x ∈ L := (oTwoUpper_le _ hx).1
  have hl1X : l1 T L V ≤ L32NSet14.nX T V := hl1 ▸ S14.L1_le_X
  have hψt : ψ ⟨t, htX⟩ ≠ 1 := fun h => htn ((hψ _).mp h)
  have hψt2 : ψ ⟨t, htX⟩ ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨t, htT⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have : (⟨t, htX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hψx : ψ ⟨x, hxX⟩ ≠ 1 := by
    intro h
    have hxt := (hψ _).mp h
    have hle : V ≤ fsuV1 T V := fun v hv => hfpf v hv ((L32NSet14.mem_trivSub.mp hxt).2.2 v hv)
    have := Subgroup.card_le_of_le hle
    rw [S14.card_V, S14.card_V1] at this
    omega
  have hψx3 : ψ ⟨x, hxX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥(L32NSet14.nX T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hsolv := isSolvable_szB1_l1T' hN1 h1222 h1332 h1334 S hK hq hKn hn hLie
  have hBL : ∀ β : ↥H, QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K →
      (β : G) ∈ Subgroup.normalizer (L : Set G) := fun β hβ =>
    mem_normalizer_L_of_solvable h29 S hsolv le_sup_right (Subgroup.mem_sup_left hβ)
  have hBX : ∀ β : ↥H, QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K →
      (β : G) ∈ L32NSet14.nX T V := fun β hβ => mem_nX_of h1332 h1334 S β.2 (hBL β hβ)
  have hBψ : ∀ (β : ↥H) (hβ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K),
      ψ ⟨β, hBX β hβ⟩ = 1 := fun β hβ =>
    psi_eq_one_of_mem S S14 hψ hK hKn hl1K hxLL hxX hxH hψx hψx3 htL htX htH hψt hψt2
      (hBX β hβ) (hBL β hβ) β.2 hβ.2
  obtain ⟨s, hsL, hsLT, ⟨ks, hks⟩, hsx⟩ :=
    exists_inv_s h1222 h1332 h1334 S S14 hx hxX hψx hx3 htT htL htX hψt
  have hsH : s ∈ H := sup_le hl1H hTH hsLT
  have hsX : s ∈ L32NSet14.nX T V := sup_le hl1X S14.T_le_X hsLT
  have hcomm : ∀ (y : G) (hyL : y ∈ L) (hyX : y ∈ L32NSet14.nX T V) (hyH : y ∈ H),
      ∀ b ∈ szB1 T H K, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * b *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹ * b⁻¹ ∈ szS1 T H K := by
    intro y hyL hyX hyH b hb
    obtain ⟨β, -, rfl⟩ := mem_modO2Image'.mp hb.2
    have h1 := comm_mem_szS1_of_psi S S14 hψ hK hKn hyL hyX hyH (hBX β hb) (hBL β hb) β.2 hb.2
      (hBψ β hb)
    simpa only [map_mul, map_inv] using h1
  refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩, mem_modO2Image'.mpr ⟨⟨x, hxH⟩, hx, rfl⟩,
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨s, hsH⟩, mem_modO2Image'.mpr ⟨⟨s, hsH⟩, hsLT, rfl⟩,
    ?_, ?_, ⟨ks, ?_⟩, ?_, hcomm x hxLL hxX hxH, hcomm s hsL hsX hsH, ?_⟩
  · rw [← map_pow]
    have : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  · intro h
    have hxO : x ∈ pCoreOf 2 H := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
        Subgroup.mem_subgroupOf] at h
    exact hψx ((hψ _).mpr (pCoreOf_le_trivSub S S14 hxO))
  · rw [← map_pow]
    have : (⟨s, hsH⟩ : ↥H) ^ 2 ^ ks = 1 := Subtype.ext (by simpa using hks)
    rw [this, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using hsx)
  · intro N hN hxN
    exact l1_star_le_of_psi_eq S S14 hψ hN hxX hψx hψx3 hxLL hxX hxH hxN rfl

theorem map_conjNormal_szS1 {K : Subgroup G} [(modO2Image H K).Normal]
    {g : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hg : g ∈ Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    ((szS1 T H K).subgroupOf (modO2Image H K)).map
      (MulAut.conjNormal g : MulAut ↥(modO2Image H K)).toMonoidHom =
      (szS1 T H K).subgroupOf (modO2Image H K) := by
  have hle : ((szS1 T H K).subgroupOf (modO2Image H K)).map
      (MulAut.conjNormal g : MulAut ↥(modO2Image H K)).toMonoidHom ≤
      (szS1 T H K).subgroupOf (modO2Image H K) := by
    rintro _ ⟨k, hk, rfl⟩
    show ((MulAut.conjNormal g k : ↥(modO2Image H K)) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ szS1 T H K
    rw [MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hk
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective
      (f := (MulAut.conjNormal g : MulAut ↥(modO2Image H K)).toMonoidHom)
      (MulAut.conjNormal g : MulAut ↥(modO2Image H K)).injective])

theorem conjNormal_mul_inv_mem (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    [(modO2Image H K).Normal] {g : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hg : ∀ b ∈ szB1 T H K, g * b * g⁻¹ * b⁻¹ ∈ szS1 T H K) :
    ∀ b ∈ Subgroup.normalizer
        (((szS1 T H K).subgroupOf (modO2Image H K) : Subgroup ↥(modO2Image H K)) :
          Set ↥(modO2Image H K)),
      (MulAut.conjNormal g : MulAut ↥(modO2Image H K)) b * b⁻¹ ∈
        (szS1 T H K).subgroupOf (modO2Image H K) := by
  intro b hb
  have hS := isSylowIn_szS1_of S hK
  have hbB : (b : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ szB1 T H K :=
    ⟨(mem_normalizer_subgroupOf_iff hS.le b).mp hb, b.2⟩
  show ((MulAut.conjNormal g b * b⁻¹ : ↥(modO2Image H K)) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
    szS1 T H K
  rw [Subgroup.coe_mul, MulAut.conjNormal_apply, Subgroup.coe_inv]
  exact hg _ hbB

theorem l1_star_le_centralizer (hN1 : LieSylowOver3) (hN3 : LieBorelThreeInner)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (cStar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hl1K : ¬ l1 T L V ≤ K) (hP : ¬ IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K))) :
    modO2Image H (l1 T L V) ≤
      Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb := modO2Image H K with hKb
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hS := isSylowIn_szS1_of S hK
  have hKbN : Kb.Normal := by
    have : (K.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
    exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)
  have hN1' := l1T_le_normalizer_szS1' hN1 h1222 h1332 h1334 S hK hq hKn hn hLie
  obtain ⟨mx, hmxL, ms, hmsLT, hx3, -, ⟨ks, hks⟩, hsx, hxB, hsB, hxN⟩ :=
    exists_inv_pair_borel hN1 h29 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K
  have hmxLT : mx ∈ modO2Image H (l1 T L V ⊔ T) := by
    obtain ⟨a, ha, hae⟩ := mem_modO2Image'.mp hmxL
    exact mem_modO2Image'.mpr ⟨a, Subgroup.mem_sup_left ha, hae⟩
  obtain ⟨hqX, hoddX, hLieX⟩ := kst_props hK hq hLie
  set SX := (szS1 T H K).subgroupOf Kb with hSX
  set α : MulAut ↥Kb := MulAut.conjNormal ms with hα
  set β : MulAut ↥Kb := MulAut.conjNormal mx with hβ
  have hα2 : ∃ k : ℕ, α ^ 2 ^ k = 1 := ⟨ks, by rw [hα, ← map_pow, hks, map_one]⟩
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hx3, map_one]
  have hαS : SX.map α.toMonoidHom = SX := map_conjNormal_szS1 (hN1' hmsLT)
  have hβS : SX.map β.toMonoidHom = SX := map_conjNormal_szS1 (hN1' hmxLT)
  have hαβ : α * β * α⁻¹ = β⁻¹ := by
    rw [hα, hβ, ← map_inv, ← map_mul, ← map_mul, hsx, map_inv]
  have hαB := conjNormal_mul_inv_mem S hK hsB
  have hβB := conjNormal_mul_inv_mem S hK hxB
  rcases hN3 (↥Kb) n hn hqX hoddX hLieX SX (isSylowTwoOf_subgroupOf hS) α β hα2 hβ3 hαS hβS
    hαβ hαB hβB with hinner | hpsl
  swap
  · exfalso
    obtain ⟨φ⟩ := nonempty_cStar_equiv_kst (H := H) hK
    exact hP (isPSL_congr (centerQuotEquiv φ).symm hpsl)
  obtain ⟨k, hk⟩ := hinner
  have hkN : k ∈ Subgroup.normalizer (SX : Set ↥Kb) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have : MulAut.conj k y ∈ SX.map β.toMonoidHom := ⟨y, hy, by rw [← hk]; rfl⟩
    rw [hβS] at this
    exact this
  have hk3 : k ^ 3 ∈ Subgroup.center ↥Kb := by
    refine mem_center_of_conj_eq_one ?_
    rw [map_pow, hk, hβ3]
  have hak : α k * k ∈ Subgroup.center ↥Kb := by
    refine mem_center_of_conj_eq_one ?_
    rw [map_mul, conj_map_eq, hk, hαβ, inv_mul_cancel]
  have hkZ : k ∈ Subgroup.center ↥Kb :=
    mem_center_of_inv_mod hoddX (isSylowTwoOf_subgroupOf hS).2.1 hk3 hak (hαB k hkN)
  have hβ1 : β = 1 := by
    rw [← hk]
    ext y
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [(Subgroup.mem_center_iff.mp hkZ y).symm, mul_inv_cancel_right]
  have hxC : mx ∈ Subgroup.centralizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := congrArg (fun φ : MulAut ↥Kb => ((φ ⟨y, hy⟩ : ↥Kb) : ↥H ⧸ CFSG.pCore 2 ↥H)) hβ1
    simp only [hβ, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc y * mx = mx * y * mx⁻¹ * mx := by rw [this]
      _ = mx * y := by group
  exact hxN _ (Subgroup.normal_centralizer) hxC

end CFSG.Quasithin.H13.L32A.C
