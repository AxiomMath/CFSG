module

public import CFSG.Quasithin.H13.L32ACL34G
public import CFSG.Quasithin.H13.L32AC42a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem exists_conj_mem_of_isSylowTwoOf {Y : Type*} [Group Y] [Finite Y] {X P : Subgroup Y}
    (hP : IsSylowTwoOf P X) {s : Y} (hs : s ∈ X) (h2 : ∃ k : ℕ, s ^ 2 ^ k = 1) :
    ∃ y ∈ X, y⁻¹ * s * y ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2
  have hQ2 : IsPGroup 2 ↥(P.subgroupOf X) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have hQi : ¬ 2 ∣ (P.subgroupOf X).index := hP.2.2
  let PS : Sylow 2 ↥X := hQ2.toSylow hQi
  have hZ : IsPGroup 2 ↥(Subgroup.zpowers (⟨s, hs⟩ : ↥X)) := by
    rintro ⟨z, hz⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, SubgroupClass.coe_zpow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq ↥X S' PS
  have hmem : n * ⟨s, hs⟩ * n⁻¹ ∈ (PS : Subgroup ↥X) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (Subgroup.mem_zpowers _))
  refine ⟨((n⁻¹ : ↥X) : Y), (n⁻¹ : ↥X).2, ?_⟩
  have h1 : ((n * ⟨s, hs⟩ * n⁻¹ : ↥X) : Y) ∈ P := hmem
  simpa using h1

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem center_kb_eq_bot_of_oddCore {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (cStar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hO : CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥) :
    Subgroup.center ↥(modO2Image H K) = ⊥ := by
  set Kb := modO2Image H K with hKb
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKbN : Kb.Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn).map _
      (QuotientGroup.mk'_surjective _)
  obtain ⟨-, hodd, -⟩ := kst_props hK hq hLie
  set Z : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := (Subgroup.center ↥Kb).map Kb.subtype with hZ
  have hZn : Z.Normal := by
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨z', hz', rfl⟩ := hz
    refine ⟨⟨g * z' * g⁻¹, hKbN.conj_mem _ z'.2 g⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    apply Subtype.ext
    have hy : g⁻¹ * (y : ↥H ⧸ CFSG.pCore 2 ↥H) * g ∈ Kb := by
      simpa using hKbN.conj_mem _ y.2 g⁻¹
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at h1 ⊢
    calc (y : ↥H ⧸ CFSG.pCore 2 ↥H) * (g * z' * g⁻¹) = g * (g⁻¹ * y * g * z') * g⁻¹ := by group
      _ = g * (z' * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * z' * g⁻¹ * y := by group
  have hZodd : Odd (Nat.card Z) := by
    rwa [hZ, Subgroup.card_map_of_injective Kb.subtype_injective]
  have hZ1 : Z = ⊥ := by
    have hle : Z ≤ CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) := le_sSup ⟨hZn, hZodd⟩
    rwa [hO, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro z hz
  have : (z : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Z := ⟨z, hz, rfl⟩
  rw [hZ1, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (Subtype.ext this)

theorem false_of_l1_star_le_centralizer (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (cStar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHeq : H = K ⊔ (l1 T L V ⊔ T)) (hl1K : ¬ l1 T L V ≤ K)
    (hO : CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥)
    (hc : modO2Image H (l1 T L V) ≤
      Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) : False := by
  have C : Hyp42 T L V H K := ⟨S, hK, hq, hKn, hHeq, hl1K, hc⟩
  have hcard := C.card_lb h1222 h1332 h1334
  have hle : modO2Image H (l1 T L V) ≤ CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) :=
    le_sSup ⟨C.lbNormal h1332, by rw [hcard]; decide⟩
  rw [hO, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hcard
  omega

theorem isPSL_kb {K : Subgroup G} (hK : K ∈ cComp H)
    (hP : IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K)))
    (hZ : Subgroup.center ↥(modO2Image H K) = ⊥) : IsPSL 3 2 2 ↥(modO2Image H K) := by
  obtain ⟨φ⟩ := nonempty_cStar_equiv_kst (H := H) hK
  have h1 := isPSL_congr (centerQuotEquiv φ) hP
  exact isPSL_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) h1

theorem exists_t_move (hN1 : LieSylowOver3) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hq : CFSG.IsQuasisimple (cStar K))
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHeq : H = K ⊔ (l1 T L V ⊔ T)) {n : ℕ}
    (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hl1K : ¬ l1 T L V ≤ K) (hO : CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥)
    (hP : IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K))) [(modO2Image H K).Normal] :
    ∃ t : ↥H, (t : G) ∈ T ∧ ∃ Q : Subgroup ↥(modO2Image H K),
      Q ≤ (szS1 T H K).subgroupOf (modO2Image H K) ∧ IsElemAbelian 2 Q ∧ Nat.card Q = 16 ∧
      Q.map (MulAut.conjNormal (QuotientGroup.mk' (CFSG.pCore 2 ↥H) t) :
        MulAut ↥(modO2Image H K)).toMonoidHom ≠ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb := modO2Image H K with hKb
  have hTH : T ≤ H := Setting147.TH' S
  have hl1H : l1 T L V ≤ H := Setting147.l1H' S
  have hS := isSylowIn_szS1_of S hK
  have hN1' := l1T_le_normalizer_szS1' hN1 h1222 h1332 h1334 S hK hq hKn hn hLie
  obtain ⟨mx, hmxL, ms, hmsLT, hx3, -, ⟨ks, hks⟩, hsx, hxB, hsB, hxN⟩ :=
    exists_inv_pair_borel hN1 h29 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K
  have hmxLT : mx ∈ modO2Image H (l1 T L V ⊔ T) := by
    obtain ⟨a, ha, hae⟩ := mem_modO2Image'.mp hmxL
    exact mem_modO2Image'.mpr ⟨a, Subgroup.mem_sup_left ha, hae⟩
  obtain ⟨hqX, hoddX, -⟩ := kst_props hK hq hLie
  have hZ := center_kb_eq_bot_of_oddCore hK hq hKn hLie hO
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
  have hβi : β ∉ (MulAut.conj : ↥Kb →* MulAut ↥Kb).range := by
    rintro ⟨k, hk⟩
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
    exact false_of_l1_star_le_centralizer h1222 h1332 h1334 S hK hq hKn hHeq hl1K hO
      (hxN _ (Subgroup.normal_centralizer) hxC)
  obtain ⟨Q₀, hQ₀S, hQ₀e, hQ₀c, hQ₀α⟩ := lieL34GraphMove_holds ↥Kb (isPSL_kb hK hP hZ) SX
    (isSylowTwoOf_subgroupOf hS) α β hα2 hβ3 hαS hβS hαβ hαB hβB hβi
  obtain ⟨s, hsLT, rfl⟩ := mem_modO2Image'.mp hmsLT
  have hs2 : ∃ k : ℕ, (s : G) ^ 2 ^ k = 1 := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (s ^ 2 ^ ks) = 1 := by rw [map_pow, hks]
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 H) ⟨_, (mk_pCore_eq_one_iff _).mp h1⟩
    refine ⟨ks + m, ?_⟩
    have hm' : (((s : G) ^ 2 ^ ks) ^ 2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    rw [pow_add, pow_mul, hm']
  have hTsyl : IsSylowTwoOf T (l1 T L V ⊔ T) := by
    have hT := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
    refine ⟨le_sup_right, hT.2.1, fun h2 => hT.2.2 ?_⟩
    have hmul := Subgroup.relIndex_mul_relIndex T (l1 T L V ⊔ T) H le_sup_right (sup_le hl1H hTH)
    exact h2.trans (Dvd.intro _ hmul)
  obtain ⟨y, hyLT, hyT⟩ := exists_conj_mem_of_isSylowTwoOf hTsyl hsLT hs2
  have hyH : y ∈ H := sup_le hl1H hTH hyLT
  set my := QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨y, hyH⟩ : ↥H) with hmy
  have hmyN : my ∈ Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    hN1' (mem_modO2Image'.mpr ⟨_, hyLT, rfl⟩)
  have hmyN' : my⁻¹ ∈ Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    inv_mem hmyN
  refine ⟨⟨y, hyH⟩⁻¹ * s * ⟨y, hyH⟩, by simpa using hyT, Q₀.map (MulAut.conjNormal my⁻¹ :
    MulAut ↥Kb).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono hQ₀S).trans (map_conjNormal_szS1 hmyN').le
  · exact isElemAbelian_map_mulEquiv _ hQ₀e
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conjNormal my⁻¹ : MulAut ↥Kb).toMonoidHom)
      (MulAut.conjNormal my⁻¹ : MulAut ↥Kb).injective, hQ₀c]
  · intro h
    apply hQ₀α
    have e : (MulAut.conjNormal (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
        (⟨y, hyH⟩⁻¹ * s * ⟨y, hyH⟩)) : MulAut ↥Kb) =
        MulAut.conjNormal my⁻¹ * α * MulAut.conjNormal my := by
      rw [hα, hmy]
      simp only [map_mul, map_inv]
    have hc : ∀ q : ↥Kb,
        (MulAut.conjNormal my : MulAut ↥Kb) ((MulAut.conjNormal my⁻¹ : MulAut ↥Kb) q) = q := by
      intro q
      simp [map_inv]
    have hcomp : (MulAut.conjNormal my⁻¹ * α * MulAut.conjNormal my : MulAut ↥Kb).toMonoidHom.comp
        (MulAut.conjNormal my⁻¹ : MulAut ↥Kb).toMonoidHom =
        (MulAut.conjNormal my⁻¹ : MulAut ↥Kb).toMonoidHom.comp α.toMonoidHom := by
      ext q
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.mul_apply, hc]
    rw [e, Subgroup.map_map, hcomp, ← Subgroup.map_map] at h
    exact Subgroup.map_injective (f := (MulAut.conjNormal my⁻¹ : MulAut ↥Kb).toMonoidHom)
      (MulAut.conjNormal my⁻¹ : MulAut ↥Kb).injective h

end CFSG.Quasithin.H13.L32A.C
