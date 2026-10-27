module

public import CFSG.Quasithin.Vol2.Ch12Sec6L13a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

theorem comm_mul_central {G : Type*} [Group G] {a b c₁ c₂ : G} (h1a : c₁ * a = a * c₁)
    (h1b : c₁ * b = b * c₁) (h2a : c₂ * a = a * c₂) (h2b : c₂ * b = b * c₂)
    (h12 : c₁ * c₂ = c₂ * c₁) :
    (c₁ * a) * (c₂ * b) * (c₁ * a)⁻¹ * (c₂ * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have k1 : c₁ * (b * c₂) * c₁⁻¹ = b * c₂ := by
    rw [mul_inv_eq_iff_eq_mul, ← mul_assoc, h1b, mul_assoc, h12, ← mul_assoc]
  have k2' : c₂ * a⁻¹ = a⁻¹ * c₂ := by
    calc c₂ * a⁻¹ = a⁻¹ * (a * c₂) * a⁻¹ := by group
      _ = a⁻¹ * (c₂ * a) * a⁻¹ := by rw [h2a]
      _ = a⁻¹ * c₂ := by group
  have k2 : c₂ * a⁻¹ * c₂⁻¹ = a⁻¹ := by rw [k2', mul_inv_cancel_right]
  calc (c₁ * a) * (c₂ * b) * (c₁ * a)⁻¹ * (c₂ * b)⁻¹ =
      (a * c₁) * (b * c₂) * (a * c₁)⁻¹ * (b * c₂)⁻¹ := by rw [h1a, h2b]
    _ = a * (c₁ * (b * c₂) * c₁⁻¹) * a⁻¹ * c₂⁻¹ * b⁻¹ := by group
    _ = a * (b * c₂) * a⁻¹ * c₂⁻¹ * b⁻¹ := by rw [k1]
    _ = a * b * (c₂ * a⁻¹ * c₂⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [k2]

theorem mem_centralizer_of_comm_mem_center {G : Type*} [Group G] {K : Subgroup G}
    (hK : ⁅K, K⁆ = K) {y : G}
    (hy : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ K ⊓ Subgroup.centralizer (K : Set G)) :
    y ∈ Subgroup.centralizer (K : Set G) := by
  have hle : ⁅K, K⁆ ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨h1K, h1C⟩ := hy a ha
    obtain ⟨h2K, h2C⟩ := hy b hb
    have c1 := Subgroup.mem_centralizer_iff.1 h1C
    have c2 := Subgroup.mem_centralizer_iff.1 h2C
    have hc : y * ⁅a, b⁆ * y⁻¹ = ⁅a, b⁆ := by
      have e : y * ⁅a, b⁆ * y⁻¹ = ((y * a * y⁻¹ * a⁻¹) * a) * ((y * b * y⁻¹ * b⁻¹) * b) *
          ((y * a * y⁻¹ * a⁻¹) * a)⁻¹ * ((y * b * y⁻¹ * b⁻¹) * b)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e, comm_mul_central (c1 a ha).symm (c1 b hb).symm (c2 a ha).symm (c2 b hb).symm
        (c2 _ h1K), commutatorElement_def]
    calc ⁅a, b⁆ * y = y * ⁅a, b⁆ * y⁻¹ * y := by rw [hc]
      _ = y * ⁅a, b⁆ := by group
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hK.symm ▸ hk))

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem a23List_Kv (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    CFSG.Milestones.SQTKSimpleList (↥Kv ⧸ CFSG.pCore 2 ↥Kv) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  set H := Gv v with hHdef
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hqtke : QuasithinUnique.QTKECore G :=
    QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hK := hC.cComp
  have hLK := hC.lv_le
  have hcases := QuasithinUnique.Vol2Native.lemma_1_2_1_four hqtke.1 h36 hH2 hK
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hK
  let eX : ↥Kv ⧸ CFSG.pCore 2 ↥Kv ≃* ↥(modO2Image H Kv) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hLvH : Lv L v ≤ H := Lv_le_Gv L v
  let φ : ↥(Lv L v) →* ↥(modO2Image H Kv) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLvH)).codRestrict
      (modO2Image H Kv) fun l => ⟨Subgroup.inclusion hLvH l, hLK l.2, rfl⟩
  have hφ : IsPGroup 2 ↥φ.ker := by
    intro k
    have hk : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (Subgroup.inclusion hLvH (k : ↥(Lv L v))) =
        1 := congrArg Subtype.val (k.2 : φ k = 1)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥H)) ⟨_, hk⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) hn
    simpa using this
  rcases hcases with ⟨-, -, hlist⟩ | ⟨-, hc3, -⟩ | h3 | h4
  · exact CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv eX hlist
  · exfalso
    have hsQ := isSimple_Kv h1222 h36 hC
    have hs : IsSimpleGroup ↥(modO2Image H Kv) := (MulEquiv.isSimpleGroup_congr eX).1 hsQ
    obtain ⟨-, -, a, b, hab⟩ := hC.quasisimple
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have hnab : ∃ a b : ↥(modO2Image H Kv), a * b ≠ b * a := ⟨eX a', eX b', fun h => hab (by
      have h' : eX (a' * b') = eX (b' * a') := by rw [map_mul, map_mul, h]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, eX.injective h'])⟩
    rw [RankThreeCoreUniqueness.Helpers.nonabelian_simple_center_eq_bot hnab,
      Subgroup.card_bot] at hc3
    omega
  · exfalso
    obtain ⟨p, hp, hp3, -, -, -, ψ₃, -, hψ₃k, -⟩ := h3
    exact false_of_map_sl2 h1222 F hH hv hβ φ hφ hp (by omega) ψ₃ hψ₃k
  · exfalso
    obtain ⟨-, -, ⟨e5⟩, -⟩ := h4
    let ψ₄ := e5.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image H Kv)))
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥(modO2Image H Kv) := by
      ext x
      simp [ψ₄]
    exact false_of_map_sl2 h1222 F hH hv hβ φ hφ Nat.prime_five (by norm_num) ψ₄ hψ₄k

theorem nonabelian_Kv {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    ∃ a b : ↥Kv ⧸ CFSG.pCore 2 ↥Kv, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hC.quasisimple
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem center_Kv_eq (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hq : CFSG.IsQuasisimple ↥Kv) : Subgroup.center ↥Kv = CFSG.pCore 2 ↥Kv := by
  have hsQ := isSimple_Kv h1222 h36 hC
  have hnab := nonabelian_Kv hC
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥Kv) with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hcen : φ.ker ≤ Subgroup.center ↥Kv := by
    rw [hφ, QuotientGroup.ker_mk']
    obtain ⟨-, hsZ, -⟩ := hq
    set πZ := QuotientGroup.mk' (Subgroup.center ↥Kv) with hπZ
    have hn : ((CFSG.pCore 2 ↥Kv).map πZ).Normal :=
      Subgroup.Normal.map inferInstance πZ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥Kv).map πZ) with h | h
    · intro p hp
      have h1 : πZ p ∈ (CFSG.pCore 2 ↥Kv).map πZ := ⟨p, hp, rfl⟩
      rw [h, Subgroup.mem_bot, hπZ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      have key : ∀ k : ↥Kv, ∃ p ∈ CFSG.pCore 2 ↥Kv, ∃ z ∈ Subgroup.center ↥Kv, k = p * z := by
        intro k
        obtain ⟨p, hp, hpk⟩ := (h ▸ Subgroup.mem_top (πZ k) : πZ k ∈ (CFSG.pCore 2 ↥Kv).map πZ)
        refine ⟨p, hp, p⁻¹ * k, ?_, by group⟩
        rw [hπZ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hpk
        exact hpk
      obtain ⟨a, b, hab⟩ := hnab
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨p₁, hp₁, z₁, hz₁, rfl⟩ := key a'
      obtain ⟨p₂, hp₂, z₂, hz₂, rfl⟩ := key b'
      apply hab
      have e1 : (QuotientGroup.mk (p₁ * z₁) : ↥Kv ⧸ CFSG.pCore 2 ↥Kv) = QuotientGroup.mk z₁ := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p₁).2 hp₁, one_mul]
      have e2 : (QuotientGroup.mk (p₂ * z₂) : ↥Kv ⧸ CFSG.pCore 2 ↥Kv) = QuotientGroup.mk z₂ := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p₂).2 hp₂, one_mul]
      rw [e1, e2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz₂ z₁]
  have := hsQ
  exact (RankThreeCoreUniqueness.Helpers.surjective_centerless_image_center_eq_kernel φ hφs hcen
    (RankThreeCoreUniqueness.Helpers.nonabelian_simple_center_eq_bot hnab)).trans
    (QuotientGroup.ker_mk' _)

end S126T2

end CFSG.Quasithin.H13
