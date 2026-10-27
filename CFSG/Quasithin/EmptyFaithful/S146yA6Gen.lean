module

public import CFSG.Quasithin.EmptyFaithful.S146yA6
public import CFSG.Quasithin.EmptyFaithful.S146yKM

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section A6Gen

variable {G : Type} [Group G] [Finite G]

theorem card_mulAut_le_of_card_le_eight {Y : Type*} [Group Y] [Finite Y]
    (hcomm : ∀ a b : Y, a * b = b * a) (hsq : ∀ a : Y, a ^ 2 = 1) (h8 : Nat.card Y ≤ 8) :
    Nat.card (MulAut Y) ≤ 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 Y := fun g => ⟨1, by simpa using hsq g⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra h
    push Not at h
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq hn
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases n <;> simp [Fin.prod_univ_succ]

omit [Finite G] in
theorem isSimpleGroup_kbar_of_kbarIsA6 {K : Subgroup G} (h : KbarIsA6 K) : IsSimpleGroup (KBar K) := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

omit [Finite G] in
theorem card_kbar_of_kbarIsA6 {K : Subgroup G} (h : KbarIsA6 K) : Nat.card (KBar K) = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

omit [Finite G] in
theorem exists_tildeElt {W U₁ : Subgroup G} (hU : U₁ ≤ Subgroup.normalizer (W : Set G))
    (y : ↥(tildeOf W U₁)) : ∃ (u : G) (hu : u ∈ U₁), tildeElt hU u hu = y := by
  obtain ⟨x, hx, hxy⟩ := mem_secImg.1 y.2
  exact ⟨(x : G), hx, Subtype.ext hxy⟩

theorem eq_of_relIndex_lt_sixteen {K Z U₁ W : Subgroup G} (hA6 : KbarIsA6 K)
    (hab : IsElemAbelian 2 U₁) (hZW : Z ≤ W) (hWU : W ≤ U₁) (hgen : ⁅U₁, K⁆ ⊔ Z = U₁)
    (hKU : K ≤ Subgroup.normalizer (U₁ : Set G)) (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Z)
    (h : W.relIndex U₁ < 16) : W = U₁ := by
  classical
  by_contra hne
  have hUW : U₁ ≤ Subgroup.normalizer (W : Set G) := by
    have : IsMulCommutative ↥U₁ := hab.1
    have hn : (W.subgroupOf U₁).Normal := inferInstance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hWU).mp hn
  have hel : IsElemAbelian 2 (tildeOf W U₁) := by
    refine isElemAbelian_secImg_normalizer (fun x hx y hy => ?_) (fun x hx => ?_)
    · have hc : x * y = y * x :=
        congrArg Subtype.val (hab.1.is_comm.comm (⟨x, hx⟩ : ↥U₁) ⟨y, hy⟩)
      rw [show x * y * x⁻¹ * y⁻¹ = 1 by rw [hc]; group]
      exact W.one_mem
    · rw [hab.2 x hx]
      exact W.one_mem
  have hcardY : Nat.card (tildeOf W U₁) = W.relIndex U₁ := by
    have h1 := relIndex_secImg (A := Subgroup.normalizer (W : Set G)) (B := W) (T := W) (H := U₁)
      le_rfl hWU hUW
    have h2 : secImg (Subgroup.normalizer (W : Set G)) W W = ⊥ := tildeOf_eq_bot_of_le le_rfl
    rw [h2, Subgroup.relIndex_bot_left] at h1
    exact h1
  have hY8 : Nat.card (tildeOf W U₁) ≤ 8 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥(tildeOf W U₁) := fun g => ⟨1, by
      have := hel.2 g.1 g.2
      exact Subtype.ext (by simpa using this)⟩
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hn3 : n ≤ 3 := by
      by_contra hcon
      push Not at hcon
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
      _ = 8 := by norm_num
  have hcomm : ∀ a b : ↥(tildeOf W U₁), a * b = b * a := fun a b =>
    Subtype.ext (isElemAbelian_comm hel a.2 b.2)
  have hsq : ∀ a : ↥(tildeOf W U₁), a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2)
  have hAut := card_mulAut_le_of_card_le_eight hcomm hsq hY8
  let ρ : ↥K →* MulAut ↥(tildeOf W U₁) := secRho hKW hKU
  have hQle : (pCoreOf 2 K).subgroupOf K ≤ ρ.ker := by
    intro p hp
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun y => ?_
    obtain ⟨u, hu, rfl⟩ := exists_tildeElt hUW y
    rw [MulAut.one_apply]
    exact (secRho_apply_tildeElt_iff hKW hKU hUW p u hu).mpr (hZW (hQ p hp u hu))
  let ρ' : KBar K →* MulAut ↥(tildeOf W U₁) := QuotientGroup.lift _ ρ hQle
  have hsimple : IsSimpleGroup (KBar K) := isSimpleGroup_kbar_of_kbarIsA6 hA6
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ'.ker with hk | hk
  · have hinj : Function.Injective ρ' := (MonoidHom.ker_eq_bot_iff ρ').mp hk
    have : Finite (MulAut ↥(tildeOf W U₁)) :=
      Finite.of_injective (fun f : MulAut ↥(tildeOf W U₁) => (f : ↥(tildeOf W U₁) → ↥(tildeOf W U₁)))
        (fun f g hfg => MulEquiv.ext (congrFun hfg))
    have hle := Nat.card_le_card_of_injective ρ' hinj
    rw [card_kbar_of_kbarIsA6 hA6] at hle
    omega
  · apply hne
    have hall : ∀ (k : G) (hkK : k ∈ K), ρ ⟨k, hkK⟩ = 1 := by
      intro k hkK
      have hmem : (QuotientGroup.mk ⟨k, hkK⟩ : KBar K) ∈ ρ'.ker := by
        rw [hk]
        exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hmem
      exact hmem
    have hcom : ⁅U₁, K⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have h1 := commutator_mem_of_secRho_eq_one hKW hKU hUW (x := ⟨g₂, hg₂⟩) (hall g₂ hg₂) hg₁
      have h2 := W.inv_mem h1
      have e : (g₂ * g₁ * g₂⁻¹ * g₁⁻¹)⁻¹ = ⁅g₁, g₂⁆ := by
        simp [commutatorElement_def, mul_assoc]
      rw [e] at h2
      exact h2
    have : U₁ ≤ W := by
      rw [← hgen]
      exact sup_le hcom hZW
    exact le_antisymm hWU this

theorem a6CoverGen_proof : A6CoverGen := by
  intro G _ _ K Z U₁ u hA6 h5 hgen hZU hab hKZ hKU hQ hu hnc W hZW hWU hKW hWu
  classical
  by_contra hne
  have hcommU : IsMulCommutative ↥U₁ := hab.1
  have hUZ : U₁ ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZU).mp inferInstance
  have hUW : U₁ ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWU).mp inferInstance
  have hWZ : W ≤ Subgroup.normalizer (Z : Set G) := hWU.trans hUZ
  have hZ32 : Z.relIndex U₁ = 32 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥U₁ := fun g => ⟨1, by
      have := hab.2 g.1 g.2
      exact Subtype.ext (by simpa using this)⟩
    obtain ⟨a, ha⟩ := hp.exists_card_eq
    have hdvd := Subgroup.relIndex_dvd_card Z U₁
    rw [ha] at hdvd
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have h5' : padicValNat 2 (Z.relIndex U₁) = 5 := h5
    rw [hb, padicValNat.prime_pow] at h5'
    rw [hb, h5']
    norm_num
  have h16 : 16 ≤ W.relIndex U₁ := by
    by_contra hlt
    push Not at hlt
    exact hne (eq_of_relIndex_lt_sixteen hA6 hab hZW hWU hgen hKU hKW hQ hlt)
  have hprod := Subgroup.relIndex_mul_relIndex Z W U₁ hZW hWU
  rw [hZ32] at hprod
  have hZW2 : Z.relIndex W = 2 := by
    have hpos : Z.relIndex W ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hprod
      omega
    have hle : Z.relIndex W ≤ 2 := by
      by_contra hgt
      push Not at hgt
      nlinarith
    have hne1 : Z.relIndex W ≠ 1 := by
      intro h1
      obtain ⟨x₀, hx₀, hx₀n⟩ := hnc
      exact hx₀n (Subgroup.relIndex_eq_one.mp h1 (hWu x₀ hx₀))
    omega
  have hcardW : Nat.card (tildeOf Z W) = 2 := by
    have h1 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (T := Z) (H := W)
      le_rfl hZW hWZ
    have h2 : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := tildeOf_eq_bot_of_le le_rfl
    rw [h2, Subgroup.relIndex_bot_left, hZW2] at h1
    exact h1
  let ρ₀ : ↥K →* MulAut ↥(tildeOf Z U₁) := secRho hKZ hKU
  let _ : MulAction ↥K ↥(tildeOf Z U₁) := MulAction.compHom _ ρ₀
  have hsmul : ∀ (x : ↥K) (w : ↥(tildeOf Z U₁)), x • w = ρ₀ x w := fun x w => rfl
  set ut : ↥(tildeOf Z U₁) := tildeElt hUZ u hu with hut
  have hstab : ∀ x : ↥K, x ∈ MulAction.stabilizer ↥K ut ↔
      (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ Z := fun x => by
    rw [MulAction.mem_stabilizer_iff, hsmul]
    exact secRho_apply_tildeElt_iff hKZ hKU hUZ x u hu
  set Wt : Subgroup ↥(tildeOf Z U₁) := (tildeOf Z W).subgroupOf (tildeOf Z U₁) with hWt
  have hWt2 : Nat.card Wt = 2 := by
    rw [← hcardW]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (secImg_mono hWU)).toEquiv
  have horb : MulAction.orbit ↥K ut ⊆ (fun w : ↥(tildeOf Z U₁) => w * ut) '' (Wt : Set ↥(tildeOf Z U₁)) := by
    rintro y ⟨x, rfl⟩
    have hxK : (x : G) ∈ K := x.2
    have hcW : (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ W := hWu x hxK
    have hcU : (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ U₁ := hWU hcW
    refine ⟨⟨secMk (Subgroup.normalizer (Z : Set G)) Z
        ⟨(x : G) * u * (x : G)⁻¹ * u⁻¹, hUZ hcU⟩, secMk_mem_secImg hcU⟩, ?_, ?_⟩
    · show secMk (Subgroup.normalizer (Z : Set G)) Z
        ⟨(x : G) * u * (x : G)⁻¹ * u⁻¹, hUZ hcU⟩ ∈ tildeOf Z W
      exact secMk_mem_secImg hcW
    · apply Subtype.ext
      show secMk (Subgroup.normalizer (Z : Set G)) Z ⟨(x : G) * u * (x : G)⁻¹ * u⁻¹, hUZ hcU⟩ *
          secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUZ hu⟩ =
          ((x • ut : ↥(tildeOf Z U₁)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z)
      rw [hsmul, secRho_coe, ← map_mul]
      change _ = secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hKZ x) *
          secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUZ hu⟩ *
          (secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hKZ x))⁻¹
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]
  have hidx : (MulAction.stabilizer ↥K ut).index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    calc (MulAction.orbit ↥K ut).ncard
        ≤ ((fun w : ↥(tildeOf Z U₁) => w * ut) '' (Wt : Set ↥(tildeOf Z U₁))).ncard :=
          Set.ncard_le_ncard horb (Set.toFinite _)
      _ ≤ (Wt : Set ↥(tildeOf Z U₁)).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card Wt := (Nat.card_coe_set_eq _).symm
      _ = 2 := hWt2
  have hQ' : (pCoreOf 2 K).subgroupOf K ≤ MulAction.stabilizer ↥K ut := fun p hp =>
    (hstab p).mpr (hQ p hp u hu)
  have hsimple : IsSimpleGroup (KBar K) := isSimpleGroup_kbar_of_kbarIsA6 hA6
  have hmap : ((MulAction.stabilizer ↥K ut).map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))).index =
      (MulAction.stabilizer ↥K ut).index :=
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hQ')
  have hidx1 : (MulAction.stabilizer ↥K ut).index = 1 := by
    have hpos : (MulAction.stabilizer ↥K ut).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    by_contra hne1
    have h2 : (MulAction.stabilizer ↥K ut).index = 2 := by omega
    have hN : ((MulAction.stabilizer ↥K ut).map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))).index = 2 := by
      rw [hmap, h2]
    have hnorm := Subgroup.normal_of_index_eq_two hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((MulAction.stabilizer ↥K ut).map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))) with hb | ht
    · rw [hb, Subgroup.index_bot, card_kbar_of_kbarIsA6 hA6] at hN
      omega
    · rw [ht, Subgroup.index_top] at hN
      omega
  have htop : MulAction.stabilizer ↥K ut = ⊤ := Subgroup.index_eq_one.mp hidx1
  obtain ⟨x₀, hx₀, hx₀n⟩ := hnc
  exact hx₀n ((hstab ⟨x₀, hx₀⟩).mp (htop ▸ Subgroup.mem_top _))

end A6Gen

theorem input14624KMoves_proof : Input14624KMoves :=
  input14624KMoves_of_gen a6CoverGen_proof

end CFSG.Quasithin
