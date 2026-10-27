module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310Q
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837Y
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative

namespace Ch8310X

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_qPi_mem' {G₁ Y : Subgroup G}
    (hO : ∀ o : ↥G₁, o ∈ CFSG.Open.pCore 2 ↥G₁ → (o : G) ∈ Y) {y : G} (hyG : y ∈ G₁)
    (h : qPi G₁ ⟨y, hyG⟩ ∈ imageOTwoQuot G₁ Y) : y ∈ Y := by
  obtain ⟨w, hw, hwy⟩ := h
  have hwY : (w : G) ∈ Y := Subgroup.mem_subgroupOf.mp hw
  have hker : w⁻¹ * ⟨y, hyG⟩ ∈ CFSG.Open.pCore 2 ↥G₁ := QuotientGroup.eq.mp hwy
  have h1 : (w : G)⁻¹ * y ∈ Y := hO _ hker
  have e : y = (w : G) * ((w : G)⁻¹ * y) := by group
  rw [e]
  exact Y.mul_mem hwY h1

omit [Finite G] in
theorem exists_of_mem_image {G₁ Y : Subgroup G} {u : OTwoQuot G₁}
    (hu : u ∈ imageOTwoQuot G₁ Y) : ∃ (y : G) (hy : y ∈ G₁), y ∈ Y ∧ qPi G₁ ⟨y, hy⟩ = u := by
  obtain ⟨w, hw, rfl⟩ := hu
  exact ⟨w, w.2, Subgroup.mem_subgroupOf.mp hw, rfl⟩

omit [Finite G] in
theorem qPi_mem_image {G₁ Y : Subgroup G} {y : G} (hyG : y ∈ G₁) (hy : y ∈ Y) :
    qPi G₁ ⟨y, hyG⟩ ∈ imageOTwoQuot G₁ Y :=
  ⟨⟨y, hyG⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem pCore_le_of_isSylowIn {G₁ T : Subgroup G} (hTG : IsSylowIn 2 T G₁) :
    ∀ o : ↥G₁, o ∈ CFSG.Open.pCore 2 ↥G₁ → (o : G) ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro o ho
  have := CFSG.LieType.BorelTits.pCore_normal 2 (G := ↥G₁)
  have h := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥G₁) 2).le_sylow_of_normal hTG.toSylow
  exact Subgroup.mem_subgroupOf.mp (h ho)

theorem pair_facts {Gz K : Subgroup G} {s : G} (hK : K ∈ cComp Gz) (hsG : s ∈ Gz)
    (hsN : s ∉ Subgroup.normalizer (K : Set G))
    (hKzN : Gz ≤ Subgroup.normalizer ((K ⊔ CFSG.Quasithin.conjSub s⁻¹ K : Subgroup G) : Set G))
    (hs : IsSimpleGroup ↥(imageOTwoQuot Gz K)) :
    (∀ a ∈ imageOTwoQuot Gz K, ∀ b ∈ imageOTwoQuot Gz (CFSG.Quasithin.conjSub s⁻¹ K),
        a * b = b * a) ∧
      imageOTwoQuot Gz K ⊓ imageOTwoQuot Gz (CFSG.Quasithin.conjSub s⁻¹ K) = ⊥ ∧
      (imageOTwoQuot Gz K).map (MulAut.conj (qPi Gz ⟨s, hsG⟩)).toMonoidHom =
        imageOTwoQuot Gz (CFSG.Quasithin.conjSub s⁻¹ K) ∧
      ∀ x : OTwoQuot Gz,
        ((imageOTwoQuot Gz K).map (MulAut.conj x).toMonoidHom = imageOTwoQuot Gz K ∧
          (imageOTwoQuot Gz (CFSG.Quasithin.conjSub s⁻¹ K)).map (MulAut.conj x).toMonoidHom =
            imageOTwoQuot Gz (CFSG.Quasithin.conjSub s⁻¹ K)) ∨
        ((imageOTwoQuot Gz K).map (MulAut.conj x).toMonoidHom =
            imageOTwoQuot Gz (CFSG.Quasithin.conjSub s⁻¹ K) ∧
          (imageOTwoQuot Gz (CFSG.Quasithin.conjSub s⁻¹ K)).map (MulAut.conj x).toMonoidHom =
            imageOTwoQuot Gz K) := by
  set K₂ := CFSG.Quasithin.conjSub s⁻¹ K with hK₂def
  have hK₂ : K₂ ∈ cComp Gz := conjSub_mem_cComp_of_mem hK (Gz.inv_mem hsG)
  have hsN' : s⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h =>
    hsN (by simpa using (Subgroup.normalizer (K : Set G)).inv_mem h)
  have hss : CFSG.Quasithin.conjSub s⁻¹ K₂ = K :=
    SBc16.conjSub_conjSub_eq_of_mem_cComp hK hK₂ (Gz.inv_mem hsG) hsN' hKzN
  have hsK : CFSG.Quasithin.conjSub s K = K₂ := by
    calc CFSG.Quasithin.conjSub s K
        = CFSG.Quasithin.conjSub s (CFSG.Quasithin.conjSub s⁻¹ K₂) := by rw [hss]
      _ = K₂ := CFSG.Quasithin.conjSub_inv_conjSub s K₂
  have hne : K ≠ K₂ := by
    intro h
    apply hsN'
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h.symm
  have h12 : K₂ ≤ Subgroup.normalizer (K : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK hK₂)
  have h21 : K ≤ Subgroup.normalizer (K₂ : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK₂ hK)
  obtain ⟨hcomm, hdisj⟩ := q_pair_comm_disjoint hK hK₂ hne hs h12 h21
  have hσ : (imageOTwoQuot Gz K).map (MulAut.conj (qPi Gz ⟨s, hsG⟩)).toMonoidHom =
      imageOTwoQuot Gz K₂ := by
    rw [← hsK]
    exact (q_image_conjSub hsG).symm
  refine ⟨hcomm, hdisj, hσ, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := qPi_surjective Gz x
  have hy : (y : G) ∈ Gz := y.2
  have hKzKz : ∀ C : Subgroup G, C ≤ K ⊔ K₂ → CFSG.Quasithin.conjSub (y : G) C ≤ K ⊔ K₂ := by
    intro C hC
    rintro _ ⟨c, hc, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hKzN hy) c).mp (hC hc)
    simpa [MulAut.conj_apply] using this
  have hcases : ∀ C : Subgroup G, C ∈ cComp Gz → C ≤ K ⊔ K₂ →
      CFSG.Quasithin.conjSub (y : G) C = K ∨ CFSG.Quasithin.conjSub (y : G) C = K₂ :=
    fun C hC hCle => SBc13.eq_or_eq_of_mem_cComp_of_le_sup hK hK₂
      (conjSub_mem_cComp_of_mem hC hy) (hKzKz C hCle)
  have hinj : ∀ A B : Subgroup G, CFSG.Quasithin.conjSub (y : G) A =
      CFSG.Quasithin.conjSub (y : G) B → A = B := fun A B h =>
    Subgroup.map_injective (MulAut.conj (y : G)).injective h
  have himg1 := q_image_conjSub (K := K) hy
  have himg2 := q_image_conjSub (K := K₂) hy
  rcases hcases K hK le_sup_left with h1 | h1
  · left
    rcases hcases K₂ hK₂ le_sup_right with h2 | h2
    · exact absurd (hinj _ _ (h2.trans h1.symm)) hne.symm
    · refine ⟨?_, ?_⟩
      · rw [← himg1, h1]
      · rw [← himg2, h2]
  · right
    rcases hcases K₂ hK₂ le_sup_right with h2 | h2
    · refine ⟨?_, ?_⟩
      · rw [← himg1, h1]
      · rw [← himg2, h2]
    · exact absurd (hinj _ _ (h1.trans h2.symm)) hne

theorem isSylowIn_inf {Gz T : Subgroup G} {N₁ N₂ : Subgroup (OTwoQuot Gz)}
    (hTG : IsSylowIn 2 T Gz) (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hn : (N₁ ⊔ N₂).Normal) : IsSylowIn 2 (imageOTwoQuot Gz T ⊓ N₁) N₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hThat : IsSylowIn 2 (imageOTwoQuot Gz T) ⊤ := by
    let P : Sylow 2 (OTwoQuot Gz) := hTG.toSylow.mapSurjective (qPi_surjective Gz)
    have hP : (P : Subgroup (OTwoQuot Gz)) = imageOTwoQuot Gz T := by
      rw [Sylow.coe_mapSurjective]
      rfl
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hP]
      exact P.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hP]
      exact P.not_dvd_index
  have hN12norm : ((N₁ ⊔ N₂).subgroupOf ⊤).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr
      (Subgroup.normalizer_eq_top_iff.mpr hn).ge
  have hS12 := hThat.inf_normal le_top hN12norm
  have hN₂N₁ : N₂ ≤ Subgroup.normalizer (N₁ : Set (OTwoQuot Gz)) :=
    Ch8310.le_normalizer_of_comm hc
  have hN1n : (N₁.subgroupOf (N₁ ⊔ N₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hN₂N₁)
  have h := hS12.inf_normal le_sup_left hN1n
  rwa [inf_assoc, inf_eq_right.mpr (le_sup_left : N₁ ≤ N₁ ⊔ N₂)] at h

omit [Finite G] in
theorem mem_centralizer_of_coprime {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (e : IntMod V hV ≃* WMod) (g : Subgroup.normalizer (V : Set G))
    (hg : congrHom e (convI hV g) ∈ stabE) (hgo : Nat.Coprime (orderOf (g : G)) 6) :
    (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : orderOf (congrHom e (convI hV g)) ∣ orderOf (g : G) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_map_dvd ((congrHom e).comp (convI hV)) g
  have h2 : orderOf (congrHom e (convI hV g)) ∣ 2 ^ 7 * 3 ^ 2 := by
    rw [← card_stabE]
    exact Subgroup.orderOf_dvd_natCard stabE hg
  have hcop : Nat.Coprime (orderOf (g : G)) (2 ^ 7 * 3 ^ 2) := by
    have h6 : Nat.Coprime (orderOf (g : G)) (2 * 3) := hgo
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (Nat.Coprime.coprime_mul_right_right h6))
      (Nat.Coprime.pow_right _ (Nat.Coprime.coprime_mul_left_right h6))
  have h3 : orderOf (congrHom e (convI hV g)) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  have hc1 : congrHom e (convI hV g) = 1 := orderOf_eq_one_iff.mp h3
  have hconv : convI hV g = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact hc1
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hval := convI_apply_val hV g (IntMod.mk hV ⟨v, hv⟩)
  rw [hconv] at hval
  change v = (g : G) * v * (g : G)⁻¹ at hval
  calc v * (g : G) = ((g : G) * v * (g : G)⁻¹) * g := by rw [← hval]
    _ = (g : G) * v := by group

theorem humax_of {Gz H T M Kz : Subgroup G} (hHG : H ≤ Gz) (hTH : T ≤ H)
    (hO : ∀ o : ↥Gz, o ∈ CFSG.Open.pCore 2 ↥Gz → (o : G) ∈ T)
    (hU : IsUniqueMaxOver H T (H ⊓ M)) :
    ∀ Y : Subgroup (OTwoQuot Gz), imageOTwoQuot Gz T ≤ Y → Y ≤ imageOTwoQuot Gz H →
      Y ≠ imageOTwoQuot Gz H → Y ⊓ imageOTwoQuot Gz Kz ≤ imageOTwoQuot Gz (M ⊓ Kz) := by
  intro Y hTY hYH hne
  set Y' : Subgroup G := (Y.comap (qPi Gz)).map Gz.subtype with hY'
  have hTG : T ≤ Gz := hTH.trans hHG
  have hTY' : T ≤ Y' := fun t ht => ⟨⟨t, hTG ht⟩, hTY (qPi_mem_image (hTG ht) ht), rfl⟩
  have hY'H : Y' ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_of_qPi_mem' (fun o ho => hTH (hO o ho)) y.2 (hYH hy)
  have hY'ne : Y' ≠ H := by
    intro h
    apply hne
    refine le_antisymm hYH ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxH : (x : G) ∈ Y' := h ▸ (Subgroup.mem_subgroupOf.mp hx)
    obtain ⟨y, hy, hyx⟩ := hxH
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hY'M : Y' ≤ H ⊓ M :=
    Vol2.Ch11.SecB.le_of_isUniqueMaxOver hU hTY' (lt_of_le_of_ne hY'H hY'ne)
  rintro u ⟨huY, huK⟩
  obtain ⟨k, hkG, hkK, rfl⟩ := exists_of_mem_image huK
  have hkY' : k ∈ Y' := ⟨⟨k, hkG⟩, huY, rfl⟩
  exact qPi_mem_image hkG ⟨(hY'M hkY').2, hkK⟩

omit [Finite G] in
theorem not_exists_of_not_autCyclic {Gz T P : Subgroup G} (hTG : T ≤ Gz) (hPG : P ≤ Gz)
    (hPinj : ∀ (x : G) (hx : x ∈ Gz) (y : G) (hy : y ∈ Gz), x ∈ P → y ∈ P →
      qPi Gz ⟨x, hx⟩ = qPi Gz ⟨y, hy⟩ → x = y)
    (hnc : ¬ EmptyFaithfulMultiple.AutCyclic T P) :
    ¬ ∃ c ∈ imageOTwoQuot Gz (T ⊓ Subgroup.normalizer (P : Set G)),
      ∀ s ∈ imageOTwoQuot Gz (T ⊓ Subgroup.normalizer (P : Set G)), ∃ k : ℕ,
        ∀ x ∈ imageOTwoQuot Gz P, s * x * s⁻¹ = c ^ k * x * (c ^ k)⁻¹ := by
  rintro ⟨c, hc, hall⟩
  obtain ⟨c₀, hc₀G, hc₀, rfl⟩ := exists_of_mem_image hc
  apply hnc
  refine ⟨c₀, hc₀, fun s hs => ?_⟩
  obtain ⟨k, hk⟩ := hall _ (qPi_mem_image (hTG hs.1) hs)
  refine ⟨k, fun x hx => ?_⟩
  have h1 := hk _ (qPi_mem_image (hPG hx) hx)
  have hsx : s * x * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hs.2 x).mp hx
  have hck : c₀ ^ k ∈ Subgroup.normalizer (P : Set G) := Subgroup.pow_mem _ hc₀.2 k
  have hcx : c₀ ^ k * x * (c₀ ^ k)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hck x).mp hx
  have hsG := hTG hs.1
  have hxG := hPG hx
  refine hPinj _ (Gz.mul_mem (Gz.mul_mem hsG hxG) (Gz.inv_mem hsG)) _
    (Gz.mul_mem (Gz.mul_mem (Gz.pow_mem hc₀G k) hxG) (Gz.inv_mem (Gz.pow_mem hc₀G k)))
    hsx hcx ?_
  have e1 : (⟨s * x * s⁻¹, Gz.mul_mem (Gz.mul_mem hsG hxG) (Gz.inv_mem hsG)⟩ : ↥Gz) =
      ⟨s, hsG⟩ * ⟨x, hxG⟩ * (⟨s, hsG⟩ : ↥Gz)⁻¹ := rfl
  have e2 : (⟨c₀ ^ k * x * (c₀ ^ k)⁻¹,
      Gz.mul_mem (Gz.mul_mem (Gz.pow_mem hc₀G k) hxG) (Gz.inv_mem (Gz.pow_mem hc₀G k))⟩ : ↥Gz) =
      (⟨c₀, hc₀G⟩ : ↥Gz) ^ k * ⟨x, hxG⟩ * ((⟨c₀, hc₀G⟩ : ↥Gz) ^ k)⁻¹ := by
    apply Subtype.ext
    simp
  rw [e1, e2, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_pow]
  exact h1

theorem card_range_eq_of_simple {A B : Type*} [Group A] [Group B] [Finite A] {N : Subgroup A}
    [N.Normal] (hs : IsSimpleGroup (A ⧸ N)) (f : A →* B) (hN : N ≤ f.ker)
    (hB : f.range ≠ ⊥) : Nat.card f.range = Nat.card (A ⧸ N) := by
  set g := QuotientGroup.lift N f hN with hg
  have hrange : g.range = f.range := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk x, rfl⟩
  have := hs
  have := g.normal_ker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker with h | h
  · rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, h]
    exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  · exfalso
    apply hB
    rw [← hrange, eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    have : x ∈ g.ker := by rw [h]; trivial
    exact (Subgroup.mem_bot).mpr this

theorem false_of_case_i
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G}
    (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z)
    {K : Subgroup G} {s : G} (hsT : s ∈ T) (hsN : s ∉ Subgroup.normalizer (K : Set G))
    (hKC : quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)))
    (hKz : ch83Kz T L z = K ⊔ CFSG.conjugate K s) {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5)
    (hKp : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 p 1)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hHK : H ≤ ch83Kz T L z ⊔ T)
    (hU : IsUniqueMaxOver H T (H ⊓ fsuM T L)) {K' : Subgroup G} (hK'c : K' ∈ cComp H)
    (hHK' : H = K' ⊔ T)
    (hty : E2.IsBenderOf 2 ↥(E2.star (H ⊓ fsuM T L) H K') ∨
      IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K') ∨ IsPSp4 2 2 ↥(E2.star (H ⊓ fsuM T L) H K'))
    (hloc : H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
      pCoreOf 2 (H ⊓ fsuM T L)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, h22, h23⟩ := hKp.1
  have hp2 : p ≠ 2 := fun h => h22 (by rw [h, pow_one])
  have hp3 : p ≠ 3 := fun h => h23 (by rw [h, pow_one])
  have hp7 : 7 ≤ p := by
    have h2 := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ 7 ≤ p by omega) with
      h | h | h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · subst h; norm_num at hp
    · exact absurd h hp5
    · subst h; norm_num at hp
    · exact h
  set Gz := Subgroup.centralizer ({z} : Set G) with hGz
  set M := fsuM T L with hM
  set Kz := ch83Kz T L z with hKzdef
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Gz := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hXGz : ch83X T L z ≤ Gz := (twoResidual_le _).trans inf_le_right
  have hKzGz : Kz ≤ Gz := conjClosure_le fun h hh x hx =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hGzKz : Gz ≤ Subgroup.normalizer (Kz : Set G) := le_normalizer_conjClosure _ _
  have hTsyl : IsSylowIn 2 T Gz := ⟨hTz, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
    (h2.trans (Subgroup.relIndex_dvd_index_of_le hTz))⟩
  have hO := pCore_le_of_isSylowIn hTsyl
  have hTM : T ≤ M := le_normalizer_conjClosure L T
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ Gz := hHK.trans (sup_le hKzGz hTz)
  have hK'H : K' ≤ H := le_of_mem_cComp hK'c
  have hOH : ∀ o : ↥Gz, o ∈ CFSG.Open.pCore 2 ↥Gz → (o : G) ∈ H := fun o ho => hTH (hO o ho)
  have hK : K ∈ cComp Gz := mem_cComp_iff.mpr hKC
  have hKG : K ≤ Gz := le_of_mem_cComp hK
  have hsG : s ∈ Gz := hTz hsT
  set K₂ := CFSG.Quasithin.conjSub s⁻¹ K with hK₂def
  have hKz' : Kz = K ⊔ K₂ := hKz
  have hK₂ : K₂ ∈ cComp Gz := conjSub_mem_cComp_of_mem hK (Gz.inv_mem hsG)
  have hK₂G : K₂ ≤ Gz := le_of_mem_cComp hK₂
  have hKzN : Gz ≤ Subgroup.normalizer ((K ⊔ K₂ : Subgroup G) : Set G) := hKz' ▸ hGzKz
  set N₁ := imageOTwoQuot Gz K with hN₁def
  set N₂ := imageOTwoQuot Gz K₂ with hN₂def
  obtain ⟨e₁⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK)
  obtain ⟨ι₀⟩ := Vol2Native.A312L.equiv_psl2_zmod_of_model hKp
  have ι : ↥N₁ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    e₁.symm.trans ((QuotientGroup.quotientMulEquivOfEq
      (BlueprintB2.pCore_eq_open_pCore 2 ↥K).symm).trans ι₀)
  have := CFSG.Quasithin.Vol2.Ch11.SecB.isSimpleGroup_psl2 (p := p) (by omega)
  have hN₁s : IsSimpleGroup ↥N₁ := ι.isSimpleGroup
  obtain ⟨hc, hd, hσ1, hperm⟩ := pair_facts hK hsG hsN hKzN hN₁s
  have hJ : imageOTwoQuot Gz Kz = N₁ ⊔ N₂ := by
    rw [hKz']
    exact q_image_sup hKG hK₂G
  have hJn : (N₁ ⊔ N₂).Normal := hJ ▸ q_normal_image_of_normal hKzGz hGzKz
  have hSyl := isSylowIn_inf hTsyl hc hJn
  set W₀ := conjClosure K' T with hW₀def
  have hW₀H : W₀ ≤ H := conjClosure_le fun t ht x hx =>
    H.mul_mem (H.mul_mem (hTH ht) (hK'H hx)) (H.inv_mem (hTH ht))
  have hW₀T : T ≤ Subgroup.normalizer (W₀ : Set G) := le_normalizer_conjClosure _ _
  have hK'W₀ : K' ≤ W₀ := le_conjClosure _ _
  have hHW₀ : H ≤ Subgroup.normalizer (W₀ : Set G) := by
    rw [hHK']
    exact sup_le (hK'W₀.trans Subgroup.le_normalizer) hW₀T
  have hHsup : T ⊔ W₀ = H :=
    le_antisymm (sup_le hTH hW₀H) (hHK' ▸ sup_le (hK'W₀.trans le_sup_right) le_sup_left)
  have hres : twoResidual H ≤ W₀ := twoResidual_le_of_isTwoQuotient hW₀H hHW₀
    (B6.isTwoQuotient_of_sup_eq hyp.fsu.sylow.1 hHW₀ hHsup)
  have hKzH : twoResidual H ≤ Kz := by
    refine (twoResidual_le_of_isTwoQuotient (N := H ⊓ Kz) inf_le_left ?_ ?_).trans inf_le_right
    · intro h hh
      exact E1.mem_normalizer_inf (Subgroup.le_normalizer hh) (hGzKz (hHG hh))
    · intro y hy
      obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq (C := Kz) (D := Kz ⊔ T) hyp.fsu.sylow.1
        (sup_le Subgroup.le_normalizer (hTz.trans hGzKz)) (sup_comm T Kz) y (hHK hy)
      exact ⟨k, H.pow_mem hy _, hk⟩
  have hK'Kz : K' ≤ Kz := (Ch838.le_twoResidual_of_mem_cComp hK'c).trans hKzH
  have hW₀Kz : W₀ ≤ Kz := conjClosure_le fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (hGzKz (hTz ht)) x).mp (hK'Kz hx)
  have hW₀p : ⁅W₀, W₀⁆ = W₀ := by
    refine le_antisymm (Subgroup.commutator_le_self W₀) ?_
    rw [hW₀def, conjClosure, Subgroup.closure_le]
    rintro _ ⟨t, ht, x, hx, rfl⟩
    have hK't : CFSG.Quasithin.conjSub t K' ≤ W₀ := by
      rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using mem_conjClosure ht hy
    have hpt : ⁅CFSG.Quasithin.conjSub t K', CFSG.Quasithin.conjSub t K'⁆ =
        CFSG.Quasithin.conjSub t K' := by
      rw [CFSG.Quasithin.conjSub, ← Subgroup.map_commutator, perfect_of_mem_cComp hK'c]
    have hmem : t * x * t⁻¹ ∈ CFSG.Quasithin.conjSub t K' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rw [← hpt] at hmem
    exact Subgroup.commutator_mono hK't hK't hmem
  set W := imageOTwoQuot Gz W₀ with hWdef
  have hWp : ⁅W, W⁆ = W := by
    rw [hWdef, imageOTwoQuot, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective Gz.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hW₀H.trans hHG), hW₀p]
  have hWJ : W ≤ N₁ ⊔ N₂ := hJ ▸ Ch8310.image_mono hW₀Kz
  have hW1 : W ≠ ⊥ := by
    intro hW
    apply ne_bot_of_mem_cComp hK'c
    have h2 : IsPGroup 2 K' := by
      intro x
      have hxG : (x : G) ∈ Gz := hHG (hK'H x.2)
      have h1 : qPi Gz ⟨x, hxG⟩ ∈ W := qPi_mem_image hxG (hK'W₀ x.2)
      rw [hW, Subgroup.mem_bot] at h1
      have h3 : (⟨x, hxG⟩ : ↥Gz) ∈ CFSG.Open.pCore 2 ↥Gz := (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Gz) 2 ⟨_, h3⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥Gz) => ((y : ↥Gz) : G)) hk
      simpa using this
    have := h2.isNilpotent
    exact Ch837.eq_bot_of_perfect_of_isSolvable (perfect_of_mem_cComp hK'c)
  have hWS : ∀ x ∈ imageOTwoQuot Gz T, ∀ w ∈ W, x * w * x⁻¹ ∈ W := q_image_normalizes hW₀T
  set Hh := imageOTwoQuot Gz H with hHhdef
  have hN1H : ¬ N₁ ≤ Hh := by
    intro hle
    have hKH : K ≤ H := fun k hk => mem_of_qPi_mem' hOH (hKG hk)
      (hle (qPi_mem_image (hKG hk) hk))
    have hKcH : K ∈ cComp H := cComp_mem_of_le hK hKH hHG
    have hKW : K ≤ conjClosure K' T := (Ch838.le_twoResidual_of_mem_cComp hKcH).trans hres
    have := hyp.fsu.simple
    have hKl : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
    obtain ⟨t, -, hKt⟩ := Ch837.exists_eq_conjByElt_of_le_conjClosure hKl h37 hH.1.2 hTH hK'c
      hKcH hKW
    rw [Ch837.conjByElt_eq_conjugate] at hKt
    obtain ⟨e₂⟩ := Ch837.nonempty_quot_conjugate_equiv K' t⁻¹
    rw [← hKt] at e₂
    have ι' := e₂.trans ι₀
    have hs' : IsSimpleGroup (↥K' ⧸ CFSG.pCore 2 ↥K') := ι'.isSimpleGroup
    set f : ↥K' →* E2.StarQuot (H ⊓ M) H :=
      (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)).comp (Subgroup.inclusion hK'H)
      with hfdef
    have hfr : f.range = E2.star (H ⊓ M) H K' := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨Subgroup.inclusion hK'H x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    have hTsylH : IsSylowIn 2 T H := ⟨hTH, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
    have hOker : pCoreOf 2 H ≤ kerIn (H ⊓ M) H := by
      intro x hx
      rw [mem_kerIn]
      intro b hb
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hb) x).mp hx
      have h2 := pCoreOf_le_of_isSylowIn hTsylH h1
      exact ⟨hTH h2, hTM h2⟩
    have hNf : CFSG.pCore 2 ↥K' ≤ f.ker := by
      intro x hx
      have h1 : (x : G) ∈ pCoreOf 2 K' := ⟨x, hx, rfl⟩
      have h2 := pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hK'c) h1
      rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hOker h2
    have hcard := Ch8310P.card_lie_two hty
    have hstar1 : f.range ≠ ⊥ := by
      intro h
      rw [hfr] at h
      rw [h, Subgroup.card_bot] at hcard
      omega
    have h1 := card_range_eq_of_simple hs' f hNf hstar1
    rw [hfr, Nat.card_congr ι'.toEquiv] at h1
    have h2 := CFSG.Quasithin.Vol2.Ch11.SecB.two_mul_card_psl2 (p := p) hp2
    rw [← h1] at h2
    obtain ⟨n1, n2, n3, n4⟩ := Ch8310P.mul_sq_sub_one_ne hp7
    rcases hcard with h | h | h | h <;> rw [h] at h2
    · exact n1 h2.symm
    · exact n2 h2.symm
    · exact n3 h2.symm
    · exact n4 h2.symm
  set Mh := imageOTwoQuot Gz (M ⊓ Kz) with hMhdef
  set Ch := imageOTwoQuot Gz (Subgroup.centralizer (fsuV T I : Set G) ⊓ M ⊓ Kz) with hChdef
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hMV : M ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hVVM]
    exact le_normalizer_conjClosure _ _
  have humax := humax_of (Kz := Kz) hHG hTH hO hU
  rw [hJ] at humax
  have hCn : ∀ m ∈ Mh, ∀ c ∈ Ch, m * c * m⁻¹ ∈ Ch := by
    refine q_image_normalizes fun m hm => ?_
    refine E1.mem_normalizer_inf (E1.mem_normalizer_inf ?_ (Subgroup.le_normalizer hm.1))
      (hGzKz (hKzGz hm.2))
    exact A4.mem_normalizer_centralizer (hMV hm.1)
  have hCH : ∀ x ∈ Ch ⊓ Hh, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    rintro x ⟨hxC, hxH⟩
    obtain ⟨c, hcG, ⟨⟨hcV, hcM⟩, -⟩, rfl⟩ := exists_of_mem_image hxC
    have hcH : c ∈ H := mem_of_qPi_mem' hOH hcG hxH
    have hcO := hloc ⟨⟨hcH, hcM⟩, hcV⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M) ⟨c, hcO⟩
    refine ⟨k, ?_⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [← map_pow]
    have : (⟨c, hcG⟩ : ↥Gz) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  obtain ⟨e, he, -, -, hz, hez⟩ := Ch837.exists_model_eW00_T hyp hV hrow hz1 hzV
  have hlift : ∀ d ∈ Mh ⊓ N₁, ∀ r : ℕ, r.Prime → 5 ≤ r → orderOf d = r → d ∈ Ch := by
    rintro d ⟨hdM, -⟩ r hr hr5 hdo
    obtain ⟨y, hyG, hyMK, rfl⟩ := exists_of_mem_image hdM
    obtain ⟨a, b, hb, hdec⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' r hr.ne_one
    have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero r)
    have hyo : orderOf (y ^ b) = r ^ a := by
      rw [orderOf_pow_of_dvd hb0 ⟨r ^ a, by rw [hdec, mul_comm]⟩, hdec,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)]
    have hr6 : Nat.Coprime r 6 := (Nat.Prime.coprime_iff_not_dvd hr).mpr fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      interval_cases r
      · norm_num at h
      · norm_num at hr
    have hcop : Nat.Coprime (orderOf (y ^ b)) 6 := by
      rw [hyo]
      exact Nat.Coprime.pow_left _ hr6
    have hyN : y ^ b ∈ Subgroup.normalizer (fsuV T I : Set G) :=
      Subgroup.pow_mem _ (hMV hyMK.1) b
    have hst := Ch8312.act_mem_stabE e he hz hez hyN (M.pow_mem hyMK.1 b) (Gz.pow_mem hyG b)
    have hyC := mem_centralizer_of_coprime e ⟨y ^ b, hyN⟩ hst hcop
    have hmem : qPi Gz ⟨y, hyG⟩ ^ b ∈ Ch := by
      rw [← map_pow]
      exact qPi_mem_image (Gz.pow_mem hyG b) ⟨⟨hyC, M.pow_mem hyMK.1 b⟩, Kz.pow_mem hyMK.2 b⟩
    have hcopb : Nat.Coprime b (orderOf (qPi Gz ⟨y, hyG⟩)) := by
      rw [hdo]
      exact ((Nat.Prime.coprime_iff_not_dvd hr).mpr hb).symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopb
    rw [← hm]
    exact Ch.pow_mem hmem m
  obtain ⟨-, -, hXi, -, P, hP, hPc, hnac⟩ := Ch837.xi_data h37 h38 h326 hyp hV hrow hN hz2 hzV
  have hPX : P ≤ ch83X T L z := hP.le
  have hXKz : ch83X T L z ≤ Kz := le_conjClosure _ _
  have hXM : ch83X T L z ≤ M :=
    ((twoResidual_le _).trans inf_le_left).trans Subgroup.le_normalizer
  have hPG : P ≤ Gz := hPX.trans hXGz
  have hP3' : ∀ x ∈ P, x ^ 3 = 1 := (Ch8310.isElemAbelian_of_isXi hXi hP hPc).2
  have hPinj : ∀ (x : G) (hx : x ∈ Gz) (y : G) (hy : y ∈ Gz), x ∈ P → y ∈ P →
      qPi Gz ⟨x, hx⟩ = qPi Gz ⟨y, hy⟩ → x = y := by
    intro x hx y hy hxP hyP hxy
    have h1 : (⟨x, hx⟩ : ↥Gz)⁻¹ * ⟨y, hy⟩ ∈ CFSG.Open.pCore 2 ↥Gz := QuotientGroup.eq.mp hxy
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Gz) 2 ⟨_, h1⟩
    have hk' : (x⁻¹ * y) ^ 2 ^ k = 1 := by
      have := congrArg (fun w : ↥(CFSG.Open.pCore 2 ↥Gz) => ((w : ↥Gz) : G)) hk
      simpa using this
    have hxyP : x⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hxP) hyP
    have h3 : (x⁻¹ * y) ^ 3 = 1 := hP3' _ hxyP
    have h4 : (x⁻¹ * y) ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.mpr ⟨hk', h3⟩
    have hg : Nat.gcd (2 ^ k) 3 = 1 :=
      Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)
    rw [hg, pow_one] at h4
    exact inv_injective (mul_eq_one_iff_eq_inv.mp h4)
  set Ph := imageOTwoQuot Gz P with hPhdef
  have hPhJ : Ph ≤ N₁ ⊔ N₂ := hJ ▸ Ch8310.image_mono (hPX.trans hXKz)
  have hPh9 : Nat.card Ph = 9 := by
    set f' : ↥P →* OTwoQuot Gz := (qPi Gz).comp (Subgroup.inclusion hPG) with hf'
    have hf'inj : Function.Injective f' := fun x y hxy => Subtype.ext
      (hPinj _ (hPG x.2) _ (hPG y.2) x.2 y.2 hxy)
    rw [hPhdef, ← q_range_comp_eq_image hPG, ← hPc]
    exact (Nat.card_congr (MonoidHom.ofInjective hf'inj).toEquiv).symm
  have hPh3 : ∀ x ∈ Ph, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hyG, hyP, rfl⟩ := exists_of_mem_image hx
    rw [← map_pow]
    have : (⟨y, hyG⟩ : ↥Gz) ^ 3 = 1 := Subtype.ext (by simpa using hP3' y hyP)
    rw [this, map_one]
  have hPhM : Ph ≤ Mh := Ch8310.image_mono (le_inf (hPX.trans hXM) (hPX.trans hXKz))
  set S' := imageOTwoQuot Gz (T ⊓ Subgroup.normalizer (P : Set G)) with hS'def
  have hS'S : S' ≤ imageOTwoQuot Gz T := Ch8310.image_mono inf_le_left
  have hS'P : ∀ t ∈ S', ∀ x ∈ Ph, t * x * t⁻¹ ∈ Ph := q_image_normalizes inf_le_right
  have hnc := not_exists_of_not_autCyclic hTz hPG hPinj hnac
  exact Ch8310Q.false_of_a5_config hp7 hc hd ι (qPi_mem_image hsG hsT) hσ1
    (fun x _ => hperm x) hSyl hWp hWJ hW1 hWS (Ch8310.image_mono hTH)
    (Ch8310.image_mono hW₀H) hN1H humax hCn hCH hlift hPhJ hPh9 hPh3 hPhM hS'S hS'P hnc

end Ch8310X

end CFSG.Quasithin.H13
