module

public import CFSG.Quasithin.Background.S1567W3
public import CFSG.Quasithin.Background.S1567Z4
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section Normalizers

variable {G : Type} [Group G]

theorem conjSubgroup_le_normalizer_conjSubgroup {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) (g : G) :
    conjSubgroup H g ≤ Subgroup.normalizer ((conjSubgroup K g : Subgroup G) : Set G) := by
  rw [← CFSG.QuasithinUnique.C5.conjSubgroup_normalizer]
  exact CFSG.QuasithinUnique.C5.conjSubgroup_mono h g

theorem mem_normalizer_sup67 {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have h1 := conjSubgroup_eq_iff_mem_normalizer.mpr hH
  have h2 := conjSubgroup_eq_iff_mem_normalizer.mpr hK
  exact conjSubgroup_eq_iff_mem_normalizer.mp
    (by rw [CFSG.QuasithinUnique.C5.conjSubgroup_sup, h1, h2])

end Normalizers

section VMc

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem conjClosure_Mc_comm (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ∀ a ∈ conjClosure (VZ T M) Mc, ∀ b ∈ conjClosure (VZ T M) Mc, a * b = b * a :=
  k.r50 Mc (isHTM153_mc k.c)

theorem conjClosure_Mc_sq (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ∀ a ∈ conjClosure (VZ T M) Mc, a ^ 2 = 1 := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, -, z, hz, rfl⟩ := hx
    have hz2 : z ^ 2 = 1 := k.c.hyp.elemAbelian.2 z hz
    have : (h * z * h⁻¹) ^ 2 = h * z ^ 2 * h⁻¹ := by simp only [pow_two]; group
    rw [this, hz2]
    group
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc : x * y = y * x := conjClosure_Mc_comm k x hx y hy
    have : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
      rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc y x y, ← hc, mul_assoc, mul_assoc]
    rw [this, ihx, ihy, one_mul]
  | inv x hx ih =>
    rw [inv_pow, ih, inv_one]

theorem T_le_Mc67 (k : Ctx67 G T Mc M V₁ V₂ E t) : T ≤ Mc := k.c.hyp.qtfe.inM_mc.2

omit [Finite G] in
theorem s_mem_T67 (gl : GoldLine153 T V₁ E s) : s ∈ T := gl.s_mem.1

theorem conjSubgroup_conjClosure_Mc (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s) :
    conjSubgroup (conjClosure (VZ T M) Mc) s = conjClosure (VZ T M) Mc := by
  refine conjSubgroup_eq_iff_mem_normalizer.mpr ?_
  exact le_normalizer_conjClosure _ _ (T_le_Mc67 k (s_mem_T67 gl))

theorem conjSubgroup_VE67_le_conjClosure_Mc (k : Ctx67 G T Mc M V₁ V₂ E t)
    (gl : GoldLine153 T V₁ E s) :
    conjSubgroup (VE67 T M E) s ≤ conjClosure (VZ T M) Mc := by
  have h := CFSG.QuasithinUnique.C5.conjSubgroup_mono (VE67_le_conjClosure_Mc k) s
  rwa [conjSubgroup_conjClosure_Mc k gl] at h

theorem VE67_comm_conj_VE67 (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s) :
    ∀ a ∈ VE67 T M E, ∀ b ∈ conjSubgroup (VE67 T M E) s, a * b = b * a := fun a ha b hb =>
  conjClosure_Mc_comm k a (VE67_le_conjClosure_Mc k ha) b
    (conjSubgroup_VE67_le_conjClosure_Mc k gl hb)

end VMc

section Core

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem YE_not_le_Mc (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) : ¬ YE153 Mc M E ≤ Mc := by
  intro hle
  obtain ⟨y, hyY, m, hm, hym, hyN, hy3, e₀, he₀, hmv⟩ := exists_odd_y_eps h113 k.c k.L
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := k.c.hyp.elemAbelian.2 x (k.L.le_V hx)
    rwa [pow_two] at this
  have hMc := k.c.hyp.lemma_15_3_4 h11
  have hyZ : y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := hMc ▸ hle hyY
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp k.c.hyp.qtfe.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzE : z ∈ E := k.r66.Z_le_E hz
  have hcomm : z * y = y * z := Subgroup.mem_centralizer_iff.mp hyZ z hz
  have hyz : y * z * y⁻¹ = z := by
    calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [hcomm]
      _ = z := mul_inv_cancel_right _ _
  exact hz1' (eq_one_of_fixed_of_order_three k.L.card_eq hE2 y hyN hy3 ⟨e₀, he₀, hmv⟩ z hzE hyz)

theorem YF_not_le_Mc (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s) : ¬ YF153 Mc M E s ≤ Mc := by
  intro hle
  apply YE_not_le_Mc h11 h113 k
  have h1 := CFSG.QuasithinUnique.C5.conjSubgroup_mono hle s⁻¹
  have h2 : conjSubgroup (YF153 Mc M E s) s⁻¹ = YE153 Mc M E :=
    CFSG.QuasithinUnique.C5.conjSubgroup_conjSubgroup_inv (YE153 Mc M E) s
  have h3 : conjSubgroup Mc s⁻¹ = Mc :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (Mc.inv_mem (T_le_Mc67 k (s_mem_T67 gl))))
  rwa [h2, h3] at h1

theorem s_mul_s_mem_TE (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s) :
    s * s ∈ TE153 T E := by
  have hsT : s ∈ T := s_mem_T67 gl
  rcases coset_of_relIndex_two k.r66.relIndex_two (T.mul_mem hsT hsT) hsT gl.s_not_mem with h | h
  · exact h
  · exact absurd (by simpa using h) gl.s_not_mem

theorem false_of_VE_normalized (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (hYF : YF153 Mc M E s ≤ Subgroup.normalizer (VE67 T M E : Set G))
    (hXE : ∀ x ∈ XE153 E, ∀ a ∈ conjSubgroup (VE67 T M E) s,
      x * a * x⁻¹ ∈ VE67 T M E ⊔ conjSubgroup (VE67 T M E) s) :
    False := by
  set A : Subgroup G := VE67 T M E ⊔ conjSubgroup (VE67 T M E) s with hA
  have hAVc : A ≤ conjClosure (VZ T M) Mc :=
    sup_le (VE67_le_conjClosure_Mc k) (conjSubgroup_VE67_le_conjClosure_Mc k gl)
  have hApg : IsPGroup 2 ↥A := fun x =>
    ⟨1, Subtype.ext (by simpa using conjClosure_Mc_sq k x.1 (hAVc x.2))⟩
  have hAne : A ≠ ⊥ := by
    intro h
    have hEA : E ≤ A := (k.L.le_V.trans VZ_le_VE67).trans le_sup_left
    have hE : E = ⊥ := le_bot_iff.mp (h ▸ hEA)
    have h4 := k.L.card_eq
    rw [hE, Subgroup.card_bot] at h4
    omega
  have hTEn : TE153 T E ≤ Subgroup.normalizer (A : Set G) := by
    intro u hu
    refine mem_normalizer_sup67 (normalizer_le_normalizer_VE67 T M E hu.2) ?_
    have hsTE : s ∈ Subgroup.normalizer (TE153 T E : Set G) :=
      T_le_normalizer_TE k.r66 (s_mem_T67 gl)
    have hsu : s * u * s⁻¹ ∈ TE153 T E := (Subgroup.mem_normalizer_iff.mp hsTE u).mp hu
    have h1 : u ∈ conjSubgroup (Subgroup.normalizer (VE67 T M E : Set G)) s := by
      rw [mem_conjSubgroup_iff]
      exact normalizer_le_normalizer_VE67 T M E hsu.2
    rwa [CFSG.QuasithinUnique.C5.conjSubgroup_normalizer] at h1
  have hsA : s ∈ Subgroup.normalizer (A : Set G) := by
    refine conjSubgroup_eq_iff_mem_normalizer.mp ?_
    rw [hA, CFSG.QuasithinUnique.C5.conjSubgroup_sup, conjSubgroup_conjSubgroup, sup_comm]
    congr 1
    exact conjSubgroup_eq_iff_mem_normalizer.mpr
      (normalizer_le_normalizer_VE67 T M E (s_mul_s_mem_TE k gl).2)
  have hTn : T ≤ Subgroup.normalizer (A : Set G) := by
    intro g hg
    rcases coset_of_relIndex_two k.r66.relIndex_two hg (s_mem_T67 gl) gl.s_not_mem with h | h
    · exact hTEn h
    · have := (Subgroup.normalizer (A : Set G)).mul_mem (hTEn h) hsA
      simpa using this
  have hXEn : XE153 E ≤ Subgroup.normalizer (A : Set G) := by
    intro x hx
    have hxV : x ∈ Subgroup.normalizer (VE67 T M E : Set G) :=
      normalizer_le_normalizer_VE67 T M E
        (Subgroup.centralizer_le_normalizer _ ((oTwoUpper_le _) hx))
    refine conjSubgroup_eq_iff_mem_normalizer.mp ?_
    have hle : A ≤ conjSubgroup A x := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [mem_conjSubgroup_iff]
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hxV a).mp ha)
      · rw [mem_conjSubgroup_iff]
        exact hXE x hx a ha
    exact (Subgroup.eq_of_le_of_card_ge hle
      (CFSG.QuasithinUnique.C5.card_conjSubgroup A x).le).symm
  have hYE : YE153 Mc M E ≤ Subgroup.normalizer (VE67 T M E : Set G) := fun y hy =>
    normalizer_le_normalizer_VE67 T M E (((oTwoUpper_le _).trans inf_le_right) hy)
  have hYFn : YF153 Mc M E s ≤ Subgroup.normalizer (A : Set G) := fun y hy =>
    mem_normalizer_sup67 (hYF hy) (conjSubgroup_le_normalizer_conjSubgroup hYE s hy)
  have hloc : IsTwoLocal (Subgroup.normalizer (A : Set G)) := ⟨A, hAne, hApg, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hInM : InM T M' := ⟨hM', hTn.trans hle⟩
  rcases (k.c.hyp.lemma_15_3_2_three h11).mp hInM with rfl | rfl
  · exact r67.XE_not_le (fun x hx => hle (hXEn hx))
  · exact YF_not_le_Mc h11 h113 k gl (fun y hy => hle (hYFn hy))

end Core

section Order

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

omit [Finite G] in
theorem card_sup_eq_mul67 (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G)) (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B :=
  CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A B hnormal hdisjoint

theorem card_VZ_inf_conj_le (k : Ctx67 G T Mc M V₁ V₂ E t) {g : G} (hg : g ∉ M) :
    Nat.card ↥(VZ T M ⊓ conjSubgroup (VZ T M) g) ≤ 4 := by
  obtain ⟨hAV, hA1, -⟩ := k.r46.totSingular_inter g hg
  set A : Subgroup G := VZ T M ⊓ conjSubgroup (VZ T M) g with hA
  have hV1N : V₁ ≤ Subgroup.normalizer (A : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      F7.isElemAbelian_comm k.c.hyp.elemAbelian (hAV ha) (k.c.decomp.le₁ hv))
  have hcard := card_sup_eq_mul67 A V₁ hV1N (disjoint_iff.mpr hA1)
  have hle : Nat.card ↥(A ⊔ V₁) ≤ Nat.card ↥(VZ T M) :=
    Subgroup.card_le_of_le (sup_le hAV k.c.decomp.le₁)
  rw [hcard, k.c.decomp.card₁, k.c.hyp.card_VZ] at hle
  omega

theorem VZ_inf_conj_eq_E (k : Ctx67 G T Mc M V₁ V₂ E t) {x : G}
    (hxC : x ∈ Subgroup.centralizer (E : Set G)) (hxM : x ∉ M) :
    VZ T M ⊓ conjSubgroup (VZ T M) x⁻¹ = E := by
  have hEle : E ≤ VZ T M ⊓ conjSubgroup (VZ T M) x⁻¹ := by
    intro e he
    refine ⟨k.L.le_V he, mem_conjSubgroup_iff.mpr ?_⟩
    have hc : e * x = x * e := Subgroup.mem_centralizer_iff.mp hxC e he
    have : x⁻¹ * e * (x⁻¹)⁻¹ = e := by
      calc x⁻¹ * e * (x⁻¹)⁻¹ = x⁻¹ * (e * x) := by group
        _ = x⁻¹ * (x * e) := by rw [hc]
        _ = e := inv_mul_cancel_left _ _
    rw [this]
    exact k.L.le_V he
  have hcard := card_VZ_inf_conj_le k (g := x⁻¹) (fun h => hxM (by simpa using M.inv_mem h))
  exact (Subgroup.eq_of_le_of_card_ge hEle (by rw [k.L.card_eq]; exact hcard)).symm

theorem sixtyFour_le_card_VE67 (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) :
    64 ≤ Nat.card ↥(VE67 T M E) := by
  obtain ⟨x, hxX, hxM⟩ := IsConcreteLE.not_le_iff_exists.mp r67.XE_not_le
  have hxC : x ∈ Subgroup.centralizer (E : Set G) := (oTwoUpper_le _) hxX
  have hxN : x ∈ Subgroup.normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ hxC
  have hxMc : x ∈ Mc := k.r66.centralizer_le_mc hxC
  have hVW : VZ T M ⊓ conjSubgroup (VZ T M) x⁻¹ = E := VZ_inf_conj_eq_E k hxC hxM
  set W₀ : Subgroup G := conjSubgroup V₁ x⁻¹ with hW₀
  have hW₀mem : ∀ y ∈ W₀, x⁻¹ * y * x ∈ V₁ := fun y hy => by
    have := mem_conjSubgroup_iff.mp hy
    simpa using this
  have hW₀eq : ∀ y ∈ W₀, y = x * (x⁻¹ * y * x) * x⁻¹ := fun y _ => by group
  have hW₀VE : W₀ ≤ VE67 T M E := fun y hy => by
    have hv : x⁻¹ * y * x ∈ VZ T M := k.c.decomp.le₁ (hW₀mem y hy)
    rw [hW₀eq y hy]
    exact mem_conjClosure hxN hv
  have hW₀Mc : W₀ ≤ conjClosure (VZ T M) Mc := fun y hy => by
    have hv : x⁻¹ * y * x ∈ VZ T M := k.c.decomp.le₁ (hW₀mem y hy)
    rw [hW₀eq y hy]
    exact mem_conjClosure hxMc hv
  have hW₀V : W₀ ≤ Subgroup.normalizer (VZ T M : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      conjClosure_Mc_comm k v (le_conjClosure _ _ hv) y (hW₀Mc hy))
  have hdisj : Disjoint (VZ T M) W₀ := by
    rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
    intro y hy
    have hyW : y ∈ conjSubgroup (VZ T M) x⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have := hW₀mem y hy.2
      simpa using k.c.decomp.le₁ this
    have hyE : y ∈ E := hVW ▸ ⟨hy.1, hyW⟩
    have hc : y * x = x * y := Subgroup.mem_centralizer_iff.mp hxC y hyE
    have : x⁻¹ * y * x = y := by
      calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
        _ = x⁻¹ * (x * y) := by rw [hc]
        _ = y := inv_mul_cancel_left _ _
    have hy1 : y ∈ E ⊓ V₁ := ⟨hyE, by simpa [this] using hW₀mem y hy.2⟩
    rw [k.L.totSingular.2.1] at hy1
    exact hy1
  have hcard := card_sup_eq_mul67 (VZ T M) W₀ hW₀V hdisj
  have hW₀card : Nat.card W₀ = 4 := by
    rw [hW₀, CFSG.QuasithinUnique.C5.card_conjSubgroup, k.c.decomp.card₁]
  have hle : Nat.card ↥(VZ T M ⊔ W₀) ≤ Nat.card ↥(VE67 T M E) :=
    Subgroup.card_le_of_le (sup_le VZ_le_VE67 hW₀VE)
  rw [hcard, hW₀card, k.c.hyp.card_VZ] at hle
  omega

end Order

end S1567

end CFSG.Quasithin
