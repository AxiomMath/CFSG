module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenFour
public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteen

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem twelve_three_of_eq (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g) {U : Subgroup G}
    (hU : uA V V₁ = U) (D : HatModelU U) (hU4 : 4 < (centerOf U).relIndex U) {a : G}
    (haV : a ∈ V) (haZ : a ∉ V₁) :
    G111Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
      (D.hat (U ⊓ Subgroup.centralizer (V : Set G) ⊓
        rconj (U ⊓ Subgroup.centralizer (V : Set G)) g))
      (D.img (rconj (U ⊓ Subgroup.centralizer (V : Set G)) g)) (D.img (rconj (centerOf U) g)) := by
  subst hU
  exact S.twelve_three hg D hU4 haV haZ

end Setting

end L128A

namespace L128P

theorem two_mul_finrank_le_of_isotropic {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (B : LinearMap.BilinForm (ZMod 2) W) (halt : ∀ v, B v v = 0)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) (E : Submodule (ZMod 2) W)
    (hE : ∀ w ∈ E, ∀ w' ∈ E, B w w' = 0) :
    2 * Module.finrank (ZMod 2) E ≤ Module.finrank (ZMod 2) W := by
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hsymm : ∀ x y, B x y = B y x := by
    intro x y
    have h1 := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h1
    exact ((by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) _ _ h1).symm
  have hrefl : B.IsRefl := fun x y h => by rw [hsymm]; exact h
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl E
  have htop : B.orthogonal ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine hnd x fun w => ?_
    have h2 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hx) w Submodule.mem_top
    rw [hsymm]
    exact h2
  rw [htop, inf_bot_eq, finrank_bot, add_zero] at h1
  have h2 : E ≤ B.orthogonal E := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 fun w hw => hE w hw x hx
  have h3 := Submodule.finrank_mono h2
  omega

theorem isSylowTwoOf_of_stabilizer {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {Γ S : Subgroup (W ≃ₗ[ZMod 2] W)} {v : W}
    (hS : IsSylowTwoOf S (Γ ⊓ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) v))
    (hodd : Odd (MulAction.stabilizer Γ v).index) : IsSylowTwoOf S Γ := by
  obtain ⟨hSle, hS2, hSi⟩ := hS
  refine ⟨hSle.trans inf_le_left, hS2, ?_⟩
  have hst : (Γ ⊓ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) v).subgroupOf Γ =
      MulAction.stabilizer Γ v := by
    ext γ
    simp [MulAction.mem_stabilizer_iff]
  have hmul := Subgroup.relIndex_mul_relIndex S (Γ ⊓ MulAction.stabilizer _ v) Γ hSle inf_le_left
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.relIndex, hst] at hmul
  rw [← hmul]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
  · exact hSi h
  · exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)

theorem pRank_le_one_of_sylow_cyclic' {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Sylow p X, IsCyclic ↥(P : Subgroup X)) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E _ hE
  have hpE : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hEP⟩ := hpE.exists_le_sylow
  have hcycP : IsCyclic ↥(P : Subgroup X) := h P
  have hcyc : IsCyclic ↥E := by
    have : IsCyclic ↥(E.subgroupOf (P : Subgroup X)) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEP).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEP).surjective
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hE.2 g g.2)
  have hdvd : Nat.card E ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hgp
  rw [pow_one]
  exact Nat.le_of_dvd hp.pos hdvd

theorem two_le_pRank_of_not_isCyclic' {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup P) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).1 hSel) hScard

theorem two_le_pRank_of_surjective' {A Q : Type} [Group A] [Finite A] [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : A →* Q) (hf : Function.Surjective f)
    (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Q)) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup A) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  have hcycA : ∀ P : Sylow p A, IsCyclic ↥(P : Subgroup A) := by
    intro P
    by_contra hnc
    have h2 := two_le_pRank_of_not_isCyclic' hp hp2 P.isPGroup' hnc
    have h3 := CFSG.SectionRank.pRank_le_map hp.one_lt (P : Subgroup A).subtype
      (P : Subgroup A).subtype_injective ⊤
    have h4 := CFSG.SectionRank.pRank_mono hp.one_lt
      (le_top : ((⊤ : Subgroup ↥(P : Subgroup A)).map (P : Subgroup A).subtype) ≤ ⊤)
    omega
  have hcycQ : ∀ P : Sylow p Q, IsCyclic ↥(P : Subgroup Q) := by
    intro P
    obtain ⟨P', rfl⟩ := Sylow.mapSurjective_surjective hf p P
    have := hcycA P'
    rw [Sylow.coe_mapSurjective]
    refine isCyclic_of_surjective
      (((f.comp (P' : Subgroup A).subtype).codRestrict ((P' : Subgroup A).map f)
        fun x => ⟨x, x.2, rfl⟩) : ↥(P' : Subgroup A) →* ↥((P' : Subgroup A).map f)) ?_
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have h1 := pRank_le_one_of_sylow_cyclic' hp hcycQ
  omega

variable {G : Type} [Group G] [Finite G]

theorem lt_zU_of_elemAbelian (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂)
    (D : HatModelU (u128 V V₁)) {a : G} (ha : a ∈ V₂) (haV₁ : a ∉ V₁)
    {Y : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (hYΓ : Y ≤ D.img (Subgroup.normalizer (V₁ : Set G))) (hYv : ∀ y ∈ Y, y (D.π a) = D.π a)
    (hY3 : IsElemAbelian 3 Y) (hY9 : Nat.card Y = 9) : V₁ < zU128 V V₁ := by
  classical
  have hle : V₁ ≤ zU128 V V₁ := hs.le_centerOf h1222 h12213
  refine lt_of_le_of_ne hle fun heq => ?_
  obtain ⟨-, -, hab⟩ := hs.hyp.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨z, hz, hz1, -, -, -⟩ := exists_gens hV₁2 hV₂4
  set C := centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂ with hCdef
  have hCN : C ≤ Subgroup.normalizer (u128 V V₁ : Set G) := fun x hx =>
    le_normalizer_conjClosure V _ hx.1
  have haV := hs.v2.1 ha
  have haU : a ∈ u128 V V₁ := le_conjClosure V _ haV
  have hYC : Y ≤ D.img C := by
    intro y hy
    obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).1 (hYΓ hy)
    refine (L128A.HatU.mem_img D).2 ⟨h, ?_, hhN, rfl⟩
    have h1 := hYv _ hy
    have heq' : centerOf (u128 V V₁) = V₁ := heq.symm
    rw [D.ρ_π ⟨h, hhN⟩ a haU, D.π_eq_iff _ (L128A.HatU.conj_mem hhN haU) a haU, heq'] at h1
    set c := (h * a * h⁻¹)⁻¹ * a with hcdef
    have hcV := hs.v1.1 h1
    have hha : h * a * h⁻¹ = a * c⁻¹ := by rw [hcdef]; group
    have hcomm : h * a * h⁻¹ * a⁻¹ ∈ V₁ := by
      rw [hha, hab a haV c⁻¹ (V.inv_mem hcV)]
      have e : c⁻¹ * a * a⁻¹ = c⁻¹ := by group
      rw [e]
      exact V₁.inv_mem h1
    have hhz : h * z * h⁻¹ = z := L1297.conj_eq_of_mem_normalizer hV₁2 hz hh
    refine ⟨hh, hh, fun w hw => ?_⟩
    rcases eq_of_mem_four hs.le hV₁2 hV₂4 hz hz1 haV₁ ha hw with e | e | e | e <;> rw [e]
    · simp
    · rw [hhz, mul_inv_cancel]
      exact V₁.one_mem
    · exact hcomm
    · have e2 : h * (z * a) * h⁻¹ * (z * a)⁻¹ = (h * z * h⁻¹) * (h * a * h⁻¹ * a⁻¹) * z⁻¹ := by
        group
      rw [e2, hhz]
      have hc' : h * a * h⁻¹ * a⁻¹ ∈ V := hs.v1.1 hcomm
      rw [hab z (hs.v1.1 hz) _ hc']
      have e3 : h * a * h⁻¹ * a⁻¹ * z * z⁻¹ = h * a * h⁻¹ * a⁻¹ := by group
      rw [e3]
      exact hcomm
  have hpr : 2 ≤ CFSG.Open.pRank 3 (D.img C) :=
    CFSG.SectionRank.le_pRank (by norm_num) hYC hY3 (by rw [hY9]; norm_num)
  rw [L1294.img_eq_range D hCN, ← pRank_top_subtype (p := 3)] at hpr
  have h2 := two_le_pRank_of_surjective' Nat.prime_three (by norm_num)
    (D.ρ.comp (Subgroup.inclusion hCN)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _) hpr
  rw [pRank_top_subtype (p := 3)] at h2
  have h3 : CFSG.Open.pRank 3 C ≤ 1 := thirteen_eight h1222 h12213 hs
  omega

end L128P

open L128P in
theorem lemma12_8_13_six_hat_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1228 : Stmt12_2_8) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h5 : Lemma12_8_8_five) (hKG : A7NatFact12813) : Lemma12_8_13_six_hat := by
  intro G _ _ T L V n V₁ V₂ hs hn D hC4
  obtain ⟨k, hk, hkN⟩ := exists_not_mem_normalizer h1222 hs
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨-, -, -, a, haV₂, haV₁⟩ := exists_gens hV₁2 hV₂4
  have S := setting128A h1222 h12213 hs
  have hUeq := uA_eq h1222 hs
  have hgood : L128A.Good V₁ (oTwoUpper (p128 T L V)) k := ⟨hk, hkN⟩
  have hG := S.twelve_three_of_eq hgood hUeq D (four_lt_relIndex h1222 h12213 hs) haV₂ haV₁
  set Γ := D.img (Subgroup.normalizer (V₁ : Set G)) with hΓ
  set v := D.π a with hv
  set W := D.hat (u128 V V₁ ⊓ Subgroup.centralizer (V₂ : Set G) ⊓
    rconj (u128 V V₁ ⊓ Subgroup.centralizer (V₂ : Set G)) k) with hW
  set X := D.img (rconj (u128 V V₁ ⊓ Subgroup.centralizer (V₂ : Set G)) k) with hX
  set X₀ := D.img (rconj (centerOf (u128 V V₁)) k) with hX₀
  obtain ⟨S', hS'syl, hXS', -⟩ := hG.four
  have hS'Γ := isSylowTwoOf_of_stabilizer hS'syl hG.odd_index
  have hS'v : ∀ s ∈ S', s v = v := fun s hs' =>
    MulAction.mem_stabilizer_iff.1 (hS'syl.1 hs').2
  obtain ⟨Up, hUpS, hUpv, hvUp, hcases⟩ :=
    hKG D.V D.B Γ S' v hC4 hG.alt hG.nondegenerate hG.isometry hS'Γ hG.point hS'v
  have hUE : ∀ w ∈ Up, w ∈ W → w = 0 := by
    intro w hwU hwW
    by_contra hw0
    have hspan : (⟨w, hwW⟩ : W) ∉ (ZMod 2) ∙ (⟨v, hG.mem_W⟩ : W) := by
      intro hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have hc' : c • v = w := by
        have := congrArg Subtype.val hc
        simpa using this
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · exact hw0 (by rw [← hc', zero_smul])
      · rw [one_smul] at hc'
        exact hvUp (by rw [hc']; exact hwU)
    obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hspan
    have hfv : f ⟨v, hG.mem_W⟩ = 0 :=
      LinearMap.mem_ker.1 (hker (Submodule.mem_span_singleton_self _))
    obtain ⟨x, hxX, hx⟩ := hG.transvection_full f hfv
    have h1 := hx ⟨w, hwW⟩
    have hf1 : f ⟨w, hwW⟩ = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hf
    rw [hf1, one_smul] at h1
    have h1' : x w = w + v := by simpa using h1
    have hxw : x w ∈ Up := hUpS x (hXS' hxX) w hwU
    apply hvUp
    have e : v = x w - w := by
      rw [h1']
      abel
    rw [e]
    exact Up.sub_mem hxw hwU
  have hXU : ∀ x ∈ X, ∀ u ∈ Up, x u = u := by
    intro x hx u hu
    have h1 := hG.commutator_le x hx u (hUpv u hu)
    have h2 : x u - u ∈ Up := Up.sub_mem (hUpS x (hXS' hx) u hu) hu
    exact sub_eq_zero.1 (hUE _ h2 h1)
  have hXel : IsElemAbelian 2 X :=
    ⟨⟨⟨fun a b => Subtype.ext (hG.X_comm _ a.2 _ b.2)⟩⟩, fun x hx => by
      rw [sq]
      exact hG.X_sq x hx⟩
  have hrank := hG.rank
  have hW3 := two_mul_finrank_le_of_isotropic D.B hG.alt hG.nondegenerate W hG.isotropic
  rw [hC4.1] at hrank hW3
  have hlog : 2 ≤ Nat.log 2 (X₀.relIndex X) := by omega
  have hne : X₀.relIndex X ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : 4 ≤ X₀.relIndex X :=
    (Nat.pow_le_pow_right (by norm_num) hlog).trans (Nat.pow_log_le_self 2 hne)
  have hcardX := Subgroup.relIndex_mul_card X₀ X
  rw [inf_eq_left.2 hG.X₀_le] at hcardX
  rcases hcases with h2 | ⟨h4, Y, hYΓ, hYv, hY3, hY9⟩
  ·
    have hX2 := h2 X hXS' hXel hXU
    have := Nat.le_mul_of_pos_right (X₀.relIndex X) (Nat.card_pos (α := ↥X₀))
    omega
  ·
    have hX4 := h4 X hXS' hXel hXU
    have hZ := lt_zU_of_elemAbelian h1222 h12213 hs D haV₂ haV₁ hYΓ hYv hY3 hY9
    have h4' := thirteen_four h1222 h12213 h1228 h37 h38 h39 h5 hs hn (oTwoUpper_le _ hk) hkN hZ
    have hTU : T ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
      (hs.almostSpecial h1222 h12213).G22_three.2
    have hX₀ne : X₀ ≠ ⊥ := by
      intro hb
      apply h4'
      intro z hz
      have hzA : z ∈ rconj (centerOf (L128A.uA V₂ V₁)) k := by
        rw [hUeq]
        exact hz
      have hzT : z ∈ T := S.rconj_wA_le_T hgood
        (L128A.Setting.rconj_centerOf_le_rconj_wA V₂ V₁ k hzA)
      have hzN : z ∈ Subgroup.normalizer (u128 V V₁ : Set G) := hTU hzT
      have hρ : D.ρ ⟨z, hzN⟩ = 1 := by
        have h5' : D.ρ ⟨z, hzN⟩ ∈ X₀ := L128A.HatU.rho_mem_img D hz hzN
        rw [hb] at h5'
        exact Subgroup.mem_bot.1 h5'
      exact ⟨hs.v1.2.2 hzT, normalizer_le_normalizer_centerOf _ hzN,
        (L128A.HatU.rho_eq_one_iff D ⟨z, hzN⟩).1 hρ⟩
    have hX₀2 : 2 ≤ Nat.card X₀ := (Subgroup.one_lt_card_iff_ne_bot X₀).2 hX₀ne
    have := Nat.mul_le_mul_left (X₀.relIndex X) hX₀2
    omega

end CFSG.Quasithin.H13
