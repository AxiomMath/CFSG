module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2J
public import CFSG.Quasithin.Vol2.Ch12Sec6T2Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_conj_not_le_D (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAQ : ¬ A ≤ Qv T V) {i j : Fin 8} (hij : i ≠ j)
    (hpair : ∀ a ∈ A, ∀ τ : Equiv.Perm (Fin 8), ActsAs F a τ →
      (τ i = i ∧ τ j = j) ∨ (τ i = j ∧ τ j = i)) :
    ∃ A'' : Subgroup G, IsMaxElemAbelian (Tv T v) A'' ∧ Nat.card A'' = Nat.card A ∧
      ¬ A'' ≤ centralizerSection ((L ⊔ T) ⊓ Gv v) (Lv L v) (pCoreOf 2 (Lv L v)) := by
  classical
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  have hAT : A ≤ T := hA.1
  obtain ⟨a₀, ha₀A, ha₀Q⟩ : ∃ a ∈ A, a ∉ Qv T V := by
    by_contra h
    push Not at h
    exact hAQ h
  obtain ⟨τ₀, -, hτ₀⟩ := actsAs_of_mem_T F (hAT ha₀A)
  have hτ₀1 : τ₀ ≠ 1 := fun e => ha₀Q ⟨hAT ha₀A, mem_centralizer_of_actsAs_one F hVL hLV
    (hTL (hAT ha₀A)) (hTV (hAT ha₀A)) (e ▸ hτ₀)⟩
  obtain ⟨i', j', hij', hpair', a₁, ha₁A, τ₁, hτ₁, k, hki, hkj, hτ₁k⟩ : ∃ i' j' : Fin 8, i' ≠ j' ∧
      (∀ a ∈ A, ∀ τ : Equiv.Perm (Fin 8), ActsAs F a τ →
        (τ i' = i' ∧ τ j' = j') ∨ (τ i' = j' ∧ τ j' = i')) ∧
      ∃ a₁ ∈ A, ∃ τ₁ : Equiv.Perm (Fin 8), ActsAs F a₁ τ₁ ∧
        ∃ k : Fin 8, k ≠ i' ∧ k ≠ j' ∧ τ₁ k ≠ k := by
    by_cases hout : ∃ a ∈ A, ∃ τ : Equiv.Perm (Fin 8), ActsAs F a τ ∧
        ∃ k : Fin 8, k ≠ i ∧ k ≠ j ∧ τ k ≠ k
    · exact ⟨i, j, hij, hpair, hout⟩
    · push Not at hout
      obtain ⟨k, l, hkl, hki, hkj, hli, hlj⟩ := S126L23c.exists_two_ne i j
      have hfix : ∀ a ∈ A, ∀ τ : Equiv.Perm (Fin 8), ActsAs F a τ → τ k = k ∧ τ l = l :=
        fun a ha τ hτ => ⟨hout a ha τ hτ k hki hkj, hout a ha τ hτ l hli hlj⟩
      obtain ⟨m, hm⟩ : ∃ m, τ₀ m ≠ m := by
        by_contra h
        push Not at h
        exact hτ₀1 (Equiv.ext h)
      have hmij : m = i ∨ m = j := by
        by_contra h
        push Not at h
        exact hm (hout a₀ ha₀A τ₀ hτ₀ m h.1 h.2)
      refine ⟨k, l, hkl, fun a ha τ hτ => Or.inl (hfix a ha τ hτ), a₀, ha₀A, τ₀, hτ₀, m, ?_, ?_,
        hm⟩
      · rintro rfl
        rcases hmij with rfl | rfl
        · exact hki rfl
        · exact hkj rfl
      · rintro rfl
        rcases hmij with rfl | rfl
        · exact hli rfl
        · exact hlj rfl
  obtain ⟨σ, hσ⟩ := exists_dAct (by norm_num : 2 ≤ 6) (⟨pe i' j', rfl, S126L20a.wt_pe hij'⟩ :
    HasWt 2 (QuotientGroup.mk (pe i' j') : D8)) (⟨pe 0 1, rfl, S126L20a.wt_pe (by decide)⟩ :
    HasWt 2 (QuotientGroup.mk (pe 0 1) : D8))
  rw [S126L20a.dAct_pe] at hσ
  have hσ01 : ((σ : Equiv.Perm (Fin 8)) i' = 0 ∧ (σ : Equiv.Perm (Fin 8)) j' = 1) ∨
      ((σ : Equiv.Perm (Fin 8)) i' = 1 ∧ (σ : Equiv.Perm (Fin 8)) j' = 0) := by
    rcases mk_pe_eq_mk_pe (by decide : (0 : Fin 8) ≠ 1) hσ.symm with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2⟩
  obtain ⟨l, hl⟩ := S126L19a.psi_surjective F hH σ
  have hlσ : ActsAs F l σ := hl ▸ S126L19a.actsAs_psi F hH l
  have hlN := hLV l.2
  set A' := B6.conjSub (l : G) A with hA'
  have hconjact : ∀ x ∈ A', ∃ a ∈ A, ∃ τ : Equiv.Perm (Fin 8), ActsAs F a τ ∧
      ActsAs F x ((σ : Equiv.Perm (Fin 8)) * τ * (σ : Equiv.Perm (Fin 8))⁻¹) ∧
      x = (l : G) * a * (l : G)⁻¹ := by
    intro x hx
    rw [hA', B6.mem_conjSub] at hx
    obtain ⟨τ, -, hτ⟩ := actsAs_of_mem_T F (hAT hx)
    have e : x = (l : G) * ((l : G)⁻¹ * x * (l : G)) * (l : G)⁻¹ := by group
    refine ⟨_, hx, τ, hτ, ?_, e⟩
    rw [e]
    exact (hlσ.mul hτ (hTV (hAT hx))).mul hlσ.inv (Subgroup.inv_mem _ hlN)
  have hA'H : A' ≤ (L ⊔ T) ⊓ Gv v := by
    intro x hx
    obtain ⟨a, ha, τ, hτ, hx', rfl⟩ := hconjact x hx
    have haN : a ∈ L ⊔ T := le_sup_right (a := L) (hAT ha)
    have hxLT : (l : G) * a * (l : G)⁻¹ ∈ L ⊔ T :=
      (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (le_sup_left (b := T) l.2) haN)
        ((L ⊔ T).inv_mem (le_sup_left (b := T) l.2))
    refine ⟨hxLT, (mem_Gv_iff h1222 F hH hv hβ (hLTL hxLT) (hLTV hxLT) hx').2 ?_⟩
    have hσi : (σ : Equiv.Perm (Fin 8))⁻¹ 0 = i' ∧ (σ : Equiv.Perm (Fin 8))⁻¹ 1 = j' ∨
        (σ : Equiv.Perm (Fin 8))⁻¹ 0 = j' ∧ (σ : Equiv.Perm (Fin 8))⁻¹ 1 = i' := by
      rcases hσ01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inl ⟨by rw [Equiv.Perm.inv_eq_iff_eq, h0], by rw [Equiv.Perm.inv_eq_iff_eq, h1]⟩
      · exact Or.inr ⟨by rw [Equiv.Perm.inv_eq_iff_eq, h1], by rw [Equiv.Perm.inv_eq_iff_eq, h0]⟩
    simp only [Equiv.Perm.mul_apply]
    rcases hσi with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rw [e0, e1] <;>
      rcases hpair' a ha τ hτ with ⟨f0, f1⟩ | ⟨f0, f1⟩ <;> rw [f0, f1] <;>
      rcases hσ01 with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> rw [g0, g1] <;> simp
  have hTsyl := isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow (le_top : T ≤ ⊤)
  have hAtop : IsMaxElemAbelian ⊤ A := B6.isMaxElemAbelian_of_sylow hTsyl hA
  have hA'max : IsMaxElemAbelian ((L ⊔ T) ⊓ Gv v) A' :=
    ⟨hA'H, B6.isElemAbelian_conjSub hA.2.1 _, fun B _ hB => by
      rw [hA', B6.card_conjSub]
      exact hAtop.2.2 B le_top hB⟩
  obtain ⟨h, hhH, hA''⟩ := B6.exists_conj_isMaxElemAbelian_of_sylow
    (isSylowTwoOf_Tv h1222 F hH hv hβ) hA'max
  refine ⟨_, hA'', by rw [B6.card_conjSub, hA', B6.card_conjSub], fun hle => ?_⟩
  have hx₁ : h * ((l : G) * a₁ * (l : G)⁻¹) * h⁻¹ ∈ B6.conjSub h A' := by
    rw [B6.mem_conjSub, show h⁻¹ * (h * ((l : G) * a₁ * (l : G)⁻¹) * h⁻¹) * h =
      (l : G) * a₁ * (l : G)⁻¹ by group, hA', B6.mem_conjSub,
      show (l : G)⁻¹ * ((l : G) * a₁ * (l : G)⁻¹) * l = a₁ by group]
    exact ha₁A
  obtain ⟨ρ, hρ⟩ := exists_actsAs F hH (hLTL hhH.1) (hLTV hhH.1)
  have hρ01 := (mem_Gv_iff h1222 F hH hv hβ (hLTL hhH.1) (hLTV hhH.1) hρ).1 hhH.2
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 8), π = ρ * (σ : Equiv.Perm (Fin 8)) := ⟨_, rfl⟩
  have hact : ActsAs F (h * ((l : G) * a₁ * (l : G)⁻¹) * h⁻¹) (π * τ₁ * π⁻¹) := by
    have h1 := ((hρ.mul ((hlσ.mul hτ₁ (hTV (hAT ha₁A))).mul hlσ.inv (Subgroup.inv_mem _ hlN))
      ((Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN (hTV (hAT ha₁A)))
        (Subgroup.inv_mem _ hlN)))).mul hρ.inv (Subgroup.inv_mem _ (hLTV hhH.1)))
    rwa [show ρ * ((σ : Equiv.Perm (Fin 8)) * τ₁ * (σ : Equiv.Perm (Fin 8))⁻¹) * ρ⁻¹ =
      π * τ₁ * π⁻¹ by rw [hπ]; group] at h1
  have hperm := perm_of_mem_D h1222 F hH hv hβ (hle hx₁) hact
  have hπk0 : π k ≠ 0 ∧ π k ≠ 1 := by
    have hk' : (σ : Equiv.Perm (Fin 8)) k ≠ 0 ∧ (σ : Equiv.Perm (Fin 8)) k ≠ 1 := by
      rcases hσ01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact ⟨fun e => hki ((σ : Equiv.Perm (Fin 8)).injective (e.trans h0.symm)),
          fun e => hkj ((σ : Equiv.Perm (Fin 8)).injective (e.trans h1.symm))⟩
      · exact ⟨fun e => hkj ((σ : Equiv.Perm (Fin 8)).injective (e.trans h1.symm)),
          fun e => hki ((σ : Equiv.Perm (Fin 8)).injective (e.trans h0.symm))⟩
    rw [hπ, Equiv.Perm.mul_apply]
    rcases hρ01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨fun e => hk'.1 (ρ.injective (e.trans h0.symm)),
        fun e => hk'.2 (ρ.injective (e.trans h1.symm))⟩
    · exact ⟨fun e => hk'.2 (ρ.injective (e.trans h1.symm)),
        fun e => hk'.1 (ρ.injective (e.trans h0.symm))⟩
  have hfixπ : (π * τ₁ * π⁻¹) (π k) = π k := by
    rcases hperm with h1 | h1
    · rw [h1, Equiv.Perm.one_apply]
    · rw [h1, Equiv.swap_apply_of_ne_of_ne hπk0.1 hπk0.2]
  apply hτ₁k
  apply π.injective
  calc π (τ₁ k) = (π * τ₁ * π⁻¹) (π k) := by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          show π⁻¹ (π k) = k from Equiv.Perm.inv_eq_iff_eq.2 rfl]
    _ = π k := hfixπ

omit [IsMulCommutative ↥V] in
theorem V_facts (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) : V ≤ T ∧ IsElemAbelian 2 V := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  exact ⟨hVT, isElemAbelian_of_reduced (hVT.trans le_sup_right) hred⟩

theorem exists_max_le_Tv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hJ : ¬ thompsonJ T ≤ Qv T V) : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ A ≤ Tv T v := by
  classical
  obtain ⟨hVT, hVe⟩ := V_facts h1222 hH
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun w hw => comm_of_mem hw hx
  have hQTv : Qv T V ≤ Tv T v := le_inf inf_le_left (Qv_le_Gv hv)
  obtain ⟨A₀, hA₀, hA₀Q⟩ : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ¬ A ≤ Qv T V := by
    by_contra h
    push Not at h
    exact hJ (iSup₂_le fun A hA => h A hA)
  by_cases hpair : ∃ i j : Fin 8, i ≠ j ∧ ∀ a ∈ A₀, ∀ τ : Equiv.Perm (Fin 8), ActsAs F a τ →
      (τ i = i ∧ τ j = j) ∨ (τ i = j ∧ τ j = i)
  · obtain ⟨i, j, hij, hp⟩ := hpair
    obtain ⟨A'', hA'', hcard, -⟩ := exists_conj_not_le_D h1222 F hH hv hβ hA₀ hA₀Q hij hp
    refine ⟨A'', ⟨hA''.1.trans inf_le_left, hA''.2.1, fun B hB hBe => ?_⟩, hA''.1⟩
    rw [hcard]
    exact hA₀.2.2 B hB hBe
  · push Not at hpair
    have hNP : ∀ i j : Fin 8, i ≠ j → ∃ a ∈ A₀, ∃ τ : Equiv.Perm (Fin 8), ActsAs F a τ ∧
        ¬ ((τ i = i ∧ τ j = j) ∨ (τ i = j ∧ τ j = i)) := by
      intro i j hij
      obtain ⟨a, ha, τ, hτ, hn⟩ := hpair i j hij
      refine ⟨a, ha, τ, hτ, fun h => ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hn.1 h1 h2
      · exact hn.2 h1 h2
    have hle := offender_le h1222 F hH hA₀.1 hA₀.2.1 hNP
    have hge := card_le_relIndex_mul_card hVe hVT hA₀
    have hA₁ := (B24_three hVe hVT hA₀ (le_antisymm hge hle)).1
    exact ⟨_, hA₁, (sup_le (le_inf (inf_le_left.trans hA₀.1) inf_le_right)
      (le_inf hVT hVC)).trans hQTv⟩

theorem part6 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) (hJ : ¬ thompsonJ T ≤ Qv T V) :
    Lv L v = ⁅Lv L v, thompsonJ (Tv T v)⁆ ∨ thompsonJ (Tv T v) = thompsonJ (Qv T V) := by
  classical
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hQTv : Qv T V ≤ Tv T v := le_inf inf_le_left (Qv_le_Gv hv)
  have hJTv : thompsonJ (Tv T v) ≤ (L ⊔ T) ⊓ Gv v :=
    (B6.thompsonJ_le _).trans (inf_le_inf_right _ le_sup_right)
  rcases comm_eq_or_le_D h1222 F hH hv hβ hJTv with h1 | hJD
  · exact Or.inl h1.symm
  right
  have hKC : ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ Tv T v → A ≤ Qv T V := by
    intro A hA hATv
    by_contra hAQ
    obtain ⟨A'', hA'', -, hA''D⟩ := exists_conj_not_le_D h1222 F hH hv hβ hA hAQ
      (by decide : (0 : Fin 8) ≠ 1) fun a ha τ hτ =>
        (mem_Gv_iff h1222 F hH hv hβ (hTL (hATv ha).1) (hTV (hATv ha).1) hτ).1 (hATv ha).2
    exact hA''D ((B6.le_thompsonJ hA'').trans hJD)
  obtain ⟨A₁, hA₁, hA₁Tv⟩ := exists_max_le_Tv h1222 F hH hv hβ hJ
  have hsub : ∀ A : Subgroup G, IsMaxElemAbelian (Tv T v) A → IsMaxElemAbelian T A :=
    fun A hA => ⟨hA.1.trans inf_le_left, hA.2.1, fun B hB hBe =>
      (hA₁.2.2 B hB hBe).trans (hA.2.2 _ hA₁Tv hA₁.2.1)⟩
  have hJQ : thompsonJ (Tv T v) ≤ Qv T V :=
    iSup₂_le fun A hA => hKC A (hsub A hA) hA.1
  exact (B6.thompsonJ_eq_of_le hJQ hQTv).symm

theorem normalizer_JQ_le (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    Subgroup.normalizer (thompsonJ (Qv T V) : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hyp := hH.hyp
  obtain ⟨hVT, hVe⟩ := V_facts h1222 hH
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun w hw => comm_of_mem hw hx
  have hJ1 : thompsonJ (Qv T V) ≠ ⊥ := by
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian (Qv T V)
    have hcard := hA₀.2.2 V (le_inf hVT hVC) hVe
    intro h
    have hA₀1 : A₀ = ⊥ := eq_bot_iff.2 ((B6.le_thompsonJ hA₀).trans h.le)
    rw [hA₀1, Subgroup.card_bot] at hcard
    exact hV1 (Subgroup.eq_bot_of_card_le V hcard)
  have hJ2 : IsPGroup 2 (thompsonJ (Qv T V)) :=
    hyp.sylow.1.to_le ((B6.thompsonJ_le _).trans inf_le_left)
  have hLTJ : L ⊔ T ≤ Subgroup.normalizer (thompsonJ (Qv T V) : Set G) :=
    (LT_le_normalizer_Qv h1222 hH).trans (normalizer_le_normalizer_thompsonJ _)
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨thompsonJ (Qv T V), hJ1, hJ2, rfl⟩ : IsTwoLocal _)
  rw [← huniq M' hM' (hLTJ.trans hle)]
  exact hle

theorem Lv_not_le (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {P : Subgroup G}
    (hP : IsPGroup 2 P) : ¬ Lv L v ≤ P := by
  intro hle
  have hbot : (Lv L v).map (MonoidHom.id G) = ⊥ :=
    map_eq_bot_of_perfect (perfectCore_perfect _) _ (isSolvable_of_isPGroup (by
      rw [Subgroup.map_id]
      exact hP.to_le hle))
  rw [Subgroup.map_id] at hbot
  obtain ⟨l, hl, hla⟩ := exists_Lv_of_A6s h1222 F hH hv hβ (cy 2 3 4)
    (cy_mem (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [hbot, Subgroup.mem_bot] at hl
  have hl1 : l = 1 := Subtype.ext hl
  rw [hl1, map_one] at hla
  exact cyc_three.2 hla.symm

end S126T2

theorem lemma12_6_6_9_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6)
    (hD2 : Lemma12_6_4_5) : Lemma12_6_6_9 := by
  intro G _ _ T L V _ F v Kv S hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hS := hC.sylow
  have hTvS := hC.tv_le
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hQTv : Qv T V ≤ Tv T v := le_inf inf_le_left (Qv_le_Gv hv)
  have hTvT : Tv T v ≤ T := inf_le_left
  have h7a : thompsonJ T ≤ Qv T V →
      thompsonJ T = thompsonJ (Qv T V) ∧ thompsonJ (Qv T V) = thompsonJ (Tv T v) := by
    intro hJ
    have e1 := B6.thompsonJ_eq_of_le hJ (inf_le_left : Qv T V ≤ T)
    have e2 := B6.thompsonJ_eq_of_le (hJ.trans hQTv) hTvT
    exact ⟨e1.symm, e1.trans e2.symm⟩
  have h7b : Lv L v = ⁅Lv L v, thompsonJ (Tv T v)⁆ → L = ⁅L, thompsonJ T⁆ := by
    intro hL
    by_cases hJ : thompsonJ T ≤ Qv T V
    · exfalso
      have hJv : thompsonJ (Tv T v) ≤ Qv T V := by
        rw [← (h7a hJ).2]
        exact B6.thompsonJ_le _
      have hle : ⁅Lv L v, thompsonJ (Tv T v)⁆ ≤ Qv T V := by
        rw [Subgroup.commutator_le]
        intro l hl j hj
        rw [commutatorElement_def]
        have hlLT : l ∈ L ⊔ T := le_sup_left (b := T) (Lv_le_L L v hl)
        have h1 : l * j * l⁻¹ ∈ Qv T V :=
          (Subgroup.mem_normalizer_iff.1 (LT_le_normalizer_Qv h1222 hH hlLT) j).1 (hJv hj)
        exact (Qv T V).mul_mem h1 ((Qv T V).inv_mem (hJv hj))
      exact Lv_not_le (P := Qv T V) h1222 F hH hv hβ (hH.hyp.sylow.1.to_le inf_le_left)
        (hL.le.trans hle)
    · exact L_eq_comm h1222 F hH hJ
  have h6 := fun hJ => part6 h1222 F hH hv hβ hJ
  have h8 : thompsonJ (Tv T v) ≤ Qv T V → S = Tv T v ∧ Rsec L Kv S v = Rv T L v ∧
      thompsonJ (Tv T v) = thompsonJ (Rv T L v) ∧ thompsonJ (Rv T L v) = thompsonJ (Qv T V) ∧
      Subgroup.normalizer (thompsonJ S : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro hJ
    have hJeq : thompsonJ (Qv T V) = thompsonJ (Tv T v) := B6.thompsonJ_eq_of_le hJ hQTv
    have hNJ := normalizer_JQ_le h331 h1222 hH
    set W := Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) with hW
    have hLTW : L ⊔ T ≤ W := le_inf (sup_le Subgroup.le_normalizer hTL) (sup_le hLV hTV)
    have hsyl := isSylowTwoOf_Tv_of_le h1222 F hH hv hβ hLTW le_rfl
    have hv1 : v ≠ 1 := by
      rintro rfl
      have h1 : F.β ⟨1, hv⟩ = 1 := map_one F.β
      rw [h1] at hβ
      exact ne_one_of_nonsing (⟨pe 0 1, rfl, S126L20a.wt_pe (by decide)⟩ :
        IsNonsing (QuotientGroup.mk (pe 0 1) : D8)) hβ.symm
    have hGvN : Gv v ≤ Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
      fun g hg => A4.mem_normalizer_of_conj_mem fun x hx => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [Gv, Subgroup.mem_centralizer_singleton_iff] at hg
        have e : g * v * g⁻¹ = v := by rw [hg, mul_inv_cancel_right]
        rw [← conj_zpow, e]
        exact Subgroup.zpow_mem_zpowers v k
    have h1226' := (h1226 G T L V hH.hyp).2 (Subgroup.zpowers v) (Gv v)
      (by rwa [Ne, Subgroup.zpowers_eq_bot]) (Subgroup.zpowers_le.2 hv) hGvN
    have hNS : S ⊓ Subgroup.normalizer (Tv T v : Set G) = Tv T v := by
      refine hsyl.eq_of_le (le_inf hTvS Subgroup.le_normalizer) ?_ (hS.2.1.to_inf_left)
      intro x hx
      have hxM : x ∈ Subgroup.normalizer (L : Set G) := by
        refine hNJ ?_
        rw [hJeq]
        exact normalizer_le_normalizer_thompsonJ _ hx.2
      have hxG : x ∈ Gv v := hS.1 hx.1
      have h2 : x ∈ Gv v ⊓ Subgroup.normalizer (V : Set G) := h1226' ▸ ⟨hxG, hxM⟩
      exact ⟨⟨hxM, h2.2⟩, hxG⟩
    have hSeq : S = Tv T v := by
      by_contra hne
      have hlt : (Tv T v).subgroupOf S < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h
        apply hne
        refine le_antisymm (fun s hs => ?_) hTvS
        have := h ▸ Subgroup.mem_top (⟨s, hs⟩ : ↥S)
        exact this
      have : Group.IsNilpotent ↥S := hS.2.1.isNilpotent
      obtain ⟨s, hsN, hsT⟩ :=
        IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
      have hsN' : (s : G) ∈ Subgroup.normalizer (Tv T v : Set G) :=
        A4.mem_normalizer_of_conj_mem fun t ht => by
          have h1 := (Subgroup.mem_normalizer_iff.1 hsN ⟨t, hTvS ht⟩).1 ht
          rw [Subgroup.mem_subgroupOf] at h1
          simpa using h1
      have hsS : (s : G) ∈ S ⊓ Subgroup.normalizer (Tv T v : Set G) := ⟨s.2, hsN'⟩
      rw [hNS] at hsS
      exact hsT hsS
    obtain ⟨-, hb, -⟩ := hD2 G T L V F v Kv S hC
    have hRS : Rsec L Kv S v ≤ S := centralizerSection_le_left _ _ _
    have hRTv : Rsec L Kv S v ≤ Tv T v := hRS.trans hSeq.le
    have hRv : Rv T L v = Rsec L Kv S v := by rw [hb, inf_eq_left.2 hRTv]
    have hQRv := Qv_le_Rv h1222 hH hv
    have hRvTv : Rv T L v ≤ Tv T v := hRv ▸ hRTv
    have hJR : thompsonJ (Rv T L v) = thompsonJ (Tv T v) :=
      B6.thompsonJ_eq_of_le (hJ.trans hQRv) hRvTv
    refine ⟨hSeq, hRv.symm, hJR.symm, hJR.trans hJeq.symm, ?_⟩
    rw [hSeq, ← hJeq]
    exact hNJ
  refine ⟨h6, h7a, h7b, h8, fun hJ => ?_⟩
  have hJT : ¬ thompsonJ T ≤ Qv T V := fun h => hJ (by
    rw [← (h7a h).2]
    exact B6.thompsonJ_le _)
  refine ⟨hJT, ?_⟩
  rcases h6 hJT with h | h
  · exact h
  · exact absurd (by rw [h]; exact B6.thompsonJ_le _) hJ

end CFSG.Quasithin.H13
