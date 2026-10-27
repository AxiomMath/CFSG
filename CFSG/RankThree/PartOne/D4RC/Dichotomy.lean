module

public import CFSG.RankThree.PartOne.D4RC.Standard
public import CFSG.Timmesfeld.ARS.CaseHBasic

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7 CFSG.Timmesfeld.ARS
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement

variable {K : Type} [Field K] {σ : K →+* K}

theorem rcg_exists_mul_of_mem_sup {G : Type*} [Group G] {H L : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ L, Commute x y) {z : G} (hz : z ∈ H ⊔ L) :
    ∃ a ∈ H, ∃ b ∈ L, a * b = z := by
  let P : Subgroup G :=
    { carrier := {z | ∃ a ∈ H, ∃ b ∈ L, a * b = z}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', H.mul_mem ha ha', b * b', L.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [(h a' ha' b hb).eq]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, H.one_mem, 1, L.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, L.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [(h a ha b hb).eq]  }
  have hHP : H ≤ P := fun a ha => ⟨a, ha, 1, L.one_mem, by simp⟩
  have hLP : L ≤ P := fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩
  exact (sup_le hHP hLP) hz

theorem rcg_coveredBy_conj {G : Type*} [Group G] {R : Set (Subgroup G)}
    (hR : ∀ A ∈ R, ∀ g : G, conjSub A g ∈ R) {H : Subgroup G} (h : CoveredBy R H) (g : G) :
    CoveredBy R (conjSub H g) := by
  rintro _ ⟨x, hx, rfl⟩ hx1
  have hx1' : x ≠ 1 := fun e => hx1 (by rw [e]; simp)
  obtain ⟨C, hC, hCH, hxC⟩ := h x hx hx1'
  exact ⟨conjSub C g, hR C hC g, Subgroup.map_mono hCH, ⟨x, hxC, rfl⟩⟩

theorem rcg_mem_long [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {t p : ℕ} (hp : p < 24)
    (hproj : proj (d4Root p) = rt t) (hrho : rho (d4Root p) = d4Root p) (x : twistedGroup σ) :
    x ∈ twistedRootGroup σ (rt t) ↔ ∃ c, σ c = c ∧ (x : adjointGroup d4 K) = xd p c :=
  (Subgroup.mem_subgroupOf).trans
    (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d4 hp) hproj hrho _)

theorem rcg_coveredBy_sup [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {t t' p r : ℕ} (ht : t < 12)
    (ht' : t' < 12) (hp : p < 24) (hr : r < 24) (hproj : proj (d4Root p) = rt t)
    (hrho : rho (d4Root p) = d4Root p) (hproj' : proj (d4Root r) = rt t')
    (hrho' : rho (d4Root r) = d4Root r)
    (hrel : ∀ x y : K, xd r y * xd 22 x = xd p (x * y) * (xd 22 x * xd r y))
    (hcomm : ∀ x y : K, Commute (xd 22 x) (xd p y))
    (hmem : twistedRootGroup σ (rt t) ∈ longClass σ) :
    CoveredBy (longClass σ) (Xh σ ⊔ twistedRootGroup σ (rt t)) := by
  intro z hz hz1
  have hc : ∀ a ∈ Xh σ, ∀ b ∈ twistedRootGroup σ (rt t), Commute a b := by
    intro a ha b hb
    obtain ⟨c, -, hac⟩ := (mem_Xh_iff hσ a).1 ha
    obtain ⟨c', -, hbc⟩ := (rcg_mem_long hσ hp hproj hrho b).1 hb
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hac, hbc]
      exact (hcomm c c').eq)
  obtain ⟨a, ha, b, hb, rfl⟩ := rcg_exists_mul_of_mem_sup hc hz
  obtain ⟨c, hcσ, hac⟩ := (mem_Xh_iff hσ a).1 ha
  obtain ⟨c', hc'σ, hbc⟩ := (rcg_mem_long hσ hp hproj hrho b).1 hb
  by_cases hc0 : c = 0
  · have ha1 : a = 1 := Subtype.ext (by rw [hac, hc0]; exact xd_zero 22)
    subst ha1
    exact ⟨_, hmem, le_sup_right, by simpa using hb⟩
  by_cases hc'0 : c' = 0
  · have hb1 : b = 1 := Subtype.ext (by rw [hbc, hc'0]; exact xd_zero p)
    subst hb1
    exact ⟨Xh σ, rcg_Xh_mem, le_sup_left, by simpa using ha⟩
  set s : K := c' / c with hsdef
  have hs : σ s = s := by rw [hsdef, map_div₀, hc'σ, hcσ]
  have hsmem : xd r s ∈ twistedRootSubgroupD4 σ (rt t') :=
    (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d4 hr) hproj' hrho' _).2 ⟨s, hs, rfl⟩
  set y : twistedGroup σ := ⟨xd r s, twistedRootSubgroupD4_le_twistedGroup σ (isRoot_rt ht')
    hsmem⟩ with hy
  have hy2 : y * y = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact xd_mul_self r s)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hconj : ∀ (x : twistedGroup σ) (d : K), σ d = d → (x : adjointGroup d4 K) = xH d →
      ∃ w ∈ twistedRootGroup σ (rt t), (w : adjointGroup d4 K) = xd p (d * s) ∧
        y * x * y⁻¹ = x * w := by
    intro x d hdσ hxd
    have hwσ : σ (d * s) = d * s := by rw [map_mul, hdσ, hs]
    have hwmem : xd p (d * s) ∈ twistedRootSubgroupD4 σ (rt t) :=
      (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d4 hp) hproj hrho _).2
        ⟨d * s, hwσ, rfl⟩
    refine ⟨⟨xd p (d * s), twistedRootSubgroupD4_le_twistedGroup σ (isRoot_rt ht) hwmem⟩,
      Subgroup.mem_subgroupOf.2 hwmem, rfl, ?_⟩
    apply Subtype.ext
    show xd r s * (x : adjointGroup d4 K) * (xd r s)⁻¹ = (x : adjointGroup d4 K) * xd p (d * s)
    have hrel' := hrel d s
    rw [xd_inv, hxd]
    show xd r s * xd 22 d * xd r s = xd 22 d * xd p (d * s)
    rw [hrel']
    calc xd p (d * s) * (xd 22 d * xd r s) * xd r s
        = xd p (d * s) * xd 22 d * (xd r s * xd r s) := by group
      _ = xd p (d * s) * xd 22 d := by rw [xd_mul_self, mul_one]
      _ = xd 22 d * xd p (d * s) := (hcomm d (d * s)).eq.symm
  refine ⟨conjSub (Xh σ) y, rcg_conjSub_mem rcg_Xh_mem y, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨d, hdσ, hxd⟩ := (mem_Xh_iff hσ x).1 hx
    obtain ⟨w, hw, -, hxw⟩ := hconj x d hdσ hxd
    have : (MulAut.conj y).toMonoidHom x = x * w := by
      rw [show (MulAut.conj y).toMonoidHom x = y * x * y⁻¹ from rfl, hxw]
    rw [this]
    exact Subgroup.mul_mem_sup hx hw
  · obtain ⟨w, hw, hwv, hxw⟩ := hconj a c hcσ hac
    have hwb : w = b := by
      apply Subtype.ext
      rw [hwv, hbc, hsdef]
      congr 1
      field_simp
    rw [← hwb, ← hxw]
    exact ⟨a, ha, rfl⟩

theorem rcg_refl_facts2 :
    CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) (ng 0) (rt 7) = rt 3 ∧
    CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) (ng 0) (rt 6) = rt 10 := by
  decide +kernel

theorem rcg_long_mem [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {t : ℕ} (ht : t ∈ longPos) :
    twistedRootGroup σ (rt t) ∈ longClass σ := by
  obtain ⟨-, r13, -, r02, r12, -⟩ := rcg_refl_facts
  obtain ⟨r73, r60⟩ := rcg_refl_facts2
  have h3 : twistedRootGroup σ (rt 3) ∈ longClass σ := by
    have := rcg_conjSub_mem (rcg_Xh_mem (σ := σ)) (nHat σ (ng 0))
    rwa [rcg_conj_nHat hσ (ng 0) (by norm_num) r73] at this
  have h0 : twistedRootGroup σ (rt 0) ∈ longClass σ := by
    have := rcg_conjSub_mem h3 (nHat σ (ng 1))
    rwa [rcg_conj_nHat hσ (ng 1) (by norm_num) r13] at this
  have h2 : twistedRootGroup σ (rt 2) ∈ longClass σ := by
    have := rcg_conjSub_mem h0 (nHat σ (ng 0))
    rwa [rcg_conj_nHat hσ (ng 0) (by norm_num) r02] at this
  have h6 : twistedRootGroup σ (rt 6) ∈ longClass σ := by
    have := rcg_conjSub_mem h2 (nHat σ (ng 1))
    rwa [rcg_conj_nHat hσ (ng 1) (by norm_num) r12] at this
  have h10 : twistedRootGroup σ (rt 10) ∈ longClass σ := by
    have := rcg_conjSub_mem h6 (nHat σ (ng 0))
    rwa [rcg_conj_nHat hσ (ng 0) (by norm_num) r60] at this
  simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h2
  · exact h3
  · exact h6
  · exact rcg_Xh_mem
  · exact h10

theorem rcg_dict_21_8 : proj (d4Root 21) = rt 6 ∧ rho (d4Root 21) = d4Root 21 ∧
    proj (d4Root 8) = rt 2 ∧ rho (d4Root 8) = d4Root 8 := by
  decide +kernel

theorem rcg_coveredBy_0 [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    CoveredBy (longClass σ) (Xh σ ⊔ twistedRootGroup σ (rt 0)) :=
  rcg_coveredBy_sup hσ (t := 0) (t' := 6) (p := 2) (r := 21) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) proj_dict.1 rho_dict.1 rcg_dict_21_8.1 rcg_dict_21_8.2.1
    (fun x y => swap_gen (Or.inr rfl) (by decide +kernel) x y) (fun x y => commute_22_2 x y)
    (rcg_long_mem hσ (by simp [longPos]))

theorem rcg_coveredBy_3 [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    CoveredBy (longClass σ) (Xh σ ⊔ twistedRootGroup σ (rt 3)) :=
  rcg_coveredBy_sup hσ (t := 3) (t' := 2) (p := 19) (r := 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) proj_dict.2.2.2.2.1 rho_dict.2.1 rcg_dict_21_8.2.2.1
    rcg_dict_21_8.2.2.2
    (fun x y => swap_gen (Or.inl rfl) (by decide +kernel) x y) (fun x y => commute_22_19 x y)
    (rcg_long_mem hσ (by simp [longPos]))

theorem rcg_isRootClass [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) [IsSimpleGroup (twistedGroup σ)] :
    IsRootClass (longClass σ) where
  conj_class := ⟨Xh σ, rfl⟩
  ne_bot := fun A hA => rcg_ne_bot hσ hA
  mul_self := fun A hA => rcg_mul_self hσ hA
  rel := fun A hA B hB hne => rcg_long_pair_dichotomy hσ hA hB hne
  gen := by
    have hbot : Subgroup.normalClosure (Xh σ : Set (twistedGroup σ)) ≠ ⊥ := fun h =>
      rcg_ne_bot hσ (rcg_Xh_mem (σ := σ)) (eq_bot_iff.2 ((Subgroup.le_normalClosure).trans h.le))
    have htop : Subgroup.normalClosure (Xh σ : Set (twistedGroup σ)) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure (Xh σ : Set (twistedGroup σ))) with h | h
      · exact absurd h hbot
      · exact h
    rw [eq_top_iff, ← htop, Subgroup.normalClosure, Subgroup.closure_le]
    intro z hz
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    exact Subgroup.mem_iSup_of_mem (conjSub (Xh σ) c) (Subgroup.mem_iSup_of_mem
      (rcg_conjSub_mem rcg_Xh_mem c) ⟨a, ha, rfl⟩)

theorem rcg_isNondegenerate [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    IsNondegenerate (longClass σ) :=
  ⟨Xh σ, rcg_Xh_mem, _, rcg_long_mem hσ (t := 2) (by simp [longPos]), rcg_special_2 hσ⟩

theorem rcg_center_eq_bot [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c)
    [IsSimpleGroup (twistedGroup σ)] : Subgroup.center (twistedGroup σ) = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (twistedGroup σ)) with h | h
  · exact h
  · exfalso
    have hc := rcg_commutator_Xp0_Xp3 hσ
    have hle : ⁅twistedRootGroup σ (rt 0), twistedRootGroup σ (rt 3)⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      have : b ∈ Subgroup.center (twistedGroup σ) := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 this a))
    rw [hc] at hle
    exact rcg_ne_bot hσ (rcg_Xh_mem (σ := σ)) (eq_bot_iff.2 hle)

theorem rcg_hyp [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) [Finite (twistedGroup σ)]
    [IsSimpleGroup (twistedGroup σ)] : Hyp (twistedGroup σ) (longClass σ) where
  finite := inferInstance
  root := rcg_isRootClass hσ
  nondeg := rcg_isNondegenerate hσ
  center := rcg_center_eq_bot hσ
  twoCore := by
    intro N hN hNp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      subst h
      have hG : IsPGroup 2 (twistedGroup σ) := hNp.of_surjective
        (Subgroup.topEquiv (G := twistedGroup σ)).toMonoidHom
        (Subgroup.topEquiv (G := twistedGroup σ)).surjective
      have : Nontrivial (twistedGroup σ) := IsSimpleGroup.toNontrivial
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnt := hG.center_nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt (rcg_center_eq_bot hσ)

theorem rcg_not_commuting_of_opposite {G : Type*} [Group G] {A B : Subgroup G}
    (h : Opposite A B) (hA : A ≠ ⊥) : ¬ Commuting A B := by
  intro hc
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
  obtain ⟨b, hb, hb1, hab⟩ := h.2.1 a ha (fun e => ha1 (Subtype.ext e))
  have h1 : conjSub A b = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : b * y * b⁻¹ = y := (hc y hy b hb).symm.mul_inv_cancel
      show (MulAut.conj b).toMonoidHom y ∈ A
      rw [show (MulAut.conj b).toMonoidHom y = b * y * b⁻¹ from rfl, this]
      exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      exact (hc x hx b hb).symm.mul_inv_cancel
  have h2 : conjSub B a = B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : a * y * a⁻¹ = y := (hc a ha y hy).mul_inv_cancel
      show (MulAut.conj a).toMonoidHom y ∈ B
      rw [show (MulAut.conj a).toMonoidHom y = a * y * a⁻¹ from rfl, this]
      exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      exact (hc a ha x hx).mul_inv_cancel
  rw [h1, h2] at hab
  exact h.1 hab

theorem rcg_sigmaEqLambda [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) [Finite (twistedGroup σ)]
    [IsSimpleGroup (twistedGroup σ)] : SigmaEqLambda (longClass σ) := by
  have hR : IsRootClass (longClass σ) := rcg_isRootClass hσ
  have hRc : ∀ A ∈ longClass σ, ∀ g, conjSub A g ∈ longClass σ :=
    fun A hA g => rcg_conjSub_mem hA g
  refine sigmaEqLambda_of_mem hR (rcg_Xh_mem (σ := σ)) ?_
  ext B
  constructor
  · rintro ⟨hB, hBne, hcomm⟩
    refine ⟨⟨hB, hBne, hcomm⟩, ?_⟩
    obtain ⟨g, t, ht, hgA, hgB⟩ := rcg_exists_standard_pair hσ (rcg_Xh_mem (σ := σ)) hB
    have hcomm' : Commuting (Xh σ) (twistedRootGroup σ (rt t)) := by
      have := rcg_commuting_conj hcomm g
      rwa [hgA, hgB] at this
    have hXh : Xh σ ≠ ⊥ := rcg_ne_bot hσ (rcg_Xh_mem (σ := σ))
    have hcov : CoveredBy (longClass σ) (Xh σ ⊔ twistedRootGroup σ (rt t)) := by
      simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · exact rcg_coveredBy_0 hσ
      · exact absurd (commuting_iff_commutator_eq_bot.1 hcomm')
          (rcg_ne_bot hσ (rcg_special_2 hσ).1)
      · exact rcg_coveredBy_3 hσ
      · exact absurd (commuting_iff_commutator_eq_bot.1 hcomm')
          (rcg_ne_bot hσ (rcg_special_6 hσ).1)
      · exact absurd (conjSub_inj g (hgB.trans hgA.symm)) hBne
      · exact absurd hcomm' (rcg_not_commuting_of_opposite (rcg_opposite_10 hσ) hXh)
    have hback := rcg_coveredBy_conj hRc hcov g⁻¹
    have e1 : conjSub (Xh σ) g⁻¹ = Xh σ := by
      have := conjSub_conjSub_inv' (Xh σ) g
      rwa [hgA] at this
    have e2 : conjSub (twistedRootGroup σ (rt t)) g⁻¹ = B := by
      rw [← hgB]
      exact conjSub_conjSub_inv' B g
    rwa [show conjSub (Xh σ ⊔ twistedRootGroup σ (rt t)) g⁻¹ = Xh σ ⊔ B by
      rw [conjSub, Subgroup.map_sup]
      exact congrArg₂ (· ⊔ ·) e1 e2] at hback
  · rintro ⟨h1, -⟩
    exact h1

end CFSG.RankThree.PartOne.D4RC
