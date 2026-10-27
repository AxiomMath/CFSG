module

public import CFSG.RankThree.GF2n.Tim78S48PairBasic
public import CFSG.RankThree.GF2n.QuotPair
import CFSG.RankThree.GF2n.Tim78S31Split
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.RankThree.GF2n.Tim78S47

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem center_eq_bot_of_simple {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z) [IsSimpleGroup Z]
    (hnc : ¬ ∀ a b : Y, a * b = b * a) : Subgroup.center Y = ⊥ := by
  haveI : IsSimpleGroup Y := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    apply hnc
    intro a b
    have : a ∈ Subgroup.center Y := by rw [h]; trivial
    exact ((Subgroup.mem_center_iff.mp this) b).symm

theorem center_eq_bot_of_equiv {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : Subgroup.center Z = ⊥) : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : e z ∈ Subgroup.center Z := by
    rw [Subgroup.mem_center_iff]
    intro w
    have := Subgroup.mem_center_iff.mp hz (e.symm w)
    have h2 := congrArg e this
    simpa using h2
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact e.injective (by simpa using this)

section QuotPairCenter

variable {X : Type} [Group X] [Finite X] {T T₁ : Subgroup X}

theorem quotPair_center_eq_bot (P : QuotPair T T₁) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) : Subgroup.center X = ⊥ := by
  obtain ⟨-, hmod⟩ := P.models hCen hU
  have hnc : ¬ ∀ a b : X, a * b = b * a := by
    intro h
    obtain ⟨x, hx⟩ := P.exists_conj_eq
    have : conjSubgroup x T = T := conjSubgroup_eq_self_iff.mpr (by
      refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
      rw [show x * y * x⁻¹ = y by rw [h x y, mul_inv_cancel_right]])
    exact P.ne (by rw [hx, this])
  rcases hmod with ⟨f, hf, -, ⟨e⟩⟩ | ⟨a, ha, -, ⟨e⟩⟩ | ⟨m, hm, h3, -, ⟨e⟩⟩
  · haveI : IsSimpleGroup PSL(2, GaloisField 2 f) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
        rw [GaloisField.card 2 f (by omega)]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
    exact center_eq_bot_of_simple e hnc
  · haveI : IsSimpleGroup (Sz a) :=
      SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup ha
    exact center_eq_bot_of_simple e hnc
  · exact center_eq_bot_of_equiv e (DihedralGroup.center_eq_bot_of_odd_ne_one hm (by omega))

end QuotPairCenter

theorem relIndex_eq_card_map_mk [Finite G] {X N S : Subgroup G} [(N.subgroupOf X).Normal]
    (hSX : S ≤ X) :
    (S ⊓ N).relIndex S =
      Nat.card ((S.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) := by
  have h1 := Subgroup.relIndex_mul_card (H := S ⊓ N) (K := S)
  rw [inf_of_le_left inf_le_left] at h1
  have h2 := card_map_mk_mul (N := N) hSX
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Certified


theorem Bg_inf_T (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hP : ¬ conjSubgroup g B ≤ P) : conjSubgroup g B ⊓ T = ⊥ :=
  H.inf_conj_B_T_eq_bot hCen hU (H.Bg_ne hP)

theorem B_inf_Tg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hP : ¬ conjSubgroup g B ≤ P) : B ⊓ conjSubgroup g T = ⊥ :=
  H.inf_B_conj_T_eq_bot hCen hU (H.Bg_ne hP)

theorem T_not_cent (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hP : ¬ conjSubgroup g B ≤ P) : ¬ ∀ t ∈ T, ∀ b ∈ conjSubgroup g B, t * b = b * t := by
  intro h
  apply hP
  refine H.tim78_4_7 hCen hU g ?_
  have hBg : conjSubgroup g B ≤ Subgroup.centralizer (T : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun t ht => h t ht b hb
  rw [inf_of_le_left hBg]
  intro hbot
  apply H.B_ne_bot
  apply Subgroup.eq_bot_of_card_eq
  have := card_conjSubgroup g B
  rw [hbot, Subgroup.card_bot] at this
  exact this.symm

theorem Tg_not_cent (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hP : ¬ conjSubgroup g B ≤ P) : ¬ ∀ t ∈ conjSubgroup g T, ∀ b ∈ B, t * b = b * t := by
  intro h
  apply hP
  have h1 : conjSubgroup g⁻¹ B ≤ P := by
    refine H.tim78_4_7 hCen hU g⁻¹ ?_
    have hBg : conjSubgroup g⁻¹ B ≤ Subgroup.centralizer (T : Set G) := by
      intro y hy
      refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
      rw [mem_conjSubgroup, inv_inv] at hy
      have ht' : g * t * g⁻¹ ∈ conjSubgroup g T := by
        rw [mem_conjSubgroup, show g⁻¹ * (g * t * g⁻¹) * g = t by group]
        exact ht
      have := h _ ht' _ hy
      calc t * y = g⁻¹ * ((g * t * g⁻¹) * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * (g * t * g⁻¹)) * g := by rw [this]
        _ = y * t := by group
    rw [inf_of_le_left hBg]
    intro hbot
    apply H.B_ne_bot
    apply Subgroup.eq_bot_of_card_eq
    have := card_conjSubgroup g⁻¹ B
    rw [hbot, Subgroup.card_bot] at this
    exact this.symm
  have := H.conj_inv_le_P_of_conj_le_P h1
  rwa [inv_inv] at this

theorem quotPair48 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    [((kernelGen48 B T g).subgroupOf (T ⊔ conjSubgroup g T)).Normal] :
    QuotPair
      ((T.subgroupOf (T ⊔ conjSubgroup g T)).map
        (QuotientGroup.mk' ((kernelGen48 B T g).subgroupOf (T ⊔ conjSubgroup g T))))
      (((conjSubgroup g T).subgroupOf (T ⊔ conjSubgroup g T)).map
        (QuotientGroup.mk' ((kernelGen48 B T g).subgroupOf (T ⊔ conjSubgroup g T)))) := by
  classical
  set X := T ⊔ conjSubgroup g T with hX
  set N := kernelGen48 B T g with hN
  set π := QuotientGroup.mk' (N.subgroupOf X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hmk : ∀ y : ↥X, π y = 1 ↔ (y : G) ∈ N := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hNK : N ≤ kernel48 B T g := H.kernelGen_le_kernel
  have hconj : ∀ (u : ↥X) (A : Subgroup G), conjSubgroup (π u) ((A.subgroupOf X).map π) =
      ((conjSubgroup (u : G) A).subgroupOf X).map π := by
    intro u A
    rw [← map_conjSubgroup]
    congr 1
    ext x
    rw [mem_conjSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjSubgroup]
    rfl
  have hcomm_mod : ∀ v w : ↥X, π v * π w = π w * π v → ⁅(v : G), (w : G)⁆ ∈ N := by
    intro v w h
    have h1 : π ⁅v, w⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h
    have := (hmk _).mp h1
    simpa [commutatorElement_def] using this
  have helem : ∀ {D S : Subgroup G}, IsSide48 B T g D S →
      Assembly.IsElemAbelian 2 ((S.subgroupOf X).map π) := by
    intro D S hs
    obtain ⟨hc, hsq⟩ := H.side_comm hs
    have hDN := H.side_le_kernelGen h48 hs
    obtain ⟨-, hSX⟩ := H.side_le hs
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul]
      refine (QuotientGroup.eq.mpr ?_)
      rw [Subgroup.mem_subgroupOf]
      have := hc _ (S.inv_mem (Subgroup.mem_subgroupOf.mp hb')) _
        (S.inv_mem (Subgroup.mem_subgroupOf.mp ha'))
      refine hDN ?_
      simpa [commutatorElement_def, mul_assoc] using this
    · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hmk]
      exact hDN (by simpa [sq] using hsq _ (Subgroup.mem_subgroupOf.mp hx'))
  have hne : ∀ {D S : Subgroup G}, IsSide48 B T g D S → (∃ s ∈ S, s ∉ kernel48 B T g) →
      (S.subgroupOf X).map π ≠ ⊥ := by
    intro D S hs ⟨s, hsS, hsK⟩ h
    obtain ⟨-, hSX⟩ := H.side_le hs
    have : π ⟨s, hSX hsS⟩ ∈ (S.subgroupOf X).map π := ⟨⟨s, hSX hsS⟩, hsS, rfl⟩
    rw [h, Subgroup.mem_bot, hmk] at this
    exact hsK (hNK this)
  have hsideT : IsSide48 B T g B T := Or.inl ⟨rfl, rfl⟩
  have hsideTg : IsSide48 B T g (conjSubgroup g B) (conjSubgroup g T) := Or.inr ⟨rfl, rfl⟩
  have hTK : ∃ s ∈ T, s ∉ kernel48 B T g := by
    by_contra hcon
    push Not at hcon
    exact H.T_not_cent hCen hU hP fun t ht b hb =>
      (H.T_mem_kernel_iff h48 ht (Subgroup.mem_sup_left ht)).mp (hcon t ht) b hb
  have hTgK : ∃ s ∈ conjSubgroup g T, s ∉ kernel48 B T g := by
    by_contra hcon
    push Not at hcon
    exact H.Tg_not_cent hCen hU hP fun t ht b hb =>
      (H.Tg_mem_kernel_iff h48 ht (Subgroup.mem_sup_right ht)).mp (hcon t ht) b hb
  have hmem : ∀ {D S : Subgroup G}, IsSide48 B T g D S → ∀ (u : ↥X) (x : ↥X ⧸ N.subgroupOf X),
      x ∈ conjSubgroup (π u) ((S.subgroupOf X).map π) → x ≠ 1 →
      ∃ y : ↥X, (y : G) ∈ conjSubgroup (u : G) S ∧ (y : G) ∉ N ∧ π y = x := by
    intro D S hs u x hx hx1
    rw [hconj] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, fun h => hx1 ((hmk y).mpr h), rfl⟩
  have hkey : ∀ {D S D' S' : Subgroup G}, IsSide48 B T g D S → IsSide48 B T g D' S' →
      ∀ u h : ↥X, ∀ x ∈ conjSubgroup (π u) ((S.subgroupOf X).map π), x ≠ 1 →
      ∀ y ∈ conjSubgroup (π h) ((S'.subgroupOf X).map π), y ≠ 1 → x * y = y * x →
      conjSubgroup (π u) ((S.subgroupOf X).map π) =
        conjSubgroup (π h) ((S'.subgroupOf X).map π) := by
    intro D S D' S' hs hs' u h x hx hx1 y hy hy1 hxy
    obtain ⟨v, hv, hvN, rfl⟩ := hmem hs u x hx hx1
    obtain ⟨w, hw, hwN, rfl⟩ := hmem hs' h y hy hy1
    have hvK : (v : G) ∉ kernel48 B T g := fun hK =>
      hvN (H.conj_side_inf_kernel_le h48 hs u.2 hv hK)
    have hwK : (w : G) ∉ kernel48 B T g := fun hK =>
      hwN (H.conj_side_inf_kernel_le h48 hs' h.2 hw hK)
    have he := (H.closure48 h48 hP hs hs' u.2 h.2 hv hw hvK hwK
      (hNK (hcomm_mod v w hxy))).2
    rw [hconj, hconj, he]
  refine ⟨helem hsideT, helem hsideTg, hne hsideT hTK, hne hsideTg hTgK, ?_, ?_, ?_⟩
  · intro hTT
    obtain ⟨t, htT, htK⟩ := hTK
    have htX : t ∈ X := Subgroup.mem_sup_left htT
    have hmem1 : π ⟨t, htX⟩ ∈ (((conjSubgroup g T).subgroupOf X).map π) := by
      rw [← hTT]
      exact ⟨⟨t, htX⟩, htT, rfl⟩
    obtain ⟨s, hs, hst⟩ := hmem1
    have hsTg : (s : G) ∈ conjSubgroup g T := Subgroup.mem_subgroupOf.mp hs
    have hsK : (s : G) ∉ kernel48 B T g := fun hK => htK (by
      have h1 := QuotientGroup.eq.mp hst
      rw [Subgroup.mem_subgroupOf] at h1
      have := (kernel48 B T g).mul_mem hK (hNK h1)
      simpa using this)
    have hκ : ⁅t, (s : G)⁆ ∈ kernel48 B T g :=
      hNK (hcomm_mod ⟨t, htX⟩ s (by rw [hst]))
    have he := (H.closure48 h48 hP hsideT hsideTg (x := 1) (y := 1) (one_mem _)
      (one_mem _) (by rw [conjSubgroup_one]; exact htT) (by rw [conjSubgroup_one]; exact hsTg)
      htK hsK hκ).2
    rw [conjSubgroup_one, conjSubgroup_one] at he
    apply H.B_ne_bot
    have h1 : B ⊓ conjSubgroup g T = B := inf_of_le_left (he ▸ H.B_le_T)
    rw [← h1]
    exact H.B_inf_Tg hCen hU hP
  · rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ hπs]
  · rintro U ⟨ub, rfl | rfl⟩ V ⟨vb, rfl | rfl⟩ x hx hx1 y hy hy1 hxy <;>
      obtain ⟨u, rfl⟩ := hπs ub <;> obtain ⟨h, rfl⟩ := hπs vb
    · exact hkey hsideT hsideT u h x hx hx1 y hy hy1 hxy
    · exact hkey hsideT hsideTg u h x hx hx1 y hy hy1 hxy
    · exact hkey hsideTg hsideT u h x hx hx1 y hy hy1 hxy
    · exact hkey hsideTg hsideTg u h x hx hx1 y hy hy1 hxy

theorem kernel48_eq_kernelGen (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    kernel48 B T g = kernelGen48 B T g := by
  haveI := H.normal_kernelGen h48
  have hQP := H.quotPair48 hCen hU h48 hP
  have hZ := quotPair_center_eq_bot hQP hCen hU
  refine le_antisymm (fun k hk => ?_) H.kernelGen_le_kernel
  set X := T ⊔ conjSubgroup g T with hX
  set N := kernelGen48 B T g with hN
  set π := QuotientGroup.mk' (N.subgroupOf X) with hπ
  have hmk : ∀ y : ↥X, π y = 1 ↔ (y : G) ∈ N := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set ks : ↥X := ⟨k, hk.1⟩ with hks
  have hc : ∀ {D S : Subgroup G}, IsSide48 B T g D S → ∀ t' : ↥X, (t' : G) ∈ S →
      π ks * π t' = π t' * π ks := by
    intro D S hs t' ht'
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have h1 := H.comm_side_kernel_mem h48 hs (S.inv_mem ht') ((kernel48 B T g).inv_mem hk)
    have h2 := H.side_inf_kernel_le hs h1
    simpa [commutatorElement_def, mul_assoc, hks] using h2
  have hsideT : IsSide48 B T g B T := Or.inl ⟨rfl, rfl⟩
  have hsideTg : IsSide48 B T g (conjSubgroup g B) (conjSubgroup g T) := Or.inr ⟨rfl, rfl⟩
  have hle : (⊤ : Subgroup (↥X ⧸ N.subgroupOf X)) ≤ Subgroup.centralizer ({π ks} : Set _) := by
    rw [← hQP.sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨t', ht', rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hc hsideT t' (Subgroup.mem_subgroupOf.mp ht')).symm
    · rintro _ ⟨t', ht', rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hc hsideTg t' (Subgroup.mem_subgroupOf.mp ht')).symm
  have hcent : π ks ∈ Subgroup.center (↥X ⧸ N.subgroupOf X) :=
    Subgroup.mem_center_iff.mpr fun y =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top y))
  rw [hZ, Subgroup.mem_bot, hmk] at hcent
  exact hcent

theorem exists_conj_Tg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    ∃ x ∈ T ⊔ conjSubgroup g T, conjSubgroup g T = conjSubgroup x T ∧
      conjSubgroup g B = conjSubgroup x B := by
  haveI := H.normal_kernelGen h48
  set X := T ⊔ conjSubgroup g T with hX
  set N := kernelGen48 B T g with hN
  set π := QuotientGroup.mk' (N.subgroupOf X) with hπ
  have hQP := H.quotPair48 hCen hU h48 hP
  obtain ⟨xb, hxb⟩ := hQP.exists_conj_eq
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hmk : ∀ y : ↥X, π y = 1 ↔ (y : G) ∈ N := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hNK : N ≤ kernel48 B T g := H.kernelGen_le_kernel
  have hconj : ∀ (u : ↥X) (A : Subgroup G), conjSubgroup (π u) ((A.subgroupOf X).map π) =
      ((conjSubgroup (u : G) A).subgroupOf X).map π := by
    intro u A
    rw [← map_conjSubgroup]
    congr 1
    ext x
    rw [mem_conjSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjSubgroup]
    rfl
  have hcomm_mod : ∀ v w : ↥X, π v * π w = π w * π v → ⁅(v : G), (w : G)⁆ ∈ N := by
    intro v w h
    have h1 : π ⁅v, w⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h
    have := (hmk _).mp h1
    simpa [commutatorElement_def] using this
  obtain ⟨u, rfl⟩ := hπs xb
  rw [hconj] at hxb
  have hsideT : IsSide48 B T g B T := Or.inl ⟨rfl, rfl⟩
  have hsideTg : IsSide48 B T g (conjSubgroup g B) (conjSubgroup g T) := Or.inr ⟨rfl, rfl⟩
  have hTgK : ∃ s ∈ conjSubgroup g T, s ∉ kernel48 B T g := by
    by_contra hcon
    push Not at hcon
    exact H.Tg_not_cent hCen hU hP fun t ht b hb =>
      (H.Tg_mem_kernel_iff h48 ht (Subgroup.mem_sup_right ht)).mp (hcon t ht) b hb
  obtain ⟨s, hsTg, hsK⟩ := hTgK
  have hsX : s ∈ X := Subgroup.mem_sup_right hsTg
  have hmem1 : π ⟨s, hsX⟩ ∈ (((conjSubgroup (u : G) T).subgroupOf X).map π) := by
    rw [← hxb]
    exact ⟨⟨s, hsX⟩, hsTg, rfl⟩
  obtain ⟨w, hw, hws⟩ := hmem1
  have hwT : (w : G) ∈ conjSubgroup (u : G) T := Subgroup.mem_subgroupOf.mp hw
  have hwK : (w : G) ∉ kernel48 B T g := fun hK => hsK (hNK (by
    have h1 := H.conj_side_inf_kernel_le h48 hsideT u.2 hwT hK
    have : π ⟨s, hsX⟩ = 1 := by rw [← hws]; exact (hmk w).mpr h1
    exact (hmk _).mp this))
  have hκ : ⁅(w : G), s⁆ ∈ kernel48 B T g := hNK (hcomm_mod w ⟨s, hsX⟩ (by rw [hws]))
  obtain ⟨hDe, hSe⟩ := H.closure48 h48 hP hsideT hsideTg (x := (u : G)) (y := 1) u.2
    (one_mem _) hwT (by rw [conjSubgroup_one]; exact hsTg) hwK hsK hκ
  rw [conjSubgroup_one] at hDe hSe
  exact ⟨u, u.2, hSe.symm, hDe.symm⟩

end Certified

end Hyp4

end CFSG.RankThree.GF2n.Tim78
