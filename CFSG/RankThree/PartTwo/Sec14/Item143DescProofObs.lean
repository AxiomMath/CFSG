module

public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofCompOne
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Desc143X

private def v41 : alternatingGroup (Fin 4) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

private def v42 : alternatingGroup (Fin 4) := ⟨Equiv.swap 0 2 * Equiv.swap 1 3,
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

private def c41 : alternatingGroup (Fin 4) := ⟨Equiv.swap 1 2 * Equiv.swap 2 3,
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

private def c42 : alternatingGroup (Fin 4) := ⟨Equiv.swap 0 2 * Equiv.swap 1 2,
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

private def c43 : alternatingGroup (Fin 4) := ⟨Equiv.swap 0 3 * Equiv.swap 1 3,
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

private theorem v4_mem : v41 ∈ alternatingGroup.kleinFour (Fin 4) ∧
    v42 ∈ alternatingGroup.kleinFour (Fin 4) := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  rw [alternatingGroup.kleinFour_eq_commutator h4, commutator_def]
  have e1 : ⁅c41, c42⁆ = v41 := Subtype.ext (by decide)
  have e2 : ⁅c41, c43⁆ = v42 := Subtype.ext (by decide)
  rw [← e1, ← e2]
  exact ⟨Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _),
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩

private theorem perm4_eq_one : ∀ s : Equiv.Perm (Fin 4), s ^ 3 = 1 →
    s * (Equiv.swap 0 1 * Equiv.swap 2 3) = (Equiv.swap 0 1 * Equiv.swap 2 3) * s →
    s * (Equiv.swap 0 2 * Equiv.swap 1 3) = (Equiv.swap 0 2 * Equiv.swap 1 3) * s → s = 1 := by
  decide

theorem a4_exists_not_comm {t : alternatingGroup (Fin 4)} (ht : t ≠ 1) (ht3 : t ^ 3 = 1) :
    ∃ v ∈ alternatingGroup.kleinFour (Fin 4), t * v ≠ v * t := by
  by_contra hno
  push Not at hno
  apply ht
  apply Subtype.ext
  refine perm4_eq_one (t : Equiv.Perm (Fin 4)) ?_ ?_ ?_
  · exact congrArg Subtype.val ht3
  · exact congrArg Subtype.val (hno v41 v4_mem.1)
  · exact congrArg Subtype.val (hno v42 v4_mem.2)

theorem exists_not_comm_pCore {H : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))}
    (hH : Nat.card H = 9) (hH3 : ∀ h ∈ H, h ^ 3 = 1) :
    ∃ h ∈ H, ∃ w ∈ CFSG.pCore 2 (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)),
      h * w ≠ w * h := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  set V := (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup.kleinFour (Fin 4))
    with hV
  have : (alternatingGroup.kleinFour (Fin 4)).Normal := alternatingGroup.normal_kleinFour h4
  have hVn : V.Normal := Subgroup.prod_normal _ _
  have hVcard : Nat.card V = 2 ^ 2 := by
    rw [hV, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
      (alternatingGroup.kleinFour_isKleinFour h4).card_four]
    norm_num
  have hVle : V ≤ CFSG.pCore 2 (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hVn (IsPGroup.of_card hVcard)
  have hex : ∃ h ∈ H, h.2 ≠ 1 := by
    by_contra hall
    push Not at hall
    have hle : H ≤ (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ :=
      fun h hh => ⟨Subgroup.mem_top _, hall h hh⟩
    have h1 := Subgroup.card_dvd_of_le hle
    rw [hH, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top,
      Subgroup.card_bot, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
    revert h1
    decide
  obtain ⟨h, hh, hh2⟩ := hex
  have ht3 : h.2 ^ 3 = 1 := by
    have := congrArg Prod.snd (hH3 h hh)
    simpa using this
  obtain ⟨v, hv, hvne⟩ := a4_exists_not_comm hh2 ht3
  refine ⟨h, hh, (1, v), hVle ⟨Subgroup.mem_bot.mpr rfl, hv⟩, fun heq => hvne ?_⟩
  have := congrArg Prod.snd heq
  simpa using this

section J2

variable {Q : Type} [Group Q]

theorem pCore_two_le_centralizer {e : Q} (he3 : e ^ 3 = 1) :
    (CFSG.pCore 2 ↥(Subgroup.normalizer (Subgroup.zpowers e : Set Q))).map
        (Subgroup.normalizer (Subgroup.zpowers e : Set Q)).subtype ≤
      Subgroup.centralizer ({e} : Set Q) := by
  set N := Subgroup.normalizer (Subgroup.zpowers e : Set Q) with hN
  set O := CFSG.pCore 2 ↥N with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  have heN : e ∈ N := Subgroup.le_normalizer (Subgroup.mem_zpowers e)
  set e' : ↥N := ⟨e, heN⟩ with he'
  rintro _ ⟨w, hw, rfl⟩
  set c := w * e' * w⁻¹ * e'⁻¹ with hc
  have hcO : c ∈ O := by
    have h1 : e' * w⁻¹ * e'⁻¹ ∈ O := hOn.conj_mem _ (O.inv_mem hw) e'
    have h2 := O.mul_mem hw h1
    rwa [show w * (e' * w⁻¹ * e'⁻¹) = c by rw [hc]; group] at h2
  have hcz : (c : Q) ∈ Subgroup.zpowers e := by
    have h1 : (w : Q) * e * (w : Q)⁻¹ ∈ Subgroup.zpowers e :=
      (Subgroup.mem_normalizer_iff.mp w.2 e).mp (Subgroup.mem_zpowers e)
    have h2 : (c : Q) = ((w : Q) * e * (w : Q)⁻¹) * e⁻¹ := by
      simp [hc, he']
    rw [h2]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.mem_zpowers e))
  have hc3 : c ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      he3, one_zpow, OneMemClass.coe_one]
  obtain ⟨k, hk⟩ := hO2 ⟨c, hcO⟩
  have hk' : c ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_of_pow_eq_one hc3))
  have hwe : w * e' = e' * w := by
    have := hc1
    rw [hc, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val hwe

theorem map_pCore_two_le (σ : Q ≃* Q) {e : Q} (hσe : σ e = e) :
    ((CFSG.pCore 2 ↥(Subgroup.normalizer (Subgroup.zpowers e : Set Q))).map
        (Subgroup.normalizer (Subgroup.zpowers e : Set Q)).subtype).map σ.toMonoidHom ≤
      (CFSG.pCore 2 ↥(Subgroup.normalizer (Subgroup.zpowers e : Set Q))).map
        (Subgroup.normalizer (Subgroup.zpowers e : Set Q)).subtype := by
  set N := Subgroup.normalizer (Subgroup.zpowers e : Set Q) with hN
  set O := CFSG.pCore 2 ↥N with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  have hσinv : σ.symm e = e := by rw [MulEquiv.symm_apply_eq, hσe]
  have hmapN : ∀ (τ : Q ≃* Q), τ e = e → ∀ n ∈ N, τ n ∈ N := by
    intro τ hτ n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro y
    have hz : ∀ z : Q, z ∈ Subgroup.zpowers e ↔ τ.symm z ∈ Subgroup.zpowers e := by
      intro z
      have hτ' : τ.symm e = e := by rw [MulEquiv.symm_apply_eq, hτ]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, by simp [map_zpow, hτ']⟩
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have := congrArg τ hk
        simp only [map_zpow, MulEquiv.apply_symm_apply, hτ] at this
        exact this
    rw [hz y, hz (τ n * y * (τ n)⁻¹)]
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact hn _
  have hNmap : N.map σ.toMonoidHom = N := by
    apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      exact hmapN σ hσe n hn
    · intro n hn
      exact ⟨σ.symm n, hmapN σ.symm hσinv n hn, by simp⟩
  set σN : ↥N ≃* ↥N := (σ.subgroupMap N).trans (MulEquiv.subgroupCongr hNmap) with hσN
  have hOσ := CFSG.pCore_map_iso 2 σN
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have h1 : σN w ∈ CFSG.pCore 2 ↥N := hOσ ▸ ⟨w, hw, rfl⟩
  exact ⟨σN w, h1, rfl⟩

end J2

section Certificates


theorem j2_exists_not_comm {Q : Type} [Group Q] [Finite Q]
    (hQ : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup Q}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : Nat.card E = 9) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ f ∈ E, ∃ w ∈ (CFSG.pCore 2 ↥(Subgroup.normalizer
        (Subgroup.zpowers e : Set Q))).map
          (Subgroup.normalizer (Subgroup.zpowers e : Set Q)).subtype,
      f * w ≠ w * f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hEp : IsPGroup 3 E := isPGroup_three_of_pow148 hE3
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨⟨hHeis, -⟩, -, -, h4, -⟩ := h415 Q hQ P _ rfl _ rfl
  have hex : ∃ e ∈ E, e ∉ (P : Subgroup Q) ⊓ Subgroup.centralizer ((P : Subgroup Q) : Set Q) := by
    by_contra hall
    push Not at hall
    have hle : E.subgroupOf P ≤ Subgroup.center ↥(P : Subgroup Q) := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hall _ hx).2 y y.2
    have h1 := Subgroup.card_le_of_le hle
    rw [hHeis.1.2.2.2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hE9] at h1
    omega
  obtain ⟨e, he, heZ⟩ := hex
  have he1 : e ≠ 1 := fun h1 => heZ (h1 ▸ Subgroup.one_mem _)
  obtain ⟨-, ⟨ψ⟩, -⟩ := h4 E ⟨hEP, hE9⟩ e he heZ
  set N := Subgroup.normalizer (Subgroup.zpowers e : Set Q) with hN
  have hEN : E ≤ N := by
    intro x hx
    have hxe : x ∈ Subgroup.centralizer ({e} : Set Q) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx e he)
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure] at hxe
    exact Subgroup.centralizer_le_normalizer _ hxe
  set E' := E.subgroupOf N with hE'
  set H := E'.map ψ.toMonoidHom with hH
  have hH9 : Nat.card H = 9 := by
    rw [hH, Subgroup.card_map_of_injective ψ.injective, hE',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hE9]
  have hH3 : ∀ h ∈ H, h ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hE3 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]
  obtain ⟨_, ⟨x, hx, rfl⟩, w, hw, hne⟩ := exists_not_comm_pCore hH9 hH3
  rw [← CFSG.pCore_map_iso 2 ψ] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  refine ⟨e, he, he1, x, Subgroup.mem_subgroupOf.mp hx, y, ⟨y, hy, rfl⟩, fun heq => hne ?_⟩
  have hxy : x * y = y * x := Subtype.ext heq
  rw [← map_mul, ← map_mul, hxy]

end Certificates

namespace One

variable {G : Type} [Group G] [Finite G]
variable {A L B Lb : Subgroup G} {c a b d : G}

theorem not_j2 (h : One A c L a b d B Lb) {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 a)
    (hJX : lB A B ≤ X) :
    ¬ Nonempty (↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  intro hφ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := h.std.isE27'
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set θ := aschbacherSolvableCore 3 ↥X with hθdef
  obtain ⟨hθs, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  have hθn : θ.Normal := by
    have := hθc
    exact Subgroup.normal_of_characteristic θ
  set π := QuotientGroup.mk' θ with hπ
  have hXa : X ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem_thetaComponentsAt hX
  have hNX : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    h.le_normalizer hX hJX
  have hEX : A ⊓ Lb ≤ X := by
    have h1 := Item148HJ.inf_le_residual h.std h.hyp h.config
    rw [← h.lB_eq] at h1
    exact h1.trans hJX
  have hS := Item148HJ.sec14Std_of_isLBConfig h.std h.config
  obtain ⟨-, h9, -⟩ := j2_point_facts hS.toSec13Data (Item148HJ.j2_of_isLBConfig h.config)
  set E' := (A ⊓ Lb).subgroupOf X with hE'
  have hinj : ∀ x ∈ E', π x = 1 → x = 1 := by
    intro x hx h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact eq_one_of_mem_aschbacherSolvableCore h1
      (Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.mp hx).1))
  have hĒ9 : Nat.card (E'.map π) = 9 := by
    rw [card_map_eq_of_ker148 hinj, hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv,
      h9]
  have hĒc : ∀ x ∈ E'.map π, ∀ y ∈ E'.map π, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hx).1 _ (Subgroup.mem_subgroupOf.mp hy).1)
  have hĒ3 : ∀ x ∈ E'.map π, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.mp hx).1)
    rw [this, map_one]
  obtain ⟨_, ⟨e', he', rfl⟩, hē1, _, ⟨f', hf', rfl⟩, wb, hwb, hne⟩ :=
    j2_exists_not_comm hφ hĒc hĒ3 hĒ9
  have heA : (e' : G) ∈ A := (Subgroup.mem_subgroupOf.mp he').1
  have heL : (e' : G) ∈ Lb := (Subgroup.mem_subgroupOf.mp he').2
  have hfA : (f' : G) ∈ A := (Subgroup.mem_subgroupOf.mp hf').1
  have he1 : (e' : G) ≠ 1 := fun h1 => hē1 (by rw [show e' = 1 from Subtype.ext h1, map_one])
  have he3 : (e' : G) ^ 3 = 1 := hA3 _ heA
  have hē3 : π e' ^ 3 = 1 := by
    rw [← map_pow, show e' ^ 3 = 1 from Subtype.ext (by simpa using he3), map_one]
  have hae : a ∉ Subgroup.zpowers (e' : G) := fun h1 =>
    h.not_mem_lb (Subgroup.zpowers_le.mpr heL h1)
  set D := Subgroup.closure {(e' : G), a} with hD
  have hDh : IsHyperplane A D := Main148.isHyperplane_closure_pair148 hA heA h.mem he1 hae
  have haD : a ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({(e' : G)} : Set G) ⊓ Subgroup.centralizer ({a} : Set G) :=
    Main148.centralizer_closure_pair148 _ a
  set Nb := Subgroup.normalizer (Subgroup.zpowers (π e') : Set (↥X ⧸ θ)) with hNb
  set Wb := (CFSG.pCore 2 ↥Nb).map Nb.subtype with hWb
  set W : Subgroup G :=
    ((Wb.comap π).map X.subtype) ⊓ Subgroup.centralizer ({(e' : G)} : Set G) with hW
  have hWX : W ≤ X := inf_le_left.trans (Subgroup.map_subtype_le _)
  have hWC : W ≤ Subgroup.centralizer (D : Set G) := by
    rw [hCD]
    exact le_inf inf_le_right (hWX.trans hXa)
  have hWn : ∀ g ∈ Subgroup.centralizer (D : Set G), ∀ x ∈ W, g * x * g⁻¹ ∈ W := by
    intro g hg x hx
    rw [hCD] at hg
    obtain ⟨hge, hga⟩ := hg
    have hgX : g ∈ Subgroup.normalizer (X : Set G) := hNX hga
    obtain ⟨⟨x', hx', rfl⟩, hxe⟩ := hx
    have hmap : X.map (MulAut.conj g).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgX
    set cg : ↥X ≃* ↥X := ((MulAut.conj g).subgroupMap X).trans (MulEquiv.subgroupCongr hmap)
      with hcg
    have hθcg : θ.map (cg : ↥X →* ↥X) = θ :=
      CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three cg
    set σ : (↥X ⧸ θ) ≃* (↥X ⧸ θ) := QuotientGroup.congr θ θ cg hθcg with hσ
    have hσπ : ∀ y : ↥X, σ (π y) = π (cg y) := fun y => QuotientGroup.congr_mk' θ θ cg hθcg y
    have hcge : cg e' = e' := by
      apply Subtype.ext
      show g * (e' : G) * g⁻¹ = e'
      rw [Subgroup.mem_centralizer_singleton_iff.mp hge, mul_inv_cancel_right]
    have hσe : σ (π e') = π e' := by rw [hσπ, hcge]
    refine ⟨⟨cg x', ?_, rfl⟩, ?_⟩
    · show π (cg x') ∈ Wb
      rw [← hσπ]
      exact map_pCore_two_le σ hσe ⟨π x', hx', rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hge hxe) (Subgroup.inv_mem _ hge)
  set ρ : ↥W →* (↥X ⧸ θ) := π.comp (Subgroup.inclusion hWX) with hρ
  have hρW : ∀ w : ↥W, ρ w ∈ Wb := by
    rintro ⟨_, ⟨⟨x', hx', rfl⟩, -⟩⟩
    exact hx'
  have hWb2 : IsPGroup 2 Wb := CFSG.pCore_isPGroup.map _
  have hrange2 : IsPGroup 2 ρ.range := hWb2.to_le (by rintro _ ⟨w, rfl⟩; exact hρW w)
  have hker : ∀ w : ↥W, w ∈ ρ.ker → Subgroup.inclusion hWX w ∈ θ := by
    intro w hw
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hw
    exact hw
  let κ : ↥ρ.ker →* ↥θ :=
    ((Subgroup.inclusion hWX).comp ρ.ker.subtype).codRestrict θ (fun w => hker w w.2)
  have hκ : Function.Injective κ := by
    intro x y hxy
    have hκz : ∀ z : ↥ρ.ker, ((κ z : ↥X) : G) = ((z : ↥W) : G) := fun z => rfl
    have h1 := congrArg (fun z : ↥θ => ((z : ↥X) : G)) hxy
    simp only [hκz] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hW3 : ¬ 3 ∣ Nat.card W := by
    have hcard : Nat.card W = Nat.card ρ.range * Nat.card ρ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    rw [hcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hrange2
      rw [hk] at h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    · exact hθ3 (h3.trans (Subgroup.card_dvd_of_injective κ hκ))
  have hWs : Group.IsSolvable ↥W := by
    have : Group.IsNilpotent ↥ρ.range := hrange2.isNilpotent
    have : Group.IsSolvable ↥θ := hθs
    have : Group.IsSolvable ↥ρ.ker := Group.isSolvable_of_isSolvable_injective hκ
    exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  set CD := Subgroup.centralizer (D : Set G) with hCDdef
  set R := W.subgroupOf CD with hR
  have hRn : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hR, Subgroup.mem_subgroupOf] at hx ⊢
    exact hWn g g.2 x hx
  have hReq : ↥R ≃* ↥W := Subgroup.subgroupOfEquivOfLe hWC
  have hRs : Group.IsSolvable ↥R :=
    Group.isSolvable_of_isSolvable_injective (f := hReq.toMonoidHom) hReq.injective
  have hR3 : ¬ 3 ∣ Nat.card R := by rwa [Nat.card_congr hReq.toEquiv]
  have hRθ := (solvable_prime_complement_core_characterization (H := ↥CD)
    Nat.prime_three).2.2.2.1 R hRn hRs hR3
  have hWθ : W ≤ inSubgroup (aschbacherSolvableCore 3) CD := fun x hx =>
    ⟨⟨x, hWC hx⟩, hRθ (show (⟨x, hWC hx⟩ : ↥CD) ∈ R from hx), rfl⟩
  have hstar := starConditionAt_of_not_mem_omegaA hA.1 h.mem h.ne_one h.not_mem_omegaA
  have hcomm := commutator_theta_le_of_starConditionAt hA h.mem h.ne_one hstar hDh haD
  have hθX := Sec6.theta_eq_inf_of_mem_thetaComponentsAt hX
  have hyf : ∀ y ∈ W, ⁅y, (f' : G)⁆ ∈ inSubgroup (aschbacherSolvableCore 3) X := by
    intro y hy
    rw [hθX]
    refine ⟨?_, hcomm (Subgroup.commutator_mem_commutator (hWθ hy) hfA)⟩
    have hyX := hWX hy
    have hfX : (f' : G) ∈ X := f'.2
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hyX hfX) (X.inv_mem hyX)) (X.inv_mem hfX)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective θ wb
  have hwbe : wb * π e' = π e' * wb :=
    Subgroup.mem_centralizer_singleton_iff.mp (pCore_two_le_centralizer hē3 hwb)
  have hθN3 : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3) X)) := by
    rw [show inSubgroup (aschbacherSolvableCore 3) X = θ.map X.subtype from rfl,
      Subgroup.card_map_of_injective X.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
  have hBN : Subgroup.zpowers (e' : G) ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) X : Set G) :=
    Subgroup.zpowers_le.mpr (Sec6.le_normalizer_theta X e'.2)
  have hB3 : IsPGroup 3 (Subgroup.zpowers (e' : G)) := isPGroup_three_of_pow148 fun β hβ => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
  have hk : ∀ β ∈ Subgroup.zpowers (e' : G),
      (x : G)⁻¹ * (β * x * β⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) X := by
    intro β hβ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ
    have hz : π (x⁻¹ * (e' ^ n * x * (e' ^ n)⁻¹)) = 1 := by
      have hc : Commute (π e' ^ n) wb := (Commute.zpow_left hwbe.symm n)
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_zpow, show π x = wb from hx, hc.eq,
        mul_inv_cancel_right, inv_mul_cancel]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
    exact ⟨_, hz, by simp⟩
  obtain ⟨y, hy, hye⟩ := exists_commute_mem_coset148 hB3 hθN3 hBN hk
  have hyX : y ∈ X := by
    have h1 : (x : G)⁻¹ * y ∈ X := Subgroup.map_subtype_le _ hy
    simpa using X.mul_mem x.2 h1
  have hπy : π ⟨y, hyX⟩ = wb := by
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : (z : G) = (x : G)⁻¹ * y := hzy
    have hxz : (⟨y, hyX⟩ : ↥X) = x * z := Subtype.ext (by
      show y = ((x * z : ↥X) : G)
      rw [Subgroup.coe_mul, hzy', mul_inv_cancel_left])
    rw [hxz, map_mul, show π z = 1 from (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
    exact hx
  have hyW : y ∈ W := by
    refine ⟨⟨⟨y, hyX⟩, ?_, rfl⟩, ?_⟩
    · show π ⟨y, hyX⟩ ∈ Wb
      rw [hπy]
      exact hwb
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hye _ (Subgroup.mem_zpowers _)).symm
  obtain ⟨z, hz, hzc⟩ := hyf y hyW
  have hzc'' : (z : G) = ⁅y, (f' : G)⁆ := hzc
  have hzc' : z = ⁅(⟨y, hyX⟩ : ↥X), f'⁆ := Subtype.ext (by rw [hzc'']; rfl)
  have h1 : π ⁅(⟨y, hyX⟩ : ↥X), f'⁆ = 1 := by
    rw [← hzc', hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hz
  rw [map_commutatorElement, hπy, commutatorElement_eq_one_iff_mul_comm] at h1
  exact hne h1.symm

end One

end Desc143X

theorem step143HJObs :
    Step143HJObs :=
  fun _ _ _ _ _ _ h _ ha ha1 hΩ _ _ _ _ hB haB hc hne _ hX hJX =>
    Desc143X.One.not_j2 ⟨h, ha, ha1, hΩ, hB, haB, hc, hne⟩ hX hJX

end CFSG.RankThree.PartTwo.Sec14
