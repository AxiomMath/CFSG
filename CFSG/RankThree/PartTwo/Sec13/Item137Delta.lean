module

public import CFSG.RankThree.PartTwo.Sec13.Item137
public import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.RankThree.PartTwo.Toolkit.Statements
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.Asc83Table.GL23

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Four

variable {α : Type*}

theorem ne_of_ncard_eq_four {a b c d : α} (h : ({a, b, c, d} : Set α).ncard = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have h3 : ∀ x y z : α, ({x, y, z} : Set α).ncard ≤ 3 := fun x y z =>
    (Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
      (by rw [Set.ncard_singleton])))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq
  · have := h3 a c d
    rw [Set.insert_eq_of_mem (by simp)] at h
    omega
  · have := h3 a b d
    rw [show ({a, b, a, d} : Set α) = {a, b, d} by ext; simp; tauto] at h
    omega
  · have := h3 a b c
    rw [show ({a, b, c, a} : Set α) = {a, b, c} by ext; simp; tauto] at h
    omega
  · have := h3 a b d
    rw [show ({a, b, b, d} : Set α) = {a, b, d} by ext; simp] at h
    omega
  · have := h3 a b c
    rw [show ({a, b, c, b} : Set α) = {a, b, c} by ext; simp; tauto] at h
    omega
  · have := h3 a b c
    rw [show ({a, b, c, c} : Set α) = {a, b, c} by ext; simp] at h
    omega

end Four

section M12

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem facts_of_m12 (h131 : Item131) (hspor : SporadicModels131) (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨φ⟩ := hM
  have hspor' := hspor
  obtain ⟨-, ⟨-, hM12z⟩, -⟩ := hspor'
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv φ hM12z
  have hnotL3 : ¬ IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) := by
    rintro ⟨p, e, hp, -, hiso⟩
    apply KFacts.KS14.not_isoLThreePi_M12 p e
    rcases hiso with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨hq, ⟨φ.symm.trans ψ⟩⟩
    · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩
  rcases cases131 h131 hspor slTwoCenter h with ⟨-, -, -, hcase⟩ | ⟨hcL, h9, -, haut⟩ |
      ⟨-, hPGL, -⟩ | ⟨hcL, -⟩
  · exfalso
    rcases hcase with ⟨hL3, -⟩ | ⟨⟨ψ⟩, -⟩ | ⟨⟨ψ⟩, -⟩
    · exact hnotL3 hL3
    · exact (KFacts.KS14.isEmpty_mulEquiv_M12_alternating.2.1).false (φ.symm.trans ψ)
    · have := Nat.card_congr (φ.symm.trans ψ).toEquiv
      rw [KFacts.KS14.card_nativeM12, KFacts.KS14.card_nativeM22] at this
      norm_num at this
  · exact ⟨hcL, h9, haut⟩
  · exact absurd (facts_of_isZ3PGLThreePi h hPGL).1 hnotL3
  · exact absurd hcL (not_mem_of_center_eq_bot h hZ)

end M12

section Chain

variable {G : Type} [Group G] [Finite G]

theorem nonempty_autIn_zpowers_sup_equiv {L Y : Subgroup G} {c : G} (hc3 : c ^ 3 = 1)
    (hcL : c ∉ L) (hLc : ∀ l ∈ L, l * c = c * l) (hYL : Y ≤ L) (hY : IsPGroup 3 Y) :
    Nonempty (Sec4.autIn L (Subgroup.zpowers c ⊔ Y) ≃*
      Sec4.autIn ⊤ ((Y.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)))) := by
  obtain ⟨e₁⟩ := nonempty_autIn_sup_equiv hLc
    (zpowers_sup_inf_eq hc3 hcL hYL fun y hy => (hLc y (hYL hy)).symm)
  obtain ⟨e₂⟩ := nonempty_autIn_subgroupOf_equiv L le_rfl hYL
  have hY' : IsPGroup 3 (Y.subgroupOf L) :=
    hY.of_equiv (Subgroup.subgroupOfEquivOfLe hYL).symm
  obtain ⟨e₃⟩ := nonempty_autIn_top_mk_equiv hY'
  exact ⟨e₁.trans (e₂.symm.trans ((MulEquiv.subgroupCongr (by rw [Subgroup.subgroupOf_self])).trans
    e₃))⟩

end Chain


section Bar

theorem conjugate_one' {X : Type*} [Group X] (H : Subgroup X) : conjugate H 1 = H := by
  ext x
  simp [conjugate]

theorem exists_bar_config (h414 : Sec4.Item4_14_local)
    (hM12D : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
      Toolkit.M12ThreeLocalData X)
    {Λ : Type} [Group Λ] [Finite Λ]
    (hM : Nonempty (Λ ⧸ aschbacherSolvableCore 3 Λ ≃* CFSG.Blueprint.NativeSporadic.M12))
    (S : Sylow 3 Λ) {B : Subgroup Λ} (hBS : B ≤ S) (hB9 : Nat.card B = 9)
    (hBaut : Nat.card (Sec4.autIn ⊤ (B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)))) =
      6) :
    ∃ (E F : Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ)) (t : Λ),
      t ∈ Subgroup.normalizer ((S : Subgroup Λ) : Set Λ) ∧
      (∀ z ∈ (S : Subgroup Λ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) ⊓
          Subgroup.centralizer (((S : Subgroup Λ).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) : Subgroup _) : Set _),
        QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) t * z *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) t)⁻¹ = z⁻¹) ∧
      {Y : Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ) |
          Y ≤ (S : Subgroup Λ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) ∧
            Nat.card Y = 9} =
        {E, F, B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)),
          conjugate (B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)))
            (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) t)} ∧
      ({E, F, B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)),
          conjugate (B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)))
            (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) t)} : Set _).ncard = 4 ∧
      Nonempty (Sec4.autIn ⊤ E ≃* GL (Fin 2) (ZMod 3)) ∧
      Nonempty (Sec4.autIn ⊤ F ≃* GL (Fin 2) (ZMod 3)) ∧
      Sec4.IsHeisThree ((S : Subgroup Λ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := hM
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) with hπ
  set Ps : Sylow 3 (Λ ⧸ aschbacherSolvableCore 3 Λ) :=
    S.mapSurjective (QuotientGroup.mk'_surjective _) with hPsdef
  have hPs : (Ps : Subgroup _) = (S : Subgroup Λ).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨hHeis, -, E, F, A, t₁, ht₁, hinv, hΔ, ⟨eE⟩, ⟨eF⟩, -, -⟩ := h414 _ ⟨φ⟩ Ps
  obtain ⟨-, -, -, -, -, hncard, -, -⟩ := hM12D _ ⟨φ⟩ Ps
  rw [hPs] at hHeis ht₁ hinv hΔ hncard
  have hBmem : B.map π ∈ {Y : Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ) |
      Y ≤ (S : Subgroup Λ).map π ∧ Nat.card Y = 9} := by
    refine ⟨Subgroup.map_mono hBS, ?_⟩
    rw [card_map_eq_of_injOn _ ((injOn_mk_of_isPGroup Nat.prime_three S.isPGroup').mono hBS), hB9]
  have hEc : Nat.card (Sec4.autIn ⊤ E) = 48 := by
    rw [Nat.card_congr eE.toEquiv]
    exact CFSG.RankThree.Asc83Table.card_GL23
  have hFc : Nat.card (Sec4.autIn ⊤ F) = 48 := by
    rw [Nat.card_congr eF.toEquiv]
    exact CFSG.RankThree.Asc83Table.card_GL23
  have hN := normalizer_map_mk_eq S.isPGroup'
  rw [← hπ] at hN
  have hΔ' := hΔ
  rw [hΔ] at hBmem
  rcases hBmem with hE | hF | hA | hAt
  · rw [hE, hEc] at hBaut
    norm_num at hBaut
  · rw [hF, hFc] at hBaut
    norm_num at hBaut
  · rw [hN] at ht₁
    obtain ⟨t, ht, rfl⟩ := ht₁
    refine ⟨E, F, t, ht, hinv, ?_, ?_, ⟨eE⟩, ⟨eF⟩, hHeis⟩
    · rw [hΔ', hA]
    · rw [hA, ← hΔ']
      exact hΔ' ▸ hncard
  · rw [hN] at ht₁
    obtain ⟨t, ht, htt⟩ := ht₁
    have hconj : conjugate (B.map π) (π t⁻¹) = A := by
      rw [hAt, map_inv, htt, KFacts.KS14.conjugate_conjugate_eq_mul, mul_inv_cancel,
        conjugate_one']
    have hset : ({E, F, B.map π, conjugate (B.map π) (π t⁻¹)} :
        Set (Subgroup (Λ ⧸ aschbacherSolvableCore 3 Λ))) = {E, F, A, conjugate A t₁} := by
      rw [hconj, hAt]
      ext X
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    refine ⟨E, F, t⁻¹, inv_mem ht, fun z hz => ?_, ?_, ?_, ⟨eE⟩, ⟨eF⟩, hHeis⟩
    · have h1 := hinv z⁻¹ (inv_mem hz)
      rw [map_inv, inv_inv, htt]
      rw [inv_inv] at h1
      calc t₁⁻¹ * z * t₁ = t₁⁻¹ * (t₁ * z⁻¹ * t₁⁻¹) * t₁ := by rw [h1]
        _ = z⁻¹ := by group
    · rw [hset, hΔ']
    · rw [hset, ← hΔ']
      exact hΔ' ▸ hncard

end Bar


section GSide

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem setOf_le_map_subtype_card_eq (K : Subgroup G) (T : Subgroup K) (n : ℕ) :
    {Y : Subgroup G | Y ≤ T.map K.subtype ∧ Nat.card Y = n} =
      (fun Y' : Subgroup K => Y'.map K.subtype) ''
        {Y' : Subgroup K | Y' ≤ T ∧ Nat.card Y' = n} := by
  ext Y
  constructor
  · rintro ⟨hYT, hYn⟩
    have hYK : Y ≤ K := hYT.trans (Subgroup.map_subtype_le T)
    refine ⟨Y.subgroupOf K, ⟨?_, ?_⟩, Subgroup.map_subgroupOf_eq_of_le hYK⟩
    · rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hYK]
      exact hYT
    · rw [← hYn]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv
  · rintro ⟨Y', ⟨hY'T, hY'n⟩, rfl⟩
    exact ⟨Subgroup.map_mono hY'T, by rw [Subgroup.card_map_of_injective K.subtype_injective,
      hY'n]⟩

omit [Finite G] in
theorem mem_normalizer_map_subtype {K : Subgroup G} {T : Subgroup K} {t : K}
    (ht : t ∈ Subgroup.normalizer (T : Set K)) :
    (t : G) ∈ Subgroup.normalizer ((T.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at ht ⊢
  have h : (T.map K.subtype).map (MulAut.conj (t : G) : G →* G) =
      (T.map (MulAut.conj t : K →* K)).map K.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [h, ht]

omit [Finite G] in
theorem conjugate_zpowers_sup {c t : G} (hct : t * c = c * t) (Y : Subgroup G) :
    conjugate (Subgroup.zpowers c ⊔ Y) t = Subgroup.zpowers c ⊔ conjugate Y t := by
  rw [conjugate, conjugate, Subgroup.map_sup, MonoidHom.map_zpowers]
  congr 2
  change t⁻¹ * c * t⁻¹⁻¹ = c
  rw [inv_inv, mul_assoc, ← hct]
  group

theorem pow_three_eq_one_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Monoid.exponent Y = 3) (x : X) : x ^ 3 = 1 := by
  apply e.injective
  rw [map_pow, map_one, ← hY]
  exact Monoid.pow_exponent_eq_one _

end GSide


section Lifted

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def liftSup (L : Subgroup G) (c : G) (S : Subgroup L)
    (Y : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Subgroup G :=
  Subgroup.zpowers c ⊔ (liftIn S Y).map L.subtype

variable {L : Subgroup G} {c : G}

theorem liftSup_inf (hc3 : c ^ 3 = 1) (hcL : c ∉ L) (hLc : ∀ l ∈ L, l * c = c * l)
    (S : Subgroup L) (Y : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :
    liftSup L c S Y ⊓ L = (liftIn S Y).map L.subtype :=
  zpowers_sup_inf_eq hc3 hcL (Subgroup.map_subtype_le _)
    (fun y hy => (hLc y (Subgroup.map_subtype_le _ hy)).symm)

theorem liftSup_injOn (hc3 : c ^ 3 = 1) (hcL : c ∉ L) (hLc : ∀ l ∈ L, l * c = c * l)
    (S : Subgroup L) :
    Set.InjOn (liftSup L c S)
      {Y | Y ≤ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))} := by
  intro Y₁ hY₁ Y₂ hY₂ h12
  have h1 := congrArg (· ⊓ L) h12
  simp only [liftSup_inf hc3 hcL hLc] at h1
  have h2 := Subgroup.map_injective L.subtype_injective h1
  rw [← map_liftIn hY₁, ← map_liftIn hY₂, h2]

theorem liftSup_map {S X : Subgroup L} (hS3 : IsPGroup 3 S) (hXS : X ≤ S) :
    liftSup L c S (X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) =
      Subgroup.zpowers c ⊔ X.map L.subtype := by
  rw [liftSup, liftIn_map hS3 hXS]

theorem liftSup_conjugate (hLc : ∀ l ∈ L, l * c = c * l) {S : Subgroup L} (hS3 : IsPGroup 3 S)
    {Y : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (hY : Y ≤ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) {t : L}
    (ht : t ∈ Subgroup.normalizer (S : Set L)) :
    liftSup L c S (conjugate Y (QuotientGroup.mk' (aschbacherSolvableCore 3 L) t)) =
      conjugate (liftSup L c S Y) (t : G) := by
  rw [liftSup, liftSup, liftIn_conjugate hS3 hY ht, map_conjugate_hom,
    conjugate_zpowers_sup (hLc t t.2)]
  rfl

theorem nonempty_autIn_liftSup (hc3 : c ^ 3 = 1) (hcL : c ∉ L) (hLc : ∀ l ∈ L, l * c = c * l)
    {S : Subgroup L} (hS3 : IsPGroup 3 S) {Y : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (hY : Y ≤ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) :
    Nonempty (Sec4.autIn L (liftSup L c S Y) ≃* Sec4.autIn ⊤ Y) := by
  have hYL : (liftIn S Y).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hYp : IsPGroup 3 ((liftIn S Y).map L.subtype) := (hS3.to_le (liftIn_le _ _)).map _
  obtain ⟨e⟩ := nonempty_autIn_zpowers_sup_equiv hc3 hcL hLc hYL hYp
  have hsub : ((liftIn S Y).map L.subtype).subgroupOf L = liftIn S Y := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  rw [hsub, map_liftIn hY] at e
  exact ⟨e⟩

theorem facts_of_isHeisThree_map {S : Subgroup L} (hS3 : IsPGroup 3 S)
    (hHeis : Sec4.IsHeisThree (S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)))) :
    Nat.card (S.map L.subtype) = 27 ∧
      Nat.card (S.map L.subtype ⊓ Subgroup.centralizer ((S.map L.subtype : Subgroup G) : Set G) :
        Subgroup G) = 3 ∧
      ∀ s ∈ S.map L.subtype, s ^ 3 = 1 := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  let ψ : (S.map L.subtype) ≃* (S.map π) :=
    (S.equivMapOfInjective L.subtype L.subtype_injective).symm.trans (mkEquivOfIsPGroup hS3)
  refine ⟨?_, ?_, fun s hs => ?_⟩
  · rw [Nat.card_congr ψ.toEquiv]
    exact hHeis.2.1
  · rw [← Sec14.map_subtype_center_eq,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      ← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, map_center_mulEquiv ψ]
    exact hHeis.1.2.2.2
  · have := pow_three_eq_one_of_mulEquiv ψ hHeis.2.2 ⟨s, hs⟩
    simpa using congrArg Subtype.val this

theorem setOf_elemAbelian_eq_image_liftSup (hc3 : c ^ 3 = 1) (hcL : c ∉ L)
    (hLc : ∀ l ∈ L, l * c = c * l) {S : Subgroup L} (hS3 : IsPGroup 3 S)
    (hHeis : Sec4.IsHeisThree (S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)))) :
    {X : Subgroup G | X ≤ Subgroup.zpowers c ⊔ S.map L.subtype ∧
        CFSG.Assembly.IsElemAbelian 3 X ∧ Nat.card X = 27} =
      liftSup L c S '' {Y | Y ≤ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ∧
        Nat.card Y = 9} := by
  obtain ⟨h27, hZ, h3⟩ := facts_of_isHeisThree_map hS3 hHeis
  have hSLL : S.map L.subtype ≤ L := Subgroup.map_subtype_le _
  rw [setOf_elemAbelian_eq_image hc3 (fun hc => hcL (hSLL hc))
      (fun s hs => (hLc s (hSLL hs)).symm) h27 hZ h3,
    setOf_le_map_subtype_card_eq L S 9, setOf_le_card_eq_image_liftIn hS3 9, Set.image_image,
    Set.image_image]
  rfl

theorem card_zpowers_sup_map (hc3 : c ^ 3 = 1) (hcL : c ∉ L) (hLc : ∀ l ∈ L, l * c = c * l)
    {S : Subgroup L} (hS27 : Nat.card (S.map L.subtype) = 27) :
    Nat.card (Subgroup.zpowers c ⊔ S.map L.subtype : Subgroup G) = 81 := by
  have hSLL : S.map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ m ∈ S.map L.subtype, x * m = m * x := by
    intro x hx m hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hLc m (hSLL hm)).symm k).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  rw [zpowers_inf_eq_bot hc3 (fun hc => hcL (hSLL hc)), Subgroup.card_bot, mul_one,
    card_zpowers_of_pow_three hc3 hc1, hS27] at hcard
  exact hcard

theorem isSylowOf_zpowers_sup (hc3 : c ^ 3 = 1) (hcL : c ∉ L) (hLc : ∀ l ∈ L, l * c = c * l)
    (S : Sylow 3 L) (hS27 : Nat.card ((S : Subgroup L).map L.subtype) = 27) :
    CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype)
      (Subgroup.zpowers c ⊔ L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP81 := card_zpowers_sup_map hc3 hcL hLc hS27
  have hle : Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype ≤ Subgroup.zpowers c ⊔ L :=
    sup_le_sup_left (Subgroup.map_subtype_le _) _
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hle, IsPGroup.of_card (n := 4) (by rw [hP81]; norm_num), ?_⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ m ∈ L, x * m = m * x := by
    intro x hx m hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hLc m hm).symm k).eq
  obtain ⟨hcardL, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  rw [zpowers_inf_eq_bot hc3 hcL, Subgroup.card_bot, mul_one,
    card_zpowers_of_pow_three hc3 hc1] at hcardL
  have hLS := Subgroup.card_mul_index (S : Subgroup L)
  rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective, hS27] at hLS
  have hrel := Subgroup.relIndex_mul_card (Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype)
    (Subgroup.zpowers c ⊔ L)
  rw [inf_eq_left.mpr hle, hP81, hcardL, ← hLS] at hrel
  have hr : (Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype).relIndex
      (Subgroup.zpowers c ⊔ L) = (S : Subgroup L).index := by omega
  rw [hr]
  exact S.not_dvd_index

omit [Finite G] in
theorem le_normalizer_of_card {A P : Subgroup G} (hAP : A ≤ P) (hA : Nat.card A = 27)
    (hP : Nat.card P = 81) : P ≤ Subgroup.normalizer (A : Set G) := by
  have hidx : (A.subgroupOf P).index = 3 := by
    have := Subgroup.relIndex_mul_card A P
    rw [inf_eq_left.mpr hAP, hA, hP] at this
    change A.relIndex P = 3
    omega
  have hmin : (Nat.card P).minFac = 3 := by rw [hP]; norm_num
  have := Subgroup.normal_of_index_eq_minFac_card (hidx.trans hmin.symm)
  exact Subgroup.le_normalizer_of_normal_subgroupOf hAP

omit [Finite G] in
theorem mem_normalizer_zpowers_sup (hLc : ∀ l ∈ L, l * c = c * l) {S : Subgroup L} {t : L}
    (ht : t ∈ Subgroup.normalizer (S : Set L)) :
    (t : G) ∈ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ S.map L.subtype : Subgroup G) : Set G) := by
  have htS := mem_normalizer_map_subtype ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htS ⊢
  rw [Subgroup.map_sup, htS, MonoidHom.map_zpowers]
  congr 2
  change (t : G) * c * (t : G)⁻¹ = c
  rw [hLc t t.2, mul_inv_cancel_right]

theorem inv_of_mem_commutator (hLc : ∀ l ∈ L, l * c = c * l) {S : Subgroup L}
    (hS3 : IsPGroup 3 S)
    (hHeis : Sec4.IsHeisThree (S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)))) {t : L}
    (ht : t ∈ Subgroup.normalizer (S : Set L))
    (hinv : ∀ z ∈ S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ⊓
        Subgroup.centralizer ((S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :
          Subgroup _) : Set _),
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) t * z *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) t)⁻¹ = z⁻¹) :
    ∀ z ∈ ⁅Subgroup.zpowers c ⊔ S.map L.subtype, Subgroup.zpowers c ⊔ S.map L.subtype⁆,
      (t : G) * z * (t : G)⁻¹ = z⁻¹ := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  have hSLL : S.map L.subtype ≤ L := Subgroup.map_subtype_le _
  intro z hz
  have hz' : z ∈ ⁅S.map L.subtype, S.map L.subtype⁆ :=
    commutator_zpowers_sup_le (fun s hs => (hLc s (hSLL hs)).symm) hz
  rw [← Subgroup.map_commutator] at hz'
  obtain ⟨z', hz'S, rfl⟩ := hz'
  have hz'S' : z' ∈ S :=
    (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hz'S
  have h2 : ⁅S.map π, S.map π⁆ =
      S.map π ⊓ Subgroup.centralizer ((S.map π : Subgroup _) : Set _) := by
    calc ⁅S.map π, S.map π⁆ = (commutator ↥(S.map π)).map (S.map π).subtype := by
          rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
            Subgroup.range_subtype]
      _ = (Subgroup.center ↥(S.map π)).map (S.map π).subtype := by rw [hHeis.1.2.1]
      _ = _ := Sec14.map_subtype_center_eq _
  have hπz : π z' ∈ S.map π ⊓ Subgroup.centralizer ((S.map π : Subgroup _) : Set _) := by
    rw [← h2, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem π hz'S
  have h3 := hinv (π z') hπz
  have hconjS : t * z' * t⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp ht z').mp hz'S'
  have h4 : t * z' * t⁻¹ = z'⁻¹ := by
    apply injOn_mk_of_isPGroup Nat.prime_three hS3 hconjS (inv_mem hz'S')
    rw [map_mul, map_mul, map_inv, map_inv]
    exact h3
  have h5 := congrArg Subtype.val h4
  simpa using h5

end Lifted

section Main

theorem item137Delta_of (h131 : Item131) (hspor : SporadicModels131) (h414 : Sec4.Item4_14_local)
    (hM12D : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
      Toolkit.M12ThreeLocalData X) : Item137Delta := by
  intro G _ _ A c L h hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcL, h9, ⟨eA⟩⟩ := facts_of_m12 h131 hspor h hM
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine hc3 (fun hcB => hcL (hBL hcB)) le_rfl h9
      (fun b hb => h.isElemAbelian.2 b hb.1) (fun b hb => h.commute h.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_eq, hcard])).symm
  have hBp : IsPGroup 3 (A ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  have hB'map : ((A ⊓ L).subgroupOf L).map L.subtype = A ⊓ L :=
    Subgroup.map_subgroupOf_eq_of_le hBL
  have hB'9 : Nat.card ((A ⊓ L).subgroupOf L) = 9 := by
    rw [← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hB'3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) :=
    IsPGroup.of_card (n := 2) (by rw [hB'9]; norm_num)
  obtain ⟨S, hBS⟩ := hB'3.exists_le_sylow
  have hS3 : IsPGroup 3 (S : Subgroup L) := S.isPGroup'
  have hBaut : Nat.card (Sec4.autIn ⊤
      (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)))) = 6 := by
    obtain ⟨e⟩ := nonempty_autIn_zpowers_sup_equiv hc3 hcL hLc hBL hBp
    rw [← hAB] at e
    rw [Nat.card_congr (e.symm.trans eA).toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  obtain ⟨Eb, Fb, t₀, ht₀, hinv, hΔ, hncard, ⟨eE⟩, ⟨eF⟩, hHeis⟩ :=
    exists_bar_config h414 hM12D hM S hBS hB'9 hBaut
  obtain ⟨hS27, -, -⟩ := facts_of_isHeisThree_map hS3 hHeis
  have hΦB := liftSup_map (c := c) hS3 hBS
  rw [hB'map, ← hAB] at hΦB
  have hΦBt := liftSup_conjugate hLc hS3 (Subgroup.map_mono hBS) ht₀
  rw [hΦB] at hΦBt
  have hsetG := setOf_elemAbelian_eq_image_liftSup hc3 hcL hLc hS3 hHeis
  rw [hΔ, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    hΦB, hΦBt] at hsetG
  have hsub4 : ({Eb, Fb,
      ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)),
      conjugate (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)))
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) t₀)} :
      Set (Subgroup (L ⧸ aschbacherSolvableCore 3 L))) ⊆
        {Y | Y ≤ (S : Subgroup L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))} := by
    rw [← hΔ]
    exact fun Y hY => hY.1
  have hncardG : ({liftSup L c S Eb, liftSup L c S Fb, A, conjugate A (t₀ : G)} :
      Set (Subgroup G)).ncard = 4 := by
    have := ((liftSup_injOn hc3 hcL hLc S).mono hsub4).ncard_image
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hΦB,
      hΦBt, hncard] at this
    exact this
  obtain ⟨hEF, hEA, hEAt, hFA, hFAt, hAAt⟩ := ne_of_ncard_eq_four hncardG
  have hP81 := card_zpowers_sup_map hc3 hcL hLc hS27
  have hAP : A ≤ Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype :=
    hAB ▸ sup_le_sup_left (hB'map ▸ Subgroup.map_mono hBS) _
  have hAL : A ⊔ L = Subgroup.zpowers c ⊔ L :=
    le_antisymm (sup_le (hAB ▸ sup_le le_sup_left (hBL.trans le_sup_right)) le_sup_right)
      (sup_le_sup_right (Subgroup.zpowers_le.mpr h.mem_A) L)
  have hPAL : Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype ≤ A ⊔ L :=
    hAL ▸ sup_le_sup_left (Subgroup.map_subtype_le _) _
  have hPNA := le_normalizer_of_card hAP h.card_eq hP81
  have hEP : ∀ Y, liftSup L c S Y ≤ Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype :=
    fun Y => sup_le_sup_left (Subgroup.map_mono (liftIn_le _ _)) _
  obtain ⟨eE'⟩ := nonempty_autIn_liftSup hc3 hcL hLc hS3 (hsub4 (by simp) : Eb ≤ _)
  obtain ⟨eF'⟩ := nonempty_autIn_liftSup hc3 hcL hLc hS3 (hsub4 (by simp) : Fb ≤ _)
  refine ⟨Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype, liftSup L c S Eb,
    liftSup L c S Fb, (t₀ : G), hAL ▸ isSylowOf_zpowers_sup hc3 hcL hLc S hS27, hAP,
    ⟨t₀.2, mem_normalizer_zpowers_sup hLc ht₀⟩, inv_of_mem_commutator hLc hS3 hHeis ht₀ hinv,
    ?_, hAAt, hEF, hEA, hEAt, hFA, hFAt, (hEP Eb).trans (le_inf hPAL hPNA),
    (hEP Fb).trans (le_inf hPAL hPNA), ⟨eE'.trans eE⟩, ⟨eF'.trans eF⟩,
    by rw [liftSup_inf hc3 hcL hLc]; rfl, by rw [liftSup_inf hc3 hcL hLc]; rfl⟩
  rw [hsetG]
  ext X
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

end Main

end CFSG.RankThree.PartTwo.Sec13
