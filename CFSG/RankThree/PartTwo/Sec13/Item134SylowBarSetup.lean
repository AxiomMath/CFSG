module

public import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Base (A : Subgroup G) (c : G) (L : Subgroup G) (d : G) (K : Subgroup G) : Prop where
  h45 : Sec4.Item4_5
  h131 : Item131
  hspor : SporadicModels131
  h415 : Sec4.Item4_15
  data : Sec13Data G A c L
  quot : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  mem_A : d ∈ A
  ne_one : d ≠ 1
  sylow : ∃ S : Subgroup G, IsSylowOf 3 S L ∧
    (Subgroup.center S).map S.subtype = Subgroup.zpowers d
  mem_K : K ∈ thetaComponentsAt 3 d
  residual_le : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K
  tripleCover : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))
  le_center : ∀ P : Subgroup G, IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)) →
    Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ (Subgroup.center P).map P.subtype

structure Hyp (A : Subgroup G) (c : G) (L : Subgroup G) (d : G) (K : Subgroup G) : Prop
    extends Base A c L d K where
  not_le : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G)

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem c_pow (H : Base A c L d K) : c ^ 3 = 1 :=
  H.data.isElemAbelian.2 c H.data.mem_A

theorem d_pow (H : Base A c L d K) : d ^ 3 = 1 :=
  H.data.isElemAbelian.2 d H.mem_A

theorem orderOf_d (H : Base A c L d K) : orderOf d = 3 :=
  orderOf_eq_prime H.d_pow H.ne_one

theorem comm_cd (H : Base A c L d K) : c * d = d * c :=
  H.data.commute H.data.mem_A H.mem_A

theorem comm_L (H : Base A c L d K) {l : G} (hl : l ∈ L) : l * c = c * l :=
  Subgroup.mem_centralizer_singleton_iff.mp (H.data.le_centralizer hl)

theorem exists_d_mem_L (H : Base A c L d K) :
    ∃ hdL : d ∈ L, ∃ S' : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S' : Subgroup ↥L) ∧
      (S' : Subgroup ↥L) ≤ Subgroup.centralizer ({(⟨d, hdL⟩ : ↥L)} : Set ↥L) :=
  exists_sylow_of_center_eq H.sylow

theorem d_mem_L (H : Base A c L d K) : d ∈ L := H.exists_d_mem_L.1

theorem center_quot (H : Base A c L d K) :
    Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
  obtain ⟨-, -, -, hJ2z⟩ := H.hspor
  obtain ⟨φ⟩ := H.quot
  exact center_eq_bot_of_mulEquiv φ hJ2z

theorem not_mem_L (H : Base A c L d K) : c ∉ L :=
  not_mem_of_center_eq_bot H.data H.center_quot

theorem card_inf (H : Base A c L d K) : Nat.card (A ⊓ L : Subgroup G) = 9 := by
  obtain ⟨φ⟩ := H.quot
  obtain ⟨-, -, h9 | hPGL⟩ := facts_of_not_mem H.h131 H.hspor slTwoCenter H.data H.not_mem_L
  · exact h9
  · exfalso
    obtain ⟨p, e, hp, -, hiso⟩ := (facts_of_isZ3PGLThreePi H.data hPGL).1
    apply KFacts.KS14.ks17J2NotList.1 p e
    rcases hiso with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨hq, ⟨φ.symm.trans ψ⟩⟩
    · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩

theorem eq_sup (H : Base A c L d K) : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr H.data.mem_A) inf_le_left
  have hcard := (isElemAbelian_zpowers_sup_of_card_nine H.c_pow
    (fun hcB => H.not_mem_L (Subgroup.mem_inf.mp hcB).2) le_rfl H.card_inf
    (fun b hb => H.data.isElemAbelian.2 b hb.1) (fun b hb => H.data.commute H.data.mem_A hb.1)).2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [H.data.card_eq, hcard])).symm

theorem c_not_mem_zpowers_d (H : Base A c L d K) : c ∉ Subgroup.zpowers d := fun hc =>
  H.not_mem_L ((Subgroup.zpowers_le.mpr H.d_mem_L) hc)

theorem B_le (H : Base A c L d K) : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A :=
  sup_le (Subgroup.zpowers_le.mpr H.data.mem_A) (Subgroup.zpowers_le.mpr H.mem_A)

end Base


section Weak

variable {L : Subgroup G}

theorem eq_one_of_mem_theta_of_pow {x : ↥L} (hx : x ∈ aschbacherSolvableCore 3 ↥L) {k : ℕ}
    (hk : x ^ 3 ^ k = 1) : x = 1 :=
  eq_one_of_pow_three_pow_of_not_dvd
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1 hx hk

theorem zpowers_eq_of_central_of_quot_j2 (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {E : Subgroup G} (hE : IsPGroup 3 E) {d₁ d₂ : G} (h₁E : d₁ ∈ E) (h₂E : d₂ ∈ E)
    (h₁L : d₁ ∈ L) (h₂L : d₂ ∈ L) (h₁ : d₁ ≠ 1) (h₂ : d₂ ≠ 1)
    (hc₁ : ∃ S : Sylow 3 ↥L, (⟨d₁, h₁L⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d₁, h₁L⟩ : ↥L)})
    (hc₂ : ∃ S : Sylow 3 ↥L, (⟨d₂, h₂L⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d₂, h₂L⟩ : ↥L)}) :
    Subgroup.zpowers d₁ = Subgroup.zpowers d₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := aschbacherSolvableCore 3 ↥L
  set π := QuotientGroup.mk' O
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  set E' := (E.subgroupOf L).map π
  have hE' : IsPGroup 3 E' :=
    (hE.comap_of_injective L.subtype L.subtype_injective).map π
  have h3 : ∀ x : ↥L, (x : G) ∈ E → ∃ k : ℕ, x ^ 3 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hE ⟨x, hx⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hne : ∀ x : ↥L, (x : G) ∈ E → (x : G) ≠ 1 → π x ≠ 1 := fun x hx hx1 h => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨k, hk⟩ := h3 x hx
    exact hx1 (congrArg Subtype.val (eq_one_of_mem_theta_of_pow h hk))
  have hcen : ∀ (x : ↥L), (∃ S : Sylow 3 ↥L, x ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {x}) →
      ∃ S' : Sylow 3 (↥L ⧸ O), π x ∈ (S' : Subgroup (↥L ⧸ O)) ∧
        (S' : Subgroup (↥L ⧸ O)) ≤ Subgroup.centralizer {π x} := by
    rintro x ⟨S, hxS, hSx⟩
    refine ⟨S.mapSurjective hπs, ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem π hxS
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp (hSx hy)]
  have hbar := Sec14.j2_zpowers_eq_of_mem h415 hJ2 hE'
    (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr h₁E))
    (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr h₂E))
    (hne _ h₁E h₁) (hne _ h₂E h₂) (hcen _ hc₁) (hcen _ hc₂)
  have lift : ∀ {x y : G} (hxE : x ∈ E) (hyE : y ∈ E) (hxL : x ∈ L) (hyL : y ∈ L),
      π ⟨y, hyL⟩ ∈ Subgroup.zpowers (π ⟨x, hxL⟩) → y ∈ Subgroup.zpowers x := by
    intro x y hxE hyE hxL hyL hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hO : (⟨x, hxL⟩ : ↥L) ^ (-k) * ⟨y, hyL⟩ ∈ O := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_zpow, ← hk,
        ← zpow_add, neg_add_cancel, zpow_zero]
    have hEz : ((⟨x, hxL⟩ : ↥L) ^ (-k) * ⟨y, hyL⟩ : ↥L).1 ∈ E := by
      simpa using E.mul_mem (E.zpow_mem hxE (-k)) hyE
    obtain ⟨j, hj⟩ := h3 _ hEz
    have h1 := eq_one_of_mem_theta_of_pow hO hj
    have h1' : x ^ (-k) * y = 1 := by simpa using congrArg Subtype.val h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    calc x ^ k = x ^ k * (x ^ (-k) * y) := by rw [h1', mul_one]
      _ = y := by rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr (lift h₂E h₁E h₂L h₁L (hbar ▸ Subgroup.mem_zpowers _))
  · exact Subgroup.zpowers_le.mpr (lift h₁E h₂E h₁L h₂L (hbar.symm ▸ Subgroup.mem_zpowers _))

theorem central_conj {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) {z : G} (hzL : z ∈ L)
    (hz : ∃ S : Sylow 3 ↥L, (⟨z, hzL⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨z, hzL⟩ : ↥L)})
    (hgz : g * z * g⁻¹ ∈ L) :
    ∃ S : Sylow 3 ↥L, (⟨g * z * g⁻¹, hgz⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨g * z * g⁻¹, hgz⟩ : ↥L)} := by
  obtain ⟨S, hzS, hSz⟩ := hz
  set σ := L.normalizerMonoidHom ⟨g, hg⟩ with hσ
  have hσz : σ ⟨z, hzL⟩ = ⟨g * z * g⁻¹, hgz⟩ := Subtype.ext rfl
  have hsurj : Function.Surjective σ.toMonoidHom := fun y => ⟨σ.symm y, by simp⟩
  refine ⟨S.mapSurjective hsurj, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective, ← hσz]
    exact Subgroup.mem_map_of_mem _ hzS
  · rw [Sylow.coe_mapSurjective]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hσz]
    change σ y * σ ⟨z, hzL⟩ = σ ⟨z, hzL⟩ * σ y
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hSz hy)]

end Weak

structure SylowData (A L : Subgroup G) (d : G) (K S : Subgroup G) : Prop where
  isSylowOf : IsSylowOf 3 S L
  inf_le : A ⊓ L ≤ S
  le_centralizer : S ≤ Subgroup.centralizer ({d} : Set G)
  card_eq : Nat.card S = 27
  commutator_mem : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ Subgroup.zpowers d
  mem_zpowers_of_central : ∀ s ∈ S, (∀ s' ∈ S, s * s' = s' * s) → s ∈ Subgroup.zpowers d
  mem_of_card : ∀ X : Subgroup G, X ≤ S → Nat.card X = 9 → d ∈ X
  le_K : S ≤ K

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem exists_sylowData (H : Base A c L d K) : ∃ S : Subgroup G, SylowData A L d K S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdL, S₀, hdS₀, hS₀d⟩ := H.exists_d_mem_L
  set E := A ⊓ L with hEdef
  have hE9 := H.card_inf
  have hEp : IsPGroup 3 (E.subgroupOf L) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ≤ L)).toEquiv, hE9]
    norm_num)
  obtain ⟨S', hS'⟩ := hEp.exists_le_sylow
  set S := (S' : Subgroup ↥L).map L.subtype with hSdef
  have hSp : IsPGroup 3 S := S'.isPGroup'.map _
  have hES : E ≤ S := fun x hx => ⟨⟨x, hx.2⟩, hS' (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hSL : S ≤ L := Subgroup.map_subtype_le _
  have hmemS : ∀ {x : G} (hx : x ∈ S), (⟨x, hSL hx⟩ : ↥L) ∈ (S' : Subgroup ↥L) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  have hdS : d ∈ S := hES ⟨H.mem_A, hdL⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hinj : Set.InjOn π (S' : Set ↥L) := injOn_mk_of_isPGroup Nat.prime_three S'.isPGroup'
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    S'.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (S' : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨⟨hHeis, -⟩, -⟩ := H.h415 _ H.quot Sb _ rfl _ rfl
  have hd'1 : (⟨d, hdL⟩ : ↥L) ≠ 1 := fun h => H.ne_one (congrArg Subtype.val h)
  obtain ⟨hdb1, hdP⟩ := bar_facts_of_central hd'1 ⟨S₀, hdS₀, hS₀d⟩
  have hdSb : π ⟨d, hdL⟩ ∈ (Sb : Subgroup _) := by
    rw [hSb]
    exact Subgroup.mem_map_of_mem π (hmemS hdS)
  have hZ := Sec14.j2_zpowers_eq H.h415 H.quot Sb hdb1 hdSb hdP
  have hdZ : π ⟨d, hdL⟩ ∈ (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ⊓
      Subgroup.centralizer ((Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rw [← hZ]
    exact Subgroup.mem_zpowers _
  have hSd : S ≤ Subgroup.centralizer ({d} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxS := hmemS hx
    have h1 : π ⟨x, hSL hx⟩ * π ⟨d, hdL⟩ = π ⟨d, hdL⟩ * π ⟨x, hSL hx⟩ :=
      (Subgroup.mem_centralizer_iff.mp hdZ.2 _ (hSb ▸ Subgroup.mem_map_of_mem π hxS))
    rw [← map_mul, ← map_mul] at h1
    have h2 := hinj ((S' : Subgroup ↥L).mul_mem hxS (hmemS hdS))
      ((S' : Subgroup ↥L).mul_mem (hmemS hdS) hxS) h1
    exact congrArg Subtype.val h2
  refine ⟨S, ⟨S', rfl⟩, hES, hSd, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hSdef, Subgroup.card_map_of_injective L.subtype_injective,
      ← card_map_eq_of_injOn π hinj, ← hSb]
    exact hHeis.2.1
  ·
    intro x hx y hy
    have hxS := hmemS hx
    have hyS := hmemS hy
    set a : ↥(Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
      ⟨π ⟨x, hSL hx⟩, hSb ▸ Subgroup.mem_map_of_mem π hxS⟩
    set b : ↥(Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
      ⟨π ⟨y, hSL hy⟩, hSb ▸ Subgroup.mem_map_of_mem π hyS⟩
    have hab : ⁅a, b⁆ ∈ Subgroup.center ↥(Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
      rw [← hHeis.1.2.1, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    have hab' : ((⁅a, b⁆ : ↥(Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
        ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈ Subgroup.zpowers (π ⟨d, hdL⟩) := by
      rw [hZ, ← Sec14.map_subtype_center_eq]
      exact Subgroup.mem_map_of_mem _ hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hab'
    have hcomm : π (⟨x, hSL hx⟩ * ⟨y, hSL hy⟩ * ⟨x, hSL hx⟩⁻¹ * ⟨y, hSL hy⟩⁻¹) =
        π (⟨d, hdL⟩ ^ k) := by
      rw [map_zpow, hk, map_mul, map_mul, map_mul, map_inv, map_inv, commutatorElement_def]
      rfl
    have hmem1 : (⟨x, hSL hx⟩ * ⟨y, hSL hy⟩ * ⟨x, hSL hx⟩⁻¹ * ⟨y, hSL hy⟩⁻¹ : ↥L) ∈
        (S' : Subgroup ↥L) :=
      mul_mem (mul_mem (mul_mem hxS hyS) (inv_mem hxS)) (inv_mem hyS)
    have heq := hinj hmem1 (zpow_mem (hmemS hdS) k) hcomm
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val heq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at this
    exact this.symm
  ·
    intro x hx hxc
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    have hxL := hSL hx
    have hc₁ : ∃ T : Sylow 3 ↥L, (⟨x, hxL⟩ : ↥L) ∈ (T : Subgroup ↥L) ∧
        (T : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨x, hxL⟩ : ↥L)} := by
      refine ⟨S', hmemS hx, fun y hy => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hxc y ⟨y, hy, rfl⟩).symm
    have := zpowers_eq_of_central_of_quot_j2 H.h415 H.quot hSp hx hdS hxL hdL hx1 H.ne_one hc₁
      ⟨S₀, hdS₀, hS₀d⟩
    rw [← this]
    exact Subgroup.mem_zpowers x
  ·
    intro X hXS hX9
    set X' := X.subgroupOf L with hX'
    have hX'S : X' ≤ (S' : Subgroup ↥L) := fun y hy => hmemS (hXS (Subgroup.mem_subgroupOf.mp hy))
    have hXb : X'.map π ≤ (Sb : Subgroup _) := by
      rw [hSb]
      exact Subgroup.map_mono hX'S
    have hXb9 : Nat.card (X'.map π) = 9 := by
      rw [card_map_eq_of_injOn π (hinj.mono hX'S), hX',
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hXS.trans hSL)).toEquiv, hX9]
    have hle := KFacts.KS14.j2_inf_centralizer_le_of_card_nine H.h415 H.quot Sb hXb hXb9
    obtain ⟨y, hy, hyd⟩ := hle hdZ
    have := hinj (hX'S hy) (hmemS hdS) hyd
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  ·
    intro x hx
    obtain ⟨k, hk⟩ := hSp ⟨x, hx⟩
    apply H.residual_le
    exact mem_residual_of_pow_three H.h415 H.quot hdL H.ne_one ⟨S₀, hdS₀, hS₀d⟩ (hSL hx) (hSd hx)
      (k := k) (by simpa using congrArg Subtype.val hk)

end Base

end CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
