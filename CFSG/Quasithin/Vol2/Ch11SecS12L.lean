module

public import CFSG.Quasithin.Vol2.Ch11SecS12B
public import CFSG.Quasithin.Vol2.Ch11SecSQuot

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.OperatorJH
open scoped commutatorElement

variable {G : Type} [Group G]

section Generic

theorem commutator_lt_of_isPGroup {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (B P : Subgroup H) (hBp : IsPGroup p B) (hPp : IsPGroup p P)
    (hPB : P ≤ Subgroup.normalizer (B : Set H)) (hBne : B ≠ ⊥) : ⁅B, P⁆ < B := by
  have hle : ⁅B, P⁆ ≤ B := (Subgroup.le_normalizer_iff_commutator_le_left).mp hPB
  refine lt_of_le_of_ne hle fun heq => ?_
  let S : Subgroup H := B ⊔ P
  have hBnormS : (B.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := B) (K := S) le_sup_left).2
      (sup_le Subgroup.le_normalizer hPB)
  have hnil : Group.IsNilpotent ↑S :=
    IsPGroup.isNilpotent (p := p) (IsPGroup.to_sup_of_normal_left' hBp hPp hPB)
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↑S)).mp hnil
  have hlcs : ∀ n : ℕ, B.subgroupOf S ≤ (⊤ : Subgroup ↑S).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simp [Subgroup.lowerCentralSeries_zero]
    | succ n ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      have hcomm : ⁅B.subgroupOf S, P.subgroupOf S⁆ = B.subgroupOf S := by
        apply (Subgroup.map_subtype_inj (H := S)).mp
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
          Subgroup.map_subgroupOf_eq_of_le le_sup_right, heq]
      rw [← hcomm]
      exact Subgroup.commutator_mono ih le_top
  have hbot : B.subgroupOf S = ⊥ := bot_unique ((hlcs n).trans_eq hn)
  apply hBne
  rw [← Subgroup.map_subgroupOf_eq_of_le (le_sup_left : B ≤ S), hbot, Subgroup.map_bot]

theorem commutator_le_of_isPGroup [Finite G] {Γ C S P : Subgroup G} (hP : IsPGroup 2 P)
    (hS : IsPGroup 2 S) (hCS : C < S) (hPS : P ≤ Subgroup.normalizer (S : Set G))
    (hPC : P ≤ Subgroup.normalizer (C : Set G)) (hSC : S ≤ Subgroup.normalizer (C : Set G))
    (hΓP : Γ ≤ Subgroup.normalizer (P : Set G)) (hΓS : Γ ≤ Subgroup.normalizer (S : Set G))
    (hΓC : Γ ≤ Subgroup.normalizer (C : Set G))
    (hsimple : ∀ J : Subgroup G, C ≤ J → J ≤ S → Γ ≤ Subgroup.normalizer (J : Set G) →
      J = C ∨ J = S) : ⁅S, P⁆ ≤ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSPS : ⁅S, P⁆ ≤ S := (Subgroup.le_normalizer_iff_commutator_le_left).mp hPS
  have hΓSP : Γ ≤ Subgroup.normalizer ((⁅S, P⁆ : Subgroup G) : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_mem_of fun z hz => ?_
    have hle : ⁅S, P⁆ ≤ ⁅S, P⁆.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro s hs p hp
      show g * ⁅s, p⁆ * g⁻¹ ∈ ⁅S, P⁆
      have e : g * ⁅s, p⁆ * g⁻¹ = ⁅g * s * g⁻¹, g * p * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (hΓS hg) s).mp hs)
        ((Subgroup.mem_normalizer_iff.mp (hΓP hg) p).mp hp)
    exact hle hz
  rcases hsimple (⁅S, P⁆ ⊔ C) le_sup_right (sup_le hSPS hCS.le)
      (fun g hg => mem_normalizer_sup_of (hΓSP hg) (hΓC hg)) with hJ | hJ
  · exact hJ ▸ le_sup_left
  exfalso
  set N := Subgroup.normalizer (C : Set G) with hN
  have hSN : S ≤ N := hSC
  have hPN : P ≤ N := hPC
  let π := QuotientGroup.mk' (C.subgroupOf N)
  have hSb : IsPGroup 2 ↥((S.subgroupOf N).map π) :=
    (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm).map π
  have hPb : IsPGroup 2 ↥((P.subgroupOf N).map π) :=
    (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm).map π
  have hPSb : (P.subgroupOf N).map π ≤
      Subgroup.normalizer (((S.subgroupOf N).map π : Subgroup _) : Set _) := by
    have hle : P.subgroupOf N ≤ Subgroup.normalizer (S.subgroupOf N : Set ↥N) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro a
      have hb' := (Subgroup.mem_normalizer_iff.mp (hPS hb)) a
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hb'
    exact (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map _)
  obtain ⟨s, hsS, hsC⟩ := Set.not_subset.mp fun h => hCS.not_ge h
  have hSbne : (S.subgroupOf N).map π ≠ ⊥ := by
    intro hb
    have h1 : π ⟨s, hSN hsS⟩ ∈ (S.subgroupOf N).map π := ⟨⟨s, hSN hsS⟩, hsS, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact hsC h1
  have hlt := commutator_lt_of_isPGroup _ _ hSb hPb hPSb hSbne
  apply hlt.not_ge
  have hcomm : ⁅S.subgroupOf N, P.subgroupOf N⁆ = (⁅S, P⁆ : Subgroup G).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSN,
      Subgroup.map_subgroupOf_eq_of_le hPN, Subgroup.map_subgroupOf_eq_of_le (hSPS.trans hSN)]
  rw [← Subgroup.map_commutator, hcomm]
  rintro _ ⟨y, hy, rfl⟩
  have hyJ : (y : G) ∈ ⁅S, P⁆ ⊔ C := by
    rw [hJ]
    exact Subgroup.mem_subgroupOf.mp hy
  have hnorm : ⁅S, P⁆ ≤ Subgroup.normalizer (C : Set G) := hSPS.trans hSC
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hyJ
  obtain ⟨a, ha, c, hc, hac⟩ := hyJ
  have haN : a ∈ N := hSN (hSPS ha)
  refine ⟨⟨a, haN⟩, ha, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  have e : ((⟨a, haN⟩ : ↥N)⁻¹ * y : ↥N) = (c : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hac]
    group
  rw [e]
  exact hc

theorem exists_isLabSeries_sub [Finite G] {Y K : Subgroup G} {x : G} {F : Type} [Field F]
    {α₀ : ↥K →* ↥(StatedSL 2 F)} (hKY : K ≤ Y) (hxY : x ∈ Y) (hα : Function.Surjective α₀)
    {V₁ U C S : Subgroup G} {l₀ : List (Subgroup G × Option F)}
    (hl₀ : IsLabSeries Y K x α₀ V₁ l₀ U) (hUab : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ V₁)
    (hV₁C : V₁ ≤ C) (hCS : C ≤ S) (hSU : S ≤ U) (hYC : Y ≤ Subgroup.normalizer (C : Set G))
    (hYS : Y ≤ Subgroup.normalizer (S : Set G)) :
    ∃ l : List (Subgroup G × Option F), IsLabSeries Y K x α₀ C l S := by
  have hJH := operatorJHNatEig_holds G Y K x 2 F α₀ hKY hxY le_rfl hα
  have hCU : C ≤ U := hCS.trans hSU
  obtain ⟨la, lb, -, hlb, -⟩ := (hJH V₁ U l₀ hl₀).2 C hV₁C hCU
    (le_normalizer_of_comm le_rfl (hV₁C.trans hCU) hCU hUab)
    (le_normalizer_of_comm hV₁C hCU le_rfl hUab) hYC
  obtain ⟨lb', -, hlb', -, -⟩ := (hJH C U lb hlb).2 S hCS hSU
    (le_normalizer_of_comm hV₁C hCU hSU hUab)
    (le_normalizer_of_comm (hV₁C.trans hCS) hSU le_rfl hUab) hYS
  exact ⟨lb', hlb'⟩

theorem eq_one_of_mem_of_isPGroup {X₁ P : Subgroup G} (hX₁ : Nat.card ↥X₁ = 3)
    (hP : IsPGroup 2 ↥P) {x : G} (hx : x ∈ X₁) (hxP : x ∈ P) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : orderOf x ∣ 3 := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥X₁)
    rwa [hX₁, Subgroup.orderOf_mk] at this
  have h4 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h5 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)) h3 h4
  exact orderOf_eq_one_iff.mp h5

end Generic

section PGL

variable {Γ : Subgroup G} {F : Type} [Field F]

@[expose] noncomputable def alphaPGL
    (e : ↥Γ ⧸ CFSG.pCore 2 ↥Γ ≃* (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))) :
    ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Γ))

variable (e : ↥Γ ⧸ CFSG.pCore 2 ↥Γ ≃* (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)))

theorem alphaPGL_surjective : Function.Surjective (alphaPGL e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem alphaPGL_eq_one_iff (γ : ↥Γ) : alphaPGL e γ = 1 ↔ (γ : G) ∈ pCoreOf 2 Γ := by
  rw [alphaPGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.injective,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, SecS.pCoreOf_two_eq_map]
  constructor
  · intro h
    exact ⟨γ, h, rfl⟩
  · rintro ⟨γ', h, hγ'⟩
    rwa [Subtype.ext hγ'] at h

theorem map_alphaPGL (B : Subgroup G) :
    (B.subgroupOf Γ).map (alphaPGL e) = (modO2Image Γ B).map e.toMonoidHom := by
  rw [modO2Image, Subgroup.map_map]
  rfl

theorem commutator_eq_map :
    commutator (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) =
      Subgroup.map e.toMonoidHom ⁅(⊤ : Subgroup (↥Γ ⧸ CFSG.pCore 2 ↥Γ)), ⊤⁆ := by
  rw [commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

end PGL

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
