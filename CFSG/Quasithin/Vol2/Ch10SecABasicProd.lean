module

public import CFSG.Quasithin.Vol2.Ch10SecABasicQuot

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_sup {A B X : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  fun x hx => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hx),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hx)]

theorem exists_proj {K K' O X : Subgroup G} (hKX : K ≤ X) (hK'X : K' ≤ X) (hOX : O ≤ X)
    (hXle : X ≤ K ⊔ (K' ⊔ O)) (hXN : X ≤ Subgroup.normalizer ((K' ⊔ O : Subgroup G) : Set G))
    (hinf : K ⊓ (K' ⊔ O) = pCoreOf 2 K) :
    ∃ φ : ↥X →* ↥K ⧸ CFSG.pCore 2 ↥K, Function.Surjective φ ∧
      φ.ker = (K' ⊔ O).subgroupOf X ∧
      (∀ (k : G) (hk : k ∈ K), φ ⟨k, hKX hk⟩ = ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)) ∧
      ∀ (k : G) (hk : k ∈ K'), φ ⟨k, hK'X hk⟩ = 1 := by
  have : ((K' ⊔ O).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hK'X hOX)).mpr hXN
  set N := (K' ⊔ O).subgroupOf X
  let q : ↥K →* ↥X ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hKX)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have hy : (y : G) ∈ ((K ⊔ (K' ⊔ O) : Subgroup G) : Set G) := hXle y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K (K' ⊔ O) (hKX.trans hXN)] at hy
    obtain ⟨k, hk, n, hn, hkn⟩ := hy
    refine ⟨⟨k, hk⟩, ?_⟩
    change ((Subgroup.inclusion hKX ⟨k, hk⟩ : ↥X) : ↥X ⧸ N) = (y : ↥X ⧸ N)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [← hkn] using hn
  have hker : q.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker, ← subgroupOf_pCoreOf, Subgroup.mem_subgroupOf, ← hinf]
    change ((Subgroup.inclusion hKX k : ↥X) : ↥X ⧸ N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  let e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥X ⧸ N :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have he : ∀ k : ↥K, e (k : ↥K ⧸ CFSG.pCore 2 ↥K) = q k := fun k => rfl
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' N), ?_, ?_, ?_, ?_⟩
  · exact e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  · ext x
    simp
  · intro k hk
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      QuotientGroup.mk'_apply, MulEquiv.symm_apply_eq, he]
    rfl
  · intro k hk
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff _).mpr (show _ ∈ N from Subgroup.mem_sup_left hk), map_one]

variable [Finite G] {T L I : Subgroup G}

theorem sup_pCoreOf_inf_eq
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    (CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L)) ⊓ (L ⊔ pCoreOf 2 (fsuL0 T L)) =
      pCoreOf 2 (fsuL0 T L) := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right le_sup_right)
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 (fsuL0 T L) : Set G) := fun _ hl =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (le_fsuL0 T L hl)
  have hx2 : x ∈ ((L ⊔ pCoreOf 2 (fsuL0 T L) : Subgroup G) : Set G) := hx.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ hLO] at hx2
  obtain ⟨l, hl, o, ho, rfl⟩ := hx2
  have hl' : l ∈ CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L) := by
    have := (CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L)).mul_mem hx.1
      (Subgroup.mem_sup_right ((pCoreOf 2 (fsuL0 T L)).inv_mem ho))
    simpa using this
  have hlO : l ∈ pCoreOf 2 L := by
    rw [← inf_sup_pCoreOf_fsuL0 h37 h38 hyp ht htn]
    exact ⟨hl, hl'⟩
  exact (pCoreOf 2 (fsuL0 T L)).mul_mem
    (sup_pCoreOf_le hyp.fsu.maximal.1 ht (Subgroup.mem_sup_left hlO)) ho

theorem exists_fsuL0_prod
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ∃ φ : ↥(fsuL0 T L) →* (↥L ⧸ CFSG.pCore 2 ↥L) ×
        (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)),
      Function.Surjective φ ∧ φ.ker = (pCoreOf 2 (fsuL0 T L)).subgroupOf (fsuL0 T L) ∧
      (∀ (l : G) (hl : l ∈ L),
        φ ⟨l, le_fsuL0 T L hl⟩ = (((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L), 1)) ∧
      ∀ (l : G) (hl : l ∈ CFSG.conjugate L t), φ ⟨l, conjugate_le_fsuL0 ht hl⟩ =
        (1, ((⟨l, hl⟩ : ↥(CFSG.conjugate L t)) :
          ↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t))) := by
  have hloc := hyp.fsu.maximal.1
  have hOX : pCoreOf 2 (fsuL0 T L) ≤ fsuL0 T L := Subgroup.map_subtype_le _
  have hL0 := fsuL0_eq_sup h37 h38 hyp ht htn
  have hNO : fsuL0 T L ≤ Subgroup.normalizer (pCoreOf 2 (fsuL0 T L) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  obtain ⟨φ₁, hs₁, hk₁, hL₁, hLt₁⟩ := exists_proj (le_fsuL0 T L) (conjugate_le_fsuL0 ht) hOX
    (by rw [hL0]; exact sup_le le_sup_left (le_sup_left.trans le_sup_right))
    (le_normalizer_sup (fsuL0_le_normalizer_conjugate hloc (le_fsuM T L ht)) hNO)
    (inf_sup_pCoreOf_fsuL0 h37 h38 hyp ht htn)
  obtain ⟨φ₂, hs₂, hk₂, hLt₂, hL₂⟩ := exists_proj (conjugate_le_fsuL0 ht) (le_fsuL0 T L) hOX
    (by rw [hL0]; exact sup_le (le_sup_left.trans le_sup_right) le_sup_left)
    (le_normalizer_sup (fsuL0_le_normalizer hloc) hNO)
    (conjugate_inf_sup_pCoreOf_fsuL0 h37 h38 hyp ht htn)
  refine ⟨φ₁.prod φ₂, ?_, ?_, fun l hl => ?_, fun l hl => ?_⟩
  · rintro ⟨a, b⟩
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨⟨l', hl'⟩, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨⟨l, le_fsuL0 T L hl⟩ * ⟨l', conjugate_le_fsuL0 ht hl'⟩, ?_⟩
    rw [map_mul, MonoidHom.prod_apply, MonoidHom.prod_apply, hL₁ l hl, hL₂ l hl, hLt₁ l' hl',
      hLt₂ l' hl']
    simp
  · rw [MonoidHom.ker_prod, hk₁, hk₂]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [← Subgroup.mem_inf, sup_pCoreOf_inf_eq h37 h38 hyp ht htn]
  · rw [MonoidHom.prod_apply, hL₁ l hl, hL₂ l hl]
  · rw [MonoidHom.prod_apply, hLt₁ l hl, hLt₂ l hl]

theorem mem_pCoreOf_fsuL0_of_commutator
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {x : G} (hx : x ∈ fsuL0 T L)
    (h : ∀ y ∈ fsuL0 T L, ⁅x, y⁆ ∈ pCoreOf 2 (fsuL0 T L)) : x ∈ pCoreOf 2 (fsuL0 T L) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨φ, hs, hk, -, -⟩ := exists_fsuL0_prod h37 h38 hyp ht htn
  have hcen : φ ⟨x, hx⟩ ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hs g
    have h1 : φ ⁅(⟨x, hx⟩ : ↥(fsuL0 T L)), y⁆ = 1 := by
      rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf]
      exact h y y.2
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [Subgroup.center_prod, center_quot_eq_bot h37 h38 hyp,
    center_quot_conjugate_eq_bot h37 h38 hyp ht htn, Subgroup.bot_prod_bot, Subgroup.mem_bot,
    ← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf] at hcen
  exact hcen

end CFSG.Quasithin.Vol2.Ch10.SecA
