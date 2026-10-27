module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCSelfNormZ2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.InnerSplit
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCT6

public section

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

section Field

variable {F : Type} [Field F] [Fintype F]

noncomputable def glEquivZ2 (hF : Fintype.card F = 2) :
    Matrix.GeneralLinearGroup (Fin 3) F ≃* G3 :=
  haveI : CharP F 2 := charP_of_card_eq_prime (p := 2) hF
  Units.mapEquiv (RingEquiv.mapMatrix (ZMod.ringEquiv F hF).symm).toMulEquiv

theorem card_gl3 (hF : Fintype.card F = 2) :
    Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) = 168 := by
  rw [Nat.card_congr (glEquivZ2 hF).toEquiv]
  exact CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.card_GL_three_two

theorem selfNormalizing_gl3 (hF : Fintype.card F = 2)
    (P : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)) (hP : Nat.card P = 8)
    {g : Matrix.GeneralLinearGroup (Fin 3) F} (h : ∀ x ∈ P, g * x * g⁻¹ ∈ P) : g ∈ P := by
  let φ := glEquivZ2 hF
  have hcard : Nat.card (P.map φ.toMonoidHom) = 8 := by
    exact (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).trans hP
  have key := selfNormalizing_of_card_eight (P.map φ.toMonoidHom) hcard (g := φ g) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨g * y * g⁻¹, h y hy, by simp⟩)
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp key
  have : y = g := φ.injective hyg
  exact this ▸ hy

end Field

section Lift

variable {G : Type} [Group G] [Finite G]

theorem pu_hself {L S : Subgroup G} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (hα : Function.Surjective α)
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L) :
    ∀ l ∈ L, (∀ p ∈ S ⊓ L, ∃ q ∈ S ⊓ L, ∃ n ∈ α.ker.map L.subtype, l * p * l⁻¹ = q * n) →
      ∃ q ∈ S ⊓ L, ∃ n ∈ α.ker.map L.subtype, l = q * n := by
  classical
  intro l hl hnorm
  let Γ := CFSG.Assembly.LowTwoRank.StatedSL 3 F
  let α' : ↥L →* Matrix.GeneralLinearGroup (Fin 3) F := Γ.subtype.comp α
  let P : Subgroup ↥L := (S ⊓ L).subgroupOf L
  let Q : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F) := P.map α'
  have hP2 : IsPGroup 2 ↥P :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨m, hm⟩ := hP2.exists_card_eq
  have hQdvd : Nat.card Q ∣ 2 ^ m := hm ▸ Subgroup.card_map_dvd P α'
  have hα' : Function.Surjective α' := by
    intro g
    have hg : g ∈ Γ := by
      show g ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 F
      rw [statedSL_eq_top_of_card_two hF]; trivial
    obtain ⟨l₀, hl₀⟩ := hα ⟨g, hg⟩
    exact ⟨l₀, by simp [α', hl₀]⟩
  have hodd : ¬ 2 ∣ Q.index := fun hd =>
    hsyl.2.2 (hd.trans (Subgroup.index_map_dvd P hα'))
  have hQ2 : Nat.card Q = 8 := by
    obtain ⟨k, hk, hkQ⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hQdvd
    have h168 : Nat.card Q * Q.index = 168 := by
      rw [Subgroup.card_mul_index, card_gl3 hF]
    have hpos : 0 < Q.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hkQ] at h168
    have hk7 : k < 8 := by
      by_contra hcon
      have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ k ≤ 2 ^ k * Q.index := Nat.le_mul_of_pos_right _ hpos
      omega
    interval_cases k <;> omega
  have hnormQ : ∀ x ∈ Q, α' ⟨l, hl⟩ * x * (α' ⟨l, hl⟩)⁻¹ ∈ Q := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    have hpS : (p : G) ∈ S ⊓ L := ⟨(Subgroup.mem_inf.mp hp).1, p.2⟩
    obtain ⟨q, hq, n, hn, hqn⟩ := hnorm p hpS
    obtain ⟨k, hk, hkn⟩ := Subgroup.mem_map.mp hn
    have hconj : (⟨l, hl⟩ : ↥L) * p * (⟨l, hl⟩ : ↥L)⁻¹ = (⟨q, (Subgroup.mem_inf.mp hq).2⟩ : ↥L) * k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [hqn, ← hkn]
      rfl
    refine Subgroup.mem_map.mpr ⟨⟨q, (Subgroup.mem_inf.mp hq).2⟩, ?_, ?_⟩
    · exact (Subgroup.mem_subgroupOf).mpr hq
    · rw [← map_mul, ← map_inv, ← map_mul, hconj, map_mul]
      have : α' k = 1 := by simp [α', MonoidHom.mem_ker.mp hk]
      rw [this, mul_one]
  have hmemQ := selfNormalizing_gl3 hF Q hQ2 hnormQ
  obtain ⟨p, hp, hpl⟩ := Subgroup.mem_map.mp hmemQ
  refine ⟨(p : G), ⟨(Subgroup.mem_inf.mp hp).1, p.2⟩, (p : G)⁻¹ * l, ?_, by group⟩
  refine Subgroup.mem_map.mpr ⟨p⁻¹ * ⟨l, hl⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  have : α' (p⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hpl, inv_mul_cancel]
  simpa [α'] using this

open CFSG.Open CFSG.LieType.BorelTits in
theorem pu_split_generic {L S U : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hα : IsModO2Surj L α) (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hSU : S ≤ Subgroup.normalizer (U : Set G))
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L) :
    ∀ s ∈ S, ∃ p ∈ S ⊓ L, ∃ c ∈ S, (∀ x ∈ L, ∃ m ∈ pCoreOf 2 L, c * x * c⁻¹ = x * m) ∧
      s = p * c := by
  have hN : α.ker.map L.subtype = pCoreOf 2 L := by
    rw [hα.2]; rfl
  have hself := pu_hself hF α hα.1 hsyl
  rw [hN] at hself
  refine CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.S_eq_mul_centralizer_mod_normal
    S L (pCoreOf 2 L) ?_ ?_ ?_ ?_ hself
  · intro x hx n hn
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hx) n).mp hn
  · intro s hs x hx
    exact (Subgroup.mem_normalizer_iff.mp (hSL hs) x).mp hx
  · intro s hs n hn
    exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 L (hSL hs)) n).mp hn
  · intro s hs
    obtain ⟨l', hl'⟩ := inner_of_natural_stated hF α hα.1 hnat (hSU hs)
    refine ⟨l', l'.2, fun x hx => ?_⟩
    have hsx : s * x * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hSL hs) x).mp hx
    have hy : (l' : G)⁻¹ * (s * x * s⁻¹) * l' ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem l'.2) hsx) l'.2
    have hα1 := hl' ⟨x, hx⟩ ⟨_, hy⟩ (by simp only; group)
    have hker : (⟨x, hx⟩ : ↥L)⁻¹ * ⟨_, hy⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα1, inv_mul_cancel]
    rw [hα.2] at hker
    have hm : x⁻¹ * ((l' : G)⁻¹ * (s * x * s⁻¹) * l') ∈ pCoreOf 2 L :=
      Subgroup.mem_map.mpr ⟨(⟨x, hx⟩ : ↥L)⁻¹ * ⟨_, hy⟩, hker, rfl⟩
    have hn : (l' : G) * (x⁻¹ * ((l' : G)⁻¹ * (s * x * s⁻¹) * l')) * (l' : G)⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L l'.2) _).mp hm
    exact ⟨_, hn, by group⟩

end Lift

section Setting

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.SBd7 CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

theorem pu_S_split {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L) :
    ∀ s ∈ Sgp153 T V₁, ∃ p ∈ Sgp153 T V₁ ⊓ L, ∃ c' ∈ Sgp153 T V₁,
      (∀ x ∈ L, ∃ m ∈ pCoreOf 2 L, c' * x * c'⁻¹ = x * m) ∧ s = p * c' := by
  obtain ⟨hLc, -, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.ctx.inH.1.1
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLle Subgroup.le_normalizer) inf_le_right
  obtain ⟨⟨n, F, _, _, α, hFc, hα, -, -, -, hnat, -, -, -⟩, -⟩ := h4
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  have hS1 : Sgp153 T V₁ ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ Sgp153 T V₁) : Set G) :=
    fun s hs => le_normalizer_pCoreOf 2 (L ⊔ Sgp153 T V₁) (Subgroup.mem_sup_right hs)
  have hSQ : Sgp153 T V₁ ≤ Subgroup.normalizer (c134Q (L ⊔ Sgp153 T V₁) L : Set G) :=
    MS93.le_normalizer_commutator_of hS1 hSL
  have hSZ : Sgp153 T V₁ ≤
      Subgroup.normalizer (centerOf (c134Q (L ⊔ Sgp153 T V₁) L) : Set G) := fun s hs =>
    mem_normalizer_inf (hSQ hs) (normalizer_le_normalizer_centralizer _ (hSQ hs))
  have hSU : Sgp153 T V₁ ≤
      Subgroup.normalizer (⁅centerOf (c134Q (L ⊔ Sgp153 T V₁) L), L⁆ : Subgroup G) :=
    MS93.le_normalizer_commutator_of hSZ hSL
  exact pu_split_generic hF α hα hnat hSL hSU hQsyl

end Setting

end Stellmacher.PU.L3YC

end CFSG.Quasithin
