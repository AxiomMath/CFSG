module

public import CFSG.LocalAnalysis.SteinbergBVGL3NaturalSelfExtension
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Sub
import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Mult
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Milestones.ASVolI.B4Ext.GL4
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open Module CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open CFSG.QuasithinUnique.Setup.Offender (commGL trivMod mem_trivMod)
open scoped Matrix

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {𝓛 : Subgroup (E ≃ₗ[ZMod 2] E)}

theorem card_eq_of_mulEquiv (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛) :
    Nat.card ↥𝓛 = 168 := by
  rw [← Nat.card_congr eV.toEquiv, natCard_linearEquiv (Module.finrank_fin_fun (ZMod 2))]

theorem exists_closure_conj_eq (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛)
    {a : E ≃ₗ[ZMod 2] E} (ha : a ∈ 𝓛) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    ∃ p ∈ 𝓛, Subgroup.closure ({a, p * a * p⁻¹, p * (p * a * p⁻¹) * p⁻¹} :
      Set (E ≃ₗ[ZMod 2] E)) = 𝓛 := by
  set f : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) →* (E ≃ₗ[ZMod 2] E) :=
    𝓛.subtype.comp eV.toMonoidHom with hf
  have hfa : f (eV.symm ⟨a, ha⟩) = a := by simp [f]
  have ha'2 : eV.symm ⟨a, ha⟩ * eV.symm ⟨a, ha⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨a, ha⟩ : ↥𝓛) * ⟨a, ha⟩ = 1 := Subtype.ext ha2
    rw [h1, map_one]
  have ha'1 : eV.symm ⟨a, ha⟩ ≠ 1 := fun h => ha1 (by
    have h1 := congrArg f h
    rwa [hfa, map_one] at h1)
  obtain ⟨p', hp'⟩ := CFSG.LocalAnalysis.SteinbergBV.ThreeInvolutions.exists_closure_conj_eq_top
    (Module.finrank_fin_fun (ZMod 2)) ha'2 ha'1
  refine ⟨f p', (eV p').2, ?_⟩
  have hrange : f.range = 𝓛 := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (eV y).2
    · intro hx
      exact ⟨eV.symm ⟨x, hx⟩, by simp [f]⟩
  rw [← hrange, MonoidHom.range_eq_map, ← hp', MonoidHom.map_closure, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton]
  simp only [map_mul, map_inv, hfa]

theorem finrank_range_conj_le [FiniteDimensional (ZMod 2) E] (q t : E ≃ₗ[ZMod 2] E) :
    finrank (ZMod 2) (LinearMap.range (((q * t * q⁻¹ : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) -
      LinearMap.id)) ≤ finrank (ZMod 2) (LinearMap.range ((t : E →ₗ[ZMod 2] E) - LinearMap.id)) := by
  have hle : LinearMap.range (((q * t * q⁻¹ : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id) ≤
      (LinearMap.range ((t : E →ₗ[ZMod 2] E) - LinearMap.id)).map (q : E →ₗ[ZMod 2] E) := by
    rintro _ ⟨e, rfl⟩
    refine ⟨t (q.symm e) - q.symm e, ⟨q.symm e, rfl⟩, ?_⟩
    show q (t (q.symm e) - q.symm e) = q (t (q.symm e)) - e
    rw [map_sub, LinearEquiv.apply_symm_apply]
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

theorem finrank_le_three_mul_twisted [FiniteDimensional (ZMod 2) E] [IsSimpleGroup ↥𝓛]
    (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛) (hE : commGL 𝓛 ⊤ = ⊤)
    {a c : E ≃ₗ[ZMod 2] E} (ha : a ∈ 𝓛) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hc : ∀ y ∈ 𝓛, c * y = y * c) (hc2 : c * c = 1) :
    finrank (ZMod 2) E ≤
      3 * finrank (ZMod 2) (LinearMap.range (((a * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) -
        LinearMap.id)) := by
  obtain ⟨p, hp, hcl⟩ := exists_closure_conj_eq eV ha ha2 ha1
  set a₂ := p * a * p⁻¹ with ha₂def
  set a₃ := p * a₂ * p⁻¹ with ha₃def
  have ha₂ : a₂ ∈ 𝓛 := mul_mem (mul_mem hp ha) (inv_mem hp)
  have ha₃ : a₃ ∈ 𝓛 := mul_mem (mul_mem hp ha₂) (inv_mem hp)
  have hinv2 : ∀ q : E ≃ₗ[ZMod 2] E, q * q = 1 → p * q * p⁻¹ * (p * q * p⁻¹) = 1 := fun q hq => by
    calc p * q * p⁻¹ * (p * q * p⁻¹) = p * (q * q) * p⁻¹ := by group
      _ = 1 := by rw [hq]; group
  have ha₂2 : a₂ * a₂ = 1 := hinv2 a ha2
  have ha₃2 : a₃ * a₃ = 1 := hinv2 a₂ ha₂2
  obtain ⟨R, hR⟩ : ∃ R : Submodule (ZMod 2) E,
      R = LinearMap.range (((a * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id) ⊔
        LinearMap.range (((a₂ * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id) ⊔
        LinearMap.range (((a₃ * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id) := ⟨_, rfl⟩
  have hmemT : ∀ t : E ≃ₗ[ZMod 2] E,
      LinearMap.range ((t : E →ₗ[ZMod 2] E) - LinearMap.id) ≤ R → t ∈ trivMod R :=
    fun t ht => mem_trivMod.2 fun w => ht ⟨w, rfl⟩
  set D := Subgroup.closure ({a * c, a₂ * c, a₃ * c} : Set (E ≃ₗ[ZMod 2] E)) with hD
  have hDT : D ≤ trivMod R := by
    rw [hD, Subgroup.closure_le]
    rintro t (rfl | rfl | rfl)
    · exact hmemT _ (hR ▸ le_sup_left.trans le_sup_left)
    · exact hmemT _ (hR ▸ le_sup_right.trans le_sup_left)
    · exact hmemT _ (hR ▸ le_sup_right)
  set K := D ⊓ 𝓛 with hK
  have hconj : ∀ q ∈ ({a, a₂, a₃} : Set (E ≃ₗ[ZMod 2] E)), ∀ k ∈ K, q * k * q⁻¹ ∈ K := by
    intro q hq k hk
    obtain ⟨hkD, hk𝓛⟩ := Subgroup.mem_inf.1 hk
    have hq𝓛 : q ∈ 𝓛 := by rcases hq with rfl | rfl | rfl <;> assumption
    have hqc : q * c ∈ D := Subgroup.subset_closure (by rcases hq with rfl | rfl | rfl <;> simp)
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hq𝓛 hk𝓛) (inv_mem hq𝓛)⟩
    have hck : c * k = k * c := hc k hk𝓛
    have e1 : q * k * q⁻¹ = q * c * k * (q * c)⁻¹ := by
      calc q * k * q⁻¹ = q * (k * c) * c⁻¹ * q⁻¹ := by group
        _ = q * (c * k) * c⁻¹ * q⁻¹ := by rw [hck]
        _ = q * c * k * (q * c)⁻¹ := by group
    rw [e1]
    exact mul_mem (mul_mem hqc hkD) (inv_mem hqc)
  have hnorm : 𝓛 ≤ Subgroup.normalizer (K : Set (E ≃ₗ[ZMod 2] E)) := by
    rw [← hcl, Subgroup.closure_le]
    intro q hq
    have hq2 : q * q = 1 := by rcases hq with rfl | rfl | rfl <;> assumption
    have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hconj q hq k, fun h => ?_⟩
    have h1 := hconj q hq _ h
    have e2 : q * (q * k * q⁻¹) * q⁻¹ = k := by
      rw [hqi]
      calc q * (q * k * q) * q = q * q * k * (q * q) := by group
        _ = k := by rw [hq2]; group
    rwa [e2] at h1
  haveI hKn : (K.subgroupOf 𝓛).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := (Subgroup.mem_normalizer_iff.1 (hnorm g.2) n).1 hn
    simpa using h1⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf 𝓛) with hbot | htop
  · exfalso
    have hmem : a * a₂ ∈ K := by
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem ha ha₂⟩
      have e3 : a * a₂ = a * c * (a₂ * c) := by
        have hca : c * a₂ = a₂ * c := hc a₂ ha₂
        calc a * a₂ = a * a₂ * (c * c) := by rw [hc2, mul_one]
          _ = a * (a₂ * c) * c := by group
          _ = a * (c * a₂) * c := by rw [hca]
          _ = a * c * (a₂ * c) := by group
      rw [e3]
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have h1 : (⟨a * a₂, (Subgroup.mem_inf.1 hmem).2⟩ : ↥𝓛) ∈ K.subgroupOf 𝓛 :=
      Subgroup.mem_subgroupOf.2 hmem
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : a * a₂ = 1 := congrArg Subtype.val h1
    have h3 : a₂ = a := by
      calc a₂ = a * (a * a₂) := by rw [← mul_assoc, ha2, one_mul]
        _ = a := by rw [h2, mul_one]
    have h4 : a₃ = a := by rw [ha₃def, h3, ← ha₂def, h3]
    have hset : ({a, a₂, a₃} : Set (E ≃ₗ[ZMod 2] E)) = {a} := by rw [h3, h4]; simp
    rw [hset, ← Subgroup.zpowers_eq_closure] at hcl
    have h5 : Nat.card ↥(Subgroup.zpowers a) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact ha2)
    rw [hcl, card_eq_of_mulEquiv eV] at h5
    omega
  · have hL : 𝓛 ≤ trivMod R := by
      intro y hy
      have h1 : (⟨y, hy⟩ : ↥𝓛) ∈ K.subgroupOf 𝓛 := by rw [htop]; exact Subgroup.mem_top _
      exact hDT (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h1)).1
    have hER : (⊤ : Submodule (ZMod 2) E) ≤ R := by
      rw [← hE]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, u, -, rfl⟩
      exact mem_trivMod.1 (hL hy) u
    have hcp : c * p⁻¹ = p⁻¹ * c := hc _ (inv_mem hp)
    have e4 : a₂ * c = p * (a * c) * p⁻¹ := by
      calc a₂ * c = p * a * (p⁻¹ * c) := by rw [ha₂def]; group
        _ = p * a * (c * p⁻¹) := by rw [hcp]
        _ = p * (a * c) * p⁻¹ := by group
    have e5 : a₃ * c = p * (a₂ * c) * p⁻¹ := by
      calc a₃ * c = p * a₂ * (p⁻¹ * c) := by rw [ha₃def]; group
        _ = p * a₂ * (c * p⁻¹) := by rw [hcp]
        _ = p * (a₂ * c) * p⁻¹ := by group
    have h1 := Submodule.finrank_mono hER
    rw [finrank_top, hR] at h1
    have h2 := Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range (((a * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id) ⊔
        LinearMap.range (((a₂ * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id))
      (LinearMap.range (((a₃ * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id))
    have h3 := Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range (((a * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id))
      (LinearMap.range (((a₂ * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id))
    have h4 := finrank_range_conj_le p (a * c)
    have h5 := finrank_range_conj_le p (a₂ * c)
    rw [← e4] at h4
    rw [← e5] at h5
    omega

theorem inf_ker_mul_eq_bot {X' : Submodule (ZMod 2) E} {a c : E ≃ₗ[ZMod 2] E}
    (hX' : ∀ x ∈ X', a x ∈ X') (hac : a * c = c * a) (hc2 : c * c = 1)
    (hX'c : X' ⊓ LinearMap.ker ((c : E →ₗ[ZMod 2] E) - LinearMap.id) = ⊥) :
    X' ⊓ LinearMap.ker (((a * c : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) - LinearMap.id) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv'
  obtain ⟨hv, hvk⟩ := Submodule.mem_inf.1 hv'
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hvk
  have hacv : a (c v) = v := hvk
  have hw : c (c v - v) = c v - v := CFSG.ASVolI.burnsideB49x_gl_apply_sub hc2 v
  have hcaw : c (a (c v - v)) = a (c v - v) := by
    rw [← CFSG.ASVolI.burnsideB49x_gl_apply_comm hac, hw]
  have h1 : a v - v ∈ X' := Submodule.sub_mem _ (hX' v hv) hv
  have h2 : a v - v = -(a (c v - v)) := by
    rw [map_sub, hacv]
    abel
  have h3 : a (c v - v) ∈ X' ⊓ LinearMap.ker ((c : E →ₗ[ZMod 2] E) - LinearMap.id) := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have h4 := X'.neg_mem h1
      rwa [h2, neg_neg] at h4
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact hcaw
  rw [hX'c, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at h3
  have h5 : v ∈ X' ⊓ LinearMap.ker ((c : E →ₗ[ZMod 2] E) - LinearMap.id) := Submodule.mem_inf.2 ⟨hv, by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    exact h3⟩
  rwa [hX'c] at h5

@[expose] noncomputable def resSub (𝓛 : Subgroup (E ≃ₗ[ZMod 2] E)) (X : Submodule (ZMod 2) E)
    (hX : ∀ y ∈ 𝓛, ∀ x ∈ X, y x ∈ X) : ↥𝓛 →* (X ≃ₗ[ZMod 2] X) :=
  CFSG.QuasithinUnique.Setup.Family.subRep 𝓛.subtype X fun y x hx => hX y y.2 x hx

theorem resSub_apply {X : Submodule (ZMod 2) E} (hX : ∀ y ∈ 𝓛, ∀ x ∈ X, y x ∈ X) (y : ↥𝓛) (x : X) :
    ((resSub 𝓛 X hX y x : X) : E) = (y : E ≃ₗ[ZMod 2] E) x :=
  rfl

theorem injective_resSub {X : Submodule (ZMod 2) E} (hX : ∀ y ∈ 𝓛, ∀ x ∈ X, y x ∈ X)
    (hfaith : ∀ y ∈ 𝓛, (∀ x ∈ X, y x = x) → y = 1) : Function.Injective (resSub 𝓛 X hX) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine hfaith y y.2 fun x hx => ?_
  exact congrArg (fun f : X ≃ₗ[ZMod 2] X => ((f ⟨x, hx⟩ : X) : E)) hy

theorem bijective_resSub [Finite E] (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛)
    {X : Submodule (ZMod 2) E} (hX : ∀ y ∈ 𝓛, ∀ x ∈ X, y x ∈ X) (hX3 : finrank (ZMod 2) X = 3)
    (hfaith : ∀ y ∈ 𝓛, (∀ x ∈ X, y x = x) → y = 1) : Function.Bijective (resSub 𝓛 X hX) :=
  (injective_resSub hX hfaith).bijective_of_nat_card_le
    (by rw [natCard_linearEquiv hX3, card_eq_of_mulEquiv eV])

theorem eq_zero_or_eq_id_of_commute_resSub [Finite E]
    (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛)
    {X : Submodule (ZMod 2) E} (hX : ∀ y ∈ 𝓛, ∀ x ∈ X, y x ∈ X) (hX3 : finrank (ZMod 2) X = 3)
    (hfaith : ∀ y ∈ 𝓛, (∀ x ∈ X, y x = x) → y = 1) {h : X →ₗ[ZMod 2] X}
    (hh : ∀ (y : ↥𝓛) (x : X), h (resSub 𝓛 X hX y x) = resSub 𝓛 X hX y (h x)) :
    h = 0 ∨ h = LinearMap.id := by
  haveI : Module.Finite (ZMod 2) X := Module.Finite.of_finite
  refine CFSG.Quasithin.H13.Mult.eq_zero_or_eq_id_of_commute (by omega) fun τ x => ?_
  obtain ⟨y, rfl⟩ := (bijective_resSub eV hX hX3 hfaith).2 τ
  exact hh y x

theorem centralizer_structure [FiniteDimensional (ZMod 2) E] [IsSimpleGroup ↥𝓛]
    (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛) (hE : commGL 𝓛 ⊤ = ⊤)
    (hdim : finrank (ZMod 2) E ≤ 6) {c : E ≃ₗ[ZMod 2] E} (hc : ∀ y ∈ 𝓛, c * y = y * c)
    (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    finrank (ZMod 2) E = 6 ∧
      LinearMap.range ((c : E →ₗ[ZMod 2] E) - LinearMap.id) =
        LinearMap.ker ((c : E →ₗ[ZMod 2] E) - LinearMap.id) ∧
      finrank (ZMod 2) (LinearMap.ker ((c : E →ₗ[ZMod 2] E) - LinearMap.id)) = 3 ∧
      (∀ y ∈ 𝓛, (∀ x ∈ LinearMap.ker ((c : E →ₗ[ZMod 2] E) - LinearMap.id), y x = x) → y = 1) ∧
      ∃ X' : Submodule (ZMod 2) E, (∀ y ∈ 𝓛, ∀ x ∈ X', y x ∈ X') ∧
        IsCompl (LinearMap.ker ((c : E →ₗ[ZMod 2] E) - LinearMap.id)) X' := by
  classical
  haveI : Finite E := Module.finite_of_finite (ZMod 2)
  set N : E →ₗ[ZMod 2] E := (c : E →ₗ[ZMod 2] E) - LinearMap.id with hN
  have hNapp : ∀ v, N v = c v - v := fun v => rfl
  have hNN : ∀ v, N (N v) = 0 := fun v => by
    rw [hNapp, hNapp, CFSG.ASVolI.burnsideB49x_gl_apply_sub hc2, sub_self]
  have hNy : ∀ y ∈ 𝓛, ∀ v, N (y v) = y (N v) := fun y hy v => by
    rw [hNapp, hNapp, map_sub, CFSG.ASVolI.burnsideB49x_gl_apply_comm (hc y hy)]
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    exact hNN v
  have hXinv : ∀ y ∈ 𝓛, ∀ x ∈ LinearMap.range N, y x ∈ LinearMap.range N := by
    rintro y hy _ ⟨v, rfl⟩
    exact ⟨y v, hNy y hy v⟩
  have hKinv : ∀ y ∈ 𝓛, ∀ x ∈ LinearMap.ker N, y x ∈ LinearMap.ker N := by
    intro y hy x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hNy y hy, hx, map_zero]
  have hfaithX : ∀ y ∈ 𝓛, (∀ x ∈ LinearMap.range N, y x = x) → y = 1 := by
    have hinj : Function.Injective (resSub 𝓛 (LinearMap.range N) hXinv) := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (resSub 𝓛 (LinearMap.range N) hXinv).ker with
        h | h
      · exact (MonoidHom.ker_eq_bot_iff _).1 h
      · exfalso
        apply hc1
        have htriv : ∀ y ∈ 𝓛, ∀ v, y (N v) = N v := fun y hy v => by
          have h1 : (⟨y, hy⟩ : ↥𝓛) ∈ (resSub 𝓛 (LinearMap.range N) hXinv).ker := by
            rw [h]
            exact Subgroup.mem_top _
          exact congrArg (fun f : LinearMap.range N ≃ₗ[ZMod 2] LinearMap.range N =>
            ((f ⟨N v, v, rfl⟩ : LinearMap.range N) : E)) (MonoidHom.mem_ker.1 h1)
        have hker : ∀ v, N v = 0 := by
          intro v
          have hv : v ∈ commGL 𝓛 ⊤ := by
            rw [hE]
            exact Submodule.mem_top
          refine Submodule.span_induction (p := fun w _ => N w = 0) ?_ ?_ ?_ ?_ hv
          · rintro _ ⟨y, hy, u, -, rfl⟩
            show N (y u - u) = 0
            rw [map_sub, hNy y hy, htriv y hy, sub_self]
          · exact map_zero N
          · intro x z _ _ hx hz
            rw [map_add, hx, hz, add_zero]
          · intro r x _ hx
            rw [map_smul, hx, smul_zero]
        refine LinearEquiv.ext fun v => ?_
        have h1 := hker v
        rw [hNapp, sub_eq_zero] at h1
        exact h1
    intro y hy hfix
    have h1 : resSub 𝓛 (LinearMap.range N) hXinv ⟨y, hy⟩ = 1 :=
      LinearEquiv.ext fun x => Subtype.ext (hfix x x.2)
    exact congrArg Subtype.val (hinj (h1.trans (map_one _).symm))
  have hX3 : 3 ≤ finrank (ZMod 2) (LinearMap.range N) := by
    by_contra hlt
    push Not at hlt
    haveI : Finite (LinearMap.range N →ₗ[ZMod 2] LinearMap.range N) := Module.finite_of_finite (ZMod 2)
    have h1 : Nat.card ↥𝓛 ≤ Nat.card (LinearMap.range N →ₗ[ZMod 2] LinearMap.range N) :=
      Nat.card_le_card_of_injective _
        (LinearEquiv.toLinearMap_injective.comp (injective_resSub hXinv hfaithX))
    rw [card_eq_of_mulEquiv eV, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      Module.finrank_linearMap] at h1
    have hd2 : finrank (ZMod 2) (LinearMap.range N) ≤ 2 := by omega
    have h2 : 2 ^ (finrank (ZMod 2) (LinearMap.range N) * finrank (ZMod 2) (LinearMap.range N)) ≤
        2 ^ (2 * 2) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hd2 hd2)
    have h3 : 168 ≤ 2 ^ (2 * 2) := h1.trans h2
    norm_num at h3
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  have hmono := Submodule.finrank_mono hle
  have hK3 : finrank (ZMod 2) (LinearMap.ker N) = 3 := by omega
  have hE6 : finrank (ZMod 2) E = 6 := by omega
  have hXK : LinearMap.range N = LinearMap.ker N := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hfaithK : ∀ y ∈ 𝓛, (∀ x ∈ LinearMap.ker N, y x = x) → y = 1 := fun y hy h =>
    hfaithX y hy fun x hx => h x (hle hx)
  let β : Module.Basis (Fin 3) (ZMod 2) (LinearMap.ker N) :=
    Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.ker N) hK3
  set σ := resSub 𝓛 (LinearMap.ker N) hKinv with hσ
  set θ : ↥𝓛 →* GL (Fin 3) (ZMod 2) := (FixedCodim.toGL β).comp σ with hθ
  have hθbij : Function.Bijective θ :=
    ((FixedCodim.toGL_injective β).comp (injective_resSub hKinv hfaithK)).bijective_of_nat_card_le
      (by rw [FixedCodim.card_GL3, card_eq_of_mulEquiv eV])
  set e₁ := MulEquiv.ofBijective θ hθbij with he₁
  let ρ₁ : Representation (ZMod 2) (GL (Fin 3) (ZMod 2)) E :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (𝓛.subtype.comp e₁.symm.toMonoidHom)
  have hρ₁ : ∀ g v, ρ₁ g v = ((e₁.symm g : ↥𝓛) : E ≃ₗ[ZMod 2] E) v := fun _ _ => rfl
  have hkey : ∀ (g : GL (Fin 3) (ZMod 2)) (w : LinearMap.ker N),
      β.equivFun (σ (e₁.symm g) w) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ β.equivFun w := by
    intro g w
    have h1 : FixedCodim.toGL β (σ (e₁.symm g)) = g := e₁.apply_symm_apply g
    rw [FixedCodim.equivFun_apply_toGL, h1]
  have hNK : ∀ v, N v ∈ LinearMap.ker N := fun v => hle ⟨v, rfl⟩
  let i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] E := (LinearMap.ker N).subtype ∘ₗ β.equivFun.symm.toLinearMap
  let π : E →ₗ[ZMod 2] (Fin 3 → ZMod 2) := β.equivFun.toLinearMap ∘ₗ N.codRestrict (LinearMap.ker N) hNK
  have hπapp : ∀ v, π v = β.equivFun (N.codRestrict (LinearMap.ker N) hNK v) := fun _ => rfl
  have hi : ∀ (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
      i ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = ρ₁ g (i v) := by
    intro g v
    have h1 : β.equivFun.symm ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) =
        σ (e₁.symm g) (β.equivFun.symm v) := by
      apply β.equivFun.injective
      rw [LinearEquiv.apply_symm_apply, hkey, LinearEquiv.apply_symm_apply]
    show ((β.equivFun.symm ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) : LinearMap.ker N) : E) =
      ((e₁.symm g : ↥𝓛) : E ≃ₗ[ZMod 2] E) ((β.equivFun.symm v : LinearMap.ker N) : E)
    rw [h1]
    rfl
  have hπ : ∀ (g : GL (Fin 3) (ZMod 2)) (e : E),
      π (ρ₁ g e) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ π e := by
    intro g e
    have h1 : N.codRestrict (LinearMap.ker N) hNK (((e₁.symm g : ↥𝓛) : E ≃ₗ[ZMod 2] E) e) =
        σ (e₁.symm g) (N.codRestrict (LinearMap.ker N) hNK e) :=
      Subtype.ext (hNy _ (e₁.symm g).2 e)
    rw [hπapp, hπapp, hρ₁, h1, hkey]
  have hinj : Function.Injective i := Subtype.val_injective.comp β.equivFun.symm.injective
  have hsurj : Function.Surjective π := by
    intro w
    obtain ⟨v, hv⟩ : ((β.equivFun.symm w : LinearMap.ker N) : E) ∈ LinearMap.range N := by
      rw [hXK]
      exact (β.equivFun.symm w).2
    refine ⟨v, ?_⟩
    have h1 : N.codRestrict (LinearMap.ker N) hNK v = β.equivFun.symm w := Subtype.ext hv
    rw [hπapp, h1, LinearEquiv.apply_symm_apply]
  have hπK : ∀ x ∈ LinearMap.ker N, π x = 0 := fun x hx => by
    have h1 : N.codRestrict (LinearMap.ker N) hNK x = 0 := Subtype.ext (LinearMap.mem_ker.1 hx)
    rw [hπapp, h1, map_zero]
  have hker : LinearMap.ker π = LinearMap.range i := by
    ext v
    constructor
    · intro hv
      rw [LinearMap.mem_ker, hπapp] at hv
      have h1 : N v = 0 := by
        have h2 : N.codRestrict (LinearMap.ker N) hNK v = 0 :=
          β.equivFun.injective (by rw [map_zero]; exact hv)
        exact congrArg Subtype.val h2
      refine ⟨β.equivFun ⟨v, h1⟩, ?_⟩
      show ((β.equivFun.symm (β.equivFun ⟨v, h1⟩) : LinearMap.ker N) : E) = v
      rw [LinearEquiv.symm_apply_apply]
    · rintro ⟨w, rfl⟩
      exact LinearMap.mem_ker.2 (hπK _ (β.equivFun.symm w).2)
  obtain ⟨j, hj, hπj, -⟩ := CFSG.LocalAnalysis.SteinbergBV.natural_binary_three_space_self_extension_splitting
    ρ₁ i π hi hπ hinj hsurj hker
  have hπjv : ∀ v, π (j v) = v := fun v => LinearMap.congr_fun hπj v
  refine ⟨hE6, hXK, hK3, hfaithK, LinearMap.range j, ?_, ?_⟩
  · rintro y hy _ ⟨v, rfl⟩
    refine ⟨((e₁ ⟨y, hy⟩ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v, ?_⟩
    rw [hj, hρ₁, MulEquiv.symm_apply_apply]
  · refine IsCompl.of_eq ?_ ?_
    · rw [eq_bot_iff]
      rintro x ⟨hxK, ⟨v, rfl⟩⟩
      have h1 := hπK _ hxK
      rw [hπjv] at h1
      rw [h1, map_zero]
      exact Submodule.zero_mem _
    · rw [eq_top_iff]
      intro x _
      have h1 : x - j (π x) ∈ LinearMap.ker π := LinearMap.mem_ker.2 (by rw [map_sub, hπjv, sub_self])
      rw [hker] at h1
      obtain ⟨w, hw⟩ := h1
      have h2 : x - j (π x) ∈ LinearMap.ker N := by
        rw [← hw]
        exact (β.equivFun.symm w).2
      have h3 : x = (x - j (π x)) + j (π x) := by abel
      rw [h3]
      exact Submodule.add_mem_sup h2 ⟨π x, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
