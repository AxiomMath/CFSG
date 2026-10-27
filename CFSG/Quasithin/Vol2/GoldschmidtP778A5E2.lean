module

public import CFSG.Quasithin.H13.NParamLiftS5
public import CFSG.Quasithin.Background.E1TwoAbs

public section

namespace CFSG.Quasithin.E1.ThinA5

open Equiv CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1.LiftS5
open scoped commutatorElement


section Target

variable {P : Type*} [Group P] (f : P →* Perm (Fin 5))

@[expose] def altPre : Subgroup P := (alternatingGroup (Fin 5)).comap f

theorem mem_altPre {x : P} : x ∈ altPre f ↔ f x ∈ alternatingGroup (Fin 5) := Iff.rfl

instance altPre_normal : (altPre f).Normal := Subgroup.normal_comap f

theorem map_altPre (hA5 : alternatingGroup (Fin 5) ≤ f.range) :
    (altPre f).map f = alternatingGroup (Fin 5) := by
  rw [altPre, Subgroup.map_comap_eq, inf_eq_right.mpr hA5]

noncomputable def altPreEquiv (hf : Function.Injective f)
    (hA5 : alternatingGroup (Fin 5) ≤ f.range) :
    ↥(altPre f) ≃* ↥(alternatingGroup (Fin 5)) :=
  (Subgroup.equivMapOfInjective (altPre f) f hf).trans
    (MulEquiv.subgroupCongr (map_altPre f hA5))

theorem nonabelian_alt : ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a := by
  have h : ∃ a b : Perm (Fin 5), Perm.sign a = 1 ∧ Perm.sign b = 1 ∧ a * b ≠ b * a :=
    ⟨swap 0 1 * swap 1 2, swap 0 1 * swap 1 3, by decide, by decide, by decide⟩
  obtain ⟨a, b, ha, hb, hab⟩ := h
  exact ⟨⟨a, Perm.mem_alternatingGroup.mpr ha⟩, ⟨b, Perm.mem_alternatingGroup.mpr hb⟩,
    fun h => hab (congrArg Subtype.val h)⟩

theorem isQuasisimple_altPre (hf : Function.Injective f)
    (hA5 : alternatingGroup (Fin 5) ≤ f.range) : CFSG.IsQuasisimple ↥(altPre f) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (altPreEquiv f hf hA5).symm
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup nonabelian_alt).1

theorem isComponent_altPre (hf : Function.Injective f)
    (hA5 : alternatingGroup (Fin 5) ≤ f.range) : CFSG.IsComponent (altPre f) :=
  ⟨isQuasisimple_altPre f hf hA5, Subgroup.Normal.isSubnormal inferInstance⟩

theorem sq_mem_altPre (x : P) : x ^ 2 ∈ altPre f := by
  rw [mem_altPre, map_pow]
  exact Perm.mem_alternatingGroup.mpr (by rw [map_pow]; exact Int.units_sq _)

theorem le_altPre_of_perfect {K : Subgroup P} (hK : ⁅K, K⁆ = K) : K ≤ altPre f := by
  have h1 : ⁅K, K⁆ ≤ (Perm.sign.comp f).ker := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [hK] at h1
  intro x hx
  exact Perm.mem_alternatingGroup.mpr (MonoidHom.mem_ker.mp (h1 hx))

theorem solvableRadical_eq_bot (hf : Function.Injective f)
    (hA5 : alternatingGroup (Fin 5) ≤ f.range) : CFSG.solvableRadical P = ⊥ := by
  refine le_bot_iff.mp (sSup_le fun N hNs => ?_)
  obtain ⟨hN, hs⟩ := hNs
  have hnorm : alternatingGroup (Fin 5) ≤ Subgroup.normalizer ((N.map f : Subgroup _) :
      Set (Perm (Fin 5))) := by
    intro σ hσ
    obtain ⟨p, rfl⟩ := hA5 hσ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨p * n * p⁻¹, hN.conj_mem n hn p, by simp⟩
    · rintro hx
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨p⁻¹ * n * p, by simpa using hN.conj_mem n hn p⁻¹, ?_⟩
      have : x = (f p)⁻¹ * (f p * x * (f p)⁻¹) * f p := by group
      rw [this, ← hnx]
      simp
  have hsol : Group.IsSolvable ↥(N.map f) := by
    have h1 : Group.IsSolvable ↥((f.comp N.subtype).range) :=
      Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (f.comp N.subtype))
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  have hbot := eq_bot_of_isSolvable hnorm hsol
  intro n hn
  have hfn : f n ∈ N.map f := ⟨n, hn, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hfn
  exact Subgroup.mem_bot.mpr (hf (hfn.trans (map_one f).symm))

theorem layer_eq_altPre (hf : Function.Injective f) (hA5 : alternatingGroup (Fin 5) ≤ f.range) :
    CFSG.layer P = altPre f := by
  refine le_antisymm (sSup_le fun K hK => ?_)
    (le_sSup (isComponent_altPre f hf hA5))
  exact le_altPre_of_perfect f (Subgroup.isPerfect_iff.mp hK.1.1)

theorem perfectCore_le_twoResidual_top [Finite P] :
    perfectCore (⊤ : Subgroup P) ≤ twoResidual (⊤ : Subgroup P) := by
  obtain ⟨T, hT⟩ := exists_isSylowIn_two (⊤ : Subgroup P)
  have : Group.IsNilpotent ↥T := hT.isPGroup.isNilpotent
  refine perfectCore_le_of_sup_solvable (B := T) (twoResidual_le ⊤)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidual_le ⊤)).2
      (le_normalizer_twoResidual ⊤)) ?_ inferInstance
  rw [sup_comm]
  exact (sup_twoResidual_eq hT).symm

theorem twoResidual_top_eq_perfectCore [Finite P] (hf : Function.Injective f)
    (hA5 : alternatingGroup (Fin 5) ≤ f.range) :
    twoResidual (⊤ : Subgroup P) = perfectCore (⊤ : Subgroup P) := by
  refine le_antisymm ?_ perfectCore_le_twoResidual_top
  have hperf : ⁅altPre f, altPre f⁆ = altPre f :=
    Subgroup.isPerfect_iff.mp (isQuasisimple_altPre f hf hA5).1
  have hL : altPre f ≤ perfectCore (⊤ : Subgroup P) := le_perfectCore_of_perfect le_top hperf
  refine twoResidual_le_of_isTwoQuotient le_top ?_ fun y _ => ⟨1, hL (sq_mem_altPre f y)⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp (perfectCore_normal ⊤)

theorem le_normalizer_commutator (L B : Subgroup P) :
    L ≤ Subgroup.normalizer ((⁅L, B⁆ : Subgroup P) : Set P) := by
  have key : ∀ l0 ∈ L, ∀ c ∈ ⁅L, B⁆, l0 * c * l0⁻¹ ∈ ⁅L, B⁆ := by
    intro l0 hl0 c hc
    rw [Subgroup.commutator_def] at hc
    induction hc using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨l, hl, b, hb, rfl⟩ := hg
      have e : l0 * ⁅l, b⁆ * l0⁻¹ = ⁅l0 * l, b⁆ * ⁅l0, b⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (L.mul_mem hl0 hl) hb)
        (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hl0 hb))
    | one => simp
    | mul x y _ _ hx hy =>
      have e : l0 * (x * y) * l0⁻¹ = (l0 * x * l0⁻¹) * (l0 * y * l0⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : l0 * x⁻¹ * l0⁻¹ = (l0 * x * l0⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  intro l0 hl0
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key l0 hl0 x hx
  · intro hx
    have := key l0⁻¹ (L.inv_mem hl0) _ hx
    simpa [mul_assoc] using this

theorem commutator_altPre_eq (hf : Function.Injective f)
    (hA5 : alternatingGroup (Fin 5) ≤ f.range) {B : Subgroup P} (hB : B ≠ ⊥) :
    ⁅altPre f, B⁆ = altPre f := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup ↥(altPre f) := (altPreEquiv f hf hA5).isSimpleGroup
  have hCL : ⁅altPre f, B⁆ ≤ altPre f := Subgroup.commutator_le_left _ _
  have hn : (⁅altPre f, B⁆.subgroupOf (altPre f)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCL).mpr (le_normalizer_commutator _ _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅altPre f, B⁆.subgroupOf (altPre f)) with h | h
  · exfalso
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB
    have hbB : (b : P) ∈ B := b.2
    have hcomm : ∀ l ∈ altPre f, l * (b : P) = b * l := by
      intro l hl
      have hmem : ⁅l, (b : P)⁆ ∈ ⁅altPre f, B⁆ := Subgroup.commutator_mem_commutator hl hbB
      have h1 : (⟨⁅l, (b : P)⁆, Subgroup.commutator_le_left _ _ hmem⟩ : ↥(altPre f)) ∈
          ⁅altPre f, B⁆.subgroupOf (altPre f) := hmem
      rw [h, Subgroup.mem_bot] at h1
      have h2 : ⁅l, (b : P)⁆ = 1 := congrArg Subtype.val h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h2
    have hcomm' : ∀ σ ∈ alternatingGroup (Fin 5), σ * f b = f b * σ := by
      intro σ hσ
      obtain ⟨p, rfl⟩ := hA5 hσ
      have := hcomm p hσ
      rw [← map_mul, ← map_mul, this]
    have hc3 : Perm.sign (swap 0 1 * swap 1 2 : Perm (Fin 5)) = 1 ∧
        Perm.sign (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 : Perm (Fin 5)) = 1 := by decide
    have h1 := eq_one_of_comm (f b) ⟨(hcomm' _ (Perm.mem_alternatingGroup.mpr hc3.1)).symm,
      (hcomm' _ (Perm.mem_alternatingGroup.mpr hc3.2)).symm⟩
    exact hb1 (Subtype.ext (hf (h1.trans (map_one f).symm)))
  · exact le_antisymm hCL (by
      intro x hx
      have : (⟨x, hx⟩ : ↥(altPre f)) ∈ ⁅altPre f, B⁆.subgroupOf (altPre f) := by rw [h]; trivial
      exact this)

theorem isTwoClosed_bot : IsTwoClosed (⊥ : Subgroup P) := by
  refine ⟨⊥, ⟨le_rfl, IsPGroup.of_card (n := 0) (by simp), ?_⟩, inferInstance⟩
  rw [Subgroup.relIndex_self]
  exact fun h => by omega

theorem eTwo_of_embedding [Finite P] (hf : Function.Injective f)
    (hA5 : alternatingGroup (Fin 5) ≤ f.range) (S : Subgroup P) {B : Subgroup P}
    (hB : B ≠ ⊥) : ETwo P S B := by
  have hrad := solvableRadical_eq_bot f hf hA5
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.solvableRadical P)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hrad]
  let e : P ≃* P ⧸ CFSG.solvableRadical P :=
    MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have he : e.toMonoidHom = QuotientGroup.mk' (CFSG.solvableRadical P) := rfl
  have hLn : ((altPre f).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ e.surjective
  refine ⟨?_, ?_, twoResidual_top_eq_perfectCore f hf hA5, ?_⟩
  · rw [hrad]
    exact isTwoClosed_bot
  · rw [pCore_two_quotient_eq_top_iff]
    intro x
    refine ⟨1, ?_⟩
    show _ ∈ (CFSG.layer (P ⧸ CFSG.solvableRadical P)).comap
      (QuotientGroup.mk' (CFSG.solvableRadical P))
    rw [Subgroup.mem_comap, ← layer_map_mulEquiv e, layer_eq_altPre f hf hA5]
    exact ⟨x ^ 2 ^ 1, by simpa using sq_mem_altPre f x, rfl⟩
  · refine ⟨(altPre f).map e.toMonoidHom,
      ((CFSG.LocalCores.component_isomorphism e).1 _).1 (isComponent_altPre f hf hA5), ?_, ?_⟩
    · rw [← layer_map_mulEquiv e, layer_eq_altPre f hf hA5]
      apply le_antisymm
      · refine le_iSup₂_of_le 1 (Subgroup.one_mem _) ?_
        intro x hx
        simpa [mem_conjSub_iff] using hx
      · refine iSup₂_le fun t _ => ?_
        intro x hx
        rw [mem_conjSub_iff] at hx
        have := hLn.conj_mem _ hx t
        simpa [mul_assoc] using this
    · left
      rw [barRad, ← he, ← Subgroup.map_commutator, commutator_altPre_eq f hf hA5 hB]

end Target

end CFSG.Quasithin.E1.ThinA5
