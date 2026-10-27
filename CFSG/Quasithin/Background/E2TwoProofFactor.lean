module

public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.A1a
public import CFSG.Quasithin.Background.E2TwoProofDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2P

section Factor

variable {Y : Type} [Group Y]

structure Factor (T M L : Subgroup Y) : Prop where
  minPar : MinParabolic (⊤ : Subgroup Y) T M
  ker : kerIn M ⊤ = ⊥
  simple : IsSimpleGroup L
  nonab : ¬ IsMulCommutative L
  le : L ≤ twoResidual (⊤ : Subgroup Y)
  gen : twoResidual (⊤ : Subgroup Y) = ⨆ t ∈ T, conjSub t L
  ind : sSupIndep {S : Subgroup Y | ∃ t ∈ T, S = conjSub t L}
  normal : ∀ t ∈ T, ((conjSub t L).subgroupOf (twoResidual (⊤ : Subgroup Y))).Normal

theorem exists_factor [Finite Y] {T M : Subgroup Y} (h : MinParabolic (⊤ : Subgroup Y) T M)
    (hJ : kerIn M ⊤ = ⊥) (hns : ¬ Group.IsSolvable Y) : ∃ L, Factor T M L := by
  obtain ⟨L, hL, hLn, hLK, hgen, hind, hnorm⟩ := exists_simple_factor h hJ hns
  exact ⟨L, ⟨h, hJ, hL, hLn, hLK, hgen, hind, hnorm⟩⟩

namespace Factor

variable {T M L : Subgroup Y}

theorem conjSub_le_sup {t : Y} (ht : t ∈ T) : conjSub t L ≤ L ⊔ T := by
  intro x hx
  rw [mem_conjSub] at hx
  have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ L ⊔ T :=
    (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hx))
      (Subgroup.mem_sup_right (T.inv_mem ht))
  simpa [mul_assoc] using h1

theorem twoResidual_normal : (twoResidual (⊤ : Subgroup Y)).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))

variable (hF : Factor T M L)
include hF

theorem conjSub_le_twoResidual {t : Y} (ht : t ∈ T) : conjSub t L ≤ twoResidual ⊤ := by
  rw [hF.gen]
  exact le_iSup₂_of_le t ht le_rfl

theorem sup_eq_top [Finite Y] : L ⊔ T = ⊤ := by
  have h1 := sup_twoResidual_eq hF.minPar.isSylow
  refine eq_top_iff.mpr ?_
  rw [← h1]
  refine sup_le le_sup_right ?_
  rw [hF.gen]
  exact iSup₂_le fun t ht => conjSub_le_sup ht

theorem normal_in_twoResidual : (L.subgroupOf (twoResidual (⊤ : Subgroup Y))).Normal := by
  have := hF.normal 1 T.one_mem
  rwa [conjSub_one] at this

theorem twoResidual_le_normalizer : twoResidual ⊤ ≤ Subgroup.normalizer (L : Set Y) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hF.le).mp hF.normal_in_twoResidual

theorem isSubnormal : CFSG.Open.IsSubnormal L ⊤ :=
  CFSG.Open.IsSubnormal.step hF.le hF.normal_in_twoResidual
    (CFSG.Open.IsSubnormal.step le_top
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr
        (le_normalizer_twoResidual ⊤))
      (CFSG.Open.IsSubnormal.refl ⊤))

theorem exists_ne_comm : ∃ a b : ↥L, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact hF.nonab ⟨⟨fun a b => hcon a b⟩⟩

theorem isQuasisimple : CFSG.IsQuasisimple ↥L := by
  have := hF.simple
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hF.exists_ne_comm).1

theorem perfect : ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.mp hF.isQuasisimple.1

theorem ne_bot : L ≠ ⊥ := by
  intro h
  obtain ⟨a, b, hab⟩ := hF.exists_ne_comm
  apply hab
  have ha : a = 1 := Subtype.ext (by simpa [h] using a.2)
  rw [ha, one_mul, mul_one]

theorem mem_cComp : L ∈ cComp (⊤ : Subgroup Y) := by
  refine ⟨hF.ne_bot, hF.perfect, hF.isSubnormal, fun K hKL hK hKp hKs => ?_⟩
  have hKs' : K.IsSubnormal := A3.subnormal_top_iff.mp hKs
  have hU : (K.subgroupOf L).IsSubnormal := hKs'.subgroupOf
  have := hF.simple
  rcases hU.eq_bot_or_top_of_isSimpleGroup this with hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact hK (hbot.eq_bot_of_le hKL.le)
  · have : L ≤ K := by
      intro x hx
      have : (⟨x, hx⟩ : ↥L) ∈ K.subgroupOf L := by rw [htop]; trivial
      exact this
    exact hKL.not_ge this

theorem inf_eq_bot_of_ne {t : Y} (ht : t ∈ T) (hne : conjSub t L ≠ L) : L ⊓ conjSub t L = ⊥ := by
  have hd : Disjoint L (sSup ({S : Subgroup Y | ∃ t ∈ T, S = conjSub t L} \ {L})) :=
    hF.ind ⟨1, T.one_mem, (conjSub_one L).symm⟩
  have hle : conjSub t L ≤ sSup ({S : Subgroup Y | ∃ t ∈ T, S = conjSub t L} \ {L}) :=
    le_sSup ⟨⟨t, ht, rfl⟩, hne⟩
  exact disjoint_iff.mp (hd.mono_right hle)

theorem commute_of_ne {t : Y} (ht : t ∈ T) (hne : conjSub t L ≠ L) : ⁅L, conjSub t L⁆ = ⊥ := by
  have hinf := hF.inf_eq_bot_of_ne ht hne
  have hNL := hF.twoResidual_le_normalizer
  have hNL' : twoResidual ⊤ ≤ Subgroup.normalizer (conjSub t L : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hF.conjSub_le_twoResidual ht)).mp
      (hF.normal t ht)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbN : b ∈ twoResidual ⊤ := hF.conjSub_le_twoResidual ht hb
  have haN : a ∈ twoResidual ⊤ := hF.le ha
  have h1 : b * a * b⁻¹ * a⁻¹ ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hNL hbN) a).mp ha
    exact L.mul_mem this (L.inv_mem ha)
  have h2 : b * a * b⁻¹ * a⁻¹ ∈ conjSub t L := by
    have := (Subgroup.mem_normalizer_iff.mp (hNL' haN) b⁻¹).mp (Subgroup.inv_mem _ hb)
    have h3 : b * (a * b⁻¹ * a⁻¹) ∈ conjSub t L := Subgroup.mul_mem _ hb this
    simpa [mul_assoc] using h3
  have h4 : b * a * b⁻¹ * a⁻¹ ∈ L ⊓ conjSub t L := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot] at h4
  have : b * a = a * b := by
    have h5 := congrArg (· * (a * b)) h4
    simp only [one_mul] at h5
    rw [← h5]
    group
  exact this

theorem normal_iff [Finite Y] : L.Normal ↔ ∀ t ∈ T, conjSub t L = L := by
  constructor
  · intro hn t _
    exact conjSub_eq_self (Subgroup.le_normalizer_of_normal (Subgroup.mem_top t))
  · intro h
    have hTN : T ≤ Subgroup.normalizer (L : Set Y) := fun t ht =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (h t ht)
    have htop : L ⊔ T ≤ Subgroup.normalizer (L : Set Y) :=
      sup_le Subgroup.le_normalizer hTN
    rw [hF.sup_eq_top] at htop
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)

theorem isPGroup_quotient [Finite Y] [L.Normal] : IsPGroup 2 (Y ⧸ L) := by
  have hT2' : IsPGroup 2 (T.map (QuotientGroup.mk' L)) := hF.minPar.isSylow.2.1.map _
  have heq : T.map (QuotientGroup.mk' L) = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective L q
    have hy : y ∈ ((L ⊔ T : Subgroup Y) : Set Y) := by rw [hF.sup_eq_top]; trivial
    rw [Subgroup.normal_mul] at hy
    obtain ⟨l, hl, t, ht, rfl⟩ := hy
    refine ⟨t, ht, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have := (inferInstance : L.Normal).conj_mem _ hl t⁻¹
    simpa [mul_assoc] using this
  rw [heq] at hT2'
  exact hT2'.of_equiv Subgroup.topEquiv

theorem centralizer_eq_bot [Finite Y] [hLn : L.Normal] : Subgroup.centralizer (L : Set Y) = ⊥ := by
  set C := Subgroup.centralizer (L : Set Y) with hC
  have hCL : ∀ x, x ∈ C → x ∈ L → x = 1 := by
    have := hF.simple
    have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hF.exists_ne_comm).2
    intro x hxC hxL
    have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y y.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨j, hj⟩ := hF.isPGroup_quotient (QuotientGroup.mk (c : Y))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hj
    refine ⟨j, Subtype.ext ?_⟩
    exact hCL _ (C.pow_mem c.2 _) hj
  have hle : C ≤ CFSG.Open.pCore 2 Y := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← pCoreOf_top]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
      (fun y _ => Subgroup.le_normalizer_of_normal (Subgroup.mem_top y)) hC2
  have h2 := hle.trans hF.minPar.pCore_le_kerIn
  rw [hF.ker] at h2
  exact le_bot_iff.mp h2

theorem asHyp [Finite Y] [L.Normal] : ASHyp L T M :=
  ⟨hF.minPar, inferInstance, hF.simple, hF.exists_ne_comm, hF.sup_eq_top, hF.centralizer_eq_bot⟩

theorem layer_eq_top : CFSG.layer ↥(twoResidual (⊤ : Subgroup Y)) = ⊤ := by
  set N := twoResidual (⊤ : Subgroup Y) with hN
  have hcomp : ∀ t ∈ T, CFSG.IsComponent ((conjSub t L).subgroupOf N) := by
    intro t ht
    have hle := hF.conjSub_le_twoResidual ht
    have e1 : ↥L ≃* ↥(conjSub t L) :=
      L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
    have e2 : ↥((conjSub t L).subgroupOf N) ≃* ↥(conjSub t L) :=
      Subgroup.subgroupOfEquivOfLe hle
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2.symm) hF.isQuasisimple,
      (hF.normal t ht).isSubnormal⟩
  have hsup : (⨆ t ∈ T, (conjSub t L).subgroupOf N) = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.map_iSup]
    conv_rhs => rw [hN, hF.gen]
    refine iSup_congr fun t => iSup_congr fun ht => ?_
    exact Subgroup.map_subgroupOf_eq_of_le (hF.conjSub_le_twoResidual ht)
  refine eq_top_iff.mpr ?_
  rw [← hsup]
  exact iSup₂_le fun t ht => CFSG.LocalCores.component_le_layer (hcomp t ht)

end Factor

theorem isPGroup_quotient_twoResidual [Finite Y] [(twoResidual (⊤ : Subgroup Y)).Normal] :
    IsPGroup 2 (Y ⧸ twoResidual (⊤ : Subgroup Y)) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup Y) y (Subgroup.mem_top y)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hk

end Factor

theorem sqtkGroup_star (hA21 : AsA21SQTKSection) {Γ : Type} [Group Γ] [Finite Γ]
    {H T M : Subgroup Γ} (h : MinParabolic H T M) (hsq : SQTKGroup ↥H)
    (hns : ¬ Group.IsSolvable ↥H) : SQTKGroup (E2.StarQuot M H) := by
  obtain ⟨L, hF⟩ := exists_factor (minParabolic_star h) (kerIn_star M H) (not_isSolvable_star h hns)
  have hN : (twoResidual (⊤ : Subgroup (E2.StarQuot M H))).Normal := Factor.twoResidual_normal
  refine hA21 ↥H hsq ⊤ (E2.StarQuot M H) ((starMap M H).comp (⊤ : Subgroup ↥H).subtype) ?_
    (twoResidual ⊤) hF.layer_eq_top isPGroup_quotient_twoResidual
  intro y
  obtain ⟨x, rfl⟩ := starMap_surjective M H y
  exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩

end E2P

end CFSG.Quasithin
