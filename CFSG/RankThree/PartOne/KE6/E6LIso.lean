module

public import CFSG.RankThree.PartOne.KE6.E6LInj

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Generation

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]

theorem minGroup_le_of_simple' {P : Subgroup (Module.End k (Fin D.d →₀ k))ˣ}
    (hP : ∀ (i : Fin τ.rank) (c : k),
      hV.xu k (Pi.single i 1) c ∈ P ∧ hV.xu k (-Pi.single i 1) c ∈ P) :
    hV.minGroup k ≤ P := by
  have hn : ∀ i, ((hV.nm k i : hV.minGroup k) : (Module.End k (Fin D.d →₀ k))ˣ) ∈ P := fun i =>
    mul_mem (mul_mem (hP i _).1 (hP i _).2) (hP i _).1
  have hx : ∀ γ, IsRoot τ γ → ∀ c : k, hV.xu k γ c ∈ P := by
    intro γ hγ
    induction hγ with
    | basis j => exact fun c => (hP j c).1
    | @reflect i v hv ih =>
      intro c
      obtain ⟨σ, hσ, h⟩ := hV.nm_conj_xm k hv i
      have e : hV.xm k (reflect τ i v) c =
          hV.nm k i * hV.xm k v (σ * c) * (hV.nm k i)⁻¹ := by
        rw [h, ← mul_assoc, hσ.mul_self, one_mul]
      have e' := congrArg (fun g : hV.minGroup k => (g : (Module.End k (Fin D.d →₀ k))ˣ)) e
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
      change hV.xu k (reflect τ i v) c = _ at e'
      rw [e']
      exact mul_mem (mul_mem (hn i) (ih _)) (inv_mem (hn i))
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨γ, hγ, c, rfl⟩
  exact hx γ hγ c

end Generation

section Injective

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {K : Type} [Field K]

theorem m27ResMin_injective : Function.Injective (m27ResMin τ K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg1 : m27Res K e6Set_lt' g = 1 := by
    have e : m27Res K e6Set_lt' g = ((m27ResMin τ K g : e6Data_valid.minGroup K) : GL27 K) := rfl
    rw [e, hg]
    rfl
  have hgfix : ∀ v, ((g : ModGL τ K) : Module.End K (RootModule τ K)) (m27Emb τ K v) =
      m27Emb τ K v := by
    intro v
    rw [m27Res_apply e6Set_lt' g v, hg1, Units.val_one, Module.End.one_apply]
  obtain ⟨⟨v, h, u, u'⟩, ⟨hv, hh, hu, hu', hgeq⟩, -⟩ := existsUnique_supportedCell_factors g.2
  simp only at hv hh hu hu' hgeq
  have hhQ : h ∈ subsystemGroup τ K (e6Set τ) := supportedTorus_le_subsystemGroup _ hh
  have huQ : u ∈ subsystemGroup τ K (e6Set τ) := parabolicLeviUnipotent_le_subsystemGroup hu
  have hu'Q : u' ∈ subsystemGroup τ K (e6Set τ) := by
    rw [subsystemGroup_eq_rootSpan]
    exact rootSpan_mono Set.inter_subset_left hu'
  have hhB : h ∈ borelGroup τ K :=
    torusGroup_le_borelGroup (supportedTorus_le_torusGroup _ hh)
  have huB : u ∈ borelGroup τ K :=
    Subgroup.mem_sup_right (parabolicLeviUnipotent_le_posUnipotent _ hu)
  have hu'B : u' ∈ borelGroup τ K :=
    Subgroup.mem_sup_right (rootSpan_le_posUnipotent (fun _ hα => ⟨hα.2.1, hα.2.2.1⟩) hu')
  have hb : (h * u)⁻¹ * u'⁻¹ ∈ borelGroup τ K :=
    mul_mem (inv_mem (mul_mem hhB huB)) (inv_mem hu'B)
  have hn : canonicalRep (coxeterSystem τ) K v = (h * u)⁻¹ * (g : ModGL τ K) * u'⁻¹ := by
    rw [← hgeq]
    group
  have hfix : ∀ a : Fin e6Data.d,
      (canonicalRep (coxeterSystem τ) K v : Module.End K (RootModule τ K))
        (rootVec τ K (m27Root τ a)) =
      (((h * u)⁻¹ * u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K))
        (rootVec τ K (m27Root τ a)) := by
    intro a
    have e0 : rootVec τ K (m27Root τ a) = m27Emb τ K (Finsupp.single a 1) :=
      (m27Emb_basis a).symm
    have e1 : ((u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K (m27Root τ a)) =
        m27Emb τ K ((m27Res K e6Set_lt' ⟨u'⁻¹, inv_mem hu'Q⟩ : Module.End K (Fin e6Data.d →₀ K))
          (Finsupp.single a 1)) := by
      rw [e0]
      exact m27Res_apply e6Set_lt' ⟨u'⁻¹, inv_mem hu'Q⟩ _
    have e2 : ((g : ModGL τ K) : Module.End K (RootModule τ K))
        (((u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K (m27Root τ a))) =
        ((u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K (m27Root τ a)) := by
      rw [e1, hgfix]
    rw [hn, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, e2,
      Units.val_mul, Module.End.mul_apply]
  choose p hp using fun a => exists_smul_m27Root (τ := τ) hv a
  have hpinj : Function.Injective p := fun a b hab => by
    have h1 : v • m27Root τ a = v • m27Root τ b := by rw [hp a, hp b, hab]
    exact m27Root_injective M27Ok.isE7E8 (MulAction.injective v h1)
  have hmaps := mapsRootLines_canonicalRep (R := K) v
  have hnp : ∀ a, ¬ Label.Precedes (m27Label (τ := τ) a) (m27Label (p a)) := by
    intro a hprec
    have hlab : (Sum.inr ⟨v • m27Root τ a, IsRoot.smul (m27_isRoot M27Ok.isE7E8 a) v⟩ : Label τ) =
        m27Label (p a) := congrArg Sum.inr (Subtype.ext (hp a))
    have := not_precedes_of_apply_eq_borel hb hmaps (m27_isRoot M27Ok.isE7E8 a) (hfix a)
    rw [hlab] at this
    exact this hprec
  have hpid := eq_self_of_not_precedes p hpinj hnp
  have hv1 : v = 1 := eq_one_of_smul_m27Root hv fun a => by rw [hp a, hpid a]
  subst hv1
  have hu'1 : u' = 1 := by
    rw [inversionSet_one, Set.inter_empty] at hu'
    simpa [rootSpan] using hu'
  rw [hu'1, canonicalRep_one, mul_one, mul_one] at hgeq
  have hhT : h ∈ torusGroup τ K := supportedTorus_le_torusGroup _ hh
  have huU : IsUpperUnitriangular (u : Module.End K (RootModule τ K)) :=
    (positive_root_triangularity.{0, 0} τ).1 K |>.1 u
      (parabolicLeviUnipotent_le_posUnipotent _ hu)
  have h27 : ∀ a : Fin e6Data.d, torusRootChar h (m27Root τ a) = 1 := by
    intro a
    have hα := m27_isRoot (τ := τ) M27Ok.isE7E8 a
    rw [← coeff_torus_mul_unitriangular' hhT huU hα, hgeq]
    have hv : rootVec τ K (m27Root τ a) = m27Emb τ K (Finsupp.single a 1) :=
      (m27Emb_basis a).symm
    rw [hv, hgfix, ← hv, rootVec_eq_single_of_isRoot hα, Finsupp.single_eq_same]
  have hh1 : h = 1 := eq_one_of_torusRootChar_single' hh (torusRootChar_single_eq_one hh h27)
  subst hh1
  rw [one_mul] at hgeq
  have hgu : g = ⟨u, huQ⟩ := Subtype.ext hgeq.symm
  rw [hgu] at hg ⊢
  exact eq_one_of_mem_parabolicLeviUnipotent_m27ResMin hu hg

theorem m27ResMin_surjective : Function.Surjective (m27ResMin τ K) := by
  have hle : e6Data_valid.minGroup K ≤
      (m27ResMin τ K).range.map (e6Data_valid.minGroup K).subtype := by
    refine minGroup_le_of_simple' e6Data_valid K fun i c => ⟨?_, ?_⟩
    · exact ⟨_, ⟨⟨xUnit τ K (e6Idx i) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set i) c⟩,
        m27ResMin_xUnit (τ := τ) (K := K) i c⟩, rfl⟩
    · exact ⟨_, ⟨⟨yUnit τ K (e6Idx i) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set i) c⟩,
        m27ResMin_yUnit (τ := τ) (K := K) i c⟩, rfl⟩
  intro g
  obtain ⟨x, ⟨q, hq⟩, hxg⟩ := Subgroup.mem_map.1 (hle g.2)
  exact ⟨q, by rw [hq]; exact Subtype.ext hxg⟩

variable (τ K) in
@[expose] def m27Equiv : subsystemGroup τ K (e6Set τ) ≃* e6Data_valid.minGroup K :=
  MulEquiv.ofBijective (m27ResMin τ K) ⟨m27ResMin_injective, m27ResMin_surjective⟩

theorem m27Equiv_apply (g : subsystemGroup τ K (e6Set τ)) :
    m27Equiv τ K g = m27ResMin τ K g := rfl

end Injective

end CFSG.RankThree.PartOne.KE6
