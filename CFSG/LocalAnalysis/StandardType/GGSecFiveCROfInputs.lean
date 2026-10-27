module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxProd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDichotomy
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggSecFiveCR_pair_order_le_four
    (hRR : GGSecFiveRootReflInput) (hCP : GGSecFiveCoxProdInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (A : Subgroup (MulAut ↥Bs)) (hA : A ≤ ggInduced ⊤ Bs)
    (hW : GGWeylReflectionGroup p A) (hnotG2 : ¬ GGWeylOfType p CoxeterMatrix.G₂ A)
    {a b : MulAut ↥Bs} (ha : a ∈ A) (hb : b ∈ A)
    (har : GGIsReflection p a) (hbr : GGIsReflection p b) : orderOf (a * b) ≤ 4 := by
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  have hM2 : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨e, rfl⟩
    exact hnotG2 (GGWeylOfType.of_reindex (p := p) (A := A) (e := e) ⟨f, hf⟩)
  obtain ⟨i, g, hag⟩ := hRR G p Bs hp hp2 hBs hNT A hA ι M hM hM2 f hf ⟨a, ha⟩ har
  obtain ⟨j, h, hbh⟩ := hRR G p Bs hp hp2 hBs hNT A hA ι M hM hM2 f hf ⟨b, hb⟩ hbr
  have hz : (⟨a, ha⟩ * ⟨b, hb⟩ : ↥A) =
      f ((g * M.simple i * g⁻¹) * (h * M.simple j * h⁻¹)) := by
    rw [hag, hbh, ← map_mul]
  calc orderOf (a * b) = orderOf (⟨a, ha⟩ * ⟨b, hb⟩ : ↥A) := by
        rw [show a * b = ((⟨a, ha⟩ * ⟨b, hb⟩ : ↥A) : MulAut ↥Bs) from rfl, Subgroup.orderOf_coe]
      _ = orderOf (f ((g * M.simple i * g⁻¹) * (h * M.simple j * h⁻¹))) := by rw [hz]
      _ = orderOf ((g * M.simple i * g⁻¹) * (h * M.simple j * h⁻¹)) :=
        MulEquiv.orderOf_eq f _
      _ ≤ 4 := hCP ι M hM hM2 i j g h

theorem ggSecFiveCRInput_of_inputs
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hRR : GGSecFiveRootReflInput) (hCP : GGSecFiveCoxProdInput)
    : GGSecFiveCRInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit t t' ht ht'refl ht'real
  obtain ⟨r, hrJ, hrrefl, g, hgInd, ht_eq⟩ := ht
  obtain ⟨g0, -, hg0N, hg0eq⟩ := hgInd
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hInn : GGInnerDiagAll p B Bs x L D J := hcfg.1.2.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hp, hBs_ea, -, -, -⟩ := hconf.tableB_facts
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  let φ : MulAut ↥Bs := ggConjAut Bs hg0N
  have hg_eq : g = φ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hg0eq b, ggConjAut_apply]
  have ht_eq' : t = φ * r * φ⁻¹ := by rw [ht_eq, hg_eq]
  let φinv : MulAut ↥Bs := ggConjAut Bs (Subgroup.inv_mem _ hg0N)
  have hφinv : φinv = φ⁻¹ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply, inv_inv]
    exact (inv_apply_of_forall (fun b => ggConjAut_apply Bs hg0N b) b).symm
  let s : MulAut ↥Bs := φinv * t' * φinv⁻¹
  have hs_real : GGRealized p Bs s := ht'real.conj hp (Subgroup.inv_mem _ hg0N)
  have hs_refl : GGIsReflection p s := ht'refl.conj' φinv
  obtain ⟨Jt, hs_ind, hs_fix, hs_pc⟩ := hs_real
  have hdich := ggDichotomy_refined hL hP hconf hInn hs_refl hs_ind hs_fix hs_pc
  have hconj : (MulAut.conj φinv) (t * t') = r * s := by
    change φinv * (t * t') * φinv⁻¹ = r * (φinv * t' * φinv⁻¹)
    rw [ht_eq', hφinv]
    group
  have horder : orderOf (t * t') = orderOf (r * s) := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj φinv) (t * t'), hconj]
  rw [horder]
  rcases hdich with hJLt | ⟨d, K, hnb, hJK, hJtK⟩ | hcomm
  ·
    have hpJ : p ∣ Nat.card J := hP G p B x L D J hconf.1 hconf.2.2
    obtain ⟨hJL, -, -⟩ := eq_of_le_of_stdSub hconf.1 hconf.2.2 hpJ
    obtain ⟨hWeyl, hnotG2⟩ := hPump.1 G p B Bs x L D J 𝒦 hcfg hsplit
    have hJle : ggAutomizer J Bs ≤ ggAutomizer L Bs := ggAutomizer_mono Bs hJL
    have hrA : r ∈ ggAutomizer L Bs := hJle hrJ
    have hsA : s ∈ ggAutomizer L Bs := by
      obtain ⟨a, ha, haN, has⟩ := hs_ind
      exact Subgroup.subset_closure ⟨a, hJLt ha, haN, has⟩
    have hAind : ggAutomizer L Bs ≤ ggInduced ⊤ Bs := by
      intro w hw
      have h1 : w ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hw
      rwa [ggAutomizer_eq] at h1
    exact ggSecFiveCR_pair_order_le_four hRR hCP hp hp2 hBs_ea hNT (ggAutomizer L Bs) hAind
      hWeyl hnotG2 hrA hsA hrrefl hs_refl
  ·
    obtain ⟨hWeyl, hnotG2⟩ := hPump.2 G p B Bs x L D J 𝒦 hcfg hsplit d K hnb
    have hJKle : ggAutomizer J Bs ≤ ggAutomizer K Bs := ggAutomizer_mono Bs hJK
    have hrA : r ∈ ggAutomizer K Bs := hJKle hrJ
    have hsA : s ∈ ggAutomizer K Bs := by
      obtain ⟨a, ha, haN, has⟩ := hs_ind
      exact Subgroup.subset_closure ⟨a, hJtK ha, haN, has⟩
    have hAind : ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
      intro w hw
      have h1 : w ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hw
      rwa [ggAutomizer_eq] at h1
    exact ggSecFiveCR_pair_order_le_four hRR hCP hp hp2 hBs_ea hNT (ggAutomizer K Bs) hAind
      hWeyl hnotG2 hrA hsA hrrefl hs_refl
  ·
    have hsr : s * r = r * s := by
      have hsub : ggInduced J Bs ⊆ (Subgroup.centralizer ({s} : Set (MulAut ↥Bs))) := by
        intro a ha
        exact Subgroup.mem_centralizer_iff.mpr (by
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact hcomm a ha)
      have hcl : ggAutomizer J Bs ≤ Subgroup.centralizer ({s} : Set (MulAut ↥Bs)) :=
        (Subgroup.closure_le (Subgroup.centralizer ({s} : Set (MulAut ↥Bs)))).mpr hsub
      have hmem := hcl hrJ
      exact (Subgroup.mem_centralizer_iff.mp hmem) s rfl
    have h2 : (r * s) ^ 2 = 1 := by
      have hcr : Commute r s := hsr.symm
      rw [hcr.mul_pow, hrrefl.1, hs_refl.1, mul_one]
    have hle2 : orderOf (r * s) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega

end CFSG.StandardType
