module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public import CFSG.Sporadic.Schreier.MathieuSylowAutCent
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Monster.B.Mathieu.M24Check
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M24
public meta import CFSG.Monster.B.Mathieu.M24Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import CFSG.Sporadic.Schreier.MathieuSylowAutM24Inputs
public import Certificates.Certificate2210
public import Certificates.Certificate2198
public import Certificates.Certificate3046

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem m24_sylowAut_check :
    sylowAutOK 24 (toTable m24gA) (toTable m24gB) m24Derivs
      m24SylowExprs (natTbl 24 m24SylowZ) 1100 244823040 10 = true :=
  Certificates.certificate2210.1

theorem m24_centralizer_check :
    sylCentOK 24 (sylowGens 24 (toTable m24gA) (toTable m24gB) m24Derivs m24SylowExprs)
      (natTbl 24 m24SylowZ) (toTable m24gB) (allTables m24CentQ1) = true :=
  Certificates.certificate2210.2.1

theorem m24_centralizer_a :
    centralizerIn NativeSporadic.M24 m24gA = m24CentQ1.originalSubgroup := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  obtain ⟨hok, hsz, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, -, -, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  rw [m24InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hrep : m24Rep1 = m24gA := by simp [m24Rep1, m24InvReps, m24InvRepWords, evalCodes]
  rw [← m24Certificate_originalSubgroup, ← hrep]
  refine centralizerIn_eq_of_reps hn m24Certificate hQ (pairTables_spec hn hA hB)
    [m24Rep1, m24Rep2]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hr1, hro1⟩
      · exact ⟨hr2, hro2⟩) 40000 hok (by simp) hK1 ?_
  rw [hsz.1, hKc1, m24Certificate_originalSubgroup, m24_card]

theorem m24_sylow_pointwise_inner :
    ∀ (T : Sylow 2 NativeSporadic.M24) (α : MulAut NativeSporadic.M24),
      (∀ t ∈ (T : Subgroup NativeSporadic.M24), α t = t) →
      ∃ z : (T : Subgroup NativeSporadic.M24),
        z ∈ Subgroup.center (T : Subgroup NativeSporadic.M24) ∧
        ∀ g : NativeSporadic.M24,
          α g = (z : NativeSporadic.M24) * g * (z : NativeSporadic.M24)⁻¹ := by
  obtain ⟨hc, -, -, -⟩ := m24_oddcore_cent1
  exact sylow_pointwise_inner_of_cent (by norm_num) NativeSporadic.M24 m24_eq m24_card
    m24_mulAut_card _ _ _ 1100 10 m24_sylowAut_check m24CentQ1 hc m24_centralizer_a.le
    m24_centralizer_check

end CFSG.Sporadic.Schreier
