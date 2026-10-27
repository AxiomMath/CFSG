module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public import CFSG.Sporadic.Schreier.MathieuSylowAutCent
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M23Pinned
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M23
public meta import CFSG.Sporadic.Schreier.M23Pinned
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import CFSG.Sporadic.Schreier.MathieuSylowAutM23Inputs
public import Certificates.Certificate2209
public import Certificates.Certificate2196
public import Certificates.Certificate2197

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem m23_sylowAut_check :
    sylowAutOK 23 (toTable m23PermA) (toTable m23PermB) m23Derivs
      m23SylowExprs (natTbl 23 m23SylowZ) 150 10200960 7 = true :=
  Certificates.certificate2209.1

theorem m23_centralizer_check :
    sylCentOK 23 (sylowGens 23 (toTable m23PermA) (toTable m23PermB) m23Derivs m23SylowExprs)
      (natTbl 23 m23SylowZ) (toTable m23PermB) (allTables m23CentQ1) = true :=
  Certificates.certificate2209.2.1

theorem m23_centralizer_a :
    centralizerIn NativeSporadic.M23 m23PermA = m23CentQ1.originalSubgroup := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hrep : m23Rep1 = m23PermA := by simp [m23Rep1, m23InvReps, m23InvRepWords, evalCodes]
  rw [← m23Certificate_originalSubgroup, ← hrep]
  refine centralizerIn_eq_of_reps hn m23Certificate hQ (pairTables_spec hn hA hB) [m23Rep1]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨hr1, hro1⟩) 4000 hok (List.mem_singleton_self _) hK1 ?_
  rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card]

theorem m23_sylow_pointwise_inner :
    ∀ (T : Sylow 2 NativeSporadic.M23) (α : MulAut NativeSporadic.M23),
      (∀ t ∈ (T : Subgroup NativeSporadic.M23), α t = t) →
      ∃ z : (T : Subgroup NativeSporadic.M23),
        z ∈ Subgroup.center (T : Subgroup NativeSporadic.M23) ∧
        ∀ g : NativeSporadic.M23,
          α g = (z : NativeSporadic.M23) * g * (z : NativeSporadic.M23)⁻¹ := by
  obtain ⟨hc, -, -, -⟩ := m23_oddcore_cent1
  exact sylow_pointwise_inner_of_cent (by norm_num) NativeSporadic.M23 m23_eq_closure m23_card
    m23_mulAut_card _ _ _ 150 7 m23_sylowAut_check m23CentQ1 hc m23_centralizer_a.le
    m23_centralizer_check

end CFSG.Sporadic.Schreier
