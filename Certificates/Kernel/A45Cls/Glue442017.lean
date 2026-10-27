module

public import Certificates.Data.OmegaSwap
public import Certificates.Kernel.A45Cls.Check442017
public import Certificates.Kernel.A45Cls.Glue218b
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.GH74.KGroups.PermCheck

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup
  Certificates.OmegaTypes CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

theorem swap442017 {u : P45} (huA : u ∈ QA45.originalSubgroup)
    (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hc : u * Certificates.P43Twin.tA () = Certificates.P43Twin.tA () * u)
    (hf : Certificates.OmegaInv.fixCnt u = 15) :
    swapChk (kaList ()) (Certificates.OmegaPk.kbList (Certificates.OmegaPk.g0 ()) (kaList ())) u =
      true := by
  obtain ⟨i, hi, hp, -⟩ := ca_point (n := Nat.card ↥(QA45.originalSubgroup ⊓
    Subgroup.centralizer ({u} : Set P45))) ⟨huA, hu2, hu1, rfl⟩ hc
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have h15 : invFixK 45 6 15 (CA.T i) = true := (invFixK_iff hp).2 ⟨⟨hu2, hu1⟩, hf⟩
  have hS := allN_spec swK442017 i hi
  rw [strictB_eq', h15] at hS
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hS
  have hconj : ∀ {X Y : ℕ → ℕ} {x y : ℕ → P45}, (∀ j < 24, PRep 45 6 (X j) (x j)) →
      (∀ j < 24, PRep 45 6 (Y j) (y j)) → cjAll 45 6 24 X Y (CA.T i) = true →
      ∀ j < 24, ∃ m < 24, y m = u * x j * u⁻¹ := by
    intro X Y x y hx hy h j hj
    rw [hinv]
    exact cjAll_spec h hp hx hy j hj
  unfold swapChk
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := mem_KAs.1 hk
    obtain ⟨m, hm, e⟩ := hconj prep_kx prep_ky hS.1 j hj
    have hmem : u * kx j * u⁻¹ ∈ KBs := mem_KBs.2 ⟨m, hm, e⟩
    unfold memB
    exact List.any_eq_true.2 ⟨_, hmem, decide_eq_true rfl⟩
  · obtain ⟨j, hj, rfl⟩ := mem_KBs.1 hk
    obtain ⟨m, hm, e⟩ := hconj prep_ky prep_kx hS.2 j hj
    have hmem : u * ky j * u⁻¹ ∈ KAs := mem_KAs.2 ⟨m, hm, e⟩
    unfold memB
    exact List.any_eq_true.2 ⟨_, hmem, decide_eq_true rfl⟩

theorem check442017 : Certificates.OmegaSwap.check () = true := by
  unfold Certificates.OmegaSwap.check Certificates.OmegaSwap.swapAll
  rw [List.all_eq_true]
  intro u hu
  have huA : u ∈ QA45.originalSubgroup := (mem_elemsT QA45 QA45_ok u).1 hu
  by_cases h2 : u * u = 1
  · by_cases h1 : u = 1
    · simp [h1]
    · by_cases hc : u * Certificates.P43Twin.tA () = Certificates.P43Twin.tA () * u
      · by_cases hf : Certificates.OmegaInv.fixCnt u = 15
        · simp [swap442017 huA h2 h1 hc hf]
        · simp [hf]
      · simp [hc]
  · simp [h2]

end CertificateChecks.KernelA45

end
