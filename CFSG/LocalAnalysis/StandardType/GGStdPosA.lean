module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123
import CFSG.LocalAnalysis.StandardType.GGStdPosACore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

private theorem ggKGPosStdPos_psl_of_card
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} {n f : ℕ}
    {ψ : (ggU .PSL n f).K →* G} (h : GGKGPosLocalHyp p Bs X .PSL n f ψ)
    (h3 : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs) :
    ∃ k : (ggU .PSL n f).K,
      GGKGPosStdPos (ggU .PSL n f).D (ψ.comp (MulAut.conj k).toMonoidHom) Bs := by
  obtain ⟨⟨hp, hp2, hadm, hrk⟩, ⟨hker, hX, -, hpq⟩, ⟨hBs, -, -⟩, hinn, -, hc1⟩ := h
  obtain ⟨-, hf, hn, -, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by
    change 3 ≤ m + 1 - 1 at hrk
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  subst hX
  change p ^ (m + 1 - 1 - 1) * _ ≤ _ at hc1
  rw [show m + 1 - 1 - 1 = m - 1 by omega] at hc1
  exact StdPosA.exists_stdPos_sl (F := GaloisField 2 f) hm hp hp2 (by rw [hF]; exact hpq) hker hBs
    hinn hc1 h3

theorem ggKGPosStdPosA :
    GGKGPosStdPosCase .PSL (fun p n => ¬ p ∣ n) := by
  intro G _ _ p Bs X n f ψ h hpn
  refine ggKGPosStdPos_psl_of_card h ?_
  have hT : ¬ GGKGPosTorsion p .PSL n := by
    rintro (⟨-, h'⟩ | ⟨h', -⟩)
    · exact hpn h'
    · cases h'
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right h.1.1.pos h.1.2.2.2)).trans
    (h.2.2.2.2.1 hT)

theorem ggKGPosStdPosATors :
    GGKGPosStdPosCase .PSL (fun p n => p ∣ n) := by
  intro G _ _ p Bs X n f ψ h hpn
  refine ggKGPosStdPos_psl_of_card h ?_
  have hrk : 3 ≤ n - 1 := h.1.2.2.2
  have hn4 : n ≠ 4 := by
    rintro rfl
    have h4 : p ∣ 2 ^ 2 := hpn
    exact h.1.2.1 ((Nat.prime_dvd_prime_iff_eq h.1.1 Nat.prime_two).mp (h.1.1.dvd_of_dvd_pow h4))
  have h3 : 3 ≤ bnRank .PSL n - 1 := by
    change 3 ≤ n - 1 - 1
    omega
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right h.1.1.pos h3)).trans h.2.2.2.2.2

end CFSG.StandardType

end
