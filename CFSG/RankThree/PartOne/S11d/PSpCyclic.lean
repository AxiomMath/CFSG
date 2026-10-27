module

public import CFSG.RankThree.PartOne.S11d.OddAlt
public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
import CFSG.LieType.SeitzGeneration.SpHyperRad

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OddIso
  CFSG.RankThree.PartOne.KCSpFull CFSG.LocalAnalysis.ComponentInitial

variable {r p : ℕ} {K : Type} [Field K]

theorem spEnd_pow' (a : StatedSp r K) (n : ℕ) : spEnd (a ^ n) = spEnd a ^ n :=
  CFSG.LieType.SeitzGeneration.spEnd_pow a n

theorem spEnd_isom (a : StatedSp r K) (v w : Fin r ⊕ Fin r → K) :
    spForm r K (spEnd a v) (spEnd a w) = spForm r K v w :=
  mem_sesqUnitaryGroup.mp (spLin_mem a) v w

theorem spEnd_comm_iff {a g : StatedSp r K} :
    g * a = a * g ↔ spEnd g * spEnd a = spEnd a * spEnd g := by
  constructor
  · intro h
    rw [← spEnd_mul, ← spEnd_mul, h]
  · intro h
    apply spLin_injective
    rw [map_mul, map_mul]
    exact Units.ext (by simpa [spEnd_mul] using h)

theorem exists_spElem_of_isom {u : Module.End K (Fin r ⊕ Fin r → K)} (hup : u ^ p = 1)
    (hp1 : 1 ≤ p) (hiso : ∀ v w, spForm r K (u v) (u w) = spForm r K v w) :
    ∃ g : StatedSp r K, spEnd g = u := by
  let uU : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) :=
    ⟨u, u ^ (p - 1), by rw [← pow_succ', Nat.sub_add_cancel hp1, hup],
      by rw [← pow_succ, Nat.sub_add_cancel hp1, hup]⟩
  have hmem : uU ∈ sesqUnitaryGroup (spForm r K) := mem_sesqUnitaryGroup.mpr hiso
  rw [← range_spLin] at hmem
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, ?_⟩
  change ((spLin r K g : LinearMap.GeneralLinearGroup K _) : Module.End K _) = u
  rw [hg]

theorem spEnd_injective : Function.Injective (spEnd : StatedSp r K → Module.End K _) :=
  fun _ _ e => spLin_injective (Units.ext e)

theorem dvd_of_natMod {p : ℕ} (hp : 0 < p) (i : ℤ) (h : p ∣ (i % p).toNat) : (p : ℤ) ∣ i := by
  have hlt : (i % p).toNat < p := by
    have h1 : i % p < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
    have h2 : (0 : ℤ) ≤ i % p := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
    omega
  have h0 : (i % p).toNat = 0 := Nat.eq_zero_of_dvd_of_lt h hlt
  have h2 : (0 : ℤ) ≤ i % p := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  exact Int.dvd_of_emod_eq_zero (by omega)

theorem zpow_eq_pow_natMod {G : Type*} [Group G] {g : G} {p : ℕ} (hp : 0 < p) (hg : g ^ p = 1)
    (i : ℤ) : g ^ i = g ^ (i % p).toNat := by
  have h1 : i = (p : ℤ) * (i / p) + i % p := (Int.mul_ediv_add_emod i p).symm
  have h2 : (0 : ℤ) ≤ i % p := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  conv_lhs => rw [h1]
  rw [zpow_add, zpow_mul, zpow_natCast, hg, one_zpow, one_mul, ← zpow_natCast,
    Int.toNat_of_nonneg h2]

theorem sp_cyclic_of_rank [Finite K] [CharP K 2] (hp : p.Prime) (hodd : Odd p) {a : StatedSp r K}
    (hap : a ^ p = 1) (ha1 : a ≠ 1) (hrank : CFSG.pRank p (StatedSp r K) ≤ 1) :
    IsCyclicOn (spEnd a) (LinearMap.range (spEnd a - 1)) := by
  by_contra hnc
  have hÂp : spEnd a ^ p = 1 := by rw [← spEnd_pow', hap, spEnd_one]
  have hW : LinearMap.range (spEnd a - 1) ≠ ⊥ := by
    intro h
    apply ha1
    apply spLin_injective
    rw [map_one]
    refine Units.ext (LinearMap.ext fun v => ?_)
    have : (spEnd a - 1) v = 0 := by
      have hv : (spEnd a - 1) v ∈ LinearMap.range (spEnd a - 1) := ⟨v, rfl⟩
      rw [h] at hv
      exact (Submodule.mem_bot K).mp hv
    have h2 : spEnd a v = v := sub_eq_zero.mp (by simpa using this)
    exact h2
  have hBn : ∀ v, (∀ w, spForm r K v w = 0) → v = 0 := fun v hv =>
    (spForm_nondegenerate (r := r) (K := K)).1 v hv
  obtain ⟨M, hMW, hM0, hMW', hMinv, hMn⟩ := exists_split spForm_isAlt hBn
    (spEnd_isom a) hodd hÂp hW hnc
  obtain ⟨u, hiso, hcomm, hup, hindep⟩ := exists_independent hp spForm_isAlt (spEnd_isom a) hodd
    hÂp hMW hM0 hMW' hMinv hMn
  obtain ⟨g, hg⟩ := exists_spElem_of_isom hup hp.pos hiso
  have hga : g * a = a * g := spEnd_comm_iff.mpr (by rw [hg]; exact hcomm)
  have hgp : g ^ p = 1 :=
    spEnd_injective (by rw [spEnd_pow', hg, hup, spEnd_one])
  have h2 := two_le_pRank_of_two_elements (P := StatedSp r K) hp (e₁ := g) (e₂ := a)
    (show Commute g a from hga) hgp hap (fun i j hij => by
      rw [zpow_eq_pow_natMod hp.pos hgp i, zpow_eq_pow_natMod hp.pos hap j] at hij
      have h3 : u ^ (i % p).toNat * (spEnd a) ^ (j % p).toNat = 1 := by
        have := congrArg spEnd hij
        rwa [spEnd_mul, spEnd_pow', spEnd_pow', spEnd_one, hg] at this
      obtain ⟨h4, h5⟩ := hindep _ _ h3
      exact ⟨dvd_of_natMod hp.pos i h4, dvd_of_natMod hp.pos j h5⟩)
  omega

end CFSG.RankThree.PartOne
