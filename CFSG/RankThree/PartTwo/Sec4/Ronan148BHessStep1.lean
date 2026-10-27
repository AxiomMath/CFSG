module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessRho
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessDickson
import CFSG.RankThree.PartOne.KF.F1322OmegaSeven
import CFSG.Dihedral.Glauberman.DicksonMaxUp

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.SubgroupLists CFSG.BenderSuzuki.MatrixGroups
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime]

@[expose] noncomputable def hessR (hp3 : p ≠ 3) : Subgroup (GL (Fin 3) (ZMod p)) :=
  Subgroup.closure (Set.range (hessT (F := ZMod p)) ∪ {hessS0 (three_ne_zero_of hp3)})

theorem hessT_mem_hessR (hp3 : p ≠ 3) (i : Fin 3) : hessT i ∈ hessR hp3 :=
  Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

theorem hessS0_mem_hessR (hp3 : p ≠ 3) : hessS0 (three_ne_zero_of hp3) ∈ hessR hp3 :=
  Subgroup.subset_closure (Or.inr rfl)

theorem hessRho2_mem_hessR (hp3 : p ≠ 3) : hessRho2 (three_ne_zero_of hp3) ∈ hessR hp3 := by
  rw [hessRho2, commutatorElement_def]
  have h0 := hessT_mem_hessR hp3 0
  have hs := hessS0_mem_hessR hp3
  exact mul_mem (mul_mem (mul_mem h0 hs) (inv_mem h0)) (inv_mem hs)

theorem omegaGL_le_hessR (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hp7 : p ≠ 7) (hp11 : p ≠ 11) :
    omegaGL (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) ≤ hessR hp3 := by
  classical
  have hp5' : 5 ≤ p := by
    have := hp.out.two_le
    by_contra h
    interval_cases p <;> simp_all (config := { decide := true })
  set h3 := three_ne_zero_of (K := ZMod p) hp3 with hh3
  set R := hessR hp3 with hR
  set Ω := omegaGL (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) with hΩ
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 hp5'
    (M := (1 : Matrix (Fin 3) (Fin 3) (ZMod p))) Matrix.transpose_one (by simp)
  set f : (R ⊓ Ω : Subgroup _) →* PSL2MatrixGroup (ZMod p) :=
    e.toMonoidHom.comp (Subgroup.inclusion inf_le_right) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    exact Subgroup.inclusion_injective _ (e.injective hab)
  set H := f.range with hH
  set θ : (R ⊓ Ω : Subgroup _) →* H := f.rangeRestrict with hθ
  have hθinj : Function.Injective θ := by
    intro a b hab
    exact hfinj (congrArg Subtype.val hab)
  have hT1 : hessT 1 ∈ R ⊓ Ω := ⟨hessT_mem_hessR hp3 1, hessT_mem_omegaGL 1⟩
  have hρ : hessRho2 h3 ∈ R ⊓ Ω := ⟨hessRho2_mem_hessR hp3, hessRho2_mem_omegaGL h3⟩
  have hy : hessRho2y h3 ∈ R ⊓ Ω := by
    rw [hessRho2y]
    exact mul_mem (mul_mem hT1 hρ) hT1
  set ρ' : (R ⊓ Ω : Subgroup _) := ⟨hessRho2 h3, hρ⟩
  set y' : (R ⊓ Ω : Subgroup _) := ⟨hessRho2y h3, hy⟩
  set t' : (R ⊓ Ω : Subgroup _) := ⟨hessT 1, hT1⟩
  have hpow : ∀ k, 1 ≤ k → k ≤ 5 → (θ ρ') ^ k ≠ 1 := by
    intro k hk1 hk5 h
    have h' : θ (ρ' ^ k) = θ 1 := by rw [map_pow, h, map_one]
    have h'' := congrArg Subtype.val (hθinj h')
    exact hessRho2_pow_ne_one (K := ZMod p) hp2 hp3 hp5 hp7 hp11 hk1 hk5 h''
  have hord : ∀ z : H, (∀ k, 1 ≤ k → k ≤ 2 → z ^ k ≠ 1) → 2 < orderOf z := by
    intro z hz
    have hpos : 0 < orderOf z := orderOf_pos z
    by_contra hle
    push Not at hle
    have h1 := pow_orderOf_eq_one z
    exact hz (orderOf z) hpos hle h1
  have hyρ : θ y' = θ t' * θ ρ' * (θ t')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hx3 : 2 < orderOf (θ ρ') := hord _ (fun k hk1 hk2 => hpow k hk1 (by omega))
  have hy3 : 2 < orderOf (θ y') := by
    refine hord _ (fun k hk1 hk2 h => hpow k hk1 (by omega) ?_)
    rw [hyρ, conj_pow] at h
    have h' := congrArg (fun z => (θ t')⁻¹ * z * θ t') h
    simpa [mul_assoc] using h'

  have hxy : θ ρ' * θ y' ≠ θ y' * θ ρ' := by
    intro h
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg Subtype.val (hθinj h)
    exact hessRho2_mul_ne (K := ZMod p) hp2 hp3 h'
  have hcard : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  rcases dickson_large hcard H hx3 hy3 hxy (hpow 2 (by norm_num) (by norm_num))
      (hpow 3 (by norm_num) (by norm_num)) (hpow 4 (by norm_num) (by norm_num))
      (hpow 5 (by norm_num) (by norm_num)) (by
        intro N hN hNel hall
        have hc := hall (θ t') (θ ρ')
        have hexp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hNel.exponent_dvd_p
          ⟨_, hc⟩
        have hc' : (θ t' * θ ρ' * (θ t')⁻¹ * (θ ρ')⁻¹) ^ p = 1 := by
          have := congrArg Subtype.val hexp
          simpa using this
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow] at hc'
        have h' := congrArg Subtype.val (hθinj (hc'.trans (map_one θ).symm))
        exact hessRho2Comm_pow_ne_one (K := ZMod p) hp2 hp3 hp5 h') with
    ⟨m, hm0, hm1, ⟨eH⟩⟩ | ⟨m, hm0, hm2, -⟩
  ·
    have hm : m = 1 := Nat.dvd_one.mp hm1
    subst hm
    have hHcard : Nat.card H = Nat.card (PSL2MatrixGroup (ZMod p)) := by
      rw [Nat.card_congr eH.toEquiv,
        CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd (p := p) (f := 1)
          (by rw [GaloisField.card p 1 one_ne_zero]) hp2,
        CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hcard hp2]
    have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H hHcard
    intro g hg
    have hmem : e ⟨g, hg⟩ ∈ H := by rw [hHtop]; exact Subgroup.mem_top _
    obtain ⟨a, ha⟩ := hmem
    have ha' : (a : GL (Fin 3) (ZMod p)) = g := by
      have := e.injective ha
      exact congrArg Subtype.val this
    rw [← ha']
    exact a.2.1
  ·
    exfalso
    have := Nat.le_of_dvd one_pos hm2
    omega

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
