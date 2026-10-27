module

public import CFSG.GroupTheory.SylowPQMaximal.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35G2

theorem isPGroup_of_sylow_le_of_normal_mulAut {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (P : Sylow p G) (H : Subgroup G) (hPH : (P : Subgroup G) ≤ H)
    (hH : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q} H)
    (hE : ∀ E : Subgroup P, E.Normal → ¬ q ∣ Nat.card (MulAut E))
    (hU : ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup q U →
      ¬ (P : Subgroup G) ≤ Subgroup.normalizer (U : Set G)) :
    IsPGroup p H := by
  classical
  have hpi := (CFSG.GroupTheory.isPiSubgroup_pair_iff (p := p) (q := q) (Y := G)
    (H := H)).mp hH
  have hdvd : Nat.card ↥H ∣ p ^ Nat.card ↥H * q ^ Nat.card ↥H := by
    have hsubset : (Nat.card ↥H).primeFactors ⊆ (p * q).primeFactors := by
      intro r hr
      obtain ⟨hrp, hrdvd, -⟩ := Nat.mem_primeFactors.mp hr
      rcases hpi r hrp hrdvd with h | h
      · exact Nat.mem_primeFactors.mpr
          ⟨hrp, h ▸ dvd_mul_right p q, (mul_pos (Fact.out : p.Prime).pos
            (Fact.out : q.Prime).pos).ne'⟩
      · exact Nat.mem_primeFactors.mpr
          ⟨hrp, h ▸ dvd_mul_left q p, (mul_pos (Fact.out : p.Prime).pos
            (Fact.out : q.Prime).pos).ne'⟩
    calc
      Nat.card ↥H ∣ (p * q) ^ Nat.card ↥H :=
        (Nat.dvd_pow_self_iff Nat.card_pos.ne'
          (mul_pos (Fact.out : p.Prime).pos (Fact.out : q.Prime).pos).ne').mpr hsubset
      _ = p ^ Nat.card ↥H * q ^ Nat.card ↥H := mul_pow p q _
  have hsolv : Group.IsSolvable ↥H :=
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow (a := Nat.card ↥H)
      (b := Nat.card ↥H) (Fact.out : p.Prime) (Fact.out : q.Prime) hdvd
  have hqcore : pCore q ↥H = ⊥ := by
    let U : Subgroup G := (pCore q ↥H).map H.subtype
    have hUq : IsPGroup q U := (pCore_isPGroup (p := q) (G := ↥H)).map H.subtype
    have hPU : (P : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
      have hle := Subgroup.le_normalizer_map (f := H.subtype) (H := pCore q ↥H)
      intro x hx
      refine hle (Subgroup.mem_map.mpr ⟨⟨x, hPH hx⟩, ?_, rfl⟩)
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    have hUbot : U = ⊥ := by
      by_contra hne
      exact hU U hne hUq hPU
    exact (Subgroup.map_eq_bot_iff_of_injective (H := pCore q ↥H)
      (f := H.subtype) H.subtype_injective).mp hUbot
  have hFp : IsPGroup p (fittingSubgroup ↥H) := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine Sylow.iSup_of_normal (fun r : (Nat.card ↥H).primeFactors.attach =>
      pCore r.1.1 ↥H) ?_
    intro r
    have hr : r.1.1 = p ∨ r.1.1 = q :=
      hpi r.1.1 (Nat.prime_of_mem_primeFactors r.1.2)
        (Nat.dvd_of_mem_primeFactors r.1.2)
    rcases hr with hp | hq
    · have hpc : pCore r.1.1 ↥H = pCore p ↥H := by rw [hp]
      rw [hpc]
      exact pCore_isPGroup (p := p) (G := ↥H)
    · rw [hq, hqcore]
      exact IsPGroup.of_bot
  let F : Subgroup ↥H := fittingSubgroup ↥H
  have hFp' : IsPGroup p F := hFp
  have hF_le_sylow : F ≤ (P.subtype hPH : Subgroup ↥H) :=
    IsPGroup.le_sylow_of_normal hFp' (P.subtype hPH)
  let Psub : Subgroup ↥H := (P : Subgroup G).subgroupOf H
  have hF_le : F ≤ Psub := by
    simpa [Psub] using hF_le_sylow
  let e : Psub ≃* P := Subgroup.subgroupOfEquivOfLe hPH
  let Fsub : Subgroup Psub := F.subgroupOf Psub
  have hFsub_normal : Fsub.Normal := by
    have : F.Normal := by
      dsimp [F]
      infer_instance
    exact Subgroup.Normal.subgroupOf this Psub
  let E : Subgroup P := Fsub.map e.toMonoidHom
  have hE_normal : E.Normal := hFsub_normal.map e.toMonoidHom e.surjective
  have hE_aut : ¬ q ∣ Nat.card (MulAut E) := hE E hE_normal
  have hEq : MulAut E ≃* MulAut F :=
    MulAut.congr ((MulEquiv.subgroupMap e Fsub).symm.trans
      (Subgroup.subgroupOfEquivOfLe hF_le))
  have hqAutF : ¬ q ∣ Nat.card (MulAut F) := fun h =>
    hE_aut (by rwa [← Nat.card_congr hEq.toEquiv] at h)
  have hCF_le : Subgroup.centralizer (F : Set ↥H) ≤ F := by
    have := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
      (G := ↥H) hsolv
    simpa [F] using this
  have hF_normal : F.Normal := by
    dsimp [F]
    infer_instance
  let φ : ↥H →* MulAut F := MulAut.conjNormal (H := F)
  have hker_le : φ.ker ≤ F := by
    intro x hx
    refine hCF_le ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx1 : φ x = 1 := hx
    have hfix : φ x ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hx1]; rfl
    have hconj : x * y * x⁻¹ = y := by
      simpa [φ, MulAut.conjNormal_apply] using congrArg Subtype.val hfix
    calc
      y * x = x * y * x⁻¹ * x := by rw [hconj]
      _ = x * y := by group
  obtain ⟨n, hn⟩ := (hFp'.to_le hker_le).exists_card_eq
  have hqker : ¬ q ∣ Nat.card φ.ker := by
    intro h
    rw [hn] at h
    exact hpq.symm ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : p.Prime)).mp ((Fact.out : q.Prime).dvd_of_dvd_pow h))
  have hqrange : ¬ q ∣ Nat.card φ.range := fun h =>
    hqAutF (h.trans (Subgroup.card_subgroup_dvd_card φ.range))
  have hqH : ¬ q ∣ Nat.card ↥H := by
    intro h
    rw [← Subgroup.card_ker_mul_card_range φ] at h
    rcases (Fact.out : q.Prime).dvd_mul.mp h with h | h
    exacts [hqker h, hqrange h]
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hr hdvd => ?_)
  rcases hpi _ hr hdvd with h | h
  · exact h
  · exact absurd (h ▸ hdvd) hqH

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35G2
