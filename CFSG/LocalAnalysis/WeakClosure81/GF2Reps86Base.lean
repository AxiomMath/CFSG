module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Ind
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleChief
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Seven
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Fpf
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8One
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv

theorem exists_isChiefFac_not_isCentralSec {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)} (hn : 5 ≤ n)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range) :
    ∃ Y₀ Y₁ : Subgroup V, IsChiefFac H Y₀ Y₁ ∧ ¬ IsCentralSec (altPre ψ) Y₀ Y₁ := by
  have hLV : ¬ (⊤ : Subgroup V) ≤ fixV (altPre ψ) := by
    intro h
    obtain ⟨x, hx, h3⟩ := exists_isThreeCycle_mem (by omega) (altPreEquiv hψ hA)
    apply ne_one_of_isThreeCycle (altPreEquiv hψ hA) hx h3
    ext v
    exact h (Subgroup.mem_top v) x hx
  have htop : H ≤ stabSub (⊤ : Subgroup V) := fun _ _ _ => by simp only [Subgroup.mem_top]
  obtain ⟨Y₀, Y₁, hY, -, hL⟩ := exists_isChiefFac_altPre hn hψ hA htop hLV
  exact ⟨Y₀, Y₁, hY, hL⟩

private theorem natVia_of_natSec_seven {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 7)}
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 7) ≤ ψ.range)
    {Y₀ Y₁ : Subgroup V} (hY : IsChiefFac H Y₀ Y₁) (hYL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁)
    (hN : NatSec ψ Y₀ Y₁) {t : ↥H} (ht : t ^ 2 = 1) (ht1 : ψ t ≠ 1) (hsw : ¬ (ψ t).IsSwap)
    (hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8) : NatVia ψ (commV H) := by
  have hperf := commutator_altPre_eq_top (by norm_num) hψ hA
  have h4Y := four_le_secIdx_seven hV hψ hA hY hYL ht ht1 hsw
  have h₀ : Y₀ ≤ fixV (altPre ψ) := by
    by_contra hc
    obtain ⟨Z₀, Z₁, hZ, hZY, hZL⟩ := exists_isChiefFac_altPre (by norm_num) hψ hA hY.stab₀ hc
    have h4Z := four_le_secIdx_seven hV hψ hA hZ hZL ht ht1 hsw
    have hprod := secIdx_mul_secIdx_le hZ.le hZY hY.le (hZ.stab₁ t.2) (hY.stab₁ t.2)
    have h16 := Nat.mul_le_mul h4Z h4Y
    omega
  have h₁ : IsCentralSec (altPre ψ) Y₁ ⊤ := by
    by_contra hc
    obtain ⟨Z₀, Z₁, hZ, hYZ, hZL⟩ :=
      exists_isChiefFac_above_of_perfect hperf altPre_le hY.stab₁ hc
    have h4Z := four_le_secIdx_seven hV hψ hA hZ hZL ht ht1 hsw
    have hprod := secIdx_mul_secIdx_le hY.le hYZ hZ.le (hY.stab₁ t.2) (hZ.stab₁ t.2)
    have h16 := Nat.mul_le_mul h4Y h4Z
    omega
  obtain ⟨π, hπ, hker, heq⟩ := hN
  have hshape : NatShape (altPre ψ).subtype
      ((alternatingGroup (Fin 7)).subtype.comp (altPreHom ψ)) :=
    ⟨Y₀, Y₁, hY.le, fun l v hv => h₀ hv l l.2, fun l v => h₁ l l.2 v (Subgroup.mem_top v), π,
      hπ, hker, fun l u v huv => heq (Subgroup.inclusion altPre_le l) u v huv⟩
  exact (natVia_commV_of_isAltNaturalSection (by norm_num) hψ hA
    (isAltNaturalSection_of_natShape (by norm_num) (altPre ψ) (altPreHom ψ)
      (altPreHom_surjective hA) hshape)).2

theorem t86_seven : T86 7 := by
  intro V _ _ hV H ψ hψ hA t ht ht1 hsw hidx
  obtain ⟨Y₀, Y₁, hY, hYL⟩ := exists_isChiefFac_not_isCentralSec (by norm_num) hψ hA
  obtain ⟨e, φ, hφe, hφ, hφr, hirr, -, hidxe, hnat⟩ :=
    exists_secTransport (by norm_num) hψ hA hY hYL
  have hV' : ∀ x : Sec Y₁ Y₀, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow, show w ^ 2 = 1 from Subtype.ext (by simpa using hV (w : V)),
        QuotientGroup.mk_one]
  have hA' : alternatingGroup (Fin 7) ≤ φ.range := by
    rw [hφr]
    exact hA
  have he2 : e t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hidx' := (hidxe t).trans_le ((secIdx_le hY.le (hY.stab₁ t.2)).trans hidx)
  rcases seven_irr hV' hφ hA' hirr he2 (by rwa [hφe]) (by rwa [hφe]) hidx' with hN | ⟨-, hr⟩
  · exact Or.inl (natVia_of_natSec_seven hV hψ hA hY hYL (hnat hN) ht ht1 hsw hidx)
  · exact Or.inr ⟨rfl, hφr.symm.trans hr⟩

theorem noFpf_ten : NoFpf 10 := by
  intro V _ _ hV H ψ hψ hA t ht htf hidx
  obtain ⟨Y₀, Y₁, hY, hYL⟩ := exists_isChiefFac_not_isCentralSec (by norm_num) hψ hA
  obtain ⟨e, φ, hφe, hφ, hφr, -, hfix, hidxe, -⟩ :=
    exists_secTransport (by norm_num) hψ hA hY hYL
  have hV' : ∀ x : Sec Y₁ Y₀, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow, show w ^ 2 = 1 from Subtype.ext (by simpa using hV (w : V)),
        QuotientGroup.mk_one]
  have hA' : alternatingGroup (Fin 10) ≤ φ.range := by
    rw [hφr]
    exact hA
  exact false_of_fpf_ten hV' hφ hA' hfix (by rw [← map_pow, ht, map_one])
    (fun i => by rw [hφe]; exact htf i)
    ((hidxe t).trans_le ((secIdx_le hY.le (hY.stab₁ t.2)).trans hidx))

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
