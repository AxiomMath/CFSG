module

public import CFSG.LocalAnalysis.WeakClosure81.W183K1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem exists_simple_subnormal_of_section (hM : OddMultiplier186Triv) {Y : Type} [Group Y]
    [Finite Y] {Kk P Lc : Subgroup Y} (hKP : Kk ≤ P)
    (hKc : Kk ≤ Subgroup.centralizer (P : Set Y)) (hodd : Odd (Nat.card ↥Kk)) (hLP : Lc ≤ P)
    (hLsub : Lc.IsSubnormal) {S : Type} [Group S] [IsSimpleGroup S]
    (hSnc : ∃ u v : S, u * v ≠ v * u) (hS : Shape186OddTriv S) (φ : ↥Lc →* S)
    (hφs : Function.Surjective φ) (hφk : ∀ k : ↥Lc, φ k = 1 ↔ (k : Y) ∈ Kk) :
    ∃ Λ : Subgroup Y, Λ.IsSubnormal ∧ Λ ≤ Lc ∧ Λ ⊓ Kk = ⊥ ∧ Nonempty (↥Λ ≃* S) := by
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition
    (derivedSeries_antitone (G := ↥Lc))
  let Λ₀ : Subgroup ↥Lc := derivedSeries ↥Lc n
  let Λ : Subgroup Y := Λ₀.map Lc.subtype
  have hstab : derivedSeries ↥Lc (n + 1) = derivedSeries ↥Lc n :=
    (hn (n + 1) (Nat.le_succ n)).symm
  have hΛ₀comm : ⁅Λ₀, Λ₀⁆ = Λ₀ := (derivedSeries_succ ↥Lc n).symm.trans hstab
  have hΛL : Λ ≤ Lc := Subgroup.map_subtype_le Λ₀
  have hΛsub : Λ.subgroupOf Lc = Λ₀ :=
    Subgroup.comap_map_eq_self_of_injective Lc.subtype_injective Λ₀
  have hΛsubn : Λ.IsSubnormal :=
    Subgroup.IsSubnormal.trans hΛL
      (by rw [hΛsub]; exact (derivedSeries_normal ↥Lc n).isSubnormal) hLsub
  have hSperf : Group.IsPerfect S :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun h => by
      obtain ⟨u, v, huv⟩ := hSnc
      exact huv (h.is_comm.comm u v)
  have hmapderiv : ∀ k, (derivedSeries ↥Lc k).map φ = ⊤ := by
    intro k
    induction k with
    | zero => rw [derivedSeries_zero, Subgroup.map_top_of_surjective φ hφs]
    | succ k ih =>
        rw [derivedSeries_succ, Subgroup.map_commutator, ih]
        rw [← _root_.commutator_def]
        exact hSperf.commutator_eq_top
  have hmap : Λ₀.map φ = ⊤ := hmapderiv n
  haveI hΛ₀perf : Group.IsPerfect ↥Λ₀ := Subgroup.isPerfect_iff.mpr hΛ₀comm
  let eΛ : ↥Λ₀ ≃* ↥Λ := Subgroup.equivMapOfInjective Λ₀ Lc.subtype Lc.subtype_injective
  have hΛperf : Group.IsPerfect ↥Λ :=
    Group.IsPerfect.ofSurjective (f := eΛ.toMonoidHom) eΛ.surjective
  have hperf : ⁅(⊤ : Subgroup ↥Λ), (⊤ : Subgroup ↥Λ)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact hΛperf.commutator_eq_top
  let ψ : ↥Λ →* S := φ.comp (Subgroup.inclusion hΛL)
  let Z : Subgroup ↥Λ := Kk.subgroupOf Λ
  have hψs : Function.Surjective ψ := by
    intro s
    have hs : s ∈ Λ₀.map φ := by rw [hmap]; exact Subgroup.mem_top s
    obtain ⟨x, hx, hφx⟩ := Subgroup.mem_map.mp hs
    let y : ↥Λ := ⟨(x : Y), Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩
    refine ⟨y, ?_⟩
    have hy : (Subgroup.inclusion hΛL y : ↥Lc) = x := Subtype.ext rfl
    change φ (Subgroup.inclusion hΛL y) = s
    rw [hy, hφx]
  have hψk : ∀ y : ↥Λ, ψ y = 1 ↔ (y : Y) ∈ Kk := fun y =>
    hφk (Subgroup.inclusion hΛL y)
  have hψker : ψ.ker = Z := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hψk y
  have hZcent : Z ≤ Subgroup.center ↥Λ := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    change ((w : ↥Λ) : Y) * ((z : ↥Λ) : Y) = ((z : ↥Λ) : Y) * ((w : ↥Λ) : Y)
    exact Subgroup.mem_centralizer_iff.mp (hKc (Subgroup.mem_subgroupOf.mp hz))
      ((w : ↥Λ) : Y) (hLP (hΛL w.2))
  haveI hZnormal : Z.Normal := Subgroup.normal_of_le_center hZcent
  have hZodd : Odd (Nat.card ↥Z) := by
    have hZmap : Z.map Λ.subtype = Kk ⊓ Λ := Subgroup.subgroupOf_map_subtype Kk Λ
    have hcard : Nat.card ↥Z = Nat.card ↥(Kk ⊓ Λ) := by
      rw [← hZmap]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective Z Λ.subtype Λ.subtype_injective).toEquiv
    rw [hcard]
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hiso : Nonempty ((↥Λ ⧸ Z) ≃* S) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩
  have hZbot : Z = ⊥ := hM S hS ↥Λ Z hZcent hZodd hperf hiso
  have hψinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).mp (by rw [hψker, hZbot])
  refine ⟨Λ, hΛsubn, hΛL, ?_, ⟨MulEquiv.ofBijective ψ ⟨hψinj, hψs⟩⟩⟩
  have hdisj : Disjoint Kk Λ := Subgroup.subgroupOf_eq_bot.mp hZbot
  rw [inf_comm]
  exact disjoint_iff.mp hdisj

end CFSG.LocalAnalysis.WeakClosure81

end
