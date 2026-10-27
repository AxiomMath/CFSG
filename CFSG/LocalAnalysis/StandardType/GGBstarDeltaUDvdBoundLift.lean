module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame

public section

namespace CFSG.StandardType

namespace TableBUDL

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU TableBUI TableBUD
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)
open CFSG.LieType.Steinberg (commutatorElement_mul_mul_of_mem_center)
open scoped commutatorElement

section Abstract

variable {L : Type*} [Group L] {N : Subgroup L} [N.Normal]

theorem exists_lift_pow_eq_one {M p : ℕ} (hN : ∀ z ∈ N, z ^ 2 ^ M = 1) (hp : Nat.Coprime 2 p)
    (x : L ⧸ N) (hx : x ^ p = 1) : ∃ e : L, e ^ p = 1 ∧ (e : L ⧸ N) = x := by
  obtain ⟨e₀, rfl⟩ := QuotientGroup.mk_surjective x
  have hcop : Nat.Coprime (2 ^ M) (orderOf (e₀ : L ⧸ N)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx) (Nat.Coprime.pow_left M hp)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have h1 : e₀ ^ p ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hx
  refine ⟨e₀ ^ (2 ^ M * m), ?_, ?_⟩
  · rw [← pow_mul, show 2 ^ M * m * p = p * 2 ^ M * m by ring, pow_mul, pow_mul, hN _ h1,
      one_pow]
  · rw [QuotientGroup.mk_pow, pow_mul]
    exact hm

omit [N.Normal] in
theorem eq_of_lift_pow_eq_one (hNc : N ≤ Subgroup.center L) {M p : ℕ}
    (hN : ∀ z ∈ N, z ^ 2 ^ M = 1) (hp : Nat.Coprime 2 p) {e e' : L} (he : e ^ p = 1)
    (he' : e' ^ p = 1) (h : (e : L ⧸ N) = e') : e = e' := by
  have hz : e⁻¹ * e' ∈ N := QuotientGroup.eq.mp h
  have hc : Commute e (e⁻¹ * e') := Subgroup.mem_center_iff.mp (hNc hz) e
  have hzp : (e⁻¹ * e') ^ p = 1 := by
    have h2 := hc.mul_pow p
    rw [mul_inv_cancel_left, he, he', one_mul] at h2
    exact h2.symm
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzp) (orderOf_dvd_of_pow_eq_one (hN _ hz))
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right M hp.symm), Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact inv_mul_eq_one.mp h1

end Abstract

theorem eq_of_mul_inv_mem_center {H M : Type*} [Group H] [Group M] {α : H →* M}
    (hα : Function.Surjective α) (hM : commutator M = ⊤) {f g : H →* M}
    (hfg : ∀ s, f s * (g s)⁻¹ ∈ Subgroup.center M) (hker : ∀ s, α s = 1 → f s = g s) (s : H) :
    f s = g s := by
  have hcomm : commutator H ≤ f.eqLocus g := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    change f ⁅x, y⁆ = g ⁅x, y⁆
    rw [map_commutatorElement, map_commutatorElement]
    have e1 : f x = (f x * (g x)⁻¹) * g x := by group
    have e2 : f y = (f y * (g y)⁻¹) * g y := by group
    rw [e1, e2, commutatorElement_mul_mul_of_mem_center (hfg x) (hfg y)]
  have h1 : α s ∈ (commutator H).map α := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hα, ← commutator_def, hM]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcs⟩ := h1
  have h2 : α (c⁻¹ * s) = 1 := by rw [map_mul, map_inv, hcs, inv_mul_cancel]
  have h4 : f c = g c := hcomm hc
  have h5 : f (c⁻¹ * s) = g (c⁻¹ * s) := hker _ h2
  calc f s = f (c * (c⁻¹ * s)) := by rw [mul_inv_cancel_left]
    _ = f c * f (c⁻¹ * s) := map_mul f c _
    _ = g c * g (c⁻¹ * s) := by rw [h4, h5]
    _ = g (c * (c⁻¹ * s)) := (map_mul g c _).symm
    _ = g s := by rw [mul_inv_cancel_left]

theorem descAut_conj {L R : Type} [Group L] [Group R] {ψ : L →* R}
    (hψ : Function.Surjective ψ) (hZ : ψ.ker = Subgroup.center L) (l : L) :
    BstarDesc.descAut hψ hZ (MulAut.conj l) = MulAut.conj (ψ l) := by
  ext r
  obtain ⟨m, rfl⟩ := hψ r
  rw [BstarDesc.descAut_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

section Frame

variable {K : Type} [Field K] {d n : ℕ} {h : UnitaryFieldData 2 n K} {Q : GL (Fin d) K}
  {hQ : Q ∈ primeFormUnitary h (idGram K d)}

theorem frameAct_conj_frameMk {s : ↥(unitarySU 2 n K d)} {τ : Fin d → Kˣ}
    (hs : (s : GL (Fin d) K) = diagHom d τ) :
    FrameAct h Q hQ (MulAut.conj (frameMk h Q hQ s)) τ := by
  refine frameAct_of fun u v huv => ?_
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [huv, ← hs, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem frameAct_pow {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    {σ : Fin d → Kˣ} (he : FrameAct h Q hQ e σ) (hσ : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1)
    (m : ℕ) : FrameAct h Q hQ (e ^ m) (σ ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    exact frameAct_one
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul he hσ

end Frame

section Lift

variable {K : Type} [Field K] [Finite K] {n d p : ℕ}

theorem exists_lift_fix
    (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Type} [Group L] [Finite L]
    {ψ : L →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) (Q : GL (Fin d) K)
    (hQ : Q ∈ primeFormUnitary h (idGram K d)) (s : ↥(unitarySU 2 n K d)) (hs : s ^ p = 1) :
    ∃ e : L, e ^ p = 1 ∧ ψ e = frameMk h Q hQ s ∧
      ∀ (a : MulAut L) (b : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
        (B : GL (Fin d) K), B ∈ primeFormUnitary h (idGram K d) → (∀ l, b (ψ l) = ψ (a l)) →
        IsSemilin (frameMk h Q hQ) b B 1 → B * (s : GL (Fin d) K) = s * B → a e = e := by
  classical
  have := Fact.mk hp
  have : CharP K 2 := h.charP
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have hZ : ψ.ker = Subgroup.center L :=
    BstarDesc.ker_eq_center hψ hker (TableBUE.center_proj_eq_bot hK hd hdq)
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* LargeEvenSUGroup (Fin d) K (2 ^ n)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSUGroup (Fin d) K (2 ^ n) →* E, ∀ h, π (s h) = h := by
    intro E _ _ π hπ hcen hC
    by_cases he : Even d
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
        (F := K) (p := 2) (f := n) hK he (by omega) E π hπ hcen hC
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := n) hK hn hd he hdq hπ hcen
  have : Finite (LargeEvenSUGroup (Fin d) K (2 ^ n)) := Finite.of_injective
    (fun x : LargeEvenSUGroup (Fin d) K (2 ^ n) =>
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  set N := TableBU.twoPartOf ψ.ker hker (Nat.card L)
  have hNk : N ≤ ψ.ker := TableBU.twoPartOf_le _ hker _
  have hNc : N ≤ Subgroup.center L := hNk.trans hker
  have hN2 : ∀ z ∈ N, z ^ 2 ^ Nat.card L = 1 := fun z hz => hz.2
  set π : L →* L ⧸ N := QuotientGroup.mk' N
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set ψb : L ⧸ N →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    QuotientGroup.lift N ψ hNk
  have hψbπ : ∀ l, ψb (π l) = ψ l := fun l => QuotientGroup.lift_mk N hNk l
  have hψbs : Function.Surjective ψb := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨π l, hψbπ l⟩
  have hψbc : ψb.ker ≤ Subgroup.center (L ⧸ N) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hπs y
    have hz : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψbπ]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := hπs w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hz) v]
  have hψbodd : ∀ y ∈ ψb.ker, y ^ 2 = 1 → y = 1 := fun y hy hy2 =>
    TableBU.sq_eq_one_ker_lift hker y hy hy2
  have hperfb : commutator (L ⧸ N) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := hπs y
    have hl : l ∈ commutator L := by rw [hperf]; exact Subgroup.mem_top l
    have h1 := Subgroup.mem_map_of_mem π hl
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπs, ← commutator_def] at h1
  obtain ⟨α, hα, hαs⟩ := StdSubRestU.exists_surjective_of_oddKernel
    (q := LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (QuotientGroup.mk'_surjective _) hsplit hψbs hψbc hperfb hψbodd
  set α' : ↥(unitarySU 2 n K d) →* L ⧸ N :=
    α.comp (TableBUE.conjSU h Q hQ).symm.toMonoidHom
  have hα'ψ : ∀ u, ψb (α' u) = frameMk h Q hQ u := fun u => hα _
  have hα's : Function.Surjective α' := hαs.comp (TableBUE.conjSU h Q hQ).symm.surjective
  obtain ⟨e, hep, hex⟩ := exists_lift_pow_eq_one hN2 hcop (α' s) (by rw [← map_pow, hs, map_one])
  have hπe : π e = α' s := hex
  refine ⟨e, hep, by rw [← hψbπ, hπe, hα'ψ], ?_⟩
  intro a b B hB hab hsl hBs
  have haN : N ≤ N.comap a.toMonoidHom := by
    intro z hz
    refine ⟨?_, ?_⟩
    · show a z ∈ ψ.ker
      rw [hZ]
      exact BstarDesc.mulAut_mem_center a (hZ ▸ hz.1)
    · show a z ^ 2 ^ Nat.card L = 1
      rw [← map_pow, hz.2, map_one]
  set β : L ⧸ N →* L ⧸ N := QuotientGroup.map N N a.toMonoidHom haN
  have hβπ : ∀ l, β (π l) = π (a l) := fun l => rfl
  have hψbβ : ∀ y, ψb (β y) = b (ψb y) := by
    intro y
    obtain ⟨l, rfl⟩ := hπs y
    rw [hβπ, hψbπ, hψbπ, hab]
  set c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d) :=
    (TableBUE.conjSU h B hB).symm.toMonoidHom
  have hcv : ∀ u, ((c u : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = B * u * B⁻¹ := fun u => rfl
  have hrig : ∀ u, β (α' u) = α' (c u) := by
    refine eq_of_mul_inv_mem_center (f := β.comp α') (g := α'.comp c) hα's hperfb ?_ ?_
    · intro u
      apply hψbc
      rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hψbβ,
        hα'ψ u, hα'ψ (c u), hsl u (c u) (by rw [map_one, MulAut.one_apply]; exact hcv u),
        mul_inv_cancel]
    · intro u hu
      have h1 : frameMk h Q hQ u = 1 := by rw [← hα'ψ u, hu, map_one]
      obtain ⟨z, hz⟩ := exists_scalar_of_frameMk_eq h Q hQ (u := 1) (v := u)
        (by rw [map_one, h1])
      have hcen := Subgroup.mem_center_iff.mp
        (TableB.scalars_le_center (ι := Fin d) (K := K) ⟨z, rfl⟩)
      have hcu : c u = u := by
        apply Subtype.ext
        rw [hcv, hz, Subgroup.coe_one, mul_one, hcen B, mul_inv_cancel_right]
      show β (α' u) = α' (c u)
      rw [hcu, hu, map_one]
  have hβx : β (α' s) = α' s := by
    rw [hrig s]
    congr 1
    apply Subtype.ext
    rw [hcv, hBs, mul_inv_cancel_right]
  refine eq_of_lift_pow_eq_one hNc hN2 hcop (by rw [← map_pow, hep, map_one]) hep ?_
  change π (a e) = π e
  rw [← hβπ, hπe, hβx]

end Lift

end TableBUDL

end CFSG.StandardType
