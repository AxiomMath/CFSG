module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDeltaCent
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDvdRNode
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUDvdBound
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwoLift
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperDefs
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUnitary

public section

namespace CFSG.StandardType.IOneUDelta

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.SectionRank.OddCover
  CFSG.StandardType.TableBUE CFSG.StandardType.InndiagSU SmallU
open CFSG.StandardType.IOneUDvdR

variable {K : Type} [Field K] {n d : ℕ}

theorem diagHom_comm' {d : ℕ} (σ τ : Fin d → Kˣ) :
    diagHom d σ * diagHom d τ = diagHom d τ * diagHom d σ := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem pow_ratio_one {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hM : UnitTB.Model φ) (hd3 : 3 ≤ d) {p : ℕ} {A : Subgroup (MulAut L')}
    (hA : CFSG.Open.IsElemAbelian p A) {a : MulAut L'} (ha : a ∈ A) (s0 : Fin d)
    {σ : Fin d → Kˣ} (hσ : ActsU φ a σ) (hσ0 : σ s0 = 1) (k : Fin d) : σ k ^ p = 1 := by
  have hap : a ^ p = 1 := hA.2 a ha
  have := ActsU.pow_ratio hM hd3 hσ hap k s0
  rw [hσ0, inv_one, mul_one] at this
  exact this

theorem inner_of_prod_one [Finite K] {L' : Type} [Group L'] [Finite L'] (h : UnitaryFieldData 2 n K)
    {p : ℕ} (hpq : p ∣ 2 ^ n + 1) {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ)
    (hd3 : 3 ≤ d) {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian p A) {a : MulAut L'}
    (ha : a ∈ A) (s0 : Fin d) {σ : Fin d → Kˣ} (hσ : ActsU φ a σ) (hσ0 : σ s0 = 1)
    (hprod : ∏ k, σ k = 1) : ∃ e : L', e ^ p = 1 ∧ MulAut.conj e = a := by
  have hσp : ∀ k, σ k ^ p = 1 := fun k => pow_ratio_one hM hd3 hA ha s0 hσ hσ0 k
  obtain ⟨hD, hact⟩ := hσ
  let sσ : ↥(unitarySU 2 n K d) := ⟨diagHom d σ, TableBUDL.diagHom_mem_unitarySU h hpq hσp hprod⟩
  have hsp : sσ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact TableBUDL.diagHom_pow_eq_one hσp)
  refine ⟨φ sσ, by rw [← map_pow, hsp, map_one], ?_⟩
  apply MulEquiv.ext
  intro l
  obtain ⟨s, rfl⟩ := hM.surj l
  have hs : LineU.conjN (diagHom d σ) hD s = sσ * s * sσ⁻¹ := rfl
  rw [MulAut.conj_apply, hact s, hs, map_mul, map_mul, map_inv]

theorem normalizer_of_mem_subgroup {G : Type} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact H.mul_mem (H.mul_mem hx hg) (H.inv_mem hx)
  · intro hg
    have := H.mul_mem (H.mul_mem (H.inv_mem hx) hg) hx
    have e : x⁻¹ * (x * g * x⁻¹) * x = g := by group
    rw [e] at this
    exact this

theorem lift_of_prod_one [Finite K] {L' : Type} [Group L'] [Finite L'] (h : UnitaryFieldData 2 n K)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {φ : ↥(unitarySU 2 n K d) →* L'}
    (hM : UnitTB.Model φ) (hd3 : 3 ≤ d) {A : Subgroup (MulAut L')}
    (hA : CFSG.Open.IsElemAbelian p A)
    (hadm : GGDeltaAdm p L' A) (s0 : Fin d) (ν : A →* (Fin d → Kˣ))
    (hν : ∀ a : A, ActsU φ (a : MulAut L') (ν a) ∧ ν a s0 = 1)
    {τ : Fin d → Kˣ} (hτp : ∀ k, τ k ^ p = 1) (hprod : ∏ k, τ k = 1) (hτs : τ s0 = 1) :
    ∃ x : A, ν x = τ := by
  let sτ : ↥(unitarySU 2 n K d) := ⟨diagHom d τ, TableBUDL.diagHom_mem_unitarySU h hpq hτp hprod⟩
  have hsp : sτ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact TableBUDL.diagHom_pow_eq_one hτp)
  have he : (φ sτ) ^ p = 1 := by rw [← map_pow, hsp, map_one]
  have hfix : ∀ a ∈ A, a (φ sτ) = φ sτ := by
    intro a ha
    obtain ⟨hD, hact⟩ := (hν ⟨a, ha⟩).1
    calc a (φ sτ) = φ (LineU.conjN (diagHom d (ν ⟨a, ha⟩)) hD sτ) := hact sτ
      _ = φ sτ := by
        congr 1
        apply Subtype.ext
        show diagHom d (ν ⟨a, ha⟩) * diagHom d τ * (diagHom d (ν ⟨a, ha⟩))⁻¹ = diagHom d τ
        rw [diagHom_comm' (ν ⟨a, ha⟩) τ, mul_inv_cancel_right]
  have hconj : MulAut.conj (φ sτ) ∈ A := hadm.1 (φ sτ) he hfix
  have hDτ : diagHom d τ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    normalizer_of_mem_subgroup (TableBUDL.diagHom_mem_unitarySU h hpq hτp hprod)
  have hact : ActsU φ (MulAut.conj (φ sτ)) τ := by
    refine ⟨hDτ, fun s => ?_⟩
    have hs : LineU.conjN (diagHom d τ) hDτ s = sτ * s * sτ⁻¹ := rfl
    rw [MulAut.conj_apply, hs, map_mul, map_mul, map_inv]
  refine ⟨⟨MulAut.conj (φ sτ), hconj⟩, funext fun i => ?_⟩
  have hr := ActsU.ratio_eq' hM hd3 (hν ⟨MulAut.conj (φ sτ), hconj⟩).1 hact i s0
  rw [(hν ⟨MulAut.conj (φ sτ), hconj⟩).2, hτs, inv_one, mul_one, mul_one] at hr
  exact hr

theorem node_exists [Finite K] {L' : Type} [Group L'] [Finite L'] (h : UnitaryFieldData 2 n K)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {φ : ↥(unitarySU 2 n K d) →* L'}
    (hM : UnitTB.Model φ) (hd3 : 3 ≤ d) {A : Subgroup (MulAut L')}
    (hA : CFSG.Open.IsElemAbelian p A)
    (hadm : GGDeltaAdm p L' A) (s0 : Fin d) (ν : A →* (Fin d → Kˣ))
    (hν : ∀ a : A, ActsU φ (a : MulAut L') (ν a) ∧ ν a s0 = 1) :
    ∃ δ : Kˣ, δ ^ p = 1 ∧ δ ≠ 1 ∧ ∀ c : Fin d, c ≠ s0 → ∃ x : A, ν x = nodeDiag c δ := by
  have hA0 : ∃ a0 : A, ∏ k, ν a0 k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hinn : ∀ a ∈ A, ∃ e : L', e ^ p = 1 ∧ MulAut.conj e = a := fun a ha =>
      inner_of_prod_one h hpq hM hd3 hA ha s0 (hν ⟨a, ha⟩).1 (hν ⟨a, ha⟩).2 (hcon ⟨a, ha⟩)
    rcases hadm.2 with ⟨⟨a, ha, hna⟩, -⟩ | ⟨-, -, a, ha, hna⟩
    · obtain ⟨e, -, rfl⟩ := hinn a ha
      exact hna ⟨e, rfl⟩
    · obtain ⟨e, he, rfl⟩ := hinn a ha
      rcases hna with hna | hna
      · exact hna ⟨e, rfl⟩
      · have h1 := hna e rfl
        rw [he, orderOf_one, Nat.dvd_one] at h1
        exact hp.one_lt.ne' h1
  obtain ⟨a0, ha0⟩ := hA0
  have hw0 : ∀ k, ν a0 k ^ p = 1 := fun k =>
    pow_ratio_one hM hd3 hA a0.2 s0 (hν a0).1 (hν a0).2 k
  set δ : Kˣ := ∏ k, ν a0 k with hδ
  have hδp : δ ^ p = 1 := by
    rw [hδ, ← Finset.prod_pow]
    exact Finset.prod_eq_one (fun k _ => hw0 k)
  refine ⟨δ, hδp, ha0, fun c hc => ?_⟩
  set τ' : Fin d → Kˣ := fun k => nodeDiag c δ k * (ν a0 k)⁻¹ with hτ'
  have hτ'p : ∀ k, τ' k ^ p = 1 := by
    intro k
    have hnd : nodeDiag c δ k ^ p = 1 := by
      unfold nodeDiag
      split_ifs
      · exact hδp
      · exact one_pow p
    simp only [hτ']
    rw [mul_pow, inv_pow, hw0 k, inv_one, mul_one, hnd]
  have hτ's : τ' s0 = 1 := by
    simp [hτ', nodeDiag, Ne.symm hc, (hν a0).2]
  have hτ'prod : ∏ k, τ' k = 1 := by
    have hnd : ∏ k, nodeDiag c δ k = δ := by simp [nodeDiag]
    simp only [hτ']
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hnd, ← hδ, mul_inv_cancel]
  obtain ⟨x', hx'⟩ := lift_of_prod_one h hp hpq hM hd3 hA hadm s0 ν hν hτ'p hτ'prod hτ's
  refine ⟨x' * a0, ?_⟩
  rw [map_mul, hx']
  funext k
  simp [hτ']

theorem exists_beta [Finite K] {L' : Type} [Group L'] (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 5 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2))
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {φ : ↥(unitarySU 2 n K d) →* L'}
    (hφ : Function.Surjective φ) :
    ∃ β : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      ∀ u : ↥(unitarySU 2 n K d), β (InndiagSU.projU n d K u) = ψ (φ u) := by
  classical
  have hcen := TableBUE.center_proj_eq_bot hK (by omega : 3 ≤ d) hdq
  let θ : ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    ψ.comp φ
  let N : Subgroup ↥(unitarySU 2 n K d) :=
    (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d)
  have hN : N ≤ θ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxc : (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      have hx' := hx
      rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at hx'
      exact hx'
    have hφc : φ x ∈ Subgroup.center L' := by
      rw [Subgroup.mem_center_iff]
      intro l
      obtain ⟨s, rfl⟩ := hφ l
      have hcs := Subgroup.mem_center_iff.mp hxc (s : GL (Fin d) K)
      have : x * s = s * x := Subtype.ext hcs.symm
      rw [← map_mul, ← map_mul, this]
    have hψc : ψ (φ x) ∈ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      have := Subgroup.mem_center_iff.mp hφc l
      rw [← map_mul, ← map_mul, this]
    rw [hcen, Subgroup.mem_bot] at hψc
    exact hψc
  let β0 : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    QuotientGroup.lift N θ hN
  have hβ0 : ∀ u : ↥(unitarySU 2 n K d), β0 (InndiagSU.projU n d K u) = ψ (φ u) := fun u =>
    QuotientGroup.lift_mk _ _ _
  have hsurj : Function.Surjective β0 := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    obtain ⟨s, rfl⟩ := hφ l
    exact ⟨InndiagSU.projU n d K s, hβ0 s⟩
  have hinj : Function.Injective β0 := Finite.injective_iff_surjective.mpr hsurj
  exact ⟨MulEquiv.ofBijective β0 ⟨hinj, hsurj⟩, hβ0⟩

theorem iter_conj {R : Type} [Group R] {n d : ℕ} {K : Type} [Field K]
    (θ : ↥(unitarySU 2 n K d) →* R) (α : MulAut R) {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hact : ∀ u : ↥(unitarySU 2 n K d), α (θ u) = θ (LineU.conjN D hD u)) (m : ℕ) :
    ∀ u : ↥(unitarySU 2 n K d), ∃ v : ↥(unitarySU 2 n K d),
      (v : GL (Fin d) K) = D ^ m * (u : GL (Fin d) K) * (D ^ m)⁻¹ ∧ (α ^ m) (θ u) = θ v := by
  induction m with
  | zero =>
    intro u
    exact ⟨u, by simp, by simp⟩
  | succ m ih =>
    intro u
    obtain ⟨w, hw1, hw2⟩ := ih (LineU.conjN D hD u)
    refine ⟨w, ?_, ?_⟩
    · rw [hw1, pow_succ]
      simp only [LineU.conjN, _root_.mul_inv_rev, mul_assoc]
    · rw [pow_succ, MulAut.mul_apply, hact u, hw2]

theorem centralizer_L [Finite K] {L' : Type} [Group L'] [Finite L'] (h : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (c : Fin d) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ)
    {a : MulAut L'} {ζ : Kˣ} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (ha : ActsU φ a (nodeDiag c ζ))
    {a' : MulAut L'} (ha'p : a' ^ p = 1)
    (hfix : ∀ u ∈ blockSU (n := n) (K := K) (Finset.univ.erase c), a' (φ u) = φ u) :
    a' ∈ Subgroup.zpowers a := by
  classical
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hq : ¬ (d = 3 ∧ 2 ^ n = 2) := fun ⟨h1, _⟩ => by omega
  have hd3 : 3 ≤ d := by omega
  have hcen := TableBUE.center_proj_eq_bot hK hd3 hdq
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hcen
  obtain ⟨β, hβ⟩ := exists_beta hK hd hdq hψ hker hM.surj
  let α' := β.trans ((BstarDesc.descAut hψ hZ a').trans β.symm)
  have hα'apply : ∀ x, β (α' x) = BstarDesc.descAut hψ hZ a' (β x) := fun x => by
    show β (β.symm (BstarDesc.descAut hψ hZ a' (β x))) = _
    rw [MulEquiv.apply_symm_apply]
  have hpowα : (BstarDesc.descAut hψ hZ a') ^ p = 1 := by
    rw [← map_pow, ha'p, map_one]
  have hα'p : α' ^ p = 1 := by
    apply MulEquiv.ext
    intro x
    have key : ∀ m : ℕ, ∀ y, (α' ^ m) y = β.symm ((BstarDesc.descAut hψ hZ a' ^ m) (β y)) := by
      intro m
      induction m with
      | zero => intro y; simp
      | succ m ih =>
        intro y
        rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply]
        simp [α']
    rw [key p x, hpowα]
    simp
  have hfix' : ∀ u ∈ blockSU (n := n) (K := K) (Finset.univ.erase c),
      α' (InndiagSU.projU n d K u) = InndiagSU.projU n d K u := by
    intro u hu
    have hb := hβ u
    apply β.injective
    rw [hα'apply, hb, BstarDesc.descAut_apply, hfix u hu, ← hb]
  obtain ⟨ρ, hρp, hact⟩ := centR_of_fix h hK hn hd c hp hpq α' hα'p hfix'
  obtain ⟨hD', hact'⟩ := hact
  obtain ⟨hDζ, hactA⟩ := ha
  haveI : Fact p.Prime := ⟨hp⟩
  have hprim : IsPrimitiveRoot ((ζ : Kˣ) : K) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hζp hζ1))
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one
    (by rw [← Units.val_pow_eq_pow_val, hρp, Units.val_one] : ((ρ : Kˣ) : K) ^ p = 1)
  have hρj : ρ = ζ ^ j := Units.ext (by rw [Units.val_pow_eq_pow_val, hj])
  subst hρj
  have hpowD : diagHom d (nodeDiag c (ζ ^ j)) = (diagHom d (nodeDiag c ζ)) ^ j := by
    rw [← map_pow]
    congr 1
    funext k
    by_cases hk : k = c
    · subst hk
      simp [nodeDiag]
    · simp [nodeDiag, hk]
  let θ : ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    ψ.comp φ
  have hθ : ∀ u, θ u = ψ (φ u) := fun u => rfl
  have hαa : ∀ u : ↥(unitarySU 2 n K d),
      BstarDesc.descAut hψ hZ a (θ u) = θ (LineU.conjN (diagHom d (nodeDiag c ζ)) hDζ u) := by
    intro u
    rw [hθ, BstarDesc.descAut_apply, hactA u, hθ]
  have hα : ∀ u : ↥(unitarySU 2 n K d),
      BstarDesc.descAut hψ hZ a' (θ u) =
        θ (LineU.conjN (diagHom d (nodeDiag c (ζ ^ j))) hD' u) := by
    intro u
    have h1 : θ u = β (InndiagSU.projU n d K u) := (hβ u).symm
    rw [h1, ← hα'apply, hact' u]
    exact hβ _
  have hiter := iter_conj θ (BstarDesc.descAut hψ hZ a) hDζ hαa j
  have hθs : Function.Surjective θ := fun r => by
    obtain ⟨l, rfl⟩ := hψ r
    obtain ⟨s, rfl⟩ := hM.surj l
    exact ⟨s, rfl⟩
  have hEq : BstarDesc.descAut hψ hZ a' = (BstarDesc.descAut hψ hZ a) ^ j := by
    apply MulEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := hθs x
    obtain ⟨v, hv1, hv2⟩ := hiter u
    rw [hα u, hv2]
    congr 1
    congr 1
    apply Subtype.ext
    show diagHom d (nodeDiag c (ζ ^ j)) * (u : GL (Fin d) K) *
      (diagHom d (nodeDiag c (ζ ^ j)))⁻¹ = (v : GL (Fin d) K)
    rw [hv1, hpowD]
  have haj : a' = a ^ j := BstarDesc.descAut_injective hψ hZ hperf (by rw [hEq, map_pow])
  exact Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), by rw [zpow_natCast, haj]⟩

theorem zpow_fix_of {L' : Type} [Group L'] {a : MulAut L'} {j : L'} (hj : a j = j) (k : ℤ) :
    (a ^ k) j = j := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [_root_.zpow_add_one, MulAut.mul_apply, hj, ih]
  | pred i ih =>
    have hinv : a⁻¹ j = j := by
      calc a⁻¹ j = a⁻¹ (a j) := by rw [hj]
        _ = (a⁻¹ * a) j := rfl
        _ = j := by rw [inv_mul_cancel, MulAut.one_apply]
    rw [_root_.zpow_sub_one, MulAut.mul_apply, hinv, ih]

theorem card_ge_delta
    [Finite K] {L' : Type} [Group L'] [Finite L'] {p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hZ : ψ.ker = Subgroup.center L')
    {A : Subgroup (MulAut L')} (hadm : GGDeltaAdm p L' A) : p ^ (d - 2) ≤ Nat.card A := by
  rcases hadm.2 with ⟨-, hδ₁⟩ | ⟨hpZ, hδ₂, -⟩
  · obtain ⟨E, hE, hEc, -⟩ := TableBUDT.exists_elemAbelian_cover hK hn hd hdq hp hpq ψ hψ hker
    rw [← hEc]
    exact hδ₁ E hE
  · rw [← hZ] at hpZ
    obtain ⟨E, hE, hEc⟩ :=
      TableBUDT.exists_elemAbelian_cover_succ hK hn hd hdq hp hpq ψ hψ hker hpZ
    have h1 := hδ₂ E hE
    rw [hEc, show d - 1 = (d - 2) + 1 by omega, pow_succ'] at h1
    exact Nat.le_of_mul_le_mul_left h1 hp.pos

theorem ggEndNodeIOneDelta_of_ne
    {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ n = 1)) :
    GGEndNodeIOneDelta p (ggUnitaryTorusRank p d) (UnitaryR K n d) (UnitaryI K n d) := by
  intro L' _ _ ψ hψ hker hperf A As hA hlt hAs hcard hAI hr h3 hadm _hNT
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hq : ¬ (d = 3 ∧ 2 ^ n = 2) := fun ⟨h1, _⟩ => by omega
  have hcen := TableBUE.center_proj_eq_bot hK hd3 hdq
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hcen
  have hh : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hAge : p ^ (d - 2) ≤ Nat.card A := card_ge_delta hK hn hd3 hdq hp hpq hψ hker hZ hadm
  have hcardD : p ^ (d / p + 2) ≤ Nat.card A := by
    refine le_trans (Nat.pow_le_pow_right hp.pos ?_) hAge
    have h1 : d / p ≤ d / 3 := Nat.div_le_div_left hp3 (by norm_num)
    omega
  have hnd' : (d, n) ≠ (6, 1) := fun he => hnd ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ := LineU.exists_diagModel hK hn hd hp hpq hpd
    (LineU.unitaryUniversalCover_holds n d K hK hd hnd') hψ hker hperf hA hAI hcardD
  let hM : UnitTB.Model φ := ⟨hh, hφs, hφker⟩
  have hd1 : 0 < d := by omega
  obtain ⟨ν, hν⟩ := SmallU.exists_nu_actsU hM hd3 hdiag (⟨0, hd1⟩ : Fin d)
  obtain ⟨δ, hδp, hδ1, hnode⟩ := node_exists hh hp hpq hM hd3 hA hadm (⟨0, hd1⟩ : Fin d) ν hν
  have hs0c : ∃ c : Fin d, c ≠ (⟨0, hd1⟩ : Fin d) := by
    by_cases h0 : (⟨1, by omega⟩ : Fin d) = ⟨0, hd1⟩
    · exact ⟨⟨2, by omega⟩, fun e => by simp [Fin.ext_iff] at e⟩
    · exact ⟨⟨1, by omega⟩, h0⟩
  obtain ⟨c, hcs⟩ := hs0c
  obtain ⟨x, hx⟩ := hnode c hcs
  have ha : ActsU φ (x : MulAut L') (nodeDiag c δ) := by
    rw [← hx]
    exact (hν x).1
  have hS : (Finset.univ.erase c : Finset (Fin d)).card = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hcS : c ∉ (Finset.univ.erase c : Finset (Fin d)) := by simp
  have hτ : IsNodeOn (nodeDiag c δ) (Finset.univ.erase c) := by
    constructor
    · intro i hi j hj
      have hic : i ≠ c := (Finset.mem_erase.mp hi).1
      have hjc : j ≠ c := (Finset.mem_erase.mp hj).1
      simp [nodeDiag, hic, hjc]
    · intro i hi j hj
      have hic : i = c := by
        by_contra h'
        exact hi (Finset.mem_erase.mpr ⟨h', Finset.mem_univ i⟩)
      subst hic
      simp only [nodeDiag, if_neg hj, if_pos rfl]
      exact fun e => hδ1 e.symm
  have hbig : BigOK n (Finset.univ.erase c : Finset (Fin d)) := Or.inl (by omega)
  obtain ⟨hlay, hcomp⟩ := layer_eq_block_of_isNodeOn hM ha hτ hbig
  have hsmall : ¬ LargeEvenSmall (LargeEvenLayer (ggFix (x : MulAut L'))) := by
    rw [hlay]
    have hSne : (Finset.univ.erase c : Finset (Fin d)) ≠ Finset.univ := fun e =>
      hcS (by rw [e]; exact Finset.mem_univ c)
    have hinj : ∀ u ∈ blockSU (n := n) (K := K) (Finset.univ.erase c), ψ (φ u) = 1 → u = 1 :=
      fun u hu hψu => psi_phi_eq_one_of_block hM hker hcen hSne hu hψu
    have hbigc : 25920 < Nat.card (blockSU (n := n) (K := K) (Finset.univ.erase c)) := by
      rw [← Nat.card_congr (TableBUE.blockSUEquiv (Finset.univ.erase c) hh).toEquiv]
      rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · have hn1' : n = 1 := by omega
        have h3p : p ∣ 3 := by
          rw [hn1'] at hpq
          norm_num at hpq
          exact hpq
        have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3p
        rw [hp3'] at hpd
        have h3d : 3 ∣ d := hpd
        exact IOneU.suCard_gt_of_five_le hh hn1' (m := (Finset.univ.erase c : Finset (Fin d)).card)
          (by omega)
      · exact IOneU.suCard_gt_of_two_le hh hn2 (m := (Finset.univ.erase c : Finset (Fin d)).card)
          (by omega)
    exact not_largeEvenSmall_of_map_big ψ _ (bigLayer_map_of_block hinj hbigc)
  have hle : LargeEvenLayer (ggFix (x : MulAut L')) ≤ ggFix (x : MulAut L') :=
    sSup_le (fun _ hK' => hK'.1)
  have hCentAs : ∀ a' ∈ As, ((∀ j ∈ LargeEvenLayer (ggFix (x : MulAut L')), a' j = j) ↔
      a' ∈ Subgroup.zpowers (x : MulAut L')) := by
    intro a' ha'
    constructor
    · intro hfixL
      have hfixU : ∀ u ∈ blockSU (n := n) (K := K) (Finset.univ.erase c), a' (φ u) = φ u := by
        intro u hu
        apply hfixL
        rw [hlay]
        exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      exact centralizer_L hh hK hn hd c hp hpq hψ hker hperf hM hδp hδ1 ha (hAs.2 a' ha') hfixU
    · intro hz j hj
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact zpow_fix_of (hle hj) k
  refine ⟨(x : MulAut L'), ⟨x.2, ?_, hcomp, fun a' ha' => hCentAs a' (hlt.le ha')⟩,
    hCentAs, fun _ _ => hsmall⟩
  intro h1
  have hx1 : x = 1 := Subtype.ext h1
  rw [hx1, map_one] at hx
  have h2 := congrFun hx c
  simp only [nodeDiag, if_pos rfl, Pi.one_apply] at h2
  exact hδ1 h2.symm

@[expose] def GGIOneUnitaryDvdDeltaSixTwoInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 →
    GGEndNodeIOneDelta 3 (ggUnitaryTorusRank 3 6) (UnitaryR K 1 6) (UnitaryI K 1 6)

theorem ggIOneUnitaryDvdDeltaInput_of_sixTwo
    (h61 : GGIOneUnitaryDvdDeltaSixTwoInput) : GGIOneUnitaryDvdDeltaInput := by
  intro K _ _ n d p hK hn hd hp hpq hpd
  by_cases hnd : d = 6 ∧ n = 1
  · obtain ⟨rfl, rfl⟩ := hnd
    have h3 : p ∣ 3 := by
      norm_num at hpq
      exact hpq
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst hp3
    exact h61 K hK
  · exact ggEndNodeIOneDelta_of_ne hK hn hd hp hpq hpd hnd

end CFSG.StandardType.IOneUDelta

end
