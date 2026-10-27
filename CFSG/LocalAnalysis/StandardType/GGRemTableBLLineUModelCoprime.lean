module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCoprime
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitAutModel

public section

namespace CFSG.StandardType.TableBUD

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag TableBUE
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

theorem exists_unitary_frame_coprime {K : Type} [Field K] [Finite K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hpd : ¬ p ∣ d)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hAb : IsElemAbelian p Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n))) :
    ∃ P ∈ primeFormUnitary h (idGram K d), ∀ a ∈ Ab, ∃ (M : GL (Fin d) K)
      (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n K d) ⟨M, gu_subset_normalizer h hM⟩ := by
  classical
  have hN := gu_subset_normalizer (d := d) h
  set ρ := TableB.projConj (unitarySU 2 n K d) with hρ
  set N₀ : Subgroup (Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :=
    Ab.comap ρ with hN₀
  set χ : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) →*
      MulAut (projectiveSL d K) :=
    (conjAut d K).comp (Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))).subtype
    with hχ
  set X := N₀.map χ with hX
  have hscal : ∀ M, ρ M = 1 → χ M = 1 := by
    intro M hM
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK hd hdq hp hpq hM
    rw [hχ, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hc, conjAut_scalar]
  have hXab : IsElemAbelian p X := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, M, hM, rfl⟩ ⟨_, M', hM', rfl⟩
      apply Subtype.ext
      show χ M * χ M' = χ M' * χ M
      have hc : ρ (M * M' * M⁻¹ * M'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          TableB.IsElemAbelian.comm hAb hM hM', mul_inv_cancel_right, mul_inv_cancel]
      have h1 := hscal _ hc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc χ M * χ M' = χ M * χ M' * (χ M)⁻¹ * (χ M')⁻¹ * (χ M' * χ M) := by group
        _ = χ M' * χ M := by rw [h1, one_mul]
    · rintro _ ⟨M, hM, rfl⟩
      rw [← map_pow]
      exact hscal _ (by rw [map_pow]; exact hAb.2 _ hM)
  have hXU : ∀ x ∈ X, ∃ M ∈ LargeEvenGUSet (Fin d) K (2 ^ n), conjAut d K M = x := by
    rintro _ ⟨M, hM, rfl⟩
    obtain ⟨M', hM'gu, hM'eq⟩ := TableB.exists_eq_projConj hN (hAbI _ hM)
    refine ⟨M', hM'gu, ?_⟩
    have hM'eq' : ρ M = ρ ⟨M', hN hM'gu⟩ := hM'eq
    have h1 : ρ ((⟨M', hN hM'gu⟩ :
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))⁻¹ * M) = 1 := by
      rw [map_mul, map_inv, hM'eq', inv_mul_cancel]
    have h2 := hscal _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hlift : ∀ a : Ab, ∃ (M : GL (Fin d) K) (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
      (a : MulAut _) = ρ ⟨M, hN hM⟩ := fun a => TableB.exists_eq_projConj hN (hAbI a a.2)
  choose Mf hMf hMfeq using hlift
  have hMN : ∀ a : Ab, (⟨Mf a, hN (hMf a)⟩ :
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) ∈ N₀ := fun a => by
    show ρ _ ∈ Ab
    rw [← hMfeq a]
    exact a.2
  obtain ⟨P, hP, hPd⟩ := ggPGUTorality_coprime h hp hpq hpd hXab hXU
  exact ⟨P, hP, fun a ha => ⟨Mf ⟨a, ha⟩, hMf ⟨a, ha⟩,
    hPd _ ⟨_, hMN ⟨a, ha⟩, rfl⟩, hMfeq ⟨a, ha⟩⟩⟩

end CFSG.StandardType.TableBUD

namespace CFSG.StandardType.LineU

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open scoped commutatorElement

theorem exists_diagModel_coprime_of_twist {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K]
    [Finite K] {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hperfSU : commutator (unitarySU 2 n K d) = ⊤)
    (hcov : ∀ θ : LargeEvenProj (unitarySU 2 n K d) ≃* LargeEvenProj (unitarySU 2 n K d),
      ∃ φ : ↥(unitarySU 2 n K d) →* L', ∀ s, θ (ψ (φ s)) = LargeEvenProjMk (unitarySU 2 n K d) s)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l)) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
        ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) ∧
      ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    obtain ⟨rfl, hq2⟩ := Prod.mk.inj heq
    have h3 : p ∣ 3 := by simpa [hq2] using hpq
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    rw [hp3] at hpd
    exact hpd (by norm_num)
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hAb : CFSG.Open.IsElemAbelian p Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ x ∈ Ab, x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  obtain ⟨P, hP, hframe⟩ :=
    TableBUD.exists_unitary_frame_coprime h hK hd hdq hp hpq hpd hAb hAbI
  have hPN := primeForm_mem_normalizer h hP
  set θ := TableBUE.conjProj h P hP with hθ
  set ψ'' : L' →* LargeEvenProj (unitarySU 2 n K d) := θ.toMonoidHom.comp ψ with hψ''
  have hψ''s : Function.Surjective ψ'' := θ.surjective.comp hψ
  have hker'' : ψ''.ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : θ (ψ x) = θ 1 := by rw [map_one]; exact hx
    exact θ.injective hx'
  obtain ⟨φ, hφ₀⟩ := hcov θ
  have hφ : ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K d) s := hφ₀
  have hφs : Function.Surjective φ := by
    have hcomm : ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ ≤ φ.range := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ : ∃ s : ↥(unitarySU 2 n K d),
          ψ'' x = LargeEvenProjMk (unitarySU 2 n K d) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ'' x)
        exact ⟨s0, hs0.symm⟩
      obtain ⟨s', hs'⟩ : ∃ s : ↥(unitarySU 2 n K d),
          ψ'' y = LargeEvenProjMk (unitarySU 2 n K d) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ'' y)
        exact ⟨s0, hs0.symm⟩
      have hz : x * (φ s)⁻¹ ∈ Subgroup.center L' := by
        apply hker''
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs, mul_inv_cancel]
      have hz' : y * (φ s')⁻¹ ∈ Subgroup.center L' := by
        apply hker''
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs', mul_inv_cancel]
      have hx : x = (x * (φ s)⁻¹) * φ s := by group
      have hy : y = (y * (φ s')⁻¹) * φ s' := by group
      rw [hx, hy, comm_mul_central hz hz']
      exact ⟨⁅s, s'⁆, by rw [map_commutatorElement]⟩
    have htop : (⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ : Subgroup L') = ⊤ := hperf
    rw [htop] at hcomm
    intro l
    obtain ⟨s, hs⟩ := hcomm (Subgroup.mem_top l)
    exact ⟨s, hs⟩
  refine ⟨φ, hφs, ?_, ?_⟩
  ·
    intro g hg
    obtain ⟨u, hu⟩ := StdSubRestU.exists_scalar_of_projMk_eq_one (z := g)
      (by rw [← hφ g, hg, map_one])
    exact ⟨u, Matrix.ext fun i j => by rw [hu, Matrix.diagonal_apply]⟩
  ·
    intro a ha
    obtain ⟨xa, hxaI, hxa⟩ := hAI a ha
    have hxaAb : xa ∈ Ab := TypeA.mem_inducedSub.mpr ⟨a, ha, hxa⟩
    obtain ⟨M, hM, hdiag, hxa_eq⟩ := hframe xa hxaAb
    have hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      TableBUE.gu_subset_normalizer h hM
    have hDN : P⁻¹ * M * P ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
    have htw : ∀ l : L', ψ'' (a l) =
        TableB.projConj (unitarySU 2 n K d) ⟨P⁻¹ * M * P, hDN⟩ (ψ'' l) := by
      intro l
      have e1 : ψ'' (a l) = θ (xa (ψ l)) := by
        rw [hψ'', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxa l]
      rw [e1, hxa_eq]
      exact TableBUD.conjProj_projConj h P hP ⟨M, hMN⟩ hDN (ψ l)
    have hdiag' : ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (Matrix.diag ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :=
      ((Matrix.isDiag_iff_diagonal_diag _).mp hdiag).symm
    refine ⟨Matrix.diag ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K),
      P⁻¹ * M * P, hDN, hdiag', fun s' => ?_⟩
    have hfun : (MulEquiv.toMonoidHom a).comp φ =
        φ.comp (conjNHom (P⁻¹ * M * P) hDN) := by
      apply CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hperfSU
      intro s
      apply hker''
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom]
      rw [htw (φ s), hφ s, projConj_mk_eq _ hDN s, ← hφ (conjN _ hDN s), inv_mul_cancel]
    have := congrArg (fun f => f s') hfun
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom] using this

theorem exists_diagModel_coprime {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hcov : UnitaryCoverAt n d K)
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l)) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
        ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) ∧
      ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t := by
  refine exists_diagModel_coprime_of_twist hK hn hd hp hpq hpd hψ hker hperf hcov.1
    (fun θ => ?_) hA hAI
  have hker' : (θ.toMonoidHom.comp ψ).ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : θ (ψ x) = θ 1 := by rw [map_one]; exact hx
    exact θ.injective hx'
  exact hcov.2 L' (θ.toMonoidHom.comp ψ) (θ.surjective.comp hψ) hker' hperf

end CFSG.StandardType.LineU

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.StandardType.LineU

theorem not_dvd_four_of_dvd_two_pow_add_one {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n + 1) : ¬ p ∣ 4 := fun h4 =>
  TableBU.ne_two_of_dvd_two_pow_add_one hn hpn ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))

theorem largeEvenLabelAll_uFour_of_forall {P : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    {lab : LargeEvenLabel} (htag : lab.tag = .twA ∨ lab.tag = .twD) (hl : lab.rank = 3)
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ lab.n) ^ 2 →
      P (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ lab.n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ lab.n)))
          (LargeEvenGUSet (Fin 4) K (2 ^ lab.n)))) :
    LargeEvenLabelAll lab fun R _ I _ => P R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl h ⊢
  subst hl
  intro Q hQ
  rcases htag with rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    exact ⟨K, i1, i2, hK, ⟨hQ', h K hK⟩⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by norm_num : ¬ (3 = 2)), if_pos rfl] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    exact ⟨K, i1, i2, hK, ⟨hQ', h K hK⟩⟩

theorem exists_diagModel_PSU_coprime
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    (hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊤)
    {Eb : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hA : IsElemAbelian p Eb)
    (hI : (Eb : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) :
    ∃ φ : ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      UnitTB.Model φ ∧ ∀ a ∈ Eb, ∃ t : Fin d → K, ActsDiagU φ a t := by
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    obtain ⟨rfl, hq2⟩ := Prod.mk.inj heq
    have h3 : p ∣ 3 := by simpa [hq2] using hpq
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    rw [hp3] at hpd
    exact hpd (by norm_num)
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := hU.charP
  have hperfSU : commutator (unitarySU 2 n K d) = ⊤ := by
    have : Group.IsPerfect ↥(unitarySU 2 n K d) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := n) hK (n := d) hd hdq
    exact Group.IsPerfect.commutator_eq_top
  have : Finite (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := inferInstance
  let ψ : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) := MonoidHom.id _
  have hψ : Function.Surjective ψ := fun x => ⟨x, rfl⟩
  have hker : ψ.ker ≤ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    rw [MonoidHom.ker_id]; exact bot_le
  have hAI : ∀ a ∈ Eb, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l, x (ψ l) = ψ (a l) :=
    fun a ha => ⟨a, hI ha, fun _ => rfl⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel_coprime_of_twist hK hn hd hp hpq hpd hψ hker hperf hperfSU
      (fun θ => ⟨θ.symm.toMonoidHom.comp (LargeEvenProjMk (unitarySU 2 n K d)), fun s =>
        θ.apply_symm_apply _⟩) hA hAI
  exact ⟨φ, ⟨hU, hφs, hφker⟩, hdiag⟩

end CFSG.StandardType
