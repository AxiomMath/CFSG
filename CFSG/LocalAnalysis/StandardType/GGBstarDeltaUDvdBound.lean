module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUDvdBoundLift
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwoLift

public section

namespace CFSG.StandardType

namespace TableBUDL

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU TableBUI TableBUD
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] {n d p : ℕ}

theorem norm_eq_one_of_pow (hpq : p ∣ 2 ^ n + 1) {τ : Fin d → Kˣ} (hτ : ∀ k, τ k ^ p = 1)
    (k : Fin d) : ((τ k : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
  obtain ⟨m, hm⟩ := hpq
  rw [← Units.val_pow_eq_pow_val, hm, pow_mul, hτ k, one_pow, Units.val_one]

theorem diagHom_mem_unitarySU (h : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1)
    {τ : Fin d → Kˣ} (hτ : ∀ k, τ k ^ p = 1) (hprod : ∏ k, τ k = 1) :
    diagHom d τ ∈ unitarySU 2 n K d := by
  refine TableBUE.mem_unitarySU_of_mem_primeFormUnitary h
    (diagHom_mem_primeFormUnitary h (norm_eq_one_of_pow hpq hτ)) ?_
  rw [det_diagHom, ← Units.coe_prod, hprod, Units.val_one]

theorem diagHom_pow_eq_one {τ : Fin d → Kˣ} (hτ : ∀ k, τ k ^ p = 1) :
    (diagHom d τ : GL (Fin d) K) ^ p = 1 := by
  rw [← map_pow, show τ ^ p = 1 from funext hτ, map_one]

theorem ggBstarBoundDelta_unitary [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) (hd5 : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (r : ℕ) :
    GGBstarBoundDelta p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  intro L' _ _ ψ hψ hker hL A Ah _ hAI _ _ hadm hAAh hAh
  set h := TableBU.unitaryFieldData_of_card hK hn
  have hd : 3 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := fun ⟨h1, _⟩ => by omega
  have := Fact.mk hp
  have : CharP K 2 := h.charP
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hZ : ψ.ker = Subgroup.center L' :=
    BstarDesc.ker_eq_center hψ hker (TableBUE.center_proj_eq_bot hK hd hdq)
  set δ := BstarDesc.descAut hψ hZ with hδ
  have hδinj := BstarDesc.descAut_injective hψ hZ hL
  have hAge : p ^ (d - 2) ≤ Nat.card A := by
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
  set Ab := A.map δ
  set Ahb := Ah.map δ
  have hAbD : Ab ≤ inndiagU h hd1 := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have he : δ a = φ := MulEquiv.ext fun s => by
      obtain ⟨l, rfl⟩ := hψ s
      rw [hδ, BstarDesc.descAut_apply, hφ]
    rw [he]
    exact congr_mem_primeFormD h hd1 hK hφI
  have hAhbab : IsElemAbelian p Ahb := TableB.isElemAbelian_map hAh δ
  set E₀ := Ahb ⊓ inndiagU h hd1
  have hE₀ab : IsElemAbelian p E₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (TableB.IsElemAbelian.comm hAhbab a.2.1 b.2.1)⟩⟩,
      fun a ha => hAhbab.2 a ha.1⟩
  have hAbE₀ : Ab ≤ E₀ := le_inf (Subgroup.map_mono hAAh) hAbD
  have hcAb : Nat.card Ab = Nat.card A := Subgroup.card_map_of_injective hδinj
  have hcAhb : Nat.card Ahb = Nat.card Ah := Subgroup.card_map_of_injective hδinj
  have hbig : p ^ (d / p + 1) < Nat.card E₀ := by
    have h1 : d / p ≤ d / 3 := Nat.div_le_div_left hp3 (by norm_num)
    have h2 : d / p + 1 < d - 2 := by omega
    have h3 : Nat.card Ab ≤ Nat.card E₀ := Subgroup.card_le_of_le hAbE₀
    exact (Nat.pow_lt_pow_right hp.one_lt h2).trans_le (hAge.trans (hcAb.symm.le.trans h3))
  obtain ⟨Q, hQ, hfr⟩ := exists_frame_inndiag hK hd hdq hq hp hpq hE₀ab inf_le_right hbig
  have hfrA : ∀ a ∈ A, ∃ σ : Fin d → Kˣ, σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ p = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) ∧ FrameAct h Q hQ (δ a) σ :=
    fun a ha => hfr (δ a) (hAbE₀ ⟨a, ha, rfl⟩)
  have hC2 : ∀ τ : Fin d → Kˣ, (∀ k, τ k ^ p = 1) → ∏ k, τ k = 1 →
      ∃ x ∈ Ab, FrameAct h Q hQ x τ := by
    intro τ hτ hprod
    set s : ↥(unitarySU 2 n K d) := ⟨diagHom d τ, diagHom_mem_unitarySU h hpq hτ hprod⟩
    have hsp : s ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact diagHom_pow_eq_one hτ)
    obtain ⟨e, hep, hψe, hfix⟩ := exists_lift_fix h hK hn hd hdq hp hp2 hψ hker hL Q hQ s hsp
    have heA : MulAut.conj e ∈ A := hadm.1 e hep fun a ha => by
      obtain ⟨σ, -, -, hσn, hfrσ⟩ := hfrA a ha
      refine hfix a (δ a) (diagHom d σ) (diagHom_mem_primeFormUnitary h hσn)
        (fun l => BstarDesc.descAut_apply hψ hZ a l) hfrσ ?_
      change diagHom d σ * diagHom d τ = diagHom d τ * diagHom d σ
      rw [← map_mul, ← map_mul, mul_comm]
    refine ⟨δ (MulAut.conj e), ⟨_, heA, rfl⟩, ?_⟩
    rw [hδ, descAut_conj, hψe]
    exact frameAct_conj_frameMk rfl
  obtain ⟨as, has, σs, -, hσsp, hσsn, hfrs, hσsprod⟩ : ∃ a ∈ A, ∃ σ : Fin d → Kˣ,
      σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ p = 1) ∧ (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) ∧
        FrameAct h Q hQ (δ a) σ ∧ ∏ k, σ k ≠ 1 := by
    by_contra hcon
    have hinn : ∀ a ∈ A, ∃ e : L', e ^ p = 1 ∧ MulAut.conj e = a := by
      intro a ha
      obtain ⟨σ, hσ0, hσp, hσn, hfrσ⟩ := hfrA a ha
      have hprod : ∏ k, σ k = 1 := by
        by_contra hne
        exact hcon ⟨a, ha, σ, hσ0, hσp, hσn, hfrσ, hne⟩
      set s : ↥(unitarySU 2 n K d) := ⟨diagHom d σ, diagHom_mem_unitarySU h hpq hσp hprod⟩
      have hsp : s ^ p = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact diagHom_pow_eq_one hσp)
      obtain ⟨e, hep, hψe, -⟩ := exists_lift_fix h hK hn hd hdq hp hp2 hψ hker hL Q hQ s hsp
      refine ⟨e, hep, hδinj ?_⟩
      change BstarDesc.descAut hψ hZ (MulAut.conj e) = δ a
      rw [descAut_conj, hψe]
      exact FrameAct.unique hσn (frameAct_conj_frameMk rfl) hfrσ
    rcases hadm.2 with ⟨⟨a, ha, hna⟩, -⟩ | ⟨-, -, a, ha, hna⟩
    · obtain ⟨e, -, rfl⟩ := hinn a ha
      exact hna ⟨e, rfl⟩
    · obtain ⟨e, hep, rfl⟩ := hinn a ha
      rcases hna with hna | hna
      · exact hna ⟨e, rfl⟩
      · have h1 := hna e rfl
        rw [hep, orderOf_one, Nat.dvd_one] at h1
        exact hp.one_lt.ne' h1
  have hfull : ∀ τ : Fin d → Kˣ, (∀ k, τ k ^ p = 1) → ∃ x ∈ Ab, FrameAct h Q hQ x τ := by
    intro τ hτ
    have hεsp : (∏ k, σs k) ^ p = 1 := by
      rw [← Finset.prod_pow]
      exact Finset.prod_eq_one fun k _ => hσsp k
    have hεp : (∏ k, τ k) ^ p = 1 := by
      rw [← Finset.prod_pow]
      exact Finset.prod_eq_one fun k _ => hτ k
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (∏ k, σs k) ^ m = ∏ k, τ k := by
      have hord : orderOf (∏ k, σs k) = p := orderOf_eq_prime hεsp hσsprod
      have hle : Subgroup.zpowers (∏ k, σs k) ≤ rootsOfUnity p K := by
        rw [Subgroup.zpowers_le]
        exact (mem_rootsOfUnity p _).mpr hεsp
      have heq : Subgroup.zpowers (∏ k, σs k) = rootsOfUnity p K := by
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        rw [Nat.card_zpowers, hord]
        exact card_rootsOfUnity K p
      have hmem : ∏ k, τ k ∈ Subgroup.zpowers (∏ k, σs k) := by
        rw [heq]
        exact (mem_rootsOfUnity p _).mpr hεp
      rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
      exact hmem
    have hσmp : ∀ k, (σs ^ m) k ^ p = 1 := fun k => by
      rw [Pi.pow_apply, ← pow_mul, mul_comm, pow_mul, hσsp k, one_pow]
    set τ' : Fin d → Kˣ := τ * (σs ^ m)⁻¹ with hτ'
    have hτ'p : ∀ k, τ' k ^ p = 1 := fun k => by
      rw [hτ', Pi.mul_apply, Pi.inv_apply, mul_pow, inv_pow, hσmp k, hτ k, inv_one, mul_one]
    have hτ'prod : ∏ k, τ' k = 1 := by
      simp only [hτ', Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Finset.prod_mul_distrib,
        Finset.prod_inv_distrib, Finset.prod_pow]
      rw [hm, mul_inv_cancel]
    obtain ⟨x', hx', hfr'⟩ := hC2 τ' hτ'p hτ'prod
    have h1 := hfr'.mul (frameAct_pow hfrs hσsn m) (norm_eq_one_of_pow hpq hσmp)
    rw [hτ', inv_mul_cancel_right] at h1
    exact ⟨x' * δ as ^ m, Ab.mul_mem hx' (Ab.pow_mem ⟨as, has, rfl⟩ m), h1⟩
  have hE₀le : E₀ ≤ Ab := by
    intro x hx
    obtain ⟨σ, -, hσp, hσn, hfrσ⟩ := hfr x hx
    obtain ⟨y, hy, hfry⟩ := hfull σ hσp
    rw [FrameAct.unique hσn hfrσ hfry]
    exact hy
  have h1 := card_le_mul_card_inf_inndiagU h hd hq hp hAhbab
  have h2 : Nat.card E₀ ≤ Nat.card Ab := Subgroup.card_le_of_le hE₀le
  rw [← hcAhb, ← hcAb]
  exact h1.trans (Nat.mul_le_mul_left p h2)

end TableBUDL

theorem ggBstarBoundDeltaUnitaryDvdInput_holds :
    GGBstarBoundDeltaUnitaryDvdInput := by
  intro K _ _ n d p hK hn hd5 hp hpq _
  exact TableBUDL.ggBstarBoundDelta_unitary hK hn hd5 hp hpq _

theorem ggBstarDeltaUnitaryInput_holds :
    GGBstarDeltaUnitaryInput :=
  ggBstarDeltaUnitaryInput_of_delta ggBstarBoundDeltaUnitaryDvdInput_holds

end CFSG.StandardType
