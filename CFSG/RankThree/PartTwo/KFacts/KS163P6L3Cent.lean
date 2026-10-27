module

public import CFSG.RankThree.PartTwo.KFacts.KS163P6
import CFSG.RankThree.PartTwo.KFacts.KS163P6L3Norm
import CFSG.RankThree.PartTwo.KFacts.KS163P6L3AutU
import CFSG.RankThree.PartTwo.KFacts.KS163P6L3AutL
import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessConj
import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTypes
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF163L3

open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec14.Res8Hess
open CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

theorem mem_of_isMaxInvTwo {X : Type} [Group X] [Finite X] {E D Θ : Subgroup X}
    (hD : IsMaxInvTwo E D) (hDΘ : D ≤ Θ) (hEΘ : E ≤ Subgroup.normalizer (Θ : Set X))
    (hcomm : ∀ a ∈ Θ, ∀ b ∈ Θ, a * b = b * a) {y : X} (hy : y ∈ Θ) {k : ℕ}
    (hyk : y ^ 2 ^ k = 1) : y ∈ D := by
  set S : Subgroup X :=
    { carrier := {z | z ∈ Θ ∧ ∃ n : ℕ, z ^ 2 ^ n = 1}
      one_mem' := ⟨Θ.one_mem', 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨haΘ, m, hm⟩ ⟨hbΘ, n, hn⟩
        refine ⟨Θ.mul_mem haΘ hbΘ, m + n, ?_⟩
        have hab : Commute a b := hcomm a haΘ b hbΘ
        have ha : a ^ 2 ^ (m + n) = 1 := by
          rw [pow_add, pow_mul, hm, one_pow]
        have hb : b ^ 2 ^ (m + n) = 1 := by
          rw [show m + n = n + m from Nat.add_comm m n, pow_add, pow_mul, hn, one_pow]
        rw [hab.mul_pow, ha, hb, mul_one]
      inv_mem' := by
        rintro a ⟨haΘ, n, hn⟩
        exact ⟨Θ.inv_mem haΘ, n, by rw [inv_pow, hn, inv_one]⟩ } with hS
  have hS2 : IsPGroup 2 S := fun z => by
    obtain ⟨n, hn⟩ := z.2.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hconj : ∀ g ∈ E, ∀ w ∈ S, g * w * g⁻¹ ∈ S := by
    rintro g hg w ⟨hwΘ, n, hn⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hEΘ hg) w).mp hwΘ, n, ?_⟩
    have h : MulAut.conj g (w ^ 2 ^ n) = (MulAut.conj g w) ^ 2 ^ n := map_pow _ _ _
    rw [MulAut.conj_apply, MulAut.conj_apply] at h
    rw [← h, hn, mul_one, mul_inv_cancel]
  have hES : E ≤ Subgroup.normalizer (S : Set X) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact hconj e he z
    · intro hz
      have h := hconj e⁻¹ (E.inv_mem he) (e * z * e⁻¹) hz
      have h' : e⁻¹ * (e * z * e⁻¹) * (e⁻¹)⁻¹ = z := by group
      rwa [h'] at h
  have hDS : D ≤ S := by
    intro d hd
    obtain ⟨n, hn⟩ := hD.1.1 ⟨d, hd⟩
    exact ⟨hDΘ hd, n, by simpa using hn⟩
  exact hD.2 ⟨hS2, hES⟩ hDS ⟨hy, k, hyk⟩

private theorem exists_model_aut {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hiso : Sec4.IsoLThreePi X p f)
    (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8)) {E D : Subgroup X}
    (hEe : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hD : IsMaxInvTwo E D) {x : X} (hxE : x ∈ E) (hx1 : x ≠ 1) (hDx : D ≤ thetaC x)
    (τ : MulAut X) (hτE : ∀ e ∈ E, τ e = e) (hτD : ∀ d ∈ D, τ d = d)
    {k : ℕ} (hk : τ ^ 2 ^ k = 1) :
    ∃ (π : Bool) (K : Type) (_ : Field K) (hK : PiField π p f K) (_ : ModThree π (p ^ f))
      (τK : K) (_ : τK ^ 3 = 1) (_ : τK ≠ 1)
      (dM cM : projImage (slPi π 3 (p ^ f) K))
      (_ : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau ‹_›))
      (_ : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
      (β : MulAut (projImage (slPi π 3 (p ^ f) K))),
      β dM = dM ∧ β cM = cM ∧ β ^ 2 ^ k = 1 ∧
        (∀ y ∈ torusM hK hp2, (∃ m : ℕ, y ^ 2 ^ m = 1) → β y = y) ∧
        (β = 1 → τ = 1) := by
  have htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁ :=
    KF163L3.transitive_of_card_nine hf hiso h9 hE9
  obtain ⟨π, K, _, hK, hq, τK, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd, Φ, hΦE⟩ :=
    exists_hessian_equiv hf hiso hEe hE9 htr
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set Ê : Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
    Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hÊ
  have hΦE' : ∀ m ∈ Ê, Φ m ∈ E := fun m hm =>
    hΦE ▸ Subgroup.mem_map_of_mem Φ.toMonoidHom hm
  have hdM1 : Φ dM ∈ E := hΦE' dM (Subgroup.mem_sup_left (Subgroup.mem_zpowers dM))
  have hdMne : Φ dM ≠ 1 := by
    intro h1
    have h2 : dM = 1 := Φ.injective (by rw [h1, map_one])
    rw [h2, orderOf_one] at hdo
    omega
  obtain ⟨w, hwN, hwx⟩ := htr (Φ dM) hdM1 hdMne x hxE hx1
  set Ψ : projImage (slPi π 3 (p ^ f) K) ≃* X := Φ.trans (MulAut.conj w) with hΨ
  have hΨd : Ψ dM = x := by
    rw [hΨ, MulEquiv.trans_apply, MulAut.conj_apply]
    exact hwx
  have hΨE : Ê.map Ψ.toMonoidHom = E := by
    rw [hΨ]
    change Ê.map ((MulAut.conj w).toMonoidHom.comp Φ.toMonoidHom) = E
    rw [← Subgroup.map_map, hΦE]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hwN
  have hΨE' : ∀ m ∈ Ê, Ψ m ∈ E := fun m hm =>
    hΨE ▸ Subgroup.mem_map_of_mem Ψ.toMonoidHom hm
  set β : MulAut (projImage (slPi π 3 (p ^ f) K)) := MulAut.congr Ψ.symm τ with hβ
  have hβd : β dM = dM := by
    change Ψ.symm (τ (Ψ dM)) = dM
    rw [hΨd, hτE x hxE, ← hΨd, MulEquiv.symm_apply_apply]
  have hβc : β cM = cM := by
    change Ψ.symm (τ (Ψ cM)) = cM
    rw [hτE _ (hΨE' cM (Subgroup.mem_sup_right (Subgroup.mem_zpowers cM))),
      MulEquiv.symm_apply_apply]
  have hβk : β ^ 2 ^ k = 1 := by
    rw [hβ, ← map_pow, hk, map_one]
  have hDΘ : D ≤ (torusM hK hp2).map Ψ.toMonoidHom := by
    have hθ : (thetaC dM).map Ψ.toMonoidHom = thetaC x := by
      rw [thetaC_map_equiv, hΨd]
    refine hDx.trans (hθ ▸ Subgroup.map_mono (thetaC_le_torusM hK hp2 hτ hτ1 hdM))
  have hcommΘ : ∀ a ∈ (torusM hK hp2).map Ψ.toMonoidHom,
      ∀ b ∈ (torusM hK hp2).map Ψ.toMonoidHom, a * b = b * a := by
    rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
    rw [← map_mul, ← map_mul, torusM_comm hK hp2 ha' hb']
  have hdMN : dM ∈ Subgroup.normalizer (torusM hK hp2 : Set _) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      change MulAut.conj dM z ∈ torusM hK hp2
      rw [MulAut.conj_apply]
      have h := commute_dM_of_mem_torusM hK hp2 hτ hdM hz
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
      exact hz
    · rw [Subgroup.card_map_of_injective (MulAut.conj dM).injective]
  have hcMN : cM ∈ Subgroup.normalizer (torusM hK hp2 : Set _) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨A, -, hA⟩ := exists_lift z
      have hoff := offDiag_of_mem_torusM hK hp2 hz hA
      have hAd : (A : Matrix (Fin 3) (Fin 3) K) =
          Matrix.diagonal ![(A : Matrix (Fin 3) (Fin 3) K) 0 0,
            (A : Matrix (Fin 3) (Fin 3) K) 1 1, (A : Matrix (Fin 3) (Fin 3) K) 2 2] :=
        eq_diagonal_of_offDiag hoff
      refine mem_torusM_of_offDiag hK hp2 (A := cycThree * A * cycThree⁻¹) ?_ ?_
      · change ProjGenLinGroup.mk (cycThree * A * cycThree⁻¹) =
          (cM : ProjGenLinGroup (Fin 3) K) * (z : ProjGenLinGroup (Fin 3) K) *
            (cM : ProjGenLinGroup (Fin 3) K)⁻¹
        rw [hcM, ← hA, ← map_inv, ← map_mul, ← map_mul]
      · intro i j hij
        rw [Units.val_mul, Units.val_mul, hAd, cyc_mul_diagonal_mul_inv']
        exact Matrix.diagonal_apply_ne _ hij
    · rw [Subgroup.card_map_of_injective (MulAut.conj cM).injective]
  have hÊN : Ê ≤ Subgroup.normalizer (torusM hK hp2 : Set _) := by
    rw [hÊ]
    exact sup_le (Subgroup.zpowers_le.mpr hdMN) (Subgroup.zpowers_le.mpr hcMN)
  have hEΘ : E ≤ Subgroup.normalizer ((torusM hK hp2).map Ψ.toMonoidHom : Set X) := by
    rw [← Subgroup.map_equiv_normalizer_eq (torusM hK hp2) Ψ, ← hΨE]
    exact Subgroup.map_mono hÊN
  have hβfix : ∀ y ∈ torusM hK hp2, (∃ m : ℕ, y ^ 2 ^ m = 1) → β y = y := by
    intro y hy hy2
    have hyΘ : Ψ y ∈ (torusM hK hp2).map Ψ.toMonoidHom :=
      Subgroup.mem_map_of_mem Ψ.toMonoidHom hy
    obtain ⟨m, hm⟩ := hy2
    have hym : (Ψ y) ^ 2 ^ m = 1 := by rw [← map_pow, hm, map_one]
    have hyD : Ψ y ∈ D := mem_of_isMaxInvTwo hD hDΘ hEΘ hcommΘ hyΘ hym
    change Ψ.symm (τ (Ψ y)) = y
    rw [hτD (Ψ y) hyD, MulEquiv.symm_apply_apply]
  refine ⟨π, K, inferInstance, hK, hq, τK, hτ, hτ1, dM, cM, hdM, hcM, β,
    hβd, hβc, hβk, hβfix, fun h1 => ?_⟩
  have h2 : MulAut.congr Ψ β = τ := MulEquiv.apply_symm_apply (MulAut.congr Ψ) τ
  rw [h1, map_one] at h2
  exact h2.symm

theorem eq_one_of_fix_of_pow_two {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hiso : Sec4.IsoLThreePi X p f)
    (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8)) {E : Subgroup X}
    (hEe : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {D : Subgroup X}
    (hD : IsMaxInvTwo E D) (τ : MulAut X) (hτE : ∀ e ∈ E, τ e = e) (hτD : ∀ d ∈ D, τ d = d)
    {k : ℕ} (hk : τ ^ 2 ^ k = 1) : τ = 1 := by
  have hp := Fact.out (p := p.Prime)
  have hmod : p ^ f % 3 = 1 ∨ p ^ f % 3 = 2 := by
    rcases hiso with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hp3 : 3 < p := by
    have hne : p ≠ 3 := by
      intro h3
      have h0 : 3 ^ f % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
      rcases hmod with h1 | h2
      · rw [h3] at h1; omega
      · rw [h3] at h2; omega
    have := hp.two_le
    omega
  have hD3 : ¬ 3 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := D)).mp hD.1.1
    rw [hn]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  obtain ⟨x, hxE, hx1, hDx, -⟩ :=
    KF163L3.exists_le_thetaC_comm hp2 hf hiso h9 hEe hE9 hD3 hD.1.2
  obtain ⟨π, K, _, hK, hq, τK, hτ, hτ1, dM, cM, hdM, hcM, β, hβd, hβc, hβk, hβfix, hβτ⟩ :=
    exists_model_aut hp2 hf hiso h9 hEe hE9 hD hxE hx1 hDx τ hτE hτD hk
  have hβ1 : β = 1 := by
    cases π
    · exact KF163L3.eq_one_of_pow_two_projImage_unitary hK hq hp3 hτ hτ1 hdM hcM β hβd hβc hβk
    ·
      haveI : Finite K := hK.finite
      have hcardK : Nat.card K = p ^ f := by
        simpa [piCard] using hK.card
      obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, orderOf ζ = 2 ^ (p ^ f - 1).factorization 2 := by
        obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
        have hq1 : p ^ f - 1 ≠ 0 := by
          have := pow_pos hp.pos f
          omega
        have hdvd : 2 ^ (p ^ f - 1).factorization 2 ∣ orderOf g := by
          rw [hg, Nat.card_units, hcardK]
          exact (Nat.prime_two.pow_dvd_iff_le_factorization hq1).mpr le_rfl
        refine ⟨g ^ (orderOf g / 2 ^ (p ^ f - 1).factorization 2), ?_⟩
        have hx : orderOf g ≠ 0 := by
          rw [hg, Nat.card_units, hcardK]
          have := pow_pos hp.pos f
          omega
        exact orderOf_pow_orderOf_div hx hdvd
      have hdet : ((diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
        rw [coe_diagUnits, Matrix.det_diagonal, Fin.prod_univ_three]
        simp
      have hmem : diagUnits ζ ζ⁻¹ 1 ∈ slPi true 3 (p ^ f) K := by
        change diagUnits ζ ζ⁻¹ 1 ∈ CFSG.Open.StatedSL 3 K
        exact Subgroup.subset_closure (by simpa using hdet)
      set yM : projImage (slPi true 3 (p ^ f) K) :=
        ⟨ProjGenLinGroup.mk (diagUnits ζ ζ⁻¹ 1),
          Subgroup.mem_map_of_mem ProjGenLinGroup.mk hmem⟩ with hyM
      have hyMlift : (yM : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (diagUnits ζ ζ⁻¹ 1) := rfl
      have hpow : yM ^ 2 ^ (p ^ f - 1).factorization 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hyMlift, ← map_pow, ← hζ,
          CFSG.RankThree.PartTwo.Sec12.KS128Move.diagUnits_pow, pow_orderOf_eq_one,
          inv_pow, pow_orderOf_eq_one, inv_one, one_pow,
          CFSG.RankThree.PartTwo.Sec12.KS128Move.diagUnits_one, map_one, Subgroup.coe_one]
      have hyMtor : yM ∈ torusM hK hp2 := by
        refine mem_torusM_of_offDiag hK hp2 hyMlift.symm ?_
        intro i j hij
        rw [coe_diagUnits]
        exact Matrix.diagonal_apply_ne _ hij
      have hβy : β yM = yM := hβfix yM hyMtor ⟨_, hpow⟩
      exact KF163L3.eq_one_of_pow_two_projImage_linear hK hq hp2 (fun h => h9 (Or.inl h))
        hτ hτ1 hζ (dM := dM) (cM := cM) (yM := yM) hdM hcM hyMlift β hβd hβc hβy hβk
  exact hβτ hβ1

end CFSG.RankThree.PartTwo.KFacts.KF163L3

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem ks163P6CentL3 : KS163P6CentL3 := by
  intro L _ _ p f _ hp2 hf hiso h9 E hEe hE9 D hD T hT hDT hcent hET
  have hp := Fact.out (p := p.Prime)
  haveI : Nontrivial L := by
    have h1 : 1 < Nat.card E := by rw [hE9]; norm_num
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨⟨x, hx⟩, hne⟩ := exists_ne (1 : E)
    exact ⟨x, 1, fun h => hne (Subtype.ext h)⟩
  haveI : Group.IsPerfect L := by
    rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · haveI : Group.IsPerfect (projSL 3 (GaloisField p f)) :=
        (Sec13.isPerfect_center_projSL p f hf hq).1
      exact Group.IsPerfect.ofSurjective (f := (φ.symm : projSL 3 (GaloisField p f) →* L))
        φ.symm.surjective
    · have hq2 : 2 < p ^ f := by
        have hp3 : 3 ≤ p := by
          have h2 := hp.two_le
          rcases hp.eq_two_or_odd with h | h
          · exact absurd h hp2
          · omega
        calc 2 < 3 := by norm_num
          _ ≤ p ^ f := le_trans hp3 (by simpa using Nat.pow_le_pow_right hp.pos hf)
      haveI : Group.IsPerfect (projSU 3 p f) :=
        (Sec13.isPerfect_center_projSU p f hf hq hq2).1
      exact Group.IsPerfect.ofSurjective (f := (φ.symm : projSU 3 p f →* L))
        φ.symm.surjective
  have hZ : Subgroup.center L = ⊥ := Sec4.RonanK429.center_eq_bot_of_isoLThreePi hf hiso
  have hc : Function.Injective (MulAut.conj : L →* MulAut L) :=
    CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hZ
  have hD3 : ¬ 3 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := D)).mp hD.1.1
    rw [hn]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  obtain ⟨x, hxE, hx1, hDx, hcomm⟩ :=
    KF163L3.exists_le_thetaC_comm hp2 hf hiso h9 hEe hE9 hD3 hD.1.2
  have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    hcomm a (hDx ha) b (hDx hb)
  set C : Subgroup (MulAut L) :=
    Subgroup.centralizer ((D.map (MulAut.conj : L →* MulAut L) : Subgroup (MulAut L)) :
      Set (MulAut L)) with hC
  have hInnD : D.map (MulAut.conj : L →* MulAut L) ≤ C := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d', hd', rfl⟩
    show MulAut.conj d' * MulAut.conj d = MulAut.conj d * MulAut.conj d'
    rw [← map_mul, ← map_mul, hDab d hd d' hd']
  have hTC : T ≤ C := by
    rw [hC] at hcent ⊢
    rwa [sup_eq_right.mpr hInnD] at hcent
  refine KF163Rigid.eq_map_conj_of_forall_fix hZ
    (CFSG.Open.IsElemAbelian.isPGroup hEe) hD hT hDT hET ?_
  intro τ hτT hτE
  obtain ⟨n, hn⟩ := hT.exists_pow_pow_eq_one ⟨τ, hτT⟩
  have hτn : τ ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hτD : ∀ d ∈ D, τ d = d := by
    intro d hd
    have hcd := (Subgroup.mem_centralizer_iff.mp (hTC hτT)) (MulAut.conj d)
      (Subgroup.mem_map_of_mem (MulAut.conj : L →* MulAut L) hd)
    refine hc ?_
    calc MulAut.conj (τ d) = τ * MulAut.conj d * τ⁻¹ :=
          (CFSG.HardMathSupport.Lang.Triality.mulAut_mul_conj_mul_inv τ d).symm
      _ = MulAut.conj d := by rw [← hcd]; group
  exact KF163L3.eq_one_of_fix_of_pow_two hp2 hf hiso h9 hEe hE9 hD τ hτE hτD hτn

theorem ks163P6Cent :
    KS163P6Cent :=
  ks163P6Cent_of_l3 ks163P6CentL3

end CFSG.RankThree.PartTwo.KFacts
