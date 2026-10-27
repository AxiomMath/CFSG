module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
import CFSG.Quasithin.Background.F918V3T3A

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7A3AJAux_z_ne_zero {p m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    (hfr : A3Frame p m θ z) : z ≠ 0 := by
  rcases hfr.2.2 with ⟨-, hz⟩ | ⟨-, hz⟩
  · exact hz
  · intro hz0
    exact hz 0 (Submodule.zero_mem _) (by rw [map_zero, hz0])

private theorem hdRo7A3AJAux_fixed_mem_span {p m : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    (hp3 : p = 3) (hfr : A3Frame p m θ z) (hpm : p ∣ m) (hm3 : 3 ≤ m)
    {AX : Subgroup (V ≃ₗ[ZMod p] V)} (hAX : ∀ g, g ∈ AX ↔ A3P p m θ z g)
    {v : V} (hv : ∀ g ∈ AX, g v = v) : v ∈ Submodule.span (ZMod p) ({z} : Set V) := by
  obtain ⟨u, hu, c, hv'⟩ := hfr.2.1 v
  rw [hv']
  have hconst : ∀ i j : Fin m, u i = u j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨t, ψ, ht, htz, hψ, hψz, hform, -⟩ := a3_transp hp3 hfr hpm hm3 hij
      have hP : A3P p m θ z t := ⟨Equiv.swap i j, ht, htz⟩
      have htv : t (θ u + c • z) = θ u + c • z := by
        rw [← hv']
        exact hv t ((hAX t).mpr hP)
      have hψv : ψ (θ u + c • z) = u i - u j := by
        rw [map_add, hψ u hu, map_smul, hψz, smul_zero, add_zero]
      rw [hform, hψv] at htv
      have hzero : (u i - u j) • θ (Pi.single i 1 - Pi.single j 1) = 0 :=
        sub_eq_self.mp htv
      have hY : θ (Pi.single i 1 - Pi.single j 1) ≠ 0 :=
        a3_theta_single_sub_ne_zero hfr hm3 hij
      by_contra hne
      exact hY ((smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne))
  let i0 : Fin m := ⟨0, by omega⟩
  obtain ⟨c', hc'⟩ := (show ∃ c' : ZMod p, u = fun _ => c' from
    ⟨u i0, funext fun i => hconst i i0⟩)
  rw [hc']
  have htheta : θ (fun _ : Fin m => c') ∈ Submodule.span (ZMod p) ({z} : Set V) := by
    have hvec : (fun _ : Fin m => c') = c' • (fun _ : Fin m => 1) := by
      funext i
      simp
    rw [hvec, map_smul]
    rcases hfr.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]
      exact Submodule.smul_mem _ c' (Submodule.subset_span (Set.mem_singleton z))
    · rw [h1, smul_zero]
      exact Submodule.zero_mem _
  exact Submodule.add_mem _ htheta
    (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton z)))

private theorem hdRo7A3AJAux_model_card_le
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    (hp3 : p = 3) (hfr : A3Frame p m θ z) (hpm : p ∣ m) (hm3 : 3 ≤ m)
    (hfin : Module.finrank (ZMod p) V = m - 1) {Bs X : Subgroup G}
    (ι : Additive ↥Bs ≃+ V)
    (hAX : ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ A3P p m θ z g)
    {Λ : Type} [Fintype Λ] {V' : Type} [AddCommGroup V'] [Module (ZMod p) V']
    (ι' : Additive ↥Bs ≃+ V') (φ : Λ → MulAut ↥Bs) (h : Λ → V')
    (α : Λ → Module.Dual (ZMod p) V')
    (hformula : ∀ i w, ggLin (p := p) ι' (φ i) w = w - α i w • h i)
    (hgenX : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) :
    m - 2 ≤ Nat.card Λ := by
  classical
  have hz : z ≠ 0 := hdRo7A3AJAux_z_ne_zero hfr
  have hfinV : Finite V := a3_finite hfr
  let Φ : Additive ↥Bs →+ (Λ → ZMod p) :=
    { toFun := fun β i => α i (ι' β)
      map_zero' := by
        ext i
        simp
      map_add' := by
        intro x y
        ext i
        simp }
  have hmem_ker : ∀ β ∈ Φ.ker, ∀ i, α i (ι' β) = 0 := by
    intro β hβ i
    have := congrFun (AddMonoidHom.mem_ker.mp hβ) i
    simpa [Φ] using this
  have hker_fix : ∀ β ∈ Φ.ker, ∀ i, Additive.ofMul (φ i (Additive.toMul β)) = β := by
    intro β hβ i
    have hβi := hmem_ker β hβ i
    have key : ggLin (p := p) ι' (φ i) (ι' β) = ι' β := by
      have h := hformula i (ι' β)
      rwa [hβi, zero_smul, sub_zero] at h
    have h2 := ggLin_apply_ofMul (p := p) ι' (φ i) (Additive.toMul β)
    have h3 : ι' (Additive.ofMul (φ i (Additive.toMul β))) = ι' β := by
      rw [← h2]
      exact key
    exact ι'.injective h3
  have hker_fixed : ∀ β ∈ Φ.ker,
      ∀ g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι), g (ι β) = ι β := by
    intro β hβ g hg
    have hstab : ∀ i, ggLin (p := p) ι (φ i) ∈
        MulAction.stabilizer (V ≃ₗ[ZMod p] V) (ι β) := by
      intro i
      have h1 : (ggLin (p := p) ι (φ i)) (ι β) = ι β := by
        have h := ggLin_apply_ofMul (p := p) ι (φ i) (Additive.toMul β)
        rw [hker_fix β hβ i] at h
        exact h
      rw [MulAction.mem_stabilizer_iff]
      simpa using h1
    have hle : (ggAutomizer X Bs).map (ggLin (p := p) ι) ≤
        MulAction.stabilizer (V ≃ₗ[ZMod p] V) (ι β) := by
      rw [hgenX, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      intro a ha
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨i, rfl⟩ := hx
      exact hstab i
    have := hle hg
    rwa [MulAction.mem_stabilizer_iff] at this
  have hker_span : ∀ β ∈ Φ.ker, ι β ∈ Submodule.span (ZMod p) ({z} : Set V) :=
    fun β hβ => hdRo7A3AJAux_fixed_mem_span hp3 hfr hpm hm3 hAX (hker_fixed β hβ)
  have hspan_card : Nat.card (Submodule.span (ZMod p) ({z} : Set V)) = p := by
    have hspan_fin : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({z} : Set V)) = 1 :=
      finrank_span_singleton (K := ZMod p) hz
    have h := FiniteField.pow_finrank_eq_natCard p
      (Submodule.span (ZMod p) ({z} : Set V))
    rw [hspan_fin] at h
    simpa using h.symm
  have hker_le : Nat.card ↥Φ.ker ≤ p := by
    have hinj : Function.Injective (fun β : ↥Φ.ker =>
        (⟨ι (β : Additive ↥Bs), hker_span (β : Additive ↥Bs) β.2⟩ :
          Submodule.span (ZMod p) ({z} : Set V))) := by
      intro β1 β2 h
      apply Subtype.ext
      have h' : ι (β1 : Additive ↥Bs) = ι (β2 : Additive ↥Bs) :=
        congrArg (fun x : Submodule.span (ZMod p) ({z} : Set V) => (x : V)) h
      exact ι.injective h'
    calc Nat.card ↥Φ.ker ≤ Nat.card (Submodule.span (ZMod p) ({z} : Set V)) :=
          Nat.card_le_card_of_injective _ hinj
      _ = p := hspan_card
  have hcard_bs : Nat.card (Additive ↥Bs) = p ^ (m - 1) := by
    rw [Nat.card_congr ι.toEquiv]
    have h := FiniteField.pow_finrank_eq_natCard p V
    rw [hfin] at h
    exact h.symm
  have hrange_le : Nat.card ↥Φ.range ≤ p ^ Nat.card Λ := by
    have hle : Nat.card ↥Φ.range ≤ Nat.card (Λ → ZMod p) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    have hpi : Nat.card (Λ → ZMod p) = p ^ Nat.card Λ := by
      rw [Nat.card_pi]
      simp [ZMod.card]
    rwa [hpi] at hle
  have hcomb : p ^ (m - 1) ≤ p ^ (Nat.card Λ + 1) := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Φ.ker
    have h2 : Nat.card (Additive ↥Bs ⧸ Φ.ker) = Nat.card ↥Φ.range :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Φ).toEquiv
    rw [h2, hcard_bs] at h1
    calc p ^ (m - 1) = Nat.card ↥Φ.range * Nat.card ↥Φ.ker := h1
      _ ≤ p ^ Nat.card Λ * p := Nat.mul_le_mul hrange_le hker_le
      _ = p ^ (Nat.card Λ + 1) := by rw [pow_succ]
  have hle' : m - 1 ≤ Nat.card Λ + 1 :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcomb
  omega

private theorem hdRo7A3AJAux_nonabelian_of_data
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    {n : ℕ} (hn5 : 5 ≤ n)
    {Λ K : Type} [Fintype Λ] [Fintype K]
    {MJ : CoxeterMatrix K}
    (hWeylMJ : GGIsWeylMatrix MJ)
    (fJ : MJ.Group ≃* ↥(ggAutomizer J Bs))
    (hΛcard : Nat.card Λ ≤ Nat.card K + 3)
    (hn : n ≤ Nat.card Λ) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  classical
  by_contra h
  push Not at h
  have hnoedge : ∀ j j' : K, j ≠ j' → MJ.M j j' = 2 := by
    intro j j' hne
    have hcomm : fJ (MJ.simple j) * fJ (MJ.simple j') =
        fJ (MJ.simple j') * fJ (MJ.simple j) :=
      Subtype.ext (h (fJ (MJ.simple j)) (fJ (MJ.simple j)).2
        (fJ (MJ.simple j')) (fJ (MJ.simple j')).2)
    have hsimple_comm : MJ.simple j * MJ.simple j' = MJ.simple j' * MJ.simple j :=
      fJ.injective (by simpa [map_mul] using hcomm)
    have hsq : (MJ.simple j * MJ.simple j') ^ 2 = 1 := by
      have hc : Commute (MJ.simple j) (MJ.simple j') := hsimple_comm
      rw [hc.mul_pow]
      rw [show MJ.simple j ^ 2 = 1 from by
            rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
            exact CoxeterSystem.simple_mul_simple_self MJ.toCoxeterSystem j,
          show MJ.simple j' ^ 2 = 1 from by
            rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
            exact CoxeterSystem.simple_mul_simple_self MJ.toCoxeterSystem j']
      simp
    have horder : orderOf (MJ.simple j * MJ.simple j') = MJ.M j j' := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple MJ.toCoxeterSystem j j'
    have hdvd : MJ.M j j' ∣ 2 := by
      rw [← horder]
      exact orderOf_dvd_iff_pow_eq_one.mpr hsq
    have h1 : MJ.M j j' ≠ 1 := MJ.off_diagonal j j' hne
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
    · exact (h1 h').elim
    · exact h'
  have hsub : Subsingleton K := by
    refine ⟨fun j j' => ?_⟩
    by_contra hne
    have hpath := ggRC_weyl_connected hWeylMJ j j'
    have hEq : j = j' := by
      induction hpath with
      | refl => rfl
      | tail _ hstep _ =>
          exact (hstep.2 (hnoedge _ _ hstep.1)).elim
    exact hne hEq
  have hKpos : 0 < Nat.card K := by omega
  have : Nonempty K := by
    rw [← Fintype.card_pos_iff]
    simpa [Nat.card_eq_fintype_card] using hKpos
  have hKcard : Nat.card K = 1 := by
    have : Fintype.card K = 1 := Fintype.card_eq_one_iff.mpr
      ⟨Classical.arbitrary K, fun x => Subsingleton.elim x _⟩
    simpa [Nat.card_eq_fintype_card] using this
  omega

private theorem hdRo7A3AJAux_sideDatum_nonabelian
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    (hp3 : p = 3) (hfr : A3Frame p m θ z) (hpm : p ∣ m) (hm3 : 3 ≤ m) (hm7 : 7 ≤ m)
    (hfin : Module.finrank (ZMod p) V = m - 1)
    (ι : Additive ↥Bs ≃+ V)
    (hAX : ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ A3P p m θ z g)
    (hD : GGResSideDatum p Bs X J) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  obtain ⟨Λ, instΛ, decΛ, b, M, C, MJ, V', instV, instMod, ι', φ, hv, hα,
    hWeylM, hCartan, hWeylMJ, hMJsub, hformula, hrefl, hpair, ⟨f, hf⟩, hgenX,
    ⟨fJ, -⟩, hgenJ, hconj⟩ := hD
  let : Fintype Λ := instΛ
  let : DecidableEq Λ := decΛ
  let : AddCommGroup V' := instV
  let : Module (ZMod p) V' := instMod
  have hn : m - 2 ≤ Nat.card Λ :=
    hdRo7A3AJAux_model_card_le hp3 hfr hpm hm3 hfin ι hAX ι' φ hv hα hformula hgenX
  have hΛcard : Nat.card Λ ≤ Nat.card {j : Λ // j ≠ b} + 3 := by
    have hEq : Nat.card Λ = Nat.card {j : Λ // j = b} +
        Nat.card {j : Λ // j ≠ b} := by
      rw [← Nat.card_congr (Equiv.sumCompl (fun j : Λ => j = b)), Nat.card_sum]
    have hsingle : Nat.card {j : Λ // j = b} = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have : (Finset.univ.filter (fun j : Λ => j = b)) = {b} := by
        ext j
        simp
      rw [this]
      simp
    omega
  exact hdRo7A3AJAux_nonabelian_of_data (p := p) (Bs := Bs) (J := J) (n := m - 2)
    (by omega) hWeylMJ fJ hΛcard hn

private theorem hdRo7A3AJAux_le3_nonabelian
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    (hp3 : p = 3) (hfr : A3Frame p m θ z) (hpm : p ∣ m) (hm3 : 3 ≤ m) (hm7 : 7 ≤ m)
    (hfin : Module.finrank (ZMod p) V = m - 1)
    (ι : Additive ↥Bs ≃+ V)
    (hAX : ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ A3P p m θ z g)
    (hD : GGResLeviSideDatumLE3 p Bs X J) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  obtain ⟨Λ, instΛ, decΛ, S, M, C, MJ, V', instV, instMod, ι', φ, hv, hα,
    hS2, hS3, hWeylM, hCartan, hWeylMJ, hMJsub, hformula, hrefl, hpair, ⟨f, hf⟩, hgenX,
    ⟨fJ, -⟩, hgenJ, hconj⟩ := hD
  let : Fintype Λ := instΛ
  let : DecidableEq Λ := decΛ
  let : AddCommGroup V' := instV
  let : Module (ZMod p) V' := instMod
  have hn : m - 2 ≤ Nat.card Λ :=
    hdRo7A3AJAux_model_card_le hp3 hfr hpm hm3 hfin ι hAX ι' φ hv hα hformula hgenX
  have hΛcard : Nat.card Λ ≤ Nat.card {j : Λ // j ∉ S} + 3 := by
    have hEq : Nat.card Λ = Nat.card {j : Λ // j ∈ S} +
        Nat.card {j : Λ // j ∉ S} := by
      rw [← Nat.card_congr (Equiv.sumCompl (fun j : Λ => j ∈ S)), Nat.card_sum]
    have hSsub : Nat.card {j : Λ // j ∈ S} = S.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe S
    omega
  exact hdRo7A3AJAux_nonabelian_of_data (p := p) (Bs := Bs) (J := J) (n := m - 2)
    (by omega) hWeylMJ fJ hΛcard hn

private theorem hdRo7A3AJAux_labelIso_twA_twA {l1 l2 : LargeEvenLabel}
    (h : GGLabelIso l1 l2) (h1 : l1.tag = .twA) (h2 : l2.tag = .twA) : l1 = l2 := by
  obtain ⟨t1, r1, n1⟩ := l1
  obtain ⟨t2, r2, n2⟩ := l2
  simp only [GGLabelIso] at h
  simp only at h1 h2
  rw [h1, h2] at h ⊢
  simpa using h

private theorem hdRo7A3AJAux_labelIso_twA_left_ne {l1 l2 : LargeEvenLabel}
    (h : GGLabelIso l1 l2) (h1 : l1.tag = .twA)
    (h2 : l2.tag = .A ∨ l2.tag = .D ∨ l2.tag = .E8 ∨ l2.tag = .triD4 ∨
      l2.tag = .G2 ∨ l2.tag = .twE6) : False := by
  obtain ⟨t1, r1, n1⟩ := l1
  obtain ⟨t2, r2, n2⟩ := l2
  simp only [GGLabelIso] at h
  simp only at h1 h2
  rw [h1] at h
  rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 <;> rw [h2] at h <;> simp at h

private theorem hdRo7A3AJAux_not_nonLevi {G : Type} [Group G] [Finite G] {p : ℕ}
    {J X : Subgroup G} (hRig : GGLabelRigidInput)
    (hSU : GGResRowAt ggRowSUCorank3 p J X)
    (hNL : GGResRowAt ggRowNonLevi p J X) : False := by
  obtain ⟨lJ1, lX1, hJ1Λ, hX1Λ, hJ1lab, hX1lab, hp3, hJ1tag, hJ1n, hX1tag, hX1n, hXrank,
    hX6, h3X⟩ := hSU
  obtain ⟨lJ2, lX2, hJ2Λ, hX2Λ, hJ2lab, hX2lab, hNL'⟩ := hNL
  have hisoJ : GGLabelIso lJ1 lJ2 := hRig lJ1 lJ2 _ hJ1Λ hJ2Λ hJ1lab hJ2lab
  have hisoX : GGLabelIso lX1 lX2 := hRig lX1 lX2 _ hX1Λ hX2Λ hX1lab hX2lab
  have hJrank : 5 ≤ lJ1.rank := by omega
  rcases hNL' with h2 | hmax | htri | htri2 | h7 | htw2
  · rcases h2 with ⟨hJA, -, -, -⟩ | ⟨hJtwA, -, hdvdr, hXeq⟩ |
      ⟨hJD, -, -, -⟩ | ⟨hJD, -, -, -⟩
    · have hJAtag : lJ2.tag = .A := by rw [hJA]
      exact hdRo7A3AJAux_labelIso_twA_left_ne hisoJ hJ1tag (Or.inl hJAtag)
    · have hJeq : lJ1 = lJ2 := hdRo7A3AJAux_labelIso_twA_twA hisoJ hJ1tag hJtwA
      have hX2tag : lX2.tag = .twA := by rw [hXeq]
      have hX12 : lX1 = lX2 := hdRo7A3AJAux_labelIso_twA_twA hisoX hX1tag hX2tag
      have h1 : lX1.rank = lJ1.rank + 3 := hXrank
      have h2 : lX1.rank = lJ2.rank + 2 := by rw [hX12, hXeq]
      rw [hJeq] at h1
      omega
    · have hJDtag : lJ2.tag = .D := by rw [hJD]
      exact hdRo7A3AJAux_labelIso_twA_left_ne hisoJ hJ1tag
        (Or.inr (Or.inl hJDtag))
    · have hJDtag : lJ2.tag = .D := by rw [hJD]
      exact hdRo7A3AJAux_labelIso_twA_left_ne hisoJ hJ1tag
        (Or.inr (Or.inl hJDtag))
  · rcases hmax with ⟨hJA, -, -, -⟩ | ⟨hJeq2, -, -, hXeq2⟩
    · have hJAtag : lJ2.tag = .A := by rw [hJA]
      exact hdRo7A3AJAux_labelIso_twA_left_ne hisoJ hJ1tag (Or.inl hJAtag)
    · have hJtwA : lJ2.tag = .twA := by rw [hJeq2]
      have hX2tag : lX2.tag = .E8 := by rw [hXeq2]
      exact hdRo7A3AJAux_labelIso_twA_left_ne hisoX hX1tag
        (Or.inr (Or.inr (Or.inl hX2tag)))
  · rcases htri with ⟨hJtri, -, -⟩ | ⟨hJG2, -, -⟩
    · exact hdRo7A3AJAux_labelIso_twA_left_ne hisoJ hJ1tag
        (Or.inr (Or.inr (Or.inr (Or.inl hJtri))))
    · exact hdRo7A3AJAux_labelIso_twA_left_ne hisoJ hJ1tag
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hJG2)))))
  · obtain ⟨hJtri, -, -, -⟩ := htri2
    exact hdRo7A3AJAux_labelIso_twA_left_ne hisoJ hJ1tag
      (Or.inr (Or.inr (Or.inr (Or.inl hJtri))))
  · obtain ⟨hp7, -⟩ := h7
    omega
  · obtain ⟨hJtwA, hJrank2, -, -, -⟩ := htw2
    have hJeq : lJ1 = lJ2 := hdRo7A3AJAux_labelIso_twA_twA hisoJ hJ1tag hJtwA
    rw [hJeq] at hJrank
    omega

private theorem hdRo7A3AJAux_three_dvd_card_of_row {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {J X : Subgroup G}
    (hrow : GGResRowAt ggRowSUCorank3 p J X) : p ∣ Nat.card J := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hp3, hJtag, hJn, hXtag, hXn, hXrank,
    hX6, h3X⟩ := hrow
  have hJrank : 5 ≤ labJ.rank := by omega
  subst hp3
  have hJlab' : LargeEvenRecipeUnitary (labJ.rank + 1) (2 ^ labJ.n)
      (fun R' _ _ _ => Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* R')) := by
    simpa only [GGHasLabel, LargeEvenRawDatum, hJtag] using hJlab
  obtain ⟨K, hKfield, hKfin, hKcard, hKiso⟩ := hJlab'
  let : Field K := hKfield
  let : Finite K := hKfin
  obtain ⟨e⟩ := hKiso
  have hcard_eq : Nat.card (↥J ⧸ Subgroup.center ↥J) =
      Nat.card (LargeEvenProj
        (LargeEvenSUGroup (Fin (labJ.rank + 1)) K (2 ^ labJ.n))) :=
    Nat.card_congr e.toEquiv
  have h3 : 3 ∣ Nat.card
      (LargeEvenProj (LargeEvenSUGroup (Fin (labJ.rank + 1)) K (2 ^ labJ.n))) := by
    exact CFSG.Quasithin.F918V3T3.three_dvd_card_PSU_of_three_le
      (n := labJ.rank + 1) (q := 2 ^ labJ.n) (K := K) (by omega) (by positivity)
  rw [← hcard_eq] at h3
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)]
  exact dvd_mul_of_dvd_left h3 _

theorem a3_aj_holds : A3AJLeaf := by
  intro hX hJ hRig hLB G _ _ p B Bs x L D J y K hH inst hmL hmK hrow
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hI : GGThmIHyp p B x L := hcfg.1
  have hStd : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hJL : J ≤ L := by
    have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
      hStd.1.2.2.2.2.2.1
    exact hcomp.1.trans inf_le_left
  have hpJ : p ∣ Nat.card J := by
    rcases hrow with hrow | hrow
    · exact hdRo7A3AJAux_three_dvd_card_of_row hrow
    · exact hdRo7A3AJAux_three_dvd_card_of_row hrow
  have hJK : J ≤ K := le_of_ggNbr hLB hI hStd hpJ hH.2.2.2.2.1
  have hle : ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs :=
    le_inf (ggAutomizer_mono Bs hJL) (ggAutomizer_mono Bs hJK)
  refine ⟨?_, hle⟩
  rcases hrow with hrowL | hrowK
  · obtain ⟨m, V, hVadd, hVmod, ι, θ, hx, hp3, hm9, h3m, hfr, hmod⟩ := hmL hrowL
    let : AddCommGroup V := hVadd
    let : Module (ZMod p) V := hVmod
    have hpm : p ∣ m := by rw [hp3]; exact h3m
    have hm2 : 2 ≤ m := by omega
    have hfin : Module.finrank (ZMod p) V = m - 1 := a3_finrank hfr hpm hm2
    have hXD : GGResXDatum p Bs L := by
      rcases (hX G p B Bs x L D J y K hH).1 with h | h7
      · exact h
      · exfalso
        obtain ⟨-, -, -, -, -, -, hp7, -⟩ := h7
        omega
    rcases (hJ G p B Bs x L D J y K hH).1 hXD with hSD | hLE3 | hNL
    · exact hdRo7A3AJAux_sideDatum_nonabelian hp3 hfr hpm (by omega) (by omega) hfin ι hmod hSD
    · exact hdRo7A3AJAux_le3_nonabelian hp3 hfr hpm (by omega) (by omega) hfin ι hmod hLE3
    · exact (hdRo7A3AJAux_not_nonLevi hRig hrowL hNL).elim
  · obtain ⟨m, V, hVadd, hVmod, ι, θ, hy, hp3, hm9, h3m, hfr, hmod⟩ := hmK hrowK
    let : AddCommGroup V := hVadd
    let : Module (ZMod p) V := hVmod
    have hpm : p ∣ m := by rw [hp3]; exact h3m
    have hm2 : 2 ≤ m := by omega
    have hfin : Module.finrank (ZMod p) V = m - 1 := a3_finrank hfr hpm hm2
    have hXD : GGResXDatum p Bs K := by
      rcases (hX G p B Bs x L D J y K hH).2 with h | h7
      · exact h
      · exfalso
        obtain ⟨-, -, -, -, -, -, hp7, -⟩ := h7
        omega
    rcases (hJ G p B Bs x L D J y K hH).2 hXD with hSD | hLE3 | hNL
    · exact hdRo7A3AJAux_sideDatum_nonabelian hp3 hfr hpm (by omega) (by omega) hfin ι hmod hSD
    · exact hdRo7A3AJAux_le3_nonabelian hp3 hfr hpm (by omega) (by omega) hfin ι hmod hLE3
    · exact (hdRo7A3AJAux_not_nonLevi hRig hrowK hNL).elim


end CFSG.StandardType.HdRo7A3
