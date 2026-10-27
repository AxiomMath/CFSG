module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkWit

public section

namespace CFSG.StandardType

namespace WitOmBlk

open CFSG.Assembly Matrix Module QuadraticMap SUTB NoOffOm OrdPNsGen OrdPNsOm
open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ}

theorem glin_pow_fix {z : GL (Fin d) K} {W : Set (Fin d → K)} (h : ∀ v ∈ W, glin z v = v) :
    ∀ (k : ℕ), ∀ v ∈ W, glin (z ^ k) v = v := by
  intro k
  induction k with
  | zero => intro v _; rw [pow_zero, glin_one]; rfl
  | succ k ih => intro v hv; rw [pow_succ, glin_mul, Module.End.mul_apply, h v hv, ih v hv]

variable [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}

theorem exists_conj_witness_of_model {G : Type} [Group G] [Finite G]
    (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    (hpq' : ¬ p ∣ Nat.card K + 1) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hcard : p ^ 4 ≤ Nat.card Bs) (φ : matrixDerived Q →* G) (hφ : Function.Injective φ)
    (hBφ : Bs ≤ φ.range) (t : StatedLieTag) (f : ℕ) {u : matrixDerived Q} (hu : u * u = 1) :
    ∃ g a : matrixDerived Q, g * u * g⁻¹ * a = a * (g * u * g⁻¹) ∧
      GGSixBstarWit p Bs φ.range t f (φ a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup (GL (Fin d) K) := (Bs.comap φ).map (matrixDerived Q).subtype with hAdef
  have hA : GenMax (polB Q) (matrixDerived Q) p A := genMax_of_orth hnd hT hp hp2 hBs hSC φ hφ hBφ
  have hAcard : Nat.card A = Nat.card Bs := by
    rw [hAdef, Subgroup.card_map_of_injective (matrixDerived Q).subtype_injective,
      ← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hBφ]
  have hmemA : ∀ c : matrixDerived Q, φ c ∈ Bs → (c : GL (Fin d) K) ∈ A :=
    fun c hc => ⟨c, hc, rfl⟩
  have hmemA' : ∀ c : matrixDerived Q, (c : GL (Fin d) K) ∈ A → φ c ∈ Bs := by
    rintro c ⟨c', hc', hcc'⟩
    rw [← Subtype.ext hcc']
    exact hc'
  obtain ⟨S, hS, hterm⟩ := exists_terminal_genPieceSet hA
  have hSc := card_eq_pow_of_terminal hA hS hterm
  have hS4 : 4 ≤ S.card := by
    have h1 : p ^ 4 ≤ p ^ S.card := by rw [← hSc, hAcard]; exact hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  obtain ⟨y₁, hy₁S, y₂, hy₂S, hy12⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hy₁ : y₁ ∈ A := hS.mem y₁ hy₁S
  have hy₂ : y₂ ∈ A := hS.mem y₂ hy₂S
  obtain ⟨m, hm⟩ := exists_lcm_eq (K := K) hp hA.natCast_ne_zero
  have hdimS : ∀ y ∈ S, finrank K (grng y) = 2 * m + 2 := fun y hy => by
    rw [finrank_grng_eq_lcm polB_self hA hS hy, hm]
  have hm1 : 1 ≤ m := one_le_of_not_dvd hp hm hpq hpq'
  have hd : 4 * (2 * m + 2) ≤ finrank K (Fin d → K) := by
    have h1 := finrank_genPieceSpan hA hS
    rw [Finset.sum_congr rfl hdimS, Finset.sum_const, smul_eq_mul] at h1
    have h2 := Submodule.finrank_le (genPieceSpan S)
    have h3 : 4 * (2 * m + 2) ≤ S.card * (2 * m + 2) := Nat.mul_le_mul_right _ hS4
    omega
  have hU₁ : NondegOn (polB Q) (grng y₁) := nondegOn_grng hA hy₁
  have hU₂ : NondegOn (polB Q) (grng y₂) := nondegOn_grng hA hy₂
  have hU12 : ∀ x ∈ grng y₁, ∀ y ∈ grng y₂, polar Q x y = 0 := fun x hx y hy => by
    have := hS.orth y₁ hy₁S y₂ hy₂S hy12 x hx y hy
    rwa [polB_apply] at this
  obtain ⟨c₀, hc₀⟩ := exists_not_mem_range_wp (K := K)
  obtain ⟨τ₀, -, -, -, -, -, -, hS₀⟩ :=
    exists_frame (Q := Q) hc₀ m (grng y₁) hU₁ (hdimS y₁ hy₁S)
  have hτ₀ : (Nat.card K : ℤ) ^ m * tailSum K τ₀ ≡ 1 [ZMOD p] := hS₀ ▸ charSum_grng_modEq hA hy₁
  obtain ⟨e₁, f₁, a₁, b₁, hmem₁, hF₁⟩ := exists_frame_of_modEq hc₀ hp hp2 hτ₀ hU₁
    (hdimS y₁ hy₁S) (charSum_grng_modEq hA hy₁)
  obtain ⟨e₂, f₂, a₂, b₂, hmem₂, hF₂⟩ := exists_frame_of_modEq hc₀ hp hp2 hτ₀ hU₂
    (hdimS y₂ hy₂S) (charSum_grng_modEq hA hy₂)
  have hUy₁ := grng_inv hA hy₁ hy₁
  have hUy₂ := grng_inv hA hy₂ hy₂
  obtain ⟨z₁, hz₁A, hz₁on, hz₁off⟩ :=
    hA.exists_mem_restrict hU₁ (fun a ha => grng_inv hA hy₁ ha) hy₁
  obtain ⟨z₂, hz₂A, hz₂on, hz₂off⟩ :=
    hA.exists_mem_restrict hU₂ (fun a ha => grng_inv hA hy₂ ha) hy₂
  have hcyc₁ : ∀ c ∈ A, ∃ k : ℕ, ∀ x ∈ grng y₁, glin c x = glin (z₁ ^ k) x := by
    intro c hc
    obtain ⟨k, hk⟩ := hS.cyc y₁ hy₁S c hc
    exact ⟨k, fun x hx => by rw [hk x hx, glin_pow_of_eqOn hUy₁ hz₁on k x hx]⟩
  have hcyc₂ : ∀ c ∈ A, ∃ k : ℕ, ∀ x ∈ grng y₂, glin c x = glin (z₂ ^ k) x := by
    intro c hc
    obtain ⟨k, hk⟩ := hS.cyc y₂ hy₂S c hc
    exact ⟨k, fun x hx => by rw [hk x hx, glin_pow_of_eqOn hUy₂ hz₂on k x hx]⟩
  have hne : ∀ y ∈ S, ∃ x ∈ grng y, x ≠ 0 := fun y hy =>
    Submodule.exists_mem_ne_zero_of_ne_bot (grng_ne_bot (hS.ne_one y hy))
  obtain ⟨x₁, hx₁, hx₁0⟩ := hne y₁ hy₁S
  obtain ⟨x₂, hx₂, hx₂0⟩ := hne y₂ hy₂S
  have hz₁1 : z₁ ≠ 1 := by
    intro h1
    have h2 := hz₁on x₁ hx₁
    rw [h1, glin_one, Module.End.one_apply] at h2
    exact hx₁0 (eq_zero_of_mem_grng hA hy₁ hx₁ h2.symm)
  have hz₂1 : z₂ ≠ 1 := by
    intro h1
    have h2 := hz₂on x₂ hx₂
    rw [h1, glin_one, Module.End.one_apply] at h2
    exact hx₂0 (eq_zero_of_mem_grng hA hy₂ hx₂ h2.symm)
  have hU₁₂ : ∀ x ∈ grng y₁, x ∈ (grng y₂).orthogonalBilin (polB Q) := fun x hx =>
    Submodule.mem_orthogonalBilin.mpr fun y hy => by
      change polar Q y x = 0
      rw [polar_comm]
      exact hU12 x hx y hy
  have hU₂₁ : ∀ x ∈ grng y₂, x ∈ (grng y₁).orthogonalBilin (polB Q) := fun x hx =>
    Submodule.mem_orthogonalBilin.mpr fun y hy => hU12 y hy x hx
  set ι : GL (Fin d) K ≃* ((Fin d → K) ≃ₗ[K] (Fin d → K)) := matrixLinearIso with hιdef
  have hιapp : ∀ (X : GL (Fin d) K) (v : Fin d → K), ι X v = glin X v := matrixLinearIso_apply
  have hιΩ : ∀ X ∈ matrixDerived Q, ι X ∈ CFSG.RankThree.Classical2.orthDerived Q :=
    fun X hX => mem_orthDerived_iff.mpr hX
  have hz₁Ω := hA.le hz₁A
  have hz₂Ω := hA.le hz₂A
  have hz₁p : z₁ ^ p = 1 := hA.pow z₁ hz₁A
  have hz₂p : z₂ ^ p = 1 := hA.pow z₂ hz₂A
  have hz₂koff : ∀ (k : ℕ), ∀ v ∈ (grng y₂).orthogonalBilin (polB Q), glin (z₂ ^ k) v = v :=
    glin_pow_fix hz₂off
  have hz₁koff : ∀ (k : ℕ), ∀ v ∈ (grng y₁).orthogonalBilin (polB Q), glin (z₁ ^ k) v = v :=
    glin_pow_fix hz₁off
  have hF3 : ∀ c ∈ CFSG.RankThree.Classical2.orthDerived Q, c ^ p = 1 → c ≠ 1 →
      (∀ y ∈ (grng y₂).orthogonalBilin (polarBilin Q), c y = y) →
      ∃ h ∈ CFSG.RankThree.Classical2.orthDerived Q,
        (∀ y ∈ (grng y₂).orthogonalBilin (polarBilin Q), h y = y) ∧
          ∃ k : ℕ, h * c * h⁻¹ = (ι z₂) ^ k := by
    intro c hc hcp hc1 hcoff
    have hC : ι.symm c ∈ matrixDerived Q := by
      rw [← mem_orthDerived_iff, MulEquiv.apply_symm_apply]
      exact hc
    have hCp : (ι.symm c) ^ p = 1 := by rw [← map_pow, hcp, map_one]
    obtain ⟨h, hh, hhoff, k, hk⟩ := exists_conj_eq_pow_of_piece hnd hT hA hy₂ (hS.cyc y₂ hy₂S)
      hz₂A hz₂on hz₂off hz₂1 hC hCp (fun v hv => by
        rw [← hιapp, MulEquiv.apply_symm_apply]
        exact hcoff v hv)
    refine ⟨ι h, hιΩ h hh, fun v hv => by rw [hιapp]; exact hhoff v hv, k, ?_⟩
    have := congrArg ι hk
    rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_pow] at this
  have hU : NondegOn (polB Q) (grng y₁ ⊔ grng y₂) := nondegOn_sup hU₁ hU₂ fun y hy x hx =>
    ⟨by rw [polB_apply, polar_comm]; exact hU12 x hx y hy, by rw [polB_apply]; exact hU12 x hx y hy⟩
  have hdimU : finrank K ↥(grng y₁ ⊔ grng y₂) + 8 ≤ finrank K (Fin d → K) := by
    have := Submodule.finrank_add_le_finrank_add_finrank (grng y₁) (grng y₂)
    rw [hdimS y₁ hy₁S, hdimS y₂ hy₂S] at this
    omega
  have hperp₁ : ∀ v ∈ (grng y₁ ⊔ grng y₂).orthogonalBilin (polB Q),
      v ∈ (grng y₁).orthogonalBilin (polB Q) := fun v hv =>
    Submodule.mem_orthogonalBilin.mpr fun x hx =>
      Submodule.mem_orthogonalBilin.mp hv x (Submodule.mem_sup_left hx)
  have hperp₂ : ∀ v ∈ (grng y₁ ⊔ grng y₂).orthogonalBilin (polB Q),
      v ∈ (grng y₂).orthogonalBilin (polB Q) := fun v hv =>
    Submodule.mem_orthogonalBilin.mpr fun x hx =>
      Submodule.mem_orthogonalBilin.mp hv x (Submodule.mem_sup_right hx)
  have hwit : ∀ k : ℕ, ∀ hk : z₁ * z₂ ^ k ∈ matrixDerived Q,
      GGSixBstarWit p Bs φ.range t f (φ ⟨z₁ * z₂ ^ k, hk⟩) := by
    intro k hk
    set a : matrixDerived Q := ⟨z₁ * z₂ ^ k, hk⟩ with ha
    have haA : (a : GL (Fin d) K) ∈ A := A.mul_mem hz₁A (A.pow_mem hz₂A k)
    have hap : (ι a) ^ p = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow]
      rw [show a ^ p = 1 from Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.pow _ haA)]
      rw [OneMemClass.coe_one, map_one]
    have haoff : ∀ v ∈ (grng y₁ ⊔ grng y₂).orthogonalBilin (polarBilin Q), ι a v = v := by
      intro v hv
      rw [hιapp, ha, glin_mul, Module.End.mul_apply, hz₂koff k v (hperp₂ v hv),
        hz₁off v (hperp₁ v hv)]
    obtain ⟨L, hLΩ, hLq, hLa, hLn, hLc⟩ := exists_component_block (K := K) hnd hp hp2
      (hιΩ _ hk) hap haoff hdimU
    set ψ : matrixDerived Q →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
      ι.toMonoidHom.comp (matrixDerived Q).subtype with hψ
    have hψinj : Function.Injective ψ := ι.injective.comp Subtype.val_injective
    have hψapp : ∀ X : matrixDerived Q, ψ X = ι X := fun X => rfl
    have hLψ : L ≤ ψ.range := by
      intro l hl
      obtain ⟨X, hX, hXl⟩ :=
        (CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q).symm ▸ hLΩ hl
      exact ⟨⟨X, hX⟩, hXl⟩
    set U : Subgroup (matrixDerived Q) := L.comap ψ with hUdef
    have hUmap : U.map ψ = L := Subgroup.map_comap_eq_self hLψ
    have eU : ↥U ≃* ↥L := (U.equivMapOfInjective ψ hψinj).trans (MulEquiv.subgroupCongr hUmap)
    have hUq : CFSG.IsQuasisimple ↥U := CFSG.LocalCores.isQuasisimple_of_mulEquiv eU.symm hLq
    have hιmul : ∀ X Y : matrixDerived Q, ψ (X * Y) = ψ X * ψ Y := fun X Y => map_mul ψ X Y
    refine bstarWit_of_component t f φ hφ hBφ (U := U) (a := a) (fun h1 => ?_) (hmemA' a haA) hUq
      (fun l hl => ?_) (fun g hg l hl => ?_) (F := fun ij => ⟨z₁ ^ (ij.1 : ℕ) * z₂ ^ (ij.2 : ℕ),
        mul_mem (pow_mem hz₁Ω _) (pow_mem hz₂Ω _)⟩) (fun c hcB hcU => ?_)
    ·
      have h2 : glin (z₁ * z₂ ^ k) x₁ = x₁ := by
        have h3 := congrArg Subtype.val h1
        simp only [ha, OneMemClass.coe_one] at h3
        rw [h3, glin_one]
        rfl
      rw [glin_mul, Module.End.mul_apply, hz₂koff k x₁ (hU₁₂ x₁ hx₁), hz₁on x₁ hx₁] at h2
      exact hx₁0 (eq_zero_of_mem_grng hA hy₁ hx₁ h2)
    ·
      apply hψinj
      rw [hιmul, hιmul, hψapp a]
      exact hLa _ hl
    ·
      have hgx : ψ g * ι a = ι a * ψ g := by rw [← hψapp a, ← hιmul, ← hιmul, hg]
      change ψ (g * l * g⁻¹) ∈ L
      rw [map_mul, map_mul, map_inv]
      exact hLn _ (hιΩ _ g.2) hgx _ hl
    ·
      have hcA := hmemA c hcB
      have hcO : ι c ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        Subgroup.commutator_le_self _ (hιΩ _ c.2)
      have hcx : ι c * ι a = ι a * ι c := by
        rw [← map_mul, ← map_mul, hA.comm _ hcA _ haA]
      have hcL : ∀ l ∈ L, ι c * l = l * ι c := by
        intro l hl
        obtain ⟨l', rfl⟩ := hLψ hl
        have hl' : l' ∈ U := hl
        rw [← hψapp c, ← hιmul, ← hιmul, hcU l' hl']
      have hcoff := hLc _ hcO hcx hcL
      obtain ⟨i, hi⟩ := hcyc₁ _ hcA
      obtain ⟨j, hj⟩ := hcyc₂ _ hcA
      refine ⟨(⟨i % p, Nat.mod_lt _ hp.pos⟩, ⟨j % p, Nat.mod_lt _ hp.pos⟩), Subtype.ext ?_⟩
      change z₁ ^ (i % p) * z₂ ^ (j % p) = (c : GL (Fin d) K)
      rw [← pow_eq_pow_mod i hz₁p, ← pow_eq_pow_mod j hz₂p]
      apply glin_injective
      refine eq_of_eqOn_sup (Q := Q) hU (fun x hx => ?_) (fun x hx => ?_) (fun y hy => ?_)
      · rw [glin_mul, Module.End.mul_apply, hz₂koff j x (hU₁₂ x hx), hi x hx]
      · have hx' : glin (z₂ ^ j) x ∈ grng y₂ := by
          rw [glin_pow_of_eqOn hUy₂ hz₂on j x hx]
          exact pow_mem_of_inv hUy₂ j x hx
        rw [glin_mul, Module.End.mul_apply, hz₁koff i _ (hU₂₁ _ hx'), hj x hx]
      · rw [glin_mul, Module.End.mul_apply, hz₂koff j y (hperp₂ y hy), hz₁koff i y (hperp₁ y hy),
          ← hιapp, hcoff y hy]
  obtain ⟨g, hg, k, hgk⟩ := exists_conj_commute_block (V := Fin d → K) hc₀ hnd hT hm1 hd
    (U₁ := grng y₁) (U₂ := grng y₂) hU₁ hU₂ hU12 hF₁ hF₂ hmem₁ hmem₂ (hdimS y₁ hy₁S)
    (hdimS y₂ hy₂S) (z₁ := ι z₁) (z₂ := ι z₂) (hιΩ _ hz₁Ω) (by rw [← map_pow, hz₁p, map_one])
    (fun h => hz₁1 (ι.injective (h.trans (map_one ι).symm)))
    (fun y hy => by rw [hιapp]; exact hz₁off y hy)
    (by rw [← map_mul, ← map_mul, hA.comm _ hz₁A _ hz₂A]) hF3 (u := ι u) (hιΩ _ u.2)
    (by rw [← map_mul, ← Subgroup.coe_mul, hu, OneMemClass.coe_one, map_one])
  have hG : ι.symm g ∈ matrixDerived Q := by
    rw [← mem_orthDerived_iff, MulEquiv.apply_symm_apply]
    exact hg
  have hk : z₁ * z₂ ^ k ∈ matrixDerived Q := mul_mem hz₁Ω (pow_mem hz₂Ω _)
  refine ⟨⟨ι.symm g, hG⟩, ⟨z₁ * z₂ ^ k, hk⟩, Subtype.ext (ι.injective ?_), hwit k hk⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, map_pow,
    MulEquiv.apply_symm_apply]
  exact hgk

end WitOmBlk

end CFSG.StandardType
