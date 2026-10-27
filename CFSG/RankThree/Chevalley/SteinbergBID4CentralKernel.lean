module

public import CFSG.RankThree.Chevalley.SteinbergBID4Triality

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem E6_native_D4_full_central_kernel_all_characteristics (K : Type) [Field K] :
    Function.Injective (d4Emb K) ∧
    (∀ k, d4Emb K (hVec Tag.D4 K k) = hVec Tag.E6 K (d4Idx k)) ∧
    (∀ β, d4Emb K (rootVec Tag.D4 K β) = rootVec Tag.E6 K (d4Lat β)) ∧
    (∀ (g : subsystemGroup Tag.E6 K d4Support) v,
      ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (d4Emb K v) =
        d4Emb K ((d4Res K g : Module.End K (RootModule Tag.D4 K)) v)) ∧
    (d4Res K).range = adjointGroup Tag.D4 K ∧
    (∀ k c, d4Res K ⟨xUnit Tag.E6 K (d4Idx k) c, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
      xUnit Tag.D4 K k c) ∧
    (∀ k c, d4Res K ⟨yUnit Tag.E6 K (d4Idx k) c, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
      yUnit Tag.D4 K k c) ∧
    (∀ k t, d4Res K ⟨weylElt Tag.E6 K (d4Idx k) t, weylElt_mem_subsystemGroup (d4Idx_mem k) t⟩ =
      weylElt Tag.D4 K k t) ∧
    (∀ k t, d4Res K ⟨torusElt Tag.E6 K (d4Idx k) t, torusElt_mem_d4Q k t⟩ =
      torusElt Tag.D4 K k t) ∧
    (∀ g : subsystemGroup Tag.E6 K d4Support, d4Res K g = 1 ↔
      ∃ a b d : Kˣ, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ d ^ 2 = 1 ∧ a * b * d = 1 ∧
        (g : ModGL Tag.E6 K) =
          torusElt Tag.E6 K 1 a * torusElt Tag.E6 K 2 b * torusElt Tag.E6 K 4 d) ∧
    (∀ a b d a' b' d' : Kˣ,
      torusElt Tag.E6 K 1 a * torusElt Tag.E6 K 2 b * torusElt Tag.E6 K 4 d =
        torusElt Tag.E6 K 1 a' * torusElt Tag.E6 K 2 b' * torusElt Tag.E6 K 4 d' →
          a = a' ∧ b = b' ∧ d = d') ∧
    (ringChar K = 2 → (d4Res K).ker = ⊥) ∧
    (ringChar K ≠ 2 → Nonempty (Multiplicative (ZMod 2 × ZMod 2) ≃* (d4Res K).ker)) ∧
    (d4Res K).ker ≤ Subgroup.center (subsystemGroup Tag.E6 K d4Support) ∧
    subsystemGroup Tag.E6 K d4Support ⊓ torusGroup Tag.E6 K = (d4TorusHom K).range ∧
    (∀ t, d4TorusHom K t = torusElt Tag.E6 K 1 (t 0) * torusElt Tag.E6 K 2 (t 1) *
      torusElt Tag.E6 K 3 (t 2) * torusElt Tag.E6 K 4 (t 3)) ∧
    Function.Injective (d4TorusHom K) ∧
    (∀ (L : Type) [Field L] (σ : K →+* L) (g : subsystemGroup Tag.E6 K d4Support),
      d4Res L (d4QBaseChange K σ g) = baseChangeGL σ (d4Res K g)) ∧
    (∀ γ, γ ∈ parabolicRoots Tag.E6 d4Support ↔ ∃ β, IsRoot Tag.D4 β ∧ d4Lat β = γ) ∧
    (∀ β (hβ : IsRoot Tag.D4 β), ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (L : Type) [Field L] (c : L),
      d4Res L ⟨pinnedX Tag.E6 L (d4Lat β) c, pinnedX_mem_d4Q hβ c⟩ =
        pinnedX Tag.D4 L β ((ε : L) * c)) ∧
    (∀ β, IsRoot Tag.D4 β →
      ((rootSubgroup Tag.E6 K (d4Lat β)).subgroupOf (subsystemGroup Tag.E6 K d4Support)).map
        (d4Res K) = rootSubgroup Tag.D4 K β) ∧
    d4TrialityRep K ∈ adjointGroup Tag.E6 K ∧
    BaseChange (Int.castRingHom K)
      (wordRep Tag.E6 ℤ d4TrialityWord : Module.End ℤ (RootModule Tag.E6 ℤ))
      (d4TrialityRep K : Module.End K (RootModule Tag.E6 K)) ∧
    (∀ α, IsRoot Tag.E6 α →
      (rootSubgroup Tag.E6 K α).map (MulAut.conj (d4TrialityRep K)).toMonoidHom =
        rootSubgroup Tag.E6 K ((coxeterSystem Tag.E6).wordProd d4TrialityWord • α)) ∧
    (coxeterSystem Tag.E6).wordProd d4TrialityWord ^ 3 = 1 ∧
    (coxeterSystem Tag.E6).wordProd d4TrialityWord ≠ 1 ∧
    (∀ k, (coxeterSystem Tag.E6).wordProd d4TrialityWord •
      (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (d4Idx (d4Rho k)) 1) ∧
    (d4Idx (d4Rho 0) = 2 ∧ d4Idx (d4Rho 1) = 4 ∧ d4Idx (d4Rho 2) = 3 ∧ d4Idx (d4Rho 3) = 1) ∧
    (∀ g : subsystemGroup Tag.E6 K d4Support,
      ((d4Triality K g : subsystemGroup Tag.E6 K d4Support) : ModGL Tag.E6 K) =
        d4TrialityRep K * g * (d4TrialityRep K)⁻¹) ∧
    (∀ k c, d4Triality K ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
      ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem (d4Rho k)) c⟩) ∧
    (∀ k c, d4Triality K ⟨_, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
      ⟨_, yUnit_mem_subsystemGroup (d4Idx_mem (d4Rho k)) c⟩) ∧
    (∀ φ : subsystemGroup Tag.E6 K d4Support ≃* subsystemGroup Tag.E6 K d4Support,
      (∀ k c, φ ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
        ⟨_, xUnit_mem_subsystemGroup (d4Idx_mem (d4Rho k)) c⟩) →
      (∀ k c, φ ⟨_, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
        ⟨_, yUnit_mem_subsystemGroup (d4Idx_mem (d4Rho k)) c⟩) → φ = d4Triality K) ∧
    (∀ g, d4Triality K (d4Triality K (d4Triality K g)) = g) ∧
    d4Triality K ≠ 1 ∧
    (∀ g, d4Res K g = 1 → d4Res K (d4Triality K g) = 1) ∧
    (∀ a b d : Kˣ, ((d4Triality K ⟨_, d4TorusHom_mem_d4Q ![a, b, 1, d]⟩ :
      subsystemGroup Tag.E6 K d4Support) : ModGL Tag.E6 K) =
        torusElt Tag.E6 K 1 d * torusElt Tag.E6 K 2 a * torusElt Tag.E6 K 4 b) ∧
    (ringChar K ≠ 2 → ∀ z z' : subsystemGroup Tag.E6 K d4Support, d4Res K z = 1 →
      d4Res K z' = 1 → z ≠ 1 → z' ≠ 1 →
        (z' = z ∨ z' = d4Triality K z ∨ z' = d4Triality K (d4Triality K z)) ∧
          d4Triality K z ≠ z ∧ d4Triality K (d4Triality K z) ≠ z ∧
            d4Triality K (d4Triality K z) ≠ d4Triality K z) := by
  refine ⟨d4Emb_injective, d4Emb_hVec, d4Emb_rootVec, d4Res_apply, range_d4Res, d4Res_xUnit,
    d4Res_yUnit, d4Res_weylElt, d4Res_torusElt, d4Res_eq_one_iff_mem_d4KernelSet,
    fun _ _ _ _ _ _ h => d4Sign_injective h, fun h2 => ?_,
    fun h2 => ⟨(d4KernelEquiv h2)⟩, fun g hg => mem_center_of_d4Res_eq_one hg, ?_,
    d4TorusHom_apply, d4TorusHom_injective, fun L _ σ g => d4Res_baseChangeGL σ g,
    fun γ => mem_parabolicRoots_d4Support_iff, fun β hβ => exists_sign_d4Res_pinnedX hβ,
    fun β hβ => map_d4Res_rootSubgroup hβ, wordRep_mem_adjointGroup K _,
    baseChange_wordRep _ _, fun α hα => d4TrialityRep_conj_rootSubgroup hα,
    d4TrialityWeyl_pow_three, d4TrialityWeyl_ne_one, fun k => ?_, ⟨rfl, rfl, rfl, rfl⟩,
    coe_d4Triality, d4Triality_xUnit, d4Triality_yUnit, fun φ hx hy => eq_d4Triality hx hy,
    d4Triality_cube, d4Triality_ne_one, fun g hg => d4Res_d4Triality_eq_one hg,
    fun a b d => ?_, fun h2 z z' hz hz' hz1 hz1' => d4Triality_cycles_kernel h2 hz hz' hz1 hz1'⟩
  · exact (MonoidHom.ker_eq_bot_iff _).2 (d4Res_injective_of_ringChar_eq_two h2)
  · rw [subsystemGroup_inf_torusGroup_eq_supportedTorus, range_d4TorusHom]
  · rw [← wordAct_eq_smul]
    exact (d4TrialityWord_check k).1
  · rw [coe_d4Triality_d4TorusHom_sign, d4TorusHom_sign]

end CFSG.RankThree.Chevalley
