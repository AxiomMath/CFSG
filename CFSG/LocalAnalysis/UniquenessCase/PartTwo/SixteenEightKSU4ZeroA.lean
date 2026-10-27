module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Cent
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private noncomputable def s16kQuotEquiv (Q : Type) [Group Q] :
    (⊤ : Subgroup Q) ⧸ (⊥ : Subgroup Q).subgroupOf ⊤ ≃* Q :=
  QuotientGroup.liftEquiv ((⊥ : Subgroup Q).subgroupOf ⊤)
    (φ := (Subgroup.topEquiv (G := Q)).toMonoidHom)
    (Subgroup.topEquiv (G := Q)).surjective (by
      rw [Subgroup.bot_subgroupOf]
      exact (Subgroup.ker_subtype (⊤ : Subgroup Q)).symm)

private theorem s16kQuotEquiv_mk (Q : Type) [Group Q] (x : ↥(⊤ : Subgroup Q)) :
    s16kQuotEquiv Q (QuotientGroup.mk x) = (x : Q) := by
  unfold s16kQuotEquiv
  exact QuotientGroup.liftEquiv_coe _ _ _ x

theorem s16k_exists_embedding_equiv {W : Type} [CommGroup W] {A H : Subgroup (MulAut W)}
    (hHA : H ≤ A) (hHn : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H) {Γ : Subgroup (GL ι K)}
    (hR : (FFModel.nat Γ).Realizes H ⊤ (fixV H)) (hcomm : commSub ⊤ H = ⊤) :
    ∃ (π : ↥Γ →* ↥H) (β : W →* Multiplicative (ι → K))
      (ρ : ↥A →* MulAut (Multiplicative (ι → K))),
      Function.Surjective β ∧ (∀ w : W, β w = 1 ↔ w ∈ fixV H) ∧
      Function.Injective ρ ∧ (∀ a : ↥A, ρ a ∈ s16gNorm Γ) ∧
      (∀ (a : ↥A) (w : W), β ((a : MulAut W) w) = ρ a (β w)) ∧
      ∀ (γ : ↥Γ) (w : W), β (((π γ : ↥H) : MulAut W) w) =
        s16gNatHom ι K (γ : GL ι K) (β w) := by
  classical
  simp only [FFModel.nat] at hR
  obtain ⟨π, hπ⟩ := hR
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  let e := s16kQuotEquiv (Multiplicative (ι → K))
  let β' : W →* Multiplicative (ι → K) :=
    e.toMonoidHom.comp (β.comp (Subgroup.topEquiv (G := W)).symm.toMonoidHom)
  have hβ's : Function.Surjective β' := by
    intro y
    obtain ⟨u, hu⟩ :=
      hβs (QuotientGroup.mk (⟨y, trivial⟩ : ↥(⊤ : Subgroup (Multiplicative (ι → K)))))
    refine ⟨(u : W), ?_⟩
    have h1 : β' (u : W) = e (β u) := by
      show e (β (Subgroup.topEquiv.symm (u : W))) = e (β u)
      rw [show Subgroup.topEquiv.symm (u : W) = u from Subtype.ext rfl]
    rw [h1, hu, s16kQuotEquiv_mk]
  have hker_beta' : ∀ w : W, β' w = 1 ↔ w ∈ fixV H := by
    intro w
    have h1 : β' w = e (β (Subgroup.topEquiv.symm w)) := rfl
    rw [h1, MulEquiv.map_eq_one_iff e, hβk]
    rfl
  have hpres : ∀ (a : ↥A) (w : W), w ∈ fixV H ↔ (a : MulAut W) w ∈ fixV H := by
    intro a w
    constructor
    · intro hw
      rw [mem_fixV] at hw ⊢
      intro x hx
      have hmem : (a : MulAut W)⁻¹ * x * (a : MulAut W) ∈ H := by
        simpa using hHn (a : MulAut W)⁻¹ (inv_mem a.2) x hx
      calc x ((a : MulAut W) w) =
            (a : MulAut W) (((a : MulAut W)⁻¹ * x * (a : MulAut W)) w) := by
            simp [MulAut.mul_apply]
        _ = (a : MulAut W) w := by rw [hw _ hmem]
    · intro hw
      rw [mem_fixV] at hw ⊢
      intro x hx
      have hmem : (a : MulAut W) * x * (a : MulAut W)⁻¹ ∈ H :=
        hHn (a : MulAut W) a.2 x hx
      calc x w = (a : MulAut W)⁻¹
              (((a : MulAut W) * x * (a : MulAut W)⁻¹) ((a : MulAut W) w)) := by
            simp [MulAut.mul_apply]
        _ = (a : MulAut W)⁻¹ ((a : MulAut W) w) := by rw [hw _ hmem]
        _ = w := by simp
  have hact_beta' : ∀ (γ : ↥Γ) (w : W),
      β' (((π γ : ↥H) : MulAut W) w) = natAct Γ γ (β' w) := by
    intro γ w
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β (⟨w, trivial⟩ : ↥(⊤ : Subgroup W)))
    have h1 : β' w = (m : Multiplicative (ι → K)) := by
      have h2 : β' w = e (β (⟨w, trivial⟩ : ↥(⊤ : Subgroup W))) := rfl
      rw [h2, ← hm, s16kQuotEquiv_mk]
    have h3 : β' (((π γ : ↥H) : MulAut W) w) = natAct Γ γ (m : Multiplicative (ι → K)) := by
      have h4 : β' (((π γ : ↥H) : MulAut W) w) =
          e (β (⟨((π γ : ↥H) : MulAut W) w, trivial⟩ : ↥(⊤ : Subgroup W))) := rfl
      rw [h4, hβe γ (⟨w, trivial⟩ : ↥(⊤ : Subgroup W)) m trivial trivial hm.symm,
        s16kQuotEquiv_mk]
    rw [h3, h1]
  have hact_triv : ∀ (a : ↥A) (w : W), β' w = 1 ↔ β' ((a : MulAut W) w) = 1 := by
    intro a w
    rw [hker_beta' w, hker_beta' ((a : MulAut W) w)]
    exact hpres a w
  have hex : ∀ a : ↥A, ∃ ψ : MulAut (Multiplicative (ι → K)),
      ∀ w : W, ψ (β' w) = β' ((a : MulAut W) w) :=
    fun a => s16g_exists_induced_aut β' hβ's (hact_triv a)
  choose ρ₀ hρ₀ using hex
  have hρ₀_mul : ∀ a b : ↥A, ρ₀ (a * b) = ρ₀ a * ρ₀ b := by
    intro a b
    ext y
    obtain ⟨w, rfl⟩ := hβ's y
    rw [hρ₀ (a * b) w, MulAut.mul_apply, hρ₀ b w, hρ₀ a ((b : MulAut W) w)]
    simp
  let ρ : ↥A →* MulAut (Multiplicative (ι → K)) := MonoidHom.mk' ρ₀ hρ₀_mul
  have hρ : ∀ (a : ↥A) (w : W), ρ a (β' w) = β' ((a : MulAut W) w) := fun a w => hρ₀ a w
  have hπγ : ∀ γ : ↥Γ, ρ ⟨π γ, hHA (π γ).2⟩ = s16gNatHom ι K (γ : GL ι K) := by
    intro γ
    ext y
    obtain ⟨w, rfl⟩ := hβ's y
    rw [hρ, hact_beta' γ w, s16gNatHom_eq_natAct]
  have hconj : ∀ b : ↥A, ∀ x ∈ Γ.map (s16gNatHom ι K),
      ρ b * x * (ρ b)⁻¹ ∈ Γ.map (s16gNatHom ι K) := by
    intro b x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨γ', hγ'⟩ := hπs ⟨(b : MulAut W) * ((π ⟨y, hy⟩ : ↥H) : MulAut W) * (b : MulAut W)⁻¹,
      hHn (b : MulAut W) b.2 (π ⟨y, hy⟩) (π ⟨y, hy⟩).2⟩
    refine Subgroup.mem_map.mpr ⟨γ', γ'.2, ?_⟩
    have hsub : (⟨π γ', hHA (π γ').2⟩ : ↥A) =
        b * ⟨π ⟨y, hy⟩, hHA (π ⟨y, hy⟩).2⟩ * b⁻¹ := by
      apply Subtype.ext
      rw [hγ']
      rfl
    rw [← hπγ γ', ← hπγ ⟨y, hy⟩, hsub]
    simp only [map_mul, map_inv]
  have hnorm : ∀ a : ↥A, ρ a ∈ s16gNorm Γ := by
    intro a
    rw [s16gNorm, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj a x
    · intro hx
      have h1 : ρ (a⁻¹) * (ρ a * x * (ρ a)⁻¹) * (ρ (a⁻¹))⁻¹ ∈ Γ.map (s16gNatHom ι K) :=
        hconj (a⁻¹) _ hx
      have heq : ρ (a⁻¹) * (ρ a * x * (ρ a)⁻¹) * (ρ (a⁻¹))⁻¹ = x := by
        rw [map_inv]
        group
      rwa [heq] at h1
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    apply s16g_eq_one_of_commSub hcomm
    · intro h hh
      have hcH : (a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹ ∈ H :=
        H.mul_mem (hHn (a : MulAut W) a.2 h hh) (H.inv_mem hh)
      have hcA : (a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹ ∈ A := hHA hcH
      have hc1 : ρ ⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hcA⟩ = 1 := by
        have heq : (⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hcA⟩ : ↥A) =
            a * ⟨h, hHA hh⟩ * a⁻¹ * ⟨h, hHA hh⟩⁻¹ := Subtype.ext rfl
        rw [heq]
        simp [map_mul, map_inv, ha]
      obtain ⟨γ', hγ'⟩ := hπs ⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hcH⟩
      have hγ1 : s16gNatHom ι K (γ' : GL ι K) = 1 := by
        rw [← hπγ γ']
        have heq2 : (⟨π γ', hHA (π γ').2⟩ : ↥A) =
            ⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hcA⟩ := by
          apply Subtype.ext
          rw [hγ']
        rw [heq2, hc1]
      have hγ'1 : γ' = 1 := by
        apply Subtype.ext
        exact s16gNatHom_injective (by rw [hγ1]; simp)
      have hcW : (a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹ = 1 := by
        have h5 : (⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hcH⟩ : ↥H) = 1 := by
          rw [← hγ', hγ'1, map_one]
        exact congrArg Subtype.val h5
      have hcomm' : (a : MulAut W) * h * (a : MulAut W)⁻¹ = h := mul_inv_eq_one.mp hcW
      calc (a : MulAut W) * h =
            (a : MulAut W) * h * (a : MulAut W)⁻¹ * (a : MulAut W) := by group
        _ = h * (a : MulAut W) := by rw [hcomm']
    · intro w
      rw [← hker_beta' ((a : MulAut W) w * w⁻¹), map_mul, map_inv]
      have h1 : β' ((a : MulAut W) w) = β' w := by
        rw [← hρ a w, ha]
        rfl
      rw [h1, mul_inv_cancel]
  exact ⟨π, β', ρ, hβ's, hker_beta', hinj, hnorm,
    fun a w => (hρ a w).symm, hact_beta'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
