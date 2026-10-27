module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
import CFSG.LocalAnalysis.StandardType.GGNbrLangRegStepZero
import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem kgLangTorAGenAux_inducedAut_mk {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (α : MulAut K) (k : K) :
    kgInducedAut θ α (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (α k)) := by
  change (MulAut.congr θ) ((centerQuotAut K) α) (θ (QuotientGroup.mk k)) =
    θ (QuotientGroup.mk (α k))
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, centerQuotAut_mk]

theorem kgLangTorA_inducedAut_trans {K R R' : Type*} [Group K] [Group R] [Group R']
    (θ : K ⧸ Subgroup.center K ≃* R) (e : R ≃* R') (α : MulAut K) :
    kgInducedAut (θ.trans e) α = MulAut.congr e (kgInducedAut θ α) := by
  ext r
  obtain ⟨k, hk⟩ : ∃ k, (θ.trans e) (QuotientGroup.mk k) = r := by
    obtain ⟨x, hx⟩ := (θ.trans e).surjective r
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective x
    exact ⟨k, by rw [hk, hx]⟩
  rw [← hk, kgLangTorAGenAux_inducedAut_mk (θ.trans e) α k]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    kgLangTorAGenAux_inducedAut_mk θ α k]

theorem kgLangTorA_nonabelian {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤) {I : Set (MulAut R)}
    (hI1 : (1 : MulAut R) ∈ I) {α₀ : MulAut K} (hα₀ : kgInducedAut θ α₀ ∉ I) :
    ∃ a b : R, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hZ : commutator K ≤ Subgroup.center K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    apply θ.injective
    rw [map_one, ← QuotientGroup.mk'_apply]
    rw [map_commutatorElement, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (h _ _)
  have hcenter : Subgroup.center K = ⊤ := by
    rw [eq_top_iff, ← hK]
    exact hZ
  have hq1 : ∀ x : K ⧸ Subgroup.center K, x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [QuotientGroup.eq_one_iff, hcenter]
      exact Subgroup.mem_top a
  have hkg1 : kgInducedAut θ α₀ = 1 := by
    ext r
    obtain ⟨z, rfl⟩ := θ.surjective r
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    show kgInducedAut θ α₀ (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk k)
    rw [kgLangTorAGenAux_inducedAut_mk θ α₀ k, hq1 (QuotientGroup.mk (α₀ k)),
      hq1 (QuotientGroup.mk k)]
  exact hα₀ (by rw [hkg1]; exact hI1)

theorem kgLangTorA_coset_decomp {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A B₀ : Subgroup G} (hA : IsElemAbelian p A) (hB₀A : B₀ ≤ A)
    (hcard : Nat.card B₀ * p = Nat.card A) {a : G} (ha : a ∈ A) (haB : a ∉ B₀) :
    ∀ α ∈ A, ∃ β ∈ B₀, ∃ j : ℕ, α = β * a ^ j := by
  intro α hα
  let B : Subgroup ↥A := B₀.subgroupOf A
  haveI : IsMulCommutative ↥A := hA.1
  haveI : B.Normal := Subgroup.normal_of_comm B
  haveI : Nonempty ↥B₀ := ⟨1⟩
  have hcardB : Nat.card ↥B = Nat.card B₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀A).toEquiv
  have hqcard : Nat.card (↥A ⧸ B) = p := by
    have h1 : Nat.card A = Nat.card (↥A ⧸ B) * Nat.card B₀ := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup B, hcardB]
    have h2 : Nat.card B₀ * p = Nat.card B₀ * Nat.card (↥A ⧸ B) := by
      rw [hcard, h1, Nat.mul_comm]
    exact (Nat.mul_left_cancel (Nat.card_pos (α := ↥B₀)) h2).symm
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (↥A ⧸ B) := isCyclic_of_prime_card hqcard
  have haBne : (QuotientGroup.mk ⟨a, ha⟩ : ↥A ⧸ B) ≠ 1 := by
    intro h
    exact haB (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have htop : Subgroup.zpowers (QuotientGroup.mk ⟨a, ha⟩ : ↥A ⧸ B) = ⊤ :=
    zpowers_eq_top_of_prime_card hqcard haBne
  have hmemα : (QuotientGroup.mk ⟨α, hα⟩ : ↥A ⧸ B) ∈
      Subgroup.zpowers (QuotientGroup.mk ⟨a, ha⟩ : ↥A ⧸ B) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨j, hj⟩ := mem_powers_iff_mem_zpowers.mpr hmemα
  have hj' : ((QuotientGroup.mk ⟨a, ha⟩ : ↥A ⧸ B)) ^ j = QuotientGroup.mk ⟨α, hα⟩ := hj
  refine ⟨α * (a ^ j)⁻¹, ?_, j, by group⟩
  have h1 : (QuotientGroup.mk (⟨α, hα⟩ * (⟨a, ha⟩ ^ j)⁻¹) : ↥A ⧸ B) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hj', mul_inv_cancel]
  have h2 : ⟨α, hα⟩ * (⟨a, ha⟩ ^ j)⁻¹ ∈ B := (QuotientGroup.eq_one_iff _).mp h1
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simpa using h3

private theorem kgLangTorAGenAux_inducedAut_injective {K R : Type*} [Group K] [Group R]
    (hK : commutator K = ⊤) (θ : K ⧸ Subgroup.center K ≃* R) :
    Function.Injective (kgInducedAut θ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hz : ∀ l : K, a l * l⁻¹ ∈ Subgroup.center K := by
    intro l
    have h1 := congrArg (fun φ => φ (θ (l : K ⧸ Subgroup.center K))) ha
    simp only [kgLangTorAGenAux_inducedAut_mk, MulAut.one_apply] at h1
    have h2 : l⁻¹ * a l ∈ Subgroup.center K := by
      have := inv_mem (QuotientGroup.eq.mp (θ.injective h1))
      simpa [mul_inv_rev] using this
    have h3 : a l * l⁻¹ = l⁻¹ * a l := by
      have := (Subgroup.mem_center_iff.mp h2) l
      calc a l * l⁻¹ = (l * (l⁻¹ * a l)) * l⁻¹ := by group
        _ = ((l⁻¹ * a l) * l) * l⁻¹ := by rw [this]
        _ = l⁻¹ * a l := by group
    rw [h3]
    exact h2
  let f : K →* K :=
    { toFun := fun l => a l * l⁻¹
      map_one' := by simp
      map_mul' := fun p q => by
        have h := (Subgroup.mem_center_iff.mp (hz q)) p⁻¹
        simp only [map_mul, mul_inv_rev]
        calc a p * a q * (q⁻¹ * p⁻¹) = a p * ((a q * q⁻¹) * p⁻¹) := by group
          _ = a p * (p⁻¹ * (a q * q⁻¹)) := by rw [h]
          _ = a p * p⁻¹ * (a q * q⁻¹) := by group }
  have hker : commutator K ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro p _ q _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hz q)) (f p)
  ext l
  have h1 : f l = 1 := hker (by rw [hK]; exact Subgroup.mem_top _)
  have h2 : a l = l := mul_inv_eq_one.mp h1
  simpa using h2

theorem kgLangTorA_setup {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {I Fd : Set (MulAut R)}
    (hsimple : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (hIF : GGRawInnField p R I Fd) (hPC : GGRawPCyclic p R I Fd) (hFC : GGRawFieldConj p R I Fd)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {A : Subgroup (MulAut K)} (hA : IsElemAbelian p A)
    (hAIF : ∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure Fd, kgInducedAut θ α = u * f)
    {α₀ : MulAut K} (hα₀ : α₀ ∈ A) (hα₀I : kgInducedAut θ α₀ ∉ I) :
    ∃ (B₀ : Subgroup (MulAut K)) (X : Subgroup (MulAut R)) (u₀ f₀ : MulAut R),
      (∀ α ∈ A, kgInducedAut θ α ∈ I → α ∈ B₀) ∧
      (∀ α ∈ A, ∃ β ∈ B₀, ∃ j : ℕ, α = β * α₀ ^ j) ∧
      Nat.card X = Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} ∧
      u₀ ∈ I ∧ f₀ ∈ Fd ∧ orderOf f₀ = p ∧ kgInducedAut θ α₀ = u₀ * f₀ * u₀⁻¹ ∧
      IsElemAbelian p X ∧ (∀ x ∈ X, x ∈ I) ∧ (∀ x ∈ X, f₀ * x = x * f₀) ∧
      ∀ β ∈ B₀, u₀⁻¹ * kgInducedAut θ β * u₀ ∈ X := by
  classical
  haveI hfinK : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  let ρ : ↥A →* MulAut R := (kgInducedAut θ).comp A.subtype
  have hb₀I : ρ ⟨α₀, hα₀⟩ ∉ I := by
    show kgInducedAut θ α₀ ∉ I
    exact hα₀I
  obtain ⟨B₀, hB₀A, hcardB₀, hα₀B₀, hmem⟩ :=
    exists_index_prime_of_raw_pcyclic hp hA hsimple hna hPC ρ hα₀ hb₀I
  obtain ⟨hmul, hinv, -, -⟩ := hIF hsimple hna
  obtain ⟨u, hu, f, hf, heq⟩ := hAIF α₀ hα₀
  have hpow : (kgInducedAut θ α₀) ^ p = 1 := by
    rw [← map_pow, hA.2 α₀ hα₀, map_one]
  obtain ⟨f₀, hf₀F, u₀, hu₀, hf₀ord, heq₀⟩ :=
    hFC hsimple hna u hu f hf (by rwa [← heq]) (by rw [← heq]; exact hpow)
  have heqα : kgInducedAut θ α₀ = u₀ * f₀ * u₀⁻¹ := by rw [heq, heq₀]
  let φ : MulAut K →* MulAut R := (MulAut.conj u₀⁻¹).toMonoidHom.comp (kgInducedAut θ)
  have hφβ : ∀ β : MulAut K, φ β = u₀⁻¹ * kgInducedAut θ β * u₀ := by
    intro β
    change (MulAut.conj u₀⁻¹) (kgInducedAut θ β) = u₀⁻¹ * kgInducedAut θ β * u₀
    rw [MulAut.conj_apply, inv_inv]
  have hφinj : Function.Injective φ := by
    have hkg : Function.Injective (kgInducedAut θ) := kgLangTorAGenAux_inducedAut_injective hK θ
    have hcj : Function.Injective (MulAut.conj u₀⁻¹ : MulAut R → MulAut R) :=
      (MulAut.conj u₀⁻¹ : MulAut (MulAut R)).injective
    exact hcj.comp hkg
  refine ⟨B₀, B₀.map φ, u₀, f₀, ?_, ?_, ?_, hu₀, hf₀F, hf₀ord, heqα, ?_, ?_, ?_, ?_⟩
  · intro α hα hαI
    exact (hmem α hα).mpr (by
      have h : ρ ⟨α, hα⟩ = kgInducedAut θ α := rfl
      rwa [h])
  · exact kgLangTorA_coset_decomp hp hA hB₀A hcardB₀ hα₀ hα₀B₀
  · have hXcard : Nat.card ↥(B₀.map φ) = Nat.card ↥B₀ :=
      Subgroup.card_map_of_injective hφinj
    have hequiv : ↥B₀ ≃ {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ I} :=
      Equiv.subtypeEquivRight (fun x => by
        constructor
        · intro hx
          refine ⟨hB₀A hx, ?_⟩
          have h := (hmem x (hB₀A hx)).mp hx
          rwa [show ρ ⟨x, hB₀A hx⟩ = kgInducedAut θ x from rfl] at h
        · intro hx
          exact (hmem x hx.1).mpr (by
            have h : ρ ⟨x, hx.1⟩ = kgInducedAut θ x := rfl
            rw [h]
            exact hx.2))
    rw [hXcard, Nat.card_congr hequiv]
  · constructor
    · refine IsMulCommutative.of_comm (fun x y => Subtype.ext ?_)
      obtain ⟨β, hβ, hxβ⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨γ, hγ, hyγ⟩ := Subgroup.mem_map.mp y.2
      show (x : MulAut R) * y = y * x
      rw [← hxβ, ← hyγ, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val ((isMulCommutative_iff.mp hA.1) ⟨β, hB₀A hβ⟩ ⟨γ, hB₀A hγ⟩)
    · intro x hx
      obtain ⟨β, hβ, hxβ⟩ := Subgroup.mem_map.mp hx
      show x ^ p = 1
      rw [← hxβ, ← map_pow, hA.2 β (hB₀A hβ), map_one]
  · intro x hx
    obtain ⟨β, hβ, hxβ⟩ := Subgroup.mem_map.mp hx
    rw [← hxβ, hφβ β]
    exact hmul _ (hmul _ (hinv u₀ hu₀) _ ((hmem β (hB₀A hβ)).mp hβ)) _ hu₀
  · intro x hx
    obtain ⟨β, hβ, hxβ⟩ := Subgroup.mem_map.mp hx
    have hcommβ : kgInducedAut θ β * kgInducedAut θ α₀ =
        kgInducedAut θ α₀ * kgInducedAut θ β := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val ((isMulCommutative_iff.mp hA.1) ⟨β, hB₀A hβ⟩ ⟨α₀, hα₀⟩)
    have hf₀' : f₀ = u₀⁻¹ * kgInducedAut θ α₀ * u₀ := by
      rw [heqα]; group
    rw [← hxβ, hφβ β, hf₀']
    calc (u₀⁻¹ * kgInducedAut θ α₀ * u₀) * (u₀⁻¹ * kgInducedAut θ β * u₀)
        = u₀⁻¹ * (kgInducedAut θ α₀ * kgInducedAut θ β) * u₀ := by group
      _ = u₀⁻¹ * (kgInducedAut θ β * kgInducedAut θ α₀) * u₀ := by rw [← hcommβ]
      _ = (u₀⁻¹ * kgInducedAut θ β * u₀) * (u₀⁻¹ * kgInducedAut θ α₀ * u₀) := by group
  · intro β hβ
    exact Subgroup.mem_map.mpr ⟨β, hβ, hφβ β⟩

theorem kgLangTorA_act {H K R : Type*} [Group H] [Group K] [Group R]
    (hH : commutator H = ⊤) (θ : K ⧸ Subgroup.center K ≃* R) (κ : H →* K)
    (α : MulAut K) (ψ : H →* H)
    (hψ : ∀ h, kgInducedAut θ α (θ (QuotientGroup.mk (κ h))) =
      θ (QuotientGroup.mk (κ (ψ h)))) :
    ∀ h, α (κ h) = κ (ψ h) := by
  let f₁ : H →* K := α.toMonoidHom.comp κ
  let f₂ : H →* K := κ.comp ψ
  have h : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.center K := by
    intro g
    rw [← QuotientGroup.eq]
    apply θ.injective
    show θ (QuotientGroup.mk (f₁ g)) = θ (QuotientGroup.mk (f₂ g))
    rw [show f₁ g = α (κ g) from rfl, ← kgLangTorAGenAux_inducedAut_mk θ α (κ g), hψ g]
    rfl
  have hfeq : f₁ = f₂ := NbrLangTypeA.eq_of_mul_mem_center hH h
  intro hh
  have := congrArg (fun f : H →* K => f hh) hfeq
  simpa [f₁, f₂] using this

theorem kgLangTorA_concl_of_lift {H K R : Type*} [Group H] [Group K] [Group R] {p : ℕ}
    (hH : commutator H = ⊤) (θ : K ⧸ Subgroup.center K ≃* R)
    (A B₀ : Subgroup (MulAut K)) {α₀ : MulAut K}
    (hdec : ∀ α ∈ A, ∃ β ∈ B₀, ∃ j : ℕ, α = β * α₀ ^ j)
    (κ : H →* K) (ψ₀ : H →* H)
    (hψ₀ : ∀ h, kgInducedAut θ α₀ (θ (QuotientGroup.mk (κ h))) =
      θ (QuotientGroup.mk (κ (ψ₀ h))))
    {e s : H} (he : κ e ≠ 1) (hep : e ^ p = 1) (he₀ : ψ₀ e = e) (hs₀ : ψ₀ s = s * e)
    (hB : ∀ β ∈ B₀, ∃ ψ : H →* H, ψ e = e ∧ ψ s = s ∧
      ∀ h, kgInducedAut θ β (θ (QuotientGroup.mk (κ h))) = θ (QuotientGroup.mk (κ (ψ h)))) :
    ∃ k e : K, e ≠ 1 ∧ e ^ p = 1 ∧ (∀ α ∈ A, α e = e) ∧ (∀ β ∈ B₀, β k = k) ∧
      k * (α₀ k)⁻¹ = e := by
  let eK : K := κ e
  let k : K := (κ s)⁻¹
  have hα₀act : ∀ h, α₀ (κ h) = κ (ψ₀ h) := kgLangTorA_act hH θ κ α₀ ψ₀ hψ₀
  have heKne : eK ≠ 1 := he
  have heKp : eK ^ p = 1 := by
    show (κ e) ^ p = 1
    rw [← map_pow, hep, map_one]
  have hα₀e : α₀ eK = eK := by
    show α₀ (κ e) = κ e
    rw [hα₀act e, he₀]
  have hβe : ∀ β ∈ B₀, β eK = eK := by
    intro β hβ
    obtain ⟨ψ, hψe, -, hβact⟩ := hB β hβ
    have hact : ∀ h, β (κ h) = κ (ψ h) := kgLangTorA_act hH θ κ β ψ hβact
    show β (κ e) = κ e
    rw [hact e, hψe]
  have hβk : ∀ β ∈ B₀, β k = k := by
    intro β hβ
    obtain ⟨ψ, -, hψs, hβact⟩ := hB β hβ
    have hact : ∀ h, β (κ h) = κ (ψ h) := kgLangTorA_act hH θ κ β ψ hβact
    show β ((κ s)⁻¹) = (κ s)⁻¹
    rw [map_inv, hact s, hψs]
  have hpow : ∀ j : ℕ, (α₀ ^ j) eK = eK := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, MulAut.mul_apply, hα₀e, ih]
  have hAe : ∀ α ∈ A, α eK = eK := by
    intro α hα
    obtain ⟨β, hβ, j, rfl⟩ := hdec α hα
    rw [MulAut.mul_apply, hpow j]
    exact hβe β hβ
  have hke : k * (α₀ k)⁻¹ = eK := by
    show (κ s)⁻¹ * (α₀ ((κ s)⁻¹))⁻¹ = κ e
    rw [map_inv, hα₀act s, hs₀, map_mul]
    group
  exact ⟨k, eK, heKne, heKp, hAe, hβk, hke⟩

end CFSG.StandardType
