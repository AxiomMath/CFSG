module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorGlue
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Setup


private theorem tensorSetup_rho {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) :
    ∃ ρ : Mbar M Q →* Multiplicative (AddAut M₀.E),
      (∀ (t : ↥M) (x : G), x ∈ Q →
        M₀.π ((t : G) * x * (t : G)⁻¹) = (ρ (QuotientGroup.mk t)).toAdd (M₀.π x)) ∧
      ∀ t : ↥M, ∃ σ : K ≃+* K, ∀ (c : K) (e : M₀.E),
        (ρ (QuotientGroup.mk t)).toAdd (c • e) = σ c • (ρ (QuotientGroup.mk t)).toAdd e := by
  obtain ⟨φ, hφπ, hφker, hφadd, hφsemi⟩ := exists_actionHom_M hc.hyp h
  let A : ↥M → AddAut M₀.E := fun m => { toEquiv := φ m, map_add' := hφadd m }
  have hA0 : ∀ m : ↥M, φ m = 1 → A m = 0 := fun m hm =>
    AddEquiv.ext fun v => congrArg (fun f : Equiv.Perm M₀.E => f v) hm
  have hAmul : ∀ m₁ m₂ : ↥M, A (m₁ * m₂) = A m₁ + A m₂ := fun m₁ m₂ =>
    AddEquiv.ext fun v => congrArg (fun f : Equiv.Perm M₀.E => f v) (map_mul φ m₁ m₂)
  let Ψ : ↥M →* Multiplicative (AddAut M₀.E) :=
    { toFun := fun m => Multiplicative.ofAdd (A m)
      map_one' := congrArg Multiplicative.ofAdd (hA0 1 (map_one φ))
      map_mul' := fun m₁ m₂ => congrArg Multiplicative.ofAdd (hAmul m₁ m₂) }
  have hker : Q.subgroupOf M ≤ Ψ.ker := fun q hq =>
    MonoidHom.mem_ker.mpr (congrArg Multiplicative.ofAdd (hA0 q ((hφker q).mpr hq)))
  refine ⟨QuotientGroup.lift (Q.subgroupOf M) Ψ hker, fun t x hx => hφπ t x hx, fun t => ?_⟩
  exact hφsemi t

private theorem tensorSetup_rho_linear {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
    [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
    (hρ : ∀ (t : ↥M) (x : G), x ∈ Q →
      M₀.π ((t : G) * x * (t : G)⁻¹) = (ρ (QuotientGroup.mk t)).toAdd (M₀.π x))
    (h : GlobalModelData M Q Z γ M₀) (t : ↥M) (hz : ∀ z ∈ Z, (t : G) * z * (t : G)⁻¹ = z) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E, (∀ e, (ρ (QuotientGroup.mk t)).toAdd e = T e) ∧
      ∀ e f, M₀.B (T e) (T f) = M₀.B e f := by
  obtain ⟨T, hT1, -, hTB⟩ := h.linear_of_centralizes t.2 hz
  refine ⟨T, fun e => ?_, hTB⟩
  have key := eq_of_pi_conj_eq (M₀ := M₀) (g := (t : G))
    (S₁ := fun e => (ρ (QuotientGroup.mk t)).toAdd e) (S₂ := fun e => T e)
    (fun x hx => hρ t x hx) (fun x hx => hT1 x hx)
  exact congrFun key e

private theorem tensorSetup_mem_bar {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
    [(Q.subgroupOf M).Normal] {S : Subgroup G} {ℓ : Mbar M Q} (hℓ : ℓ ∈ bar M Q S) :
    ∃ t : ↥M, (t : G) ∈ S ∧ (QuotientGroup.mk t : Mbar M Q) = ℓ := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hℓ
  exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩

private theorem tensorSetup_mk_mem_iff {G : Type} [Group G] [Finite G] {M Q S : Subgroup G}
    [(Q.subgroupOf M).Normal] (hQS : Q ≤ S) (y : ↥M) :
    (QuotientGroup.mk y : Mbar M Q) ∈ bar M Q S ↔ (y : G) ∈ S :=
  mk_mem_bar_iff_sec4 hQS y

private theorem tensorSetup_conj_of_H0 {G : Type} [Group G] {M Z : Subgroup G} {t : G}
    (ht : t ∈ H0 M Z) : ∀ z ∈ Z, t * z * t⁻¹ = z := by
  intro z hz
  have hm : t ∈ M ⊓ Subgroup.centralizer (Z : Set G) := ht
  have h1 := Subgroup.mem_centralizer_iff.mp hm.2 z hz
  rw [← h1]
  group

private theorem tensorSetup_sup_le_lift {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    (B ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img B) := by
  refine sup_le (fun u hu => ⟨hc.le hu, M₀.pi_mem_img hu (hc.le hu)⟩) (fun z hz => ?_)
  refine ⟨h.reg.V_le hz, ?_⟩
  rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
  exact AddSubgroup.zero_mem _

theorem tensorSetup_of_34 (h34 : Stroth34Statement) : TensorSetupStatement := by
  intro G _ _ M Q Z B _ hc n hw hn hno hgen
  have h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 h34 hc hw hn hno hgen).2.1
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, -, hB, -, -⟩ := hc.dictB h
  have hK : 1 < Nat.card (GaloisField 2 m) := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  obtain ⟨ρ, hρ, hsemi⟩ := tensorSetup_rho hc h
  have hle : (B ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img B) := tensorSetup_sup_le_lift hc h
  have hBZQ : (B ⊔ Z : Subgroup G) ≤ Q := sup_le hc.le hc.Z_le_Q
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hQn : ∀ (t : G), t ∈ M → ∀ y ∈ Q, t * y * t⁻¹ ∈ Q := fun t ht y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ht) y).mp hy
  have hb_img : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
  refine ⟨GaloisField 2 m, inferInstance, inferInstance, γ, M₀, ρ, b, ?_⟩
  refine
    { model := h
      card := h.card
      dim := h.finrank_E hw hK
      conj := hρ
      lin := ?_
      iso := ?_
      b_ne := hb0
      fix := ?_
      stab := ?_
      b_img := hb_img }
  · intro g hg c v
    obtain ⟨t, ht, rfl⟩ := tensorSetup_mem_bar hg
    obtain ⟨T, hT, -⟩ := tensorSetup_rho_linear hρ h t (tensorSetup_conj_of_H0 ht)
    rw [hT, hT, map_smul]
  · intro g hg v w
    obtain ⟨t, ht, rfl⟩ := tensorSetup_mem_bar hg
    obtain ⟨T, hT, hTB⟩ := tensorSetup_rho_linear hρ h t (tensorSetup_conj_of_H0 ht)
    rw [hT, hT]
    exact hTB v w
  · intro v
    constructor
    · intro hv
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj v
      have hx : x ∈ CQt Q Z (LB M Q B) := by
        refine ⟨hxQ, fun t ht => ?_⟩
        have hmem : (QuotientGroup.mk (⟨t, hc.LB_le_M ht⟩ : ↥M) : Mbar M Q) ∈
            bar M Q (LB M Q B) := (tensorSetup_mk_mem_iff hQLB ⟨t, hc.LB_le_M ht⟩).mpr ht
        have h1 : M₀.π ((t : G) * x * (t : G)⁻¹) = M₀.π x :=
          (hρ ⟨t, hc.LB_le_M ht⟩ x hxQ).trans (hv _ hmem)
        exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ
          (hQn t (hc.LB_le_M ht) x hxQ)).mpr h1
      rw [h35] at hx
      obtain ⟨s, hs⟩ := (hB _).mp ((hle hx).2)
      exact Submodule.mem_span_singleton.mpr ⟨s, hs.symm⟩
    · intro hv ℓ hℓ
      obtain ⟨t, ht, rfl⟩ := tensorSetup_mem_bar hℓ
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      obtain ⟨T, hT, -⟩ := tensorSetup_rho_linear hρ h t (fun z hz => hc.LB_centralizes_Z ht z hz)
      have hfixb : (ρ (QuotientGroup.mk t)).toAdd b = b := by
        obtain ⟨u, huB, huQ, hu⟩ := hb_img
        have h2 : M₀.π ((t : G) * u * (t : G)⁻¹) = M₀.π u :=
          (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) huQ (hQn (t : G) t.2 u huQ)).mp
            (hc.comm_B_mem_Z ht huB)
        rw [← hu, ← hρ t u huQ]
        exact h2
      rw [hT, map_smul, (hT b).symm.trans hfixb]
  · rintro g ⟨c, hc'⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨σ, hσ⟩ := hsemi a
    have hN : (a : G) ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have hxZB : x ∈ B ⊔ Z := hx
      have hxQ : x ∈ Q := hBZQ hxZB
      obtain ⟨s, hs⟩ := (hB _).mp ((hle hxZB).2)
      have hax : (a : G) * x * (a : G)⁻¹ ∈ Q := hQn (a : G) a.2 x hxQ
      have himg : M₀.π ((a : G) * x * (a : G)⁻¹) ∈ M₀.img B := by
        rw [hB]
        refine ⟨σ s * c, ?_⟩
        rw [hρ a x hxQ, hs, hσ, hc', smul_smul]
      exact (Tim79.QuadModel.mem_img_iff (M₀ := M₀) (S := B ⊔ Z) le_sup_right hax).mp
        (Tim79.QuadModel.img_mono (M₀ := M₀) (S := B) (T := B ⊔ Z) le_sup_left himg)
    have hL : (a : G) ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      (hc.mem_normalizer_LB_iff h35 a.2).mpr hN
    have key : ∀ y : ↥M, (QuotientGroup.mk y : Mbar M Q) ∈ bar M Q (LB M Q B) ↔
        (y : G) ∈ LB M Q B := fun y => tensorSetup_mk_mem_iff hQLB y
    rw [Subgroup.mem_normalizer_iff]
    intro n
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective n
    have e : (QuotientGroup.mk a : Mbar M Q) * QuotientGroup.mk t * (QuotientGroup.mk a)⁻¹ =
        QuotientGroup.mk (a * t * a⁻¹) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [e, key, key]
    exact Subgroup.mem_normalizer_iff.mp hL (t : G)

end Setup

end CFSG.RankThree.GF2n.Stroth80
