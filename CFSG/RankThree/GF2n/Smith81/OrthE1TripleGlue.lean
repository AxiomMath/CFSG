module

public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleCore
public import CFSG.RankThree.GF2n.Smith81.OrthE1B2

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Dictionary

variable {G : Type} [Group G] {Q H : Subgroup G} {T : Type*} [Group T] (Ψ : ↥H →* T)

@[expose] def Img (S : Subgroup G) : Subgroup T := (S.subgroupOf H).map Ψ

theorem mem_Img {S : Subgroup G} {y : T} :
    y ∈ Img Ψ S ↔ ∃ x : ↥H, (x : G) ∈ S ∧ Ψ x = y := by
  unfold Img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem Img_mono {S S' : Subgroup G} (h : S ≤ S') : Img Ψ S ≤ Img Ψ S' := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_Img Ψ).mp hy
  exact (mem_Img Ψ).mpr ⟨x, h hx, rfl⟩

section Kernel

variable (hΨ : ∀ x : ↥H, Ψ x = 1 ↔ (x : G) ∈ Q)
include hΨ

theorem mem_of_mem_Img {S : Subgroup G} (hQS : Q ≤ S) (x : ↥H) (h : Ψ x ∈ Img Ψ S) :
    (x : G) ∈ S := by
  obtain ⟨x₀, hx₀, he⟩ := (mem_Img Ψ).mp h
  have h1 : Ψ (x₀⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have h2 : ((x₀⁻¹ * x : ↥H) : G) ∈ Q := (hΨ _).mp h1
  have h3 : (x : G) = (x₀ : G) * ((x₀⁻¹ * x : ↥H) : G) := by
    simp
  rw [h3]
  exact S.mul_mem hx₀ (hQS h2)

theorem Img_le_iff {S S' : Subgroup G} (hQS' : Q ≤ S') (hS : S ≤ H) :
    Img Ψ S ≤ Img Ψ S' ↔ S ≤ S' := by
  refine ⟨fun h x hx => ?_, Img_mono Ψ⟩
  have hxH : x ∈ H := hS hx
  have : Ψ ⟨x, hxH⟩ ∈ Img Ψ S' := h ((mem_Img Ψ).mpr ⟨⟨x, hxH⟩, hx, rfl⟩)
  exact mem_of_mem_Img Ψ hΨ hQS' ⟨x, hxH⟩ this

theorem Img_inj {S S' : Subgroup G} (hQS : Q ≤ S) (hQS' : Q ≤ S') (hS : S ≤ H) (hS' : S' ≤ H)
    (h : Img Ψ S = Img Ψ S') : S = S' :=
  le_antisymm ((Img_le_iff Ψ hΨ hQS' hS).mp h.le) ((Img_le_iff Ψ hΨ hQS hS').mp h.ge)

theorem Img_inf {S S' : Subgroup G} (hQS : Q ≤ S) :
    Img Ψ (S ⊓ S') = Img Ψ S ⊓ Img Ψ S' := by
  apply le_antisymm
  · exact le_inf (Img_mono Ψ inf_le_left) (Img_mono Ψ inf_le_right)
  · intro y hy
    obtain ⟨hyS, hyT⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨x, hxT, rfl⟩ := (mem_Img Ψ).mp hyT
    have hxS : (x : G) ∈ S := mem_of_mem_Img Ψ hΨ hQS x hyS
    exact (mem_Img Ψ).mpr ⟨x, ⟨hxS, hxT⟩, rfl⟩

theorem Img_bot_of_le {S : Subgroup G} (hS : S ≤ Q) : Img Ψ S = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_Img Ψ).mp hy
  exact (hΨ x).mpr (hS hx)

theorem card_Img {S : Subgroup G} (hQS : Q ≤ S) (hS : S ≤ H) :
    Nat.card S = Nat.card Q * Nat.card (Img Ψ S) := by
  let f : ↥S →* T := Ψ.comp (Subgroup.inclusion hS)
  have hrange : f.range = Img Ψ S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_Img Ψ).mpr ⟨⟨x, hS x.2⟩, x.2, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := (mem_Img Ψ).mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : f.ker = Q.subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hΨ ⟨x, hS x.2⟩
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card S := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hker, hrange] at h1
  rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv]

theorem Img_comm {S S' : Subgroup G} (hcomm : ∀ a ∈ S, ∀ b ∈ S', ⁅a, b⁆ ∈ Q) :
    ∀ u ∈ Img Ψ S, ∀ v ∈ Img Ψ S', u * v = v * u := by
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := (mem_Img Ψ).mp hu
  obtain ⟨b, hb, rfl⟩ := (mem_Img Ψ).mp hv
  have h1 : Ψ ⁅a, b⁆ = 1 := (hΨ _).mpr (by
    simpa [commutatorElement_def] using hcomm a ha b hb)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

end Kernel

theorem Img_sup {S S' : Subgroup G} (hS : S ≤ H) (hS' : S' ≤ H) :
    Img Ψ (S ⊔ S') = Img Ψ S ⊔ Img Ψ S' := by
  unfold Img
  rw [Subgroup.subgroupOf_sup hS hS', Subgroup.map_sup]

theorem Img_conj (x : ↥H) {S : Subgroup G} (hS : S ≤ H) :
    Img Ψ (conjSubgroup (x : G) S) = (Img Ψ S).map (MulAut.conj (Ψ x)).toMonoidHom := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := (mem_Img Ψ).mp hy
    have hz' : (x : G)⁻¹ * (z : G) * (x : G) ∈ S := mem_conjSubgroup.mp hz
    have hwH : (x : G)⁻¹ * (z : G) * (x : G) ∈ H :=
      mul_mem (mul_mem (inv_mem x.2) z.2) x.2
    refine ⟨Ψ ⟨(x : G)⁻¹ * (z : G) * (x : G), hwH⟩,
      (mem_Img Ψ).mpr ⟨⟨_, hwH⟩, hz', rfl⟩, ?_⟩
    have e : x * ⟨(x : G)⁻¹ * (z : G) * (x : G), hwH⟩ * x⁻¹ = z := by
      apply Subtype.ext
      simp [mul_assoc]
    change Ψ x * Ψ ⟨(x : G)⁻¹ * (z : G) * (x : G), hwH⟩ * (Ψ x)⁻¹ = Ψ z
    rw [← map_inv, ← map_mul, ← map_mul, e]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (mem_Img Ψ).mp hu
    refine (mem_Img Ψ).mpr ⟨x * w * x⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup]
      show (x : G)⁻¹ * ((x : G) * (w : G) * (x : G)⁻¹) * (x : G) ∈ S
      have : (x : G)⁻¹ * ((x : G) * (w : G) * (x : G)⁻¹) * (x : G) = (w : G) := by group
      rw [this]
      exact hw
    · change Ψ (x * w * x⁻¹) = Ψ x * Ψ w * (Ψ x)⁻¹
      rw [map_mul, map_mul, map_inv]

theorem not_pgroup_of_card {A : Type*} [Group A] [Finite A] {q n : ℕ}
    (hc : Nat.card A = q * (q ^ 2 - 1)) (hq : q = 2 ^ n) (h4 : 4 ≤ q) : ¬ IsPGroup 2 A := by
  intro h2
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hq; omega
    · exact h
  have hqe : Even q := by rw [hq]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hodd := orth_odd_sq_sub_one hqe (by omega)
  rw [hc] at hj
  have h16 : 16 ≤ q ^ 2 := by nlinarith
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show q ^ 2 - 1 ≠ 1 by omega)
  have h3 : p ∣ 2 ^ j := hj ▸ dvd_mul_of_dvd_right hpd _
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3)
  subst hp2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)

section SLImage

variable (hΨ : ∀ x : ↥H, Ψ x = 1 ↔ (x : G) ∈ Q)
include hΨ

noncomputable def imgEquiv {F : Subgroup G} [(Q.subgroupOf F).Normal] (hQF : Q ≤ F) (hFH : F ≤ H) :
    (↥F ⧸ Q.subgroupOf F) ≃* ↥(Img Ψ F) := by
  let f : ↥F →* T := Ψ.comp (Subgroup.inclusion hFH)
  have hrange : f.range = Img Ψ F := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_Img Ψ).mpr ⟨⟨x, hFH x.2⟩, x.2, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := (mem_Img Ψ).mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : f.ker = Q.subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hΨ ⟨x, hFH x.2⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))

theorem Img_sl_facts {F : Subgroup G} (hQF : Q ≤ F) (hFH : F ≤ H) {q n : ℕ}
    (hF : QuotSat F Q (IsSLModel 2 q)) (hq : q = 2 ^ n) (h4 : 4 ≤ q) :
    IsSimpleGroup ↥(Img Ψ F) ∧ ¬ IsMulCommutative ↥(Img Ψ F) ∧
      Nat.card ↥(Img Ψ F) = q * (q ^ 2 - 1) := by
  obtain ⟨hN, hX⟩ := hF
  haveI := hN
  obtain ⟨hcard, hsimp, hcen⟩ := b2_sl_facts hX hq h4
  let e := imgEquiv Ψ hΨ hQF hFH
  haveI : IsSimpleGroup ↥(Img Ψ F) := e.symm.isSimpleGroup
  refine ⟨inferInstance, ?_, ?_⟩
  · intro hcomm
    have h1 : ∀ x : (↥F ⧸ Q.subgroupOf F), x = 1 := by
      intro x
      apply hcen
      intro y
      apply e.injective
      rw [map_mul, map_mul]
      exact hcomm.is_comm.comm _ _
    haveI := hsimp.toNontrivial
    obtain ⟨a, ha⟩ := exists_ne (1 : (↥F ⧸ Q.subgroupOf F))
    exact ha (h1 a)
  · rw [← Nat.card_congr e.toEquiv, hcard]

end SLImage

end Dictionary

section Instances

variable {G : Type} [Group G] {M Q Z : Subgroup G} (AM : ActionModel M Q Z)
  (θ : AM.M₀.E ≃ₗ[AM.K] Tensor3 AM.K)

@[expose] def PhiT : ↥(H0 M Z) →* T3E AM.K := (conjE θ).toMonoidHom.comp AM.φ

theorem PhiT_ker (x : ↥(H0 M Z)) : PhiT AM θ x = 1 ↔ (x : G) ∈ Q := by
  rw [← AM.φ_ker]
  constructor
  · intro h
    exact (conjE θ).injective (by simpa [PhiT] using h)
  · intro h
    simp [PhiT, h]

abbrev TI (S : Subgroup G) : Subgroup (T3E AM.K) := Img (PhiT AM θ) S

theorem TI_le_Ok {κ : AM.K} (hθ : ∀ e, AM.M₀.Qf e = Qk κ (θ e)) (S : Subgroup G) :
    TI AM θ S ≤ Ok κ := by
  intro y hy T
  obtain ⟨x, hx, rfl⟩ := (mem_Img (PhiT AM θ)).mp hy
  change Qk κ (θ (AM.φ x (θ.symm T))) = Qk κ T
  rw [← hθ, AM.φ_Qf, hθ, LinearEquiv.apply_symm_apply]

theorem TI_eq_map (S : Subgroup G) :
    TI AM θ S = (AM.actImage S).map (conjE θ).toMonoidHom := by
  unfold TI Img ActionModel.actImage PhiT
  rw [Subgroup.map_map]

theorem factorAct_of_img (F : Subgroup G) (act : Matrix (Fin 2) (Fin 2) AM.K →
      Tensor3 AM.K → Tensor3 AM.K)
    (actE : Matrix.SpecialLinearGroup (Fin 2) AM.K →* T3E AM.K)
    (hact : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) AM.K) T,
      actE A T = act (A : Matrix (Fin 2) (Fin 2) AM.K) T)
    (himg : Img (PhiT AM θ) F = actE.range) : FactorAct AM θ F act := by
  have key : ∀ (x : ↥(H0 M Z)) e, θ (AM.φ x e) = PhiT AM θ x (θ e) := fun x e => by
    change θ (AM.φ x e) = θ (AM.φ x (θ.symm (θ e)))
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨fun x hx => ?_, fun A hA => ?_⟩
  · have hmem : PhiT AM θ x ∈ Img (PhiT AM θ) F := (mem_Img _).mpr ⟨x, hx, rfl⟩
    rw [himg] at hmem
    obtain ⟨A, hA⟩ := hmem
    refine ⟨A, A.2, fun e => ?_⟩
    rw [key, ← hA, hact]
  · let A' : Matrix.SpecialLinearGroup (Fin 2) AM.K := ⟨A, hA⟩
    have hmem : actE A' ∈ Img (PhiT AM θ) F := by
      rw [himg]
      exact ⟨A', rfl⟩
    obtain ⟨x, hx, hxA⟩ := (mem_Img _).mp hmem
    refine ⟨x, hx, fun e => ?_⟩
    rw [key, hxA]
    exact hact A' (θ e)

end Instances

section LCStd

theorem lcData_std {K : Type} [Field K] [CharP K 2] (S : QSpace K)
    (V : Submodule K S.E) (Xg : Subgroup (S.E ≃ₗ[K] S.E)) (hXO : Xg ≤ S.O) (hts : S.IsTS V)
    (hperp : ∀ e, (∀ v ∈ V, S.B e v = 0) → e ∈ V) (hV : Module.finrank K V = 4)
    (hE : Module.finrank K S.E = 8)
    (c : ↥V ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K))
    (hirr : ∀ A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      (∀ g ∈ StatedOmega (StatedQuadPlus 2 K),
        A * (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * A) →
        ∃ k : K, A = k • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hact : ActsAsNatural S V Xg c (StatedQuadPlus 2 K)) :
    ∃ D : LCData S V Xg, ∀ v w, D.pf v w = plusPolar 2 K (c v) (c w) := by
  obtain ⟨hX, h1, h2, -⟩ := hact
  let act : ↥Xg → V →ₗ[K] V := fun g => ((g : S.E ≃ₗ[K] S.E) : S.E →ₗ[K] S.E).restrict (hX g g.2)
  have hc : ∀ g : ↥Xg, ∃ A ∈ StatedOmega (StatedQuadPlus 2 K),
      ∀ v : V, c (act g v) = (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ c v := by
    intro g
    obtain ⟨A, hA, hAe⟩ := h1 g g.2
    exact ⟨A, hA, fun v => hAe v v.2⟩
  have hnd : ∀ x, (∀ y, plusPolar 2 K x y = 0) → x = 0 := plusPolar_nondeg
  refine ⟨
    { O_le := hXO
      ts := hts
      perp := hperp
      dimV := hV
      dimE := hE
      act := act
      act_coe := fun _ _ => rfl
      pf := (plusPolar 2 K).compl₁₂ c.toLinearMap c.toLinearMap
      pf_nondeg := fun v hv => by
        apply c.injective
        rw [map_zero]
        apply hnd
        intro y
        have := hv (c.symm y)
        simpa [LinearMap.compl₁₂_apply] using this
      pf_alt := fun v => (plusPolar_isPolar (m := 2) (K := K)).alt (c v)
      pf_inv := fun g v w => by
        obtain ⟨A, hA, hAe⟩ := hc g
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
        rw [hAe v, hAe w]
        exact (plusPolar_isPolar (m := 2) (K := K)).map_apply (Matrix.mulVecLin A)
          (fun x => KFLin.isometry_of_mem_statedOmega hA x) (c v) (c w)
      schur := fun a ha => by
        let L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
          c.toLinearMap ∘ₗ a ∘ₗ c.symm.toLinearMap
        let M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := LinearMap.toMatrix' L
        have hM : ∀ x, M *ᵥ x = L x := LinearMap.toMatrix'_mulVec L
        obtain ⟨k, hk⟩ := hirr M (by
          intro A hA
          obtain ⟨g, hg, hgA⟩ := h2 A hA
          refine Matrix.ext_iff_mulVec.2 fun x => ?_
          have key : ∀ v : V, c (act ⟨g, hg⟩ v) = (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
              c v := fun v => hgA v v.2
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, hM]
          obtain ⟨v, rfl⟩ := c.surjective x
          simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
          rw [← key v, LinearEquiv.symm_apply_apply, ha ⟨g, hg⟩ v, key (a v)])
        refine ⟨k, fun v => ?_⟩
        apply c.injective
        have := hM (c v)
        rw [hk, Matrix.smul_mulVec, Matrix.one_mulVec] at this
        simpa [L, map_smul] using this.symm },
    fun v w => rfl⟩

end LCStd

section TwoBound

theorem card_SL2_eq (K : Type) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
    CFSG.Open.StatedAPI.card_statedSL_two]

theorem card_sup_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p =>
    ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      have : (a : G) * b * (b : G)⁻¹ = a' * b' * (b : G)⁻¹ := by rw [h1]
      rw [mul_inv_cancel_right] at this
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a' * b' * (b : G)⁻¹) := by rw [← this]
        _ = b' * (b : G)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem a'.2) a.2,
      h2 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hinf, Subgroup.mem_bot] at h3
    have ha : a = a' := Subtype.ext (inv_mul_eq_one.mp h3).symm
    subst ha
    have : (b : G) = b' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext this)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := fu_mem_sup hcomm hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem two_group_bound {n : ℕ} (hq : Nat.card K = 2 ^ n) (hK : 4 ≤ Nat.card K)
    (U : Subgroup (T3E K)) (hU : U ≤ lineG ⊔ rowG) (hsq : ∀ u ∈ U, u * u = 1) :
    Nat.card U ≤ Nat.card K ^ 2 := by
  have hinf : (lineG : Subgroup (T3E K)) ⊓ rowG = ⊥ := by
    rw [eq_bot_iff, ← slotG_inf_rowG (K := K)]
    exact inf_le_inf_right _ lineG_le_slotG
  have hcard : Nat.card ↥(lineG ⊔ rowG : Subgroup (T3E K)) =
      Nat.card K * (Nat.card K * (Nat.card K ^ 2 - 1)) := by
    rw [card_sup_of_comm lineG_comm_rowG hinf, card_lineG, card_rowG, card_SL2_eq]
  have hp : IsPGroup 2 ↥U := fun u => ⟨1, Subtype.ext (by simpa [pow_two] using hsq u u.2)⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp hp
  have hdvd := Subgroup.card_dvd_of_le hU
  rw [hj, hcard] at hdvd
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hq; omega
    · exact h
  have hqe : Even (Nat.card K) := by rw [hq]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hodd := orth_odd_sq_sub_one hqe (by omega)
  have hcop : Nat.Coprime (2 ^ j) (Nat.card K ^ 2 - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have h2 : 2 ^ j ∣ Nat.card K * Nat.card K := by
    have : Nat.card K * (Nat.card K * (Nat.card K ^ 2 - 1)) =
        Nat.card K * Nat.card K * (Nat.card K ^ 2 - 1) := by ring
    rw [this] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  rw [hj]
  exact Nat.le_of_dvd (by positivity) (by rw [pow_two]; exact h2)

end TwoBound

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
