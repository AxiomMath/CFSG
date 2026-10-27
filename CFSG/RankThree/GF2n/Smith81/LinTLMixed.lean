module

public import CFSG.RankThree.GF2n.Smith81.LinTLAbelian
public import CFSG.RankThree.GF2n.Smith81.LinTLIndexTwo
public import CFSG.RankThree.GF2n.Smith81.LinCoord
public import CFSG.RankThree.GF2n.Stroth80.Sec34TailModule

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

section Perp

variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]

private def subOfSmul (S : AddSubgroup E) (hS : ∀ (c : K) {x : E}, x ∈ S → c • x ∈ S) :
    Submodule K E where
  carrier := (S : Set E)
  add_mem' := fun ha hb => S.add_mem ha hb
  zero_mem' := S.zero_mem
  smul_mem' := fun c {_} hx => hS c hx

private theorem exists_perp_decomp (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (hanti : ∀ x y, B x y = -B y x)
    (W₁ W₂ : Submodule K E) (hsum : ∀ e : E, ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, e = w₁ + w₂)
    (hW₁ : ∀ x ∈ W₁, ∀ y ∈ W₁, B x y = 0) (hW₂ : ∀ x ∈ W₂, ∀ y ∈ W₂, B x y = 0)
    {b₂ : E} (hb₂W : b₂ ∈ W₂) (hb₂ : b₂ ≠ 0) :
    ∃ e₀ ∈ W₁, ∀ e ∈ W₁, ∃ μ : K, B (e - μ • e₀) b₂ = 0 := by
  have he₀ : ∃ e₀ ∈ W₁, B e₀ b₂ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hb₂
    apply hnd
    intro f
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hsum f
    have h1 : B b₂ w₁ = 0 := by rw [hanti b₂ w₁, hcon w₁ hw₁, neg_zero]
    have h2 : B b₂ w₂ = 0 := hW₂ b₂ hb₂W w₂ hw₂
    rw [map_add, h1, h2, add_zero]
  obtain ⟨e₀, he₀W, he₀b⟩ := he₀
  refine ⟨e₀, he₀W, fun e _ => ⟨B e b₂ / B e₀ b₂, ?_⟩⟩
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [div_mul_cancel₀ _ he₀b, sub_self]

private theorem scalar_of_perp (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (hanti : ∀ x y, B x y = -B y x)
    (W₁ W₂ : Submodule K E) (hsum : ∀ e : E, ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, e = w₁ + w₂)
    (hW₁ : ∀ x ∈ W₁, ∀ y ∈ W₁, B x y = 0) (hW₂ : ∀ x ∈ W₂, ∀ y ∈ W₂, B x y = 0)
    {b₁ : E} (hb₁W : b₁ ∈ W₁) (hb₁ne : b₁ ≠ 0) {g : E} (hgW : g ∈ W₁)
    (hg : ∀ f ∈ W₂, B f b₁ = 0 → B g f = 0) : ∃ μ : K, g = μ • b₁ := by
  have hf₀ : ∃ f₀ ∈ W₂, B f₀ b₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hb₁ne
    apply hnd
    intro f
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hsum f
    have h1 : B b₁ w₁ = 0 := hW₁ b₁ hb₁W w₁ hw₁
    have h2 : B b₁ w₂ = 0 := by rw [hanti b₁ w₂, hcon w₂ hw₂, neg_zero]
    rw [map_add, h1, h2, add_zero]
  obtain ⟨f₀, hf₀W, hκ⟩ := hf₀
  have hproj : ∀ f ∈ W₂, B g f = (B f b₁ / B f₀ b₁) * B g f₀ := by
    intro f hf
    have hf' : f - (B f b₁ / B f₀ b₁) • f₀ ∈ W₂ := W₂.sub_mem hf (W₂.smul_mem _ hf₀W)
    have h1 : B (f - (B f b₁ / B f₀ b₁) • f₀) b₁ = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [div_mul_cancel₀ _ hκ, sub_self]
    have h2 := hg _ hf' h1
    simp only [map_sub, map_smul, smul_eq_mul] at h2
    linear_combination h2
  refine ⟨-(B g f₀ / B f₀ b₁), ?_⟩
  have hz : g - (-(B g f₀ / B f₀ b₁)) • b₁ = 0 := by
    apply hnd
    intro f
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hsum f
    have h1 : B (g - (-(B g f₀ / B f₀ b₁)) • b₁) w₁ = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hW₁ g hgW w₁ hw₁, hW₁ b₁ hb₁W w₁ hw₁]
      ring
    have h2 : B (g - (-(B g f₀ / B f₀ b₁)) • b₁) w₂ = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hproj w₂ hw₂, hanti b₁ w₂]
      ring
    rw [map_add, h1, h2, add_zero]
  exact sub_eq_zero.mp hz

end Perp

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem LinSetup.not_mixed_of_index_le_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) {A : Subgroup G} (hA : Ctx M Q Z A) {P : Subgroup G} (hQP : Q ≤ P)
    (hPA : P ≤ LB M Q A) (hPB : P ≤ Lgen M (LB M Q B))
    (hPn₁ : P ≤ Subgroup.normalizer (V₁ : Set G)) (hPn₂ : P ≤ Subgroup.normalizer (V₂ : Set G))
    (hPi : (P.subgroupOf (LB M Q A)).index ≤ 2) :
    ¬ ((A ⊔ Z) ⊓ V₁ = Z ∧ (A ⊔ Z) ⊓ V₂ = Z) := by
  rintro ⟨hm1, hm2⟩
  have hcom₁ : ∀ u ∈ V₁, ∀ v ∈ V₁, u * v = v * u := fun u hu v hv =>
    LinSetup.comm_eq_one_V₁ hc hS hn hu hv
  have hcom₂ : ∀ u ∈ V₂, ∀ v ∈ V₂, u * v = v * u := fun u hu v hv =>
    LinSetup.comm_eq_one_V₂ hc hS hn hu hv
  have hsumQ : ∀ q ∈ Q, ∃ a ∈ V₁, ∃ b' ∈ V₂, q = a * b' := LinSetup.exists_mul hc.hyp hS
  have hfaith := linFaithfulStatement_holds G M Q Z B n V₁ V₂ hc hS
  have hwidth : Width Q Z n := LinSetup.width hc.hyp hS
  have hS2 := hS
  obtain ⟨F₀, hF₀field, hF₀fin, hF₀card, φ', hrange, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, -, -⟩ := hS2
  have hPH : P ≤ H0 M Z := fun t ht => hA.LB_le_H0 (hPA ht)
  have hPM : P ≤ M := fun t ht => hA.LB_le_M (hPA ht)
  have hPi' : ((QB A ⊓ M ⊓ P).subgroupOf (QB A ⊓ M)).index ≤ 2 := by
    have hne : (P.subgroupOf (LB M Q A)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : QB A ⊓ M ≤ LB M Q A := le_sup_right
    show (QB A ⊓ M ⊓ P).relIndex (QB A ⊓ M) ≤ 2
    rw [Subgroup.inf_relIndex_left]
    exact (Subgroup.relIndex_le_of_le_right hle hne).trans hPi
  have hL₁ : Q ⊓ QB A ⊓ V₁ = Z := hA.inf_QB_inf_eq_of_sup_inf_sub hZV₁ hPA hPn₁ hPi' hm1
  have hL₂ : Q ⊓ QB A ⊓ V₂ = Z := hA.inf_QB_inf_eq_of_sup_inf_sub hZV₂ hPA hPn₂ hPi' hm2
  obtain ⟨K, hKf, hKfin, -, γ, M₀, hGM⟩ := stroth_globalModelData hc.hyp
  obtain ⟨u, -, -, hAline, hcentA, -⟩ := hA.dictB hGM
  obtain ⟨φ, hφπ, hφQ, hφQf⟩ := exists_actionHom_H0 hc.hyp hGM
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨Φc, hΦc, hΦ₁, hΦ₂⟩ := exists_equivariant_coord M₀ (φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => hφπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, hCΦ⟩ := exists_natDualCoord_of_equivariant (φ.comp (Subgroup.inclusion hSH)) φ' hn
    hrange (by rw [hGM.card, hF₀card]) Φc hΦc
  have hV1 : ∀ e : M₀.E, e ∈ M₀.img V₁ ↔ (C.Ψ e).2 = 0 := fun e => by
    rw [hCΦ]; exact hΦ₁ e
  have hV2 : ∀ e : M₀.E, e ∈ M₀.img V₂ ↔ (C.Ψ e).1 = 0 := fun e => by
    rw [hCΦ]; exact hΦ₂ e
  have hK₁ : ∀ (c : K) {x : M₀.E}, x ∈ M₀.img V₁ → c • x ∈ M₀.img V₁ := by
    intro c x hx
    rw [hV1] at hx ⊢
    rw [C.smul]
    show C.θ₂ c • (C.Ψ x).2 = 0
    rw [hx, smul_zero]
  have hK₂ : ∀ (c : K) {x : M₀.E}, x ∈ M₀.img V₂ → c • x ∈ M₀.img V₂ := by
    intro c x hx
    rw [hV2] at hx ⊢
    rw [C.smul]
    show C.θ₁ c • (C.Ψ x).1 = 0
    rw [hx, smul_zero]
  let W₁ : Submodule K M₀.E := subOfSmul (M₀.img V₁) hK₁
  let W₂ : Submodule K M₀.E := subOfSmul (M₀.img V₂) hK₂
  have hW₁mem : ∀ x : M₀.E, x ∈ W₁ ↔ x ∈ M₀.img V₁ := fun x => Iff.rfl
  have hW₂mem : ∀ x : M₀.E, x ∈ W₂ ↔ x ∈ M₀.img V₂ := fun x => Iff.rfl
  have hsumE : ∀ e : M₀.E, ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, e = w₁ + w₂ := by
    intro e
    obtain ⟨q, hq, rfl⟩ := M₀.π_surj e
    obtain ⟨a, ha, b', hb', rfl⟩ := hsumQ q hq
    exact ⟨M₀.π a, (hW₁mem _).mpr (M₀.pi_mem_img ha (hV₁Q ha)), M₀.π b',
      (hW₂mem _).mpr (M₀.pi_mem_img hb' (hV₂Q hb')), M₀.π_mul a (hV₁Q ha) b' (hV₂Q hb')⟩
  have hW₁iso : ∀ x ∈ W₁, ∀ y ∈ W₁, M₀.B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, haQ, rfl⟩ := (hW₁mem x).mp hx
    obtain ⟨a', ha', ha'Q, rfl⟩ := (hW₁mem y).mp hy
    exact (M₀.comm_iff_B hGM.reg haQ ha'Q).mp (hcom₁ a ha a' ha')
  have hW₂iso : ∀ x ∈ W₂, ∀ y ∈ W₂, M₀.B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, haQ, rfl⟩ := (hW₂mem x).mp hx
    obtain ⟨a', ha', ha'Q, rfl⟩ := (hW₂mem y).mp hy
    exact (M₀.comm_iff_B hGM.reg haQ ha'Q).mp (hcom₂ a ha a' ha')
  have hnd : ∀ e : M₀.E, (∀ f : M₀.E, M₀.B e f = 0) → e = 0 := fun e h => M₀.nondeg e h
  have hanti : ∀ x y : M₀.E, M₀.B x y = -M₀.B y x := fun x y =>
    Tim79.QuadModel.B_comm (M₀ := M₀) x y
  have hbne : ∀ (V : Subgroup G), Z ≤ V → V ≤ Q → (A ⊔ Z) ⊓ V = Z →
      (∀ s : K, s • u ∈ M₀.img V) → False := by
    intro V hZV hVQ hAV hsV
    have hAV' : A ≤ V := fun x hx => by
      obtain ⟨s, hs⟩ := (hAline (M₀.π x)).mp (M₀.pi_mem_img hx (hA.le hx))
      exact (M₀.mem_img_iff hZV (hA.le hx)).mp (by rw [hs]; exact hsV s)
    have hAZ : A ⊔ Z = Z := by
      have h1 : (A ⊔ Z) ⊓ V = A ⊔ Z := inf_eq_left.mpr (sup_le hAV' hZV)
      rw [h1] at hAV
      exact hAV
    obtain ⟨g, hg⟩ := hA.conj
    have hcard : Nat.card Z ≤ Nat.card A := le_of_eq (by rw [hg, card_conjSubgroup])
    exact hA.ne (Subgroup.eq_of_le_of_card_ge (le_sup_left.trans hAZ.le) hcard)
  obtain ⟨u₁, hu₁W, u₂, hu₂W, husum⟩ := hsumE u
  have hu₁ne : u₁ ≠ 0 := by
    intro h0
    refine hbne V₂ hZV₂ hV₂Q hm2 fun s => (hW₂mem _).mp ?_
    rw [husum, h0, zero_add]
    exact W₂.smul_mem s hu₂W
  have hu₂ne : u₂ ≠ 0 := by
    intro h0
    refine hbne V₁ hZV₁ hV₁Q hm1 fun s => (hW₁mem _).mp ?_
    rw [husum, h0, add_zero]
    exact W₁.smul_mem s hu₁W
  obtain ⟨e₀, he₀W, hdec⟩ := exists_perp_decomp M₀.B hnd hanti W₁ W₂ hsumE hW₁iso hW₂iso
    hu₂W hu₂ne
  let Tₕ : ↥P →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hPH)
  have hTπ : ∀ (t : ↥P) (x : G), x ∈ Q →
      M₀.π ((t : G) * x * (t : G)⁻¹) = Tₕ t (M₀.π x) :=
    fun t x hx => hφπ ⟨(t : G), hPH t.2⟩ x hx
  have hTQf : ∀ (t : ↥P) (e : M₀.E), M₀.Qf (Tₕ t e) = M₀.Qf e :=
    fun t e => hφQf ⟨(t : G), hPH t.2⟩ e
  have hTiso : ∀ (t : ↥P) (e f : M₀.E), M₀.B (Tₕ t e) (Tₕ t f) = M₀.B e f :=
    fun t e f => polar_apply_apply_of_isometry M₀.B M₀.Qf M₀.Qf_add (Tₕ t) (hTQf t) e f
  have hTQ1 : ∀ t : ↥P, (t : G) ∈ Q → Tₕ t = 1 :=
    fun t ht => (hφQ ⟨(t : G), hPH t.2⟩).mpr ht
  have hTW₁ : ∀ (t : ↥P) (e : M₀.E), e ∈ W₁ → Tₕ t e ∈ W₁ := by
    intro t e he
    obtain ⟨v, hv, hvQ, rfl⟩ := (hW₁mem e).mp he
    rw [← hTπ t v hvQ]
    have hcv : (t : G) * v * (t : G)⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hPn₁ t.2) v).mp hv
    exact (hW₁mem _).mpr (M₀.pi_mem_img hcv (hV₁Q hcv))
  have hfixV : ∀ (V : Subgroup G), Z ≤ V → V ≤ Q → P ≤ Subgroup.normalizer (V : Set G) →
      Q ⊓ QB A ⊓ V = Z → ∀ (t : ↥P) (x : G), x ∈ V → M₀.B (M₀.π x) u = 0 →
        Tₕ t (M₀.π x) = M₀.π x := by
    intro V hZV hVQ hVn hL t x hxV hxb
    have hxQ : x ∈ Q := hVQ hxV
    have hxC : x ∈ Subgroup.centralizer (A : Set G) := (hcentA x hxQ).mpr hxb
    have hcQB : ⁅(t : G), x⁆ ∈ Q ⊓ QB A :=
      hA.comm_mem_inf_of_mem_LB (hPA t.2) (Subgroup.mem_inf.mpr ⟨hxQ, hxC⟩)
    have hcV : ⁅(t : G), x⁆ ∈ V := by
      have h3 : (t : G) * x * (t : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hVn t.2) x).mp hxV
      rw [commutatorElement_def]
      exact V.mul_mem h3 (V.inv_mem hxV)
    have hcZ : ⁅(t : G), x⁆ ∈ Z := by
      rw [← hL]
      exact Subgroup.mem_inf.mpr ⟨hcQB, hcV⟩
    have hz : M₀.π ⁅(t : G), x⁆ = 0 := (M₀.π_ker _ (hA.Z_le_Q hcZ)).mpr hcZ
    have e : (t : G) * x * (t : G)⁻¹ = ⁅(t : G), x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [← hTπ t x hxQ, e, M₀.π_mul _ (hA.Z_le_Q hcZ) x hxQ, hz, zero_add]
  have hfix₁ : ∀ (t : ↥P) (e : M₀.E), e ∈ W₁ → M₀.B e u = 0 → Tₕ t e = e := by
    intro t e he heb
    obtain ⟨x, hx, -, rfl⟩ := (hW₁mem e).mp he
    exact hfixV V₁ hZV₁ hV₁Q hPn₁ hL₁ t x hx heb
  have hfix₂ : ∀ (t : ↥P) (e : M₀.E), e ∈ W₂ → M₀.B e u = 0 → Tₕ t e = e := by
    intro t e he heb
    obtain ⟨x, hx, -, rfl⟩ := (hW₂mem e).mp he
    exact hfixV V₂ hZV₂ hV₂Q hPn₂ hL₂ t x hx heb
  have hgW : ∀ (t : ↥P) (e : M₀.E), e ∈ W₁ → ∃ μ : K, Tₕ t e - e = μ • u₁ := by
    intro t e he
    refine scalar_of_perp M₀.B hnd hanti W₁ W₂ hsumE hW₁iso hW₂iso hu₁W hu₁ne
      (W₁.sub_mem (hTW₁ t e he) he) ?_
    intro f hf hfu₁
    have hfu : M₀.B f u = 0 := by
      rw [husum, map_add, hW₂iso f hf u₂ hu₂W, add_zero]
      exact hfu₁
    have hiso := hTiso t e f
    rw [hfix₂ t f hf hfu] at hiso
    simp only [map_sub, LinearMap.sub_apply]
    rw [hiso, sub_self]
  choose cf hcf using fun t : ↥P => hgW t e₀ he₀W
  have hT0 : ∀ t : ↥P, Tₕ t e₀ = e₀ + cf t • u₁ := fun t => by
    rw [← hcf t]
    abel
  have hTeval : ∀ (t : ↥P) (e : M₀.E) (μ : K), e ∈ W₁ → M₀.B (e - μ • e₀) u₂ = 0 →
      Tₕ t e = (e - μ • e₀) + μ • (e₀ + cf t • u₁) := by
    intro t e μ he hμ
    have hh : e - μ • e₀ ∈ W₁ := W₁.sub_mem he (W₁.smul_mem μ he₀W)
    have hhb : M₀.B (e - μ • e₀) u = 0 := by
      rw [husum, map_add, hW₁iso _ hh u₁ hu₁W, zero_add, hμ]
    have hfixh : Tₕ t (e - μ • e₀) = e - μ • e₀ := hfix₁ t _ hh hhb
    calc Tₕ t e = Tₕ t ((e - μ • e₀) + μ • e₀) := by rw [sub_add_cancel]
      _ = (e - μ • e₀) + μ • (e₀ + cf t • u₁) := by
        rw [map_add, map_smul, hfixh, hT0 t]
  have hFeq : ∀ t t' : ↥P, (t : G)⁻¹ * (t' : G) ∈ Q → cf t = cf t' := by
    intro t t' htt
    have hs1 : Tₕ (t⁻¹ * t') = 1 :=
      hTQ1 (t⁻¹ * t') (by rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact htt)
    have hs : Tₕ t' = Tₕ t := by
      have e1 : t' = t * (t⁻¹ * t') := by group
      rw [e1, map_mul, hs1, mul_one]
    have h1 := hT0 t
    have h2 := hT0 t'
    rw [hs] at h2
    have h3 : cf t • u₁ = cf t' • u₁ := add_left_cancel (h1.symm.trans h2)
    exact smul_left_injective K hu₁ne h3
  have hFinj : ∀ t t' : ↥P, cf t = cf t' → (t : G)⁻¹ * (t' : G) ∈ Q := by
    intro t t' hcc
    by_contra hsQ
    have hT' : ∀ e ∈ W₁, Tₕ t' e = Tₕ t e := by
      intro e he
      obtain ⟨μ, hμ⟩ := hdec e he
      rw [hTeval t' e μ he hμ, hTeval t e μ he hμ, hcc]
    have hinv : ∀ e : M₀.E, Tₕ t⁻¹ (Tₕ t e) = e := by
      intro e
      have h1 : Tₕ t⁻¹ * Tₕ t = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      have h2 := congrArg (fun T : M₀.E ≃ₗ[K] M₀.E => T e) h1
      simpa using h2
    have hsx : ∀ x ∈ V₁, Tₕ (t⁻¹ * t') (M₀.π x) = M₀.π x := by
      intro x hx
      have hxe : M₀.π x ∈ W₁ := (hW₁mem _).mpr (M₀.pi_mem_img hx (hV₁Q hx))
      rw [map_mul, LinearEquiv.mul_apply, hT' _ hxe, hinv]
    have hcomm : ∀ x ∈ V₁, ⁅((t⁻¹ * t' : ↥P) : G), x⁆ ∈ Z := by
      intro x hx
      have hxQ : x ∈ Q := hV₁Q hx
      have hsN : ((t⁻¹ * t' : ↥P) : G) * x * ((t⁻¹ * t' : ↥P) : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hPM (t⁻¹ * t').2)) x).mp hxQ
      have hpi : M₀.π (((t⁻¹ * t' : ↥P) : G) * x *
          ((t⁻¹ * t' : ↥P) : G)⁻¹) = M₀.π x := by
        rw [hTπ (t⁻¹ * t') x hxQ, hsx x hx]
      exact (M₀.comm_mem_iff hxQ hsN).mpr hpi
    obtain ⟨⟨v, hv, hsv⟩, -⟩ := hfaith _ (hPB (t⁻¹ * t').2) hsQ
    exact hsv (hcomm v hv)
  have hwd : ∀ a a' : ↥P, (QuotientGroup.leftRel (Q.subgroupOf P)).r a a' → cf a = cf a' := by
    intro a a' hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    exact hFeq a a' hab
  let ψq : (↥P ⧸ Q.subgroupOf P) → K := Quotient.lift cf hwd
  have hψinj : Function.Injective ψq := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hFinj a a' hxy
  have hcardψ : Nat.card (↥P ⧸ Q.subgroupOf P) ≤ Nat.card K :=
    Nat.card_le_card_of_injective ψq hψinj
  have hidxQ : (Q.subgroupOf P).index ≤ Nat.card Z := by
    have h := hcardψ
    rw [hGM.card] at h
    exact h
  have hcardLB := hA.card_LB_ge hwidth (by omega : 1 ≤ n)
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hpow : Nat.card Z ^ 2 ≤ Nat.card Z ^ (n - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hQcard : Nat.card ↥(Q.subgroupOf P) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
  have hidxQP : Nat.card Q * (Q.subgroupOf P).index = Nat.card ↥P := by
    have h := Subgroup.card_mul_index (Q.subgroupOf P)
    rwa [hQcard] at h
  have hPcard : Nat.card ↥(P.subgroupOf (LB M Q A)) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv
  have hidxPL : Nat.card ↥P * (P.subgroupOf (LB M Q A)).index = Nat.card ↥(LB M Q A) := by
    have h := Subgroup.card_mul_index (P.subgroupOf (LB M Q A))
    rwa [hPcard] at h
  have hmain : Nat.card Q * Nat.card Z ^ 2 ≤ Nat.card Q * (2 * Nat.card Z) := by
    calc Nat.card Q * Nat.card Z ^ 2 ≤ Nat.card Q * Nat.card Z ^ (n - 1) :=
          Nat.mul_le_mul_left _ hpow
      _ ≤ Nat.card ↥(LB M Q A) := hcardLB
      _ = Nat.card ↥P * (P.subgroupOf (LB M Q A)).index := hidxPL.symm
      _ ≤ Nat.card ↥P * 2 := Nat.mul_le_mul_left _ hPi
      _ = Nat.card Q * (Q.subgroupOf P).index * 2 := by rw [hidxQP]
      _ ≤ Nat.card Q * Nat.card Z * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hidxQ)
      _ = Nat.card Q * (2 * Nat.card Z) := by ring
  have hfin : Nat.card Z ^ 2 ≤ 2 * Nat.card Z := Nat.le_of_mul_le_mul_left hmain hQpos
  have h4 : 4 * Nat.card Z ≤ Nat.card Z ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right _ hq4
  linarith

theorem LinSetup.not_mixed (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) :
    ¬ ((B ⊔ Z) ⊓ V₁ = Z ∧ (B ⊔ Z) ⊓ V₂ = Z) := by
  have hS2 := hS
  obtain ⟨_, _, _, -, _, -, -, -, -, -, -, -, -, hact₁, hact₂, -, -⟩ := hS2
  have hLL : LB M Q B ≤ Lgen M (LB M Q B) := le_Lgen_self M (LB M Q B)
  have hPi : ((LB M Q B).subgroupOf (LB M Q B)).index ≤ 2 := by
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  exact LinSetup.not_mixed_of_index_le_two hc hS hn hc (le_sup_left : Q ≤ LB M Q B) le_rfl hLL
    (hLL.trans hact₁.1) (hLL.trans hact₂.1) hPi

end CFSG.RankThree.GF2n.Smith81
