module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepF1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open Equiv (Perm)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

set_option linter.unusedSectionVars false

section Finite

open Equiv

set_option synthInstance.maxSize 2048 in
theorem tabF2_nat_fix : ∀ w : nat.W, w ≠ 1 → (∀ d ∈ S5SylF, nat.act d w = w) →
    ∀ z : Perm (Fin 5), nat.act z w = w → z ∈ S5SylF := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
theorem tabF2_orth_inv : ∀ w0 : orth.W, w0 ≠ 1 → (∀ d ∈ S5SylF, orth.act d w0 = w0) →
    ∀ b ∈ S5SylF, (b ∈ S5ThatF ∨ (b * b = 1 ∧ Perm.sign b ≠ 1)) → ∀ u : orth.W, ∀ d ∈ S5SylF,
      orth.act d (orth.act b u * u⁻¹) = orth.act b u * u⁻¹ ∨
      orth.act d (orth.act b u * u⁻¹) = (orth.act b u * u⁻¹) * w0 := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
theorem tabF2_orth_S4 : ∀ w0 : orth.W, w0 ≠ 1 → (∀ d ∈ S5SylF, orth.act d w0 = w0) →
    ∀ z : Perm (Fin 5), orth.act z w0 = w0 → z ∉ S5SylF → ∀ g : orth.W, g ≠ 1 → g ≠ w0 →
    (∀ d ∈ S5SylF, orth.act d g = g ∨ orth.act d g = g * w0) → orth.act z g = g →
    ∀ d ∈ S5SylF, orth.act d g = g := by
  decide +kernel

end Finite

section Algebra

theorem mem_oTwoRes_sup_of_alt {F Q : Subgroup G} {θ : ↥F →* Perm (Fin 5)}
    (hθs : Function.Surjective θ) (hk : ∀ x : ↥F, θ x = 1 ↔ (x : G) ∈ Q) {f : G}
    (hf : f ∈ F) (hA : θ ⟨f, hf⟩ ∈ alternatingGroup (Fin 5)) : f ∈ oTwoRes F ⊔ Q := by
  have hthree : ∀ τ : Perm (Fin 5), τ.IsThreeCycle →
      ∃ o : G, o ∈ F ∧ (∃ m : ℕ, Odd m ∧ o ^ m = 1) ∧ ∃ ho : o ∈ F, θ ⟨o, ho⟩ = τ := by
    intro τ hτ
    obtain ⟨g, rfl⟩ := hθs τ
    have hg : IsOfFinOrder (g : G) := (isOfFinOrder_of_finite g.1)
    obtain ⟨j, m', hm', hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
    have hτ3 : θ g ^ 3 = 1 := by
      rw [← pow_orderOf_eq_one (θ g), hτ.orderOf]
    refine ⟨(g : G) ^ (4 ^ j), F.pow_mem g.2 _, ⟨m', hm', ?_⟩, F.pow_mem g.2 _, ?_⟩
    · rw [← pow_mul]
      have : 4 ^ j * m' = 2 ^ j * m' * 2 ^ j := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring
      rw [this, pow_mul, ← hm, pow_orderOf_eq_one, one_pow]
    · show θ (g ^ 4 ^ j) = θ g
      rw [map_pow]
      have h4 : ∀ t : ℕ, θ g ^ (4 ^ t) = θ g := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          rw [pow_succ, pow_mul, ih]
          have : θ g ^ 4 = θ g := by
            rw [show 4 = 3 + 1 by norm_num, pow_add, hτ3, one_mul, pow_one]
          exact this
      exact h4 j
  have hA5 : alternatingGroup (Fin 5) ≤ ((oTwoRes F).subgroupOf F).map θ := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro τ hτ
    obtain ⟨o, hoF, hodd, ho, hθo⟩ := hthree τ hτ
    exact ⟨⟨o, hoF⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨hoF, hodd⟩), hθo⟩
  obtain ⟨o, hoO, hoθ⟩ := hA5 hA
  have hoF : (o : G) ∈ oTwoRes F := Subgroup.mem_subgroupOf.mp hoO
  have hcf : f * (o : G)⁻¹ ∈ Q := by
    have h1 : θ (⟨f, hf⟩ * o⁻¹) = 1 := by rw [map_mul, map_inv, hoθ]; simp
    have := (hk (⟨f, hf⟩ * o⁻¹)).mp h1
    simpa using this
  have : f = (f * (o : G)⁻¹) * (o : G) := by group
  rw [sup_comm, this]
  exact Subgroup.mul_mem_sup hcf hoF


omit [Finite G] in
theorem conj_eq_of_mem_centralizer {R : Subgroup G} {k r : G}
    (hk : k ∈ Subgroup.centralizer (R : Set G)) (hr : r ∈ R) : k * r * k⁻¹ = r := by
  have := Subgroup.mem_centralizer_iff.mp hk r hr
  rw [mul_inv_eq_iff_eq_mul, this]

section SecLemmas

variable {M5 : Model 5} {K L X : Subgroup G} [(L.subgroupOf X).Normal]
  {Ψ : ↥K →* Perm (Fin 5)} {β : M5.W →* ↥X ⧸ L.subgroupOf X}

omit [Finite G] in
theorem _root_.CFSG.Quasithin.F53Mod.SecData.act_eq_of_comm (h : SecData M5 K L X Ψ β) {k : G} (hk : k ∈ K) {u₀ : M5.W}
    {x : ↥X} (hx : β u₀ = QuotientGroup.mk x) (hc : k * (x : G) * k⁻¹ = x) :
    M5.act (Ψ ⟨k, hk⟩) u₀ = u₀ := by
  obtain ⟨hkx, h1⟩ := h.equiv ⟨k, hk⟩ u₀ x hx
  apply h.inj
  rw [h1, hx]
  congr 1
  exact Subtype.ext hc

omit [Finite G] in
theorem _root_.CFSG.Quasithin.F53Mod.SecData.exists_comm_elt (h : SecData M5 K L X Ψ β) {A : Subgroup G} {b : Perm (Fin 5)}
    (hb : b ∈ (A.subgroupOf K).map Ψ) (u₀ : M5.W) :
    ∃ r : G, r ∈ ⁅A, X⁆ ∧ ∃ hr : r ∈ X,
      β (M5.act b u₀ * u₀⁻¹) = QuotientGroup.mk ⟨r, hr⟩ := by
  obtain ⟨a', ha', rfl⟩ := hb
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β u₀)
  obtain ⟨hax, h1⟩ := h.beta_comm a'.2 hx.symm
  exact ⟨_, Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha') x.2, hax, h1⟩

end SecLemmas

end Algebra

section ModelFinal

open Equiv

theorem tabF2_orth_finish {w0 : orth.W} (hw0 : w0 ≠ 1) (hfix : ∀ d ∈ S5SylF, orth.act d w0 = w0)
    {z : Perm (Fin 5)} (hz : orth.act z w0 = w0) (hzS : z ∉ S5SylF) {b : Perm (Fin 5)}
    (hbS : b ∈ S5SylF ∧ (b ∈ S5ThatF ∨ (b * b = 1 ∧ Perm.sign b ≠ 1))) {u0 : orth.W}
    {d : Perm (Fin 5)} (hd : d ∈ S5SylF)
    (hne : orth.act d (orth.act b u0 * u0⁻¹) ≠ orth.act b u0 * u0⁻¹)
    (hzg : orth.act z (orth.act b u0 * u0⁻¹) = orth.act b u0 * u0⁻¹) : False := by
  have hg1 : orth.act b u0 * u0⁻¹ ≠ 1 := fun h => hne (by rw [h, map_one])
  have hgw : orth.act b u0 * u0⁻¹ ≠ w0 := fun h => hne (by rw [h]; exact hfix d hd)
  exact hne (tabF2_orth_S4 w0 hw0 hfix z hz hzS _ hg1 hgw
    (tabF2_orth_inv w0 hw0 hfix b hbS.1 hbS.2 u0) hzg d hd)

theorem tabF2_model_final (M5 : Model 5) {B : Subgroup (Perm (Fin 5))}
    (hcase : (M5 = nat ∧ B = S5T) ∨
        (M5 = orth ∧ ∃ t : Perm (Fin 5), t.IsSwap ∧ t ∈ S5Syl ∧ B = Subgroup.zpowers t) ∨
        (M5 = orth ∧ B = S5That))
    (w0 : M5.W) (hw0 : w0 ≠ 1) (hfix : ∀ d ∈ S5Syl, M5.act d w0 = w0)
    (z : Perm (Fin 5)) (hz : M5.act z w0 = w0) (hzS : z ∉ S5Syl)
    (hzB : ∀ b ∈ B, ∀ u : M5.W, M5.act z (M5.act b u * u⁻¹) = M5.act b u * u⁻¹) : False := by
  obtain ⟨b, hb, u0, d, hd, hne⟩ := witness_of_cases M5 hcase
  have hsub : ∀ x ∈ S5ThatF, x ∈ S5SylF := by decide +kernel
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, t, ht, htS, rfl⟩ | ⟨rfl, rfl⟩
  · exact hzS ((mem_S5Syl_iff z).mpr (tabF2_nat_fix w0 hw0
      (fun d hd => hfix d ((mem_S5Syl_iff d).mpr hd)) z hz))
  all_goals
    have hfix' : ∀ d ∈ S5SylF, orth.act d w0 = w0 := fun d hd => hfix d ((mem_S5Syl_iff d).mpr hd)
    have hzS' : z ∉ S5SylF := fun h => hzS ((mem_S5Syl_iff z).mpr h)
    have hd' : d ∈ S5SylF := (mem_S5Syl_iff d).mp hd
  · obtain ⟨h1, h2, h3⟩ := (isSwap_iff t).mp ht
    have hb' : b = 1 ∨ b = t := by
      obtain ⟨k, hk, hkb⟩ := (mem_zpowers_iff_of_pow_eq_one (m := 2) h2 (by norm_num)).mp hb
      interval_cases k
      · left; simpa using hkb.symm
      · right; simpa using hkb.symm
    have hbS : b ∈ S5SylF ∧ (b ∈ S5ThatF ∨ (b * b = 1 ∧ Perm.sign b ≠ 1)) := by
      rcases hb' with rfl | rfl
      · exact ⟨by decide +kernel, Or.inl (by decide +kernel)⟩
      · exact ⟨(mem_S5Syl_iff _).mp htS, Or.inr ⟨by simpa [pow_two] using h2, h3⟩⟩
    exact tabF2_orth_finish hw0 hfix' hz hzS' hbS hd' hne (hzB b hb u0)
  · have hbT : b ∈ S5ThatF := (mem_S5That_iff b).mp hb
    exact tabF2_orth_finish hw0 hfix' hz hzS' ⟨hsub b hbT, Or.inl hbT⟩ hd' hne (hzB b hb u0)

end ModelFinal


section OffenderMap

theorem offender_cases_map (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h113a : Hss113aAt H M)
    {α β α' : Geo H M} (hc : IsCritData α β α') (hv : vtype α = true)
    (hn : ¬ Zv β ≤ centerOf (stab β)) {u δ μ : Geo H M} (hcp : IsCritPair₁ u δ)
    (hne : ⁅Zv u, Zv δ⁆ ≠ ⊥) (hδu : Zv δ ≤ stab u) (hδμ : Zv δ ≤ stab μ) (hδQ : ¬ Zv δ ≤ Qv u)
    (V : VuModule u μ) :
    (V.M5 = nat ∧ ((Zv δ).subgroupOf (stab u)).map V.Ψ = S5T) ∨
      (V.M5 = orth ∧ ∃ t : Perm (Fin 5), t.IsSwap ∧ t ∈ S5Syl ∧
        ((Zv δ).subgroupOf (stab u)).map V.Ψ = Subgroup.zpowers t) ∨
      (V.M5 = orth ∧ ((Zv δ).subgroupOf (stab u)).map V.Ψ = S5That) := by
  have hLX : Nu u ≤ Zv u := inf_le_left
  have hBS : ((Zv δ).subgroupOf (stab u)).map V.Ψ ≤ S5Syl := by
    rw [← V.sylow]
    refine Subgroup.map_mono ?_
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨x.2, hδμ hx⟩
  have hbot : ((Zv δ).subgroupOf (stab u)).map V.Ψ ≠ ⊥ := by
    intro h
    obtain ⟨z, hz, hzQ⟩ := IsConcreteLE.not_le_iff_exists.mp hδQ
    have hmem : V.Ψ ⟨z, hδu hz⟩ ∈ ((Zv δ).subgroupOf (stab u)).map V.Ψ :=
      ⟨⟨z, hδu hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hzQ ((V.ker _).mp hmem)
  have hexp : ∀ x ∈ ((Zv δ).subgroupOf (stab u)).map V.Ψ, x * x = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have hz2 : (z : G) ^ 2 = 1 :=
      isElemAbelian_pow_eq_one (isElemAbelian_Zv hA δ) (Subgroup.mem_subgroupOf.mp hz)
    rw [← map_mul]
    have : z * z = 1 := Subtype.ext (by simpa [pow_two] using hz2)
    rw [this, map_one]
  have hoff : (fixW V.M5 (((Zv δ).subgroupOf (stab u)).map V.Ψ)).index ≤
      Nat.card (((Zv δ).subgroupOf (stab u)).map V.Ψ) := by
    have := V.norm
    have h1 := V.secData.relIndex_fixSecIn hLX hδu
    have hle : Zv u ⊓ Subgroup.centralizer (Zv δ : Set G) ≤ fixSecIn (Zv δ) (Nu u) (Zv u) := by
      intro x hx
      refine Subgroup.subset_closure ⟨hx.1, fun a ha => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hx.2 a ha
      rw [this]
      simp
    have h2 : (fixW V.M5 (((Zv δ).subgroupOf (stab u)).map V.Ψ)).index ≤
        (Zv u ⊓ Subgroup.centralizer (Zv δ : Set G)).relIndex (Zv u) := by
      rw [← h1]
      exact Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
    refine h2.trans (le_of_eq ?_)
    rw [F1a_relIndex hA h27 h113a hc hv hn hcp hne, card_map_subgroupOf_eq V.Ψ V.ker hδu,
      Subgroup.inf_relIndex_left]
  exact (offender_cases_syl V.M5 V.isModel hBS hbot hexp hoff).2

end OffenderMap

section Assembly

variable {α β α' u c c' : Geo H M} {y : ↥(H ⊔ M)}

theorem Zv_le_stab_self' (hA : F53Amalgam H M S) (δ : Geo H M) : Zv δ ≤ stab δ :=
  (Zv_le_Qv hA δ).trans (pCoreOf_le 2 (stab δ))

theorem Qv_le_centralizer_of_le_Zv (hA : F53Amalgam H M S) {δ : Geo H M} {R : Subgroup G}
    (h : R ≤ Zv δ) : Qv δ ≤ Subgroup.centralizer (R : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA δ (h hr)).2 q hq).symm

theorem StepFPts.R_le_Zv (hA : F53Amalgam H M S) (h28 : Hss28At H M) (h113a : Hss113aAt H M)
    (hc : IsCritData α β α') (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hb2 : 2 ≤ bMin H M) (P : StepFPts α β α' u c c' y) :
    ⁅Zv α, Zv α'⁆ ≤ Zv α ∧ ⁅Zv α, Zv α'⁆ ≤ Zv α' ∧ ⁅Zv α, Zv α'⁆ ≤ Zv u := by
  obtain ⟨hZα'α, hZαα'⟩ := Zv_le_stab_pair hA hc hcomm
  refine ⟨commutator_le_left_of_le_normalizer (hZα'α.trans (stab_le_normalizer_Zv hA α)), ?_, ?_⟩
  · rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer (hZαα'.trans (stab_le_normalizer_Zv hA α'))
  · obtain ⟨hcp', hne'⟩ := isCritPair₁_symm_of_comm_ne hA (⟨hc.not_le, hc.dist_eq⟩ : IsCritPair₁ α α')
      hcomm
    have h1 := (comm_eq_line hA h28 h113a hb2 P.α'_type P.u_crit.bAt_eq hcp' hne' P.u_crit).1
    have h2 := Lv_le_Zv_inf hA h28 h113a hb2 P.α'_type P.u_crit.bAt_eq hcp' hne' P.u_crit.adj
    rw [Subgroup.commutator_comm, h1]
    exact h2.trans inf_le_right

theorem StepFPts.cent_facts (hA : F53Amalgam H M S) (h28 : Hss28At H M) (h113a : Hss113aAt H M)
    (hc : IsCritData α β α') (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hb2 : 2 ≤ bMin H M) (P : StepFPts α β α' u c c' y) :
    Qv u ≤ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) ∧
    stab u ⊓ stab α' ≤ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) ∧
    Zv c ≤ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) := by
  obtain ⟨hRα, hRα', hRu⟩ := P.R_le_Zv hA h28 h113a hc hcomm hb2
  refine ⟨Qv_le_centralizer_of_le_Zv hA hRu, ?_, ?_⟩
  · have h := h28 (by omega) α' u P.u_crit.adj P.u_crit.bAt_eq
    rw [inf_comm, ← h]
    exact sup_le (Qv_le_centralizer_of_le_Zv hA hRα') (Qv_le_centralizer_of_le_Zv hA hRu)
  · exact (Zv_le_Qv_of_mem_nbrs (mem_nbrs_symm' P.c_nbr) hb2).trans
      (Qv_le_centralizer_of_le_Zv hA hRα)


theorem StepFPts.R_not_le_Nu (hA : F53Amalgam H M S) (h28 : Hss28At H M) (h113a : Hss113aAt H M)
    (hc : IsCritData α β α') (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hb2 : 2 ≤ bMin H M) (P : StepFPts α β α' u c c' y) (V : VuModule u α')
    (hRnot : ¬ ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)) : ¬ ⁅Zv α, Zv α'⁆ ≤ Nu u := by
  intro hRN
  apply hRnot
  obtain ⟨-, -, hRu⟩ := P.R_le_Zv hA h28 h113a hc hcomm hb2
  obtain ⟨hQu, hD, -⟩ := P.cent_facts hA h28 h113a hc hcomm hb2
  have hRstab : ⁅Zv α, Zv α'⁆ ≤ stab u := hRu.trans (Zv_le_stab_self' hA u)
  have hall : stab u ≤ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨k, hk, hkΨ⟩ : ∃ k ∈ ((stab u ⊓ stab α').subgroupOf (stab u)),
        V.Ψ k = Equiv.swap 0 2 := by
      have h : Equiv.swap (0 : Fin 5) 2 ∈ S5Syl := (mem_S5Syl_iff _).mpr (by decide +kernel)
      rw [← V.sylow] at h
      obtain ⟨k, hk, hkΨ⟩ := h
      exact ⟨k, hk, hkΨ⟩
    have hkC : (k : G) ∈ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) :=
      hD (Subgroup.mem_subgroupOf.mp hk)
    have hO : oTwoRes (stab u) ≤ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact ((Subgroup.mem_centralizer_iff.mp (hRN hr).2) x hx).symm
    have hev : ∀ f : ↥(stab u), V.Ψ f ∈ alternatingGroup (Fin 5) →
        (f : G) ∈ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) := by
      intro f hf
      have := mem_oTwoRes_sup_of_alt V.surj V.ker f.2 hf
      exact (sup_le hO hQu) this
    by_cases hev' : V.Ψ ⟨g, hg⟩ ∈ alternatingGroup (Fin 5)
    · exact hev _ hev'
    · have h1 := hev (⟨g, hg⟩ * k⁻¹) (by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hkΨ, Equiv.Perm.sign_mul,
          Equiv.Perm.sign_inv, Equiv.Perm.sign_swap (by decide)]
        rw [Equiv.Perm.mem_alternatingGroup] at hev'
        rcases Int.units_eq_one_or (Equiv.Perm.sign (V.Ψ ⟨g, hg⟩)) with h | h
        · exact absurd h hev'
        · rw [h]; rfl)
      have h2 := Subgroup.mul_mem _ h1 hkC
      simpa using h2
  refine le_inf hRstab ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (Subgroup.mem_centralizer_iff.mp (hall hg) x hx).symm


theorem stepF_D2 (hA : F53Amalgam H M S) (h27 : Hss27At H M) (h28 : Hss28At H M)
    (h113a : Hss113aAt H M) (hc : IsCritData α β α') (hv : vtype α = true)
    (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb4 : 4 ≤ bMin H M)
    (hn : ¬ Zv β ≤ centerOf (stab β)) (P : StepFPts α β α' u c c' y) (V : VuModule u α')
    (hRnot : ¬ ⁅Zv α, Zv α'⁆ ≤ centerOf (stab u)) : False := by
  have hb2 : 2 ≤ bMin H M := by omega
  obtain ⟨hRα, hRα', hRu⟩ := P.R_le_Zv hA h28 h113a hc hcomm hb2
  obtain ⟨hQu, hD, hZc⟩ := P.cent_facts hA h28 h113a hc hcomm hb2
  have hRN := P.R_not_le_Nu hA h28 h113a hc hcomm hb2 V hRnot
  obtain ⟨r0, hr0R, hr0N⟩ := IsConcreteLE.not_le_iff_exists.mp hRN
  have hr0u : r0 ∈ Zv u := hRu hr0R
  have := V.norm
  obtain ⟨w0, hw0⟩ := V.secData.surj (QuotientGroup.mk (⟨r0, hr0u⟩ : ↥(Zv u)))
  have hw0ne : w0 ≠ 1 := by
    intro h
    rw [h, map_one] at hw0
    exact hr0N (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hw0.symm))
  have hw0D : ∀ d ∈ S5Syl, V.M5.act d w0 = w0 := by
    intro d hd
    rw [← V.sylow] at hd
    obtain ⟨k, hk, rfl⟩ := hd
    exact V.secData.act_eq_of_comm k.2 hw0
      (conj_eq_of_mem_centralizer (hD (Subgroup.mem_subgroupOf.mp hk)) hr0R)
  obtain ⟨xc, hxcZ, hxcn⟩ := IsConcreteLE.not_le_iff_exists.mp P.c_not_le
  have hxcu : xc ∈ stab u := (P.Zc_le_stab_u hA).1 hxcZ
  have hzw0 : V.M5.act (V.Ψ ⟨xc, hxcu⟩) w0 = w0 :=
    V.secData.act_eq_of_comm hxcu hw0 (conj_eq_of_mem_centralizer (hZc hxcZ) hr0R)
  have hzS : V.Ψ ⟨xc, hxcu⟩ ∉ S5Syl := by
    intro h
    rw [← V.sylow] at h
    obtain ⟨k, hk, hkΨ⟩ := h
    have h1 : V.Ψ (⟨xc, hxcu⟩ * k⁻¹) = 1 := by rw [map_mul, map_inv, hkΨ, mul_inv_cancel]
    have h2 : xc * (k : G)⁻¹ ∈ Qv u := by simpa using (V.ker _).mp h1
    have hQ : Qv u ≤ stab α' := Qv_le_stab_of_mem_nbrs hA (mem_nbrs_symm' P.u_crit.adj)
    have h3 : (k : G) ∈ stab α' := (Subgroup.mem_subgroupOf.mp hk).2
    apply hxcn
    have := (stab α').mul_mem (hQ h2) h3
    simpa using this
  have hZcQ : Zv c ≤ Qv β := P.Zc_le_Qβ hA hb4 hc
  have hR₁ : Qv β ≤ Subgroup.centralizer ((⁅Zv β, Zv c'⁆ : Subgroup G) : Set G) :=
    Qv_le_centralizer_of_le_Zv hA (P.R₁_le.trans inf_le_left)
  obtain ⟨hcpu, hneu⟩ := P.uStar hA
  have hcases := offender_cases_map hA h27 h113a hc hv hn hcpu hneu (P.star_le_stab_u hA)
    P.star_le_stab_α' P.star_pair.1 V
  refine tabF2_model_final V.M5 hcases w0 hw0ne hw0D _ hzw0 hzS ?_
  intro b hb u₀
  obtain ⟨r, hr, hrX, hβ⟩ := V.secData.exists_comm_elt hb u₀
  rw [P.star_comm] at hr
  exact V.secData.act_eq_of_comm hxcu hβ
    (conj_eq_of_mem_centralizer (hR₁ (hZcQ hxcZ)) hr)

end Assembly

end F53.Stellmacher
end CFSG.Quasithin
