module

public import CFSG.Milestones.ASVolI.F45.Engine
public import CFSG.Milestones.ASVolI.F45.BNSix
public import CFSG.Quasithin.Recognition.F4Apart

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF CFSG.Quasithin.F7

@[expose] def burnsideF45_C6Body (p : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E)
    (u v : (incl M₁ M₂).Γ) : Prop :=
  Qu p Gp (incl M₁ M₂) u ≤ oPPrime p (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) ∧
  (∀ w ∈ CosetGeom.nbrs u, ∀ q ∈ Qu p Gp (incl M₁ M₂) u, q • w = w) ∧
  (∀ w₁ ∈ CosetGeom.nbrs u \ {v}, ∀ w₂ ∈ CosetGeom.nbrs u \ {v},
    ∃ g ∈ oPPrime p (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v), g • w₁ = w₂) ∧
  (∀ g ∈ oPPrime p (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v), ∀ w ∈ CosetGeom.nbrs u \ {v},
    g • w = w → g ∈ Qu p Gp (incl M₁ M₂) u) ∧
  Nat.card ↥(CosetGeom.nbrs u \ {v}) =
    qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (CosetGeom.vtype u)

section Generic

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF45_pCoreOf_le_sylow [Finite E] (hp : p.Prime)
    {H P S : Subgroup E} (hS : IsSylowOf p S H) (hSP : S ≤ P) (hPH : P ≤ H) :
    pCoreOf p P ≤ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSH, hSp, hSidx⟩ := hS
  have h1 : IsPGroup p (S.subgroupOf P) := hSp.comap_subtype
  have hdvd : S.relIndex P ∣ S.relIndex H :=
    ⟨P.relIndex H, (Subgroup.relIndex_mul_relIndex S P H hSP hPH).symm⟩
  have h2 : ¬ p ∣ (S.subgroupOf P).index := fun h => hSidx (h.trans hdvd)
  let T : Sylow p ↥P := h1.toSylow h2
  have hcore : CFSG.pCore p ↥P ≤ (T : Subgroup ↥P) := by
    haveI : (CFSG.pCore p ↥P).Normal := CFSG.LieType.BorelTits.pCore_normal p
    exact (CFSG.LieType.BorelTits.pCore_isPGroup p).le_sylow_of_normal T
  have h3 : (T : Subgroup ↥P) = S.subgroupOf P := rfl
  rw [h3] at hcore
  have := Subgroup.map_mono (f := P.subtype) hcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hSP] at this

theorem burnsideF45_pCoreOf_le_other [Finite E] (hp : p.Prime)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    pCoreOf p (Gp ⊓ M₁) ≤ M₂ ∧ pCoreOf p (Gp ⊓ M₂) ≤ M₁ := by
  obtain ⟨S, hS, hB⟩ := hP.1
  have hSB : S ≤ Gp ⊓ (M₁ ⊓ M₂) := by
    rw [hB]; exact le_inf hS.1 Subgroup.le_normalizer
  refine ⟨?_, ?_⟩
  · have hSP : S ≤ Gp ⊓ M₁ := hSB.trans (inf_le_inf_left _ inf_le_left)
    exact (burnsideF45_pCoreOf_le_sylow hp hS hSP inf_le_left).trans
      (hSB.trans (inf_le_right.trans inf_le_right))
  · have hSP : S ≤ Gp ⊓ M₂ := hSB.trans (inf_le_inf_left _ inf_le_right)
    exact (burnsideF45_pCoreOf_le_sylow hp hS hSP inf_le_left).trans
      (hSB.trans (inf_le_right.trans inf_le_left))

theorem burnsideF45_Qbar_le_stv_nbr (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    {u w : (incl M₁ M₂).Γ} (huw : (incl M₁ M₂).graph.Adj u w) :
    (burnsideF45_setting hyp hp hm).Qbar u ≤ stv (incl M₁ M₂) w := by
  haveI : Finite E := hyp.finite
  set S := burnsideF45_setting hyp hp hm with hS
  have hcore := burnsideF45_pCoreOf_le_other hp hP
  have hxl : S.Qbar (incl M₁ M₂).xv ≤ stv (incl M₁ M₂) (incl M₁ M₂).lv := fun x hx =>
    (burnsideF45_mem_stv_lv_iff' x).2 (hcore.1 ((burnsideF45_mem_Qbar_xv hyp hp hm x).1 hx))
  have hlx : S.Qbar (incl M₁ M₂).lv ≤ stv (incl M₁ M₂) (incl M₁ M₂).xv := fun x hx =>
    (burnsideF45_mem_stv_xv_iff x).2 (hcore.2 ((burnsideF45_mem_Qbar_lv hyp hp hm x).1 hx))
  have hbase : ∀ (b : Bool) (w : (incl M₁ M₂).Γ),
      (incl M₁ M₂).graph.Adj ((incl M₁ M₂).baseVert b) w →
      S.Qbar ((incl M₁ M₂).baseVert b) ≤ stv (incl M₁ M₂) w := by
    intro b w hw
    have hother : S.Qbar ((incl M₁ M₂).baseVert b) ≤
        stv (incl M₁ M₂) ((incl M₁ M₂).baseVert (!b)) := by
      cases b
      · exact hxl
      · exact hlx
    have hadj0 : (incl M₁ M₂).graph.Adj ((incl M₁ M₂).baseVert b)
        ((incl M₁ M₂).baseVert (!b)) := by
      cases b
      · exact CosetGeom.adj_γ₀_γ₁
      · exact CosetGeom.adj_γ₀_γ₁.symm
    obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq hadj0 hw
    have hgx : g ∈ stv (incl M₁ M₂) ((incl M₁ M₂).baseVert b) :=
      MulAction.mem_stabilizer_iff.mpr hg1
    rw [← hg2, stv_smul]
    have := conjSub_mono g hother
    rwa [S.conjSub_Qbar hgx] at this
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert (incl M₁ M₂) u
  have hadj : (incl M₁ M₂).graph.Adj ((incl M₁ M₂).baseVert (CosetGeom.vtype u)) (g⁻¹ • w) := by
    have := (CosetGeom.smul_adj g⁻¹).mpr huw
    rwa [show g⁻¹ • u = (incl M₁ M₂).baseVert (CosetGeom.vtype u) from
      inv_smul_eq_iff.mpr hg.symm] at this
  have h1 := conjSub_mono g (hbase _ _ hadj)
  rw [← S.Qbar_smul, ← stv_smul, hg, smul_inv_smul] at h1
  exact h1

theorem burnsideF45_oPPrime_map_le {G G' : Type} [Group G] [Group G'] (hp : p.Prime)
    (φ : G →* G') (H : Subgroup G) : (oPPrime p H).map φ ≤ oPPrime p (H.map φ) := by
  unfold oPPrime
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨x, ⟨hxH, k, hk⟩, rfl⟩
  refine ⟨⟨x, hxH, rfl⟩, ?_⟩
  have h1 : orderOf (φ x) ∣ p ^ k := hk ▸ orderOf_map_dvd φ x
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h1
  exact ⟨j, hj⟩

theorem burnsideF45_C6_abe (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    {u v : (incl M₁ M₂).Γ} (huv : (incl M₁ M₂).graph.Adj u v) :
    Qu p Gp (incl M₁ M₂) u ≤ oPPrime p (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) ∧
    (∀ w ∈ CosetGeom.nbrs u, ∀ q ∈ Qu p Gp (incl M₁ M₂) u, q • w = w) ∧
    Nat.card ↥(CosetGeom.nbrs u \ {v}) =
      qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (CosetGeom.vtype u) := by
  haveI : Finite E := hyp.finite
  have hQ : Qu p Gp (incl M₁ M₂) u = (burnsideF45_setting hyp hp hm).Qbar u :=
    burnsideF45_Qu_eq_Qbar hyp hp hm u
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ]
    intro x hx
    have hxu : x ∈ stv (incl M₁ M₂) u := (burnsideF45_setting hyp hp hm).Qbar_le_stv u hx
    have hxv : x ∈ stv (incl M₁ M₂) v := burnsideF45_Qbar_le_stv_nbr hyp hp hm hP huv hx
    haveI : Fact p.Prime := ⟨hp⟩
    have hpg : IsPGroup p ((burnsideF45_setting hyp hp hm).Qbar u) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup p _
    obtain ⟨k, hk⟩ := hpg ⟨x, hx⟩
    have hk' : x ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk')
    exact Subgroup.subset_closure ⟨⟨hxu, hxv⟩, j, hj⟩
  · intro w hw q hq
    rw [hQ] at hq
    exact MulAction.mem_stabilizer_iff.mp (burnsideF45_Qbar_le_stv_nbr hyp hp hm hP hw hq)
  · haveI : Finite (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 :=
      Finite.of_injective _ (incl_faithful M₁ M₂).1
    have hcard := card_nbrs (c := incl M₁ M₂) (incl_faithful M₁ M₂) u
    have hfin : (CosetGeom.nbrs u).Finite := by
      rw [← Set.finite_coe_iff]
      exact Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
    have hv : v ∈ CosetGeom.nbrs u := huv
    rw [Nat.card_coe_set_eq] at hcard ⊢
    rw [Set.ncard_diff_singleton_of_mem hv, hcard]
    cases hb : CosetGeom.vtype u <;> rfl

end Generic

section Transport

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

@[expose] def burnsideF45_C6cd (p : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E)
    (u v : (incl M₁ M₂).Γ) : Prop :=
  (∀ w₁ ∈ CosetGeom.nbrs u \ {v}, ∀ w₂ ∈ CosetGeom.nbrs u \ {v},
    ∃ g ∈ oPPrime p (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v), g • w₁ = w₂) ∧
  (∀ g ∈ oPPrime p (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v), ∀ w ∈ CosetGeom.nbrs u \ {v},
    g • w = w → g ∈ Qu p Gp (incl M₁ M₂) u)

theorem burnsideF45_oPPrime_conj_le {G : Type} [Group G] (hp : p.Prime) (g : G) (H : Subgroup G)
    {x : G} (hx : x ∈ oPPrime p H) : g * x * g⁻¹ ∈ oPPrime p (conjSub g H) := by
  have h := burnsideF45_oPPrime_map_le hp (MulAut.conj g).toMonoidHom H
  exact h ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem burnsideF45_C6cd_smul (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (g : (incl M₁ M₂).G0) {u v : (incl M₁ M₂).Γ} (h : burnsideF45_C6cd p Gp M₁ M₂ u v) :
    burnsideF45_C6cd p Gp M₁ M₂ (g • u) (g • v) := by
  have hstv : stv (incl M₁ M₂) (g • u) ⊓ stv (incl M₁ M₂) (g • v) =
      conjSub g (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) := by
    rw [stv_smul, stv_smul, conjSub_inf]
  have hnbr : ∀ {a w : (incl M₁ M₂).Γ}, w ∈ CosetGeom.nbrs (g • a) ↔ g⁻¹ • w ∈ CosetGeom.nbrs a := by
    intro a w
    show (incl M₁ M₂).graph.Adj (g • a) w ↔ (incl M₁ M₂).graph.Adj a (g⁻¹ • w)
    rw [← CosetGeom.smul_adj g⁻¹, inv_smul_smul]
  have hmem : ∀ {w : (incl M₁ M₂).Γ}, w ∈ CosetGeom.nbrs (g • u) \ {g • v} →
      g⁻¹ • w ∈ CosetGeom.nbrs u \ {v} := by
    intro w ⟨hw1, hw2⟩
    refine ⟨hnbr.1 hw1, fun h' => hw2 ?_⟩
    have h'' : g⁻¹ • w = v := h'
    show w = g • v
    rw [← h'', smul_inv_smul]
  refine ⟨fun w₁ hw₁ w₂ hw₂ => ?_, fun x hx w hw hxw => ?_⟩
  · obtain ⟨y, hy, hyw⟩ := h.1 _ (hmem hw₁) _ (hmem hw₂)
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · rw [hstv]
      exact burnsideF45_oPPrime_conj_le hp g _ hy
    · rw [mul_smul, mul_smul, hyw, smul_inv_smul]
  · have hy : g⁻¹ * x * g⁻¹⁻¹ ∈ oPPrime p (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) := by
      have := burnsideF45_oPPrime_conj_le hp g⁻¹ _ (hstv ▸ hx)
      rwa [conjSub_conjSub_inv] at this
    have hyw : (g⁻¹ * x * g⁻¹⁻¹) • (g⁻¹ • w) = g⁻¹ • w := by
      rw [inv_inv, mul_smul, mul_smul, smul_inv_smul, hxw]
    have hQ := h.2 _ hy _ (hmem hw) hyw
    rw [burnsideF45_Qu_eq_Qbar hyp hp hm] at hQ ⊢
    rw [(burnsideF45_setting hyp hp hm).Qbar_smul]
    rw [mem_conjSub]
    simpa [mul_assoc] using hQ

theorem burnsideF45_C6cd_of_base (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hx : burnsideF45_C6cd p Gp M₁ M₂ (incl M₁ M₂).xv (incl M₁ M₂).lv)
    (hl : burnsideF45_C6cd p Gp M₁ M₂ (incl M₁ M₂).lv (incl M₁ M₂).xv)
    {u v : (incl M₁ M₂).Γ} (huv : (incl M₁ M₂).graph.Adj u v) :
    burnsideF45_C6cd p Gp M₁ M₂ u v := by
  obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge huv
  · rw [← hg.1, ← hg.2]
    exact burnsideF45_C6cd_smul hyp hp hm g hx
  · rw [← hg.1, ← hg.2]
    exact burnsideF45_C6cd_smul hyp hp hm g hl

theorem burnsideF45_C6_of_base (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (hx : burnsideF45_C6cd p Gp M₁ M₂ (incl M₁ M₂).xv (incl M₁ M₂).lv)
    (hl : burnsideF45_C6cd p Gp M₁ M₂ (incl M₁ M₂).lv (incl M₁ M₂).xv)
    {u v : (incl M₁ M₂).Γ} (huv : (incl M₁ M₂).graph.Adj u v) :
    burnsideF45_C6Body p Gp M₁ M₂ u v := by
  obtain ⟨ha, hb, he⟩ := burnsideF45_C6_abe hyp hp hm hP huv
  obtain ⟨hc, hd⟩ := burnsideF45_C6cd_of_base hyp hp hm hx hl huv
  exact ⟨ha, hb, hc, hd, he⟩

end Transport

section Model

open CFSG.Quasithin.H13.F431

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

noncomputable def burnsideF45_eIso (hyp : HypF_4_4 κ p f Gp M₁ M₂) : (incl M₁ M₂).G0 ≃* E :=
  MulEquiv.ofBijective (toE (incl M₁ M₂)) (burnsideF45_toE_bijective hyp.gen)

noncomputable def burnsideF45_Phi (hyp : HypF_4_4 κ p f Gp M₁ M₂) {X : Type} [Group X]
    (θ : X ≃* ↥Gp) : X →* (incl M₁ M₂).G0 :=
  (burnsideF45_eIso hyp).symm.toMonoidHom.comp (Gp.subtype.comp θ.toMonoidHom)

theorem burnsideF45_eIso_Phi (hyp : HypF_4_4 κ p f Gp M₁ M₂) {X : Type} [Group X]
    (θ : X ≃* ↥Gp) (y : X) : burnsideF45_eIso hyp (burnsideF45_Phi hyp θ y) = ((θ y : ↥Gp) : E) := by
  simp [burnsideF45_Phi]

theorem burnsideF45_xdatum_of_model (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) {X : Type} [Group X] {V : Type} [MulAction X V] {ΓM : SimpleGraph V}
    (θ : X ≃* ↥Gp) {v₁ v₂ : V}
    (hstab1 : ∀ y : X, ((θ y : ↥Gp) : E) ∈ M₁ ↔ y • v₁ = v₁)
    (hstab2 : ∀ y : X, ((θ y : ↥Gp) : E) ∈ M₂ ↔ y • v₂ = v₂)
    (hdisj : ∀ y z : X, y • v₁ ≠ z • v₂)
    (hnoadj1 : ∀ y z : X, ¬ ΓM.Adj (y • v₁) (z • v₁))
    (hnoadj2 : ∀ y z : X, ¬ ΓM.Adj (y • v₂) (z • v₂))
    (hadj : ΓM.Adj v₁ v₂) :
    F45.XDatum (burnsideF45_setting hyp hp hm) (burnsideF45_Phi hyp θ) ΓM v₁ v₂ := by
  set e := burnsideF45_eIso hyp
  have hΦ : ∀ y : X, e (burnsideF45_Phi hyp θ y) = ((θ y : ↥Gp) : E) :=
    burnsideF45_eIso_Phi hyp θ
  have hstabx : ∀ g : (incl M₁ M₂).G0, g • (incl M₁ M₂).xv = (incl M₁ M₂).xv ↔ e g ∈ M₁ :=
    fun g => (MulAction.mem_stabilizer_iff.symm).trans (burnsideF45_mem_stv_xv_iff g)
  have hstabl : ∀ g : (incl M₁ M₂).G0, g • (incl M₁ M₂).lv = (incl M₁ M₂).lv ↔ e g ∈ M₂ :=
    fun g => (MulAction.mem_stabilizer_iff.symm).trans (burnsideF45_mem_stv_lv_iff' g)
  refine ⟨?_, ?_, ?_, ?_, ?_, hdisj, hnoadj1, hnoadj2, hadj⟩
  · intro a b hab
    apply θ.injective
    apply Subtype.ext
    have := congrArg e hab
    rwa [hΦ, hΦ] at this
  · ext x
    constructor
    · intro hx
      refine ⟨θ.symm ⟨e x, hx⟩, ?_⟩
      apply e.injective
      rw [hΦ]
      simp
    · rintro ⟨y, rfl⟩
      show e (burnsideF45_Phi hyp θ y) ∈ Gp
      rw [hΦ]
      exact (θ y).2
  · intro g
    obtain ⟨n, hn, h, hh, hgnh⟩ := hyp.split (e g)
    refine ⟨θ.symm ⟨n, hn⟩, e.symm h, ?_, ?_, ?_⟩
    · rw [hstabx]
      simpa using hh.1
    · rw [hstabl]
      simpa using hh.2
    · apply e.injective
      rw [map_mul, hΦ, hgnh]
      simp
  · intro y
    rw [hstabx, hΦ]
    exact hstab1 y
  · intro y
    rw [hstabl, hΦ]
    exact hstab2 y

theorem burnsideF45_C6cd_base_of_model (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (hGp : Gp = ⊤) {X : Type} [Group X] {V : Type} [MulAction X V]
    {ΓM : SimpleGraph V} [GraphAction X ΓM] (θ : X ≃* ↥Gp) {v₁ v₂ : V}
    (hstab1 : ∀ y : X, ((θ y : ↥Gp) : E) ∈ M₁ ↔ y • v₁ = v₁)
    (hstab2 : ∀ y : X, ((θ y : ↥Gp) : E) ∈ M₂ ↔ y • v₂ = v₂)
    (hdisj : ∀ y z : X, y • v₁ ≠ z • v₂)
    (hnoadj1 : ∀ y z : X, ¬ ΓM.Adj (y • v₁) (z • v₁))
    (hnoadj2 : ∀ y z : X, ¬ ΓM.Adj (y • v₂) (z • v₂))
    (hadj : ΓM.Adj v₁ v₂) (hpoly : IsGenPolygon ΓM κ.m)
    (hn1 : 3 ≤ Nat.card (ΓM.neighborSet v₁)) (hn2 : 3 ≤ Nat.card (ΓM.neighborSet v₂))
    (MB₁ : F45.ModelBase ΓM κ.m v₁ (pCoreOf p (MulAction.stabilizer X v₁)))
    (MB₂ : F45.ModelBase ΓM κ.m v₂ (pCoreOf p (MulAction.stabilizer X v₂)))
    (hc₁ : ∀ w₁ w₂, ΓM.Adj v₁ w₁ → w₁ ≠ v₂ → ΓM.Adj v₁ w₂ → w₂ ≠ v₂ →
      ∃ y ∈ oPPrime p (MulAction.stabilizer X v₁ ⊓ MulAction.stabilizer X v₂), y • w₁ = w₂)
    (hd₁ : ∀ y ∈ oPPrime p (MulAction.stabilizer X v₁ ⊓ MulAction.stabilizer X v₂),
      ∀ w, ΓM.Adj v₁ w → w ≠ v₂ → y • w = w → y ∈ pCoreOf p (MulAction.stabilizer X v₁))
    (hc₂ : ∀ w₁ w₂, ΓM.Adj v₂ w₁ → w₁ ≠ v₁ → ΓM.Adj v₂ w₂ → w₂ ≠ v₁ →
      ∃ y ∈ oPPrime p (MulAction.stabilizer X v₂ ⊓ MulAction.stabilizer X v₁), y • w₁ = w₂)
    (hd₂ : ∀ y ∈ oPPrime p (MulAction.stabilizer X v₂ ⊓ MulAction.stabilizer X v₁),
      ∀ w, ΓM.Adj v₂ w → w ≠ v₁ → y • w = w → y ∈ pCoreOf p (MulAction.stabilizer X v₂)) :
    burnsideF45_C6cd p Gp M₁ M₂ (incl M₁ M₂).xv (incl M₁ M₂).lv ∧
      burnsideF45_C6cd p Gp M₁ M₂ (incl M₁ M₂).lv (incl M₁ M₂).xv := by
  set S := burnsideF45_setting hyp hp hm with hS
  set Φ := burnsideF45_Phi hyp θ with hΦdef
  have D := burnsideF45_xdatum_of_model hyp hp hm θ hstab1 hstab2 hdisj hnoadj1 hnoadj2 hadj
  have f₁ := MB₁.flag hn1 hadj
  have f₂ := MB₂.flag hn2 hadj.symm
  obtain ⟨e, he1, he2, heq, hadjE⟩ := D.exists_equiv (F45.cov_of_flags hpoly.connected f₁ f₂) f₁
  have hsurj : Function.Surjective Φ := by
    intro g
    have hg : g ∈ S.N := by
      show burnsideF45_eIso hyp g ∈ Gp
      have h0 : burnsideF45_eIso hyp g ∈ (⊤ : Subgroup E) := Subgroup.mem_top _
      rwa [← hGp] at h0
    rw [D.N_eq] at hg
    exact hg
  let Ψ : X ≃* (incl M₁ M₂).G0 := MulEquiv.ofBijective Φ ⟨D.inj, hsurj⟩
  have hΨ : ∀ y, Ψ y = Φ y := fun _ => rfl
  have hst₁ : ∀ y : X, Φ y ∈ stv (incl M₁ M₂) (incl M₁ M₂).xv ↔ y ∈ MulAction.stabilizer X v₁ :=
    fun y => (MulAction.mem_stabilizer_iff).trans ((D.stab1 y).trans MulAction.mem_stabilizer_iff.symm)
  have hst₂ : ∀ y : X, Φ y ∈ stv (incl M₁ M₂) (incl M₁ M₂).lv ↔ y ∈ MulAction.stabilizer X v₂ :=
    fun y => (MulAction.mem_stabilizer_iff).trans ((D.stab2 y).trans MulAction.mem_stabilizer_iff.symm)
  have hmapInf : ∀ (A₁ A₂ : Subgroup X) (B₁ B₂ : Subgroup (incl M₁ M₂).G0),
      (∀ y, Φ y ∈ B₁ ↔ y ∈ A₁) → (∀ y, Φ y ∈ B₂ ↔ y ∈ A₂) →
      (A₁ ⊓ A₂).map Ψ.toMonoidHom = B₁ ⊓ B₂ := by
    intro A₁ A₂ B₁ B₂ h₁ h₂
    ext g
    obtain ⟨y, rfl⟩ := hsurj g
    rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf]
    have : Ψ.symm (Φ y) = y := by rw [← hΨ, MulEquiv.symm_apply_apply]
    rw [this, h₁, h₂]
  have hQ₁ : S.Qbar (incl M₁ M₂).xv = (pCoreOf p (MulAction.stabilizer X v₁)).map Φ :=
    D.qbar_eq _ (MulAction.stabilizer X v₁) _ (fun y => (hst₁ y).symm) rfl
  have hQ₂ : S.Qbar (incl M₁ M₂).lv = (pCoreOf p (MulAction.stabilizer X v₂)).map Φ :=
    D.qbar_eq _ (MulAction.stabilizer X v₂) _ (fun y => (hst₂ y).symm) rfl
  have step : ∀ (a b : (incl M₁ M₂).Γ) (va vb : V) (Aa Ab : Subgroup X),
      e a = va → e b = vb →
      (∀ y, Φ y ∈ stv (incl M₁ M₂) a ↔ y ∈ Aa) → (∀ y, Φ y ∈ stv (incl M₁ M₂) b ↔ y ∈ Ab) →
      Aa = MulAction.stabilizer X va →
      S.Qbar a = (pCoreOf p Aa).map Φ →
      (∀ w₁ w₂, ΓM.Adj va w₁ → w₁ ≠ vb → ΓM.Adj va w₂ → w₂ ≠ vb →
        ∃ y ∈ oPPrime p (Aa ⊓ Ab), y • w₁ = w₂) →
      (∀ y ∈ oPPrime p (Aa ⊓ Ab), ∀ w, ΓM.Adj va w → w ≠ vb → y • w = w →
        y ∈ pCoreOf p Aa) →
      burnsideF45_C6cd p Gp M₁ M₂ a b := by
    intro a b va vb Aa Ab hea heb hsa hsb hAa hQa hc hd
    have hmap := hmapInf Aa Ab _ _ hsa hsb
    refine ⟨fun w₁ hw₁ w₂ hw₂ => ?_, fun x hx w hw hxw => ?_⟩
    · have h₁ : ΓM.Adj va (e w₁) := by rw [← hea]; exact (hadjE _ _).mp hw₁.1
      have h₂ : ΓM.Adj va (e w₂) := by rw [← hea]; exact (hadjE _ _).mp hw₂.1
      have h₁' : e w₁ ≠ vb := fun h => hw₁.2 (e.injective (h.trans heb.symm))
      have h₂' : e w₂ ≠ vb := fun h => hw₂.2 (e.injective (h.trans heb.symm))
      obtain ⟨y, hy, hyw⟩ := hc _ _ h₁ h₁' h₂ h₂'
      refine ⟨Φ y, ?_, ?_⟩
      · have h1 := burnsideF45_oPPrime_map_le hp Ψ.toMonoidHom (Aa ⊓ Ab) ⟨y, hy, rfl⟩
        rw [hmap] at h1
        exact h1
      · apply e.injective
        rw [heq, hyw]
    · obtain ⟨y, rfl⟩ := hsurj x
      have hy : y ∈ oPPrime p (Aa ⊓ Ab) := by
        have h1 := burnsideF45_oPPrime_map_le hp Ψ.symm.toMonoidHom
          (stv (incl M₁ M₂) a ⊓ stv (incl M₁ M₂) b) ⟨Φ y, hx, rfl⟩
        have h2 : (stv (incl M₁ M₂) a ⊓ stv (incl M₁ M₂) b).map Ψ.symm.toMonoidHom = Aa ⊓ Ab := by
          rw [← hmap, Subgroup.map_map]
          simp
        rw [h2] at h1
        have : Ψ.symm.toMonoidHom (Φ y) = y := by
          show Ψ.symm (Φ y) = y
          rw [← hΨ, MulEquiv.symm_apply_apply]
        rwa [this] at h1
      have h₁ : ΓM.Adj va (e w) := by rw [← hea]; exact (hadjE _ _).mp hw.1
      have h₁' : e w ≠ vb := fun h => hw.2 (e.injective (h.trans heb.symm))
      have hyw : y • e w = e w := by rw [← heq, hxw]
      have hyQ := hd y hy (e w) h₁ h₁' hyw
      rw [burnsideF45_Qu_eq_Qbar hyp hp hm, hQa]
      exact ⟨y, hyQ, rfl⟩
  refine ⟨step _ _ v₁ v₂ _ _ he1 he2 hst₁ hst₂ rfl hQ₁ hc₁ hd₁, ?_⟩
  exact step _ _ v₂ v₁ _ _ he2 he1 hst₂ hst₁ rfl hQ₂ hc₂ hd₂

end Model

section System

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF45_C6_of_system (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (hGp : Gp = ⊤)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    {X : Type} [Group X] (θ₀ : X ≃* ↥Gp) {n : ℕ} (D : RankTwoSystem X n) (hn : n = κ.m)
    (hU : IsSylowOf p D.U ⊤) :
    ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body p Gp M₁ M₂ u v := by
  haveI : Finite E := hyp.finite
  haveI : Finite X := Finite.of_injective _ θ₀.injective
  obtain ⟨g, b, hgb⟩ := burnsideF45_conj_parabolics hp hP θ₀ D hU
  subst hn
  let θ : X ≃* ↥Gp := (MulAut.conj g).symm.trans θ₀
  have hθ : ∀ y : X, θ y = θ₀ (g⁻¹ * y * g) := fun y => by
    show θ₀ ((MulAut.conj g).symm y) = _
    simp [MulAut.conj_symm_apply]
  have hst : ∀ (i : Bool) (y : X), y ∈ P D i ↔ y • v D i = v D i := fun i y => by
    rw [← stabilizer_v_eq D i, MulAction.mem_stabilizer_iff]
  have hdisj : ∀ (i : Bool) (y z : X), y • v D i ≠ z • v D (!i) := by
    intro i y z
    cases i
    · exact fun h => disj D z y h.symm
    · exact disj D y z
  have hnoadj : ∀ (i : Bool) (y z : X), ¬ (Γ D).Adj (y • v D i) (z • v D i) := by
    intro i
    cases i
    · exact noadj_false D
    · exact noadj_true D
  have hadj : ∀ i : Bool, (Γ D).Adj (v D i) (v D (!i)) := by
    intro i
    cases i
    · exact (adj_v D).symm
    · exact adj_v D
  have hc₂ : ∀ w₁ w₂ : V D, (Γ D).Adj (v D (!b)) w₁ → w₁ ≠ v D b →
      (Γ D).Adj (v D (!b)) w₂ → w₂ ≠ v D b →
      ∃ y ∈ oPPrime p (MulAction.stabilizer X (v D (!b)) ⊓ MulAction.stabilizer X (v D b)),
        y • w₁ = w₂ := by
    intro w₁ w₂ h₁ h₁' h₂ h₂'
    have h := burnsideF45_bn_six_trans D hp hU (!b) h₁ (by rwa [Bool.not_not]) h₂
      (by rwa [Bool.not_not])
    rwa [Bool.not_not] at h
  have hd₂ : ∀ y ∈ oPPrime p (MulAction.stabilizer X (v D (!b)) ⊓ MulAction.stabilizer X (v D b)),
      ∀ w : V D, (Γ D).Adj (v D (!b)) w → w ≠ v D b → y • w = w →
        y ∈ pCoreOf p (MulAction.stabilizer X (v D (!b))) := by
    intro y hy w hw hw' hyw
    refine burnsideF45_bn_six_free D hp hU (!b) ?_ hw (by rwa [Bool.not_not]) hyw
    rwa [Bool.not_not]
  obtain ⟨hx, hl⟩ := burnsideF45_C6cd_base_of_model hyp hp hm hGp θ (v₁ := v D b)
    (v₂ := v D (!b))
    (fun y => by rw [hθ]; exact ((hgb y).1).trans (hst b y))
    (fun y => by rw [hθ]; exact ((hgb y).2).trans (hst (!b) y))
    (hdisj b) (hnoadj b) (hnoadj (!b)) (hadj b) (isGenPolygon D)
    (three_le_card_neighborSet D (v D b)) (three_le_card_neighborSet D (v D (!b)))
    (burnsideF45_bn_modelBase D hp hU b) (burnsideF45_bn_modelBase D hp hU (!b))
    (fun w₁ w₂ h₁ h₁' h₂ h₂' => burnsideF45_bn_six_trans D hp hU b h₁ h₁' h₂ h₂')
    (fun y hy w hw hw' hyw => burnsideF45_bn_six_free D hp hU b hy hw hw' hyw)
    hc₂ hd₂
  exact fun u v huv => burnsideF45_C6_of_base hyp hp hm hP hx hl huv

end System

end CFSG.ASVolI
