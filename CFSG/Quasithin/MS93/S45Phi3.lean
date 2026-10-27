module

public import CFSG.Quasithin.MS93.S45Phi2
public import CFSG.Quasithin.MS93.S45B5

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Frattini

variable {𝔾 : Type} [Group 𝔾]

theorem frattiniIn_eq_closure {V : Subgroup 𝔾} [Finite V] (hV : IsPGroup 2 V) :
    frattiniIn V =
      Subgroup.closure (((⁅V, V⁆ : Subgroup 𝔾) : Set 𝔾) ∪ {x | ∃ v ∈ V, v ^ 2 = x}) := by
  have : Fact (IsPGroup 2 ↥V) := ⟨hV⟩
  rw [frattiniIn, CFSG.frattini_eq_closure_commutator_union_powers (p := 2),
    MonoidHom.map_closure, Set.image_union]
  congr 2
  · rw [← Subgroup.coe_map, _root_.commutator_def, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, y.2, by simp⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩ ^ 2, ⟨⟨v, hv⟩, rfl⟩, by simp⟩

theorem frattiniIn_le_of {V N : Subgroup 𝔾} [Finite V] (hV : IsPGroup 2 V) (hc : ⁅V, V⁆ ≤ N)
    (hs : ∀ v ∈ V, v ^ 2 ∈ N) : frattiniIn V ≤ N := by
  rw [frattiniIn_eq_closure hV, Subgroup.closure_le]
  rintro x (hx | ⟨v, hv, rfl⟩)
  · exact hc hx
  · exact hs v hv

theorem commutator_le_frattiniIn {V : Subgroup 𝔾} [Finite V] (hV : IsPGroup 2 V) :
    ⁅V, V⁆ ≤ frattiniIn V := by
  rw [frattiniIn_eq_closure hV]
  exact fun x hx => Subgroup.subset_closure (Or.inl hx)

theorem le_normalizer_frattiniIn {K V : Subgroup 𝔾} [Finite V] (hV : IsPGroup 2 V)
    (hKV : K ≤ Subgroup.normalizer (V : Set 𝔾)) :
    K ≤ Subgroup.normalizer ((frattiniIn V : Subgroup 𝔾) : Set 𝔾) := by
  rw [frattiniIn_eq_closure hV]
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx | ⟨v, hv, rfl⟩, rfl⟩
  · refine Subgroup.subset_closure (Or.inl ?_)
    have := (le_normalizer_commutator hKV hKV) hg
    exact (Subgroup.mem_normalizer_iff.mp this x).mp hx
  · refine Subgroup.subset_closure (Or.inr ⟨g * v * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hKV hg) v).mp hv, ?_⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [sq, sq]; group

theorem conj_inv_of_mul_eq {g z : 𝔾} (h : g * z = z * g) : g * z⁻¹ * g⁻¹ = z⁻¹ := by
  rw [(show Commute g z from h).inv_right.eq, mul_inv_cancel_right]

theorem commutator_le_of_trivial_top {K X X' A Z P : Subgroup 𝔾} (hXK : ⁅X, K⁆ ≤ X')
    (hX'X : X' ≤ X) (hKA : K ≤ Subgroup.normalizer (A : Set 𝔾)) (hcov : A ≤ ⁅K, A⁆ ⊔ Z)
    (hZA : Z ≤ A) (hXZ : ∀ c ∈ X, ∀ z ∈ Z, ⁅c, z⁆ = 1)
    (hcen : ∀ c ∈ X, ∀ u ∈ A, ∀ g ∈ K ⊔ X ⊔ A, g * ⁅c, u⁆ = ⁅c, u⁆ * g)
    (hP : ⁅X', A⁆ ≤ P) : ⁅X, A⁆ ≤ P := by
  have hKs : K ≤ K ⊔ X ⊔ A := le_sup_left.trans le_sup_left
  have hXs : X ≤ K ⊔ X ⊔ A := le_sup_right.trans le_sup_left
  have hAs : A ≤ K ⊔ X ⊔ A := le_sup_right
  rw [Subgroup.commutator_le]
  intro c hc
  let S : Subgroup 𝔾 :=
    { carrier := {u | u ∈ A ∧ ⁅c, u⁆ ∈ P}
      one_mem' := ⟨A.one_mem, by rw [commutatorElement_one_right]; exact P.one_mem⟩
      mul_mem' := fun {u u'} hu hu' => ⟨A.mul_mem hu.1 hu'.1, by
        rw [S46.commutatorElement_mul_right_conj, hcen c hc u' hu'.1 u (hAs hu.1),
          mul_inv_cancel_right]
        exact P.mul_mem hu.2 hu'.2⟩
      inv_mem' := fun {u} hu => ⟨A.inv_mem hu.1, by
        have e : ⁅c, u⁻¹⁆ = u⁻¹ * ⁅c, u⁆⁻¹ * u⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e, conj_inv_of_mul_eq (hcen c hc u hu.1 u⁻¹ (hAs (A.inv_mem hu.1)))]
        exact P.inv_mem hu.2⟩ }
  have hZS : Z ≤ S := fun z hz => ⟨hZA hz, by rw [hXZ c hc z hz]; exact P.one_mem⟩
  have hKS : ⁅K, A⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro l hl u hu
    have hwA : l * u * l⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hKA hl) u).mp hu
    have hx' : ⁅l, c⁆ ∈ X' := hXK (by
      rw [Subgroup.commutator_comm]; exact Subgroup.commutator_mem_commutator hl hc)
    have hcu := hcen c hc u hu
    have hcw := hcen c hc _ hwA
    have hE1 : ⁅c, u⁆ = ⁅c, l * u * l⁻¹⁆ * ⁅⁅l, c⁆, l * u * l⁻¹⁆ := by
      calc ⁅c, u⁆ = l * ⁅c, u⁆ * l⁻¹ := by rw [hcu l (hKs hl), mul_inv_cancel_right]
        _ = ⁅l, c⁆ * ⁅c, l * u * l⁻¹⁆ * ⁅l, c⁆⁻¹ * ⁅⁅l, c⁆, l * u * l⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        _ = ⁅c, l * u * l⁻¹⁆ * ⁅⁅l, c⁆, l * u * l⁻¹⁆ := by
          rw [hcw _ (hXs (hX'X hx')), mul_inv_cancel_right]
    have hE2 : ⁅c, ⁅l, u⁆⁆ = ⁅c, l * u * l⁻¹⁆ *
        ((l * u * l⁻¹) * (u⁻¹ * ⁅c, u⁆⁻¹ * u⁻¹⁻¹) * (l * u * l⁻¹)⁻¹) := by
      simp only [commutatorElement_def]; group
    have hmem : ⁅⁅l, c⁆, l * u * l⁻¹⁆ ∈ P := hP (Subgroup.commutator_mem_commutator hx' hwA)
    have hxw : ⁅⁅l, c⁆, l * u * l⁻¹⁆⁻¹ ∈ K ⊔ X ⊔ A := by
      refine (K ⊔ X ⊔ A).inv_mem ?_
      rw [commutatorElement_def]
      exact (K ⊔ X ⊔ A).mul_mem ((K ⊔ X ⊔ A).mul_mem ((K ⊔ X ⊔ A).mul_mem (hXs (hX'X hx'))
        (hAs hwA)) ((K ⊔ X ⊔ A).inv_mem (hXs (hX'X hx')))) ((K ⊔ X ⊔ A).inv_mem (hAs hwA))
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact A.mul_mem hwA (A.inv_mem hu)
    · rw [hE2, conj_inv_of_mul_eq (hcu u⁻¹ (hAs (A.inv_mem hu))),
        conj_inv_of_mul_eq (hcu _ (hAs hwA)), hE1, mul_inv_rev, ← mul_assoc,
        (hcw _ hxw).symm, mul_assoc, mul_inv_cancel, mul_one]
      exact P.inv_mem hmem
  intro u hu
  exact (sup_le hKS hZS (hcov hu)).2

end Frattini

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem top_le_vsix (hZV : c.HZV) (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ}
    (ha : Even a) (h10 : 10 ≤ a) (haN : a + 14 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i) :
    (conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2))) ⊔
        (conjCl (stab (puAmalgam c.hyp.le) (p a))
            (Vcirc c.hyp.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2))) ≤
      conjCl (stab (puAmalgam c.hyp.le) (p a)) (whv c.hyp (p (a + 2)) (p a)) := by
  have h := c.hyp
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) le_rfl
  have e : whv h (p (a + 2)) (p (a + 2 + 2)) = whv h (p (a + 2)) (p (a + 2 - 2)) :=
    c.whv_eq_of_isGoodPath hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
  rw [show a + 2 + 2 = a + 4 by omega, show a + 2 - 2 = a by omega] at e
  have hγγ : Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)) ≤ whv h (p (a + 2)) (p a) := by
    have := c.vhat_le_whv' hZV hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 + 2 = a + 4 by omega] at this
    rwa [← e]
  have hμγ : Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) ≤ whv h (p (a + 2)) (p a) := by
    rw [← e]; exact c.vhat_le_whv_self
  have hμ'γ : Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4)) ≤ whv h (p (a + 2)) (p a) := by
    have e' : whv h (p' (a + 2)) (p' (a + 2 + 2)) = whv h (p' (a + 2)) (p' (a + 2 - 2)) :=
      c.whv_eq_of_isGoodPath hp' (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 + 2 = a + 4 by omega, show a + 2 - 2 = a by omega, hpa, hpa2] at e'
    rw [← e']; exact c.vhat_le_whv_self
  have hWhγ : whv h (p a) (p (a + 2)) ≤
      conjCl (stab (puAmalgam h.le) (p a)) (whv h (p (a + 2)) (p a)) := conjCl_mono hγγ
  exact sup_le (sup_le (conjCl_mono hμγ) hWhγ) (sup_le (conjCl_mono hμ'γ) hWhγ)

theorem isPGroup_commutator_qv_ltil {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    IsPGroup 2 ↥⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ∧
      Finite ↥⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ := by
  have h := c.hyp
  obtain ⟨ρ, hρ⟩ := exists_adj (puAmalgam h.le) δ
  have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
  have hle : ⁅Qv (puAmalgam h.le) δ, Ltil h.le L δ⁆ ≤ Qv _ ρ :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp ((ltil_le_stab h _).trans
      (stab_le_normalizer_qv _ _))).trans (qv_le_qv _ h.hyp20 hδ hρ)
  have : Finite ↥(Qv (puAmalgam h.le) ρ) := finite_qv _ h.hyp20 hρH
  exact ⟨(isPGroup_qv _ h.hyp20 hρH).to_le hle,
    Finite.of_injective _ (Subgroup.inclusion_injective hle)⟩

theorem frattiniIn_le_vcirc (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)))
    (hC1 : ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
      Hloc c.hyp.le L (p a)) :
    frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
      Vcirc c.hyp.le L (p a) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  obtain ⟨hV2, hVf⟩ := c.isPGroup_commutator_qv_ltil hα
  have hB5 := c.commutator_qv_ltil_le_top hZV hp hp' ha h34 haN hpp' hU3
  have hV6 := c.top_le_vsix hZV hp hp' ha (by omega) (by omega) hpp'
  have hDD := c.commutator_vsix_le_vhat h14 hSQ hZV hQ4 hp ha h34 haN
  set Qα := Qv (puAmalgam h.le) (p a) with hQα
  set Lt := Ltil h.le L (p a) with hLt
  set V := ⁅Qα, Lt⁆ with hV
  set U := Uloc h.le L (p a) with hU
  set H := Hloc h.le L (p a) with hH
  set Z := ZM (puAmalgam h.le) (p a) with hZ
  set Vc := Vcirc h.le L (p a) with hVc
  have hVV6 : V ≤ conjCl (stab (puAmalgam h.le) (p a)) (whv h (p (a + 2)) (p a)) :=
    hB5.trans hV6
  have hQs : Qα ≤ stab (puAmalgam h.le) (p a) := qv_le_stab _ _
  have hKQ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Qα : Set _) :=
    stab_le_normalizer_qv _ _
  have hLs : Lt ≤ stab (puAmalgam h.le) (p a) := ltil_le_stab h _
  have hKV : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (V : Set _) :=
    le_normalizer_commutator hKQ (stab_le_normalizer_ltil h _)
  have hVQ : V ≤ Qα := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hKQ)
  have hKZ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Z : Set _) :=
    stab_le_normalizer_zm _ _
  have hKVc : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Vc : Set _) :=
    c.stab_le_normalizer_vcirc _
  have hVvQ : Vv (puAmalgam h.le) (p a) ≤ Qα := c.vv_le_qv' hα
  have hUZ : U ≤ Z := uloc_le_zm h c.full hα
  have hZQ : Z ≤ Qα := zm_le_qv_of_dist_lt _ hα (by simp [c.b8])
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hUL : ⁅U, Lt⁆ = U := c.commutator_uloc_ltil hα
  have hUVc : U ≤ Vc := by
    rw [← hUL]
    exact Subgroup.commutator_mono (hUZ.trans (le_sup_right.trans (c.vhat_le_vv hα))) le_rfl
  have hVcV : Vc ≤ V := Subgroup.commutator_mono hVvQ le_rfl
  have hUV : U ≤ V := hUVc.trans hVcV
  have hHVc : H ≤ Vc := Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hKVc)
  have hUn : U ≤ Subgroup.normalizer (Zloc h.le L (p a) : Set _) :=
    (hUZ.trans (hZQ.trans hQs)).trans (c.stab_le_normalizer_of_le_centralizer hZc)
  have hVZ : Z ⊓ V ≤ U ⊔ H := by
    have e := zm_eq_uloc_sup_zloc h c.full hα
    calc Z ⊓ V = (U ⊔ Zloc h.le L (p a)) ⊓ V := by rw [hZ, e]
      _ = U ⊔ (Zloc h.le L (p a) ⊓ V) := sup_inf_eq_of_le hUV hUn
      _ ≤ U ⊔ H := sup_le_sup_left (by rw [inf_comm]; exact hC1) _
  have hVVh : (Vc ⊔ Z) ⊓ V ≤ Vc := by
    rw [sup_inf_eq_of_le hVcV (hVcV.trans (hVQ.trans (hQs.trans hKZ)))]
    exact sup_le le_rfl (hVZ.trans (sup_le hUVc hHVc))
  refine (frattiniIn_le_of hV2 (le_inf ?_ ?_) fun v hv => ⟨?_, pow_mem hv 2⟩).trans hVVh
  · exact (Subgroup.commutator_mono hVV6 hVV6).trans hDD
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp Subgroup.le_normalizer
  · exact hDD (c.sq_mem_commutator_vsix hZV hp ha h34 (by omega) (hVV6 hv))

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
