module

import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F429.Base

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {G : Type} [Group G]

theorem burnsideF429b_oTwoRes_mono {A B : Subgroup G} (h : A ≤ B) : oTwoRes A ≤ oTwoRes B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem burnsideF429b_oTwoRes_map {N : Type} [Group N] (θ : N →* G) (hθ : Function.Injective θ)
    (X : Subgroup N) : oTwoRes (X.map θ) = (oTwoRes X).map θ := by
  unfold oTwoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, m, hm, hxm⟩
    exact ⟨x, ⟨hx, m, hm, hθ (by rw [map_pow, hxm, map_one])⟩, rfl⟩
  · rintro ⟨x, ⟨hx, m, hm, hxm⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, m, hm, by rw [← map_pow, hxm, map_one]⟩

theorem burnsideF429b_mem_oTwoRes_of_pow_three {P : Subgroup G} {g : G} (hg : g ∈ P)
    (h3 : g ^ 3 = 1) : g ∈ oTwoRes P :=
  Subgroup.subset_closure ⟨hg, 3, ⟨1, by norm_num⟩, h3⟩

theorem burnsideF429b_comm_mem {P S : Subgroup G} {g t : G} (hg : g ∈ P) (h3 : g ^ 3 = 1)
    (htP : t ∈ P) (ht : t ∈ S) (hgt : g * t * g⁻¹ ∈ S) :
    g * t * g⁻¹ * t⁻¹ ∈ S ⊓ oTwoRes P := by
  refine ⟨S.mul_mem hgt (S.inv_mem ht), ?_⟩
  have h1 := burnsideF429b_mem_oTwoRes_of_pow_three hg h3
  have h2 := burnsideF429b_mem_oTwoRes_of_pow_three
    (P.mul_mem (P.mul_mem htP hg) (P.inv_mem htP))
    (show (t * g * t⁻¹) ^ 3 = 1 by rw [conj_pow, h3, mul_one, mul_inv_cancel])
  have e : g * t * g⁻¹ * t⁻¹ = g * (t * g * t⁻¹)⁻¹ := by group
  rw [e]
  exact (oTwoRes P).mul_mem h1 ((oTwoRes P).inv_mem h2)

theorem burnsideF429b_oTwoRes_le_of_index_two {H : Subgroup G} (hH : H.index = 2)
    (X : Subgroup G) : oTwoRes X ≤ H := by
  refine (Subgroup.closure_le H).2 ?_
  rintro x ⟨-, m, ⟨k, rfl⟩, hxm⟩
  have e : x * (x ^ k * x ^ k) = 1 := by
    rw [← pow_add, ← pow_succ', ← two_mul]
    exact hxm
  have e2 : x = (x ^ k)⁻¹ * (x ^ k)⁻¹ := by
    rw [← mul_inv_rev]
    exact eq_inv_of_mul_eq_one_left e
  rw [e2]
  exact Subgroup.mul_self_mem_of_index_two hH _

theorem burnsideF429b_map_conj_comp {N : Type} [Group N] (ψ : N →* G) (h : N) (X : Subgroup N) :
    (X.map (MulAut.conj h).toMonoidHom).map (ψ.comp (MulAut.conj h⁻¹).toMonoidHom) = X.map ψ := by
  have e : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom = MonoidHom.id N := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [Subgroup.map_map, MonoidHom.comp_assoc, e, MonoidHom.comp_id]

theorem burnsideF429b_inf_sup_inf {Gp M₁ M₂ : Subgroup G} (hN : Gp.Normal) (hgen : M₁ ⊔ M₂ = ⊤)
    (hsplit : ∀ e : G, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h) : (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂) = Gp := by
  have hHG : (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂) ≤ Gp := sup_le inf_le_left inf_le_left
  have hnorm : ∀ m ∈ M₁ ⊓ M₂, ∀ x ∈ (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂),
      m * x * m⁻¹ ∈ (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂) := by
    intro m hm x hx
    have hle : ((Gp ⊓ M₁) ⊔ (Gp ⊓ M₂)).map (MulAut.conj m).toMonoidHom ≤
        (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂) := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨y, ⟨hyG, hy⟩, rfl⟩
        exact ⟨hN.conj_mem y hyG m, M₁.mul_mem (M₁.mul_mem hm.1 hy) (M₁.inv_mem hm.1)⟩
      · rintro _ ⟨y, ⟨hyG, hy⟩, rfl⟩
        exact ⟨hN.conj_mem y hyG m, M₂.mul_mem (M₂.mul_mem hm.2 hy) (M₂.inv_mem hm.2)⟩
    exact hle ⟨x, hx, rfl⟩
  have key : ∀ e : G, ∃ x ∈ (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂), ∃ m ∈ M₁ ⊓ M₂, e = x * m := by
    intro e
    have he : e ∈ Subgroup.closure ((M₁ : Set G) ∪ M₂) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hgen]
      exact Subgroup.mem_top e
    induction he using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨n, hn, m, hm, rfl⟩ := hsplit y
      have hn' : n = (n * m) * m⁻¹ := by group
      rcases hy with hy | hy
      · refine ⟨n, Subgroup.mem_sup_left ⟨hn, ?_⟩, m, hm, rfl⟩
        rw [hn']
        exact M₁.mul_mem hy (M₁.inv_mem hm.1)
      · refine ⟨n, Subgroup.mem_sup_right ⟨hn, ?_⟩, m, hm, rfl⟩
        rw [hn']
        exact M₂.mul_mem hy (M₂.inv_mem hm.2)
    | one => exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by group⟩
    | mul y z _ _ ihy ihz =>
      obtain ⟨x₁, hx₁, m₁, hm₁, rfl⟩ := ihy
      obtain ⟨x₂, hx₂, m₂, hm₂, rfl⟩ := ihz
      exact ⟨x₁ * (m₁ * x₂ * m₁⁻¹), Subgroup.mul_mem _ hx₁ (hnorm m₁ hm₁ x₂ hx₂), m₁ * m₂,
        Subgroup.mul_mem _ hm₁ hm₂, by group⟩
    | inv y _ ih =>
      obtain ⟨x, hx, m, hm, rfl⟩ := ih
      exact ⟨m⁻¹ * x⁻¹ * m⁻¹⁻¹, hnorm m⁻¹ (Subgroup.inv_mem _ hm) x⁻¹ (Subgroup.inv_mem _ hx),
        m⁻¹, Subgroup.inv_mem _ hm, by group⟩
  refine le_antisymm hHG fun g hg => ?_
  obtain ⟨x, hx, m, hm, rfl⟩ := key g
  have hmG : m ∈ Gp := by
    have e : m = x⁻¹ * (x * m) := by group
    rw [e]
    exact Gp.mul_mem (Gp.inv_mem (hHG hx)) hg
  exact Subgroup.mul_mem _ hx (Subgroup.mem_sup_left ⟨hmG, hm.1⟩)

theorem burnsideF429b_c8sbar_of_inj {Gp M₁ M₂ : Subgroup G} {C : Type} [Group C] (φ : C →* G)
    (hφ : Function.Injective φ) {P₁ P₂ B : Subgroup C} (hG : Gp = (⊤ : Subgroup C).map φ)
    (h1 : Gp ⊓ M₁ = P₁.map φ) (h2 : Gp ⊓ M₂ = P₂.map φ) (hB : Gp ⊓ (M₁ ⊓ M₂) = B.map φ)
    (hB2 : IsPGroup 2 B) (ha : B ⊓ oTwoRes ⊤ ≤ (B ⊓ oTwoRes P₁) ⊔ (B ⊓ oTwoRes P₂))
    (hb : (B ⊓ oTwoRes ⊤).relIndex B ∣ 2) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp ≤
        ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)) ⊔ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂)) ∧
      (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp).relIndex (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∣ 2 := by
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = B.map φ := by
    rw [hB]
    exact burnsideF4gG2TwoInv_pCoreOf_eq_self (hB2.map φ)
  have hO : oTwoRes Gp = (oTwoRes ⊤).map φ := by
    rw [hG]
    exact burnsideF429b_oTwoRes_map φ hφ ⊤
  have hSO : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp = (B ⊓ oTwoRes ⊤).map φ := by
    rw [hS, hO, Subgroup.map_inf _ _ _ hφ]
  have hBM : B.map φ ≤ M₁ ⊓ M₂ := by
    rw [← hB]
    exact inf_le_right
  have hpiece : ∀ {M : Subgroup G} {P : Subgroup C}, Gp ⊓ M = P.map φ →
      (B ⊓ oTwoRes P).map φ ≤ (M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M) := by
    intro M P hM
    rw [Subgroup.map_inf _ _ _ hφ, hM, burnsideF429b_oTwoRes_map φ hφ]
    exact inf_le_inf_right _ hBM
  refine ⟨?_, ?_⟩
  · rw [hSO]
    refine (Subgroup.map_mono ha).trans ?_
    rw [Subgroup.map_sup]
    exact sup_le_sup (hpiece h1) (hpiece h2)
  · rw [hSO, hS, Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact hb

end Generic

section G2TwoChk

open CFSG.Quasithin.F6 CFSG.Quasithin.H13.F431.G2Two

@[expose] def burnsideF429b_xTab : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (1, 11, 17), (2, 22, 11), (3, 7, 16), (4, 19, 7), (6, 16, 19), (7, 4, 3),
    (8, 26, 12), (9, 17, 22), (11, 2, 1), (12, 8, 26), (16, 3, 6), (17, 1, 9), (19, 6, 4),
    (22, 9, 2), (26, 12, 8)]

theorem burnsideF429b_xTab_chk : ∀ t ∈ burnsideF429b_xTab, t.1 < 64 ∧ t.2.1 < 64 ∧ t.2.2 < 64 ∧
    compL (compL (g22gl 3) (u33XL t.2.1)) (g22gil 3) = u33XL t.2.2 ∧
    Tab.mulT t.2.2 (Tab.invT t.2.1) = t.1 := by
  decide +kernel

theorem burnsideF429b_yTab_chk : (5 : ℕ) < 64 ∧ (8 : ℕ) < 64 ∧
    compL (compL (g22gl 4) (u33XL 5)) (g22gil 4) = u33XL 8 ∧ Tab.mulT 8 (Tab.invT 5) = 18 := by
  decide +kernel

theorem burnsideF429b_cover_chk : ∀ i < 32, (∃ t ∈ burnsideF429b_xTab, t.1 = i) ∨
    (∃ t ∈ burnsideF429b_xTab, Tab.mulT t.1 18 = i) := by
  decide +kernel

end G2TwoChk

section G2TwoModel

open CFSG.Quasithin.F6 CFSG.Quasithin.H13.F431.G2Two

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

include hk2

theorem burnsideF429b_G2two_S_inf_range :
    (F6.G22Shape.lat h2 hk2).S ⊓ (g2HomC h2).range ≤ Model.TpSub h2 hk2 := by
  rintro g ⟨hgS, hgR⟩
  obtain ⟨i, hi, rfl⟩ := (F6.G22Shape.mem_S_iff h2 hk2).1 hgS
  by_cases hi32 : i < 32
  · exact Model.sEl_mem_TpSub h2 hk2 hi32
  · exfalso
    apply (g2IndexTwoData h2 hk2).rho_not_mem
    have e : F6.G22Perm.sEl h2 i = g2RhoC h2 * g2HomC h2 (u33Tel u33GenPG (i - 32)) := by
      rw [F6.G22Perm.sEl, if_neg hi32]
    have e2 : g2RhoC h2 = F6.G22Perm.sEl h2 i * (g2HomC h2 (u33Tel u33GenPG (i - 32)))⁻¹ := by
      rw [e, mul_inv_cancel_right]
    rw [e2]
    exact Subgroup.mul_mem _ hgR (Subgroup.inv_mem _ ⟨_, rfl⟩)

theorem burnsideF429b_G2two_Tp_le :
    Model.TpSub h2 hk2 ≤ ((F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes (F6.G22Shape.lat h2 hk2).P₂) ⊔
      ((F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes (F6.G22Shape.lat h2 hk2).P₁) := by
  have hx3 : g2HomC h2 (u33GenPG 3) ^ 3 = 1 := by rw [← map_pow, u33_orders.2.2.2.1, map_one]
  have hy3 : g2HomC h2 (u33GenPG 4) ^ 3 = 1 := by rw [← map_pow, u33_orders.2.2.2.2, map_one]
  have hZ : ∀ t ∈ burnsideF429b_xTab, F6.G22Perm.sEl h2 t.1 ∈
      ((F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes (F6.G22Shape.lat h2 hk2).P₂) ⊔
        ((F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes (F6.G22Shape.lat h2 hk2).P₁) := by
    intro t ht
    obtain ⟨-, hj, hl, hconj, hz⟩ := burnsideF429b_xTab_chk t ht
    have hc := Model.conjG h2 hk2 (by norm_num) hj hl hconj
    have hmem := burnsideF429b_comm_mem (Model.x_mem h2 hk2) hx3
      ((F6.G22Shape.lat h2 hk2).S_le_P₁ (F6.G22Shape.sEl_mem_S h2 hk2 hj))
      (F6.G22Shape.sEl_mem_S h2 hk2 hj) (by rw [hc]; exact F6.G22Shape.sEl_mem_S h2 hk2 hl)
    rw [hc, Model.sEl_inv h2 hk2 hj, Model.sEl_mulT h2 hk2 hl (Tab.invT_spec _ hj).1, hz] at hmem
    exact Subgroup.mem_sup_right hmem
  have h18 : F6.G22Perm.sEl h2 18 ∈
      ((F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes (F6.G22Shape.lat h2 hk2).P₂) ⊔
        ((F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes (F6.G22Shape.lat h2 hk2).P₁) := by
    obtain ⟨hj, hl, hconj, hz⟩ := burnsideF429b_yTab_chk
    have hc := Model.conjG h2 hk2 (by norm_num) hj hl hconj
    have hmem := burnsideF429b_comm_mem (Model.y_mem h2 hk2) hy3
      ((F6.G22Shape.lat h2 hk2).S_le_P₂ (F6.G22Shape.sEl_mem_S h2 hk2 hj))
      (F6.G22Shape.sEl_mem_S h2 hk2 hj) (by rw [hc]; exact F6.G22Shape.sEl_mem_S h2 hk2 hl)
    rw [hc, Model.sEl_inv h2 hk2 hj, Model.sEl_mulT h2 hk2 hl (Tab.invT_spec _ hj).1, hz] at hmem
    exact Subgroup.mem_sup_left hmem
  intro g hg
  obtain ⟨i, hi, rfl⟩ := (Model.mem_TpSub h2 hk2).1 hg
  rcases burnsideF429b_cover_chk i hi with ⟨t, ht, hti⟩ | ⟨t, ht, hti⟩
  · rw [← hti]
    exact hZ t ht
  · rw [← hti, ← Model.sEl_mulT h2 hk2 (burnsideF429b_xTab_chk t ht).1 (by norm_num)]
    exact Subgroup.mul_mem _ (hZ t ht) h18

theorem burnsideF429b_G2two_model :
    (F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes ⊤ ≤
        ((F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes (F6.G22Shape.lat h2 hk2).P₂) ⊔
          ((F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes (F6.G22Shape.lat h2 hk2).P₁) ∧
      ((F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes ⊤).relIndex (F6.G22Shape.lat h2 hk2).S ∣ 2 := by
  have hTp := burnsideF429b_G2two_Tp_le h2 hk2
  have hle : (F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes ⊤ ≤ Model.TpSub h2 hk2 :=
    (inf_le_inf_left _ (burnsideF429b_oTwoRes_le_of_index_two
      (g2IndexTwoData h2 hk2).index_range ⊤)).trans (burnsideF429b_G2two_S_inf_range h2 hk2)
  refine ⟨hle.trans hTp, ?_⟩
  have hTO : Model.TpSub h2 hk2 ≤ (F6.G22Shape.lat h2 hk2).S ⊓ oTwoRes ⊤ :=
    hTp.trans (sup_le (inf_le_inf_left _ (burnsideF429b_oTwoRes_mono le_top))
      (inf_le_inf_left _ (burnsideF429b_oTwoRes_mono le_top)))
  refine (Subgroup.relIndex_dvd_of_le_left _ hTO).trans ?_
  have h : (Model.TpSub h2 hk2).relIndex (F6.G22Shape.lat h2 hk2).S *
      Nat.card ↥(Model.TpSub h2 hk2 ⊓ (F6.G22Shape.lat h2 hk2).S) =
        Nat.card ↥(F6.G22Shape.lat h2 hk2).S := Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.2 (Model.TpSub_le_S h2 hk2), Model.card_TpSub h2 hk2,
    F6.G22Shape.card_S h2 hk2] at h
  have h' : (Model.TpSub h2 hk2).relIndex (F6.G22Shape.lat h2 hk2).S = 2 := by omega
  rw [h']

end G2TwoModel

section G2Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2


theorem burnsideF429b_G2_chart3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .G2 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ Ψ : H13.F431.G2.C K ≃* ↥Gp,
        M₁.subgroupOf Gp = (G2Native.pointParabolic K).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (G2Native.lineParabolic K).map Ψ.toMonoidHom ∧
        (M₁ ⊓ M₂).subgroupOf Gp = (G2Native.positiveBorel K).map Ψ.toMonoidHom := by
  obtain ⟨chart, hb, hpts, hlns⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · letI := fK
    haveI := finK
    haveI : CharP K 2 := burnsideF4f_charP_of_card hd card
    let Ψ : H13.F431.G2.C K ≃* ↥Gp := (H13.F431.G2.mk K).trans marking
    have hΨ : ∀ L : Subgroup (G2Native.Parent K),
        G2Native.fullImage K marking L = L.map Ψ.toMonoidHom := by
      intro L
      unfold G2Native.fullImage G2Native.fullLocal
      rw [Subgroup.map_map]
      exact congrArg (fun φ => Subgroup.map φ L) (MonoidHom.ext fun y => rfl)
    have hsub : ∀ (X : Subgroup E) (L : Subgroup (G2Native.Parent K)),
        Gp ⊓ X = (G2Native.fullImage K marking L).map Gp.subtype →
          X.subgroupOf Gp = L.map Ψ.toMonoidHom := by
      intro X L hX
      rw [← Subgroup.inf_subgroupOf_left X Gp, hX, ← hΨ]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    exact ⟨K, fK, finK, inferInstance, card, Ψ, hsub _ _ (hpts.trans h2),
      hsub _ _ (hlns.trans h3), hsub _ _ (hb.trans h1)⟩
  all_goals exact absurd hk (by decide)

theorem burnsideF429b_c8sbar_G2two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 1 Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp ≤
        ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)) ⊔ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂)) ∧
      (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp).relIndex (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∣ 2 := by
  obtain ⟨K, fK, finK, cK, hcard, Ψ, h1, h2', hB⟩ := burnsideF429b_G2_chart3 hyp.toHypF_4_4g
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  have h2 : (2 : K) = 0 := CFSG.Quasithin.two_eq_zero_of_card_two hK
  have hk2 : ∀ c : K, c = 0 ∨ c = 1 := CFSG.Quasithin.eq_zero_or_eq_one_of_card_two hK
  have hinf : G2Native.pointParabolic K ⊓ G2Native.lineParabolic K =
      G2Native.positiveBorel K := by
    apply Subgroup.map_injective (f := Ψ.toMonoidHom) Ψ.injective
    rw [Subgroup.map_inf _ _ Ψ.toMonoidHom Ψ.injective, ← h1, ← h2', ← hB]
    exact (Subgroup.comap_inf M₁ M₂ Gp.subtype).symm
  have hsup : G2Native.pointParabolic K ⊔ G2Native.lineParabolic K = ⊤ := by
    apply Subgroup.map_injective (f := Ψ.toMonoidHom) Ψ.injective
    rw [Subgroup.map_sup, ← h1, ← h2', Subgroup.map_top_of_surjective Ψ.toMonoidHom Ψ.surjective,
      ← Subgroup.inf_subgroupOf_left M₁ Gp, ← Subgroup.inf_subgroupOf_left M₂ Gp,
      ← Subgroup.subgroupOf_sup inf_le_left inf_le_left,
      burnsideF429b_inf_sup_inf hyp.normal hyp.gen hyp.split, Subgroup.subgroupOf_self]
  obtain ⟨h, hh⟩ := burnsideF4gG2TwoInv_borel_conj hK h2 hk2
  have hP := (burnsideF4gG2TwoInv_Pc_conj hK h2 hk2 hh).1
  have hQ := burnsideF4gG2TwoInv_Qc_conj hK h2 hk2 hh hsup hinf
  have hBS : (G2Native.positiveBorel K).map (MulAut.conj h).toMonoidHom =
      (F6.G22Shape.lat h2 hk2).S := by
    ext g
    rw [Subgroup.mem_map, hh g]
    simp [MulAut.conj_apply]
  have hφ : Function.Injective
      ((Gp.subtype.comp Ψ.toMonoidHom).comp (MulAut.conj h⁻¹).toMonoidHom) :=
    (Gp.subtype_injective.comp Ψ.injective).comp (MulAut.conj h⁻¹).injective
  have hG : Gp = (⊤ : Subgroup (G2Group K)).map
      ((Gp.subtype.comp Ψ.toMonoidHom).comp (MulAut.conj h⁻¹).toMonoidHom) := by
    rw [← Subgroup.map_top_of_surjective (MulAut.conj h).toMonoidHom (MulAut.conj h).surjective,
      burnsideF429b_map_conj_comp, ← Subgroup.map_map,
      Subgroup.map_top_of_surjective Ψ.toMonoidHom Ψ.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hM1 : Gp ⊓ M₁ = (F6.G22Shape.lat h2 hk2).P₂.map
      ((Gp.subtype.comp Ψ.toMonoidHom).comp (MulAut.conj h⁻¹).toMonoidHom) := by
    rw [burnsideF429_inf_eq_map Ψ h1, ← hP, burnsideF429b_map_conj_comp]
  have hM2 : Gp ⊓ M₂ = (F6.G22Shape.lat h2 hk2).P₁.map
      ((Gp.subtype.comp Ψ.toMonoidHom).comp (MulAut.conj h⁻¹).toMonoidHom) := by
    rw [burnsideF429_inf_eq_map Ψ h2', ← hQ, burnsideF429b_map_conj_comp]
  have hM12 : Gp ⊓ (M₁ ⊓ M₂) = (F6.G22Shape.lat h2 hk2).S.map
      ((Gp.subtype.comp Ψ.toMonoidHom).comp (MulAut.conj h⁻¹).toMonoidHom) := by
    rw [burnsideF429_inf_eq_map Ψ hB, ← hBS, burnsideF429b_map_conj_comp]
  obtain ⟨ha, hb⟩ := burnsideF429b_G2two_model h2 hk2
  exact burnsideF429b_c8sbar_of_inj _ hφ hG hM1 hM2 hM12 (F6.G22Shape.lat h2 hk2).sylow.1 ha hb

end G2Two

end CFSG.ASVolI
