module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95COrth
public import CFSG.RankThree.GF2n.Stroth80.Sec53aProof
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6NbarGe
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Nat
public import CFSG.RankThree.GF2n.Stroth80.Sec92Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec95N6Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → n = 6 →
      ∃ x ∈ LB M Q B, x ∉ hc.CN t ∧
        ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t

namespace HS9

theorem comm_LB_inf_QB (hc : Ctx M Q Z B) {l x : G} (hl : l ∈ LB M Q B) (hx : x ∈ Q ⊓ QB B) :
    ⁅l, x⁆ ∈ (B ⊔ Z : Subgroup G) := by
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have h1 : ⁅y, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy hx.1
  have h2 : s * ⁅y, x⁆ * s⁻¹ ∈ Z := by
    have hsN : s ∈ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2 hs.2
    simpa using (Subgroup.mem_normalizer_iff.mp hsN _).mp h1
  have h3 : ⁅s, x⁆ ∈ B := hc.comm_QB_le_B hs.1 hx.2
  have e : ⁅s * y, x⁆ = s * ⁅y, x⁆ * s⁻¹ * ⁅s, x⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (B ⊔ Z : Subgroup G).mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left h3)

theorem bilin_orthogonal_sup_eq_inf' {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (U W : Submodule K E) :
    B.orthogonal (U ⊔ W) = B.orthogonal U ⊓ B.orthogonal W := by
  ext e
  constructor
  · intro h
    exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
      fun w hw => h w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, LinearMap.add_apply, h1 y hy, h2 z hz, add_zero]

theorem exists_trivial_on_WV6 (h34 : Stroth34Statement) (h2 : Step91OrderVQBStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) (hn6 : n = 6) :
    ∃ C : Subgroup G, C ≤ LB M Q B ∧
      (∀ l, l ∈ C ↔ l ∈ LB M Q B ∧
        ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅l, w⁆ ∈ Vt M (LB M Q B) B Z t) ∧
      C.relIndex (LB M Q B) ≤ Nat.card Z := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨K, fK, finK, chK, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ₀, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  haveI : Finite M₀.E := Module.finite_of_finite K
  set V := Vt M (LB M Q B) B Z t with hV
  set W := Wt Q V with hW
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hWQ : W ≤ Q := inf_le_left
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVW : V ≤ W := HS6.Vt_le_Wt h34 hc hs5
  have hZW : Z ≤ W := hZV.trans hVW
  have hMQ : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) x).mp hx
  have hKZ : Nat.card K = Nat.card Z := h.card
  have hq4 := hc.hyp.q4
  have hK2 : 1 < Nat.card K := by rw [hKZ]; omega
  have hE : Module.finrank K M₀.E = 2 * n := h.finrank_E hs5.width hK2
  have h35all := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hcard33 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) := h35all.2.2.2
  obtain ⟨U, hUmem⟩ := hc.exists_submodule_inf_QB hs5.width hcard33 h
  let Vsub : Submodule K M₀.E := imgSub M₀ V (fun c e he => hc.smul_mem_img_Vt h t c he)
  let Wsub : Submodule K M₀.E :=
    imgSub M₀ W (fun c e he => smul_mem_img_Wt M₀ h.reg hVQ c he)
  have hVsub_mem : ∀ e, e ∈ Vsub ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have hWsub_mem : ∀ e, e ∈ Wsub ↔ e ∈ M₀.img W := fun e => mem_imgSub
  have hB : M₀.B.Nondegenerate := modelB_nondegenerate M₀
  have hrefl : M₀.B.IsRefl := LinearMap.IsAlt.isRefl (fun e => M₀.alt e)
  have hQ : IsQuadSpace M₀.B M₀.Qf := ⟨M₀.alt, M₀.nondeg, M₀.Qf_add⟩
  have hUsing : ∀ e ∈ U, M₀.Qf e = 0 := fun e he => by
    have := (M₀.isElemAbelian_iff h.reg (inf_le_left : Q ⊓ QB B ≤ Q)).mp hc.inf_QB_elemAbelian
    exact this e ((hUmem e).mp he)
  have hUorth : ∀ e ∈ U, ∀ f ∈ U, M₀.B e f = 0 := by
    intro e he f hf
    have h1 := M₀.Qf_add e f
    rw [hUsing _ (U.add_mem he hf), hUsing e he, hUsing f hf] at h1
    linear_combination -h1
  have hUle : U ≤ M₀.B.orthogonal U := by
    intro e he f hf
    rw [Tim79.QuadModel.B_comm, hUorth e he f hf, neg_zero]
  have hUdim : Module.finrank K U = n := by
    have hUcardImg : Nat.card ↥U = Nat.card (M₀.img (Q ⊓ QB B)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => hUmem e)
    have hQcard : Nat.card ↥(Q ⊓ QB B) = Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) :=
      M₀.card_eq inf_le_left (le_inf hZQ hc.Z_le_QB.1)
    have hUcard : Nat.card ↥U = Nat.card Z ^ n := by
      rw [hUcardImg]
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hQcard, hcard33, pow_succ]; ring
    have h1 : Nat.card K ^ Module.finrank K U = Nat.card K ^ n := by
      rw [← Module.natCard_eq_pow_finrank, hUcard, hKZ]
    exact Nat.pow_right_injective hK2 h1
  have hUlag : M₀.B.orthogonal U = U := by
    refine (Submodule.eq_of_le_of_finrank_eq hUle ?_).symm
    have h1 := LinearMap.BilinForm.finrank_orthogonal hB U
    omega
  have hVdim : Module.finrank K Vsub = 4 := by
    have hVcardImg : Nat.card ↥Vsub = Nat.card (M₀.img V) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => (hVsub_mem e).symm)
    have hQcard : Nat.card ↥V = Nat.card Z * Nat.card (M₀.img V) := M₀.card_eq hVQ hZV
    have hVcard : Nat.card ↥Vsub = Nat.card Z ^ 4 := by
      rw [hVcardImg]
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hQcard, hs.card_V]; ring
    have h1 : Nat.card K ^ Module.finrank K Vsub = Nat.card K ^ 4 := by
      rw [← Module.natCard_eq_pow_finrank, hVcard, hKZ]
    exact Nat.pow_right_injective hK2 h1
  have hWorth : Wsub = M₀.B.orthogonal Vsub := by
    ext e
    rw [hWsub_mem, mem_img_Wt_iff M₀ h.reg hVQ]
    constructor
    · intro hh f hf
      rw [Tim79.QuadModel.B_comm, hh f ((hVsub_mem f).mpr hf), neg_zero]
    · intro hh f hf
      have := hh f ((hVsub_mem f).mpr hf)
      rwa [Tim79.QuadModel.B_comm, neg_eq_zero] at this
  have hWdim : Module.finrank K Wsub = 2 * n - 4 := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hB Vsub
    rw [← hWorth] at h1
    omega
  have hVsubW : Vsub ≤ Wsub := fun e he =>
    (hWsub_mem e).mpr (M₀.img_mono hVW ((hVsub_mem e).mp he))
  have hVQB : Nat.card ↥(V ⊓ QB B) = Nat.card Z ^ 4 := h2 G M Q Z B hc n t hs V rfl
  have hUVdim : Module.finrank K ↥(U ⊓ Vsub) = 3 := by
    have hsetV : V ⊓ QB B = (Q ⊓ QB B) ⊓ V := by
      ext x
      constructor
      · rintro ⟨hx, hxB⟩
        exact ⟨⟨hVQ hx, hxB⟩, hx⟩
      · rintro ⟨⟨-, hxB⟩, hx⟩
        exact ⟨hx, hxB⟩
    have hinfimg : M₀.img ((Q ⊓ QB B) ⊓ V) = M₀.img (Q ⊓ QB B) ⊓ M₀.img V :=
      quadModel_img_inf M₀ (le_inf hZQ hc.Z_le_QB.1) hZV inf_le_left hVQ
    have hset : ∀ e, e ∈ U ⊓ Vsub ↔ e ∈ M₀.img (V ⊓ QB B) := by
      intro e
      rw [Submodule.mem_inf, hUmem, hVsub_mem, hsetV]
      constructor
      · rintro ⟨he1, he2⟩
        rw [hinfimg]
        exact ⟨he1, he2⟩
      · intro he
        rw [hinfimg] at he
        exact ⟨he.1, he.2⟩
    have hcardImg : Nat.card (M₀.img (V ⊓ QB B)) = Nat.card Z ^ 3 := by
      have h1 : Nat.card ↥(V ⊓ QB B) = Nat.card Z * Nat.card (M₀.img (V ⊓ QB B)) :=
        M₀.card_eq ((inf_le_left : V ⊓ QB B ≤ _).trans hVQ) (le_inf hZV hc.Z_le_QB.1)
      rw [hVQB] at h1
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← h1]; ring
    have hUVcard : Nat.card ↥(U ⊓ Vsub) = Nat.card Z ^ 3 :=
      (Nat.card_congr (Equiv.subtypeEquivRight fun e => hset e)).trans hcardImg
    have hh2 : Nat.card ↥(U ⊓ Vsub) = Nat.card K ^ 3 := by rw [hUVcard, hKZ]
    have h1 : Nat.card K ^ Module.finrank K ↥(U ⊓ Vsub) = Nat.card K ^ 3 := by
      conv_lhs => rw [← Module.natCard_eq_pow_finrank]
      exact hh2
    exact Nat.pow_right_injective hK2 h1
  have horthsup : M₀.B.orthogonal (U ⊔ Wsub) = U ⊓ Vsub := by
    rw [bilin_orthogonal_sup_eq_inf', hUlag, hWorth,
      LinearMap.BilinForm.orthogonal_orthogonal hB hrefl Vsub]
  have hUWdim : Module.finrank K ↥(U ⊓ Wsub) = n - 1 := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq U Wsub
    have e2 := LinearMap.BilinForm.finrank_orthogonal hB (U ⊔ Wsub)
    rw [horthsup, hUVdim] at e2
    have e3 : Module.finrank K ↥(U ⊔ Wsub) ≤ Module.finrank K M₀.E := Submodule.finrank_le _
    omega
  let N : Submodule K M₀.E := (U ⊓ Wsub) ⊔ Vsub
  have hNdim : Module.finrank K N = n := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ Wsub) Vsub
    have e2 : (U ⊓ Wsub) ⊓ Vsub = U ⊓ Vsub := by
      ext e
      simp only [Submodule.mem_inf]
      constructor
      · rintro ⟨⟨a, _⟩, c⟩
        exact ⟨a, c⟩
      · rintro ⟨a, c⟩
        exact ⟨⟨a, hVsubW c⟩, c⟩
    rw [e2, hUVdim, hUWdim, hVdim] at e1
    have e1' : Module.finrank K N + 3 = (n - 1) + 4 := e1
    have : n = 6 := hn6
    omega
  have hVsing : ∀ e ∈ Vsub, M₀.Qf e = 0 := fun e he => by
    have hel := hc.Vt_isElemAbelian h35all.2.1 ht hs5.notQ
    exact (M₀.isElemAbelian_iff h.reg hVQ).mp hel e ((hVsub_mem e).mp he)
  have hF : OrthFlag M₀.B M₀.Qf Vsub N Wsub :=
    { VN := le_sup_right
      NW := sup_le inf_le_right hVsubW
      Wperp := fun w => by rw [hWorth]; exact LinearMap.BilinForm.mem_orthogonal_iff
      Nsing := by
        intro x hx
        obtain ⟨a, ha, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
        have hBva : M₀.B v a = 0 := by
          have h1 : a ∈ Wsub := (Submodule.mem_inf.mp ha).2
          rw [hWorth] at h1
          exact LinearMap.BilinForm.mem_orthogonal_iff.mp h1 v hv
        have hBav : M₀.B a v = 0 := by
          rw [Tim79.QuadModel.B_comm, hBva, neg_zero]
        have := M₀.Qf_add a v
        rw [this, hUsing a ha.1, hVsing v hv, hBav]
        simp
      Ndim := by omega
      Wdim := by
        have : n = 6 := hn6
        omega }
  set α : ↥(LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E) := φ₀.comp (Subgroup.inclusion hc.LB_le_H0) with hα
  have hαπ : ∀ (l : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((l : G) * x * (l : G)⁻¹) = α l (M₀.π x) := fun l x hx =>
    hφπ ⟨(l : G), hc.LB_le_H0 l.2⟩ x hx
  have hlR : ∀ l : ↥(LB M Q B), (l : G) ∈ Rt M (LB M Q B) t := fun l =>
    le_Rt (M := M) (LB M Q B) ht l.2
  have hiso : ∀ (l : ↥(LB M Q B)) e, M₀.Qf (α l e) = M₀.Qf e := fun l e =>
    hφiso ⟨(l : G), hc.LB_le_H0 l.2⟩ e
  have hWact : ∀ (l : ↥(LB M Q B)), ∀ w ∈ Wsub, α l w ∈ Wsub := by
    intro l w' hw
    obtain ⟨w, hwW, hwQ, rfl⟩ := (hWsub_mem _).mp hw
    have hw' : (l : G) * w * (l : G)⁻¹ ∈ W := sec9_conj_mem_Wt hc ht (hlR l) hwW
    rw [← hαπ l w hwQ]
    exact (hWsub_mem _).mpr (M₀.pi_mem_img hw' (hWQ hw'))
  have hVact : ∀ (l : ↥(LB M Q B)), ∀ v ∈ Vsub, α l v ∈ Vsub := by
    intro l v' hv
    obtain ⟨v, hvV, hvQ, rfl⟩ := (hVsub_mem _).mp hv
    have hv' : (l : G) * v * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht (hlR l)) v).mp hvV
    rw [← hαπ l v hvQ]
    exact (hVsub_mem _).mpr (M₀.pi_mem_img hv' (hVQ hv'))
  have hdict : ∀ (l : ↥(LB M Q B)) (x : G), x ∈ Q →
      ⁅(l : G), x⁆ ∈ Q ∧ M₀.π ⁅(l : G), x⁆ = α l (M₀.π x) - M₀.π x := by
    intro l x hx
    have hxQ' : (l : G) * x * (l : G)⁻¹ ∈ Q := hMQ l (hc.LB_le_M l.2) x hx
    have e : ⁅(l : G), x⁆ = ((l : G) * x * (l : G)⁻¹) * x⁻¹ := by
      simp only [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Q.mul_mem hxQ' (Q.inv_mem hx)
    · rw [e, M₀.π_mul _ hxQ' _ (Q.inv_mem hx), Tim79.QuadModel.pi_inv M₀ hx, hαπ l x hx]
      abel
  have hNV : ∀ (l : ↥(LB M Q B)), ∀ x ∈ N, α l x - x ∈ Vsub := by
    intro l x hx
    obtain ⟨a, ha, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    have hau : a ∈ U := (Submodule.mem_inf.mp ha).1
    have h1 : α l a - a ∈ Vsub := by
      obtain ⟨y, hyS, hyQ, rfl⟩ := (hUmem a).mp hau
      obtain ⟨hcQ, hπ⟩ := hdict l y hyQ
      have hcV : ⁅(l : G), y⁆ ∈ V :=
        (sup_le (hc.B_le_Vt ht) hZV) (comm_LB_inf_QB hc l.2 hyS)
      rw [← hπ]
      exact (hVsub_mem _).mpr (M₀.pi_mem_img hcV hcQ)
    have h2 : α l v - v ∈ Vsub := Vsub.sub_mem (hVact l v hv) hv
    have : α l (a + v) - (a + v) = (α l a - a) + (α l v - v) := by
      rw [map_add]
      abel
    rw [this]
    exact Vsub.add_mem h1 h2
  obtain ⟨C, hCmem, hCidx⟩ := exists_orth_subgroup hQ hF α hiso hWact hNV
  have hiff : ∀ l : ↥(LB M Q B), l ∈ C ↔ ∀ w ∈ W, ⁅(l : G), w⁆ ∈ V := by
    intro l
    rw [hCmem l]
    constructor
    · intro hl w hw
      obtain ⟨hQc, hπ⟩ := hdict l w (hWQ hw)
      have h2 := hl (M₀.π w) ((hWsub_mem _).mpr (M₀.pi_mem_img hw (hWQ hw)))
      rw [← hπ] at h2
      exact (M₀.mem_img_iff hZV hQc).mp ((hVsub_mem _).mp h2)
    · intro hl w' hw'
      obtain ⟨w, hwW, hwQ, rfl⟩ := (hWsub_mem _).mp hw'
      obtain ⟨hQc, hπ⟩ := hdict l w hwQ
      rw [← hπ]
      exact (hVsub_mem _).mpr (M₀.pi_mem_img (hl w hwW) hQc)
  refine ⟨C.map (LB M Q B).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨c, -, rfl⟩
    exact c.2
  · intro l
    constructor
    · rintro ⟨c, hcC, rfl⟩
      exact ⟨c.2, (hiff c).mp hcC⟩
    · rintro ⟨hl, hlw⟩
      exact ⟨⟨l, hl⟩, (hiff ⟨l, hl⟩).mpr hlw, rfl⟩
  · have hsub : (C.map (LB M Q B).subtype).subgroupOf (LB M Q B) = C := by
      unfold Subgroup.subgroupOf
      exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective C
    rw [Subgroup.relIndex, hsub, ← hKZ]
    exact hCidx

end HS9

theorem sec95N6_of (h34 : Stroth34Statement) (h91 : Stroth91Statement)
    (h2 : Step91OrderVQBStatement) (hA : Sec9AExistsStatement) : Sec95N6Statement := by
  intro G _ _ M Q Z B hc n t hs hn6
  obtain ⟨C, hCL, hC, hidx⟩ := HS9.exists_trivial_on_WV6 h34 h2 hs hn6
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hNW := (h91.2.1 G M Q Z B hc n t hs r hr _ _ rfl rfl).2
  have hq := HS9.relIndex_LB_CN h34 hs
  by_contra hno
  push Not at hno
  have hCN : C ≤ hc.CN t := fun x hx => by
    by_contra hxN
    obtain ⟨w, hw, hnot⟩ := hno x ((hC x).mp hx).1 hxN
    exact hnot (((hC x).mp hx).2 w hw)
  have hLN : hc.CN t ⊓ LB M Q B ≤ C := fun x hx => (hC x).mpr ⟨hx.2, hNW x hx.1⟩
  have hCeq : C = hc.CN t ⊓ LB M Q B := le_antisymm (le_inf hCN hCL) hLN
  have h1 : C.relIndex (LB M Q B) = Nat.card Z ^ 2 := by
    rw [hCeq, Subgroup.inf_relIndex_right, hq]
  have hq4 := hc.hyp.q4
  rw [h1] at hidx
  nlinarith [hidx]

end CFSG.RankThree.GF2n.Stroth80
