module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CSieg
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CRed
public import CFSG.RankThree.GF2n.Stroth80.Sec12LBFlag
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Nat
public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem exists_lagrangian95 {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (h34 : Stroth34Statement) (hs : Sec9Hyp hc n t) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) :
    ∃ U : Submodule K M₀.E, (∀ e, e ∈ U ↔ e ∈ M₀.img (Q ⊓ QB B)) ∧ Module.finrank K U = n ∧
      Module.finrank K M₀.E = 2 * n ∧ (∀ e ∈ U, M₀.Qf e = 0) ∧
      ∀ e, (∀ u ∈ U, M₀.B u e = 0) → e ∈ U := by
  classical
  have hs5 := hs.toSec5
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hKZ : Nat.card K = Nat.card Z := h.card
  have hq4 := hc.hyp.q4
  have hK2 : 1 < Nat.card K := by rw [hKZ]; omega
  have hE : Module.finrank K M₀.E = 2 * n := h.finrank_E hs5.width hK2
  have h35all := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hcard33 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) := h35all.2.2.2
  obtain ⟨U, hUmem⟩ := hc.exists_submodule_inf_QB hs5.width hcard33 h
  have hB : M₀.B.Nondegenerate := modelB_nondegenerate M₀
  have hrefl : M₀.B.IsRefl := LinearMap.IsAlt.isRefl (fun e => M₀.alt e)
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
  refine ⟨U, hUmem, hUdim, hE, hUsing, fun e he => ?_⟩
  rw [← hUlag]
  exact (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun u hu => he u hu

theorem Q_le_N1 {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) : Q ≤ N1 hc t :=
  le_inf sec39_Q_le_LB (hc.Q_le_CN hs.mem)

theorem relIndex_Q_N1 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) : Q.relIndex (N1 hc t) = Nat.card Z ^ (n - 3) := by
  classical
  have hs5 := hs.toSec5
  have h35 := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hcardLB : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) := h35.2.2.1
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hQN : Q ≤ N1 hc t := Q_le_N1 hs
  have hN1L : N1 hc t ≤ LB M Q B := inf_le_left
  have hrel1 : Q.relIndex (LB M Q B) = Nat.card Z ^ (n - 1) := by
    have h1 : Nat.card (Q.subgroupOf (LB M Q B)) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
    have h2 := Subgroup.card_mul_index (Q.subgroupOf (LB M Q B))
    rw [h1] at h2
    have h3 : Nat.card Q * Q.relIndex (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) := by
      rw [← hcardLB]
      exact h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
  have hN1rel : (N1 hc t).relIndex (LB M Q B) = Nat.card Z ^ 2 := by
    show (LB M Q B ⊓ hc.CN t).relIndex (LB M Q B) = _
    rw [Subgroup.inf_relIndex_left]
    exact relIndex_LB_CN h34 hs
  have hmul := Subgroup.relIndex_mul_relIndex Q (N1 hc t) (LB M Q B) hQN hN1L
  rw [hN1rel, hrel1] at hmul
  have hn3 : n - 1 = (n - 3) + 2 := by have := hs5.n_gt; omega
  rw [hn3, pow_add] at hmul
  exact Nat.eq_of_mul_eq_mul_right (by have := hc.hyp.q4; positivity) hmul

theorem A0_le_Q (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (φ₀ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ₀ m (M₀.π x))
    (hφQ : ∀ m : H0 M Z, φ₀ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ₀ m e) = M₀.Qf e)
    (hno : NoA2 Q Z (LB M Q B)) {U : Submodule K M₀.E}
    (hUmem : ∀ e, e ∈ U ↔ e ∈ M₀.img (Q ⊓ QB B)) (hUsing : ∀ e ∈ U, M₀.Qf e = 0)
    (hUperp : ∀ e, (∀ u ∈ U, M₀.B u e = 0) → e ∈ U)
    {b : M₀.E} (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0)
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {a : G} (ha : a ∈ A0 Q Z B) : a ∈ Q := by
  classical
  by_contra haQ
  have haQM : a ∈ QB B ⊓ M := by rw [hc.QB_inf_M_eq]; exact ha.1
  have haM : a ∈ M := haQM.2
  have haL : a ∈ LB M Q B := Subgroup.mem_sup_right haQM
  have haH : a ∈ H0 M Z := ⟨haM, ha.1.2⟩
  let T : M₀.E ≃ₗ[K] M₀.E := φ₀ ⟨a, haH⟩
  have hTπ : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x) := fun x hx => hφπ ⟨a, haH⟩ x hx
  have hTQ : ∀ e, M₀.Qf (T e) = M₀.Qf e := fun e => hφiso ⟨a, haH⟩ e
  have hQ : IsQuadSpace M₀.B M₀.Qf := ⟨M₀.alt, M₀.nondeg, M₀.Qf_add⟩
  have hTT : ∀ e, T (T e) = e := by
    have h1 : φ₀ ⟨a, haH⟩ * φ₀ ⟨a, haH⟩ = 1 := by
      rw [← map_mul, hφQ]
      show a * a ∈ Q
      rw [← pow_two]
      exact hc.sq_mem_Q_of_mem_LB haL
    intro e
    have := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) h1
    simpa using this
  have hTb : T b = b := (hc.LB_act_fix_line h hB haL (T := (T : M₀.E →ₗ[K] M₀.E)) hTπ).1
  have hTU : ∀ u ∈ U, T u = u := by
    intro u hu
    obtain ⟨r, hr, hrQ, rfl⟩ := (hUmem u).mp hu
    have hnorm : a * r * a⁻¹ ∈ Q := hc.L0_normalizes_Q ha.1 r hrQ
    have hcQ : ⁅a, r⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hnorm (Q.inv_mem hrQ)
    have hZ : ⁅a, r⁆ ∈ Z := ha.2 r hr
    have hkd : ⁅a, r⁆ * r = a * r * a⁻¹ := by rw [commutatorElement_def]; group
    rw [← hTπ r hrQ, ← hkd, M₀.π_mul _ hcQ _ hrQ, (M₀.π_ker _ hcQ).mpr hZ, zero_add]
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : M₀.E, M₀.B b f₀ = 1 := by
    by_contra hcon
    push Not at hcon
    refine hb0 ((modelB_nondegenerate M₀).1 b fun y => ?_)
    by_contra hy
    apply hcon ((M₀.B b y)⁻¹ • y)
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
  have hmemU : T f₀ - f₀ ∈ U := by
    apply hUperp
    intro u hu
    have h1 : M₀.B u (T f₀) = M₀.B (T u) f₀ := by
      have := hQ.B_iso T hTQ u (T f₀)
      rw [hTT f₀] at this
      exact this.symm
    rw [map_sub, h1, hTU u hu, sub_self]
  have hqv : M₀.Qf (T f₀ - f₀) = 0 := hUsing _ hmemU
  exact hno a haL (hc.isA2_of_A0_qf h ha haQ hb0 hbs hB hcent T hTπ hTQ hTb hf₀ hqv)

theorem faithful95 (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (φ₀ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ₀ m (M₀.π x))
    (hφQ : ∀ m : H0 M Z, φ₀ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ₀ m e) = M₀.Qf e)
    (hno : NoA2 Q Z (LB M Q B)) {U : Submodule K M₀.E}
    (hUmem : ∀ e, e ∈ U ↔ e ∈ M₀.img (Q ⊓ QB B)) (hUsing : ∀ e ∈ U, M₀.Qf e = 0)
    (hUperp : ∀ e, (∀ u ∈ U, M₀.B u e = 0) → e ∈ U)
    {b : M₀.E} (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0)
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {a : G} (haQM : a ∈ QB B ⊓ M) (haH : a ∈ H0 M Z)
    (hTU : ∀ u ∈ U, φ₀ ⟨a, haH⟩ u = u) : a ∈ Q := by
  classical
  have haM : a ∈ M := haQM.2
  have hZc : a ∈ Subgroup.centralizer (Z : Set G) := haH.2
  refine A0_le_Q hc h φ₀ hφπ hφQ hφiso hno hUmem hUsing hUperp hb0 hbs hB hcent
    ⟨⟨haQM.1, hZc⟩, fun r hr => ?_⟩
  have hrQ : r ∈ Q := (Subgroup.mem_inf.mp hr).1
  have hnorm : a * r * a⁻¹ ∈ Q := hc.L0_normalizes_Q ⟨haQM.1, hZc⟩ r hrQ
  have hcQ : ⁅a, r⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem hnorm (Q.inv_mem hrQ)
  have hkd : ⁅a, r⁆ * r = a * r * a⁻¹ := by rw [commutatorElement_def]; group
  have h1 : M₀.π (a * r * a⁻¹) = M₀.π r := by
    have hu : M₀.π r ∈ U := (hUmem _).mpr (M₀.pi_mem_img hr hrQ)
    rw [hφπ ⟨a, haH⟩ r hrQ]
    exact hTU _ hu
  rw [← hkd, M₀.π_mul _ hcQ _ hrQ] at h1
  have h2 : M₀.π ⁅a, r⁆ = 0 := by
    have : M₀.π ⁅a, r⁆ + M₀.π r = 0 + M₀.π r := by rw [h1, zero_add]
    exact add_right_cancel this
  exact (M₀.π_ker _ hcQ).mp h2

theorem sec95One_core (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hcen : Centre95 hc t Z0)
    {g : G} (hgM : g ∈ M) (hgN : conjSubgroup g (N1 hc t) = N1 hc t) :
    conjSubgroup g Z0 = Z0 := by
  classical
  by_contra hne
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨hZ0LN, hZ0rel, hZ0V⟩ := hcen
  have hZ0N1 : Z0 ≤ N1 hc t := hZ0LN
  have hZ0L : Z0 ≤ LB M Q B := fun x hx => (hZ0LN hx).1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hN1L : N1 hc t ≤ LB M Q B := inf_le_left
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hq4 := hc.hyp.q4
  obtain ⟨K, fK, finK, chK, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ₀, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨φ, hφπ', hφker, hφadd, hφsemi⟩ := exists_actionHom_M hc.hyp h
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hKZ : Nat.card K = Nat.card Z := h.card
  have hK2 : 1 < Nat.card K := by rw [hKZ]; omega
  obtain ⟨U, hUmem, hUdim, hE, hUsing, hUperp⟩ := exists_lagrangian95 h34 hs h
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  have hQ : IsQuadSpace M₀.B M₀.Qf := ⟨M₀.alt, M₀.nondeg, M₀.Qf_add⟩
  have hbU : b ∈ U := (hUmem b).mpr (M₀.img_mono (le_inf hc.le hc.B_le_QB)
    ((hB b).mpr ⟨1, (one_smul K b).symm⟩))
  let α : ↥(LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E) := φ₀.comp (Subgroup.inclusion hc.LB_le_H0)
  have hαπ : ∀ (l : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((l : G) * x * (l : G)⁻¹) = α l (M₀.π x) := fun l x hx =>
    hφπ ⟨(l : G), hc.LB_le_H0 l.2⟩ x hx
  have hα1 : ∀ l : ↥(LB M Q B), α l = 1 ↔ (l : G) ∈ Q := fun l =>
    hφQ ⟨(l : G), hc.LB_le_H0 l.2⟩
  have hαiso : ∀ (l : ↥(LB M Q B)) e, M₀.Qf (α l e) = M₀.Qf e := fun l e =>
    hφiso ⟨(l : G), hc.LB_le_H0 l.2⟩ e
  have hφα : ∀ (l : ↥(LB M Q B)) e, φ ⟨(l : G), hc.LB_le_M l.2⟩ e = α l e := by
    intro l e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hφπ' ⟨(l : G), hc.LB_le_M l.2⟩ x hxQ, hαπ l x hxQ]
  have hφQf : ∀ m : ↥M, ∃ (σ : K ≃+* K) (a : K), ∀ e, M₀.Qf (φ m e) = a * σ (M₀.Qf e) := by
    intro m
    obtain ⟨σ, a, T, hT1, hTπ, -, hTQ⟩ := h.act (m : G) m.2
    refine ⟨σ, (a : K), fun e => ?_⟩
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hφπ' m x hxQ, hTπ x hxQ, hTQ]
  have hφ0 : ∀ m : ↥M, φ m 0 = 0 := fun m => by
    have := hφadd m 0 0
    simpa using this
  have hφsub : ∀ (m : ↥M) a b, φ m (a - b) = φ m a - φ m b := fun m a b => by
    have := hφadd m (a - b) b
    rw [sub_add_cancel] at this
    rw [this]; abel
  have hS : Siegel M₀.B M₀.Qf α U b := by
    refine ⟨hαiso, fun l e => ?_, hUsing, hUperp, hbU, hb0, fun l => ?_, fun l u hu => ?_⟩
    · have h1 : α l * α l = 1 := by
        rw [← map_mul, hα1]
        show (l : G) * (l : G) ∈ Q
        rw [← pow_two]
        exact hc.sq_mem_Q_of_mem_LB l.2
      have := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) h1
      simpa using this
    · exact (hc.LB_act_fix_line h hB l.2 (T := (α l : M₀.E →ₗ[K] M₀.E)) (hαπ l)).1
    · obtain ⟨c, hc'⟩ := (hc.LB_act_fix_line h hB l.2 (T := (α l : M₀.E →ₗ[K] M₀.E))
        (hαπ l)).2 u ((hUmem u).mp hu)
      refine ⟨c, ?_⟩
      have : α l u - u = c • b := hc'
      rw [← this]; abel
  set Γ₁ : Subgroup ↥(LB M Q B) := (N1 hc t).subgroupOf (LB M Q B) with hΓ₁
  have hΓ₁mem : ∀ x : ↥(LB M Q B), x ∈ Γ₁ ↔ (x : G) ∈ N1 hc t := fun x => Subgroup.mem_subgroupOf
  have hker : α.ker = Q.subgroupOf (LB M Q B) := by
    ext x
    rw [MonoidHom.mem_ker, hα1, Subgroup.mem_subgroupOf]
  have hfaith : ∀ x ∈ Γ₁, (∀ u ∈ U, α x u = u) → ∀ e, α x e = e := by
    intro x _ hxU e
    obtain ⟨s', hs', y, hy, hxsy⟩ := hc.exists_mul_of_mem_LB x.2
    have hs'' : s' ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := by
      rw [← hc.QB_inf_M_eq]; exact hs'
    have hsH : s' ∈ H0 M Z := ⟨hs'.2, hs''.2⟩
    have hyH : y ∈ H0 M Z := hc.LB_le_H0 (hQL hy)
    have hxH : (x : G) ∈ H0 M Z := hc.LB_le_H0 x.2
    have hφx : φ₀ ⟨(x : G), hxH⟩ = φ₀ ⟨s', hsH⟩ := by
      have : (⟨(x : G), hxH⟩ : H0 M Z) = ⟨s', hsH⟩ * ⟨y, hyH⟩ := Subtype.ext hxsy
      rw [this, map_mul, (hφQ ⟨y, hyH⟩).mpr hy, mul_one]
    have hTU : ∀ u ∈ U, φ₀ ⟨s', hsH⟩ u = u := by
      intro u hu
      rw [← hφx]
      exact hxU u hu
    have hsQ : s' ∈ Q := faithful95 hc h φ₀ hφπ hφQ hφiso hs5.noA2 hUmem hUsing hUperp hb0 hbs
      hB hcent hs' hsH hTU
    have hxQ : (x : G) ∈ Q := by rw [hxsy]; exact Q.mul_mem hsQ hy
    rw [(hα1 x).mpr hxQ]
    rfl
  have hcardΓ₁ : Nat.card K ^ (n - 3) ≤ α.ker.relIndex Γ₁ := by
    rw [hker, hΓ₁, Subgroup.relIndex_subgroupOf hN1L, relIndex_Q_N1 h34 hs, hKZ]
  have hCU : Module.finrank K ↥(U ⊓ fixSpace α Γ₁) ≤ 3 := by
    have h1 := hS.finrank_fix_le hQ Γ₁ (n - 3) hfaith hcardΓ₁
    have h2 := hs5.n_gt
    omega
  set V := Vt M (LB M Q B) B Z t with hV
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  let Vsub : Submodule K M₀.E := imgSub M₀ V (fun c e he => hc.smul_mem_img_Vt h t c he)
  have hVsub_mem : ∀ e, e ∈ Vsub ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have h35all := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hVsing : ∀ e ∈ Vsub, M₀.Qf e = 0 := fun e he => by
    have hel := hc.Vt_isElemAbelian h35all.2.1 ht hs5.notQ
    exact (M₀.isElemAbelian_iff h.reg hVQ).mp hel e ((hVsub_mem e).mp he)
  obtain ⟨z, hzZ0, hzQ⟩ : ∃ z ∈ Z0, z ∉ Q := by
    by_contra hcon
    push Not at hcon
    have h1 : Q.relIndex Z0 = 1 := Subgroup.relIndex_eq_one.mpr hcon
    rw [hZ0rel] at h1
    omega
  have hrangeV : ∀ (w : G) (hw : w ∈ Z0) (e : M₀.E), α ⟨w, hZ0L hw⟩ e - e ∈ Vsub := by
    intro w hw e
    by_cases hwQ : w ∈ Q
    · have : α ⟨w, hZ0L hw⟩ = 1 := (hα1 _).mpr hwQ
      rw [this]
      simp
    · obtain ⟨hwQ1, hwQ2⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M (hZ0L hw))
      have hmem := (mem_img_comm_zpowers_sup_iff M₀ h.reg (α ⟨w, hZ0L hw⟩) hwQ1 hwQ2
        (hαπ ⟨w, hZ0L hw⟩) (α ⟨w, hZ0L hw⟩ e - e)).mpr ⟨e, by simp⟩
      rw [hZ0V w hw hwQ] at hmem
      exact (hVsub_mem _).mpr hmem
  have hrangeV' : ∀ v ∈ Vsub, ∃ e, α ⟨z, hZ0L hzZ0⟩ e - e = v := by
    intro v hv
    obtain ⟨hzQ1, hzQ2⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M (hZ0L hzZ0))
    have hmem : v ∈ M₀.img (⁅Q, Subgroup.zpowers z⁆ ⊔ Z) := by
      rw [hZ0V z hzZ0 hzQ]
      exact (hVsub_mem v).mp hv
    obtain ⟨e, he⟩ := (mem_img_comm_zpowers_sup_iff M₀ h.reg (α ⟨z, hZ0L hzZ0⟩) hzQ1 hzQ2
      (hαπ ⟨z, hZ0L hzZ0⟩) v).mp hmem
    exact ⟨e, by simpa using he⟩
  have hfixV : ∀ (y : G) (hy : y ∈ N1 hc t) (v : M₀.E), v ∈ Vsub → α ⟨y, hN1L hy⟩ v = v := by
    intro y hy v hv
    obtain ⟨x, hxV, hxQ, rfl⟩ := (hVsub_mem v).mp hv
    have hZ' : ⁅y, x⁆ ∈ Z := (Ctx.mem_CN.mp (Subgroup.mem_inf.mp hy).2).2 x hxV
    have hQ' : ⁅y, x⁆ ∈ Q := hZQ hZ'
    have hkd : ⁅y, x⁆ * x = y * x * y⁻¹ := by rw [commutatorElement_def]; group
    rw [← hαπ ⟨y, hN1L hy⟩ x hxQ]
    show M₀.π (y * x * y⁻¹) = M₀.π x
    rw [← hkd, M₀.π_mul _ hQ' _ hxQ, (M₀.π_ker _ hQ').mpr hZ', zero_add]
  have hgi : g⁻¹ ∈ M := M.inv_mem hgM
  have hconj_mem : ∀ w ∈ N1 hc t, g * w * g⁻¹ ∈ N1 hc t := fun w hw => by
    have : g * w * g⁻¹ ∈ conjSubgroup g (N1 hc t) :=
      mem_conjSubgroup.mpr (by rw [show g⁻¹ * (g * w * g⁻¹) * g = w by group]; exact hw)
    rwa [hgN] at this
  have hconj_mem' : ∀ w ∈ N1 hc t, g⁻¹ * w * g ∈ N1 hc t := fun w hw => by
    have : w ∈ conjSubgroup g (N1 hc t) := by rwa [hgN]
    exact mem_conjSubgroup.mp this
  have hgg : φ ⟨g, hgM⟩ * φ ⟨g⁻¹, hgi⟩ = 1 := by
    rw [← map_mul]
    have : (⟨g, hgM⟩ * ⟨g⁻¹, hgi⟩ : ↥M) = 1 := Subtype.ext (mul_inv_cancel g)
    rw [this, map_one]
  have hφconj : ∀ (w : G) (hw : w ∈ LB M Q B) (hw' : g * w * g⁻¹ ∈ LB M Q B) (e : M₀.E),
      α ⟨g * w * g⁻¹, hw'⟩ e = φ ⟨g, hgM⟩ (α ⟨w, hw⟩ (φ ⟨g⁻¹, hgi⟩ e)) := by
    intro w hw hw' e
    have h1 : (⟨g * w * g⁻¹, hc.LB_le_M hw'⟩ : ↥M) =
        ⟨g, hgM⟩ * ⟨w, hc.LB_le_M hw⟩ * ⟨g⁻¹, hgi⟩ := Subtype.ext rfl
    have h2 := hφα ⟨g * w * g⁻¹, hw'⟩ e
    have h3 := hφα ⟨w, hw⟩ (φ ⟨g⁻¹, hgi⟩ e)
    rw [← h2]
    show φ ⟨g * w * g⁻¹, hc.LB_le_M hw'⟩ e = _
    rw [h1, map_mul, map_mul]
    show φ ⟨g, hgM⟩ (φ ⟨w, hc.LB_le_M hw⟩ (φ ⟨g⁻¹, hgi⟩ e)) = _
    rw [h3]
  have hφinv : ∀ e, φ ⟨g, hgM⟩ (φ ⟨g⁻¹, hgi⟩ e) = e := fun e => by
    have := congrArg (fun f : Equiv.Perm M₀.E => f e) hgg
    simpa using this
  have hφinv' : ∀ e, φ ⟨g⁻¹, hgi⟩ (φ ⟨g, hgM⟩ e) = e := fun e => by
    have h1 : φ ⟨g⁻¹, hgi⟩ * φ ⟨g, hgM⟩ = 1 := by
      rw [← map_mul]
      have : (⟨g⁻¹, hgi⟩ * ⟨g, hgM⟩ : ↥M) = 1 := Subtype.ext (inv_mul_cancel g)
      rw [this, map_one]
    have := congrArg (fun f : Equiv.Perm M₀.E => f e) h1
    simpa using this
  have hconj_range : ∀ (w : G) (hw : w ∈ Z0) (e : M₀.E),
      ∃ v ∈ Vsub, α ⟨g * w * g⁻¹, hN1L (hconj_mem w (hZ0N1 hw))⟩ e - e = φ ⟨g, hgM⟩ v := by
    intro w hw e
    refine ⟨α ⟨w, hZ0L hw⟩ (φ ⟨g⁻¹, hgi⟩ e) - φ ⟨g⁻¹, hgi⟩ e, hrangeV w hw _, ?_⟩
    rw [hφconj w (hZ0L hw) (hN1L (hconj_mem w (hZ0N1 hw))) e, hφsub]
    congr 1
    exact (hφinv e).symm
  have hz'N1 : g * z * g⁻¹ ∈ N1 hc t := hconj_mem z (hZ0N1 hzZ0)
  let z'' : ↥(LB M Q B) := ⟨g * z * g⁻¹, hN1L hz'N1⟩
  let Tsub : Submodule K M₀.E := LinearMap.range ((α z'' : M₀.E →ₗ[K] M₀.E) - 1)
  have hTmem : ∀ t', t' ∈ Tsub ↔ ∃ e, α z'' e - e = t' := fun t' => by
    simp [Tsub]
  have hT0 : ∀ t' ∈ Tsub, ∃ v ∈ Vsub, t' = φ ⟨g, hgM⟩ v := by
    intro t' ht'
    obtain ⟨e, rfl⟩ := (hTmem t').mp ht'
    obtain ⟨v, hv, hv'⟩ := hconj_range z hzZ0 e
    exact ⟨v, hv, hv'⟩
  have hTsub_ge : ∀ v ∈ Vsub, φ ⟨g, hgM⟩ v ∈ Tsub := by
    intro v hv
    obtain ⟨e₀, he₀⟩ := hrangeV' v hv
    refine (hTmem _).mpr ⟨φ ⟨g, hgM⟩ e₀, ?_⟩
    rw [← he₀, hφsub]
    have := hφconj z (hZ0L hzZ0) (hN1L hz'N1) (φ ⟨g, hgM⟩ e₀)
    rw [hφinv'] at this
    rw [show α z'' (φ ⟨g, hgM⟩ e₀) = φ ⟨g, hgM⟩ (α ⟨z, hZ0L hzZ0⟩ e₀) from this]
  have hT1 : ∀ t', t' ∈ Tsub → M₀.Qf t' = 0 := by
    intro t' ht'
    obtain ⟨v, hv, rfl⟩ := hT0 t' ht'
    obtain ⟨σ, a, ha⟩ := hφQf ⟨g, hgM⟩
    rw [ha, hVsing v hv, map_zero, mul_zero]
  have hT2 : ∀ v ∈ Vsub, ∀ t', t' ∈ Tsub → M₀.B v t' = 0 := by
    intro v hv t' ht'
    obtain ⟨e, rfl⟩ := (hTmem t').mp ht'
    rw [hS.form_symm hQ z'' v e, hfixV _ hz'N1 v hv, sub_self, LinearMap.map_zero₂]
  have hT3 : ∀ (y : G) (hy : y ∈ N1 hc t) (t' : M₀.E), t' ∈ Tsub → α ⟨y, hN1L hy⟩ t' = t' := by
    intro y hy t' ht'
    obtain ⟨v, hv, rfl⟩ := hT0 t' ht'
    have hyc := hconj_mem' y hy
    have h1 : φ ⟨g, hgM⟩ * φ ⟨g⁻¹ * y * g, hc.LB_le_M (hN1L hyc)⟩ =
        φ ⟨y, hc.LB_le_M (hN1L hy)⟩ * φ ⟨g, hgM⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp [mul_assoc])
    have h2 := congrArg (fun f : Equiv.Perm M₀.E => f v) h1
    simp only [Equiv.Perm.mul_apply] at h2
    have h3 : φ ⟨g⁻¹ * y * g, hc.LB_le_M (hN1L hyc)⟩ v = v := by
      rw [hφα ⟨g⁻¹ * y * g, hN1L hyc⟩ v]
      exact hfixV _ hyc v hv
    rw [h3] at h2
    rw [← hφα ⟨y, hN1L hy⟩]
    exact h2.symm
  let FS : Submodule K M₀.E := fixSpace α Γ₁
  let Tot : Submodule K M₀.E := Vsub ⊔ Tsub
  have hVF : Vsub ≤ FS := by
    intro v hv
    show v ∈ fixSpace α Γ₁
    rw [mem_fixSpace]
    intro y hy
    exact hfixV (y : G) ((hΓ₁mem y).mp hy) v hv
  have hTF : Tsub ≤ FS := by
    intro t' ht'
    show t' ∈ fixSpace α Γ₁
    rw [mem_fixSpace]
    intro y hy
    exact hT3 (y : G) ((hΓ₁mem y).mp hy) t' ht'
  have hTot : ∀ e ∈ Tot, M₀.Qf e = 0 := by
    intro e he
    obtain ⟨v, hv, t', ht', rfl⟩ := Submodule.mem_sup.mp he
    rw [M₀.Qf_add, hVsing v hv, hT1 t' ht', hT2 v hv t' ht']
    ring
  let G₂ : Subgroup ↥(LB M Q B) :=
    { carrier := {x | ∀ e, α x e - e ∈ Tot ⊓ FS}
      mul_mem' := by
        intro x y hx hy e
        have e1 : α (x * y) e - e = (α x (α y e) - α y e) + (α y e - e) := by
          rw [map_mul]
          simp only [LinearEquiv.mul_apply]
          abel
        rw [e1]
        exact (Tot ⊓ FS).add_mem (hx (α y e)) (hy e)
      one_mem' := by
        intro e
        simp
      inv_mem' := by
        intro x hx e
        have h1 : α x (α x⁻¹ e) = e := by
          have := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e)
            (show α x * α x⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
          simpa using this
        have e1 : α x⁻¹ e - e = -(α x (α x⁻¹ e) - α x⁻¹ e) := by
          rw [h1]; abel
        rw [e1]
        exact (Tot ⊓ FS).neg_mem (hx (α x⁻¹ e)) }
  have hmemG₂ : ∀ x : ↥(LB M Q B), x ∈ G₂ ↔ ∀ e, α x e - e ∈ Tot ⊓ FS := fun x => Iff.rfl
  have hZ0G₂ : ∀ (w : G) (hw : w ∈ Z0), (⟨w, hZ0L hw⟩ : ↥(LB M Q B)) ∈ G₂ := by
    intro w hw e
    exact ⟨Submodule.mem_sup_left (hrangeV w hw e), hVF (hrangeV w hw e)⟩
  have hconjG₂ : ∀ (w : G) (hw : w ∈ Z0),
      (⟨g * w * g⁻¹, hN1L (hconj_mem w (hZ0N1 hw))⟩ : ↥(LB M Q B)) ∈ G₂ := by
    intro w hw e
    obtain ⟨v, hv, hv'⟩ := hconj_range w hw e
    rw [hv']
    exact ⟨Submodule.mem_sup_right (hTsub_ge v hv), hTF (hTsub_ge v hv)⟩
  have hfix : ∀ x ∈ G₂, ∀ e, ∀ y ∈ Γ₁, α y (α x e - e) = α x e - e :=
    fun x hx e y hy => mem_fixSpace.mp ((hx e).2) y hy
  have hnot : ∃ w ∈ Z0, g * w * g⁻¹ ∉ Z0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hle : conjSubgroup g Z0 ≤ Z0 := fun x hx => by
      have hw : g⁻¹ * x * g ∈ Z0 := mem_conjSubgroup.mp hx
      have := hcon _ hw
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  have hcard : ∀ C : Subgroup ↥(LB M Q B), C ≤ G₂ → (∀ x ∈ C, α x = 1) →
      Nat.card K < C.relIndex G₂ := by
    intro C hCG hC1
    have hCk : C ≤ α.ker := fun x hx => (MonoidHom.mem_ker).mpr (hC1 x hx)
    have hZ0'G : Z0.subgroupOf (LB M Q B) ≤ G₂ := fun x hx => by
      have := hZ0G₂ (x : G) (Subgroup.mem_subgroupOf.mp hx)
      exact this
    have hkZ0' : α.ker ≤ Z0.subgroupOf (LB M Q B) := by
      rw [hker]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hQZ0 (Subgroup.mem_subgroupOf.mp hx))
    have h1 : α.ker.relIndex (Z0.subgroupOf (LB M Q B)) = Nat.card Z := by
      rw [hker, Subgroup.relIndex_subgroupOf hZ0L, hZ0rel]
    have h2 : (Z0.subgroupOf (LB M Q B)).relIndex G₂ ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle
      obtain ⟨w, hw, hwn⟩ := hnot
      have := hle (hconjG₂ w hw)
      exact hwn (Subgroup.mem_subgroupOf.mp this)
    have h3 : (Z0.subgroupOf (LB M Q B)).relIndex G₂ ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    have h4 := Subgroup.relIndex_mul_relIndex α.ker (Z0.subgroupOf (LB M Q B)) G₂ hkZ0' hZ0'G
    have h5 : α.ker.relIndex G₂ ∣ C.relIndex G₂ := Subgroup.relIndex_dvd_of_le_left G₂ hCk
    have h6 : C.relIndex G₂ ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    have h7 : α.ker.relIndex G₂ ≤ C.relIndex G₂ := Nat.le_of_dvd (Nat.pos_of_ne_zero h6) h5
    rw [h1] at h4
    have h8 : 2 ≤ (Z0.subgroupOf (LB M Q B)).relIndex G₂ := by omega
    rw [hKZ.symm] at h4
    nlinarith
  obtain ⟨x, hxG₂, hxne, hxr⟩ := hS.exists_rank_two hQ Γ₁ G₂ hCU hfix hcard
  have hxQ : (x : G) ∉ Q := fun hxQ => hxne ((hα1 x).mpr hxQ)
  have hxM : (x : G) ∈ M := hc.LB_le_M x.2
  obtain ⟨hxQ1, hxQ2⟩ := hc.conj_mem_Q_of_mem_M hxM
  have hr : ∀ e, M₀.B e b = 0 → ∃ c : K, α x e = e + c • b := fun e he => by
    refine hxr e ?_
    rw [hQ.B_neg e b, he, neg_zero]
  have hne1 : ∃ e, (α x : M₀.E →ₗ[K] M₀.E) e ≠ e := by
    by_contra hcon
    push Not at hcon
    exact hxne (LinearEquiv.ext fun e => by simpa using hcon e)
  have hfin : Module.finrank K (LinearMap.range ((α x : M₀.E →ₗ[K] M₀.E) - 1)) = 2 :=
    Tim79.QuadModel.finrank_range_eq_two (M₀ := M₀) (T := (α x : M₀.E →ₗ[K] M₀.E))
      (hαiso x) hb0 hbs hr hne1
  have hsing : ∀ v ∈ LinearMap.range ((α x : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf v = 0 := by
    rintro v ⟨e, rfl⟩
    exact hTot _ (hxG₂ e).1
  have hA2 := (isA2_iff M₀ h.reg h.card hK2 (a := (x : G)) (α x) hxQ1 hxQ2 (hαπ x)).mpr
    ⟨hxQ, hc.sq_mem_Q_of_mem_LB x.2, hfin, hsing⟩
  exact hs5.noA2 (x : G) x.2 hA2

end HS9

theorem sec95One_of (h34 : Stroth34Statement) : Step95OneStatement := by
  intro G _ _ M Q Z B hc n t Z0 cfg g hg hgN
  exact HS9.sec95One_core h34 cfg.hs cfg.hZ0 cfg.centre hg hgN

theorem sec95OneFrom_of (h34 : Stroth34Statement) (n0 : ℕ) : Step95OneStatementFrom n0 := by
  intro G _ _ M Q Z B hc n t Z0 cfg _
  exact sec95One_of h34 G M Q Z B hc n t Z0 cfg

end CFSG.RankThree.GF2n.Stroth80
