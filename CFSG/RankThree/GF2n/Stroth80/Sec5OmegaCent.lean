module

public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaSingular
public import CFSG.RankThree.GF2n.Stroth80.Sec57D
public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem isElemAbelian_two_of_le {E F : Subgroup G} (h : E ≤ F) (hF : IsElemAbelian 2 F) :
    IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => by
      apply Subtype.ext
      have := hF.1.is_comm.comm ⟨a, h a.2⟩ ⟨b, h b.2⟩
      exact congrArg (fun z : ↥F => (z : G)) this⟩⟩, fun x hx => hF.2 x (h hx)⟩

theorem Ctx.card_LB_inf_CN_mul (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) :
    Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card ↥(Q ⊓ QB B) =
      Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) * Nat.card Q := by
  have hQN : Q ≤ hc.CN t := fun y hy =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt hs.mem hy, fun v hv =>
      hc.hyp.toHyp79.comm_mem_V hy (hc.Vt_le_Q t hv)⟩
  have hQM : Q ≤ M := fun x hx => hc.hyp.Q_normal.1 hx
  have hΛnorm : (QB B ⊓ M) ⊓ hc.CN t ≤ Subgroup.normalizer (Q : Set G) := fun x hx =>
    hc.hyp.Q_normal.2 hx.1.2
  have hinf : ((QB B ⊓ M) ⊓ hc.CN t) ⊓ Q = Q ⊓ QB B := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, -⟩, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨h2, hQM h1⟩, hQN h1⟩, h1⟩
  have hsup : ((QB B ⊓ M) ⊓ hc.CN t) ⊔ Q = LB M Q B ⊓ hc.CN t := by
    apply le_antisymm
    · refine sup_le (le_inf ?_ inf_le_right) (le_inf sec39_Q_le_LB hQN)
      intro x hx
      have : x ∈ (QB B ⊓ M) ⊔ Q := Subgroup.mem_sup_left hx.1
      unfold LB
      rw [sup_comm]
      exact this
    · intro x hx
      obtain ⟨s, hs', y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hx.1
      have hsN : s ∈ hc.CN t := by
        have := (hc.CN t).mul_mem hx.2 ((hc.CN t).inv_mem (hQN hy))
        rwa [mul_inv_cancel_right] at this
      exact Subgroup.mul_mem_sup ⟨hs', hsN⟩ hy
  have e := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hΛnorm
  rw [hinf, hsup] at e
  exact e

theorem card_polar_perp {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (Q' : QuadraticForm K (ι → K)) (hQ : (polarBilin Q').Nondegenerate) {u : ι → K}
    (hu0 : u ≠ 0) :
    Nat.card {x : ι → K // polar Q' u x = 0} = Nat.card K ^ (Fintype.card ι - 1) := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, polar Q' u y ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hQ.1 u (fun y => by simpa using h y))
  let f : (ι → K) →ₗ[K] K := polarBilin Q' u
  have hf : ∀ x, f x = polar Q' u x := fun x => rfl
  have hsurj : Function.Surjective f := fun c =>
    ⟨(c / f y) • y, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (by rw [hf]; exact hy)]⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hrank
  have hker : Module.finrank K (LinearMap.ker f) = Fintype.card ι - 1 := by omega
  have hcard : Nat.card {x : ι → K // polar Q' u x = 0} = Nat.card (LinearMap.ker f) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [LinearMap.mem_ker, hf])
  rw [hcard, Module.natCard_eq_pow_finrank (K := K), hker]

theorem card_eq_of_secVec {V Z W : Subgroup G} [(Z.subgroupOf V).Normal] {ι : Type} [Fintype ι]
    {K : Type} [Field K]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (hZW : Z ≤ W) (hWV : W ≤ V)
    (S : Set (ι → K))
    (hS : ∀ x, (∃ w : ↥V, (w : G) ∈ W ∧ secVec ψ w = x) ↔ x ∈ S) :
    Nat.card ↥W = Nat.card Z * Nat.card S := by
  let g : ↥W →* Multiplicative (ι → K) :=
    ψ.toMonoidHom.comp ((QuotientGroup.mk' (Z.subgroupOf V)).comp (Subgroup.inclusion hWV))
  have hker : g.ker = Z.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show ψ (QuotientGroup.mk (Subgroup.inclusion hWV w)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hrange : Nat.card g.range = Nat.card S := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun y : g.range => (⟨Multiplicative.toAdd y.1, ?_⟩ : S)) ⟨?_, ?_⟩)
    · obtain ⟨w, hw⟩ := y.2
      refine (hS _).mp ⟨⟨(w : G), hWV w.2⟩, w.2, ?_⟩
      rw [← hw]
      rfl
    · intro y y' h
      have h' : Multiplicative.toAdd y.1 = Multiplicative.toAdd y'.1 :=
        congrArg (fun z : ↥S => (z : ι → K)) h
      exact Subtype.ext (Multiplicative.toAdd.injective h')
    · rintro ⟨x, hx⟩
      obtain ⟨w, hwW, hw⟩ := (hS x).mpr hx
      exact ⟨⟨g ⟨(w : G), hwW⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩, Subtype.ext hw⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv] at h1
  rw [h1, mul_comm]

theorem Ctx.inf_CN_inf_Q (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) :
    ((QB B ⊓ M) ⊓ hc.CN t) ⊓ Q = Q ⊓ QB B := by
  have hQN : Q ≤ hc.CN t := fun y hy =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt hs.mem hy, fun v hv =>
      hc.hyp.toHyp79.comm_mem_V hy (hc.Vt_le_Q t hv)⟩
  have hQM : Q ≤ M := fun x hx => hc.hyp.Q_normal.1 hx
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, -⟩, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨h2, hQM h1⟩, hQN h1⟩, h1⟩

theorem Ctx.centLam_omega (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hnatSO : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    ∀ d ∈ Q ⊓ QB B, (∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
      d ∈ Vt M (LB M Q B) B Z t := by
  classical
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hsing := hc.omega_singular h34 hRoot hs hnatSO hK E hQ h3 hX φ hφ ψ hψ
  obtain ⟨u, hQu, hu0, -, hW, hL, -⟩ :=
    hc.omega_points_core h34 hRoot hs hnatSO hK E hQ h3 hX φ hφ hker ψ hψ hsing
  have h35 := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ := hc.Vt_le_Q t
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hZW0 : Z ≤ Vt M (LB M Q B) B Z t ⊓ QB B := le_inf hZV hZQB
  have hW0le : Vt M (LB M Q B) B Z t ⊓ QB B ≤ Q ⊓ QB B := inf_le_inf_right _ hVQ
  have hW0el : IsElemAbelian 2 (Vt M (LB M Q B) B Z t ⊓ QB B) :=
    isElemAbelian_two_of_le hW0le hc.inf_QB_elemAbelian
  obtain ⟨A, hAW, -, hAZ, hAsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing
    Nat.prime_two hW0el hZW0 (bot_le : (⊥ : Subgroup G) ≤ _) (inf_bot_eq Z)
  have hd3 : 3 ≤ Fintype.card ι := by
    rw [← Module.finrank_fintype_fun_eq_card (R := K)]; exact h3
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hW0card : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) =
      Nat.card Z * Nat.card K ^ (Fintype.card ι - 1) := by
    have h1 := card_eq_of_secVec (Z := Z) ψ hZW0 inf_le_left {x | polar Q' u x = 0}
      (fun x => hW x)
    rw [h1]
    congr 1
    exact card_polar_perp Q' hQ hu0
  have hAcard : Nat.card ↥A = Nat.card K ^ (Fintype.card ι - 1) := by
    have h2 := CFSG.SignalizerFunctorTheorem.card_mul_card_complement hW0el hZW0 hAW hAZ hAsup
    rw [hW0card] at h2
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hcim := card_inf_mul_card_map hLR φ hker
  rw [hL, E.card_LomGL hQ hQu hu0, Module.finrank_fintype_fun_eq_card, h35.2.2.1, hK] at hcim
  have hE2 := hc.card_LB_inf_CN_mul hs
  rw [h35.2.2.2] at hE2
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hqpos : 0 < Nat.card Z := by omega
  have key : Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) * Nat.card Z ^ (Fintype.card ι - 2) =
      Nat.card Z ^ (2 * n) := by
    apply Nat.eq_of_mul_eq_mul_left hQpos
    calc Nat.card Q * (Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) * Nat.card Z ^ (Fintype.card ι - 2))
        = (Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) * Nat.card Q) * Nat.card Z ^ (Fintype.card ι - 2) :=
          by ring
      _ = (Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (n + 1)) *
            Nat.card Z ^ (Fintype.card ι - 2) := by rw [hE2]
      _ = (Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (Fintype.card ι - 2)) *
            Nat.card Z ^ (n + 1) := by ring
      _ = (Nat.card Q * Nat.card Z ^ (n - 1)) * Nat.card Z ^ (n + 1) := by rw [hcim]
      _ = Nat.card Q * Nat.card Z ^ (2 * n) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          have := hs.n_gt
          omega
  have hcard : Nat.card Z ^ n * Nat.card ↥(((QB B ⊓ M) ⊓ hc.CN t) ⊓ Q) ≤
      Nat.card ↥A * Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) := by
    rw [hc.inf_CN_inf_Q hs, h35.2.2.2, hAcard, hK]
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hqpos (Fintype.card ι - 2))
    refine le_of_eq ?_
    calc Nat.card Z ^ n * Nat.card Z ^ (n + 1) * Nat.card Z ^ (Fintype.card ι - 2)
        = Nat.card Z ^ (Fintype.card ι - 1) * Nat.card Z ^ (2 * n) := by
          rw [← pow_add, ← pow_add, ← pow_add]
          congr 1
          omega
      _ = Nat.card Z ^ (Fintype.card ι - 1) *
            (Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) * Nat.card Z ^ (Fintype.card ι - 2)) := by
          rw [key]
      _ = Nat.card Z ^ (Fintype.card ι - 1) * Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) *
            Nat.card Z ^ (Fintype.card ι - 2) := by ring
  have hAD : A ≤ Q ⊓ QB B := hAW.trans hW0le
  have hcomm : ∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ∀ a ∈ A, ⁅l, a⁆ = 1 := by
    intro l hl a ha
    have haW := hAW ha
    have hZc : ⁅l, a⁆ ∈ Z := (Ctx.mem_CN.mp hl.2).2 a haW.1
    have hBc : ⁅l, a⁆ ∈ B := hc.comm_QB_le_B hl.1.1 haW.2
    have hmem : ⁅l, a⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hZc, hBc⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  intro d hd hdz
  have hd' := Ctx.pairing_count h34 hc hs (inf_le_left : (QB B ⊓ M) ⊓ hc.CN t ≤ QB B ⊓ M) hAD
    (by rw [inf_comm]; exact hAZ) hcomm hcard d hd hdz
  rw [sup_comm, hAsup] at hd'
  exact hd'.1

end CFSG.RankThree.GF2n.Stroth80
