module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec78Centre
public import CFSG.RankThree.GF2n.Stroth80.Sec78CV
public import CFSG.RankThree.GF2n.Stroth80.Sec310Count
public import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.mem_Q_of_comm_inf_QB_mem_Z (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) {x : G}
    (hx : x ∈ LB M Q B) (hxa : ∀ a ∈ Q ⊓ QB B, ⁅x, a⁆ ∈ Z) : x ∈ Q := by
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hx
  refine Q.mul_mem (hc.centralizer_inf_QB_le hw hn hno h hs.1 fun a ha => ?_) hy
  have h1 : ⁅y, a⁆ ∈ Z := Smith81.comm_mem_Z hc.hyp hy ha.1
  have h2 : s * ⁅y, a⁆ * s⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) _).mp h1
  have h3 : ⁅s, a⁆ ∈ Z := by
    have hsa := hxa a ha
    have he : ⁅s, a⁆ = (s * ⁅y, a⁆ * s⁻¹)⁻¹ * ⁅s * y, a⁆ := by
      simp only [commutatorElement_def]; group
    rw [he]
    exact Z.mul_mem (Z.inv_mem h2) hsa
  have h4 : ⁅s, a⁆ ∈ B := hc.comm_QB_le_B hs.1 ha.2
  have h5 : ⁅s, a⁆ = 1 := by
    have : ⁅s, a⁆ ∈ Z ⊓ B := ⟨h3, h4⟩
    rw [hc.inf_eq_bot] at this
    exact this
  rw [commutatorElement_def] at h5
  calc s * a = s * a * s⁻¹ * a⁻¹ * (a * s) := by group
    _ = a * s := by rw [h5, one_mul]

section model

variable {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.conj_mem_Q (hc : Ctx M Q Z B) {m x : G} (hm : m ∈ M) (hx : x ∈ Q) :
    m * x * m⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) x).mp hx

theorem Ctx.exists_T_of_LB (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {l : G}
    (hl : l ∈ LB M Q B) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E, ∀ x ∈ Q, M₀.π (l * x * l⁻¹) = T (M₀.π x) := by
  have h0 := hc.LB_le_H0 hl
  obtain ⟨T, hT, -, -⟩ := h.linear_of_centralizes h0.1 fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp h0.2 z hz
    rw [← this]; group
  exact ⟨T, hT⟩

theorem Ctx.pi_comm_eq (hc : Ctx M Q Z B) {T : M₀.E ≃ₗ[K] M₀.E} {l a : G} (hl : l ∈ M)
    (ha : a ∈ Q) (hT : ∀ x ∈ Q, M₀.π (l * x * l⁻¹) = T (M₀.π x)) :
    M₀.π ⁅l, a⁆ = T (M₀.π a) - M₀.π a := by
  have hla := hc.conj_mem_Q hl ha
  rw [commutatorElement_def, M₀.π_mul _ hla _ (Q.inv_mem ha), Tim79.QuadModel.pi_inv M₀ ha,
    hT a ha, sub_eq_add_neg]

theorem Ctx.comm_mem_Q_left (hc : Ctx M Q Z B) {l a : G} (hl : l ∈ M) (ha : a ∈ Q) :
    ⁅l, a⁆ ∈ Q := by
  rw [commutatorElement_def]
  exact Q.mul_mem (hc.conj_mem_Q hl ha) (Q.inv_mem ha)

theorem Ctx.pi_mem_img_B_of_mem_sup (hc : Ctx M Q Z B) {y : G} (hy : y ∈ Z ⊔ B) :
    M₀.π y ∈ M₀.img B := by
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have key : y ∈ Q ∧ M₀.π y ∈ M₀.img B := by
    rw [Subgroup.sup_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨hZQ hx, by rw [(M₀.π_ker x (hZQ hx)).2 hx]; exact (M₀.img B).zero_mem⟩
      · exact ⟨hc.le hx, Tim79.QuadModel.pi_mem_img M₀ hx (hc.le hx)⟩
    | one => exact ⟨Q.one_mem, by rw [Tim79.QuadModel.pi_one]; exact (M₀.img B).zero_mem⟩
    | mul x y _ _ hx hy =>
      exact ⟨Q.mul_mem hx.1 hy.1, by
        rw [M₀.π_mul x hx.1 y hy.1]; exact (M₀.img B).add_mem hx.2 hy.2⟩
    | inv x _ hx =>
      exact ⟨Q.inv_mem hx.1, by rw [Tim79.QuadModel.pi_inv M₀ hx.1]; exact (M₀.img B).neg_mem hx.2⟩
  exact key.2

end model

theorem sec7CentreMpr_of_inputs (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) : Sec7CentreMprStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 x hx hxW
  classical
  obtain ⟨d, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have h5 := hs.toSec5
  have hw := h5.width
  have hn := h5.n_gt
  have hno := h5.noA2
  have htL := h5.mem
  have htM : t ∈ M := hc.LB_le_M htL
  set V := Vt M (LB M Q B) B Z t with hV
  set W := Wt Q V with hW
  have hQ1 : W = Q1 hc t :=
    (stroth310Chi_of_34 h34 G M Q Z B hc n t h5 (Or.inr hs.omegaNat)).2
  have hmemW : ∀ a ∈ Q, ⁅t, a⁆ ∈ Z → a ∈ W := fun a ha hta => by
    rw [hQ1]; exact (hc.mem_Q1_iff htM).2 ⟨ha, hta⟩
  have hBW : B ≤ W := (hc.B_le_Vt htL).trans (sec7ctr_Vt_le_Wt h34 hc h5)
  have hMp := sec7CentreMp_of_inputs h51 h52a hA G M Q Z B hc n t hs Z0 hZ0
  have hcard := sec7ZCard_of_inputs h51 hA G M Q Z B hc n t hs Z0 hZ0
  obtain ⟨b, hb0, -, hbB, -, -⟩ := hc.dictB h
  obtain ⟨Λ, hΛ, -, -, -⟩ := hc.lagr hw hn hno h
  set P := Q ⊓ QB B with hP
  have hline : ∀ l ∈ LB M Q B, ∀ a ∈ P, ∃ s : GaloisField 2 d, M₀.π ⁅l, a⁆ = s • b :=
    fun l hl a ha => (hbB _).1 (hc.pi_mem_img_B_of_mem_sup (hc.comm_LB_inf_QB_mem_sup hl ha))
  have hker : ∀ l ∈ M, ∀ a ∈ Q, (M₀.π ⁅l, a⁆ = 0 ↔ ⁅l, a⁆ ∈ Z) :=
    fun l hl a ha => M₀.π_ker _ (hc.comm_mem_Q_left hl ha)
  obtain ⟨a0, ha0, hta0⟩ : ∃ a0 ∈ P, ⁅t, a0⁆ ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact h5.notQ (hc.mem_Q_of_comm_inf_QB_mem_Z hw hn hno h htL hcon)
  obtain ⟨Tt, hTt⟩ := hc.exists_T_of_LB h htL
  obtain ⟨s0, hs0⟩ := hline t htL a0 ha0
  have hs0ne : s0 ≠ 0 := by
    rintro rfl
    exact hta0 ((hker t htM a0 ha0.1).1 (by rw [hs0, zero_smul]))
  have hC : ∀ y ∈ LB M Q B, (∀ w ∈ W, ⁅y, w⁆ ∈ Z) → ∀ a ∈ P, ∃ c : GaloisField 2 d,
      (∀ y' ∈ LB M Q B, (∀ w ∈ W, ⁅y', w⁆ ∈ Z) →
        M₀.π ⁅y', a⁆ = c • M₀.π ⁅y', a0⁆) := by
    intro _ _ _ a ha
    obtain ⟨s1, hs1⟩ := hline t htL a ha
    refine ⟨s1 / s0, fun y' hy' hy'W => ?_⟩
    set c := s1 / s0
    have he : M₀.π a - c • M₀.π a0 ∈ M₀.img P := by
      rw [hΛ]
      exact Λ.sub_mem ((hΛ _).1 (Tim79.QuadModel.pi_mem_img M₀ ha ha.1))
        (Λ.smul_mem c ((hΛ _).1 (Tim79.QuadModel.pi_mem_img M₀ ha0 ha0.1)))
    obtain ⟨a', ha'P, ha'Q, ha'e⟩ := he
    have hta' : ⁅t, a'⁆ ∈ Z := by
      rw [← hker t htM a' ha'Q, hc.pi_comm_eq htM ha'Q hTt, ha'e, map_sub, map_smul,
        sub_sub_sub_comm, ← smul_sub, ← hc.pi_comm_eq htM ha.1 hTt,
        ← hc.pi_comm_eq htM ha0.1 hTt, hs1, hs0, smul_smul, div_mul_cancel₀ _ hs0ne, sub_self]
    have hya' : M₀.π ⁅y', a'⁆ = 0 :=
      (hker y' (hc.LB_le_M hy') a' ha'Q).2 (hy'W a' (hmemW a' ha'Q hta'))
    obtain ⟨Ty, hTy⟩ := hc.exists_T_of_LB h hy'
    rw [hc.pi_comm_eq (hc.LB_le_M hy') ha'Q hTy, ha'e, map_sub, map_smul, sub_sub_sub_comm,
      ← smul_sub, ← hc.pi_comm_eq (hc.LB_le_M hy') ha.1 hTy,
      ← hc.pi_comm_eq (hc.LB_le_M hy') ha0.1 hTy, sub_eq_zero] at hya'
    exact hya'
  have hD : ∀ y ∈ LB M Q B, (∀ w ∈ W, ⁅y, w⁆ ∈ Z) → ∀ z ∈ LB M Q B, (∀ w ∈ W, ⁅z, w⁆ ∈ Z) →
      M₀.π ⁅y, a0⁆ = M₀.π ⁅z, a0⁆ → y * z⁻¹ ∈ Q := by
    intro y hy hyW z hz hzW hyz
    have hyM := hc.LB_le_M hy
    have hzM := hc.LB_le_M hz
    have hpre : ∀ u ∈ LB M Q B, (∀ w ∈ W, ⁅u, w⁆ ∈ Z) → ∀ a ∈ P,
        M₀.π (u⁻¹ * a * u) = M₀.π a - M₀.π ⁅u, a⁆ := by
      intro u hu huW a ha
      have huM := hc.LB_le_M hu
      obtain ⟨Tu, hTu⟩ := hc.exists_T_of_LB h hu
      have hfixb : ∀ s : GaloisField 2 d, Tu (s • b) = s • b := by
        intro s
        obtain ⟨b0, hb0B, hb0Q, rfl⟩ := (hbB b).2 ⟨1, (one_smul _ _).symm⟩
        have hcomm := (hker u huM b0 hb0Q).2 (huW b0 (hBW hb0B))
        rw [hc.pi_comm_eq huM hb0Q hTu, sub_eq_zero] at hcomm
        rw [map_smul, hcomm]
      have hu' : u⁻¹ * a * u ∈ Q := by
        simpa using hc.conj_mem_Q (M.inv_mem huM) ha.1
      apply Tu.injective
      obtain ⟨s, hs⟩ := hline u hu a ha
      rw [← hTu _ hu', show u * (u⁻¹ * a * u) * u⁻¹ = a by group, map_sub, hs, hfixb,
        ← hs, hc.pi_comm_eq huM ha.1 hTu]
      abel
    refine hc.mem_Q_of_comm_inf_QB_mem_Z hw hn hno h
      ((LB M Q B).mul_mem hy ((LB M Q B).inv_mem hz)) fun a ha => ?_
    obtain ⟨c, hc'⟩ := hC y hy hyW a ha
    have hyzA : M₀.π ⁅y, a⁆ = M₀.π ⁅z, a⁆ := by rw [hc' y hy hyW, hc' z hz hzW, hyz]
    set u := y⁻¹ * a * y
    set v := z⁻¹ * a * z
    have huQ : u ∈ Q := by simpa using hc.conj_mem_Q (M.inv_mem hyM) ha.1
    have hvQ : v ∈ Q := by simpa using hc.conj_mem_Q (M.inv_mem hzM) ha.1
    have huv : u⁻¹ * v ∈ Z := by
      rw [← Tim79.QuadModel.pi_eq_iff M₀ huQ hvQ, hpre y hy hyW a ha, hpre z hz hzW a ha, hyzA]
    have hyu : y * u ∈ M := M.mul_mem hyM (hc.hyp.Q_normal.1 huQ)
    have he : ⁅y * z⁻¹, a⁆ = (y * u) * (u⁻¹ * v) * (y * u)⁻¹ := by
      simp only [u, v, commutatorElement_def]; group
    rw [he]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hyu) _).mp huv
  have hQZ0 : Q ≤ Z0 := by
    intro q hq
    have hR : Q ≤ Rt M (LB M Q B) t := le_sup_left.trans (le_Rt (LB M Q B) htL)
    refine (hZ0 q).2 ⟨hR hq, fun r hr => ?_⟩
    have hrq := hc.conj_mem_Q (hc.Rt_le_M t hr) (Q.inv_mem hq)
    have e : ⁅q, r⁆ = q * (r * q⁻¹ * r⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem hq hrq
  set H := Q.subgroupOf Z0
  let L := Submodule.span (GaloisField 2 d) ({b} : Set M₀.E)
  let g : (↥Z0 ⧸ H) → L := fun z => ⟨M₀.π ⁅(Quotient.out z : ↥Z0).1, a0⁆, by
    obtain ⟨s, hs⟩ := hline _ (hMp _ (Quotient.out z).2).1 a0 ha0
    rw [hs]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)⟩
  have hginj : Function.Injective g := by
    intro z1 z2 h12
    have h12' := congrArg Subtype.val h12
    have hm := hD _ (hMp _ (Quotient.out z1).2).1 (hMp _ (Quotient.out z1).2).2
      _ (hMp _ (Quotient.out z2).2).1 (hMp _ (Quotient.out z2).2).2 h12'
    rw [← Quotient.out_eq z1, ← Quotient.out_eq z2]
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    set w1 := (Quotient.out z1 : ↥Z0).1
    set w2 := (Quotient.out z2 : ↥Z0).1
    have hw1M : w1 ∈ M := hc.LB_le_M (hMp _ (Quotient.out z1).2).1
    have := hc.conj_mem_Q (M.inv_mem hw1M) (Q.inv_mem hm)
    simpa [w1, w2, mul_assoc] using this
  have hcardL : Nat.card L = Nat.card (GaloisField 2 d) :=
    (Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton (GaloisField 2 d) M₀.E b hb0).toEquiv).symm
  have hcardH : Nat.card H = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQZ0).toEquiv
  have hcardQuot : Nat.card (↥Z0 ⧸ H) = Nat.card Z := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup H
    rw [hcardH, hcard, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  haveI : Finite M₀.E := Module.finite_of_finite (GaloisField 2 d)
  have hbij := hginj.bijective_of_nat_card_le (by rw [hcardL, h.card, hcardQuot])
  obtain ⟨s, hs⟩ := hline x hx a0 ha0
  obtain ⟨z, hz⟩ := hbij.2 ⟨M₀.π ⁅x, a0⁆, by
    rw [hs]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)⟩
  have hz' := congrArg Subtype.val hz
  have hxz := hD x hx hxW _ (hMp _ (Quotient.out z).2).1 (hMp _ (Quotient.out z).2).2 hz'.symm
  have : x = (x * (Quotient.out z : ↥Z0).1⁻¹) * (Quotient.out z : ↥Z0).1 := by group
  rw [this]
  exact Z0.mul_mem (hQZ0 hxz) (Quotient.out z).2

end CFSG.RankThree.GF2n.Stroth80
