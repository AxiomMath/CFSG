module

public import CFSG.RankThree.GF2n.Stroth80.Sec12MixedRoot
public import CFSG.RankThree.GF2n.Stroth80.Sec12Index
public import CFSG.RankThree.GF2n.Stroth80.Sec12Aniso
public import CFSG.RankThree.GF2n.Stroth80.Sec12LBFlag
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stab

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

@[expose] def fixingSub (M₀ : Tim79.QuadModel Q Z K γ) (R : Submodule K M₀.E) :
    Subgroup (M₀.E ≃ₗ[K] M₀.E) where
  carrier := {T | ∀ y ∈ R, T y = y}
  mul_mem' := fun {a b} ha hb y hy => by
    show a (b y) = y
    rw [hb y hy, ha y hy]
  one_mem' := fun y _ => rfl
  inv_mem' := fun {a} ha y hy => by
    show a.symm y = y
    exact (LinearEquiv.symm_apply_eq a).mpr (ha y hy).symm

theorem mem_fixingSub {R : Submodule K M₀.E} {T : M₀.E ≃ₗ[K] M₀.E} :
    T ∈ fixingSub M₀ R ↔ ∀ y ∈ R, T y = y := Iff.rfl

theorem Ctx.false_of_mixed [CharP K 2] (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (hno : NoA2 Q Z (LB M Q B)) (hng : ¬ GenByB M Q B) (hw : Width Q Z 3)
    (hS : Nat.card hc.Spure = Nat.card Q * Nat.card Z ^ 2) {b : M₀.E} (hb0 : b ≠ 0)
    (hbs : M₀.Qf b = 0) (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {X : Subgroup G} (hX : Ctx M Q Z X) {x : G} (hxX : x ∈ X) (hxW : M₀.π x ∉ hc.Wn h) :
    False := by
  classical
  haveI : Finite M₀.E := Module.finite_of_finite K
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hn : 2 < 3 := by norm_num
  have hd := hc.finrank_Wp_eq_two h hng hS
  have hsup := hc.Wn_sup_Wp h
  obtain ⟨w, hwW, w', hw'P, hww'⟩ : ∃ w ∈ hc.Wn h, ∃ w' ∈ PerpSub M₀ (Lgen M B),
      w + w' = M₀.π x := by
    have : M₀.π x ∈ hc.Wn h ⊔ PerpSub M₀ (Lgen M B) := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨a, ha, b', hb', hab⟩ := Submodule.mem_sup.mp this
    exact ⟨a, ha, b', hb', hab⟩
  have hw'0 : w' ≠ 0 := by
    intro h0
    apply hxW
    rw [← hww', h0, add_zero]
    exact hwW
  have hπx : M₀.π x ≠ 0 := fun h0 => hxW (by rw [h0]; exact (hc.Wn h).zero_mem)
  have hxQ : x ∈ Q := hX.le hxX
  have hxsing : M₀.Qf (M₀.π x) = 0 :=
    (M₀.isElemAbelian_iff h.reg hX.le).mp hX.isElemAbelian_B _ (M₀.pi_mem_img hxX hxQ)
  have hww'0 : M₀.B w w' = 0 := hc.B_Wn_Wp h hw'P hwW
  have hQ' : M₀.Qf w' ≠ 0 := fun hq =>
    hw'0 (hc.Wp_anisotropic h hno hng hw hn rfl hS hb0 hbs hB hcent hw'P hq)
  have hQw : M₀.Qf w = M₀.Qf w' := by
    have := M₀.Qf_add w w'
    rw [hww', hxsing, hww'0] at this
    linear_combination (-1 : K) * this + (-M₀.Qf w') * h2
  have hQw0 : M₀.Qf w ≠ 0 := hQw ▸ hQ'
  obtain ⟨Φ, hΦπ, hΦker, hΦiso⟩ := hX.exists_actionHom_LB h
  have hBX := hX.img_eq_line_of_ne h hxX hπx
  have hLM : ∀ r : ↥(LB M Q X), (r : G) ∈ M := fun r => hX.LB_le_M r.2
  have hstWn : ∀ r : ↥(LB M Q X), ∀ e ∈ hc.Wn h, Φ r e ∈ hc.Wn h := by
    rintro r e ⟨n, hn', hnQ, rfl⟩
    rw [← hΦπ r n (hc.Lgen_le_Q hn')]
    exact hc.mem_Wn_of_mem_img h
      ((Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M B (hLM r)) n).mp hn')
  have hstWp : ∀ r : ↥(LB M Q X), ∀ e ∈ PerpSub M₀ (Lgen M B), Φ r e ∈ PerpSub M₀ (Lgen M B) := by
    intro r e he
    obtain ⟨c, hcP, hcQ, rfl⟩ := (hc.mem_img_PerpB_iff h e).mpr he
    rw [← hΦπ r c hcQ]
    exact (hc.mem_img_PerpB_iff h _).mp
      (M₀.pi_mem_img (hc.PerpB_conj (hLM r) hcP) ((hc.conj_mem_Q_of_mem_M (hLM r)).1 c hcQ))
  have hfixx : ∀ r : ↥(LB M Q X), Φ r (M₀.π x) = M₀.π x := fun r =>
    (hX.LB_act_fix_line h hBX r.2 (T := (Φ r : M₀.E →ₗ[K] M₀.E)) (fun z hz => hΦπ r z hz)).1
  have hfixw : ∀ r : ↥(LB M Q X), Φ r w = w ∧ Φ r w' = w' := by
    intro r
    have e1 : Φ r w + Φ r w' = w + w' := by rw [← map_add, hww', hfixx r]
    have hmem : Φ r w - w ∈ hc.Wn h ⊓ PerpSub M₀ (Lgen M B) := by
      refine ⟨(hc.Wn h).sub_mem (hstWn r w hwW) hwW, ?_⟩
      have : Φ r w - w = -(Φ r w' - w') := by
        rw [neg_sub]
        linear_combination (norm := module) e1
      rw [this]
      exact (PerpSub M₀ (Lgen M B)).neg_mem ((PerpSub M₀ (Lgen M B)).sub_mem (hstWp r w' hw'P) hw'P)
    rw [hc.Wn_inf_Wp h, Submodule.mem_bot, sub_eq_zero] at hmem
    refine ⟨hmem, ?_⟩
    have := e1
    rw [hmem] at this
    exact add_left_cancel this
  set Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E) := Φ.range with hΛ
  set Λ₀ : Subgroup (M₀.E ≃ₗ[K] M₀.E) := Λ ⊓ fixingSub M₀ (PerpSub M₀ (Lgen M B)) with hΛ₀
  have hΛcard : Nat.card (LB M Q X) = Nat.card Q * Nat.card Λ :=
    card_eq_card_mul_range le_sup_left Φ hΦker
  have hΛge : Nat.card Z ^ 2 ≤ Nat.card Λ := by
    have h1 := hX.card_LB_ge hw (by norm_num)
    rw [hΛcard] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    exact Nat.le_of_mul_le_mul_left (by simpa using h1) hQpos
  have hK : 1 < Nat.card K := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hE := h.finrank_E hw hK
  have hdim4 : Module.finrank K (hc.Wn h) = 4 := by
    have := hc.finrank_Wn_add h
    omega
  have hP : IsPGroup 2 Λ₀ := by
    intro T
    have hTΛ : T.1 ∈ Λ := T.2.1
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hTΛ
    have hsq : T.1 * T.1 = 1 := by
      rw [← hr, ← map_mul]
      exact (hΦker (r * r)).mpr (by simpa [pow_two] using hX.sq_mem_Q_of_mem_LB r.2)
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two, hsq]
  have hindex := card_le_two_mul_of_fixer M₀ Λ Λ₀ (PerpSub M₀ (Lgen M B)) w' hd
    (hc.Wp_inf_orthogonal h) hw'P hQ'
    (by rintro _ ⟨r, rfl⟩ e; exact hΦiso r e)
    (by rintro _ ⟨r, rfl⟩; exact (hfixw r).2)
    (by rintro _ ⟨r, rfl⟩ y hy; exact hstWp r y hy) inf_le_left
    (fun T hT => ⟨fun hT₀ => hT₀.2, fun hTf => ⟨hT, hTf⟩⟩)
  have hstab := card_le_two_mul_of_stab M₀ Λ₀ hP (hc.Wn h) (PerpSub M₀ (Lgen M B)) hdim4
    (hc.Wn_inf_orthogonal h) hsup hwW hQw0
    (by rintro T ⟨⟨r, rfl⟩, -⟩ e; exact hΦiso r e)
    (by rintro T ⟨⟨r, rfl⟩, -⟩; exact (hfixw r).1)
    (fun T hT y hy => hT.2 y hy)
    (by rintro T ⟨⟨r, rfl⟩, -⟩ y hy; exact hstWn r y hy)
  have hq4 := hc.hyp.q4
  have hΛle : Nat.card Λ ≤ 4 * Nat.card K := by
    calc Nat.card Λ ≤ 2 * Nat.card Λ₀ := hindex
      _ ≤ 2 * (2 * Nat.card K) := Nat.mul_le_mul_left _ hstab
      _ = 4 * Nat.card K := by ring
  have hqK : Nat.card K = Nat.card Z := h.card
  have hq : Nat.card Z = 4 := by
    have h1 : Nat.card Z ^ 2 ≤ 4 * Nat.card K := hΛge.trans hΛle
    rw [hqK] at h1
    nlinarith
  have hΛ16 : Nat.card Λ = 16 := by
    have : Nat.card Λ ≤ 16 := by rw [hqK] at hΛle; omega
    have h1 : 16 ≤ Nat.card Λ := by
      have := hΛge
      rw [hq] at this
      omega
    omega
  have hD : Nat.card ↥(Q ⊓ QB X) = Nat.card Z ^ (3 + 1) := by
    have h1 := hX.card_LB_mul hw
    rw [hΛcard, hΛ16, hq] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have h2 : Nat.card Q * 16 * Nat.card ↥(Q ⊓ QB X) = Nat.card Q * 4 ^ (2 * 3) := h1
    have h3 : 16 * Nat.card ↥(Q ⊓ QB X) = 4 ^ (2 * 3) := by
      apply Nat.eq_of_mul_eq_mul_left hQpos
      rw [← h2]
      ring
    rw [hq]
    omega
  have hΛ₀triv : ∀ T ∈ Λ₀, T = 1 := by
    rintro T ⟨⟨r, rfl⟩, hTfix⟩
    obtain ⟨s, hs, y, hy, hsy⟩ := hX.exists_mul_of_mem_LB r.2
    have hfixD : ∀ d ∈ Q ⊓ QB X, Φ r (M₀.π d) = M₀.π d := by
      intro d hd'
      have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd').1
      obtain ⟨c, hc'⟩ := (hX.LB_act_fix_line h hBX r.2 (T := (Φ r : M₀.E →ₗ[K] M₀.E))
        (fun z hz => hΦπ r z hz)).2 (M₀.π d) (M₀.pi_mem_img hd' hdQ)
      have hWnd : Φ r (M₀.π d) - M₀.π d ∈ hc.Wn h := by
        have hdec : M₀.π d ∈ hc.Wn h ⊔ PerpSub M₀ (Lgen M B) := by
          rw [hsup]; exact Submodule.mem_top
        obtain ⟨en, hen, ep, hep, hdecEq⟩ := Submodule.mem_sup.mp hdec
        rw [← hdecEq, map_add, show Φ r ep = ep from mem_fixingSub.mp hTfix ep hep]
        have : Φ r en + ep - (en + ep) = Φ r en - en := by abel
        rw [this]
        exact (hc.Wn h).sub_mem (hstWn r en hen) hen
      have hc'' : Φ r (M₀.π d) - M₀.π d = c • M₀.π x := hc'
      rw [hc''] at hWnd
      have hcw : c • w' ∈ hc.Wn h ⊓ PerpSub M₀ (Lgen M B) := by
        refine ⟨?_, (PerpSub M₀ (Lgen M B)).smul_mem c hw'P⟩
        have : c • w' = c • M₀.π x - c • w := by rw [← hww', smul_add]; abel
        rw [this]
        exact (hc.Wn h).sub_mem hWnd ((hc.Wn h).smul_mem c hwW)
      rw [hc.Wn_inf_Wp h, Submodule.mem_bot] at hcw
      have hc0 : c = 0 := (smul_eq_zero.mp hcw).resolve_right hw'0
      rw [hc0, zero_smul] at hc''
      exact sub_eq_zero.mp hc''
    have hlD : ∀ d ∈ Q ⊓ QB X, ⁅s, d⁆ ∈ Z := by
      intro d hd'
      have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd').1
      have hrdQ : (r : G) * d * (r : G)⁻¹ ∈ Q := (hX.conj_mem_Q_of_mem_M (hLM r)).1 d hdQ
      have hrZ : ⁅(r : G), d⁆ ∈ Z := (M₀.comm_mem_iff hdQ hrdQ).mpr (by
        rw [hΦπ r d hdQ, hfixD d hd'])
      rw [hsy] at hrZ
      have hyd : ⁅y, d⁆ ∈ Z := hX.hyp.toHyp79.comm_mem_V hy hdQ
      have hsZ : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z := fun z hz =>
        (Subgroup.mem_normalizer_iff.mp (hX.hyp.Z_normal.2 hs.2) z).mp hz
      have e : ⁅s * y, d⁆ = (s * ⁅y, d⁆ * s⁻¹) * ⁅s, d⁆ := by
        simp only [commutatorElement_def]
        group
      have h1 : ⁅s, d⁆ = (s * ⁅y, d⁆ * s⁻¹)⁻¹ * ⁅s * y, d⁆ := by
        rw [e]
        group
      rw [h1]
      exact Z.mul_mem (Z.inv_mem (hsZ _ hyd)) hrZ
    have hsQ : s ∈ Q := hX.LB_hom_inj_of_card hw hD hs hlD
    exact (hΦker r).mpr (by rw [hsy]; exact Q.mul_mem hsQ hy)
  have hΛ₀card : Nat.card Λ₀ = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b' => Subtype.ext ?_⟩, ⟨⟨1, Λ₀.one_mem⟩⟩⟩
    rw [hΛ₀triv a.1 a.2, hΛ₀triv b'.1 b'.2]
  rw [hΛ₀card, hΛ16] at hindex
  omega

end CFSG.RankThree.GF2n.Stroth80
