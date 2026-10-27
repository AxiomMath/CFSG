module

public import CFSG.RankThree.GF2n.Stroth80.Sec103ATools
public import CFSG.RankThree.GF2n.Stroth80.Sec101Tt
public import CFSG.RankThree.GF2n.Stroth80.Sec103Three
public import CFSG.RankThree.GF2n.Stroth80.Sec10Second
public import CFSG.RankThree.GF2n.Stroth80.Sec56Frame

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem eq_one_of_mul_mem_QB_conj_of_y_eq_one {hc : Ctx M Q Z B}
    {Y : Subgroup G} {c a : G} (hcQ : c ∈ Q) (ha : a ∈ Q ⊓ QB Y)
    (hu : c⁻¹ * a * c ∈ QB Y) (hZY : Z ⊓ QB Y = ⊥) : a * c = c * a := by
  have h1 : a⁻¹ * (c⁻¹ * a * c) ∈ Z := by
    have h0 := comm_mem_Z hc.hyp (Q.inv_mem ha.1) (Q.inv_mem hcQ)
    have e : ⁅a⁻¹, c⁻¹⁆ = a⁻¹ * (c⁻¹ * a * c) := by
      simp only [commutatorElement_def]; group
    rwa [e] at h0
  have h2 : a⁻¹ * (c⁻¹ * a * c) ∈ QB Y := (QB Y).mul_mem ((QB Y).inv_mem ha.2) hu
  have h3 : a⁻¹ * (c⁻¹ * a * c) = 1 := by
    have h4 : a⁻¹ * (c⁻¹ * a * c) ∈ Z ⊓ QB Y := ⟨h1, h2⟩
    rwa [hZY, Subgroup.mem_bot] at h4
  have h4 : c⁻¹ * a * c = a := by
    calc c⁻¹ * a * c = a * (a⁻¹ * (c⁻¹ * a * c)) := by group
      _ = a := by rw [h3, mul_one]
  calc a * c = c * (c⁻¹ * a * c) := by group
    _ = c * a := by rw [h4]

private theorem mem_Wt_of_mul_mem_QB_conj_of_ne_one (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {c : G} (hcQ : c ∈ Q) {y a : G} (hy : y ∈ Y)
    (hy1 : y ≠ 1) (ha : a ∈ Q ⊓ QB Y)
    (hya : y * a ∈ QB (conjSubgroup c Y)) : c ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hYQB : Y ≤ QB Y := Sit.le_QB hs
  have hu : c⁻¹ * (y * a) * c ∈ QB Y := by
    rw [QB_conj] at hya
    exact mem_conjSubgroup.mp hya
  have hζZ : ⁅a, c⁆ ∈ Z := comm_mem_Z hc.hyp ha.1 hcQ
  have hsy := Sit.of_mem_root hs hy hy1
  have hty := ht.of_mem_root_good101 h34 hspread H hs hy hy1
  have hVy := ht.Vt_eq_of_mem_root h34 hspread H hs hy hy1
  obtain ⟨hyQ1, -⟩ := hc.conj_mem_Q_of_mem_M hsy.memM
  have huQB : c⁻¹ * (y * a) * c * (y * a)⁻¹ ∈ QB Y :=
    (QB Y).mul_mem hu ((QB Y).inv_mem ((QB Y).mul_mem (hYQB hy) ha.2))
  have huQ : c⁻¹ * (y * a) * c * (y * a)⁻¹ ∈ Q := by
    have e : c⁻¹ * (y * a) * c * (y * a)⁻¹ = c⁻¹ * (y * (a * c * a⁻¹) * y⁻¹) := by group
    rw [e]
    exact Q.mul_mem (Q.inv_mem hcQ) (hyQ1 _ (Q.mul_mem (Q.mul_mem ha.1 hcQ) (Q.inv_mem ha.1)))
  have hyζ : y * ⁅a, c⁆ * y⁻¹ = ⁅a, c⁆ := hsy.x_cent (smith_1_12 hsy) _ hζZ
  have hcζ : ⁅a, c⁆ * c⁻¹ = c⁻¹ * ⁅a, c⁆ := Z_central hc.hyp hζZ (Q.inv_mem hcQ)
  have e2 : c⁻¹ * (y * a) * c * (y * a)⁻¹ = ⁅a, c⁆ * ⁅c⁻¹, y⁆ := by
    calc c⁻¹ * (y * a) * c * (y * a)⁻¹
        = c⁻¹ * (y * ⁅a, c⁆ * y⁻¹) * (y * c * y⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = c⁻¹ * ⁅a, c⁆ * (y * c * y⁻¹) := by rw [hyζ]
      _ = ⁅a, c⁆ * c⁻¹ * (y * c * y⁻¹) := by rw [hcζ]
      _ = ⁅a, c⁆ * ⁅c⁻¹, y⁆ := by
          simp only [commutatorElement_def]; group
  have huUt : c⁻¹ * (y * a) * c * (y * a)⁻¹ ∈ Ut Q Z y := by
    rw [e2]
    exact (Ut Q Z y).mul_mem (Subgroup.mem_sup_right hζZ) (comm_mem_Ut (Q.inv_mem hcQ))
  have huT : c⁻¹ * (y * a) * c * (y * a)⁻¹ ∈ Tt Q Z (Vt M (LB M Q B) B Z y) y :=
    hty.inf_QB_inf_Ut_le_Tt h34 hspread H hsy ⟨⟨huQ, huQB⟩, huUt⟩
  have hcy : ⁅c⁻¹, y⁆ ∈ Tt Q Z (Vt M (LB M Q B) B Z y) y := by
    have e3 : ⁅c⁻¹, y⁆ = ⁅a, c⁆⁻¹ * (c⁻¹ * (y * a) * c * (y * a)⁻¹) := by
      rw [e2]; group
    rw [e3]
    exact (Tt Q Z _ y).mul_mem ((Tt Q Z _ y).inv_mem (Subgroup.mem_sup_right hζZ)) huT
  have hcW' := (hc.comm_mem_Tt_iff hty.mem_LB (hty.Vt_le_Ut h34 H) (Q.inv_mem hcQ)).mp hcy
  rw [hVy] at hcW'
  simpa using (Wt Q (Vt M (LB M Q B) B Z t)).inv_mem hcW'

theorem Good101.eq_one_of_mul_mem_QB_conj (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {c : G} (hcQ : c ∈ Q)
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {y a : G} (hy : y ∈ Y) (ha : a ∈ Q ⊓ QB Y)
    (hya : y * a ∈ QB (conjSubgroup c Y)) : y = 1 ∧ a * c = c * a := by
  have hZY : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot hs (smith_1_12 hs)
  have hu : c⁻¹ * (y * a) * c ∈ QB Y := by
    rw [QB_conj] at hya
    exact mem_conjSubgroup.mp hya
  by_cases hy1 : y = 1
  · subst hy1
    simp only [one_mul] at hu
    exact ⟨rfl, eq_one_of_mul_mem_QB_conj_of_y_eq_one (hc := hc) hcQ ha hu hZY⟩
  · exact absurd (mem_Wt_of_mul_mem_QB_conj_of_ne_one h34 hspread H ht hs hcQ hy hy1 ha hya)
      hcW

private theorem centralizer_of_comm_mem_QB_of_line (hc : Ctx M Q Z B) {t c : G}
    {X : Subgroup G} (hX : Ctx M Q Z X) (hcQ : c ∈ Q) {d₀ : G} (hd₀D : d₀ ∈ Q ⊓ QB X)
    (hx₀c : ⁅d₀, t⁆ * c = c * ⁅d₀, t⁆) (hx₀X : ⁅d₀, t⁆ ∈ X)
    (hx₀Z : ⁅d₀, t⁆ ∉ Z) : c ∈ Subgroup.centralizer (X : Set G) := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨gX, hgX⟩ := hX.conj
  have hXQ : X ≤ Q := hX.le
  obtain ⟨e, -, he⟩ := hD.line gX (by rw [← hgX]; exact hX.ne) (by rw [← hgX]; exact hXQ)
  rw [← hgX] at he
  obtain ⟨s, hs⟩ := (he _).mp (M₀.pi_mem_img hx₀X (hXQ hx₀X))
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hs
    exact hx₀Z ((M₀.π_ker _ (hXQ hx₀X)).mp hs)
  have hB0 : M₀.B (M₀.π c) (M₀.π ⁅d₀, t⁆) = 0 :=
    (Tim79.QuadModel.comm_iff_B M₀ hD.reg hcQ (hXQ hx₀X)).mp hx₀c.symm
  have hBe : M₀.B (M₀.π c) e = 0 := by
    rw [hs, map_smul, smul_eq_mul] at hB0
    exact (mul_eq_zero.mp hB0).resolve_left hs0
  exact (Tim79.QuadModel.centralizer_iff hD.reg hXQ he hcQ).mpr hBe

theorem Sec10Hyp.comm_of_comm_mem_QB (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (htM : t ∈ M) (htQ : t ∉ Q) (ht2 : t * t = 1) {X : Subgroup G} (hX : Ctx M Q Z X)
    (htX : t ∈ QB X) {c : G} (hcQ : c ∈ Q) (hx : ⁅t, c⁆ ∈ QB X) : ∀ e ∈ X, e * c = c * e := by
  obtain ⟨m, hm, hmX⟩ := (H.rootTrans h34 hspread) X hX
  have HX : Sec10Hyp hX n := (H.conj_of_mem hm).of_eq hX rfl rfl rfl hmX
  have htLX : t ∈ LB M Q X := Subgroup.mem_sup_right ⟨htX, htM⟩
  have h5 := HX.toSec5 htLX htQ
  obtain ⟨d₀, hd₀D, hd₀Z⟩ : ∃ d ∈ Q ⊓ QB X, ⁅t, d⁆ ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact htQ (hX.LB_hom_inj h34 h5 ⟨htX, htM⟩ hcon)
  have hZX : Z ⊓ X = ⊥ := hX.inf_eq_bot
  have hVab : ∀ a ∈ Q ⊓ QB X, ∀ b ∈ Q ⊓ QB X, a * b = b * a := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ Z ⊓ X := ⟨comm_mem_Z hc.hyp ha.1 hb.1, hX.QB_comm_mem ha.2 hb.2⟩
    rw [hZX, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hctV : ⁅c, t⁆ ∈ Q ⊓ QB X := by
    refine ⟨hX.comm_mem_Q htM hcQ, ?_⟩
    rw [← commutatorElement_inv]
    exact (QB X).inv_mem hx
  have hd₀W : d₀ ∈ Wt Q (Q ⊓ QB X) :=
    ⟨hd₀D.1, Subgroup.mem_centralizer_iff.mpr fun v hv => hVab v hv d₀ hd₀D⟩
  have hTc := hX.Tt_le_centralizer_of_comm_mem htLX ht2 hcQ hctV
  have hx₀c : ⁅d₀, t⁆ * c = c * ⁅d₀, t⁆ :=
    Subgroup.mem_centralizer_singleton_iff.mp (hTc (Subgroup.mem_sup_left
      (Subgroup.commutator_mem_commutator hd₀W (Subgroup.mem_zpowers t))))
  have hx₀X : ⁅d₀, t⁆ ∈ X := hX.QB_comm_mem hd₀D.2 htX
  have hx₀Z : ⁅d₀, t⁆ ∉ Z := fun h => hd₀Z (by rw [← commutatorElement_inv]; exact Z.inv_mem h)
  have hcX := centralizer_of_comm_mem_QB_of_line hc hX hcQ hd₀D hx₀c hx₀X hx₀Z
  exact fun e' he' => Subgroup.mem_centralizer_iff.mp hcX e' he'

end CFSG.RankThree.GF2n.Stroth80
