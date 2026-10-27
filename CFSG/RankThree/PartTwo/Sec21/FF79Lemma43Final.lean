module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43GoodBeta
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Conj
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma44
import CFSG.GroupTheory.CoprimeHyperplaneCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem conj_cenS {B : Subgroup G} {n σ : G} (hn : n ∈ Nor B) (hσ : σ ∈ CenS B) :
    n⁻¹ * σ * n ∈ CenS B := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : n * y * n⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hn y).mp hy
  have h2 := Subgroup.mem_centralizer_iff.mp hσ _ h1
  calc y * (n⁻¹ * σ * n) = n⁻¹ * ((n * y * n⁻¹) * σ) * n := by group
    _ = n⁻¹ * (σ * (n * y * n⁻¹)) * n := by rw [h2]
    _ = (n⁻¹ * σ * n) * y := by group

theorem orderOf_conj_inv (n σ : G) : orderOf (n⁻¹ * σ * n) = orderOf σ := by
  have := MulEquiv.orderOf_eq (MulAut.conj n⁻¹) σ
  simpa [MulAut.conj_apply] using this

theorem good_B0 {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) {σ : G}
    (hσB : σ ∈ CenS B) (hσo : orderOf σ = 2)
    (hall : ∀ τ ∈ CenS B, orderOf τ = 2 → Good43 τ b ∧ Good43 τ (b₁ * b₂)) :
    ∀ x ∈ Subgroup.closure ({b₁, b₂} : Set G), x ≠ 1 → Good43 σ x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hb₁3, hb₂3, hb₁b₂, hK1, -, -⟩ := sec4_facts h4
  obtain ⟨-, -, -, ⟨n₀, hn₀, h0b, h0b₁, h0b₂⟩, ⟨n₁, hn₁, h1b, h1b₁, h1b₂⟩,
    ⟨n₂, hn₂, h2b, h2b₁, h2b₂⟩⟩ := h4.mono
  obtain ⟨hβ3, hγo⟩ := s43_beta_gamma h4
  have hc : Commute b₁ b₂ := hb₁b₂
  have hall' := fun n (hn : n ∈ Nor B) => hall _ (conj_cenS (n := n) hn hσB)
    (by rw [orderOf_conj_inv, hσo])
  have gb : ∀ n ∈ Nor B, Good43 σ (n * b * n⁻¹) := fun n hn => good43_conj n (hall' n hn).1
  have gβ : ∀ n ∈ Nor B, Good43 σ (n * (b₁ * b₂) * n⁻¹) := fun n hn =>
    good43_conj n (hall' n hn).2
  have g1 : Good43 σ b₁ := h1b ▸ gb n₁ hn₁
  have g2 : Good43 σ b₂ := by
    have := gb (n₂ * n₂) (Subgroup.mul_mem _ hn₂ hn₂)
    have e : (n₂ * n₂) * b * (n₂ * n₂)⁻¹ = b₂ := by
      calc (n₂ * n₂) * b * (n₂ * n₂)⁻¹ = n₂ * (n₂ * b * n₂⁻¹) * n₂⁻¹ := by group
        _ = n₂ * b₁ * n₂⁻¹ := by rw [h2b]
        _ = b₂ := h2b₁
    rwa [e] at this
  have g3 : Good43 σ (b₁ * b₂) := by
    have := gβ 1 (Subgroup.one_mem _)
    simpa using this
  have g4 : Good43 σ (b₁ ^ 2 * b₂) := by
    have hn : n₁ * n₀ * n₁⁻¹ ∈ Nor B :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hn₁ hn₀) (Subgroup.inv_mem _ hn₁)
    have this := gβ _ hn
    have e1 : n₁⁻¹ * b₁ * n₁ = b := by rw [← h1b]; group
    have e2 : n₁⁻¹ * b₂ * n₁ = b₂ := by
      calc n₁⁻¹ * b₂ * n₁ = n₁⁻¹ * (n₁ * b₂ * n₁⁻¹) * n₁ := by rw [h1b₂]
        _ = b₂ := by group
    have f1 : (n₁ * n₀ * n₁⁻¹) * b₁ * (n₁ * n₀ * n₁⁻¹)⁻¹ = b₁⁻¹ := by
      calc (n₁ * n₀ * n₁⁻¹) * b₁ * (n₁ * n₀ * n₁⁻¹)⁻¹
          = n₁ * (n₀ * (n₁⁻¹ * b₁ * n₁) * n₀⁻¹) * n₁⁻¹ := by group
        _ = n₁ * (n₀ * b * n₀⁻¹) * n₁⁻¹ := by rw [e1]
        _ = n₁ * b⁻¹ * n₁⁻¹ := by rw [h0b]
        _ = (n₁ * b * n₁⁻¹)⁻¹ := by group
        _ = b₁⁻¹ := by rw [h1b]
    have f2 : (n₁ * n₀ * n₁⁻¹) * b₂ * (n₁ * n₀ * n₁⁻¹)⁻¹ = b₂ := by
      calc (n₁ * n₀ * n₁⁻¹) * b₂ * (n₁ * n₀ * n₁⁻¹)⁻¹
          = n₁ * (n₀ * (n₁⁻¹ * b₂ * n₁) * n₀⁻¹) * n₁⁻¹ := by group
        _ = n₁ * (n₀ * b₂ * n₀⁻¹) * n₁⁻¹ := by rw [e2]
        _ = n₁ * b₂ * n₁⁻¹ := by rw [h0b₂]
        _ = b₂ := h1b₂
    have e3 : (n₁ * n₀ * n₁⁻¹) * (b₁ * b₂) * (n₁ * n₀ * n₁⁻¹)⁻¹ = b₁⁻¹ * b₂ := by
      calc (n₁ * n₀ * n₁⁻¹) * (b₁ * b₂) * (n₁ * n₀ * n₁⁻¹)⁻¹
          = ((n₁ * n₀ * n₁⁻¹) * b₁ * (n₁ * n₀ * n₁⁻¹)⁻¹) *
            ((n₁ * n₀ * n₁⁻¹) * b₂ * (n₁ * n₀ * n₁⁻¹)⁻¹) := by group
        _ = b₁⁻¹ * b₂ := by rw [f1, f2]
    have e4 : b₁⁻¹ = b₁ ^ 2 := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ']; exact hb₁3
    rwa [e3, e4] at this
  have hγ3 : (b₁ ^ 2 * b₂) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (b₁ ^ 2 * b₂)
    rwa [hγo] at this
  have o1 : orderOf b₁ = 3 := (s43_orders h4).1
  have o2 : orderOf b₂ = 3 := (s43_orders h4).2.1
  have z2 : ∀ y : G, y ^ (2 : ℤ) = y ^ 2 := fun y => by rw [zpow_two, pow_two]
  have hmul : ∀ y : G, y ^ 3 = 1 → y * y ^ 2 = 1 := fun y hy => by
    rw [← pow_succ']; exact hy
  intro x hx hx1
  have hx' : x ∈ Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ := by
    refine ((Subgroup.closure_le _).mpr ?_) hx
    rintro y (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨u, hu, v, hv, rfl⟩ := s43_mem_sup_of_comm (A := Subgroup.zpowers b₁)
    (H := Subgroup.zpowers b₂)
    (fun a ha h hh => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((hc.zpow_left i).zpow_right j).eq) hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hi : b₁ ^ i = b₁ ^ (i % 3) := by
    have := zpow_mod_orderOf b₁ i
    rw [o1] at this; simpa using this.symm
  have hj : b₂ ^ j = b₂ ^ (j % 3) := by
    have := zpow_mod_orderOf b₂ j
    rw [o2] at this; simpa using this.symm
  rw [hi, hj] at hx1 ⊢
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h <;>
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h' | h' | h' <;>
    rw [h, h'] at hx1 ⊢ <;> simp only [zpow_zero, zpow_one, z2, mul_one, one_mul]
  · simp at hx1
  · exact g2
  · exact g2.of_mul_eq_one (hmul _ hb₂3)
  · exact g1
  · exact g3
  · have e : b₁ * b₂ ^ 2 = (b₁ ^ 2 * b₂) ^ 2 := by
      rw [(hc.pow_left 2).mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hb₁3,
        one_mul, pow_one]
    rw [e]
    exact g4.of_mul_eq_one (hmul _ hγ3)
  · exact g1.of_mul_eq_one (hmul _ hb₁3)
  · exact g4
  · have e : b₁ ^ 2 * b₂ ^ 2 = (b₁ * b₂) ^ 2 := (hc.mul_pow 2).symm
    rw [e]
    exact g3.of_mul_eq_one (hmul _ hβ3)

theorem zpow_eq_one_or_self' {σ : G} (hσ : orderOf σ = 2) (k : ℤ) : σ ^ k = 1 ∨ σ ^ k = σ := by
  have h := zpow_mod_orderOf σ k
  rw [hσ] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h]; simp [h0]
  · right
    rw [← h]; simp [h1]

theorem cen_isPLocal {σ : G} (hσ : orderOf σ = 2) : IsPLocal 2 (Cen σ) := by
  have hσ1 : σ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hσ; omega
  refine ⟨Subgroup.zpowers σ, ?_, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ, pow_one]),
    ?_⟩
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · refine le_antisymm ?_ ?_
    · show Subgroup.centralizer ({σ} : Set G) ≤ _
      rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_le_normalizer _
    · intro g hg
      have h1 : g * σ * g⁻¹ ∈ Subgroup.zpowers σ :=
        (Subgroup.mem_normalizer_iff.mp hg σ).mp (Subgroup.mem_zpowers σ)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      rcases zpow_eq_one_or_self' hσ k with h2 | h2
      · exfalso
        rw [h2] at hk
        apply hσ1
        calc σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
          _ = 1 := by rw [← hk]; group
      · rw [h2] at hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc g * σ = (g * σ * g⁻¹) * g := by group
          _ = σ * g := by rw [← hk]

theorem Op_isPGroup (p : ℕ) (H : Subgroup G) : IsPGroup p (Op p H) := by
  intro z
  obtain ⟨z', hz', hzz⟩ := Subgroup.mem_map.mp z.2
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥H)) ⟨z', hz'⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun w : ↥(pCore p ↥H) => ((w : ↥H) : G)) hk
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
  rw [← hzz]
  simpa using this

theorem Op_conj_mem {p : ℕ} {H : Subgroup G} {g z : G} (hg : g ∈ H) (hz : z ∈ Op p H) :
    g * z * g⁻¹ ∈ Op p H := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  haveI : (pCore p ↥H).Normal := CFSG.pCore_normal
  exact Subgroup.Normal.conj_mem inferInstance z' hz' ⟨g, hg⟩

theorem Op_le (p : ℕ) (H : Subgroup G) : Op p H ≤ H := Subgroup.map_subtype_le _

theorem no_involution {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂)
    (hall : ∀ τ ∈ CenS B, orderOf τ = 2 → Good43 τ b ∧ Good43 τ (b₁ * b₂)) {σ : G}
    (hσB : σ ∈ CenS B) (hσo : orderOf σ = 2) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hb₁3, hb₂3, hb₁b₂, hK1, hcard, hE3⟩ := sec4_facts h4
  have hgood := good_B0 h4 hσB hσo hall
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  set E : Subgroup G := Subgroup.closure ({b₁, b₂} : Set G) with hEdef
  set R : Subgroup G := Op 2 (Cen σ) with hRdef
  have hEB : E ≤ B := by
    rw [hEdef, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hb₁B
    · exact hb₂B
  have hEcen : E ≤ Cen σ := fun x hx =>
    s43_mem_cen (Subgroup.mem_centralizer_iff.mp hσB x (hEB hx)).symm
  have hEcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv => by
    have := s43_Bcomm h4
    exact this u (hEB hu) v (hEB hv)
  have hE : CFSG.Open.IsElemAbelian 3 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hEcomm a.1 a.2 b.1 b.2)⟩⟩, hE3⟩
  have hRp : IsPGroup 2 R := Op_isPGroup 2 _
  have hRnor : Cen σ ≤ Nor R := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => Op_conj_mem hc hh, fun hh => ?_⟩
    have := Op_conj_mem (Subgroup.inv_mem _ hc) hh
    simpa [mul_assoc] using this
  have h3R : ¬ 3 ∣ Nat.card R := by
    obtain ⟨a, ha⟩ := hRp.exists_card_eq
    rw [ha]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hfaith : ¬ E ≤ CenS R := by
    intro hcon
    have hb₁E : b₁ ∈ E := Subgroup.subset_closure (by simp)
    have hb₁σ : b₁ ∈ Cen σ := hEcen hb₁E
    have hloc := cen_isPLocal hσo
    have hchar := h4.char2 (Cen σ) hloc
    have hmem : (⟨b₁, hb₁σ⟩ : ↥(Cen σ)) ∈ pCore 2 ↥(Cen σ) := by
      refine hchar ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwR : (w : G) ∈ R := Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcon hb₁E) _ hwR)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(Cen σ))) ⟨_, hmem⟩
    have h2 : Is2El b₁ := ⟨k, by
      have := congrArg (fun w : ↥(pCore 2 ↥(Cen σ)) => ((w : ↥(Cen σ)) : G)) hk
      simpa using this⟩
    have hb1 : b₁ = 1 := h2.eq_one_of_pow_odd (by decide : Odd 3) hb₁3
    have ho := (s43_orders h4).1
    rw [hb1, orderOf_one] at ho
    omega
  obtain ⟨Y, hYE, hYc, hYn⟩ := CFSG.GroupTheory.exists_hyperplane_not_le_centralizer_inf_centralizer
    (r := 3) hE hcard.ge (hEcen.trans hRnor) h3R hfaith
  apply hYn
  obtain ⟨x, hxY, hx1⟩ : ∃ x ∈ Y, x ≠ 1 := by
    by_contra hno
    push Not at hno
    have hYbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).mpr hno
    rw [hYbot, Subgroup.card_bot, hcard] at hYc
    omega
  have hG := hgood x (hYE hxY) hx1
  have hQ₁ : R ⊓ Cen x ≤ Subgroup.zpowers σ := by
    refine hG (R ⊓ Cen x) (hRp.to_le inf_le_left)
      (fun y hy => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).2,
        Op_le 2 _ (Subgroup.mem_inf.mp hy).1⟩) ?_
    intro c hc q hq
    obtain ⟨hcx, hcσ⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨hqR, hqx⟩ := Subgroup.mem_inf.mp hq
    exact Subgroup.mem_inf.mpr ⟨Op_conj_mem hcσ hqR,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcx hqx) (Subgroup.inv_mem _ hcx)⟩
  intro y hy z hz
  have hz' : z ∈ R ⊓ Cen x := Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1,
    s43_mem_cen (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 x hxY)⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hQ₁ hz')
  exact ((show Commute σ y from s43_cen_comm (hEcen hy)).zpow_left i).eq

end CFSG.RankThree.PartTwo.Sec21.FF79
