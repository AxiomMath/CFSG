module

public import CFSG.RankThree.GF2n.Smith81.LinTLOfConj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

private theorem LinSetup.facts_card (hS : LinSetup M Q Z B n V₁ V₂) :
    Z ≤ V₁ ∧ V₁ ≤ Q ∧ Z ≤ V₂ ∧ V₂ ≤ Q ∧ V₁ ⊓ V₂ = Z ∧
      Lgen M (LB M Q B) ≤ Subgroup.normalizer (V₁ : Set G) ∧
      Lgen M (LB M Q B) ≤ Subgroup.normalizer (V₂ : Set G) := by
  obtain ⟨K, _, _, -, φ, -, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, -, hs₁, hs₂, -, -⟩ := hS
  obtain ⟨hN₁, -⟩ := hs₁
  obtain ⟨hN₂, -⟩ := hs₂
  exact ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hN₁, hN₂⟩

theorem card_comm_sup_le_of_transv (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    {y : G} (hy2 : y * y = 1) (hy₁ : y ∈ Subgroup.normalizer (V₁ : Set G))
    (hy₂ : y ∈ Subgroup.normalizer (V₂ : Set G))
    (h1 : HasDimOn V₁ Z 1 y) (h2 : HasDimOn V₂ Z 1 y) :
    Nat.card ↥(⁅Q, Subgroup.zpowers y⁆ ⊔ Z) ≤ Nat.card Z ^ 3 := by
  have H := hc.hyp
  obtain ⟨hZ₁, hV₁Q, hZ₂, hV₂Q, hint, -, -⟩ := hS.facts_card
  have hQ := LinSetup.exists_mul H hS
  set P₁ : Subgroup G := ⁅V₁, Subgroup.zpowers y⁆ ⊔ Z with hP₁
  set P₂ : Subgroup G := ⁅V₂, Subgroup.zpowers y⁆ ⊔ Z with hP₂
  have hP₁V : P₁ ≤ V₁ := sup_le (commutator_zpowers_le hy₁) hZ₁
  have hP₂V : P₂ ≤ V₂ := sup_le (commutator_zpowers_le hy₂) hZ₂
  have hZP₁ : Z ≤ P₁ := le_sup_right
  have hZP₂ : Z ≤ P₂ := le_sup_right
  have hP₁₂ : P₁ ⊓ P₂ = Z :=
    le_antisymm ((inf_le_inf hP₁V hP₂V).trans hint.le) (le_inf hZP₁ hZP₂)
  have hnorm : P₂ ≤ Subgroup.normalizer (P₁ : Set G) :=
    (hP₂V.trans hV₂Q).trans (Q_le_normalizer_of_Z_le H hZP₁ (hP₁V.trans hV₁Q))
  have hprod := card_sup_mul_card_inf_of_normalizer hnorm
  rw [hP₁₂] at hprod
  have hc₁ : Nat.card P₁ = Nat.card Z ^ 2 := h1
  have hc₂ : Nat.card P₂ = Nat.card Z ^ 2 := h2
  have hq : 0 < Nat.card Z := by have := H.q4; omega
  have hsup : Nat.card ↥(P₁ ⊔ P₂) = Nat.card Z ^ 3 := by
    rw [hc₁, hc₂] at hprod
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [hprod]
    ring
  have hgen : ∀ q ∈ Q, ⁅q, y⁆ ∈ P₁ ⊔ P₂ := by
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := hQ q hq
    have hbx : ⁅b, y⁆ ∈ P₂ :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hb (Subgroup.mem_zpowers y))
    have hax : ⁅a, y⁆ ∈ P₁ :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers y))
    have hbxQ : ⁅b, y⁆ ∈ Q := hV₂Q (hP₂V hbx)
    have hz : ⁅a, ⁅b, y⁆⁆ ∈ Z := comm_mem_Z H (hV₁Q ha) hbxQ
    have e : ⁅a * b, y⁆ = (⁅a, ⁅b, y⁆⁆ * (⁅b, y⁆ * ⁅a, y⁆ * ⁅b, y⁆⁻¹)) * ⁅b, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hb' : ⁅b, y⁆ ∈ P₁ ⊔ P₂ := Subgroup.mem_sup_right hbx
    have ha' : ⁅a, y⁆ ∈ P₁ ⊔ P₂ := Subgroup.mem_sup_left hax
    have hz' : ⁅a, ⁅b, y⁆⁆ ∈ P₁ ⊔ P₂ := Subgroup.mem_sup_left (hZP₁ hz)
    exact (P₁ ⊔ P₂).mul_mem ((P₁ ⊔ P₂).mul_mem hz' ((P₁ ⊔ P₂).mul_mem
      ((P₁ ⊔ P₂).mul_mem hb' ha') ((P₁ ⊔ P₂).inv_mem hb'))) hb'
  have hcomm : ⁅Q, Subgroup.zpowers y⁆ ≤ P₁ ⊔ P₂ := by
    rw [commutator_zpowers_eq_closure hy2, Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    exact hgen q hq
  rw [← hsup]
  exact Subgroup.card_le_of_le (sup_le hcomm (hZP₁.trans le_sup_left))

theorem card_Q_le_centralizer_mul (H : StrothHyp M Q Z) {y : G} (hyM : y ∈ M) (hy2 : y * y = 1) :
    Nat.card Q ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) *
      Nat.card ↥(⁅Q, Subgroup.zpowers y⁆ ⊔ Z) := by
  set C : Subgroup G := Q ⊓ Subgroup.centralizer ({y} : Set G) with hC
  set P : Subgroup G := ⁅Q, Subgroup.zpowers y⁆ ⊔ Z with hP
  have hmem : ∀ q : Q, ⁅(q : G), y⁆ ∈ P := fun q =>
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator q.2 (Subgroup.mem_zpowers y))
  have hiff : ∀ a b : G, ⁅a, y⁆ = ⁅b, y⁆ ↔ a⁻¹ * b * y = y * (a⁻¹ * b) := by
    intro a b
    simp only [commutatorElement_def]
    constructor
    · intro h
      have h3 : a * y * a⁻¹ = b * y * b⁻¹ := mul_right_cancel h
      calc a⁻¹ * b * y = a⁻¹ * (b * y * b⁻¹) * b := by group
        _ = a⁻¹ * (a * y * a⁻¹) * b := by rw [h3]
        _ = y * (a⁻¹ * b) := by group
    · intro h
      have h3 : b * y * b⁻¹ = a * y * a⁻¹ := by
        calc b * y * b⁻¹ = a * (a⁻¹ * b * y) * b⁻¹ := by group
          _ = a * (y * (a⁻¹ * b)) * b⁻¹ := by rw [h]
          _ = a * y * a⁻¹ := by group
      rw [h3]
  let f : Q → P := fun q => ⟨⁅(q : G), y⁆, hmem q⟩
  have hf : ∀ a b : Q, QuotientGroup.leftRel (C.subgroupOf Q) a b → f a = f b := by
    intro a b hab
    have hab' : a⁻¹ * b ∈ C.subgroupOf Q := QuotientGroup.leftRel_apply.mp hab
    have hab'' : (a : G)⁻¹ * b ∈ C := hab'
    exact Subtype.ext ((hiff a b).mpr (Subgroup.mem_centralizer_singleton_iff.mp hab''.2))
  let F : Q ⧸ C.subgroupOf Q → P := Quotient.lift f hf
  have hinj : Function.Injective F := by
    intro u v huv
    induction u using QuotientGroup.induction_on with | H a => ?_
    induction v using QuotientGroup.induction_on with | H b => ?_
    have hab : f a = f b := huv
    have hab' : ⁅(a : G), y⁆ = ⁅(b : G), y⁆ := congrArg Subtype.val hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (a : G)⁻¹ * (b : G) ∈ C
    exact ⟨Q.mul_mem (Q.inv_mem a.2) b.2,
      Subgroup.mem_centralizer_singleton_iff.mpr ((hiff a b).mp hab')⟩
  have hidx : (C.subgroupOf Q).index ≤ Nat.card P := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_le_card_of_injective F hinj
  have hCQ : Nat.card ↥(C.subgroupOf Q) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card Q = Nat.card ↥(C.subgroupOf Q) * (C.subgroupOf Q).index :=
        (Subgroup.card_mul_index _).symm
    _ ≤ Nat.card C * Nat.card P := by rw [hCQ]; exact Nat.mul_le_mul_left _ hidx

theorem card_Lx_ge (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n)
    {x : G} (hs : Sit M Q Z X x) {A : Subgroup G} (hA : IsZConjugate Z A)
    (hAQ : A ≤ Q) (hAX : A ≤ QB X) :
    Nat.card Z ^ (2 * n - 2) ≤ Nat.card ↥(Lx M X) := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Z_ne_bot H)
    exact ⟨z, hz, fun h => hz1 (Subtype.ext h)⟩
  have hzN : z₀ ∈ Subgroup.normalizer (conjSubgroup g Z : Set G) := by
    rw [← hg]; exact Z_le_normalizer_X h12 hz₀
  have hzQ : z₀ ∉ QB (conjSubgroup g Z) := by
    rw [← hg]
    intro h
    have hmem : z₀ ∈ Z ⊓ QB X := ⟨hz₀, h⟩
    rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at hmem
    exact hz₀1 hmem
  have hsy : Sit M Q Z (conjSubgroup g⁻¹ Z) (g⁻¹ * z₀ * g) :=
    sit_conj_back H (IsZConjugate.self Z) hz₀ hz₀1 hzN hzQ
  have hy2 : (g⁻¹ * z₀ * g) * (g⁻¹ * z₀ * g) = 1 := hsy.x_sq
  have hA'Z : IsZConjugate Z (conjSubgroup g⁻¹ A) := hA.conj g⁻¹
  have hA'Q : conjSubgroup g⁻¹ A ≤ Q := by
    intro a ha
    rw [mem_conjSubgroup] at ha
    have h1 := hAX ha
    rw [hQB, mem_conjSubgroup] at h1
    have e : g⁻¹ * ((g⁻¹)⁻¹ * a * g⁻¹) * g = a := by group
    rwa [e] at h1
  have hA'Y : conjSubgroup g⁻¹ A ≤ QB (conjSubgroup g⁻¹ Z) := by
    rw [QB_conj_eq H g⁻¹]
    exact Subgroup.map_mono hAQ
  obtain ⟨hA'ne, -, hYL⟩ := lin29_of_sit hsy hA'Z hA'Q hA'Y
  have hcA' : Ctx M Q Z (conjSubgroup g⁻¹ A) := ⟨H, hA'Z, hA'Q, hA'ne⟩
  obtain ⟨hA'V, htr⟩ := hS.transv_of_conj hc hn hcA'
  have hLg : LB M Q (conjSubgroup g⁻¹ A) ≤ Lgen M (LB M Q B) := by
    rcases hA'V with h | h
    · exact hS.LB_le_Lgen_of_le_V₁ hc hn hcA' h
    · exact hS.symm.LB_le_Lgen_of_le_V₁ hc hn hcA' h
  obtain ⟨-, -, -, -, -, hN₁, hN₂⟩ := hS.facts_card
  have hyL : g⁻¹ * z₀ * g ∈ LB M Q (conjSubgroup g⁻¹ A) := hYL hsy.mem
  obtain ⟨hd₁, hd₂, -⟩ := htr _ hyL hsy.notQ
  have hP := card_comm_sup_le_of_transv hc hS hy2 (hN₁ (hLg hyL)) (hN₂ (hLg hyL)) hd₁ hd₂
  have hCQ := card_Q_le_centralizer_mul H hsy.memM hy2
  have hW : Nat.card Q = Nat.card Z ^ (2 * n + 1) := LinSetup.width H hS
  have hq : 0 < Nat.card Z := by have := H.q4; omega
  have hq3 : 0 < Nat.card Z ^ 3 := pow_pos hq 3
  have hmul : Nat.card Z ^ (2 * n - 2) * Nat.card Z ^ 3 ≤
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({g⁻¹ * z₀ * g} : Set G)) * Nat.card Z ^ 3 := by
    calc Nat.card Z ^ (2 * n - 2) * Nat.card Z ^ 3 = Nat.card Z ^ (2 * n + 1) := by
          rw [← pow_add]; congr 1; omega
      _ = Nat.card Q := hW.symm
      _ ≤ _ := hCQ
      _ ≤ _ := Nat.mul_le_mul_left _ hP
  have hC := Nat.le_of_mul_le_mul_right hmul hq3
  have hconj : conjSubgroup g (Q ⊓ Subgroup.centralizer ({g⁻¹ * z₀ * g} : Set G)) ≤ Lx M X := by
    intro c' hc'
    rw [mem_conjSubgroup] at hc'
    obtain ⟨hcQ, hcC⟩ := hc'
    have hcy : g⁻¹ * c' * g * (g⁻¹ * z₀ * g) = g⁻¹ * z₀ * g * (g⁻¹ * c' * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp hcC
    have hcz : c' * z₀ = z₀ * c' := by
      calc c' * z₀ = g * (g⁻¹ * c' * g * (g⁻¹ * z₀ * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * z₀ * g * (g⁻¹ * c' * g)) * g⁻¹ := by rw [hcy]
        _ = z₀ * c' := by group
    refine ⟨?_, mem_M_of_commute_Z H hz₀ hz₀1 hcz⟩
    show c' ∈ QB X
    rw [hQB, mem_conjSubgroup]
    exact hcQ
  calc Nat.card Z ^ (2 * n - 2)
      ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({g⁻¹ * z₀ * g} : Set G)) := hC
    _ = Nat.card ↥(conjSubgroup g (Q ⊓ Subgroup.centralizer ({g⁻¹ * z₀ * g} : Set G))) :=
        (card_conjSubgroup g _).symm
    _ ≤ Nat.card ↥(Lx M X) := Subgroup.card_le_of_le hconj

end CFSG.RankThree.GF2n.Smith81
