module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre41b

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

def mulSub (A C : Subgroup G) (hn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) : Subgroup G where
  carrier := {x | ∃ a ∈ A, ∃ c ∈ C, x = a * c}
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨a', ha', c', hc', rfl⟩
    exact ⟨a * (c * a' * c⁻¹), mul_mem ha (hn c hc a' ha'), c * c', mul_mem hc hc', by group⟩
  inv_mem' := by
    rintro _ ⟨a, ha, c, hc, rfl⟩
    exact ⟨c⁻¹ * a⁻¹ * c⁻¹⁻¹, hn c⁻¹ (inv_mem hc) a⁻¹ (inv_mem ha), c⁻¹, inv_mem hc, by group⟩

theorem le_mulSub_left {A C : Subgroup G} {hn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A} :
    A ≤ mulSub A C hn := fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩

theorem le_mulSub_right {A C : Subgroup G} {hn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A} :
    C ≤ mulSub A C hn := fun c hc => ⟨1, one_mem _, c, hc, by simp⟩

theorem coprime_mulSub {A C : Subgroup G} (hn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) {p : ℕ}
    (hA : Nat.Coprime p (Nat.card A)) (hC : Nat.Coprime p (Nat.card C)) :
    Nat.Coprime p (Nat.card (mulSub A C hn)) := by
  set W := mulSub A C hn with hW
  have hAW : A ≤ W := le_mulSub_left
  have hCW : C ≤ W := le_mulSub_right
  have hnorm : (A.subgroupOf W).Normal := ⟨fun x hx w => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨a, ha, c, hc, hw⟩ := w.2
    show (w : G) * (x : G) * (w : G)⁻¹ ∈ A
    have e : (w : G) * (x : G) * (w : G)⁻¹ = a * (c * (x : G) * c⁻¹) * a⁻¹ := by
      rw [hw]; group
    rw [e]
    exact mul_mem (mul_mem ha (hn c hc _ hx)) (inv_mem ha)⟩
  let f : ↥C →* ↥W ⧸ A.subgroupOf W :=
    (QuotientGroup.mk' (A.subgroupOf W)).comp (Subgroup.inclusion hCW)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, c, hc, hw⟩ := w.2
    refine ⟨⟨c, hc⟩, ?_⟩
    show (QuotientGroup.mk (⟨c, hCW hc⟩ : W) : ↥W ⧸ A.subgroupOf W) = QuotientGroup.mk w
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show c⁻¹ * (w : G) ∈ A
    rw [hw]
    have := hn c⁻¹ (inv_mem hc) a ha
    simpa [mul_assoc] using this
  have hdvd : Nat.card (↥W ⧸ A.subgroupOf W) ∣ Nat.card C := Subgroup.card_dvd_of_surjective hf
  have hcard := Subgroup.card_mul_index (A.subgroupOf W)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv, Subgroup.index_eq_card] at hcard
  rw [← hcard]
  exact hA.mul_right (Nat.Coprime.coprime_dvd_right hdvd hC)

theorem S41_first (h23 : FF84_2_3) (h : FF84Sec4 b L B K b₁ b₂)
    (hA : A8Model L) :
    ∀ d ∈ Cen (b * b₁), ∃ y ∈ Opp 3 (Cen (b * b₁)),
      ∃ n ∈ Cen (b * b₁) ⊓ Nor (Subgroup.closure ({b, b₁} : Set G)), d = y * n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D₀, hDD, hnorm, hrel, -, hsyl⟩ := S41_D0 h
  have hne : D₀ ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.relIndex_top_left] at hrel
    exact absurd hrel (by norm_num)
  have hn : ∀ g ∈ Cen (b * b₁), ∀ x ∈ D₀, g * x * g⁻¹ ∈ D₀ := by
    intro g hg x hx
    have := hnorm.conj_mem ⟨x, hDD hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hn₁, hn₂, hP₁J₁, hP₂J₂, hJO⟩ := S41_J h23 h hDD hne hsyl
  have hdec := D₀_decomp h hA hDD hJ₁ hJ₂ hn₁ hn₂ hP₁J₁ hP₂J₂ hJO hsyl
  intro d hd
  obtain ⟨d₀, hd₀, n, hnB, rfl⟩ :=
    exists_mul_of_index_three hDD hn (B_le_cen_bb₁ h) hrel (B_not_le_D₀ h hsyl) d hd
  obtain ⟨o, ho, m, hm, rfl⟩ := hdec d₀ hd₀
  refine ⟨o, FF79.L14.Opp_le_Opp_of_normalized hDD hn ho, m * n, ?_, by group⟩
  obtain ⟨hmD, hmN⟩ := Subgroup.mem_inf.1 hm
  have h1 : m ∈ Cen (b * b₁) ⊓ Nor (Subgroup.zpowers (b * b₁ ^ 2)) :=
    Subgroup.mem_inf.2 ⟨hDD hmD, hmN⟩
  have h2 : n ∈ Cen (b * b₁) ⊓ Nor (Subgroup.zpowers (b * b₁ ^ 2)) :=
    Subgroup.mem_inf.2 ⟨B_le_cen_bb₁ h hnB, B_le_nor_P₁ h hnB⟩
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (mul_mem h1 h2)).1, nor_P₁_le_nor_E h (mul_mem h1 h2)⟩

theorem S41_second (h23 : FF84_2_3) (h : FF84Sec4 b L B K b₁ b₂)
    (hA : A8Model L) : Opp 3 (Cen b) ≤ Opp 3 (Cen (b * b₁)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfirst := S41_first h23 h hA
  set D := Cen (b * b₁) with hD
  set Y := Opp 3 D with hY
  set E := Subgroup.closure ({b, b₁} : Set G) with hE
  set X := Opp 3 (Cen b) with hX
  have hYn : ∀ g ∈ D, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun g hg y hy => FF79.L14.Opp_conj_mem hg hy
  set M : Subgroup G := D ⊓ Subgroup.centralizer (E : Set G) with hM
  have hMY : ∀ m ∈ M, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y := fun m hm y hy => hYn m (Subgroup.mem_inf.1 hm).1 y hy
  have hXb : ∀ x ∈ X, x ∈ Cen b := fun x hx => Opp_le 3 _ hx
  have hXM : X ≤ M := by
    intro x hx
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 (hXb x hx)
    have hxb₁ : x * b₁ = b₁ * x := Subgroup.mem_centralizer_singleton_iff.1 (S41_cen_X hA h hx)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hD, Subgroup.mem_centralizer_singleton_iff]
      rw [← mul_assoc, hxb, mul_assoc, hxb₁, ← mul_assoc]
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hle : E ≤ Subgroup.centralizer ({x} : Set G) := by
        refine (Subgroup.closure_le _).2 ?_
        rintro z (rfl | hz)
        · exact Subgroup.mem_centralizer_singleton_iff.2 hxb.symm
        · rw [Set.mem_singleton_iff.1 hz]
          exact Subgroup.mem_centralizer_singleton_iff.2 hxb₁.symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
  have hMD : M ≤ D := inf_le_left
  have hXD : X ≤ D := hXM.trans hMD
  have hMX : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
    intro m hm x hx
    have hmb : m ∈ Cen b := by
      have hbE : b ∈ E := Subgroup.subset_closure (by simp)
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hm).2 b hbE
      exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
    exact FF79.L14.Opp_conj_mem hmb hx
  have hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := fun x hx y hy => hYn x (hXD hx) y hy
  set Z := mulSub Y M hMY with hZ
  set W := mulSub Y X hXY with hW
  have hYD : Y ≤ D := Opp_le 3 D
  have hZD : Z ≤ D := by
    rintro _ ⟨a, ha, c, hc, rfl⟩
    exact mul_mem (hYD ha) (hMD hc)
  have hYZ : Y ≤ Z := le_mulSub_left
  have hYW : Y ≤ W := le_mulSub_left
  have hXW : X ≤ W := le_mulSub_right
  have hWZ : W ≤ Z := by
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x, hXM hx, rfl⟩
  have hMn : ∀ n ∈ D ⊓ Nor E, ∀ z ∈ Z, n * z * n⁻¹ ∈ Z := by
    intro n hn z hz
    obtain ⟨a, ha, m, hm, rfl⟩ := hz
    obtain ⟨hnD, hnN⟩ := Subgroup.mem_inf.1 hn
    have e : n * (a * m) * n⁻¹ = (n * a * n⁻¹) * (n * m * n⁻¹) := by group
    rw [e]
    refine ⟨n * a * n⁻¹, hYn n hnD a ha, n * m * n⁻¹, ?_, rfl⟩
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hnD (hMD hm)) (inv_mem hnD), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e' he'
    have hmc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hm).2
    have hmem : n⁻¹ * e' * n ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 hnN (n⁻¹ * e' * n)).2
      rw [show n * (n⁻¹ * e' * n) * n⁻¹ = e' by group] at this
      exact this he'
    have key := hmc _ hmem
    have h1 : e' * (n * m * n⁻¹) = n * ((n⁻¹ * e' * n) * m) * n⁻¹ := by group
    have h2 : n * m * n⁻¹ * e' = n * (m * (n⁻¹ * e' * n)) * n⁻¹ := by group
    rw [h1, h2, key]
  have hZn : ∀ d ∈ D, ∀ z ∈ Z, d * z * d⁻¹ ∈ Z := by
    intro d hd z hz
    obtain ⟨y, hy, n, hn, rfl⟩ := hfirst d hd
    have e : y * n * z * (y * n)⁻¹ = y * (n * z * n⁻¹) * y⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hYZ hy) (hMn n hn z hz)) (inv_mem (hYZ hy))
  have hWm : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W := by
    intro m hm w hw
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    have e : m * (a * x) * m⁻¹ = (m * a * m⁻¹) * (m * x * m⁻¹) := by group
    rw [e]
    exact ⟨m * a * m⁻¹, hMY m hm a ha, m * x * m⁻¹, hMX m hm x hx, rfl⟩
  have hWn : ∀ z ∈ Z, ∀ w ∈ W, z * w * z⁻¹ ∈ W := by
    intro z hz w hw
    obtain ⟨a, ha, m, hm, rfl⟩ := hz
    have e : a * m * w * (a * m)⁻¹ = a * (m * w * m⁻¹) * a⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hYW ha) (hWm m hm w hw)) (inv_mem (hYW ha))
  have hWc : Nat.Coprime 3 (Nat.card W) :=
    coprime_mulSub hXY (FF79.L14.Opp_coprime 3 D) (FF79.L14.Opp_coprime 3 (Cen b))
  have h1 : W ≤ Opp 3 Z := FF79.L14.le_Opp_of_normalized hWZ hWn hWc
  have h2 : Opp 3 Z ≤ Opp 3 D := FF79.L14.Opp_le_Opp_of_normalized hZD hZn
  exact hXW.trans (h1.trans h2)

theorem S41_main (h23 : FF84_2_3) (h : FF84Sec4 b L B K b₁ b₂)
    (hA : A8Model L) :
    setMul (Opp 3 (Cen (b * b₁))) (Cen (b * b₁) ⊓ Nor (Subgroup.closure {b, b₁})) =
        (Cen (b * b₁) : Set G) ∧
      Opp 3 (Cen b) ≤ Opp 3 (Cen (b * b₁)) := by
  refine ⟨?_, S41_second h23 h hA⟩
  ext d
  constructor
  · rintro ⟨y, hy, n, hn, rfl⟩
    exact mul_mem (Opp_le 3 _ hy) (Subgroup.mem_inf.1 hn).1
  · intro hd
    obtain ⟨y, hy, n, hn, rfl⟩ := S41_first h23 h hA d hd
    exact ⟨y, hy, n, hn, rfl⟩

theorem ff84_4_1
    (h23 : FF84_2_3) :
    FF84_4_1 := fun _ _ _ _ _ _ _ _ _ h =>
  S41_main h23 h (a8Model_of_hyp h.hyp)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
