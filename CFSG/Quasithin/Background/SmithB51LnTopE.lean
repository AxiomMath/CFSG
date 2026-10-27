module

public import CFSG.Quasithin.Background.ConjTransportRk
public import CFSG.Quasithin.Background.SmithB51LnSub
public import CFSG.Quasithin.Background.SmithB51LnSum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix Module
open scoped Matrix

section Conj

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {n : ℕ}

theorem inner_of_conj {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hπ : Function.Bijective π)
    {g : MulAut V} (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L)
    {P : GL (Fin n) (ZMod 2)}
    (hP : ∀ γ, mat (conjSL hπ hgL hgL' γ) = (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat γ *
      ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) :
    ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹ := by
  have hp : ∀ γ, conjSL hπ hgL hgL' γ = ofGL P * γ * (ofGL P)⁻¹ := by
    intro γ
    apply mat_injective
    rw [hP γ, mat_mul, mat_mul, mat_ofGL]
    rfl
  refine ⟨((π (ofGL P) : ↥L) : MulAut V), (π (ofGL P)).2, fun x hx => ?_⟩
  obtain ⟨γ, hγ⟩ := hπ.2 ⟨x, hx⟩
  have h1 := conjSL_spec hπ hgL hgL' γ
  rw [hp, map_mul, map_mul, hγ] at h1
  rw [← h1]
  simp

theorem conjSL_mul {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hπ : Function.Bijective π)
    {g₁ g₂ : MulAut V} (h₁ : ∀ x ∈ L, g₁ * x * g₁⁻¹ ∈ L) (h₁' : ∀ x ∈ L, g₁⁻¹ * x * g₁ ∈ L)
    (h₂ : ∀ x ∈ L, g₂ * x * g₂⁻¹ ∈ L) (h₂' : ∀ x ∈ L, g₂⁻¹ * x * g₂ ∈ L)
    (h₁₂ : ∀ x ∈ L, g₁ * g₂ * x * (g₁ * g₂)⁻¹ ∈ L)
    (h₁₂' : ∀ x ∈ L, (g₁ * g₂)⁻¹ * x * (g₁ * g₂) ∈ L) (γ : ↥(StatedSL n (ZMod 2))) :
    conjSL hπ h₁₂ h₁₂' γ = conjSL hπ h₁ h₁' (conjSL hπ h₂ h₂' γ) := by
  apply hπ.1
  apply Subtype.ext
  rw [conjSL_spec, conjSL_spec, conjSL_spec]
  group

end Conj

section Outer

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} {n : ℕ}

theorem graph_of_not_mem (h : B51Hyp G L) (hn : 3 ≤ n) {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (hπ : Function.Bijective π) {g : MulAut V} (hgG : g ∈ G) (hg2 : g ^ 2 = 1) (hgL : g ∉ L)
    (h₁ : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (h₁' : ∀ x ∈ L, g⁻¹ * x * g ∈ L) :
    ∃ P : GL (Fin n) (ZMod 2), ∀ γ, mat (conjSL hπ h₁ h₁' γ) =
      (P : Matrix (Fin n) (Fin n) (ZMod 2)) * dmat γ *
        ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  obtain ⟨P, hP | hP⟩ := aut_cases hn (conjSL hπ h₁ h₁')
  · exfalso
    obtain ⟨l, hl, hinner⟩ := inner_of_conj hπ h₁ h₁' hP
    exact hgL (mem_of_inner h hgG hg2 hl hinner)
  · exact ⟨P, hP⟩

theorem conj_mem (h : B51Hyp G L) {g : MulAut V} (hgG : g ∈ G) :
    (∀ x ∈ L, g * x * g⁻¹ ∈ L) ∧ ∀ x ∈ L, g⁻¹ * x * g ∈ L :=
  ⟨normal_L h g hgG, fun x hx => by simpa using normal_L h g⁻¹ (G.inv_mem hgG) x hx⟩

theorem mul_mem_of_not_mem (h : B51Hyp G L) (hn : 3 ≤ n) {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (hπ : Function.Bijective π) {a b : MulAut V} (haG : a ∈ G) (hbG : b ∈ G) (ha2 : a ^ 2 = 1)
    (hb2 : b ^ 2 = 1) (hab2 : (a * b) ^ 2 = 1) (haL : a ∉ L) (hbL : b ∉ L) : a * b ∈ L := by
  obtain ⟨ha₁, ha₁'⟩ := conj_mem h haG
  obtain ⟨hb₁, hb₁'⟩ := conj_mem h hbG
  obtain ⟨hab₁, hab₁'⟩ := conj_mem h (G.mul_mem haG hbG)
  obtain ⟨P, hP⟩ := graph_of_not_mem h hn hπ haG ha2 haL ha₁ ha₁'
  obtain ⟨Q, hQ⟩ := graph_of_not_mem h hn hπ hbG hb2 hbL hb₁ hb₁'
  have hR : ∀ γ, mat (conjSL hπ hab₁ hab₁' γ) =
      ((P * invT Q : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) * mat γ *
        (((P * invT Q)⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    intro γ
    rw [conjSL_mul hπ ha₁ ha₁' hb₁ hb₁' hab₁ hab₁', hP, dmat_of_dmat_conj hQ, _root_.mul_inv_rev,
      Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨l, hl, hinner⟩ := inner_of_conj hπ hab₁ hab₁' hR
  exact mem_of_inner h (G.mul_mem haG hbG) hab2 hl hinner

end Outer

section Copies

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} {n : ℕ}

theorem rkIdx_fixV_conjSub (g : MulAut V) (C : Subgroup (MulAut V)) :
    rkIdx (fixV (conjSub g C)) = rkIdx (fixV C) :=
  CFSG.Quasithin.ConjTransport.rkIdx_fixV_map_conj C g

theorem mem_of_copies (h : B51Hyp G L) (hn : 3 ≤ n) {k : ℕ} (hk : 1 ≤ k) {I : Fin k → Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hI : ∀ i, RealM L (I i) ⊥ π mat)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) (hsum : ⨆ i, I i = ⊤)
    {g : MulAut V} (hgG : g ∈ G) (hg2 : g ^ 2 = 1) : g ∈ L := by
  by_contra hgL
  have hπ : Function.Bijective π := ⟨(hI ⟨0, hk⟩).injective (Or.inl rfl), (hI ⟨0, hk⟩).1⟩
  obtain ⟨h₁, h₁'⟩ := conj_mem h hgG
  obtain ⟨P, hP⟩ := graph_of_not_mem h hn hπ hgG hg2 hgL h₁ h₁'
  obtain ⟨B₀, hB₀⟩ := exists_fixD_lt_fixN hn
  set C : Subgroup (MulAut V) := (B₀.map π).map L.subtype with hC
  have hCL : C ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hpreC : pre π C = B₀ := by
    ext γ
    rw [mem_pre]
    constructor
    · rintro ⟨y, ⟨δ, hδ, rfl⟩, hy⟩
      have : δ = γ := hπ.1 (Subtype.ext hy)
      rw [← this]
      exact hδ
    · intro hγ
      exact ⟨π γ, ⟨γ, hγ, rfl⟩, rfl⟩
  have hrk : ∀ D : Subgroup (MulAut V), D ≤ L →
      rkSub D ⊤ = k * (n - finrank (ZMod 2) (fixN (pre π D))) := by
    intro D hDL
    rw [← hsum, rkSub_iSup I (fun i b hb x hx => (hI i).2.2.1 ⟨b, hDL hb⟩ x hx) hind,
      Finset.sum_congr rfl (fun i _ => (hI i).rkSub_eq hDL), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, fixM_mat]
  have hgC : conjSub g C ≤ L := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_conjSub.1 hx
    exact h₁ c (hCL hc)
  have e1 := hrk C hCL
  have e2 := hrk (conjSub g C) hgC
  rw [pre_conjSub hπ h₁ h₁' hCL, fixN_map_eq hP, hpreC, fixM_dmat] at e2
  rw [hpreC] at e1
  have e3 : rkSub (conjSub g C) ⊤ = rkSub C ⊤ := by
    rw [rkSub_top, rkSub_top, rkIdx_fixV_conjSub]
  have e4 := finrank_fixN_le B₀
  have e5 := finrank_fixD_add B₀
  have e6 : k * (n - finrank (ZMod 2) (fixD B₀)) = k * (n - finrank (ZMod 2) (fixN B₀)) := by
    rw [← e1, ← e2, e3]
  have e7 := Nat.eq_of_mul_eq_mul_left hk e6
  omega

theorem eq_L_of_copies (h : B51Hyp G L) (hn : 3 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hD : DirectSumOfCopies L ⊤ ⊥ (FFModel.nat (StatedSL n (ZMod 2))) k) : G = L := by
  obtain ⟨I, π, -, hind, hsum, hreal⟩ := hD
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf G
  refine eq_of_offenders_le h hT fun A hA _ a ha => ?_
  refine mem_of_copies h hn hk (fun i => realM_mat_iff.2 (hreal i)) (fun i => ?_) ?_ (hA.1 ha)
    (hA.2.2.1.2 a ha)
  · have := hind i
    rwa [bot_sup_eq] at this
  · rwa [bot_sup_eq] at hsum

end Copies

section NatDual

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem le_L_of_sumNatDual (h : B51Hyp G L) (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ}
    (hS : SumNatDual L ⊤ n) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) : A ≤ L := by
  classical
  obtain ⟨hn, π, U₁, U₂, ⟨hsup, hinf⟩, h1, h2⟩ := hS
  have hR1 := realM_mat_iff.2 h1
  have hR2 := realM_dmat_iff.2 h2
  have hπ : Function.Bijective π := ⟨hR1.injective (Or.inl rfl), hR1.1⟩
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hAel : IsElemAbelian2 A := hA.2.2.1
  intro a haA
  by_contra haL
  have haG : a ∈ G := hA.1 haA
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  obtain ⟨ha₁, ha₁'⟩ := conj_mem h haG
  set aU := U₁.map a.toMonoidHom with haU
  have haUinv : ∀ l ∈ L, ∀ x ∈ aU, l x ∈ aU := by
    rintro l hl _ ⟨u, hu, rfl⟩
    refine ⟨(a⁻¹ * l * a) u, hR1.2.2.1 ⟨_, ha₁' l hl⟩ u hu, ?_⟩
    simp [MulAut.mul_apply]
  have hcap : U₁ ⊓ aU = ⊥ := by
    rcases hR1.eq_or_eq (Or.inl rfl) (CFSG.Quasithin.isInv_inf
        (fun l hl x hx => hR1.2.2.1 ⟨l, hl⟩ x hx) haUinv) bot_le inf_le_left with h0 | h0
    · exact h0
    · exfalso
      have hle : U₁ ≤ aU := h0 ▸ inf_le_right
      have hcard : Nat.card aU = Nat.card U₁ :=
        Subgroup.card_map_of_injective (fun x y hxy => a.injective hxy)
      have heq : aU = U₁ := (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
      have hainv : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq, ha2]
      have hstab : a ∈ stabSub U₁ := by
        have hmap : ∀ u ∈ U₁, a u ∈ U₁ := fun u hu => by
          rw [← heq]
          exact ⟨u, hu, rfl⟩
        refine mem_stabSub_of_inv hmap ?_
        rw [hainv]
        exact hmap
      obtain ⟨l, hl, hinner⟩ := hR1.exists_inner (Or.inl rfl) (by omega) ha₁ ha₁' hstab
        (stabSub_bot_le G haG)
      exact haL (mem_of_inner h haG ha2 hl hinner)
  set A₀ := A ⊓ L with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hA₀L : A₀ ≤ L := inf_le_right
  have hcardA : Nat.card A ≤ Nat.card A₀ * 2 := by
    let f : ↥A → ↥A₀ × Fin 2 := fun x =>
      if hx : (x : MulAut V) ∈ L then (⟨x, x.2, hx⟩, 0) else
        (⟨a * x, A.mul_mem haA x.2, mul_mem_of_not_mem h hn3 hπ haG (hA.1 x.2) ha2
          (hAel.2 x x.2) (hAel.2 _ (A.mul_mem haA x.2)) haL hx⟩, 1)
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : (x : MulAut V) ∈ L <;> by_cases hy : (y : MulAut V) ∈ L
      · simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        have e := congrArg Subtype.val hxy.1
        exact Subtype.ext e
      · simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        exact absurd hxy.2 (by decide)
      · simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        exact absurd hxy.2 (by decide)
      · simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
        have e : a * (x : MulAut V) = a * (y : MulAut V) := congrArg Subtype.val hxy.1
        exact Subtype.ext (mul_left_cancel e)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_fin] at this
  have hA2 : IsPGroup 2 ↥A := hAel.isPGroup
  have hA₀2 : IsPGroup 2 ↥A₀ := hA2.to_le hA₀A
  have hrkA : rk A ≤ rk A₀ + 1 := by
    rw [card_eq_two_pow_of_isPGroup hA2, card_eq_two_pow_of_isPGroup hA₀2, ← pow_succ] at hcardA
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcardA
  have hinv1 : ∀ b ∈ A₀, ∀ x ∈ U₁, b x ∈ U₁ := fun b hb x hx => hR1.2.2.1 ⟨b, hA₀L hb⟩ x hx
  have hinv2 : ∀ b ∈ A₀, ∀ x ∈ U₂, b x ∈ U₂ := fun b hb x hx => hR2.2.2.1 ⟨b, hA₀L hb⟩ x hx
  have hsumrk := rkSub_sup hinv1 hinv2 hinf
  rw [hsup, rkSub_top, hR1.rkSub_eq hA₀L, hR2.rkSub_eq hA₀L, fixM_mat, fixM_dmat] at hsumrk
  have hrkU : ∀ {X : Subgroup V} {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)},
      RealM L X ⊥ π M → rk X = n := by
    intro X M hX
    have e1 := hX.card_sec
    have e2 := card_sec_mul (bot_le : (⊥ : Subgroup V) ≤ X)
    rw [Subgroup.card_bot, mul_one, e1] at e2
    unfold rk
    rw [← e2, padicValNat.prime_pow]
  have hrkU₁ := hrkU hR1
  have hrkU₂ := hrkU hR2
  have hrkV : rk V = 2 * n := by
    have e1 := rk_sup_add_rk_inf U₁ U₂
    rw [hsup, hinf, rk_bot, add_zero, rk_top, hrkU₁, hrkU₂] at e1
    omega
  have hc₁ : rk ↥(U₁ ⊓ fixV A₀) = finrank (ZMod 2) (fixN (pre π A₀)) := by
    have e1 := hR1.rkSub_eq hA₀L
    rw [fixM_mat] at e1
    have e2 : rkSub A₀ U₁ = rk U₁ - rk ↥(U₁ ⊓ fixV A₀) := rfl
    have e3 := rk_mono (inf_le_left : U₁ ⊓ fixV A₀ ≤ U₁)
    have e4 := finrank_fixN_le (pre π A₀)
    omega
  have hdisj : fixV A ⊓ (U₁ ⊓ fixV A₀) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvA, hvU, -⟩
    have hav : a v = v := hvA a haA
    have : v ∈ U₁ ⊓ aU := ⟨hvU, ⟨v, hvU, hav⟩⟩
    rwa [hcap] at this
  have hle : fixV A ⊔ (U₁ ⊓ fixV A₀) ≤ fixV A₀ := sup_le (B1.fixV_le_fixV hA₀A) inf_le_right
  have e1 := rk_sup_add_rk_inf (fixV A) (U₁ ⊓ fixV A₀)
  rw [hdisj, rk_bot, add_zero] at e1
  have e2 := rk_mono hle
  have r1 := rk_add_rkIdx (fixV A)
  have r2 := rk_add_rkIdx (fixV A₀)
  have hA₀el : IsElemAbelian2 A₀ :=
    ⟨fun x hx y hy => hAel.1 x (hA₀A hx) y (hA₀A hy), fun x hx => hAel.2 x (hA₀A hx)⟩
  have o1 := rk_add_le_of_card_le hV hA₀el hAel (hA.2.2.2 A₀ hA₀A)
  have o2 := rkIdx_fixV_le_rk hV hA
  have hB2 : IsPGroup 2 ↥(pre π A₀) := isPGroup_pre hπ hA₀2
  have hfN := fixN_ne_bot_of_isPGroup hB2 (by omega)
  have hfN1 : 1 ≤ finrank (ZMod 2) (fixN (pre π A₀)) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hfN (Submodule.finrank_eq_zero.1 h0)
  have hc₁1 : finrank (ZMod 2) (fixN (pre π A₀)) = 1 := by omega
  have hA₀ne : A₀ ≠ ⊥ := by
    intro h0
    have : U₁ ⊓ fixV A₀ = U₁ := by rw [h0, B1.fixV_bot, inf_top_eq]
    rw [this, hrkU₁] at hc₁
    omega
  have hcommB : ∀ x ∈ pre π A₀, ∀ y ∈ pre π A₀, x * y = y * x := by
    intro x hx y hy
    apply hπ.1
    apply Subtype.ext
    rw [map_mul, map_mul]
    exact hAel.1 _ (hA₀A hx) _ (hA₀A hy)
  have hcardB := card_le_of_finrank_fixN_eq_one hcommB hB2 hc₁1
  rw [card_pre hπ hA₀L, card_eq_two_pow_of_isPGroup hA₀2] at hcardB
  have hrkA₀ : rk A₀ ≤ n - 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcardB
  have hfD := finrank_fixM_lt hπ (Or.inr rfl) hA₀L hA₀ne
  rw [fixM_dmat] at hfD
  omega

theorem eq_L_of_sumNatDual (h : B51Hyp G L) (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ}
    (hS : SumNatDual L ⊤ n) : G = L := by
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf G
  exact eq_of_offenders_le h hT fun A hA _ => le_L_of_sumNatDual h hV hS hA

end NatDual

end CFSG.Quasithin.B5.Ln
