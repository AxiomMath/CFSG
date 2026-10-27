module

public import CFSG.Quasithin.Background.RonanG25GroupV

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

section Helpers

variable {G : Type} [Group G]

theorem grpU_sup_mul {W K : Subgroup G} (hK : ∀ w ∈ W, ∀ k ∈ K, w * k * w⁻¹ ∈ K) {x : G}
    (hx : x ∈ W ⊔ K) : ∃ w ∈ W, ∃ k ∈ K, x = w * k := by
  let T : Subgroup G :=
    { carrier := {x | ∃ w ∈ W, ∃ k ∈ K, x = w * k}
      one_mem' := ⟨1, W.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨w₁, hw₁, k₁, hk₁, rfl⟩ ⟨w₂, hw₂, k₂, hk₂, rfl⟩
        refine ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, (w₂⁻¹ * k₁ * w₂) * k₂, K.mul_mem ?_ hk₂, ?_⟩
        · simpa [mul_assoc] using hK w₂⁻¹ (W.inv_mem hw₂) k₁ hk₁
        · group
      inv_mem' := by
        rintro _ ⟨w, hw, k, hk, rfl⟩
        exact ⟨w⁻¹, W.inv_mem hw, w * k⁻¹ * w⁻¹, hK w hw k⁻¹ (K.inv_mem hk), by group⟩ }
  have hle : W ⊔ K ≤ T :=
    sup_le (fun w hw => ⟨w, hw, 1, K.one_mem, (mul_one w).symm⟩)
      (fun k hk => ⟨1, W.one_mem, k, hk, (one_mul k).symm⟩)
  exact hle hx

theorem grpU_dual {F : Type} [Field F] (Q : SL(3, F)) (lam : Fin 3 → F)
    (hlam : ∀ k, lam k ≠ 0) (u : Fin 3 → Fin 3 → F) (hQ : ∀ k, Q • vE F k = lam k • u k) :
    ∃ P₀ P₁ P₂ : (Fin 3 → F) → (Fin 3 → F),
      (∀ f, f = P₀ f + P₁ f + P₂ f) ∧
      (∀ f, P₀ f ⬝ᵥ u 1 = 0 ∧ P₀ f ⬝ᵥ u 2 = 0) ∧
      (∀ f, P₁ f ⬝ᵥ u 0 = 0 ∧ P₁ f ⬝ᵥ u 2 = 0) ∧
      (∀ f, P₂ f ⬝ᵥ u 0 = 0 ∧ P₂ f ⬝ᵥ u 1 = 0) ∧
      (∀ f, f ⬝ᵥ u 0 = 0 → P₀ f = 0) := by
  have hent : ∀ i k, (Q : Matrix (Fin 3) (Fin 3) F) i k = lam k * u k i := by
    intro i k
    have h2 : Matrix.mulVec (Q : Matrix (Fin 3) (Fin 3) F) (vE F k) i = lam k * u k i :=
      congrFun (hQ k) i
    simpa [Matrix.mulVec, dotProduct, vE, Pi.single_apply] using h2
  set R : Matrix (Fin 3) (Fin 3) F := ((Q⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) with hR
  have hRQ : R * (Q : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [hR, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hQR : (Q : Matrix (Fin 3) (Fin 3) F) * R = 1 := by
    rw [hR, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hu' : ∀ i j, u j i = (lam j)⁻¹ * (Q : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    rw [hent i j, ← mul_assoc, inv_mul_cancel₀ (hlam j), one_mul]
  have hA : ∀ k j, ∑ i, lam k * R k i * u j i = if k = j then 1 else 0 := by
    intro k j
    have h1 : ∀ i, lam k * R k i * u j i =
        (lam k * (lam j)⁻¹) * (R k i * (Q : Matrix (Fin 3) (Fin 3) F) i j) := by
      intro i
      rw [hu' i j]
      ring
    simp only [h1]
    rw [← Finset.mul_sum]
    have h2 : ∑ i, R k i * (Q : Matrix (Fin 3) (Fin 3) F) i j =
        (R * (Q : Matrix (Fin 3) (Fin 3) F)) k j := by
      simp [Matrix.mul_apply]
    rw [h2, hRQ, Matrix.one_apply]
    split_ifs with hkj
    · subst hkj
      simp [hlam k]
    · simp
  have hB : ∀ i j, ∑ k, lam k * R k i * u k j = if i = j then 1 else 0 := by
    intro i j
    have h1 : ∀ k, lam k * R k i * u k j = (Q : Matrix (Fin 3) (Fin 3) F) j k * R k i := by
      intro k
      rw [hu' j k]
      calc lam k * R k i * ((lam k)⁻¹ * (Q : Matrix (Fin 3) (Fin 3) F) j k)
          = (lam k * (lam k)⁻¹) * ((Q : Matrix (Fin 3) (Fin 3) F) j k * R k i) := by ring
        _ = (Q : Matrix (Fin 3) (Fin 3) F) j k * R k i := by
          rw [mul_inv_cancel₀ (hlam k), one_mul]
    simp only [h1]
    have h2 : ∑ k, (Q : Matrix (Fin 3) (Fin 3) F) j k * R k i =
        ((Q : Matrix (Fin 3) (Fin 3) F) * R) j i := by
      simp [Matrix.mul_apply]
    rw [h2, hQR, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
  have hdec : ∃ d : Fin 3 → Fin 3 → F, (∀ k j, d k ⬝ᵥ u j = if k = j then 1 else 0) ∧
      ∀ f : Fin 3 → F, f = (f ⬝ᵥ u 0) • d 0 + (f ⬝ᵥ u 1) • d 1 + (f ⬝ᵥ u 2) • d 2 := by
    refine ⟨fun k i => lam k * R k i, fun k j => hA k j, fun f => ?_⟩
    funext i
    have hsc : f i = ∑ k, (f ⬝ᵥ u k) * (lam k * R k i) := by
      calc f i = ∑ j, f j * (if i = j then 1 else 0) := by simp
        _ = ∑ j, f j * ∑ k, lam k * R k i * u k j := by simp only [hB]
        _ = ∑ k, ∑ j, f j * (lam k * R k i * u k j) := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]
        _ = ∑ k, (f ⬝ᵥ u k) * (lam k * R k i) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [dotProduct, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
    rw [Fin.sum_univ_three] at hsc
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hsc
  obtain ⟨d, hd, hfd⟩ := hdec
  refine ⟨fun f => (f ⬝ᵥ u 0) • d 0, fun f => (f ⬝ᵥ u 1) • d 1, fun f => (f ⬝ᵥ u 2) • d 2,
    fun f => hfd f, ?_, ?_, ?_, ?_⟩
  · intro f
    simp [smul_dotProduct, hd 0 1, hd 0 2]
  · intro f
    simp [smul_dotProduct, hd 1 0, hd 1 2]
  · intro f
    simp [smul_dotProduct, hd 2 0, hd 2 1]
  · intro f hf
    simp [hf]

theorem grpU_pre_bot {B N' : Subgroup G} {E : Type} [AddCommGroup E]
    {φ : ↥B →* Multiplicative E} (hN' : N' ≤ B) (hker : ∀ y : ↥B, φ y = 1 ↔ (y : G) ∈ N') :
    pre B φ (⊥ : AddSubgroup E) = N' := by
  ext y
  rw [mem_pre]
  constructor
  · rintro ⟨hy, h⟩
    exact (hker ⟨y, hy⟩).mp (toAdd_eq_zero.mp (AddSubgroup.mem_bot.mp h))
  · intro hy
    have hyB : y ∈ B := hN' hy
    exact ⟨hyB, AddSubgroup.mem_bot.mpr (toAdd_eq_zero.mpr ((hker ⟨y, hyB⟩).mpr hy))⟩

theorem grpU_pre_all {B : Subgroup G} {E : Type} [AddCommGroup E]
    {φ : ↥B →* Multiplicative E} {M : AddSubgroup E}
    (h : ∀ y : ↥B, Multiplicative.toAdd (φ y) ∈ M) : pre B φ M = B := by
  ext y
  rw [mem_pre]
  exact ⟨fun ⟨hy, _⟩ => hy, fun hy => ⟨hy, h ⟨y, hy⟩⟩⟩

theorem grpU_range_top {B : Subgroup G} {E : Type} [AddCommGroup E]
    {φ : ↥B →* Multiplicative E} (hφ : Function.Surjective φ) (e : E) :
    e ∈ (⊤ : AddSubgroup E) ↔ ∃ y, φ y = Multiplicative.ofAdd e :=
  ⟨fun _ => hφ (Multiplicative.ofAdd e), fun _ => AddSubgroup.mem_top _⟩

def grpU_tqHom (F : Type) [Field F] : Multiplicative (Fin 2 → F) →* SL(3, F) where
  toFun q := tqv (Multiplicative.toAdd q)
  map_one' := by simp [tqv, tq_zero]
  map_mul' a b := by simp [tqv, ← tq_add]

theorem grpU_tqHom_injective (F : Type) [Field F] : Function.Injective (grpU_tqHom F) := by
  intro a b hab
  have h' : tq (Multiplicative.toAdd a 0) (Multiplicative.toAdd a 1) =
      tq (Multiplicative.toAdd b 0) (Multiplicative.toAdd b 1) := hab
  obtain ⟨h0, h1⟩ := tq_injective h'
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem grpU_tqHom_range (F : Type) [Field F] :
    (grpU_tqHom F).range = Qv (vE F 0) := by
  ext A
  constructor
  · rintro ⟨q, rfl⟩
    exact tq_mem_Qv _ _
  · intro hA
    obtain ⟨b, c, rfl⟩ := mem_Qv_e0.1 hA
    refine ⟨Multiplicative.ofAdd ![b, c], ?_⟩
    show tq (![b, c] 0) (![b, c] 1) = tq b c
    simp

end Helpers

section GroupU

variable {G : Type} [Group G] [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G}

theorem mem_gS₂_iff {g h : G} (hsub : SubFacts V L H g h) {y : G} :
    y ∈ gS₂ V H g h ↔ y ∈ gW V H L ∧ y ∈ rconj (gW V H L) g ∧ y ∈ rconj (gW V H L) h := by
  rw [← hsub.dir]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨_, h3⟩⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, ⟨h1, h3⟩⟩

theorem gS₂_le_gW {g h : G} (hsub : SubFacts V L H g h) : gS₂ V H g h ≤ gW V H L :=
  fun _ hy => ((mem_gS₂_iff hsub).1 hy).1

theorem W_inf_S₃_eq (St : L3Setting n V V₁ L T H) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) :
    gW V H L ⊓ gS₃ V H L g h =
      pre (gS₃ V H L g h) φ₆ (piPow s (annSub (GaloisField 2 n))) := by
  obtain ⟨Q, lam, hlam, hQ⟩ := St.exists_basis_Q hg hh hV
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → Fin 3 → GaloisField 2 n,
      ∀ k, u k = St.pvec (tripleConj_mem hg hh k) := ⟨_, fun k => rfl⟩
  have hQ' : ∀ k, Q • vE (GaloisField 2 n) k = lam k • u k := fun k => by
    rw [hu]
    exact hQ k
  obtain ⟨P₀, P₁, P₂, hsplit, hP₀, hP₁, hP₂, hP₀zero⟩ := grpU_dual Q lam hlam u hQ'
  have hu0 : u 0 = vE (GaloisField 2 n) 0 := by
    rw [hu]
    exact St.pvec_tripleConj_zero hg hh
  have hu1 : u 1 = St.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0 := by
    rw [hu]
    exact St.pvec_tripleConj_one hg hh
  have hu2 : u 2 = St.D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0 := by
    rw [hu]
    exact St.pvec_tripleConj_two hg hh
  have hG : ∀ f : Fin 3 → GaloisField 2 n,
      (f ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧ f ⬝ᵥ (St.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) = 0) ↔
        (f ⬝ᵥ u 0 = 0 ∧ f ⬝ᵥ u 1 = 0) := fun f => by
    rw [hu0, hu1]
  have hH : ∀ f : Fin 3 → GaloisField 2 n,
      (f ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧ f ⬝ᵥ (St.D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) = 0) ↔
        (f ⬝ᵥ u 0 = 0 ∧ f ⬝ᵥ u 2 = 0) := fun f => by
    rw [hu0, hu2]
  have hGH : ∀ f : Fin 3 → GaloisField 2 n,
      (f ⬝ᵥ (St.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) = 0 ∧
        f ⬝ᵥ (St.D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) = 0) ↔
        (f ⬝ᵥ u 1 = 0 ∧ f ⬝ᵥ u 2 = 0) := fun f => by
    rw [hu1, hu2]
  have hann : ∀ f : Fin 3 → GaloisField 2 n, f ∈ annSub (GaloisField 2 n) ↔ f ⬝ᵥ u 0 = 0 := by
    intro f
    have hdot : f ⬝ᵥ vE (GaloisField 2 n) 0 = f 0 := by
      simp [dotProduct, vE, Pi.single_apply]
    rw [hu0, hdot]
    exact Iff.rfl
  ext x
  constructor
  · rintro ⟨hxW, hxS₃⟩
    refine mem_pre.2 ⟨hxS₃, ?_⟩
    rw [mem_piPow]
    intro l
    rw [hann]
    obtain ⟨v, hv⟩ : ∃ v : Fin s → Fin 3 → GaloisField 2 n,
        Multiplicative.toAdd (φ₆ ⟨x, hxS₃⟩) = v := ⟨_, rfl⟩
    rw [hv]
    have hvsum : v = (fun l => P₀ (v l)) + (fun l => P₁ (v l)) + (fun l => P₂ (v l)) := by
      funext l
      exact hsplit (v l)
    obtain ⟨x₁, hx₁⟩ := hsum.six.1 (Multiplicative.ofAdd (fun l => P₂ (v l)))
    obtain ⟨x₂, hx₂⟩ := hsum.six.1 (Multiplicative.ofAdd (fun l => P₁ (v l)))
    obtain ⟨x₃, hx₃⟩ := hsum.six.1 (Multiplicative.ofAdd (fun l => P₀ (v l)))
    have hx₁W : (x₁ : G) ∈ gW V H L ⊓ rconj (gW V H L) g :=
      (hsum.six_g x₁).2 fun l => (hG _).2 (by rw [hx₁, toAdd_ofAdd]; exact hP₂ (v l))
    have hx₂W : (x₂ : G) ∈ gW V H L ⊓ rconj (gW V H L) h :=
      (hsum.six_h x₂).2 fun l => (hH _).2 (by rw [hx₂, toAdd_ofAdd]; exact hP₁ (v l))
    have hx₃W : (x₃ : G) ∈ rconj (gW V H L) g ⊓ rconj (gW V H L) h :=
      (hsum.six_gh x₃).2 fun l => (hGH _).2 (by rw [hx₃, toAdd_ofAdd]; exact hP₀ (v l))
    obtain ⟨k, hk⟩ : ∃ k : ↥(gS₃ V H L g h), k = ⟨x, hxS₃⟩ * (x₁ * x₂ * x₃)⁻¹ := ⟨_, rfl⟩
    have hkG : (k : G) = x * ((x₁ : G) * (x₂ : G) * (x₃ : G))⁻¹ := by
      rw [hk]
      simp
    have hφk : φ₆ k = 1 := by
      have hmul : ∀ a b : ↥(gS₃ V H L g h), Multiplicative.toAdd (φ₆ (a * b)) =
          Multiplicative.toAdd (φ₆ a) + Multiplicative.toAdd (φ₆ b) := fun a b => by
        rw [map_mul, toAdd_mul]
      have hinv : ∀ a : ↥(gS₃ V H L g h), Multiplicative.toAdd (φ₆ a⁻¹) =
          -Multiplicative.toAdd (φ₆ a) := fun a => by
        rw [map_inv, toAdd_inv]
      have e1 : Multiplicative.toAdd (φ₆ k) = v - ((fun l => P₀ (v l)) + (fun l => P₁ (v l)) +
          (fun l => P₂ (v l))) := by
        rw [hk, hmul, hinv, hmul, hmul, hx₁, hx₂, hx₃, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd, hv]
        abel
      have e0 : Multiplicative.toAdd (φ₆ k) = 0 := by
        rw [e1]
        exact sub_eq_zero.mpr hvsum
      exact toAdd_eq_zero.mp e0
    have hkW : (k : G) ∈ gW V H L := gS₂_le_gW hsub ((hsum.six.2.1 k).1 hφk)
    have hx₃eq : (x₃ : G) = (x₂ : G)⁻¹ * ((x₁ : G)⁻¹ * ((k : G)⁻¹ * x)) := by
      rw [hkG]
      group
    have hx₃W' : (x₃ : G) ∈ gW V H L := by
      rw [hx₃eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₂W.1)
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₁W.1)
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkW) hxW))
    have hx₃S₂ : (x₃ : G) ∈ gS₂ V H g h := (mem_gS₂_iff hsub).2 ⟨hx₃W', hx₃W.1, hx₃W.2⟩
    have hφx₃ : φ₆ x₃ = 1 := (hsum.six.2.1 x₃).2 hx₃S₂
    rw [hx₃] at hφx₃
    have hC : (fun l => P₀ (v l)) = 0 := ofAdd_eq_one.mp hφx₃
    have hC' : P₀ (v l) = 0 := congrFun hC l
    rw [hsplit (v l), hC', zero_add, add_dotProduct, (hP₁ _).1, (hP₂ _).1, add_zero]
  · intro hx
    obtain ⟨hxS₃, hpre⟩ := mem_pre.1 hx
    refine ⟨?_, hxS₃⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin s → Fin 3 → GaloisField 2 n,
        Multiplicative.toAdd (φ₆ ⟨x, hxS₃⟩) = v := ⟨_, rfl⟩
    rw [hv] at hpre
    have hv0 : ∀ l, v l ⬝ᵥ u 0 = 0 := fun l => (hann _).1 ((mem_piPow.1 hpre) l)
    have hvAB : v = (fun l => P₁ (v l)) + (fun l => P₂ (v l)) := by
      funext l
      have h0 : P₀ (v l) = 0 := hP₀zero (v l) (hv0 l)
      have h1 := hsplit (v l)
      rw [h0, zero_add] at h1
      exact h1
    obtain ⟨x₁, hx₁⟩ := hsum.six.1 (Multiplicative.ofAdd (fun l => P₂ (v l)))
    obtain ⟨x₂, hx₂⟩ := hsum.six.1 (Multiplicative.ofAdd (fun l => P₁ (v l)))
    have hx₁W : (x₁ : G) ∈ gW V H L :=
      ((hsum.six_g x₁).2 fun l => (hG _).2 (by rw [hx₁, toAdd_ofAdd]; exact hP₂ (v l))).1
    have hx₂W : (x₂ : G) ∈ gW V H L :=
      ((hsum.six_h x₂).2 fun l => (hH _).2 (by rw [hx₂, toAdd_ofAdd]; exact hP₁ (v l))).1
    obtain ⟨k, hk⟩ : ∃ k : ↥(gS₃ V H L g h), k = ⟨x, hxS₃⟩ * (x₁ * x₂)⁻¹ := ⟨_, rfl⟩
    have hkG : (k : G) = x * ((x₁ : G) * (x₂ : G))⁻¹ := by
      rw [hk]
      simp
    have hφk : φ₆ k = 1 := by
      have hmul : ∀ a b : ↥(gS₃ V H L g h), Multiplicative.toAdd (φ₆ (a * b)) =
          Multiplicative.toAdd (φ₆ a) + Multiplicative.toAdd (φ₆ b) := fun a b => by
        rw [map_mul, toAdd_mul]
      have hinv : ∀ a : ↥(gS₃ V H L g h), Multiplicative.toAdd (φ₆ a⁻¹) =
          -Multiplicative.toAdd (φ₆ a) := fun a => by
        rw [map_inv, toAdd_inv]
      have e1 : Multiplicative.toAdd (φ₆ k) = v - ((fun l => P₁ (v l)) + (fun l => P₂ (v l))) := by
        rw [hk, hmul, hinv, hmul, hx₁, hx₂, toAdd_ofAdd, toAdd_ofAdd, hv]
        abel
      have e0 : Multiplicative.toAdd (φ₆ k) = 0 := by
        rw [e1]
        exact sub_eq_zero.mpr hvAB
      exact toAdd_eq_zero.mp e0
    have hkW : (k : G) ∈ gW V H L := gS₂_le_gW hsub ((hsum.six.2.1 k).1 hφk)
    have hxeq : (x : G) = (k : G) * (x₁ : G) * (x₂ : G) := by
      rw [hkG]
      group
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkW hx₁W) hx₂W

theorem grpU_normalizes {g h : G} (hsub : SubFacts V L H g h) {w k : G}
    (hw : w ∈ gW V H L) (hk : k ∈ gS₃ V H L g h) : w * k * w⁻¹ ∈ gS₃ V H L g h :=
  (Subgroup.mem_normalizer_iff.1 (hsub.I_S₃ ((le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H)
    hw.1)) k).1 hk

theorem chain_S₂_WS₃_group (St : L3Setting n V V₁ L T H) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) {ord : Bool} :
    ChainCounts (GaloisField 2 n) (lOne L V₁) ord (gS₂ V H g h) (gW V H L ⊓ gS₃ V H L g h) s 0 := by
  have hmod := chain_piVd_ann (l1Rep St) s
  have hE : Equivariant (lOne L V₁) (gS₃ V H L g h) φ₆ (piAct s (actVd (rho St.D))) := by
    refine ⟨fun x hx y hy => ?_, fun x y y' hxy => ?_⟩
    · have hxN : x ∈ Subgroup.normalizer ((gS₃ V H L g h : Subgroup G) : Set G) :=
        hsub.I_S₃ ((le_sup_left : L ≤ L ⊔ conjClosure V H) (lOne_le_L hx))
      exact (Subgroup.mem_normalizer_iff.1 hxN y).mp hy
    · have h6 := hsum.six.2.2 ⟨(x : G), lOne_le_L x.2⟩ y y' hxy.symm
      exact h6.trans (congrArg (fun v => Multiplicative.ofAdd v) (funext fun l => rfl))
  have key := ModChain.transport (ord := ord) (grpU_range_top hsum.six.1) hE hmod le_top
  rw [grpU_pre_bot hsub.S₂_le_S₃ hsum.six.2.1, ← W_inf_S₃_eq St hg hh hV hsub hsum] at key
  exact key

theorem chain_WS₃_W_group (St : L3Setting n V V₁ L T H) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) {ord : Bool} :
    ChainCounts (GaloisField 2 n) (lOne L V₁) ord (gW V H L ⊓ gS₃ V H L g h) (gW V H L) 0
      (if 2 < Nat.card (GaloisField 2 n) then r else 0) := by
  have hWS : gW V H L ≤ gS V H L := inf_le_right
  obtain ⟨φW, hφW⟩ : ∃ φW : ↥(gW V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n),
      ∀ y : ↥(gW V H L), φW y = φ₇ ⟨(y : G), hWS y.2⟩ :=
    ⟨φ₇.comp (Subgroup.inclusion hWS), fun y => rfl⟩
  have hWpi : ∀ y : ↥(gW V H L),
      Multiplicative.toAdd (φW y) ∈ piPow r (lineSub (GaloisField 2 n)) := by
    intro y
    rw [hφW, mem_piPow]
    intro l
    obtain ⟨c, hc⟩ := (hsum.seven_W ⟨(y : G), hWS y.2⟩).1
      ((le_sup_left : gW V H L ≤ gW V H L ⊔ gS₃ V H L g h) y.2) l
    rw [hc]
    exact (Submodule.mem_toAddSubgroup _).2
      (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))
  have hsurjW : ∀ e ∈ piPow r (lineSub (GaloisField 2 n)),
      ∃ y : ↥(gW V H L), φW y = Multiplicative.ofAdd e := by
    intro e he
    obtain ⟨x, hx⟩ := hsum.seven.1 (Multiplicative.ofAdd e)
    have hxmem : (x : G) ∈ gW V H L ⊔ gS₃ V H L g h := by
      refine (hsum.seven_W x).2 fun l => ?_
      have hl : e l ∈ (Submodule.span (GaloisField 2 n) {vE (GaloisField 2 n) 0}) :=
        (Submodule.mem_toAddSubgroup _).1 (mem_piPow.1 he l)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hl
      refine ⟨c, ?_⟩
      rw [hx, toAdd_ofAdd, hc]
    obtain ⟨w, hw, s', hs', hxws⟩ :=
      grpU_sup_mul (W := gW V H L) (K := gS₃ V H L g h)
        (fun w hw k hk => grpU_normalizes hsub hw hk) hxmem
    have hwS : w ∈ gS V H L := hWS hw
    have hs'S : s' ∈ gS V H L := hsub.S₃_le_S hs'
    have hφs' : φ₇ ⟨s', hs'S⟩ = 1 := (hsum.seven.2.1 ⟨s', hs'S⟩).2 hs'
    have hxeq : x = ⟨w, hwS⟩ * ⟨s', hs'S⟩ := Subtype.ext hxws
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [hφW]
    have h1 : φ₇ x = φ₇ ⟨w, hwS⟩ := by
      rw [hxeq, map_mul, hφs', mul_one]
    exact h1.symm.trans hx
  have hE : Equivariant (lOne L V₁) (gW V H L) φW (piAct r (actV (rho St.D))) := by
    refine ⟨fun x hx y hy => ?_, fun x y y' hxy => ?_⟩
    · have hxH : (x : G) ∈ H :=
        St.hyp.base.lOne_sup_le ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) hx)
      refine ⟨(Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V H hxH) y).1 hy.1, ?_⟩
      exact (Subgroup.mem_normalizer_iff.1
        (hsub.I_S ((le_sup_left : L ≤ L ⊔ conjClosure V H) (lOne_le_L hx))) y).1 hy.2
    · have h7 := hsum.seven.2.2 ⟨(x : G), lOne_le_L x.2⟩ ⟨(y : G), hWS y.2⟩
        ⟨(y' : G), hWS y'.2⟩ hxy.symm
      rw [hφW, hφW]
      exact h7.trans (congrArg (fun v => Multiplicative.ofAdd v) (funext fun l => rfl))
  have hN : ∀ e, e ∈ piPow r (lineSub (GaloisField 2 n)) ↔
      ∃ y : ↥(gW V H L), φW y = Multiplicative.ofAdd e := fun e =>
    ⟨hsurjW e, fun ⟨y, hy⟩ => by
      have h := hWpi y
      rw [hy, toAdd_ofAdd] at h
      exact h⟩
  have hker : ∀ y : ↥(gW V H L), φW y = 1 ↔ (y : G) ∈ gW V H L ⊓ gS₃ V H L g h := fun y => by
    rw [hφW]
    constructor
    · intro h1
      exact ⟨y.2, (hsum.seven.2.1 ⟨(y : G), hWS y.2⟩).1 h1⟩
    · intro h1
      exact (hsum.seven.2.1 ⟨(y : G), hWS y.2⟩).2 h1.2
  have key := ModChain.transport (ord := ord) hN hE (chain_piV_lines (l1Rep St) r) (le_refl _)
  rw [grpU_pre_bot inf_le_left hker, grpU_pre_all (φ := φW) (M := piPow r (lineSub (GaloisField 2 n)))
    hWpi] at key
  exact key

theorem chain_W_U_group (St : L3Setting n V V₁ L T H) {g h : G} (hsub : SubFacts V L H g h)
    {ord : Bool} :
    ChainCounts (GaloisField 2 n) (lOne L V₁) ord (gW V H L) (conjClosure V H) 1 0 := by
  have hUR : St.betaU.range ≤ (grpU_tqHom (GaloisField 2 n)).range := by
    rw [grpU_tqHom_range]
    exact St.Ubar_le_Qv
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(conjClosure V H) →* Multiplicative (Fin 2 → GaloisField 2 n),
      ∀ y, grpU_tqHom (GaloisField 2 n) (φ y) = St.betaU y := by
    refine ⟨((MonoidHom.ofInjective (grpU_tqHom_injective (GaloisField 2 n))).symm.toMonoidHom).comp
      ((Subgroup.inclusion hUR).comp St.betaU.rangeRestrict), fun y => ?_⟩
    have h1 := congrArg Subtype.val
      ((MonoidHom.ofInjective (grpU_tqHom_injective (GaloisField 2 n))).apply_symm_apply
        (Subgroup.inclusion hUR (St.betaU.rangeRestrict y)))
    exact h1
  have hφs : Function.Surjective φ := by
    intro w
    have hw : grpU_tqHom (GaloisField 2 n) w ∈ St.betaU.range := by
      have h1 : grpU_tqHom (GaloisField 2 n) w ∈ (grpU_tqHom (GaloisField 2 n)).range :=
        ⟨w, rfl⟩
      rw [grpU_tqHom_range, ← St.Ubar_eq_Qv] at h1
      exact h1
    obtain ⟨u, hu⟩ := hw
    exact ⟨u, grpU_tqHom_injective (GaloisField 2 n) (by rw [hφ, hu])⟩
  have hker : ∀ y : ↥(conjClosure V H), φ y = 1 ↔ (y : G) ∈ gW V H L := by
    intro y
    have hyLU : (y : G) ∈ L ⊔ conjClosure V H :=
      (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) y.2
    have hPhi : St.Phi ⟨(y : G), hyLU⟩ = St.betaU y := rfl
    constructor
    · intro h
      have h1 : St.Phi ⟨(y : G), hyLU⟩ = 1 := by
        rw [hPhi, ← hφ y, h, map_one]
      exact ⟨y.2, (St.Phi_eq_one_iff_mem_S _).1 h1⟩
    · intro h
      apply grpU_tqHom_injective (GaloisField 2 n)
      rw [hφ y, map_one, ← hPhi]
      exact (St.Phi_eq_one_iff_mem_S _).2 h.2
  have hE : Equivariant (lOne L V₁) (conjClosure V H) φ (actU (rho St.D)) := by
    refine ⟨fun x hx y hy => ?_, fun x y y' hxy => ?_⟩
    · have hxH : (x : G) ∈ H :=
        St.hyp.base.lOne_sup_le ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) hx)
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V H hxH) y).1 hy
    · have hxLU : (x : G) ∈ L ⊔ conjClosure V H :=
        (le_sup_left : L ≤ L ⊔ conjClosure V H) (lOne_le_L x.2)
      have hyLU : (y : G) ∈ L ⊔ conjClosure V H :=
        (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) y.2
      have hy'LU : (y' : G) ∈ L ⊔ conjClosure V H :=
        (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) y'.2
      have hΦx : St.Phi ⟨(x : G), hxLU⟩ = rho St.D x := St.Phi_of_L ⟨(x : G), lOne_le_L x.2⟩
      have key : St.betaU y' = rho St.D x * St.betaU y * (rho St.D x)⁻¹ := by
        have e : (⟨(y' : G), hy'LU⟩ : ↥(L ⊔ conjClosure V H)) =
            ⟨(x : G), hxLU⟩ * ⟨(y : G), hyLU⟩ * ⟨(x : G), hxLU⟩⁻¹ := Subtype.ext hxy.symm
        calc St.betaU y' = St.Phi ⟨(y' : G), hy'LU⟩ := rfl
          _ = St.Phi (⟨(x : G), hxLU⟩ * ⟨(y : G), hyLU⟩ * ⟨(x : G), hxLU⟩⁻¹) := by rw [e]
          _ = St.Phi ⟨(x : G), hxLU⟩ * St.Phi ⟨(y : G), hyLU⟩ * (St.Phi ⟨(x : G), hxLU⟩)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
          _ = rho St.D x * St.betaU y * (rho St.D x)⁻¹ := by
            rw [hΦx, St.betaU_apply]
      have hv : grpU_tqHom (GaloisField 2 n) (φ y) = St.betaU y := hφ y
      apply grpU_tqHom_injective (GaloisField 2 n)
      rw [hφ y', key, ← hv]
      exact conj_tqv ((l1Rep St).stab x) (Multiplicative.toAdd (φ y))
  have hmod := ModChain.transport (ord := ord) (grpU_range_top hφs) hE (chain_U (l1Rep St)) le_top
  rw [grpU_pre_bot (inf_le_left : gW V H L ≤ conjClosure V H) hker,
    grpU_pre_all (φ := φ) (M := ⊤) (fun _ => AddSubgroup.mem_top _)] at hmod
  exact hmod

end GroupU

end CFSG.Quasithin.RonanG25
