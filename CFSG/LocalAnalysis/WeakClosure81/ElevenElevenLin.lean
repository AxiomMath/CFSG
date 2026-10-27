module

public import CFSG.Quasithin.Background.E6Sixteen
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

section Module

variable {W : Type*} [CommGroup W]

theorem two_mul_rkIdx_fixV_le_of_complement [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {b : MulAut W}
    (hb : b * b = 1) {A B : Subgroup W} (hsup : A ⊔ B = ⊤) (hA : ∀ a ∈ A, b a = a)
    (hB : ∀ x ∈ B, b x ∈ B) :
    2 * rkIdx (fixV (Subgroup.zpowers b)) ≤ rk ↥B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := fixV (Subgroup.zpowers b) with hF
  let f : W →* W :=
    { toFun := fun w => b w * w⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        show b (v * w) * (v * w)⁻¹ = b v * v⁻¹ * (b w * w⁻¹)
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hf : ∀ w, f w = b w * w⁻¹ := fun _ => rfl
  have hker : f.ker = F := by
    ext w
    rw [MonoidHom.mem_ker, hF, E6.mem_fixV_zpowers_iff', hf]
    exact mul_inv_eq_one
  have hinv : ∀ x : W, x⁻¹ = x := fun x => by
    have hx := hW x
    rw [sq] at hx
    exact inv_eq_of_mul_eq_one_right hx
  have hbb : ∀ w, b (b w) = w := fun w => by
    have := congrArg (fun φ : MulAut W => φ w) hb
    simpa [MulAut.mul_apply] using this
  have hrangeF : f.range ≤ F := by
    rintro _ ⟨w, rfl⟩
    rw [hF, E6.mem_fixV_zpowers_iff', hf]
    rw [map_mul, map_inv, hbb, hinv (b w), hinv w, mul_comm]
  have hrangeB : f.range ≤ B := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨a, ha, β, hβ, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [hf, map_mul, hA a ha]
    have e : a * b β * (a * β)⁻¹ = b β * β⁻¹ := by
      rw [mul_inv, mul_comm a (b β), mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact B.mul_mem (hB β hβ) (B.inv_mem hβ)
  have hrange : f.range ≤ F ⊓ B := le_inf hrangeF hrangeB
  have hidx : F.index = Nat.card f.range := by rw [← hker]; exact Subgroup.index_ker f
  have hFB : F ⊔ B = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine sup_le_sup_right ?_ B
    intro a ha
    rw [hF, E6.mem_fixV_zpowers_iff']
    exact hA a ha
  have hcard1 := rk_sup_add_rk_inf F B
  rw [hFB] at hcard1
  have h2 := rk_add_rkIdx F
  have hrkTop : rk (⊤ : Subgroup W) = rk W := by
    unfold rk
    rw [Subgroup.card_top]
  have hrkr : rkIdx F = rk f.range := by
    unfold rkIdx rk
    rw [hidx]
  have hle := rk_mono hrange
  omega


theorem vs_le_fixV_of_ne {s : ℕ} {Y : Fin s → Subgroup (MulAut W)} {Vs : Fin s → Subgroup W}
    (hind : iSupIndep Vs) (hVs : ∀ i, commSub ⊤ (Y i) = Vs i)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ Y i, ∀ b ∈ Y j, a * b = b * a)
    {i k : Fin s} (hik : i ≠ k) : Vs k ≤ fixV (Y i) := by
  intro v hv
  rw [mem_fixV]
  intro a ha
  have hdisj : Disjoint (Vs i) (Vs k) := hind.pairwiseDisjoint hik
  have hconj : (Y k).map (MulAut.conj a).toMonoidHom = Y k := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hc := hcomm i k hik a ha z hz
      have : (MulAut.conj a) z = z := by
        rw [MulAut.conj_apply, hc, mul_inv_cancel_right]
      show (MulAut.conj a) z ∈ Y k
      rw [this]
      exact hz
    · intro hy
      refine ⟨y, hy, ?_⟩
      have hc := hcomm i k hik a ha y hy
      show (MulAut.conj a) y = y
      rw [MulAut.conj_apply, hc, mul_inv_cancel_right]
  have hmap : (Vs k).map (a : MulAut W).toMonoidHom = Vs k := by
    rw [← hVs k, ← Asc81c.commSub_map_conj, hconj]
  have hav : a v ∈ Vs k := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hv
  have h1 : a v * v⁻¹ ∈ Vs i := by
    rw [← hVs i]
    exact Subgroup.subset_closure ⟨a, ha, v, Subgroup.mem_top _, rfl⟩
  have h2 : a v * v⁻¹ ∈ Vs k := (Vs k).mul_mem hav ((Vs k).inv_mem hv)
  have h3 : a v * v⁻¹ = 1 := Subgroup.mem_bot.1 (hdisj.le_bot ⟨h1, h2⟩)
  exact mul_inv_eq_one.1 h3


theorem rkIdx_fixV_le_of_fixes_rest [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {s : ℕ}
    {Y : Fin s → Subgroup (MulAut W)} {Vs : Fin s → Subgroup W} {Gb : Subgroup (MulAut W)}
    (hind : iSupIndep Vs) (hsup : ⨆ i, Vs i = ⊤) (hne : ∀ i, Vs i ≠ ⊥)
    (hVs : ∀ i, commSub ⊤ (Y i) = Vs i)
    (hperm : ∀ φ ∈ Gb, ∀ i, ∃ j, (Y i).map (MulAut.conj φ).toMonoidHom = Y j)
    {i₀ j₀ : Fin s} {t : MulAut W} (ht : t ∈ Gb) (ht2 : orderOf t = 2)
    (hfix : ∀ k, k ≠ i₀ → k ≠ j₀ → ∀ w ∈ Vs k, t w = w) :
    2 * rkIdx (fixV (Subgroup.zpowers t)) ≤ rk ↥(Vs i₀ ⊔ Vs j₀) := by
  have htt : t * t = 1 := by rw [← sq, ← ht2]; exact pow_orderOf_eq_one t
  have htperm : ∀ i, ∃ j, (Vs i).map (t : MulAut W).toMonoidHom = Vs j := by
    intro i
    obtain ⟨j, hj⟩ := hperm t ht i
    refine ⟨j, ?_⟩
    rw [← hVs i, ← hVs j, ← hj, Asc81c.commSub_map_conj]
  set B := Vs i₀ ⊔ Vs j₀ with hBdef
  have hjmem : ∀ i, (i = i₀ ∨ i = j₀) →
      ∃ j, (j = i₀ ∨ j = j₀) ∧ (Vs i).map (t : MulAut W).toMonoidHom = Vs j := by
    intro i hi
    obtain ⟨j, hj⟩ := htperm i
    refine ⟨j, ?_, hj⟩
    by_contra hcon
    obtain ⟨hj1, hj2⟩ := not_or.1 hcon
    apply hne i
    rw [eq_bot_iff]
    intro v hv
    have htv : t v ∈ Vs j := by
      rw [← hj]
      exact Subgroup.mem_map_of_mem _ hv
    have h2 : t v = v := t.injective (hfix j hj1 hj2 _ htv)
    have hij : i ≠ j := by
      rcases hi with h | h
      · rw [h]; exact fun h' => hj1 h'.symm
      · rw [h]; exact fun h' => hj2 h'.symm
    have hdisj : Disjoint (Vs i) (Vs j) := hind.pairwiseDisjoint hij
    exact hdisj.le_bot ⟨hv, h2 ▸ htv⟩
  have himg : ∀ i, (i = i₀ ∨ i = j₀) → ∀ v ∈ Vs i, t v ∈ B := by
    intro i hi v hv
    obtain ⟨j, hj, hjeq⟩ := hjmem i hi
    have htv : t v ∈ Vs j := by
      rw [← hjeq]
      exact Subgroup.mem_map_of_mem _ hv
    rcases hj with h | h
    · rw [h] at htv
      exact Subgroup.mem_sup_left htv
    · rw [h] at htv
      exact Subgroup.mem_sup_right htv
  have hB : ∀ x ∈ B, t x ∈ B := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul]
    exact B.mul_mem (himg i₀ (Or.inl rfl) y hy) (himg j₀ (Or.inr rfl) z hz)
  set A : Subgroup W := ⨆ k, ⨆ (_ : k ≠ i₀ ∧ k ≠ j₀), Vs k with hAdef
  have hA : ∀ a ∈ A, t a = a := by
    have hle : A ≤ fixV (Subgroup.zpowers t) := by
      refine iSup₂_le fun k hk => ?_
      intro w hw
      rw [E6.mem_fixV_zpowers_iff']
      exact hfix k hk.1 hk.2 w hw
    intro a ha
    exact E6.mem_fixV_zpowers_iff'.1 (hle ha)
  have hsup' : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine iSup_le fun k => ?_
    by_cases h1 : k = i₀
    · subst h1
      exact le_sup_of_le_right le_sup_left
    by_cases h2 : k = j₀
    · subst h2
      exact le_sup_of_le_right le_sup_right
    exact le_sup_of_le_left (le_iSup₂_of_le k ⟨h1, h2⟩ le_rfl)
  exact two_mul_rkIdx_fixV_le_of_complement hW htt hsup' hA hB


theorem even_card_of_two_factors [Finite W] {s : ℕ} {Y : Fin s → Subgroup (MulAut W)}
    {Gb : Subgroup (MulAut W)}
    (hperm : ∀ φ ∈ Gb, ∀ i, ∃ j, (Y i).map (MulAut.conj φ).toMonoidHom = Y j)
    {i₀ j₀ : Fin s} (hall : ∀ k, k = i₀ ∨ k = j₀) (hne : Y i₀ ≠ Y j₀) {φ : MulAut W}
    (hφ : φ ∈ Gb) (hφ' : (Y i₀).map (MulAut.conj φ).toMonoidHom = Y j₀) :
    Even (Nat.card Gb) := by
  have hφ10 : (Y j₀).map (MulAut.conj φ).toMonoidHom = Y i₀ := by
    obtain ⟨j, hj⟩ := hperm φ hφ j₀
    rcases hall j with h0 | h1
    · rw [h0] at hj
      exact hj
    · exfalso
      rw [h1] at hj
      exact hne (Subgroup.map_injective (MulAut.conj φ).injective (hφ'.trans hj.symm))
  have hstep : ∀ k : ℕ, (Y i₀).map (MulAut.conj (φ ^ (k + 1))).toMonoidHom =
      ((Y i₀).map (MulAut.conj (φ ^ k)).toMonoidHom).map (MulAut.conj φ).toMonoidHom := by
    intro k
    rw [pow_succ', map_mul, Subgroup.map_map]
    rfl
  have horb : ∀ k : ℕ, (Y i₀).map (MulAut.conj (φ ^ (2 * k))).toMonoidHom = Y i₀ ∧
      (Y i₀).map (MulAut.conj (φ ^ (2 * k + 1))).toMonoidHom = Y j₀ := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [mul_zero, pow_zero, map_one]
        exact Subgroup.map_id _
      · rw [mul_zero, zero_add, pow_one]
        exact hφ'
    | succ k ih =>
      have e1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      have h1 : (Y i₀).map (MulAut.conj (φ ^ (2 * (k + 1)))).toMonoidHom = Y i₀ := by
        rw [e1, hstep, ih.2]
        exact hφ10
      refine ⟨h1, ?_⟩
      rw [hstep, h1]
      exact hφ'
  have hev : Even (orderOf φ) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨k, hk⟩ := hodd
    have h1 := (horb k).2
    rw [← hk, pow_orderOf_eq_one, map_one] at h1
    exact hne ((Subgroup.map_id (Y i₀)).symm.trans h1)
  have hdvd := Subgroup.orderOf_dvd_natCard Gb hφ
  exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 hev).trans hdvd)


end Module

end CFSG.LocalAnalysis.WeakClosure81
