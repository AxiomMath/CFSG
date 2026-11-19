module

public import CFSG.RankThree.GF2n.Smith81.Sec1Main
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.GF2n.Smith81.Sec1Local

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem sq_mem_Q_of_centralizes (H : StrothHyp M Q Z) {y : G} (hyM : y ∈ M)
    (hyZ : ∀ z ∈ Z, y * z * y⁻¹ = z) (hy4 : y ^ 4 = 1)
    (hy : ∀ c ∈ Q, y ^ 2 * c = c * y ^ 2 → y * c = c * y) : y ^ 2 ∈ Q := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨T, hTπ, hTQ, hTB⟩ := hD.linear_of_centralizes hyM hyZ
  obtain ⟨n, k, -, hcp⟩ := H.cp
  have hZ2 : ∀ z ∈ Z, z ^ 2 = 1 := sq_eq_one_of_cp hcp
  have h2 : ∀ e : M₀.E, e + e = 0 := fun e => by
    rw [← two_smul K e, CharTwo.two_eq_zero, zero_smul]
  have hneg : ∀ e : M₀.E, -e = e := fun e => neg_eq_of_add_eq_zero_right (h2 e)
  have hy2M : y ^ 2 ∈ M := M.pow_mem hyM 2
  have hT2π : ∀ c ∈ Q, M₀.π (y ^ 2 * c * (y ^ 2)⁻¹) = T (T (M₀.π c)) := by
    intro c hc
    have : y ^ 2 * c * (y ^ 2)⁻¹ = y * (y * c * y⁻¹) * y⁻¹ := by rw [pow_two]; group
    rw [this, hTπ _ (conj_mem_Q H hyM hc), hTπ c hc]
  by_cases hW : ∀ e, T (T e) = e
  · refine H.centralizer_Qt _ hy2M fun c hc => ?_
    have e : ⁅y ^ 2, c⁆ = (y ^ 2 * c * (y ^ 2)⁻¹) * c⁻¹ := by simp only [commutatorElement_def]
    have hsc : y ^ 2 * c * (y ^ 2)⁻¹ ∈ Q := conj_mem_Q H hy2M hc
    rw [e]
    refine (M₀.π_ker _ (Q.mul_mem hsc (Q.inv_mem hc))).mp ?_
    rw [M₀.π_mul _ hsc _ (Q.inv_mem hc), Tim79.QuadModel.pi_inv M₀ hc, hT2π c hc, hW,
      add_neg_cancel]
  exfalso
  push Not at hW
  obtain ⟨e, he⟩ := hW
  have hT4 : ∀ f, T (T (T (T f))) = f := by
    intro f
    obtain ⟨c, hc, rfl⟩ := M₀.π_surj f
    have h := congrArg M₀.π (show y ^ 4 * c * (y ^ 4)⁻¹ = c by rw [hy4]; group)
    have : y ^ 4 * c * (y ^ 4)⁻¹ = y ^ 2 * (y ^ 2 * c * (y ^ 2)⁻¹) * (y ^ 2)⁻¹ := by group
    rw [this, hT2π _ (conj_mem_Q H hy2M hc), hT2π c hc] at h
    exact h
  obtain ⟨N, hN⟩ : ∃ N : M₀.E → M₀.E, ∀ f, N f = T f + f := ⟨_, fun _ => rfl⟩
  have hNN : ∀ f, N (N f) = T (T f) + f := by
    intro f
    rw [hN, hN, map_add]
    calc T (T f) + T f + (T f + f) = T (T f) + f + (T f + T f) := by abel
      _ = T (T f) + f := by rw [h2, add_zero]
  have hN0 : ∀ f, N f = 0 → T f = f := by
    intro f hf
    rw [hN] at hf
    exact (eq_neg_of_add_eq_zero_left hf).trans (hneg f)
  have hNNNN : ∀ f, N (N (N (N f))) = 0 := by
    intro f
    rw [hNN, hNN, map_add, map_add, hT4]
    calc f + T (T f) + (T (T f) + f) = (f + f) + (T (T f) + T (T f)) := by abel
      _ = 0 := by rw [h2, h2, add_zero]
  have hπu : ∀ c ∈ Q, ⁅y, c⁆ ∈ Q ∧ M₀.π ⁅y, c⁆ = N (M₀.π c) := by
    intro c hc
    have e : ⁅y, c⁆ = (y * c * y⁻¹) * c⁻¹ := by simp only [commutatorElement_def]
    have hyc := conj_mem_Q H hyM hc
    refine ⟨by rw [e]; exact Q.mul_mem hyc (Q.inv_mem hc), ?_⟩
    rw [e, M₀.π_mul _ hyc _ (Q.inv_mem hc), Tim79.QuadModel.pi_inv M₀ hc, hTπ c hc, hneg, hN]
  have hconj : ∀ c ∈ Q, y * ⁅y, c⁆ = ⁅y, c⁆ * y →
      y ^ 2 * c * (y ^ 2)⁻¹ = ⁅y, c⁆ ^ 2 * c := by
    intro c hc hu
    have h1 : y * c * y⁻¹ = ⁅y, c⁆ * c := by simp only [commutatorElement_def]; group
    have h3 : y * ⁅y, c⁆ * y⁻¹ = ⁅y, c⁆ := by rw [hu]; group
    calc y ^ 2 * c * (y ^ 2)⁻¹ = y * (y * c * y⁻¹) * y⁻¹ := by rw [pow_two]; group
      _ = y * (⁅y, c⁆ * c) * y⁻¹ := by rw [h1]
      _ = (y * ⁅y, c⁆ * y⁻¹) * (y * c * y⁻¹) := by group
      _ = ⁅y, c⁆ ^ 2 * c := by rw [h3, h1, pow_two]; group
  have hii : ∀ c ∈ Q, N (M₀.π c) = 0 → y ^ 2 * c = c * y ^ 2 := by
    intro c hc h0
    obtain ⟨huQ, hu⟩ := hπu c hc
    have huZ : ⁅y, c⁆ ∈ Z := (M₀.π_ker _ huQ).mp (by rw [hu, h0])
    have hyu : y * ⁅y, c⁆ = ⁅y, c⁆ * y := by
      have := hyZ _ huZ
      calc y * ⁅y, c⁆ = (y * ⁅y, c⁆ * y⁻¹) * y := by group
        _ = ⁅y, c⁆ * y := by rw [this]
    have := hconj c hc hyu
    rw [hZ2 _ huZ, one_mul] at this
    calc y ^ 2 * c = (y ^ 2 * c * (y ^ 2)⁻¹) * y ^ 2 := by group
      _ = c * y ^ 2 := by rw [this]
  have hiv : ∀ c ∈ Q, N (N (M₀.π c)) = 0 → M₀.Qf (N (M₀.π c)) = 0 → N (M₀.π c) = 0 := by
    intro c hc hNN0 hQf0
    obtain ⟨huQ, hu⟩ := hπu c hc
    have hyu : y * ⁅y, c⁆ = ⁅y, c⁆ * y :=
      hy _ huQ (hii _ huQ (by rw [hu]; exact hNN0))
    have hsq : ⁅y, c⁆ ^ 2 = 1 := (GM.sq_eq_one_iff hD huQ).mpr (by rw [hu]; exact hQf0)
    have h5 := hconj c hc hyu
    rw [hsq, one_mul] at h5
    have hyc : y * c = c * y := hy c hc (by
      calc y ^ 2 * c = (y ^ 2 * c * (y ^ 2)⁻¹) * y ^ 2 := by group
        _ = c * y ^ 2 := by rw [h5])
    have : T (M₀.π c) = M₀.π c := by
      rw [← hTπ c hc]; congr 1; rw [hyc]; group
    rw [hN, this, h2]
  have hWe : N (N e) ≠ 0 := by
    rw [hNN]; intro h; exact he ((eq_neg_of_add_eq_zero_left h).trans (hneg e))
  obtain ⟨w, hNNw, hNw⟩ : ∃ w, N (N (N w)) = 0 ∧ N (N w) ≠ 0 := by
    by_cases h3 : N (N (N e)) = 0
    · exact ⟨e, h3, hWe⟩
    · exact ⟨N e, by rw [hNNNN], h3⟩
  have hQfv : M₀.Qf (N (N w)) = 0 := by
    have hTv : T (N w) = N (N w) + N w := by
      rw [hN (N w), add_assoc, h2, add_zero]
    have h1 := hTQ (N w)
    rw [hTv, M₀.Qf_add] at h1
    have hTNv : T (N (N w)) = N (N w) := hN0 _ hNNw
    have hB : M₀.B (N (N w)) (N w) = 0 := by
      generalize N (N w) = u at hTNv ⊢
      rw [hN w, map_add, ← hTNv, hTB, hTNv, ← two_mul, CharTwo.two_eq_zero, zero_mul]
    rw [hB, add_zero] at h1
    have h0 : M₀.Qf (N (N w)) + M₀.Qf (N w) = 0 + M₀.Qf (N w) := by rw [h1, zero_add]
    exact add_right_cancel h0
  obtain ⟨c, hc, hcπ⟩ := M₀.π_surj (N w)
  exact hNw (by
    have := hiv c hc (by rw [hcπ]; exact hNNw) (by rw [hcπ]; exact hQfv)
    rwa [hcπ] at this)

variable {X : Subgroup G} {x : G}

theorem Lx_sq_eq_one (hs : Sit M Q Z X x) (hQ : Q ⊓ QB X = ⊥) {l : G} (hl : l ∈ Lx M X) :
    l ^ 2 = 1 := by
  have h12 := smith_1_12 hs
  by_contra hl2
  obtain ⟨-, -, hd⟩ := smith_1_15_direct hs h12 hQ
  obtain ⟨hl2X, hCl⟩ := hd l hl hl2
  have hK2 := Kx_eq_of_mem hs h12 hl2X hl2
  have hlH := Lx_le_H0 hs h12 hl
  have hlM : l ∈ M := hlH.1
  have hlZ : ∀ z ∈ Z, l * z * l⁻¹ = z := by
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp hlH.2 z hz
    rw [← this]; group
  have hl4 : l ^ 4 = 1 := by
    have := hs.X_sq _ hl2X
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two (l ^ 2), this]
  have hsq := sq_mem_Q_of_centralizes hs.hyp hlM hlZ hl4 (fun c hc hcomm => by
    have hcK : c ∈ Kx Q X := by
      rw [hK2]
      exact ⟨hc, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rw [← hCl] at hcK
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hcK).2).symm)
  have : l ^ 2 ∈ X ⊓ Q := ⟨hl2X, hsq⟩
  rw [h12.2, Subgroup.mem_bot] at this
  exact hl2 this

theorem Kx_sq_eq_one (hs : Sit M Q Z X x) (hQ : Q ⊓ QB X = ⊥) {k : G} (hk : k ∈ Kx Q X) :
    k ^ 2 = 1 := by
  have h12 := smith_1_12 hs
  have H := hs.hyp
  by_contra hk2
  obtain ⟨hcomm, -, -⟩ := smith_1_15_direct hs h12 hQ
  obtain ⟨g, hgX, hgQ, hgM⟩ := hs.QB_eq
  obtain ⟨hkQ, hkN⟩ := Subgroup.mem_inf.mp hk
  have hk2Z : k ^ 2 ∈ Z := sq_mem_Z H hkQ
  have hkX := Kx_le_centralizer_X hs h12 hk
  obtain ⟨k', hk'⟩ : ∃ k', k' = g⁻¹ * k * g := ⟨_, rfl⟩
  have hk'M : k' ∈ M := by
    rw [hgM, mem_conjSubgroup] at hkN; rw [hk']; exact hkN
  have hk'Z : ∀ z ∈ Z, k' * z * k'⁻¹ = z := by
    intro z hz
    have hzX : g * z * g⁻¹ ∈ X := by
      rw [hgX, mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]; exact hz
    have h := Subgroup.mem_centralizer_iff.mp hkX _ hzX
    calc k' * z * k'⁻¹ = g⁻¹ * (k * (g * z * g⁻¹) * k⁻¹) * g := by rw [hk']; group
      _ = z := by rw [← h]; group
  have hk'pow : ∀ m : ℕ, k' ^ m = g⁻¹ * k ^ m * g := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, pow_succ, hk']; group
  have hk'4 : k' ^ 4 = 1 := by
    rw [hk'pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Z_sq H hk2Z]; group
  have hsq := sq_mem_Q_of_centralizes H hk'M hk'Z hk'4 (fun c hc hc2 => by
    obtain ⟨d, hd⟩ : ∃ d, d = g * c * g⁻¹ := ⟨_, rfl⟩
    have hdQ : d ∈ QB X := by
      rw [hgQ, mem_conjSubgroup, hd, show g⁻¹ * (g * c * g⁻¹) * g = c by group]; exact hc
    have hd2 : k ^ 2 * d = d * k ^ 2 := by
      have h' : g⁻¹ * k ^ 2 * g * c = c * (g⁻¹ * k ^ 2 * g) := by rw [← hk'pow]; exact hc2
      rw [hd]
      calc k ^ 2 * (g * c * g⁻¹) = g * (g⁻¹ * k ^ 2 * g * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * k ^ 2 * g)) * g⁻¹ := by rw [h']
        _ = (g * c * g⁻¹) * k ^ 2 := by group
    have hdM : d ∈ M := by
      have := Tim77.mem_normalizer_of_commute_of_isTI H.ti hk2Z hk2 hd2.symm
      rwa [H.normalizer_Z.1] at this
    have hkd := hcomm k hk d ⟨hdQ, hdM⟩
    calc k' * c = g⁻¹ * (k * d) * g := by rw [hk', hd]; group
      _ = g⁻¹ * (d * k) * g := by rw [hkd]
      _ = c * k' := by rw [hk', hd]; group)
  have hk2Qx : k ^ 2 ∈ QB X := by
    rw [hgQ, mem_conjSubgroup]
    rw [hk'pow] at hsq
    exact hsq
  have : k ^ 2 ∈ Q ⊓ QB X := ⟨Q.pow_mem hkQ 2, hk2Qx⟩
  rw [hQ, Subgroup.mem_bot] at this
  exact hk2 this

omit [Finite G] in
private theorem isElemAbelian_two_of_sq {A : Subgroup G} (h : ∀ a ∈ A, a ^ 2 = 1) :
    IsElemAbelian 2 A := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, h⟩
  have ha := h a a.2
  have hb := h b b.2
  have hab := h _ (A.mul_mem a.2 b.2)
  rw [pow_two] at ha hb hab
  have ha' : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hb' : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have := inv_eq_of_mul_eq_one_left hab
  rw [mul_inv_rev, ha', hb'] at this
  simpa using this.symm

theorem smith_1_15_elem (hs : Sit M Q Z X x) (hQ : Q ⊓ QB X = ⊥) :
    IsElemAbelian 2 (Kx Q X ⊔ Lx M X) ∧ (∀ k ∈ Kx Q X, ∀ l ∈ Lx M X, k * l = l * k) ∧
      Kx Q X ⊓ Lx M X = ⊥ := by
  obtain ⟨hcomm, hinf, -⟩ := smith_1_15_direct hs (smith_1_12 hs) hQ
  exact ⟨IsElemAbelian.sup_of_commute
    (isElemAbelian_two_of_sq fun k hk => Kx_sq_eq_one hs hQ hk)
    (isElemAbelian_two_of_sq fun l hl => Lx_sq_eq_one hs hQ hl) hcomm, hcomm, hinf⟩

@[expose] def Smith115DimStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z X : Subgroup G) (x : G), Sit M Q Z X x →
    ∀ n : ℕ, Width Q Z n → Q ⊓ QB X = ⊥ → HasDim Q Z n x ∨ (Odd n ∧ HasDim Q Z (n - 1) x)

@[expose] def Smith115Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z X : Subgroup G) (x : G), Sit M Q Z X x →
    ∀ n : ℕ, Width Q Z n → Q ⊓ QB X = ⊥ →
      IsElemAbelian 2 (Kx Q X ⊔ Lx M X) ∧ (∀ k ∈ Kx Q X, ∀ l ∈ Lx M X, k * l = l * k) ∧
        Kx Q X ⊓ Lx M X = ⊥ ∧ (HasDim Q Z n x ∨ (Odd n ∧ HasDim Q Z (n - 1) x))

theorem smith115Statement_of_dim (h : Smith115DimStatement) : Smith115Statement :=
  fun G _ _ M Q Z X x hs n hw hQ =>
    ⟨(smith_1_15_elem hs hQ).1, (smith_1_15_elem hs hQ).2.1, (smith_1_15_elem hs hQ).2.2,
      h G M Q Z X x hs n hw hQ⟩

end CFSG.RankThree.GF2n.Smith81
