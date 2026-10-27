module

public import CFSG.Quasithin.Background.Harris.R1.InvolPair
public import CFSG.Quasithin.Background.Harris.R1.InvolKer
public import CFSG.Quasithin.Background.Harris.R1.Parity

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  [Fintype Ω] [DecidableEq Ω]

theorem exists_comm_not_Zs (C : FamCtx K1 L2 S Zs Ω) (hΩ : Fintype.card Ω = 5)
    (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hQ : pCoreOf 2 (K1 ⊔ S) = vBeta K1 L2 S Zs) (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs)
    {g : G} (hgZ : g ∉ Subgroup.normalizer (Zs : Set G)) {b : G}
    (hbQ : b ∈ pCoreOf 2 (L2 ⊔ S)) (hbW : b ∈ conjSub g (vBeta K1 L2 S Zs))
    (hbV : b ∉ C.D.Vf (conjClosure Zs L2) C.D.pt) :
    ∃ a ∈ vBeta K1 L2 S Zs, a ∈ pCoreOf 2 (L2 ⊔ S) ∧ b * a * b⁻¹ * a⁻¹ ∉ Zs := by
  by_contra hcon
  push Not at hcon
  have hbsup : b ∈ K1 ⊔ S := Subgroup.mem_sup_right (C.pCore_le_S hbQ)
  have hone := FamCtxLemmas.permHom_eq_one_of_comm_Zs C hΩ hbsup (pCore_centralizes_Vf C hbQ)
    (fun i j hi hj _ => hcon _ ((vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U i) (C.zf_mem_U j))
      (C.zf_mul_mem_pCore hi hj))
  have hM : b ∈ C.kerM := (permHom_eq_one_iff C ⟨b, hbsup⟩).1 hone
  exact hbV (mem_Vf_of_mem_inter C hΩ hcen hgZ (kerM_le_vBeta C hΩ hL24 hQ hQK hM) hbQ hbW)


theorem exists_involution_outside_pCore (C : FamCtx K1 L2 S Zs Ω) (hΩ : Fintype.card Ω = 5)
    (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hQ : pCoreOf 2 (K1 ⊔ S) = vBeta K1 L2 S Zs) (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) :
    ∃ t ∈ K1, t * t = 1 ∧ t ∉ pCoreOf 2 K1 := by
  obtain ⟨i₀, j₀, hij₀⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Ω)
  set W := vBeta K1 L2 S Zs with hW
  set Q := pCoreOf 2 (L2 ⊔ S) with hQdef
  set Vc := C.D.Vf (conjClosure Zs L2) C.D.pt with hVc
  set z := C.cm i₀ j₀ with hzdef
  have hz1 : z ≠ 1 := C.cm_ne_one hij₀
  have hzZ : z ∈ Zs := C.cm_mem i₀ j₀
  have hzz : z * z = 1 := C.Zs_sq hzZ
  have hZV : Zs ≤ Vc := C.Zs_le_Vf C.D.pt
  obtain ⟨g, hgL, hgZ⟩ : ∃ g ∈ L2, g ∉ Subgroup.normalizer (Zs : Set G) := by
    by_contra h
    push Not at h
    exact C.h.Z_not_norm (fun x hx => h x hx)
  have hgP : g ∈ L2 ⊔ S := Subgroup.mem_sup_left hgL
  have hgiP : g⁻¹ ∈ L2 ⊔ S := (L2 ⊔ S).inv_mem hgP
  have hgiZ : g⁻¹ ∉ Subgroup.normalizer (Zs : Set G) := fun h => hgZ (by
    simpa using (Subgroup.normalizer (Zs : Set G)).inv_mem h)
  have hmove : g * z * g⁻¹ ≠ z := g_move_of_not_mem_normalizer C hij₀ hgZ
  have hQn : ∀ p ∈ L2 ⊔ S, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q := fun p hp q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (L2 ⊔ S) hp) q).mp hq
  have hVn : ∀ p ∈ L2 ⊔ S, ∀ v ∈ Vc, p * v * p⁻¹ ∈ Vc := by
    intro p hp v hv
    rw [hVc, C.Vf_pt] at hv ⊢
    exact (Subgroup.mem_normalizer_iff.mp (C.amalgamHypV.normalizes hp) v).mp hv
  have hQc : ∀ q ∈ Q, ∀ v ∈ Vc, v * q = q * v := fun q hq => pCore_centralizes_Vf C hq
  have hVcomm : ∀ x ∈ Vc, ∀ y ∈ Vc, x * y = y * x := fun x hx y hy => C.Vf_comm hx hy
  have hVsq : ∀ x ∈ Vc, x * x = 1 := fun x hx => C.Vf_sq hx
  set z' := g * z * g⁻¹ with hz'def
  have hz'V : z' ∈ Vc := hVn g hgP z (hZV hzZ)
  have hz'sq : z' * z' = 1 := hVsq _ hz'V
  have hzV : z ∈ Vc := hZV hzZ
  have hzz' : z * z' = z' * z := hVcomm _ hzV _ hz'V
  have hZc : ∀ x ∈ Zs, x = 1 ∨ x = z := fun x hx => Zs_eq_one_or C hij₀ hx
  have hsqz : ∀ x ∈ W, x ∈ Q → x ∉ Vc → x * x = z := by
    intro x hxW hxQ hxV
    rcases hZc _ (FamCtxLemmas.sq_mem_Zs C hij₀ hxW) with h | h
    · exact absurd (FamCtxLemmas.mem_Vf_pt_of_sq_eq_one C hΩ hcen hxW
        (hQc x hxQ _ (C.zf_mem C.D.pt)).symm h) hxV
    · exact h
  have hVcases : ∀ v ∈ Vc, v = 1 ∨ v = z ∨ v = z' ∨ v = z * z' := by
    intro v hv
    have hz'nZ : z' ∉ Zs := by
      intro h
      rcases hZc _ h with h | h
      · exact hz1 (by
          have : g⁻¹ * z' * g = z := by rw [hz'def]; group
          rw [h] at this; simpa using this.symm)
      · exact hmove h
    have hz'e : ∃ δ ∈ Zs, z' = C.zf C.D.pt * δ := by
      rcases C.Vf_eq hz'V with h | h
      · exact absurd h hz'nZ
      · exact ⟨_, h, by group⟩
    obtain ⟨δ, hδ, hz'δ⟩ := hz'e
    rcases C.Vf_eq hv with h | h
    · rcases hZc _ h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨ε, hε, hvε⟩ : ∃ ε ∈ Zs, v = C.zf C.D.pt * ε := ⟨_, h, by group⟩
      have hv' : v = z' * (δ⁻¹ * ε) := by rw [hvε, hz'δ]; group
      have hδε : δ⁻¹ * ε ∈ Zs := Zs.mul_mem (Zs.inv_mem hδ) hε
      rcases hZc _ hδε with h1 | h1
      · rw [h1, mul_one] at hv'; exact Or.inr (Or.inr (Or.inl hv'))
      · rw [h1] at hv'
        exact Or.inr (Or.inr (Or.inr (by rw [hv', hzz'])))
  obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Ω) C.D.pt
  obtain ⟨j, -, hj, -, hij, -, -⟩ := exists_two_ne (by omega : 4 ≤ Fintype.card Ω) C.D.pt i
  have hinv : ∀ l : Ω, (C.zf l)⁻¹ = C.zf l := fun l =>
    inv_eq_of_mul_eq_one_right (C.Vf_sq (C.zf_mem l))
  have ha₀W : C.zf i * C.zf j ∈ W := W.mul_mem (C.zf_mem_U i) (C.zf_mem_U j)
  have ha₀Q : C.zf i * C.zf j ∈ Q := C.zf_mul_mem_pCore hi hj
  have ha₀sq : (C.zf i * C.zf j) * (C.zf i * C.zf j) = z := by
    have h1 : C.cm i j = z := C.cm_const hij₀ hij
    rw [← h1]
    unfold FamCtx.cm
    rw [hinv i, hinv j]
    group
  set a₀ := C.zf i * C.zf j with ha₀
  have ha₀V : a₀ ∉ Vc := fun h => hz1 (by rw [← ha₀sq]; exact hVsq _ h)
  have hb''Q : g⁻¹ * a₀ * g ∈ Q := by
    have := hQn g⁻¹ hgiP a₀ ha₀Q
    simpa using this
  have hb''W : g⁻¹ * a₀ * g ∈ conjSub g⁻¹ W := by
    rw [mem_conjSub]
    have e : (g⁻¹)⁻¹ * (g⁻¹ * a₀ * g) * g⁻¹ = a₀ := by group
    rw [e]; exact ha₀W
  have hb''V : g⁻¹ * a₀ * g ∉ Vc := by
    intro h
    have := hVn g hgP _ h
    have e : g * (g⁻¹ * a₀ * g) * g⁻¹ = a₀ := by group
    rw [e] at this
    exact ha₀V this
  obtain ⟨a'', ha''W, ha''Q, ha''c⟩ :=
    exists_comm_not_Zs C hΩ hL24 hcen hQ hQK hgiZ hb''Q hb''W hb''V
  set b0 := g * a'' * g⁻¹ with hb0
  have hb0Q : b0 ∈ Q := hQn g hgP a'' ha''Q
  have hb0W : b0 ∈ conjSub g W := by
    rw [mem_conjSub]
    have e : g⁻¹ * (g * a'' * g⁻¹) * g = a'' := by group
    rw [e]; exact ha''W
  have hx0 : b0 * a₀ * b0⁻¹ * a₀⁻¹ ∉ conjSub g Zs := by
    intro h
    apply ha''c
    rw [mem_conjSub] at h
    have e : (g⁻¹ * a₀ * g) * a'' * (g⁻¹ * a₀ * g)⁻¹ * a''⁻¹ =
        (g⁻¹ * (b0 * a₀ * b0⁻¹ * a₀⁻¹) * g)⁻¹ := by rw [hb0]; group
    rw [e]
    exact Zs.inv_mem h
  have hb0V : b0 ∉ Vc := by
    intro h
    apply hx0
    have hc := hQc a₀ ha₀Q b0 h
    have : b0 * a₀ * b0⁻¹ * a₀⁻¹ = 1 := by
      calc b0 * a₀ * b0⁻¹ * a₀⁻¹ = (a₀ * b0) * b0⁻¹ * a₀⁻¹ := by rw [hc]
        _ = 1 := by group
    rw [this]
    exact (conjSub g Zs).one_mem
  obtain ⟨a1, ha1W, ha1Q, ha1c⟩ := exists_comm_not_Zs C hΩ hL24 hcen hQ hQK hgZ hb0Q hb0W hb0V
  have hX : ∀ a ∈ W, a ∈ Q → b0 * a * b0⁻¹ * a⁻¹ ∈ Vc := fun a haW haQ =>
    comm_mem_Vf C hΩ hcen hgP hgZ haW haQ hb0Q hb0W
  have hXmul : ∀ a a', a ∈ W → a ∈ Q → a' ∈ W → a' ∈ Q →
      b0 * (a * a') * b0⁻¹ * (a * a')⁻¹ =
        (b0 * a * b0⁻¹ * a⁻¹) * (b0 * a' * b0⁻¹ * a'⁻¹) := by
    intro a a' haW haQ ha'W ha'Q
    have hc := hQc a haQ _ (hX a' ha'W ha'Q)
    calc b0 * (a * a') * b0⁻¹ * (a * a')⁻¹
        = (b0 * a * b0⁻¹ * a⁻¹) * (a * (b0 * a' * b0⁻¹ * a'⁻¹) * a⁻¹) := by group
      _ = _ := by rw [← hc]; group
  have hz'mem : z' ∈ conjSub g Zs := by
    rw [mem_conjSub]
    have e : g⁻¹ * z' * g = z := by rw [hz'def]; group
    rw [e]; exact hzZ
  have hsol : ∃ a ∈ W, a ∈ Q ∧ b0 * a * b0⁻¹ * a⁻¹ = z * z' := by
    rcases hVcases _ (hX a₀ ha₀W ha₀Q) with h0 | h0 | h0 | h0
    · exact (hx0 (by rw [h0]; exact (conjSub g Zs).one_mem)).elim
    · rcases hVcases _ (hX a1 ha1W ha1Q) with h1 | h1 | h1 | h1
      · exact (ha1c (by rw [h1]; exact Zs.one_mem)).elim
      · exact (ha1c (by rw [h1]; exact hzZ)).elim
      · refine ⟨a₀ * a1, W.mul_mem ha₀W ha1W, Q.mul_mem ha₀Q ha1Q, ?_⟩
        rw [hXmul _ _ ha₀W ha₀Q ha1W ha1Q, h0, h1]
      · exact ⟨a1, ha1W, ha1Q, h1⟩
    · exact (hx0 (by rw [h0]; exact hz'mem)).elim
    · exact ⟨a₀, ha₀W, ha₀Q, h0⟩
  obtain ⟨a, haW, haQ, hXa⟩ := hsol
  have hzz'1 : z * z' ≠ 1 := by
    intro h
    apply hmove
    have h1 : z' = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hzz
  have haV : a ∉ Vc := by
    intro h
    apply hzz'1
    rw [← hXa]
    have hc := hQc b0 hb0Q a h
    calc b0 * a * b0⁻¹ * a⁻¹ = (a * b0) * b0⁻¹ * a⁻¹ := by rw [hc]
      _ = 1 := by group
  have ha2 : a * a = z := hsqz a haW haQ haV
  have hb0sq : b0 * b0 = z' := by
    have hwW : g⁻¹ * b0 * g ∈ W := mem_conjSub.mp hb0W
    have hwQ : g⁻¹ * b0 * g ∈ Q := by
      have := hQn g⁻¹ hgiP b0 hb0Q
      simpa using this
    have hwV : g⁻¹ * b0 * g ∉ Vc := by
      intro h
      apply hb0V
      have := hVn g hgP _ h
      have e : g * (g⁻¹ * b0 * g) * g⁻¹ = b0 := by group
      rw [e] at this
      exact this
    have h1 := hsqz _ hwW hwQ hwV
    calc b0 * b0 = g * ((g⁻¹ * b0 * g) * (g⁻¹ * b0 * g)) * g⁻¹ := by group
      _ = z' := by rw [h1]
  have htt : (a * b0) * (a * b0) = 1 := by
    have hc : b0 * a = (z * z') * a * b0 := by
      calc b0 * a = (b0 * a * b0⁻¹ * a⁻¹) * a * b0 := by group
        _ = _ := by rw [hXa]
    have hza : (z * z') * a = a * (z * z') := hQc a haQ _ (Vc.mul_mem hzV hz'V)
    calc a * b0 * (a * b0) = a * (b0 * a) * b0 := by group
      _ = a * ((z * z') * a * b0) * b0 := by rw [hc]
      _ = (a * (z * z')) * a * (b0 * b0) := by group
      _ = ((z * z') * a) * a * (b0 * b0) := by rw [← hza]
      _ = (z * z') * (a * a) * (b0 * b0) := by group
      _ = (z * z') * z * z' := by rw [ha2, hb0sq]
      _ = z * (z' * z) * z' := by group
      _ = z * (z * z') * z' := by rw [← hzz']
      _ = (z * z) * (z' * z') := by group
      _ = 1 := by rw [hzz, hz'sq, one_mul]
  have hWK : W ≤ K1 := by rw [← hQK]; exact pCoreOf_le 2 K1
  obtain ⟨k, hk, m, hm, hbkm⟩ := exists_mul_of_mem_conj C hΩ hL24 hcen hgP hgZ hb0Q hb0W
  have hb0K : b0 ∈ K1 := by
    rw [hbkm]
    exact K1.mul_mem hk (hWK (kerM_le_vBeta C hΩ hL24 hQ hQK hm))
  refine ⟨a * b0, K1.mul_mem (hWK haW) hb0K, htt, fun h => ?_⟩
  rw [hQK] at h
  have hb0W' : b0 ∈ W := by
    have := W.mul_mem (W.inv_mem haW) h
    simpa using this
  exact hb0V (mem_Vf_of_mem_inter C hΩ hcen hgZ hb0W' hb0Q hb0W)

end CFSG.Quasithin.Background.Harris.R1
