module

public import CFSG.Quasithin.H13.NQS134EA
public import CFSG.Quasithin.H13.NQS1342
public import CFSG.Quasithin.H13.U3S1349L

public section

namespace CFSG.Quasithin.H13.NQS134

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem exists_mem_not_mem_of_lt {B : Subgroup G} (s : Finset G) (hs : s.card < Nat.card B) :
    ∃ b ∈ B, b ∉ s := by
  by_contra h
  push Not at h
  have hle : Nat.card B ≤ s.card := by
    calc Nat.card B = (B : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ (s : Set G).ncard := Set.ncard_le_ncard (fun b hb => h b hb) (Finset.finite_toSet _)
      _ = s.card := Set.ncard_coe_finset _
  omega

theorem P6_mul_self : ∀ x : P6, x * x = 1 := by decide

namespace End134

variable (S : A6.Setting134 G T L V)
include S

theorem psi_z_cases' {z : G} (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) :
    (S.frame.ψ ⟨z, hz.1⟩ : P6) = e0123 ∨ (S.frame.ψ ⟨z, hz.1⟩ : P6) = e45 := by
  obtain ⟨hzV, hW⟩ := S.mem_V1_iff.1 hz
  rcases W1_cases _ (S.frame.ψ ⟨z, hzV⟩).2 hW with h | h | h | h
  · exfalso
    have h1 : S.frame.ψ ⟨z, hz.1⟩ = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h1
    have h2 : z = 1 := congrArg Subtype.val h1
    exact hzL (h2 ▸ one_mem _)
  · exfalso
    have h1 : S.frame.ψ ⟨z, hz.1⟩ = S.frame.ψ ⟨S.zV, S.zV_mem_V⟩ := by
      rw [S.psi_zV]
      exact Subtype.ext h
    have h2 := congrArg Subtype.val (S.frame.ψ.injective h1)
    apply hzL
    rw [show z = S.zV from h2]
    exact (S.mem_ZV_iff.2 (Or.inr rfl)).2
  · exact Or.inl h
  · exact Or.inr h

theorem psi_mul_zV {v : G} (hv : v ∈ V) :
    (S.frame.ψ ⟨v * S.zV, mul_mem hv S.zV_mem_V⟩ : P6) =
      (S.frame.ψ ⟨v, hv⟩ : P6) * G6.allOnes 6 := by
  have h : (⟨v * S.zV, mul_mem hv S.zV_mem_V⟩ : ↥V) = ⟨v, hv⟩ * ⟨S.zV, S.zV_mem_V⟩ := rfl
  rw [h, map_mul, S.psi_zV]
  rfl

theorem exists_conj_of_permAct {u v : G} (hu : u ∈ V) (hv : v ∈ V)
    (h45 : G6.permAct 6 (swap 4 5) (S.frame.ψ ⟨u, hu⟩ : P6) = S.frame.ψ ⟨u, hu⟩)
    {σ : Perm (Fin 6)} (hσ : G6.permAct 6 σ (S.frame.ψ ⟨u, hu⟩ : P6) = S.frame.ψ ⟨v, hv⟩) :
    ∃ l ∈ L, l * u * l⁻¹ = v := by
  obtain ⟨σ', hσ'A, hσ'⟩ : ∃ σ' : Perm (Fin 6), σ' ∈ alternatingGroup (Fin 6) ∧
      G6.permAct 6 σ' (S.frame.ψ ⟨u, hu⟩ : P6) = S.frame.ψ ⟨v, hv⟩ := by
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h
    · exact ⟨σ, Perm.mem_alternatingGroup.2 h, hσ⟩
    · refine ⟨σ * swap 4 5, Perm.mem_alternatingGroup.2 ?_, ?_⟩
      · rw [Perm.sign_mul, h, swap45_facts.1]
        rfl
      · rw [map_mul, MulAut.mul_apply, h45, hσ]
  obtain ⟨g, hgL, hgρ⟩ := (S.frame.image_L σ').2 hσ'A
  refine ⟨g, hgL, ?_⟩
  have h1 := S.psi_conj g ⟨u, hu⟩
  have h2 : S.frame.ψ ⟨(g : G) * u * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 u).mp hu⟩ =
      S.frame.ψ ⟨v, hv⟩ := by
    rw [h1]
    exact Subtype.ext (by rw [G6.coreAct_coe, hgρ, hσ'])
  exact congrArg Subtype.val (S.frame.ψ.injective h2)

variable {z : G} (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G))
  (huniq : ∀ z' ∈ quasithinOmegaOneCenter T, z' ≠ 1 →
    ¬ centralizer ({z'} : Set G) ≤ normalizer (L : Set G) → z' = z)
include hz hzL huniq

theorem centralizer_le_of_wtP_ne (h1222 : Stmt12_2_2) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hw : wtP (S.frame.ψ ⟨v, hv⟩ : P6) ≠ wtP (S.frame.ψ ⟨z, hz.1⟩ : P6)) :
    centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  have hzV := S.zV_mem_V
  have hz' : z * S.zV ∈ V := mul_mem hz.1 hzV
  have hzz : centralizer ({z * S.zV} : Set G) ≤ normalizer (L : Set G) := by
    by_contra h
    have hZ : z * S.zV ∈ quasithinOmegaOneCenter T := mul_mem hz.2 (U3.s134_zV_mem_Z S)
    have hne1 : z * S.zV ≠ 1 := by
      intro h1
      have : z = S.zV⁻¹ := eq_inv_of_mul_eq_one_left h1
      apply hzL
      rw [this]
      exact inv_mem (S.mem_ZV_iff.2 (Or.inr rfl)).2
    have h2 := huniq _ hZ hne1 h
    apply S.zV_ne_one
    have : z * S.zV * S.zV⁻¹ = z * S.zV⁻¹ := by rw [h2]
    simpa using this
  rcases wtP_cases _ (S.frame.ψ ⟨v, hv⟩).2 with h | h | h | h
  · exfalso
    apply hv1
    have h1 : S.frame.ψ ⟨v, hv⟩ = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  · have hvz : v = S.zV := by
      have h1 : S.frame.ψ ⟨v, hv⟩ = S.frame.ψ ⟨S.zV, hzV⟩ := by
        rw [S.psi_zV]
        exact Subtype.ext h
      exact congrArg Subtype.val (S.frame.ψ.injective h1)
    rw [hvz, S.centralizer_zV h1222]
  all_goals
    have hzz' := psi_mul_zV S hz.1
    obtain ⟨l, hlL, hlv⟩ : ∃ l ∈ L, l * (z * S.zV) * l⁻¹ = v := by
      rcases psi_z_cases' S hz hzL with hz0 | hz0
      · rw [hz0] at hw hzz'
        have hzz2 : (S.frame.ψ ⟨z * S.zV, hz'⟩ : P6) = e45 := by
          rw [hzz']
          decide
        have hv2 : wtP (S.frame.ψ ⟨v, hv⟩ : P6) = 2 := by
          rw [wtP_e0123] at hw
          omega
        obtain ⟨σ, hσ⟩ := exists_perm_e45 _ hv2
        refine exists_conj_of_permAct S hz' hv (by rw [hzz2]; exact swap45_facts.2.1) (σ := σ) ?_
        rw [hzz2, hσ]
      · rw [hz0] at hw hzz'
        have hzz2 : (S.frame.ψ ⟨z * S.zV, hz'⟩ : P6) = e0123 := by
          rw [hzz']
          decide
        have hv2 : wtP (S.frame.ψ ⟨v, hv⟩ : P6) = 4 := by
          rw [wtP_e45] at hw
          omega
        obtain ⟨σ, hσ⟩ := exists_perm_e0123 _ hv2
        refine exists_conj_of_permAct S hz' hv (by rw [hzz2]; exact swap45_facts.2.2) (σ := σ) ?_
        rw [hzz2, hσ]
    have hlM : l ∈ normalizer (L : Set G) := le_normalizer hlL
    intro c hc
    have hc' : l⁻¹ * c * l ∈ centralizer ({z * S.zV} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      have e : z * S.zV = l⁻¹ * v * l := by rw [← hlv]; group
      rw [e]
      calc l⁻¹ * c * l * (l⁻¹ * v * l) = l⁻¹ * (c * v) * l := by group
        _ = l⁻¹ * (v * c) * l := by rw [hc]
        _ = l⁻¹ * v * l * (l⁻¹ * c * l) := by group
    have h1 := hzz hc'
    have e : c = l * (l⁻¹ * c * l) * l⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hlM h1) (inv_mem hlM)

theorem wtP_eq_of_not_le (h1222 : Stmt12_2_2) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hC : ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G)) :
    wtP (S.frame.ψ ⟨v, hv⟩ : P6) = wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
  by_contra h
  exact hC (centralizer_le_of_wtP_ne S hz hzL huniq h1222 hv hv1 h)

theorem eq_of_mem_conj (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {v g : G} (hv : v ∈ V)
    (hv1 : v ≠ 1) (hw : wtP (S.frame.ψ ⟨v, hv⟩ : P6) ≠ wtP (S.frame.ψ ⟨z, hz.1⟩ : P6))
    (hvg : v ∈ V.map (MulAut.conj g).toMonoidHom) : V.map (MulAut.conj g).toMonoidHom = V := by
  have h1 : v ∈ V.map (MulAut.conj (1 : G)).toMonoidHom := by rw [map_conj_one]; exact hv
  obtain ⟨c, hc, hcV⟩ := lemma13_4_2_three h331 h1222 S hvg h1
  have hcN : c ∈ normalizer (V : Set G) :=
    S.normalizer_L_le h1222 (centralizer_le_of_wtP_ne S hz hzL huniq h1222 hv hv1 hw hc)
  rw [← hcV, map_conj_one, map_conj_eq_of_mem hcN]

theorem card_le_four (h1222 : Stmt12_2_2) {B : Subgroup G} (hBV : B ≤ V)
    (hB : ¬ centralizer (B : Set G) ≤ normalizer (L : Set G)) : Nat.card B ≤ 4 := by
  classical
  by_contra h4
  push Not at h4
  have hw : ∀ (b : G) (hb : b ∈ B), b ≠ 1 →
      wtP (S.frame.ψ ⟨b, hBV hb⟩ : P6) = wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
    intro b hb hb1
    refine wtP_eq_of_not_le S hz hzL huniq h1222 (hBV hb) hb1 fun h => hB ?_
    exact (centralizer_le (Set.singleton_subset_iff.2 hb)).trans h
  have hsq : ∀ b ∈ B, b * b = 1 := fun b hb => by
    have h1 : S.frame.ψ (⟨b, hBV hb⟩ * ⟨b, hBV hb⟩) = 1 :=
      Subtype.ext (by rw [map_mul]; exact P6_mul_self _)
    rw [MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  have hinv : ∀ b ∈ B, b⁻¹ = b := fun b hb => inv_eq_of_mul_eq_one_right (hsq b hb)
  have hψmul : ∀ (a b : G) (ha : a ∈ V) (hb : b ∈ V),
      (S.frame.ψ ⟨a * b, mul_mem ha hb⟩ : P6) =
        (S.frame.ψ ⟨a, ha⟩ : P6) * (S.frame.ψ ⟨b, hb⟩ : P6) := fun a b ha hb => by
    rw [show (⟨a * b, mul_mem ha hb⟩ : ↥V) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
    rfl
  obtain ⟨x, hxB, hx⟩ := exists_mem_not_mem_of_lt (B := B) ({1} : Finset G) (by simp; omega)
  have hx1 : x ≠ 1 := by simpa using hx
  obtain ⟨y, hyB, hy⟩ := exists_mem_not_mem_of_lt (B := B) ({1, x} : Finset G)
    ((Finset.card_le_two).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hy1, hyx⟩ := hy
  obtain ⟨u, huB, hu⟩ := exists_mem_not_mem_of_lt (B := B) ({1, x, y, x * y} : Finset G)
    ((Finset.card_le_four).trans_lt h4)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨hu1, hux, huy, huxy⟩ := hu
  have hne : ∀ {a b : G}, a ∈ B → b ∈ B → a ≠ b → a * b ≠ 1 := fun ha hb hab h => by
    apply hab
    rw [eq_inv_of_mul_eq_one_left h, hinv _ hb]
  have hxy1 : x * y ≠ 1 := hne hxB hyB (Ne.symm hyx)
  have hxu1 : x * u ≠ 1 := hne hxB huB (Ne.symm hux)
  have hyu1 : y * u ≠ 1 := hne hyB huB (Ne.symm huy)
  have hxyu1 : x * y * u ≠ 1 := hne (mul_mem hxB hyB) huB (Ne.symm huxy)
  have wx := hw x hxB hx1
  have wy := hw y hyB hy1
  have wu := hw u huB hu1
  have wxy := hw _ (mul_mem hxB hyB) hxy1
  have wxu := hw _ (mul_mem hxB huB) hxu1
  have wyu := hw _ (mul_mem hyB huB) hyu1
  have wxyu := hw _ (mul_mem (mul_mem hxB hyB) huB) hxyu1
  have hxV := hBV hxB
  have hyV := hBV hyB
  have huV := hBV huB
  rw [hψmul x y hxV hyV] at wxy
  rw [hψmul x u hxV huV] at wxu
  rw [hψmul y u hyV huV] at wyu
  rw [hψmul (x * y) u (mul_mem hxV hyV) huV, hψmul x y hxV hyV] at wxyu
  rcases psi_z_cases' S hz hzL with hz0 | hz0
  · rw [hz0, wtP_e0123] at wx wy wu wxy wxu wyu wxyu
    exact no_E8_wt_four _ (mem_wt4List.2 wx) _ (mem_wt4List.2 wy) (mem_wt4List.2 wxy) _
      (mem_wt4List.2 wu) (mem_wt4List.2 wxu) (mem_wt4List.2 wyu) (mem_wt4List.2 wxyu)
  · rw [hz0, wtP_e45] at wx wy wu wxy wxu wyu wxyu
    exact no_E8_wt_two _ (mem_wt2List.2 wx) _ (mem_wt2List.2 wy) (mem_wt2List.2 wxy) _
      (mem_wt2List.2 wu) (mem_wt2List.2 wxu) (mem_wt2List.2 wyu) (mem_wt2List.2 wxyu)

end End134

end CFSG.Quasithin.H13.NQS134
