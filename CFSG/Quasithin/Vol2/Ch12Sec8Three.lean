module

public import CFSG.Quasithin.Vol2.Ch12Sec8Basic
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

theorem eq_or_eq_or_eq_or_eq_of_card_four {V : Type*} [Finite V] (hV : Nat.card V = 4)
    {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (w : V) : w = a ∨ w = b ∨ w = c ∨ w = d := by
  classical
  by_contra hw
  push Not at hw
  have hcard : (({a, b, c, d, w} : Finset V)).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair]
    · exact hw.2.2.2.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hcd, fun h => hw.2.2.1 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hbc, hbd, fun h => hw.2.1 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac, had, fun h => hw.1 h.symm⟩
  have : Fintype V := Fintype.ofFinite V
  have hle := Finset.card_le_univ ({a, b, c, d, w} : Finset V)
  rw [hcard, ← Nat.card_eq_fintype_card, hV] at hle
  omega

variable {G : Type} [Group G] [Finite G]

theorem isTwoReducedIn_of_inf_centralizer_eq {X V : Subgroup G} (hVX : V ≤ X)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hC : X ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X) : IsTwoReducedIn X V := by
  refine ⟨hVX, hXN, hV, fun D hDX hXD hD => ?_⟩
  have hD2 : IsPGroup 2 D := by
    refine isPGroup_two_of_forall fun d hd => ?_
    obtain ⟨k, hk⟩ := hD d hd
    have hmem : d ^ 2 ^ k ∈ pCoreOf 2 X := by
      rw [← hC]
      exact ⟨X.pow_mem (hDX hd) _, hk⟩
    obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one_of_mem (pCoreOf_isPGroup 2 X) hmem
    exact ⟨k + j, by rw [pow_add, pow_mul, hj]⟩
  have hDO : D ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hDX hXD hD2
  rw [← hC] at hDO
  exact hDO.trans inf_le_right

variable {T M L : Subgroup G}

namespace Hyp1281Two

theorem isTwoReducedIn_LT (h : Hyp1281Two G T M L) : IsTwoReducedIn (L ⊔ T) (VZ T M) := by
  obtain ⟨hVred, hVT⟩ := h.isTwoReducedIn
  exact isTwoReducedIn_of_inf_centralizer_eq (hVT.trans le_sup_right)
    ((sup_le h.le h.inM.2).trans hVred.2.1) hVred.2.2.1 h.centralizer

theorem not_le_centralizer_L (h : Hyp1281Two G T M L) :
    ¬ L ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro hLC
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hsyl : IsSylowTwoOf T (L ⊔ T) := by
    have := isSylowTwoOf_of_sylow S (hS ▸ (le_sup_right : T ≤ L ⊔ T))
    rwa [hS] at this
  have hLT : L ≤ T := by
    have hLO : L ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← h.centralizer]
      exact le_inf le_sup_left hLC
    exact hLO.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl)
  have h2 : IsPGroup 2 ↥(L ⊔ T) := h.sylow.1.to_le (sup_le hLT le_rfl)
  obtain ⟨e⟩ := h.sThree
  have hq : IsPGroup 2 (OTwoQuot (L ⊔ T)) := h2.to_quotient _
  have hP : IsPGroup 2 (Equiv.Perm (Fin 3)) := hq.of_equiv e
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hn
  have h6 : (3 : ℕ).factorial = 6 := rfl
  rw [h6] at hn
  rcases n with _ | _ | _ | n
  · simp at hn
  · simp at hn
  · simp at hn
  · have : 2 ^ 3 ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem exists_odd_not_mem_centralizer (h : Hyp1281Two G T M L) :
    ∃ l ∈ L, Odd (orderOf l) ∧ l ∉ Subgroup.centralizer (VZ T M : Set G) := by
  by_contra hall
  push Not at hall
  apply h.not_le_centralizer_L
  rw [← h.residual]
  exact (Subgroup.closure_le _).mpr fun x hx => hall x hx.1 hx.2

theorem exists_conj_eq (h : Hyp1281Two G T M L) {v w : G} (hv : v ∈ VZ T M) (hw : w ∈ VZ T M)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) : ∃ l ∈ L, l * v * l⁻¹ = w := by
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  obtain ⟨l, hlL, hlodd, hlC⟩ := h.exists_odd_not_mem_centralizer
  have hlN : l ∈ Subgroup.normalizer (VZ T M : Set G) := hVred.2.1 (h.le hlL)
  have hsq : ∀ u : VZ T M, u * u = 1 := fun u =>
    Subtype.ext (by simpa [sq] using hVred.2.2.1.2 u u.2)
  have hconj : ∀ k : ℕ, ∀ u ∈ VZ T M, l ^ k * u * (l ^ k)⁻¹ ∈ VZ T M := fun k u hu =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hlN k) u).mp hu
  have hfix : ∀ k : ℕ, ∀ u ∈ VZ T M, u ≠ 1 → l ^ k * u * (l ^ k)⁻¹ = u →
      l ^ k ∈ Subgroup.centralizer (VZ T M : Set G) := by
    intro k u hu hu1 hfixu
    have hNk : l ^ k ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.pow_mem _ hlN k
    set σ : MulAut (VZ T M) := conjAct (VZ T M) ⟨l ^ k, hNk⟩ with hσ
    have hσapp : ∀ y : VZ T M, ((σ y : VZ T M) : G) = l ^ k * y * (l ^ k)⁻¹ := fun y =>
      Subgroup.normalizerMonoidHom_apply_apply_coe (VZ T M) (Subgroup.inclusion le_rfl ⟨l ^ k, hNk⟩) y
    have hσu : σ ⟨u, hu⟩ = ⟨u, hu⟩ := Subtype.ext (by rw [hσapp]; exact hfixu)
    have hσm : σ ^ orderOf l = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨l ^ k, hNk⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ orderOf l = 1 :=
        Subtype.ext (by
          simp only [Subgroup.coe_pow, Subgroup.coe_one]
          rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow])
      rw [this, map_one]
    have hσ1 := mulAut_eq_one_of_fix_of_odd h.rank_two hsq (z := ⟨u, hu⟩)
      (fun h1 => hu1 (show u = 1 from congrArg (fun y : VZ T M => (y : G)) h1)) hσu hlodd hσm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := congrArg (fun φ : MulAut (VZ T M) => ((φ ⟨y, hy⟩ : VZ T M) : G)) hσ1
    simp only [hσapp, MulAut.one_apply] at this
    calc y * l ^ k = (l ^ k * y * (l ^ k)⁻¹) * l ^ k := by rw [this]
      _ = l ^ k * y := by group
  have hl2C : l ^ 2 ∉ Subgroup.centralizer (VZ T M : Set G) := by
    intro hl2
    apply hlC
    obtain ⟨m, hm⟩ := hlodd
    have hlm : l ^ (2 * m + 1) = 1 := by rw [← hm, pow_orderOf_eq_one]
    have e : l = (l ^ 2) ^ (m + 1) := by
      calc l = l ^ (2 * m + 1) * l := by rw [hlm, one_mul]
        _ = (l ^ 2) ^ (m + 1) := by rw [← pow_succ, ← pow_mul]; ring_nf
    rw [e]
    exact Subgroup.pow_mem _ hl2 _
  have hlC1 : l ^ 1 ∉ Subgroup.centralizer (VZ T M : Set G) := by rwa [pow_one]
  set v1 := l * v * l⁻¹ with hv1def
  set v2 := l ^ 2 * v * (l ^ 2)⁻¹ with hv2def
  have hv1V : v1 ∈ VZ T M := by simpa using hconj 1 v hv
  have hv2V : v2 ∈ VZ T M := hconj 2 v hv
  have hne1 : v1 ≠ v := fun he => hlC1 (hfix 1 v hv hv1 (by simpa using he))
  have hne2 : v2 ≠ v := fun he => hl2C (hfix 2 v hv hv1 he)
  have hne12 : v1 ≠ v2 := by
    intro he
    apply hne1
    have : l⁻¹ * v1 * l = l⁻¹ * v2 * l := by rw [he]
    have e1 : l⁻¹ * v1 * l = v := by rw [hv1def]; group
    have e2 : l⁻¹ * v2 * l = v1 := by rw [hv2def, hv1def]; group
    rw [e1, e2] at this
    exact this.symm
  have hv1' : v1 ≠ 1 := fun he => hv1 (by
    have : l⁻¹ * v1 * l = 1 := by rw [he]; group
    rw [hv1def] at this
    simpa [mul_assoc] using this)
  have hv2' : v2 ≠ 1 := fun he => hv1 (by
    have : (l ^ 2)⁻¹ * v2 * l ^ 2 = 1 := by rw [he]; group
    rw [hv2def] at this
    simpa [mul_assoc] using this)
  have hcases := eq_or_eq_or_eq_or_eq_of_card_four h.rank_two
    (a := (1 : VZ T M)) (b := ⟨v, hv⟩) (c := ⟨v1, hv1V⟩) (d := ⟨v2, hv2V⟩)
    (fun he => hv1 (congrArg (fun y : VZ T M => (y : G)) he).symm)
    (fun he => hv1' (congrArg (fun y : VZ T M => (y : G)) he).symm)
    (fun he => hv2' (congrArg (fun y : VZ T M => (y : G)) he).symm)
    (fun he => hne1 (congrArg (fun y : VZ T M => (y : G)) he).symm)
    (fun he => hne2 (congrArg (fun y : VZ T M => (y : G)) he).symm)
    (fun he => hne12 (congrArg (fun y : VZ T M => (y : G)) he)) ⟨w, hw⟩
  rcases hcases with he | he | he | he
  · exact absurd (congrArg (fun y : VZ T M => (y : G)) he) hw1
  · refine ⟨1, L.one_mem, ?_⟩
    have := congrArg (fun y : VZ T M => (y : G)) he
    simp only at this
    rw [this]
    group
  · exact ⟨l, hlL, (congrArg (fun y : VZ T M => (y : G)) he).symm⟩
  · exact ⟨l ^ 2, L.pow_mem hlL 2, (congrArg (fun y : VZ T M => (y : G)) he).symm⟩

theorem exists_eq_conjSub (h : Hyp1281Two G T M L) {g : G}
    (hg : quasithinOmegaOneCenter T ≤ conjSub g (VZ T M)) :
    ∃ x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G),
      conjSub g (VZ T M) = conjSub x (VZ T M) := by
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  have hZ2 := h.card_omegaOneCenter
  obtain ⟨z, hzZ⟩ : ∃ z : quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact h.omegaOneCenter_ne_bot (by
      rw [eq_bot_iff]
      intro w hw
      have := hall ⟨w, hw⟩
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : quasithinOmegaOneCenter T)).mp hZ2
  have hz1 : (z : G) ≠ 1 := fun he => hzZ (Subtype.ext he)
  have hzV : (z : G) ∈ VZ T M := le_conjClosure _ _ z.2
  have hgz : g⁻¹ * z * g ∈ VZ T M := mem_conjSub.mp (hg z.2)
  have hgz1 : g⁻¹ * z * g ≠ 1 := fun he => hz1 (by
    have : g * (g⁻¹ * z * g) * g⁻¹ = 1 := by rw [he]; group
    simpa [mul_assoc] using this)
  obtain ⟨l, hlL, hl⟩ := h.exists_conj_eq hzV hgz hz1 hgz1
  set x := g * l with hx
  have hxz : x * z * x⁻¹ = z := by
    rw [hx]
    calc g * l * z * (g * l)⁻¹ = g * (l * z * l⁻¹) * g⁻¹ := by group
      _ = z := by rw [hl]; group
  have hxC : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, one_mul, mul_one]
    · have hwz : w = z := by
        have h1 := hy ⟨w, hw⟩ (fun he => hw1 (congrArg Subtype.val he))
        have h2 := hy z hzZ
        exact congrArg Subtype.val (h1.trans h2.symm)
      rw [hwz]
      calc (z : G) * x = (x * z * x⁻¹) * x := by rw [hxz]
        _ = x * z := by group
  refine ⟨x, Subgroup.centralizer_le_normalizer _ hxC, ?_⟩
  have hlN : l ∈ Subgroup.normalizer (VZ T M : Set G) := hVred.2.1 (h.le hlL)
  rw [hx]
  ext u
  rw [mem_conjSub, mem_conjSub]
  constructor
  · intro hu
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) _).mp hu
    have e : (g * l)⁻¹ * u * (g * l) = l⁻¹ * (g⁻¹ * u * g) * l⁻¹⁻¹ := by group
    rw [e]
    exact this
  · intro hu
    have := (Subgroup.mem_normalizer_iff.mp hlN _).mp hu
    have e : g⁻¹ * u * g = l * ((g * l)⁻¹ * u * (g * l)) * l⁻¹ := by group
    rw [e]
    exact this

end Hyp1281Two

end CFSG.Quasithin
