module

public import CFSG.RankThree.GF2n.Stroth80.Sec715OrthTorus
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.RankThree.GF2n.Stroth80.NonsingularPerp
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec715Torus

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalGroups.F2Fixed

section Normalizer

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem gom_app_zero (g : Gom Q) : g.app 0 = 0 := map_zero (g : V ≃ₗ[K] V)

theorem gom_inv_app_smul {g : Gom Q} {e : V} {c : K} (hc : c ≠ 0) (hg : g.app e = c • e) :
    g⁻¹.app e = c⁻¹ • e := by
  have h1 := Gom.app_inv_app g e
  rw [hg, Gom.map_smul] at h1
  calc g⁻¹.app e = c⁻¹ • (c • g⁻¹.app e) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • e := by rw [h1]

theorem mem_Lom_app_iff_conj (g h : Gom Q) (u : V) :
    h ∈ Lom Q (g.app u) ↔ g⁻¹ * h * g ∈ Lom Q u := by
  constructor
  · intro hh
    have := conj_mem_Lom g⁻¹ hh
    rwa [Gom.app_inv_app, inv_inv] at this
  · intro hh
    have := conj_mem_Lom g hh
    have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rwa [e] at this

theorem exists_app_eq_smul_of_mem_normalizer_Lom [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ Module.finrank K V) {e : V} (he : Q e = 0)
    (he0 : e ≠ 0) {g : Gom Q} (hg : g ∈ Subgroup.normalizer (Lom Q e : Set (Gom Q))) :
    ∃ c : K, c ≠ 0 ∧ g.app e = c • e := by
  have hge0 : g.app e ≠ 0 := by
    intro h
    apply he0
    have := Gom.app_inv_app g e
    rw [h, gom_app_zero] at this
    exact this.symm
  have hEq : rootGroup Q e = rootGroup Q (g.app e) := by
    ext a
    constructor
    · intro ha
      have haE : a ∈ elementaryGroup Q := rootGroup_le_elementaryGroup Q e ha
      have hA : (⟨a, haE⟩ : Gom Q) ∈ Lom Q e := ha
      have h1 : g⁻¹ * ⟨a, haE⟩ * g⁻¹⁻¹ ∈ Lom Q e :=
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) _).mp hA
      have h2 := conj_mem_Lom g h1
      have e1 : g * (g⁻¹ * (⟨a, haE⟩ : Gom Q) * g⁻¹⁻¹) * g⁻¹ = ⟨a, haE⟩ := by group
      rw [e1] at h2
      exact h2
    · intro ha
      have haE : a ∈ elementaryGroup Q := rootGroup_le_elementaryGroup Q _ ha
      have hA : (⟨a, haE⟩ : Gom Q) ∈ Lom Q (g.app e) := ha
      have h1 : g⁻¹ * ⟨a, haE⟩ * g ∈ Lom Q e := (mem_Lom_app_iff_conj g _ e).mp hA
      have h2 : g * (g⁻¹ * ⟨a, haE⟩ * g) * g⁻¹ ∈ Lom Q e :=
        (Subgroup.mem_normalizer_iff.mp hg _).mp h1
      have e1 : g * (g⁻¹ * (⟨a, haE⟩ : Gom Q) * g) * g⁻¹ = ⟨a, haE⟩ := by group
      rw [e1] at h2
      exact h2
  obtain ⟨c, hc0, hc⟩ := (rootGroup_eq_iff hQ h3 he0 hge0 he).mp hEq
  exact ⟨c, hc0, hc⟩

end Normalizer

section FPF

open CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem torusG_inv_app (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0)
    (v : Fin n ⊕ Fin n → K) : (torusG hn P hs)⁻¹.app v = torusLin P s⁻¹ v := by
  rw [← torusG_swap, torusG_app, torusLin_swap]

theorem torus_comm_mem_Lom (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0)
    {g : Gom (quadPlus n K)} {c : K} (hc : c ≠ 0) (hg : g.app P.e = c • P.e) :
    g * torusG hn P hs * g⁻¹ * (torusG hn P hs)⁻¹ ∈ Lom (quadPlus n K) P.e := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  rw [mem_Lom, mem_rootGroup_iff hQ P.Q_e P.e_ne_zero]
  have hgi : g⁻¹.app P.e = c⁻¹ • P.e := gom_inv_app_smul hc hg
  have hτe : (torusG hn P hs).app P.e = s • P.e := torusLin_app_e P s
  have hτie : (torusG hn P hs)⁻¹.app P.e = s⁻¹ • P.e := by
    rw [torusG_inv_app]
    exact torusLin_app_e P s⁻¹
  refine ⟨elementaryGroup_le_orthogonalGroup _ (g * torusG hn P hs * g⁻¹ * (torusG hn P hs)⁻¹).2,
    ?_, ?_⟩
  · show (g * torusG hn P hs * g⁻¹ * (torusG hn P hs)⁻¹).app P.e = P.e
    simp only [Gom.app_mul, hτie, Gom.map_smul, hgi, hτe, hg, smul_smul]
    have : s⁻¹ * (c⁻¹ * (s * c)) = 1 := by field_simp
    rw [this, one_smul]
  · intro x hx
    have hpe : polar (quadPlus n K) x P.e = 0 := hx
    have h1 : (torusG hn P hs)⁻¹.app x =
        x + ((s⁻¹ - 1) * polar (quadPlus n K) x P.f) • P.e := by
      rw [torusG_inv_app, torusLin_apply, hpe]
      simp
    have hy : polar (quadPlus n K) (g⁻¹.app x) P.e = 0 := by
      rw [gom_polar_inv_app, hg, polar_smul_right_eq, hpe, mul_zero]
    have e1 : g⁻¹.app ((torusG hn P hs)⁻¹.app x) = g⁻¹.app x +
        (((s⁻¹ - 1) * polar (quadPlus n K) x P.f) * c⁻¹) • P.e := by
      rw [h1, Gom.map_add, Gom.map_smul, hgi, smul_smul]
    have e2 : ∀ a : K, (torusG hn P hs).app (g⁻¹.app x + a • P.e) = g⁻¹.app x +
        ((s - 1) * polar (quadPlus n K) (g⁻¹.app x) P.f + a * s) • P.e := by
      intro a
      rw [torusG_app, map_add, map_smul, torusLin_app_e, torusLin_apply, hy]
      simp only [mul_zero, zero_smul, add_zero, smul_smul, add_smul]
      module
    have e3 : ∀ b : K, g.app (g⁻¹.app x + b • P.e) = x + (b * c) • P.e := by
      intro b
      rw [Gom.map_add, Gom.map_smul, hg, Gom.app_app_inv, smul_smul]
    refine ⟨((s - 1) * polar (quadPlus n K) (g⁻¹.app x) P.f +
      (((s⁻¹ - 1) * polar (quadPlus n K) x P.f) * c⁻¹) * s) * c, ?_⟩
    show (g * torusG hn P hs * g⁻¹ * (torusG hn P hs)⁻¹).app x - x = _
    rw [Gom.app_mul, Gom.app_mul, Gom.app_mul, e1, e2, e3]
    abel

section ModuleFacts

variable {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [DistribMulAction Γ M]

theorem smul_mem_fixedSub_of_normalizer {S : Set Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer S) {m : M} (hm : m ∈ fixedSub M S) :
    g • m ∈ fixedSub M S := by
  intro t ht
  have hginv : g⁻¹ ∈ Subgroup.normalizer S := (Subgroup.normalizer S).inv_mem hg
  have h1 : g⁻¹ * t * g⁻¹⁻¹ ∈ S := ((Subgroup.mem_set_normalizer_iff.mp hginv) t).mp ht
  have e : t • g • m = g • (g⁻¹ * t * g⁻¹⁻¹) • m := by
    simp only [mul_smul, inv_inv, smul_inv_smul]
  rw [e, hm _ h1]

end ModuleFacts

theorem finrank_quadPlus_space : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem exists_gom_swap (hn : 2 ≤ n) (P : HypPair (quadPlus n K)) :
    ∃ w : Gom (quadPlus n K), w.app P.e = P.f ∧ w.app P.f = P.e :=
  exists_gom_pair (nondegenerate_polarBilin_quadPlus n K)
    (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    P.Q_e P.Q_f P.Q_f P.Q_e P.polar_ef P.polar_fe

theorem torusG_conj_swap (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0)
    {w : Gom (quadPlus n K)} (hwe : w.app P.e = P.f) (hwf : w.app P.f = P.e) :
    w * torusG hn P hs * w⁻¹ = (torusG hn P hs)⁻¹ := by
  have hP : pairMap P w = pairSwap P := by
    obtain ⟨e, f, h1, h2, h3⟩ := P
    simp only [pairMap, pairSwap, HypPair.mk.injEq]
    exact ⟨hwe, hwf⟩
  rw [torusG_conj, hP, torusG_swap]

theorem torusG_conj_swap' (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0)
    {w : Gom (quadPlus n K)} (hwe : w.app P.e = P.f) (hwf : w.app P.f = P.e) :
    w⁻¹ * torusG hn P hs * w = (torusG hn P hs)⁻¹ := by
  have h := torusG_conj_swap hn P hs hwe hwf
  have h' : w * (torusG hn P hs)⁻¹ * w⁻¹ = torusG hn P hs := by
    calc w * (torusG hn P hs)⁻¹ * w⁻¹ = (w * torusG hn P hs * w⁻¹)⁻¹ := by group
      _ = torusG hn P hs := by rw [h, inv_inv]
  calc w⁻¹ * torusG hn P hs * w = w⁻¹ * (w * (torusG hn P hs)⁻¹ * w⁻¹) * w := by rw [h']
    _ = (torusG hn P hs)⁻¹ := by group

theorem smul_mem_fixedSub_Lom_of_app {V : Type} [AddCommGroup V] {K' : Type} [Field K']
    [Module K' V] {Q' : QuadraticForm K' V} {M : Type*} [AddCommGroup M]
    [DistribMulAction (Gom Q') M] {e f : V} {w : Gom Q'} (hwe : w.app e = f) {m : M}
    (hm : m ∈ fixedSub M (Lom Q' e : Set (Gom Q'))) :
    w • m ∈ fixedSub M (Lom Q' f : Set (Gom Q')) := by
  have := smul_mem_fixedSub_conj w hm
  rwa [image_conj_Lom, hwe] at this

theorem torus_smul_fixed (hn : 3 ≤ n) (P : HypPair (quadPlus n K)) {s : K} (hs : s ≠ 0)
    {M : Type} [AddCommGroup M] [DistribMulAction (Gom (quadPlus n K)) M]
    {g : Gom (quadPlus n K)}
    (hg : g ∈ Subgroup.normalizer (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))))
    {x : M} (hx : x ∈ fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))))
    (hτx : torusG hn P hs • x = x) : torusG hn P hs • g • x = g • x := by
  have hQ := nondegenerate_polarBilin_quadPlus n K
  obtain ⟨c, hc0, hc⟩ := exists_app_eq_smul_of_mem_normalizer_Lom hQ
    (by rw [finrank_quadPlus_space]; omega) P.Q_e P.e_ne_zero
    ((Subgroup.normalizer _).inv_mem hg)
  have hmem := torus_comm_mem_Lom hn P hs hc0 hc
  have h1 : (g⁻¹ * torusG hn P hs * g⁻¹⁻¹ * (torusG hn P hs)⁻¹) • torusG hn P hs • x = x := by
    rw [hτx]
    exact hx _ hmem
  have e1 : (g⁻¹ * torusG hn P hs * g⁻¹⁻¹ * (torusG hn P hs)⁻¹) * torusG hn P hs =
      g⁻¹ * torusG hn P hs * g := by group
  rw [← mul_smul, e1, mul_smul, mul_smul] at h1
  calc torusG hn P hs • g • x = g • (g⁻¹ • (torusG hn P hs • (g • x))) := by
        rw [smul_inv_smul]
    _ = g • x := by rw [h1]

theorem torus_not_trivial (hn : 4 ≤ n)
    {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction (Gom (quadPlus n K)) M]
    (h2 : ∀ m : M, m + m = 0) [Nontrivial M] (P : HypPair (quadPlus n K))
    {w : Gom (quadPlus n K)} (hwf : w.app P.f = P.e)
    (hdec : IsCompl (fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))))
      (fixedSub M (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K)))))
    {s : K} (hs : s ≠ 0) (hs1 : s ≠ 1)
    (htriv : ∀ m : M, torusG (by omega) P hs • m = m) : False := by
  have hn3 : 3 ≤ n := by omega
  have hQ := nondegenerate_polarBilin_quadPlus n K
  have hfin : FiniteDimensional K (Fin n ⊕ Fin n → K) := inferInstance
  obtain ⟨b₁, hb₁e, hQb₁⟩ := exists_nonsingular_perp hQ
    (by rw [finrank_quadPlus_space]; omega) P.e_ne_zero
  obtain ⟨b, hbf, hbe, hQb, -⟩ := exists_perp_eichlerG_eq (e := P.f) (f := P.e) (w := b₁) P.Q_e
    (by rw [P.polar_fe]; exact one_ne_zero) hb₁e
  have hQb0 : (quadPlus n K) b ≠ 0 := by rw [hQb]; exact hQb₁
  set τ := torusG hn3 P hs with hτ
  have hτb : τ.app b = b :=
    torusLin_app_of_perp P s (by rw [polar_comm]; exact hbe) (by rw [polar_comm]; exact hbf)
  have hτe : τ.app P.e = s • P.e := torusLin_app_e P s
  have hτinv : ∀ z : M, τ⁻¹ • z = z := by
    intro z
    have h1 : τ • τ⁻¹ • z = τ⁻¹ • z := htriv _
    rw [smul_inv_smul] at h1
    exact h1.symm
  have hconj : τ * eichlerG (quadPlus n K) P.e b * τ⁻¹ =
      eichlerG (quadPlus n K) P.e (s • b) := by
    rw [eichlerG_conj, hτe, hτb, eichlerG_smul_left]
  have hsb : polar (quadPlus n K) P.e (s • b) = 0 := by rw [polar_smul_right_eq, hbe, mul_zero]
  have hy : (τ * eichlerG (quadPlus n K) P.e b * τ⁻¹) * eichlerG (quadPlus n K) P.e b =
      eichlerG (quadPlus n K) P.e ((s + 1) • b) := by
    rw [hconj, eichlerG_mul hsb hbe, add_smul, one_smul]
  have hxx : eichlerG (quadPlus n K) P.e b * eichlerG (quadPlus n K) P.e b = 1 :=
    eichlerG_mul_self hbe
  have hytriv : ∀ m : M, eichlerG (quadPlus n K) P.e ((s + 1) • b) • m = m := by
    intro m
    rw [← hy]
    have e1 : (τ * eichlerG (quadPlus n K) P.e b * τ⁻¹ * eichlerG (quadPlus n K) P.e b) • m =
        τ • eichlerG (quadPlus n K) P.e b • τ⁻¹ • eichlerG (quadPlus n K) P.e b • m := by
      simp only [mul_smul]
    have e2 : eichlerG (quadPlus n K) P.e b • eichlerG (quadPlus n K) P.e b • m = m := by
      rw [← mul_smul, hxx, one_smul]
    rw [e1, hτinv, e2, htriv]
  have hs1' : s + 1 ≠ 0 := by
    intro h
    apply hs1
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  have hb'e : polar (quadPlus n K) P.e ((s + 1) • b) = 0 := by
    rw [polar_smul_right_eq, hbe, mul_zero]
  have hQb' : (quadPlus n K) ((s + 1) • b) ≠ 0 := by
    rw [map_smul_eq_sq]
    exact mul_ne_zero (pow_ne_zero 2 hs1') hQb0
  have hymem : eichlerG (quadPlus n K) P.e ((s + 1) • b) ∈ Lom (quadPlus n K) P.e :=
    eichlerG_mem_Lom hb'e
  have hnA2 : (eichlerG (quadPlus n K) P.e ((s + 1) • b)).NonA2 := by
    refine ⟨P.f, ?_⟩
    show polar (quadPlus n K) P.f (eichler (quadPlus n K) P.e ((s + 1) • b) P.f) ≠ 0
    rw [polar_apply_eichler_self P.Q_e hb'e, P.Q_f, P.polar_fe, CharTwo.two_eq_zero]
    simpa using hQb'
  obtain ⟨hfix, -, hcard⟩ := stroth_2_1_ii_omega_fixed hQ h2 P.Q_f P.Q_e
    (by rw [P.polar_fe]; exact one_ne_zero) hwf hdec.symm hymem hnA2
  have hC : fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) = ⊤ := by
    rw [← hfix, eq_top_iff]
    intro m _ g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hytriv m
  rw [hC, AddSubgroup.card_top] at hcard
  have hpos : 0 < Nat.card M := Nat.card_pos
  have h1 : Nat.card M = 1 := by
    have : Nat.card M * Nat.card M = Nat.card M * 1 := by
      rw [mul_one, ← pow_two]
      exact hcard.symm
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have := Nat.card_eq_one_iff_unique.mp h1
  obtain ⟨hsub, -⟩ := this
  exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance

theorem torus_fixedSub_Lom_inf_eq_bot (hK : 2 < Nat.card K) (hn : 4 ≤ n)
    {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction (Gom (quadPlus n K)) M]
    (h2 : ∀ m : M, m + m = 0) [Nontrivial M]
    (hirr : ∀ W : AddSubgroup M, (∀ (g : Gom (quadPlus n K)) (x : M), x ∈ W → g • x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (P : HypPair (quadPlus n K))
    (hdec : IsCompl (fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))))
      (fixedSub M (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K)))))
    {s : K} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) ⊓
      fixedSub M {torusG (by omega) P hs} = ⊥ := by
  have hn3 : 3 ≤ n := by omega
  have hQ := nondegenerate_polarBilin_quadPlus n K
  obtain ⟨w, hwe, hwf⟩ := exists_gom_swap (by omega) P
  set τ := torusG hn3 P hs with hτ
  set C : AddSubgroup M := fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) with hC
  set C' : AddSubgroup M := fixedSub M (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K)))
    with hC'
  set FC : AddSubgroup M := C ⊓ fixedSub M {τ} with hFC
  have hFCN : ∀ g ∈ Subgroup.normalizer (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))),
      ∀ x ∈ FC, g • x ∈ FC := by
    intro g hg x hx
    refine ⟨smul_mem_fixedSub_of_normalizer hg hx.1, ?_⟩
    intro t ht
    rw [Set.mem_singleton_iff.mp ht]
    exact torus_smul_fixed hn3 P hs hg hx.1 (hx.2 τ rfl)
  have hdec' : IsCompl (fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))))
      (fixedSub M (Lom (quadPlus n K) (w.app P.e) : Set (Gom (quadPlus n K)))) := by
    rw [hwe]
    exact hdec
  have hug : polar (quadPlus n K) P.e (w.app P.e) ≠ 0 := by
    rw [hwe, P.polar_ef]
    exact one_ne_zero
  have key := stroth_2_1_iii_omega hQ hK h2 P.Q_e hug hdec' (U := FC) (fun x hx => hx.1) hFCN
  have hW := hirr _ key
  rcases hW with hW | hW
  · exact eq_bot_iff.mpr (le_trans le_sup_left hW.le)
  · exfalso
    have hwe' : w⁻¹.app P.f = P.e := by
      have := Gom.app_inv_app w P.e
      rwa [hwe] at this
    have hCfix : ∀ c ∈ C, τ • c = c := by
      intro c hc
      have hc' : c ∈ FC ⊔ FC.map (DistribSMul.toAddMonoidHom M w) := by rw [hW]; trivial
      obtain ⟨f, hf, y, hy, hfy⟩ := AddSubgroup.mem_sup.mp hc'
      obtain ⟨f', hf', rfl⟩ := AddSubgroup.mem_map.mp hy
      have hyC' : w • f' ∈ C' := smul_mem_fixedSub_Lom_of_app hwe hf'.1
      have hyC : w • f' ∈ C := by
        have : w • f' = c - f := by
          rw [← hfy]
          show w • f' = f + w • f' - f
          abel
        rw [show DistribSMul.toAddMonoidHom M w f' = w • f' from rfl] at hfy
        rw [this]
        exact C.sub_mem hc hf.1
      have h0 : w • f' ∈ C ⊓ C' := ⟨hyC, hyC'⟩
      rw [hdec.inf_eq_bot, AddSubgroup.mem_bot] at h0
      have hcf : c = f := by
        rw [← hfy]
        show f + w • f' = f
        rw [h0, add_zero]
      rw [hcf]
      exact hf.2 τ rfl
    have hC'fix : ∀ c ∈ C', τ • c = c := by
      intro c' hc'
      have hc'' : w⁻¹ • c' ∈ C := smul_mem_fixedSub_Lom_of_app hwe' hc'
      have hfix'' := hCfix _ hc''
      have e1 : τ • c' = w • (w⁻¹ * τ * w) • w⁻¹ • c' := by
        simp only [mul_smul, smul_inv_smul]
      have e2 : (w⁻¹ * τ * w) • w⁻¹ • c' = w⁻¹ • c' := by
        rw [torusG_conj_swap' hn3 P hs hwe hwf]
        have h3 : τ⁻¹ • w⁻¹ • c' = w⁻¹ • c' := by
          have := hfix''
          calc τ⁻¹ • w⁻¹ • c' = τ⁻¹ • τ • w⁻¹ • c' := by rw [this]
            _ = w⁻¹ • c' := inv_smul_smul τ _
        exact h3
      rw [e1, e2, smul_inv_smul]
    have htriv : ∀ m : M, τ • m = m := by
      intro m
      have hm : m ∈ C ⊔ C' := by rw [hdec.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hm
      rw [smul_add, hCfix a ha, hC'fix b hb]
    exact torus_not_trivial hn h2 P hwf hdec hs hs1 htriv

theorem fixedSub_inv_singleton {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M]
    [DistribMulAction Γ M] (τ : Γ) : fixedSub M {τ⁻¹} = fixedSub M {τ} := by
  ext m
  simp only [mem_fixedSub, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc τ • m = τ • (τ⁻¹ • m) := by rw [h]
      _ = m := smul_inv_smul τ m
  · intro h
    rw [inv_smul_eq_iff]
    exact h.symm

theorem torus_fixedSub_eq_bot (hK : 2 < Nat.card K) (hn : 4 ≤ n)
    {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction (Gom (quadPlus n K)) M]
    (h2 : ∀ m : M, m + m = 0) [Nontrivial M]
    (hirr : ∀ W : AddSubgroup M, (∀ (g : Gom (quadPlus n K)) (x : M), x ∈ W → g • x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (P : HypPair (quadPlus n K))
    (hdec : IsCompl (fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))))
      (fixedSub M (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K)))))
    {s : K} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    fixedSub M {torusG (by omega) P hs} = ⊥ := by
  have hn3 : 3 ≤ n := by omega
  have h1 := torus_fixedSub_Lom_inf_eq_bot hK hn h2 hirr P hdec hs hs1
  have h1' := torus_fixedSub_Lom_inf_eq_bot hK hn h2 hirr (pairSwap P) hdec.symm hs hs1
  rw [torusG_swap, fixedSub_inv_singleton] at h1'
  set τ := torusG hn3 P hs with hτ
  have hτe : τ.app P.e = s • P.e := torusLin_app_e P s
  have hτf : τ.app P.f = s⁻¹ • P.f := torusLin_app_f P hs
  have hNe : τ ∈ Subgroup.normalizer (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) :=
    mem_normalizer_Lom hs hτe
  have hNf : τ ∈ Subgroup.normalizer (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K))) :=
    mem_normalizer_Lom (inv_ne_zero hs) hτf
  rw [eq_bot_iff]
  intro m hm
  have hm' : m ∈ fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) ⊔
      fixedSub M (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K))) := by
    rw [hdec.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hm'
  have hτm : τ • (a + b) = a + b := hm τ rfl
  have haτ : τ • a ∈ fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) :=
    smul_mem_fixedSub_of_normalizer hNe ha
  have hbτ : τ • b ∈ fixedSub M (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K))) :=
    smul_mem_fixedSub_of_normalizer hNf hb
  have hdiff : τ • a - a ∈ fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) ⊓
      fixedSub M (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K))) := by
    refine ⟨AddSubgroup.sub_mem _ haτ ha, ?_⟩
    have : τ • a - a = b - τ • b := by
      rw [smul_add] at hτm
      have := congrArg (fun z => z - a - τ • b) hτm
      rw [show τ • a + τ • b - a - τ • b = τ • a - a by abel,
        show a + b - a - τ • b = b - τ • b by abel] at this
      exact this
    rw [this]
    exact AddSubgroup.sub_mem _ hb hbτ
  rw [hdec.inf_eq_bot, AddSubgroup.mem_bot, sub_eq_zero] at hdiff
  have hbfix : τ • b = b := by
    rw [smul_add, hdiff] at hτm
    exact add_left_cancel hτm
  have haM : a ∈ fixedSub M (Lom (quadPlus n K) P.e : Set (Gom (quadPlus n K))) ⊓
      fixedSub M {τ} := ⟨ha, fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact hdiff⟩
  have hbM : b ∈ fixedSub M (Lom (quadPlus n K) P.f : Set (Gom (quadPlus n K))) ⊓
      fixedSub M {τ} := ⟨hb, fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact hbfix⟩
  rw [h1, AddSubgroup.mem_bot] at haM
  have hbM' : b ∈ (⊥ : AddSubgroup M) := h1' ▸ hbM
  rw [AddSubgroup.mem_bot] at hbM'
  rw [haM, hbM', add_zero]
  exact AddSubgroup.zero_mem _

end FPF

end CFSG.RankThree.GF2n.Stroth80.Sec715Torus
