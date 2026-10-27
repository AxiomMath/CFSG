module

public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Flag
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75
open CFSG.SignalizerFunctorTheorem.Quadratic
open Subgroup

private def w16q_fixSet {B W : Type*} [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : B →* LGL 2 W) (T : Subgroup B) : Set W :=
  {v | ∀ a ∈ T, ρ a v = v}

private lemma w16q_fixSet_mem_conj {B W : Type*} [Group B] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : B →* LGL 2 W) (g : B) (T : Subgroup B) (v : W) :
    v ∈ w16q_fixSet ρ (conjSubgroup g T) ↔ ρ g⁻¹ v ∈ w16q_fixSet ρ T := by
  constructor
  · intro hv a ha
    have hmem : g * a * g⁻¹ ∈ conjSubgroup g T := by
      rw [mem_conjSubgroup]
      have heq : g⁻¹ * (g * a * g⁻¹) * g = a := by group
      rwa [heq]
    have h1 : ρ g (ρ a (ρ g⁻¹ v)) = v := by
      have h := hv (g * a * g⁻¹) hmem
      rw [map_mul, map_mul] at h
      exact h
    have h2 : ρ g (ρ g⁻¹ v) = v := by
      simpa [map_inv] using (ρ g).apply_symm_apply v
    exact (ρ g).injective (h1.trans h2.symm)
  · intro hv a ha
    rw [conjSubgroup, Subgroup.mem_map] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    change ρ (MulAut.conj g c) v = v
    rw [MulAut.conj_apply, map_mul, map_mul]
    change ρ g (ρ c (ρ g⁻¹ v)) = v
    rw [hv c hc]
    simpa [map_inv] using (ρ g).apply_symm_apply v

private lemma w16q_fixSet_conj {B W : Type*} [Group B] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : B →* LGL 2 W) (g : B) (T : Subgroup B) :
    w16q_fixSet ρ (conjSubgroup g T) = ρ g '' w16q_fixSet ρ T := by
  ext v
  rw [w16q_fixSet_mem_conj, Set.mem_image]
  constructor
  · intro hv
    exact ⟨ρ g⁻¹ v, hv, by simpa [map_inv] using (ρ g).apply_symm_apply v⟩
  · rintro ⟨u, hu, rfl⟩
    have hgu : ρ g⁻¹ (ρ g u) = u := by
      simpa [map_inv] using (ρ g).symm_apply_apply u
    simpa [hgu] using hu

private lemma w16q_sup_le_fixSet {B W : Type*} [Group B] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : B →* LGL 2 W) (v : W) {s t : Subgroup B}
    (hs : ∀ b ∈ s, ρ b v = v) (ht : ∀ b ∈ t, ρ b v = v) :
    ∀ b ∈ s ⊔ t, ρ b v = v := by
  let K : Subgroup B :=
    { carrier := {b : B | ρ b v = v}
      mul_mem' := by
        rintro a b (ha : ρ a v = v) (hb : ρ b v = v)
        show ρ (a * b) v = v
        rw [map_mul]
        change ρ a (ρ b v) = v
        rw [hb, ha]
      one_mem' := by
        show ρ 1 v = v
        rw [map_one]
        rfl
      inv_mem' := by
        rintro a (ha : ρ a v = v)
        show ρ a⁻¹ v = v
        have h2 : ρ a⁻¹ (ρ a v) = v := by
          simpa [map_inv] using (ρ a).symm_apply_apply v
        exact (congrArg (fun w => ρ a⁻¹ w) ha).symm.trans h2 }
  have hK : s ⊔ t ≤ K := sup_le (fun b hb => hs b hb) (fun b hb => ht b hb)
  intro b hb
  exact hK hb

private lemma w16q_ncard_iUnion_of_pairwise_disjoint {ι α : Type*} [Finite ι]
    {s : ι → Set α} (hfin : ∀ i, (s i).Finite)
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j))
    (c : ℕ) (hc : ∀ i, (s i).ncard = c) :
    (⋃ i, s i).ncard = Nat.card ι * c := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [Set.ncard_iUnion_of_finite hfin hdisj]
  rw [finsum_congr hc, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card]
  simp

private lemma w16q_index_arith (q : ℕ) (hq : 2 ≤ q) :
    q * (q ^ 2 - 1) / (q * (q - 1)) = q + 1 := by
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h := Nat.sq_sub_sq q 1
    simpa [mul_comm] using h
  have hpos : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
  have hmul : q * (q ^ 2 - 1) = (q * (q - 1)) * (q + 1) := by
    rw [hfac]
    ring
  rw [hmul, Nat.mul_div_cancel_left (q + 1) hpos]

theorem exists_dvd_two_pow_sub_one {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hdvd : r ∣ Nat.card (LGL 2 W)) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ Module.finrank (ZMod 2) W ∧ r ∣ 2 ^ i - 1 := by
  haveI : FiniteDimensional (ZMod 2) W :=
    (Module.finite_iff_finite (R := ZMod 2) (M := W)).2 inferInstance
  have hcard : Nat.card (LGL 2 W) =
      ∏ i : Fin (Module.finrank (ZMod 2) W),
        (2 ^ Module.finrank (ZMod 2) W - 2 ^ (i : ℕ)) := by
    rw [← Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toEquiv]
    rw [CFSG.LocalAnalysis.UniquenessCase.UCK.card_generalLinearGroup (K := ZMod 2) (M := W) rfl]
    simp [ZMod.card]
  rw [hcard] at hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hr.prime
    (fun i : Fin (Module.finrank (ZMod 2) W) =>
      2 ^ Module.finrank (ZMod 2) W - 2 ^ (i : ℕ))).mp hdvd
  have hid : (i : ℕ) < Module.finrank (ZMod 2) W := i.2
  have hsplit : 2 ^ Module.finrank (ZMod 2) W - 2 ^ (i : ℕ) =
      2 ^ (i : ℕ) * (2 ^ (Module.finrank (ZMod 2) W - i) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hid.le]
  rw [hsplit] at hi
  have hcop : Nat.Coprime r (2 ^ (i : ℕ)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  exact ⟨Module.finrank (ZMod 2) W - i, by omega, by omega, hcop.dvd_of_dvd_mul_left hi⟩

theorem four_mul_le_finrank_of_simple {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hcard : (2 ^ n) ^ 2 + 1 ∣ Nat.card X) (B : Subgroup X) (hB : B = ⊤)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : ↥B →* LGL 2 W) (hρ : ρ ≠ 1) :
    4 * n ≤ Module.finrank (ZMod 2) W := by
  subst hB
  let e : (⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
  let ρ' : X →* LGL 2 W := ρ.comp e.symm.toMonoidHom
  have hρ' : ρ' ≠ 1 := by
    intro h
    apply hρ
    refine MonoidHom.ext fun b => ?_
    have h1 : ρ' (e b) = ρ b := by
      show ρ (e.symm (e b)) = ρ b
      rw [MulEquiv.symm_apply_apply]
    have h2 : ρ' (e b) = 1 := by rw [h]; rfl
    rw [← h1, h2, MonoidHom.one_apply]
  have hker : ρ'.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ'.ker with h | h
    · exact h
    · exfalso
      apply hρ'
      refine MonoidHom.ext fun x => ?_
      have hx : x ∈ ρ'.ker := by rw [h]; trivial
      rw [MonoidHom.mem_ker] at hx
      rwa [MonoidHom.one_apply]
  have hinj : Function.Injective ρ' := (MonoidHom.ker_eq_bot_iff ρ').mp hker
  have hdvdGL : Nat.card X ∣ Nat.card (LGL 2 W) :=
    Subgroup.card_dvd_of_injective ρ' hinj
  obtain ⟨r, hr, hrdvd, hprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (4 * n) (by omega) (by omega)
  have hmodd : r ≠ 2 := by
    intro h2
    have he : Even (2 ^ (4 * n)) := Even.pow_of_ne_zero even_two (by omega)
    have ho : Odd (2 ^ (4 * n) - 1) :=
      Nat.Even.sub_odd (Nat.one_le_two_pow : 1 ≤ 2 ^ (4 * n)) he odd_one
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (h2 ▸ hrdvd))
  have hfac : 2 ^ (4 * n) - 1 = (2 ^ (2 * n) - 1) * ((2 ^ n) ^ 2 + 1) := by
    have h4 : 2 ^ (4 * n) = (2 ^ (2 * n)) ^ 2 := by rw [← pow_mul]; congr 1; ring
    have h2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul]; congr 1; ring
    rw [h4, h2]
    have hsq : ((2 ^ n) ^ 2) ^ 2 - 1 = ((2 ^ n) ^ 2 + 1) * ((2 ^ n) ^ 2 - 1) := by
      simpa using Nat.sq_sub_sq ((2 ^ n) ^ 2) 1
    rw [hsq]
    exact mul_comm _ _
  have hdvd' : r ∣ (2 ^ (2 * n) - 1) * ((2 ^ n) ^ 2 + 1) := hfac ▸ hrdvd
  have hrdvdGL : r ∣ Nat.card (LGL 2 W) := by
    rcases (hr.dvd_mul).mp hdvd' with h1 | h2
    · exact absurd h1 (hprim (2 * n) (by omega) (by omega))
    · exact dvd_trans (dvd_trans h2 hcard) hdvdGL
  obtain ⟨i, hi1, hi2, hri⟩ := exists_dvd_two_pow_sub_one hr hmodd hrdvdGL
  have h4i : 4 * n ≤ i := by
    by_contra hlt
    exact (hprim i hi1 (by omega)) hri
  omega

theorem exists_fixing_conj_of_card_eq {n : ℕ} (hn : 1 < n) {B : Type} [Group B] [Finite B]
    {P : Subgroup B} (hP : IsL2Pair B P (2 ^ n)) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : B →* LGL 2 W) (hW : Nat.card W = (2 ^ n) ^ 2)
    (hfix : Nat.card {w : W // ∀ a ∈ P, ρ a w = w} = 2 ^ n)
    (hB : ∀ w : W, (∀ b : B, ρ b w = w) → w = 0) (w : W) :
    ∃ b : B, ∀ a ∈ P, ρ a (ρ b w) = ρ b w := by
  have hq2 : 2 ≤ 2 ^ n := by
    have h := Nat.one_lt_pow (by omega : n ≠ 0) (by norm_num : (1 : ℕ) < 2)
    omega
  obtain ⟨P₀, hP₀⟩ := hP.exists_sylow_eq
  let F : Sylow 2 B → Set W := fun P' => w16q_fixSet ρ (P' : Subgroup B)
  have hFP₀ : (F P₀).ncard = 2 ^ n := by
    show (w16q_fixSet ρ (P₀ : Subgroup B)).ncard = 2 ^ n
    rw [hP₀]
    exact hfix
  have hI : Nat.card (Sylow 2 B) = 2 ^ n + 1 := by
    have h1 : Nat.card (Sylow 2 B) = (Subgroup.normalizer (P : Set B)).index := by
      rw [P₀.card_eq_index_normalizer]
      show (Subgroup.normalizer ((P₀ : Subgroup B) : Set B)).index =
        (Subgroup.normalizer (P : Set B)).index
      exact congrArg Subgroup.index
        (congrArg Subgroup.normalizer (congrArg (fun S : Subgroup B => (S : Set B)) hP₀))
    rw [h1, Subgroup.index_eq_card_div, hP.card_eq_mul, hP.card_normalizer]
    exact w16q_index_arith (2 ^ n) hq2
  have hFcard : ∀ P' : Sylow 2 B, (F P').ncard = 2 ^ n := by
    intro P'
    obtain ⟨g, hg⟩ := hP.exists_conj_eq_sylow P'
    have hP'eq : (P' : Subgroup B) = conjSubgroup g (P₀ : Subgroup B) := by
      rw [← hg, hP₀]
    have hset : F P' = ρ g '' F P₀ := by
      show w16q_fixSet ρ (P' : Subgroup B) =
        ρ g '' w16q_fixSet ρ (P₀ : Subgroup B)
      rw [hP'eq, w16q_fixSet_conj]
    rw [hset, Set.ncard_image_of_injective _ (ρ g).injective]
    exact hFP₀
  have hFzero : ∀ P' : Sylow 2 B, (0 : W) ∈ F P' := fun P' => by
    change ∀ a ∈ (P' : Subgroup B), ρ a (0 : W) = 0
    intro a _
    exact map_zero (ρ a)
  have hFinter : ∀ P' Q' : Sylow 2 B, P' ≠ Q' → F P' ∩ F Q' = {0} := by
    intro P' Q' hPQ
    ext v
    rw [Set.mem_inter_iff, Set.mem_singleton_iff]
    change ((∀ a ∈ (P' : Subgroup B), ρ a v = v) ∧
      (∀ a ∈ (Q' : Subgroup B), ρ a v = v)) ↔ v = 0
    constructor
    · rintro ⟨hvP, hvQ⟩
      apply hB v
      intro b
      have hsup : (P' : Subgroup B) ⊔ (Q' : Subgroup B) = ⊤ := hP.sup_sylow_eq_top hPQ
      exact w16q_sup_le_fixSet ρ v hvP hvQ b (by rw [hsup]; trivial)
    · intro hv
      subst hv
      exact ⟨fun a _ => map_zero (ρ a), fun a _ => map_zero (ρ a)⟩
  have hGdisj : Pairwise fun P' Q' : Sylow 2 B =>
      Disjoint (F P' \ {0}) (F Q' \ {0}) := by
    intro P' Q' hPQ
    rw [Set.disjoint_left]
    intro v hv hw
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hv hw
    have hmem : v ∈ ({0} : Set W) := by
      rw [← hFinter P' Q' hPQ]
      exact ⟨hv.1, hw.1⟩
    exact hv.2 hmem
  have hGcard : ∀ P' : Sylow 2 B, (F P' \ {0}).ncard = 2 ^ n - 1 := fun P' => by
    rw [Set.ncard_sdiff_singleton_of_mem (hFzero P'), hFcard P']
  have hGunion : (⋃ P' : Sylow 2 B, F P' \ {0}).ncard =
      Nat.card (Sylow 2 B) * (2 ^ n - 1) :=
    w16q_ncard_iUnion_of_pairwise_disjoint
      (fun _ => (Set.finite_univ (α := W)).subset (Set.subset_univ _))
      hGdisj (2 ^ n - 1) hGcard
  have hnotmem : (0 : W) ∉ ⋃ P' : Sylow 2 B, F P' \ {0} := by
    intro h
    obtain ⟨P', hP'⟩ := Set.mem_iUnion.mp h
    exact hP'.2 rfl
  have hinsert : insert (0 : W) (⋃ P' : Sylow 2 B, F P' \ {0}) =
      ⋃ P' : Sylow 2 B, F P' := by
    ext v
    rw [Set.mem_insert_iff, Set.mem_iUnion, Set.mem_iUnion]
    constructor
    · rintro (rfl | ⟨P', hP'⟩)
      · exact ⟨P₀, hFzero P₀⟩
      · exact ⟨P', hP'.1⟩
    · rintro ⟨P', hP'⟩
      by_cases h0 : v = 0
      · exact Or.inl h0
      · exact Or.inr ⟨P', hP', h0⟩
  have hcard : Nat.card W = (⋃ P' : Sylow 2 B, F P').ncard := by
    rw [← hinsert, Set.ncard_insert_of_notMem hnotmem, hGunion, hI, hW]
    have hq1 : 1 ≤ (2 ^ n) ^ 2 := by
      have hp : (0 : ℕ) < (2 ^ n) ^ 2 := pow_pos (by positivity) 2
      omega
    have hh : (2 ^ n + 1) * (2 ^ n - 1) = (2 ^ n) ^ 2 - 1 := by
      have := (Nat.sq_sub_sq (2 ^ n) 1).symm
      simpa using this
    rw [hh]
    exact (Nat.sub_add_cancel hq1).symm
  have hcover : (⋃ P' : Sylow 2 B, F P') = Set.univ := by
    rw [Set.eq_univ_iff_ncard]
    exact hcard.symm
  have hwU : w ∈ ⋃ P' : Sylow 2 B, F P' := by
    rw [hcover]
    trivial
  obtain ⟨P', hP'w⟩ := Set.mem_iUnion.mp hwU
  change ∀ a ∈ (P' : Subgroup B), ρ a w = w at hP'w
  obtain ⟨g, hg⟩ := hP.exists_conj_eq_sylow P'
  refine ⟨g⁻¹, fun a ha => ?_⟩
  have hmem : g * a * g⁻¹ ∈ (P' : Subgroup B) := by
    rw [← hg, mem_conjSubgroup]
    have heq : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rwa [heq]
  have h1 := hP'w (g * a * g⁻¹) hmem
  have h2 : ρ g (ρ a (ρ g⁻¹ w)) = w := by
    rw [map_mul, map_mul] at h1
    exact h1
  have h3 : ρ g (ρ g⁻¹ w) = w := by
    simpa [map_inv] using (ρ g).apply_symm_apply w
  exact (ρ g).injective (h2.trans h3.symm)

end CFSG.LocalAnalysis.WeakClosure81

end
