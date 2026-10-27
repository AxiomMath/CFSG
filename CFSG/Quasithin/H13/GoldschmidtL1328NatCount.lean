module

public import CFSG.Quasithin.H13.A6Set14
public import CFSG.Quasithin.H13.U3S1344A

public section

namespace CFSG.Quasithin.H13.A6

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def k4F : Fin 4 → Perm (Fin 6) :=
  ![1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

theorem k4F_inj : ∀ i j : Fin 4, k4F i = k4F j → i = j := by decide +kernel

theorem k4F_surj : ∀ σ ∈ K4L, ∃ i, k4F i = σ := by decide +kernel

theorem k4F_zero : k4F 0 = 1 := by decide +kernel

theorem k4_card_mul_lt_sixteen : ∀ f : Fin 4 → Bool, (∃ i, i ≠ 0 ∧ f i = true) →
    (Finset.univ.filter (fun i => f i = true)).card *
      (Finset.univ.filter (fun x : P6 => InW4 x ∧
        ∀ i, f i = true → act4f (k4F i) x = x)).card < 16 := by
  decide +kernel

theorem e8_even_K4 : ∀ σ ∈ S14.E8, Perm.sign σ = 1 → σ ∈ K4L := by decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s4_conjAct_eq_one_iff_rho (S : Setting4 G T L V) (g : ↥(normalizer (V : Set G))) :
    conjAct V g = 1 ↔ S.frame.ρ g = 1 := by
  rw [A4.conjAct_eq_one_iff, S.rho_eq_one_iff]

theorem s4_card_coords (S : Setting4 G T L V) {A : Subgroup G}
    (hAN : A ≤ normalizer (V : Set G))
    (hAK : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A → S.frame.ρ a ∈ K4L) :
    ∃ f : Fin 4 → Bool,
      (∀ i, f i = true ↔ ∃ a : ↥(normalizer (V : Set G)), (a : G) ∈ A ∧ S.frame.ρ a = k4F i) ∧
      (A ⊓ centralizer (V : Set G)).relIndex A =
        (Finset.univ.filter (fun i => f i = true)).card ∧
      Nat.card ↥(V ⊓ centralizer (A : Set G)) =
        (Finset.univ.filter (fun x : P6 => InW4 x ∧
          ∀ i, f i = true → act4f (k4F i) x = x)).card := by
  classical
  have hinj := k4F_inj
  have hsurj := k4F_surj
  let f : Fin 4 → Bool := fun i =>
    decide (∃ a : ↥(normalizer (V : Set G)), (a : G) ∈ A ∧ S.frame.ρ a = k4F i)
  have hf : ∀ i, f i = true ↔
      ∃ a : ↥(normalizer (V : Set G)), (a : G) ∈ A ∧ S.frame.ρ a = k4F i := fun i =>
    decide_eq_true_iff
  refine ⟨f, hf, ?_, ?_⟩
  ·
    rw [← card_autOn_eq_relIndex hAN]
    set X := (A.subgroupOf (normalizer (V : Set G))).map S.frame.ρ with hX
    have h1 : Nat.card ↥(autOn A V) = Nat.card ↥X :=
      Nat.card_congr (U3.mapMulEquivOfKer (conjAct V) S.frame.ρ (s4_conjAct_eq_one_iff_rho S)
        (A.subgroupOf (normalizer (V : Set G)))).toEquiv
    rw [h1]
    let φ : {i : Fin 4 // f i = true} → ↥X := fun i => ⟨k4F i.1, by
      obtain ⟨a, ha, hρ⟩ := (hf i.1).1 i.2
      exact ⟨a, mem_subgroupOf.2 ha, hρ⟩⟩
    have hφ : Function.Bijective φ := by
      refine ⟨fun i j hij => Subtype.ext (hinj _ _ (congrArg Subtype.val hij)), fun σ => ?_⟩
      obtain ⟨a, ha, hρ⟩ := σ.2
      obtain ⟨i, hi⟩ := hsurj _ (hAK a (mem_subgroupOf.1 ha))
      exact ⟨⟨i, (hf i).2 ⟨a, mem_subgroupOf.1 ha, hi.symm⟩⟩,
        Subtype.ext (hi.trans hρ)⟩
    have e : {i : Fin 4 // f i = true} ≃ ↥X := Equiv.ofBijective φ hφ
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  ·
    set s := Finset.univ.filter (fun x : P6 => InW4 x ∧
      ∀ i, f i = true → act4f (k4F i) x = x) with hs
    have hfwd : ∀ w : ↥(V ⊓ centralizer (A : Set G)),
        (S.frame.ψ ⟨w, w.2.1⟩ : P6) ∈ s := by
      intro w
      rw [hs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (S.frame.ψ ⟨w, w.2.1⟩).2, fun i hi => ?_⟩
      obtain ⟨a, ha, hρ⟩ := (hf i).1 hi
      have hc : (a : G) * w * (a : G)⁻¹ = w := by
        rw [mem_centralizer_iff.mp w.2.2 a ha, mul_inv_cancel_right]
      have := congrArg Subtype.val ((S.conj_eq_iff a ⟨w, w.2.1⟩).1 hc)
      rw [act4_coe, hρ] at this
      exact this
    have hbwd : ∀ x : ↥s, ((S.frame.ψ.symm ⟨x.1, (Finset.mem_filter.1 x.2).2.1⟩ : ↥V) : G) ∈
        V ⊓ centralizer (A : Set G) := by
      intro x
      refine ⟨(S.frame.ψ.symm _).2, mem_centralizer_iff.2 fun a ha => ?_⟩
      set v : ↥V := S.frame.ψ.symm ⟨x.1, (Finset.mem_filter.1 x.2).2.1⟩ with hv
      obtain ⟨i, hi⟩ := hsurj _ (hAK ⟨a, hAN ha⟩ ha)
      have hfi : f i = true := (hf i).2 ⟨⟨a, hAN ha⟩, ha, hi.symm⟩
      have hfix := (Finset.mem_filter.1 x.2).2.2 i hfi
      have hc : (a : G) * v * a⁻¹ = v := by
        refine (S.conj_eq_iff ⟨a, hAN ha⟩ v).2 (Subtype.ext ?_)
        rw [act4_coe, ← hi, hv, MulEquiv.apply_symm_apply]
        exact hfix
      calc a * (v : G) = a * v * a⁻¹ * a := by group
        _ = v * a := by rw [hc]
    have e : ↥(V ⊓ centralizer (A : Set G)) ≃ ↥s :=
      { toFun := fun w => ⟨S.frame.ψ ⟨w, w.2.1⟩, hfwd w⟩
        invFun := fun x => ⟨_, hbwd x⟩
        left_inv := fun w => by
          apply Subtype.ext
          show ((S.frame.ψ.symm ⟨(S.frame.ψ ⟨w, w.2.1⟩ : P6), _⟩ : ↥V) : G) = w
          exact congrArg (Subtype.val : ↥V → G) (S.frame.ψ.symm_apply_apply ⟨w, w.2.1⟩)
        right_inv := fun x => by
          apply Subtype.ext
          show ((S.frame.ψ (⟨_, (hbwd x).1⟩ : ↥V)) : P6) = x
          have : (⟨_, (hbwd x).1⟩ : ↥V) =
              S.frame.ψ.symm ⟨x.1, (Finset.mem_filter.1 x.2).2.1⟩ := rfl
          rw [this, MulEquiv.apply_symm_apply] }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem s4_relIndex_mul_card_lt (S : Setting4 G T L V) {A : Subgroup G}
    (hAN : A ≤ normalizer (V : Set G))
    (hAK : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A → S.frame.ρ a ∈ K4L)
    (hA : ¬ A ≤ centralizer (V : Set G)) :
    (A ⊓ centralizer (V : Set G)).relIndex A * Nat.card ↥(V ⊓ centralizer (A : Set G)) < 16 := by
  obtain ⟨f, hf, h1, h2⟩ := s4_card_coords S hAN hAK
  rw [h1, h2]
  refine k4_card_mul_lt_sixteen f ?_
  obtain ⟨a, haA, haC⟩ := Set.not_subset.1 hA
  have haN : a ∈ normalizer (V : Set G) := hAN haA
  obtain ⟨i, hi⟩ := k4F_surj _ (hAK ⟨a, haN⟩ haA)
  refine ⟨i, fun hi0 => haC ?_, (hf i).2 ⟨⟨a, haN⟩, haA, hi.symm⟩⟩
  rw [hi0, k4F_zero] at hi
  exact (S.rho_eq_one_iff ⟨a, haN⟩).1 hi.symm

end CFSG.Quasithin.H13.A6
