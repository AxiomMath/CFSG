module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Strip
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
import CFSG.HardMathSupport.U4FF.SmallGL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

private theorem eq_one_of_forall_even : ∀ σ : Equiv.Perm (Fin 5),
    (∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 → (fun i => y (σ.symm i)) = y) → σ = 1 := by
  decide +kernel

private theorem card_fix_two_le : ∀ σ τ : Equiv.Perm (Fin 5), σ * σ = 1 ∧ σ ≠ 1 →
    τ * τ = 1 ∧ σ * τ = τ * σ ∧ τ ≠ 1 ∧ σ ≠ τ →
      (Finset.univ.filter fun y : Fin 5 → ZMod 2 => ∑ i, y i = 0 ∧
        (fun i => y (σ.symm i)) = y ∧ (fun i => y (τ.symm i)) = y).card ≤ 4 := by
  decide +kernel

private theorem mem_four_of_commute : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 ∧ σ ≠ 1 →
    ∀ τ : Equiv.Perm (Fin 5), τ * τ = 1 ∧ σ * τ = τ * σ ∧ τ ≠ 1 ∧ σ ≠ τ →
      ∀ υ : Equiv.Perm (Fin 5), υ * υ = 1 ∧ σ * υ = υ * σ ∧ τ * υ = υ * τ →
        υ = 1 ∨ υ = σ ∨ υ = τ ∨ υ = σ * τ := by
  decide +kernel

private theorem card_even : Nat.card {y : Fin 5 → ZMod 2 // ∑ i, y i = 0} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem card_le_of_forall_mem {M : Type*} [Group M] {K : Subgroup M} {F : Finset M}
    (h : ∀ z ∈ K, z ∈ F) : Nat.card K ≤ F.card :=
  (Nat.card_le_card_of_injective (fun z : K => (⟨z, h z z.2⟩ : F))
    fun _ _ hab => Subtype.ext (congrArg (fun w : F => (w : M)) hab)).trans_eq
      (by rw [Nat.card_eq_fintype_card, Fintype.card_coe])

private theorem two_mul_card_fixOn_le [Finite V] {X : Subgroup G} {N : Submodule (ZMod 2) V}
    {x : G} (hx : x ∈ X) {u : V} (hu : u ∈ N) (hxu : ρ x u ≠ u) :
    2 * Nat.card (fixOn ρ X N) ≤ Nat.card N := by
  have hlt : fixOn ρ X N < N :=
    lt_of_le_of_ne inf_le_left fun h => hxu ((mem_fixOn.1 (h ▸ hu)).2 x hx)
  have hr := Submodule.finrank_lt_finrank_of_lt hlt
  rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) hr

private theorem noExcess_of_card_imgGL_mul_le {X : Subgroup G} {N : Submodule (ZMod 2) V}
    (hXN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X N)
    (h : Nat.card (imgGL ρ X N hXN X) * Nat.card (fixOn ρ X N) ≤ Nat.card N) :
    NoExcess ρ X N := by
  have hc := card_imgGL_mul_card_cenOn (ρ := ρ) (H := X) (U := N) (hU := hXN) le_rfl
  show Nat.card X * Nat.card (fixOn ρ X N) ≤ Nat.card N * Nat.card (cenOn ρ X N)
  rw [← hc, mul_comm (Nat.card (imgGL ρ X N hXN X)), mul_assoc, mul_comm (Nat.card N)]
  exact Nat.mul_le_mul_left _ h

private theorem noExcess_of_card_imgGL_le_two [Finite V] {X : Subgroup G}
    {N : Submodule (ZMod 2) V} (hXN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X N)
    (h2 : Nat.card (imgGL ρ X N hXN X) ≤ 2) : NoExcess ρ X N := by
  refine noExcess_of_card_imgGL_mul_le hXN ?_
  by_cases hbot : imgGL ρ X N hXN X = ⊥
  · rw [hbot, Subgroup.card_bot, one_mul, card_eq_two_pow_finrank, card_eq_two_pow_finrank]
    exact Nat.pow_le_pow_right (by norm_num) (Submodule.finrank_mono inf_le_left)
  · rw [imgGL_eq_bot_iff le_rfl] at hbot
    obtain ⟨x, hx, hxN⟩ := Set.not_subset.1 hbot
    obtain ⟨u, hu, hxu⟩ : ∃ u ∈ N, ρ x u ≠ u := by
      by_contra hne
      exact hxN ⟨hx, fun u hu => by_contra fun h => hne ⟨u, hu, h⟩⟩
    exact (Nat.mul_le_mul_right _ h2).trans (two_mul_card_fixOn_le hx hu hxu)

theorem noExcess_of_finrank_two [Finite V] {X : Subgroup G} {N : Submodule (ZMod 2) V}
    (hN : Module.finrank (ZMod 2) N = 2) (hX : CFSG.Open.IsElemAbelian 2 X)
    (hXN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X N) : NoExcess ρ X N := by
  refine noExcess_of_card_imgGL_le_two hXN ?_
  have hGL : Nat.card (N ≃ₗ[ZMod 2] N) = 6 := by
    rw [CFSG.HardMathSupport.U4FF.card_linearEquiv_eq_prod hN, Fin.prod_univ_two]
    norm_num
  haveI : Finite (N ≃ₗ[ZMod 2] N) := Nat.finite_of_card_ne_zero (by rw [hGL]; norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(imgGL ρ X N hXN X) := fun z => by
    obtain ⟨b, hb, hbz⟩ := mem_imgGL.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    have hb2 : b ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hX.2 _ hb)
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hbz, ← map_pow, hb2, map_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  have hdvd : 2 ^ k ∣ 6 := hk ▸ hGL ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have h4 : 2 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    exact absurd h4 (by decide)
  rw [hk]
  interval_cases k <;> norm_num

private theorem resGL_eq_of_forall {X : Subgroup G} {N : Submodule (ZMod 2) V}
    {hXN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X N} {b c : ↥X} (h : ∀ u ∈ N, ρ b u = ρ c u) :
    resGL ρ X N hXN b = resGL ρ X N hXN c :=
  LinearEquiv.ext fun u => Subtype.ext (h u u.2)

theorem noExcess_of_secNatS5 [Finite V] {H : Subgroup G} {N : Submodule (ZMod 2) V}
    (hS5 : SecNatS5 ρ H N ⊥) {X : Subgroup G} (hX : CFSG.Open.IsElemAbelian 2 X)
    (hXH : ∀ x ∈ X, ∃ h ∈ H, ∀ u ∈ N, ρ x u = ρ h u) : NoExcess ρ X N := by
  classical
  obtain ⟨hHN, -, -, φ, ψ, -, hK, hsum, hsurj, hE⟩ := hS5
  have hXN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X N := fun x hx u hu => by
    obtain ⟨h, hh, hhN⟩ := hXH x hx
    rw [hhN u hu]
    exact hHN h hh u hu
  have hinj : ∀ u ∈ N, ∀ u' ∈ N, ψ u = ψ u' → u = u' := fun u hu u' hu' h =>
    sub_eq_zero.1 ((Submodule.mem_bot _).1 (hK _ (sub_mem hu hu') (by rw [map_sub, h, sub_self])))
  have hσ : ∀ x ∈ X, ∃ σ : Equiv.Perm (Fin 5), ∀ u ∈ N, ψ (ρ x u) = fun i => ψ u (σ.symm i) :=
    fun x hx => by
      obtain ⟨h, hh, hhN⟩ := hXH x hx
      exact ⟨φ ⟨h, hh⟩, fun u hu => by rw [hhN u hu]; exact hE ⟨h, hh⟩ u hu⟩
  choose σ hσ using hσ
  have hfa : ∀ τ τ' : Equiv.Perm (Fin 5),
      (∀ u ∈ N, (fun i => ψ u (τ.symm i)) = fun i => ψ u (τ'.symm i)) → τ = τ' :=
    fun τ τ' h => by
      have h1 : τ'⁻¹ * τ = 1 := eq_one_of_forall_even _ fun y hy => by
        obtain ⟨u, hu, rfl⟩ := hsurj y hy
        funext i
        have h2 := congrFun (h u hu) (τ' i)
        rw [Equiv.symm_apply_apply] at h2
        exact h2
      exact (inv_mul_eq_one.1 h1).symm
  have hmul : ∀ x (hx : x ∈ X) y (hy : y ∈ X), ∀ u ∈ N,
      ψ (ρ x (ρ y u)) = fun i => ψ u ((σ x hx * σ y hy).symm i) := fun x hx y hy u hu => by
    rw [hσ x hx _ (hXN y hy u hu), hσ y hy u hu]
    rfl
  have hsq : ∀ x ∈ X, ∀ u : V, ρ x (ρ x u) = u := fun x hx u => by
    rw [← glRep_mul_apply, ← pow_two, hX.2 x hx, map_one]
    rfl
  have hcm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hX.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hinv : ∀ x (hx : x ∈ X), σ x hx * σ x hx = 1 := fun x hx =>
    hfa _ _ fun u hu => by rw [← hmul x hx x hx u hu, hsq x hx]; rfl
  have hcomm : ∀ x (hx : x ∈ X) y (hy : y ∈ X), σ x hx * σ y hy = σ y hy * σ x hx :=
    fun x hx y hy => hfa _ _ fun u hu => by
      rw [← hmul x hx y hy u hu, ← hmul y hy x hx u hu, ← glRep_mul_apply, ← glRep_mul_apply,
        hcm x hx y hy]
  have hsame : ∀ x (hx : x ∈ X) (τ : Equiv.Perm (Fin 5)) (w : G), (∀ u ∈ N, ρ w u ∈ N) →
      (∀ u ∈ N, ψ (ρ w u) = fun i => ψ u (τ.symm i)) → σ x hx = τ → ∀ u ∈ N, ρ x u = ρ w u :=
    fun x hx τ w hwN hw he u hu =>
      hinj _ (hXN x hx u hu) _ (hwN u hu) (by rw [hσ x hx u hu, hw u hu, he])
  by_cases hbig : ∃ x ∈ X, ∃ y ∈ X, (∃ u ∈ N, ρ x u ≠ u) ∧ (∃ u ∈ N, ρ y u ≠ u) ∧
      ∃ u ∈ N, ρ y u ≠ ρ x u
  · obtain ⟨x, hx, y, hy, ⟨u₁, hu₁, h₁⟩, ⟨u₂, hu₂, h₂⟩, ⟨u₃, hu₃, h₃⟩⟩ := hbig
    have hid : ∀ u ∈ N, ψ (ρ 1 u) = fun i => ψ u ((1 : Equiv.Perm (Fin 5)).symm i) :=
      fun u _ => by rw [map_one]; rfl
    have hx1 : σ x hx ≠ 1 := fun he =>
      h₁ ((hsame x hx 1 1 (fun u hu => by rw [map_one]; exact hu) hid he u₁ hu₁).trans
        (by rw [map_one]; rfl))
    have hy1 : σ y hy ≠ 1 := fun he =>
      h₂ ((hsame y hy 1 1 (fun u hu => by rw [map_one]; exact hu) hid he u₂ hu₂).trans
        (by rw [map_one]; rfl))
    have hxy : σ x hx ≠ σ y hy := fun he =>
      h₃ (hsame y hy (σ x hx) x (hXN x hx) (hσ x hx) he.symm u₃ hu₃)
    refine noExcess_of_card_imgGL_mul_le hXN ?_
    have hN16 : Nat.card N = 16 := by
      rw [← card_even]
      refine Nat.card_congr (Equiv.ofBijective (fun u : N => ⟨ψ u, hsum u u.2⟩) ⟨fun u u' h =>
        Subtype.ext (hinj _ u.2 _ u'.2 (congrArg Subtype.val h)), fun y => ?_⟩)
      obtain ⟨u, hu, hyu⟩ := hsurj y.1 y.2
      exact ⟨⟨u, hu⟩, Subtype.ext hyu⟩
    have hI : Nat.card (imgGL ρ X N hXN X) ≤ 4 := by
      refine (card_le_of_forall_mem (F := {1, resGL ρ X N hXN ⟨x, hx⟩,
        resGL ρ X N hXN ⟨y, hy⟩, resGL ρ X N hXN ⟨x * y, X.mul_mem hx hy⟩}) ?_).trans
          Finset.card_le_four
      intro z hz
      obtain ⟨b, hb, rfl⟩ := mem_imgGL.1 hz
      have hb' : (b : G) ∈ X := b.2
      rcases mem_four_of_commute _ ⟨hinv x hx, hx1⟩ _ ⟨hinv y hy, hcomm x hx y hy, hy1, hxy⟩ _
        ⟨hinv b hb', hcomm x hx b hb', hcomm y hy b hb'⟩ with h | h | h | h
      · refine Finset.mem_insert.2 (Or.inl ?_)
        exact (resGL_eq_one_iff _).2 fun u hu =>
          (hsame b hb' 1 1 (fun u hu => by rw [map_one]; exact hu) hid h u hu).trans
            (by rw [map_one]; rfl)
      · refine Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inl ?_)))
        exact resGL_eq_of_forall (hsame b hb' (σ x hx) x (hXN x hx) (hσ x hx) h)
      · refine Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inr
          (Finset.mem_insert.2 (Or.inl ?_)))))
        exact resGL_eq_of_forall (hsame b hb' (σ y hy) y (hXN y hy) (hσ y hy) h)
      · refine Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inr
          (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 ?_))))))
        refine resGL_eq_of_forall (hsame b hb' _ (x * y) (hXN _ (X.mul_mem hx hy)) ?_ h)
        intro u hu
        rw [glRep_mul_apply]
        exact hmul x hx y hy u hu
    have hF : Nat.card (fixOn ρ X N) ≤ 4 := by
      refine le_trans ?_
        (card_fix_two_le _ _ ⟨hinv x hx, hx1⟩ ⟨hinv y hy, hcomm x hx y hy, hy1, hxy⟩)
      refine (Nat.card_le_card_of_injective (fun u : fixOn ρ X N => (⟨ψ u, ?_⟩ :
        ↥(Finset.univ.filter fun v : Fin 5 → ZMod 2 => ∑ i, v i = 0 ∧
          (fun i => v ((σ x hx).symm i)) = v ∧ (fun i => v ((σ y hy).symm i)) = v)))
        fun u u' h => Subtype.ext (hinj _ (mem_fixOn.1 u.2).1 _ (mem_fixOn.1 u'.2).1
          (congrArg (fun w : ↥(Finset.univ.filter fun v : Fin 5 → ZMod 2 => ∑ i, v i = 0 ∧
            (fun i => v ((σ x hx).symm i)) = v ∧ (fun i => v ((σ y hy).symm i)) = v) =>
              (w : Fin 5 → ZMod 2)) h))).trans_eq (by rw [Nat.card_eq_fintype_card,
                Fintype.card_coe])
      obtain ⟨huN, huX⟩ := mem_fixOn.1 u.2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hsum _ huN, ?_, ?_⟩
      · rw [← hσ x hx _ huN, huX x hx]
      · rw [← hσ y hy _ huN, huX y hy]
    calc Nat.card (imgGL ρ X N hXN X) * Nat.card (fixOn ρ X N) ≤ 4 * 4 := Nat.mul_le_mul hI hF
      _ = Nat.card N := hN16.symm
  · refine noExcess_of_card_imgGL_le_two hXN ?_
    by_cases hx : ∃ x ∈ X, ∃ u ∈ N, ρ x u ≠ u
    · obtain ⟨x, hx, hxu⟩ := hx
      refine (card_le_of_forall_mem (F := {1, resGL ρ X N hXN ⟨x, hx⟩}) fun z hz => ?_).trans
        Finset.card_le_two
      obtain ⟨b, hb, rfl⟩ := mem_imgGL.1 hz
      by_cases hb1 : ∃ u ∈ N, ρ b u ≠ u
      · have hbx : ∀ u ∈ N, ρ b u = ρ x u := fun u hu => by
          by_contra hne
          exact hbig ⟨x, hx, b, hb, hxu, hb1, u, hu, hne⟩
        exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (resGL_eq_of_forall hbx)))
      · refine Finset.mem_insert.2 (Or.inl ((resGL_eq_one_iff _).2 fun u hu => ?_))
        by_contra hne
        exact hb1 ⟨u, hu, hne⟩
    · refine (card_le_of_forall_mem (F := {1}) fun z hz => ?_).trans (by simp)
      obtain ⟨b, hb, rfl⟩ := mem_imgGL.1 hz
      refine Finset.mem_singleton.2 ((resGL_eq_one_iff _).2 fun u hu => ?_)
      by_contra hne
      exact hx ⟨b, hb, u, hu, hne⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
