module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.Open.LocalVocabulary
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.StandardType.OrthAnchor

open CFSG.RankThree.Classical2 (orthDerived)

theorem bsL_data {G : Type} [Group G] {L Bs : Subgroup G} {x : G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hBsL : ∀ b : Bs, (b : G) ∈ L ↔ eta b i0 = 1) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    CFSG.Open.IsElemAbelian 3 (Bs.subgroupOf L) ∧ Nat.card (Bs.subgroupOf L) = 3 ^ (n - 1) ∧
      ∀ g ∈ Subgroup.centralizer (Bs.subgroupOf L : Set ↥L), g ^ 3 = 1 → g ∈ Bs.subgroupOf L := by
  classical
  have hj_exists : ∀ c d : Multiplicative (ZMod 3), c ≠ 1 →
      ∃ j : Fin 3, c ^ (j : ℕ) = d := by
    decide
  let α := Fin n → Multiplicative (ZMod 3)
  let phi : Bs.subgroupOf L →* α :=
    { toFun := fun a => eta ⟨(a : G), Subgroup.mem_subgroupOf.mp a.property⟩
      map_one' := by
        have h : (⟨((1 : Bs.subgroupOf L) : G),
            Subgroup.mem_subgroupOf.mp (1 : Bs.subgroupOf L).property⟩ : Bs) = 1 := by
          ext
          rfl
        rw [h, map_one]
      map_mul' := by
        intro a b
        have h : (⟨((a * b : Bs.subgroupOf L) : G),
            Subgroup.mem_subgroupOf.mp (a * b).property⟩ : Bs) =
            ⟨(a : G), Subgroup.mem_subgroupOf.mp a.property⟩ *
              ⟨(b : G), Subgroup.mem_subgroupOf.mp b.property⟩ := by
          ext
          rfl
        rw [h, map_mul] }
  have phi_injective : Function.Injective phi := by
    intro a b h
    have hb : (⟨(a : G), Subgroup.mem_subgroupOf.mp a.property⟩ : Bs) =
        ⟨(b : G), Subgroup.mem_subgroupOf.mp b.property⟩ := eta.injective h
    have hG : (a : G) = (b : G) := congrArg (fun z : Bs => (z : G)) hb
    apply Subtype.ext
    apply Subtype.ext
    exact hG
  have hsquare : IsMulCommutative (Bs.subgroupOf L) := by
    refine IsMulCommutative.of_comm (fun a b => phi_injective ?_)
    rw [map_mul, map_mul]
    exact mul_comm (phi a) (phi b)
  have hcube : ∀ a : Bs.subgroupOf L, a ^ 3 = 1 := by
    intro a
    have h3 : ∀ y : Multiplicative (ZMod 3), y ^ 3 = 1 := by
      intro y
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    apply phi_injective
    rw [map_pow, map_one]
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    exact h3 (phi a i)
  have hcard_sub : Nat.card (Bs.subgroupOf L) = Nat.card {f : α // f i0 = 1} := by
    let e1 : Bs.subgroupOf L ≃ {b : Bs // (b : G) ∈ L} :=
      { toFun := fun y => ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp y.property⟩, y.1.property⟩
        invFun := fun b => ⟨⟨(b.1 : G), b.2⟩, Subgroup.mem_subgroupOf.mpr b.1.property⟩
        left_inv := fun y => Subtype.ext (Subtype.ext rfl)
        right_inv := fun b => Subtype.ext (Subtype.ext rfl) }
    let e2 : {b : Bs // (b : G) ∈ L} ≃ {f : α // f i0 = 1} :=
      { toFun := fun b => ⟨eta b.1, (hBsL b.1).mp b.2⟩
        invFun := fun f => ⟨eta.symm f.1, (hBsL (eta.symm f.1)).mpr (by
          rw [eta.apply_symm_apply]
          exact f.2)⟩
        left_inv := fun b => by
          apply Subtype.ext
          exact eta.symm_apply_apply b.1
        right_inv := fun f => by
          apply Subtype.ext
          exact eta.apply_symm_apply f.1 }
    exact (Nat.card_congr e1).trans (Nat.card_congr e2)
  have hcard_fiber : Nat.card {f : α // f i0 = 1} = 3 ^ (n - 1) := by
    let e3 : {f : α // f i0 = 1} ≃ ({i : Fin n // i ≠ i0} → Multiplicative (ZMod 3)) :=
      { toFun := fun f i => f.1 i.1
        invFun := fun g => ⟨fun i => if h : i = i0 then 1 else g ⟨i, h⟩, by simp⟩
        left_inv := fun f => by
          apply Subtype.ext
          funext i
          by_cases h : i = i0
          · subst h
            simp [f.2]
          · simp [h]
        right_inv := fun g => by
          funext i
          simp [i.2] }
    have hα : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
      exact ZMod.card 3
    have hsub : Nat.card {i : Fin n // i ≠ i0} = n - 1 := by
      rw [Nat.card_eq_fintype_card]
      have h := Fintype.card_subtype_compl (fun i : Fin n => i = i0)
      rw [Fintype.card_fin, Fintype.card_subtype_eq i0] at h
      exact h
    calc
      Nat.card {f : α // f i0 = 1} =
          Nat.card ({i : Fin n // i ≠ i0} → Multiplicative (ZMod 3)) :=
        Nat.card_congr e3
      _ = Nat.card (Multiplicative (ZMod 3)) ^ Nat.card {i : Fin n // i ≠ i0} := Nat.card_fun
      _ = 3 ^ (n - 1) := by rw [hα, hsub]
  have hself : ∀ g ∈ Subgroup.centralizer (Bs.subgroupOf L : Set ↥L), g ^ 3 = 1 →
      g ∈ Bs.subgroupOf L := by
    intro g hg hg3
    have hcentral : (g : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hbcomm : Commute (g : G) ((⟨b, hb⟩ : Bs) : G) := by
        let c : Multiplicative (ZMod 3) := eta ⟨x, hx⟩ i0
        let d : Multiplicative (ZMod 3) := eta (⟨b, hb⟩ : Bs) i0
        have hc : c ≠ 1 := by
          intro h
          exact hxL ((hBsL ⟨x, hx⟩).mpr h)
        obtain ⟨j, hj⟩ := hj_exists c d hc
        let xt : Bs := ⟨x, hx⟩
        let y : Bs := ⟨b, hb⟩ * (xt ^ (j : ℕ))⁻¹
        have hycoord : eta y i0 = 1 := by
          have h1 : eta y = eta ⟨b, hb⟩ * (eta xt ^ (j : ℕ))⁻¹ := by
            dsimp only [y]
            rw [map_mul, map_inv, map_pow]
          rw [h1]
          simp only [Pi.mul_apply, Pi.inv_apply]
          have hxt : (eta xt ^ (j : ℕ)) i0 = c ^ (j : ℕ) := by
            simp [xt, c]
          rw [hxt, hj]
          exact mul_inv_cancel _
        have hyL : (y : G) ∈ L := (hBsL y).mpr hycoord
        have hgy : Commute (g : G) (y : G) := by
          rw [commute_iff_eq]
          have hmem : (⟨(y : G), hyL⟩ : ↥L) ∈ Bs.subgroupOf L :=
            Subgroup.mem_subgroupOf.mpr y.property
          have h := (Subgroup.mem_centralizer_iff.mp hg) ⟨(y : G), hyL⟩ hmem
          have h' := congrArg (fun z : ↥L => (z : G)) h
          exact h'.symm
        have hxg : Commute (g : G) x :=
          Subgroup.mem_centralizer_singleton_iff.mp (hLx g.property)
        have hb_eq : (y : G) * (x : G) ^ (j : ℕ) = ((⟨b, hb⟩ : Bs) : G) := by
          have h : y * xt ^ (j : ℕ) = ⟨b, hb⟩ := by
            simp only [y, mul_assoc, inv_mul_cancel, mul_one]
          exact congrArg (fun z : Bs => (z : G)) h
        rw [← hb_eq]
        exact Commute.mul_right hgy (hxg.pow_right (j : ℕ))
      simpa using Commute.eq hbcomm.symm
    have hg3G : (g : G) ^ 3 = 1 := by
      have h := congrArg (fun z : ↥L => (z : G)) hg3
      simpa using h
    exact Subgroup.mem_subgroupOf.mpr (hstar (g : G) hcentral hg3G)
  refine ⟨⟨hsquare, ?_⟩, ?_, ?_⟩
  · intro a ha
    simpa using hcube ⟨a, ha⟩
  · exact hcard_sub.trans hcard_fiber
  · exact hself

theorem card_normFrame_torus {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {A : Subgroup ↥(orthDerived Q)} {k : ℕ} {M : Type} [Field M]
    [Finite M] [Algebra F M] {U : Type} [AddCommGroup U] [Module F U]
    (Φ : ((Fin k → M) × U) ≃ₗ[F] V) (hM : Nat.card M = 4)
    (hdiag : ∀ e ∈ A, ∃ a : Fin k → M, (∀ i, a i ^ 3 = 1) ∧
      ∀ d w, (e : V ≃ₗ[F] V) (Φ (d, w)) = Φ (fun i => a i * d i, w))
    (hfull : ∀ a : Fin k → M, (∀ i, a i ^ 3 = 1) → ∃ e ∈ A,
      ∀ d w, (e : V ≃ₗ[F] V) (Φ (d, w)) = Φ (fun i => a i * d i, w)) :
    Nat.card A = 3 ^ k := by
  classical
  let _ : Fintype M := Fintype.ofFinite M
  have hroot : Nat.card {y : M // y ^ 3 = 1} = 3 := by
    let e : {y : M // y ^ 3 = 1} ≃ Mˣ :=
      { toFun := fun y => Units.mk0 y.1 (by
          rintro h
          have hy := y.2
          rw [h] at hy
          simp at hy)
        invFun := fun u => ⟨(u : M), by
          have h := FiniteField.pow_card_sub_one_eq_one (u : M) (Units.ne_zero u)
          rw [← Nat.card_eq_fintype_card, hM] at h
          norm_num at h
          exact h⟩
        left_inv := fun y => Subtype.ext rfl
        right_inv := fun u => Units.ext rfl }
    calc
      Nat.card {y : M // y ^ 3 = 1} = Nat.card Mˣ := Nat.card_congr e
      _ = 3 := by
        rw [Nat.card_units, hM]
  let aOf : A → (Fin k → M) := fun e => Classical.choose (hdiag e e.property)
  have aOf_spec : ∀ e : A, (∀ i, aOf e i ^ 3 = 1) ∧
      ∀ d w, (e : V ≃ₗ[F] V) (Φ (d, w)) = Φ (fun i => aOf e i * d i, w) :=
    fun e => Classical.choose_spec (hdiag e e.property)
  have aOf_unique : ∀ (e : A) (a : Fin k → M),
      (∀ d w, (e : V ≃ₗ[F] V) (Φ (d, w)) = Φ (fun i => a i * d i, w)) → a = aOf e := by
    intro e a ha
    funext i
    have h1 := ha (Pi.single i 1) 0
    have h2 := (aOf_spec e).2 (Pi.single i 1) 0
    have hp := Φ.injective (h1.symm.trans h2)
    have hi := congrFun (congrArg Prod.fst hp) i
    simpa using hi
  let f : A → {a : Fin k → M // ∀ i, a i ^ 3 = 1} :=
    fun e => ⟨aOf e, (aOf_spec e).1⟩
  have hf_inj : Function.Injective f := by
    intro e1 e2 h
    have h' : aOf e1 = aOf e2 := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨p, hp⟩ := Φ.surjective v
    obtain ⟨d, w⟩ := p
    rw [← hp, (aOf_spec e1).2 d w, (aOf_spec e2).2 d w, h']
  have hf_surj : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨e, heA, he⟩ := hfull a ha
    refine ⟨⟨e, heA⟩, ?_⟩
    apply Subtype.ext
    exact (aOf_unique ⟨e, heA⟩ a he).symm
  have hcardA : Nat.card A = Nat.card {a : Fin k → M // ∀ i, a i ^ 3 = 1} :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hcount : Nat.card {a : Fin k → M // ∀ i, a i ^ 3 = 1} = 3 ^ k := by
    have hprod : Nat.card {a : Fin k → M // ∀ i, a i ^ 3 = 1} =
        ∏ _i : Fin k, Nat.card {y : M // y ^ 3 = 1} := by
      calc
        Nat.card {a : Fin k → M // ∀ i, a i ^ 3 = 1} =
            Nat.card (∀ _i : Fin k, {y : M // y ^ 3 = 1}) :=
          Nat.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin k => M)
            (p := fun _ y => y ^ 3 = 1))
        _ = ∏ _i : Fin k, Nat.card {y : M // y ^ 3 = 1} := Nat.card_pi
    calc
      Nat.card {a : Fin k → M // ∀ i, a i ^ 3 = 1} =
          ∏ _i : Fin k, Nat.card {y : M // y ^ 3 = 1} := hprod
      _ = ∏ _i : Fin k, 3 := Finset.prod_congr rfl (fun _ _ => hroot)
      _ = 3 ^ k := Fin.prod_const k 3
  exact hcardA.trans hcount

theorem finrank_normFrame {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {k : ℕ} {M : Type} [Field M] [Finite M]
    [Algebra F M] {U : Type} [AddCommGroup U] [Module F U] (Φ : ((Fin k → M) × U) ≃ₗ[F] V)
    (hM : Nat.card M = 4) :
    Module.finrank F V = 2 * k + Module.finrank F U := by
  classical
  have hdimM : Module.finrank F M = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := M)
    rw [hM, hF] at h
    have h' : 2 ^ Module.finrank F M = 2 ^ 2 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective (by norm_num) h'
  have hU : FiniteDimensional F U :=
    FiniteDimensional.of_injective
      (Φ.toLinearMap.comp (LinearMap.inr F (Fin k → M) U)) (by
        intro u v h
        have h' : Φ ((0 : Fin k → M), u) = Φ ((0 : Fin k → M), v) := h
        have h'' := Φ.injective h'
        simpa using h'')
  have hk : Module.finrank F (Fin k → M) = k * 2 := by
    rw [Module.finrank_pi_fintype]
    simp [hdimM]
  calc
    Module.finrank F V = Module.finrank F ((Fin k → M) × U) := (LinearEquiv.finrank_eq Φ).symm
    _ = Module.finrank F (Fin k → M) + Module.finrank F U := Module.finrank_prod
    _ = 2 * k + Module.finrank F U := by rw [hk, Nat.mul_comm k 2]

end CFSG.StandardType.OrthAnchor

end
