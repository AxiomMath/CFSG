module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res5ProofDefs
public import CFSG.RankThree.PartTwo.Sec21.Item224Res5ProofLift
public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.LieType.CurtisTits.Recognition
public import CFSG.RankThree.PartTwo.Sec21.Implications

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem thetaQuotMulAut_normalizerMonoidHom_of_mem {L : Subgroup G} {l : G} (hl : l ∈ L) :
    Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨l, L.le_normalizer hl⟩) =
      MulAut.conj ((⟨l, hl⟩ : L) : lBar L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

theorem autThetaQuot_mono {H K L : Subgroup G} (hHK : H ≤ K) :
    Sec4.autThetaQuot H L ≤ Sec4.autThetaQuot K L := by
  intro τ hτ
  obtain ⟨h, hN, hH, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
  exact Sec4.mem_autThetaQuot_iff.mpr ⟨h, hN, hHK hH, rfl⟩

theorem isPGroup_autThetaQuot {p : ℕ} {H : Subgroup G} (L : Subgroup G) (hH : IsPGroup p H) :
    IsPGroup p (Sec4.autThetaQuot H L) :=
  (((hH.to_le inf_le_left).comap_subtype).map _).map _

theorem mem_normalizer_autThetaQuot {H L : Subgroup G} {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgH : g ∈ Subgroup.normalizer (H : Set G)) :
    Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hgL⟩) ∈
      Subgroup.normalizer (Sec4.autThetaQuot H L : Set (MulAut (lBar L))) := by
  set φ := (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
  have key : ∀ k : Subgroup.normalizer (L : Set G),
      (k : G) ∈ Subgroup.normalizer (H : Set G) → ∀ τ ∈ Sec4.autThetaQuot H L,
        φ k * τ * (φ k)⁻¹ ∈ Sec4.autThetaQuot H L := by
    intro k hk τ hτ
    obtain ⟨h, hN, hH, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    have hkh : (k : G) * h * (k : G)⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hk h).mp hH
    refine Sec4.mem_autThetaQuot_iff.mpr ⟨(k : G) * h * (k : G)⁻¹,
      ((Subgroup.normalizer (L : Set G)).mul_mem ((Subgroup.normalizer (L : Set G)).mul_mem k.2 hN)
        ((Subgroup.normalizer (L : Set G)).inv_mem k.2)), hkh, ?_⟩
    change φ ⟨(k : G) * h * (k : G)⁻¹, _⟩ = φ k * φ ⟨h, hN⟩ * (φ k)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [Subgroup.mem_normalizer_iff]
  intro τ
  constructor
  · exact key ⟨g, hgL⟩ hgH τ
  · intro hτ
    have hτ' : φ ⟨g, hgL⟩ * τ * (φ ⟨g, hgL⟩)⁻¹ ∈ Sec4.autThetaQuot H L := hτ
    have h := key ⟨g, hgL⟩⁻¹ (Subgroup.inv_mem _ hgH) _ hτ'
    have e : φ (⟨g, hgL⟩⁻¹) * (φ ⟨g, hgL⟩ * τ * (φ ⟨g, hgL⟩)⁻¹) * (φ (⟨g, hgL⟩⁻¹))⁻¹ = τ := by
      rw [map_inv]
      group
    rwa [e] at h

theorem exists_centralizer_lift_of_odd {L T : Subgroup G} (hLq : IsQuasisimple L)
    (hT2 : IsPGroup 2 T) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {x : lBar L}
    (hx : Odd (orderOf x)) (hfix : ∀ τ ∈ Sec4.autThetaQuot T L, τ x = x) :
    ∃ l : L, (l : G) ∈ Subgroup.centralizer (T : Set G) ∧ (l : lBar L) = x := by
  set ψ : T →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hTL) with hψ
  obtain ⟨l, hlx, hl⟩ := exists_fixed_lift_of_odd (aschbacherSolvableCore 3 L)
    (aschbacherSolvableCore_le_center hLq) hT2 ψ x hx (by
      intro t y hy
      have hτ : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨t, hTL t.2⟩) ∈
          Sec4.autThetaQuot T L := Sec4.mem_autThetaQuot_iff.mpr ⟨t, hTL t.2, t.2, rfl⟩
      have h := hfix _ hτ
      rw [← hy] at h ⊢
      exact h)
  refine ⟨l, ?_, hlx⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h := congrArg Subtype.val (hl ⟨t, ht⟩)
  change t * (l : G) * t⁻¹ = l at h
  calc t * (l : G) = (t * l * t⁻¹) * t := by group
    _ = l * t := by rw [h]

theorem exists_lift_pow_three {L B : Subgroup G} (hLq : IsQuasisimple L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) {x : lBar L} (hx : x ^ 3 = 1)
    (hfix : ∀ τ ∈ Sec4.autThetaQuot B L, τ x = x) :
    ∃ l : L, (l : G) ∈ Subgroup.centralizer (B : Set G) ∧ (l : lBar L) = x ∧ l ^ 3 = 1 := by
  set ψ : B →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBL) with hψ
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  obtain ⟨l, hlx, hl3, hl⟩ := exists_fixed_lift_of_three (aschbacherSolvableCore 3 L)
    (aschbacherSolvableCore_le_center hLq) hθ3 ψ x hx (by
      intro t y hy
      have hτ : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨t, hBL t.2⟩) ∈
          Sec4.autThetaQuot B L := Sec4.mem_autThetaQuot_iff.mpr ⟨t, hBL t.2, t.2, rfl⟩
      have h := hfix _ hτ
      rw [← hy] at h ⊢
      exact h)
  refine ⟨l, ?_, hlx, hl3⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h := congrArg Subtype.val (hl ⟨t, ht⟩)
  change t * (l : G) * t⁻¹ = l at h
  calc t * (l : G) = (t * l * t⁻¹) * t := by group
    _ = l * t := by rw [h]

theorem oddFixed_bot_eq_top {X : Type*} [Group X] [Finite X] (hX : Group.IsPerfect X) :
    oddFixed X ⊥ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : ∀ x : X, ∀ t ∈ (⊥ : Subgroup (MulAut X)), t x = x := by
    intro x t ht
    rw [Subgroup.mem_bot.mp ht]
    rfl
  have hK : (oddFixed X ⊥).Normal := by
    constructor
    intro n hn g
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨hbot _, ?_⟩
      have h := (MulAut.conj g).orderOf_eq x
      rw [MulAut.conj_apply] at h
      rw [h]
      exact hx.2
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have h2 : IsPGroup 2 (X ⧸ oddFixed X ⊥) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine Subgroup.subset_closure ⟨hbot _, ?_⟩
    have h1 : (x ^ 2 ^ a) ^ b = 1 := by rw [← pow_mul, ← hab, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat hb (orderOf_dvd_of_pow_eq_one h1)
  have : Group.IsNilpotent (X ⧸ oddFixed X ⊥) := h2.isNilpotent
  have : Group.IsPerfect (X ⧸ oddFixed X ⊥) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (oddFixed X ⊥))
      (QuotientGroup.mk'_surjective _)
  have hsub : Subsingleton (X ⧸ oddFixed X ⊥) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable (X ⧸ oddFixed X ⊥) inferInstance
  rw [eq_top_iff]
  intro x _
  rw [← QuotientGroup.eq_one_iff]
  exact Subsingleton.elim _ _

theorem autElliptic_bot {X : Type*} [Group X] [Finite X] (hX : IsQuasisimple X) :
    AutElliptic X ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect X := hX.1
  intro P hP2 hPN
  rw [oddFixed_bot_eq_top hperf] at hPN ⊢
  have hN : ∀ x : X, MulAut.conj x ∈ Subgroup.normalizer (P : Set (MulAut X)) :=
    fun x => hPN ⟨x, Subgroup.mem_top x, rfl⟩
  set Q : Subgroup X := P.comap MulAut.conj with hQ
  have hQn : Q.Normal := by
    constructor
    intro n hn g
    change MulAut.conj (g * n * g⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hN g) _).mp hn
  have hQZ : Q ≤ Subgroup.center X := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hX Q with h | h
    · exact h
    · exfalso
      obtain ⟨-, hsimple, a, b, hab⟩ := hX
      have : Nontrivial (X ⧸ Subgroup.center X) := ⟨⟨a * b, b * a, hab⟩⟩
      have h2 : IsPGroup 2 (X ⧸ Subgroup.center X) := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        have hxQ : x ∈ Q := h ▸ Subgroup.mem_top x
        obtain ⟨k, hk⟩ := hP2 ⟨MulAut.conj x, hxQ⟩
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
        intro y
        have hk' : MulAut.conj (x ^ 2 ^ k) = 1 := by
          rw [map_pow]
          exact congrArg Subtype.val hk
        have hy := congrArg (fun σ : MulAut X => σ y) hk'
        simp only [MulAut.conj_apply, MulAut.one_apply] at hy
        calc y * x ^ 2 ^ k = (x ^ 2 ^ k * y * (x ^ 2 ^ k)⁻¹) * x ^ 2 ^ k := by rw [hy]
          _ = x ^ 2 ^ k * y := by group
      have : Group.IsNilpotent (X ⧸ Subgroup.center X) := h2.isNilpotent
      have : Group.IsPerfect (X ⧸ Subgroup.center X) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center X))
          (QuotientGroup.mk'_surjective _)
      exact Group.IsPerfect.not_isSolvable (X ⧸ Subgroup.center X) inferInstance
  have hcent : ∀ p ∈ P, ∀ x : X, x⁻¹ * p x ∈ Subgroup.center X := by
    intro p hp x
    apply hQZ
    change MulAut.conj (x⁻¹ * p x) ∈ P
    have e : MulAut.conj (x⁻¹ * p x) =
        (MulAut.conj x⁻¹ * p * (MulAut.conj x⁻¹)⁻¹) * p⁻¹ := by
      ext y
      simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
        inv_inv, MulEquiv.apply_symm_apply]
    rw [e]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN x⁻¹) p).mp hp) (P.inv_mem hp)
  have hp1 : ∀ p ∈ P, p = 1 := by
    intro p hp
    let f : X →* Subgroup.center X :=
      { toFun := fun x => ⟨x⁻¹ * p x, hcent p hp x⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          change (a * b)⁻¹ * p (a * b) = (a⁻¹ * p a) * (b⁻¹ * p b)
          have hc := Subgroup.mem_center_iff.mp (hcent p hp a) b⁻¹
          rw [map_mul, mul_inv_rev]
          calc b⁻¹ * a⁻¹ * (p a * p b) = (b⁻¹ * (a⁻¹ * p a)) * p b := by group
            _ = ((a⁻¹ * p a) * b⁻¹) * p b := by rw [hc]
            _ = (a⁻¹ * p a) * (b⁻¹ * p b) := by group }
    ext x
    have hx : x ∈ f.ker := Abelianization.commutator_subset_ker f
      (hperf.commutator_eq_top.symm ▸ Subgroup.mem_top x)
    rw [MonoidHom.mem_ker] at hx
    have h := congrArg Subtype.val hx
    change x⁻¹ * p x = 1 at h
    rw [inv_mul_eq_one] at h
    exact h.symm
  have hPbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr hp1
  subst hPbot
  refine ⟨fun p hp x _ => by rw [Subgroup.mem_bot.mp hp]; rfl, ?_⟩
  exact isCyclic_of_subsingleton

end CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
