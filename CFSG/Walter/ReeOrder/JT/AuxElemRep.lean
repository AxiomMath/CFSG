module

public import CFSG.Walter.ReeOrder.JT.AuxWeights
public import CFSG.Walter.ReeOrder.JT.AuxGroup

public section

namespace CFSG.Walter.JT

open Module
open scoped TensorProduct IsMulCommutative

theorem forall_mul_comm_of_forall_normal {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P)
    (h : ∀ B : Subgroup P, B.Normal → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      B ≤ Subgroup.center P) :
    ∀ a b : P, a * b = b * a := by
  classical
  set S : Set (Subgroup P) := {B | B.Normal ∧ ∀ a ∈ B, ∀ b ∈ B, a * b = b * a} with hS
  have hbot : (⊥ : Subgroup P) ∈ S := ⟨inferInstance, by simp⟩
  obtain ⟨B, ⟨hBn, hBc⟩, hBmax⟩ := (Set.toFinite S).exists_maximal ⟨⊥, hbot⟩
  have hBZ := h B hBn hBc
  have hBtop : B = ⊤ := by
    by_contra hBt
    have hQ : IsPGroup p (P ⧸ B) := hP.to_quotient B
    have : Nontrivial (P ⧸ B) := QuotientGroup.nontrivial_iff.mpr hBt
    have := hQ.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (P ⧸ B))
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (z : P ⧸ B)
    set C : Subgroup P := (Subgroup.zpowers (z : P ⧸ B)).comap (QuotientGroup.mk' B)
    have hzZ : Subgroup.zpowers (z : P ⧸ B) ≤ Subgroup.center (P ⧸ B) :=
      (Subgroup.zpowers_le).mpr z.2
    have hCn : C.Normal := (Subgroup.normal_of_le_center hzZ).comap _
    have hBC : B ≤ C := fun b hb => by
      change (QuotientGroup.mk' B b) ∈ Subgroup.zpowers (z : P ⧸ B)
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff b).mpr hb]
      exact Subgroup.one_mem _
    have hdecomp : ∀ a ∈ C, ∃ i : ℤ, ∃ β ∈ B, a = x ^ i * β := by
      intro a ha
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
      refine ⟨i, (x ^ i)⁻¹ * a, ?_, by group⟩
      rw [← QuotientGroup.eq]
      change QuotientGroup.mk (x ^ i) = QuotientGroup.mk' B a
      rw [← hi, QuotientGroup.mk_zpow, hx]
    have hcen : ∀ β ∈ B, ∀ y : P, β * y = y * β := fun β hβ y =>
      (Subgroup.mem_center_iff.mp (hBZ hβ) y).symm
    have hCc : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, β, hβ, rfl⟩ := hdecomp a ha
      obtain ⟨j, γ, hγ, rfl⟩ := hdecomp b hb
      have hxx : x ^ i * x ^ j = x ^ j * x ^ i := (Commute.zpow_zpow_self x i j).eq
      calc x ^ i * β * (x ^ j * γ) = x ^ i * (β * x ^ j) * γ := by group
        _ = x ^ i * (x ^ j * β) * γ := by rw [hcen β hβ]
        _ = (x ^ i * x ^ j) * (β * γ) := by group
        _ = (x ^ j * x ^ i) * (γ * β) := by rw [hxx, hcen β hβ γ]
        _ = x ^ j * (x ^ i * γ) * β := by group
        _ = x ^ j * (γ * x ^ i) * β := by rw [hcen γ hγ]
        _ = x ^ j * γ * (x ^ i * β) := by group
    have hCB : C ≤ B := hBmax ⟨hCn, hCc⟩ hBC
    have hxC : x ∈ C := by
      change QuotientGroup.mk' B x ∈ Subgroup.zpowers (z : P ⧸ B)
      rw [QuotientGroup.mk'_apply, hx]
      exact Subgroup.mem_zpowers _
    apply hz
    apply Subtype.ext
    rw [← hx, Subgroup.coe_one, QuotientGroup.eq_one_iff]
    exact hCB hxC
  intro a b
  exact Subgroup.mem_center_iff.mp (hBZ (hBtop ▸ Subgroup.mem_top b)) a

section BaseChange

variable {F K V : Type*} [Field F] [Field K] [Algebra F K] [AddCommGroup V] [Module F V]

theorem baseChange_injective {f g : V →ₗ[F] V} (h : f.baseChange K = g.baseChange K) :
    f = g := by
  ext v
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := F) (B := K) (M := V)
  have := DFunLike.congr_fun h (1 ⊗ₜ v)
  simpa using this

end BaseChange

@[expose] noncomputable def autRep (p : ℕ) [Fact p.Prime] (A : Type*) [Group A]
    [IsElementaryAbelian p A] :
    Representation (AlgebraicClosure (ZMod p)) (MulAut A)
      (AlgebraicClosure (ZMod p) ⊗[ZMod p] Additive A) :=
  Theory.Representation.extendScalars (AlgebraicClosure (ZMod p))
    (Theory.Representation.ofElementaryAbelianAction (A := MulAut A) (G := A) (p := p))

variable {A : Type*} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime] [IsElementaryAbelian p A]

omit [Finite A] in
theorem autRep_injective : Function.Injective (autRep p A) := by
  intro f g hfg
  have h1 : Theory.Representation.ofElementaryAbelianAction (A := MulAut A) (G := A) (p := p) f =
      Theory.Representation.ofElementaryAbelianAction (A := MulAut A) (G := A) (p := p) g :=
    baseChange_injective (K := AlgebraicClosure (ZMod p)) hfg
  ext a
  have h2 := congrArg Additive.toMul (DFunLike.congr_fun h1 (Additive.ofMul a))
  simpa using h2

theorem finrank_autRep_le (ha : Nat.card A ≤ p ^ 3) :
    finrank (AlgebraicClosure (ZMod p)) (AlgebraicClosure (ZMod p) ⊗[ZMod p] Additive A) ≤ 3 := by
  rw [Module.finrank_baseChange]
  have h := FiniteField.pow_finrank_eq_natCard p (Additive A)
  have h2 : Nat.card (Additive A) = Nat.card A := rfl
  rw [h2] at h
  rw [← h] at ha
  exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp ha

omit [Finite A] [IsElementaryAbelian p A] in
private theorem cast_card_ne_zero {N : Subgroup (MulAut A)} (hNp : ¬ p ∣ Nat.card N) :
    ((Nat.card N : ℕ) : AlgebraicClosure (ZMod p)) ≠ 0 := by
  rwa [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]

omit [Finite A] in
private theorem autRep_comm {N : Subgroup (MulAut A)} (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) :
    ∀ a ∈ N, ∀ b ∈ N, autRep p A a * autRep p A b = autRep p A b * autRep p A a := by
  intro a ha b hb
  rw [← map_mul, ← map_mul, hN a ha b hb]

theorem sq_or_cube_of_mem_normalizer (hAcard : Nat.card A ≤ p ^ 3) {N : Subgroup (MulAut A)}
    (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNp : ¬ p ∣ Nat.card N) {g : MulAut A}
    (hg : g ∈ Subgroup.normalizer (N : Set (MulAut A))) :
    (∀ n ∈ N, g ^ 2 * n * (g ^ 2)⁻¹ = n) ∨ (∀ n ∈ N, g ^ 3 * n * (g ^ 3)⁻¹ = n) := by
  rcases map_conj_sq_or_cube (autRep p A) N (autRep_comm hN) (cast_card_ne_zero hNp)
    (finrank_autRep_le hAcard) hg with h | h
  · exact Or.inl fun n hn => autRep_injective (h n hn)
  · exact Or.inr fun n hn => autRep_injective (h n hn)

theorem commute_of_coprime_six (hAcard : Nat.card A ≤ p ^ 3) {N : Subgroup (MulAut A)}
    (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNp : ¬ p ∣ Nat.card N) {g : MulAut A}
    (hg : g ∈ Subgroup.normalizer (N : Set (MulAut A))) (hcop : Nat.Coprime (orderOf g) 6) :
    ∀ n ∈ N, g * n * g⁻¹ = n := fun n hn =>
  autRep_injective (map_conj_eq_of_coprime_six (autRep p A) N (autRep_comm hN)
    (cast_card_ne_zero hNp) (finrank_autRep_le hAcard) hg hcop n hn)

theorem commute_of_isPGroup (hAcard : Nat.card A ≤ p ^ 3) {N : Subgroup (MulAut A)}
    (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNp : ¬ p ∣ Nat.card N) {r : ℕ} (hr : r.Prime)
    (hr3 : 3 < r) {R : Subgroup (MulAut A)} (hR : IsPGroup r R)
    (hRN : R ≤ Subgroup.normalizer (N : Set (MulAut A))) :
    ∀ g ∈ R, ∀ n ∈ N, g * n * g⁻¹ = n := fun g hg n hn =>
  autRep_injective (map_conj_eq_of_isPGroup (autRep p A) N (autRep_comm hN)
    (cast_card_ne_zero hNp) hr ((finrank_autRep_le hAcard).trans_lt hr3) hR hRN g hg n hn)

theorem mul_comm_of_isPGroup (hAcard : Nat.card A ≤ p ^ 3) {r : ℕ} [hr : Fact r.Prime]
    (hr3 : 3 < r) (hrp : r ≠ p) {R : Subgroup (MulAut A)} (hR : IsPGroup r R) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  have key := forall_mul_comm_of_forall_normal hR fun B hBn hBc => by
    set B' : Subgroup (MulAut A) := B.map R.subtype
    have hB'c : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hBc a ha b hb)
    have hB'p : ¬ p ∣ Nat.card B' := by
      rw [Subgroup.card_map_of_injective R.subtype_injective]
      intro hdvd
      obtain ⟨k, hk⟩ := (hR.to_subgroup B).exists_card_eq
      rw [hk] at hdvd
      exact hrp ((Nat.prime_dvd_prime_iff_eq hp.out hr.out).mp
        (hp.out.dvd_of_dvd_pow hdvd)).symm
    have hRB' : R ≤ Subgroup.normalizer (B' : Set (MulAut A)) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨g, hg⟩ * b * ⟨g, hg⟩⁻¹, hBn.conj_mem b hb _, rfl⟩
      · rintro ⟨b, hb, hbx⟩
        refine ⟨⟨g, hg⟩⁻¹ * b * ⟨g, hg⟩, ?_, ?_⟩
        · simpa using hBn.conj_mem b hb ⟨g, hg⟩⁻¹
        · simp only [Subgroup.coe_subtype] at hbx ⊢
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hbx]
          group
    have hcomm := commute_of_isPGroup hAcard hB'c hB'p hr.out hr3 hR hRB'
    intro b hb
    rw [Subgroup.mem_center_iff]
    intro g
    have := hcomm g g.2 b ⟨b, hb, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul] at this ⊢
    calc (g : MulAut A) * b = (g * b * (g : MulAut A)⁻¹) * g := by group
      _ = b * g := by rw [this]
  intro a ha b hb
  exact congrArg Subtype.val (key ⟨a, ha⟩ ⟨b, hb⟩)


section Section

variable {A : Type*} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime] [IsElementaryAbelian p A]

theorem conj_pow_mul_of_comm {Y : Type*} [Group Y] {E : Subgroup Y}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {d e : Y}
    (hd : d ∈ Subgroup.normalizer (E : Set Y)) (he : e ∈ E) (k : ℕ) :
    ∀ x ∈ E, (e * d) ^ k * x * ((e * d) ^ k)⁻¹ = d ^ k * x * (d ^ k)⁻¹ := by
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have hdx : d * x * d⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hd x).mp hx
    have hdkx : d ^ k * x * (d ^ k)⁻¹ ∈ E := by
      have := Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hd k) x
      exact this.mp hx
    have hm : d * (d ^ k * x * (d ^ k)⁻¹) * d⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp hd _).mp hdkx
    have e1 : (e * d) ^ (k + 1) * x * ((e * d) ^ (k + 1))⁻¹ =
        e * (d * ((e * d) ^ k * x * ((e * d) ^ k)⁻¹) * d⁻¹) * e⁻¹ := by
      rw [pow_succ', mul_inv_rev, mul_inv_rev]
      simp only [mul_assoc]
    have e2 : d ^ (k + 1) * x * (d ^ (k + 1))⁻¹ = d * (d ^ k * x * (d ^ k)⁻¹) * d⁻¹ := by
      rw [pow_succ']
      group
    rw [e1, e2, ih x hx, hEc e he _ hm, mul_inv_cancel_right]

theorem exists_nonabelian_of_sq_cube (hA : Nat.card A ≤ p ^ 3) {X : Subgroup (MulAut A)}
    {Y : Type*} [Group Y] (π : X →* Y) {s : ℕ} [hs : Fact s.Prime] (hsp : s ≠ p)
    {E : Subgroup Y} (hE : IsPGroup s E) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hEπ : E ≤ π.range) {d : Y} (hdπ : d ∈ π.range)
    (hdE : d ∈ Subgroup.normalizer (E : Set Y)) {x : Y} (hxE : x ∈ E)
    (h2 : d ^ 2 * x * (d ^ 2)⁻¹ ≠ x) (h3 : d ^ 3 * x * (d ^ 3)⁻¹ ≠ x) :
    ∃ R : Subgroup X, IsPGroup s R ∧ R ≤ E.comap π ∧ ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a := by
  classical
  by_contra! hab
  set Et : Subgroup X := E.comap π with hEt
  obtain ⟨P₀⟩ : Nonempty (Sylow s Et) := inferInstance
  set P : Subgroup X := (P₀ : Subgroup Et).map Et.subtype with hP
  have hPEt : P ≤ Et := Subgroup.map_subtype_le _
  have hPs : IsPGroup s P := P₀.isPGroup'.map _
  have hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := hab P hPs hPEt
  let πE : Et →* E := (π.comp Et.subtype).codRestrict E fun y => y.2
  have hπE : Function.Surjective πE := by
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hEπ hy
    exact ⟨⟨z, hy⟩, rfl⟩
  have hPmap : x ∈ P.map π := by
    let Q := Sylow.mapSurjective hπE P₀
    have hQ : (Q : Subgroup E) = ⊤ := (Q.is_maximal' (hE.to_subgroup ⊤) le_top).symm
    have hxQ : (⟨x, hxE⟩ : E) ∈ (Q : Subgroup E) := hQ ▸ Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hxQ
    obtain ⟨z, hz, hzx⟩ := hxQ
    exact ⟨z, ⟨z, hz, rfl⟩, congrArg Subtype.val hzx⟩
  obtain ⟨z, hzP, rfl⟩ := hPmap
  obtain ⟨d₀, rfl⟩ := hdπ
  have hd₀Et : d₀ ∈ Subgroup.normalizer (Et : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    simp only [hEt, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hdE (π w)
  obtain ⟨y, hy, hyd⟩ := exists_mul_mem_normalizer_of_sylow P₀ hd₀Et
  set P' : Subgroup (MulAut A) := P.map X.subtype
  have hP'c : ∀ a ∈ P', ∀ b ∈ P', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hPc a ha b hb)
  have hP'p : ¬ p ∣ Nat.card P' := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    intro hdvd
    obtain ⟨k, hk⟩ := hPs.exists_card_eq
    rw [hk] at hdvd
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp.out hs.out).mp
      (hp.out.dvd_of_dvd_pow hdvd)).symm
  have hgN : ((y * d₀ : X) : MulAut A) ∈ Subgroup.normalizer (P' : Set (MulAut A)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, (Subgroup.mem_normalizer_iff.mp hyd a).mp ha, by simp⟩
    · rintro ⟨b, hb, hbw⟩
      have hw : w ∈ X := by
        have : w = ((y * d₀ : X) : MulAut A)⁻¹ * (b : MulAut A) * ((y * d₀ : X) : MulAut A) := by
          rw [Subgroup.coe_subtype] at hbw
          rw [hbw]
          group
        rw [this]
        exact X.mul_mem (X.mul_mem (X.inv_mem (y * d₀).2) b.2) (y * d₀).2
      refine ⟨⟨w, hw⟩, (Subgroup.mem_normalizer_iff.mp hyd ⟨w, hw⟩).mpr ?_, rfl⟩
      have : (y * d₀) * ⟨w, hw⟩ * (y * d₀)⁻¹ = b := by
        apply Subtype.ext
        rw [Subgroup.coe_subtype] at hbw
        rw [hbw]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [this]
      exact hb
  have key := sq_or_cube_of_mem_normalizer hA hP'c hP'p hgN
  have hyE : π y ∈ E := hy
  have hconj := conj_pow_mul_of_comm hEc hdE hyE
  rcases key with hk | hk
  · apply h2
    have h1 := hk z ⟨z, hzP, rfl⟩
    have h1' : (y * d₀) ^ 2 * z * ((y * d₀) ^ 2)⁻¹ = z := by
      apply Subtype.ext
      simpa using h1
    rw [← hconj 2 (π z) (hPEt hzP), ← map_mul, ← map_pow, ← map_mul, ← map_inv, ← map_mul, h1']
  · apply h3
    have h1 := hk z ⟨z, hzP, rfl⟩
    have h1' : (y * d₀) ^ 3 * z * ((y * d₀) ^ 3)⁻¹ = z := by
      apply Subtype.ext
      simpa using h1
    rw [← hconj 3 (π z) (hPEt hzP), ← map_mul, ← map_pow, ← map_mul, ← map_inv, ← map_mul, h1']

end Section

end CFSG.Walter.JT
