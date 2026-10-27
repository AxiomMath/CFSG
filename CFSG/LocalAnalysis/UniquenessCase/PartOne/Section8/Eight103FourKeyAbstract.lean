module

public import CFSG.GroupTheory.SylowAutConj
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.ConjMulPowCyclic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

@[expose] def U45KeyDvdConcl (X : Type*) [Group X] (p : ℕ) : Prop :=
  ∀ R : Subgroup (MulAut X), IsElemAbelian p R →
    ∃ S : Subgroup X, IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧
      ∃ C : Subgroup (MulAut X), C ≤ R ∧ (∀ α ∈ C, ∀ s ∈ S, α s = s) ∧
        Nat.card R ≤ p ^ 2 * Nat.card C

theorem U45KeyDvdConcl.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : U45KeyDvdConcl Y p) : U45KeyDvdConcl X p := by
  intro R hR
  let f : MulAut X ≃* MulAut Y := MulAut.congr e
  obtain ⟨S', hS', hS'i, C', hC', hfix', hcard'⟩ := h (R.map f.toMonoidHom) (hR.map _)
  refine ⟨S'.map e.symm.toMonoidHom, hS'.map _, ?_, C'.map f.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rwa [Subgroup.index_map_of_bijective (f := e.symm.toMonoidHom) e.symm.bijective]
  · intro γ hγ
    obtain ⟨γ', hγ'C', rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨α, hαR, hαeq⟩ := Subgroup.mem_map.mp (hC' hγ'C')
    rw [← hαeq]
    simpa using hαR
  · intro γ hγ s hs
    obtain ⟨γ', hγ'C', rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨s', hs'S', rfl⟩ := Subgroup.mem_map.mp hs
    have hfs : (f.symm γ') (e.symm s') = e.symm (γ' s') := by
      simp [f, MulAut.congr_symm_apply]
    change (f.symm γ') (e.symm s') = e.symm s'
    rw [hfs, hfix' γ' hγ'C' s' hs'S']
  · rw [← Subgroup.card_map_of_injective (f := f.toMonoidHom) (K := R) f.injective,
      Subgroup.card_map_of_injective (f := f.symm.toMonoidHom) (K := C') f.symm.injective]
    exact hcard'

section

variable {X : Type*} [Group X]

private theorem inner_range_normal : ((MulAut.conj : X →* MulAut X).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨x, rfl⟩ := hn
  have hconj : g * MulAut.conj x * g⁻¹ = MulAut.conj (g x) := by
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [show g (g⁻¹ y) = y from MulEquiv.apply_symm_apply g y]
  exact ⟨g x, hconj.symm⟩

private theorem comap_conj_eq_of_conj
    {φ : MulAut X} {P₀ B₀ : Subgroup X} {R' R'' : Subgroup (MulAut X)} {y : X}
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X))
    (hφinn : ∀ k : ℕ, φ ^ k ∈ (MulAut.conj : X →* MulAut X).range → φ ^ k = 1)
    (hP₀c : ∀ a ∈ P₀, ∀ b ∈ P₀, a * b = b * a)
    (hR'el : ∀ δ ∈ R', ∃ s ∈ P₀, ∃ j : ℕ, δ = MulAut.conj s * φ ^ j)
    (hB₀def : B₀ = R'.comap (MulAut.conj : X →* MulAut X))
    (hB₀P : B₀ ≤ P₀) (hyP : y ∈ P₀)
    (hR''eq : R'' = R'.map (MulAut.conj (MulAut.conj y)).toMonoidHom) :
    R''.comap (MulAut.conj : X →* MulAut X) = B₀ := by
  rw [hB₀def]
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [Subgroup.mem_comap] at hz ⊢
    rw [hR''eq] at hz
    obtain ⟨ρ, hρR', hρeq⟩ := Subgroup.mem_map.mp hz
    have hρval : ρ = MulAut.conj (y⁻¹ * z * y) := by
      have h1 : (MulAut.conj y)⁻¹ = (MulAut.conj y⁻¹ : MulAut X) := (map_inv _ y).symm
      calc ρ = (MulAut.conj y)⁻¹ * ((MulAut.conj y) * ρ * (MulAut.conj y)⁻¹) *
            (MulAut.conj y) := by group
        _ = (MulAut.conj y)⁻¹ * MulAut.conj z * (MulAut.conj y) := by
            rw [show (MulAut.conj y) * ρ * (MulAut.conj y)⁻¹ = MulAut.conj z from hρeq]
        _ = MulAut.conj y⁻¹ * MulAut.conj z * MulAut.conj y := by rw [h1]
        _ = MulAut.conj (y⁻¹ * z * y) := by rw [← map_mul, ← map_mul]
    obtain ⟨s, hsP, j, hρel⟩ := hR'el ρ hρR'
    rw [hρval] at hρel
    have hφj_inner : φ ^ j ∈ (MulAut.conj : X →* MulAut X).range := by
      refine ⟨s⁻¹ * (y⁻¹ * z * y), ?_⟩
      rw [map_mul, map_inv, hρel]
      group
    have hφj : φ ^ j = 1 := hφinn j hφj_inner
    rw [hφj, mul_one] at hρel
    have hzy : y⁻¹ * z * y = s := hZ hρel
    have hzs : z = s := by
      calc z = y * (y⁻¹ * z * y) * y⁻¹ := by group
        _ = y * s * y⁻¹ := by rw [hzy]
        _ = s := by rw [hP₀c y hyP s hsP]; group
    rw [hzs, ← hρel, ← hρval]
    exact hρR'
  · intro z hz
    have hzB : z ∈ B₀ := by rwa [← hB₀def] at hz
    have hzP : z ∈ P₀ := hB₀P hzB
    rw [Subgroup.mem_comap] at hz ⊢
    rw [hR''eq]
    have himg : ((MulAut.conj (MulAut.conj y)).toMonoidHom) (MulAut.conj z) =
        MulAut.conj z := by
      change MulAut.conj y * MulAut.conj z * (MulAut.conj y)⁻¹ = MulAut.conj z
      rw [show (MulAut.conj y)⁻¹ = (MulAut.conj y⁻¹ : MulAut X) from (map_inv _ y).symm]
      rw [← map_mul, ← map_mul, hP₀c y hyP z hzP]
      group
    rw [← himg]
    exact Subgroup.mem_map_of_mem _ hz

private theorem transport_of_count {p : ℕ} [Fact p.Prime]
    {R : Subgroup (MulAut X)} {γ : MulAut X} {R'' : Subgroup (MulAut X)}
    (hR''def : R'' = R.map (MulAut.conj γ).toMonoidHom) {S₃ : Subgroup X}
    (hS₃ : IsPGroup 3 S₃) (hS₃i : ¬ 3 ∣ S₃.index)
    (hcard : Nat.card R'' ≤
      p ^ 2 * Nat.card ↥(R'' ⊓ fixingSubgroup (MulAut X) (S₃ : Set X))) :
    ∃ S : Subgroup X, IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧
      ∃ C : Subgroup (MulAut X), C ≤ R ∧ (∀ α ∈ C, ∀ s ∈ S, α s = s) ∧
        Nat.card R ≤ p ^ 2 * Nat.card C := by
  classical
  let C'' : Subgroup (MulAut X) := R'' ⊓ fixingSubgroup (MulAut X) (S₃ : Set X)
  let S : Subgroup X := S₃.map γ.symm.toMonoidHom
  let C : Subgroup (MulAut X) := C''.map (MulAut.conj γ⁻¹).toMonoidHom
  have hRcard : Nat.card R = Nat.card R'' := by
    rw [hR''def, Subgroup.card_map_of_injective (MulAut.conj γ).injective]
  have hCcard : Nat.card C = Nat.card C'' := by
    rw [Subgroup.card_map_of_injective (MulAut.conj γ⁻¹).injective]
  refine ⟨S, hS₃.map γ.symm.toMonoidHom, ?_, C, ?_, ?_, ?_⟩
  · rw [Subgroup.index_map_of_bijective (f := γ.symm.toMonoidHom) γ.symm.bijective]
    exact hS₃i
  · intro δ hδ
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hδ
    have hcR : c ∈ R'' := hc.1
    rw [hR''def] at hcR
    obtain ⟨α, hα, hαc⟩ := Subgroup.mem_map.mp hcR
    have hδeq : ((MulAut.conj γ⁻¹).toMonoidHom) c = α := by
      rw [← hαc]
      change (MulAut.conj γ⁻¹) ((MulAut.conj γ) α) = α
      rw [show MulAut.conj γ⁻¹ = (MulAut.conj γ)⁻¹ from map_inv _ γ]
      exact MulEquiv.symm_apply_apply (MulAut.conj γ) α
    rw [hδeq]
    exact hα
  · intro δ hδ s hs
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hδ
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    have hct : c t = t := (mem_fixingSubgroup_iff (MulAut X)).1 hc.2 t ht
    change (MulAut.conj γ⁻¹) c (γ.symm t) = γ.symm t
    rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
      inv_inv, MulEquiv.apply_symm_apply, hct]
  · calc Nat.card R = Nat.card R'' := hRcard
      _ ≤ p ^ 2 * Nat.card C'' := hcard
      _ = p ^ 2 * Nat.card C := by rw [hCcard]

end

section

variable {X : Type*} [Group X] [Finite X]

private theorem prime_le_card_of_mem_of_pow_eq_one {p : ℕ} [Fact p.Prime]
    {C : Subgroup X} {x : X} (hx : x ∈ C) (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    p ≤ Nat.card C := by
  have hle : Nat.card (Subgroup.zpowers x) ≤ Nat.card C :=
    Nat.card_le_card_of_injective
      (fun a : Subgroup.zpowers x => (⟨a, Subgroup.zpowers_le.mpr hx a.2⟩ : C))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  rwa [Nat.card_zpowers, orderOf_eq_prime hxp hx1] at hle

private theorem prime_sq_le_card_of_two_zpowers {p : ℕ} [Fact p.Prime]
    {C : Subgroup X} {x y : X} (hx : x ∈ C) (hy : y ∈ C) (hxp : x ^ p = 1)
    (hyp : y ^ p = 1) (hx1 : x ≠ 1) (hxy : y ∉ Subgroup.zpowers x) :
    p * p ≤ Nat.card C := by
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hy1 : y ≠ 1 := fun h => hxy (h ▸ Subgroup.one_mem _)
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hxcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
  have hycard : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyord]
  have hle : Nat.card (Subgroup.zpowers x × Subgroup.zpowers y) ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective
      (fun ab : Subgroup.zpowers x × Subgroup.zpowers y =>
        (⟨(ab.1 : X) * ab.2, C.mul_mem (Subgroup.zpowers_le.mpr hx ab.1.2)
          (Subgroup.zpowers_le.mpr hy ab.2.2)⟩ : C)) ?_
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ hab
    have h : (a1 : X) * b1 = a2 * b2 := congrArg Subtype.val hab
    have hkey : (a2 : X)⁻¹ * a1 = b2 * (b1 : X)⁻¹ := by
      have h' := congrArg (fun t => (a2 : X)⁻¹ * t * (b1 : X)⁻¹) h
      simpa [mul_assoc] using h'
    by_cases hz : (a2 : X)⁻¹ * a1 = 1
    · have ha : (a1 : X) = a2 := by
        calc (a1 : X) = a2 * ((a2 : X)⁻¹ * a1) := by group
          _ = a2 := by rw [hz, mul_one]
      have hb : (b1 : X) = b2 := by
        rw [ha] at h
        exact mul_left_cancel h
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · exfalso
      have hzx : (a2 : X)⁻¹ * a1 ∈ Subgroup.zpowers x :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ a2.2) a1.2
      have hzy : (a2 : X)⁻¹ * a1 ∈ Subgroup.zpowers y := by
        rw [hkey]
        exact Subgroup.mul_mem _ b2.2 (Subgroup.inv_mem _ b1.2)
      have hzp : ((a2 : X)⁻¹ * a1) ^ p = 1 := by
        have hdvd := orderOf_dvd_of_mem_zpowers hzx
        rw [hxord] at hdvd
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have hzord : orderOf ((a2 : X)⁻¹ * a1) = p := orderOf_eq_prime hzp hz
      have hzcard : Nat.card (Subgroup.zpowers ((a2 : X)⁻¹ * a1)) = p := by
        rw [Nat.card_zpowers, hzord]
      have hzx_eq : Subgroup.zpowers ((a2 : X)⁻¹ * a1) = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzx)
          (by rw [hzcard, hxcard])
      have hzy_eq : Subgroup.zpowers ((a2 : X)⁻¹ * a1) = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzy)
          (by rw [hzcard, hycard])
      exact hxy (by rw [← hzx_eq, hzy_eq]; exact Subgroup.mem_zpowers y)
  simpa [Nat.card_prod, hxcard, hycard] using hle

private theorem card_le_prime_sq_of_isPGroup {p : ℕ} [Fact p.Prime] {B : Subgroup X}
    (hB : IsPGroup p B) (hcard : Nat.card B ≤ p ^ 3) (hne : Nat.card B ≠ p ^ 3) :
    Nat.card B ≤ p ^ 2 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hB
  have hn3 : n ≤ 3 := by
    by_contra h
    have h3 : 3 < n := Nat.lt_of_not_le h
    have hlt : p ^ 3 < p ^ n := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt h3
    omega
  have hnne : n ≠ 3 := fun h => hne (by rw [hn, h])
  have hn2 : n ≤ 2 := by omega
  rw [hn]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn2

private theorem card_le_mul_card_comap_conj {p : ℕ} [Fact p.Prime] {Φ : MulAut X}
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X))
    (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j)
    {R : Subgroup (MulAut X)} (hR : IsElemAbelian p R) :
    Nat.card R ≤ p * Nat.card (R.comap (MulAut.conj : X →* MulAut X)) := by
  classical
  let Inn : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  have hInn : Inn.Normal := inner_range_normal
  let Q := MulAut X ⧸ Inn
  have hQcyc : IsCyclic Q := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨QuotientGroup.mk' Inn Φ, ?_⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨j, hj⟩ := CFSG.exists_eq_quotient_mk'_pow hΦ le_rfl x
    exact Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), by rw [zpow_natCast]; exact hj.symm⟩
  let f : R →* Q := (QuotientGroup.mk' Inn).comp R.subtype
  have hker : f.ker = (R ⊓ Inn).subgroupOf R := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      exact (QuotientGroup.eq_one_iff ((x : R) : MulAut X)).mp hx
    · rintro ⟨-, hx⟩
      exact (QuotientGroup.eq_one_iff ((x : R) : MulAut X)).mpr hx
  have hinf : R ⊓ Inn = (R.comap (MulAut.conj : X →* MulAut X)).map MulAut.conj := by
    refine le_antisymm ?_ ?_
    · rintro z ⟨hzR, hzInn⟩
      obtain ⟨x, rfl⟩ := hzInn
      exact ⟨x, hzR, rfl⟩
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
      exact ⟨Subgroup.mem_comap.mp hx, ⟨x, rfl⟩⟩
  have hrange_le : Nat.card f.range ≤ p := by
    have hTcard : Nat.card {q : Q // q ^ p = 1} ≤ p := by
      have hFQ : Fintype Q := Fintype.ofFinite Q
      have h := IsCyclic.card_pow_eq_one_le (α := Q) (n := p) (Fact.out : p.Prime).pos
      simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
    have hpt : ∀ q ∈ f.range, q ^ p = 1 := by
      intro q hq
      obtain ⟨x, rfl⟩ := hq
      change ((QuotientGroup.mk' Inn) (x : MulAut X)) ^ p = 1
      rw [← map_pow, hR.2 (x : MulAut X) x.2, map_one]
    refine (Nat.card_le_card_of_injective
      (fun q : f.range => (⟨(q : Q), hpt (q : Q) q.2⟩ : {r : Q // r ^ p = 1})) ?_).trans hTcard
    intro a b hab
    exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  calc Nat.card R = Nat.card f.ker * Nat.card f.range :=
        (Subgroup.card_ker_mul_card_range f).symm
    _ = Nat.card ((R ⊓ Inn).subgroupOf R) * Nat.card f.range := by rw [hker]
    _ = Nat.card ↥(R ⊓ Inn) * Nat.card f.range := by
        rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := R ⊓ Inn) (K := R) inf_le_left).toEquiv]
    _ = Nat.card ↥((R.comap (MulAut.conj : X →* MulAut X)).map MulAut.conj) *
          Nat.card f.range := by rw [hinf]
    _ = Nat.card ↥(R.comap (MulAut.conj : X →* MulAut X)) * Nat.card f.range := by
        rw [Subgroup.card_map_of_injective hZ]
    _ ≤ Nat.card ↥(R.comap (MulAut.conj : X →* MulAut X)) * p :=
        Nat.mul_le_mul_left _ hrange_le
    _ = p * Nat.card ↥(R.comap (MulAut.conj : X →* MulAut X)) := Nat.mul_comm _ _

private theorem inner_count {p : ℕ} [Fact p.Prime]
    {P₀ : Subgroup X} {B₀ : Subgroup X} {R' : Subgroup (MulAut X)} {t₀ : X}
    {S₃ : Subgroup X}
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X))
    (hΩ : ∀ E : Subgroup X, E ≤ P₀ → IsElemAbelian p E → Nat.card E ≤ p ^ 3)
    (hB₀el : IsElemAbelian p B₀) (hB₀P : B₀ ≤ P₀)
    (ht₀E : ∀ E : Subgroup X, E ≤ P₀ → IsElemAbelian p E → Nat.card E = p ^ 3 → t₀ ∈ E)
    (hR'eq : R' = B₀.map (MulAut.conj : X →* MulAut X))
    (ht₀ : t₀ ≠ 1) (ht₀S : ∀ s ∈ S₃, t₀ * s = s * t₀) :
    Nat.card R' ≤ p ^ 2 * Nat.card ↥(R' ⊓ fixingSubgroup (MulAut X) (S₃ : Set X)) := by
  classical
  let C'' : Subgroup (MulAut X) := R' ⊓ fixingSubgroup (MulAut X) (S₃ : Set X)
  have hB₀card : Nat.card B₀ ≤ p ^ 3 := hΩ B₀ hB₀P hB₀el
  have hR'card : Nat.card R' = Nat.card B₀ := by
    rw [hR'eq, Subgroup.card_map_of_injective hZ]
  by_cases h3 : Nat.card B₀ = p ^ 3
  · have ht₀B : t₀ ∈ B₀ := ht₀E B₀ hB₀P hB₀el h3
    have ht₀pow : t₀ ^ p = 1 := hB₀el.2 t₀ ht₀B
    have hconjmem : MulAut.conj t₀ ∈ C'' := by
      refine ⟨?_, ?_⟩
      · rw [hR'eq]
        exact Subgroup.mem_map_of_mem _ ht₀B
      · apply (mem_fixingSubgroup_iff (MulAut X)).2
        intro s hs
        change (MulAut.conj t₀) s = s
        rw [MulAut.conj_apply, ht₀S s hs, mul_assoc, mul_inv_cancel, mul_one]
    have hconj1 : MulAut.conj t₀ ≠ 1 := by
      intro h
      apply ht₀
      exact hZ (by rw [h, map_one])
    have hp : p ≤ Nat.card C'' :=
      prime_le_card_of_mem_of_pow_eq_one hconjmem (by rw [← map_pow, ht₀pow, map_one]) hconj1
    calc Nat.card R' = p ^ 3 := by rw [hR'card, h3]
      _ = p ^ 2 * p := by ring
      _ ≤ p ^ 2 * Nat.card C'' := Nat.mul_le_mul_left _ hp
  · have hB₀le : Nat.card B₀ ≤ p ^ 2 :=
      card_le_prime_sq_of_isPGroup (IsElemAbelian.isPGroup hB₀el) hB₀card h3
    have hCpos : 1 ≤ Nat.card C'' := Nat.card_pos
    calc Nat.card R' = Nat.card B₀ := hR'card
      _ ≤ p ^ 2 := hB₀le
      _ = p ^ 2 * 1 := (mul_one _).symm
      _ ≤ p ^ 2 * Nat.card C'' := Nat.mul_le_mul_left _ hCpos

private theorem outer_count {p : ℕ} [Fact p.Prime] {Φ φ : MulAut X}
    {P₀ B₀ : Subgroup X} {R R' : Subgroup (MulAut X)} {β : MulAut X}
    {t₀ : X} {S₃ : Subgroup X}
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X))
    (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j)
    (hP₀c : ∀ a ∈ P₀, ∀ b ∈ P₀, a * b = b * a)
    (hR'def : R' = R.map (MulAut.conj β).toMonoidHom)
    (hR'abel : IsElemAbelian p R')
    (hR'el : ∀ δ ∈ R', ∃ s ∈ P₀, ∃ j : ℕ, δ = MulAut.conj s * φ ^ j)
    (hB₀def : B₀ = R'.comap (MulAut.conj : X →* MulAut X))
    (hB₀P : B₀ ≤ P₀) (hB₀el : IsElemAbelian p B₀)
    (hout : ¬ R' ≤ (MulAut.conj : X →* MulAut X).range)
    (hφinn : ∀ k : ℕ, φ ^ k ∈ (MulAut.conj : X →* MulAut X).range → φ ^ k = 1)
    (hH1 : ∀ x ∈ P₀, ∀ k : ℕ, φ ^ k ≠ 1 →
      (MulAut.conj x * φ ^ k) ^ p = 1 →
      ∃ y ∈ P₀, MulAut.conj y * (MulAut.conj x * φ ^ k) * (MulAut.conj y)⁻¹ = φ ^ k)
    (hΩ : ∀ E : Subgroup X, E ≤ P₀ → IsElemAbelian p E → Nat.card E ≤ p ^ 3)
    (ht₀E : ∀ E : Subgroup X, E ≤ P₀ → IsElemAbelian p E → Nat.card E = p ^ 3 → t₀ ∈ E)
    (ht₀ : t₀ ≠ 1) (ht₀S : ∀ s ∈ S₃, t₀ * s = s * t₀)
    (hφS : ∀ s ∈ S₃, φ s = s) :
    ∃ γ : MulAut X, Nat.card ↥(R.map (MulAut.conj γ).toMonoidHom) ≤
      p ^ 2 * Nat.card ↥((R.map (MulAut.conj γ).toMonoidHom) ⊓
        fixingSubgroup (MulAut X) (S₃ : Set X)) := by
  classical
  obtain ⟨r, hrR', hrnot⟩ : ∃ r ∈ R', r ∉ (MulAut.conj : X →* MulAut X).range := by
    by_contra h
    apply hout
    intro x hx
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  obtain ⟨x, hxP, k, hxk⟩ := hR'el r hrR'
  have hk1 : φ ^ k ≠ 1 := by
    intro h
    apply hrnot
    rw [hxk, h, mul_one]
    exact ⟨x, rfl⟩
  have hrp : (MulAut.conj x * φ ^ k) ^ p = 1 := by
    rw [← hxk]
    exact hR'abel.2 r hrR'
  obtain ⟨y, hyP, hyconj⟩ := hH1 x hxP k hk1 hrp
  let γ : MulAut X := MulAut.conj y * β
  refine ⟨γ, ?_⟩
  let R'' : Subgroup (MulAut X) := R.map (MulAut.conj γ).toMonoidHom
  have hR''eq : R'' = R'.map (MulAut.conj (MulAut.conj y)).toMonoidHom := by
    calc R'' = R.map (MulAut.conj γ).toMonoidHom := rfl
      _ = R.map (((MulAut.conj (MulAut.conj y)).toMonoidHom).comp
            (MulAut.conj β).toMonoidHom) := by
          congr 1
      _ = R'.map (MulAut.conj (MulAut.conj y)).toMonoidHom := by
          rw [← Subgroup.map_map, ← hR'def]
  have hR''abel : IsElemAbelian p R'' := by
    rw [hR''eq]
    exact hR'abel.map _
  have hfr : ((MulAut.conj (MulAut.conj y)).toMonoidHom) r = φ ^ k := by
    rw [hxk]
    simpa [MulAut.mul_apply] using hyconj
  have hφkR'' : φ ^ k ∈ R'' := by
    rw [hR''eq, ← hfr]
    exact Subgroup.mem_map_of_mem _ hrR'
  have hcomap : R''.comap (MulAut.conj : X →* MulAut X) = B₀ :=
    comap_conj_eq_of_conj hZ hφinn hP₀c hR'el hB₀def hB₀P hyP hR''eq
  have hquot : Nat.card R'' ≤ p * Nat.card B₀ := by
    rw [← hcomap]
    exact card_le_mul_card_comap_conj hZ hΦ hR''abel
  have hφpowS : ∀ j : ℕ, ∀ s ∈ S₃, (φ ^ j) s = s := by
    intro j
    induction j with
    | zero => intro s hs; rfl
    | succ j ih =>
        intro s hs
        rw [pow_succ, MulAut.mul_apply, hφS s hs, ih s hs]
  let C'' : Subgroup (MulAut X) := R'' ⊓ fixingSubgroup (MulAut X) (S₃ : Set X)
  have hφkC : φ ^ k ∈ C'' := by
    refine ⟨hφkR'', ?_⟩
    apply (mem_fixingSubgroup_iff (MulAut X)).2
    intro s hs
    change (φ ^ k) s = s
    exact hφpowS k s hs
  have hfinal : Nat.card R'' ≤ p ^ 2 * Nat.card C'' := by
    by_cases h3 : Nat.card B₀ = p ^ 3
    · have ht₀B : t₀ ∈ B₀ := ht₀E B₀ hB₀P hB₀el h3
      have ht₀R'' : MulAut.conj t₀ ∈ R'' :=
        Subgroup.mem_comap.mp (by rw [hcomap]; exact ht₀B)
      have hctC : MulAut.conj t₀ ∈ C'' := by
        refine ⟨ht₀R'', ?_⟩
        apply (mem_fixingSubgroup_iff (MulAut X)).2
        intro s hs
        change (MulAut.conj t₀) s = s
        rw [MulAut.conj_apply, ht₀S s hs, mul_assoc, mul_inv_cancel, mul_one]
      have ht₀pow : t₀ ^ p = 1 := hB₀el.2 t₀ ht₀B
      have hctpow : (MulAut.conj t₀) ^ p = 1 := by rw [← map_pow, ht₀pow, map_one]
      have hct1 : MulAut.conj t₀ ≠ 1 := by
        intro h
        apply ht₀
        exact hZ (by rw [h, map_one])
      have hφkpow : (φ ^ k) ^ p = 1 := hR''abel.2 _ hφkR''
      have hφk_notin : φ ^ k ∉ Subgroup.zpowers (MulAut.conj t₀) := by
        intro hmem
        have hmemrange : MulAut.conj t₀ ∈ (MulAut.conj : X →* MulAut X).range :=
          ⟨t₀, rfl⟩
        have hin : φ ^ k ∈ (MulAut.conj : X →* MulAut X).range :=
          Subgroup.zpowers_le.mpr hmemrange hmem
        exact hk1 (hφinn k hin)
      have hC2 : p * p ≤ Nat.card C'' :=
        prime_sq_le_card_of_two_zpowers hctC hφkC hctpow hφkpow hct1 hφk_notin
      calc Nat.card R'' ≤ p * Nat.card B₀ := hquot
        _ = p * p ^ 3 := by rw [h3]
        _ = p ^ 2 * (p * p) := by ring
        _ ≤ p ^ 2 * Nat.card C'' := Nat.mul_le_mul_left _ hC2
    · have hB₀le : Nat.card B₀ ≤ p ^ 2 :=
        card_le_prime_sq_of_isPGroup (IsElemAbelian.isPGroup hB₀el)
          (hΩ B₀ hB₀P hB₀el) h3
      have hC1 : p ≤ Nat.card C'' :=
        prime_le_card_of_mem_of_pow_eq_one hφkC (hR''abel.2 _ hφkR'') hk1
      calc Nat.card R'' ≤ p * Nat.card B₀ := hquot
        _ ≤ p * p ^ 2 := Nat.mul_le_mul_left _ hB₀le
        _ = p ^ 2 * p := by ring
        _ ≤ p ^ 2 * Nat.card C'' := Nat.mul_le_mul_left _ hC1
  exact hfinal

end

theorem u45KeyDvdConcl_of_torus {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X)) {Φ : MulAut X}
    (hΦ : ∀ α : MulAut X, ∃ y : X, ∃ j : ℕ, α = MulAut.conj y * Φ ^ j)
    (hΦinn : ∀ k : ℕ, Φ ^ k ∈ (MulAut.conj : X →* MulAut X).range → Φ ^ k = 1)
    {m a : ℕ} (hm : ¬ p ∣ m) (hΦm : Φ ^ (p ^ a * m) = 1)
    {P₀ : Subgroup X} (hP₀ : IsPGroup p P₀) (hP₀i : ¬ p ∣ P₀.index)
    (hP₀c : ∀ x ∈ P₀, ∀ y ∈ P₀, x * y = y * x) (hΦP : ∀ s ∈ P₀, (Φ ^ m) s ∈ P₀)
    (hΩ : ∀ E : Subgroup X, E ≤ P₀ → IsElemAbelian p E → Nat.card E ≤ p ^ 3)
    {t₀ : X} (ht₀ : t₀ ≠ 1)
    (ht₀E : ∀ E : Subgroup X, E ≤ P₀ → IsElemAbelian p E → Nat.card E = p ^ 3 → t₀ ∈ E)
    (hH1 : ∀ x ∈ P₀, ∀ k : ℕ, (Φ ^ m) ^ k ≠ 1 → (MulAut.conj x * (Φ ^ m) ^ k) ^ p = 1 →
      ∃ y ∈ P₀, MulAut.conj y * (MulAut.conj x * (Φ ^ m) ^ k) * (MulAut.conj y)⁻¹ =
        (Φ ^ m) ^ k)
    {S₃ : Subgroup X} (hS₃ : IsPGroup 3 S₃) (hS₃i : ¬ 3 ∣ S₃.index)
    (ht₀S : ∀ s ∈ S₃, t₀ * s = s * t₀) (hΦS : ∀ s ∈ S₃, (Φ ^ m) s = s) :
    U45KeyDvdConcl X p := by
  classical
  intro R hR
  let φ : MulAut X := Φ ^ m
  have hφp : φ ^ (p ^ a) = 1 := by
    show (Φ ^ m) ^ (p ^ a) = 1
    rw [← pow_mul, Nat.mul_comm]
    exact hΦm
  have hφi : ¬ p ∣ (((MulAut.conj : X →* MulAut X).range) ⊔ zpowers φ).index := by
    intro hd
    exact hm (hd.trans (CFSG.index_range_conj_sup_zpowers_pow_dvd hΦ m))
  have hφinn : ∀ k : ℕ, φ ^ k ∈ (MulAut.conj : X →* MulAut X).range → φ ^ k = 1 := by
    intro k hk
    rw [← pow_mul] at hk ⊢
    exact hΦinn (m * k) hk
  obtain ⟨Q, hRQ⟩ := CFSG.exists_sylow_forall_apply_mem (p := p) hR.isPGroup
  obtain ⟨β, -, hβconj⟩ :=
    CFSG.exists_mulAut_map_eq_and_conj_mem hP₀ hP₀i ⟨a, hφp⟩ hΦP hφi
      Q.isPGroup' Q.not_dvd_index hR.isPGroup hRQ
  let R' : Subgroup (MulAut X) := R.map (MulAut.conj β).toMonoidHom
  have hR'def : R' = R.map (MulAut.conj β).toMonoidHom := rfl
  have hR'abel : IsElemAbelian p R' := hR.map _
  have hR'el : ∀ δ ∈ R', ∃ s ∈ P₀, ∃ j : ℕ, δ = MulAut.conj s * φ ^ j := by
    intro δ hδ
    obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp hδ
    obtain ⟨s, hs, j, hj⟩ := hβconj α hα
    exact ⟨s, hs, j, hj⟩
  let B₀ : Subgroup X := R'.comap (MulAut.conj : X →* MulAut X)
  have hB₀def : B₀ = R'.comap (MulAut.conj : X →* MulAut X) := rfl
  have hB₀P : B₀ ≤ P₀ := by
    intro x hx
    obtain ⟨s, hs, j, hj⟩ := hR'el (MulAut.conj x) hx
    have hmem : φ ^ j ∈ (MulAut.conj : X →* MulAut X).range := by
      refine ⟨s⁻¹ * x, ?_⟩
      rw [map_mul, map_inv, hj]
      group
    have hφj : φ ^ j = 1 := hφinn j hmem
    rw [hφj, mul_one] at hj
    exact hZ hj ▸ hs
  have hB₀el : IsElemAbelian p B₀ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hP₀c (a : X) (hB₀P a.2) (b : X) (hB₀P b.2))⟩⟩, ?_⟩
    intro a ha
    apply hZ
    rw [map_pow, map_one]
    exact hR'abel.2 (MulAut.conj a) ha
  by_cases hInner : R' ≤ (MulAut.conj : X →* MulAut X).range
  · have hR'eq : R' = B₀.map (MulAut.conj : X →* MulAut X) := by
      refine le_antisymm ?_ (Subgroup.map_comap_le _ _)
      intro δ hδ
      obtain ⟨s, rfl⟩ := hInner hδ
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.mpr hδ)
    exact transport_of_count hR'def hS₃ hS₃i
      (inner_count hZ hΩ hB₀el hB₀P ht₀E hR'eq ht₀ ht₀S)
  · obtain ⟨γ, hcount⟩ :=
      outer_count hZ hΦ hP₀c hR'def hR'abel hR'el hB₀def hB₀P hB₀el hInner
        hφinn hH1 hΩ ht₀E ht₀ ht₀S hΦS
    exact transport_of_count rfl hS₃ hS₃i hcount

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
