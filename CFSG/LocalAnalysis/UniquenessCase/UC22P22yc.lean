module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xh
import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise

namespace P22y

section ConjOn

variable {A : Type} [Group A]

@[expose] def conjAutOf (Y : Subgroup A) {g : A} (hg : g ∈ normalizer (Y : Set A)) : MulAut ↥Y where
  toFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg y).1 y.2⟩
  invFun y := ⟨g⁻¹ * y * g, (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)).2 (by
    simpa [mul_assoc] using y.2)⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def conjOnHom {P : Type} [Group P] (Y : Subgroup A) (f : P →* A)
    (hf : ∀ x, f x ∈ normalizer (Y : Set A)) : P →* MulAut ↥Y where
  toFun x := conjAutOf Y (hf x)
  map_one' := MulEquiv.ext fun y => Subtype.ext (by simp [conjAutOf])
  map_mul' a b := MulEquiv.ext fun y => Subtype.ext (by simp [conjAutOf, mul_assoc])

theorem conjOnHom_apply {P : Type} [Group P] (Y : Subgroup A) (f : P →* A)
    (hf : ∀ x, f x ∈ normalizer (Y : Set A)) (x : P) (y : ↥Y) :
    ((conjOnHom Y f hf x y : ↥Y) : A) = f x * y * (f x)⁻¹ :=
  rfl

theorem mem_normalizer_of_smul_eq {P : Type} [Group P] {p : ℕ} [Fact p.Prime] {Y : Subgroup A}
    (f : P →* A) (hf : ∀ x, f x ∈ normalizer (Y : Set A)) (ω : Sylow p ↥Y) {x : P}
    (hx : conjOnHom Y f hf x • ω = ω) :
    f x ∈ normalizer (((ω : Subgroup ↥Y).map Y.subtype : Subgroup A) : Set A) := by
  have hmem : ∀ s : ↥Y, s ∈ (ω : Subgroup ↥Y) ↔ conjOnHom Y f hf x s ∈ (ω : Subgroup ↥Y) := by
    intro s
    have h1 := Subgroup.ext_iff.1 (congrArg (fun P : Sylow p ↥Y => (P : Subgroup ↥Y)) hx)
      (conjOnHom Y f hf x • s)
    rw [Sylow.pointwise_smul_def, Subgroup.smul_mem_pointwise_smul_iff, MulAut.smul_def] at h1
    exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨conjOnHom Y f hf x s, (hmem s).1 hs, rfl⟩
  · rintro ⟨t, ht, hta⟩
    have haY : a ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.1 (hf x) a).2
      apply this
      rw [← hta]
      exact t.2
    refine ⟨⟨a, haY⟩, (hmem _).2 ?_, rfl⟩
    have he : conjOnHom Y f hf x ⟨a, haY⟩ = t := Subtype.ext (by
      rw [conjOnHom_apply]
      exact hta.symm)
    rw [he]
    exact ht

end ConjOn

end P22y

open P22y

variable {G : Type} [Group G] [Finite G]

@[expose] def toMbarOf (D : Data G) {P : Subgroup G} (hPM : P ≤ D.M) : ↥P →* MBar D.M D.U :=
  (QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp (Subgroup.inclusion hPM)

theorem uc22p22yc_conj_le_normalizer (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m) {P : Subgroup G}
    (hPM : P ≤ D.M) (hPN : ∀ x : ↥P, toMbarOf D hPM x ∈ normalizer (Nb i : Set (MBar D.M D.U)))
    (ω : Sylow 2 ↥(Nb i)) {R : Subgroup ↥P}
    (hR : ∀ x ∈ R, conjOnHom (Nb i) (toMbarOf D hPM) hPN x • ω = ω) :
    ∃ n ∈ D.M, (R.map P.subtype).map (MulAut.conj n⁻¹).toMonoidHom ≤
      normalizer (proofEiHat D (preN D (Nb i)) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hE⟩ := uc22p22xh_conj D Ch h2 h3 h51 hH c m Nb hNb i ω
  refine ⟨n, P22x.preN_le_M D (Nb i) hn, ?_⟩
  rintro _ ⟨_, ⟨x, hxR, rfl⟩, rfl⟩
  have hxQ := mem_normalizer_of_smul_eq (toMbarOf D hPM) hPN ω (hR x hxR)
  have hx := uc22p22xh_mem_normalizer D (Y := Nb i) (y := (x : G)) (hPM x.2) (hPN x) hxQ
  rw [hE] at hx
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro e
  have key : ∀ e : G, e ∈ proofEiHat D (preN D (Nb i)) ↔
      n * e * n⁻¹ ∈ (proofEiHat D (preN D (Nb i))).map (MulAut.conj n).toMonoidHom := by
    intro e
    constructor
    · intro he
      exact ⟨e, he, rfl⟩
    · rintro ⟨f, hf, hfe⟩
      have : f = e := by
        have h1 : n * f * n⁻¹ = n * e * n⁻¹ := hfe
        simpa using h1
      rwa [← this]
  rw [key, key]
  have h1 := hx (n * e * n⁻¹)
  have e1 : (x : G) * (n * e * n⁻¹) * (x : G)⁻¹ =
      n * ((MulAut.conj n⁻¹).toMonoidHom (x : G) * e * ((MulAut.conj n⁻¹).toMonoidHom (x : G))⁻¹) * n⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e1] at h1
  exact h1

theorem uc22p22yc_noncyclic_conj (D : Data G) {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hPM : P ≤ D.M)
    (hel : IsElemAbelian p P) {R : Subgroup ↥P} (hR : p ^ 2 ≤ Nat.card R) {n : G} (hn : n ∈ D.M) :
    (R.map P.subtype).map (MulAut.conj n⁻¹).toMonoidHom ≤ D.M ∧
      IsPGroup p ↥((R.map P.subtype).map (MulAut.conj n⁻¹).toMonoidHom) ∧
      ¬ IsCyclic ↥((R.map P.subtype).map (MulAut.conj n⁻¹).toMonoidHom) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hRel : IsElemAbelian p (R.map P.subtype) := hel.mono (Subgroup.map_subtype_le R)
  have hXel : IsElemAbelian p ((R.map P.subtype).map (MulAut.conj n⁻¹).toMonoidHom) :=
    hRel.map _
  have hcard : Nat.card ↥((R.map P.subtype).map (MulAut.conj n⁻¹).toMonoidHom) = Nat.card R := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective,
      Subgroup.card_map_of_injective P.subtype_injective]
  refine ⟨?_, hXel.isPGroup, CFSG.LocalAnalysis.GLTheoremB.not_isCyclic_of_isElemAbelian hXel (hcard ▸ hR)⟩
  rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
  have hx : (x : G) ∈ D.M := hPM x.2
  have hn' : n⁻¹ ∈ D.M := D.M.inv_mem hn
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
  exact D.M.mul_mem (D.M.mul_mem hn' hx) (by simpa using hn)

theorem uc22p22yc_caseA (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U))
    (hNb : NbarSplit D Nb) (i : Fin m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hPM : P ≤ D.M) (hel : IsElemAbelian p P) (hcard : Nat.card P = p ^ 3)
    (hPN : ∀ x : ↥P, toMbarOf D hPM x ∈ normalizer (Nb i : Set (MBar D.M D.U))) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≤ normalizer (proofEiHat D (preN D (Nb i)) : Set G) ∧
      IsPGroup p ↥X ∧ ¬ IsCyclic ↥X := by
  obtain ⟨n, hn, -⟩ := h51 hH c m Nb hNb i
  have hexp : ∀ x : ↥P, x ^ p = 1 := fun x => Subtype.ext (hel.2 x x.2)
  have hPab : ∀ x y : ↥P, x * y = y * x := fun x y => hel.1.is_comm.comm x y
  obtain ⟨ω, hω⟩ := P22y.exists_sylow_index_le hn hp hp2 hexp hPab
    (conjOnHom (Nb i) (toMbarOf D hPM) hPN)
  set R : Subgroup ↥P := (MulAction.stabilizer (MulAut ↥(Nb i)) ω).comap
    (conjOnHom (Nb i) (toMbarOf D hPM) hPN) with hRdef
  have hR : p ^ 2 ≤ Nat.card R := by
    have h1 := Subgroup.card_mul_index R
    rw [hcard] at h1
    have h2 : p ^ 3 ≤ Nat.card R * p := h1 ▸ Nat.mul_le_mul_left _ hω
    have h3 : p ^ 2 * p ≤ Nat.card R * p := by rw [← pow_succ]; exact h2
    exact Nat.le_of_mul_le_mul_right h3 hp.pos
  obtain ⟨g, hg, hle⟩ := uc22p22yc_conj_le_normalizer D Ch h2 h3 h51 hH c m Nb hNb i hPM hPN ω
    (R := R) fun x hx => hx
  obtain ⟨hXM, hXp, hXc⟩ := uc22p22yc_noncyclic_conj D hp hPM hel hR hg
  exact ⟨_, hXM, hle, hXp, hXc⟩

theorem uc22p22yc_caseA2 (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U))
    (hNb : NbarSplit D Nb) (i : Fin m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hPM : P ≤ D.M) (hel : IsElemAbelian p P) (hcard : p ^ 2 ≤ Nat.card P)
    (hpN : ¬ p ∣ Nat.card (Nb i))
    (hPN : ∀ x : ↥P, toMbarOf D hPM x ∈ normalizer (Nb i : Set (MBar D.M D.U))) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≤ normalizer (proofEiHat D (preN D (Nb i)) : Set G) ∧
      IsPGroup p ↥X ∧ ¬ IsCyclic ↥X := by
  obtain ⟨n, hn, -⟩ := h51 hH c m Nb hNb i
  have hexp : ∀ x : ↥P, x ^ p = 1 := fun x => Subtype.ext (hel.2 x x.2)
  obtain ⟨ω, hω⟩ := P22y.exists_sylow_fixed_of_not_dvd hn hp hp2 hexp hpN
    (conjOnHom (Nb i) (toMbarOf D hPM) hPN)
  have hR : p ^ 2 ≤ Nat.card (⊤ : Subgroup ↥P) := by rwa [Subgroup.card_top]
  obtain ⟨g, hg, hle⟩ := uc22p22yc_conj_le_normalizer D Ch h2 h3 h51 hH c m Nb hNb i hPM hPN ω
    (R := ⊤) fun x _ => hω x
  obtain ⟨hXM, hXp, hXc⟩ := uc22p22yc_noncyclic_conj D hp hPM hel hR hg
  exact ⟨_, hXM, hle, hXp, hXc⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
