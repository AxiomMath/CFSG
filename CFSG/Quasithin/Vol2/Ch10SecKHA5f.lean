module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5d
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M22Data

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] def NoSL25Norm (X : Type) [Group X] : Prop :=
  ∀ T B : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Subgroup.normalizer (B : Set X) →
    ¬ IsSL25Group ↥B

theorem NoSL25Norm.noSL25In {X : Type} [Group X] [Finite X] (h : NoSL25Norm X) : NoSL25In X :=
  fun T hT B _ _ hTB => h T B hT hTB

section Transport

variable {A C : Type} [Group A] [Group C]

theorem sl25_pullback (e : C ≃* A) {T B : Subgroup A}
    (hTB : T ≤ Subgroup.normalizer (B : Set A)) (hD : IsSL25Group ↥B) :
    T.map e.symm.toMonoidHom ≤ Subgroup.normalizer ((B.map e.symm.toMonoidHom : Subgroup C) :
      Set C) ∧ IsSL25Group ↥(B.map e.symm.toMonoidHom) := by
  refine ⟨?_, hD.of_equiv (B.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have h1 := Subgroup.mem_normalizer_iff.mp (hTB ht) (e b)
  have hm : ∀ z : C, z ∈ B.map e.symm.toMonoidHom ↔ e z ∈ B := by
    intro z
    rw [A5.G3.mem_map_iff_symm]
    simp
  rw [hm, hm]
  have : e (e.symm.toMonoidHom t * b * (e.symm.toMonoidHom t)⁻¹) = t * e b * t⁻¹ := by
    simp
  rw [this]
  exact h1

theorem NoSL25Norm.of_mulEquiv (e : C ≃* A) (h : NoSL25Norm C) : NoSL25Norm A := by
  intro T B hT hTB hD
  obtain ⟨h1, h2⟩ := sl25_pullback e hTB hD
  refine h (T.map e.symm.toMonoidHom) (B.map e.symm.toMonoidHom) ?_ h1 h2
  have := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := T)
    (Y := ⊤)).mpr hT
  rwa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at this

theorem noSL25Norm_of_sylow {M : Type} [Group M] [Finite M] {U : Subgroup M}
    (hU : IsSylowTwoOf U ⊤)
    (h : ∀ B : Subgroup M, U ≤ Subgroup.normalizer (B : Set M) → ¬ IsSL25Group ↥B) :
    NoSL25Norm M := by
  intro T B hT hTB hD
  obtain ⟨g, hg⟩ := A5.G3.exists_conj_eq_of_isSylowTwoOf hU hT
  obtain ⟨h1, h2⟩ := sl25_pullback (MulAut.conj g) hTB hD
  have hU' : T.map (MulAut.conj g).symm.toMonoidHom = U := by
    rw [← hg, Subgroup.map_map]
    have : ((MulAut.conj g).symm.toMonoidHom).comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id M := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  rw [hU'] at h1
  exact h _ h1 h2

end Transport

theorem IsSL25Group.commutator_eq {X : Type} [Group X] {B : Subgroup X}
    (hD : IsSL25Group ↥B) : ⁅B, B⁆ = B := by
  have h1 := hD.perfect
  have h2 : (commutator ↥B).map B.subtype = ⁅B, B⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← h2, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem not_isSL25_of_latCert {n : ℕ} (c : LatCert (Perm (Fin n)))
    (hck : c.check RN.enc = true) (htle : c.tleOK RN.enc = true)
    (hk : c.sizes.headD 0 = 2 ^ 7) {m : ℕ} (hm : c.msize = 2 ^ 7 * m) (hodd : ¬ 2 ∣ m)
    (hA : ∀ (j : ℕ) (hj : j < (c.tGens :: c.lat).length), c.sizes.getD j 0 = 1920 →
      ∃ A : Subgroup (Perm (Fin n)), A ≤ Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]} ∧
        Nat.card A = 960 ∧ ⁅A, A⁆ = A ∧ ∀ g ∈ A, orderOf g ≠ 6)
    (B : Subgroup ↥(Subgroup.closure {g | g ∈ c.mGens})) (hD : IsSL25Group ↥B)
    (hUB : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (Subgroup.closure {g | g ∈ c.mGens}) ≤
      Subgroup.normalizer (B : Set ↥(Subgroup.closure {g | g ∈ c.mGens}))) : False := by
  classical
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hTM : Subgroup.closure {g | g ∈ c.tGens} ≤ Subgroup.closure {g | g ∈ c.mGens} :=
    c.t_le_m (rawIsEnc n) hcl htle
  have hUsyl := c.isSylowTwoOf_top (rawIsEnc n) hck (k := 7) hk hm hodd
  have hUcard : Nat.card ↥((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv,
      c.card_t (rawIsEnc n) hcl hsz, hk]
  obtain ⟨j, hj1, hj2, -, -⟩ := sl25_sup_data hUsyl hD hUB
  have hj : j = 0 := by
    have h2 : 2 ^ (7 + j) = 2 ^ 7 := by rw [← hj1, hUcard]
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hj
  have hYcard : Nat.card ↥(B ⊔ (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})) = 1920 := by rw [hj2]; norm_num
  obtain ⟨i, hi, hLM, hYL, hcardi⟩ := c.overgroup_cases_idx (rawIsEnc n) hck
    (B ⊔ (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (Subgroup.closure {g | g ∈ c.mGens}))
    le_sup_right
  have hLcard : Nat.card (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]}) = 1920 := by
    rw [hYL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv] at hYcard
    exact hYcard
  have hsizes : c.sizes.getD i 0 = 1920 := by rw [← hcardi]; exact hLcard
  obtain ⟨A, hAL', hAcard, -, -⟩ := hA i hi hsizes
  have hY₀ : (B ⊔ (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ c.mGens})).map (Subgroup.closure {g | g ∈ c.mGens}).subtype =
        Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]} := by
    rw [hYL]
    exact Subgroup.map_subgroupOf_eq_of_le hLM
  have hB₀Y₀ : B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype ≤
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]} := by
    rw [← hY₀]
    exact Subgroup.map_mono le_sup_left
  have hB₀card : Nat.card (B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype) = 1920 := by
    rw [Subgroup.card_map_of_injective (Subgroup.closure {g | g ∈ c.mGens}).subtype_injective]
    exact hD.card
  have hperf : ⁅B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype,
      B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype⁆ =
        B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype := by
    rw [← Subgroup.map_commutator, hD.commutator_eq]
  have hcomm : ⁅Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]},
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[i]}⁆ ≤ A :=
    commutator_le_of_card_eq_two_mul hAL' (by rw [hLcard, hAcard])
  have hle : B.map (Subgroup.closure {g | g ∈ c.mGens}).subtype ≤ A := by
    rw [← hperf]
    exact (Subgroup.commutator_mono hB₀Y₀ hB₀Y₀).trans hcomm
  have := Subgroup.card_le_of_le hle
  rw [hB₀card, hAcard] at this
  omega

theorem not_isSL25_of_latCert_amb {n : ℕ} (c : LatCert (Perm (Fin n)))
    (hck : c.check RN.enc = true) (htle : c.tleOK RN.enc = true)
    (hk : c.sizes.headD 0 = 2 ^ 7) {m : ℕ} (hm : c.msize = 2 ^ 7 * m) (hodd : ¬ 2 ∣ m)
    (hA : ∀ (j : ℕ) (hj : j < (c.tGens :: c.lat).length), c.sizes.getD j 0 = 1920 →
      ∃ A : Subgroup (Perm (Fin n)), A ≤ Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]} ∧
        Nat.card A = 960 ∧ ⁅A, A⁆ = A ∧ ∀ g ∈ A, orderOf g ≠ 6)
    (B : Subgroup (Perm (Fin n))) (hBM : B ≤ Subgroup.closure {g | g ∈ c.mGens})
    (hD : IsSL25Group ↥B)
    (hTB : Subgroup.closure {g | g ∈ c.tGens} ≤ Subgroup.normalizer (B : Set (Perm (Fin n)))) :
    False :=
  not_isSL25_of_latCert c hck htle hk hm hodd hA
    (B.subgroupOf (Subgroup.closure {g | g ∈ c.mGens}))
    (hD.of_equiv (Subgroup.subgroupOfEquivOfLe hBM).symm) (A5.G3.subgroupOf_le_normalizer hTB)

theorem noSL25Norm_of_latSix {n : ℕ} (c : LatCert (Perm (Fin n)))
    (hck : c.check RN.enc = true) (htle : c.tleOK RN.enc = true)
    (hk : c.sizes.headD 0 = 2 ^ 7) {m : ℕ} (hm : c.msize = 2 ^ 7 * m) (hodd : ¬ 2 ∣ m)
    (ds : List (A5.G3.AData n)) (hs : A5.G3.latSixCheck c ds = true) :
    NoSL25Norm ↥(Subgroup.closure {g | g ∈ c.mGens}) := by
  have hUsyl := c.isSylowTwoOf_top (rawIsEnc n) hck (k := 7) hk hm hodd
  exact noSL25Norm_of_sylow hUsyl fun B hUB hD =>
    not_isSL25_of_latCert c hck htle hk hm hodd (A5.G3.hA_of_latSixCheck c
      (LatCert.closedOK_of_check hck) ds hs) B hD hUB

theorem noSL25Norm_m22
    {X : Type} [Group X] (h : IsSporadic .M22 X) : NoSL25Norm X := by
  obtain ⟨e⟩ := h
  let e' : X ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  exact NoSL25Norm.of_mulEquiv
    ((MulEquiv.subgroupCongr Vol2Native.A312L.M22Lat.mGens_closure).trans e'.symm)
    (noSL25Norm_of_latSix Vol2Native.A312L.M22Lat.cert Vol2Native.A312L.M22Lat.cert_check
      A5.G3.m22_tle (by decide) (m := 3465) (by decide) (by omega) [A5.G3.m22AData]
      A5.G3.m22_latSix)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
