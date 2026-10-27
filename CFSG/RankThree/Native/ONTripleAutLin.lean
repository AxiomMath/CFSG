module

public import CFSG.RankThree.Native.ONTripleAutSp
public import CFSG.RankThree.Native.ONTripleSig

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open Subgroup
open scoped commutatorElement

attribute [local irreducible] dotProduct

@[expose] def matOf (f : P0G →* P0G) : M4 :=
  Matrix.of fun i j => relG.coord (f ⟨xG i, ThreeQRel.v_mem i⟩) j

@[expose] def vecMulHom (A : M4) :
    Multiplicative (Fin 4 → ZMod 3) →* Multiplicative (Fin 4 → ZMod 3) where
  toFun v := Multiplicative.ofAdd (Matrix.vecMul (Multiplicative.toAdd v) A)
  map_one' := by simp
  map_mul' u v := by simp [Matrix.add_vecMul]

theorem single_vecMul (A : M4) (i : Fin 4) : Matrix.vecMul (Pi.single i 1) A = A i := by
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem coord_map (f : P0G →* P0G) (hz : relG.coord (f ⟨zG, ThreeQRel.x_mem⟩) = 0)
    (g : P0G) : relG.coord (f g) = Matrix.vecMul (relG.coord g) (matOf f) := by
  have h : relG.coordHom.comp f = (vecMulHom (matOf f)).comp relG.coordHom := by
    apply MonoidHom.eq_of_eqOn_dense threeQ_closure_top
    rintro ⟨g, hg⟩ hgS
    simp only [Set.mem_preimage, Subgroup.coe_subtype] at hgS
    rcases hgS with rfl | ⟨i, rfl⟩
    · show Multiplicative.ofAdd (relG.coord (f ⟨zG, hg⟩)) =
        Multiplicative.ofAdd (Matrix.vecMul (relG.coord ⟨zG, hg⟩) (matOf f))
      rw [hz, coord_zG, Matrix.zero_vecMul]
    · show Multiplicative.ofAdd (relG.coord (f ⟨xG i, hg⟩)) =
        Multiplicative.ofAdd (Matrix.vecMul (relG.coord ⟨xG i, hg⟩) (matOf f))
      rw [coord_xG, single_vecMul]
      rfl
  exact congrArg (fun φ => Multiplicative.toAdd (φ g)) h

theorem matOf_comp (f g : P0G →* P0G) (hf : relG.coord (f ⟨zG, ThreeQRel.x_mem⟩) = 0) :
    matOf (f.comp g) = matOf g * matOf f := by
  ext i j
  rw [matOf, Matrix.of_apply, MonoidHom.comp_apply, coord_map f hf, Matrix.mul_apply]
  simp [Matrix.vecMul, dotProduct, matOf]

theorem threePair_single : ∀ i j : Fin 4,
    ThreeQRel.threePair omegaZ (Pi.single i 1) (Pi.single j 1) = omegaZ i j := by
  decide +kernel

theorem threePair_matOf (f : P0G →* P0G) (hz : f ⟨zG, ThreeQRel.x_mem⟩ = ⟨zG, ThreeQRel.x_mem⟩)
    (u v : Fin 4 → ZMod 3) :
    ThreeQRel.threePair omegaZ (Matrix.vecMul u (matOf f)) (Matrix.vecMul v (matOf f)) =
      ThreeQRel.threePair omegaZ u v := by
  have hz' : relG.coord (f ⟨zG, ThreeQRel.x_mem⟩) = 0 := by rw [hz, coord_zG]
  set g : P0G := ⟨threeNF zG xG 0 u, ThreeQRel.nf_mem 0 u⟩ with hgdef
  set h : P0G := ⟨threeNF zG xG 0 v, ThreeQRel.nf_mem 0 v⟩ with hhdef
  have hg : relG.coord g = u := relG.coord_nf 0 u
  have hh : relG.coord h = v := relG.coord_nf 0 v
  have e1 := relG.comm_coord_coord g h
  have e2 := relG.comm_coord_coord (f g) (f h)
  rw [coord_map f hz' g, coord_map f hz' h, hg, hh] at e2
  rw [hg, hh] at e1
  have e4 : ⁅g, h⁆ = (⟨zG, ThreeQRel.x_mem⟩ : P0G) ^ (ThreeQRel.threePair omegaZ u v).val := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    exact e1
  have e3 : ((f ⁅g, h⁆ : P0G) : GM) = ⁅((f g : P0G) : GM), ((f h : P0G) : GM)⁆ := by
    rw [map_commutatorElement]
    rfl
  rw [e4, map_pow, hz, SubgroupClass.coe_pow, e2] at e3
  exact (relG.x_pow_val_inj e3).symm

theorem matOf_sp (f : P0G →* P0G) (hz : f ⟨zG, ThreeQRel.x_mem⟩ = ⟨zG, ThreeQRel.x_mem⟩) :
    ∀ i j, ThreeQRel.threePair omegaZ (matOf f i) (matOf f j) = omegaZ i j := by
  intro i j
  have := threePair_matOf f hz (Pi.single i 1) (Pi.single j 1)
  rw [single_vecMul, single_vecMul] at this
  rw [this, threePair_single]

abbrev NP0 : Subgroup GM := normalizer (P0G : Set GM)

theorem conj_mem_P0_of {n : GM} (hn : n ∈ NP0) {g : GM} (hg : g ∈ P0G) :
    n⁻¹ * g * n ∈ P0G := by
  have := (mem_normalizer_iff.1 (inv_mem hn) g).1 hg
  simpa using this

theorem mem_NP0_of {n : GM} (h : ∀ g ∈ P0G, n⁻¹ * g * n ∈ P0G) : n ∈ NP0 := by
  have hle : P0G.map (MulAut.conj n⁻¹).toMonoidHom ≤ P0G := by
    rintro _ ⟨g, hg, rfl⟩
    simpa [MulAut.conj_apply] using h g hg
  have heq : P0G.map (MulAut.conj n⁻¹).toMonoidHom = P0G :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj n⁻¹).injective])
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← heq] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    simpa [MulAut.conj_apply, mul_assoc] using hp
  · intro hg
    have := h _ hg
    simpa [mul_assoc] using this

@[expose] def conjN (n : NP0) : P0G →* P0G where
  toFun g := ⟨(n : GM)⁻¹ * g * n, conj_mem_P0_of n.2 g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show (n : GM)⁻¹ * (a * b : P0G) * n = (n : GM)⁻¹ * a * n * ((n : GM)⁻¹ * b * n)
    rw [Subgroup.coe_mul]
    group)

theorem conjN_apply (n : NP0) (g : P0G) : ((conjN n g : P0G) : GM) = (n : GM)⁻¹ * g * n := rfl

theorem conjN_zG (n : NP0) : conjN n ⟨zG, ThreeQRel.x_mem⟩ = ⟨zG, ThreeQRel.x_mem⟩ := by
  apply Subtype.ext
  rw [conjN_apply]
  show (n : GM)⁻¹ * zG * n = zG
  rw [mul_assoc, zG_central, ← mul_assoc, inv_mul_cancel, one_mul]

@[expose] def muN (n : NP0) : M4 := matOf (conjN n)

theorem coord_conjN (n : NP0) (g : P0G) :
    relG.coord (conjN n g) = Matrix.vecMul (relG.coord g) (muN n) :=
  coord_map _ (by rw [conjN_zG, coord_zG]) g

theorem muN_mul (a b : NP0) : muN (a * b) = muN a * muN b := by
  have h : conjN (a * b) = (conjN b).comp (conjN a) := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    rw [conjN_apply, MonoidHom.comp_apply, conjN_apply, conjN_apply, Subgroup.coe_mul]
    group
  rw [muN, h, matOf_comp _ _ (by rw [conjN_zG, coord_zG])]
  rfl

theorem muN_of_central {n : NP0} (hn : ∀ g (hg : g ∈ P0G),
    relG.coord ⟨(n : GM)⁻¹ * g * n, conj_mem_P0_of n.2 hg⟩ = relG.coord ⟨g, hg⟩) :
    muN n = 1 := by
  ext i j
  rw [muN, matOf, Matrix.of_apply]
  have := hn (xG i) (ThreeQRel.v_mem i)
  rw [show (conjN n ⟨xG i, ThreeQRel.v_mem i⟩ : P0G) =
    ⟨(n : GM)⁻¹ * xG i * n, conj_mem_P0_of n.2 (ThreeQRel.v_mem i)⟩ from rfl, this, coord_xG,
    Matrix.one_apply, Pi.single_apply]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

theorem muN_one : muN 1 = 1 :=
  muN_of_central fun g hg => by
    have e : (⟨(↑(1 : NP0) : GM)⁻¹ * g * ↑(1 : NP0), conj_mem_P0_of (1 : NP0).2 hg⟩ : P0G) =
        ⟨g, hg⟩ := by
      apply Subtype.ext
      change (↑(1 : NP0) : GM)⁻¹ * g * ↑(1 : NP0) = g
      rw [OneMemClass.coe_one, inv_one, one_mul, mul_one]
    exact congrArg _ e

@[expose] def muHom : NP0 →* M4 where
  toFun := muN
  map_one' := muN_one
  map_mul' := muN_mul

theorem muN_P0 (n : NP0) (hn : (n : GM) ∈ P0G) : muN n = 1 := by
  apply muN_of_central
  intro g hg
  have h1 := relG.coord_mul ((⟨(n : GM), hn⟩ : P0G)⁻¹ * ⟨g, hg⟩) ⟨(n : GM), hn⟩
  have h2 := relG.coord_mul ((⟨(n : GM), hn⟩ : P0G)⁻¹) ⟨g, hg⟩
  have h3 := relG.coord_mul ((⟨(n : GM), hn⟩ : P0G)⁻¹) ⟨(n : GM), hn⟩
  rw [inv_mul_cancel] at h3
  have h0 : relG.coord (1 : P0G) = 0 := (relG.coord_eq_zero_iff _).2 (one_mem _)
  rw [h0] at h3
  have e : (⟨(n : GM)⁻¹ * g * n, conj_mem_P0_of n.2 hg⟩ : P0G) =
      (⟨(n : GM), hn⟩ : P0G)⁻¹ * ⟨g, hg⟩ * ⟨(n : GM), hn⟩ := rfl
  rw [e, h1, h2]
  calc relG.coord (⟨(n : GM), hn⟩ : P0G)⁻¹ + relG.coord ⟨g, hg⟩ + relG.coord ⟨(n : GM), hn⟩ =
      (relG.coord (⟨(n : GM), hn⟩ : P0G)⁻¹ + relG.coord ⟨(n : GM), hn⟩) +
        relG.coord ⟨g, hg⟩ := by abel
    _ = relG.coord ⟨g, hg⟩ := by rw [← h3, zero_add]

theorem nG_mem_NP0 {k : ℕ} (hk : k < 2) : nG k ∈ NP0 :=
  mem_NP0_of fun _ hg => conj_mem_P0 k hk hg

theorem muN_nG {k : ℕ} (hk : k < 2) : muN ⟨nG k, nG_mem_NP0 hk⟩ = matNM k := by
  ext i j
  rw [muN, matOf, Matrix.of_apply, matNM, Matrix.of_apply]
  have e : (conjN ⟨nG k, nG_mem_NP0 hk⟩ ⟨xG i, ThreeQRel.v_mem i⟩ : P0G) =
      conjP0 k hk ⟨xG i, ThreeQRel.v_mem i⟩ := rfl
  rw [e, coord_conj, coord_xG, vmul_single]

theorem wordN_mem_NP0 (w : List ℕ) (hw : ∀ k ∈ w, k < 2) : wordN w ∈ NP0 := by
  induction w with
  | nil => exact one_mem _
  | cons k w ih =>
    rw [wordN_cons]
    exact mul_mem (nG_mem_NP0 (hw k (by simp))) (ih fun j hj => hw j (by simp [hj]))

theorem muN_wordN (w : List ℕ) (hw : ∀ k ∈ w, k < 2) :
    muN ⟨wordN w, wordN_mem_NP0 w hw⟩ = (w.map fun k => matNM k).prod := by
  induction w with
  | nil =>
    have : (⟨wordN [], wordN_mem_NP0 [] hw⟩ : NP0) = 1 := Subtype.ext rfl
    rw [this, muN_one]
    rfl
  | cons k w ih =>
    have hk := hw k (by simp)
    have hw' : ∀ j ∈ w, j < 2 := fun j hj => hw j (by simp [hj])
    have e : (⟨wordN (k :: w), wordN_mem_NP0 _ hw⟩ : NP0) =
        ⟨nG k, nG_mem_NP0 hk⟩ * ⟨wordN w, wordN_mem_NP0 w hw'⟩ := Subtype.ext (wordN_cons k w)
    rw [e, muN_mul, muN_nG hk, ih hw', List.map_cons, List.prod_cons]

theorem relIndex_not_dvd : ¬ 3 ∣ (P0G.subgroupOf NP0).index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := Subgroup.relIndex_mul_index (H := P0G) (K := NP0) le_normalizer
  have h2 := P0Syl.not_dvd_index
  rw [P0Syl_coe] at h2
  intro h
  apply h2
  rw [← h1]
  exact Dvd.dvd.mul_right h _

theorem pow_relIndex_mem (y : NP0) : ((y : GM) ^ (P0G.subgroupOf NP0).index) ∈ P0G := by
  have hN : (P0G.subgroupOf NP0).Normal := Subgroup.normal_in_normalizer
  have h := pow_card_eq_one' (G := NP0 ⧸ P0G.subgroupOf NP0) (x := (y : NP0 ⧸ _))
  rw [← Subgroup.index] at h
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
  exact h

theorem muN_mem_R0 (n : NP0) : muN n ∈ R0list := by
  have hsp := matOf_sp (conjN n) (conjN_zG n)
  rcases (sp_facts (muN n) hsp).2.2 with h | ⟨r, hr, k, -, hne, h3⟩
  · exact h
  · exfalso
    obtain ⟨w, hw, rfl⟩ := exists_word_of_mem_R0 hr
    set y : NP0 := (⟨wordN w, wordN_mem_NP0 w hw⟩ * n) ^ k
    have hy : muN y = ((w.map fun k => matNM k).prod * muN n) ^ k := by
      show muHom ((⟨wordN w, wordN_mem_NP0 w hw⟩ * n) ^ k) = _
      rw [map_pow, map_mul]
      show (muN _ * muN n) ^ k = _
      rw [muN_wordN w hw]
    have hq := muN_P0 (y ^ (P0G.subgroupOf NP0).index) (by
      rw [Subgroup.coe_pow]
      exact pow_relIndex_mem y)
    rw [show muN (y ^ (P0G.subgroupOf NP0).index) = muN y ^ (P0G.subgroupOf NP0).index from
      map_pow muHom y _, hy] at hq
    have h1 : orderOf (((w.map fun k => matNM k).prod * muN n) ^ k) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one h3
    have h2 : orderOf (((w.map fun k => matNM k).prod * muN n) ^ k) ∣
        (P0G.subgroupOf NP0).index := orderOf_dvd_of_pow_eq_one hq
    have hcop : Nat.Coprime 3 (P0G.subgroupOf NP0).index :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 relIndex_not_dvd
    have : orderOf (((w.map fun k => matNM k).prod * muN n) ^ k) ∣ 1 := by
      rw [← hcop]
      exact Nat.dvd_gcd h1 h2
    rw [Nat.dvd_one, orderOf_eq_one_iff] at this
    exact hne this

theorem mem_zpowers_of_centralizes_P0 {c : GM} (hc : ∀ g ∈ P0G, c * g = g * c) :
    c ∈ zpowers zG := by
  have hx0 : c ∈ centralizer {xG 0} :=
    mem_centralizer_singleton_iff.2 (hc _ (ThreeQRel.v_mem 0))
  obtain ⟨a, k, hk, rfl⟩ := mem_centralizer_x0_iff.1 hx0
  have hky : ∀ j < 2, k * yG j = yG j * k := by
    intro j hj
    have h1 := hc _ (yG_mem_P0 hj)
    have hx : Commute (xG 0 ^ a) (yG j) := Commute.pow_left (yG_comm_x0 hj).symm a
    have e : xG 0 ^ a * (k * yG j) = xG 0 ^ a * (yG j * k) := by
      calc xG 0 ^ a * (k * yG j) = xG 0 ^ a * k * yG j := by rw [mul_assoc]
        _ = yG j * (xG 0 ^ a * k) := h1
        _ = yG j * xG 0 ^ a * k := by rw [mul_assoc]
        _ = xG 0 ^ a * yG j * k := by rw [hx.eq]
        _ = xG 0 ^ a * (yG j * k) := by rw [mul_assoc]
    exact mul_left_cancel e
  have hact : ∀ j < 2, actK ⟨k, hk⟩ * sY j = sY j * actK ⟨k, hk⟩ := by
    intro j hj
    rw [← actK_yG hj, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hky j hj)
  obtain ⟨p, hp, q, hq, he⟩ := cent_sY _ (hact 0 (by norm_num)) (hact 1 (by norm_num))
  have hyk : actK ⟨k, hk⟩ = actK (⟨yG 0, yG_mem_K0 (by norm_num)⟩ ^ p *
      ⟨yG 1, yG_mem_K0 (by norm_num)⟩ ^ q) := by
    rw [map_mul, map_pow, map_pow, actK_yG (by norm_num), actK_yG (by norm_num), he]
  obtain ⟨e, he'⟩ := zG_mem_ker (⟨k, hk⟩ * (⟨yG 0, yG_mem_K0 (by norm_num)⟩ ^ p *
    ⟨yG 1, yG_mem_K0 (by norm_num)⟩ ^ q)⁻¹) (by rw [map_mul, map_inv, hyk, mul_inv_cancel])
  have hkP : k ∈ P0G := by
    have : k = zG ^ e * (yG 0 ^ p * yG 1 ^ q) := by
      rw [← he']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
      group
    rw [this]
    exact mul_mem (pow_mem ThreeQRel.x_mem e) (mul_mem (pow_mem (yG_mem_P0 (by norm_num)) p)
      (pow_mem (yG_mem_P0 (by norm_num)) q))
  have hcP : xG 0 ^ a * k ∈ P0G := mul_mem (pow_mem (ThreeQRel.v_mem 0) a) hkP
  have hform : ThreeQRel.threeForm omegaZ (relG.coord ⟨_, hcP⟩) = 0 := by
    funext j
    have h1 := (relG.commute_iff ⟨_, hcP⟩ ⟨xG j, ThreeQRel.v_mem j⟩).1
      (Subtype.ext (hc _ (ThreeQRel.v_mem j)))
    rw [coord_xG] at h1
    simpa [ThreeQRel.threePair, Pi.single_apply] using h1
  have h0 : relG.coord ⟨_, hcP⟩ = 0 := by
    apply relG.threeForm_injective
    rw [hform]
    funext j
    simp [ThreeQRel.threeForm]
  exact (relG.coord_eq_zero_iff _).1 h0

end CFSG.RankThree.Native.ONTriple
