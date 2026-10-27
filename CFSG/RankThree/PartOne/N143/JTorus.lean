module

public import CFSG.RankThree.PartOne.N143.JSetup
public import CFSG.RankThree.PartOne.KFOUT3.Std
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.N143.JFacts

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG
open CFSG.RankThree.PartOne.KFU (IsCentralPQuot torusSU mem_torusSU_iff isDiag_diagU torusSU_char_distinct
  exists_perm_of_normalizes)
open CFSG.RankThree.PartOne.KFOUT3 (SL3 PSL3 Tor IsZeta diagSL tSep tSep_ne tSep_mem diagSL_mem_Tor
  mem_Tor_iff ent_mul_diagSL ent_diagSL_mul ent permSL permSL_inv ent_permSL_conj ent_ext)
open Matrix
open scoped commutatorElement

section Basic

variable {K : Type} [Field K]

theorem Tor_pow_eq_one {p : ℕ} {t : SL3 K} (ht : t ∈ Tor p K) : t ^ p = 1 := by
  obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 ht
  have hpow : ((fun i => (v i : K)) ^ p : Fin 3 → K) = 1 := funext fun i => by
    have := congrArg (fun u : Kˣ => (u : K)) (hv1 i)
    simpa using this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    KFOUT3.coe_diagSL, Matrix.diagonal_pow, hpow]
  exact Matrix.diagonal_one

theorem isDiag_of_mem_centralizer_Tor {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) {m : SL3 K}
    (hm : m ∈ Subgroup.centralizer (Tor p K : Set (SL3 K))) {i j : Fin 3} (hij : i ≠ j) :
    ent m i j = 0 := by
  have hv0 : ∏ k, tSep ζ i j k = 1 := KFU.prod_torusElt i j ζ
  have ht : diagSL (tSep ζ i j) hv0 ∈ Tor p K := tSep_mem hζ hij
  have hc := Subgroup.mem_centralizer_iff.1 hm _ ht
  have h1 := congrArg (fun y : SL3 K => ent y i j) hc
  simp only [ent_mul_diagSL, ent_diagSL_mul] at h1
  have hne : (tSep ζ i j i : K) ≠ (tSep ζ i j j : K) := fun h => tSep_ne hζ hij (Units.ext h)
  have : ent m i j * ((tSep ζ i j j : K) - (tSep ζ i j i : K)) = 0 := by linear_combination -h1
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd (sub_eq_zero.1 h).symm hne

theorem commute_of_mem_centralizer_Tor {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) {m n : SL3 K}
    (hm : m ∈ Subgroup.centralizer (Tor p K : Set (SL3 K)))
    (hn : n ∈ Subgroup.centralizer (Tor p K : Set (SL3 K))) : m * n = n * m := by
  have hdm : (m : Matrix (Fin 3) (Fin 3) K).IsDiag := fun i j hij =>
    isDiag_of_mem_centralizer_Tor hζ hm hij
  have hdn : (n : Matrix (Fin 3) (Fin 3) K).IsDiag := fun i j hij =>
    isDiag_of_mem_centralizer_Tor hζ hn hij
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← hdm.diagonal_diag,
    ← hdn.diagonal_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end Basic

section Dict

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G}
  {K : Type} [Field K] [Finite K] {ρ : SL3 K →* G}

omit [Finite G] [Finite K] in
theorem IsPSL3Cover.isCentralPQuot (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) :
    IsCentralPQuot p ρ.rangeRestrict := by
  refine ⟨ρ.rangeRestrict_surjective, ?_, ?_⟩
  · rw [MonoidHom.ker_rangeRestrict]
    exact hρ.ker_central
  · rw [MonoidHom.ker_rangeRestrict]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hρ.ker_coprime

omit [Finite G] [Finite K] in
theorem IsPSL3Cover.eq_of_map_eq (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {a b : SL3 K}
    (ha : a ^ p = 1) (hb : b ^ p = 1) (h : ρ a = ρ b) : a = b :=
  (hρ.isCentralPQuot hp).eq_of_map_eq ha hb (Subtype.ext h)

omit [Finite G] [Finite K] in
theorem IsPSL3Cover.commute_of_commute (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {a b : SL3 K}
    (ha : a ^ p = 1) (hab : ρ a * ρ b = ρ b * ρ a) : a * b = b * a :=
  (hρ.isCentralPQuot hp).commute_of_map_commute ha (Subtype.ext hab)

omit [Finite K] in
theorem IsPSL3Cover.mem_inf_centralizer_iff (hp : p.Prime) (h : JGood p A c J)
    (hρ : IsPSL3Cover p A J ρ) {x : G} :
    x ∈ J ⊓ Subgroup.centralizer (A : Set G) ↔
      ∃ m ∈ Subgroup.centralizer (Tor p K : Set (SL3 K)), ρ m = x := by
  constructor
  · rintro ⟨hxJ, hxC⟩
    rw [← hρ.range_eq] at hxJ
    obtain ⟨m, rfl⟩ := hxJ
    refine ⟨m, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htA : ρ t ∈ A :=
      Tof_le A J (hρ.map_torus ▸ Subgroup.mem_map_of_mem ρ ht)
    have hcomm : ρ t * ρ m = ρ m * ρ t := Subgroup.mem_centralizer_iff.1 hxC (ρ t) htA
    exact hρ.commute_of_commute hp (Tor_pow_eq_one ht) hcomm
  · rintro ⟨m, hm, rfl⟩
    have hmJ : ρ m ∈ J := hρ.range_eq ▸ ⟨m, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hmJ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [h.A_eq.1] at ha
    obtain ⟨k, hk, t', ht', rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
      (fun k hk l hl => Sec12Three.mul_comm_of_mem_A h.hyp
        ((Subgroup.zpowers_le).2 h.hyp.c_mem hk) (Tof_le A J hl)) ha
    have hc : c * ρ m = ρ m * c := Sec12Three.comm_c_L h.hyp (ρ m) hmJ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have h1 : c ^ i * ρ m = ρ m * c ^ i := (Commute.zpow_left (hc : Commute c (ρ m)) i).eq
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 (hρ.map_torus ▸ ht' : t' ∈ (Tor p K).map ρ)
    have h2 : ρ t * ρ m = ρ m * ρ t := by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hm t ht]
    calc c ^ i * ρ t * ρ m = c ^ i * (ρ t * ρ m) := by rw [mul_assoc]
      _ = c ^ i * (ρ m * ρ t) := by rw [h2]
      _ = (c ^ i * ρ m) * ρ t := by rw [mul_assoc]
      _ = (ρ m * c ^ i) * ρ t := by rw [h1]
      _ = ρ m * (c ^ i * ρ t) := by rw [mul_assoc]

omit [Finite G] in
theorem conj_mem_Tof_of_mem {x : G} (hx : x ∈ J ⊓ torusNormalizer A) {t : G}
    (ht : t ∈ Tof A J) : x * t * x⁻¹ ∈ Tof A J := by
  have hle : (Tof A J).map (MulAut.conj x).toMonoidHom ≤ Tof A J := by
    rw [Subgroup.map_le_iff_le_comap, Tof, Subgroup.commutator_le]
    intro a ha y hy
    show x * ⁅a, y⁆ * x⁻¹ ∈ ⁅A, J ⊓ torusNormalizer A⁆
    have e : x * ⁅a, y⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * y * x⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Subgroup.commutator_mem_commutator ?_ ?_
    · exact (Subgroup.mem_normalizer_iff.1 hx.2 a).1 ha
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx)
  exact hle ⟨t, ht, rfl⟩

theorem IsPSL3Cover.mem_inf_normalizer_iff (hp : p.Prime) (h : JGood p A c J)
    (hρ : IsPSL3Cover p A J ρ) {x : G} :
    x ∈ J ⊓ torusNormalizer A ↔
      ∃ m ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)), ρ m = x := by
  constructor
  · intro hx
    have hxJ : x ∈ J := hx.1
    rw [← hρ.range_eq] at hxJ
    obtain ⟨m, rfl⟩ := hxJ
    refine ⟨m, ?_, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    have ht' : t ∈ Tor p K := ht
    show m * t * m⁻¹ ∈ (Tor p K : Set (SL3 K))
    have h1 : ρ m * ρ t * (ρ m)⁻¹ ∈ Tof A J :=
      conj_mem_Tof_of_mem hx (hρ.map_torus ▸ Subgroup.mem_map_of_mem ρ ht')
    obtain ⟨s, hs, hsρ⟩ := Subgroup.mem_map.1 (hρ.map_torus.symm ▸ h1 : _ ∈ (Tor p K).map ρ)
    have hpow : (m * t * m⁻¹) ^ p = 1 := by
      rw [conj_pow, Tor_pow_eq_one ht', mul_one, mul_inv_cancel]
    have : m * t * m⁻¹ = s := hρ.eq_of_map_eq hp hpow (Tor_pow_eq_one hs) (by
      rw [map_mul, map_mul, map_inv]
      exact hsρ.symm)
    rw [this]
    exact hs
  · rintro ⟨m, hm, rfl⟩
    have hmJ : ρ m ∈ J := hρ.range_eq ▸ ⟨m, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hmJ, ?_⟩
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have ha' : a ∈ A := ha
    show ρ m * a * (ρ m)⁻¹ ∈ (A : Set G)
    rw [h.A_eq.1] at ha'
    obtain ⟨k, hk, t', ht', rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
      (fun k hk l hl => Sec12Three.mul_comm_of_mem_A h.hyp
        ((Subgroup.zpowers_le).2 h.hyp.c_mem hk) (Tof_le A J hl)) ha'
    have hc : c * ρ m = ρ m * c := Sec12Three.comm_c_L h.hyp (ρ m) hmJ
    have hck : ρ m * k * (ρ m)⁻¹ = k := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      have : c ^ i * ρ m = ρ m * c ^ i := (Commute.zpow_left (hc : Commute c (ρ m)) i).eq
      rw [mul_inv_eq_iff_eq_mul, ← this]
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 (hρ.map_torus ▸ ht' : t' ∈ (Tor p K).map ρ)
    have hmt : m * t * m⁻¹ ∈ Tor p K := by
      have := (Subgroup.mem_normalizer_iff.1 hm t).1 ht
      exact this
    have : ρ m * (k * ρ t) * (ρ m)⁻¹ = k * ρ (m * t * m⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      calc ρ m * (k * ρ t) * (ρ m)⁻¹ = (ρ m * k * (ρ m)⁻¹) * (ρ m * ρ t * (ρ m)⁻¹) := by group
        _ = k * (ρ m * ρ t * (ρ m)⁻¹) := by rw [hck]
    rw [this]
    refine A.mul_mem ((Subgroup.zpowers_le).2 h.hyp.c_mem hk) ?_
    exact Tof_le A J (hρ.map_torus ▸ Subgroup.mem_map_of_mem ρ hmt)

end Dict

section Perm

variable {K : Type} [Field K]

@[expose] def permVec (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → Kˣ) : Fin 3 → Kˣ := fun i => v (σ⁻¹ i)

theorem prod_permVec (σ : Equiv.Perm (Fin 3)) {v : Fin 3 → Kˣ} (hv : ∏ i, v i = 1) :
    ∏ i, permVec σ v i = 1 := by
  rw [← hv]
  exact Equiv.prod_comp σ⁻¹ v

variable [CharP K 2]

theorem permSL_conj_diagSL (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) :
    permSL σ * diagSL v hv * (permSL σ)⁻¹ = diagSL (permVec σ v) (prod_permVec σ hv) := by
  apply ent_ext
  intro a b
  rw [ent_permSL_conj, KFOUT3.diagSL_apply, KFOUT3.diagSL_apply]
  by_cases hab : a = b
  · subst hab
    simp [permVec]
  · simp [hab]

theorem permSL_mem_normalizer_Tor [Finite K] {p : ℕ} (σ : Equiv.Perm (Fin 3)) :
    permSL σ ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) := by
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  have ht' : t ∈ Tor p K := ht
  obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 ht'
  show permSL σ * diagSL v hv * (permSL σ)⁻¹ ∈ (Tor p K : Set (SL3 K))
  rw [permSL_conj_diagSL]
  exact diagSL_mem_Tor _ (fun i => hv1 _) _

theorem permSL_pow_three (σ : Equiv.Perm (Fin 3)) (h : σ ^ 3 = 1) :
    (permSL σ : SL3 K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, KFOUT3.coe_permSL]
  have h1 : (σ⁻¹).permMatrix K = Matrix.permMatrixHom (R := K) σ := rfl
  rw [h1, ← map_pow, h, map_one]
  rfl

theorem rotate_not_commute {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) (hv : ∏ i, tSep ζ 0 1 i = 1) :
    permSL (finRotate 3) * diagSL (tSep ζ 0 1) hv * (permSL (finRotate 3))⁻¹ ≠
      diagSL (tSep ζ 0 1) hv := by
  intro h2
  have h3 : ent (permSL (finRotate 3) * diagSL (tSep ζ 0 1) hv * (permSL (finRotate 3))⁻¹) 0 0 =
      ent (diagSL (tSep ζ 0 1) hv) 0 0 := by rw [h2]
  rw [ent_permSL_conj, KFOUT3.diagSL_apply, KFOUT3.diagSL_apply] at h3
  have e1 : (finRotate 3)⁻¹ 0 = 2 := by decide
  have e2 : tSep ζ 0 1 2 = 1 := KFU.torusElt_apply_other (by decide) (by decide) ζ
  have e3 : tSep ζ 0 1 0 = ζ := KFU.torusElt_apply_left (by decide) ζ
  have h4 : (tSep ζ 0 1 2 : K) = (tSep ζ 0 1 0 : K) := by simpa [e1] using h3
  have h5 : tSep ζ 0 1 2 = tSep ζ 0 1 0 := Units.ext h4
  rw [e2, e3] at h5
  apply hζ.cube
  rw [← h5, one_pow]

end Perm

section X0

variable {G : Type} [Group G] [Finite G]

theorem exists_isZeta {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hdvd : p ∣ Nat.card K - 1) : ∃ ζ : Kˣ, IsZeta p ζ := by
  have : Fact p.Prime := ⟨hp⟩
  have hpu : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hdvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpu
  exact ⟨u, KFOUT3.IsZeta.of_orderOf h5 hu⟩

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)

theorem jFactX0_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    JFactX0 := by
  intro G _ _ p A c J h
  classical
  obtain ⟨f, -, hf, hm⟩ := h.model
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hGA h hf hm
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have hchar : CharP K 2 := charP_two_of_card hK
  obtain ⟨ζ, hζ⟩ := exists_isZeta hp h5 (by rw [hK]; exact hf)
  have hm_norm : permSL (finRotate 3) ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) :=
    permSL_mem_normalizer_Tor _
  have hx : ρ (permSL (finRotate 3)) ∈ J ⊓ torusNormalizer A :=
    (hρ.mem_inf_normalizer_iff hp h).2 ⟨_, hm_norm, rfl⟩
  refine ⟨ρ (permSL (finRotate 3)), hx, ?_, ?_⟩
  · rw [← map_pow, permSL_pow_three _ (by decide), map_one]
  · have ht : diagSL (tSep ζ 0 1) (KFU.prod_torusElt 0 1 ζ) ∈ Tor p K := tSep_mem hζ (by decide)
    refine ⟨ρ (diagSL (tSep ζ 0 1) (KFU.prod_torusElt 0 1 ζ)),
      Tof_le A J (hρ.map_torus ▸ Subgroup.mem_map_of_mem ρ ht), ?_⟩
    intro hcon
    have h1 : ρ (permSL (finRotate 3) * diagSL (tSep ζ 0 1) (KFU.prod_torusElt 0 1 ζ) *
        (permSL (finRotate 3))⁻¹) = ρ (diagSL (tSep ζ 0 1) (KFU.prod_torusElt 0 1 ζ)) := by
      rw [map_mul, map_mul, map_inv]
      exact hcon
    exact rotate_not_commute hζ (KFU.prod_torusElt 0 1 ζ)
      (hρ.eq_of_map_eq hp (by rw [conj_pow, Tor_pow_eq_one ht, mul_one, mul_inv_cancel])
        (Tor_pow_eq_one ht) h1)

end X0

section NormalForm

variable {K : Type} [Field K]

theorem exists_Tor_of_mem_torusSU {p : ℕ} {g : GL (Fin 3) K} (hg : g ∈ torusSU p 3 K) :
    ∃ x ∈ Tor p K, Matrix.SpecialLinearGroup.toGL x = g := by
  obtain ⟨d, hd1, hd, rfl⟩ := mem_torusSU_iff.1 hg
  refine ⟨diagSL d hd, diagSL_mem_Tor d hd1 hd, ?_⟩
  apply Units.ext
  rfl

theorem exists_perm_conj_Tor {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) {m : SL3 K}
    (hm : m ∈ Subgroup.normalizer (Tor p K : Set (SL3 K))) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
      m * diagSL v hv * m⁻¹ = diagSL (permVec σ v) (prod_permVec σ hv) := by
  classical
  have hdiag : ∀ g ∈ torusSU p 3 K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro g hg
    obtain ⟨d, -, -, rfl⟩ := mem_torusSU_iff.1 hg
    exact isDiag_diagU d
  have hdist : ∀ i j : Fin 3, i ≠ j → ∃ g ∈ torusSU p 3 K, KFU.ent g i i ≠ KFU.ent g j j :=
    fun i j hij => torusSU_char_distinct hζ.pow hζ.sq hij
  have hTT : ∀ x ∈ Tor p K, m * x * m⁻¹ ∈ Tor p K := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hm x).1 hx
  have hTT' : ∀ x ∈ Tor p K, m⁻¹ * x * m ∈ Tor p K := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Tor p K : Set (SL3 K))).inv_mem hm)
      x).1 hx
    simpa using this
  have hw : ∀ g ∈ torusSU p 3 K, Matrix.SpecialLinearGroup.toGL m * g *
      (Matrix.SpecialLinearGroup.toGL m)⁻¹ ∈ torusSU p 3 K := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := exists_Tor_of_mem_torusSU hg
    have := hTT x hx
    rw [← map_inv, ← map_mul, ← map_mul]
    exact this
  have hinv : ∀ g ∈ torusSU p 3 K, (Matrix.SpecialLinearGroup.toGL m)⁻¹ * g *
      Matrix.SpecialLinearGroup.toGL m ∈ torusSU p 3 K := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := exists_Tor_of_mem_torusSU hg
    have := hTT' x hx
    rw [← map_inv, ← map_mul, ← map_mul]
    exact this
  obtain ⟨σ, -, -, hσ⟩ := exists_perm_of_normalizes (torusSU p 3 K) hdiag hdist hw hinv
  refine ⟨σ, fun v hv hv1 => ?_⟩
  have ht : diagSL v hv ∈ Tor p K := diagSL_mem_Tor v hv1 hv
  have hconj : m * diagSL v hv * m⁻¹ ∈ Tor p K := hTT _ ht
  obtain ⟨u, hu1, hu, hu'⟩ := mem_Tor_iff.1 hconj
  apply ent_ext
  intro a b
  rw [hu', KFOUT3.diagSL_apply, KFOUT3.diagSL_apply]
  by_cases hab : a = b
  · subst hab
    have h1 := hσ (Matrix.SpecialLinearGroup.toGL (diagSL v hv))
      (by
        refine mem_torusSU_iff.2 ⟨v, hv1, hv, ?_⟩
        apply Units.ext
        rfl) (σ⁻¹ a)
    have e1 : Matrix.SpecialLinearGroup.toGL m * Matrix.SpecialLinearGroup.toGL (diagSL v hv) *
        (Matrix.SpecialLinearGroup.toGL m)⁻¹ = Matrix.SpecialLinearGroup.toGL (diagSL u hu) := by
      rw [← map_inv, ← map_mul, ← map_mul, hu']
    have e0 : σ (σ⁻¹ a) = a := Equiv.apply_symm_apply σ a
    rw [e1, e0] at h1
    have e2 : ((u a : Kˣ) : K) = ((v (σ⁻¹ a) : Kˣ) : K) := by
      simpa [KFU.ent, KFOUT3.coe_diagSL, Matrix.diagonal_apply_eq] using h1
    have e3 : u a = v (σ⁻¹ a) := Units.ext e2
    simp [permVec, e3]
  · simp [hab]

end NormalForm

end CFSG.RankThree.PartOne.N143
