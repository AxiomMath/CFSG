module

public import CFSG.RankThree.PartOne.N143.JTorus
public import CFSG.RankThree.PartOne.N143.JBlock
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor IsZeta diagSL tSep tNon permSL permSL_inv ent ent_ext
  ent_mul_diagSL ent_diagSL_mul nonreg)
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem conj_eq_self_of_mem_center {z : X} (hz : z ∈ Subgroup.center X) (g : X) :
    g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]

end Generic

section Vec

variable {K : Type} [Field K]

theorem diagSL_congr {v w : Fin 3 → Kˣ} (h : v = w) (hv : ∏ i, v i = 1) (hw : ∏ i, w i = 1) :
    diagSL v hv = diagSL w hw := by
  subst h
  rfl

theorem permVec_permVec (σ τ : Equiv.Perm (Fin 3)) (v : Fin 3 → Kˣ) :
    permVec σ (permVec τ v) = permVec (σ * τ) v := by
  funext i
  simp [permVec, mul_inv_rev]

theorem permVec_one (v : Fin 3 → Kˣ) : permVec 1 v = v := by
  funext i
  simp [permVec]

theorem conj_pow_diagSL {p : ℕ} {m : SL3 K} {σ : Equiv.Perm (Fin 3)}
    (hσ : ∀ (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1), (∀ i, v i ^ p = 1) →
      m * diagSL v hv * m⁻¹ = diagSL (permVec σ v) (prod_permVec σ hv))
    (n : ℕ) (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) (hv1 : ∀ i, v i ^ p = 1) :
    m ^ n * diagSL v hv * (m ^ n)⁻¹ = diagSL (permVec (σ ^ n) v) (prod_permVec (σ ^ n) hv) := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, inv_one, mul_one]
    exact diagSL_congr (permVec_one v).symm _ _
  | succ n ih =>
    have e1 : m ^ (n + 1) * diagSL v hv * (m ^ (n + 1))⁻¹ =
        m * (m ^ n * diagSL v hv * (m ^ n)⁻¹) * m⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      simp only [mul_assoc]
    rw [e1, ih, hσ (permVec (σ ^ n) v) (prod_permVec (σ ^ n) hv) (fun i => hv1 _)]
    exact diagSL_congr (by rw [permVec_permVec, pow_succ']) _ _

end Vec

section Cover

variable {G : Type} [Group G] {p : ℕ} {A J : Subgroup G} {K : Type} [Field K] {ρ : SL3 K →* G}

theorem map_conj_permSL_Tor [CharP K 2] [Finite K] (τ : Equiv.Perm (Fin 3)) :
    (Tor p K).map (MulAut.conj (permSL τ)).toMonoidHom = Tor p K := by
  have hP : permSL τ ∈ Subgroup.normalizer (Tor p K : Set (SL3 K)) := permSL_mem_normalizer_Tor τ
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hP x).1 hx
  · intro hy
    refine ⟨(permSL τ)⁻¹ * y * permSL τ, ?_, by group⟩
    have hP' := Subgroup.inv_mem _ hP
    have := (Subgroup.mem_normalizer_iff.1 hP' y).1 hy
    simpa using this

theorem IsPSL3Cover.conjPerm [CharP K 2] [Finite K] (hρ : IsPSL3Cover p A J ρ)
    (τ : Equiv.Perm (Fin 3)) :
    IsPSL3Cover p A J (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom) := by
  have hker : (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom).ker = ρ.ker := by
    ext s
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hs
      have hz : permSL τ * s * (permSL τ)⁻¹ ∈ Subgroup.center (SL3 K) :=
        hρ.ker_central (MonoidHom.mem_ker.2 hs)
      have h1 := conj_eq_self_of_mem_center hz (permSL τ)⁻¹
      have h2 : (permSL τ)⁻¹ * (permSL τ * s * (permSL τ)⁻¹) * ((permSL τ)⁻¹)⁻¹ = s := by group
      rw [h2] at h1
      rw [← h1] at hs
      exact hs
    · intro hs
      have hz : s ∈ Subgroup.center (SL3 K) := hρ.ker_central (MonoidHom.mem_ker.2 hs)
      rw [conj_eq_self_of_mem_center hz]
      exact hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hρ.range_eq]
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨s, rfl⟩
      refine ⟨(permSL τ)⁻¹ * s * permSL τ, ?_⟩
      congr 1
      group
  · rw [hker]
    exact hρ.ker_central
  · rw [hker]
    exact hρ.ker_coprime
  · rw [← Subgroup.map_map, map_conj_permSL_Tor, hρ.map_torus]

end Cover

section Decomp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  {ρ : SL3 K →* G}

theorem IsPSL3Cover.exists_decomp (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {a : G}
    (ha : a ∈ A) : ∃ (i : ℤ) (d : SL3 K), d ∈ Tor p K ∧ a = c ^ i * ρ d := by
  rw [h.A_eq.1] at ha
  obtain ⟨k, hk, t', ht', rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
    (fun k hk l hl => Sec12Three.mul_comm_of_mem_A h.hyp
      ((Subgroup.zpowers_le).2 h.hyp.c_mem hk) (Tof_le A J hl)) ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 (hρ.map_torus ▸ ht' : t' ∈ (Tor p K).map ρ)
  exact ⟨i, d, hd, rfl⟩

theorem IsPSL3Cover.conj_decomp (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) (m : SL3 K) (i : ℤ)
    (d : SL3 K) : ρ m * (c ^ i * ρ d) * (ρ m)⁻¹ = c ^ i * ρ (m * d * m⁻¹) := by
  have hmJ : ρ m ∈ J := hρ.range_eq ▸ ⟨m, rfl⟩
  have hc : c * ρ m = ρ m * c := Sec12Three.comm_c_L h.hyp (ρ m) hmJ
  have hci : c ^ i * ρ m = ρ m * c ^ i := (Commute.zpow_left (hc : Commute c (ρ m)) i).eq
  calc ρ m * (c ^ i * ρ d) * (ρ m)⁻¹ = (ρ m * c ^ i) * ρ d * (ρ m)⁻¹ := by simp only [mul_assoc]
    _ = (c ^ i * ρ m) * ρ d * (ρ m)⁻¹ := by rw [← hci]
    _ = c ^ i * (ρ m * ρ d * (ρ m)⁻¹) := by simp only [mul_assoc]
    _ = c ^ i * ρ (m * d * m⁻¹) := by rw [map_mul, map_mul, map_inv]

omit [Finite G] in
theorem IsPSL3Cover.map_mem_A (hρ : IsPSL3Cover p A J ρ) {d : SL3 K} (hd : d ∈ Tor p K) :
    ρ d ∈ A :=
  Tof_le A J (hρ.map_torus ▸ Subgroup.mem_map_of_mem ρ hd)

theorem JGood.comm_A (h : JGood p A c J) {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  Sec12Three.mul_comm_of_mem_A h.hyp ha hb

theorem JGood.zpow_c_mem (h : JGood p A c J) (i : ℤ) : c ^ i ∈ A :=
  A.zpow_mem h.hyp.c_mem i

end Decomp

section Single

variable {G : Type} [Group G] {p : ℕ} {A J : Subgroup G} {K : Type} [Field K] {ρ : SL3 K →* G}

theorem IsPSL3Cover.mem_inf_centralizer_single (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {d : SL3 K}
    (hd : d ^ p = 1) {x : G} :
    x ∈ J ⊓ Subgroup.centralizer ({ρ d} : Set G) ↔
      ∃ m ∈ Subgroup.centralizer ({d} : Set (SL3 K)), ρ m = x := by
  constructor
  · rintro ⟨hxJ, hxC⟩
    rw [← hρ.range_eq] at hxJ
    obtain ⟨m, rfl⟩ := hxJ
    refine ⟨m, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxC' : ρ m * ρ d = ρ d * ρ m := Subgroup.mem_centralizer_singleton_iff.1 hxC
    exact (hρ.commute_of_commute hp hd hxC'.symm).symm
  · rintro ⟨m, hm, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hρ.range_eq ▸ ⟨m, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 hm]

theorem IsPSL3Cover.inf_centralizer_tNon (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) :
    J ⊓ Subgroup.centralizer ({ρ (tNon ζ 2)} : Set G) = (Zc (K := K) ζ).map ρ := by
  have hpow : (tNon ζ 2 : SL3 K) ^ p = 1 := Tor_pow_eq_one (KFOUT3.tNon_mem hζ 2)
  ext x
  exact (hρ.mem_inf_centralizer_single hp hpow).trans Subgroup.mem_map.symm

theorem IsPSL3Cover.commutator_inf_centralizer_tNon [CharP K 2] (hp : p.Prime)
    (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ} (hζ : IsZeta p ζ) (h4 : 4 ≤ Nat.card K) :
    ⁅J ⊓ Subgroup.centralizer ({ρ (tNon ζ 2)} : Set G),
        J ⊓ Subgroup.centralizer ({ρ (tNon ζ 2)} : Set G)⁆ =
      (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range.map ρ := by
  rw [hρ.inf_centralizer_tNon hp hζ, ← Subgroup.map_commutator, commutator_Zc_eq hζ h4]

@[expose] def blkφ (ρ : SL3 K →* G) : Matrix.SpecialLinearGroup (Fin 2) K →* G := ρ.comp blkSL

theorem blkφ_apply (M : Matrix.SpecialLinearGroup (Fin 2) K) : blkφ ρ M = ρ (blkSL M) := rfl

theorem blkφ_injective (hρ : IsPSL3Cover p A J ρ) : Function.Injective (blkφ ρ) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  exact eq_one_of_blkSL_mem_center (hρ.ker_central (MonoidHom.mem_ker.2 hM))

theorem map_blkSL_range_eq :
    (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range.map ρ = (blkφ ρ).range := by
  ext x
  constructor
  · rintro ⟨y, ⟨M, rfl⟩, rfl⟩
    exact ⟨M, rfl⟩
  · rintro ⟨M, rfl⟩
    exact ⟨blkSL M, ⟨M, rfl⟩, rfl⟩

end Single

section Weyl

variable {G : Type} [Group G]

theorem mem_autFixedInG_normalizerMonoidHom {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G)) {a : G} :
    a ∈ autFixedInG A (A.normalizerMonoidHom ⟨x, hx⟩) ↔ a ∈ A ∧ x * a * x⁻¹ = a := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.2, congrArg (fun y : A => (y : G)) he⟩
  · rintro ⟨ha, h⟩
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    apply Subtype.ext
    exact h

theorem normalizerMonoidHom_pow_eq_one {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G)) (n : ℕ)
    (h : ∀ a ∈ A, x ^ n * a * (x ^ n)⁻¹ = a) : (A.normalizerMonoidHom ⟨x, hx⟩) ^ n = 1 := by
  rw [← map_pow]
  ext a
  show x ^ n * (a : G) * (x ^ n)⁻¹ = (a : G)
  exact h a a.2

end Weyl

theorem swap01_two : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide

theorem three_le_of_dvd_pred {p f : ℕ} (h5 : 5 ≤ p) (hf1 : 1 ≤ f) (hf : p ∣ 2 ^ f - 1) :
    3 ≤ f := by
  by_contra hlt
  have hf12 : f = 1 ∨ f = 2 := by omega
  rcases hf12 with rfl | rfl
  · have := Nat.le_of_dvd (by norm_num) hf
    norm_num at this
    omega
  · have := Nat.le_of_dvd (by norm_num) hf
    norm_num at this
    omega

end CFSG.RankThree.PartOne.N143
