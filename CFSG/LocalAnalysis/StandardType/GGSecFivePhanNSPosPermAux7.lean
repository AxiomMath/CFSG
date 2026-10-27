module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

theorem ggNSPosPA_pow_eq_pow_iff {K : Type} [Field K] {p : ℕ} {ζ : Kˣ} (hζ : orderOf ζ = p)
    (m n : ℕ) : ζ ^ m = ζ ^ n ↔ (m : ZMod p) = (n : ZMod p) := by
  rw [pow_eq_pow_iff_modEq, hζ, ZMod.natCast_eq_natCast_iff]

theorem ggNSPosPA_permSU_inv_eq_permutationGL {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (ggPermSU (K := K) (f := f) σ⁻¹ : GL (Fin n) K) = TauCeti.permutationGL σ := by
  apply Units.ext
  rw [TauCeti.permutationGL_coe]
  rfl

theorem ggNSPosPA_permAutHom_eq_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) {σ : Equiv.Perm (Fin n)}
    (hσ : ggNSPosPA_permAutHom h hd σ = 1) : σ = 1 := by
  classical
  obtain ⟨ζ, hζ, hζq⟩ := ggNSPosPA_exists_zeta h
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  by_contra hne
  have hρ : σ⁻¹ ≠ 1 := by simpa [inv_eq_one] using hne
  have hex : ∃ a : Fin n, σ⁻¹ a ≠ a := by
    by_contra h
    push Not at h
    exact hρ (Equiv.ext (fun i => h i))
  obtain ⟨a, ha⟩ := hex
  let b : Fin n := σ⁻¹ a
  have hba : b ≠ a := ha
  have hfix : ∀ s : ↥Bs, ψ (ggPermSU (K := K) (f := f) σ⁻¹) * (s : G) *
      (ψ (ggPermSU (K := K) (f := f) σ⁻¹))⁻¹ = s := by
    intro s
    have h1 : ((ggNSPosPA_permAutHom h hd σ : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) s = s := by
      rw [hσ]; rfl
    have h2 := congrArg Subtype.val h1
    rw [ggNSPosPA_permAutHom_apply h hd σ s] at h2
    exact h2
  let v : Fin n → ℕ := fun i => (if i = a then 1 else 0) + (if i = b then p - 1 else 0)
  have hv : p ∣ ∑ i, v i := by
    have hsum : ∑ i, v i = p := by
      have h1 : ∑ i, (if i = a then (1 : ℕ) else 0) = 1 := by
        rw [Finset.sum_ite_eq' Finset.univ a (fun _ => 1)]; simp
      have h2 : ∑ i, (if i = b then (p - 1 : ℕ) else 0) = p - 1 := by
        rw [Finset.sum_ite_eq' Finset.univ b (fun _ => p - 1)]; simp
      simp only [v, Finset.sum_add_distrib, h1, h2]
      have hp2 := h.prime.two_le
      omega
    rw [hsum]
  let t : Su K 2 f n :=
    ⟨TauCeti.diagGL (fun i => ζ ^ (v i)), ggNSPosPA_diag_mem_SUid hζp hζq hv⟩
  have ht_coe : (t : GL (Fin n) K) = TauCeti.diagGL (fun i => ζ ^ (v i)) := rfl
  have ht_diag : ∃ d : Fin n → K, (t : GL (Fin n) K) = Matrix.diagonal d ∧ ∀ i, d i ^ p = 1 := by
    refine ⟨fun i => (ζ : K) ^ (v i), ?_, ?_⟩
    · rw [ht_coe, ggNSPosPA_coe_diagGL]
      rfl
    · intro i
      rw [← pow_mul, mul_comm, pow_mul,
        show ((ζ : K) ^ p) = 1 by rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one],
        one_pow]
  have htBs : ψ t ∈ Bs := ggNSDiag_torus_le h hd t ht_diag
  let P : Su K 2 f n := ggPermSU (K := K) (f := f) σ⁻¹
  let z : Su K 2 f n := P * t * P⁻¹ * t⁻¹
  have hzψ : ψ z = 1 := by
    have hPt : ψ P * ψ t * (ψ P)⁻¹ = ψ t := hfix ⟨ψ t, htBs⟩
    have hz_eq : ψ z = (ψ P * ψ t * (ψ P)⁻¹) * (ψ t)⁻¹ := by
      show ψ (P * t * P⁻¹ * t⁻¹) = _
      simp only [map_mul, map_inv]
    rw [hz_eq, hPt, mul_inv_cancel]
  have hzscal := ggNSPosPA_scalar_of_mem_center h (h.ker hzψ)
  rw [largeEvenScalars_def, MonoidHom.mem_range] at hzscal
  obtain ⟨c, hc⟩ := hzscal
  let u : Fin n → Kˣ := fun i => ζ ^ (v (σ⁻¹ i)) * (ζ ^ (v i))⁻¹
  have hz_diag : (z : GL (Fin n) K) = TauCeti.diagGL u := by
    show (P : GL (Fin n) K) * (t : GL (Fin n) K) * (P : GL (Fin n) K)⁻¹ *
        (t : GL (Fin n) K)⁻¹ = TauCeti.diagGL u
    rw [ht_coe, show (P : GL (Fin n) K) = TauCeti.permutationGL σ from
        ggNSPosPA_permSU_inv_eq_permutationGL σ,
      TauCeti.permutationGL_mul_diagGL_mul_inv]
    rw [← map_inv, ← map_mul]
    rfl
  have hui : ∀ i, (u i : K) = (c : K) := by
    intro i
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i)
      (congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hc)
    rw [Matrix.GeneralLinearGroup.coe_scalar, hz_diag, ggNSPosPA_coe_diagGL] at h2
    simpa using h2.symm
  have hab : a ≠ b := Ne.symm hba
  have hpb : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have h1 : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
      have hnat : ((p - 1 : ℕ) + 1 : ℕ) = p := Nat.sub_add_cancel h.prime.one_le
      calc ((p - 1 : ℕ) : ZMod p) + 1 = (((p - 1 : ℕ) + 1 : ℕ) : ZMod p) := by push_cast; ring
        _ = (p : ZMod p) := by rw [hnat]
        _ = 0 := ZMod.natCast_self p
    exact eq_neg_of_add_eq_zero_left h1
  have hvcast : ∀ m : Fin n, (v m : ZMod p) =
      (if m = a then 1 else 0) + (if m = b then (p - 1 : ZMod p) else 0) := by
    intro m
    by_cases h1 : m = a <;> by_cases h2 : m = b <;> simp_all [v, hpb]
  have hconst : ∀ i, (v (σ⁻¹ i) : ZMod p) - (v i : ZMod p) =
      (v (σ⁻¹ a) : ZMod p) - (v a : ZMod p) := by
    intro i
    have he : u i = u a := by
      apply Units.ext
      rw [hui i, hui a]
    have h2 : ζ ^ (v (σ⁻¹ i) + v a) = ζ ^ (v (σ⁻¹ a) + v i) := by
      have h' : ζ ^ v (σ⁻¹ i) * (ζ ^ v i)⁻¹ = ζ ^ v (σ⁻¹ a) * (ζ ^ v a)⁻¹ := he
      have h3 : ζ ^ ((v (σ⁻¹ i) : ℤ) + v a) = ζ ^ ((v i : ℤ) + v (σ⁻¹ a)) := by
        have := congrArg (fun x : Kˣ => x * ζ ^ v i * ζ ^ v a) h'
        group at this
        exact this
      rw [← Nat.cast_add, ← Nat.cast_add, zpow_natCast, zpow_natCast,
        add_comm (v i) (v (σ⁻¹ a))] at h3
      exact h3
    have h4 := (ggNSPosPA_pow_eq_pow_iff hζ _ _).mp h2
    have h4' : (v (σ⁻¹ i) : ZMod p) + (v a : ZMod p) =
        (v (σ⁻¹ a) : ZMod p) + (v i : ZMod p) := by
      rw [← Nat.cast_add, ← Nat.cast_add]
      exact h4
    exact (sub_eq_sub_iff_add_eq_add).mpr h4'
  have hcard : ({a, b, σ a} : Finset (Fin n)).card ≤ 3 := by
    simpa using Finset.card_le_three (a := a) (b := b) (c := σ a)
  have hlt : ({a, b, σ a} : Finset (Fin n)).card < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    have h4 := h.four_le
    omega
  obtain ⟨i0, hi0⟩ : ∃ i0, i0 ∉ ({a, b, σ a} : Finset (Fin n)) := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ ({a, b, σ a} : Finset (Fin n)) :=
      fun i _ => hcon i
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h4 := h.four_le
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi0
  obtain ⟨hia, hib, hisa⟩ := hi0
  have hsa : (σ⁻¹ a : Fin n) = b := rfl
  have hb_sigma : σ b = a := by
    show σ (σ⁻¹ a) = a
    simp
  have hgamma_a : (v (σ⁻¹ a) : ZMod p) - (v a : ZMod p) = -2 := by
    have h1 : (v (σ⁻¹ a) : ZMod p) = -1 := by
      rw [hsa, hvcast b, if_neg hba, if_pos rfl]
      simp [hpb]
    have h2 : (v a : ZMod p) = 1 := by
      rw [hvcast a, if_pos rfl, if_neg (Ne.symm hba)]
      simp
    rw [h1, h2]; ring
  have hgamma_0 : (v (σ⁻¹ i0) : ZMod p) - (v i0 : ZMod p) = 0 := by
    have hsi0a : σ⁻¹ i0 ≠ a := by
      intro hcon; exact hisa (by rw [← hcon]; simp)
    have hsi0b : σ⁻¹ i0 ≠ b := by
      intro hcon
      exact hia (by
        have h2 := congrArg σ hcon
        simpa [hb_sigma] using h2)
    have h1 : (v (σ⁻¹ i0) : ZMod p) = 0 := by
      rw [hvcast (σ⁻¹ i0), if_neg hsi0a, if_neg hsi0b]; simp
    have h2 : (v i0 : ZMod p) = 0 := by
      rw [hvcast i0, if_neg hia, if_neg hib]; simp
    rw [h1, h2]; ring
  have hcontra : (-2 : ZMod p) = 0 := by
    have hh := hconst i0
    rw [hgamma_0, hgamma_a] at hh
    exact hh.symm
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h0
    exact h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp this)
  exact (neg_ne_zero.mpr hp2) hcontra

theorem ggNSPosPA_permAutHom_injective {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) :
    Function.Injective (ggNSPosPA_permAutHom h hd) := by
  intro σ τ hστ
  have h1 : ggNSPosPA_permAutHom h hd (σ * τ⁻¹) = 1 := by
    rw [map_mul, hστ, map_inv, mul_inv_cancel]
  have h2 := ggNSPosPA_permAutHom_eq_one h hd h1
  rwa [mul_inv_eq_one] at h2


noncomputable def ggNSPosPA_permAutEquiv {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) :
    Equiv.Perm (Fin n) ≃* ↥(ggAutomizer ψ.range Bs) :=
  MulEquiv.ofBijective (ggNSPosPA_permAutHom h hd)
    ⟨ggNSPosPA_permAutHom_injective h hd, ggNSPosPA_permAutHom_surjective h hd⟩

theorem ggNSPosPA_permAutEquiv_apply {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (σ : Equiv.Perm (Fin n)) (s : ↥Bs) :
    ((((ggNSPosPA_permAutEquiv h hd σ : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) s : ↥Bs) : G) =
      ψ (ggPermSU (K := K) (f := f) σ⁻¹) * (s : G) *
        (ψ (ggPermSU (K := K) (f := f) σ⁻¹))⁻¹ :=
  ggNSPosPA_permAutHom_apply h hd σ s

end CFSG.StandardType

end
