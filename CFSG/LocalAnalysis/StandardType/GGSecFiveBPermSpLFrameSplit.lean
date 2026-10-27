module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitRank
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic
import CFSG.LocalAnalysis.StandardType.GGSixLinearModelOmega
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

namespace LFrameSplit

open Matrix

private theorem lfs_cast_p_ne_zero {F : Type} [Field F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : F) ≠ 0 := by
  intro h
  have h2p : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
  exact hp2 ((hp.dvd_iff_eq (by norm_num)).mp h2p)

private theorem lfs_coprime_card_units {F : Type} [Field F]
    {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card F - 1) :
    (Nat.card Fˣ).Coprime p := by
  have h' : ¬ p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  exact Nat.coprime_comm.mpr (hp.coprime_iff_not_dvd.mpr h')

private theorem lfs_pow_surjective {F : Type} [Field F]
    {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card F - 1) :
    ∀ c : Fˣ, ∃ μ : Fˣ, μ ^ p = c := by
  intro c
  obtain ⟨μ, hμ⟩ := (powCoprime (lfs_coprime_card_units hp h)).surjective c
  exact ⟨μ, by rwa [powCoprime_apply] at hμ⟩

private theorem lfs_pow_eq_one {F : Type} [Field F]
    {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card F - 1) {ν : Fˣ} (hν : ν ^ p = 1) :
    ν = 1 := by
  have hcop := lfs_coprime_card_units hp h
  apply (powCoprime hcop).injective
  rw [powCoprime_apply, powCoprime_apply, hν, one_pow]

private theorem lfs_scalar_pow {m : ℕ} {F : Type} [Field F] (u : Fˣ) (k : ℕ) :
    GeneralLinearGroup.scalar (Fin (m + 1)) u ^ k =
      GeneralLinearGroup.scalar (Fin (m + 1)) (u ^ k) :=
  (map_pow (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (R := F)) u k).symm

private theorem lfs_normalize {m : ℕ} {F : Type} [Field F] [CharP F 2]
    {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {p : ℕ} (hp : p.Prime) {Bs : Subgroup G}
    (hBs : CFSG.Open.IsElemAbelian p Bs) (h : ¬ p ∣ Nat.card F - 1)
    {b : ↥Bs} {A : GL (Fin (m + 1)) F}
    (hA : ((b : G), A) ∈ LinFusion.ggInducedPairs ψ) :
    ∃ A' : GL (Fin (m + 1)) F,
      ((b : G), A') ∈ LinFusion.ggInducedPairs ψ ∧ A' ^ p = 1 := by
  have hb : (b : G) ^ p = 1 := hBs.2 (b : G) b.2
  have h1 : ((1 : G), A ^ p) ∈ LinFusion.ggInducedPairs ψ := by
    have hpow := (LinFusion.ggInducedPairs ψ).pow_mem hA p
    rw [Prod.pow_mk, hb] at hpow
    exact hpow
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_of_mem_ggInducedPairs_one hker h1
  obtain ⟨μ, hμ⟩ := lfs_pow_surjective hp h c
  refine ⟨GeneralLinearGroup.scalar (Fin (m + 1)) μ⁻¹ * A, ?_, ?_⟩
  · exact LinModel.scalar_mul_mem_ggInducedPairs hA μ⁻¹
  · calc (GeneralLinearGroup.scalar (Fin (m + 1)) μ⁻¹ * A) ^ p
        = (GeneralLinearGroup.scalar (Fin (m + 1)) μ⁻¹) ^ p * A ^ p :=
          Commute.mul_pow (TypeA.PGLTor.commute_scalar μ⁻¹ A) p
      _ = GeneralLinearGroup.scalar (Fin (m + 1)) ((μ⁻¹) ^ p) *
            GeneralLinearGroup.scalar (Fin (m + 1)) c := by rw [lfs_scalar_pow, hc]
      _ = GeneralLinearGroup.scalar (Fin (m + 1)) ((μ⁻¹) ^ p * c) := by rw [map_mul]
      _ = 1 := by
          rw [← hμ, inv_pow, inv_mul_cancel, map_one]

private theorem lfs_unique {m : ℕ} {F : Type} [Field F] [CharP F 2]
    {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card F - 1)
    {b : G} {A₁ A₂ : GL (Fin (m + 1)) F}
    (h₁ : (b, A₁) ∈ LinFusion.ggInducedPairs ψ)
    (h₂ : (b, A₂) ∈ LinFusion.ggInducedPairs ψ)
    (hp₁ : A₁ ^ p = 1) (hp₂ : A₂ ^ p = 1) : A₁ = A₂ := by
  obtain ⟨ν, hν⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker h₁ h₂
  have hνp : ν ^ p = 1 := by
    have h2 : GeneralLinearGroup.scalar (Fin (m + 1)) (ν ^ p) = 1 := by
      have h3 : A₂ ^ p = GeneralLinearGroup.scalar (Fin (m + 1)) (ν ^ p) := by
        calc A₂ ^ p = (GeneralLinearGroup.scalar (Fin (m + 1)) ν * A₁) ^ p := by rw [hν]
          _ = (GeneralLinearGroup.scalar (Fin (m + 1)) ν) ^ p * A₁ ^ p :=
              Commute.mul_pow (TypeA.PGLTor.commute_scalar ν A₁) p
          _ = GeneralLinearGroup.scalar (Fin (m + 1)) (ν ^ p) := by
              rw [lfs_scalar_pow, hp₁, mul_one]
      rw [h3] at hp₂
      exact hp₂
    exact TypeA.PGLTor.scalar_injective (by rw [h2, map_one])
  have hν1 : ν = 1 := lfs_pow_eq_one hp h hνp
  rw [hν, hν1, map_one, one_mul]

private theorem lfs_commute {m : ℕ} {F : Type} [Field F] [CharP F 2]
    {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card F - 1) {Bs : Subgroup G}
    (hBs : CFSG.Open.IsElemAbelian p Bs)
    {b b' : ↥Bs} {A A' : GL (Fin (m + 1)) F}
    (hA : ((b : G), A) ∈ LinFusion.ggInducedPairs ψ)
    (hA' : ((b' : G), A') ∈ LinFusion.ggInducedPairs ψ)
    (hpA' : A' ^ p = 1) : Commute A A' := by
  have hbb : (b : G) * (b' : G) = (b' : G) * (b : G) := by
    have h := (isMulCommutative_iff.mp hBs.1) b b'
    simpa using congrArg (fun x : ↥Bs => (x : G)) h
  have h1 : ((b : G) * (b' : G), A * A') ∈ LinFusion.ggInducedPairs ψ := by
    have h := (LinFusion.ggInducedPairs ψ).mul_mem hA hA'
    simpa using h
  have h2 : ((b : G) * (b' : G), A' * A) ∈ LinFusion.ggInducedPairs ψ := by
    have h0 : ((b' : G) * (b : G), A' * A) ∈ LinFusion.ggInducedPairs ψ := by
      have h := (LinFusion.ggInducedPairs ψ).mul_mem hA' hA
      simpa using h
    rwa [← hbb] at h0
  obtain ⟨ν, hν⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker h1 h2
  have hconj : A⁻¹ * A' * A = GeneralLinearGroup.scalar (Fin (m + 1)) ν * A' := by
    calc A⁻¹ * A' * A = A⁻¹ * (A' * A) := by group
      _ = A⁻¹ * (GeneralLinearGroup.scalar (Fin (m + 1)) ν * (A * A')) := by rw [hν]
      _ = GeneralLinearGroup.scalar (Fin (m + 1)) ν * A' := by
            rw [← mul_assoc (GeneralLinearGroup.scalar (Fin (m + 1)) ν) A A',
              TypeA.PGLTor.scalar_mul_comm ν A]
            group
  have hνp : ν ^ p = 1 := by
    have hconjeq : A⁻¹ * A' * A = MulAut.conj A⁻¹ A' := by
      rw [MulAut.conj_apply]
      group
    have hconjpow : (A⁻¹ * A' * A) ^ p = 1 := by
      rw [hconjeq, ← map_pow (MulAut.conj A⁻¹), hpA', map_one]
    have h2 : (GeneralLinearGroup.scalar (Fin (m + 1)) ν * A') ^ p =
        GeneralLinearGroup.scalar (Fin (m + 1)) (ν ^ p) := by
      rw [Commute.mul_pow (TypeA.PGLTor.commute_scalar ν A'), lfs_scalar_pow, hpA',
        mul_one]
    have hscalar : GeneralLinearGroup.scalar (Fin (m + 1)) (ν ^ p) = 1 := by
      rw [← h2, ← hconj]
      exact hconjpow
    exact TypeA.PGLTor.scalar_injective (by rw [hscalar, map_one])
  have hν1 : ν = 1 := lfs_pow_eq_one hp h hνp
  rw [hν1, map_one, one_mul] at hν
  exact hν.symm

theorem dvd_card_sub_one_of_ggInducedPairs {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hm : 2 ≤ m) {G : Type} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G} (hBs : CFSG.Open.IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, ∃ A : GL (Fin (m + 1)) F, (b, A) ∈ LinFusion.ggInducedPairs ψ)
    (hc : p ^ m * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card Bs) :
    p ∣ Nat.card F - 1 := by
  by_contra h
  have hK : (p : F) ≠ 0 := lfs_cast_p_ne_zero hp hp2
  have hnorm : ∀ b : ↥Bs, ∃ A : GL (Fin (m + 1)) F,
      ((b : G), A) ∈ LinFusion.ggInducedPairs ψ ∧ A ^ p = 1 := by
    intro b
    obtain ⟨A, hA⟩ := hinn (b : G) b.2
    exact lfs_normalize hker hp hBs h hA
  let theta : ↥Bs → GL (Fin (m + 1)) F := fun b => Classical.choose (hnorm b)
  have theta_mem : ∀ b : ↥Bs, ((b : G), theta b) ∈ LinFusion.ggInducedPairs ψ :=
    fun b => (Classical.choose_spec (hnorm b)).1
  have theta_pow : ∀ b : ↥Bs, theta b ^ p = 1 :=
    fun b => (Classical.choose_spec (hnorm b)).2
  have theta_mul : ∀ b b' : ↥Bs, theta (b * b') = theta b * theta b' := by
    intro b b'
    refine lfs_unique hker hp h (theta_mem (b * b')) ?_ (theta_pow (b * b')) ?_
    · have h := (LinFusion.ggInducedPairs ψ).mul_mem (theta_mem b) (theta_mem b')
      simpa using h
    · rw [Commute.mul_pow (lfs_commute hker hp h hBs (theta_mem b) (theta_mem b')
        (theta_pow b')), theta_pow b, theta_pow b', mul_one]
  let θ : ↥Bs →* GL (Fin (m + 1)) F := MonoidHom.mk' theta theta_mul
  have θ_apply : ∀ b : ↥Bs, θ b = theta b :=
    fun b => congrFun (MonoidHom.mk'_apply theta theta_mul) b
  let C : Subgroup G := Subgroup.centralizer (ψ.range : Set G)
  have hcent : ∀ b : ↥Bs, θ b = 1 → (b : G) ∈ C := by
    intro b hb
    show (b : G) ∈ Subgroup.centralizer (ψ.range : Set G)
    apply LinFusion.mem_centralizer_of_mem_ggInducedPairs_one
    have h : ((b : G), θ b) ∈ LinFusion.ggInducedPairs ψ := by
      rw [θ_apply]
      exact theta_mem b
    rw [hb] at h
    exact h
  have hcardker : Nat.card ↥θ.ker ≤ Nat.card ↥(Bs ⊓ C) := by
    let φ : ↥θ.ker → ↥(Bs ⊓ C) := fun z =>
      ⟨((z : ↥Bs) : G), by
        rw [Subgroup.mem_inf]
        exact ⟨(z : ↥Bs).2, hcent (z : ↥Bs) (MonoidHom.mem_ker.mp z.2)⟩⟩
    refine Nat.card_le_card_of_injective φ ?_
    intro z w hzw
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥(Bs ⊓ C) => (x : G)) hzw
  have hcardBs : Nat.card ↥Bs = Nat.card ↥θ.ker * Nat.card ↥θ.range :=
    (Subgroup.card_ker_mul_card_range θ).symm
  have hcardle : Nat.card ↥Bs ≤ Nat.card ↥(Bs ⊓ C) * Nat.card ↥θ.range := by
    rw [hcardBs]
    exact Nat.mul_le_mul hcardker (le_refl _)
  let S : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    (fun A : GL (Fin (m + 1)) F =>
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) '' (θ.range : Set (GL (Fin (m + 1)) F))
  have hrange_le : Nat.card ↥θ.range ≤ Nat.card S := by
    let φ : ↥θ.range → S := fun A =>
      ⟨((A : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F),
        ⟨(A : GL (Fin (m + 1)) F), A.2, rfl⟩⟩
    refine Nat.card_le_card_of_injective φ ?_
    intro A B hAB
    apply Subtype.ext
    exact Units.ext (congrArg (fun x : S => (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hAB)
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro x ⟨A, hA, rfl⟩ y ⟨B, hB, rfl⟩
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hA
    obtain ⟨b', rfl⟩ := MonoidHom.mem_range.mp hB
    have hcomm : Commute (θ b) (θ b') :=
      lfs_commute hker hp h hBs (theta_mem b) (theta_mem b') (theta_pow b')
    rw [θ_apply b, θ_apply b'] at hcomm ⊢
    exact hcomm.map (Units.coeHom (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
  have hpowS : ∀ x ∈ S, x ^ p = 1 := by
    rintro x ⟨A, hA, rfl⟩
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hA
    have h := theta_pow b
    rw [θ_apply b]
    simpa using congrArg (fun M : GL (Fin (m + 1)) F =>
      (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) h
  have hcountS : Nat.card S ≤ p ^ ((m + 1) / OrdPNS.ordQ F p) :=
    OrdPNS.card_le_pow_ordQ_matrix (K := F) (n := m + 1) hp hK S hcommS hpowS
  have hcount : Nat.card ↥θ.range ≤ p ^ ((m + 1) / OrdPNS.ordQ F p) :=
    le_trans hrange_le hcountS
  have hdpos : 0 < OrdPNS.ordQ F p := OrdPNS.ordQ_pos (K := F) hp hK
  have hdne1 : OrdPNS.ordQ F p ≠ 1 := by
    intro hd
    apply h
    have horder : orderOf ((Nat.card F : ℕ) : ZMod p) = 1 := by
      rw [← OrdPNS.ordQ_def F p]
      exact hd
    have hone : ((Nat.card F : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.mp horder
    have hFpos : 1 ≤ Nat.card F := by
      have hpos : 0 < Nat.card F := Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
      omega
    have hcast : ((Nat.card F - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hFpos, hone]
      simp
    exact (ZMod.natCast_eq_zero_iff (Nat.card F - 1) p).mp hcast
  have hdge2 : 2 ≤ OrdPNS.ordQ F p := by omega
  have hdiv : (m + 1) / OrdPNS.ordQ F p ≤ (m + 1) / 2 :=
    Nat.div_le_div_left (a := m + 1) hdge2 (by norm_num)
  have hcount' : Nat.card ↥θ.range ≤ p ^ ((m + 1) / 2) :=
    le_trans hcount (Nat.pow_le_pow_right hp.pos hdiv)
  have hpm : p ^ m * Nat.card ↥(Bs ⊓ C) ≤
      Nat.card ↥(Bs ⊓ C) * p ^ ((m + 1) / 2) := by
    calc p ^ m * Nat.card ↥(Bs ⊓ C) ≤ Nat.card ↥Bs := hc
      _ ≤ Nat.card ↥(Bs ⊓ C) * Nat.card ↥θ.range := hcardle
      _ ≤ Nat.card ↥(Bs ⊓ C) * p ^ ((m + 1) / 2) :=
          Nat.mul_le_mul (le_refl _) hcount'
  have hCpos : 0 < Nat.card ↥(Bs ⊓ C) :=
    Nat.card_pos_iff.mpr ⟨⟨1, one_mem _⟩, inferInstance⟩
  have hpm' : p ^ m ≤ p ^ ((m + 1) / 2) := by
    rw [Nat.mul_comm (Nat.card ↥(Bs ⊓ C)) (p ^ ((m + 1) / 2))] at hpm
    exact Nat.le_of_mul_le_mul_right hpm hCpos
  have hmle : m ≤ (m + 1) / 2 := by
    by_contra hlt
    exact absurd hpm' (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt
      (Nat.lt_of_not_le hlt)))
  have hlt : (m + 1) / 2 < m := by omega
  exact absurd hmle (not_le.mpr hlt)

end LFrameSplit

end CFSG.StandardType

end
