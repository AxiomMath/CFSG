module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTableP
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigB
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS1
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS4
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS5
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS6
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS8

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem qtwoDB44_case_symplectic_of (hm : 6 ≤ m) {N J₁ J₂ : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (N : Set G)) (eN : ↥N ≃* StatedSp (m - 1) (ZMod 2))
    (τ : Multiplicative (DVec m) →* ↥N)
    (hτker : ∀ v : DVec m, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0)
    (hconj : ∀ (s : ↥Bs) (n : ↥N), ggGamma N hBsN s n =
      τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) * n *
        (τ (Multiplicative.ofAdd (βL (Additive.ofMul s))))⁻¹)
    (hscτ : ∀ z : ↥N,
      (∀ v : DVec m, z * τ (Multiplicative.ofAdd v) = τ (Multiplicative.ofAdd v) * z) →
        z ^ 3 = 1 → z ∈ τ.range)
    (hWτ : ∀ w ∈ dEvenStab m (Pi.single c 1), ∃ y : ↥N, ∀ v : DVec m,
      y * τ (Multiplicative.ofAdd v) * y⁻¹ = τ (Multiplicative.ofAdd (w v)))
    (hJ₁N : J₁ ≤ N) (hJ₁p : J₁ ≤ ⁅J₁, J₁⁆) {u₁ : DVec m} (hu₁ : ∀ i, i ≠ c → u₁ i ≠ 0)
    (hJ1c : ∀ n : ↥N, (n : G) ∈ J₁ →
      n * τ (Multiplicative.ofAdd u₁) = τ (Multiplicative.ofAdd u₁) * n)
    (hJ₂N : J₂ ≤ N) (hJ₂p : J₂ ≤ ⁅J₂, J₂⁆) {u₂ : DVec m} (hu₂ : ∀ i, i ≠ c → u₂ i ≠ 0)
    (hJ2c : ∀ n : ↥N, (n : G) ∈ J₂ →
      n * τ (Multiplicative.ofAdd u₂) = τ (Multiplicative.ofAdd u₂) * n)
    {s₀ : ↥Bs} (hs₀ : ∃ i, i ≠ c ∧ βL (Additive.ofMul s₀) i ≠ 0) :
    ∃ Y : Subgroup G, J₁ ≤ Y ∧ J₂ ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
        Subgroup.center ↥Y = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let τP : Multiplicative (DVec m) →* StatedSp (m - 1) (ZMod 2) := eN.toMonoidHom.comp τ
  have hτPker : ∀ v : DVec m, τP (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0 := by
    intro v
    rw [← hτker v]
    exact MulEquiv.map_eq_one_iff eN
  have hscP : ∀ z : StatedSp (m - 1) (ZMod 2),
      (∀ v : DVec m, z * τP (Multiplicative.ofAdd v) = τP (Multiplicative.ofAdd v) * z) →
        z ^ 3 = 1 → z ∈ τP.range := by
    intro z hz hz3
    obtain ⟨n, rfl⟩ := eN.surjective z
    have hn : ∀ v : DVec m, n * τ (Multiplicative.ofAdd v) = τ (Multiplicative.ofAdd v) * n :=
      fun v => eN.injective (by simpa [τP] using hz v)
    obtain ⟨u, hu⟩ := hscτ n hn (eN.injective (by rw [map_pow, hz3, map_one]))
    exact ⟨u, by simp [τP, hu]⟩
  have hWP : ∀ w ∈ dEvenStab m (Pi.single c 1), ∃ y : StatedSp (m - 1) (ZMod 2),
      ∀ v : DVec m, y * τP (Multiplicative.ofAdd v) * y⁻¹ =
        τP (Multiplicative.ofAdd (w v)) := by
    intro w hw
    obtain ⟨y, hy⟩ := hWτ w hw
    exact ⟨eN y, fun v => by simpa [τP] using congrArg eN (hy v)⟩
  obtain ⟨Q, hQpol, hQplus, hQinv, hQcent⟩ := qtwoDB44_core hm τP hτPker hscP hWP
  obtain ⟨ψY, hψYinj, hψY⟩ := qtwoDB44_embedding eN hQpol
  have hJ₁Y : J₁ ≤ ψY.range := by
    refine qtwoDB44_subgroup_le_range eN ψY hψY hJ₁N hJ₁p ?_
    intro n hn x
    refine hQcent u₁ hu₁ (eN n) ?_ x
    simpa [τP] using congrArg eN (hJ1c n hn)
  have hJ₂Y : J₂ ≤ ψY.range := by
    refine qtwoDB44_subgroup_le_range eN ψY hψY hJ₂N hJ₂p ?_
    intro n hn x
    refine hQcent u₂ hu₂ (eN n) ?_ x
    simpa [τP] using congrArg eN (hJ2c n hn)
  let bm : ↥Bs →* Multiplicative (DVec m) :=
    { toFun := fun s => Multiplicative.ofAdd (βL (Additive.ofMul s))
      map_one' := by simp
      map_mul' := fun s s' => by simp }
  let τBP : ↥Bs →* StatedSp (m - 1) (ZMod 2) := τP.comp bm
  have hd4 : 4 ≤ m - 1 := by omega
  have hτBPmem : ∀ s : ↥Bs, qtwoDB44_linEquiv (m - 1) (τBP s) ∈ qtwoDB44_Omega Q := by
    intro s
    refine qtwoDB44_mem_Omega_of_pow_three hd4 hQpol (hQinv (βL (Additive.ofMul s))) ?_
    have hs3 : s ^ 3 = 1 := Subtype.ext (by simpa using hBs.2 (s : G) s.2)
    rw [← map_pow, hs3, map_one]
  let βY : ↥Bs →* ↥(qtwoDB44_Omega Q) :=
    ((qtwoDB44_linEquiv (m - 1)).comp τBP).codRestrict (qtwoDB44_Omega Q) hτBPmem
  have hOle : qtwoDB44_Omega Q ≤ (qtwoDB44_linEquiv (m - 1)).range :=
    (qtwoDB44_Omega_le_orthogonalGroup Q).trans (qtwoDB44_orthogonalGroup_le_range hQpol)
  have hcompat : ∀ (s : ↥Bs) (y : ↥(qtwoDB44_Omega Q)),
      ψY (βY s * y * (βY s)⁻¹) = (s : G) * ψY y * (s : G)⁻¹ := by
    intro s y
    obtain ⟨z, hz⟩ := hOle y.2
    have hzO : qtwoDB44_linEquiv (m - 1) z ∈ qtwoDB44_Omega Q := by rw [hz]; exact y.2
    have hy : y = ⟨qtwoDB44_linEquiv (m - 1) z, hzO⟩ := Subtype.ext hz.symm
    have hconjO : qtwoDB44_linEquiv (m - 1) (τBP s * z * (τBP s)⁻¹) ∈ qtwoDB44_Omega Q := by
      rw [map_mul, map_mul, map_inv]
      exact (qtwoDB44_Omega Q).mul_mem ((qtwoDB44_Omega Q).mul_mem (hτBPmem s) hzO)
        ((qtwoDB44_Omega Q).inv_mem (hτBPmem s))
    have hprod : βY s * y * (βY s)⁻¹ =
        ⟨qtwoDB44_linEquiv (m - 1) (τBP s * z * (τBP s)⁻¹), hconjO⟩ := by
      apply Subtype.ext
      rw [hy]
      simp [βY, map_mul, map_inv]
    rw [hprod, hψY _ hconjO, hy, hψY _ hzO]
    have h1 : eN.symm (τBP s * z * (τBP s)⁻¹) =
        τ (bm s) * eN.symm z * (τ (bm s))⁻¹ := by
      simp [τBP, τP, map_mul, map_inv]
    rw [h1]
    have h2 := congrArg Subtype.val (hconj s (eN.symm z))
    rw [ggGamma_coe] at h2
    exact h2.symm
  have hne : ∃ s : ↥Bs, βY s ≠ 1 := by
    obtain ⟨i, hic, hi⟩ := hs₀
    refine ⟨s₀, fun h1 => ?_⟩
    have h2 : qtwoDB44_linEquiv (m - 1) (τBP s₀) = 1 := congrArg Subtype.val h1
    have h3 : τBP s₀ = 1 := by
      apply qtwoDB44_linEquiv_injective (m - 1)
      rw [h2, map_one]
    have h4 : τ (bm s₀) = 1 := (MulEquiv.map_eq_one_iff eN).mp h3
    exact hi ((hτker (βL (Additive.ofMul s₀))).mp h4 i hic)
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    have h : QuadraticMap.polarBilin Q = CFSG.RankThree.Classical.spForm (m - 1) (ZMod 2) :=
      LinearMap.ext₂ fun x y => hQpol x y
    rw [h]
    exact CFSG.RankThree.Classical.spForm_nondegenerate
  have hdim : Module.finrank (ZMod 2) (Fin (m - 1) ⊕ Fin (m - 1) → ZMod 2) = 2 * (m - 1) := by
    simp [Module.finrank_fintype_fun_eq_card, two_mul]
  obtain ⟨⟨Φ, hΦcard, hΦr⟩, hcen⟩ := qtwoDB42_frameCore_of_model (Y := ψY.range) hBs hSC hQnd
    hd4 hdim hQplus ψY hψYinj rfl βY hcompat hne
  exact ⟨ψY.range, hJ₁Y, hJ₂Y, Φ, hΦcard, hΦr, hcen⟩



set_option linter.unusedVariables false in
theorem qtwoDB44_case_symplectic
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hC : lab = ⟨.C, m - 1, 1⟩) :
    ∃ Y : Subgroup G, qtwoDelJ ψ c ≤ Y ∧ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
        Subgroup.center ↥Y = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  subst hC
  have hstar : GGBstar 3 B Bs := hbase.p_eq ▸ hcfg.1.1.1.2.1
  have hperfN : Group.IsPerfect ↥N := Group.isPerfect_def.mpr (qtwoDB36_perfect hN)
  have hBsN : Bs ≤ Subgroup.normalizer (N : Set G) :=
    ggQTwoDUnit_normalizer_N (by omega) hbase b'.2 hN hJ₁
  obtain ⟨hZ, ⟨eN⟩⟩ := qtwoDB44_model (N := ↥N) (d := m - 1) (by omega) hlab
  obtain ⟨τ, hτker, hconj, hscτ, hWτ, hJ1c, hJ2c⟩ :=
    qtwoDB44_torus hm hbase hcoords hdel hN hJ₁ hJ₂ hBsN hZ
  have hperf₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤
      ⁅(qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom,
        (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (qtwoDB16_J_perfect (by omega) hbase)
  refine qtwoDB44_case_symplectic_of (by omega) hstar.2.1 hstar.2.2.2 hBsN eN τ hτker hconj hscτ
    hWτ hJ₁
    (qtwoDB16_J_perfect (by omega) hbase) (fun i _ => one_ne_zero) hJ1c hJ₂ hperf₂
    (fun i _ => ?_) hJ2c (s₀ := ⟨x, hbase.x_mem⟩)
    ⟨a, hdel.hca.symm, by rw [hcoords.x_coord hbase.x_mem]; exact one_ne_zero⟩
  rw [show (fun _ => (1 : ZMod 3)) = (1 : DVec m) from rfl, qtwoDB16_dSign_one_apply]
  split_ifs <;> decide

end CFSG.StandardType.QTwo

end
