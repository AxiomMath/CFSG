module

public import CFSG.LocalAnalysis.StandardType.GGNbrTransvectionDichotomy
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_ggOverGamma_one {p : ℕ} (hp : p.Prime) {Bs K : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hNoTr : GGNoTransvection p Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p)
    {κ : MulAut ↥Bs} (hκ : κ ∈ ggAutomizer K Bs) (hover : GGOverGamma hN κ 1) : κ = 1 := by
  classical
  obtain ⟨g, hgK, hg, hκg⟩ := mem_ggAutomizer_iff.mp hκ
  let N : Subgroup ↥Bs := (Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)).subgroupOf Bs
  have hVc : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hVp : ∀ v : ↥Bs, v ^ p = 1 := fun v => Subtype.ext (by simpa using hBs.2 v v.2)
  have hleBs : Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G) ≤ Bs := by
    intro x hx
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  have hNcard : Nat.card N ≤ p := by
    change Nat.card ↥((Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)).subgroupOf Bs) ≤ p
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleBs).toEquiv]
    exact hZ
  have hκN : ∀ v : ↥Bs, v⁻¹ * κ v ∈ N := by
    intro v
    have hw : ((v⁻¹ * κ v : ↥Bs) : G) = (v : G)⁻¹ * g * (v : G) * g⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hκg v]
      group
    have hwK : ((v⁻¹ * κ v : ↥Bs) : G) ∈ K := by
      rw [hw]
      exact K.mul_mem ((Subgroup.mem_normalizer_iff''.mp (hN v.2) g).mp hgK)
        (K.inv_mem hgK)
    have hwC : ((v⁻¹ * κ v : ↥Bs) : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [← ggGamma_eq_one_iff K hN (v⁻¹ * κ v)]
      have hgamma : ggGamma K hN (κ v) = ggGamma K hN v := by
        have hv := hover v
        simp only [MulAut.one_apply] at hv
        simpa only [MonoidHom.coe_rangeRestrict] using Subtype.ext_iff.mp hv
      rw [map_mul, map_inv, hgamma, inv_mul_cancel]
    change ((v⁻¹ * κ v : ↥Bs) : G) ∈ Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)
    exact ⟨⟨(v⁻¹ * κ v).2, hwK⟩, hwC⟩
  have hfix : ∀ n ∈ N, κ n = n := by
    intro n hn
    have hn' : (n : G) ∈ Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G) := hn
    have hnK : (n : G) ∈ K := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hn').1).2
    have hnC : (n : G) ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp hn').2
    have hgn : g * (n : G) = (n : G) * g := (Subgroup.mem_centralizer_iff.mp hnC) g hgK
    apply Subtype.ext
    rw [hκg n, hgn]
    group
  have hmem : κ ∈ ggInduced ⊤ Bs := ⟨g, Subgroup.mem_top g, hg, hκg⟩
  rcases mulAut_eq_one_or_transvection hp hVc hVp N hNcard κ hκN hfix with h1 | h2
  · exact h1
  · exact absurd h2 (hNoTr κ hmem)

theorem pow_eq_one_of_ggOverGamma_one {p : ℕ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {κ : MulAut ↥Bs} (hκ : κ ∈ ggAutomizer X Bs) (hover : GGOverGamma hN κ 1) :
    κ ^ p = 1 := by
  obtain ⟨g, hgX, hgN, hκg⟩ := mem_ggAutomizer_iff.mp hκ
  apply MulEquiv.ext
  intro b
  let d : ↥Bs := b⁻¹ * κ b
  have hdC : (d : G) ∈ Subgroup.centralizer (X : Set G) := by
    rw [← ggGamma_eq_one_iff X hN d]
    have he : ggGamma X hN (κ b) = ggGamma X hN b := by
      have hv := hover b
      simp only [MulAut.one_apply] at hv
      simpa only [MonoidHom.coe_rangeRestrict] using Subtype.ext_iff.mp hv
    dsimp only [d]
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hd : κ d = d := by
    apply Subtype.ext
    rw [hκg d, Subgroup.mem_centralizer_iff.mp hdC g hgX]
    simp
  have hbd : κ b = b * d := by dsimp [d]; group
  have hiter : ∀ k : ℕ, (κ ^ k) b = b * d ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hd, hbd, pow_succ']
      group
  have hdp : d ^ p = 1 := Subtype.ext (by simpa using hBs.2 d d.2)
  simpa [hdp] using hiter p

theorem prime_dvd_ggAutomizer_dvd_gamma {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hne : ℓ ≠ p) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hdiv : ℓ ∣ Nat.card (ggAutomizer X Bs)) :
    ℓ ∣ Nat.card (ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
      (ggGamma X hN).range) := by
  classical
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' ℓ hdiv
  obtain ⟨g, hgX, hgN, hcg⟩ := mem_ggAutomizer_iff.mp c.2
  have hceq : (c : MulAut ↥Bs) = ggConjAut Bs hgN :=
    MulEquiv.ext fun b => Subtype.ext (hcg b)
  let hn := conj_mem_normalizer_range_ggGamma hN hgX hgN
  let a : MulAut ↥(ggGamma X hN).range := ggConjAut (ggGamma X hN).range hn
  have ha : a ∈ ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
      (ggGamma X hN).range :=
    ggConjAut_mem_ggAutomizer (g := MulAut.conj (⟨g, hgX⟩ : ↥X))
      (MonoidHom.mem_range.mpr ⟨⟨g, hgX⟩, rfl⟩) hn
  have hover : GGOverGamma hN (c : MulAut ↥Bs) a := by
    rw [hceq]
    exact ggOverGamma_conjAut hgX hgN
  have hcℓ : (c : MulAut ↥Bs) ^ ℓ = 1 := by
    have h := pow_orderOf_eq_one c
    rw [hc] at h
    exact congrArg Subtype.val h
  have haℓ : a ^ ℓ = 1 := by
    apply MulEquiv.ext
    intro v
    obtain ⟨b, rfl⟩ := (ggGamma X hN).rangeRestrict_surjective v
    have h := hover.pow ℓ b
    simpa only [hcℓ, MulAut.one_apply] using h.symm
  by_cases ha1 : a = 1
  · have hcp := pow_eq_one_of_ggOverGamma_one hBs hN c.2 (ha1 ▸ hover)
    have hcp' : c ^ p = 1 := Subtype.ext hcp
    have hdp : ℓ ∣ p := hc ▸ orderOf_dvd_of_pow_eq_one hcp'
    exact (hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hdp)).elim
  · have hao : orderOf a = ℓ := orderOf_eq_prime haℓ ha1
    exact hao ▸ Subgroup.orderOf_dvd_natCard _ ha

end CFSG.StandardType

end
