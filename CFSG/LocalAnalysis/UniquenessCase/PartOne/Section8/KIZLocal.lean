module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TorusLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransLocal
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CommutatorCentralDecomposition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem eq_one_of_torusLocal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup X}
    (hRp : IsPGroup p R) (hT : CFSG.AGLEmbeddingD2.TorusLocal p R) {x : X} (hxR : x ∈ R)
    (hx : ∀ n ∈ normalizer (R : Set X), x * n = n * x) : x = 1 := by
  obtain ⟨-, -, -, -, t, htN, m, lam, e, -, -, -, -, hinv, -⟩ := hT
  have htNe : t ^ e ∈ normalizer (R : Set X) := Subgroup.pow_mem _ htN e
  have hxte : x * t ^ e = t ^ e * x := hx _ htNe
  have hxe : t ^ e * x * (t ^ e)⁻¹ = x := by
    rw [← hxte, mul_assoc, mul_inv_cancel, mul_one]
  have hxinv : x = x⁻¹ := hxe.symm.trans (hinv x hxR)
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxinv]
    exact mul_inv_cancel x
  have hcop : Nat.Coprime p 2 := (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)).symm
  have hc : (orderOf x).Coprime 2 := by
    simpa only [Subgroup.orderOf_mk] using hRp.orderOf_coprime hcop (⟨x, hxR⟩ : R)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc (orderOf_dvd_of_pow_eq_one hx2))

theorem eq_one_of_d2HeisLocalAt {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (H : CFSG.AGLEmbeddingD2.D2HeisLocalAt i Pp) {K : Subgroup X} (hK : K.Normal)
    (hKC : centralizer (K : Set X) = ⊥) (he : Nonempty (↥K ≃* i.Group)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpp : Pp p) (P : Sylow p X) {x : X}
    (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, hC, hZ, hcomm, hexp, -, t, htN, m, lam, e, hm, hlam, -, hpow, -, -⟩ :=
    H X K hK hKC he p hpp P
  let Z : Subgroup X := (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X)
  have hZ' : Nat.card Z = p := hZ
  have hp2 : 2 ≤ p := hp.two_le
  have hxcent : x ∈ centralizer ((P : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
    intro n hn
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (hx n (Subgroup.le_normalizer hn)).symm
  have hxZ : x ∈ Z := ⟨hxP, hxcent⟩
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card Z = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hPPne : ⁅(P : Subgroup X), (P : Subgroup X)⁆ ≠ ⊥ := by
    rw [hcomm]
    exact hZne
  have hex : ∃ a ∈ (P : Subgroup X), ∃ b ∈ (P : Subgroup X), ⁅a, b⁆ ≠ 1 := by
    by_contra h
    push Not at h
    have hle : (P : Subgroup X) ≤ centralizer ((P : Subgroup X) : Set X) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
      intro b hb
      exact h a ha b hb
    exact hPPne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
  obtain ⟨a, haP, b, hbP, hwne⟩ := hex
  let w : X := ⁅a, b⁆
  have hwZ : w ∈ Z := by
    have hw : w ∈ ⁅(P : Subgroup X), (P : Subgroup X)⁆ := by
      simpa only [w] using Subgroup.commutator_mem_commutator haP hbP
    rwa [hcomm] at hw
  have hwgen : Subgroup.zpowers w = Z := by
    have hdiv : orderOf w ∣ p := by
      have := Subgroup.orderOf_dvd_natCard Z hwZ
      rwa [hZ'] at this
    have hord : orderOf w = p := by
      rcases (Nat.dvd_prime hp).mp hdiv with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hwne
      · exact h1
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwZ) ?_
    rw [Nat.card_zpowers, hZ', hord]
  have hxmem : x ∈ Subgroup.zpowers w := by
    rw [hwgen]
    exact hxZ
  obtain ⟨k, -, hxk⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hxmem)
  have htNm : t ^ m ∈ normalizer ((P : Subgroup X) : Set X) := Subgroup.pow_mem _ htN m
  let φ : X ≃* X := MulAut.conj (t ^ m)
  obtain ⟨z₁, hz₁Z, hz₁⟩ := hpow a haP
  obtain ⟨z₂, hz₂Z, hz₂⟩ := hpow b hbP
  have hz₁c : ∀ y ∈ (P : Subgroup X), y * z₁ = z₁ * y :=
    fun y hy => Subgroup.mem_centralizer_iff.mp hz₁Z.2 y hy
  have hz₂c : ∀ y ∈ (P : Subgroup X), y * z₂ = z₂ * y :=
    fun y hy => Subgroup.mem_centralizer_iff.mp hz₂Z.2 y hy
  have hφa : φ a = z₁ * a ^ lam := by
    change MulAut.conj (t ^ m) a = z₁ * a ^ lam
    rw [MulAut.conj_apply, hz₁]
    exact hz₁c (a ^ lam) (P.pow_mem haP lam)
  have hφb : φ b = z₂ * b ^ lam := by
    change MulAut.conj (t ^ m) b = z₂ * b ^ lam
    rw [MulAut.conj_apply, hz₂]
    exact hz₂c (b ^ lam) (P.pow_mem hbP lam)
  have hφaP : φ a ∈ (P : Subgroup X) := by
    rw [hφa]
    exact P.mul_mem hz₁Z.1 (P.pow_mem haP lam)
  have hφbP : φ b ∈ (P : Subgroup X) := by
    rw [hφb]
    exact P.mul_mem hz₂Z.1 (P.pow_mem hbP lam)
  have hcomp : ⁅φ a, φ b⁆ = ⁅a ^ lam, b ^ lam⁆ :=
    CFSG.GorensteinWalter.commutator_eq_of_central_decomposition hφa hφb
      (hz₁c (a ^ lam) (P.pow_mem haP lam)).symm
      (hz₁c (b ^ lam) (P.pow_mem hbP lam)).symm
      (hz₂c (a ^ lam) (P.pow_mem haP lam)).symm
      (hz₂c (b ^ lam) (P.pow_mem hbP lam)).symm
      (hz₁c (φ b) hφbP).symm (hz₂c (φ a) hφaP).symm
  have hcw1 : ⁅a ^ lam, b ^ lam⁆ = w ^ (lam * lam) := by
    have hwa : Commute a w := Subgroup.mem_centralizer_iff.mp hwZ.2 a haP
    have hwb : Commute b w := Subgroup.mem_centralizer_iff.mp hwZ.2 b hbP
    have hleft : ⁅a ^ lam, b⁆ = w ^ lam := (hwa.commutatorElement_pow_left lam).symm
    have hbcomm : Commute b ⁅a ^ lam, b⁆ := by
      rw [hleft]
      exact hwb.pow_right lam
    calc ⁅a ^ lam, b ^ lam⁆ = ⁅a ^ lam, b⁆ ^ lam :=
          (hbcomm.commutatorElement_pow_right lam).symm
      _ = (w ^ lam) ^ lam := by rw [hleft]
      _ = w ^ (lam * lam) := (pow_mul w lam lam).symm
  have hcw : φ w = w ^ (lam * lam) := by
    have hwmap : φ w = ⁅φ a, φ b⁆ := by
      change φ ⁅a, b⁆ = ⁅φ a, φ b⁆
      exact map_commutatorElement φ a b
    exact hwmap.trans (hcomp.trans hcw1)
  have hφx : φ x = x ^ (lam * lam) := by
    rw [← hxk]
    calc φ (w ^ k) = (φ w) ^ k := map_pow φ w k
      _ = (w ^ (lam * lam)) ^ k := by rw [hcw]
      _ = w ^ ((lam * lam) * k) := (pow_mul w (lam * lam) k).symm
      _ = w ^ (k * (lam * lam)) := by rw [Nat.mul_comm]
      _ = (w ^ k) ^ (lam * lam) := pow_mul w k (lam * lam)
  have hφx_eq : φ x = x := by
    change t ^ m * x * (t ^ m)⁻¹ = x
    rw [← hx _ htNm, mul_assoc, mul_inv_cancel, mul_one]
  have hxact : x ^ (lam * lam) = x := hφx.symm.trans hφx_eq
  have hlam2 : (lam : ZMod p) ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf (lam : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hlam] at hdvd
    have hle : p - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hlam0 : lam ≠ 0 := by
    intro h0
    subst h0
    rw [Nat.cast_zero, orderOf_zero (ZMod p)] at hlam
    omega
  have hlam1 : 1 ≤ lam := by omega
  have hlampos : 1 ≤ lam * lam := by nlinarith
  have hnotdvd : ¬ p ∣ lam * lam - 1 := by
    intro hdvd
    apply hlam2
    have hmod : 1 ≡ lam * lam [MOD p] := (Nat.modEq_iff_dvd' hlampos).mpr hdvd
    have hcast : ((1 : ℕ) : ZMod p) = ((lam * lam : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff 1 (lam * lam) p).mpr hmod
    rw [pow_two, ← Nat.cast_mul]
    simpa using hcast.symm
  have hcop : Nat.Coprime p (lam * lam - 1) := (hp.coprime_iff_not_dvd).mpr hnotdvd
  have hxlam : x ^ (lam * lam - 1) = 1 := by
    have h1 : x ^ (lam * lam - 1) * x = x := by
      rw [← pow_succ, Nat.sub_add_cancel hlampos]
      exact hxact
    have h2 : x ^ (lam * lam - 1) * x = 1 * x := by rw [h1, one_mul]
    exact mul_right_cancel h2
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hexp x hxP, hxlam⟩

theorem eq_one_of_d2TransLocalAt {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (H : CFSG.AGLEmbeddingD2.D2TransLocalAt i Pp) {K : Subgroup X} (hK : K.Normal)
    (hKC : centralizer (K : Set X) = ⊥) (he : Nonempty (↥K ≃* i.Group)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpp : Pp p) (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    (P : Sylow p X) {x : X} (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hEea, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup X)
  have hEcard' : Nat.card ↥E = p ^ CFSG.Open.pRank p (⊤ : Subgroup X) := by simpa using hEcard
  have hE2 : p ^ 2 ≤ Nat.card ↥E := by
    rw [hEcard']
    exact Nat.pow_le_pow_right hp.pos h2
  obtain ⟨K₂, hK₂card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card hp hEea.isPGroup hE2
  let E₂ : Subgroup X := K₂.map E.subtype
  have hE₂E : E₂ ≤ E := Subgroup.map_subtype_le K₂
  have hE₂card : Nat.card E₂ = p ^ 2 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hK₂card
  have hE₂ea : CFSG.Open.IsElemAbelian p E₂ := hEea.mono hE₂E
  obtain ⟨Q, hE₂Q⟩ := hE₂ea.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  let A : Subgroup X := E₂.map (MulAut.conj g).toMonoidHom
  have hAea : CFSG.Open.IsElemAbelian p A :=
    hE₂ea.map (MulAut.conj g).toMonoidHom
  have hAcard : Nat.card A = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE₂card
  have hQP : Q.map (MulAut.conj g).toMonoidHom = (P : Subgroup X) := by
    have h := congrArg (fun S : Sylow p X => (S : Subgroup X)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    exact h
  have hAP : A ≤ (P : Subgroup X) := by
    calc A ≤ Q.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hE₂Q
      _ = (P : Subgroup X) := hQP
  obtain ⟨z, -, hz, -, hcen, -, -, -, -, -, -, ⟨t, htN, e, -, hinv⟩, -⟩ :=
    H X K hK hKC he p hpp P A hAP hAea hAcard
  have hxcent : x ∈ centralizer ((P : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
    intro n hn
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (hx n (Subgroup.le_normalizer hn)).symm
  have hxmem : x ∈ Subgroup.zpowers z := by
    rw [hcen]
    exact ⟨hxP, hxcent⟩
  obtain ⟨k, -, hxk⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hxmem)
  have htNe : t ^ e ∈ normalizer ((P : Subgroup X) : Set X) := Subgroup.pow_mem _ htN e
  let φ : X ≃* X := MulAut.conj (t ^ e)
  have hφz : φ z = z⁻¹ := by
    change t ^ e * z * (t ^ e)⁻¹ = z⁻¹
    exact hinv
  have hφx : φ x = x⁻¹ := by
    rw [← hxk]
    calc φ (z ^ k) = (φ z) ^ k := map_pow φ z k
      _ = (z⁻¹) ^ k := by rw [hφz]
      _ = (z ^ k)⁻¹ := inv_pow z k
  have hφx_eq : φ x = x := by
    change t ^ e * x * (t ^ e)⁻¹ = x
    rw [← hx _ htNe, mul_assoc, mul_inv_cancel, mul_one]
  have hxinv : x = x⁻¹ := hφx_eq.symm.trans hφx
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxinv]
    exact mul_inv_cancel x
  have hcop : Nat.Coprime p 2 := (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)).symm
  have hc : (orderOf x).Coprime 2 := by
    simpa only [Subgroup.orderOf_mk] using P.isPGroup'.orderOf_coprime hcop (⟨x, hxP⟩ : P)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc (orderOf_dvd_of_pow_eq_one hx2))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ
