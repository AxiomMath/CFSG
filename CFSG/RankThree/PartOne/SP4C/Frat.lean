module

public import CFSG.RankThree.PartOne.SP4C.Row7
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.S12.Sec12FusSplit
import CFSG.RankThree.PartOne.S12.Sec12FusGen
import CFSG.RankThree.PartOne.S11d.FiveClaimAux
import CFSG.RankThree.PartOne.S12K.Class

public section

namespace CFSG.RankThree.PartOne.SP4C

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G]

theorem n_centralizes [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (ctx : Fus12Ctx G p A c L E) {b : G} {K I X P Q : Subgroup G}
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I) {n : G} (hnW : n ∈ torusNormalizer E)
    (hnb : n ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) (hnc : n ∈ cNormalizer c) :
    n * c * n⁻¹ = c := by
  classical
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  obtain ⟨hbA, hbL, hb1⟩ := hL.b_mem
  have hbp : b ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) b hbA
  have hnL : n ∈ Subgroup.normalizer (L : Set G) := ctx.facts.twoB ⟨hnc, hnW⟩
  obtain ⟨lam, hlam⟩ := Subgroup.mem_zpowers_iff.1
    ((Subgroup.mem_normalizer_iff.1 hnb b).1 (Subgroup.mem_zpowers b))
  have hlam' : ¬ (p : ℤ) ∣ lam := by
    intro hdvd
    obtain ⟨m, hm⟩ := hdvd
    apply hb1
    have h5 : n * b * n⁻¹ = 1 := by
      rw [← hlam, hm, zpow_mul, zpow_natCast, hbp, one_zpow]
    have h6 : b = n⁻¹ * (n * b * n⁻¹) * n := by group
    rw [h6, h5]
    group
  have hI' : conjBy n I ∈ thetaComponentsAt p b :=
    S11d.conjBy_mem_thetaComponentsAt_of_zpow hp hL.I_mem hbp hlam' hlam.symm
  have hCb : ∀ x : G, n⁻¹ * x * n ∈ Subgroup.centralizer ({b} : Set G) ↔
      x ∈ Subgroup.centralizer ({b} : Set G) := by
    intro x
    have hcz := S11d.centralizer_zpow_eq hp hbp hlam'
    rw [Subgroup.mem_centralizer_singleton_iff, Sec12Fus.conj_comm_iff, ← hlam,
      ← Subgroup.mem_centralizer_singleton_iff, hcz]
  have hLC : conjBy n (L ⊓ Subgroup.centralizer ({b} : Set G)) =
      L ⊓ Subgroup.centralizer ({b} : Set G) := by
    ext x
    rw [Equivariance.mem_conjBy, Subgroup.mem_inf, Subgroup.mem_inf, hCb x]
    have hLn : n⁻¹ * x * n ∈ L ↔ x ∈ L := by
      constructor
      · intro h1
        have := (Subgroup.mem_normalizer_iff.1 hnL (n⁻¹ * x * n)).1 h1
        simpa [mul_assoc] using this
      · intro h1
        have hn' : n⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
          (Subgroup.normalizer (L : Set G)).inv_mem hnL
        have := (Subgroup.mem_normalizer_iff.1 hn' x).1 h1
        simpa [mul_assoc] using this
    rw [hLn]
  have hKn : conjBy n K = K := by
    rw [hL.K_eq]
    unfold kLayer
    rw [← Equivariance.inSubgroup_layer_conjBy, hLC]
  have hKI' : K ≤ conjBy n I := by
    rw [← hKn]
    exact Subgroup.map_mono hL.K_le
  have hov : ∃ x ∈ K, ∃ hxE : x ∈ K, (⟨x, hxE⟩ : ↥K) ∉ Subgroup.center ↥K := by
    obtain ⟨a, b', hab⟩ := hL.K_qs.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    refine ⟨x, x.2, x.2, ?_⟩
    intro hx
    apply hab
    have h1 : ((x : ↥K) : ↥K ⧸ Subgroup.center ↥K) = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [h1, one_mul, mul_one]
  have hIeq : I = conjBy n I :=
    thetaComponent_eq_of_overlap hp hL.I_mem hI' hL.K_qs hL.K_le hKI' hov
  have hnI : n ∈ Subgroup.normalizer (I : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : n * x * n⁻¹ ∈ conjBy n I ↔ x ∈ I := by
      rw [Equivariance.mem_conjBy]
      simp [mul_assoc]
    rw [← h1, ← hIeq]
  exact S12K.kf1215Class_holds G p A c L E ctx b K I X P Q hL hC hF n hnc hnI

theorem kf1215Sp4Frat_holds : KF1215Sp4Frat := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF hout _ h7 g hg hginv
  classical
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  have hcA : c ∈ A := h.c_mem
  have hcp : c ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c hcA
  have hcord : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := h.L_mem.2
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hLH : L ≤ cNormalizer c := fun l hl =>
    mem_cNormalizer_of_commute (Subgroup.mem_centralizer_singleton_iff.1 (hLc hl))
  obtain ⟨x, hx, n, hn, hgxn⟩ := frat_core ctx hout g hg
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  have hnL : n ∈ Subgroup.normalizer (L : Set G) := ctx.facts.twoB hn
  have hnF := ctx.mem_normalizer_inf hn
  obtain ⟨l, hlL, hlF, k, hk⟩ := row7_sq_scalar ctx.table_core h7 hnL hnF
  have hlc : l * c = c * l := Subgroup.mem_centralizer_singleton_iff.1 (hLc hlL)
  have hbE : b ∈ E ⊓ L := ⟨h.A_le_E hL.b_mem.1, hL.b_mem.2.1⟩
  have hmW : l⁻¹ * (n * n) ∈ torusNormalizer E :=
    (torusNormalizer E).mul_mem
      (ctx.mem_torusNormalizer (L.inv_mem hlL) ((Subgroup.normalizer _).inv_mem hlF))
      ((torusNormalizer E).mul_mem hn.2 hn.2)
  have hmb : l⁻¹ * (n * n) ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    refine mem_normalizer_zpowers_of_conj_mem ?_
    have : l⁻¹ * (n * n) * b * (l⁻¹ * (n * n))⁻¹ = b ^ k := by
      calc l⁻¹ * (n * n) * b * (l⁻¹ * (n * n))⁻¹ = l⁻¹ * ((n * n) * b * (n * n)⁻¹) * l := by group
        _ = l⁻¹ * (l * b ^ k * l⁻¹) * l := by rw [hk b hbE]
        _ = b ^ k := by group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
  have hmc : l⁻¹ * (n * n) ∈ cNormalizer c :=
    (cNormalizer c).mul_mem ((cNormalizer c).inv_mem (hLH hlL)) ((cNormalizer c).mul_mem hn.1 hn.1)
  have hcen := n_centralizes ctx hL hC hF hmW hmb hmc
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    ((Subgroup.mem_normalizer_iff.1 hn.1 c).1 (Subgroup.mem_zpowers c))
  have hnn : (n * n) * c * (n * n)⁻¹ = c ^ (j * j) := by
    calc (n * n) * c * (n * n)⁻¹ = n * (n * c * n⁻¹) * n⁻¹ := by group
      _ = n * c ^ j * n⁻¹ := by rw [← hj]
      _ = (n * c * n⁻¹) ^ j := by rw [conj_zpow]
      _ = (c ^ j) ^ j := by rw [← hj]
      _ = c ^ (j * j) := by rw [← zpow_mul]
  have hcomm : l⁻¹ * c ^ (j * j) * l = c ^ (j * j) := by
    have h1 : l * c ^ (j * j) = c ^ (j * j) * l :=
      (Commute.zpow_right (show Commute l c from hlc) (j * j)).eq
    calc l⁻¹ * c ^ (j * j) * l = l⁻¹ * (c ^ (j * j) * l) := by group
      _ = l⁻¹ * (l * c ^ (j * j)) := by rw [h1]
      _ = c ^ (j * j) := by group
  have hjj : c ^ (j * j) = c := by
    calc c ^ (j * j) = l⁻¹ * c ^ (j * j) * l := hcomm.symm
      _ = l⁻¹ * ((n * n) * c * (n * n)⁻¹) * l := by rw [hnn]
      _ = l⁻¹ * (n * n) * c * (l⁻¹ * (n * n))⁻¹ := by group
      _ = c := hcen
  have hdvd : (p : ℤ) ∣ (j - 1) * (j + 1) := by
    have h1 : c ^ ((j - 1) * (j + 1)) = 1 := by
      have : (j - 1) * (j + 1) = j * j - 1 := by ring
      rw [this, zpow_sub, zpow_one, hjj, mul_inv_cancel]
    have := (orderOf_dvd_iff_zpow_eq_one (x := c) (i := (j - 1) * (j + 1))).2 h1
    rwa [hcord] at this
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hxinv : ∀ i : ℤ, x * c ^ i * x⁻¹ = c ^ i := fun i => by
    have := (Commute.zpow_right (show Commute x c from hxc) i).eq
    calc x * c ^ i * x⁻¹ = c ^ i * x * x⁻¹ := by rw [this]
      _ = c ^ i := by group
  have hgc : g * c * g⁻¹ = x * c ^ j * x⁻¹ := by
    calc g * c * g⁻¹ = x * (n * c * n⁻¹) * x⁻¹ := by rw [hgxn]; group
      _ = x * c ^ j * x⁻¹ := by rw [← hj]
  rcases hpz.dvd_or_dvd hdvd with h1 | h1
  ·
    have h2 : c ^ (j - 1) = 1 := by
      have := (orderOf_dvd_iff_zpow_eq_one (x := c) (i := j - 1)).1 (by rw [hcord]; exact h1)
      exact this
    have hcj : c ^ j = c := by
      rw [show j = (j - 1) + 1 by ring, zpow_add_one, h2, one_mul]
    have hgc' : g * c * g⁻¹ = c := by
      rw [hgc, hcj]
      have := hxinv 1
      rwa [zpow_one] at this
    refine ⟨1, ⟨⟨(torusNormalizer E).one_mem, (Subgroup.normalizer _).one_mem⟩,
      (cNormalizer c).one_mem⟩, ?_⟩
    rw [hgc']
    group
  ·
    exfalso
    apply hginv
    have h2 : c ^ (j + 1) = 1 := by
      have := (orderOf_dvd_iff_zpow_eq_one (x := c) (i := j + 1)).1 (by rw [hcord]; exact h1)
      exact this
    have hcj : c ^ j = c⁻¹ := by
      rw [zpow_add_one] at h2
      exact eq_inv_of_mul_eq_one_left h2
    rw [hgc, hcj]
    calc x * c⁻¹ * x⁻¹ = x * c ^ (-1 : ℤ) * x⁻¹ := by rw [zpow_neg_one]
      _ = c ^ (-1 : ℤ) := hxinv (-1)
      _ = c⁻¹ := zpow_neg_one c

end CFSG.RankThree.PartOne.SP4C
