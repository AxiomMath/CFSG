module

public import CFSG.RankThree.PartOne.S12.Sec12Fus
import CFSG.RankThree.PartOne.S12.Sec12FusSyl
import CFSG.RankThree.PartOne.S11d.FiveClaimAux

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

namespace Sec12Fus

theorem card_le_of_isSylowOf [Finite G] {p : ℕ} (hp : p.Prime) {H S₀ T : Subgroup G}
    (hS : IsSylowOf p S₀ H) (hT : T ≤ H) (hTp : IsPGroup p T) : Nat.card T ≤ Nat.card S₀ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hS0H, -, hidx⟩ := hS
  have hTH : Nat.card T ∣ Nat.card H := by
    have := Subgroup.card_subgroup_dvd_card (T.subgroupOf H)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv] at this
  obtain ⟨a, ha⟩ := hTp.exists_card_eq
  have h1 := (S₀.subgroupOf H).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0H).toEquiv] at h1
  have hidx' : ¬ p ∣ (S₀.subgroupOf H).index := hidx
  have hcop : Nat.Coprime (p ^ a) (S₀.subgroupOf H).index :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hidx')
  have hdvd : p ^ a ∣ Nat.card S₀ := by
    have : p ^ a ∣ (S₀.subgroupOf H).index * Nat.card S₀ := by
      rw [h1, ← ha]
      exact hTH
    exact hcop.dvd_of_dvd_mul_left this
  rw [ha]
  exact Nat.le_of_dvd Nat.card_pos hdvd

theorem conj_mem_zpowers_of_commute {c y : G} (hyc : y * c = c * y) {g : G}
    (hg : g ∈ Subgroup.zpowers c) : y * g * y⁻¹ ∈ Subgroup.zpowers c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have : y * c ^ k * y⁻¹ = c ^ k := by
    have h1 : Commute y (c ^ k) := Commute.zpow_right (show Commute y c from hyc) k
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.eq
  rw [this]
  exact Subgroup.zpow_mem_zpowers c k

theorem mem_cNormalizer_of_commute {c x : G} (hxc : x * c = c * x) : x ∈ cNormalizer c := by
  unfold cNormalizer
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact conj_mem_zpowers_of_commute hxc
  · intro hg
    have hx' : x⁻¹ * c = c * x⁻¹ := (Commute.inv_left (show Commute x c from hxc)).eq
    have := conj_mem_zpowers_of_commute hx' hg
    simpa [mul_assoc] using this

theorem conj_comm_iff (n x b : G) :
    (n⁻¹ * x * n) * b = b * (n⁻¹ * x * n) ↔ x * (n * b * n⁻¹) = (n * b * n⁻¹) * x := by
  constructor
  · intro h
    calc x * (n * b * n⁻¹) = n * ((n⁻¹ * x * n) * b) * n⁻¹ := by group
      _ = n * (b * (n⁻¹ * x * n)) * n⁻¹ := by rw [h]
      _ = (n * b * n⁻¹) * x := by group
  · intro h
    calc (n⁻¹ * x * n) * b = n⁻¹ * (x * (n * b * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * b * n⁻¹) * x) * n := by rw [h]
      _ = b * (n⁻¹ * x * n) := by group

end Sec12Fus

theorem node1215_core [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (ctx : Fus12Ctx G p A c L E) {b : G} {K I X P Q : Subgroup G}
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I) (hout : Out1214 p c L E I P Q) (hClass : KF1215Class)
    (hFrat : ∀ g ∈ cNormalizer c, ∃ n ∈ torusNormalizer E ⊓
      Subgroup.normalizer (Subgroup.zpowers b : Set G) ⊓ cNormalizer c,
        n * c * n⁻¹ = g * c * g⁻¹)
    {g : G} (hg : g * c * g⁻¹ ∈ P) : ∃ q ∈ Q, g * c * g⁻¹ = c * q := by
  classical
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) x hx
  have hcA : c ∈ A := h.c_mem
  have hcE : c ∈ E := h.A_le_E hcA
  have hcL : c ∉ L := ctx.c_not_mem
  obtain ⟨hbA, hbL, hb1⟩ := hL.b_mem
  have hbE : b ∈ E := h.A_le_E hbA
  have hbp : b ^ p = 1 := hApow b hbA
  have hcp : c ^ p = 1 := hApow c hcA
  have hcord : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hEP : E ≤ P := by
    rw [← hout.omega]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hcP : c ∈ P := hEP hcE
  have hcQ : c ∉ Q := fun hQ => by
    have : c ∈ Q ⊓ E := ⟨hQ, hcE⟩
    rw [hout.QE] at this
    exact hcL this.2
  set y := g * c * g⁻¹ with hy
  have hypow : y ^ p = 1 := by
    rw [hy, conj_pow, hcp]
    group
  have hy1 : y ≠ 1 := by
    intro h1
    apply h.c_ne_one
    have : c = g⁻¹ * y * g := by rw [hy]; group
    rw [this, h1]
    group
  have hyord : orderOf y = p := orderOf_eq_prime hypow hy1
  have hyE : y ∈ E := by
    rw [← hout.omega]
    exact Subgroup.subset_closure ⟨hg, hypow⟩
  have hbcA : c * b ∈ A := A.mul_mem hcA hbA
  have hbc1 : c * b ≠ 1 := by
    intro h1
    apply hcL
    have : c = b⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact L.inv_mem hbL
  have hbcord : orderOf (c * b) = p := orderOf_eq_prime (hApow _ hbcA) hbc1
  have hbcE : c * b ∈ E := E.mul_mem hcE hbE
  have hbcQ : c * b ∉ Q := fun hQ => by
    have : c * b ∈ Q ⊓ E := ⟨hQ, hbcE⟩
    rw [hout.QE] at this
    apply hcL
    have := L.mul_mem this.2 (L.inv_mem hbL)
    simpa using this
  have hPH : ¬ P ≤ cNormalizer c := by
    intro hPH
    obtain ⟨u, huP, hu⟩ := hout.trans (Subgroup.zpowers c) (Subgroup.zpowers (c * b))
      (Subgroup.zpowers_le.2 hcP) (Subgroup.zpowers_le.2 (hEP hbcE))
      (by rw [Nat.card_zpowers, hcord]) (by rw [Nat.card_zpowers, hbcord])
      (fun hU => hcQ (hU (Subgroup.mem_zpowers c)))
      (fun hV => hbcQ (hV (Subgroup.mem_zpowers _)))
    have hu' : u ∈ cNormalizer c := hPH huP
    have hconj : conjBy u (Subgroup.zpowers c) = Subgroup.zpowers c :=
      Equivariance.conjBy_eq_of_mem_normalizer hu'
    rw [hconj] at hu
    have hcb : c * b ∈ Subgroup.zpowers c := hu ▸ Subgroup.mem_zpowers _
    have hbmem : b ∈ Subgroup.zpowers c := by
      have := (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c))
        hcb
      simpa using this
    have hle : Subgroup.zpowers b ≤ Subgroup.zpowers c := Subgroup.zpowers_le.2 hbmem
    have heq : Subgroup.zpowers b = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hcord, orderOf_eq_prime hbp hb1]
    apply hcL
    have : c ∈ Subgroup.zpowers b := heq ▸ Subgroup.mem_zpowers c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
    rw [← hk]
    exact Subgroup.zpow_mem _ hbL k
  have hyB : y ∉ E ⊓ L := by
    intro hyB
    have hyZ : y ∈ (Subgroup.center ↥P).map P.subtype := by
      have hmem : y ∈ omegaOne p ((Subgroup.center ↥P).map P.subtype) := by
        rw [← hout.BZ]
        exact hyB
      exact (Subgroup.closure_le _).2 (fun x hx => hx.1) hmem
    have hycomm : ∀ t ∈ P, t * y = y * t := by
      obtain ⟨z, hz, hzy⟩ := hyZ
      intro t ht
      have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨t, ht⟩)
      simp only [Subgroup.coe_mul] at h2
      rw [← hzy]
      exact h2
    have hP''C : conjBy g⁻¹ P ≤ Subgroup.centralizer ({c} : Set G) := by
      intro x hx
      rw [Equivariance.mem_conjBy] at hx
      have hx' : g * x * g⁻¹ ∈ P := by simpa using hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h4 := hycomm _ hx'
      have h3 : g * (x * c) * g⁻¹ = g * (c * x) * g⁻¹ := by
        calc g * (x * c) * g⁻¹ = (g * x * g⁻¹) * (g * c * g⁻¹) := by group
          _ = (g * c * g⁻¹) * (g * x * g⁻¹) := h4
          _ = g * (c * x) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h3)
    have hP''H : conjBy g⁻¹ P ≤ cNormalizer c := fun x hx =>
      Sec12Fus.mem_cNormalizer_of_commute (Subgroup.mem_centralizer_singleton_iff.1 (hP''C hx))
    have hPp : IsPGroup p P := hC.P_sylow.1.2.1
    have hP''p : IsPGroup p (conjBy g⁻¹ P) := hPp.map (MulAut.conj g⁻¹).toMonoidHom
    have hcard : Nat.card ↥(conjBy g⁻¹ P) ≤ Nat.card ↥(P ⊓ cNormalizer c) :=
      Sec12Fus.card_le_of_isSylowOf hp hout.H_sylow hP''H hP''p
    have hcardeq : Nat.card ↥(conjBy g⁻¹ P) = Nat.card ↥P := by
      unfold conjBy
      exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have heq : P ⊓ cNormalizer c = P :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : P ⊓ cNormalizer c ≤ P)
        (by rw [← hcardeq]; exact hcard)
    exact hPH fun x hx => (heq.symm ▸ hx : x ∈ P ⊓ cNormalizer c).2
  have hyQ : y ∉ Q := fun hQ => hyB (by
    have : y ∈ Q ⊓ E := ⟨hQ, hyE⟩
    rwa [hout.QE] at this)
  obtain ⟨u, huP, hu⟩ := hout.trans (Subgroup.zpowers c) (Subgroup.zpowers y)
    (Subgroup.zpowers_le.2 hcP) (Subgroup.zpowers_le.2 hg)
    (by rw [Nat.card_zpowers, hcord]) (by rw [Nat.card_zpowers, hyord])
    (fun hU => hcQ (hU (Subgroup.mem_zpowers c))) (fun hV => hyQ (hV (Subgroup.mem_zpowers y)))
  have hu2 : Subgroup.zpowers y = Subgroup.zpowers (u * c * u⁻¹) := by
    rw [hu]
    unfold conjBy
    rw [MonoidHom.map_zpowers]
    rfl
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (hu2 ▸ Subgroup.mem_zpowers y : y ∈ Subgroup.zpowers (u * c * u⁻¹))
  set g' := u⁻¹ * g with hg'
  have hg'c : g' * c * g'⁻¹ = c ^ k := by
    have h1 : u⁻¹ * y * u = c ^ k := by
      rw [← hk, conj_zpow]
      group
    calc g' * c * g'⁻¹ = u⁻¹ * y * u := by rw [hg', hy]; group
      _ = c ^ k := h1
  have hg'H : g' ∈ cNormalizer c :=
    Sec12Fus.mem_normalizer_zpowers_of_conj
      (by rw [hg'c]; exact Subgroup.zpow_mem_zpowers c k)
  obtain ⟨n, ⟨⟨hnW, hnb⟩, hnc⟩, hncn'⟩ := hFrat g' hg'H
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
  have hcc := hClass G p A c L E ctx b K I X P Q hL hC hF n hnc hnI
  have hg'c' : g' * c * g'⁻¹ = c := by
    rw [← hncn']
    exact hcc
  have hgu : g * c * g⁻¹ = u * c * u⁻¹ := by
    have : g = u * g' := by rw [hg']; group
    calc g * c * g⁻¹ = u * (g' * c * g'⁻¹) * u⁻¹ := by rw [this]; group
      _ = u * c * u⁻¹ := by rw [hg'c']
  obtain ⟨f, hfP, hPf⟩ := hout.P_gen
  have hab := quotient_abelian_of_sup_zpowers hout.Q_norm.1 hout.Q_norm.2 hfP hPf
  have hcomm : u * c * u⁻¹ * c⁻¹ ∈ Q := by
    have := hab ⟨u, huP⟩ ⟨c, hcP⟩
    exact Subgroup.mem_subgroupOf.1 this
  refine ⟨c⁻¹ * (u * c * u⁻¹ * c⁻¹) * c, ?_, ?_⟩
  · have hcPQ : (⟨u * c * u⁻¹ * c⁻¹, hout.Q_norm.1 hcomm⟩ : ↥P) ∈ Q.subgroupOf P :=
      Subgroup.mem_subgroupOf.2 hcomm
    have := hout.Q_norm.2.conj_mem _ hcPQ ⟨c⁻¹, P.inv_mem hcP⟩
    simpa using Subgroup.mem_subgroupOf.1 this
  · rw [hy, hgu]
    group

theorem node1215Gen_of_inputs (hFrat : KF1215Frat) (hClass : KF1215Class) : Node1215Gen := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF hout _ h7 g hg
  exact node1215_core ctx hL hC hF hout hClass
    (fun g' hg' => hFrat G p A c L E ctx b K I X P Q hL hC hF hout h7 g' hg') hg

end CFSG.RankThree.PartOne
