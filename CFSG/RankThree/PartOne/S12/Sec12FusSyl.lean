module

public import CFSG.RankThree.PartOne.S12.Sec12Fus

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

namespace Sec12Fus

theorem conj_mem_omegaOne {p : ℕ} {K : Subgroup G} {y : G} (hy : ∀ x ∈ K, y * x * y⁻¹ ∈ K)
    {e : G} (he : e ∈ omegaOne p K) : y * e * y⁻¹ ∈ omegaOne p K := by
  refine Subgroup.closure_induction (p := fun e _ => y * e * y⁻¹ ∈ omegaOne p K) ?_ ?_ ?_ ?_ he
  · rintro x ⟨hxK, hxp⟩
    refine Subgroup.subset_closure ⟨hy x hxK, ?_⟩
    have : (y * x * y⁻¹) ^ p = y * x ^ p * y⁻¹ := by
      rw [conj_pow]
    rw [this, hxp]
    group
  · simp
  · intro a b _ _ ha hb
    have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem conj_mem_center_map {P : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (P : Set G))
    {x : G} (hx : x ∈ (Subgroup.center ↥P).map P.subtype) :
    y * x * y⁻¹ ∈ (Subgroup.center ↥P).map P.subtype := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hyP : y * (z : G) * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hy _).1 z.2
  refine ⟨⟨y * (z : G) * y⁻¹, hyP⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  have hw' : y⁻¹ * (w : G) * y ∈ P := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (P : Set G)).inv_mem hy)
      (w : G)).1 w.2
    simpa [mul_assoc] using this
  have hzw := Subgroup.mem_center_iff.1 hz ⟨y⁻¹ * (w : G) * y, hw'⟩
  have h1 : y⁻¹ * (w : G) * y * (z : G) = (z : G) * (y⁻¹ * (w : G) * y) :=
    congrArg Subtype.val hzw
  show (w : G) * (y * (z : G) * y⁻¹) = y * (z : G) * y⁻¹ * (w : G)
  calc (w : G) * (y * (z : G) * y⁻¹) = y * (y⁻¹ * (w : G) * y * (z : G)) * y⁻¹ := by group
    _ = y * ((z : G) * (y⁻¹ * (w : G) * y)) * y⁻¹ := by rw [h1]
    _ = y * (z : G) * y⁻¹ * (w : G) := by group

theorem conj_mem_omega_of_normalizes {p : ℕ} {P : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (P : Set G)) {e : G} (he : e ∈ omegaOne p P) :
    y * e * y⁻¹ ∈ omegaOne p P :=
  conj_mem_omegaOne (fun x hx => (Subgroup.mem_normalizer_iff.1 hy x).1 hx) he

theorem exists_mem_normalizer_sdiff [Finite G] {p : ℕ} [Fact p.Prime] {P S : Subgroup G}
    (hPS : P ≤ S) (hS : IsPGroup p S) (hne : P ≠ S) :
    ∃ y ∈ S, y ∉ P ∧ y ∈ Subgroup.normalizer (P : Set G) := by
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hlt : P.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hPS
    intro x hx
    have : (⟨x, hx⟩ : ↥S) ∈ P.subgroupOf S := by rw [htop]; trivial
    exact this
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥S) (P.subgroupOf S) hlt
  obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt hgrow
  refine ⟨y, y.2, fun h => hyP h, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have := (Subgroup.mem_normalizer_iff.1 hyN ⟨g, hPS hg⟩).1 hg
    exact this
  · intro hg
    have hgS : g ∈ S := by
      have h1 : (y : G) * g * (y : G)⁻¹ ∈ S := hPS hg
      have h2 := S.mul_mem (S.mul_mem (S.inv_mem y.2) h1) y.2
      simpa [mul_assoc] using h2
    have := (Subgroup.mem_normalizer_iff.1 hyN ⟨g, hgS⟩).2 hg
    exact this

theorem mem_normalizer_omegaOne {p : ℕ} {P : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (P : Set G)) :
    y ∈ Subgroup.normalizer (omegaOne p P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact conj_mem_omega_of_normalizes hy he
  · intro he
    have hy' : y⁻¹ ∈ Subgroup.normalizer (P : Set G) := (Subgroup.normalizer (P : Set G)).inv_mem hy
    have := conj_mem_omega_of_normalizes hy' he
    simpa [mul_assoc] using this

theorem mem_normalizer_zpowers_of_conj [Finite G] {c y : G}
    (h : y * c * y⁻¹ ∈ Subgroup.zpowers c) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  set f : G →* G := (MulAut.conj y).toMonoidHom with hf
  have hfc : f c = y * c * y⁻¹ := rfl
  have hle : (Subgroup.zpowers c).map f ≤ Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers, hfc]
    exact Subgroup.zpowers_le.2 h
  have heq : (Subgroup.zpowers c).map f = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact hle ⟨g, hg, rfl⟩
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg', hgg'⟩ := hg
    have : g' = g := (MulAut.conj y).injective hgg'
    rw [← this]
    exact hg'

theorem eq_one_of_pow_eq_one_of_not_dvd {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hH : ¬ p ∣ Nat.card H) {γ : H} {m : ℕ} (hγ : γ ^ (p ^ m) = 1) : γ = 1 := by
  have h1 : orderOf γ ∣ p ^ m := orderOf_dvd_of_pow_eq_one hγ
  have h2 : orderOf γ ∣ Nat.card H := orderOf_dvd_natCard γ
  have hcop : Nat.Coprime (p ^ m) (Nat.card H) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hH)
  have h3 := Nat.dvd_gcd h1 h2
  rw [hcop] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

end Sec12Fus

theorem node1214Syl_of_inputs : Node1214Syl := by
  classical
  intro G _ _ p A c L E ctx hnH b K I X P Q hL hC hF hout
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hPs := hC.P_sylow.1
  have hPp : IsPGroup p P := hPs.2.1
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hPeq : P = (S : Subgroup G) := by
    by_contra hne
    obtain ⟨y, hyS, hyP, hyN⟩ := Sec12Fus.exists_mem_normalizer_sdiff hPS S.isPGroup' hne
    have hyN' : y⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normalizer (P : Set G)).inv_mem hyN
    have hEy : ∀ e ∈ E, y * e * y⁻¹ ∈ E := fun e he => by
      rw [← hout.omega] at he ⊢
      exact Sec12Fus.conj_mem_omega_of_normalizes hyN he
    have hEy' : ∀ e ∈ E, y⁻¹ * e * y⁻¹⁻¹ ∈ E := fun e he => by
      rw [← hout.omega] at he ⊢
      exact Sec12Fus.conj_mem_omega_of_normalizes hyN' he
    have hBy : ∀ e ∈ E ⊓ L, y * e * y⁻¹ ∈ E ⊓ L := fun e he => by
      rw [hout.BZ] at he ⊢
      exact Sec12Fus.conj_mem_omegaOne (fun x hx => Sec12Fus.conj_mem_center_map hyN hx) he
    have hBy' : ∀ e ∈ E ⊓ L, y⁻¹ * e * y⁻¹⁻¹ ∈ E ⊓ L := fun e he => by
      rw [hout.BZ] at he ⊢
      exact Sec12Fus.conj_mem_omegaOne (fun x hx => Sec12Fus.conj_mem_center_map hyN' hx) he
    have hcA : c ∈ A := h.c_mem
    have hcE : c ∈ E := h.A_le_E hcA
    have hcL : c ∉ L := ctx.c_not_mem
    have hEP : E ≤ P := by
      rw [← hout.omega]
      exact (Subgroup.closure_le _).2 fun x hx => hx.1
    have hcQ : c ∉ Q := fun hcQ => by
      have : c ∈ Q ⊓ E := ⟨hcQ, hcE⟩
      rw [hout.QE] at this
      exact hcL this.2
    set c' := y * c * y⁻¹ with hc'
    have hc'E : c' ∈ E := hEy c hcE
    have hc'L : c' ∉ L := fun hc'L => by
      have := hBy' c' ⟨hc'E, hc'L⟩
      have h2 : y⁻¹ * c' * y⁻¹⁻¹ = c := by rw [hc']; group
      rw [h2] at this
      exact hcL this.2
    have hc'Q : c' ∉ Q := fun hQ => by
      have : c' ∈ Q ⊓ E := ⟨hQ, hc'E⟩
      rw [hout.QE] at this
      exact hc'L this.2
    have hcpow : c ^ p = 1 := by
      have := h.A_elem
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c hcA
    have hcord : orderOf c = p := orderOf_eq_prime hcpow h.c_ne_one
    have hc'ord : orderOf c' = p := by
      rw [hc', ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hcord
    obtain ⟨u, huP, hu⟩ := hout.trans (Subgroup.zpowers c) (Subgroup.zpowers c')
      (Subgroup.zpowers_le.2 (hEP hcE)) (Subgroup.zpowers_le.2 (hEP hc'E))
      (by rw [Nat.card_zpowers, hcord]) (by rw [Nat.card_zpowers, hc'ord])
      (fun hU => hcQ (hU (Subgroup.mem_zpowers c)))
      (fun hV => hc'Q (hV (Subgroup.mem_zpowers c')))
    have hu' : Subgroup.zpowers c' = Subgroup.zpowers (u * c * u⁻¹) := by
      rw [hu]
      unfold conjBy
      rw [MonoidHom.map_zpowers]
      rfl
    have hc'mem : c' ∈ Subgroup.zpowers (u * c * u⁻¹) := by
      rw [← hu']
      exact Subgroup.mem_zpowers c'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc'mem
    set y' := u⁻¹ * y with hy'
    have hy'c : y' * c * y'⁻¹ = c ^ k := by
      have h1 : u⁻¹ * c' * u = c ^ k := by
        rw [← hk, conj_zpow]
        group
      have h2 : y' * c * y'⁻¹ = u⁻¹ * c' * u := by rw [hy', hc']; group
      rw [h2, h1]
    have hy'H : y' ∈ cNormalizer c :=
      Sec12Fus.mem_normalizer_zpowers_of_conj (by rw [hy'c]; exact Subgroup.zpow_mem_zpowers c k)
    have hy'P : y' ∈ Subgroup.normalizer (P : Set G) :=
      mul_mem ((Subgroup.normalizer (P : Set G)).inv_mem (Subgroup.le_normalizer huP)) hyN
    have hy'E : y' ∈ Subgroup.normalizer (E : Set G) := by
      have := Sec12Fus.mem_normalizer_omegaOne (p := p) hy'P
      rw [hout.omega] at this
      exact this
    have hy'S : y' ∈ S := S.mul_mem (S.inv_mem (hPS huP)) hyS
    obtain ⟨m, hm⟩ := S.isPGroup' ⟨y', hy'S⟩
    have hy'pow : y' ^ (p ^ m) = 1 := congrArg Subtype.val hm
    set γ : ↥(torusImage E (cNormalizer c)) :=
      ⟨E.normalizerMonoidHom ⟨y', hy'E⟩, Subgroup.mem_map.2 ⟨⟨y', hy'E⟩,
        Subgroup.mem_subgroupOf.2 hy'H, rfl⟩⟩ with hγ
    have hγpow : γ ^ (p ^ m) = 1 := by
      apply Subtype.ext
      show (E.normalizerMonoidHom ⟨y', hy'E⟩) ^ (p ^ m) = 1
      rw [← map_pow]
      have : (⟨y', hy'E⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (p ^ m) = 1 :=
        Subtype.ext hy'pow
      rw [this, map_one]
    have hγ1 : γ = 1 := Sec12Fus.eq_one_of_pow_eq_one_of_not_dvd hp hnH hγpow
    have hγ1' : E.normalizerMonoidHom ⟨y', hy'E⟩ = 1 := congrArg Subtype.val hγ1
    have hbE : b ∈ E := h.A_le_E hL.b_mem.1
    have hy'b : y' * b * y'⁻¹ = b := by
      have h3 := Equivariance.coe_conjAut hy'E ⟨b, hbE⟩
      have h4 : (conjAut E y' hy'E) ⟨b, hbE⟩ = ⟨b, hbE⟩ := by
        have : conjAut E y' hy'E = 1 := hγ1'
        rw [this]
        rfl
      rw [h4] at h3
      exact h3.symm
    have hy'C : y' ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [mul_inv_eq_iff_eq_mul] at hy'b
      exact hy'b
    have hPC : P ≤ Subgroup.centralizer ({b} : Set G) := hPs.1
    have hPp' : IsPGroup p (P.subgroupOf (Subgroup.centralizer ({b} : Set G))) :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
    have hidx' : ¬ p ∣ (P.subgroupOf (Subgroup.centralizer ({b} : Set G))).index := hPs.2.2
    let Q' : Sylow p ↥(Subgroup.centralizer ({b} : Set G)) := hPp'.toSylow hidx'
    let yC : ↥(Subgroup.centralizer ({b} : Set G)) := ⟨y', hy'C⟩
    have hzp : IsPGroup p (Subgroup.zpowers yC) := by
      intro x
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 x.2
      refine ⟨m, Subtype.ext ?_⟩
      have h5 : yC ^ (p ^ m) = 1 := Subtype.ext hy'pow
      rw [Subgroup.coe_pow]
      show (x : ↥(Subgroup.centralizer ({b} : Set G))) ^ (p ^ m) = 1
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5, one_zpow]
    have hinf := hzp.inf_normalizer_sylow Q'
    have hyCN0 : yC ∈ Subgroup.normalizer ((P.subgroupOf (Subgroup.centralizer ({b} : Set G)) :
        Subgroup ↥(Subgroup.centralizer ({b} : Set G))) : Set ↥(Subgroup.centralizer ({b} : Set G))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.1 hy'P (g : G)
    have hyCN : yC ∈ Subgroup.normalizer (Q' : Set ↥(Subgroup.centralizer ({b} : Set G))) := hyCN0
    have hmem : yC ∈ Subgroup.zpowers yC ⊓
        Subgroup.normalizer (Q' : Set ↥(Subgroup.centralizer ({b} : Set G))) :=
      ⟨Subgroup.mem_zpowers yC, hyCN⟩
    rw [hinf] at hmem
    have hy'P' : y' ∈ P := hmem.2
    apply hyP
    have : y = u * y' := by rw [hy']; group
    rw [this]
    exact P.mul_mem huP hy'P'
  refine ⟨le_top, hPp, ?_⟩
  rw [hPeq, Subgroup.relIndex_top_right]
  exact S.not_dvd_index

end CFSG.RankThree.PartOne
