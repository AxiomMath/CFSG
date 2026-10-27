module

public import CFSG.LocalAnalysis.StandardType.GGSix
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Group

variable {G : Type*} [Group G]

theorem mem_normalizer_centralizer {S : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (S : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ y ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      y * c * y⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro y hy c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : y⁻¹ * s * y ∈ S := (Subgroup.mem_normalizer_iff''.mp hy s).mp hs
    have := hc _ hs'
    calc s * (y * c * y⁻¹) = y * ((y⁻¹ * s * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * s * y)) * y⁻¹ := by rw [this]
      _ = y * c * y⁻¹ * s := by group
  refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨key x hx c, fun hc => ?_⟩
  have := key x⁻¹ (Subgroup.inv_mem _ hx) _ hc
  simpa [mul_assoc] using this

theorem not_dvd_card_of_isCyclic_of_mem_normalizer [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {N Y : Subgroup G} {x : G} (hx : orderOf x = p) (hxN : x ∉ N)
    (hxn : x ∈ Subgroup.normalizer (N : Set G)) (hNY : N ≤ Y) (hxY : x ∈ Y)
    (hcyc : ∀ S : Subgroup G, S ≤ Y → IsPGroup p S → IsCyclic S) : ¬ p ∣ Nat.card N := by
  set n : Subgroup.normalizer (N : Set G) := ⟨x, hxn⟩ with hn
  have hno : orderOf n = p := by rw [hn, Subgroup.orderOf_mk]; exact hx
  have hPp : IsPGroup p (Subgroup.zpowers n) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hno, pow_one])
  have hcard : ¬ p ∣ Nat.card (Sylow p N) := by
    intro h
    have h1 := (Nat.modEq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modEq_one p N)
    have h2 : p ∣ 1 := (Nat.modEq_iff_dvd' (Nat.zero_le 1)).mp h1
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  obtain ⟨S, hS⟩ := hPp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p N) hcard
  have hfix : ∀ k : ℤ, n ^ k • S = S := fun k =>
    hS ⟨n ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩
  set S' : Subgroup G := (S : Subgroup N).map N.subtype with hS'
  have hconj : ∀ k : ℤ, ∀ a ∈ S', x ^ k * a * (x ^ k)⁻¹ ∈ S' := by
    intro k a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have hmem : n ^ k • b ∈ ((n ^ k • S : Sylow p N) : Subgroup N) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul b (n ^ k) (S : Subgroup N) hb
    rw [hfix k] at hmem
    refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
    have hk : ((n ^ k : Subgroup.normalizer (N : Set G)) : G) = x ^ k := by simp [hn]
    change ((n ^ k : Subgroup.normalizer (N : Set G)) : G) * (b : G) *
      ((n ^ k : Subgroup.normalizer (N : Set G)) : G)⁻¹ = x ^ k * (b : G) * (x ^ k)⁻¹
    rw [hk]
  have hxS' : x ∈ Subgroup.normalizer (S' : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => by simpa using hconj 1 a ha,
      fun ha => ?_⟩
    have := hconj (-1) _ ha
    simpa [mul_assoc] using this
  have hS'p : IsPGroup p S' := S.isPGroup'.map N.subtype
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hCp : IsPGroup p (S' ⊔ Subgroup.zpowers x : Subgroup G) :=
    hS'p.to_sup_of_normal_left' hxp (Subgroup.zpowers_le.mpr hxS')
  have hS'N : S' ≤ N := Subgroup.map_subtype_le _
  have hCY : S' ⊔ Subgroup.zpowers x ≤ Y := sup_le (hS'N.trans hNY) (Subgroup.zpowers_le.mpr hxY)
  have hCcyc : IsCyclic (S' ⊔ Subgroup.zpowers x : Subgroup G) := hcyc _ hCY hCp
  have hS'dvd : ¬ p ∣ Nat.card S' := by
    intro hdvd
    have hr : Subgroup.zpowers x ≤ S' ⊔ Subgroup.zpowers x := le_sup_right
    have hl : S' ≤ S' ⊔ Subgroup.zpowers x := le_sup_left
    have hle : (Subgroup.zpowers x).subgroupOf (S' ⊔ Subgroup.zpowers x) ≤
        S'.subgroupOf (S' ⊔ Subgroup.zpowers x) := by
      rw [IsCyclic.subgroup_le_iff_card_dvd,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hr).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl).toEquiv, Nat.card_zpowers, hx]
      exact hdvd
    have : (⟨x, hr (Subgroup.mem_zpowers x)⟩ : ↥(S' ⊔ Subgroup.zpowers x)) ∈
        S'.subgroupOf (S' ⊔ Subgroup.zpowers x) :=
      hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x))
    exact hxN (hS'N (Subgroup.mem_subgroupOf.mp this))
  have hScard : Nat.card (S : Subgroup N) = 1 := by
    rcases S.isPGroup'.card_eq_or_dvd with h | h
    · exact h
    · exact absurd (by rwa [hS', Subgroup.card_map_of_injective Subtype.coe_injective]) hS'dvd
  rw [← Subgroup.card_mul_index (S : Subgroup N), hScard, one_mul]
  exact S.not_dvd_index

theorem mem_normalizer_pCoreOf {p : ℕ} {H : Subgroup G} {n : G} (hn : n ∈ H) :
    n ∈ Subgroup.normalizer (pCoreOf p H : Set G) := by
  have key : ∀ m ∈ H, ∀ h ∈ pCoreOf p H, m * h * m⁻¹ ∈ pCoreOf p H := by
    intro m hm h hh
    obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨⟨m, hm⟩ * h' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (Dichotomy.CentralizerContainment.pCore_normal_assembly p H).conj_mem h' hh' _
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨key n hn h, fun hh => ?_⟩
  have := key n⁻¹ (H.inv_mem hn) _ hh
  simpa [mul_assoc] using this

end Group

section Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem mem_normalizer_ggG0_of_ctx (hctx : GGSixCtx p B Bs x L D J) :
    x ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  obtain ⟨-, -, -, -, -, -, hS, hst, hsix⟩ := hctx
  have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  refine mem_normalizer_ggG0 (Subgroup.centralizer_le_normalizer (L : Set G) hxCL)
    fun y K hK => (hst.2.2.1 y K ⟨hK.1, D, J, hsix.2.1, hK.2⟩).1 hS.2.1

theorem not_mem_centralizer_ggG0_of_ctx (hctx : GGSixCtx p B Bs x L D J) :
    x ∉ Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, hst, hsix⟩ := hctx
  obtain ⟨⟨y, K, hK⟩, -⟩ := hst.2.2.2 D J hsix.2.1
  intro hx
  apply hK.2.2.2
  have hxK : x ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.centralizer_le (fun k hk => le_ggG0_of_neighbor hK hk) hx
  have hbot : ⁅K, Subgroup.zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.zpowers_le.mpr hxK
  rw [hbot]
  exact bot_le

theorem not_dvd_card_centralizer_ggG0 (hctx : GGSixCtx p B Bs x L D J) :
    ¬ p ∣ Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G)) := by
  have hxn := mem_normalizer_ggG0_of_ctx hctx
  have hxc := not_mem_centralizer_ggG0_of_ctx hctx
  obtain ⟨-, -, -, -, -, hp, hS, -, -⟩ := hctx
  have : Fact p.Prime := ⟨hp.1⟩
  have hox : orderOf x = p := orderOf_eq_prime (hS.1.1.2 x hS.2.1) hS.2.2.1
  have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  exact not_dvd_card_of_isCyclic_of_mem_normalizer hox hxc (mem_normalizer_centralizer hxn)
    (Subgroup.centralizer_le (fun l hl => (le_sup_left : L ≤ ggG0 p B x L D J) hl)) hxCL
    hS.2.2.2.2

theorem centralizer_ggG0_eq_bot (hctx : GGSixCtx p B Bs x L D J)
    (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))))
    (hsig : ∀ Q : Subgroup G, D ≤ Subgroup.normalizer (Q : Set G) →
      Nat.Coprime p (Nat.card Q) → Q ≤ ggM p B x L D J)
    (hJ : 2 ∣ Nat.card J) :
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ := by
  obtain ⟨-, -, -, hchar, -, hp, -, -, hsix⟩ := hctx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := Subgroup.centralizer (ggG0 p B x L D J : Set G) with hX
  have hJLD : J ≤ L ⊓ Subgroup.centralizer (D : Set G) := hsix.2.1.1.2.2.2.2.2.1.1
  have hJG₀ : J ≤ ggG0 p B x L D J := (hJLD.trans inf_le_left).trans le_sup_left
  have hDJ : D ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.le_centralizer_iff.mp (hJLD.trans inf_le_right)
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 J))
  set T' : Subgroup G := (T : Subgroup J).map J.subtype with hT'
  have hT'J : T' ≤ J := Subgroup.map_subtype_le _
  have hT'ne : T' ≠ ⊥ := by
    intro h
    have hT1 : (T : Subgroup J) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ Subtype.coe_injective).mp h
    have := T.not_dvd_index
    rw [hT1, Subgroup.index_bot] at this
    exact this hJ
  have hT'p : IsPGroup 2 T' := T.isPGroup'.map J.subtype
  set Nn := Subgroup.normalizer (T' : Set G) with hNn
  have hcharN := hchar Nn ⟨T', hT'ne, hT'p, rfl⟩
  set Q := pCoreOf 2 Nn with hQ
  have hQp : IsPGroup 2 Q :=
    (Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 Nn).map Nn.subtype
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  have hcen : ∀ c ∈ Subgroup.centralizer (J : Set G), c ∈ Nn := fun c hc =>
    Subgroup.centralizer_le_normalizer (T' : Set G) (Subgroup.centralizer_le hT'J hc)
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := fun d hd =>
    mem_normalizer_pCoreOf (hcen d (hDJ hd))
  have hcop : Nat.Coprime p (Nat.card Q) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp.1 Nat.prime_two).mpr hp.2.1)
  have hQM : Q ≤ ggM p B x L D J := hsig Q hDQ hcop
  have hXN : X ≤ Nn := fun c hc =>
    Subgroup.centralizer_le_normalizer (T' : Set G)
      (Subgroup.centralizer_le (fun t ht => hJG₀ (hT'J ht)) hc)
  have hXinf : Q ⊓ X = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hXC : X ≤ Subgroup.centralizer (Q : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hw1 : q * c * q⁻¹ * c⁻¹ ∈ Q := by
      have h1 : c * q⁻¹ * c⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_pCoreOf (hXN hc)) q⁻¹).mp
          (Q.inv_mem hq)
      have := Q.mul_mem hq h1
      simpa [mul_assoc] using this
    have hw2 : q * c * q⁻¹ * c⁻¹ ∈ X := by
      have h1 : q * c * q⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (hQM hq)) c).mp hc
      exact X.mul_mem h1 (X.inv_mem hc)
    have hw : q * c * q⁻¹ * c⁻¹ = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hw1, hw2⟩
      rwa [hXinf, Subgroup.mem_bot] at this
    calc q * c = q * c * q⁻¹ * c⁻¹ * (c * q) := by group
      _ = c * q := by rw [hw, one_mul]
  rw [eq_bot_iff]
  intro c hc
  have hcQ : c ∈ Q := hcharN (Subgroup.mem_inf.mpr ⟨hXN hc, hXC hc⟩)
  have := Subgroup.mem_inf.mpr ⟨hcQ, hc⟩
  rwa [hXinf] at this

end Ctx

end CFSG.StandardType
