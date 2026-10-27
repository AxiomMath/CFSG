module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5L47

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_of_omega {p : ℕ} {U Bs : Subgroup G} (hBsU : Bs ≤ U)
    (hBsp : ∀ b ∈ Bs, b ^ p = 1) (hΩ : ∀ u ∈ U, u ^ p = 1 → u ∈ Bs) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (Bs : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    refine hΩ _ ((Subgroup.mem_normalizer_iff.mp hn h).mp (hBsU hh)) ?_
    rw [conj_pow, hBsp h hh, mul_one, mul_inv_cancel]
  · intro hh
    refine hΩ _ ((Subgroup.mem_normalizer_iff.mp hn h).mpr (hBsU hh)) ?_
    have h1 := hBsp _ hh
    rw [conj_pow] at h1
    have h2 : h ^ p = n⁻¹ * (n * h ^ p * n⁻¹) * n := by group
    rw [h2, h1]
    group

theorem pow_sub_one_conj_mul_inv_mem [Finite G] {p : ℕ} [Fact p.Prime] {V H : Subgroup G}
    {x g : G} (hV : IsElemAbelian p V) (hHV : H ≤ V) (hxV : x ∈ V) (hxH : x ∉ H)
    (hVeq : V = H ⊔ Subgroup.zpowers x) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) :
    g ^ (p - 1) * x * (g ^ (p - 1))⁻¹ * x⁻¹ ∈ H := by
  have hp := (Fact.out : p.Prime)
  have hgH' : ∀ h ∈ H, g * h * g⁻¹ ∈ H := fun h hh => (Subgroup.mem_normalizer_iff.mp hgH h).mp hh
  have hxB : ∀ b ∈ H, x * b = b * x := fun b hb => mul_comm_of_isElemAbelian hV hxV (hHV hb)
  have hcV : g * x * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV x).mp hxV
  obtain ⟨b, hb, j, hc⟩ := exists_mem_mul_pow_of_mem_sup hxB (hVeq ▸ hcV)
  have hiter : ∀ n : ℕ, ∃ b' ∈ H, g ^ n * x * (g ^ n)⁻¹ = b' * x ^ (j ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨1, H.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨b', hb', h'⟩ := ih
      refine ⟨(g * b' * g⁻¹) * b ^ (j ^ n), H.mul_mem (hgH' b' hb') (H.pow_mem hb _), ?_⟩
      have hcomm : Commute b (x ^ j) :=
        mul_comm_of_isElemAbelian hV (hHV hb) (V.pow_mem hxV j)
      calc g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by
              rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
        _ = (g * b' * g⁻¹) * (g * x * g⁻¹) ^ (j ^ n) := by
              rw [h', conj_pow]; simp only [mul_assoc, inv_mul_cancel_left]
        _ = (g * b' * g⁻¹) * b ^ (j ^ n) * x ^ (j ^ (n + 1)) := by
              rw [hc, hcomm.mul_pow, ← pow_mul, pow_succ']; simp only [mul_assoc]
  have hxp : x ^ p = 1 := hV.2 x hxV
  have hj : (j : ZMod p) ≠ 0 := by
    intro hj0
    have hxj : x ^ j = 1 := by
      rw [pow_eq_pow_mod_of_pow_eq_one hxp,
        Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff j p).mp hj0), pow_zero]
    rw [hxj, mul_one] at hc
    exact hxH ((Subgroup.mem_normalizer_iff.mp hgH x).mpr (hc ▸ hb))
  obtain ⟨b', hb', h'⟩ := hiter (p - 1)
  have hjmod : x ^ (j ^ (p - 1)) = x := by
    have hz : ((j ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast
      exact ZMod.pow_card_sub_one_eq_one hj
    rw [pow_eq_pow_mod_of_pow_eq_one hxp, (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz,
      Nat.mod_eq_of_lt hp.one_lt, pow_one]
  rw [h', hjmod, mul_inv_cancel_right]
  exact hb'

theorem conj_mul_inv_mem_of_conj_gen_mem [Finite G] {p : ℕ} {V H : Subgroup G} {x g : G}
    (hV : IsElemAbelian p V) (hHV : H ≤ V) (hxV : x ∈ V) (hVeq : V = H ⊔ Subgroup.zpowers x)
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgx : g * x * g⁻¹ * x⁻¹ ∈ H) :
    ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ H := by
  have hxB : ∀ b ∈ H, x * b = b * x := fun b hb => mul_comm_of_isElemAbelian hV hxV (hHV hb)
  intro v hv
  obtain ⟨b, hb, i, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxB (hVeq ▸ hv)
  set e := g * x * g⁻¹ * x⁻¹ with hedef
  have e1 : g * x * g⁻¹ = e * x := by rw [hedef, inv_mul_cancel_right]
  have hex : Commute e x := (hxB e hgx).symm
  have hbe : Commute b (e ^ i) := mul_comm_of_isElemAbelian hV (hHV hb) (V.pow_mem (hHV hgx) i)
  have e2 : g * (b * x ^ i) * g⁻¹ * (b * x ^ i)⁻¹ = (g * b * g⁻¹) * e ^ i * b⁻¹ := by
    calc g * (b * x ^ i) * g⁻¹ * (b * x ^ i)⁻¹
        = (g * b * g⁻¹) * (g * x ^ i * g⁻¹) * (x ^ i)⁻¹ * b⁻¹ := by group
      _ = (g * b * g⁻¹) * e ^ i * b⁻¹ := by
          rw [← conj_pow, e1, hex.mul_pow]; group
  rw [e2]
  exact H.mul_mem (H.mul_mem ((Subgroup.mem_normalizer_iff.mp hgH b).mp hb) (H.pow_mem hgx i))
    (H.inv_mem hb)

theorem pow_prime_mem_centralizer_of_triv {p : ℕ} {V H : Subgroup G} {h : G}
    (hHp : ∀ t ∈ H, t ^ p = 1) (hhH : h ∈ Subgroup.centralizer (H : Set G))
    (hhV : ∀ v ∈ V, h * v * h⁻¹ * v⁻¹ ∈ H) : h ^ p ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨t, htdef⟩ : ∃ t, t = h * v * h⁻¹ * v⁻¹ := ⟨_, rfl⟩
  have ht : t ∈ H := htdef ▸ hhV v hv
  have hht : h * t = t * h := (Subgroup.mem_centralizer_iff.mp hhH t ht).symm
  have hiter : ∀ n : ℕ, h ^ n * v * (h ^ n)⁻¹ = t ^ n * v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : h * v * h⁻¹ = t * v := by rw [htdef]; group
      have ht' : h * t ^ n * h⁻¹ = t ^ n := by
        rw [← conj_pow, show h * t * h⁻¹ = t by rw [hht, mul_inv_cancel_right]]
      calc h ^ (n + 1) * v * (h ^ (n + 1))⁻¹ = h * (h ^ n * v * (h ^ n)⁻¹) * h⁻¹ := by
            rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
        _ = (h * t ^ n * h⁻¹) * (h * v * h⁻¹) := by rw [ih]; group
        _ = t ^ (n + 1) * v := by rw [ht', e1, pow_succ, mul_assoc]
  have h1 := hiter p
  rw [hHp t ht, one_mul] at h1
  calc v * h ^ p = (h ^ p * v * (h ^ p)⁻¹) * h ^ p := by rw [h1]
    _ = h ^ p * v := by group

theorem mem_of_pow_mem_of_coprime {K : Subgroup G} {g : G} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hm : g ^ m ∈ K) (hn : g ^ n ∈ K) : g ∈ K := by
  have hb := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one, Nat.cast_one] at hb
  have e : g = (g ^ m) ^ (Nat.gcdA m n) * (g ^ n) ^ (Nat.gcdB m n) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb, zpow_one]
  rw [e]
  exact K.mul_mem (K.zpow_mem hm _) (K.zpow_mem hn _)

end General

section L46v

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_of_ggFieldCase {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hFC : GGFieldCase p B Bs x L D J X) {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) :
    ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G),
      n * b * n⁻¹ ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
  obtain ⟨-, -, hXN, -, hXn, -, -⟩ := hFC
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  intro c hc
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn c).mp hc.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' : n⁻¹ * g * n⁻¹⁻¹ ∈ X := hconj _ (Subgroup.inv_mem _ hn) g hg
  have hcg := Subgroup.mem_centralizer_iff.mp hc.2 _ hg'
  rw [inv_inv] at hcg
  calc g * (n * c * n⁻¹) = n * ((n⁻¹ * g * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * g * n)) * n⁻¹ := by rw [hcg]
    _ = n * c * n⁻¹ * g := by group

theorem normalizer_le_normalizer_of_ggFieldCase {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X : Subgroup G} (hFC : GGFieldCase p B Bs x L D J X) :
    Subgroup.normalizer (Bs : Set G) ≤
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  intro n hn
  apply mem_normalizer_of_forall_conj_mem
  intro w hw
  simpa using conj_mem_of_ggFieldCase hFC (Subgroup.inv_mem _ hn) w hw

theorem ggOpAutTrivial_of_omega (h43 : GGL43Input) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X U : Subgroup G} (hFC : GGFieldCase p B Bs x L D J X) (hU : GGL45Setup p Bs X U)
    (hΩ : ∀ u ∈ U, u ^ p = 1 → u ∈ Bs) :
    GGOpAutTrivial p (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  obtain ⟨hcfg, hbl5, hXN, hCX, hXn, hXp, hXC⟩ := id hFC
  have hI := hcfg.1
  have : Fact p.Prime := ⟨hI.2.2.2.2.2.1.1⟩
  have hp := (Fact.out : p.Prime)
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hI.2.2.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hL43 := h43 G p B Bs x L D J X hFC
  have hL44 := ggL44i_of_ggL43 hBs hxBs hXN hXp hL43
  have hYM := normalizer_le_normalizer_of_ggFieldCase hFC
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hB₁Bs : B₁ ≤ Bs := inf_le_left
  have hB₁p : ∀ t ∈ B₁, t ^ p = 1 := fun t ht => hBs.2 t ht.1
  have hZC : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.centralizer (B₁ : Set G) :=
    Subgroup.centralizer_le hB₁Bs
  have hXC₁ : X ≤ Subgroup.centralizer (B₁ : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp hb.2 g hg).symm
  have hNUY : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (Bs : Set G) :=
    normalizer_le_normalizer_of_omega hU.2.2.2 hBs.2 hΩ
  intro Q hQM hCQ hQn hQp
  have hQconj : ∀ n ∈ Subgroup.normalizer (B₁ : Set G), ∀ g ∈ Q, n * g * n⁻¹ ∈ Q := by
    intro n hn g hg
    have := hQn.conj_mem ⟨g, hQM hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : Subgroup G, ∀ g, g ∈ Q₀ ↔ g ∈ Q ∧
      g ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ v ∈ Bs, g * v * g⁻¹ * v⁻¹ ∈ B₁ :=
    ⟨{ carrier := {g | g ∈ Q ∧ g ∈ Subgroup.normalizer (Bs : Set G) ∧
          ∀ v ∈ Bs, g * v * g⁻¹ * v⁻¹ ∈ B₁}
       mul_mem' := fun {g h} hg hh => ⟨Q.mul_mem hg.1 hh.1, Subgroup.mul_mem _ hg.2.1 hh.2.1,
         triv_mod_mul (fun b hb => (Subgroup.mem_normalizer_iff.mp (hQM hg.1) b).mp hb)
           hg.2.2 hh.2.2⟩
       one_mem' := ⟨Q.one_mem, Subgroup.one_mem _, fun v _ => by simp⟩
       inv_mem' := fun {g} hg => ⟨Q.inv_mem hg.1, Subgroup.inv_mem _ hg.2.1,
         triv_mod_inv (fun v hv => (Subgroup.mem_normalizer_iff''.mp hg.2.1 v).mp hv) hg.2.2⟩ },
      fun g => Iff.rfl⟩
  have hXQ₀ : X ≤ Q₀ := fun g hg => (hQ₀ g).mpr ⟨hCQ (hXC₁ hg), hXN hg, hL44.2.1 g hg⟩
  have hFC₀ : GGFieldCase p B Bs x L D J Q₀ := by
    refine ⟨hcfg, hbl5, fun g hg => ((hQ₀ g).mp hg).2.1, fun z hz => (hQ₀ z).mpr
      ⟨hCQ (hZC hz), Subgroup.centralizer_le_normalizer _ hz, fun v hv => ?_⟩, ⟨fun n hn y => ?_⟩,
      fun g hg => ?_, fun h => hXC (hXQ₀.trans h)⟩
    · have hzv : v * z = z * v := Subgroup.mem_centralizer_iff.mp hz v hv
      rw [← hzv, mul_inv_cancel_right, mul_inv_cancel]
      exact B₁.one_mem
    · rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hn1, -, hn3⟩ := (hQ₀ n).mp hn
      have hy : (y : G) ∈ Subgroup.normalizer (Bs : Set G) := y.2
      refine (hQ₀ _).mpr ⟨?_, (y * n * y⁻¹).2, ?_⟩
      · simpa using hQconj y (hYM hy) n hn1
      · have := triv_mod_conj (V := Bs) (B₁ := B₁) (g := (y : G)) (n := (n : G))
          (fun v hv => (Subgroup.mem_normalizer_iff''.mp hy v).mp hv)
          (fun b hb => (Subgroup.mem_normalizer_iff.mp (hYM hy) b).mp hb) hn3
        simpa using this
    · obtain ⟨a, ha⟩ := hQp g ((hQ₀ g).mp hg).1
      refine ⟨a + 1, ?_⟩
      have hga : g ^ p ^ a ∈ Q₀ := Q₀.pow_mem hg _
      rw [pow_succ, pow_mul]
      exact pow_prime_mem_centralizer_of_triv hB₁p ha ((hQ₀ _).mp hga).2.2
  have hL43₀ := h43 G p B Bs x L D J Q₀ hFC₀
  have hQ₀C : Q₀ ≤ Subgroup.centralizer (B₁ : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hxc : ∀ c ∈ Bs ⊓ Subgroup.centralizer (Q₀ : Set G), x * c = c * x :=
      fun c hc => mul_comm_of_isElemAbelian hBs hxBs hc.1
    obtain ⟨c, hc, j, hbc⟩ := exists_mem_mul_pow_of_mem_sup hxc (hL43₀.2 ▸ hb.1)
    have hcB₁ : c ∈ B₁ := ⟨hc.1, Subgroup.centralizer_le hXQ₀ hc.2⟩
    have hxj : x ^ j = 1 := by
      by_contra hne
      have hmem : x ^ j ∈ B₁ := by
        have e : x ^ j = c⁻¹ * b := by rw [hbc]; group
        rw [e]
        exact B₁.mul_mem (B₁.inv_mem hcB₁) hb
      have hz := zpowers_eq_of_mem_of_ne_one hxp
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j) hne
      exact hL43.1 (Subgroup.zpowers_le.mp (hz ▸ Subgroup.zpowers_le.mpr hmem))
    rw [hbc, hxj, mul_one]
    exact (Subgroup.mem_centralizer_iff.mp hc.2 g hg).symm
  have hQY : ∀ g ∈ Q, g ∈ Subgroup.normalizer (Bs : Set G) →
      g ∈ Subgroup.centralizer (B₁ : Set G) := by
    intro g hgQ hgY
    have hgM : g ∈ Subgroup.normalizer (B₁ : Set G) := hQM hgQ
    have h1 : g ^ (p - 1) ∈ Q₀ := by
      have hx := pow_sub_one_conj_mul_inv_mem hBs hB₁Bs hxBs hL43.1 hL43.2 hgY hgM
      exact (hQ₀ _).mpr ⟨Q.pow_mem hgQ _, Subgroup.pow_mem _ hgY _,
        conj_mul_inv_mem_of_conj_gen_mem hBs hB₁Bs hxBs hL43.2 (Subgroup.pow_mem _ hgM _) hx⟩
    obtain ⟨a, ha⟩ := hQp g hgQ
    have hcop : Nat.Coprime (p - 1) (p ^ a) := by
      refine Nat.Coprime.pow_right a ?_
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos one_pos)
    exact mem_of_pow_mem_of_coprime hcop (hQ₀C h1) ha
  intro q hq
  obtain ⟨c, hc, hcq⟩ := exists_mul_mem_normalizer_of_maxPSubgroup
    (ggNormalizer_le_normalizer_centralizer B₁ (hQM hq)) hU.2.1 hU.1 hU.2.2.1
  have h := hQY _ (Q.mul_mem (hCQ hc) hq) (hNUY hcq)
  simpa using (Subgroup.centralizer (B₁ : Set G)).mul_mem (Subgroup.inv_mem _ hc) h

end L46v

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGL46Struct (p : ℕ) (Bs : Subgroup G) (x : G) (X U U₁ : Subgroup G) : Prop :=
  IsMulCommutative U₁ ∧
    (∃ s : ℕ, 2 ≤ s ∧ (∀ u ∈ U₁, u ^ p ^ s = 1) ∧ (∃ u ∈ U₁, orderOf u = p ^ s) ∧
      (∃ x' : G, Subgroup.zpowers x' = Subgroup.zpowers x ∧
        ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1))) ∧
      ∃ (H : Subgroup G) (r : ℕ), H ≤ U₁ ∧ (∀ h ∈ H, h ^ p ^ s = 1) ∧
        Nat.card H = p ^ (s * r) ∧
        Nat.card (H ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) = p ^ r ∧
        Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤ p ^ (r + 1)) ∧
    (∀ A ∈ thompsonAbelianSubgroups U, A = U₁) ∧
    (∀ u : G, u ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ↔ u ∈ U₁ ∧ u ^ p = 1) ∧
    (∀ u ∈ U, u ^ p = 1 → u ∈ Bs)

end Defs

@[expose] def GGL46StructInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46Struct p Bs x X U U₁

theorem ggL46Input_of_struct (h43 : GGL43Input) (h : GGL46StructInput) : GGL46Input := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS
  obtain ⟨h1, h2, h3, h4, h5⟩ := h G p B Bs x L D J X B₂ d y K U U₁ hS
  exact ⟨h1, h2, h3, h4, h5, ggOpAutTrivial_of_omega h43 hS.1 hS.2.2.2.2.2.2.1 h5⟩

theorem ggL46Input_of_tableB (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (h : GGL46StructInput) :
    GGL46Input :=
  ggL46Input_of_struct
    (ggL43Input_of_inputs hTB hNN (ggL43ProdInput_of_hard hTBM (ggL43HardInput_of_tableB hTB hTBA)))
    h

theorem ggFieldCaseInput_of_tableB_l46 (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (h44 : GGL44iiiInput)
    (h45 : GGL45Input) (h46 : GGL46StructInput) (h47 : GGL47Input) (h48 : GGL48Input) :
    GGFieldCaseInput :=
  ggFieldCaseInput_of_tableB hTB hNN hTBM hTBA h44 h45 (ggL46Input_of_tableB hTB hNN hTBM hTBA h46)
    h47 h48

theorem ggProp41Input_of_tableB_l46 (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (h44 : GGL44iiiInput)
    (h45 : GGL45Input) (h46 : GGL46StructInput) (h47 : GGL47Input) (h48 : GGL48Input) :
    GGProp41Input :=
  ggProp41Input_of_input (ggFieldCaseInput_of_tableB_l46 hTB hNN hTBM hTBA h44 h45 h46 h47 h48)

end CFSG.StandardType

end
