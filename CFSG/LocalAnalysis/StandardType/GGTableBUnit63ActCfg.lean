module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Cfg
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63ActDesc
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Mod

public section

namespace CFSG.StandardType.U63TB

open CFSG CFSG.Assembly CFSG.StandardType TableB NbrInnerRest

theorem eq_one_of_two_pow_of_exp {G : Type*} [Group G] {z : G} {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hz : z ^ p = 1) (hk : z ^ 2 ^ k = 1) : z = 1 := by
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have := pow_gcd_eq_one.mpr ⟨hz, hk⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

section Square

variable {G : Type*} [Group G]

theorem pow_eq_one_of_sq_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs Hc : Subgroup G}
    {x m v h : G} {j : ℕ} (hBs : CFSG.Assembly.IsElemAbelian p Bs) (hxBs : x ∈ Bs)
    (hHBs : Hc ≤ Bs) (hhH : h ∈ Hc) (hmh : m * h * m⁻¹ ∈ Hc) (hmx : m * x = x * m)
    (hmv : (m * m) * v = v * (m * m)) (hHx : Hc ⊓ Subgroup.zpowers x = ⊥)
    (hz : m * v * m⁻¹ * v⁻¹ = h * x ^ j) : x ^ j = 1 := by
  have hmxj : m * x ^ j * m⁻¹ = x ^ j := by
    have c : Commute m (x ^ j) := (show Commute m x from hmx).pow_right j
    rw [c.eq, mul_inv_cancel_right]
  have hxjBs : x ^ j ∈ Bs := Bs.pow_mem hxBs j
  have hmz : m * (m * v * m⁻¹ * v⁻¹) * m⁻¹ = (m * v * m⁻¹ * v⁻¹)⁻¹ :=
    calc m * (m * v * m⁻¹ * v⁻¹) * m⁻¹ = ((m * m) * v) * m⁻¹ * v⁻¹ * m⁻¹ := by group
      _ = (v * (m * m)) * m⁻¹ * v⁻¹ * m⁻¹ := by rw [hmv]
      _ = (m * v * m⁻¹ * v⁻¹)⁻¹ := by group
  rw [hz] at hmz
  have ha' : (m * h * m⁻¹) * x ^ j = (x ^ j)⁻¹ * h⁻¹ := by
    rw [← mul_inv_rev, ← hmz]
    calc (m * h * m⁻¹) * x ^ j = (m * h * m⁻¹) * (m * x ^ j * m⁻¹) := by rw [hmxj]
      _ = m * (h * x ^ j) * m⁻¹ := by group
  have hay : (m * h * m⁻¹) * x ^ j = x ^ j * (m * h * m⁻¹) :=
    mul_comm_of_isElemAbelian hBs (hHBs hmh) hxjBs
  have h1 : (m * h * m⁻¹) * (x ^ j * x ^ j) = h⁻¹ :=
    calc (m * h * m⁻¹) * (x ^ j * x ^ j) = ((m * h * m⁻¹) * x ^ j) * x ^ j := by group
      _ = ((x ^ j)⁻¹ * h⁻¹) * x ^ j := by rw [ha']
      _ = (x ^ j)⁻¹ * (h⁻¹ * x ^ j) := by group
      _ = (x ^ j)⁻¹ * (x ^ j * h⁻¹) := by
        rw [mul_comm_of_isElemAbelian hBs (Bs.inv_mem (hHBs hhH)) hxjBs]
      _ = h⁻¹ := by group
  have h2 : x ^ j * x ^ j = (m * h * m⁻¹)⁻¹ * h⁻¹ := eq_inv_mul_of_mul_eq h1
  have h3 : x ^ j * x ^ j ∈ Hc ⊓ Subgroup.zpowers x := by
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j)⟩
    rw [h2]
    exact Hc.mul_mem (Hc.inv_mem hmh) (Hc.inv_mem hhH)
  rw [hHx, Subgroup.mem_bot] at h3
  have hsq : (x ^ j) ^ 2 = 1 := by rw [sq]; exact h3
  have hxp : (x ^ j) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hBs.2 x hxBs, one_pow]
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (fun h => hp2 h.symm)
  have h4 := (pow_gcd_eq_one (a := x ^ j) (m := 2) (n := p)).mpr ⟨hsq, hxp⟩
  rwa [hcop.gcd_eq_one, pow_one] at h4

end Square

@[expose] def GGTableBActionSCrW (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  p ≠ 2 ∧ ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), CFSG.Assembly.IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ActConclW p ψ.ker A

theorem ggTableBActionSCrW_of {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTableBActionSCr p r R I) : GGTableBActionSCrW p r R I :=
  ⟨h.1, fun L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc =>
    ActConcl.toW ψ.ker (h.2 L' ψ hψ hker hperf A hA hAI hr h3 hsc)⟩

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggTableBAction_of_cardW {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma L hN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma L hN).range)
    (hT : GGTableBActionSCrW p r R I) {B₂ : Subgroup G}
    (hM : GGTableBModule p Bs x L B₂) : GGTableBAction Bs x L B₂ := by
  classical
  obtain ⟨hp2, hT⟩ := hT
  obtain ⟨hp, hBs, hxBs, hLx, hcard4⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma L hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  obtain ⟨H, W, hHA, hHne, hHinv, hW1, hW3, hW4, hW5, hW6, hW8, hW7⟩ := hT L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI hr h3
    (ggTorusSelfCent_ggGamma hN hSC)
  have hker : ∀ c : Bs, γ c = 1 ↔ (c : G) ∈ Subgroup.zpowers x := by
    intro c
    rw [hγ, ggGamma_eq_one_iff, ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs
      hS.2.2.1 hLx hS.2.2.2.2]
    exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩
  have hconjL : ∀ n : L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) → ∀ c : Bs,
      ∃ hnc : (n : G) * (c : G) * (n : G)⁻¹ ∈ Bs,
        γ ⟨(n : G) * (c : G) * (n : G)⁻¹, hnc⟩ = MulAut.conj n * γ c * (MulAut.conj n)⁻¹ := by
    intro n hn c
    have hcn : (n : G) * (c : G) * (n : G)⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hn c).mp c.2
    exact ⟨hcn, ggGamma_conj L hN n c hcn⟩
  have hNA : ∀ n (hn : n ∈ L ⊓ Subgroup.normalizer (Bs : Set G)),
      MulAut.conj (⟨n, (Subgroup.mem_inf.mp hn).1⟩ : L) ∈
        Subgroup.normalizer ((γ.range : Subgroup (MulAut L)) : Set (MulAut L)) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro e
    have hc' : ∀ c : Bs, (n : G)⁻¹ * (c : G) * (n : G)⁻¹⁻¹ ∈ Bs := fun c =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hn).2) c).mp c.2
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨hnc, he⟩ := hconjL ⟨n, (Subgroup.mem_inf.mp hn).1⟩ (Subgroup.mem_inf.mp hn).2 c
      exact ⟨⟨_, hnc⟩, he⟩
    · rintro ⟨c, hce⟩
      refine ⟨⟨_, hc' c⟩, ?_⟩
      have hc'' : ((⟨n, (Subgroup.mem_inf.mp hn).1⟩⁻¹ : L) : G) * c *
          ((⟨n, (Subgroup.mem_inf.mp hn).1⟩⁻¹ : L) : G)⁻¹ ∈ Bs := by
        simpa using hc' c
      have h1 := ggGamma_conj L hN (⟨n, (Subgroup.mem_inf.mp hn).1⟩⁻¹ : L) c hc''
      have e2 : (⟨_, hc' c⟩ : Bs) = ⟨_, hc''⟩ := Subtype.ext (by simp)
      rw [e2, h1, hce, map_inv]
      group
  have hWN : ∀ w ∈ W, (w : G) ∈ L ⊓ Subgroup.normalizer (Bs : Set G) := fun w hw =>
    ⟨w.2, mem_normalizer_of_weyl hN hSC (hW1 w hw)⟩
  obtain ⟨hxB₂, hB₂Bs, hcardB₂, hB₂inv, hirr₂, -⟩ := hM
  set A₂ : Subgroup (MulAut L) := (B₂.subgroupOf Bs).map γ with hA₂
  have hmemA₂ : ∀ c : Bs, γ c ∈ A₂ ↔ (c : G) ∈ B₂ := by
    intro c
    constructor
    · rintro ⟨b, hb, hbc⟩
      have h1 : γ (c * b⁻¹) = 1 := by rw [map_mul, map_inv, ← hbc, mul_inv_cancel]
      have h3 : ((c * b⁻¹ : Bs) : G) ∈ B₂ := Subgroup.zpowers_le.mpr hxB₂ ((hker _).mp h1)
      have h4 : (c : G) = ((c * b⁻¹ : Bs) : G) * (b : G) := by simp
      rw [h4]
      exact B₂.mul_mem h3 (Subgroup.mem_subgroupOf.mp hb)
    · intro hc
      exact ⟨c, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
  have hHA₂ : H ≤ A₂ := by
    have hne : A₂ ≠ ⊥ := by
      intro hbot
      have hle : B₂ ≤ Subgroup.zpowers x := by
        intro g hg
        have hgBs : g ∈ Bs := hB₂Bs hg
        have h1 : γ ⟨g, hgBs⟩ ∈ A₂ := (hmemA₂ _).mpr hg
        rw [hbot, Subgroup.mem_bot] at h1
        exact (hker _).mp h1
      have hcB₂ : Nat.card B₂ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers] at hcB₂
      have hox : orderOf x ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hBs.2 x hxBs))
      have h5 : p ^ 4 ≤ p * p :=
        calc p ^ 4 ≤ Nat.card Bs := hcard4
          _ ≤ p * Nat.card B₂ := hcardB₂
          _ ≤ p * p := Nat.mul_le_mul_left p (hcB₂.trans hox)
      have hpp : 4 ≤ p * p := by nlinarith [hp.two_le]
      have h6 : p ^ 4 = (p * p) * (p * p) := by ring
      nlinarith [Nat.mul_le_mul_right (p * p) hpp]
    refine hW3 A₂ (Subgroup.map_le_range _ _) hne ?_
    rintro w hw _ ⟨c, hc, rfl⟩
    obtain ⟨hwc, he⟩ := hconjL w (hWN w hw).2 c
    rw [← he]
    exact (hmemA₂ _).mpr (hB₂inv w (hWN w hw) c (Subgroup.mem_subgroupOf.mp hc))
  have hHB₂ : ∀ c : Bs, γ c ∈ H ↔ (c : G) ∈ B₂ := by
    set S : Subgroup G := B₂ ⊓ (H.comap γ).map Bs.subtype with hS'
    have hxS : Subgroup.zpowers x ≤ S := by
      rw [Subgroup.zpowers_le]
      refine ⟨hxB₂, ⟨⟨x, hxBs⟩, ?_, rfl⟩⟩
      show γ ⟨x, hxBs⟩ ∈ H
      rw [(hker ⟨x, hxBs⟩).mpr (Subgroup.mem_zpowers x)]
      exact H.one_mem
    have hSinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
      rintro n hn _ ⟨hsB₂, ⟨c, hc, rfl⟩⟩
      have hnL := (Subgroup.mem_inf.mp hn).1
      have hnN := (Subgroup.mem_inf.mp hn).2
      obtain ⟨hnc, he⟩ := hconjL ⟨n, hnL⟩ hnN c
      refine ⟨hB₂inv n hn _ hsB₂, ⟨⟨_, hnc⟩, ?_, rfl⟩⟩
      show γ ⟨_, hnc⟩ ∈ H
      rw [he]
      exact hHinv _ (hNA n hn) _ (Subgroup.mem_comap.mp hc)
    rcases hirr₂ S hxS inf_le_left hSinv with h | h
    · exfalso
      apply hHne
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨c, hc, rfl⟩ := hHA₂ ha
      have hcS : (c : G) ∈ S :=
        ⟨Subgroup.mem_subgroupOf.mp hc, ⟨c, Subgroup.mem_comap.mpr ha, rfl⟩⟩
      rw [h] at hcS
      exact Subgroup.mem_bot.mpr ((hker c).mpr hcS)
    · intro c
      refine ⟨fun hc => (hmemA₂ c).mp (hHA₂ hc), fun hc => ?_⟩
      have hcS : (c : G) ∈ S := h ▸ hc
      obtain ⟨-, ⟨c', hc', hcc'⟩⟩ := hcS
      have : c' = c := Subtype.ext hcc'
      subst this
      exact Subgroup.mem_comap.mp hc'
  refine ⟨?_, fun Hc hHcB₂ hHcinv hHcsup hHcinf => ⟨?_, ?_⟩⟩
  ·
    intro v hv hvN
    have h1 : γ ⟨v, hv⟩ = 1 := by
      apply hW4 _ ⟨⟨v, hv⟩, rfl⟩
      intro w hw
      obtain ⟨hvw, he⟩ := hconjL w (hWN w hw).2 ⟨v, hv⟩
      have hwv : (w : G) * v * (w : G)⁻¹ = v := by rw [hvN w (hWN w hw), mul_inv_cancel_right]
      rw [← he]
      congr 1
      exact Subtype.ext hwv
    exact (hker _).mp h1
  ·
    have hHcBs : Hc ≤ Bs := hHcB₂.trans hB₂Bs
    have hxHc : ∀ h ∈ Hc, x * h = h * x := fun h hh =>
      mul_comm_of_isElemAbelian hBs hxBs (hHcBs hh)
    have hnx : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), n * x = x * n := fun n hn =>
      (Subgroup.mem_centralizer_iff.mp (hLx (Subgroup.mem_inf.mp hn).1) x rfl).symm
    let Z : Subgroup G :=
      { carrier := {n | n ∈ L ⊓ Subgroup.normalizer (Bs : Set G) ∧
          ∀ v ∈ Bs, n * v * n⁻¹ * v⁻¹ ∈ Hc}
        mul_mem' := by
          rintro n n' ⟨hn, hZ⟩ ⟨hn', hZ'⟩
          refine ⟨Subgroup.mul_mem _ hn hn', fun v hv => ?_⟩
          have e : n * n' * v * (n * n')⁻¹ * v⁻¹ =
              (n * (n' * v * n'⁻¹ * v⁻¹) * n⁻¹) * (n * v * n⁻¹ * v⁻¹) := by group
          rw [e]
          exact Hc.mul_mem (hHcinv n hn _ (hZ' v hv)) (hZ v hv)
        one_mem' := ⟨Subgroup.one_mem _, fun v _ => by simp⟩
        inv_mem' := by
          rintro n ⟨hn, hZ⟩
          refine ⟨Subgroup.inv_mem _ hn, fun v hv => ?_⟩
          have e : n⁻¹ * v * n⁻¹⁻¹ * v⁻¹ = n⁻¹ * (n * v * n⁻¹ * v⁻¹)⁻¹ * n⁻¹⁻¹ := by group
          rw [e]
          exact hHcinv n⁻¹ (Subgroup.inv_mem _ hn) _ (Hc.inv_mem (hZ v hv)) }
    have hZmem : ∀ g, g ∈ Z ↔ g ∈ L ⊓ Subgroup.normalizer (Bs : Set G) ∧
        ∀ v ∈ Bs, g * v * g⁻¹ * v⁻¹ ∈ Hc := fun g => Iff.rfl
    have hcent : ∀ s : L, IsTwoIn (ggQuotHom θ).ker s →
        (s : G) ∈ Subgroup.normalizer (Bs : Set G) → ∀ v ∈ Bs, (s : G) * v = v * (s : G) := by
      rintro s ⟨hsK, k, hsk⟩ hsN v hv
      have hsC : s ∈ Subgroup.center L := by
        rw [← ker_ggQuotHom θ]
        exact hsK
      have hγs : ggGamma L hN ⟨v, hv⟩ s ∈ Subgroup.center L :=
        mulAut_mem_center (ggGamma L hN ⟨v, hv⟩) hsC
      have hγk : (ggGamma L hN ⟨v, hv⟩ s) ^ 2 ^ k = 1 := by rw [← map_pow, hsk, map_one]
      have hcomm : Commute (ggGamma L hN ⟨v, hv⟩ s) s :=
        (Subgroup.mem_center_iff.mp hγs s).symm
      have huk : (ggGamma L hN ⟨v, hv⟩ s * s⁻¹) ^ 2 ^ k = 1 := by
        rw [Commute.mul_pow hcomm.inv_right, hγk, inv_pow, hsk, inv_one, one_mul]
      have huG : v * (s : G) * v⁻¹ * (s : G)⁻¹ = ((ggGamma L hN ⟨v, hv⟩ s * s⁻¹ : L) : G) := by
        push_cast
        rw [ggGamma_coe]
      have huB : v * (s : G) * v⁻¹ * (s : G)⁻¹ ∈ Bs := by
        have h1 : (s : G) * v⁻¹ * (s : G)⁻¹ ∈ Bs :=
          (Subgroup.mem_normalizer_iff.mp hsN v⁻¹).mp (Bs.inv_mem hv)
        have := Bs.mul_mem hv h1
        simpa [mul_assoc] using this
      have hu2 : (v * (s : G) * v⁻¹ * (s : G)⁻¹) ^ 2 ^ k = 1 := by
        rw [huG, ← Subgroup.coe_pow, huk]
        rfl
      have hu1 := eq_one_of_two_pow_of_exp hp hp2 (hBs.2 _ huB) hu2
      have hu3 : v * (s : G) * v⁻¹ = (s : G) := mul_inv_eq_one.mp hu1
      calc (s : G) * v = (v * (s : G) * v⁻¹) * v := by rw [hu3]
        _ = v * (s : G) := by group
    have key : ∀ y : L, y ∈ Subgroup.closure
        {m | m ∈ W ∧ ∃ z, IsTwoIn (ggQuotHom θ).ker z ∧ m * m = z} → (y : G) ∈ Z := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem m hm =>
        obtain ⟨hmW, s, hs2, hmm⟩ := hm
        have hmN := hWN m hmW
        refine (hZmem _).mpr ⟨hmN, fun v hv => ?_⟩
        obtain ⟨hmv, he⟩ := hconjL m (Subgroup.mem_inf.mp hmN).2 ⟨v, hv⟩
        have hsG : (s : G) = (m : G) * (m : G) := by rw [← hmm]; rfl
        have hsN : (s : G) ∈ Subgroup.normalizer (Bs : Set G) := by
          rw [hsG]
          exact Subgroup.mul_mem _ (Subgroup.mem_inf.mp hmN).2 (Subgroup.mem_inf.mp hmN).2
        have hmmv : ((m : G) * (m : G)) * v = v * ((m : G) * (m : G)) := by
          rw [← hsG]
          exact hcent s hs2 hsN v hv
        have hzB : (m : G) * v * (m : G)⁻¹ * v⁻¹ ∈ Bs := Bs.mul_mem hmv (Bs.inv_mem hv)
        have hzB₂ : (m : G) * v * (m : G)⁻¹ * v⁻¹ ∈ B₂ := by
          have h1 : γ ⟨_, hzB⟩ ∈ H := by
            have e : (⟨_, hzB⟩ : Bs) =
                ⟨(m : G) * v * (m : G)⁻¹, hmv⟩ * (⟨v, hv⟩ : Bs)⁻¹ := rfl
            rw [e, map_mul, map_inv, he]
            exact hW5 m hmW _ ⟨⟨v, hv⟩, rfl⟩
          exact (hHB₂ ⟨_, hzB⟩).mp h1
        obtain ⟨h, hh, j, hzj⟩ := exists_mem_mul_pow_of_mem_sup hxHc
          (by rw [hHcsup]; exact hzB₂)
        have hxj : x ^ j = 1 := pow_eq_one_of_sq_central hp hp2 hBs hxBs hHcBs hh
          (hHcinv _ hmN _ hh) (hnx _ hmN) hmmv hHcinf hzj
        rw [hzj, hxj, mul_one]
        exact hh
      | one => exact Z.one_mem
      | mul a b _ _ ha hb =>
        rw [Subgroup.coe_mul]
        exact Z.mul_mem ha hb
      | inv a _ ha =>
        rw [Subgroup.coe_inv]
        exact Z.inv_mem ha
    have hWZ : ∀ w : L, w ∈ W → (w : G) ∈ Z := by
      intro w hw
      obtain ⟨c, hc, z, hz2, hwcz⟩ := hW8 w hw
      have hcZ := key c hc
      have hzcw : z = c⁻¹ * w := by rw [hwcz]; group
      have hzN : (z : G) ∈ Subgroup.normalizer (Bs : Set G) := by
        rw [hzcw]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ((hZmem c).mp hcZ).1.2) (hWN w hw).2
      have hzZ : (z : G) ∈ Z := by
        refine (hZmem _).mpr ⟨⟨z.2, hzN⟩, fun v hv => ?_⟩
        have h1 : (z : G) * v = v * (z : G) := hcent z hz2 hzN v hv
        have h2 : (z : G) * v * (z : G)⁻¹ * v⁻¹ = 1 := by
          rw [h1]
          group
        rw [h2]
        exact Hc.one_mem
      rw [hwcz, Subgroup.coe_mul]
      exact Z.mul_mem hcZ hzZ
    intro n hn v hv
    have hnL := (Subgroup.mem_inf.mp hn).1
    have hnN := (Subgroup.mem_inf.mp hn).2
    have hnZ : n ∈ Z := by
      obtain ⟨w, hwW, hwfix⟩ := hW6 ⟨n, hnL⟩ (hNA n hn)
      have hwN := hWN w hwW
      have htG : ((⟨n, hnL⟩ * w⁻¹ : L) : G) = n * (w : G)⁻¹ := rfl
      have htN : n * (w : G)⁻¹ ∈ Subgroup.normalizer (Bs : Set G) :=
        Subgroup.mul_mem _ hnN (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hwN).2)
      have ht : ((⟨n, hnL⟩ * w⁻¹ : L) : G) ∈ Z := by
        refine (hZmem _).mpr ⟨⟨(⟨n, hnL⟩ * w⁻¹ : L).2, by rw [htG]; exact htN⟩, fun v' hv' => ?_⟩
        obtain ⟨z, hz2, hz⟩ := hwfix (γ ⟨v', hv'⟩) ⟨⟨v', hv'⟩, rfl⟩
        have h1 := congrArg Subtype.val hz
        rw [hγ, ggGamma_coe] at h1
        rw [htG] at h1 ⊢
        have h1' : v' * (n * (w : G)⁻¹) * v'⁻¹ = n * (w : G)⁻¹ * (z : G) := h1
        have hzG : (z : G) = (n * (w : G)⁻¹)⁻¹ * (v' * (n * (w : G)⁻¹) * v'⁻¹) := by
          rw [h1']
          group
        have hzB : (z : G) ∈ Bs := by
          rw [hzG]
          have h2 : (n * (w : G)⁻¹)⁻¹ * v' * (n * (w : G)⁻¹)⁻¹⁻¹ ∈ Bs :=
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) v').mp hv'
          have := Bs.mul_mem h2 (Bs.inv_mem hv')
          simpa [mul_assoc] using this
        obtain ⟨-, k, hk⟩ := hz2
        have hzk : (z : G) ^ 2 ^ k = 1 := by
          rw [← Subgroup.coe_pow, hk]
          rfl
        have hz1 : (z : G) = 1 := eq_one_of_two_pow_of_exp hp hp2 (hBs.2 _ hzB) hzk
        rw [hz1, mul_one] at h1'
        have h3 : v' * (n * (w : G)⁻¹) = (n * (w : G)⁻¹) * v' := by
          calc v' * (n * (w : G)⁻¹) = v' * (n * (w : G)⁻¹) * v'⁻¹ * v' := by group
            _ = (n * (w : G)⁻¹) * v' := by rw [h1']
        rw [← h3]
        have : v' * (n * (w : G)⁻¹) * (n * (w : G)⁻¹)⁻¹ * v'⁻¹ = 1 := by group
        rw [this]
        exact Hc.one_mem
      have h5 := Z.mul_mem ht (hWZ w hwW)
      simpa using h5
    exact ((hZmem n).mp hnZ).2 v hv
  ·
    intro φ hφH hφmul hφN
    have hHcBs : Hc ≤ Bs := hHcB₂.trans hB₂Bs
    have hxHc : ∀ h ∈ Hc, x * h = h * x := fun h hh =>
      mul_comm_of_isElemAbelian hBs hxBs (hHcBs hh)
    have hH1 : ∀ h (hh : h ∈ Hc), γ ⟨h, hHcBs hh⟩ = 1 → h = 1 := by
      intro h hh h1
      have h2 : h ∈ Hc ⊓ Subgroup.zpowers x := ⟨hh, (hker _).mp h1⟩
      rw [hHcinf] at h2
      exact Subgroup.mem_bot.mp h2
    have huniq : ∀ h (hh : h ∈ Hc) h' (hh' : h' ∈ Hc),
        γ ⟨h, hHcBs hh⟩ = γ ⟨h', hHcBs hh'⟩ → h = h' := by
      intro h hh h' hh' he
      have h1 : γ ⟨h * h'⁻¹, hHcBs (Hc.mul_mem hh (Hc.inv_mem hh'))⟩ = 1 := by
        have e : (⟨h * h'⁻¹, hHcBs (Hc.mul_mem hh (Hc.inv_mem hh'))⟩ : Bs) =
            ⟨h, hHcBs hh⟩ * (⟨h', hHcBs hh'⟩ : Bs)⁻¹ := rfl
        rw [e, map_mul, map_inv, he, mul_inv_cancel]
      have h2 := hH1 _ (Hc.mul_mem hh (Hc.inv_mem hh')) h1
      rw [mul_inv_eq_one] at h2
      exact h2
    have hex : ∀ a ∈ H, ∃ h, ∃ hh : h ∈ Hc, γ ⟨h, hHcBs hh⟩ = a := by
      intro a ha
      obtain ⟨c, hc, rfl⟩ := hHA₂ ha
      have hcB₂ : (c : G) ∈ B₂ := Subgroup.mem_subgroupOf.mp hc
      obtain ⟨h, hh, j, hj⟩ := exists_mem_mul_pow_of_mem_sup hxHc (by rw [hHcsup]; exact hcB₂)
      refine ⟨h, hh, ?_⟩
      have e : c = ⟨h, hHcBs hh⟩ * (⟨x, hxBs⟩ : Bs) ^ j := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_pow]
        exact hj)
      have hx1 : γ ⟨x, hxBs⟩ = 1 := (hker _).mpr (Subgroup.mem_zpowers x)
      rw [e, map_mul, map_pow, hx1, one_pow, mul_one]
    have hHcH : ∀ h (hh : h ∈ Hc), γ ⟨h, hHcBs hh⟩ ∈ H := fun h hh =>
      (hHB₂ ⟨h, hHcBs hh⟩).mpr (hHcB₂ hh)
    let f : MulAut L → MulAut L := fun a =>
      if ha : ∃ h, ∃ hh : h ∈ Hc, γ ⟨h, hHcBs hh⟩ = a then
        γ ⟨φ ha.choose, hHcBs (hφH _ ha.choose_spec.choose)⟩
      else a
    have hf : ∀ h (hh : h ∈ Hc), f (γ ⟨h, hHcBs hh⟩) = γ ⟨φ h, hHcBs (hφH h hh)⟩ := by
      intro h hh
      have hex' : ∃ h', ∃ hh' : h' ∈ Hc, γ ⟨h', hHcBs hh'⟩ = γ ⟨h, hHcBs hh⟩ := ⟨h, hh, rfl⟩
      have heq : hex'.choose = h :=
        huniq _ hex'.choose_spec.choose _ hh hex'.choose_spec.choose_spec
      change (if ha : ∃ h', ∃ hh' : h' ∈ Hc, γ ⟨h', hHcBs hh'⟩ = γ ⟨h, hHcBs hh⟩ then
        γ ⟨φ ha.choose, hHcBs (hφH _ ha.choose_spec.choose)⟩ else γ ⟨h, hHcBs hh⟩) = _
      rw [dite_eq_left hex']
      congr 1
      exact Subtype.ext (congrArg φ heq)
    obtain ⟨c, hc⟩ := hW7 f
      (by
        intro a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        rw [hf h hh]
        exact hHcH _ (hφH h hh))
      (by
        intro a ha b hb
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨h', hh', rfl⟩ := hex b hb
        have e : γ ⟨h, hHcBs hh⟩ * γ ⟨h', hHcBs hh'⟩ = γ ⟨h * h', hHcBs (Hc.mul_mem hh hh')⟩ := by
          rw [← map_mul]
          rfl
        rw [e, hf _ (Hc.mul_mem hh hh'), hf h hh, hf h' hh', ← map_mul]
        congr 1
        exact Subtype.ext (hφmul h hh h' hh'))
      (by
        intro n hn a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨hnh, he⟩ := hconjL n (Subgroup.mem_inf.mp (hWN n hn)).2 ⟨h, hHcBs hh⟩
        have hnhH : (n : G) * h * (n : G)⁻¹ ∈ Hc := hHcinv n (hWN n hn) h hh
        obtain ⟨hnφ, he'⟩ := hconjL n (Subgroup.mem_inf.mp (hWN n hn)).2
          ⟨φ h, hHcBs (hφH h hh)⟩
        have e1 : γ ⟨(n : G) * h * (n : G)⁻¹, hnh⟩ =
            γ ⟨(n : G) * h * (n : G)⁻¹, hHcBs hnhH⟩ := rfl
        rw [← he, e1, hf _ hnhH, hf h hh, ← he']
        congr 1
        exact Subtype.ext (hφN n (hWN n hn) h hh))
    refine ⟨c, fun h hh => ?_⟩
    have h1 := hc _ (hHcH h hh)
    rw [hf h hh, ← map_pow] at h1
    have hhc : h ^ c ∈ Hc := Hc.pow_mem hh c
    have e : ((⟨h, hHcBs hh⟩ : Bs) ^ c) = ⟨h ^ c, hHcBs hhc⟩ := rfl
    rw [e] at h1
    exact huniq _ (hφH h hh) _ hhc h1

end Config

end CFSG.StandardType.U63TB

end
