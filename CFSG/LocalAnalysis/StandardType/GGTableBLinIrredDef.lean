module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLMod

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def GGTableBActionSCr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  p ≠ 2 ∧ ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ (H : Subgroup (MulAut L')) (W : Set L'), H ≤ A ∧ H ≠ ⊥ ∧
        (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
          ∀ h ∈ H, MulAut.conj n * h * (MulAut.conj n)⁻¹ ∈ H) ∧
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        (∀ A' : Subgroup (MulAut L'), A' ≤ A → A' ≠ ⊥ →
          (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → H ≤ A') ∧
        (∀ a ∈ A, (∀ n ∈ W, MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1) ∧
        (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ * a⁻¹ ∈ H) ∧
        (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
          ∃ w ∈ W, ∀ a ∈ A, a (n * w⁻¹) = n * w⁻¹) ∧
        (∀ n ∈ W, n ∈ Subgroup.closure {m | m ∈ W ∧ m * m = 1}) ∧
        ∀ f : MulAut L' → MulAut L', (∀ a ∈ H, f a ∈ H) →
          (∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a * f b) →
          (∀ n ∈ W, ∀ a ∈ H, f (MulAut.conj n * a * (MulAut.conj n)⁻¹) =
            MulAut.conj n * f a * (MulAut.conj n)⁻¹) → ∃ c : ℕ, ∀ a ∈ H, f a = a ^ c

theorem ggTableBActionSCr_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTableBActionSCr p r R' I') :
    GGTableBActionSCr p r R I := by
  refine ⟨h.1, fun L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc => ?_⟩
  refine h.2 L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 hsc
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]

namespace LinIrred

variable {G : Type*} [Group G]

theorem pow_eq_one_of_involution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs Hc : Subgroup G}
    {x m v h : G} {j : ℕ} (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs) (hHBs : Hc ≤ Bs)
    (hhH : h ∈ Hc) (hmh : m * h * m⁻¹ ∈ Hc) (hmx : m * x = x * m) (hmm : m * m = 1)
    (hHx : Hc ⊓ Subgroup.zpowers x = ⊥) (hz : m * v * m⁻¹ * v⁻¹ = h * x ^ j) : x ^ j = 1 := by
  have hmi : m⁻¹ = m := inv_eq_of_mul_eq_one_right hmm
  have hmxj : m * x ^ j * m⁻¹ = x ^ j := by
    have c : Commute m (x ^ j) := (show Commute m x from hmx).pow_right j
    rw [c.eq, mul_inv_cancel_right]
  have hxjBs : x ^ j ∈ Bs := Bs.pow_mem hxBs j
  have hmz : m * (m * v * m⁻¹ * v⁻¹) * m⁻¹ = (m * v * m⁻¹ * v⁻¹)⁻¹ :=
    calc m * (m * v * m⁻¹ * v⁻¹) * m⁻¹ = (m * m) * v * m⁻¹ * v⁻¹ * m⁻¹ := by group
      _ = v * m⁻¹ * v⁻¹ * m⁻¹ := by rw [hmm, one_mul]
      _ = v * m * v⁻¹ * m⁻¹ := by rw [hmi]
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

end LinIrred

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggTableBAction_of_actionSCr {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTableBActionSCr p r R I) {B₂ : Subgroup G}
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
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hN hlift
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
    have hWZ : ∀ w : L, w ∈ W → (w : G) ∈ Z := by
      have key : ∀ y : L, y ∈ Subgroup.closure {m | m ∈ W ∧ m * m = 1} → (y : G) ∈ Z := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem m hm =>
          obtain ⟨hmW, hmm⟩ := hm
          have hmN := hWN m hmW
          refine (hZmem _).mpr ⟨hmN, fun v hv => ?_⟩
          obtain ⟨hmv, he⟩ := hconjL m (Subgroup.mem_inf.mp hmN).2 ⟨v, hv⟩
          have hmm' : (m : G) * (m : G) = 1 := by
            have := congrArg Subtype.val hmm
            simpa using this
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
          have hxj : x ^ j = 1 := LinIrred.pow_eq_one_of_involution hp hp2 hBs hxBs hHcBs hh
            (hHcinv _ hmN _ hh) (hnx _ hmN) hmm' hHcinf hzj
          rw [hzj, hxj, mul_one]
          exact hh
        | one => exact Z.one_mem
        | mul a b _ _ ha hb =>
          rw [Subgroup.coe_mul]
          exact Z.mul_mem ha hb
        | inv a _ ha =>
          rw [Subgroup.coe_inv]
          exact Z.inv_mem ha
      exact fun w hw => key w (hW8 w hw)
    intro n hn v hv
    have hnL := (Subgroup.mem_inf.mp hn).1
    have hnN := (Subgroup.mem_inf.mp hn).2
    have hnZ : n ∈ Z := by
      obtain ⟨w, hwW, hwfix⟩ := hW6 ⟨n, hnL⟩ (hNA n hn)
      have hwN := hWN w hwW
      have ht : ((⟨n, hnL⟩ * w⁻¹ : L) : G) ∈ Z := by
        have htG : ((⟨n, hnL⟩ * w⁻¹ : L) : G) = n * (w : G)⁻¹ := rfl
        refine (hZmem _).mpr ⟨⟨(⟨n, hnL⟩ * w⁻¹ : L).2, ?_⟩, fun v' hv' => ?_⟩
        · rw [htG]
          exact Subgroup.mul_mem _ hnN (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hwN).2)
        · have h1 := congrArg Subtype.val (hwfix (γ ⟨v', hv'⟩) ⟨⟨v', hv'⟩, rfl⟩)
          rw [hγ, ggGamma_coe] at h1
          rw [htG] at h1 ⊢
          have h3 : v' * (n * (w : G)⁻¹) = (n * (w : G)⁻¹) * v' := by
            calc v' * (n * (w : G)⁻¹) = v' * (n * (w : G)⁻¹) * v'⁻¹ * v' := by group
              _ = (n * (w : G)⁻¹) * v' := by rw [h1]
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

theorem ggTableBActionInputOn_of_labelsSCr {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGBstarInnerDiagLInputOn S)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTableBActionSCr p r R I) :
    GGTableBActionInputOn S := by
  intro G _ _ p B Bs x L D J B₂ hcfg hM hMod
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1)
    (hD G p B Bs x L D J hcfg hM)
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  exact ggTableBAction_of_actionSCr hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hlift hT hMod

end CFSG.StandardType

end
