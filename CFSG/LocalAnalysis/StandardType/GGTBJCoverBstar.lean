module

public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem exists_pow_eq_of_mem_ker {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {H : Type} [Group H] (ψ : ↥X →* H) (hker : ψ.ker ≤ Subgroup.center ↥X)
    {a : ↥X} (ha : a ∈ ψ.ker) : ∃ z ∈ ψ.ker, z ^ p = a := by
  have hcop : (Nat.card ↥ψ.ker).Coprime p := by
    rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.ker) p hdvd
    have hzp : ((z : ↥X)) ^ p = 1 := by
      have h : ((z : ↥ψ.ker)) ^ p = 1 := by rw [← hz, pow_orderOf_eq_one]
      simpa using congrArg (fun w : ↥ψ.ker => ((w : ↥ψ.ker) : ↥X)) h
    have hz1 : z = 1 := Subtype.ext (hZp _ (hker z.2) hzp)
    rw [hz1, orderOf_one] at hz
    exact (Fact.out : p.Prime).ne_one hz.symm
  obtain ⟨z, hz⟩ :=
    (Nat.Coprime.pow_left_bijective (G := ↥ψ.ker) hcop).surjective ⟨a, ha⟩
  exact ⟨(z : ↥X), z.2,
    by simpa using congrArg (fun w : ↥ψ.ker => ((w : ↥ψ.ker) : ↥X)) hz⟩

private theorem pow_eq_one_unique_of_psi_eq {G : Type} [Group G] {p : ℕ}
    {X : Subgroup G} (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {H : Type} [Group H] (ψ : ↥X →* H) (hker : ψ.ker ≤ Subgroup.center ↥X)
    {x x' : ↥X} (hx : x ^ p = 1) (hx' : x' ^ p = 1) (hψ : ψ x = ψ x') : x = x' := by
  have hu : x' * x⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψ, mul_inv_cancel]
  have huc : x' * x⁻¹ ∈ Subgroup.center ↥X := hker hu
  have hcomm : Commute x' x := by
    have hux : x * (x' * x⁻¹) = (x' * x⁻¹) * x := Subgroup.mem_center_iff.mp huc x
    calc x' * x = (x' * x⁻¹) * x * x := by group
      _ = x * (x' * x⁻¹) * x := by rw [hux]
      _ = x * x' := by group
  have hup : (x' * x⁻¹) ^ p = 1 := by
    rw [hcomm.inv_right.mul_pow p, hx', inv_pow, hx, inv_one, mul_one]
  have hu1 : x' * x⁻¹ = 1 := hZp _ huc hup
  have hx'x : x' = x := by
    calc x' = (x' * x⁻¹) * x := by group
      _ = x := by rw [hu1, one_mul]
  exact hx'x.symm

theorem ggCover_bstar {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {H : Type} [Group H] (ψ : ↥X →* H) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center ↥X) (Λ : H →* MulAut ↥X) (hΛ : Function.Injective Λ)
    (hΛc : ∀ x, Λ (ψ x) = MulAut.conj x) (hΛn : ∀ g l, ψ (Λ g l) = g * ψ l * g⁻¹)
    {E : Subgroup H} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hA : (ggGamma X hN).range = E.map Λ) :
    ∃ ε : ↥Bs →* H,
      (∀ b, Λ (ε b) = ggGamma X hN b) ∧
      (∀ b, ε b ∈ E) ∧ (∀ c ∈ E, ∃ b, ε b = c) ∧
      (∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G)) ∧
      (∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = ψ ⟨b, hb⟩) ∧
      (∀ b, ∃ x : ↥X, (x : G) ∈ Bs ∧ ψ x = ε b) ∧
      (∀ x x' : ↥X, (x : G) ∈ Bs → (x' : G) ∈ Bs → ψ x = ψ x' → x = x') ∧
      (∀ g : ↥X, ψ g ∈ Subgroup.normalizer (E : Set H) →
        (g : G) ∈ Subgroup.normalizer (Bs : Set G)) ∧
      (∀ g : ↥X, (g : G) ∈ Subgroup.normalizer (Bs : Set G) →
        ψ g ∈ Subgroup.normalizer (E : Set H)) ∧
      ∀ (g : ↥X) (b : ↥Bs) (hb : (g : G) * b * (g : G)⁻¹ ∈ Bs),
        ε ⟨_, hb⟩ = ψ g * ε b * (ψ g)⁻¹ := by
  classical
  have hex : ∀ b : ↥Bs, ∃ c : H, c ∈ E ∧ Λ c = ggGamma X hN b := by
    intro b
    have hb : ggGamma X hN b ∈ E.map Λ := by
      rw [← hA]
      exact ⟨b, rfl⟩
    obtain ⟨c, hcE, hc⟩ := Subgroup.mem_map.mp hb
    exact ⟨c, hcE, hc⟩
  let epsFun : ↥Bs → H := fun b => (hex b).choose
  have hspec : ∀ b, epsFun b ∈ E ∧ Λ (epsFun b) = ggGamma X hN b := fun b =>
    (hex b).choose_spec
  have huniq : ∀ (b : ↥Bs) (c : H), c ∈ E → ggGamma X hN b = Λ c → epsFun b = c := by
    intro b c _ hc
    exact hΛ (by rw [(hspec b).2, hc])
  have hone : epsFun 1 = 1 := by
    refine huniq 1 1 E.one_mem ?_
    simp only [map_one]
  have hmul : ∀ a b : ↥Bs, epsFun (a * b) = epsFun a * epsFun b := by
    intro a b
    refine huniq (a * b) (epsFun a * epsFun b) (E.mul_mem (hspec a).1 (hspec b).1) ?_
    simp only [map_mul, (hspec a).2, (hspec b).2]
  let eps : ↥Bs →* H :=
    { toFun := epsFun, map_one' := hone, map_mul' := hmul }
  have hspec' : ∀ b, eps b ∈ E ∧ Λ (eps b) = ggGamma X hN b := hspec
  have hinner : ∀ (b : ↥Bs) (hb : (b : G) ∈ X), eps b = ψ ⟨b, hb⟩ := by
    intro b hb
    apply hΛ
    rw [(hspec' b).2, hΛc]
    ext y
    rw [MulAut.conj_apply, ggGamma_coe]
    rfl
  have honto : ∀ c ∈ E, ∃ b : ↥Bs, eps b = c := by
    intro c hcE
    have hcin : Λ c ∈ (ggGamma X hN).range := by
      rw [hA]
      exact Subgroup.mem_map_of_mem Λ hcE
    obtain ⟨b, hb⟩ := hcin
    exact ⟨b, huniq b c hcE hb⟩
  have hker' : ∀ b : ↥Bs, eps b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G) := by
    intro b
    rw [← ggGamma_eq_one_iff X hN b]
    constructor
    · intro h
      rw [← (hspec' b).2, h, map_one]
    · intro h
      refine hΛ ?_
      rw [(hspec' b).2, h, map_one]
  have hbp : ∀ b : ↥Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hepsp : ∀ b : ↥Bs, eps b ^ p = 1 := by
    intro b
    rw [← map_pow eps b p, hbp b, map_one]
  have hmemX : ∀ x : ↥X, x ^ p = 1 → ψ x ∈ E → (x : G) ∈ Bs := by
    intro x hxp hxE
    have hxpG : ((x : G)) ^ p = 1 := by simpa using congrArg Subtype.val hxp
    obtain ⟨b, hb⟩ := honto (ψ x) hxE
    have hcen : (x : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      let bB : ↥Bs := ⟨b', hb'⟩
      have hb'X : (b' : G) ∈ Subgroup.normalizer (X : Set G) := hN hb'
      have hyX : (b' : G) * (x : G) * (b' : G)⁻¹ ∈ X :=
        ((Subgroup.mem_normalizer_iff.mp hb'X) (x : G)).mp x.2
      have hconjpow : ((b' : G) * (x : G) * (b' : G)⁻¹) ^ p = 1 := by
        rw [conj_pow, hxpG]
        simp
      have hyp : (⟨(b' : G) * (x : G) * (b' : G)⁻¹, hyX⟩ : ↥X) ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow]
        exact hconjpow
      have hψy : ψ (⟨(b' : G) * (x : G) * (b' : G)⁻¹, hyX⟩ : ↥X) = eps b := by
        have harg : (⟨(b' : G) * (x : G) * (b' : G)⁻¹, hyX⟩ : ↥X) = Λ (eps bB) x := by
          rw [(hspec' bB).2]
          exact Subtype.ext (ggGamma_coe X hN bB x).symm
        rw [harg]
        calc ψ (Λ (eps bB) x) = eps bB * ψ x * (eps bB)⁻¹ := hΛn _ _
          _ = eps bB * eps b * (eps bB)⁻¹ := by rw [← hb]
          _ = eps b * eps bB * (eps bB)⁻¹ :=
              by rw [hEc (eps bB) (hspec' bB).1 (eps b) (hspec' b).1]
          _ = eps b := mul_inv_cancel_right _ _
      have hyx : (⟨(b' : G) * (x : G) * (b' : G)⁻¹, hyX⟩ : ↥X) = x :=
        pow_eq_one_unique_of_psi_eq hZp ψ hker hyp hxp (by rw [hψy, ← hb])
      have hconj_eq : (b' : G) * (x : G) * (b' : G)⁻¹ = (x : G) := by
        simpa using congrArg Subtype.val hyx
      calc (b' : G) * (x : G) = ((b' : G) * (x : G) * (b' : G)⁻¹) * (b' : G) := by group
        _ = (x : G) * (b' : G) := by rw [hconj_eq]
    exact hSC (x : G) hcen hxpG
  have hlift : ∀ b : ↥Bs, ∃ x : ↥X, (x : G) ∈ Bs ∧ ψ x = eps b := by
    intro b
    obtain ⟨x₀, hx₀⟩ := hψ (eps b)
    have hx₀p : (x₀ ^ p)⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_inv, map_pow, hx₀, hepsp b, inv_one]
    obtain ⟨z, hzmem, hz⟩ := exists_pow_eq_of_mem_ker hZp ψ hker hx₀p
    have hzc : Commute x₀ z := Subgroup.mem_center_iff.mp (hker hzmem) x₀
    have hxp : (x₀ * z) ^ p = 1 := by
      rw [hzc.mul_pow p, hz, mul_inv_cancel]
    have hψx : ψ (x₀ * z) = eps b := by
      rw [map_mul, hx₀, MonoidHom.mem_ker.mp hzmem, mul_one]
    exact ⟨x₀ * z, hmemX _ hxp (by rw [hψx]; exact (hspec' b).1), hψx⟩
  let xb : ↥Bs → ↥X := fun b => (hlift b).choose
  have hxbBs : ∀ b, ((xb b : ↥X) : G) ∈ Bs := fun b => ((hlift b).choose_spec).1
  have hxbψ : ∀ b, ψ (xb b) = eps b := fun b => ((hlift b).choose_spec).2
  have hxbpG : ∀ b, ((xb b : ↥X) : G) ^ p = 1 := fun b => hBs.2 _ (hxbBs b)
  let cb : ↥Bs → ↥Bs := fun b =>
    (⟨((xb b : ↥X) : G), hxbBs b⟩ : ↥Bs)⁻¹ * b
  have hcbBs : ∀ b, (cb b : G) ∈ Bs := fun b =>
    Bs.mul_mem (Bs.inv_mem (hxbBs b)) b.2
  have hcbε : ∀ b, eps (cb b) = 1 := by
    intro b
    let b' : ↥Bs := ⟨((xb b : ↥X) : G), hxbBs b⟩
    have hb'ε : eps b' = eps b := by
      rw [hinner b' (xb b).2]
      exact hxbψ b
    have hcb' : cb b = b'⁻¹ * b := rfl
    rw [hcb', map_mul, map_inv, hb'ε, inv_mul_cancel]
  have hcbC : ∀ b, (cb b : G) ∈ Subgroup.centralizer (X : Set G) := fun b =>
    (hker' (cb b)).mp (hcbε b)
  have hcbcoe : ∀ b, (cb b : G) = ((xb b : ↥X) : G)⁻¹ * (b : G) := fun b => rfl
  have hconj_mem : ∀ (h : ↥X), ψ h ∈ Subgroup.normalizer (E : Set H) →
      ∀ y : ↥Bs, (h : G) * (y : G) * (h : G)⁻¹ ∈ Bs := by
    intro h hh y
    have hdecomp : (y : G) = ((xb y : ↥X) : G) * (cb y : G) := by
      rw [hcbcoe]
      group
    have hy1 : (h : G) * ((xb y : ↥X) : G) * (h : G)⁻¹ ∈ Bs := by
      have hy1X : (h : G) * ((xb y : ↥X) : G) * (h : G)⁻¹ ∈ X :=
        X.mul_mem (X.mul_mem h.2 (xb y).2) (X.inv_mem h.2)
      refine hmemX ⟨_, hy1X⟩ ?_ ?_
      · have hconjpow : ((h : G) * ((xb y : ↥X) : G) * (h : G)⁻¹) ^ p = 1 := by
          rw [conj_pow, hxbpG y]
          simp
        apply Subtype.ext
        rw [Subgroup.coe_pow]
        exact hconjpow
      · have harg : (⟨(h : G) * ((xb y : ↥X) : G) * (h : G)⁻¹, hy1X⟩ : ↥X) =
            Λ (ψ h) (xb y) := by
          rw [hΛc]
          exact Subtype.ext rfl
        rw [show ψ ⟨_, hy1X⟩ = ψ (Λ (ψ h) (xb y)) from congrArg ψ harg, hΛn, hxbψ]
        exact ((Subgroup.mem_normalizer_iff.mp hh) (eps y)).mp ((hspec' y).1)
    have hy2 : (h : G) * (cb y : G) * (h : G)⁻¹ = (cb y : G) := by
      have hcomm : (h : G) * (cb y : G) = (cb y : G) * (h : G) :=
        Subgroup.mem_centralizer_iff.mp (hcbC y) (h : G) h.2
      rw [hcomm, mul_inv_cancel_right]
    have hsplit : (h : G) * (y : G) * (h : G)⁻¹ =
        ((h : G) * ((xb y : ↥X) : G) * (h : G)⁻¹) *
          ((h : G) * (cb y : G) * (h : G)⁻¹) := by
      rw [hdecomp]
      group
    rw [hsplit, hy2]
    exact Bs.mul_mem hy1 (hcbBs y)
  have hnorm1 : ∀ g : ↥X, ψ g ∈ Subgroup.normalizer (E : Set H) →
      (g : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconj_mem g hg ⟨y, hy⟩
    · intro hy
      have hg' : ψ (g⁻¹) ∈ Subgroup.normalizer (E : Set H) := by
        rw [map_inv]
        exact (Subgroup.normalizer (E : Set H)).inv_mem hg
      have h1 : (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * ((g : G)⁻¹)⁻¹ ∈ Bs := by
        simpa using hconj_mem g⁻¹ hg' ⟨(g : G) * y * (g : G)⁻¹, hy⟩
      rwa [show (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * ((g : G)⁻¹)⁻¹ = y from by
        group] at h1
  have hfwd : ∀ g : ↥X, (g : G) ∈ Subgroup.normalizer (Bs : Set G) →
      ∀ c ∈ E, ψ g * c * (ψ g)⁻¹ ∈ E := by
    intro g hg c hc
    obtain ⟨y, hy⟩ := honto c hc
    have hxbBs' : (g : G) * ((xb y : ↥X) : G) * (g : G)⁻¹ ∈ Bs :=
      ((Subgroup.mem_normalizer_iff.mp hg) ((xb y : ↥X) : G)).mp (hxbBs y)
    have hxbX' : (g : G) * ((xb y : ↥X) : G) * (g : G)⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem g.2 (xb y).2) (X.inv_mem g.2)
    have hψconj : ψ (⟨(g : G) * ((xb y : ↥X) : G) * (g : G)⁻¹, hxbX'⟩ : ↥X) =
        ψ g * c * (ψ g)⁻¹ := by
      have harg : (⟨(g : G) * ((xb y : ↥X) : G) * (g : G)⁻¹, hxbX'⟩ : ↥X) =
          Λ (ψ g) (xb y) := by
        rw [hΛc]
        exact Subtype.ext rfl
      rw [show ψ ⟨_, hxbX'⟩ = ψ (Λ (ψ g) (xb y)) from congrArg ψ harg, hΛn, hxbψ, hy]
    rw [← hψconj, ← hinner ⟨_, hxbBs'⟩ hxbX']
    exact (hspec' _).1
  have hnorm2 : ∀ g : ↥X, (g : G) ∈ Subgroup.normalizer (Bs : Set G) →
      ψ g ∈ Subgroup.normalizer (E : Set H) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hfwd g hg c hc
    · intro hc
      have hg' : ((g⁻¹ : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
        have h := (Subgroup.normalizer (Bs : Set G)).inv_mem hg
        simpa using h
      have h1 := hfwd g⁻¹ hg' (ψ g * c * (ψ g)⁻¹) hc
      rw [map_inv] at h1
      have h2 : (ψ g)⁻¹ * (ψ g * c * (ψ g)⁻¹) * ((ψ g)⁻¹)⁻¹ = c := by group
      rwa [h2] at h1
  have huniqX : ∀ x x' : ↥X, (x : G) ∈ Bs → (x' : G) ∈ Bs → ψ x = ψ x' → x = x' := by
    intro x x' hx hx' hψ'
    exact pow_eq_one_unique_of_psi_eq hZp ψ hker
      (Subtype.ext (by simpa using hBs.2 (x : G) hx))
      (Subtype.ext (by simpa using hBs.2 (x' : G) hx')) hψ'
  have hequiv : ∀ (g : ↥X) (b : ↥Bs) (hb : (g : G) * b * (g : G)⁻¹ ∈ Bs),
      eps ⟨_, hb⟩ = ψ g * eps b * (ψ g)⁻¹ := by
    intro g b hb
    apply hΛ
    have hgg : ggGamma X hN ⟨_, hb⟩ =
        MulAut.conj g * ggGamma X hN b * MulAut.conj g⁻¹ := by
      ext y
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ggGamma_coe]
      group
    rw [map_mul, map_mul, map_inv]
    calc Λ (eps ⟨_, hb⟩) = ggGamma X hN ⟨_, hb⟩ := (hspec' _).2
      _ = MulAut.conj g * ggGamma X hN b * MulAut.conj g⁻¹ := hgg
      _ = Λ (ψ g) * Λ (eps b) * (Λ (ψ g))⁻¹ := by rw [hΛc, (hspec' b).2, map_inv]
  exact ⟨eps, (fun b => (hspec' b).2), (fun b => (hspec' b).1), honto, hker', hinner,
    hlift, huniqX, hnorm1, hnorm2, hequiv⟩

private theorem ggCover_aut_eq_of_eps_eq {G H : Type} [Group G] [Group H]
    {Bs X : Subgroup G} (ψ : ↥X →* H) (ε : ↥Bs →* H)
    (hεker : ∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G))
    (hεX : ∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = ψ ⟨b, hb⟩)
    (hεlift : ∀ b, ∃ x : ↥X, (x : G) ∈ Bs ∧ ψ x = ε b)
    (huniq : ∀ x x' : ↥X, (x : G) ∈ Bs → (x' : G) ∈ Bs → ψ x = ψ x' → x = x')
    {σ τ : MulAut ↥Bs} (hσ : σ ∈ ggAutomizer X Bs) (hτ : τ ∈ ggAutomizer X Bs)
    (hε : ∀ b, ε (σ b) = ε (τ b)) : σ = τ := by
  obtain ⟨s, hsX, -, hσs⟩ := mem_ggAutomizer_iff.mp hσ
  obtain ⟨t, htX, -, hτt⟩ := mem_ggAutomizer_iff.mp hτ
  refine MulEquiv.ext fun b => ?_
  obtain ⟨x, hxB, hxε⟩ := hεlift b
  let b₀ : ↥Bs := ⟨(x : G), hxB⟩
  have hb₀X : (b₀ : G) ∈ X := x.2
  have hb₀ε : ε b₀ = ε b := (hεX b₀ hb₀X).trans hxε
  let c : ↥Bs := b * b₀⁻¹
  have hcε : ε c = 1 := by
    change ε (b * b₀⁻¹) = 1
    rw [map_mul, map_inv, hb₀ε, mul_inv_cancel]
  have hcX : (c : G) ∈ Subgroup.centralizer (X : Set G) := (hεker c).mp hcε
  have hσc : σ c = c := by
    apply Subtype.ext
    rw [hσs c, (Subgroup.mem_centralizer_iff.mp hcX) s hsX, mul_inv_cancel_right]
  have hτc : τ c = c := by
    apply Subtype.ext
    rw [hτt c, (Subgroup.mem_centralizer_iff.mp hcX) t htX, mul_inv_cancel_right]
  have hσX : (σ b₀ : G) ∈ X := by
    rw [hσs b₀]
    exact X.mul_mem (X.mul_mem hsX hb₀X) (X.inv_mem hsX)
  have hτX : (τ b₀ : G) ∈ X := by
    rw [hτt b₀]
    exact X.mul_mem (X.mul_mem htX hb₀X) (X.inv_mem htX)
  have hσb₀ : σ b₀ = τ b₀ := by
    have h := huniq ⟨σ b₀, hσX⟩ ⟨τ b₀, hτX⟩ (σ b₀).2 (τ b₀).2 (by
      rw [← hεX (σ b₀) hσX, ← hεX (τ b₀) hτX]
      exact hε b₀)
    exact Subtype.ext (congrArg (fun x : ↥X => (x : G)) h)
  have hb : c * b₀ = b := by dsimp only [c]; group
  calc σ b = σ (c * b₀) := congrArg σ hb.symm
    _ = σ c * σ b₀ := map_mul σ c b₀
    _ = τ c * τ b₀ := by rw [hσc, hτc, hσb₀]
    _ = τ (c * b₀) := (map_mul τ c b₀).symm
    _ = τ b := congrArg τ hb

theorem ggCover_automizer {G H : Type} [Group G] [Group H] {Bs X : Subgroup G}
    (ψ : ↥X →* H) (hψ : Function.Surjective ψ) {E : Subgroup H}
    (ε : ↥Bs →* H) (hεE : ∀ b, ε b ∈ E)
    (hεsurj : ∀ c ∈ E, ∃ b, ε b = c)
    (hεker : ∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G))
    (hεX : ∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = ψ ⟨b, hb⟩)
    (hεlift : ∀ b, ∃ x : ↥X, (x : G) ∈ Bs ∧ ψ x = ε b)
    (huniq : ∀ x x' : ↥X, (x : G) ∈ Bs → (x' : G) ∈ Bs → ψ x = ψ x' → x = x')
    (hN1 : ∀ g : ↥X, ψ g ∈ Subgroup.normalizer (E : Set H) →
      (g : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hN2 : ∀ g : ↥X, (g : G) ∈ Subgroup.normalizer (Bs : Set G) →
      ψ g ∈ Subgroup.normalizer (E : Set H))
    (hεconj : ∀ (g : ↥X) (b : ↥Bs) (hb : (g : G) * b * (g : G)⁻¹ ∈ Bs),
      ε ⟨_, hb⟩ = ψ g * ε b * (ψ g)⁻¹) :
    ∃ θ : ↥(ggAutomizer X Bs) ≃* ↥(ggAutomizer (⊤ : Subgroup H) E),
      ∀ (σ : ↥(ggAutomizer X Bs)) (b : ↥Bs),
        ((θ σ : MulAut ↥E) ⟨ε b, hεE b⟩ : H) = ε ((σ : MulAut ↥Bs) b) := by
  classical
  let β : ↥Bs →* ↥E := ε.codRestrict E hεE
  have hβsurj : Function.Surjective β := by
    intro e
    obtain ⟨b, hb⟩ := hεsurj e e.2
    exact ⟨b, Subtype.ext hb⟩
  have hex : ∀ σ : ↥(ggAutomizer X Bs),
      ∃ ρ : ↥(ggAutomizer (⊤ : Subgroup H) E),
        ∀ b, (ρ : MulAut ↥E) (β b) = β ((σ : MulAut ↥Bs) b) := by
    intro σ
    obtain ⟨g, hgX, hgN, hσg⟩ := mem_ggAutomizer_iff.mp σ.2
    let gX : ↥X := ⟨g, hgX⟩
    have hgE : ψ gX ∈ Subgroup.normalizer (E : Set H) := hN2 gX hgN
    refine ⟨⟨ggConjAut E hgE, ggConjAut_mem_ggAutomizer (Subgroup.mem_top _) hgE⟩, ?_⟩
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply]
    have hb : (g : G) * b * (g : G)⁻¹ ∈ Bs :=
      ((Subgroup.mem_normalizer_iff.mp hgN) (b : G)).mp b.2
    calc ψ gX * ε b * (ψ gX)⁻¹ = ε ⟨_, hb⟩ := (hεconj gX b hb).symm
      _ = ε ((σ : MulAut ↥Bs) b) := congrArg ε (Subtype.ext (hσg b).symm)
  let θfun : ↥(ggAutomizer X Bs) → ↥(ggAutomizer (⊤ : Subgroup H) E) :=
    fun σ => (hex σ).choose
  have hspec : ∀ (σ : ↥(ggAutomizer X Bs)) (b : ↥Bs),
      (θfun σ : MulAut ↥E) (β b) = β ((σ : MulAut ↥Bs) b) :=
    fun σ => (hex σ).choose_spec
  let Θ : ↥(ggAutomizer X Bs) →* ↥(ggAutomizer (⊤ : Subgroup H) E) :=
    { toFun := θfun
      map_one' := by
        apply Subtype.ext
        refine MulEquiv.ext fun e => ?_
        obtain ⟨b, rfl⟩ := hβsurj e
        rw [hspec]
        rfl
      map_mul' := by
        intro σ τ
        apply Subtype.ext
        refine MulEquiv.ext fun e => ?_
        obtain ⟨b, rfl⟩ := hβsurj e
        change (θfun (σ * τ) : MulAut ↥E) (β b) =
          (θfun σ : MulAut ↥E) ((θfun τ : MulAut ↥E) (β b))
        rw [hspec, hspec, hspec]
        rfl }
  have hΘinj : Function.Injective Θ := by
    intro σ τ h
    apply Subtype.ext
    refine ggCover_aut_eq_of_eps_eq ψ ε hεker hεX hεlift huniq σ.2 τ.2 fun b => ?_
    have hs := congrArg Subtype.val (hspec σ b)
    have ht := congrArg Subtype.val (hspec τ b)
    change θfun σ = θfun τ at h
    rw [h] at hs
    exact hs.symm.trans ht
  have hΘsurj : Function.Surjective Θ := by
    intro ρ
    obtain ⟨g, -, hgN, hρg⟩ := mem_ggAutomizer_iff.mp ρ.2
    obtain ⟨x, hx⟩ := hψ g
    have hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G) := hN1 x (hx ▸ hgN)
    let σ : ↥(ggAutomizer X Bs) :=
      ⟨ggConjAut Bs hxN, ggConjAut_mem_ggAutomizer x.2 hxN⟩
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    refine MulEquiv.ext fun e => ?_
    obtain ⟨b, rfl⟩ := hβsurj e
    apply Subtype.ext
    change ((θfun σ : MulAut ↥E) (β b) : H) = ((ρ : MulAut ↥E) (β b) : H)
    rw [hspec]
    have hb : (x : G) * b * (x : G)⁻¹ ∈ Bs :=
      ((Subgroup.mem_normalizer_iff.mp hxN) (b : G)).mp b.2
    have hσb : (σ : MulAut ↥Bs) b = ⟨_, hb⟩ := Subtype.ext (ggConjAut_apply Bs hxN b)
    change ε ((σ : MulAut ↥Bs) b) = ((ρ : MulAut ↥E) (β b) : H)
    rw [hσb, hεconj, hx, hρg]
    rfl
  exact ⟨MulEquiv.ofBijective Θ ⟨hΘinj, hΘsurj⟩, fun σ b =>
    congrArg Subtype.val (hspec σ b)⟩

end CFSG.StandardType

end
