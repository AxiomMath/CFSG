module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL46J

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace GGL48

variable {G : Type} [Group G]

theorem inv_mul_pow_mul (x y : G) (k : ℕ) : x⁻¹ * y ^ k * x = (x⁻¹ * y * x) ^ k := by
  have h := conj_pow (a := x⁻¹) (b := y) (i := k)
  rw [inv_inv] at h
  exact h.symm

theorem mul_pow_eq_of_conj {x' u a : G} (hxu : x'⁻¹ * u * x' = u * a) (hxa : x'⁻¹ * a * x' = a)
    (hua : Commute u a) (n : ℕ) :
    (x' * u) ^ n = x' ^ n * (u ^ n * a ^ (∑ i ∈ Finset.range n, i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : x'⁻¹ * (u ^ n * a ^ (∑ i ∈ Finset.range n, i)) * x' =
        (u * a) ^ n * a ^ (∑ i ∈ Finset.range n, i) := by
      have : x'⁻¹ * (u ^ n * a ^ (∑ i ∈ Finset.range n, i)) * x' =
          (x'⁻¹ * u ^ n * x') * (x'⁻¹ * a ^ (∑ i ∈ Finset.range n, i) * x') := by group
      rw [this, inv_mul_pow_mul, inv_mul_pow_mul, hxu, hxa]
    have e2 : (u * a) ^ n * a ^ (∑ i ∈ Finset.range n, i) * u =
        u ^ (n + 1) * a ^ (∑ i ∈ Finset.range (n + 1), i) := by
      rw [hua.mul_pow, Finset.sum_range_succ, pow_add a, pow_succ u]
      have h1 : Commute (a ^ n) u := (hua.symm.pow_left n)
      have h2 : Commute (a ^ (∑ i ∈ Finset.range n, i)) u := (hua.symm.pow_left _)
      have h3 : Commute (a ^ (∑ i ∈ Finset.range n, i)) (a ^ n) := Commute.pow_pow_self a _ _
      calc u ^ n * a ^ n * a ^ (∑ i ∈ Finset.range n, i) * u
          = u ^ n * (a ^ n * (a ^ (∑ i ∈ Finset.range n, i) * u)) := by group
        _ = u ^ n * (a ^ n * (u * a ^ (∑ i ∈ Finset.range n, i))) := by rw [h2.eq]
        _ = u ^ n * ((a ^ n * u) * a ^ (∑ i ∈ Finset.range n, i)) := by group
        _ = u ^ n * ((u * a ^ n) * a ^ (∑ i ∈ Finset.range n, i)) := by rw [h1.eq]
        _ = u ^ n * u * (a ^ (∑ i ∈ Finset.range n, i) * a ^ n) := by
          rw [h3.eq]; group
    calc (x' * u) ^ (n + 1) = (x' * u) ^ n * (x' * u) := pow_succ _ _
      _ = x' ^ n * (u ^ n * a ^ (∑ i ∈ Finset.range n, i)) * (x' * u) := by rw [ih]
      _ = x' ^ n * x' * (x'⁻¹ * (u ^ n * a ^ (∑ i ∈ Finset.range n, i)) * x') * u := by group
      _ = x' ^ (n + 1) * ((u * a) ^ n * a ^ (∑ i ∈ Finset.range n, i) * u) := by
        rw [e1, ← pow_succ]; group
      _ = x' ^ (n + 1) * (u ^ (n + 1) * a ^ (∑ i ∈ Finset.range (n + 1), i)) := by rw [e2]

theorem mul_pow_prime_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x' u a : G}
    (hxu : x'⁻¹ * u * x' = u * a) (hxa : x'⁻¹ * a * x' = a) (hua : Commute u a)
    (hx'p : x' ^ p = 1) (hap : a ^ p = 1) : (x' * u) ^ p = u ^ p := by
  rw [mul_pow_eq_of_conj hxu hxa hua p, hx'p, one_mul]
  have hsum := Finset.sum_range_id_mul_two p
  have hdvd : p ∣ ∑ i ∈ Finset.range p, i := by
    have h2 : p ∣ (∑ i ∈ Finset.range p, i) * 2 := hsum ▸ dvd_mul_right p (p - 1)
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, pow_mul, hap, one_pow, mul_one]

theorem isPGroup_zpowers_of_pow_eq_one {H : Type*} [Group H] {p : ℕ} {w : H} (hw : w ^ p = 1) :
    IsPGroup p (Subgroup.zpowers w) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨1, Subtype.ext ?_⟩
  change (w ^ n) ^ p ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]

theorem exists_conj_mem_sup_of_pow_eq_one [Finite G] {p : ℕ} [Fact p.Prime]
    {C₀ U₁ : Subgroup G} {x' : G} (hU₁C : U₁ ≤ C₀)
    (hpel : ∀ c ∈ C₀, ∀ k : ℕ, c ^ p ^ k = 1 → c ∈ U₁) (hU₁p : IsPGroup p U₁)
    (hx'C : x' ∈ Subgroup.normalizer (C₀ : Set G))
    (hx'U : x' ∈ Subgroup.normalizer (U₁ : Set G)) (hx'p : x' ^ p = 1) {z : G}
    (hzT : z ∈ C₀ ⊔ Subgroup.zpowers x') (hzp : z ^ p = 1) :
    ∃ g ∈ C₀ ⊔ Subgroup.zpowers x', g * z * g⁻¹ ∈ U₁ ⊔ Subgroup.zpowers x' := by
  set T : Subgroup G := C₀ ⊔ Subgroup.zpowers x' with hT
  set S : Subgroup G := U₁ ⊔ Subgroup.zpowers x' with hSdef
  have hST : S ≤ T := sup_le_sup_right hU₁C _
  have hSp : IsPGroup p S := IsPGroup.to_sup_of_normal_left' hU₁p
    (isPGroup_zpowers_of_pow_eq_one hx'p) (Subgroup.zpowers_le.mpr hx'U)
  have hmax : ∀ P : Subgroup G, IsPGroup p P → S ≤ P → P ≤ T → P = S := by
    intro P hPp hSP hPT
    refine le_antisymm (fun g hgP => ?_) hSP
    have hg' : g ∈ ((Subgroup.zpowers x' ⊔ C₀ : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hPT hgP
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.zpowers_le.mpr hx'C)] at hg'
    obtain ⟨w, hw, c, hc, rfl⟩ := hg'
    have hwP : w ∈ P := hSP (Subgroup.mem_sup_right hw)
    have hcP : c ∈ P := by
      have := P.mul_mem (P.inv_mem hwP) hgP
      simpa using this
    obtain ⟨k, hk⟩ := hPp ⟨c, hcP⟩
    have hck : c ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact S.mul_mem (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left (hpel c hc k hck))
  have hSTp : IsPGroup p (S.subgroupOf T) :=
    hSp.comap_of_injective T.subtype T.subtype_injective
  let ST : Sylow p ↥T := ⟨S.subgroupOf T, hSTp, fun {Q} hQ hSQ => by
    have hQm : IsPGroup p (Q.map T.subtype) := hQ.map T.subtype
    have hSQm : S ≤ Q.map T.subtype := fun s hs =>
      ⟨⟨s, hST hs⟩, hSQ (by rw [Subgroup.mem_subgroupOf]; exact hs), rfl⟩
    have heq := hmax _ hQm hSQm (Subgroup.map_subtype_le Q)
    ext g
    rw [Subgroup.mem_subgroupOf, ← heq]
    constructor
    · intro hgQ
      exact ⟨g, hgQ, rfl⟩
    · rintro ⟨g', hg'Q, hgg⟩
      have : g' = g := Subtype.ext hgg
      rw [← this]
      exact hg'Q⟩
  have hz' : IsPGroup p (Subgroup.zpowers (⟨z, hzT⟩ : ↥T)) :=
    isPGroup_zpowers_of_pow_eq_one (Subtype.ext (by simpa using hzp))
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup hz' ST
  refine ⟨g, g.2, ?_⟩
  have h1 := hg _ (Subgroup.mem_zpowers _)
  change _ ∈ S.subgroupOf T at h1
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

end GGL48

section Config

variable {G : Type} [Group G]

@[expose] def GGL48Homocyclic (p : ℕ) (U₁ : Subgroup G) : Prop :=
  ∀ s : ℕ, 2 ≤ s → (∀ u ∈ U₁, u ^ p ^ s = 1) → (∃ u ∈ U₁, orderOf u = p ^ s) →
    ∀ b ∈ U₁, b ^ p = 1 → ∃ v ∈ U₁, v ^ p ^ (s - 1) = b

variable [Finite G]

theorem normalizer_le_sup_of_homocyclic {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) (hhom : GGL48Homocyclic p U₁) :
    Subgroup.normalizer (U₁ : Set G) ≤ ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G) := by
  obtain ⟨hp, hxp, hxN, -, hpel⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hS.1.1.1.2.2.2.2.2.1.2.1
  obtain ⟨hab, ⟨s, hs2, hexp, ⟨u₀, hu₀, hord⟩, ⟨x', hx'x, hx'⟩, -⟩, -, -⟩ := h46
  have hU₁p : IsPGroup p U₁ := hRp.to_le (mem_thompsonAbelianSubgroups_of_forall_eq hA).1
  set C₀ : Subgroup G := Subgroup.centralizer (U₁ : Set G) with hC₀
  set N₀ : Subgroup G := Subgroup.normalizer (U₁ : Set G) with hN₀
  have hU₁C : U₁ ≤ C₀ := Subgroup.le_centralizer_iff_isMulCommutative.mpr hab
  have hCN : C₀ ≤ N₀ := Subgroup.centralizer_le_normalizer _
  have hU₁N : U₁ ≤ N₀ := hU₁C.trans hCN
  have hNC : N₀ ≤ Subgroup.normalizer (C₀ : Set G) := ggNormalizer_le_normalizer_centralizer U₁
  have hx'mem : x' ∈ Subgroup.zpowers x := hx'x ▸ Subgroup.mem_zpowers x'
  have hxmem : x ∈ Subgroup.zpowers x' := hx'x.symm ▸ Subgroup.mem_zpowers x
  have hx'p : x' ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'mem
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hx'N : x' ∈ N₀ := (Subgroup.zpowers_le.mpr hxN) hx'mem
  have hcx : ∀ m : G, m * x' * m⁻¹ = x' → m ∈ Subgroup.centralizer ({x} : Set G) := by
    intro m hm
    have hc : Commute m x' := by
      show m * x' = x' * m
      calc m * x' = m * x' * m⁻¹ * m := by group
        _ = x' * m := by rw [hm]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxmem
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc.zpow_right k).eq
  have hx'H : x' ∈ ggL48H0 x U₁ := ⟨hcx x' (by group), hx'N⟩
  have hzC : ∀ i : ℕ, x' ^ i ∈ C₀ → x' ^ i = 1 := by
    intro i hi
    by_cases hpi : p ∣ i
    · obtain ⟨c, rfl⟩ := hpi
      rw [pow_mul, hx'p, one_pow]
    · exfalso
      have h1 := pow_pow_sub_one_eq_one_of_commute hs2 hexp hx' hpi hu₀
        ((Subgroup.mem_centralizer_iff.mp hi) u₀ hu₀).symm
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at h2
      have h3 := Nat.le_of_dvd (pow_pos hp.pos _) h2
      have h4 : p ^ (s - 1) < p ^ s := Nat.pow_lt_pow_right hp.one_lt (by omega)
      omega
  intro n hn
  set z : G := n⁻¹ * x' * n with hz
  have hcn : n⁻¹ * x' * n⁻¹⁻¹ * x'⁻¹ ∈ C₀ :=
    GGL48.conj_mul_inv_mem_centralizer hx' (N₀.inv_mem hn)
  rw [inv_inv] at hcn
  have hzT : z ∈ C₀ ⊔ Subgroup.zpowers x' := by
    have : z = (n⁻¹ * x' * n * x'⁻¹) * x' := by rw [hz]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcn)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x'))
  have hzp : z ^ p = 1 := by
    rw [hz, show n⁻¹ * x' * n = n⁻¹ * x' * n⁻¹⁻¹ by rw [inv_inv], conj_pow, hx'p]
    group
  obtain ⟨g, hgT, hgS⟩ := GGL48.exists_conj_mem_sup_of_pow_eq_one hU₁C
    (fun c hc k hk => hpel c hc k hk) hU₁p (hNC hx'N) hx'N hx'p hzT hzp
  have hTN : C₀ ⊔ Subgroup.zpowers x' ≤ N₀ := sup_le hCN (Subgroup.zpowers_le.mpr hx'N)
  have hgN : g ∈ N₀ := hTN hgT
  have hgS' : g * z * g⁻¹ ∈ ((Subgroup.zpowers x' ⊔ U₁ : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hgS
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.zpowers_le.mpr hx'N)] at hgS'
  obtain ⟨w, hw, u, hu, hwu⟩ := hgS'
  dsimp only at hwu
  replace hwu : g * z * g⁻¹ = w * u := hwu.symm
  have hm : (g * n⁻¹) * x' * (g * n⁻¹)⁻¹ * x'⁻¹ ∈ C₀ :=
    GGL48.conj_mul_inv_mem_centralizer hx' (N₀.mul_mem hgN (N₀.inv_mem hn))
  have hwx : w * x'⁻¹ ∈ C₀ := by
    have e : w * x'⁻¹ = ((g * n⁻¹) * x' * (g * n⁻¹)⁻¹ * x'⁻¹) * (x' * u⁻¹ * x'⁻¹) := by
      have h1 : (g * n⁻¹) * x' * (g * n⁻¹)⁻¹ = w * u := by rw [← hwu, hz]; group
      rw [h1]
      group
    have hconj : x' * u⁻¹ * x'⁻¹ ∈ C₀ :=
      hU₁C ((Subgroup.mem_normalizer_iff.mp hx'N _).mp (U₁.inv_mem hu))
    rw [e]
    exact C₀.mul_mem hm hconj
  have hw' : w = x' := by
    have hwz : w * x'⁻¹ ∈ Subgroup.zpowers x' :=
      Subgroup.mul_mem _ hw (Subgroup.inv_mem _ (Subgroup.mem_zpowers x'))
    rw [← mem_powers_iff_mem_zpowers] at hwz
    obtain ⟨i, hi⟩ := hwz
    dsimp only at hi
    have := hzC i (by rw [hi]; exact hwx)
    rw [hi] at this
    calc w = w * x'⁻¹ * x' := by group
      _ = x' := by rw [this, one_mul]
  rw [hw'] at hwu
  have hupow : ∀ v ∈ U₁, v ^ (p ^ (s - 1) * p ^ (s - 1)) = 1 := by
    intro v hv
    have e : p ^ (s - 1) * p ^ (s - 1) = p ^ s * p ^ (s - 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [e, pow_mul, hexp v hv, one_pow]
  have hup : u ^ p = 1 := by
    set a : G := u ^ p ^ (s - 1) with ha
    have haU : a ∈ U₁ := U₁.pow_mem hu _
    have hxu : x'⁻¹ * u * x' = u * a := by rw [hx' u hu, pow_add, pow_one]
    have hxa : x'⁻¹ * a * x' = a := by
      rw [hx' a haU, pow_add, pow_one, ha, ← pow_mul, hupow u hu, mul_one]
    have hap : a ^ p = 1 := by
      rw [ha, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s), hexp u hu]
    have h1 := GGL48.mul_pow_prime_eq hp hp2 hxu hxa ((Commute.refl u).pow_right _) hx'p hap
    rw [← h1, ← hwu, conj_pow, hzp]
    group
  obtain ⟨v, hv, hvu⟩ := hhom s hs2 hexp ⟨u₀, hu₀, hord⟩ u hu hup
  have hvx : v * x' * v⁻¹ = x' * u := by
    calc v * x' * v⁻¹ = x' * (x'⁻¹ * v * x') * v⁻¹ := by group
      _ = x' * v ^ (1 + p ^ (s - 1)) * v⁻¹ := by rw [hx' v hv]
      _ = x' * u := by
        rw [pow_add, pow_one, hvu]
        have hc : Commute v u := hvu ▸ (Commute.refl v).pow_right _
        calc x' * (v * u) * v⁻¹ = x' * (u * v) * v⁻¹ := by rw [hc.eq]
          _ = x' * u := by group
  set m : G := v⁻¹ * g * n⁻¹ with hmdef
  have hmx : m * x' * m⁻¹ = x' := by
    have h1 : g * z * g⁻¹ = v * x' * v⁻¹ := by rw [hwu, hvx]
    calc m * x' * m⁻¹ = v⁻¹ * (g * z * g⁻¹) * v := by rw [hmdef, hz]; group
      _ = v⁻¹ * (v * x' * v⁻¹) * v := by rw [h1]
      _ = x' := by group
  have hmH : m ∈ ggL48H0 x U₁ :=
    ⟨hcx m hmx, N₀.mul_mem (N₀.mul_mem (N₀.inv_mem (hU₁N hv)) hgN) (N₀.inv_mem hn)⟩
  have hgHC : g ∈ ggL48H0 x U₁ ⊔ C₀ := by
    have : C₀ ⊔ Subgroup.zpowers x' ≤ ggL48H0 x U₁ ⊔ C₀ :=
      sup_le le_sup_right ((Subgroup.zpowers_le.mpr hx'H).trans le_sup_left)
    exact this hgT
  have hn' : n = m⁻¹ * v⁻¹ * g := by rw [hmdef]; group
  rw [hn']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hmH))
    (Subgroup.mem_sup_right (C₀.inv_mem (hU₁C hv)))) hgHC

end Config

@[expose] def GGL48NonHomocyclicInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁ →
      ∀ R : Subgroup G, IsPGroup p R → (∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R) →
        U ≤ R → (∀ A ∈ thompsonAbelianSubgroups R, A = U₁) →
        x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁ →
        ¬ Subgroup.normalizer (U₁ : Set G) ≤
          ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G) →
        ¬ GGL48Homocyclic p U₁ →
        ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1

theorem ggL48NonCoverInput_of_nonHomocyclic (h : GGL48NonHomocyclicInput) :
    GGL48NonCoverInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA hcent hcov
  exact h G p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA hcent hcov
    fun hhom => hcov (normalizer_le_sup_of_homocyclic hS h46 hRp hRmax hA hhom)

theorem ggL48QuotInput_of_cent_nonHomocyclic (hC : GGL48CentInput)
    (hN : GGL48NonHomocyclicInput) : GGL48QuotInput :=
  ggL48QuotInput_of_cent hC (ggL48NonCoverInput_of_nonHomocyclic hN)

end CFSG.StandardType

end
