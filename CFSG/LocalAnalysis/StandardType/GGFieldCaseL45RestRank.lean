module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestOmega
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem exists_pow_prime_pow_not_mem {p : ℕ} {U₁ : Subgroup G} {w : G}
    (hw : ∃ n : ℕ, w ^ p ^ n = 1) (hwU₁ : w ∉ U₁) :
    ∃ k : ℕ, w ^ p ^ k ∉ U₁ ∧ (w ^ p ^ k) ^ p ∈ U₁ := by
  classical
  have hex : ∃ n : ℕ, w ^ p ^ n ∈ U₁ := by
    obtain ⟨n, hn⟩ := hw
    exact ⟨n, hn ▸ one_mem _⟩
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero, pow_one] at this
    exact hwU₁ this
  refine ⟨Nat.find hex - 1, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
  exact Nat.find_spec hex

theorem mul_pow_mul_mul_pow_mem_iff {V : Subgroup G} {e₁ e₂ g₁ g₂ : G} (he₁ : e₁ ∈ V)
    (he₂ : e₂ ∈ V) (hg₁ : g₁ ∈ Subgroup.normalizer (V : Set G))
    (hg₂ : g₂ ∈ Subgroup.normalizer (V : Set G)) (i j : ℕ) :
    (e₁ * g₁) ^ i * (e₂ * g₂) ^ j ∈ V ↔ g₁ ^ i * g₂ ^ j ∈ V := by
  have h₁ := mul_pow_mul_inv_pow_mem he₁ hg₁ i
  have h₂ := mul_pow_mul_inv_pow_mem he₂ hg₂ j
  have h₃ : g₁ ^ i * ((e₂ * g₂) ^ j * (g₂ ^ j)⁻¹) * (g₁ ^ i)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hg₁ i) _).mp h₂
  have e : (e₁ * g₁) ^ i * (e₂ * g₂) ^ j =
      (((e₁ * g₁) ^ i * (g₁ ^ i)⁻¹) * (g₁ ^ i * ((e₂ * g₂) ^ j * (g₂ ^ j)⁻¹) * (g₁ ^ i)⁻¹)) *
        (g₁ ^ i * g₂ ^ j) := by group
  rw [e]
  exact V.mul_mem_cancel_left (V.mul_mem h₁ h₃)

theorem mul_pow_mem_iff {V : Subgroup G} {e g : G} (he : e ∈ V)
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (i : ℕ) : (e * g) ^ i ∈ V ↔ g ^ i ∈ V := by
  have h := mul_pow_mul_mul_pow_mem_iff he (one_mem V) hg (one_mem _) i 0
  simpa using h

end General

@[expose] def GGL45CyclicD4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → p = 3 →
    LargeEvenMarking K (fun lab _ _ I _ θ => lab.tag = .D ∧ lab.rank = 4 ∧
      ∀ u ∈ U, u ∈ U₁ ↔ ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = u⁻¹ * k * u) φ) →
    ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁

theorem ggL46CyclicD4Input_of_l45 (h : GGL45CyclicD4Input) : GGL46CyclicD4Input :=
  fun G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hp3 hmk =>
    h G p B Bs x L D J X B₂ d y K U U₁ (ggL45Config_of_setup hS) hp3 hmk

theorem GGL45Config.exists_cyclic {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (h : GGRawPCyclicOn GGNotD4Three) (hD4 : GGL45CyclicD4Input)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁ := by
  have hp : p.Prime := hcfg.prime
  have hp2 : p ≠ 2 := hcfg.odd
  obtain ⟨-, hUp, -, -⟩ := hcfg.2.2.2.2.2.2.1
  obtain ⟨hUN, -, hmk⟩ := hcfg.2.2.2.2.2.2.2.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hmk
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  · obtain ⟨ht, hr, hp3⟩ := hD
    refine hD4 G p B Bs x L D J X B₂ d y K U U₁ hcfg hp3 ⟨hK, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, ht, hr, hθ⟩
  · have hraw' := h p hp hp2 lab hlab hD _ hraw
    obtain ⟨R, _, I, F, ⟨hs, hna, θ, hθ⟩, hcyc⟩ := largeEvenRawDatum_exists hraw'
    obtain ⟨J', S, hJ', -, hN, hgen, hpS⟩ := hcyc hs hna
    let ρ : U →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hUN)
    have hρ : ∀ u : U, ρ u = ggLAut K θ ⟨u, hUN u.2⟩ := fun _ => rfl
    have hρS : ∀ u : U, ρ u ∈ S := fun u => by
      obtain ⟨k, hk⟩ := hUp u
      exact hpS _ ⟨k, by rw [← map_pow, hk, map_one]⟩
    refine exists_le_zpowers_sup_of_cyclic ρ hN hgen hρS (fun u => ?_)
    · rw [hθ u u.2, hρ]
      constructor
      · rintro ⟨φ, hφ, hind⟩
        rw [eq_ggLAut_of_induces K θ (hUN u.2) hind, ← hJ'] at hφ
        have := J'.inv_mem hφ
        rw [← map_inv] at this
        convert this using 2
        exact Subtype.ext (by simp)
      · intro hmem
        refine ⟨ggLAut K θ ⟨(u : G)⁻¹, inv_mem (hUN u.2)⟩, ?_,
          largeEvenInduces_ggLAut_inv K θ (inv_mem (hUN u.2))⟩
        rw [← hJ']
        have := J'.inv_mem hmem
        rw [← map_inv] at this
        convert this using 2

theorem ggL46CyclicInput_of_l45 (h : GGRawPCyclicOn GGNotD4Three) (hD4 : GGL45CyclicD4Input) :
    GGL46CyclicInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS => (ggL45Config_of_setup hS).exists_cyclic h hD4

@[expose] def GGL45RankXInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ →
      ∃ a₁ ∈ U₁, ∃ a₂ ∈ U₁,
        (a₁ * x * a₁⁻¹ * x⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
        (a₂ * x * a₂⁻¹ * x⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
        ∀ i j : ℕ, (a₁ * x * a₁⁻¹ * x⁻¹) ^ i * (a₂ * x * a₂⁻¹ * x⁻¹) ^ j ∈
          U ⊓ Subgroup.centralizer (K : Set G) → p ∣ i ∧ p ∣ j

theorem ggL45RankXInput_of_rank (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (h : GGL45RankInput) : GGL45RankXInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg
  obtain ⟨-, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  exact h G p B Bs x L D J X B₂ d y K U U₁ hcfg x (hcfg.bs_le hcfg.x_mem) hxU₁

section Rank

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.exists_conj_eq_mul (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {g₀ : G} (hg₀ : g₀ ∈ U)
    (hcyc : U ≤ Subgroup.zpowers g₀ ⊔ U₁) {n : G} (hn : n ∈ Subgroup.normalizer (U : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) (hw : n * v * n⁻¹ ∉ U₁) :
    ∃ v'' ∈ U ⊓ Subgroup.centralizer (K : Set G), ∃ b ∈ U₁, n * v'' * n⁻¹ = x * b := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  obtain ⟨-, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hwU : n * v * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn v).mp hv.1
  obtain ⟨m, hm⟩ := hcfg.isPGroup ⟨_, hwU⟩
  have hwm : (n * v * n⁻¹) ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨k, hk1, hk2⟩ := exists_pow_prime_pow_not_mem ⟨m, hwm⟩ hw
  rw [conj_pow] at hk1 hk2
  have hw'U : n * v ^ p ^ k * n⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (U.pow_mem hv.1 _)
  obtain ⟨t, b, hb, hxe⟩ := exists_pow_mul_of_cyclic hcfg.le_normalizer_part hg₀ hcyc hw'U hk1
    hk2 hxU (by rw [hcfg.x_pow]; exact one_mem _)
  refine ⟨(v ^ p ^ k) ^ t, Subgroup.pow_mem _ (Subgroup.pow_mem _ hv _) _, b⁻¹, U₁.inv_mem hb, ?_⟩
  rw [← conj_pow, hxe]
  group

theorem ggL45_conj_V_mem_of_rankX (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hcomm : ∀ z ∈ U₁, z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G))
    (hcommU₁ : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G))
    {g₀ : G} (hg₀ : g₀ ∈ U) (hcyc : U ≤ Subgroup.zpowers g₀ ⊔ U₁)
    (hrx : ∃ a₁ ∈ U₁, ∃ a₂ ∈ U₁,
        (a₁ * x * a₁⁻¹ * x⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
        (a₂ * x * a₂⁻¹ * x⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
        ∀ i j : ℕ, (a₁ * x * a₁⁻¹ * x⁻¹) ^ i * (a₂ * x * a₂⁻¹ * x⁻¹) ^ j ∈
          U ⊓ Subgroup.centralizer (K : Set G) → p ∣ i ∧ p ∣ j) {n : G}
    (hn : n ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) : n * v * n⁻¹ ∈ U₁ := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  set V : Subgroup G := U ⊓ Subgroup.centralizer (K : Set G) with hV
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hNV : ∀ u ∈ U, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    mem_normalizer_of_forall_conj_mem fun v hv => by
      have := hcfg.conj_mem_V (U.inv_mem hu) hv
      rwa [inv_inv] at this
  refine ggL45_conj_V_mem_of_moving hraw hiso hcfg (fun n hn hnd v hv => ?_) hn hv
  by_contra hw
  obtain ⟨v'', hv'', b, hb, hvb⟩ := hcfg.exists_conj_eq_mul hraw hiso hg₀ hcyc hn.1 hv hw
  obtain ⟨a₁, ha₁, a₂, ha₂, hp₁, hp₂, hind⟩ := hrx
  have key : ∀ a ∈ U₁, ∃ e ∈ V,
      a * (n * v'' * n⁻¹) * a⁻¹ * (n * v'' * n⁻¹)⁻¹ = e * (a * x * a⁻¹ * x⁻¹) := by
    intro a ha
    set c := a * x * a⁻¹ * x⁻¹ with hc
    have hcU : c ∈ U := U.mul_mem (U.mul_mem (U.mul_mem (hcfg.part_le ha) hxU)
      (U.inv_mem (hcfg.part_le ha))) (U.inv_mem hxU)
    have h1 : x * (a * b * a⁻¹ * b⁻¹) * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hNV x hxU) _).mp (hcommU₁ a ha b hb)
    refine ⟨c * (x * (a * b * a⁻¹ * b⁻¹) * x⁻¹) * c⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hNV c hcU) _).mp h1, ?_⟩
    rw [hvb, hc]
    group
  obtain ⟨e₁, he₁, hc₁⟩ := key a₁ ha₁
  obtain ⟨e₂, he₂, hc₂⟩ := key a₂ ha₂
  have hg₁ : a₁ * x * a₁⁻¹ * x⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    hNV _ (U.mul_mem (U.mul_mem (U.mul_mem (hcfg.part_le ha₁) hxU)
      (U.inv_mem (hcfg.part_le ha₁))) (U.inv_mem hxU))
  have hg₂ : a₂ * x * a₂⁻¹ * x⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    hNV _ (U.mul_mem (U.mul_mem (U.mul_mem (hcfg.part_le ha₂) hxU)
      (U.inv_mem (hcfg.part_le ha₂))) (U.inv_mem hxU))
  have hq₁ := ggL45_comm_mem_zpowers_of_comm hraw hiso hcent hcfg hcomm hn hnd hv'' ha₁
    (by rw [hc₁]; exact (mul_pow_mem_iff he₁ hg₁ p).mpr hp₁)
  have hq₂ := ggL45_comm_mem_zpowers_of_comm hraw hiso hcent hcfg hcomm hn hnd hv'' ha₂
    (by rw [hc₂]; exact (mul_pow_mem_iff he₂ hg₂ p).mpr hp₂)
  have hd'p : (n * d * n⁻¹) ^ p = 1 := by rw [conj_pow, hcfg.d_pow]; group
  refine not_independent_of_mem_zpowers hd'p hq₁ hq₂ V (fun i j hij => hind i j ?_)
  rw [hc₁, hc₂] at hij
  exact (mul_pow_mul_mul_pow_mem_iff he₁ he₂ hg₁ hg₂ i j).mp hij

end Rank

theorem ggL45MovingInput_of_rankX (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (htorus : GGL45TorusInput) (hrankx : GGL45RankXInput)
    (hpc : GGRawPCyclicOn GGNotD4Three) (hD4 : GGL45CyclicD4Input) (hfive : GGL45FiveInput) :
    GGL45MovingInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hFC hTBM hL43 hL44 hL44ii hK hsetup hpart hon r hr
    hrd
  have hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁ :=
    ⟨hFC, hTBM, hL43, hL44, hL44ii, hK, hsetup, hpart,
      fun u hu => hon ⟨Subgroup.le_normalizer hu, hpart.1 hu⟩⟩
  obtain ⟨s, hs, hcommU₁, -, -, x', hx'x, hx'V⟩ := htorus G p B Bs x L D J X B₂ d y K U U₁ hcfg
  have hcomm := fun z (hz : z ∈ U₁) hzp => hcfg.comm_mem_V_of_torus hs hx'x hx'V hz hzp
  obtain ⟨g₀, hg₀, hcyc⟩ := hcfg.exists_cyclic hpc hD4
  have hrx := hrankx G p B Bs x L D J X B₂ d y K U U₁ hcfg
  have hconj := fun n hn v (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) =>
    ggL45_conj_V_mem_of_rankX hraw hiso hcent hcfg hcomm hcommU₁ hg₀ hcyc hrx (n := n) hn hv
  exact hfive G p B Bs x L D J X B₂ d y K U U₁ hcfg hon
    (fun r hr hrd => ggL45_inf_conj_eq_one hraw hiso hcent hcfg hr hrd)
    (fun v hv hvp => ggL45_omega_V_of_conj hraw hiso hcent hcfg hcomm hconj hv hvp)
    hconj r hr hrd

theorem ggL45Input_of_rankX (hN : GGInndiagNormalInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput) (htorus : GGL45TorusInput)
    (hrankx : GGL45RankXInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hD4 : GGL45CyclicD4Input)
    (hfive : GGL45FiveInput) : GGL45Input :=
  ggL45Input_of_moving_rawInnField hN hraw
    (ggL45MovingInput_of_rankX hraw hiso hcent htorus hrankx hpc hD4 hfive)

end CFSG.StandardType

end
