module

public import CFSG.Quasithin.Background.F918Z8Def2
public import CFSG.Quasithin.Background.F918N6
public import CFSG.Quasithin.Background.F918H3
public import CFSG.Quasithin.Background.F918N1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

section Abstract

variable {X : Type} [CommGroup X]

theorem d391nf_cent (hexp : ∀ x : X, x ^ 2 = 1) {H : Subgroup (MulAut X)}
    (hirr : ∀ U : Subgroup X, (∀ h ∈ H, ∀ u ∈ U, h u ∈ U) → U = ⊥ ∨ U = ⊤) {c : MulAut X}
    (hc2 : c ^ 2 = 1) (hcomm : ∀ h ∈ H, c * h = h * c) : c = 1 := by
  have hcc : ∀ v : X, c (c v) = v := fun v => by
    have := congrArg (fun φ : MulAut X => φ v) hc2
    simpa [pow_two, MulAut.mul_apply] using this
  have hhc : ∀ h ∈ H, ∀ v : X, c (h v) = h (c v) := fun h hh v => by
    have := congrArg (fun φ : MulAut X => φ v) (hcomm h hh)
    simpa [MulAut.mul_apply] using this
  let Y : Subgroup X := MonoidHom.eqLocus c.toMonoidHom (MonoidHom.id X)
  have hY : ∀ h ∈ H, ∀ u ∈ Y, h u ∈ Y := fun h hh u hu => by
    have hu' : c u = u := hu
    show c (h u) = h u
    rw [hhc h hh, hu']
  have hfix : ∀ v : X, c v * v⁻¹ ∈ Y := fun v => by
    have hsq : (c v * v⁻¹) * (c v * v⁻¹) = 1 := by
      rw [← pow_two, mul_pow, hexp, inv_pow, hexp]
      simp
    have h2 : c (c v * v⁻¹) = v * (c v)⁻¹ := by
      rw [map_mul, map_inv, hcc]
    have h3 : (c v * v⁻¹)⁻¹ = c v * v⁻¹ := inv_eq_of_mul_eq_one_right hsq
    show c (c v * v⁻¹) = c v * v⁻¹
    rw [h2]
    calc v * (c v)⁻¹ = (c v * v⁻¹)⁻¹ := by simp [mul_comm]
      _ = c v * v⁻¹ := h3
  ext v
  rcases hirr Y hY with h0 | h0
  · have h1 : c v * v⁻¹ ∈ Y := hfix v
    rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at h1
    simpa using h1
  · have : v ∈ Y := by rw [h0]; trivial
    simpa using (show c v = v from this)

theorem d391nf_pow_cent (hexp : ∀ x : X, x ^ 2 = 1) {H : Subgroup (MulAut X)}
    (hirr : ∀ U : Subgroup X, (∀ h ∈ H, ∀ u ∈ U, h u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∀ (n : ℕ) (c : MulAut X), c ^ (2 ^ n) = 1 → (∀ h ∈ H, c * h = h * c) → c = 1 := by
  intro n
  induction n with
  | zero =>
    intro c hc _
    simpa using hc
  | succ n ih =>
    intro c hc hcomm
    have hc2 : c ^ 2 = 1 := by
      refine ih (c ^ 2) ?_ fun h hh => (Commute.pow_left (show Commute c h from hcomm h hh) 2).eq
      rw [← pow_mul, ← pow_succ']
      exact hc
    exact d391nf_cent hexp hirr hc2 hcomm

theorem d391nf_pGroup_eq_bot (hexp : ∀ x : X, x ^ 2 = 1) {H N : Subgroup (MulAut X)}
    (hirr : ∀ U : Subgroup X, (∀ h ∈ H, ∀ u ∈ U, h u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hN : IsPGroup 2 ↥N) (hcomm : ∀ h ∈ H, ∀ n ∈ N, n * h = h * n) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨k, hk⟩ := hN ⟨n, hn⟩
  have hk' : n ^ (2 ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  rw [Subgroup.mem_bot]
  exact d391nf_pow_cent hexp hirr k n hk' fun h hh => hcomm h hh n hn

end Abstract

section General

variable {G : Type*} [Group G]

theorem d391nf_mem_normalizer {H N : Subgroup G} (hN : ∀ m ∈ H, ∀ k ∈ N, m * k * m⁻¹ ∈ N)
    {m : G} (hm : m ∈ H) : m ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨hN m hm k, fun hk => ?_⟩
  have h1 := hN m⁻¹ (H.inv_mem hm) _ hk
  have e : m⁻¹ * (m * k * m⁻¹) * m⁻¹⁻¹ = k := by group
  rwa [e] at h1

theorem d391nf_comm_sup {K₁ K₂ : Subgroup G} {q : G} (h₁ : ∀ k ∈ K₁, k * q = q * k)
    (h₂ : ∀ k ∈ K₂, k * q = q * k) : ∀ m ∈ K₁ ⊔ K₂, m * q = q * m := by
  have : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({q} : Set G) := by
    refine sup_le (fun k hk => ?_) (fun k hk => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h₁ k hk)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h₂ k hk)
  intro m hm
  exact Subgroup.mem_centralizer_singleton_iff.1 (this hm)

end General

section Main

variable {X : Type} [CommGroup X] [Finite X]

theorem d391nf_false (hB56 : AsB56) (hexp : ∀ x : X, x ^ 2 = 1) {G K₁ K₂ : Subgroup (MulAut X)}
    (hq₁ : CFSG.IsQuasisimple ↥K₁) (hq₂ : CFSG.IsQuasisimple ↥K₂)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (h₁G : K₁ ≤ G) (h₂G : K₂ ≤ G)
    (hGn : ∀ g ∈ G, ∀ m ∈ K₁ ⊔ K₂, g * m * g⁻¹ ∈ K₁ ⊔ K₂) {s : MulAut X} (hsG : s ∈ G)
    (hs₁ : ∀ k ∈ K₁, s * k * s⁻¹ ∈ K₂) (hs₂ : ∀ k ∈ K₂, s⁻¹ * k * s ∈ K₁)
    (hirr : ∀ U : Subgroup X, (∀ h ∈ K₁ ⊔ K₂, ∀ u ∈ U, h u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hsq : IsQuotientOfSQTKTC ↥G) (hFF : IsFFModule G) : False := by
  set H : Subgroup (MulAut X) := K₁ ⊔ K₂ with hH
  have hK₁H : K₁ ≤ H := le_sup_left
  have hK₂H : K₂ ≤ H := le_sup_right
  have hHG : H ≤ G := sup_le h₁G h₂G
  have hnorm₁ : H ≤ Subgroup.normalizer (K₁ : Set (MulAut X)) := by
    refine sup_le Subgroup.le_normalizer fun y hy => Subgroup.centralizer_le_normalizer _ ?_
    exact Subgroup.mem_centralizer_iff.2 fun x hx => hcomm x hx y hy
  have hnorm₂ : H ≤ Subgroup.normalizer (K₂ : Set (MulAut X)) := by
    refine sup_le (fun x hx => Subgroup.centralizer_le_normalizer _ ?_) Subgroup.le_normalizer
    exact Subgroup.mem_centralizer_iff.2 fun y hy => (hcomm x hx y hy).symm
  have hKn₁ : ∀ m ∈ H, ∀ k ∈ K₁, m * k * m⁻¹ ∈ K₁ := fun m hm k hk =>
    (Subgroup.mem_normalizer_iff.1 (hnorm₁ hm) k).1 hk
  have hKn₂ : ∀ m ∈ H, ∀ k ∈ K₂, m * k * m⁻¹ ∈ K₂ := fun m hm k hk =>
    (Subgroup.mem_normalizer_iff.1 (hnorm₂ hm) k).1 hk
  have hcommV : ∀ {K : Subgroup (MulAut X)}, CFSG.IsQuasisimple ↥K →
      (∀ m ∈ H, ∀ k ∈ K, m * k * m⁻¹ ∈ K) → commV K = ⊤ := by
    intro K hK hKn
    have hinv : ∀ m ∈ H, ∀ u ∈ commV K, m u ∈ commV K := by
      intro m hm u hu
      rw [commV_eq_commSub] at hu ⊢
      exact n6_commSub_inv (Y := ⊤) (fun y _ => trivial) (d391nf_mem_normalizer hKn hm) hu
    rcases hirr (commV K) hinv with h0 | h0
    · exfalso
      have hK0 : K = ⊥ := by
        rw [eq_bot_iff]
        intro k hk
        rw [Subgroup.mem_bot]
        ext v
        have : k v * v⁻¹ ∈ commV K := Subgroup.subset_closure ⟨k, hk, v, rfl⟩
        rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at this
        simpa using this
      have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK
      exact (Subgroup.nontrivial_iff_ne_bot K).1 this hK0
    · exact h0
  obtain ⟨A, hAG, hAne, hAe, hAcard⟩ := hFF
  have hA2 : IsA2 G A := ⟨hAG, hAne, hAe⟩
  obtain ⟨B, hBA, hB, -⟩ := B1.exists_offender_below hA2 0 (by rw [add_zero]; exact hAcard)
  set J := ffJ G with hJdef
  have hJG : J ≤ G := B6.ffJ_le G
  have hJn : ∀ g ∈ G, ∀ j ∈ J, g * j * g⁻¹ ∈ J := fun g hg j hj =>
    (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ G hg) j).mp hj
  have hBJ : B ≤ J := B6.le_ffJ hB
  have hJne : J ≠ ⊥ := fun hJ0 => hB.2.1 (eq_bot_iff.2 (hJ0 ▸ hBJ))
  have hQ : pCoreOf 2 G = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
    have hQG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
    have hQn : ∀ g ∈ G, ∀ q ∈ pCoreOf 2 G, g * q * g⁻¹ ∈ pCoreOf 2 G :=
      fun g hg q hq => B1Red.conj_mem_pCoreOf hg hq
    have hcent : ∀ {K : Subgroup (MulAut X)}, CFSG.IsQuasisimple ↥K → K ≤ H →
        (∀ m ∈ H, ∀ k ∈ K, m * k * m⁻¹ ∈ K) → ∀ q ∈ pCoreOf 2 G, ∀ k ∈ K, k * q = q * k := by
      intro K hK hKH hKn q hq k hk
      rcases n6_le_or_commute hK hKH hHG hKn hGn hQG hQn with hle | hc
      · exfalso
        have : Group.IsPerfect ↥K := hK.1
        have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK
        exact Group.IsPerfect.not_isNilpotent _ (hQ2.to_le hle).isNilpotent
      · exact hc k hk q hq
    refine d391nf_pGroup_eq_bot hexp hirr hQ2 fun m hm q hq => ?_
    exact (d391nf_comm_sup (fun k hk => hcent hq₁ hK₁H hKn₁ q hq k hk)
      (fun k hk => hcent hq₂ hK₂H hKn₂ q hq k hk) m hm).symm
  have hKJ : K₁ ≤ J ∨ K₂ ≤ J := by
    by_cases h1 : K₁ ≤ J
    · exact Or.inl h1
    by_cases h2 : K₂ ≤ J
    · exact Or.inr h2
    exfalso
    have hc₁ := (n6_le_or_commute hq₁ hK₁H hHG hKn₁ hGn hJG hJn).resolve_left h1
    have hc₂ := (n6_le_or_commute hq₂ hK₂H hHG hKn₂ hGn hJG hJn).resolve_left h2
    refine hB.2.1 (d391nf_pGroup_eq_bot hexp hirr hB.2.2.1.isPGroup fun m hm b hb => ?_)
    exact (d391nf_comm_sup (fun k hk => hc₁ k hk b (hBJ hb)) (fun k hk => hc₂ k hk b (hBJ hb))
      m hm).symm
  have hK₂J : K₂ ≤ J := by
    rcases hKJ with h | h
    · intro x hx
      have h2 := hJn s hsG _ (h (hs₂ x hx))
      have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
      rwa [e] at h2
    · exact h
  have hK₁J : K₁ ≤ J := by
    rcases hKJ with h | h
    · exact h
    · intro x hx
      have h2 := hJn s⁻¹ (G.inv_mem hsG) _ (h (hs₁ x hx))
      have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
      rwa [e] at h2
  have hHJ : H ≤ J := sup_le hK₁J hK₂J
  have hQJ : pCoreOf 2 J = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J G hJG
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJG).2 (B6.le_normalizer_ffJ G))
    rw [hQ] at this
    exact le_bot_iff.1 this
  have hJsqtk : IsQuotientOfSQTKTC ↥J := n6_isQuotientOfSQTK_of_le hJG hsq
  have hb53 : B53Hyp J := ⟨hQJ, (InternalSec.ffJ_ffJ _).symm, n6_b53_clause hJsqtk⟩
  have hcases := hB56 X hexp J hJne hb53
  have hF₁ : quasithinGenFitting J = K₁ :=
    n6_genFitting_eq_of_b56Cases hq₁ hK₁H hHJ hKn₁ (fun j hj m hm => hGn j (hJG hj) m hm)
      (hcommV hq₁ hKn₁) hcases
  have hF₂ : quasithinGenFitting J = K₂ :=
    n6_genFitting_eq_of_b56Cases hq₂ hK₂H hHJ hKn₂ (fun j hj m hm => hGn j (hJG hj) m hm)
      (hcommV hq₂ hKn₂) hcases
  have h12 : K₁ = K₂ := hF₁.symm.trans hF₂
  exact InternalSec.not_commute_of_isQuasisimple hq₁ fun a ha b hb => hcomm a ha b (h12 ▸ hb)

end Main

section Sec

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem d391nf_conj_mem_centSec {V Z : Subgroup W} {g k : MulAut W} (hgV : g ∈ stabSub V)
    (hgZ : g ∈ stabSub Z) (hk : k ∈ centSec V Z) : g * k * g⁻¹ ∈ centSec V Z :=
  CFSG.Quasithin.StabLat.conj_mem_centSec hgV hgZ hk

theorem d391nf_sec (hB56 : AsB56) (hexp : ∀ w : W, w ^ 2 = 1)
    {G₀ N₁ N₂ : Subgroup (MulAut W)} {V Z : Subgroup W} (hGV : G₀ ≤ stabSub V)
    (hGZ : G₀ ≤ stabSub Z) (hZV : Z < V) (hN₁G : N₁ ≤ G₀) (hN₂G : N₂ ≤ G₀)
    (hq₁ : CFSG.IsQuasisimple ↥N₁) (hq₂ : CFSG.IsQuasisimple ↥N₂)
    (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) (hnt₁ : ¬ N₁ ≤ centSec V Z)
    (hnt₂ : ¬ N₂ ≤ centSec V Z) (hnorm : ∀ g ∈ G₀, ∀ m ∈ N₁ ⊔ N₂, g * m * g⁻¹ ∈ N₁ ⊔ N₂)
    {t : MulAut W} (htG : t ∈ G₀) (ht₁ : ∀ k ∈ N₁, t * k * t⁻¹ ∈ N₂)
    (ht₂ : ∀ k ∈ N₂, t⁻¹ * k * t ∈ N₁)
    (hirr : ∀ J : Subgroup W, (∀ x ∈ N₁ ⊔ N₂, ∀ w ∈ J, x w ∈ J) → Z ≤ J → J ≤ V →
      J = Z ∨ J = V)
    (hsq : IsQuotientOfSQTKTC ↥G₀) : ¬ IsFFModule (autSec G₀ V Z) := by
  intro hFF
  let ρ : ↥G₀ →* MulAut (Sec V Z) := B5.secHom G₀ hGV hGZ
  have hNG : N₁ ⊔ N₂ ≤ G₀ := sup_le hN₁G hN₂G
  have hne : ∀ {N : Subgroup (MulAut W)}, N ≤ G₀ → ¬ N ≤ centSec V Z →
      (N.subgroupOf G₀).map ρ ≠ ⊥ := by
    intro N hNG hNc hbot
    apply hNc
    intro n hn
    have h1 : ρ ⟨n, hNG hn⟩ ∈ (N.subgroupOf G₀).map ρ :=
      ⟨⟨n, hNG hn⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (B5.mem_ker_secHom G₀ hGV hGZ ⟨n, hNG hn⟩).1 h1
  have hq₁' : CFSG.IsQuasisimple ↥((N₁.subgroupOf G₀).map ρ) :=
    isQuasisimple_map_subgroupOf_of_ne_bot hN₁G hq₁ ρ (hne hN₁G hnt₁)
  have hq₂' : CFSG.IsQuasisimple ↥((N₂.subgroupOf G₀).map ρ) :=
    isQuasisimple_map_subgroupOf_of_ne_bot hN₂G hq₂ ρ (hne hN₂G hnt₂)
  have hcomm' : ∀ a ∈ (N₁.subgroupOf G₀).map ρ, ∀ b ∈ (N₂.subgroupOf G₀).map ρ, a * b = b * a := by
    rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.1 hα) _ (Subgroup.mem_subgroupOf.1 hβ))
  have hKK : (N₁.subgroupOf G₀).map ρ ⊔ (N₂.subgroupOf G₀).map ρ =
      ((N₁ ⊔ N₂).subgroupOf G₀).map ρ := by
    rw [← Subgroup.map_sup, Subgroup.subgroupOf_sup hN₁G hN₂G]
  have hKK' : ((N₁ ⊔ N₂).subgroupOf G₀).map ρ = autSec (N₁ ⊔ N₂) V Z :=
    B5.map_secHom_eq_autSec G₀ hGV hGZ hNG
  have hGn : ∀ g ∈ ρ.range, ∀ m ∈ (N₁.subgroupOf G₀).map ρ ⊔ (N₂.subgroupOf G₀).map ρ,
      g * m * g⁻¹ ∈ (N₁.subgroupOf G₀).map ρ ⊔ (N₂.subgroupOf G₀).map ρ := by
    rintro _ ⟨γ, rfl⟩ m hm
    rw [hKK] at hm ⊢
    obtain ⟨μ, hμ, rfl⟩ := hm
    refine ⟨γ * μ * γ⁻¹, ?_, by simp⟩
    exact Subgroup.mem_subgroupOf.2 (hnorm γ γ.2 μ (Subgroup.mem_subgroupOf.1 hμ))
  have htG' : ρ ⟨t, htG⟩ ∈ ρ.range := ⟨_, rfl⟩
  have hs₁ : ∀ k ∈ (N₁.subgroupOf G₀).map ρ,
      ρ ⟨t, htG⟩ * k * (ρ ⟨t, htG⟩)⁻¹ ∈ (N₂.subgroupOf G₀).map ρ := by
    rintro _ ⟨κ, hκ, rfl⟩
    refine ⟨⟨t, htG⟩ * κ * ⟨t, htG⟩⁻¹, ?_, by simp⟩
    exact Subgroup.mem_subgroupOf.2 (ht₁ _ (Subgroup.mem_subgroupOf.1 hκ))
  have hs₂ : ∀ k ∈ (N₂.subgroupOf G₀).map ρ,
      (ρ ⟨t, htG⟩)⁻¹ * k * ρ ⟨t, htG⟩ ∈ (N₁.subgroupOf G₀).map ρ := by
    rintro _ ⟨κ, hκ, rfl⟩
    refine ⟨⟨t, htG⟩⁻¹ * κ * ⟨t, htG⟩, ?_, by simp⟩
    exact Subgroup.mem_subgroupOf.2 (ht₂ _ (Subgroup.mem_subgroupOf.1 hκ))
  have hirrSec : XMod.IsIrrSec ↥(autSec (N₁ ⊔ N₂) V Z) (⊥ : Subgroup (Sec V Z)) ⊤ :=
    B5.isIrrSec_autSec hZV hirr (hNG.trans hGV) (hNG.trans hGZ)
  have hirr' : ∀ U : Subgroup (Sec V Z),
      (∀ h ∈ (N₁.subgroupOf G₀).map ρ ⊔ (N₂.subgroupOf G₀).map ρ, ∀ u ∈ U, h u ∈ U) →
        U = ⊥ ∨ U = ⊤ := by
    intro U hU
    rw [hKK, hKK'] at hU
    exact hirrSec.2 U ((isInv_iff _ _).2 hU) bot_le le_top
  have hsq' : IsQuotientOfSQTKTC ↥ρ.range := isQuotientOfSQTK_range_aux ρ hsq
  rw [← B5.range_secHom G₀ hGV hGZ] at hFF
  exact d391nf_false hB56 (Bridge.sec_sq_eq_one hexp V Z) hq₁' hq₂' hcomm'
    (Subgroup.map_le_range ρ _) (Subgroup.map_le_range ρ _) hGn htG' hs₁ hs₂ hirr' hsq' hFF

end Sec

section Headline

theorem d391NotFFTop_of_b56 (hL38 : D3L38) (hB56 : AsB56) :
    D391NotFFTop := by
  intro W _ _ M Mp T L V hD hVT t htT htL hMp
  obtain ⟨-, hcomm, -, -⟩ := hL38 W M Mp T L V hD t htT htL hMp
  have hexp := hD.hyp.exp
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    calc T ≤ Subgroup.normalizer (conjClosure L T : Set (MulAut W)) :=
          le_normalizer_conjClosure L T
      _ = Subgroup.normalizer (Mp : Set (MulAut W)) := by rw [← hD.hyp.Mp_eq]
  have hGN : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hTn
  have hN : ∀ g ∈ Mp ⊔ T, ∀ l ∈ Mp, g * l * g⁻¹ ∈ Mp := fun g hg l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hGN hg)) l).1 hl
  have hG := n1_sup_le_stabSub_sec hD.hyp
  rw [← hVT] at hG
  have hGV : Mp ⊔ T ≤ stabSub V := hG.trans inf_le_left
  have hGC : Mp ⊔ T ≤ stabSub (V ⊓ fixV Mp) := hG.trans inf_le_right
  obtain ⟨-, hVcomm, hVlt, hVirr⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hntV : ¬ Mp ≤ centSec V (V ⊓ fixV Mp) := by
    intro h
    have h1 : commSub V Mp ≤ V ⊓ fixV Mp := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact (h hx).2 w hw
    rw [hVcomm] at h1
    exact lt_irrefl _ (lt_of_lt_of_le hVlt h1)
  have hconj : ∀ g ∈ Mp ⊔ T, ∀ c ∈ centSec V (V ⊓ fixV Mp),
      g * c * g⁻¹ ∈ centSec V (V ⊓ fixV Mp) := fun g hg c hc =>
    d391nf_conj_mem_centSec (hGV hg) (hGC hg) hc
  have htG : t ∈ Mp ⊔ T := (le_sup_right : T ≤ Mp ⊔ T) htT
  have hLtC : L ≤ centSec V (V ⊓ fixV Mp) → conjAutSub t L ≤ centSec V (V ⊓ fixV Mp) := by
    intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hconj t htG y (h hy)
  have hLC' : conjAutSub t L ≤ centSec V (V ⊓ fixV Mp) → L ≤ centSec V (V ⊓ fixV Mp) := by
    intro h x hx
    have hx' : t * x * t⁻¹ ∈ conjAutSub t L := ⟨x, hx, rfl⟩
    have := hconj t⁻¹ ((Mp ⊔ T).inv_mem htG) _ (h hx')
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rwa [e] at this
  have hLMp : L ≤ Mp := by rw [hMp]; exact le_sup_left
  have hLtMp : conjAutSub t L ≤ Mp := by rw [hMp]; exact le_sup_right
  have hLnot : ¬ L ≤ centSec V (V ⊓ fixV Mp) := fun h =>
    hntV (hMp.le.trans (sup_le h (hLtC h)))
  have hLtnot : ¬ conjAutSub t L ≤ centSec V (V ⊓ fixV Mp) := fun h =>
    hntV (hMp.le.trans (sup_le (hLC' h) h))
  have hcomm' : ∀ x ∈ L, ∀ y ∈ conjAutSub t L, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_le.1 hcomm.le x hx y hy
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have hMpM : Mp ≤ M := by
    rw [hD.hyp.Mp_eq]
    exact conjClosure_le fun s hs z hz =>
      M.mul_mem (M.mul_mem (hD.hyp.sylow.1 hs) (le_of_mem_cComp hD.hyp.comp hz))
        (M.inv_mem (hD.hyp.sylow.1 hs))
  have hsq : IsQuotientOfSQTKTC ↥(Mp ⊔ T) :=
    isQuotientOfSQTK_of_le_aux (sup_le hMpM hD.hyp.sylow.1) hD.hyp.qsqtk
  refine d391nf_sec hB56 hexp hGV hGC hVlt (hLMp.trans le_sup_left) (hLtMp.trans le_sup_left)
    hD.hyp.quasi (hD.hyp.conj htT).quasi hcomm' hLnot hLtnot ?_ htG ?_ ?_ ?_ hsq
  · intro g hg m hm
    rw [← hMp] at hm ⊢
    exact hN g hg m hm
  · intro k hk
    refine mem_conjAutSub_iff.2 ?_
    have e : t⁻¹ * (t * k * t⁻¹) * t = k := by group
    rw [e]
    exact hk
  · intro k hk
    exact mem_conjAutSub_iff.1 hk
  · intro J hJ hZJ hJV
    exact hVirr J (fun x hx w hw => hJ x (hMp ▸ hx) w hw) hZJ hJV

end Headline

end CFSG.Quasithin
