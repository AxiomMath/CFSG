module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvPow

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

namespace TransvSetup

theorem three_elem_C (h : TransvSetup b₀ K E) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hOut : ¬ 3 ∣ Nat.card (Outer K)) {x : G}
    (hxC : x ∈ Subgroup.centralizer ({b₀} : Set G)) {k : ℕ} (hx : x ^ 3 ^ k = 1) :
    ∃ y ∈ K, ∃ i : ℤ, x = y * b₀ ^ i := by
  set C := Subgroup.centralizer ({b₀} : Set G) with hC
  set D := C ⊓ Subgroup.centralizer (K : Set G) with hD
  have hidx : ¬ 3 ∣ ((K ⊔ D).subgroupOf C).index := fs81Sp_no_three_index hKC hKn hOut
  have : ((K ⊔ D).subgroupOf C).Normal := fs81Fus_sup_normal hKC hKn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers (⟨x, hxC⟩ : C)) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (⟨x, hxC⟩ : C) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hx)
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1,
      one_zpow, Subgroup.coe_one]
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow (p := 3) (G := C) hP
  have hxKD : x ∈ K ⊔ D := fs81Sp_sylow_le_normal hidx P (hPle (Subgroup.mem_zpowers _))
  obtain ⟨a, ha, d, hd, hxad⟩ := fs81Sp_mem_sup_of_commute fs81Sp_comm hxKD
  have hcomm : Commute a d := fs81Sp_comm a ha d hd
  have hd3 : d ^ 3 ^ k = 1 := by
    have h1 : a ^ 3 ^ k * d ^ 3 ^ k = 1 := by rw [← hcomm.mul_pow, ← hxad, hx]
    have h2 : d ^ 3 ^ k ∈ K ⊓ D := by
      refine ⟨?_, D.pow_mem hd _⟩
      rw [eq_inv_of_mul_eq_one_right h1]
      exact K.inv_mem (K.pow_mem ha _)
    rw [fs81Sp_inf_eq_bot hKC hKz] at h2
    exact h2
  have hdE : d ∈ Subgroup.centralizer (E : Set G) :=
    h.mem_centralizer_of (Subgroup.mem_centralizer_iff.mp hd.1 b₀ (Set.mem_singleton b₀)).symm
      fun a' ha' => (Subgroup.mem_centralizer_iff.mp hd.2 a' ha'.2).symm
  have hdE' : d ∈ E := h.syl d hdE k hd3
  rw [← h.sup] at hdE'
  obtain ⟨u, hu, a', ha', hdu⟩ := fs81Sp_mem_sup_of_commute (A := Subgroup.zpowers b₀)
    (B := E ⊓ K) (fun u hu v hv => h.comm (Subgroup.zpowers_le.mpr h.b0_mem hu) hv.1) hdE'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  refine ⟨a * a', K.mul_mem ha ha'.2, i, ?_⟩
  rw [hxad, hdu, h.comm (E.zpow_mem h.b0_mem i) ha'.1, mul_assoc]

theorem exists_psi (h : TransvSetup b₀ K E) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hOut : ¬ 3 ∣ Nat.card (Outer K)) :
    ∃ ψ : ↥(Subgroup.centralizer ({b₀} : Set G)) →* Multiplicative (ZMod 3),
      (∀ x : ↥(Subgroup.centralizer ({b₀} : Set G)), (x : G) ∈ K → ψ x = 1) ∧
      ∀ x : ↥(Subgroup.centralizer ({b₀} : Set G)), (x : G) = b₀ → ψ x ≠ 1 := by
  set C := Subgroup.centralizer ({b₀} : Set G) with hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb₀C : b₀ ∈ C := Subgroup.mem_centralizer_iff.mpr fun g hg => by
    rw [Set.mem_singleton_iff.mp hg]
  set b : C := ⟨b₀, hb₀C⟩ with hb
  set π := QuotientGroup.mk' (K.subgroupOf C) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπK : ∀ x : C, (x : G) ∈ K → π x = 1 := fun x hx =>
    MonoidHom.mem_ker.mp (by rw [QuotientGroup.ker_mk']; exact Subgroup.mem_subgroupOf.mpr hx)
  have hbo : orderOf b = 3 := by rw [← Subgroup.orderOf_coe]; exact h.ord
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  have hbP : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  obtain ⟨P₀, hP₀⟩ := IsPGroup.exists_le_sylow hbP
  set S := Sylow.mapSurjective hπs P₀ with hS
  set z := π b with hz
  have hzS : z ∈ (S : Subgroup (C ⧸ K.subgroupOf C)) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem _ (hP₀ (Subgroup.mem_zpowers b))
  have hSz : (S : Subgroup (C ⧸ K.subgroupOf C)) ≤ Subgroup.zpowers z := by
    intro w hw
    rw [Sylow.coe_mapSurjective] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨k, hk⟩ := P₀.isPGroup' ⟨x, hx⟩
    have hx3 : (x : G) ^ 3 ^ k = 1 := by
      have := congrArg (fun y : ↥(P₀ : Subgroup C) => ((y : C) : G)) hk
      simpa using this
    obtain ⟨y, hy, i, hxy⟩ := h.three_elem_C hKC hKn hKz hOut x.2 hx3
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    have hx' : x = ⟨y, hKC hy⟩ * b ^ i := Subtype.ext (by simp [b, hxy])
    rw [hx', map_mul, map_zpow, hπK _ hy, one_mul]
  have hcent : ∀ w, w * z = z * w := by
    intro w
    obtain ⟨x, rfl⟩ := hπs w
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2 b₀ (Set.mem_singleton b₀)).symm
  have hPc : Subgroup.normalizer ((S : Subgroup (C ⧸ K.subgroupOf C)) : Set (C ⧸ K.subgroupOf C)) ≤
      Subgroup.centralizer ((S : Subgroup (C ⧸ K.subgroupOf C)) : Set (C ⧸ K.subgroupOf C)) := by
    intro w _
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hSz hv)
    exact (Commute.zpow_left (hcent w).symm j).eq
  set T := MonoidHom.transferSylow S hPc with hT
  have hz1 : z ≠ 1 := by
    intro hz1
    have hbK : b ∈ π.ker := MonoidHom.mem_ker.mpr hz1
    rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hbK
    have h1 := Subgroup.disjoint_def.mp h.disj (Subgroup.mem_zpowers b₀) ⟨h.b0_mem, hbK⟩
    have h2 := h.ord
    rw [h1, orderOf_one] at h2
    omega
  have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, hb3, map_one]
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hTz : ((T z : ↥(S : Subgroup (C ⧸ K.subgroupOf C))) : C ⧸ K.subgroupOf C) =
      z ^ (S : Subgroup (C ⧸ K.subgroupOf C)).index := by
    rw [hT, MonoidHom.transferSylow_eq_pow S hPc z hzS]
  have hTz1 : T z ≠ 1 := by
    intro h1
    have h2 : z ^ (S : Subgroup (C ⧸ K.subgroupOf C)).index = 1 := by rw [← hTz, h1]; rfl
    have h4 := orderOf_dvd_of_pow_eq_one h2
    rw [hzo] at h4
    exact S.not_dvd_index h4
  have hScard : Nat.card ↥(S : Subgroup (C ⧸ K.subgroupOf C)) = 3 := by
    rw [le_antisymm hSz (Subgroup.zpowers_le.mpr hzS), Nat.card_zpowers, hzo]
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  set e := mulEquivOfPrimeCardEq hScard h3 with he
  refine ⟨e.toMonoidHom.comp (T.comp π), fun x hx => ?_, fun x hx => ?_⟩
  · simp [hπK x hx]
  · have hxb : x = b := Subtype.ext hx
    rw [hxb]
    intro h1
    apply hTz1
    apply e.injective
    rw [map_one]
    exact h1

end TransvSetup

namespace TransvP1

theorem conj_b0_mem (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁)
    (hfix : ∀ m ∈ Subgroup.normalizer (P₁ : Set G), ∀ a ∈ E ⊓ K, m * b₀ * m⁻¹ ≠ b₀⁻¹ * a) :
    ∀ g ∈ Subgroup.normalizer (E : Set G), b₀⁻¹ * (g * b₀ * g⁻¹) ∈ E ⊓ K := by
  set NE := Subgroup.normalizer (E : Set G) with hNE
  have hcommE : ∀ u ∈ Subgroup.zpowers b₀, ∀ v ∈ E ⊓ K, u * v = v * u :=
    fun u hu v hv => h.comm (Subgroup.zpowers_le.mpr h.b0_mem hu) hv.1
  intro g hg
  obtain ⟨c, hc, hcg⟩ :=
    h.exists_centralizer_mul_mem_normalizer hP.le hP.pgroup hP.card hP.surj' hg
  have hgb : g * b₀ * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hg b₀).mp h.b0_mem
  have hcgb : c * g * b₀ * (c * g)⁻¹ = g * b₀ * g⁻¹ := by
    rw [show c * g * b₀ * (c * g)⁻¹ = c * (g * b₀ * g⁻¹) * c⁻¹ by group,
      ← Subgroup.mem_centralizer_iff.mp hc _ hgb, mul_inv_cancel_right]
  have hcgN : c * g ∈ NE := NE.mul_mem (Subgroup.centralizer_le_normalizer _ hc) hg
  rw [← hcgb]
  set m := c * g with hm
  have hmb : m * b₀ * m⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hcgN b₀).mp h.b0_mem
  rw [← h.sup] at hmb
  obtain ⟨u, hu, a, ha, hua⟩ := fs81Sp_mem_sup_of_commute hcommE hmb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hb3 : b₀ ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one b₀
  have hi : b₀ ^ i = b₀ ^ (i % 3) := by
    have := zpow_mod_orderOf b₀ i
    rw [h.ord] at this
    exact_mod_cast this.symm
  have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · exfalso
    rw [hi, hr, zpow_zero, one_mul] at hua
    have hbA : b₀ ∈ E ⊓ K := by
      have := h.inv m⁻¹ (NE.inv_mem hcgN) a ha
      rwa [← hua, inv_inv, show m⁻¹ * (m * b₀ * m⁻¹) * m = b₀ by group] at this
    have h1 := Subgroup.disjoint_def.mp h.disj (Subgroup.mem_zpowers b₀) hbA
    have h2 := h.ord
    rw [h1, orderOf_one] at h2
    omega
  · rw [hi, hr, zpow_one] at hua
    rw [hua, inv_mul_cancel_left]
    exact ha
  · exfalso
    rw [hi, hr] at hua
    have h2 : b₀ ^ (2 : ℤ) = b₀⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num,
        zpow_natCast, hb3]
    exact hfix m hcg a ha (by rw [hua, h2])

theorem not_mem_commutator_of_psi (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁)
    {B₂ : Subgroup G} (hB₂P : B₂ ≤ P₁) (hB₂E : ∀ x ∈ B₂, x ∈ E → x ∈ E ⊓ K)
    (hcos : ∀ x ∈ P₁, ∃ j : ℤ, x * b₀ ^ j ∈ B₂) (hab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    (hnorm : ∀ m ∈ Subgroup.normalizer (P₁ : Set G), ∀ x ∈ B₂, m * x * m⁻¹ ∈ B₂)
    (hfix : ∀ m ∈ Subgroup.normalizer (P₁ : Set G), ∀ a ∈ E ⊓ K, m * b₀ * m⁻¹ ≠ b₀⁻¹ * a)
    {H : Type} [CommGroup H] (hH : ∀ x : H, x ^ 3 = 1)
    (ψ : ↥(Subgroup.centralizer ({b₀} : Set G)) →* H)
    (hψA : ∀ x : ↥(Subgroup.centralizer ({b₀} : Set G)), (x : G) ∈ E ⊓ K → ψ x = 1)
    (hψb : ∀ x : ↥(Subgroup.centralizer ({b₀} : Set G)), (x : G) = b₀ → ψ x ≠ 1) :
    (⟨b₀, Subgroup.le_normalizer h.b0_mem⟩ : ↥(Subgroup.normalizer (E : Set G))) ∉
      commutator ↥(Subgroup.normalizer (E : Set G)) := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({b₀} : Set G)
  set NE := Subgroup.normalizer (E : Set G) with hNE
  set NP := Subgroup.normalizer (P₁ : Set G) with hNP
  set CE := Subgroup.centralizer (E : Set G) with hCE
  have hb₀C : b₀ ∈ C := Subgroup.mem_centralizer_iff.mpr fun g hg => by
    rw [Set.mem_singleton_iff.mp hg]
  have hEC : ∀ {e}, e ∈ E → e ∈ C := fun he => Subgroup.mem_centralizer_iff.mpr fun g hg => by
    rw [Set.mem_singleton_iff.mp hg]
    exact h.comm h.b0_mem he
  have hCEC : ∀ {c}, c ∈ CE → c ∈ C :=
    fun hc => Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.b0_mem) hc
  have hmemC : ∀ {g}, g * b₀ * g⁻¹ = b₀ → g ∈ C := fun {g} hg =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  have hcommE : ∀ u ∈ Subgroup.zpowers b₀, ∀ v ∈ E ⊓ K, u * v = v * u :=
    fun u hu v hv => h.comm (Subgroup.zpowers_le.mpr h.b0_mem hu) hv.1
  set ψG : G → H := fun g => if hg : g ∈ C then ψ ⟨g, hg⟩ else 1 with hψGdef
  have hψG : ∀ {g} (hg : g ∈ C), ψG g = ψ ⟨g, hg⟩ := fun hg => dif_pos hg
  have hψmul : ∀ {x y}, x ∈ C → y ∈ C → ψG (x * y) = ψG x * ψG y := fun hx hy => by
    rw [hψG hx, hψG hy, hψG (C.mul_mem hx hy), ← map_mul]
    rfl
  have hψ1 : ψG 1 = 1 := by rw [hψG C.one_mem]; exact map_one ψ
  have hψinv : ∀ {x}, x ∈ C → ψG x⁻¹ = (ψG x)⁻¹ := fun hx => by
    rw [hψG hx, hψG (C.inv_mem hx), ← map_inv]
    rfl
  have hψzpow : ∀ {x}, x ∈ C → ∀ i : ℤ, ψG (x ^ i) = ψG x ^ i := fun hx i => by
    rw [hψG hx, hψG (C.zpow_mem hx i), ← map_zpow]
    rfl
  have hψpow : ∀ {x}, x ∈ C → ∀ i : ℕ, ψG (x ^ i) = ψG x ^ i := fun hx i => by
    rw [hψG hx, hψG (C.pow_mem hx i), ← map_pow]
    rfl
  have hψA' : ∀ {a}, a ∈ E ⊓ K → ψG a = 1 := fun ha => by
    rw [hψG (hEC ha.1)]
    exact hψA ⟨_, hEC ha.1⟩ ha
  have hψb' : ψG b₀ ≠ 1 := by
    rw [hψG hb₀C]
    exact hψb ⟨b₀, hb₀C⟩ rfl
  have hconjC : ∀ {g c}, g ∈ NE → c ∈ CE → g * c * g⁻¹ ∈ CE := by
    intro g c hg hc
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have he' : g⁻¹ * e * g ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (NE.inv_mem hg) e).mp he
      rwa [inv_inv] at this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ he'
    calc e * (g * c * g⁻¹) = g * (g⁻¹ * e * g * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * e := by group
  have hCEN : ∀ {c}, c ∈ CE → c ∈ NE := fun hc => Subgroup.centralizer_le_normalizer _ hc
  have hT2 := hP.conj_b0_mem h hfix
  have hT3E : ∀ g ∈ NE, ∀ e ∈ E, ψG (g * e * g⁻¹) = ψG e := by
    intro g hg e he
    have he' := he
    rw [← h.sup] at he'
    obtain ⟨u, hu, a, ha, rfl⟩ := fs81Sp_mem_sup_of_commute hcommE he'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hga : g * a * g⁻¹ ∈ E ⊓ K := h.inv g hg a ha
    have hgb := hT2 g hg
    have hgb' : g * b₀ * g⁻¹ = b₀ * (b₀⁻¹ * (g * b₀ * g⁻¹)) := by rw [mul_inv_cancel_left]
    have hbaC : b₀ * (b₀⁻¹ * (g * b₀ * g⁻¹)) ∈ C := C.mul_mem hb₀C (hEC hgb.1)
    have h1 : g * (b₀ ^ i * a) * g⁻¹ =
        (b₀ * (b₀⁻¹ * (g * b₀ * g⁻¹))) ^ i * (g * a * g⁻¹) := by
      rw [← hgb', conj_zpow]
      group
    rw [h1, hψmul (C.zpow_mem hbaC i) (hEC hga.1), hψzpow hbaC, hψmul hb₀C (hEC hgb.1), hψA' hgb,
      hψA' hga, hψmul (C.zpow_mem hb₀C i) (hEC ha.1), hψzpow hb₀C, hψA' ha, mul_one, mul_one,
      mul_one]
  have hT3 : ∀ g ∈ NE, ∀ c ∈ CE, ψG (g * c * g⁻¹) = ψG c := by
    intro g hg c hc
    obtain ⟨e, m, hm, hcm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 3 (by norm_num)
    have hcm3 : (c ^ m) ^ 3 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hcm, pow_orderOf_eq_one]
    have hcmE : c ^ m ∈ E := h.syl _ (CE.pow_mem hc m) e hcm3
    have h1 : ψG (g * c * g⁻¹) ^ m = ψG c ^ m := by
      rw [← hψpow (hCEC (hconjC hg hc)), ← hψpow (hCEC hc), conj_pow, hT3E g hg _ hcmE]
    set q := ψG (g * c * g⁻¹) * (ψG c)⁻¹ with hq
    have hq1 : q ^ m = 1 := by rw [hq, mul_pow, inv_pow, h1, mul_inv_cancel]
    have hgcd : Nat.gcd m 3 = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)
    have hq' : q = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hq1, hH q⟩
      rwa [hgcd, pow_one] at this
    exact mul_inv_eq_one.mp hq'
  have hexy : ∀ m ∈ NE, ∃ y ∈ B₂, y⁻¹ * m ∈ C := by
    intro m hm
    obtain ⟨x, hx, hxa⟩ := hP.surj _ (hT2 m hm)
    obtain ⟨j, hj⟩ := hcos x hx
    refine ⟨x * b₀ ^ j, hj, hmemC ?_⟩
    have htb : tb b₀ (x * b₀ ^ j) = b₀⁻¹ * (m * b₀ * m⁻¹) := by
      rw [tb_mul (hP.le hx) (hP.le (hP.E_le (E.zpow_mem h.b0_mem j))),
        tb_eq_one_of_mem_E h (E.zpow_mem h.b0_mem j), mul_one, hxa]
    have hyb : x * b₀ ^ j * b₀ * (x * b₀ ^ j)⁻¹ = m * b₀ * m⁻¹ := by
      rw [conj_b0_eq_tb b₀ (x * b₀ ^ j), htb, mul_inv_cancel_left]
    rw [show (x * b₀ ^ j)⁻¹ * m * b₀ * ((x * b₀ ^ j)⁻¹ * m)⁻¹ =
      (x * b₀ ^ j)⁻¹ * (m * b₀ * m⁻¹) * (x * b₀ ^ j) by group, ← hyb]
    group
  have hwd : ∀ {m y y' : G}, y ∈ B₂ → y' ∈ B₂ → y⁻¹ * m ∈ C → y'⁻¹ * m ∈ C →
      ψG (y⁻¹ * m) = ψG (y'⁻¹ * m) := by
    intro m y y' hy hy' hym hy'm
    have hz : y'⁻¹ * y ∈ C := by
      have := C.mul_mem hy'm (C.inv_mem hym)
      rwa [show y'⁻¹ * m * (y⁻¹ * m)⁻¹ = y'⁻¹ * y by group] at this
    have hzB : y'⁻¹ * y ∈ B₂ := B₂.mul_mem (B₂.inv_mem hy') hy
    have hzA : y'⁻¹ * y ∈ E ⊓ K := by
      refine hB₂E _ hzB (hP.mem_E h (hB₂P hzB) ?_)
      have hc : b₀ * (y'⁻¹ * y) = y'⁻¹ * y * b₀ :=
        Subgroup.mem_centralizer_iff.mp hz b₀ (Set.mem_singleton b₀)
      rw [tb, ← hc, mul_inv_cancel_right, inv_mul_cancel]
    rw [show y'⁻¹ * m = (y'⁻¹ * y) * (y⁻¹ * m) by group, hψmul hz hym, hψA' hzA, one_mul]
  set yOf : G → G := fun m => if hm : ∃ y ∈ B₂, y⁻¹ * m ∈ C then hm.choose else 1 with hyOfdef
  have hyOf : ∀ {m}, (∃ y ∈ B₂, y⁻¹ * m ∈ C) → yOf m ∈ B₂ ∧ (yOf m)⁻¹ * m ∈ C := fun hm => by
    rw [hyOfdef]
    simp only [dif_pos hm]
    exact hm.choose_spec
  set thM : G → H := fun m => ψG ((yOf m)⁻¹ * m) with hthMdef
  have hthM : ∀ {m y}, y ∈ B₂ → y⁻¹ * m ∈ C → thM m = ψG (y⁻¹ * m) := fun hy hym =>
    hwd (hyOf ⟨_, hy, hym⟩).1 hy (hyOf ⟨_, hy, hym⟩).2 hym
  have hthM_C : ∀ {z}, z ∈ C → thM z = ψG z := fun hz => by
    rw [hthM B₂.one_mem (by rwa [inv_one, one_mul]), inv_one, one_mul]
  have hthM_mul : ∀ {m m'}, m ∈ NE → m ∈ NP → m' ∈ NE → thM (m * m') = thM m * thM m' := by
    intro m m' hm hmP hm'
    obtain ⟨y, hy, hym⟩ := hexy m hm
    obtain ⟨y', hy', hy'm⟩ := hexy m' hm'
    have hu : m * y' * m⁻¹ ∈ B₂ := hnorm m hmP y' hy'
    have hkey : (y * (m * y' * m⁻¹))⁻¹ * (m * m') = (y⁻¹ * m) * (y'⁻¹ * m') := by
      have hc : (m * y' * m⁻¹)⁻¹ * y⁻¹ = y⁻¹ * (m * y' * m⁻¹)⁻¹ :=
        hab _ (B₂.inv_mem hu) _ (B₂.inv_mem hy)
      calc (y * (m * y' * m⁻¹))⁻¹ * (m * m') = ((m * y' * m⁻¹)⁻¹ * y⁻¹) * (m * m') := by group
        _ = (y⁻¹ * (m * y' * m⁻¹)⁻¹) * (m * m') := by rw [hc]
        _ = (y⁻¹ * m) * (y'⁻¹ * m') := by group
    have hC'' : (y * (m * y' * m⁻¹))⁻¹ * (m * m') ∈ C := hkey ▸ C.mul_mem hym hy'm
    rw [hthM (B₂.mul_mem hy hu) hC'', hkey, hψmul hym hy'm, hthM hy hym, hthM hy' hy'm]
  set cOf : G → G := fun g => if hg : ∃ c ∈ CE, c * g ∈ NP then hg.choose else 1 with hcOfdef
  have hcOf : ∀ {g}, (∃ c ∈ CE, c * g ∈ NP) → cOf g ∈ CE ∧ cOf g * g ∈ NP := fun hg => by
    rw [hcOfdef]
    simp only [dif_pos hg]
    exact hg.choose_spec
  set θ : G → H := fun g => thM (cOf g * g) * (ψG (cOf g))⁻¹ with hθdef
  have hθ : ∀ {g c}, g ∈ NE → c ∈ CE → c * g ∈ NP → θ g = thM (c * g) * (ψG c)⁻¹ := by
    intro g c hg hc hcg
    obtain ⟨hc', hc'g⟩ := hcOf ⟨c, hc, hcg⟩
    have hcc : cOf g * c⁻¹ ∈ CE := CE.mul_mem hc' (CE.inv_mem hc)
    have hccP : cOf g * c⁻¹ ∈ NP := by
      have := NP.mul_mem hc'g (NP.inv_mem hcg)
      rwa [show cOf g * g * (c * g)⁻¹ = cOf g * c⁻¹ by group] at this
    have hcgN : c * g ∈ NE := NE.mul_mem (hCEN hc) hg
    have h1 : thM (cOf g * g) = ψG (cOf g) * (ψG c)⁻¹ * thM (c * g) := by
      rw [show cOf g * g = (cOf g * c⁻¹) * (c * g) by group, hthM_mul (hCEN hcc) hccP hcgN,
        hthM_C (hCEC hcc), hψmul (hCEC hc') (C.inv_mem (hCEC hc)), hψinv (hCEC hc)]
    show thM (cOf g * g) * (ψG (cOf g))⁻¹ = thM (c * g) * (ψG c)⁻¹
    rw [h1, mul_inv_eq_iff_eq_mul]
    ac_rfl
  have hθmul : ∀ {g g'}, g ∈ NE → g' ∈ NE → θ (g * g') = θ g * θ g' := by
    intro g g' hg hg'
    obtain ⟨c, hc, hcg⟩ :=
      h.exists_centralizer_mul_mem_normalizer hP.le hP.pgroup hP.card hP.surj' hg
    obtain ⟨c', hc', hc'g⟩ :=
      h.exists_centralizer_mul_mem_normalizer hP.le hP.pgroup hP.card hP.surj' hg'
    have hgc : g * c' * g⁻¹ ∈ CE := hconjC hg hc'
    have hc'' : c * (g * c' * g⁻¹) ∈ CE := CE.mul_mem hc hgc
    have hcgg : c * (g * c' * g⁻¹) * (g * g') = (c * g) * (c' * g') := by group
    have hcggP : c * (g * c' * g⁻¹) * (g * g') ∈ NP := hcgg ▸ NP.mul_mem hcg hc'g
    rw [hθ (NE.mul_mem hg hg') hc'' hcggP, hθ hg hc hcg, hθ hg' hc' hc'g, hcgg,
      hthM_mul (NE.mul_mem (hCEN hc) hg) hcg (NE.mul_mem (hCEN hc') hg'),
      hψmul (hCEC hc) (hCEC hgc), hT3 g hg c' hc', mul_inv]
    ac_rfl
  have hb0P : b₀ ∈ NP := Subgroup.le_normalizer (hP.E_le h.b0_mem)
  have hθb : θ b₀ = ψG b₀ := by
    rw [hθ (Subgroup.le_normalizer h.b0_mem) CE.one_mem (by rwa [one_mul]), one_mul,
      hthM_C hb₀C, hψ1, inv_one, mul_one]
  let θN : ↥NE →* H :=
    { toFun := fun g => θ g
      map_one' := by
        show θ 1 = 1
        rw [hθ NE.one_mem CE.one_mem (by rw [mul_one]; exact NP.one_mem), mul_one,
          hthM_C C.one_mem, hψ1, inv_one, mul_one]
      map_mul' := fun g g' => hθmul g.2 g'.2 }
  intro hmem
  have hker := Abelianization.commutator_subset_ker θN hmem
  rw [MonoidHom.mem_ker] at hker
  exact hψb' (hθb ▸ hker)

theorem not_mem_commutator (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E)
    (hKl : KleinSigns B E) (hd3 : DiagSigns3 B E) {μ : ℕ}
    (hμ : ∀ y ∈ P₁, y ^ 3 = tb b₀ y ^ μ) (hne : ¬ ∀ x ∈ P₁, x ^ 3 = 1)
    (hA9 : 9 ≤ Nat.card ↥(E ⊓ K)) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hOut : ¬ 3 ∣ Nat.card (Outer K)) :
    (⟨b₀, Subgroup.le_normalizer h.b0_mem⟩ : ↥(Subgroup.normalizer (E : Set G))) ∉
      commutator ↥(Subgroup.normalizer (E : Set G)) := by
  obtain ⟨B₂, hB₂P, hAB₂, hB₂E, hcos, -, hinv⟩ := hP.exists_B2 h B hB hsc hKl
  have hab := hP.B2_comm h B hB hsc hd3 hB₂P hB₂E hcos hinv
  have hcomm : ∀ x ∈ P₁, ∀ y ∈ P₁, x * y * x⁻¹ * y⁻¹ ∈ E ⊓ K :=
    fun x hx y hy => hP.comm_mem_A h B hB hsc hx hy
  have hA1 : ∃ a ∈ E ⊓ K, a ≠ 1 := by
    rcases (E ⊓ K).bot_or_exists_ne_one with hbot | hex
    · rw [hbot, Subgroup.card_bot] at hA9
      omega
    · exact hex
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  obtain ⟨ψ, hψK, hψb⟩ := h.exists_psi hKC hKn hKz hOut
  exact hP.not_mem_commutator_of_psi h hB₂P hB₂E hcos hab
    (fun m hm => hP.B2_normalizer h hcomm hB₂P hAB₂ hB₂E hcos hab hA9 hm)
    (fun m hm a ha => hP.not_conj_b0_inv h hμ hne hA1 hm ha)
    (fun x => by have := pow_card_eq_one' (x := x); rwa [h3] at this) ψ
    (fun x hx => hψK x hx.2) hψb

end TransvP1

end CFSG.StandardType.FrameRoute.FS81

end
