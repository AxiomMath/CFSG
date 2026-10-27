module

public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424SL2
public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Model

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K] {π : Bool} {n : ℕ} {T : Type} [Group T]

theorem conj_pow_scalar {G : Type*} [Group G] {g a u : G} (hu : ∀ x : G, x * u = u * x)
    (h : g * a * g⁻¹ = u * a) (k : ℕ) : g ^ k * a * (g ^ k)⁻¹ = u ^ k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : g * u ^ k = u ^ k * g := (Commute.pow_right (show Commute g u from hu g) k).eq
    calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by
          rw [pow_succ']
          group
      _ = g * (u ^ k * a) * g⁻¹ := by rw [ih]
      _ = (g * u ^ k * g⁻¹) * (g * a * g⁻¹) := by group
      _ = u ^ k * (u * a) := by rw [hc, mul_inv_cancel_right, h]
      _ = u ^ (k + 1) * a := by rw [pow_succ, mul_assoc]

theorem commute_of_order_prime_three {G : Type*} [Group G] {g a u : G} (hu : ∀ x : G, x * u = u * x)
    (hu3 : u ^ 3 = 1) (h : g * a * g⁻¹ = u * a) {m : ℕ} (hm : Nat.Coprime 3 m)
    (hgm : ∀ x : G, g ^ m * x = x * g ^ m) : g * a = a * g := by
  have h1 := conj_pow_scalar hu h m
  have h2 : g ^ m * a * (g ^ m)⁻¹ = a := by
    rw [hgm a]
    group
  rw [h2] at h1
  have h3 : u ^ m = 1 := by
    have : u ^ m * a = 1 * a := by rw [← h1, one_mul]
    exact mul_right_cancel this
  have h4 : u = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hu3, h3⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at this
  rw [h4, one_mul] at h
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [h]

theorem mem_cent_of_commute {L : Subgroup (GL (Fin 3) K)} {a c z : GL (Fin 3) K}
    (hz : z ∈ StatedScalars (Fin 3) K) (hcL : c ∈ L) (h : c * a = a * c) :
    c ∈ L ⊓ Subgroup.centralizer ({a * z} : Set (GL (Fin 3) K)) := by
  have hzc : ∀ x : GL (Fin 3) K, x * z = z * x := commute_of_mem_statedScalars hz
  refine Subgroup.mem_inf.mpr ⟨hcL, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc c * (a * z) = (c * a) * z := by rw [mul_assoc]
    _ = (a * c) * z := by rw [h]
    _ = a * (c * z) := by rw [mul_assoc]
    _ = a * (z * c) := by rw [hzc c]
    _ = (a * z) * c := by rw [mul_assoc]

theorem commute_of_mem_cent {a c z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (h : c * (a * z) = (a * z) * c) : c * a = a * c := by
  have hzc : ∀ x : GL (Fin 3) K, x * z = z * x := commute_of_mem_statedScalars hz
  have h2 : (c * a) * z = (a * c) * z := by
    calc (c * a) * z = c * (a * z) := by rw [mul_assoc]
      _ = (a * z) * c := h
      _ = a * (z * c) := by rw [mul_assoc]
      _ = a * (c * z) := by rw [hzc c]
      _ = (a * c) * z := by rw [mul_assoc]
  exact mul_right_cancel h2

theorem type_i_core (hK : PiField π 2 n K) (M : LModel π 2 n K T)
    {a g b : ↥(slPi π 3 (2 ^ n) K)} {z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (hcomm : ∀ u v : ↥(slPi π 3 (2 ^ n) K ⊓
      Subgroup.centralizer ({(a : GL (Fin 3) K) * z} : Set (GL (Fin 3) K))), u * v = v * u)
    {N : Subgroup T} (hN3 : ¬ 3 ∣ Nat.card N) (hg : M.μ g ∈ N)
    (hga : M.μ g * M.μ a = M.μ a * M.μ g) (hba : (b : GL (Fin 3) K) * a = a * b) :
    M.μ g * M.μ b = M.μ b * M.μ g := by
  have hmem : ∀ c : ↥(slPi π 3 (2 ^ n) K), (c : GL (Fin 3) K) * a = a * c →
      (c : GL (Fin 3) K) ∈ slPi π 3 (2 ^ n) K ⊓
        Subgroup.centralizer ({(a : GL (Fin 3) K) * z} : Set (GL (Fin 3) K)) :=
    fun c hc => mem_cent_of_commute hz c.2 hc
  obtain ⟨u, hu3, hu⟩ := commutator_scalar hK M hga
  have hgau : (g : GL (Fin 3) K) * a * (g : GL (Fin 3) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) u * a := by
    calc (g : GL (Fin 3) K) * a * (g : GL (Fin 3) K)⁻¹ =
        ((g : GL (Fin 3) K) * a * (g : GL (Fin 3) K)⁻¹ * (a : GL (Fin 3) K)⁻¹) * a := by group
      _ = _ := by rw [hu]
  have hsc : ∀ x : GL (Fin 3) K, x * GeneralLinearGroup.scalar (Fin 3) u =
      GeneralLinearGroup.scalar (Fin 3) u * x := fun x =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u x).eq
  have hmN : orderOf (M.μ g) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hg
  have hcop : Nat.Coprime 3 (orderOf (M.μ g)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hN3 (h3.trans hmN)
  have hgm : ∀ x : GL (Fin 3) K,
      (g : GL (Fin 3) K) ^ orderOf (M.μ g) * x = x * (g : GL (Fin 3) K) ^ orderOf (M.μ g) := by
    have h1 : M.μ (g ^ orderOf (M.μ g)) = 1 := by
      rw [map_pow]
      exact pow_orderOf_eq_one _
    obtain ⟨c, hc⟩ := (M.ker_iff _).mp h1
    intro x
    have hcoe : ((g ^ orderOf (M.μ g) : ↥(slPi π 3 (2 ^ n) K)) : GL (Fin 3) K) =
        (g : GL (Fin 3) K) ^ orderOf (M.μ g) := by simp
    rw [← hcoe, ← hc]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c x).eq.symm
  have hu3' : GeneralLinearGroup.scalar (Fin 3) u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hga' : (g : GL (Fin 3) K) * a = a * g :=
    commute_of_order_prime_three hsc hu3' hgau hcop hgm
  have h2 := hcomm ⟨g, hmem g hga'⟩ ⟨b, hmem b hba⟩
  have h3 : (g : GL (Fin 3) K) * b = b * g := congrArg Subtype.val h2
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h3

theorem type_ii_core (hK : PiField π 2 n K) (hn : 2 ≤ n) (M : LModel π 2 n K T)
    {y g₀ : GL (Fin 3) K} (hg₀ : g₀ ∈ glPi π 3 (2 ^ n) K) {e₀ : Kˣ} (he₀ : e₀ ≠ 1)
    (hD : g₀⁻¹ * y * g₀ = diagE e₀) {N : Subgroup T} (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ c : ↥(slPi π 3 (2 ^ n) K), (c : GL (Fin 3) K) ∈ slPi π 3 (2 ^ n) K ⊓
      Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) →
      ∀ t ∈ N, M.μ c * t * (M.μ c)⁻¹ ∈ N)
    {g b : ↥(slPi π 3 (2 ^ n) K)}
    (hg : (g : GL (Fin 3) K) ∈ slPi π 3 (2 ^ n) K ⊓
      Subgroup.centralizer ({y} : Set (GL (Fin 3) K)))
    (hb : (b : GL (Fin 3) K) ∈ slPi π 3 (2 ^ n) K ⊓
      Subgroup.centralizer ({y} : Set (GL (Fin 3) K)))
    (hgN : M.μ g ∈ N) : M.μ g * M.μ b = M.μ b * M.μ g := by
  have := hK.finite
  have : Finite T := Finite.of_surjective M.μ M.surjective
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ := unitary_of hK
  let Φ : GL (Fin 2) K →* GL (Fin 3) K := (MulAut.conj g₀).toMonoidHom.comp blockHom
  have hCΦ : slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) =
      (glPi π 2 (2 ^ n) K).map Φ := by
    have h1 := map_conj_centralizer hπ hg₀ (diagE e₀)
    have h2 : g₀ * diagE e₀ * g₀⁻¹ = y := by rw [← hD]; group
    rw [h2, centralizer_diagE_eq hK he₀, Subgroup.map_map] at h1
    exact h1.symm
  have hΦL : ∀ B : ↥(glPi π 2 (2 ^ n) K), Φ (B : GL (Fin 2) K) ∈ slPi π 3 (2 ^ n) K := fun B => by
    have h : Φ (B : GL (Fin 2) K) ∈ (glPi π 2 (2 ^ n) K).map Φ :=
      Subgroup.mem_map_of_mem Φ B.2
    rw [← hCΦ] at h
    exact h.1
  let ΦL : ↥(glPi π 2 (2 ^ n) K) →* ↥(slPi π 3 (2 ^ n) K) :=
    (Φ.comp (glPi π 2 (2 ^ n) K).subtype).codRestrict (slPi π 3 (2 ^ n) K) hΦL
  let Ψ : ↥(glPi π 2 (2 ^ n) K) →* T := M.μ.comp ΦL
  have hSΓ : slPi π 2 (2 ^ n) K ≤ glPi π 2 (2 ^ n) K := slPi_le_glPi hπ
  let S₂ : Subgroup ↥(glPi π 2 (2 ^ n) K) :=
    (slPi π 2 (2 ^ n) K).subgroupOf (glPi π 2 (2 ^ n) K)
  let f' : ↥S₂ →* T := Ψ.comp S₂.subtype
  have hdetS : ∀ B : ↥S₂,
      (((B : ↥(glPi π 2 (2 ^ n) K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    fun B => ((mem_slPi_iff hπ).mp (Subgroup.mem_subgroupOf.mp B.2)).2
  have hinj : Function.Injective f' := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hs1 : M.μ (ΦL (s : ↥(glPi π 2 (2 ^ n) K))) = 1 := hs
    obtain ⟨c, hc⟩ := (M.ker_iff _).mp hs1
    set B : GL (Fin 2) K := ((s : ↥(glPi π 2 (2 ^ n) K)) : GL (Fin 2) K) with hB
    have hΦB : g₀ * blockHom B * g₀⁻¹ = GeneralLinearGroup.scalar (Fin 3) c := hc.symm
    have hbh : blockHom B = GeneralLinearGroup.scalar (Fin 3) c := by
      calc blockHom B = g₀⁻¹ * (g₀ * blockHom B * g₀⁻¹) * g₀ := by group
        _ = g₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) c * g₀ := by rw [hΦB]
        _ = GeneralLinearGroup.scalar (Fin 3) c := by
            rw [mul_assoc, ← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c g₀).eq,
              inv_mul_cancel_left]
    have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hbh
    have hdB : GeneralLinearGroup.det B = 1 :=
      Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact hdetS s)
    have hc1 : c = 1 := by
      have h00' : (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) = (c : K) := by
        simpa [coe_blockHom, blockMat] using h00
      rw [hdB, inv_one, Units.val_one] at h00'
      exact Units.ext h00'.symm
    rw [hc1, map_one] at hbh
    have hB1 : B = 1 := blockHom_injective (by rw [hbh, map_one])
    exact Subtype.ext (Subtype.ext hB1)
  obtain ⟨hsimple, hcard⟩ := sl2_data hK hn
  let e : ↥(slPi π 2 (2 ^ n) K) ≃* ↥f'.range :=
    (Subgroup.subgroupOfEquivOfLe hSΓ).symm.trans (MonoidHom.ofInjective hinj)
  have hR₂simple : IsSimpleGroup ↥f'.range := e.symm.isSimpleGroup
  have hR₂card : Nat.card ↥f'.range = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hcard
  have h3 : 3 ∣ Nat.card ↥f'.range := by
    rw [hR₂card]
    refine Dvd.dvd.mul_left ?_ _
    have h4 : (2 ^ n) ^ 2 % 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
      norm_num
    omega
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥f'.range) 3 h3
  have hnormR : ∀ s ∈ f'.range, ∀ t ∈ N, s * t * s⁻¹ ∈ N := by
    rintro _ ⟨σ, rfl⟩ t ht
    have hmem : ((ΦL (σ : ↥(glPi π 2 (2 ^ n) K))) : GL (Fin 3) K) ∈
        slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) := by
      rw [hCΦ]
      exact Subgroup.mem_map_of_mem Φ (σ : ↥(glPi π 2 (2 ^ n) K)).2
    exact hNn (ΦL σ) hmem t ht
  have hP : (N.subgroupOf f'.range).Normal := ⟨fun p hp s => by
    rw [Subgroup.mem_subgroupOf] at hp ⊢
    exact hnormR s s.2 p hp⟩
  have hbot : ∀ t ∈ N, t ∈ f'.range → t = 1 := by
    intro t htN htR
    rcases hP.eq_bot_or_eq_top with h | h
    · have h1 : (⟨t, htR⟩ : ↥f'.range) ∈ N.subgroupOf f'.range := Subgroup.mem_subgroupOf.mpr htN
      rw [h, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · exfalso
      have h1 : w ∈ N.subgroupOf f'.range := by rw [h]; exact Subgroup.mem_top w
      have h2 : orderOf ((w : T)) ∣ Nat.card N :=
        Subgroup.orderOf_dvd_natCard N (Subgroup.mem_subgroupOf.mp h1)
      rw [Subgroup.orderOf_coe, hw] at h2
      exact hN3 h2
  have hgC := hg
  rw [hCΦ] at hgC
  obtain ⟨B₁, hB₁, hB₁g⟩ := Subgroup.mem_map.mp hgC
  have hbC := hb
  rw [hCΦ] at hbC
  obtain ⟨B₂, hB₂, hB₂b⟩ := Subgroup.mem_map.mp hbC
  set c : GL (Fin 2) K := B₁ * B₂ * B₁⁻¹ * B₂⁻¹ with hc
  have hcΓ : c ∈ glPi π 2 (2 ^ n) K :=
    mul_mem (mul_mem (mul_mem hB₁ hB₂) (inv_mem hB₁)) (inv_mem hB₂)
  have hcdet : (c : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have : GeneralLinearGroup.det c = 1 := by
      rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_comm (GeneralLinearGroup.det B₁) (GeneralLinearGroup.det B₂)]
      group
    rw [← GeneralLinearGroup.val_det_apply, this, Units.val_one]
  have hcS : c ∈ slPi π 2 (2 ^ n) K := (mem_slPi_iff hπ).mpr ⟨hcΓ, hcdet⟩
  have hΦc : Φ c = (g : GL (Fin 3) K) * b * (g : GL (Fin 3) K)⁻¹ * (b : GL (Fin 3) K)⁻¹ := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, hB₁g, hB₂b]
  set r : T := f' ⟨⟨c, hcΓ⟩, Subgroup.mem_subgroupOf.mpr hcS⟩ with hr
  have hrc : r = M.μ g * M.μ b * (M.μ g)⁻¹ * (M.μ b)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    show M.μ (ΦL ⟨c, hcΓ⟩) = _
    congr 1
    exact Subtype.ext hΦc
  have hrN : r ∈ N := by
    have h1 := hNn b hb (M.μ g)⁻¹ (inv_mem hgN)
    have h2 : r = M.μ g * (M.μ b * (M.μ g)⁻¹ * (M.μ b)⁻¹) := by rw [hrc]; group
    rw [h2]
    exact mul_mem hgN h1
  have hr1 : r = 1 := hbot r hrN ⟨_, rfl⟩
  rw [hrc] at hr1
  calc M.μ g * M.μ b = M.μ g * M.μ b * (M.μ g)⁻¹ * (M.μ b)⁻¹ * (M.μ b * M.μ g) := by group
    _ = M.μ b * M.μ g := by rw [hr1, one_mul]

theorem toral_core (hn : 4 ≤ n) (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n))
    (M : LModel π 2 n K T) {E : Subgroup T} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (htor : ∀ a b : ↥(slPi π 3 (2 ^ n) K), M.μ a ∈ E → M.μ b ∈ E → a * b = b * a)
    {x : T} (hxE : x ∈ E) (hx1 : x ≠ 1) {N : Subgroup T}
    (hN : N ≤ Subgroup.centralizer ({x} : Set T))
    (hNn : Subgroup.centralizer ({x} : Set T) ≤ Subgroup.normalizer (N : Set T))
    (hN3 : ¬ 3 ∣ Nat.card N) : ∀ t ∈ N, ∀ e ∈ E, t * e = e * t := by
  have := hK.finite
  have : Finite T := Finite.of_surjective M.μ M.surjective
  obtain ⟨a, rfl⟩ := M.surjective x
  have haZ : (a : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := fun h => hx1 ((M.ker_iff a).mpr h)
  have ha3 : (a : GL (Fin 3) K) ^ 3 ∈ StatedScalars (Fin 3) K := by
    have h1 : M.μ (a ^ 3) = 1 := by
      rw [map_pow]
      exact hE.2 _ hxE
    have h2 := (M.ker_iff (a ^ 3)).mp h1
    simpa using h2
  obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := type_data hK hq a.2 haZ ha3
  have hEmem : ∀ b : ↥(slPi π 3 (2 ^ n) K), M.μ b ∈ E → (b : GL (Fin 3) K) ∈
      slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({(a : GL (Fin 3) K) * z} : Set (GL (Fin 3) K)) :=
    fun b hb => mem_cent_of_commute hz b.2 (congrArg Subtype.val (htor b a hb hxE))
  have hNnorm : ∀ c : ↥(slPi π 3 (2 ^ n) K), (c : GL (Fin 3) K) ∈ slPi π 3 (2 ^ n) K ⊓
      Subgroup.centralizer ({(a : GL (Fin 3) K) * z} : Set (GL (Fin 3) K)) →
      ∀ t ∈ N, M.μ c * t * (M.μ c)⁻¹ ∈ N := by
    intro c hc t ht
    have hca : (c : GL (Fin 3) K) * a = a * c :=
      commute_of_mem_cent hz (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
    have hcx : M.μ c ∈ Subgroup.centralizer ({M.μ a} : Set T) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg M.μ (Subtype.ext hca)
    exact (Subgroup.mem_normalizer_iff.mp (hNn hcx) t).mp ht
  intro t ht e he
  obtain ⟨g, rfl⟩ := M.surjective t
  obtain ⟨b, rfl⟩ := M.surjective e
  have hgx : M.μ g * M.μ a = M.μ a * M.μ g := Subgroup.mem_centralizer_singleton_iff.mp (hN ht)
  rcases hy with ⟨⟨eA⟩, -⟩ | ⟨⟨g₀, hg₀, e₀, he₀, hD⟩, hcent⟩
  · have hAc : ∀ u v : ↥(slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer
        ({(a : GL (Fin 3) K) * z} : Set (GL (Fin 3) K))), u * v = v * u := fun u v =>
      eA.injective (by rw [map_mul, map_mul, mul_comm])
    exact type_i_core hK M hz hAc hN3 ht hgx (congrArg Subtype.val (htor b a he hxE))
  · have hgC : (g : GL (Fin 3) K) ∈ centMod (slPi π 3 (2 ^ n) K) ((a : GL (Fin 3) K) * z) :=
      mem_centMod_of_commute hK M hz hgx
    rw [hcent] at hgC
    exact type_ii_core hK (by omega) M hg₀ he₀ hD hN3 hNnorm hgC (hEmem b he) ht

end CFSG.RankThree.PartTwo.Sec15.KS1424
