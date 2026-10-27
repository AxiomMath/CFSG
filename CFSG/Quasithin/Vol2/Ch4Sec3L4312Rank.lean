module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Rank
public import CFSG.Quasithin.Vol2.KGNatSL3Lev
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank L436
open scoped IsMulCommutative commutatorElement MatrixGroups

namespace L4312

theorem isCyclic_of_isPGroup_ker {X J : Type*} [Group X] [Group J] (χ : X →* J)
    (hχ : IsPGroup 2 χ.ker)
    (hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (Q : Sylow r J),
      IsCyclic (Q : Subgroup J))
    {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) {R : Subgroup X} (hR : IsPGroup r R) :
    IsCyclic R := by
  have hinj : Function.Injective (χ.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨a, ha⟩ := hR x
    obtain ⟨b, hb⟩ := hχ ⟨(x : X), hx⟩
    have ha' : (x : X) ^ r ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hb' : (x : X) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have hcop : Nat.Coprime (r ^ a) (2 ^ b) :=
      Nat.Coprime.pow a b ((Nat.coprime_primes hr.out Nat.prime_two).mpr hr2)
    have h3 : orderOf (x : X) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha')
        (orderOf_dvd_of_pow_eq_one hb')
    exact Subtype.ext (orderOf_eq_one_iff.mp h3)
  obtain ⟨Q, hQ⟩ := (hR.map χ).exists_le_sylow
  have hQc := hcyc r hr.out hr2 Q
  have hRc : IsCyclic (R.map χ) := Subgroup.isCyclic_of_le hQ
  have hrange : (χ.comp R.subtype).range = R.map χ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact (MulEquiv.isCyclic ((MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr hrange))).mpr hRc

theorem sl2_isCyclic_of_isPGroup {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {R : Subgroup SL(2, F)}
    (hR : IsPGroup r R) : IsCyclic R := by
  refine isCyclic_of_isPGroup_ker (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.toMonoidHom
    ?_ (fun r _ hr2 _ Q => psl_two_sylow_isCyclic_even hn hF hr2 Q) hr2 hR
  rw [(MonoidHom.ker_eq_bot_iff _).mpr
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.injective]
  exact IsPGroup.of_bot

section Proj

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem exists_t' {A B K : Subgroup Ω} (hBA : B ≤ Subgroup.centralizer (A : Set Ω))
    (hKAB : K ≤ A ⊔ B) (hKB : K ≤ Subgroup.normalizer (B : Set Ω)) (hKB2 : IsPGroup 2 ↥(K ⊓ B))
    (hO2 : pCoreOf 2 A = ⊥) (hKp : ⁅K, K⁆ = K) {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (χ : ↥K →* SL(2, F))
    (hχ : Function.Surjective χ) (hχk : IsPGroup 2 χ.ker) {a : Ω} (haK : a ∈ K)
    (hao : Odd (orderOf a)) :
    ∃ t ∈ A, orderOf t = orderOf a ∧ (∀ j : ℕ, t ^ j ∈ B → a ^ j = 1) ∧
      ∀ y : Ω, (∀ x ∈ A, y * x * y⁻¹ ∈ A) → (∀ b ∈ B, y * b * y⁻¹ ∈ B) →
        (∀ k ∈ K, y * k * y⁻¹ ∈ K) → y * a = a * y → y * t = t * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := K ⊔ B with hY
  have hYB : Y ≤ Subgroup.normalizer (B : Set Ω) := _root_.sup_le hKB Subgroup.le_normalizer
  have hBY : B ≤ Y := le_sup_right
  have : (B.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).2 hYB
  set q := QuotientGroup.mk' (B.subgroupOf Y) with hq
  have hqeq : ∀ u v : ↥Y, q u = q v ↔ (u : Ω)⁻¹ * v ∈ B := by
    intro u v
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp
  set ι : ↥K →* ↥Y ⧸ B.subgroupOf Y := q.comp (Subgroup.inclusion le_sup_left) with hι
  have hιs : Function.Surjective ι := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf Y) z
    have hy : (y : Ω) ∈ ((K ⊔ B : Subgroup Ω) : Set Ω) := y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K B hKB] at hy
    obtain ⟨k, hk, b, hb, hkb⟩ := hy
    refine ⟨⟨k, hk⟩, ?_⟩
    show q (Subgroup.inclusion le_sup_left ⟨k, hk⟩) = q y
    rw [hqeq]
    have e : (k : Ω)⁻¹ * y = b := by rw [← hkb]; group
    simpa using e ▸ hb
  have hι1 : ∀ k : ↥K, ι k = 1 ↔ (k : Ω) ∈ B := by
    intro k
    have h := hqeq 1 (Subgroup.inclusion le_sup_left k)
    rw [map_one] at h
    rw [hι, MonoidHom.comp_apply, eq_comm, h]
    simp
  have hKBχ : ι.ker ≤ χ.ker := by
    set N : Subgroup ↥K := (K ⊓ B).subgroupOf K with hN
    have hNn : N.Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun k hk => ?_
      exact mem_normalizer_inf (Subgroup.le_normalizer hk) (hKB hk)
    have hN2 : IsPGroup 2 ↥(N.map χ) := by
      have h1 : IsPGroup 2 ↥N := A4.isPGroup_subgroupOf_of_le inf_le_left hKB2
      exact h1.map χ
    have hNm : (N.map χ).Normal := hNn.map χ hχ
    have hbot := Vol2.KGNat.eq_bot_of_normal_isPGroup_SL2 hN2
    intro k hk
    have hkN : k ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact ⟨k.2, (hι1 k).mp hk⟩
    have : χ k ∈ N.map χ := Subgroup.mem_map_of_mem χ hkN
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  set χ' : ↥Y ⧸ B.subgroupOf Y →* SL(2, F) := (MonoidHom.liftOfSurjective ι hιs) ⟨χ, hKBχ⟩
    with hχ'
  have hχ'ι : ∀ k : ↥K, χ' (ι k) = χ k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  have hker' : IsPGroup 2 χ'.ker := by
    have hle : χ'.ker ≤ χ.ker.map ι := by
      intro z hz
      obtain ⟨k, rfl⟩ := hιs z
      refine Subgroup.mem_map_of_mem ι ?_
      rw [MonoidHom.mem_ker, ← hχ'ι]
      exact hz
    exact (hχk.map ι).to_le hle
  have hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (Q : Sylow r (↥Y ⧸ B.subgroupOf Y)),
      IsCyclic (Q : Subgroup (↥Y ⧸ B.subgroupOf Y)) := fun r _ hr2 _ Q =>
    isCyclic_of_isPGroup_ker χ' hker'
      (fun r' _ hr2' _ Q' => sl2_isCyclic_of_isPGroup hn hF hr2' Q'.isPGroup') hr2 Q.isPGroup'
  set M := A ⊓ Y with hM
  set φ₀ : ↥M →* ↥Y ⧸ B.subgroupOf Y := q.comp (Subgroup.inclusion inf_le_right) with hφ₀
  have hφ₀s : Function.Surjective φ₀ := by
    intro z
    obtain ⟨k, rfl⟩ := hιs z
    have hk : (k : Ω) ∈ ((A ⊔ B : Subgroup Ω) : Set Ω) := hKAB k.2
    have hAB : A ≤ Subgroup.normalizer (B : Set Ω) :=
      (Subgroup.le_centralizer_iff.mp hBA).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hk
    obtain ⟨x, hx, b, hb, hxb⟩ := hk
    have hxY : x ∈ Y := by
      have e : x = (k : Ω) * b⁻¹ := by rw [← hxb]; group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right (inv_mem hb))
    refine ⟨⟨x, hx, hxY⟩, ?_⟩
    show q (Subgroup.inclusion inf_le_right ⟨x, hx, hxY⟩) = q (Subgroup.inclusion le_sup_left k)
    rw [hqeq]
    have e : x⁻¹ * k = b := by rw [← hxb]; group
    simpa using e ▸ hb
  have hφ₀eq : ∀ (m : ↥M) (k : ↥K), φ₀ m = ι k ↔ (k : Ω)⁻¹ * m ∈ B := by
    intro m k
    rw [hφ₀, hι, MonoidHom.comp_apply, MonoidHom.comp_apply, eq_comm, hqeq]
    simp
  set P' : Subgroup ↥M := perfectCore ⊤ with hP'
  let ψ : ↥P' →* ↥Y ⧸ B.subgroupOf Y := φ₀.comp P'.subtype
  have hYBp : Group.IsPerfect (↥Y ⧸ B.subgroupOf Y) := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKp
    exact Group.IsPerfect.ofSurjective hιs
  have hQtop : perfectCore (⊤ : Subgroup (↥Y ⧸ B.subgroupOf Y)) = ⊤ :=
    perfectCore_eq_self_of_perfect (Group.isPerfect_def.mp hYBp)
  have hψs : Function.Surjective ψ := by
    have h1 : P'.map φ₀ = ⊤ := by
      rw [hP', map_perfectCore, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hφ₀s,
        hQtop]
    intro z
    obtain ⟨m, hm, hmz⟩ : z ∈ P'.map φ₀ := h1 ▸ Subgroup.mem_top z
    exact ⟨⟨m, hm⟩, hmz⟩
  have : Group.IsPerfect ↥P' := Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  have hkerB : ∀ m : ↥P', ψ m = 1 → (((m : ↥M) : Ω)) ∈ B := by
    intro m hm
    have h1 : φ₀ (m : ↥M) = ι 1 := by rw [map_one]; exact hm
    have := (hφ₀eq (m : ↥M) 1).mp h1
    simpa using this
  have hkerc : ψ.ker ≤ Subgroup.center ↥P' := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    have hb := hkerB m hm
    have hgA : ((g : ↥M) : Ω) ∈ A := (g : ↥M).2.1
    exact Subgroup.mem_centralizer_iff.mp (hBA hb) _ hgA
  have h2 : IsPGroup 2 ψ.ker := isPGroup_two_ker_of_cyclic_odd_sylow ψ hψs hkerc hcyc
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hb := hkerB m hm
    have hmA : ((m : ↥M) : Ω) ∈ A := (m : ↥M).2.1
    obtain ⟨k, hk⟩ := h2 ⟨m, hm⟩
    have hk' : ((m : ↥M) : Ω) ^ 2 ^ k = 1 := by
      have := congrArg (fun x : ↥ψ.ker => (((x : ↥P') : ↥M) : Ω)) hk
      simpa using this
    have hzA : Subgroup.zpowers ((m : ↥M) : Ω) ≤ A := Subgroup.zpowers_le.mpr hmA
    have hzN : A ≤ Subgroup.normalizer (Subgroup.zpowers ((m : ↥M) : Ω) : Set Ω) := by
      intro g hg
      have hc : Commute g ((m : ↥M) : Ω) := Subgroup.mem_centralizer_iff.mp (hBA hb) g hg
      have hgc : g ∈ Subgroup.centralizer (Subgroup.zpowers ((m : ↥M) : Ω) : Set Ω) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨j, rfl⟩
        exact ((hc.zpow_right j).eq).symm
      exact Subgroup.centralizer_le_normalizer _ hgc
    have hz2 : IsPGroup 2 (Subgroup.zpowers ((m : ↥M) : Ω)) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
    have hz : Subgroup.zpowers ((m : ↥M) : Ω) ≤ pCoreOf 2 A :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hzA hzN hz2
    rw [hO2] at hz
    have h1 := hz (Subgroup.mem_zpowers _)
    rw [Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hKB1 : ∀ j : ℕ, ι (⟨a, haK⟩ ^ j) = 1 → a ^ j = 1 := by
    intro j hj
    have hb : a ^ j ∈ B := by
      have := (hι1 _).mp hj
      simpa using this
    obtain ⟨e, he⟩ := hKB2 ⟨a ^ j, Subgroup.pow_mem _ haK j, hb⟩
    have he' : (a ^ j) ^ 2 ^ e = 1 := by
      have := congrArg Subtype.val he
      simpa using this
    have hd1 : orderOf (a ^ j) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one he'
    have hd2 : orderOf (a ^ j) ∣ orderOf a := orderOf_dvd_of_mem_zpowers
      (Subgroup.npow_mem_zpowers a j)
    have hcop : Nat.Coprime (2 ^ e) (orderOf a) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hao)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  obtain ⟨m, hm⟩ := hψs (ι ⟨a, haK⟩)
  have hmo : orderOf m = orderOf a := by
    have h1 := orderOf_injective ψ hinj m
    rw [hm] at h1
    rw [← h1]
    apply le_antisymm
    · apply Nat.le_of_dvd (orderOf_pos _)
      have := orderOf_map_dvd ι ⟨a, haK⟩
      rwa [Subgroup.orderOf_mk] at this
    · apply Nat.le_of_dvd (orderOf_pos _)
      apply orderOf_dvd_of_pow_eq_one
      apply hKB1
      rw [map_pow, pow_orderOf_eq_one]
  refine ⟨((m : ↥M) : Ω), (m : ↥M).2.1, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hmo]
  · intro j hj
    apply hKB1
    have h1 : ψ (m ^ j) = ι 1 := by
      rw [map_one]
      have hmj : (((m ^ j : ↥P') : ↥M) : Ω) ∈ B := by simpa using hj
      have := (hφ₀eq ((m ^ j : ↥P') : ↥M) 1).mpr (by simpa using hmj)
      rw [map_one] at this
      exact this
    rw [map_pow, hm, map_one] at h1
    rw [map_pow]
    exact h1
  · intro y hyA hyB hyK hya
    have hyM : ∀ x ∈ M, y * x * y⁻¹ ∈ M := by
      intro x hx
      refine ⟨hyA x hx.1, ?_⟩
      have hle : K ⊔ B ≤ (K ⊔ B).comap (MulAut.conj y).toMonoidHom := by
        refine _root_.sup_le (fun k hk => ?_) (fun b hb => ?_)
        · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact Subgroup.mem_sup_left (hyK k hk)
        · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact Subgroup.mem_sup_right (hyB b hb)
      simpa [MulAut.conj_apply] using hle hx.2
    let c : ↥M →* ↥M :=
      { toFun := fun x => ⟨y * x * y⁻¹, hyM x x.2⟩
        map_one' := by ext; simp
        map_mul' := fun u v => by
          ext
          simp only [Subgroup.coe_mul]
          group }
    have hcinj : Function.Injective c := fun u v h => by
      have h1 := congrArg Subtype.val h
      simp only [c, MonoidHom.coe_mk, OneHom.coe_mk] at h1
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
    have hcsurj : Function.Surjective c := Finite.injective_iff_surjective.mp hcinj
    have hcP : ∀ x ∈ P', c x ∈ P' := by
      have h1 : P'.map c = P' := by
        rw [hP', map_perfectCore, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hcsurj]
      intro x hx
      rw [← h1]
      exact Subgroup.mem_map_of_mem c hx
    have hψc : ψ ⟨c m, hcP m m.2⟩ = ψ m := by
      have hm' : φ₀ (m : ↥M) = ι ⟨a, haK⟩ := hm
      have h1 := (hφ₀eq (m : ↥M) ⟨a, haK⟩).mp hm'
      show φ₀ (c m) = φ₀ (m : ↥M)
      rw [hm', hφ₀eq]
      have e : a⁻¹ * ((c m : ↥M) : Ω) = y * (a⁻¹ * ((m : ↥M) : Ω)) * y⁻¹ := by
        show a⁻¹ * (y * ((m : ↥M) : Ω) * y⁻¹) = _
        have hya' : y * a⁻¹ = a⁻¹ * y := by
          calc y * a⁻¹ = a⁻¹ * (a * y) * a⁻¹ := by group
            _ = a⁻¹ * (y * a) * a⁻¹ := by rw [hya]
            _ = a⁻¹ * y := by group
        calc a⁻¹ * (y * ((m : ↥M) : Ω) * y⁻¹) = (a⁻¹ * y) * ((m : ↥M) : Ω) * y⁻¹ := by group
          _ = (y * a⁻¹) * ((m : ↥M) : Ω) * y⁻¹ := by rw [hya']
          _ = y * (a⁻¹ * ((m : ↥M) : Ω)) * y⁻¹ := by group
      simpa using e ▸ hyB _ (by simpa using h1)
    have heq : (⟨c m, hcP m m.2⟩ : ↥P') = m := hinj hψc
    have h3 := congrArg (fun x : ↥P' => ((x : ↥M) : Ω)) heq
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk] at h3
    calc y * ((m : ↥M) : Ω) = (y * ((m : ↥M) : Ω) * y⁻¹) * y := by group
      _ = ((m : ↥M) : Ω) * y := by rw [h3]

end Proj

section Rank

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem exists_le_of_commuting' {𝓛 : Set (Subgroup Ω)}
    (hcomm : ∀ A ∈ 𝓛, ∀ B ∈ 𝓛, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hO2 : ∀ A ∈ 𝓛, pCoreOf 2 A = ⊥) {K : Subgroup Ω}
    (hKn : ∀ N : Subgroup Ω, N ≤ K → K ≤ Subgroup.normalizer (N : Set Ω) →
      N = K ∨ IsPGroup 2 ↥N)
    (hKp : ⁅K, K⁆ = K) {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (χ : ↥K →* SL(2, F)) (hχ : Function.Surjective χ)
    (hχk : IsPGroup 2 χ.ker) (hKL : K ≤ sSup 𝓛) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {a : Ω} (haK : a ∈ K) (hao : orderOf a = p) {y : Ω} (hyo : orderOf y = p)
    (hya : y * a = a * y) (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (hyL : ∀ A ∈ 𝓛, A.map (MulAut.conj y).toMonoidHom ∈ 𝓛) (hyS : y ∉ sSup 𝓛)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup Ω) ≤ 2) :
    ∃ A ∈ 𝓛, K ≤ A := by
  classical
  set mv : Subgroup Ω → Prop := fun A => ∃ x ∈ A, ∃ k ∈ K, x * k ≠ k * x with hmv
  have haodd : Odd (orderOf a) := by
    rw [hao]
    exact hp.out.odd_of_ne_two hp2
  have hKB1 : ∀ A ∈ 𝓛, mv A → IsPGroup 2 ↥(K ⊓ sSup (𝓛 \ {A})) := by
    intro A hA hmvA
    have hKN : K ≤ Subgroup.normalizer ((sSup (𝓛 \ {A}) : Subgroup Ω) : Set Ω) :=
      hKL.trans (sSup_le_normalizer_sSup_diff hcomm A)
    rcases hKn (K ⊓ sSup (𝓛 \ {A})) inf_le_left (fun k hk =>
        mem_normalizer_inf (Subgroup.le_normalizer hk) (hKN hk)) with h | h
    · exfalso
      obtain ⟨x, hx, k, hk, hxk⟩ := hmvA
      have hkB : k ∈ sSup (𝓛 \ {A}) := by
        have : k ∈ K ⊓ sSup (𝓛 \ {A}) := by
          rw [h]
          exact hk
        exact this.2
      exact hxk (Subgroup.mem_centralizer_iff.mp (sSup_diff_le_centralizer hcomm hA hkB) x hx)
    · exact h
  have ht : ∀ A ∈ 𝓛, mv A → ∃ t ∈ A, orderOf t = p ∧
      (∀ j : ℕ, t ^ j ∈ sSup (𝓛 \ {A}) → p ∣ j) ∧
      (A.map (MulAut.conj y).toMonoidHom = A → y * t = t * y) := by
    intro A hA hmvA
    obtain ⟨t, htA, hto, htj, hty⟩ := exists_t' (sSup_diff_le_centralizer hcomm hA)
      (hKL.trans (sSup_eq_sup_sSup_diff hA).le) (hKL.trans (sSup_le_normalizer_sSup_diff hcomm A))
      (hKB1 A hA hmvA) (hO2 A hA) hKp hn hF χ hχ hχk haK haodd
    refine ⟨t, htA, hto.trans hao, fun j hj => hao ▸ orderOf_dvd_of_pow_eq_one (htj j hj),
      fun hyA => hty y ?_ ?_ hyK hya⟩
    · intro x hx
      have : (MulAut.conj y).toMonoidHom x ∈ A.map (MulAut.conj y).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hyA] at this
      simpa [MulAut.conj_apply] using this
    · refine conj_mem_sSup fun D hD d hd => ?_
      have hD' : D.map (MulAut.conj y).toMonoidHom ∈ 𝓛 \ {A} := by
        refine ⟨hyL D hD.1, fun h => hD.2 ?_⟩
        have h1 : D.map (MulAut.conj y).toMonoidHom = A.map (MulAut.conj y).toMonoidHom := by
          rw [hyA]
          exact h
        exact Subgroup.map_injective (MulAut.conj y).injective h1
      have : (MulAut.conj y).toMonoidHom d ∈ D.map (MulAut.conj y).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hd
      exact le_sSup hD' (by simpa [MulAut.conj_apply] using this)
  have hex : ∃ A ∈ 𝓛, mv A := by
    by_contra hno
    push Not at hno
    have hc : sSup 𝓛 ≤ Subgroup.centralizer (K : Set Ω) := sSup_le fun A hA x hx =>
      Subgroup.mem_centralizer_iff.mpr fun k hk => by
        have := hno A hA
        simp only [hmv, not_exists, not_and, not_not] at this
        exact (this x hx k hk).symm
    have hb : ⁅K, K⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (hKL.trans hc)
    rw [hKp] at hb
    have ha1 : a = 1 := by
      have : a ∈ (⊥ : Subgroup Ω) := hb ▸ haK
      exact Subgroup.mem_bot.mp this
    rw [ha1, orderOf_one] at hao
    exact hp.out.one_lt.ne hao
  obtain ⟨A₀, hA₀, hmv₀⟩ := hex
  have hpow : ∀ {t : Ω}, orderOf t = p → t ^ p = 1 := fun h => h ▸ pow_orderOf_eq_one _
  have hzero : ∀ (c : ZMod p), p ∣ c.val → c = 0 := fun c h =>
    (ZMod.val_eq_zero c).mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt c))
  by_cases h1 : ∃ A₁ ∈ 𝓛, A₁ ≠ A₀ ∧ mv A₁
  · exfalso
    obtain ⟨A₁, hA₁, hne, hmv₁⟩ := h1
    obtain ⟨t₀, ht₀A, ht₀o, ht₀j, ht₀y⟩ := ht A₀ hA₀ hmv₀
    obtain ⟨t₁, ht₁A, ht₁o, ht₁j, ht₁y⟩ := ht A₁ hA₁ hmv₁
    have hA₁B₀ : A₁ ≤ sSup (𝓛 \ {A₀}) := le_sSup ⟨hA₁, hne⟩
    have hA₀B₁ : A₀ ≤ sSup (𝓛 \ {A₁}) := le_sSup ⟨hA₀, hne.symm⟩
    have hc01 : t₀ * t₁ = t₁ * t₀ := hcomm A₀ hA₀ A₁ hA₁ hne.symm t₀ ht₀A t₁ ht₁A
    by_cases h2 : ∃ A₂ ∈ 𝓛, A₂ ≠ A₀ ∧ A₂ ≠ A₁ ∧ mv A₂
    · obtain ⟨A₂, hA₂, hne₀, hne₁, hmv₂⟩ := h2
      obtain ⟨t₂, ht₂A, ht₂o, -, -⟩ := ht A₂ hA₂ hmv₂
      have hc02 := hcomm A₀ hA₀ A₂ hA₂ hne₀.symm t₀ ht₀A t₂ ht₂A
      have hc12 := hcomm A₁ hA₁ A₂ hA₂ hne₁.symm t₁ ht₁A t₂ ht₂A
      have hA₂B₀ : A₂ ≤ sSup (𝓛 \ {A₀}) := le_sSup ⟨hA₂, hne₀⟩
      have hA₂B₁ : A₂ ≤ sSup (𝓛 \ {A₁}) := le_sSup ⟨hA₂, hne₁⟩
      have h3 := three_le_pRank_of_commute (hpow ht₀o) (hpow ht₁o) (hpow ht₂o) hc01 hc02 hc12
        (fun a b d hab => by
          have ha : a = 0 := by
            apply hzero
            apply ht₀j
            have e : t₀ ^ a.val = (t₁ ^ b.val * t₂ ^ d.val)⁻¹ := by
              rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
              exact hab
            rw [e]
            exact inv_mem (mul_mem (pow_mem (hA₁B₀ ht₁A) _) (pow_mem (hA₂B₀ ht₂A) _))
          rw [ha, ZMod.val_zero, pow_zero, one_mul] at hab
          have hb : b = 0 := by
            apply hzero
            apply ht₁j
            rw [eq_inv_of_mul_eq_one_left hab]
            exact inv_mem (pow_mem (hA₂B₁ ht₂A) _)
          rw [hb, ZMod.val_zero, pow_zero, one_mul] at hab
          have hd : d = 0 := by
            apply hzero
            have := orderOf_dvd_of_pow_eq_one hab
            rwa [ht₂o] at this
          exact ⟨ha, hb, hd⟩)
      omega
    · push Not at h2
      have hmvy : ∀ A, mv A → mv (A.map (MulAut.conj y).toMonoidHom) := by
        rintro A ⟨x, hx, k, hk, hxk⟩
        refine ⟨y * x * y⁻¹, ⟨x, hx, by simp [MulAut.conj_apply]⟩, y * k * y⁻¹, hyK k hk,
          fun h => hxk ?_⟩
        have e1 : y * x * y⁻¹ * (y * k * y⁻¹) = y * (x * k) * y⁻¹ := by group
        have e2 : y * k * y⁻¹ * (y * x * y⁻¹) = y * (k * x) * y⁻¹ := by group
        rw [e1, e2] at h
        exact mul_left_cancel (mul_right_cancel h)
      have hin : ∀ A ∈ 𝓛, mv A → A = A₀ ∨ A = A₁ := fun A hA hmvA => by
        by_contra h
        push Not at h
        exact h2 A hA h.1 h.2 hmvA
      have hσ₀ := hin _ (hyL A₀ hA₀) (hmvy A₀ hmv₀)
      have hσ₁ := hin _ (hyL A₁ hA₁) (hmvy A₁ hmv₁)
      have hinjσ : ∀ X Y : Subgroup Ω, X.map (MulAut.conj y).toMonoidHom =
          Y.map (MulAut.conj y).toMonoidHom → X = Y := fun X Y h =>
        Subgroup.map_injective (MulAut.conj y).injective h
      have hfix : A₀.map (MulAut.conj y).toMonoidHom = A₀ ∧
          A₁.map (MulAut.conj y).toMonoidHom = A₁ := by
        by_contra hnot
        have hswap : A₀.map (MulAut.conj y).toMonoidHom = A₁ ∧
            A₁.map (MulAut.conj y).toMonoidHom = A₀ := by
          rcases hσ₀ with h0 | h0 <;> rcases hσ₁ with h1' | h1'
          · exact absurd (hinjσ _ _ (h0.trans h1'.symm)) hne.symm
          · exact absurd ⟨h0, h1'⟩ hnot
          · exact ⟨h0, h1'⟩
          · exact absurd (hinjσ _ _ (h0.trans h1'.symm)) hne.symm
        have hsq : ∀ x ∈ A₀, y * (y * x * y⁻¹) * y⁻¹ ∈ A₀ := by
          intro x hx
          have h1 : y * x * y⁻¹ ∈ A₁ := by
            rw [← hswap.1]
            exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
          have h2 : y * (y * x * y⁻¹) * y⁻¹ ∈ A₁.map (MulAut.conj y).toMonoidHom :=
            ⟨_, h1, by simp [MulAut.conj_apply]⟩
          rwa [hswap.2] at h2
        have hev : ∀ j : ℕ, ∀ x ∈ A₀, y ^ (2 * j) * x * (y ^ (2 * j))⁻¹ ∈ A₀ := by
          intro j
          induction j with
          | zero => intro x hx; simpa using hx
          | succ j ih =>
            intro x hx
            have e : y ^ (2 * (j + 1)) * x * (y ^ (2 * (j + 1)))⁻¹ =
                y * (y * (y ^ (2 * j) * x * (y ^ (2 * j))⁻¹) * y⁻¹) * y⁻¹ := by
              rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, pow_succ]
              group
            rw [e]
            exact hsq _ (ih x hx)
        obtain ⟨j, hj⟩ : ∃ j : ℕ, p + 1 = 2 * j := by
          rcases hp.out.eq_two_or_odd' with h | h
          · exact absurd h hp2
          · obtain ⟨k, hk⟩ := h
            exact ⟨k + 1, by omega⟩
        have hyp1 : y ^ (2 * j) = y := by
          rw [← hj, pow_succ, hpow hyo, one_mul]
        have hle : A₀.map (MulAut.conj y).toMonoidHom ≤ A₀ := by
          rintro _ ⟨x, hx, rfl⟩
          have := hev j x hx
          rw [hyp1] at this
          simpa [MulAut.conj_apply] using this
        have hcard : Nat.card ↥(A₀.map (MulAut.conj y).toMonoidHom) = Nat.card ↥A₀ :=
          Subgroup.card_map_of_injective (MulAut.conj y).injective
        have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
        exact hne (hswap.1.symm.trans heq)
      have h3 := three_le_pRank_of_commute (hpow ht₀o) (hpow ht₁o) (hpow hyo) hc01
        (ht₀y hfix.1).symm (ht₁y hfix.2).symm
        (fun a b d hab => by
          have hd : d = 0 := by
            by_contra hd0
            apply hyS
            have hyd : y ^ d.val ∈ sSup 𝓛 := by
              have e : y ^ d.val = (t₀ ^ a.val * t₁ ^ b.val)⁻¹ := eq_inv_of_mul_eq_one_right hab
              rw [e]
              exact inv_mem (mul_mem (pow_mem (le_sSup hA₀ ht₀A) _)
                (pow_mem (le_sSup hA₁ ht₁A) _))
            have hcop : Nat.Coprime (orderOf y) d.val := by
              rw [hyo]
              exact Nat.coprime_of_lt_prime (fun h => hd0 ((ZMod.val_eq_zero d).mp h))
                (ZMod.val_lt d) hp.out
            have hord : orderOf (y ^ d.val) = orderOf y := Nat.Coprime.orderOf_pow hcop
            have hle : Subgroup.zpowers (y ^ d.val) ≤ Subgroup.zpowers y :=
              Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers y _)
            have heq : Subgroup.zpowers (y ^ d.val) = Subgroup.zpowers y :=
              Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
            have hy : y ∈ Subgroup.zpowers (y ^ d.val) := heq ▸ Subgroup.mem_zpowers y
            exact (Subgroup.zpowers_le.mpr hyd) hy
          rw [hd, ZMod.val_zero, pow_zero, mul_one] at hab
          have ha : a = 0 := by
            apply hzero
            apply ht₀j
            rw [eq_inv_of_mul_eq_one_left hab]
            exact inv_mem (pow_mem (hA₁B₀ ht₁A) _)
          rw [ha, ZMod.val_zero, pow_zero, one_mul] at hab
          have hb : b = 0 := by
            apply hzero
            have := orderOf_dvd_of_pow_eq_one hab
            rwa [ht₁o] at this
          exact ⟨ha, hb, hd⟩)
      omega
  ·
    push Not at h1
    refine ⟨A₀, hA₀, ?_⟩
    set B₀ := sSup (𝓛 \ {A₀}) with hB₀
    have hB₀K : B₀ ≤ Subgroup.centralizer (K : Set Ω) := sSup_le fun D hD x hx =>
      Subgroup.mem_centralizer_iff.mpr fun k hk => by
        have := h1 D hD.1 hD.2
        simp only [hmv, not_exists, not_and, not_not] at this
        exact (this x hx k hk).symm
    have hB₀A : B₀ ≤ Subgroup.centralizer (A₀ : Set Ω) := sSup_diff_le_centralizer hcomm hA₀
    have hAN : A₀ ≤ Subgroup.normalizer (B₀ : Set Ω) :=
      (Subgroup.le_centralizer_iff.mp hB₀A).trans (Subgroup.centralizer_le_normalizer _)
    have hdec : ∀ k ∈ K, ∃ x ∈ A₀, ∃ b ∈ B₀, x * b = k := by
      intro k hk
      have h1 : k ∈ ((A₀ ⊔ B₀ : Subgroup Ω) : Set Ω) := by
        rw [← sSup_eq_sup_sSup_diff hA₀]
        exact hKL hk
      rw [Subgroup.coe_mul_of_left_le_normalizer_right A₀ B₀ hAN] at h1
      obtain ⟨x, hx, b, hb, hxb⟩ := h1
      exact ⟨x, hx, b, hb, hxb⟩
    rw [← hKp, Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hdec k₁ hk₁
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hdec k₂ hk₂
    have c1 : Commute b₁ a₂ := (Subgroup.mem_centralizer_iff.mp (hB₀A hb₁) a₂ ha₂).symm
    have c3 : Commute b₂ a₁ := (Subgroup.mem_centralizer_iff.mp (hB₀A hb₂) a₁ ha₁).symm
    have c2 : Commute b₁ b₂ := by
      have h1 : Commute b₂ (a₁ * b₁) :=
        (Subgroup.mem_centralizer_iff.mp (hB₀K hb₂) _ hk₁).symm
      have h2 : Commute b₂ a₁⁻¹ := c3.inv_right
      have h3 : Commute b₂ (a₁⁻¹ * (a₁ * b₁)) := h2.mul_right h1
      rw [inv_mul_cancel_left] at h3
      exact h3.symm
    have e : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹
          = a₁ * (b₁ * a₂) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
        _ = a₁ * (a₂ * b₁) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [c1.eq]
        _ = a₁ * a₂ * (b₁ * b₂ * b₁⁻¹) * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
        _ = a₁ * a₂ * b₂ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [c2.eq, mul_inv_cancel_right]
        _ = a₁ * a₂ * (b₂ * a₁⁻¹ * b₂⁻¹) * a₂⁻¹ := by group
        _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by rw [(c3.inv_right).eq, mul_inv_cancel_right]
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha₁ ha₂) (inv_mem ha₁)) (inv_mem ha₂)

end Rank

end L4312

end CFSG.Quasithin.H13.Ch4
