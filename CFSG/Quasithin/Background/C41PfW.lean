module

public import CFSG.Quasithin.Background.C41PfV
public import CFSG.Quasithin.Background.C41PfE

public section

namespace CFSG.Quasithin.C41Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isPSL_two_two_of_equiv_sl2 {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : X ≃* SpecialLinearGroup (Fin 2) F) : IsPSL 2 2 n X := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hF,
    ⟨e.trans sl2EquivStatedProj⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

theorem c47_core {H R M L V K : Subgroup G} (hP : C41Post H R M L V K) {F : Type} [Field F]
    [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥K) (hMKmax : IsMaxParabolic2 K (M ⊓ K)) :
    ∃ (g : SpecialLinearGroup (Fin 3) F) (j : Fin 2),
      (∀ m : ↥K, (m : G) ∈ conjClosure L M → g⁻¹ * α m * g ∈ perfectCore (Q3 F j)) ∧
      (∀ x ∈ perfectCore (Q3 F j), ∃ m : ↥K, (m : G) ∈ conjClosure L M ∧ α m = g * x * g⁻¹) ∧
      (∀ m : ↥K, (m : G) ∈ conjClosure L M → g⁻¹ * α m * g ∈ SL3N.rad3 j →
        (m : G) ∈ pCoreOf 2 (conjClosure L M)) ∧
      (∀ x : ↥K, (x : G) ∈ M → ∀ r ∈ SL3N.rad3 j, ∃ r' ∈ SL3N.rad3 j,
        (α x)⁻¹ * (g * r * g⁻¹) * α x = g * r' * g⁻¹) ∧
      IsPSL 2 2 n (ModO2 (conjClosure L M)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.hyp
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := n) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four h4
  have hFk : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨n, hF'⟩
  set M0 := conjClosure L M with hM0
  have hM0K : M0 ≤ K := hP.le
  have hM0M : M0 ≤ M := C2Nine.conjClosure_le_M h
  have hM0perf : ⁅M0, M0⁆ = M0 := C2Nine.perfect_conjClosure_of_hyp h
  have hMM0 : M ≤ Subgroup.normalizer (M0 : Set G) := le_normalizer_conjClosure L M
  have hpO : pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := C2A3Orbits.pCoreOf_eq_map_pCore K
  have hker : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
    intro k
    rw [← MonoidHom.mem_ker, hαk, hpO]
    constructor
    · intro hk
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k', hk', he⟩
      rwa [show k = k' from Subtype.ext he.symm]
  have hO2MK : pCoreOf 2 K ≤ M ⊓ K := by
    obtain ⟨-, S, hS, hSP⟩ := hMKmax.1
    have hOS : pCoreOf 2 K ≤ S := CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
    exact fun x hx => hSP ⟨hS.1 (hOS hx), Subgroup.le_normalizer (hOS hx)⟩
  set P' : Subgroup (SpecialLinearGroup (Fin 3) F) := ((M ⊓ K).subgroupOf K).map α with hP'
  have hP'par : IsParabolic2 ⊤ P' := isParabolic2_map_top α hαs hαk hMKmax.1
  have hP'ne : P' ≠ ⊤ := by
    intro htop
    apply hMKmax.2.1
    refine le_antisymm inf_le_right fun k hk => ?_
    have hmem : α ⟨k, hk⟩ ∈ P' := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, he⟩ := hmem
    have h3 : α (m⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have h4 := hO2MK ((hker _).mp h3)
    have e : k = (m : G) * ((m⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
    rw [e]
    exact (M ⊓ K).mul_mem hm h4
  set X : Subgroup (SpecialLinearGroup (Fin 3) F) := (M0.subgroupOf K).map α with hX
  have hXP : X ≤ P' := Subgroup.map_mono fun x hx => ⟨hM0M hx, hM0K hx⟩
  have hXperf : ⁅X, X⁆ = X := by
    rw [hX, ← Subgroup.map_commutator, commutator_subgroupOf hM0K hM0K, hM0perf]
  have hM0O : X = ⊥ → M0 ≤ pCoreOf 2 K := by
    intro hb m hm
    refine (hker ⟨m, hM0K hm⟩).mp ?_
    have : α ⟨m, hM0K hm⟩ ∈ X := ⟨⟨m, hM0K hm⟩, hm, rfl⟩
    rw [hb, Subgroup.mem_bot] at this
    exact this
  have hXne : X ≠ ⊥ := by
    intro hb
    apply hP.not_commutator_le
    rw [Subgroup.commutator_le]
    intro m hm k hk
    have hmO := hM0O hb hm
    have h3 : k * m⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) _).mp
        ((pCoreOf 2 K).inv_mem hmO)
    have e : ⁅m, k⁆ = m * (k * m⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 K).mul_mem hmO h3
  have hXnorm : ∀ p ∈ P', ∀ x ∈ X, p * x * p⁻¹ ∈ X := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m₀, hm₀, rfl⟩
    refine ⟨m * m₀ * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMM0 hm.1) m₀).mp hm₀
  have hXcore : X ≤ perfectCore P' := le_perfectCore_of_perfect hXP hXperf
  obtain ⟨g, j, hgj⟩ := (SL3N.sl3_perfectCore_parabolic_conj hFk hP'par hP'ne).resolve_left
    fun hb => hXne (le_bot_iff.mp (hb ▸ hXcore))
  set N := perfectCore (Q3 F j) with hN
  have hconj : ∀ y : SpecialLinearGroup (Fin 3) F, y ∈ perfectCore P' ↔ g⁻¹ * y * g ∈ N := by
    intro y
    rw [hgj]
    constructor
    · rintro ⟨n, hn, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hn
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  set Y : Subgroup (SpecialLinearGroup (Fin 3) F) := X.map (MulAut.conj g⁻¹).toMonoidHom with hY
  have hYN : Y ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hconj x).mp (hXcore hx)
    simpa [MulAut.conj_apply] using this
  have hYnorm : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
    rintro n hn _ ⟨x, hx, rfl⟩
    have hgn : g * n * g⁻¹ ∈ perfectCore P' := (hconj _).mpr (by simpa [mul_assoc] using hn)
    have h3 := hXnorm _ (perfectCore_le _ hgn) x hx
    refine ⟨_, h3, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hYperf : ⁅Y, Y⁆ = Y := by rw [hY, ← Subgroup.map_commutator, hXperf]
  have hYne : Y ≠ ⊥ := by
    intro hb
    apply hXne
    have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hb
    rw [hY, Subgroup.map_map, Subgroup.map_bot] at this
    have e : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun y => by simp [MulAut.conj_apply, mul_assoc]
    rwa [e, Subgroup.map_id] at this
  have hYeq : Y = N := SL3N.eq_perfectCore_of_normal hK4 hFk hYN hYnorm hYperf hYne
  have hXmem : ∀ n ∈ N, ∃ m : ↥K, (m : G) ∈ M0 ∧ α m = g * n * g⁻¹ := by
    intro n hn
    rw [← hYeq] at hn
    obtain ⟨x, hx, hxe⟩ := hn
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨m, hm, ?_⟩
    rw [← hxe]
    simp [mul_assoc]
  have hXsub : ∀ m : ↥K, (m : G) ∈ M0 → g⁻¹ * α m * g ∈ N := by
    intro m hm
    have : (MulAut.conj g⁻¹).toMonoidHom (α m) ∈ Y := ⟨α m, ⟨m, hm, rfl⟩, rfl⟩
    rw [hYeq] at this
    simpa [MulAut.conj_apply] using this
  set T : Subgroup G :=
    ((((SL3N.rad3 j).map (MulAut.conj g).toMonoidHom).comap α).map K.subtype) ⊓ M0 with hT
  have hT2 : IsPGroup 2 ↥T := by
    rintro ⟨t, ⟨⟨k, ⟨r, hr, hre⟩, rfl⟩, -⟩⟩
    obtain ⟨a, ha⟩ := SL3N.rad3_isPGroup hFk j ⟨r, hr⟩
    have hra : r ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have h3 : α (k ^ 2 ^ a) = 1 := by
      rw [map_pow, ← hre]
      show ((MulAut.conj g) r) ^ 2 ^ a = 1
      rw [MulAut.conj_apply, conj_pow, hra, mul_one, mul_inv_cancel]
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨_, (hker _).mp h3⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((k : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_subtype]
    rw [pow_add, pow_mul]
    exact hb'
  have hTnorm : M0 ≤ Subgroup.normalizer (T : Set G) := by
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    obtain ⟨⟨k, ⟨r, hr, hre⟩, rfl⟩, htM⟩ := ht
    refine ⟨⟨⟨m, hM0K hm⟩ * k * ⟨m, hM0K hm⟩⁻¹, ?_, rfl⟩, ?_⟩
    · have hn := hXsub ⟨m, hM0K hm⟩ hm
      refine ⟨(g⁻¹ * α ⟨m, hM0K hm⟩ * g) * r * (g⁻¹ * α ⟨m, hM0K hm⟩ * g)⁻¹,
        SL3N.conj_mem_rad3 hn hr, ?_⟩
      simp only [map_mul, map_inv, ← hre, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · exact M0.mul_mem (M0.mul_mem hm htM) (M0.inv_mem hm)
  have hTO : T ≤ pCoreOf 2 M0 := le_pCoreOf_of_le_normalizer 2 inf_le_right hTnorm hT2
  have hXN : ∀ x ∈ X, g⁻¹ * x * g ∈ N := by
    rintro _ ⟨m, hm, rfl⟩
    exact hXsub m hm
  have hNX : ∀ n ∈ N, g * n * g⁻¹ ∈ X := by
    intro n hn
    obtain ⟨m, hm, hme⟩ := hXmem n hn
    exact ⟨m, hm, hme⟩
  have hqN : ∀ p ∈ P', ∀ n ∈ N, (g⁻¹ * p * g) * n * (g⁻¹ * p * g)⁻¹ ∈ N := by
    intro p hp n hn
    have h3 := hXN _ (hXnorm p hp _ (hNX n hn))
    convert h3 using 1
    group
  have hPrad : ∀ p ∈ P', ∀ r ∈ SL3N.rad3 (K := F) j, ∃ r' ∈ SL3N.rad3 (K := F) j,
      p⁻¹ * (g * r * g⁻¹) * p = g * r' * g⁻¹ := by
    intro p hp r hr
    set q := g⁻¹ * p⁻¹ * g with hq
    have hp' : p⁻¹ ∈ P' := P'.inv_mem hp
    set Rq : Subgroup (SpecialLinearGroup (Fin 3) F) :=
      (SL3N.rad3 (K := F) j).map (MulAut.conj q).toMonoidHom with hRq
    have hRqN : Rq ≤ N := by
      rintro _ ⟨r₀, hr₀, rfl⟩
      exact hqN p⁻¹ hp' r₀ (SL3N.rad3_le j hr₀)
    have hRqn : ∀ n ∈ N, ∀ y ∈ Rq, n * y * n⁻¹ ∈ Rq := by
      rintro n hn _ ⟨r₀, hr₀, rfl⟩
      have hn' : q⁻¹ * n * q⁻¹⁻¹ ∈ N := by
        have := hqN p hp n hn
        convert this using 1
        simp only [hq]
        group
      refine ⟨(q⁻¹ * n * q⁻¹⁻¹) * r₀ * (q⁻¹ * n * q⁻¹⁻¹)⁻¹, SL3N.conj_mem_rad3 hn' hr₀, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hRq2 : IsPGroup 2 ↥Rq := (SL3N.rad3_isPGroup hFk j).map _
    have hle := SL3N.le_rad3_of_isPGroup hK4 hRqN hRqn hRq2
    refine ⟨q * r * q⁻¹, hle ⟨r, hr, rfl⟩, ?_⟩
    simp only [hq]
    group
  have hψN : ∀ m : ↥M0, (MulAut.conj g⁻¹).toMonoidHom (α (Subgroup.inclusion hM0K m)) ∈ N :=
    fun m => by simpa [MulAut.conj_apply] using hXsub (Subgroup.inclusion hM0K m) m.2
  set ψ : ↥M0 →* ↥N :=
    (((MulAut.conj g⁻¹).toMonoidHom.comp α).comp (Subgroup.inclusion hM0K)).codRestrict N hψN
    with hψ
  have hψv : ∀ m : ↥M0,
      ((ψ m : ↥N) : SpecialLinearGroup (Fin 3) F) = g⁻¹ * α (Subgroup.inclusion hM0K m) * g := by
    intro m
    simp [hψ]
  have hψs : Function.Surjective ψ := by
    rintro ⟨n, hn⟩
    obtain ⟨m, hm, hme⟩ := hXmem n hn
    refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
    rw [hψv]
    show g⁻¹ * α m * g = n
    rw [hme]
    group
  set φ : ↥M0 →* SpecialLinearGroup (Fin 2) F := (blk3 j).comp ψ with hφ
  have hφs : Function.Surjective φ := fun A => by
    obtain ⟨n, hn⟩ := blk3_surjective hK4 j A
    obtain ⟨m, rfl⟩ := hψs n
    exact ⟨m, hn⟩
  have hpO0 : pCoreOf 2 M0 = (CFSG.pCore 2 ↥M0).map M0.subtype :=
    C2A3Orbits.pCoreOf_eq_map_pCore M0
  have hφk : φ.ker = CFSG.pCore 2 ↥M0 := by
    apply le_antisymm
    · intro m hm
      rw [MonoidHom.mem_ker] at hm
      have hr : ((ψ m : ↥N) : SpecialLinearGroup (Fin 3) F) ∈ SL3N.rad3 (K := F) j :=
        SL3N.mem_rad3 (ψ m).2 hm
      have hmT : (m : G) ∈ T := by
        refine ⟨⟨Subgroup.inclusion hM0K m, ⟨_, hr, ?_⟩, rfl⟩, m.2⟩
        rw [hψv]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have hmO := hTO hmT
      rw [hpO0] at hmO
      obtain ⟨m', hm', he⟩ := hmO
      rwa [← show m' = m from Subtype.ext he]
    · intro m hm
      set S : Subgroup (SpecialLinearGroup (Fin 3) F) :=
        ((CFSG.pCore 2 ↥M0).map ψ).map N.subtype with hS
      have hSN : S ≤ N := by
        rintro _ ⟨n, -, rfl⟩
        exact n.2
      have hSn : ∀ n ∈ N, ∀ y ∈ S, n * y * n⁻¹ ∈ S := by
        intro n hn y hy
        obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hy
        obtain ⟨m₁, hm₁⟩ := hψs ⟨n, hn⟩
        refine ⟨ψ (m₁ * q * m₁⁻¹), ⟨m₁ * q * m₁⁻¹, CFSG.pCore_normal.conj_mem q hq m₁, rfl⟩, ?_⟩
        simp [map_mul, map_inv, hm₁]
      have hS2 : IsPGroup 2 ↥S := (CFSG.pCore_isPGroup.map ψ).map _
      have hmr : ((ψ m : ↥N) : SpecialLinearGroup (Fin 3) F) ∈ SL3N.rad3 (K := F) j :=
        SL3N.le_rad3_of_isPGroup hK4 hSN hSn hS2 ⟨ψ m, ⟨m, hm, rfl⟩, rfl⟩
      obtain ⟨hg', hb1⟩ := SL3N.blk3_eq_one_of_mem_rad3 hmr
      rw [MonoidHom.mem_ker]
      exact hb1
  have hpsl : IsPSL 2 2 n (ModO2 M0) :=
    isPSL_two_two_of_equiv_sl2 hn hF'
      ((QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφs))
  refine ⟨g, j, hXsub, hXmem, fun m hm hr => hTO ⟨⟨m, ⟨_, hr, ?_⟩, rfl⟩, hm⟩,
    fun x hx r hr => hPrad (α x) ⟨x, ⟨hx, x.2⟩, rfl⟩ r hr, hpsl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end CFSG.Quasithin.C41Pf
