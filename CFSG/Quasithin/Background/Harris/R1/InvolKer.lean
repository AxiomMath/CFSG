module

public import CFSG.Quasithin.Background.Harris.R1.PermHom

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7 CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem act_eq_one_mem_vBeta (C : FamCtx K1 L2 S Zs Ω) [Fintype Ω]
    (hΩ : Fintype.card Ω = 5) (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) {k : ↥K1} (hk : C.D.act k = 1) :
    (k : G) ∈ vBeta K1 L2 S Zs := by
  obtain ⟨e1⟩ := hL24
  obtain ⟨e2⟩ := F112J2.nonempty_psl_four_equiv_alt5
  let e : OTwoQuot K1 ≃* A5 := e1.trans e2
  have : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup (OTwoQuot K1) := e.isSimpleGroup
  have hmem : ∀ x : ↥K1, x ∈ CFSG.Open.pCore 2 ↥K1 → (x : G) ∈ vBeta K1 L2 S Zs := by
    intro x hx
    rw [← hQK]
    exact Subgroup.mem_map_of_mem K1.subtype hx
  let q : ↥K1 →* OTwoQuot K1 := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1)
  let N : Subgroup ↥K1 := (C.D.act).ker
  have hNn : (N.map q).Normal :=
    Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map q) with h | h
  · have : q k = 1 := by
      have hkN : q k ∈ N.map q := Subgroup.mem_map_of_mem q (MonoidHom.mem_ker.2 hk)
      rw [h, Subgroup.mem_bot] at hkN
      exact hkN
    exact hmem k ((QuotientGroup.eq_one_iff _).1 this)
  · exfalso
    obtain ⟨ω, hω⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Ω) C.D.pt
    obtain ⟨x, hx⟩ := C.D.trans ω
    have hx1 : C.D.act x = 1 := by
      have hqx : q x ∈ N.map q := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hqn⟩ := Subgroup.mem_map.1 hqx
      have hn1 : C.D.act n = 1 := MonoidHom.mem_ker.1 hn
      have hy : n⁻¹ * x ∈ CFSG.Open.pCore 2 ↥K1 := by
        apply (QuotientGroup.eq_one_iff _).1
        show q (n⁻¹ * x) = 1
        rw [map_mul, map_inv, hqn, inv_mul_cancel]
      have hyW := hmem _ hy
      have hyM : ((n⁻¹ * x : ↥K1) : G) ∈ C.kerM := C.vBeta_le_kerM hyW
      have hperm : permHom C ⟨((n⁻¹ * x : ↥K1) : G), Subgroup.mem_sup_left (n⁻¹ * x).2⟩ = 1 :=
        (permHom_eq_one_iff C _).2 hyM
      rw [permHom_K1] at hperm
      have : C.D.act x = C.D.act n * C.D.act (n⁻¹ * x) := by
        rw [← map_mul]; simp
      rw [this, hperm, mul_one, hn1]
    rw [hx1] at hx
    exact hω hx.symm

theorem exists_pow_mem_K1 (C : FamCtx K1 L2 S Zs Ω) {x : G} (hx : x ∈ K1 ⊔ S) :
    ∃ n : ℕ, x ^ (2 ^ n) ∈ K1 := by
  obtain ⟨k, hk, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes C.hSK).1 hx
  obtain ⟨n, hn⟩ := C.h.hyp.h1.pgroup ⟨s, hs⟩
  have hs' : s ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have key : ∀ m : ℕ, ∃ k' ∈ K1, (k * s) ^ m = k' * s ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, K1.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨k', hk', e⟩ := ih
      refine ⟨k' * (s ^ m * k * (s ^ m)⁻¹), K1.mul_mem hk' ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp
          (C.hSK (S.pow_mem hs m)) k).mp hk
        exact this
      · rw [pow_succ, e]
        group
  obtain ⟨k', hk', e⟩ := key (2 ^ n)
  exact ⟨n, by rw [e, hs', mul_one]; exact hk'⟩

theorem kerM_le_vBeta (C : FamCtx K1 L2 S Zs Ω) [Fintype Ω]
    (hΩ : Fintype.card Ω = 5) (hL24 : IsL2Quot 2 (OTwoQuot K1))
    (hQ : pCoreOf 2 (K1 ⊔ S) = vBeta K1 L2 S Zs) (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) :
    C.kerM ≤ vBeta K1 L2 S Zs := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 (vBeta K1 L2 S Zs) := by
    rw [← hQK]; exact pCoreOf_isPGroup 2 K1
  have hMp : IsPGroup 2 C.kerM := by
    intro m
    have hmH : (m : G) ∈ K1 ⊔ S := C.kerM_le_sup m.2
    obtain ⟨n, hn⟩ := exists_pow_mem_K1 C hmH
    have hmn : (m : G) ^ (2 ^ n) ∈ C.kerM := C.kerM.pow_mem m.2 _
    have hact : C.D.act ⟨(m : G) ^ (2 ^ n), hn⟩ = 1 := by
      rw [← permHom_K1]
      exact (permHom_eq_one_iff C _).2 hmn
    have hW := act_eq_one_mem_vBeta C hΩ hL24 hQK hact
    obtain ⟨r, hr⟩ := hWp ⟨_, hW⟩
    refine ⟨n + r, ?_⟩
    have h1 : ((m : G) ^ (2 ^ n)) ^ (2 ^ r) = 1 := congrArg Subtype.val hr
    apply Subtype.ext
    show (m : G) ^ (2 ^ (n + r)) = 1
    rw [pow_add, pow_mul]
    exact h1
  have := le_pCoreOf_of_le_normalizer 2 C.kerM_le_sup C.sup_le_normalizer_kerM hMp
  rwa [hQ] at this

end CFSG.Quasithin.Background.Harris.R1
