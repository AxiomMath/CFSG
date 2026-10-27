module

public import CFSG.Quasithin.Vol2.GoldschmidtE217B1A6Aut
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique E217R3

namespace E217R4

theorem eq_of_le_of_card_24 {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hcard : Nat.card K = 360) {P₁ Q : Subgroup K} (hP : Nat.card P₁ = 24) (hPQ : P₁ ≤ Q)
    (hQ : Q ≠ ⊤) : Q = P₁ := by
  have hi : P₁.index = 15 := by
    have h := Subgroup.index_mul_card P₁
    rw [hP, hcard] at h
    omega
  have hdvd : Q.index ∣ 15 := hi ▸ Subgroup.index_dvd_of_le hPQ
  have hQ1 : Q.index ≠ 1 := fun h => hQ (Subgroup.index_eq_one.1 h)
  have hcore : Q.normalCore = ⊥ := by
    rcases Q.normalCore_normal.eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (top_le_iff.1 (h ▸ Q.normalCore_le)) hQ
  have hfac : 360 ≤ Nat.factorial Q.index := by
    have := Subgroup.index_normalCore_le_factorial_index Q
    rwa [hcore, Subgroup.index_bot, hcard] at this
  have hn : ∀ n : ℕ, n < 16 → n ∣ 15 → n ≠ 1 → 360 ≤ Nat.factorial n → n = 15 := by decide
  have h15 : Q.index = 15 :=
    hn _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hdvd)) hdvd hQ1 hfac
  exact (Subgroup.eq_of_index_dvd_index hPQ (by rw [hi, h15])).symm

theorem a6_false
    {Y : Type} [Group Y] [Finite Y] {K T : Subgroup Y} (hKn : K.Normal)
    (hCK : Subgroup.centralizer (K : Set Y) = ⊥) (hT : IsSylowTwoOf T ⊤)
    (hK : Nonempty (↥K ≃* alternatingGroup (Fin 6))) {v : Y} (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hvT : ∀ t ∈ T, t * v = v * t) (hodd : OddCube v)
    (hdiag : ∀ P : Subgroup Y, IsMaxParabolic2 K P →
      K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) ≤ P →
      ¬ T ≤ Subgroup.normalizer (P : Set Y)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hK
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥K := e.isSimpleGroup
  have hcard : Nat.card ↥K = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hTi : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    change ¬ 2 ∣ T.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  obtain ⟨P, hP⟩ := exists_sylow_eq_subgroupOf_of_normal (hT.2.1.toSylow hTi) K
  have hPT : (P : Subgroup ↥K) = T.subgroupOf K := by
    rw [hP]
    rfl
  have hQ : IsPGroup 2 (T.subgroupOf K) := hPT ▸ P.isPGroup'
  have hQi : ¬ 2 ∣ (T.subgroupOf K).index := hPT ▸ P.not_dvd_index
  obtain ⟨P₁, hSP₁, hP₁card, hNS, htab, hnoodd⟩ := a6_table ⟨e⟩ (T.subgroupOf K) hQ hQi
  have hα2 : (MulAut.conjNormal v : MulAut ↥K) ^ 2 = 1 := by
    rw [← map_pow, pow_two, hv2, map_one]
  have hαS : ∀ s ∈ T.subgroupOf K, (MulAut.conjNormal v : MulAut ↥K) s = s := fun s hs => by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have := hvT (s : Y) hs
    calc v * (s : Y) * v⁻¹ = (s : Y) * v * v⁻¹ := by rw [← this]
      _ = s := by group
  rcases htab _ hα2 hαS with ⟨z, hzS, hz2, hz⟩ | hout
  ·
    have hvz : v = (z : Y) := by
      have hc : (z : Y)⁻¹ * v ∈ Subgroup.centralizer (K : Set Y) := fun k hk => by
        have := congrArg (fun φ : MulAut ↥K => (φ ⟨k, hk⟩ : Y)) hz
        simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at this
        show k * ((z : Y)⁻¹ * v) = ((z : Y)⁻¹ * v) * k
        calc k * ((z : Y)⁻¹ * v) = (z : Y)⁻¹ * ((z : Y) * k * (z : Y)⁻¹) * v := by group
          _ = (z : Y)⁻¹ * (v * k * v⁻¹) * v := by rw [this]; rfl
          _ = ((z : Y)⁻¹ * v) * k := by group
      rw [hCK, Subgroup.mem_bot] at hc
      exact (inv_mul_eq_one.1 hc).symm
    have hz1 : z ≠ 1 := fun h => hv1 (by rw [hvz, h]; rfl)
    have hO : OddCube z := by
      have := OddCube.of_subgroup (K := K) (hvz ▸ z.2) fun g _ n hn h1 => hodd g n hn h1
      have hzz : (⟨v, hvz ▸ z.2⟩ : ↥K) = z := Subtype.ext hvz
      rwa [hzz] at this
    exact hnoodd z hz2 hz1 hO
  ·
    set P₁' : Subgroup Y := P₁.map K.subtype with hP₁'
    have hBor : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) ≤ P₁' := by
      rintro g ⟨hgK, hgN⟩
      have hg : (⟨g, hgK⟩ : ↥K) ∈ T.subgroupOf K := by
        refine hNS ⟨g, hgK⟩ fun s hs => ?_
        have hsK : (s : Y) ∈ T ⊓ K := ⟨hs, s.2⟩
        exact ((Subgroup.mem_normalizer_iff.1 hgN _).1 hsK).1
      exact ⟨_, hSP₁ hg, rfl⟩
    have hpar : IsParabolic2 K P₁' := by
      refine ⟨Subgroup.map_subtype_le P₁, T ⊓ K, ⟨inf_le_right, hT.2.1.to_inf_left, ?_⟩, hBor⟩
      have : (T ⊓ K).subgroupOf K = T.subgroupOf K := by
        ext x
        exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
      rw [this]
      exact hQi
    have hmax : IsMaxParabolic2 K P₁' := by
      refine ⟨hpar, ?_, fun Q hQpar hQK hle => ?_⟩
      · intro h
        have : Nat.card ↥P₁' = Nat.card ↥K := by rw [h]
        rw [hP₁', Subgroup.card_map_of_injective K.subtype_injective, hP₁card, hcard] at this
        omega
      · have hQK' : Q ≤ K := hQpar.1
        have hPQ' : P₁ ≤ Q.subgroupOf K := fun p hp => hle ⟨p, hp, rfl⟩
        have hQ'top : Q.subgroupOf K ≠ ⊤ := fun h => hQK (le_antisymm hQK' fun x hx =>
          (show (⟨x, hx⟩ : ↥K) ∈ Q.subgroupOf K by rw [h]; exact Subgroup.mem_top _))
        have hQ'eq := eq_of_le_of_card_24 hcard hP₁card hPQ' hQ'top
        refine le_antisymm (fun x hx => ?_) hle
        have hxK := hQK' hx
        have : (⟨x, hxK⟩ : ↥K) ∈ P₁ := by rw [← hQ'eq]; exact hx
        exact ⟨_, this, rfl⟩
    have hTN : T ≤ Subgroup.normalizer (P₁' : Set Y) := by
      have key : ∀ t ∈ T, ∀ y ∈ P₁', t * y * t⁻¹ ∈ P₁' := by
        intro t ht y hy
        obtain ⟨p, hp, rfl⟩ := hy
        have hβS : ∀ s ∈ T.subgroupOf K, (MulAut.conjNormal t : MulAut ↥K) s ∈ T.subgroupOf K :=
          fun s hs => by
            show t * (s : Y) * t⁻¹ ∈ T
            exact T.mul_mem (T.mul_mem ht hs) (T.inv_mem ht)
        have hcomm : (MulAut.conjNormal t : MulAut ↥K) * MulAut.conjNormal v =
            MulAut.conjNormal v * MulAut.conjNormal t := by
          rw [← map_mul, ← map_mul, hvT t ht]
        exact ⟨_, hout _ hβS hcomm p hp, MulAut.conjNormal_apply t p⟩
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨key t ht y, fun h => ?_⟩
      have := key t⁻¹ (T.inv_mem ht) _ h
      rwa [show t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y by group] at this
    exact hdiag P₁' hmax hBor hTN

end E217R4

end CFSG.Quasithin
