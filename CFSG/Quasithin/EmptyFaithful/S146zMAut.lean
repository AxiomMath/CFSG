module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.SectionRank.Ccomm

theorem card_GL_two_three : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [card_GL_zmod (p := 3) 2]
  simp [Fin.prod_univ_two]

theorem card_GL_two_five : Nat.card (GL (Fin 2) (ZMod 5)) = 480 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [card_GL_zmod (p := 5) 2]
  simp [Fin.prod_univ_two]

theorem prime_dvd_card_aut_of_pRank_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (hr : CFSG.Open.pRank p (⊤ : Subgroup P) ≤ 2) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card (MulAut P)) : q = p ∨ q ∣ Nat.card (GL (Fin 2) (ZMod p)) := by
  obtain ⟨φ, hφ⟩ := exists_hom_ker_eq_pCore_aut hp2 hP hr
  have hcard : Nat.card (MulAut P) = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (r := p) (G := MulAut P)).exists_card_eq
  have hrange : Nat.card φ.range ∣ Nat.card (GL (Fin 2) (ZMod p)) :=
    Subgroup.card_subgroup_dvd_card φ.range
  rw [hcard, hφ, hk] at hdvd
  rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
  · exact Or.inr (h.trans hrange)
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Fact.out).1 (hq.dvd_of_dvd_pow h))

variable {D : Type*} [Group D] [Finite D]

theorem exists_pow_mem_centralizer_pCore {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Ĝ : Type*}
    [Group Ĝ] [Finite Ĝ] (φ : Ĝ →* D) (hφ : Function.Surjective φ)
    (hr : CFSG.Open.pRank p (⊤ : Subgroup Ĝ) ≤ 2) :
    ∃ k : ℕ, 0 < k ∧
      (∀ q : ℕ, q.Prime → q ∣ k → q = p ∨ q ∣ Nat.card (GL (Fin 2) (ZMod p))) ∧
      ∀ g : D, g ^ k ∈ Subgroup.centralizer (CFSG.Open.pCore p D : Set D) := by
  have hOn : (CFSG.Open.pCore p D).Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hNn : ((CFSG.Open.pCore p D).comap φ).Normal := hOn.comap φ
  obtain ⟨P⟩ : Nonempty (Sylow p ↥((CFSG.Open.pCore p D).comap φ)) := inferInstance
  set N := (CFSG.Open.pCore p D).comap φ
  set P' : Subgroup Ĝ := (P : Subgroup N).map N.subtype
  let ψ : ↥N →* ↥(CFSG.Open.pCore p D) :=
    (φ.comp N.subtype).codRestrict (CFSG.Open.pCore p D) (fun x => x.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have himg : ∀ y ∈ CFSG.Open.pCore p D, ∃ x ∈ P', φ x = y := by
    intro y hy
    have htop : IsPGroup p (⊤ : Subgroup ↥(CFSG.Open.pCore p D)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup p).of_equiv Subgroup.topEquiv.symm
    have hmax := (P.mapSurjective hψ).is_maximal' htop le_top
    have hmem : (⟨y, hy⟩ : ↥(CFSG.Open.pCore p D)) ∈ ((P.mapSurjective hψ : Subgroup _)) := by
      rw [← hmax]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨x, hx, hxy⟩ := hmem
    exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩
  have hsurj : ∀ g : D, ∃ n ∈ Subgroup.normalizer (P' : Set Ĝ), φ n = g := by
    intro g
    obtain ⟨x, rfl⟩ := hφ g
    have hx : x ∈ ((Subgroup.normalizer (P' : Set Ĝ) ⊔ N : Subgroup Ĝ) : Set Ĝ) := by
      rw [Sylow.normalizer_sup_eq_top P]
      exact Subgroup.mem_top x
    rw [Subgroup.mul_normal] at hx
    obtain ⟨n, hn, m, hm, rfl⟩ := hx
    obtain ⟨y, hy, hym⟩ := himg (φ m) hm
    refine ⟨n * y, Subgroup.mul_mem _ hn (Subgroup.le_normalizer hy), ?_⟩
    rw [map_mul, map_mul, hym]
  have hPp : IsPGroup p ↥P' := P.isPGroup'.map N.subtype
  have hrP : CFSG.Open.pRank p (⊤ : Subgroup ↥P') ≤ 2 := by
    rw [pRank_top_subtype]
    exact (CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt le_top).trans hr
  refine ⟨Nat.card (MulAut ↥P'), Nat.card_pos,
    fun q hq hqd => prime_dvd_card_aut_of_pRank_two hp2 hPp hrP hq hqd, fun g => ?_⟩
  obtain ⟨n, hn, rfl⟩ := hsurj g
  have h1 : P'.normalizerMonoidHom (⟨n, hn⟩ ^ Nat.card (MulAut ↥P')) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := himg y hy
  have h2 := congrArg (fun a : MulAut ↥P' => ((a ⟨x, hx⟩ : ↥P') : Ĝ)) h1
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply,
    SubmonoidClass.mk_pow] at h2
  have h3 : φ (n ^ Nat.card (MulAut ↥P') * x * (n ^ Nat.card (MulAut ↥P'))⁻¹) = φ x := by
    rw [h2]
  rw [map_mul, map_mul, map_inv, map_pow] at h3
  calc φ x * φ n ^ Nat.card (MulAut ↥P') =
        φ n ^ Nat.card (MulAut ↥P') * φ x * (φ n ^ Nat.card (MulAut ↥P'))⁻¹ *
          φ n ^ Nat.card (MulAut ↥P') := by rw [h3]
    _ = φ n ^ Nat.card (MulAut ↥P') * φ x := by group

end CFSG.Quasithin
