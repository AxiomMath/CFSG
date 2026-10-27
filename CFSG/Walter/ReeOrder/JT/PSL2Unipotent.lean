module

public import CFSG.Walter.ReeOrder.JT.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSylowNormalizer

public section

namespace CFSG.Walter.JT

open scoped MatrixGroups Pointwise

section PSL2

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]

theorem psl2_card_sylow_p (hK : Nat.card K = p ^ f) (hp : p ≠ 2) (hf : f ≠ 0)
    (P : Sylow p PSL(2, K)) : Nat.card P = p ^ f := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hKo : GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, Fact.out, hpodd, Nat.one_le_iff_ne_zero.mpr hf, hK⟩
  rw [Sylow.card_eq_multiplicity, GorensteinWalter.psl2_card_formula K hKo, hK]
  congr 1
  have hq1 : 1 < p ^ f := Nat.one_lt_pow hf (Fact.out : p.Prime).one_lt
  have hev : 2 ∣ (p ^ f) ^ 2 - 1 := by
    have : Odd ((p ^ f) ^ 2) := (hpodd.pow).pow
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by omega⟩
  rw [Nat.mul_div_assoc _ hev, Nat.factorization_mul (by positivity) (by
    have : 2 < (p ^ f) ^ 2 := by nlinarith
    omega), Finsupp.add_apply, Nat.Prime.factorization_pow Fact.out, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd, add_zero]
  intro hdvd
  have h1 : p ∣ (p ^ f) ^ 2 - 1 := hdvd.trans (Nat.div_dvd_of_dvd hev)
  have h2 : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p hf) two_ne_zero
  have h3 : p ∣ (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) := Nat.dvd_sub h2 h1
  rw [Nat.sub_sub_self (by nlinarith)] at h3
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h3)

theorem psl2_sylow_p_ti (hK : Nat.card K = p ^ f) (P₁ P₂ : Sylow p PSL(2, K))
    {x : PSL(2, K)} (h1 : x ∈ P₁) (h2 : x ∈ P₂) (hx : x ≠ 1) : P₁ = P₂ := by
  obtain ⟨U, S, -, -, -, -, hpart⟩ :=
    Glauberman.Dickson.huppert_II_8_5_a_psl2_cover (F := K) hK P₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, K) P₁ P₂
  have hP₂ : (P₂ : Subgroup PSL(2, K)) =
      (P₁ : Subgroup PSL(2, K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  have hu := (hpart x hx).unique
    (y₁ := (P₁ : Subgroup PSL(2, K))) (y₂ := (P₂ : Subgroup PSL(2, K)))
    ⟨h1, Or.inl ⟨1, by ext y; simp⟩⟩ ⟨h2, Or.inl ⟨g, hP₂⟩⟩
  exact Sylow.ext hu

theorem psl2_sylow_p_borel (hK : Nat.card K = p ^ f) (hp : p ≠ 2) (hf : f ≠ 0)
    (P : Sylow p PSL(2, K)) :
    IsMulCommutative (P : Subgroup PSL(2, K)) ∧
      Nat.card (Subgroup.normalizer ((P : Subgroup PSL(2, K)) : Set PSL(2, K))) ∣
        p ^ f * ((p ^ f - 1) / 2) ∧
      ∀ n ∈ Subgroup.normalizer ((P : Subgroup PSL(2, K)) : Set PSL(2, K)), n ∉ P →
        ∀ x ∈ P, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  classical
  set ι := (⊤ : Subgroup PSL(2, K)).subtype with hιdef
  have hι : Function.Injective ι := Subtype.val_injective
  set P' : Sylow p (⊤ : Subgroup PSL(2, K)) := P.subtype le_top with hP'def
  have hP'coe : (P' : Subgroup (⊤ : Subgroup PSL(2, K))) =
      (P : Subgroup PSL(2, K)).subgroupOf ⊤ := Sylow.coe_subtype _ _
  have hP'map : (P' : Subgroup (⊤ : Subgroup PSL(2, K))).map ι = P := by
    rw [hP'coe, Subgroup.subgroupOf_map_subtype, inf_top_eq]
  have hcardP : Nat.card P = p ^ f := psl2_card_sylow_p hK hp hf P
  have hcardP' : Nat.card (P' : Subgroup (⊤ : Subgroup PSL(2, K))) = p ^ f := by
    rw [← Subgroup.card_map_of_injective hι, hP'map, hcardP]
  have hP'ne : (P' : Subgroup (⊤ : Subgroup PSL(2, K))) ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hcardP'
    exact (Nat.one_lt_pow hf (Fact.out : p.Prime).one_lt).ne' hcardP'.symm
  set N := Subgroup.normalizer
    ((P' : Subgroup (⊤ : Subgroup PSL(2, K))) : Set (⊤ : Subgroup PSL(2, K))) with hNdef
  have hNmap : N.map ι = Subgroup.normalizer ((P : Subgroup PSL(2, K)) : Set PSL(2, K)) := by
    rw [hNdef, map_normalizer_of_injective ι hι, hP'map, hιdef, Subgroup.range_subtype,
      top_inf_eq]
  obtain ⟨-, hdvd, hfix, U, T, conjH, hinj, -, hU, -, -, -, hPU, -⟩ :=
    Glauberman.Dickson.h821_borel_quotient_data (F := K) hK ⊤ P' hP'ne N rfl
      ((P' : Subgroup (⊤ : Subgroup PSL(2, K))).subgroupOf N) rfl
  have hmemP' : ∀ {a : PSL(2, K)}, a ∈ P →
      (⟨a, trivial⟩ : (⊤ : Subgroup PSL(2, K))) ∈ (P' : Subgroup (⊤ : Subgroup PSL(2, K))) := by
    intro a ha
    rw [hP'coe, Subgroup.mem_subgroupOf]
    exact ha
  refine ⟨?_, ?_, ?_⟩
  ·
    refine ⟨⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => Subtype.ext ?_⟩⟩
    have hc := hU.is_comm.comm ⟨conjH ⟨a, trivial⟩, hPU ⟨_, hmemP' ha, rfl⟩⟩
      ⟨conjH ⟨b, trivial⟩, hPU ⟨_, hmemP' hb, rfl⟩⟩
    have := @hinj ((⟨a, trivial⟩ : (⊤ : Subgroup PSL(2, K))) * ⟨b, trivial⟩)
      (⟨b, trivial⟩ * ⟨a, trivial⟩) (by rw [map_mul, map_mul]; exact congrArg Subtype.val hc)
    change a * b = b * a
    exact congrArg Subtype.val this
  ·
    have hcardN : Nat.card N =
        Nat.card (Subgroup.normalizer ((P : Subgroup PSL(2, K)) : Set PSL(2, K))) := by
      rw [← hNmap, Subgroup.card_map_of_injective hι]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((P' : Subgroup (⊤ : Subgroup PSL(2, K))).subgroupOf N)
    have hPN : Nat.card ((P' : Subgroup (⊤ : Subgroup PSL(2, K))).subgroupOf N) = p ^ f := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hcardP']
    have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
    have hgcd : Nat.gcd (p ^ f - 1) 2 = 2 := by
      apply Nat.gcd_eq_right
      obtain ⟨k, hk⟩ := hpodd.pow (n := f)
      exact ⟨k, by omega⟩
    rw [hK, hgcd] at hdvd
    rw [← hcardN, h1, hPN, mul_comm]
    exact Nat.mul_dvd_mul_left _ hdvd
  ·
    intro n hn hnP x hxP hx1 hcomm
    obtain ⟨m, hmN, hmn⟩ := hNmap ▸ hn
    have hm : m = ⟨n, trivial⟩ := Subtype.ext hmn
    subst hm
    refine hfix ⟨⟨n, trivial⟩, hmN⟩ ?_ ⟨⟨x, trivial⟩, hmemP' hxP⟩ ?_ ?_
    · intro h0
      apply hnP
      rw [Subgroup.mem_subgroupOf, hP'coe, Subgroup.mem_subgroupOf] at h0
      exact h0
    · intro h0
      apply hx1
      exact congrArg (fun y : (P' : Subgroup (⊤ : Subgroup PSL(2, K))) =>
        ((y : (⊤ : Subgroup PSL(2, K))) : PSL(2, K))) h0
    · exact Subtype.ext hcomm

end PSL2

structure PSL2UnipotentFacts {G : Type*} [Group G] (F : Subgroup G) (p f : ℕ) : Prop where
  exists_le : ∀ P : Subgroup G, P ≤ F → IsPGroup p P →
    ∃ R : Subgroup G, P ≤ R ∧ R ≤ F ∧ Nat.card R = p ^ f
  card_dvd : ∀ P : Subgroup G, P ≤ F → IsPGroup p P → Nat.card P ∣ p ^ f
  abelian : ∀ R : Subgroup G, R ≤ F → Nat.card R = p ^ f → IsMulCommutative R
  ti : ∀ R₁ R₂ : Subgroup G, R₁ ≤ F → R₂ ≤ F → Nat.card R₁ = p ^ f → Nat.card R₂ = p ^ f →
    ∀ x ∈ R₁, x ∈ R₂ → x ≠ 1 → R₁ = R₂
  normalizer : ∀ R : Subgroup G, R ≤ F → Nat.card R = p ^ f →
    Nat.card (F ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) ∣ p ^ f * ((p ^ f - 1) / 2)
  centralizer : ∀ R : Subgroup G, R ≤ F → Nat.card R = p ^ f → ∀ x ∈ R, x ≠ 1 →
    F ⊓ Subgroup.centralizer ({x} : Set G) = R

theorem psl2UnipotentFacts {G : Type*} [Group G] {p f : ℕ} [Fact p.Prime] (F : Subgroup G)
    (e : F ≃* PSL(2, GaloisField p f)) (hp : p ≠ 2) (hf : f ≠ 0) :
    PSL2UnipotentFacts F p f := by
  classical
  set K := GaloisField p f
  have hKcard : Nat.card K = p ^ f := GaloisField.card p f hf
  let ι : PSL(2, K) →* G := F.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := F.subtype_injective.comp e.symm.injective
  have hrange : ι.range = F := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [ι]⟩
  have hmapcomap : ∀ X : Subgroup G, X ≤ F → (X.comap ι).map ι = X := fun X hX =>
    Subgroup.map_comap_eq_self (hrange ▸ hX)
  have hcardcomap : ∀ X : Subgroup G, X ≤ F → Nat.card (X.comap ι) = Nat.card X := fun X hX => by
    rw [← Subgroup.card_map_of_injective hι, hmapcomap X hX]
  have hfac : p ^ (Nat.card PSL(2, K)).factorization p = p ^ f := by
    rw [← Sylow.card_eq_multiplicity (default : Sylow p PSL(2, K))]
    exact psl2_card_sylow_p hKcard hp hf _
  have hsyl : ∀ R : Subgroup G, R ≤ F → Nat.card R = p ^ f →
      ∃ S : Sylow p PSL(2, K), (S : Subgroup PSL(2, K)).map ι = R := by
    intro R hRF hR
    refine ⟨Sylow.ofCard (R.comap ι) (by rw [hcardcomap R hRF, hR, hfac]), ?_⟩
    exact hmapcomap R hRF
  have hpg : ∀ P : Subgroup G, P ≤ F → IsPGroup p P → IsPGroup p (P.comap ι) :=
    fun P hPF hP => hP.of_equiv (((P.comap ι).equivMapOfInjective ι hι).trans
      (MulEquiv.subgroupCongr (hmapcomap P hPF))).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hPF hP
    obtain ⟨S, hS⟩ := (hpg P hPF hP).exists_le_sylow
    refine ⟨(S : Subgroup PSL(2, K)).map ι, ?_, ?_, ?_⟩
    · rw [← hmapcomap P hPF]
      exact Subgroup.map_mono hS
    · rw [← hrange]
      exact Subgroup.map_le_range ι _
    · rw [Subgroup.card_map_of_injective hι]
      exact psl2_card_sylow_p hKcard hp hf S
  · intro P hPF hP
    obtain ⟨S, hS⟩ := (hpg P hPF hP).exists_le_sylow
    rw [← hcardcomap P hPF, ← psl2_card_sylow_p hKcard hp hf S]
    exact Subgroup.card_dvd_of_le hS
  · intro R hRF hR
    obtain ⟨S, rfl⟩ := hsyl R hRF hR
    have hab := (psl2_sylow_p_borel hKcard hp hf S).1
    have eS := (S : Subgroup PSL(2, K)).equivMapOfInjective ι hι
    exact ⟨⟨fun a b => eS.symm.injective (by rw [map_mul, map_mul]; exact hab.is_comm.comm _ _)⟩⟩
  · intro R₁ R₂ hR₁F hR₂F hR₁ hR₂ x hx₁ hx₂ hx1
    obtain ⟨S₁, rfl⟩ := hsyl R₁ hR₁F hR₁
    obtain ⟨S₂, rfl⟩ := hsyl R₂ hR₂F hR₂
    obtain ⟨y, hy₁, rfl⟩ := hx₁
    obtain ⟨y', hy₂, hyy⟩ := hx₂
    have hyy' : y' = y := hι hyy
    subst hyy'
    rw [psl2_sylow_p_ti hKcard S₁ S₂ hy₁ hy₂ (fun h0 => hx1 (by rw [h0, map_one]))]
  · intro R hRF hR
    obtain ⟨S, rfl⟩ := hsyl R hRF hR
    have h := map_normalizer_of_injective ι hι (S : Subgroup PSL(2, K))
    rw [hrange] at h
    rw [← h, Subgroup.card_map_of_injective hι]
    exact (psl2_sylow_p_borel hKcard hp hf S).2.1
  · intro R hRF hR x hx hx1
    obtain ⟨S, rfl⟩ := hsyl R hRF hR
    obtain ⟨y, hy, rfl⟩ := hx
    have hy1 : y ≠ 1 := fun h0 => hx1 (by rw [h0, map_one])
    obtain ⟨hab, -, hfrob⟩ := psl2_sylow_p_borel hKcard hp hf S
    have hC : Subgroup.centralizer ({y} : Set PSL(2, K)) = S := by
      apply le_antisymm
      · intro g hg
        have hgy : g * y * g⁻¹ = y := by
          rw [(Subgroup.mem_centralizer_singleton_iff.mp hg), mul_inv_cancel_right]
        have hgS : g ∈ Subgroup.normalizer ((S : Subgroup PSL(2, K)) : Set PSL(2, K)) := by
          have hS' : (g • S : Sylow p PSL(2, K)) = S := by
            refine (psl2_sylow_p_ti hKcard S (g • S) hy ?_ hy1).symm
            change y ∈ MulAut.conj g • (S : Subgroup PSL(2, K))
            exact ⟨y, hy, hgy⟩
          exact (Sylow.smul_eq_iff_mem_normalizer).mp hS'
        by_contra hgS'
        exact hfrob g hgS hgS' y hy hy1 hgy
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hab.is_comm.comm ⟨z, hz⟩ ⟨y, hy⟩)
    have h := map_centralizer_singleton_of_injective ι hι y
    rw [hrange, hC] at h
    exact h.symm

end CFSG.Walter.JT
