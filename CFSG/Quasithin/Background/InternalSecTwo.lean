module

public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.Foundations.KCoreClosure
public import CFSG.LocalAnalysis.QuasithinUnique.Reduction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open

section TwoPow

variable {Ω : Type} [Group Ω]

theorem mem_of_pow_mem_of_odd {K : Subgroup Ω} {x : Ω} {e : ℕ} (hx : x ^ 2 ^ e ∈ K)
    (ho : Odd (orderOf x)) : x ∈ K := by
  have hcop : Nat.Coprime (2 ^ e) (orderOf x) :=
    Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr ho)
  exact (Subgroup.zpowers_le.mpr hx) (A4.mem_zpowers_pow_of_coprime hcop)

theorem quasithinGenFitting_eq_of_two_pow [Finite Ω] {Y L : Subgroup Ω} (hLY : L ≤ Y)
    (hn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hL : CFSG.Open.IsQuasisimple ↥L)
    (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L) (hO2 : pCoreOf 2 Y = ⊥) :
    quasithinGenFitting Y = L := by
  apply le_antisymm
  · unfold quasithinGenFitting
    refine sup_le (sSup_le ?_) (sSup_le ?_)
    · rintro N ⟨hNY, hNn, hNnil⟩ x hx
      have hn' : ∀ y ∈ Y, ∀ z ∈ N, y * z * y⁻¹ ∈ N := by
        intro y hy z hz
        have := hNn.conj_mem ⟨z, hNY hz⟩ (by rw [Subgroup.mem_subgroupOf]; exact hz) ⟨y, hy⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      have hodd := B1Red.odd_orderOf_of_nilpotent_normal hNY hn' hO2 x hx
      obtain ⟨e, he⟩ := h2 x (hNY hx)
      exact mem_of_pow_mem_of_odd he hodd
    · rintro K ⟨hKY, -, hKq⟩ k hk
      have hperf : Group.IsPerfect ↥K := ⟨hKq.1⟩
      have h1 : K ≤ oTwoUpper Y := B1Red.perfect_le_oTwoUpper' hKY hperf
      have h3 : oTwoUpper Y ≤ L := oTwoUpper_le_of_pow_mem h2
      exact h3 (h1 hk)
  · refine le_sup_of_le_right (le_sSup ⟨hLY, ?_, hL⟩)
    refine IsSubnormal.step hLY ?_ (IsSubnormal.refl _)
    exact (Subgroup.normal_subgroupOf_iff hLY).2 fun l y hl hy => hn y hy l hl

theorem pRank_top_le_of_two_pow [Finite Ω] {Y K : Subgroup Ω} (hKY : K ≤ Y)
    (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥Y) ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup ↥Y)
  have hEK : E ≤ K.subgroupOf Y := by
    intro x hx
    have hxp : x ^ p = 1 := hE.2 x hx
    have hodd : Odd (orderOf x) := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hxp) with h | h
      · rw [h]
        exact odd_one
      · rw [h]
        exact hp.odd_of_ne_two hp2
    obtain ⟨e, he⟩ := h2 (x : Ω) x.2
    have he' : x ^ 2 ^ e ∈ K.subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      simpa using he
    exact mem_of_pow_mem_of_odd he' hodd
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥Y) ≤ CFSG.Open.pRank p (K.subgroupOf Y) :=
    CFSG.SectionRank.le_pRank hp1 hEK hE hcard
  have h2' : CFSG.Open.pRank p (⊤ : Subgroup ↥(K.subgroupOf Y)) =
      CFSG.Open.pRank p (K.subgroupOf Y) :=
    CFSG.Quasithin.pRank_top_subtype (p := p) (K.subgroupOf Y)
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup ↥(K.subgroupOf Y)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥K) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 (Subgroup.subgroupOfEquivOfLe hKY)
  omega

theorem stronglyQuasithin_of_two_pow [Finite Ω] {Y K : Subgroup Ω} (hKY : K ≤ Y)
    (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ K) (hK : SQTKTauCeti.StronglyQuasithin ↥K) :
    SQTKTauCeti.StronglyQuasithin ↥Y := fun p hp hp2 =>
  (pRank_top_le_of_two_pow hKY h2 hp hp2).trans (hK p hp hp2)

theorem commute_of_isPGroup_two {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : IsPGroup 2 S) (a b : S) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nontrivial ↥(Subgroup.center S) := hS.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).1 hc)
  · have hb : b ∈ Subgroup.center S := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 hb a)

theorem isKGroupCat_of_two_pow [Finite Ω] {Y K : Subgroup Ω}
    (hn : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K) (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ K)
    (hK : CFSG.SectionRank.IsKGroupCat ↥K) : CFSG.SectionRank.IsKGroupCat ↥Y := by
  have : (K.subgroupOf Y).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn _ g.2 _ hx⟩
  have hP : IsPGroup 2 (↥Y ⧸ K.subgroupOf Y) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := h2 y y.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (↥Y ⧸ K.subgroupOf Y) := hP.isNilpotent
  let f : ↥(K.subgroupOf Y) →* ↥K :=
    { toFun := fun x => ⟨((x : Y) : Ω), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b hab => by
    apply Subtype.ext
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hab
  exact CFSG.KCore.KGroupAllSimple.of_ker CFSG.SectionRank.catalog_isoInvariant
    (QuotientGroup.mk' (K.subgroupOf Y))
    ((hK.of_injective f hf).of_mulEquiv (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' _)))
    (CFSG.KCore.KGroupAllSimple.of_isSolvable CFSG.SectionRank.catalog_containsAbelianSimple
      inferInstance)

theorem sqtkGroup_of_two_pow [Finite Ω] {Y K : Subgroup Ω} (hKY : K ≤ Y)
    (hn : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K) (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ K)
    (hK : SQTKGroup ↥K) : SQTKGroup ↥Y :=
  ⟨stronglyQuasithin_of_two_pow hKY h2 hK.1, isKGroupCat_of_two_pow hn h2 hK.2⟩

end TwoPow

section Surjective

theorem sqtkGroup_of_surjective {X Q : Type} [Group X] [Group Q] [Finite X] [Finite Q]
    (f : X →* Q) (hf : Function.Surjective f) (hker : IsPGroup 2 ↥f.ker) (hS : SQTKGroup X) :
    SQTKGroup Q := by
  set e : X ⧸ f.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hf
  refine ⟨fun p hp hp2 => ?_, (hS.2.quotient f.ker).of_mulEquiv e.symm⟩
  have : Fact p.Prime := ⟨hp⟩
  have hndvd : ¬ p ∣ Nat.card ↥f.ker := by
    intro hd
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    rw [hn] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup Q) = CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ f.ker)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e.symm
  have h2 := CFSG.SectionRank.pRank_quotient_eq (p := p) f.ker hndvd
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := hS.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup Q) ≤ 2
  omega

end Surjective

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem sqtkGroup_mono {P L : Subgroup G} (hS : SQTKGroup ↥P) (hLP : L ≤ P) : SQTKGroup ↥L := by
  refine ⟨fun p hp hp2 => ?_, (hS.2.subgroup (L.subgroupOf P)).of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hLP).symm⟩
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥L) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(L.subgroupOf P)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (Subgroup.subgroupOfEquivOfLe hLP).symm
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥(L.subgroupOf P)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup ↥P) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (L.subgroupOf P).subtype
      (L.subgroupOf P).subtype_injective
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup ↥P) ≤ 2 := hS.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ 2
  omega

theorem sqtkGroup_of_localSQTK (h : QuasithinUnique.LocalSQTK G) {P : Subgroup G}
    (hP : pCoreOf 2 P ≠ ⊥) : SQTKGroup ↥P :=
  ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mp (h P hP).1, (h P hP).2⟩

end Ambient

end CFSG.Quasithin.InternalSec
