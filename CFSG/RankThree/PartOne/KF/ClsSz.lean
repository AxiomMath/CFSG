module

public import CFSG.RankThree.PartOne.KF.ClassifyTags
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.LieType.BorelTits.Suzuki

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank

namespace KFU

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_borel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Q : Sylow 2 G)
    (hB : fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup G) : Set G)))
    {D : Subgroup G} (hDcyc : IsCyclic D) (hQDsup : (Q : Subgroup G) ⊔ D =
      Subgroup.normalizer ((Q : Subgroup G) : Set G)) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hU0 : U ≠ ⊥) (hUQ : U ≤ (Q : Subgroup G)) {E : Subgroup G}
    (hEU : E ≤ Subgroup.normalizer (U : Set G)) (hEel : IsElementaryAbelian p E) :
    Nat.card E ≤ p := by
  set B := Subgroup.normalizer ((Q : Subgroup G) : Set G) with hBdef
  obtain ⟨-, -, hodd⟩ := hB
  have hQB : (Q : Subgroup G) ≤ B := Subgroup.le_normalizer
  have hNU : Subgroup.normalizer (U : Set G) ≤ B := by
    intro g hg
    by_contra hgB
    have hgodd := hodd g hgB
    have hUle : U ≤ B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro u hu
      refine ⟨hQB (hUQ hu), Subgroup.mem_map.mpr ⟨g * u * g⁻¹, ?_, ?_⟩⟩
      · exact hQB (hUQ ((Subgroup.mem_normalizer_iff.mp hg u).mp hu))
      · simp [mul_assoc]
    have hne : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU0
    obtain ⟨n, hn, hcard⟩ := hU2.nontrivial_iff_card.mp hne
    have hdvd : 2 ∣ Nat.card (B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) :=
      (dvd_pow_self 2 hn.ne').trans (hcard ▸ Subgroup.card_dvd_of_le hUle)
    exact (Nat.not_even_iff_odd.mpr hgodd) (even_iff_two_dvd.mpr hdvd)
  have hEB : E ≤ B := hEU.trans hNU
  have hDB : D ≤ B := le_sup_right.trans hQDsup.le
  have hEexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hEQ : E ⊓ (Q : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxQ⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨x, hxQ⟩
    have hk' : orderOf x = 2 ^ k := by
      rw [← hk, ← Subgroup.orderOf_coe]
    have hdvd : 2 ^ k ∣ p := hk' ▸ orderOf_dvd_of_pow_eq_one (hEexp x hxE)
    have hcop : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
    have h1 : orderOf x = 1 := by rw [hk', Nat.Coprime.eq_one_of_dvd hcop hdvd]
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  let Q' : Subgroup B := (Q : Subgroup G).subgroupOf B
  have : Q'.Normal := Subgroup.normal_in_normalizer
  let π : B →* B ⧸ Q' := QuotientGroup.mk' Q'
  let ι : D →* B := Subgroup.inclusion hDB
  have htop : Q' ⊔ D.subgroupOf B = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQB hDB, hQDsup, Subgroup.subgroupOf_self]
  have hsurj : Function.Surjective (π.comp ι) := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hb : b ∈ Q' ⊔ D.subgroupOf B := htop ▸ Subgroup.mem_top b
    obtain ⟨q, hq, d, hd, hqd⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    refine ⟨⟨(d : G), Subgroup.mem_subgroupOf.mp hd⟩, ?_⟩
    have hιd : ι ⟨(d : G), Subgroup.mem_subgroupOf.mp hd⟩ = d := Subtype.ext rfl
    rw [MonoidHom.comp_apply, hιd, ← hqd]
    have hπq : π q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    change π d = π (q * d)
    rw [map_mul, hπq, one_mul]
  have : IsCyclic (B ⧸ Q') := isCyclic_of_surjective (π.comp ι) hsurj
  have hinj : Function.Injective (π.comp (E.subgroupOf B).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      at hx
    have hxE : ((x : B) : G) ∈ E := x.2
    have hxQ : ((x : B) : G) ∈ (Q : Subgroup G) := hx
    have : ((x : B) : G) ∈ E ⊓ (Q : Subgroup G) := ⟨hxE, hxQ⟩
    rw [hEQ, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext this))
  have : IsCyclic (E.subgroupOf B) := isCyclic_of_injective _ hinj
  have : IsCyclic E := isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEB).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hEB).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hEexp g g.2)
  exact (hord ▸ Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp))

theorem localRank_le_one_of_fusionBenderBorel {q k : ℕ} (hG : fusionBenderBorel G q k) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : localRank p G ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hU2, hU0, E, hEU, hEel, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hlt
  obtain ⟨Q, hUQ⟩ := hU2.exists_le_sylow
  obtain ⟨hSE, ⟨D, hDcyc, -, -, hQDsup⟩, -, -, -⟩ := hG Q
  have h1 := card_le_of_borel hp hp2 Q hSE hDcyc hQDsup hU2 hU0 hUQ hEU hEel
  rw [hEc] at h1
  have := hp.two_le
  nlinarith

end KFU

theorem kf123ClassifyTag_twistedB2 : KF123ClassifyTag .twistedB2 := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  exfalso
  have hS : Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := hS
  let e' : (↥L ⧸ Subgroup.center ↥L) ≃* Sz a :=
    e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  have : Finite (Sz a) := Finite.of_equiv _ e'.toEquiv
  have hrank := h.localRank_eq_two_of_mulEquiv e'
  have hle := KFU.localRank_le_one_of_fusionBenderBorel (bender_suzuki_borel_full a ha) h.prime
    (by have := h.five_le; omega)
  omega

end CFSG.RankThree.PartOne
