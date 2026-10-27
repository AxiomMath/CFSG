module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Basic

variable {S : Type} [Group S] {c : S} {L : Subgroup S} {𝒟 : Subgroup (MulAut S)}

@[expose] def fixIn (𝒟 : Subgroup (MulAut S)) (L : Subgroup S) : Subgroup S where
  carrier := {l | l ∈ L ∧ ∀ φ ∈ 𝒟, φ l = l}
  mul_mem' := by
    rintro a b ⟨haL, ha⟩ ⟨hbL, hb⟩
    exact ⟨mul_mem haL hbL, fun φ hφ => by rw [map_mul, ha φ hφ, hb φ hφ]⟩
  one_mem' := ⟨one_mem L, fun φ _ => map_one φ⟩
  inv_mem' := by
    rintro a ⟨haL, ha⟩
    exact ⟨inv_mem haL, fun φ hφ => by rw [map_inv, ha φ hφ]⟩

theorem mem_fixIn {l : S} : l ∈ fixIn 𝒟 L ↔ l ∈ L ∧ ∀ φ ∈ 𝒟, φ l = l := Iff.rfl

theorem fixIn_le (𝒟 : Subgroup (MulAut S)) (L : Subgroup S) : fixIn 𝒟 L ≤ L :=
  fun _ hl => (mem_fixIn.mp hl).1

theorem comap_conj_le_centralizer (𝒟 : Subgroup (MulAut S)) (L : Subgroup S) :
    𝒟.comap (MulAut.conj : S →* MulAut S) ≤ Subgroup.centralizer (fixIn 𝒟 L : Set S) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : MulAut.conj s l = l := (mem_fixIn.mp hl).2 _ (Subgroup.mem_comap.mp hs)
  rw [MulAut.conj_apply] at h1
  calc l * s = (s * l * s⁻¹) * s := by rw [h1]
    _ = s * l := by group

namespace CoprimeAux

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hmem : s ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj s g = g := by rw [hs]; rfl
    rw [MulAut.conj_apply] at h1
    calc g * s = (s * g * s⁻¹) * s := by rw [h1]
      _ = s * g := by group
  rw [hZ] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem pow_three_eq_one_of_conj_mem (hZ : Subgroup.center S = ⊥) (h3 : ∀ φ ∈ 𝒟, φ ^ 3 = 1)
    {s : S} (hs : MulAut.conj s ∈ 𝒟) : s ^ 3 = 1 := by
  apply conj_injective_of_center_eq_bot hZ
  rw [map_pow, map_one]
  exact h3 _ hs

theorem mem_thetaIn_iff {x : S} :
    x ∈ thetaIn L ↔ ∃ z : L, z ∈ aschbacherSolvableCore 3 L ∧ (z : S) = x := by
  unfold thetaIn
  exact Subgroup.mem_map

theorem coe_mem_thetaIn_iff (z : L) :
    (z : S) ∈ thetaIn L ↔ z ∈ aschbacherSolvableCore 3 L := by
  rw [mem_thetaIn_iff]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := Subtype.ext hwz
    exact hwz' ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem thetaIn_le (L : Subgroup S) : thetaIn L ≤ L := by
  intro x hx
  obtain ⟨z, -, rfl⟩ := mem_thetaIn_iff.mp hx
  exact z.2

theorem thetaIn_conj_mem {x y : S} (hx : x ∈ L) (hy : y ∈ thetaIn L) :
    x * y * x⁻¹ ∈ thetaIn L := by
  obtain ⟨z, hz, rfl⟩ := mem_thetaIn_iff.mp hy
  refine mem_thetaIn_iff.mpr ⟨⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹, ?_, rfl⟩
  exact (inferInstance : (aschbacherSolvableCore 3 L).Normal).conj_mem z hz ⟨x, hx⟩

end CoprimeAux

theorem card_comap_conj (hZ : Subgroup.center S = ⊥)
    (h𝒟 : 𝒟 ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S) :
    Nat.card (𝒟.comap (MulAut.conj : S →* MulAut S)) = Nat.card 𝒟 := by
  have hinj := CoprimeAux.conj_injective_of_center_eq_bot hZ
  refine Nat.card_congr (Equiv.ofBijective
    (fun s : 𝒟.comap (MulAut.conj : S →* MulAut S) =>
      (⟨MulAut.conj (s : S), Subgroup.mem_comap.mp s.2⟩ : 𝒟)) ⟨?_, ?_⟩)
  · intro s t hst
    exact Subtype.ext (hinj (congrArg Subtype.val hst))
  · intro φ
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (h𝒟 φ.2)
    exact ⟨⟨s, Subgroup.mem_comap.mpr (by rw [hs]; exact φ.2)⟩, Subtype.ext hs⟩

theorem isElemAbelian_comap_conj (hZ : Subgroup.center S = ⊥)
    (hab : ∀ φ ∈ 𝒟, ∀ ψ ∈ 𝒟, φ * ψ = ψ * φ) (h3 : ∀ φ ∈ 𝒟, φ ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (𝒟.comap (MulAut.conj : S →* MulAut S)) := by
  have hinj := CoprimeAux.conj_injective_of_center_eq_bot hZ
  refine ⟨isMulCommutative_iff.mpr fun a b => ?_,
    fun x hx => CoprimeAux.pow_three_eq_one_of_conj_mem hZ h3 (Subgroup.mem_comap.mp hx)⟩
  apply Subtype.ext
  apply hinj
  simp only [Subgroup.coe_mul, map_mul]
  exact hab _ (Subgroup.mem_comap.mp a.2) _ (Subgroup.mem_comap.mp b.2)

theorem le_inner_of_not_dvd (h3 : ∀ φ ∈ 𝒟, φ ^ 3 = 1)
    (hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) :
    𝒟 ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
  intro φ hφ
  have hq3 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S) φ) ^ 3
      = 1 := by
    rw [← map_pow, h3 φ hφ, map_one]
  have hdvd3 := orderOf_dvd_of_pow_eq_one hq3
  have hdvdN := orderOf_dvd_natCard
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S) φ)
  have hone : orderOf
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S) φ) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact h
    · exact absurd (h ▸ hdvdN) hout
  exact (QuotientGroup.eq_one_iff φ).mp (orderOf_eq_one_iff.mp hone)

end Basic

section Finite

variable {S : Type} [Group S] [Finite S] {c : S} {L : Subgroup S} {𝒟 : Subgroup (MulAut S)}

namespace CoprimeAux

private def restrictAut (φ : MulAut S) (hφ : ∀ l : S, φ l ∈ L ↔ l ∈ L) : MulAut L where
  toFun l := ⟨φ l, (hφ l).2 l.2⟩
  invFun l := ⟨φ.symm l, (hφ (φ.symm l)).1 (by rw [MulEquiv.apply_symm_apply]; exact l.2)⟩
  left_inv l := Subtype.ext (φ.symm_apply_apply l)
  right_inv l := Subtype.ext (φ.apply_symm_apply l)
  map_mul' a b := Subtype.ext (map_mul φ (a : S) (b : S))

theorem map_mem_thetaIn {φ : MulAut S} (hφ : ∀ l : S, φ l ∈ L ↔ l ∈ L) {y : S}
    (hy : y ∈ thetaIn L) : φ y ∈ thetaIn L := by
  obtain ⟨z, hz, rfl⟩ := mem_thetaIn_iff.mp hy
  have hσ : restrictAut φ hφ z ∈ aschbacherSolvableCore 3 L := by
    have h1 := Subgroup.mem_map_of_mem (restrictAut φ hφ : L →* L) hz
    rw [Sec4.map_aschbacherSolvableCore (restrictAut φ hφ)] at h1
    exact h1
  exact mem_thetaIn_iff.mpr ⟨restrictAut φ hφ z, hσ, rfl⟩

theorem not_dvd_card_thetaIn (L : Subgroup S) : ¬ 3 ∣ Nat.card (thetaIn L) := by
  have h := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  unfold thetaIn
  rwa [Subgroup.card_map_of_injective L.subtype_injective]

theorem eq_one_of_mem_thetaIn_of_pow_three {u : S} (hu : u ∈ thetaIn L) (h3 : u ^ 3 = 1) :
    u = 1 := by
  have hcop : Nat.Coprime 3 (Nat.card (thetaIn L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_dvd_card_thetaIn L)
  have h1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf u ∣ Nat.card (thetaIn L) := by
    have := orderOf_dvd_natCard (⟨u, hu⟩ : thetaIn L)
    rwa [Subgroup.orderOf_mk] at this
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end CoprimeAux

theorem AutDatum.surj_fixIn (h : AutDatum S c L 𝒟) (t : L ⧸ aschbacherSolvableCore 3 L) :
    ∃ l : L, (l : S) ∈ fixIn 𝒟 L ∧ ((l : L) : L ⧸ aschbacherSolvableCore 3 L) = t := by
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective t
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup 3 𝒟 := IsPGroup.of_card (n := 2) (by rw [h.card]; norm_num)
  have hinv : ∀ a : 𝒟, ∀ x : S, (l₀ : S)⁻¹ * x ∈ thetaIn L →
      (l₀ : S)⁻¹ * (a : MulAut S) x ∈ thetaIn L := by
    intro a x hx
    have hφ : (a : MulAut S) ∈ 𝒟 := a.2
    have h1 : (l₀ : S)⁻¹ * (a : MulAut S) l₀ ∈ thetaIn L := by
      have e : (l₀ : S)⁻¹ * (a : MulAut S) l₀
          = (l₀ : S)⁻¹ * ((a : MulAut S) l₀ * (l₀ : S)⁻¹) * ((l₀ : S)⁻¹)⁻¹ := by group
      rw [e]
      exact CoprimeAux.thetaIn_conj_mem (inv_mem l₀.2) (h.trivial _ hφ l₀ l₀.2)
    have h2 : (a : MulAut S) ((l₀ : S)⁻¹ * x) ∈ thetaIn L :=
      CoprimeAux.map_mem_thetaIn (h.map_eq _ hφ) hx
    have e : (l₀ : S)⁻¹ * (a : MulAut S) x
        = ((l₀ : S)⁻¹ * (a : MulAut S) l₀) * (a : MulAut S) ((l₀ : S)⁻¹ * x) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact mul_mem h1 h2
  obtain ⟨c', hc'θ, hc'fix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA 𝒟.subtype (thetaIn L)
      (CoprimeAux.not_dvd_card_thetaIn L) (l₀ : S)).2 hinv
  have hc'L : c' ∈ L := by
    have := mul_mem l₀.2 (CoprimeAux.thetaIn_le L hc'θ)
    rwa [mul_inv_cancel_left] at this
  refine ⟨⟨c', hc'L⟩, ⟨hc'L, fun φ hφ => hc'fix ⟨φ, hφ⟩⟩, ?_⟩
  symm
  rw [QuotientGroup.eq]
  exact (CoprimeAux.coe_mem_thetaIn_iff (l₀⁻¹ * ⟨c', hc'L⟩)).mp hc'θ

theorem AutDatum.exists_lift (h : AutDatum S c L 𝒟)
    (Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) (hQ : IsPGroup 3 Q) :
    ∃ P : Subgroup S, P ≤ fixIn 𝒟 L ∧ IsPGroup 3 P ∧ Nonempty (P ≃* Q) := by
  let π : fixIn 𝒟 L →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion (fixIn_le 𝒟 L))
  have hsurj : Function.Surjective π := by
    intro t
    obtain ⟨l, hl, hlt⟩ := h.surj_fixIn t
    exact ⟨⟨l, hl⟩, hlt⟩
  have hker : Nat.Coprime 3 (Nat.card π.ker) := by
    have hle : π.ker.map (fixIn 𝒟 L).subtype ≤ thetaIn L := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π x = 1 := hx
      have hmem : Subgroup.inclusion (fixIn_le 𝒟 L) x ∈ aschbacherSolvableCore 3 L :=
        (QuotientGroup.eq_one_iff _).mp hx'
      exact (CoprimeAux.coe_mem_thetaIn_iff (Subgroup.inclusion (fixIn_le 𝒟 L) x)).mpr hmem
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (fixIn 𝒟 L).subtype_injective] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (fun h3 => CoprimeAux.not_dvd_card_thetaIn L (h3.trans hdvd))
  obtain ⟨P₀, hP₀, ⟨e⟩⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3 Nat.prime_three π hsurj
      hker Q hQ
  exact ⟨P₀.map (fixIn 𝒟 L).subtype, Subgroup.map_subtype_le P₀, hP₀.map _,
    ⟨(P₀.equivMapOfInjective _ (fixIn 𝒟 L).subtype_injective).symm.trans e⟩⟩

namespace CoprimeAux

theorem mk_mem_center (h : AutDatum S c L 𝒟) {s : S} (hs : MulAut.conj s ∈ 𝒟) (hsL : s ∈ L) :
    ((⟨s, hsL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨l, hl, rfl⟩ := h.surj_fixIn g
  have hcent : s ∈ Subgroup.centralizer (fixIn 𝒟 L : Set S) :=
    comap_conj_le_centralizer 𝒟 L (Subgroup.mem_comap.mpr hs)
  have hcomm : (l : S) * s = s * (l : S) := Subgroup.mem_centralizer_iff.mp hcent l hl
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg (fun x : L => (x : L ⧸ aschbacherSolvableCore 3 L))
    (Subtype.ext hcomm)

theorem eq_of_mk_eq (h : AutDatum S c L 𝒟) (hZ : Subgroup.center S = ⊥) {s t : S}
    (hs : MulAut.conj s ∈ 𝒟) (ht : MulAut.conj t ∈ 𝒟) (hsL : s ∈ L) (htL : t ∈ L)
    (hst : ((⟨s, hsL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = ((⟨t, htL⟩ : L) :
      L ⧸ aschbacherSolvableCore 3 L)) : s = t := by
  rw [QuotientGroup.eq] at hst
  have hθ : s⁻¹ * t ∈ thetaIn L := (coe_mem_thetaIn_iff (⟨s, hsL⟩⁻¹ * ⟨t, htL⟩)).mpr hst
  have hu : (s⁻¹ * t) ^ 3 = 1 := pow_three_eq_one_of_conj_mem hZ h.pow_three (by
    rw [map_mul, map_inv]
    exact mul_mem (inv_mem hs) ht)
  exact inv_mul_eq_one.mp (eq_one_of_mem_thetaIn_of_pow_three hθ hu)

end CoprimeAux

theorem AutDatum.card_comap_inf_le (h : AutDatum S c L 𝒟) (hZ : Subgroup.center S = ⊥) :
    Nat.card (𝒟.comap (MulAut.conj : S →* MulAut S) ⊓ L : Subgroup S) ≤
      Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
  refine Nat.card_le_card_of_injective
    (fun s : (𝒟.comap (MulAut.conj : S →* MulAut S) ⊓ L : Subgroup S) =>
      (⟨((⟨(s : S), s.2.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L),
        CoprimeAux.mk_mem_center h (Subgroup.mem_comap.mp s.2.1) s.2.2⟩ :
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))) ?_
  intro s t hst
  exact Subtype.ext (CoprimeAux.eq_of_mk_eq h hZ (Subgroup.mem_comap.mp s.2.1)
    (Subgroup.mem_comap.mp t.2.1) s.2.2 t.2.2 (congrArg Subtype.val hst))

theorem AutDatum.comm (h : AutDatum S c L 𝒟) : ∀ φ ∈ 𝒟, ∀ ψ ∈ 𝒟, φ * ψ = ψ * φ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : IsMulCommutative 𝒟 :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [h.card]; norm_num)
  intro φ hφ ψ hψ
  exact congrArg Subtype.val (isMulCommutative_iff.mp hcomm ⟨φ, hφ⟩ ⟨ψ, hψ⟩)

end Finite

end CFSG.RankThree.PartTwo.Sec19.SimsC198
