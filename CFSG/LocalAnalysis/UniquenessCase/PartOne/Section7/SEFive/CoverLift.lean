module

import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Basic
import CFSG.Foundations.MaxOrderThompsonImage
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPDim
import CFSG.LieType.TwoRank.GLElementaryAbelian
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open Subgroup

theorem ker_le_or_eq_one {L : Type*} [Group L] [IsSimpleGroup L] {J : Type*} [Group J]
    (hJ : Group.IsPerfect J) (φ : J →* L) (hφ : Function.Surjective φ) (hsol : IsSolvable φ.ker)
    {M : Type*} [Group M] (ρ : J →* M) : ρ.ker ≤ φ.ker ∨ ρ = 1 := by
  haveI : Group.IsPerfect J := hJ
  haveI : (ρ.ker.map φ).Normal := Subgroup.Normal.map ρ.normal_ker φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map φ) with hbot | htop
  · left
    intro x hx
    have hx' : φ x ∈ ρ.ker.map φ := Subgroup.mem_map_of_mem φ hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact MonoidHom.mem_ker.mp hx'
  · right
    by_contra hρ
    have hkerne : ρ.ker ≠ ⊤ := by
      intro h
      apply hρ
      ext g
      exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g)
    haveI : Nontrivial (J ⧸ ρ.ker) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact hkerne
    have hsurj : Function.Surjective ((QuotientGroup.mk' ρ.ker).comp φ.ker.subtype) := by
      intro z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker z
      have hg : φ g ∈ ρ.ker.map φ := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hg
      refine ⟨⟨n⁻¹ * g, ?_⟩, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hng, inv_mul_cancel]
      · show (QuotientGroup.mk' ρ.ker) (n⁻¹ * g) = (QuotientGroup.mk' ρ.ker) g
        have hn1 : (QuotientGroup.mk' ρ.ker) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
        rw [map_mul, map_inv, hn1, inv_one, one_mul]
    haveI : Group.IsSolvable φ.ker := hsol
    haveI : Group.IsSolvable (J ⧸ ρ.ker) := Group.isSolvable_of_surjective hsurj
    haveI : Group.IsPerfect (J ⧸ ρ.ker) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' ρ.ker) (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.not_isSolvable (J ⧸ ρ.ker) inferInstance

theorem exists_lift {L : Type*} [Group L] {J : Type*} [Group J] [Finite J] (φ : J →* L)
    (hφ : Function.Surjective φ) {q : ℕ} [Fact q.Prime] (hq : Nat.Coprime q (Nat.card φ.ker))
    {S : Subgroup L} (hS : IsPGroup q S) {t : L} (ht : t ∈ Subgroup.normalizer (S : Set L)) :
    ∃ (S' : Subgroup J) (t' : J), IsPGroup q S' ∧ S'.map φ = S ∧ Set.InjOn φ S' ∧
      t' ∈ Subgroup.normalizer (S' : Set J) ∧ φ t' = t := by
  obtain ⟨S', hS'p, hS'map, hN⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1020_frattini_lift φ hφ hS
  have hinj : Set.InjOn φ S' := by
    have h := CFSG.injective_comp_subtype_of_coprime_card_ker φ hq hS'p
    intro a ha b hb hab
    exact congrArg Subtype.val (h (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  obtain ⟨t', ht', ht't⟩ := Subgroup.mem_map.mp (hN ht)
  exact ⟨S', t', hS'p, hS'map, hinj, ht', ht't⟩

theorem coverActsTriviallyOnSmall_of_nonabelian {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {L : Type*} [Group L] [Finite L] [IsSimpleGroup L] {R : Subgroup L} (hR : IsPGroup p R)
    (hnc : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) : CoverActsTriviallyOnSmall p L := by
  intro J instJ finJ hJ φ hφ hcop hsol ℓ hℓ hℓ2 hℓp V instV finV hVcomm hVpow hVcard ρ
  rcases ker_le_or_eq_one hJ φ hφ hsol ρ with hker | hρ
  · exfalso
    haveI : Fact p.Prime := ⟨hp⟩
    have hq : Nat.Coprime p (Nat.card φ.ker) :=
      Nat.Coprime.of_dvd_left (dvd_mul_left p 2) hcop.symm
    obtain ⟨S', t', hS'p, hS'map, hinj, -, -⟩ :=
      exists_lift φ hφ hq hR (t := 1) (Subgroup.one_mem (Subgroup.normalizer (R : Set L)))
    have hnc' : ¬ ∀ a b : ↥S', a * b = b * a := by
      rintro hab
      obtain ⟨a, ha, b, hb, habne⟩ := hnc
      obtain ⟨a', ha', ha'a⟩ := Subgroup.mem_map.mp (hS'map ▸ ha)
      obtain ⟨b', hb', hb'b⟩ := Subgroup.mem_map.mp (hS'map ▸ hb)
      refine habne ?_
      rw [← ha'a, ← hb'b]
      have h := hab ⟨a', ha'⟩ ⟨b', hb'⟩
      simpa using congrArg (fun x : ↥S' => φ (x : J)) h
    have hfaith : ∀ g : ↥S', (ρ.comp S'.subtype) g = 1 → g = 1 := by
      intro g hg
      have hgker : (g : J) ∈ ρ.ker := MonoidHom.mem_ker.mpr hg
      have hgphi : φ (g : J) = 1 := MonoidHom.mem_ker.mp (hker hgker)
      exact Subtype.ext (hinj g.2 (Subgroup.one_mem S') (by simpa using hgphi))
    have hle := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.card_ge_of_faithful_nonabelian
      hℓ hp hℓp hVcomm hVpow hS'p (ρ.comp S'.subtype) hfaith hnc'
    have hlt : ℓ ^ 4 < ℓ ^ p := Nat.pow_lt_pow_right hℓ.one_lt (by omega)
    omega
  · exact hρ

theorem coverActsTriviallyOnSmall_of_elemAbelian {p : ℕ} {L : Type*} [Group L] [Finite L]
    [IsSimpleGroup L] {E : Subgroup L} (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hexp : ∀ a ∈ E, a ^ 2 = 1) (hcard : 32 ≤ Nat.card E) : CoverActsTriviallyOnSmall p L := by
  intro J instJ finJ hJ φ hφ hcop hsol ℓ hℓ hℓ2 hℓp V instV finV hVcomm hVpow hVcard ρ
  rcases ker_le_or_eq_one hJ φ hφ hsol ρ with hker | hρ
  · exfalso
    have hq : Nat.Coprime 2 (Nat.card φ.ker) :=
      Nat.Coprime.of_dvd_left (dvd_mul_right 2 p) hcop.symm
    have hEcomm' : ∀ a b : ↥E, a * b = b * a := by
      intro a b
      apply Subtype.ext
      show (a : L) * (b : L) = (b : L) * (a : L)
      exact hcomm (a : L) a.2 (b : L) b.2
    haveI hEEA : IsElementaryAbelian 2 E :=
      { is_comm := ⟨hEcomm'⟩
        exponent_dvd_p := by
          rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
          intro x
          exact Subtype.ext (hexp x x.2) }
    have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
    obtain ⟨E', t', hE'2, hE'map, hE'inj, -, -⟩ :=
      exists_lift φ hφ hq hE2 (t := 1) (Subgroup.one_mem (Subgroup.normalizer (E : Set L)))
    have hE'comm : ∀ a b : ↥E', a * b = b * a := by
      intro a b
      apply Subtype.ext
      apply hE'inj (E'.mul_mem a.2 b.2) (E'.mul_mem b.2 a.2)
      simp only [Subgroup.coe_mul, map_mul]
      exact hcomm (φ a) (hE'map ▸ Subgroup.mem_map_of_mem φ a.2)
        (φ b) (hE'map ▸ Subgroup.mem_map_of_mem φ b.2)
    have hE'pow : ∀ a : ↥E', a ^ 2 = 1 := by
      intro a
      apply Subtype.ext
      apply hE'inj (E'.pow_mem a.2 2) (Subgroup.one_mem E')
      simp only [Subgroup.coe_pow, map_pow, map_one]
      exact hexp (φ a) (hE'map ▸ Subgroup.mem_map_of_mem φ a.2)
    let ρ' : ↥E' →* MulAut V := ρ.comp E'.subtype
    have hρ'faith : ∀ g : ↥E', ρ' g = 1 → g = 1 := by
      intro g hg
      have hgker : (g : J) ∈ ρ.ker := MonoidHom.mem_ker.mpr hg
      have hgphi : φ (g : J) = 1 := MonoidHom.mem_ker.mp (hker hgker)
      exact Subtype.ext (hE'inj g.2 (Subgroup.one_mem E') (by simpa using hgphi))
    have hρ'inj : Function.Injective ρ' := (injective_iff_map_eq_one ρ').mpr hρ'faith
    let A : Subgroup (MulAut V) := ρ'.range
    have hAcard : Nat.card ↥A = Nat.card ↥E' := by
      have h := Subgroup.card_map_of_injective (f := ρ') (K := ⊤) hρ'inj
      rwa [Subgroup.map_top, Subgroup.card_top] at h
    have hAcomm : ∀ a b : ↥A, a * b = b * a := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hb
      apply Subtype.ext
      change ρ' x * ρ' y = ρ' y * ρ' x
      rw [← map_mul, ← map_mul, hE'comm]
    have hApow : ∀ a : ↥A, a ^ 2 = 1 := by
      rintro ⟨a, ha⟩
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
      apply Subtype.ext
      change (ρ' x) ^ 2 = 1
      rw [← map_pow, hE'pow, map_one]
    haveI hAEA : IsElementaryAbelian 2 A :=
      { is_comm := ⟨hAcomm⟩
        exponent_dvd_p := by
          rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
          exact hApow }
    haveI hℓfact : Fact ℓ.Prime := ⟨hℓ⟩
    haveI hVEA : IsElementaryAbelian ℓ V :=
      { is_comm := ⟨hVcomm⟩
        exponent_dvd_p := by
          rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
          exact hVpow }
    have hVp : IsPGroup ℓ V := IsElementaryAbelian.isPGroup ℓ V
    obtain ⟨n, hncard⟩ := IsPGroup.iff_card.mp hVp
    obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hVcomm hVpow hncard
    let ψ : MulAut V ≃* GL (Fin n) (ZMod ℓ) := CFSG.SectionRank.Ccomm.elemAutEquivGL e
    let B : Subgroup (GL (Fin n) (ZMod ℓ)) := A.map ψ.toMonoidHom
    haveI hBEA : IsElementaryAbelian 2 B :=
      IsElementaryAbelian.map (A := A) ψ.toMonoidHom
    have h2 : (2 : ZMod ℓ) ≠ 0 := by
      intro hzero
      have hdvd : ℓ ∣ 2 := (ZMod.natCast_eq_zero_iff 2 ℓ).mp hzero
      have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hge : 2 ≤ ℓ := hℓ.two_le
      omega
    have hBle : Nat.card ↥B ≤ 2 ^ n := by
      simpa using CFSG.LieType.TwoRank.card_le_two_pow_of_isElementaryAbelian h2 B
    have hBcard : Nat.card ↥B = Nat.card ↥A :=
      Subgroup.card_map_of_injective (f := ψ.toMonoidHom) (K := A) ψ.injective
    have hcardE' : Nat.card ↥E' = Nat.card ↥E := by
      rw [← hE'map]
      exact (Nat.card_image_of_injOn hE'inj).symm
    have h32 : 32 ≤ 2 ^ n := by
      calc 32 ≤ Nat.card ↥E := hcard
        _ = Nat.card ↥E' := hcardE'.symm
        _ = Nat.card ↥A := hAcard.symm
        _ = Nat.card ↥B := hBcard.symm
        _ ≤ 2 ^ n := hBle
    have hn4 : 4 < n := by
      by_contra h
      have hnle : n ≤ 4 := by omega
      have hpow : 2 ^ n ≤ 2 ^ 4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hnle
      omega
    have hlt : ℓ ^ 4 < ℓ ^ n := Nat.pow_lt_pow_right hℓ.one_lt hn4
    have hle : ℓ ^ n ≤ ℓ ^ 4 := hncard ▸ hVcard
    omega
  · exact hρ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
