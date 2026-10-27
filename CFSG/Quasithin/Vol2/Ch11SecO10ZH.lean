module

public import CFSG.Quasithin.Vol2.Ch11SecO10Q

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

theorem isQuasisimple_of_simple {Y : Type*} [Group Y] (hs : IsSimpleGroup Y)
    (hnc : ∃ a b : Y, a * b ≠ b * a) : CFSG.IsQuasisimple Y := by
  obtain ⟨a, b, hab⟩ := hnc
  have hZ : Subgroup.center Y = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  have hperf : Group.IsPerfect Y := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exfalso
      apply hab
      have : ⁅a, b⁆ ∈ commutator Y :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact ⟨h⟩
  let e : Y ⧸ Subgroup.center Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem stronglyQuasithin_of_card {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 2520) :
    CFSG.Open.SQTKTauCeti.StronglyQuasithin Y := by
  intro p hp hp2
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hE⟩
  have hdvd : p ^ k ∣ 2520 := hE ▸ hY ▸ Subgroup.card_subgroup_dvd_card E
  by_contra hk3
  have h3 : p ^ 3 ∣ 2520 := (Nat.pow_dvd_pow p (by omega)).trans hdvd
  have hp3 : p ^ 3 ≤ 2520 := Nat.le_of_dvd (by norm_num) h3
  have hp13 : p ≤ 13 := by
    by_contra h
    have : 14 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases p
  all_goals first
    | exact absurd rfl hp2
    | exact absurd hp (by decide)
    | exact absurd h3 (by decide)

variable {G : Type} [Group G] [Finite G]

theorem sqtkGroup_autOn_of_fsu {T K I : Subgroup G} (hfsu : FSU G T K I)
    (hKV : K ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hcard : Nat.card ↥(autOn K (fsuV T I)) = 2520) : SQTKGroup ↥(autOn K (fsuV T I)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hfsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat hfsu.nonabelian hfsu.qtke).1
  have hVe := isElemAbelian_fsuV_of_fsu hfsu
  have hV2 : IsPGroup 2 (fsuV T I) := fun v => ⟨1, Subtype.ext (by simpa using hVe.2 v v.2)⟩
  have hIV : I ≤ fsuV T I := le_conjClosure I T
  have hP : pCoreOf 2 (Subgroup.normalizer (fsuV T I : Set G)) ≠ ⊥ := by
    have hle : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (fsuV T I : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV2
    intro hb
    rw [hb] at hle
    exact hfsu.irrPlus.2.1 (le_bot_iff.mp (hIV.trans hle))
  have hSK := InternalSec.sqtkGroup_mono (InternalSec.sqtkGroup_of_localSQTK hloc hP) hKV
  set f := InternalSec.autOnHom hKV with hf
  have hfs := InternalSec.autOnHom_surjective hKV
  let e : ↥K ⧸ f.ker ≃* ↥(autOn K (fsuV T I)) := QuotientGroup.quotientKerEquivOfSurjective f hfs
  exact ⟨stronglyQuasithin_of_card hcard, (hSK.2.quotient f.ker).of_mulEquiv e.symm⟩

omit [Finite G] in
theorem le_normalizer_conjugate {K I : Subgroup G} {t : G}
    (hKI : K ≤ Subgroup.normalizer (I : Set G)) (htK : t ∈ Subgroup.normalizer (K : Set G)) :
    K ≤ Subgroup.normalizer (CFSG.conjugate I t : Set G) := by
  intro k hk
  have hk' : t * k * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 htK k).1 hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  unfold CFSG.conjugate
  rw [Subgroup.map_map]
  have h1 : I.map (MulAut.conj (t * k * t⁻¹)).toMonoidHom = I :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hKI hk')
  calc I.map (((MulAut.conj k).toMonoidHom).comp (MulAut.conj t⁻¹).toMonoidHom)
      = (I.map (MulAut.conj (t * k * t⁻¹)).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [mul_assoc]
    _ = I.map (MulAut.conj t⁻¹).toMonoidHom := by rw [h1]

omit [Finite G] in
theorem mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

omit [Finite G] in
theorem irr_conjugate {K I : Subgroup G} {t : G} (htK : t ∈ Subgroup.normalizer (K : Set G))
    (hirr : ∀ J : Subgroup G, J ≤ I → K ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = I) :
    ∀ J : Subgroup G, J ≤ CFSG.conjugate I t → K ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = CFSG.conjugate I t := by
  intro J hJ hKJ
  have hJ' : CFSG.conjugate J t⁻¹ ≤ I := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have := mem_conjugate_iff.1 (hJ hx)
    simpa [mul_assoc] using this
  have hKJ' := le_normalizer_conjugate hKJ (Subgroup.inv_mem _ htK)
  have hmem : ∀ x, x ∈ J ↔ t * x * t⁻¹ ∈ CFSG.conjugate J t⁻¹ := fun x => by
    rw [mem_conjugate_iff, inv_inv]
    simp [mul_assoc]
  rcases hirr _ hJ' hKJ' with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    rw [hmem, h, Subgroup.mem_bot] at hx
    rw [Subgroup.mem_bot]
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [hx]; group
  · right
    ext x
    rw [hmem, h, mem_conjugate_iff]

omit [Finite G] in
theorem not_le_centralizer_conjugate {K I : Subgroup G} {t : G}
    (htK : t ∈ Subgroup.normalizer (K : Set G))
    (hI : ¬ I ≤ Subgroup.centralizer (K : Set G)) :
    ¬ CFSG.conjugate I t ≤ Subgroup.centralizer (K : Set G) := by
  intro h
  apply hI
  intro x hx
  have h1 : t⁻¹ * x * t ∈ CFSG.conjugate I t := by
    rw [mem_conjugate_iff]
    simpa [mul_assoc] using hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : t⁻¹ * k * t ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ htK) k).1 hk
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.1 (h h1) _ hk'
  calc k * x = t * ((t⁻¹ * k * t) * (t⁻¹ * x * t)) * t⁻¹ := by group
    _ = t * ((t⁻¹ * x * t) * (t⁻¹ * k * t)) * t⁻¹ := by rw [h2]
    _ = x * k := by group

end CFSG.Quasithin.Vol2.Ch11.O10
