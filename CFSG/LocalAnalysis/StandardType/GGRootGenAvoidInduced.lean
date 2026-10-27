module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenKGDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private theorem ggConjAut_eq_self_iff {G : Type} [Group G] {Bs : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs) :
    ggConjAut Bs hg b = b ↔ g * (b : G) = (b : G) * g := by
  constructor
  · intro h
    have h1 := congrArg (fun x : ↥Bs => (x : G)) h
    rw [ggConjAut_apply] at h1
    calc g * (b : G) = g * (b : G) * g⁻¹ * g := by group
      _ = (b : G) * g := by rw [h1]
  · intro h
    apply Subtype.ext
    rw [ggConjAut_apply]
    calc g * (b : G) * g⁻¹ = (b : G) * g * g⁻¹ := by rw [h]
      _ = (b : G) := by group

private theorem mulAut_conj_commute_iff {G H : Type} [Group G] [Group H]
    {A : Subgroup (MulAut G)} {A_R : Subgroup (MulAut H)} (e : ↥A ≃* ↥A_R)
    {n : G} {m : H}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut G)))
    (hm : MulAut.conj m ∈ Subgroup.normalizer (A_R : Set (MulAut H)))
    (hcompat : ∀ a : ↥A, e (ggConjAut A hn a) = ggConjAut A_R hm (e a)) (a : ↥A) :
    MulAut.conj n * a.1 = a.1 * MulAut.conj n ↔
      MulAut.conj m * (e a).1 = (e a).1 * MulAut.conj m := by
  have h1 : MulAut.conj n * a.1 = a.1 * MulAut.conj n ↔ ggConjAut A hn a = a :=
    (ggConjAut_eq_self_iff hn a).symm
  have h2 : MulAut.conj m * (e a).1 = (e a).1 * MulAut.conj m ↔
      ggConjAut A_R hm (e a) = e a :=
    (ggConjAut_eq_self_iff hm (e a)).symm
  have h3 : ggConjAut A hn a = a ↔ ggConjAut A_R hm (e a) = e a := by
    rw [← hcompat a]
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [h1, h3, ← h2]

section InducedSubEquiv

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

theorem inducedSubEquiv_ggConjAut (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l))
    {n : L'} {m : R} (hψn : ψ n = m)
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hm : MulAut.conj m ∈
      Subgroup.normalizer (TypeA.inducedSub ψ A : Set (MulAut R))) (a : ↥A) :
    TypeA.inducedSubEquiv hψ hker hperf hind (ggConjAut A hn a) =
      ggConjAut (TypeA.inducedSub ψ A) hm (TypeA.inducedSubEquiv hψ hker hperf hind a) := by
  apply Subtype.ext
  refine TypeA.induced_unique ψ hψ (a := (ggConjAut A hn a).1)
    (TypeA.inducedSubEquiv_apply hψ hker hperf hind (ggConjAut A hn a)) ?_
  intro l
  rw [ggConjAut_apply, ggConjAut_apply, ← hψn]
  exact TypeA.conj_induced_apply ψ (a := a.1) (φ := (TypeA.inducedSubEquiv hψ hker hperf hind a).1)
    (TypeA.inducedSubEquiv_apply hψ hker hperf hind a) n l

private theorem inducedSub_conj_mem_of_normalizer (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')}
    (hind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l))
    {n : L'} {m : R} (hψn : ψ n = m)
    (hm : MulAut.conj m ∈
      Subgroup.normalizer (TypeA.inducedSub ψ A : Set (MulAut R)))
    {a : MulAut L'} (ha : a ∈ A) :
    MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A := by
  obtain ⟨φ, hφa⟩ := hind a ha
  have hφR : φ ∈ TypeA.inducedSub ψ A := ⟨a, ha, hφa⟩
  have hmem := (Subgroup.mem_normalizer_iff.mp hm φ).mp hφR
  obtain ⟨a', ha', hφa'⟩ := TypeA.mem_inducedSub.mp hmem
  have heq : MulAut.conj n * a * (MulAut.conj n)⁻¹ = a' := by
    apply TypeA.mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← hφa' l, ← hψn]
    exact (TypeA.conj_induced_apply ψ hφa n l).symm
  rw [heq]
  exact ha'

theorem inducedSub_conj_mem_normalizer (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l))
    {n : L'} {m : R} (hψn : ψ n = m)
    (hm : MulAut.conj m ∈
      Subgroup.normalizer (TypeA.inducedSub ψ A : Set (MulAut R))) :
    MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact inducedSub_conj_mem_of_normalizer hker hperf hind hψn hm ha
  · intro ha
    have hψn' : ψ n⁻¹ = m⁻¹ := by rw [map_inv, hψn]
    have hm' : MulAut.conj (m⁻¹) ∈
        Subgroup.normalizer (TypeA.inducedSub ψ A : Set (MulAut R)) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hm
    have h1 := inducedSub_conj_mem_of_normalizer hker hperf hind hψn' hm'
      (a := MulAut.conj n * a * (MulAut.conj n)⁻¹) ha
    have h2 : MulAut.conj n⁻¹ * (MulAut.conj n * a * (MulAut.conj n)⁻¹) *
        (MulAut.conj n⁻¹)⁻¹ = a := by
      rw [map_inv]
      group
    rwa [h2] at h1

private theorem GGIsReflection.congr {p : ℕ} {G H : Type} [Group G] [Group H] {A : Subgroup G}
    {Bs : Subgroup H} (e : ↥A ≃* ↥Bs) {φ : MulAut ↥A} (h : GGIsReflection p φ) :
    GGIsReflection p (MulAut.congr e φ) := by
  refine ⟨by rw [← map_pow, h.1, map_one], ?_⟩
  have hfix : Nat.card {b : ↥Bs // MulAut.congr e φ b = b} =
      Nat.card {a : ↥A // φ a = a} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun b => ?_)
    rw [MulAut.congr_apply]
    show e (φ (e.symm b)) = b ↔ φ (e.symm b) = e.symm b
    constructor
    · intro hb
      have h1 := congrArg e.symm hb
      rwa [MulEquiv.symm_apply_apply] at h1
    · intro hb
      rw [hb, MulEquiv.apply_symm_apply]
  rw [hfix, h.2]
  exact Nat.card_congr e.toEquiv

private theorem GGIsReflection.congr_iff {p : ℕ} {G H : Type} [Group G] [Group H] {A : Subgroup G}
    {Bs : Subgroup H} (e : ↥A ≃* ↥Bs) {φ : MulAut ↥A} :
    GGIsReflection p (MulAut.congr e φ) ↔ GGIsReflection p φ := by
  refine ⟨fun h => ?_, GGIsReflection.congr e⟩
  have hcomp : MulAut.congr e.symm (MulAut.congr e φ) = φ := by
    ext x
    simp [MulAut.congr_apply]
  have h1 := GGIsReflection.congr e.symm h
  rwa [hcomp] at h1

private theorem mulAut_congr_eq_of_apply {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {f : MulAut G} {g : MulAut H} (h : ∀ a, e (f a) = g (e a)) : MulAut.congr e f = g := by
  ext b
  rw [MulAut.congr_apply]
  have h1 := h (e.symm b)
  rwa [MulEquiv.apply_symm_apply] at h1

theorem mem_commutator_comap_of_pow_two_pow
    {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hodd : ∀ z ∈ ψ.ker, Odd (orderOf z))
    {P : Subgroup R} (hP : ⁅P, P⁆ = P) {x : L'} (hx : ψ x ∈ P)
    {k : ℕ} (hx2 : x ^ (2 ^ k) = 1) : x ∈ ⁅P.comap ψ, P.comap ψ⁆ := by
  let J := ⁅P.comap ψ, P.comap ψ⁆
  have hmap : J.map ψ = P := CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hP
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (show ψ x ∈ J.map ψ by rw [hmap]; exact hx)
  let z := y⁻¹ * x
  have hz : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have hzcentral : z ∈ Subgroup.center L' := hker hz
  have hyz : Commute y z := (Subgroup.mem_center_iff.mp hzcentral y)
  have hxz : x = y * z := by dsimp [z]; group
  have hm : x ^ orderOf z ∈ J := by
    rw [hxz, hyz.mul_pow, pow_orderOf_eq_one, mul_one]
    exact J.pow_mem hy _
  have hc : (orderOf z).Coprime (2 ^ k) := (Nat.coprime_two_right.mpr (hodd z hz)).pow_right k
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have hpow : x = (x ^ orderOf z) ^ a * (x ^ (2 ^ k)) ^ b := by
    rw [← zpow_natCast x (orderOf z), ← zpow_natCast x (2 ^ k),
      ← zpow_mul, ← zpow_mul, ← zpow_add]
    have h1 : (orderOf z : ℤ) * a + (2 ^ k : ℕ) * b = 1 := by linarith [hab]
    rw [h1, zpow_one]
  rw [hpow]
  exact J.mul_mem (J.zpow_mem hm a) (J.zpow_mem (hx2 ▸ J.one_mem) b)

theorem isComponentOf_commutator_comap_ggHypCent
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} {A_R : Subgroup (MulAut R)}
    (hA_R : ∀ φ ∈ A_R, ∃ a ∈ A, ∀ l, φ (ψ l) = ψ (a l))
    (e : ↥A ≃* ↥A_R)
    (he : ∀ (a : ↥A) (l : L'), ((e a : ↥A_R) : MulAut R) (ψ l) = ψ (a.1 l))
    {n : L'}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hm : MulAut.conj (ψ n) ∈ Subgroup.normalizer (A_R : Set (MulAut R)))
    (hcompat : ∀ a : ↥A, e (ggConjAut A hn a) = ggConjAut A_R hm (e a))
    {J_R : Subgroup R} (hcomp : IsComponentOf J_R (ggHypCent A_R (ψ n))) :
    IsComponentOf ⁅J_R.comap ψ, J_R.comap ψ⁆ (ggHypCent A n) ∧
      (⁅J_R.comap ψ, J_R.comap ψ⁆).map ψ = J_R := by
  have hq : CFSG.IsQuasisimple ↥J_R := (TableBSymp.isQuasisimple_iff ↥J_R).mp hcomp.2.2
  have hperf : ⁅J_R, J_R⁆ = J_R := Subgroup.isPerfect_iff.1 hq.1
  have hmap : (⁅J_R.comap ψ, J_R.comap ψ⁆).map ψ = J_R :=
    CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hperf
  have hcm : ∀ a : ↥A, MulAut.conj n * a.1 = a.1 * MulAut.conj n ↔
      MulAut.conj (ψ n) * (e a).1 = (e a).1 * MulAut.conj (ψ n) :=
    fun a => mulAut_conj_commute_iff e hn hm hcompat a
  have hle : ggHypCent A n ≤ (ggHypCent A_R (ψ n)).comap ψ := by
    intro z hz
    rw [Subgroup.mem_comap]
    refine Subgroup.mem_iInf.mpr fun φ => Subgroup.mem_iInf.mpr fun hφ => ?_
    obtain ⟨a, ha, hφa⟩ := hA_R φ hφ.1
    have hea : ((e ⟨a, ha⟩ : ↥A_R) : MulAut R) = φ :=
      TypeA.induced_unique ψ hψ (he ⟨a, ha⟩) hφa
    have hzn : a z = z := by
      have h1 := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hz a)
        ⟨ha, (hcm ⟨a, ha⟩).mpr (by rw [hea]; exact hφ.2)⟩
      rwa [mem_ggFix] at h1
    rw [mem_ggFix, ← hea, he ⟨a, ha⟩ z, hzn]
  have hleJ : ⁅J_R.comap ψ, J_R.comap ψ⁆ ≤ ggHypCent A n := by
    refine le_iInf fun a => le_iInf fun ha => ?_
    refine LayerCC.commutator_le_ggFix fun y hy => ?_
    have hmem : ψ y ∈ ggHypCent A_R (ψ n) := hcomp.1 hy
    have hfix : ((e ⟨a, ha.1⟩ : ↥A_R) : MulAut R) (ψ y) = ψ y := by
      have h1 := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hmem (e ⟨a, ha.1⟩).1)
        ⟨(e ⟨a, ha.1⟩).2, (hcm ⟨a, ha.1⟩).mp ha.2⟩
      rwa [mem_ggFix] at h1
    exact hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← he ⟨a, ha.1⟩ y, hfix, inv_mul_cancel])
  have hsub : IsSubnormal ⁅J_R.comap ψ, J_R.comap ψ⁆ (ggHypCent A n) := by
    have hnorm : ((⁅J_R.comap ψ, J_R.comap ψ⁆).subgroupOf (J_R.comap ψ)).Normal :=
      ⟨fun n hn g => CFSG.RankThree.PartOne.KCUnitary.conj_mem_commutator_self g.2 hn⟩
    have h1 : IsSubnormal ⁅J_R.comap ψ, J_R.comap ψ⁆ ((ggHypCent A_R (ψ n)).comap ψ) :=
      IsSubnormal.step (CFSG.RankThree.PartOne.KCUnitary.commutator_self_le _) hnorm
        (hcomp.2.1.comap ψ)
    exact LayerCC.isSubnormal_of_le h1 hleJ hle
  exact ⟨⟨hleJ, hsub, (TableBSymp.isQuasisimple_iff _).mpr
    (CFSG.RankThree.PartOne.S15K.isQuasisimple_commutator_comap hψ hker hq)⟩, hmap⟩

end InducedSubEquiv

theorem conj_mem_normalizer_inducedSub
    {L R : Type} [Group L] [Group R] (ψ : L →* R)
    {A : Subgroup (MulAut L)} {n : L}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L))) :
    MulAut.conj (ψ n) ∈ Subgroup.normalizer (TypeA.inducedSub ψ A : Set (MulAut R)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro φ
  constructor
  · rintro ⟨a, ha, hφ⟩
    refine ⟨MulAut.conj n * a * (MulAut.conj n)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hn a).mp ha, ?_⟩
    exact TypeA.conj_induced_apply ψ hφ n
  · intro hφ
    obtain ⟨a, ha, hφa⟩ := TypeA.mem_inducedSub.mp hφ
    let b := (MulAut.conj n)⁻¹ * a * MulAut.conj n
    have hb : b ∈ A := by
      have heq : MulAut.conj n * b * (MulAut.conj n)⁻¹ = a := by dsimp [b]; group
      exact (Subgroup.mem_normalizer_iff.mp hn b).mpr (heq.symm ▸ ha)
    refine ⟨b, hb, fun l => ?_⟩
    have hcompat := TypeA.conj_induced_apply ψ
      (a := a) (φ := MulAut.conj (ψ n) * φ * (MulAut.conj (ψ n))⁻¹) hφa n⁻¹ l
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one, b] using hcompat

theorem ggHypCent_eq_centralizer_comap
    {R : Type} {G : Type*} [Group R] [Group G]
    (ι : R →* G) (hι : Function.Injective ι)
    {A : Subgroup (MulAut R)} (ρ : A →* G)
    (hconj : ∀ (a : A) (x : R), ι (a.1 x) = ρ a * ι x * (ρ a)⁻¹)
    {n : R} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut R))) :
    ggHypCent A n = (Subgroup.centralizer
      (((ggConjAut A hn).toMonoidHom.eqLocus (MonoidHom.id A)).map ρ : Set G)).comap ι := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    have ha' : MulAut.conj n * a.1 = a.1 * MulAut.conj n := by
      have h := congrArg Subtype.val (show ggConjAut A hn a = a from ha)
      rw [ggConjAut_apply] at h
      exact (mul_inv_eq_iff_eq_mul).mp h
    have hax : a.1 x = x :=
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx a.1) ⟨a.2, ha'⟩
    have h := hconj a x
    rw [hax] at h
    exact (mul_inv_eq_iff_eq_mul).mp h.symm
  · intro hx
    refine Subgroup.mem_iInf.mpr fun a => Subgroup.mem_iInf.mpr fun ha => ?_
    let a₀ : A := ⟨a, ha.1⟩
    have ha₀ : ggConjAut A hn a₀ = a₀ := by
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact (mul_inv_eq_iff_eq_mul).mpr ha.2
    have hc := hx (ρ a₀) (Subgroup.mem_map.mpr ⟨a₀, ha₀, rfl⟩)
    rw [mem_ggFix]
    apply hι
    rw [hconj a₀ x, hc, mul_inv_cancel_right]

theorem ggHypCent_induced_eq_centralizer_comap
    {L R : Type} {G : Type*} [Group L] [Group R] [Group G]
    {ψ : L →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) {A : Subgroup (MulAut L)}
    (hAI : ∀ a ∈ A, ∃ α : MulAut R, ∀ x, α (ψ x) = ψ (a x))
    (ι : R →* G) (hι : Function.Injective ι) (ρ : A →* G)
    (hconj : ∀ (a : A) (x : L), ι (ψ (a.1 x)) = ρ a * ι (ψ x) * (ρ a)⁻¹)
    {n : L} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L))) :
    ggHypCent (TypeA.inducedSub ψ A) (ψ n) = (Subgroup.centralizer
      (((ggConjAut A hn).toMonoidHom.eqLocus (MonoidHom.id A)).map ρ : Set G)).comap ι := by
  let B := TypeA.inducedSub ψ A
  let e := TypeA.inducedSubEquiv hψ hker hperf hAI
  have hm := conj_mem_normalizer_inducedSub ψ hn
  let ρB : B →* G := ρ.comp e.symm.toMonoidHom
  have hBconj : ∀ (b : B) (x : R), ι (b.1 x) = ρB b * ι x * (ρB b)⁻¹ := by
    intro b x
    obtain ⟨a, rfl⟩ := e.surjective b
    obtain ⟨l, rfl⟩ := hψ x
    rw [TypeA.inducedSubEquiv_apply hψ hker hperf hAI]
    simpa only [ρB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hconj a l
  have hH : ((ggConjAut B hm).toMonoidHom.eqLocus (MonoidHom.id B)).map ρB =
      ((ggConjAut A hn).toMonoidHom.eqLocus (MonoidHom.id A)).map ρ := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, rfl⟩ := e.surjective b
      have hcompat := inducedSubEquiv_ggConjAut hψ hker hperf hAI rfl hn hm a
      have ha : ggConjAut A hn a = a := e.injective (hcompat.trans hb)
      exact ⟨a, ha, by simp only [ρB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply]⟩
    · rintro ⟨a, ha, rfl⟩
      have hcompat := inducedSubEquiv_ggConjAut hψ hker hperf hAI rfl hn hm a
      have ha' : ggConjAut A hn a = a := ha
      have hb : ggConjAut B hm (e a) = e a := hcompat.symm.trans (congrArg e ha')
      exact ⟨e a, hb, by simp only [ρB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply]⟩
  rw [ggHypCent_eq_centralizer_comap ι hι ρB hBconj hm, hH]


theorem ggTorusRootGenAvoid_of_inducedSub {p : ℕ} {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hinn : ∀ a ∈ A, ∃ x : L', a = MulAut.conj x)
    (hcomm : ∀ x y : L', MulAut.conj x ∈ A → MulAut.conj y ∈ A → x * y = y * x)
    (h : GGTorusRootGenAvoid p (TypeA.inducedSub ψ A)) :
    GGTorusRootGenAvoid p A := by
  classical
  intro ρ
  have hind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨x, rfl⟩ := hinn a ha
    exact ⟨MulAut.conj (ψ x), fun l => by
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]⟩
  let A_R := TypeA.inducedSub ψ A
  let e : ↥A ≃* ↥A_R := TypeA.inducedSubEquiv hψ hker hperf hind
  have he : ∀ (a : ↥A) (l : L'), ((e a : ↥A_R) : MulAut R) (ψ l) = ψ (a.1 l) :=
    TypeA.inducedSubEquiv_apply hψ hker hperf hind
  let T : Subgroup L' := ⨆ (n : L')
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) (J : Subgroup L')
    (_ : GGTorusWeylElt p A n ∧ GGIsReflection p (ggConjAut A hn) ∧ ggConjAut A hn ≠ ρ ∧
      n ∈ J ∧ IsComponentOf J (ggHypCent A n) ∧ p ∣ Nat.card J), J
  change T = ⊤
  have hle : ∀ (m : R) (hm : MulAut.conj m ∈ Subgroup.normalizer (A_R : Set (MulAut R)))
      (J_R : Subgroup R), (GGTorusWeylElt p A_R m ∧ GGIsReflection p (ggConjAut A_R hm) ∧
        ggConjAut A_R hm ≠ MulAut.congr e ρ ∧ m ∈ J_R ∧
        IsComponentOf J_R (ggHypCent A_R m) ∧ p ∣ Nat.card J_R) → J_R ≤ T.map ψ := by
    intro m hm J_R hcond
    obtain ⟨-, hreflR, hneR, hmJ, hcompR, hdvdR⟩ := hcond
    have hmapJ : (⁅J_R.comap ψ, J_R.comap ψ⁆).map ψ = J_R :=
      CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ
        (Subgroup.isPerfect_iff.1 ((TableBSymp.isQuasisimple_iff ↥J_R).mp hcompR.2.2).1)
    have hmem : m ∈ (⁅J_R.comap ψ, J_R.comap ψ⁆).map ψ := by rw [hmapJ]; exact hmJ
    obtain ⟨n, hnJ, hψn⟩ := Subgroup.mem_map.mp hmem
    obtain rfl : m = ψ n := hψn.symm
    have hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
      inducedSub_conj_mem_normalizer hker hperf hind hψn hm
    have hcompat : ∀ a : ↥A, e (ggConjAut A hn a) = ggConjAut A_R hm (e a) :=
      inducedSubEquiv_ggConjAut hψ hker hperf hind hψn hn hm
    have hcomp : IsComponentOf ⁅J_R.comap ψ, J_R.comap ψ⁆ (ggHypCent A n) :=
      (isComponentOf_commutator_comap_ggHypCent hψ hker
        (fun φ hφ => TypeA.mem_inducedSub.mp hφ) e he hn hm hcompat hcompR).1
    have hW : GGTorusWeylElt p A n :=
      ggTorusWeylElt_of_conj_mem_normalizer hA hinn hcomm hn
    have hgcc : MulAut.congr e (ggConjAut A hn) = ggConjAut A_R hm :=
      mulAut_congr_eq_of_apply e hcompat
    have hrefl : GGIsReflection p (ggConjAut A hn) :=
      (GGIsReflection.congr_iff e).mp (hgcc ▸ hreflR)
    have hne : ggConjAut A hn ≠ ρ := by
      intro hEq
      exact hneR (by rw [← hgcc, hEq])
    have hdvd : p ∣ Nat.card ↥⁅J_R.comap ψ, J_R.comap ψ⁆ := by
      have h1 : Nat.card ((⁅J_R.comap ψ, J_R.comap ψ⁆).map ψ) ∣
          Nat.card ↥⁅J_R.comap ψ, J_R.comap ψ⁆ :=
        Subgroup.card_map_dvd ⁅J_R.comap ψ, J_R.comap ψ⁆ ψ
      rw [hmapJ] at h1
      exact hdvdR.trans h1
    let J : Subgroup L' := ⁅J_R.comap ψ, J_R.comap ψ⁆
    have hterm : J ≤ T :=
      le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le J
        (le_iSup_of_le ⟨hW, hrefl, hne, hnJ, hcomp, hdvd⟩ le_rfl)))
    rw [← hmapJ]
    exact Subgroup.map_mono hterm
  have hmapT : T.map ψ = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← h (MulAut.congr e ρ)]
    exact iSup_le fun m => iSup_le fun hm => iSup_le fun J_R => iSup_le fun hcond =>
      hle m hm J_R hcond
  have hY : ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ = ⊤ := by
    rw [← commutator_def]
    exact hperf
  have h2 : (⊤ : Subgroup L').map ψ ≤ ⨆ _ : Unit, T.map ψ := by
    rw [Subgroup.map_top_of_surjective ψ hψ]
    simp only [iSup_const, hmapT, le_top]
  have htop : ⊤ ≤ T := by
    have h1 := CFSG.RankThree.PartOne.S15K.le_iSup_of_isPerfect_of_map_le (ι := Unit)
      (Φ := ψ) hker (Q := fun _ => T) (F := fun _ => T.map ψ) (Y := ⊤) (fun _ => rfl) hY h2
    simpa using h1
  exact eq_top_iff.mpr htop

end CFSG.StandardType
