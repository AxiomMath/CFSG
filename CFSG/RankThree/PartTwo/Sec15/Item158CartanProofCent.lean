module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofSigma
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofSignal
public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofInv
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open CFSG.RankThree.PartTwo.Sec14.Proof142Res (centP mem_centP_iff)

namespace Proof158CartanCent

section Solvable

theorem isSolvable_of_commutator_mem {X : Type*} [Group X] {M T : Subgroup X}
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hMT : ∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ T) : Group.IsSolvable M := by
  have h1 : derivedSeries M 1 ≤ T.subgroupOf M := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_subgroupOf, commutatorElement_def]
    exact hMT g₁ g₁.2 g₂ g₂.2
  have h2 : derivedSeries M 2 = ⊥ := by
    rw [derivedSeries_succ, eq_bot_iff]
    refine (Subgroup.commutator_mono h1 h1).trans ?_
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hT _ (Subgroup.mem_subgroupOf.mp hg₁) _ (Subgroup.mem_subgroupOf.mp hg₂))
  exact ⟨⟨2, h2⟩⟩

variable {K : Type} [Field K]

theorem conj_scalar_mul {z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (g y : GL (Fin 3) K) : g * (z * y) * g⁻¹ = z * (g * y * g⁻¹) := by
  have h := commute_of_mem_statedScalars hz g
  calc g * (z * y) * g⁻¹ = (g * z) * y * g⁻¹ := by group
    _ = (z * g) * y * g⁻¹ := by rw [h]
    _ = z * (g * y * g⁻¹) := by group

theorem commutator_mem_of_mem_centMod {L : Subgroup (GL (Fin 3) K)} {y a b : GL (Fin 3) K}
    (ha : a ∈ centMod L y) (hb : b ∈ centMod L y) :
    a * b * a⁻¹ * b⁻¹ ∈ L ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) := by
  obtain ⟨haL, za, hza, hay⟩ := mem_centMod_iff_scalar.mp ha
  obtain ⟨hbL, zb, hzb, hby⟩ := mem_centMod_iff_scalar.mp hb
  refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.mul_mem (L.mul_mem haL hbL) (L.inv_mem haL))
    (L.inv_mem hbL), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hza' := commute_of_mem_statedScalars hza
  have hzb' := commute_of_mem_statedScalars hzb
  have hay' : a⁻¹ * y * a = za⁻¹ * y := by
    have h1 : y = a⁻¹ * (za * y) * a := by rw [← hay]; group
    have hc := commute_of_mem_statedScalars (inv_mem hza) a⁻¹
    calc a⁻¹ * y * a = (a⁻¹ * za⁻¹) * (za * y) * a := by group
      _ = (za⁻¹ * a⁻¹) * (za * y) * a := by rw [hc]
      _ = za⁻¹ * (a⁻¹ * (za * y) * a) := by group
      _ = za⁻¹ * y := by rw [← h1]
  have hby' : b⁻¹ * y * b = zb⁻¹ * y := by
    have h1 : y = b⁻¹ * (zb * y) * b := by rw [← hby]; group
    have hc := commute_of_mem_statedScalars (inv_mem hzb) b⁻¹
    calc b⁻¹ * y * b = (b⁻¹ * zb⁻¹) * (zb * y) * b := by group
      _ = (zb⁻¹ * b⁻¹) * (zb * y) * b := by rw [hc]
      _ = zb⁻¹ * (b⁻¹ * (zb * y) * b) := by group
      _ = zb⁻¹ * y := by rw [← h1]
  have key : (a * b * a⁻¹ * b⁻¹) * y * (a * b * a⁻¹ * b⁻¹)⁻¹ = y := by
    calc (a * b * a⁻¹ * b⁻¹) * y * (a * b * a⁻¹ * b⁻¹)⁻¹ =
        (a * b * a⁻¹) * (b⁻¹ * y * b) * (a * b * a⁻¹)⁻¹ := by group
      _ = (a * b * a⁻¹) * (zb⁻¹ * y) * (a * b * a⁻¹)⁻¹ := by rw [hby']
      _ = zb⁻¹ * ((a * b) * (a⁻¹ * y * a) * (a * b)⁻¹) := by
          rw [conj_scalar_mul (inv_mem hzb)]; group
      _ = zb⁻¹ * ((a * b) * (za⁻¹ * y) * (a * b)⁻¹) := by rw [hay']
      _ = zb⁻¹ * (za⁻¹ * (a * (b * y * b⁻¹) * a⁻¹)) := by
          rw [conj_scalar_mul (inv_mem hza)]; group
      _ = zb⁻¹ * (za⁻¹ * (a * (zb * y) * a⁻¹)) := by rw [hby]
      _ = zb⁻¹ * (za⁻¹ * (zb * (a * y * a⁻¹))) := by rw [conj_scalar_mul hzb]
      _ = zb⁻¹ * (za⁻¹ * (zb * (za * y))) := by rw [hay]
      _ = y := by
          have e1 : za⁻¹ * (zb * (za * y)) = zb * y := by
            rw [← mul_assoc zb, ← hzb' za, mul_assoc za, ← mul_assoc]; group
          rw [e1]; group
  calc (a * b * a⁻¹ * b⁻¹) * y = (a * b * a⁻¹ * b⁻¹) * y * (a * b * a⁻¹ * b⁻¹)⁻¹ *
        (a * b * a⁻¹ * b⁻¹) := by group
    _ = y * (a * b * a⁻¹ * b⁻¹) := by rw [key]

theorem isSolvable_centMod {L : Subgroup (GL (Fin 3) K)} {y : GL (Fin 3) K}
    (hT : ∀ a ∈ L ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)),
      ∀ b ∈ L ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)), a * b = b * a) :
    Group.IsSolvable (centMod L y) :=
  isSolvable_of_commutator_mem hT fun _ ha _ hb => commutator_mem_of_mem_centMod ha hb

variable {π : Bool} {p f : ℕ}

theorem isSolvable_centP {y : GL (Fin 3) K}
    (h : Group.IsSolvable (centMod (slPi π 3 (p ^ f) K) y)) :
    Group.IsSolvable (centP (slPi π 3 (p ^ f) K) y) := by
  have hMS : centMod (slPi π 3 (p ^ f) K) y ≤ slPi π 3 (p ^ f) K := inf_le_left
  have hle : centP (slPi π 3 (p ^ f) K) y ≤
      ((centMod (slPi π 3 (p ^ f) K) y).subgroupOf (slPi π 3 (p ^ f) K)).map
        (projOf (slPi π 3 (p ^ f) K)) := by
    intro s hs
    obtain ⟨m, hmS, hms⟩ := Subgroup.mem_map.mp s.2
    refine ⟨⟨m, hmS⟩, Subgroup.mem_subgroupOf.mpr (Sec13.mem_centMod_of_mk_commute hmS ?_),
      Subtype.ext hms⟩
    rw [hms]
    exact (mem_centP_iff.mp hs).symm
  have h1 : Group.IsSolvable
      ((centMod (slPi π 3 (p ^ f) K) y).subgroupOf (slPi π 3 (p ^ f) K)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hMS).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hMS).injective
  have h2 : Group.IsSolvable (((centMod (slPi π 3 (p ^ f) K) y).subgroupOf
      (slPi π 3 (p ^ f) K)).map (projOf (slPi π 3 (p ^ f) K))) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem centP_mul_eq {y z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K) :
    centP (slPi π 3 (p ^ f) K) (y * z) = centP (slPi π 3 (p ^ f) K) y := by
  have hmkz : ProjGenLinGroup.mk z = 1 := mk_eq_one_iff_mem_statedScalars.mpr hz
  ext s
  rw [mem_centP_iff, mem_centP_iff, map_mul, hmkz, mul_one]

theorem isSolvable_centP_of_type3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) (hy3 : Type123 π (p ^ f) K y 3) :
    Group.IsSolvable (centP (slPi π 3 (p ^ f) K) y) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hya : y * y * y⁻¹ * y⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  obtain ⟨y', ⟨z, hz, rfl⟩, hcyc, -⟩ := Sec13.exists_irreducible_structure hK hq hyH hy3.1
    hy3.2.1 (not_inner_of_type3 hK hq hyH hy3) hy3 hya
  have hTcomm : ∀ a ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y * z} : Set (GL (Fin 3) K)),
      ∀ c ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y * z} : Set (GL (Fin 3) K)),
        a * c = c * a := by
    intro a ha c hc
    have h1 := (IsCyclic.commGroup (α := ↥(slPi π 3 (p ^ f) K ⊓
      Subgroup.centralizer ({y * z} : Set (GL (Fin 3) K))))).mul_comm ⟨a, ha⟩ ⟨c, hc⟩
    exact congrArg Subtype.val h1
  rw [← centP_mul_eq (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)]
  exact isSolvable_centP (isSolvable_centMod hTcomm)

theorem isSolvable_centP_of_type1 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {s : GL (Fin 3) K} (hsH : s ∈ glPi π 3 (p ^ f) K) (hsZ : s ∉ zPi π 3 (p ^ f) K)
    (hs3 : s ^ 3 ∈ zPi π 3 (p ^ f) K) (hs1 : Type123 π (p ^ f) K s 1) :
    Group.IsSolvable (centP (slPi π 3 (p ^ f) K) s) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨y', ⟨z, hz, rfl⟩, h⟩ := rank3II_4_10_one hK hq hτ hτ1 hsH hsZ hs3
  rcases h with ⟨-, ⟨φ⟩, -⟩ | ⟨⟨g, hg, e, he, hD⟩, -, -⟩ | ⟨-, hirr, -⟩
  · have hTcomm : ∀ a ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({s * z} : Set (GL (Fin 3) K)),
        ∀ c ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({s * z} : Set (GL (Fin 3) K)),
          a * c = c * a := by
      intro a ha c hc
      have h1 : φ (⟨a, ha⟩ * ⟨c, hc⟩) = φ (⟨c, hc⟩ * ⟨a, ha⟩) := by
        rw [map_mul, map_mul, mul_comm]
      exact congrArg Subtype.val (φ.injective h1)
    rw [← centP_mul_eq (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)]
    exact isSolvable_centP (isSolvable_centMod hTcomm)
  · exfalso
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [Units.val_one] at he
      have hτ0 : τ ≠ 0 := by
        rintro rfl
        simp at hτ
      rcases he with he | he
      · exact hτ1 he.symm
      · apply hτ1
        have h2 : τ ^ 2 * τ = τ ^ 3 := by ring
        rw [← he, one_mul, hτ] at h2
        exact h2
    exact not_type123_one_two hK hq hs1 ⟨e, he3, he1, z, hz, g, hg, hD⟩
  · exact (not_type123_three_of_one hK hq hs1 ⟨hsZ, hs3, hirr⟩).elim

end Solvable

section Fixed

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_inf_centralizer_of_thetaFix {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) {M : Type*} [Group M] {C : Subgroup M}
    (hC : Group.IsSolvable C) (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* M)
    (he : ∀ u ∈ Sec14.thetaFix L hb, e u ∈ C) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have hNL : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ L := inf_le_left
  set φ : ↥(L ⊓ Subgroup.centralizer ({b} : Set G)) →* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hNL) with hφ
  have hrange : ∀ g, (e.toMonoidHom.comp φ) g ∈ C := fun g =>
    he _ (Sec14.mem_thetaFix_of_mem_centralizer hb (g := Subgroup.inclusion hNL g) g.2.2)
  set ψ := (e.toMonoidHom.comp φ).codRestrict C hrange with hψ
  have hker : ∀ n ∈ ψ.ker, Subgroup.inclusion hNL n ∈ aschbacherSolvableCore 3 ↥L := by
    intro n hn
    have h1 : e (φ n) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
    have h2 : φ n = 1 := e.injective (h1.trans e.map_one.symm)
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hθ : Group.IsSolvable (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  set ι : ↥ψ.ker →* ↥(aschbacherSolvableCore 3 ↥L) :=
    ((Subgroup.inclusion hNL).comp ψ.ker.subtype).codRestrict _ fun n => hker n n.2 with hι
  have hιinj : Function.Injective ι := by
    intro n₁ n₂ h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (Subgroup.inclusion_injective hNL h1)
  have hK : Group.IsSolvable ψ.ker := Group.isSolvable_of_isSolvable_injective hιinj
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by rw [Subgroup.range_subtype])

theorem isSolvable_of_inducesTypeOn_three {L : Subgroup G} {b : G}
    (hb : InducesTypeOn L b 3) : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨hbN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hb
  refine isSolvable_inf_centralizer_of_thetaFix hbN (isSolvable_centP_of_type3 hK hq hyH hy3) e
    fun u hu => ?_
  rw [mem_centP_iff]
  have h1 := hact u
  rw [show thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hbN⟩) u = u from hu] at h1
  calc (e u : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk y =
      (ProjGenLinGroup.mk y * (e u : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) *
        ProjGenLinGroup.mk y := by rw [← h1]
    _ = ProjGenLinGroup.mk y * (e u : ProjGenLinGroup (Fin 3) K) := by group

theorem isSolvable_of_mem_of_commute_type3 {L : Subgroup G} {d x : G} (hdL : d ∈ L)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hxd : x * d = d * x) (hx : InducesTypeOn L x 3) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  set σx := thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) with hσx
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  set db : ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ d' with hdb
  have hdb3 : db ^ 3 = 1 := by rw [hdb, ← map_pow, hd'3, map_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (Sec16.Proof1613Inv.isPGroup_zpowers_three hd'3) (Subgroup.mem_zpowers _)
      (Subgroup.one_mem _) (by rw [map_one]; exact h1)
    exact hd1 (congrArg Subtype.val h2)
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e db).2
  have hsH : s ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) K := by
    intro hsZ
    apply hdb1
    apply e.injective
    apply Subtype.ext
    rw [← hse, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse, ← Subgroup.coe_pow, ← map_pow, hdb3,
      map_one, Subgroup.coe_one]
  have hfix : σx db = db := by
    rw [hσx, hdb, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe, hxd, mul_inv_cancel_right]
  have h1 := hact db
  rw [hfix, ← hse] at h1
  have hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1,
      mul_inv_cancel]
  have htype : Type123 π (p ^ f) K s 1 :=
    Sec14.Proof142Res.type1_of_commute_mod_type3 hK hq hy3 hs hsZ hs3 hysZ
  have hsZ' : s ∉ zPi π 3 (p ^ f) K := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hs3' : s ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3⟩
  have hσd : thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) = MulAut.conj db := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [thetaQuotMulAut_mk, MulAut.conj_apply, hdb, QuotientGroup.mk'_apply,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
  apply isSolvable_inf_centralizer_of_thetaFix hdN
    (isSolvable_centP_of_type1 hK hq hsH hsZ' hs3' htype) e
  intro u hu
  have hu' : db * u * db⁻¹ = u := by
    have h2 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) u = u := hu
    rwa [hσd, MulAut.conj_apply] at h2
  have hcomm : u * db = db * u := by
    calc u * db = (db * u * db⁻¹) * db := by rw [hu']
      _ = db * u := by group
  rw [mem_centP_iff, hse]
  have h3 := congrArg (fun v => ((e v : projImage (slPi π 3 (p ^ f) K)) :
    ProjGenLinGroup (Fin 3) K)) hcomm
  simpa only [map_mul, Subgroup.coe_mul] using h3

end Fixed

end Proof158CartanCent

open Proof158CartanCent

theorem ks158CentSolvR : KS158CentSolvR := by
  intro G _ _ A c L hR p e _ he hL3 hPGL htype a haA hac
  have hD := hR.toSec13Data
  obtain ⟨x, hxA, hx⟩ := htype
  have hA := hD.isElemAbelian
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  have hAN := hD.le_normalizer
  have hLc := hD.le_centralizer
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hD.commute ha hb
  obtain ⟨d, hdAL, hd1, -⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL)
  have hdA : d ∈ A := hdAL.1
  have hdL : d ∈ L := hdAL.2
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot hD
    (Sec13.facts_of_isZ3PGLThreePi hD hPGL).2.1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have h9 := Sec13.card_zpowers_sup_zpowers_eq_nine hA h27 hcA hdA hd1 hcd
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN hcA
  have hσc : ∀ k : ℤ, ∀ hk : c ^ k ∈ Subgroup.normalizer (L : Set G),
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨c ^ k, hk⟩) = 1 := by
    intro k hk
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [thetaQuotMulAut_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe]
      have hlc : (l : G) * c ^ k = c ^ k * l :=
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)) k)
      rw [← hlc, mul_inv_cancel_right]
  have hxcd : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro hxm
    obtain ⟨i, j, hxij⟩ := exists_zpow_mul_of_mem_sup (hcomm c hcA d hdA) hxm
    have hx' := Sec14.Proof142Res.inducesTypeOn_mul_of_eq_one hx (Subgroup.zpow_mem _ hcN (-i))
      (hσc (-i) (Subgroup.zpow_mem _ hcN (-i)))
    apply Sec16.Proof1613Fix.not_mem_of_inducesTypeOn_three hD.mem_thetaComponentsAt hx'
    rw [hxij, mul_assoc, (hcomm _ (Subgroup.zpow_mem _ hdA j) _
      (Subgroup.zpow_mem _ hcA (-i))), ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero,
      one_mul]
    exact Subgroup.zpow_mem _ hdL j
  obtain ⟨i, j, m, hm3, rfl⟩ := Sec14.Proof142Res.exists_pow_mul_eq hA h27 hcA hdA hxA h9 hxcd haA
  have hxd : x * d = d * x := hcomm x hxA d hdA
  have hle : L ⊓ Subgroup.centralizer ({c ^ i * d ^ j * x ^ m} : Set G) ≤
      L ⊓ Subgroup.centralizer ({d ^ j * x ^ m} : Set G) := by
    intro l hl
    obtain ⟨hlL, hla⟩ := Subgroup.mem_inf.mp hl
    refine Subgroup.mem_inf.mpr ⟨hlL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hla ⊢
    have hlc : l * c ^ i = c ^ i * l :=
      (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLc hlL)) i)
    have e1 : d ^ j * x ^ m = c ^ (-i) * (c ^ i * d ^ j * x ^ m) := by group
    have hlc' : l * c ^ (-i) = c ^ (-i) * l := by
      rw [zpow_neg]
      calc l * (c ^ i)⁻¹ = (c ^ i)⁻¹ * (c ^ i * l) * (c ^ i)⁻¹ := by group
        _ = (c ^ i)⁻¹ * (l * c ^ i) * (c ^ i)⁻¹ := by rw [hlc]
        _ = (c ^ i)⁻¹ * l := by group
    rw [e1]
    calc l * (c ^ (-i) * (c ^ i * d ^ j * x ^ m)) =
        (l * c ^ (-i)) * (c ^ i * d ^ j * x ^ m) := by group
      _ = c ^ (-i) * (l * (c ^ i * d ^ j * x ^ m)) := by rw [hlc']; group
      _ = c ^ (-i) * ((c ^ i * d ^ j * x ^ m) * l) := by rw [hla]
      _ = c ^ (-i) * (c ^ i * d ^ j * x ^ m) * l := by group
  suffices hsol : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({d ^ j * x ^ m} : Set G)) from
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
  ·
    have hdj1 : d ^ j ≠ 1 := by
      intro h1
      apply hac
      rw [h1, pow_zero, mul_one, mul_one]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i
    have hdj3 : (d ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
    have hxdj : x * d ^ j = d ^ j * x := (Commute.zpow_right hxd j).eq
    rw [pow_zero, mul_one]
    exact isSolvable_of_mem_of_commute_type3 (Subgroup.zpow_mem _ hdL j) hdj3 hdj1 hxdj hx
  ·
    have hb := Sec14.Proof142Res.inducesTypeOn_three_mul_zpow hdL hd3 hd1 hxd hx j
    have e1 : d ^ j * x ^ 1 = x * d ^ j := by
      rw [pow_one]
      exact (Commute.zpow_right hxd j).eq.symm
    rw [e1]
    exact isSolvable_of_inducesTypeOn_three hb
  ·
    have hb := Sec14.Proof142Res.inducesTypeOn_three_mul_zpow hdL hd3 hd1 hxd hx (2 * j)
    have hx3 : x ^ 3 = 1 := hA.2 x hxA
    set b := x * d ^ (2 * j) with hbdef
    have hcb : Commute x (d ^ (2 * j)) := Commute.zpow_right hxd (2 * j)
    have hd2j3 : (d ^ (2 * j)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
    have hb3 : b ^ 3 = 1 := by
      rw [hbdef, hcb.mul_pow, hx3, one_mul, hd2j3]
    have hb2 : d ^ j * x ^ 2 = b ^ 2 := by
      rw [hbdef, hcb.mul_pow, ← zpow_natCast (d ^ (2 * j)), ← zpow_mul]
      have hd4 : d ^ (2 * j * ((2 : ℕ) : ℤ)) = d ^ j := by
        have e2 : 2 * j * ((2 : ℕ) : ℤ) = j + 3 * j := by push_cast; ring
        rw [e2, zpow_add, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast,
          hd3, one_zpow, mul_one]
      rw [hd4]
      exact (Commute.zpow_right (Commute.pow_left hxd 2) j).eq.symm
    have hle2 : L ⊓ Subgroup.centralizer ({d ^ j * x ^ 2} : Set G) ≤
        L ⊓ Subgroup.centralizer ({b} : Set G) := by
      intro l hl'
      obtain ⟨hlL, hl⟩ := Subgroup.mem_inf.mp hl'
      refine Subgroup.mem_inf.mpr ⟨hlL, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hl ⊢
      rw [hb2] at hl
      have hl4 : l * b ^ 4 = b ^ 4 * l := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
        exact ((Commute.pow_right (Commute.symm (Commute.symm hl)) 2)).eq
      have e3 : b ^ 4 = b := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hb3, one_mul]
      rwa [e3] at hl4
    have hsb := isSolvable_of_inducesTypeOn_three hb
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle2)

end CFSG.RankThree.PartTwo.Sec15
